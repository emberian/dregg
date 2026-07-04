import Reactor.Pipeline
import Rate

/-!
# Reactor.Stage.Rate — the rate-limit GATE, as a pipeline stage

A byte-driving `Stage` for the extensible serve fold: on the request phase it
consults the **real** `Rate` token bucket and, when the bucket is over the limit
(no token to spend), short-circuits the whole pipeline with a `429 Too Many
Requests` — the handler and every later stage are skipped. Under the limit the
request passes through untouched.

The decision is the real limiter, not a stub: `admits` runs `Rate.refill` to the
request's clock and then `Rate.tryAdmit`, exactly the `Rate.Bucket` transition
proven in `Rate/Bucket.lean`. The live bucket the gate decides on is read off the
context's attribute bag — the standing token count is the length of the token
attr, the arrival clock the length of the clock attr — so a request carrying no
tokens is over the limit and one carrying a token is under it.

The byte effect is a genuine change to the emitted response:

* `rateStage_gate_build` — over the limit, the built pipeline response IS the
  `429` (`rateStage_over_status`: its status byte is `429`);
* `rateStage_pass` — under the limit, the stage is transparent: the emitted bytes
  are the tail/handler's, unchanged;
* `rateStage_changes_bytes` — with the same handler and tail, an over-limit
  request and an under-limit request emit *different* status bytes: the gate
  really drives the wire.

`overCtx_over` / `underCtx_under` exhibit concrete over- and under-limit contexts
(closed by `decide` on the real bucket), so none of the above is vacuous.
-/

namespace Reactor.Stage.Rate

open Reactor.Pipeline
open Proto (Bytes)

/-! ## The 429 rejection response -/

/-- Reason phrase for the rejection. -/
def reason429 : Bytes := "Too Many Requests".toUTF8.toList

/-- Body prose for the rejection. -/
def tooManyBody : Bytes := "rate limit exceeded\n".toUTF8.toList

/-- The `429 Too Many Requests` response the gate answers with when the bucket is
over the limit — a real `Response` (`error4xx`) whose status is `429`. -/
def resp429 : Response := error4xx 429 reason429 tooManyBody

/-! ## Reading the live bucket off the context

The gate is stateless per request; the connection's live token count and the
arrival clock ride in the extensible attribute bag. The token count is the length
of the value at `tokKey` (a request carrying no tokens is over the limit), the
clock the length of the value at `nowKey`. `cap`/`rate` are fixed config. -/

/-- Attribute key holding the standing token bytes (its length = token count). -/
def tokKey : String := "rate-tokens"

/-- Attribute key holding the arrival-clock bytes (its length = the clock). -/
def nowKey : String := "rate-now"

/-- Burst capacity (max standing tokens). -/
def rateCap : Nat := 1000000

/-- Refill rate, tokens per clock unit. -/
def rateRate : Nat := 1

/-- Look the value bytes up for a key in the attribute bag (`[]` if absent). -/
def lookupBytes (c : Ctx) (k : String) : Bytes :=
  match c.attrs.find? (fun p => p.1 == k) with
  | some p => p.2
  | none   => []

/-- The live bucket the gate decides on, read off the context: standing tokens =
the token attr's length, clock last-set at `0`, `cap`/`rate` from config. -/
def bucketOf (c : Ctx) : _root_.Rate.Bucket :=
  { tokens := (lookupBytes c tokKey).length, last := 0, cap := rateCap, rate := rateRate }

/-- The arrival clock the gate refills to = the clock attr's length. -/
def clockOf (c : Ctx) : Nat := (lookupBytes c nowKey).length

/-- **The real admit decision.** Refill the context's bucket to its arrival clock,
then consult the real `Rate.tryAdmit`. `true` = a token was available (under the
limit, admit); `false` = none (over the limit, reject). This is exactly the
`Rate` transition, not a stub. -/
def admits (c : Ctx) : Bool :=
  (_root_.Rate.tryAdmit (_root_.Rate.refill (clockOf c) (bucketOf c))).2

/-! ## The stage -/

/-- **The rate-limit gate stage.** Request phase: consult the real bucket — admit
→ `.continue` (pass through), reject → `.respond resp429` (short-circuit with the
`429`, skipping the handler and every later stage). Response phase: transparent —
the affine builder is threaded through unchanged (the gate adds no bytes on the
pass-through path; its whole effect is the short-circuit). -/
def rateStage : Stage where
  name := "rate"
  onRequest  := fun c => cond (admits c) (.continue c) (.respond resp429)
  onResponse := fun _ b => b

/-! ## The gate's request-phase decision -/

/-- Over the limit, the gate short-circuits with the `429`. -/
theorem rateStage_onReq_respond (c : Ctx) (hover : admits c = false) :
    rateStage.onRequest c = .respond resp429 := by
  simp only [rateStage, hover, cond]

/-- Under the limit, the gate passes the context through. -/
theorem rateStage_onReq_continue (c : Ctx) (hunder : admits c = true) :
    rateStage.onRequest c = .continue c := by
  simp only [rateStage, hunder, cond]

/-! ## The byte effect -/

/-- **Gate byte-effect.** Over the limit, the BUILT pipeline response — for ANY
tail and handler — is exactly `resp429`: the handler and every later stage are
skipped and the emitted bytes are the `429`. Rides on `pipeline_gate_short_circuits`
and `build_ofResponse`. -/
theorem rateStage_gate_build (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : admits c = false) :
    (runPipeline (rateStage :: rest) h c).build = resp429 := by
  rw [pipeline_gate_short_circuits rateStage rest h c resp429
        (rateStage_onReq_respond c hover), build_ofResponse]

/-- The `429`'s status field is `429`. -/
theorem resp429_status : resp429.status = 429 := rfl

/-- The over-limit response's status byte is `429` — the change is visible on the
wire, not merely attached. -/
theorem rateStage_over_status (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : admits c = false) :
    ((runPipeline (rateStage :: rest) h c).build).status = 429 := by
  rw [rateStage_gate_build rest h c hover, resp429_status]

/-- **Pass-through byte-effect.** Under the limit, the stage is transparent: the
pipeline output is exactly the tail's — the gate contributes no bytes. Rides on
`pipeline_stage_effect` with the identity `onResponse`. -/
theorem rateStage_pass (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hunder : admits c = true) :
    runPipeline (rateStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect rateStage rest h c c (rateStage_onReq_continue c hunder)]
  rfl

/-! ## Concrete over- and under-limit contexts (non-vacuity) -/

/-- A context carrying no tokens — over the limit. -/
def overCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- A context carrying one token — under the limit. -/
def underCtx : Ctx := { input := [], req := {}, attrs := [(tokKey, [0])] }

/-- `overCtx` is over the limit — the real bucket rejects it. -/
theorem overCtx_over : admits overCtx = false := by decide

/-- `underCtx` is under the limit — the real bucket admits it. -/
theorem underCtx_under : admits underCtx = true := by decide

/-- An over-limit request emits a `429`. -/
theorem overCtx_emits_429 (rest : List Stage) (h : Ctx → Response) :
    ((runPipeline (rateStage :: rest) h overCtx).build).status = 429 :=
  rateStage_over_status rest h overCtx overCtx_over

/-- An under-limit request passes through to the tail unchanged. -/
theorem underCtx_passes (rest : List Stage) (h : Ctx → Response) :
    runPipeline (rateStage :: rest) h underCtx = runPipeline rest h underCtx :=
  rateStage_pass rest h underCtx underCtx_under

/-- **The gate genuinely drives the wire.** With the SAME handler and tail, an
over-limit request and an under-limit request emit different status bytes: the
over-limit one is forced to `429`, the under-limit one keeps the handler's status
(here, any status `≠ 429`). So the stage really changes the bytes the serve
emits — it is a byte-driver, not a proof attachment. -/
theorem rateStage_changes_bytes (h : Ctx → Response)
    (hstatus : (h underCtx).status ≠ 429) :
    ((runPipeline [rateStage] h overCtx).build).status
      ≠ ((runPipeline [rateStage] h underCtx).build).status := by
  rw [overCtx_emits_429 [] h, underCtx_passes [] h, pipeline_empty, build_ofResponse]
  exact fun heq => hstatus heq.symm

end Reactor.Stage.Rate
