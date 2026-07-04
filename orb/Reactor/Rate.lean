import Reactor.Serve
import Reactor.Deploy
import Rate.Trace

/-!
# Reactor.Rate — wiring the real token-bucket limiter into reactor admission

The `Rate` token bucket was proven in isolation (`Rate.rate_bound_cap`
bounds admits over a trace) but never consulted by anything that serves. This file
closes that gap: it puts the **real** bucket in front of the **real** reactor so
that a request the reactor serves is a request the bucket admitted.

Time is an input, exactly as `Rate` insists: an `Arrival` carries the client's
request bytes *and* the clock reading that is its time input. There is no ambient
clock; the wrapper refills the bucket to the arrival's clock before it decides.

The admission step (`admit`) does one thing: refill the real `Rate` bucket to the
arrival's clock, consult the real `Rate.tryAdmit`, and then

  * on **admit** — serve the request through the proven reactor (`Reactor.serve`);
  * on **reject** — answer with a `429 Too Many Requests` built by the proven
    serializer (so its framing is `serialize_framing`, not `s!`-glue).

The bucket the step returns is *exactly* `Rate.stepB`'s (`admit_bucket`), and the
served/rejected decision is *exactly* `Rate.admits`'s (`served_admits`). Those two
equalities are the seam: they force the reactor's admit-count to be the bucket's
admit-count (`servedCount_eq_countAdmits`), so `Rate.rate_bound_cap` transports
through unchanged.

**Seam theorem** — `reactor_rate_bound`: over a window of arrivals the number of
requests the reactor *admits* (serves, not 429s) is at most `cap + rate * D`,
where `D` is the window duration the clock advanced. A limiter that ignored the
bucket (a stub that always served) would break `served_admits` and so fail this
bound. `reactor_rate_bound_window`/`…_init` restate it against an explicit window
length `W`: from a cold start, at most `cap + rate * W` requests are served over a
window ending by clock `W`.
-/

namespace Reactor
namespace RateGate

open Proto (Bytes)

/-! ## The 429 rejection response (proven-serialized) -/

/-- `429` body prose. -/
def tooManyBody : Bytes := str "rate limit exceeded\n"

/-- Reason phrase for `429`. -/
def reason429 : Bytes := str "Too Many Requests"

/-- The `429 Too Many Requests` response, built by the proven serializer — its
bytes are `serialize` of a known `Response`, so framing is a theorem
(`resp429_framing`), never hand-interpolated. -/
def resp429 : Bytes := serialize (error4xx 429 reason429 tooManyBody)

/-! ## Arrivals: request bytes with their time input -/

/-- A timed arrival at the reactor: the client's request bytes together with the
clock reading that is its time input (time-as-input, per `Rate`). -/
structure Arrival where
  now : Nat
  input : Bytes
deriving Repr

/-- The `Rate` event an arrival denotes: a request at its arrival clock. This is
the single point that maps the reactor's admission vocabulary onto the bucket's,
so the two counts cannot drift. -/
def eventOf (a : Arrival) : Rate.Event := .req a.now

/-- The event trace a window of arrivals denotes. -/
def eventsOf (arrivals : List Arrival) : List Rate.Event := arrivals.map eventOf

/-! ## The rate-gated admission step -/

/-- **The rate-gated reactor admission step.** Refill the real `Rate` bucket to
the arrival's clock, then consult the real `Rate.tryAdmit`. On admit, the request
is served by the proven reactor (`Reactor.serve`); on reject, it is answered by
the proven-serialized 429. The bucket returned is exactly `Rate.stepB`'s. -/
def admit (b : Rate.Bucket) (a : Arrival) : Rate.Bucket × Bytes :=
  let r := Rate.tryAdmit (Rate.refill a.now b)
  (r.1, if r.2 then Reactor.serve a.input else resp429)

/-- Whether the gate admitted (served) this arrival: the real bucket's decision. -/
def served (b : Rate.Bucket) (a : Arrival) : Bool :=
  (Rate.tryAdmit (Rate.refill a.now b)).2

/-- Serve a whole window: the response bytes for each arrival, in order. Each is
either the proven reactor's served response or the proven-serialized 429. -/
def serveWindow (b : Rate.Bucket) : List Arrival → List Bytes
  | [] => []
  | a :: rest => (admit b a).2 :: serveWindow (admit b a).1 rest

/-- The number of arrivals the reactor **admitted** (served, not 429'd) over a
window — counted from the real bucket's decision at each step. -/
def servedCount (b : Rate.Bucket) : List Arrival → Nat
  | [] => 0
  | a :: rest => (if served b a then 1 else 0) + servedCount (admit b a).1 rest

/-! ## The seam: the gate's bucket and count ARE the bucket's own -/

/-- The gate's next bucket is exactly what `Rate.stepB` produces for the arrival's
event — the gate does not fork the bucket state. -/
theorem admit_bucket (b : Rate.Bucket) (a : Arrival) :
    (admit b a).1 = Rate.stepB b (eventOf a) := rfl

/-- An admitted arrival is answered by the proven reactor; a rejected one by the
proven-serialized 429 — the gate invents no bytes and the response tracks the
bucket's decision. -/
theorem admit_response (b : Rate.Bucket) (a : Arrival) :
    (admit b a).2 = if served b a then Reactor.serve a.input else resp429 := rfl

/-- The gate's served/rejected decision is exactly `Rate.admits` — a served
arrival contributes `1`, a rejected one `0`, matching the bucket's own count. -/
theorem served_admits (b : Rate.Bucket) (a : Arrival) :
    (if served b a then 1 else 0) = Rate.admits b (eventOf a) := by
  unfold served eventOf Rate.admits
  by_cases h1 : 1 ≤ (Rate.refill a.now b).tokens
  · rw [Rate.tryAdmit_snd_true h1]; simp [h1]
  · rw [Rate.tryAdmit_snd_false h1]; simp [h1]

/-- **The count seam.** The number of requests the gated reactor admits over a
window is exactly the `Rate` bucket's own admit count over the denoted event
trace. This is what forces the bound below to be about the real limiter: a stub
that served without consulting the bucket would break `served_admits` here. -/
theorem servedCount_eq_countAdmits (b : Rate.Bucket) (arrivals : List Arrival) :
    servedCount b arrivals = Rate.countAdmits b (eventsOf arrivals) := by
  induction arrivals generalizing b with
  | nil => rfl
  | cons a rest ih =>
    show (if served b a then 1 else 0) + servedCount (admit b a).1 rest
        = Rate.admits b (eventOf a)
            + Rate.countAdmits (Rate.stepB b (eventOf a)) (eventsOf rest)
    rw [served_admits, admit_bucket, ih]

/-! ## The rate bound, transported through the reactor -/

/-- **Seam theorem — `reactor_rate_bound`.** Over a window of arrivals, the number
of requests the reactor *admits* (serves, not 429s) is at most `cap + rate * D`,
where `D` is the duration the clock advanced over the window — provided the bucket
starts within capacity. This is `Rate.rate_bound_cap` transported through the
admission wrapper via the count seam: the reactor cannot serve more than the real
token bucket allows. -/
theorem reactor_rate_bound (b : Rate.Bucket) (arrivals : List Arrival)
    (h : b.tokens ≤ b.cap) :
    servedCount b arrivals ≤ b.cap + b.rate * Rate.duration b (eventsOf arrivals) := by
  rw [servedCount_eq_countAdmits]
  exact Rate.rate_bound_cap b (eventsOf arrivals) h

/-- **Cold start.** From a full-bucket cold boot, the reactor serves at most
`cap + rate * D` requests over a window. -/
theorem reactor_rate_bound_init (cap rate : Nat) (arrivals : List Arrival) :
    servedCount (Rate.init cap rate) arrivals
      ≤ cap + rate * Rate.duration (Rate.init cap rate) (eventsOf arrivals) := by
  rw [servedCount_eq_countAdmits]
  exact Rate.rate_bound_from_init cap rate (eventsOf arrivals)

/-! ## An explicit window length -/

/-- Over a run of arrivals whose clocks never exceed `W`, the recorded clock never
exceeds `W` — so the window duration is bounded by `W - last`. -/
theorem run_last_le (W : Nat) : ∀ (b : Rate.Bucket) (arrivals : List Arrival),
    b.last ≤ W → (∀ a ∈ arrivals, a.now ≤ W) →
    (Rate.run b (eventsOf arrivals)).last ≤ W := by
  intro b arrivals
  induction arrivals generalizing b with
  | nil => intro hb _; simpa [eventsOf, Rate.run] using hb
  | cons a rest ih =>
    intro hb hall
    have hnow : a.now ≤ W := hall a (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, x.now ≤ W := fun x hx => hall x (List.mem_cons_of_mem _ hx)
    have hstep : (Rate.stepB b (eventOf a)).last ≤ W := by
      show (Rate.tryAdmit (Rate.refill a.now b)).1.last ≤ W
      rw [Rate.tryAdmit_last_eq]
      unfold Rate.refill
      split
      · exact hnow
      · exact hb
    show (Rate.run (Rate.stepB b (eventOf a)) (eventsOf rest)).last ≤ W
    exact ih (Rate.stepB b (eventOf a)) hstep hrest

/-- **Windowed bound.** If every arrival's clock lies within a window that ends by
`W`, the reactor serves at most `cap + rate * (W - last)` requests. -/
theorem reactor_rate_bound_window (W : Nat) (b : Rate.Bucket) (arrivals : List Arrival)
    (hcap : b.tokens ≤ b.cap) (hlast : b.last ≤ W)
    (hall : ∀ a ∈ arrivals, a.now ≤ W) :
    servedCount b arrivals ≤ b.cap + b.rate * (W - b.last) := by
  have hbound := reactor_rate_bound b arrivals hcap
  have hdur : Rate.duration b (eventsOf arrivals) ≤ W - b.last := by
    unfold Rate.duration
    exact Nat.sub_le_sub_right (run_last_le W b arrivals hlast hall) b.last
  exact Nat.le_trans hbound
    (Nat.add_le_add_left (Nat.mul_le_mul (Nat.le_refl _) hdur) _)

/-- **Windowed bound, cold start.** From a full-bucket cold boot, the reactor
serves at most `cap + rate * W` requests over a window ending by clock `W`. This
is the headline rate-limiting guarantee, over the running reactor. -/
theorem reactor_rate_bound_window_init (W cap rate : Nat) (arrivals : List Arrival)
    (hall : ∀ a ∈ arrivals, a.now ≤ W) :
    servedCount (Rate.init cap rate) arrivals ≤ cap + rate * W := by
  have h := reactor_rate_bound_window W (Rate.init cap rate) arrivals
      (Nat.le_refl _) (by simp [Rate.init]) hall
  simpa [Rate.init, Nat.sub_zero] using h

/-! ## The 429 rejection is well-formed -/

/-- The `429` rejection is a well-formed HTTP response: its bytes decompose as
`statusLine ++ CRLF ++ headerBlock ++ CRLF ++ CRLF ++ body`, by the serializer's
`serialize_framing`. No `s!`-glue on the rejection path. -/
theorem resp429_framing :
    resp429
      = statusLineOf (error4xx 429 reason429 tooManyBody) ++ crlf
          ++ headerBlockOf (error4xx 429 reason429 tooManyBody) ++ crlf ++ crlf
          ++ tooManyBody :=
  serialize_framing (error4xx 429 reason429 tooManyBody)

/-! ## The deployed path

`admit` serves an admitted request through `Reactor.serve` (the test view). The
deployed orb serves through the full pipeline `Reactor.Deploy.serveFull`. The
rate bound depends only on the bucket's admit *decision* (`served`), never on the
bytes the served response contains, so plugging the deployed serve into the gate
leaves every count — and hence the bound — unchanged. The theorems below make
that explicit: the deployed-gated reactor admits no more than the real token
bucket allows, and an admitted arrival is answered by `serveFull` itself. -/

/-- The rate-gated admission step wired to the DEPLOYED serve pipeline: on admit,
the request is served through `Reactor.Deploy.serveFull` (the bytes `main`
writes); on reject, the same proven-serialized 429. The bucket transition is
identical to `admit`'s. -/
def admitDeployed (b : Rate.Bucket) (a : Arrival) : Rate.Bucket × Bytes :=
  let r := Rate.tryAdmit (Rate.refill a.now b)
  (r.1, if r.2 then Reactor.Deploy.serveFull a.input else resp429)

/-- The number of arrivals the deployed-gated reactor admits over a window —
counted from the real bucket's decision at each step, exactly as `servedCount`. -/
def servedCountDeployed (b : Rate.Bucket) : List Arrival → Nat
  | [] => 0
  | a :: rest => (if served b a then 1 else 0) + servedCountDeployed (admitDeployed b a).1 rest

/-- The deployed gate's bucket transition is exactly `admit`'s — swapping the
served-response function does not fork the bucket state. -/
theorem admitDeployed_bucket (b : Rate.Bucket) (a : Arrival) :
    (admitDeployed b a).1 = (admit b a).1 := rfl

/-- An admitted arrival, on the deployed gate, is answered by the deployed
pipeline `serveFull` itself — the bytes the orb writes, not a stub. -/
theorem admitDeployed_serves_full (b : Rate.Bucket) (a : Arrival)
    (h : served b a = true) :
    (admitDeployed b a).2 = Reactor.Deploy.serveFull a.input := by
  show (if served b a then Reactor.Deploy.serveFull a.input else resp429) = _
  rw [if_pos h]

/-- **The count is unchanged by the deployed serve.** The deployed-gated admit
count equals `servedCount`, because both count the same bucket decision and share
the same bucket transition (`admitDeployed_bucket`). -/
theorem servedCountDeployed_eq (b : Rate.Bucket) (arrivals : List Arrival) :
    servedCountDeployed b arrivals = servedCount b arrivals := by
  induction arrivals generalizing b with
  | nil => rfl
  | cons a rest ih =>
    show (if served b a then 1 else 0) + servedCountDeployed (admitDeployed b a).1 rest
        = (if served b a then 1 else 0) + servedCount (admit b a).1 rest
    rw [admitDeployed_bucket, ih]

/-- **`reactor_rate_bound_deployed` — the rate bound over the DEPLOYED serve
pipeline.** Over a window of arrivals, the number of requests the deployed-gated
reactor admits (serves through `serveFull`, not 429s) is at most `cap + rate * D`,
where `D` is the clock duration over the window — provided the bucket starts
within capacity. `reactor_rate_bound` transported across `servedCountDeployed_eq`:
routing admitted requests through the full deployed pipeline cannot lift the
bound. -/
theorem reactor_rate_bound_deployed (b : Rate.Bucket) (arrivals : List Arrival)
    (h : b.tokens ≤ b.cap) :
    servedCountDeployed b arrivals
      ≤ b.cap + b.rate * Rate.duration b (eventsOf arrivals) := by
  rw [servedCountDeployed_eq]
  exact reactor_rate_bound b arrivals h

/-- **Windowed bound, cold start, deployed.** From a full-bucket cold boot, the
deployed-gated reactor serves at most `cap + rate * W` requests over a window
ending by clock `W`. The headline rate guarantee, over the deployed serve. -/
theorem reactor_rate_bound_window_init_deployed (W cap rate : Nat)
    (arrivals : List Arrival) (hall : ∀ a ∈ arrivals, a.now ≤ W) :
    servedCountDeployed (Rate.init cap rate) arrivals ≤ cap + rate * W := by
  rw [servedCountDeployed_eq]
  exact reactor_rate_bound_window_init W cap rate arrivals hall

end RateGate
end Reactor
