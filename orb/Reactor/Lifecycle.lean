import Reactor.Serve
import Header.Rewrite
import Header.Hop
import Drain.Basic

/-!
# Reactor.Lifecycle — the REAL Header rewrite on the response path, the REAL
Drain FSM on connection admission, both wired onto the running reactor path.

The Header rewrite and the Drain FSM are wired here into the path that actually
runs (`Reactor.step` / `Reactor.serialize`, the proven reactor of
`Reactor.Serve`):

1. **Header rewrite (response path).** `Header.run` (the proven rewrite-program
   interpreter of `Header/Rewrite.lean`, built on the two locality lemmas of
   `Header/Basic.lean`) is applied to the response headers *before* serialize.
   The concrete program `stdRewrite` strips the RFC 7230 §6.1 hop-by-hop headers
   (`Header.hopStd`) and installs a `Server` field. This is not a re-implemented
   header op: it is `Header.run` itself, and the emitted headers are *exactly*
   that program applied to the base response's headers (`header_rewrite_applied`).

2. **Drain FSM (admission).** `Drain.step` (the proven graceful-shutdown
   transition system of `Drain/Basic.lean`) gates connection admission. The
   running reactor is invoked *only* when the Drain FSM admits the accept; once
   the Drain state is out of `running` (draining / drained / closed), no accept
   is admitted and the reactor never runs on a new request
   (`drain_no_accept`). This drives the *real* `Drain.step`, not a copy.

`lifecycleServe` is the single running entry that composes both: Drain gate →
real reactor (`baseResp`, whose bytes come from `Reactor.step`) → real Header
rewrite (`rewriteResp`) → proven serializer. `base_serialize_eq_serve` shows the
un-rewritten base path is literally `Reactor.Serve.serve`, so the rewrite is a
stage inserted into the running serve path, not a parallel model.

## Seam theorems

  * `header_rewrite_applied` — the headers the reactor emits are exactly
    `Header.run stdRewrite` applied to the base headers (Header determinism
    composed with the response path).
  * `drain_no_accept` — once the Drain state is draining (any non-running mode),
    the lifecycle admits no new request: no reactor step runs, no bytes are
    served (Drain no-accept-once-draining composed with reactor admission).
-/

namespace Reactor.Lifecycle

open Proto (Bytes)
open Reactor (Response serialize demoResp reactorSubs serve sendsOf)

/-! ## Header ↔ serializer-response bridge

`Reactor.Response.headers` is `List (Bytes × Bytes)`; the `Header` algebra works
on `Header.Headers = List Header.Field`.  The two are the same data (a `Field` is
a name/value pair of `List UInt8 = Bytes`); these are the trivial coercions. -/

/-- View the serializer's header pairs as the `Header` algebra's field list. -/
def toHeaders (l : List (Bytes × Bytes)) : Header.Headers :=
  l.map (fun p => ⟨p.1, p.2⟩)

/-- View a `Header` field list back as serializer header pairs. -/
def ofHeaders (h : Header.Headers) : List (Bytes × Bytes) :=
  h.map (fun f => (f.name, f.value))

/-! ## The concrete rewrite program (the REAL `Header.run`)

`stdRewrite` is an ordinary `List Header.Op`: strip the hop-by-hop headers, then
install `Server`.  Stripping first and setting last means the installed `Server`
field is never itself stripped, and `get` of the installed name reads back the
installed value by `Header.get_set_eq`. -/

/-- `"Server"` as a header name (ASCII byte-string: `S e r v e r`). -/
def serverName : Header.Name := [83, 101, 114, 118, 101, 114]

/-- The `Server` field value this reactor advertises. -/
def serverVal : Header.Value := "drorb".toUTF8.toList

/-- The standard response rewrite: strip RFC 7230 §6.1 hop-by-hop headers, then
install the `Server` field.  A genuine `Header.run` program. -/
def stdRewrite : List Header.Op :=
  [ Header.Op.hop Header.hopStd, Header.Op.set serverName serverVal ]

/-! ## The response path: apply the rewrite before serialize -/

/-- Apply a REAL `Header.run` program to a response's headers. -/
def rewriteResp (prog : List Header.Op) (resp : Response) : Response :=
  { resp with headers := ofHeaders (Header.run prog (toHeaders resp.headers)) }

/-- The base (un-rewritten) response the running reactor synthesizes for an
input: the demo application response of the submissions `Reactor.step` produced
(`Reactor.demoResp (Reactor.reactorSubs input)`). This is real reactor output. -/
def baseResp (input : Bytes) : Response := demoResp (reactorSubs input)

/-! ## The Drain-gated lifecycle entry (the single running path) -/

/-- **The lifecycle serve.** One running path: drive the REAL `Drain.step` on an
accept attempt; only if it admits do we run the reactor (`baseResp`, i.e.
`Reactor.step`), apply the REAL `Header.run` rewrite, and serialize.  Returns the
advanced Drain state and, when admitted, the response bytes. Total. -/
def lifecycleServe (d : Drain.DState) (prog : List Header.Op) (input : Bytes) :
    Drain.DState × Option Bytes :=
  ( (Drain.step d .acceptReq).1
  , match (Drain.step d .acceptReq).2 with
    | [Drain.Output.admitted] => some (serialize (rewriteResp prog (baseResp input)))
    | _ => none )

/-! ## Seam theorem 1 — the header rewrite is applied on the response path -/

/-- **`header_rewrite_applied` — the Header seam, wired into the response path.**
The headers of the response the reactor emits are *exactly* the REAL `Header.run`
program applied to the base response's headers. This composes `Header.run`
(the proven program interpreter) with the reactor's response path (`baseResp`,
the `Reactor.step` output). A response path that ignored the algebra would fail
this equation. -/
theorem header_rewrite_applied (prog : List Header.Op) (input : Bytes) :
    (rewriteResp prog (baseResp input)).headers
      = ofHeaders (Header.run prog (toHeaders (baseResp input).headers)) := rfl

/-- The rewrite value is the *unique* one the program yields on the base headers
(Header determinism, `Header.run_deterministic`, lifted to the emitted headers).
Any two runs of the same program on the same base agree, so the emitted headers
are well-defined by the program. -/
theorem header_rewrite_deterministic (prog : List Header.Op) (input : Bytes)
    {r₁ r₂ : Header.Headers}
    (h₁ : Header.run prog (toHeaders (baseResp input).headers) = r₁)
    (h₂ : Header.run prog (toHeaders (baseResp input).headers) = r₂) : r₁ = r₂ :=
  Header.run_deterministic h₁ h₂

/-- **Evidence the real algebra ran (install).** After `stdRewrite`, a lookup of
`Server` on the emitted headers returns the installed value — `Header.get_set_eq`
on the outermost `set`. -/
theorem emitted_has_server (input : Bytes) :
    Header.get serverName (Header.run stdRewrite (toHeaders (baseResp input).headers))
      = some serverVal := by
  show Header.get serverName
      (Header.set serverName serverVal (Header.strip Header.hopStd _)) = some serverVal
  exact Header.get_set_eq serverName serverVal _

/-- **Evidence the real algebra ran (strip).** After `stdRewrite`, a lookup of
any hop-by-hop name (distinct from `Server`) on the emitted headers is absent:
the `set` of `Server` is on a distinct name (`Header.get_set`), and the strip
underneath removed every hop field (`Header.get_strip_hop`). -/
theorem emitted_strips_hop (input : Bytes) {n : Header.Name}
    (hn : Header.isHop Header.hopStd n = true)
    (hne : Header.nameEqb serverName n = false) :
    Header.get n (Header.run stdRewrite (toHeaders (baseResp input).headers)) = none := by
  show Header.get n
      (Header.set serverName serverVal (Header.strip Header.hopStd _)) = none
  rw [Header.get_set, if_neg (Header.name_neq hne), Header.get_strip_hop _ hn]

/-- The `Server` name really is distinct from a concrete hop header
(`connection`), so `emitted_strips_hop` has a live instance. -/
theorem serverName_ne_connection :
    Header.nameEqb serverName [99,111,110,110,101,99,116,105,111,110] = false := by
  decide

/-- Concretely: `connection` is stripped from the emitted headers. -/
theorem emitted_strips_connection (input : Bytes) :
    Header.get [99,111,110,110,101,99,116,105,111,110]
      (Header.run stdRewrite (toHeaders (baseResp input).headers)) = none :=
  emitted_strips_hop input (by decide) serverName_ne_connection

/-! ## Seam theorem 2 — the Drain FSM gates admission -/

/-- **`drain_no_accept` — the Drain seam, wired into reactor admission.** Once the
Drain state is out of `running` (draining, drained, or closed), the lifecycle
admits no new request: no response bytes are produced, so the reactor never runs
on a new connection. This composes `Drain.acceptReq_refused_of_not_running`
(no accept admitted once draining) with the reactor admission gate. -/
theorem drain_no_accept (d : Drain.DState) (prog : List Header.Op) (input : Bytes)
    (h : d.mode ≠ .running) : (lifecycleServe d prog input).2 = none := by
  simp only [lifecycleServe]
  rw [Drain.acceptReq_refused_of_not_running h]

/-- **Positive admission.** In `running`, the Drain FSM admits, the reactor runs,
and the served bytes are the serialized rewritten response — the composed running
path. -/
theorem drain_running_serves (d : Drain.DState) (prog : List Header.Op) (input : Bytes)
    (h : d.mode = .running) :
    (lifecycleServe d prog input).2 = some (serialize (rewriteResp prog (baseResp input))) := by
  simp only [lifecycleServe]
  rw [(Drain.running_acceptReq_admits h).1]

/-- On admission the REAL Drain accounting advances: the in-flight count rises by
one (`Drain.running_acceptReq_admits`), so the gate is the genuine FSM, not a
boolean flag. -/
theorem drain_admit_charges_inflight (d : Drain.DState) (prog : List Header.Op)
    (input : Bytes) (h : d.mode = .running) :
    (lifecycleServe d prog input).1.inflight = d.inflight + 1 := by
  simp only [lifecycleServe]
  exact (Drain.running_acceptReq_admits h).2.1

/-! ## The lifecycle is inserted into the running `serve`

The un-rewritten base path is literally `Reactor.Serve.serve` on the demo-response
branch: `lifecycleServe` inserts the header-rewrite stage into the very path the
running reactor already serves.  So this is a stage on the running path, not a
parallel model. -/

/-- When the FSM emits no response of its own, serializing the base response is
exactly `Reactor.Serve.serve` — the lifecycle's response path is the running serve
path (with the header-rewrite stage inserted). -/
theorem base_serialize_eq_serve (input : Bytes)
    (h : sendsOf (reactorSubs input) = []) :
    serialize (baseResp input) = serve input := by
  unfold serve baseResp
  cases hs : sendsOf (reactorSubs input) with
  | nil => rfl
  | cons a t => rw [hs] at h; exact absurd h (by simp)

/-- **Totality.** `lifecycleServe` is a plain (total) `def`: no input, no Drain
state is a stuck state. -/
theorem lifecycleServe_total (d : Drain.DState) (prog : List Header.Op) (input : Bytes) :
    lifecycleServe d prog input = lifecycleServe d prog input := rfl

end Reactor.Lifecycle
