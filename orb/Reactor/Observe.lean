import Reactor.Serve
import Metrics.Basic
import Trace.Correlation
import Tap.Basic
import Tap.Trace

/-!
# Reactor.Observe — wiring the real Metrics, Trace and Tap libraries onto the
running reactor request path

Three observability libraries are proven in isolation and, on their own, consulted
by nothing that serves:

  * `Metrics` — monotone counters with an exact-delta identity (`inc_exact`);
  * `Trace.Correlation` — correlation-id assignment and faithful propagation
    (`inject_faithful` / `upstream_sees_request_corr`);
  * `Tap` — the gated diagnostic copy whose security property is a no-copy-when-
    disabled boundary (`no_copy_when_disabled`, the PF-6 info-leak property).

This file puts all three on the **running** per-request path. `observe` wraps the
proven reactor view `Reactor.serve` (the same view the Rate, App, and Body
wirings use): it serves the request through `serve` and, in the same step,

  1. bumps the **real** `Metrics` request counter by exactly one;
  2. assigns a correlation id with the **real** `Trace.process`, recording it so
     the id the reactor forwards is `Trace.inject`'s (propagation-faithful);
  3. offers the request bytes to the **real** `Tap.step` gate — the only way a
     request reaches the diagnostic sink.

Observation is a pure side-channel: `observe_transparent` /
`respWindow_eq_map_serve` prove the served bytes are exactly `serve`'s, never
rewritten — the observation cannot perturb the traffic it observes.

**Seam theorems.**

  * `metrics_counts_requests` — the reactor's served-request counter after a
    window of `N` requests equals the **real** `Metrics` counter incremented `N`
    times. Composes `Metrics.inc_exact` (the exact-delta identity) with the
    reactor fold; a wrapper that under/over-counted would break the per-step
    `inc_exact` and fail here.
  * `tap_gated_in_reactor` — over the reactor path the tap copies a request to the
    diagnostic sink ONLY when the gate is enabled. The default-disabled path
    leaks NOTHING (`tap_gated_in_reactor`, composing `Tap.no_copy_when_disabled`),
    and an enabled gate copies EXACTLY the served requests, in order
    (`tap_enabled_copies`, composing `Tap.enabled_faithful`). This is PF-6, the
    info-leak boundary, now on the running reactor path.
  * `reactor_corr_propagates` / `observe_records_corr` — the correlation id
    `observe` records on the running path is exactly the id the upstream request
    (`Trace.inject`) exposes (composing `Trace.upstream_sees_request_corr`).
-/

namespace Reactor
namespace Observe

open Proto (Bytes)

/-! ## The observation state — the three real library states, bundled -/

/-- The observation state threaded down the reactor path: the **real** `Metrics`
registry, the **real** `Tap` gate/sink over request bytes, and the correlation
ids assigned so far (newest first), each assigned by the **real** `Trace`. -/
structure ObsState where
  /-- The real `Metrics` registry (monotone counters). -/
  metrics : Metrics.Registry
  /-- The real `Tap` gate + sink; packets are request byte-strings. -/
  tap : Tap.State Bytes
  /-- The correlation ids assigned by the real `Trace`, newest first. -/
  corrs : List Trace.CorrId

/-- Cold start: empty registry, tap gate DISABLED (the safe default), no ids. -/
def ObsState.init : ObsState :=
  { metrics := Metrics.Registry.empty, tap := Tap.init, corrs := [] }

/-- A start with the tap gate already ENABLED — used to state enabled-window
faithfulness from a clean start. -/
def ObsState.initOn : ObsState :=
  { metrics := Metrics.Registry.empty, tap := Tap.initOn, corrs := [] }

/-! ## Vocabulary shared by the three concerns -/

/-- The counter name the reactor bumps per served request. -/
def reqCounter : String := "reactor.requests"

/-- The `Trace` generator seed a request denotes: its bytes as an id (the sole
input to a freshly generated correlation id, per `Trace.Correlation`). -/
def seedOf (input : Bytes) : Trace.CorrId := input.map UInt8.toNat

/-- The `Trace.Inbound` a request denotes: no client-supplied id, seeded by the
request bytes. Mapping the reactor's request vocabulary onto `Trace`'s in one
place keeps the two from drifting. -/
def inboundOf (input : Bytes) : Trace.Inbound :=
  { carried := none, seed := seedOf input }

/-- The correlation id the real `Trace` assigns to a request. -/
def corrOf (gen : Trace.CorrId → Trace.CorrId) (trust : Trace.Trust)
    (input : Bytes) : Trace.CorrId :=
  (Trace.process gen trust (inboundOf input)).corr

/-- The upstream request the reactor would forward this request on, with the
assigned id injected by the real `Trace.inject`. -/
def upstreamOf (gen : Trace.CorrId → Trace.CorrId) (trust : Trace.Trust)
    (input : Bytes) : Trace.UpReq :=
  Trace.inject (Trace.process gen trust (inboundOf input))

/-! ## The observed reactor step -/

/-- **The observed reactor step.** Serve the request through the **proven**
reactor (`Reactor.serve`), then update the observation state:

  * bump the **real** `Metrics` request counter by exactly one;
  * offer the request bytes to the **real** `Tap.step` gate (the only path to the
    diagnostic sink);
  * record the correlation id the **real** `Trace.process` assigned.

Returns the served response bytes (exactly `serve`'s — never rewritten) and the
new observation state. -/
def observe (gen : Trace.CorrId → Trace.CorrId) (trust : Trace.Trust)
    (st : ObsState) (input : Bytes) : Bytes × ObsState :=
  ( Reactor.serve input
  , { metrics := st.metrics.inc reqCounter 1
    , tap     := Tap.step st.tap (Tap.Ev.pkt input)
    , corrs   := (Trace.process gen trust (inboundOf input)).corr :: st.corrs } )

/-- Thread the observation state over a window of requests, left to right. -/
def obsRun (gen : Trace.CorrId → Trace.CorrId) (trust : Trace.Trust)
    (st : ObsState) : List Bytes → ObsState
  | [] => st
  | input :: rest => obsRun gen trust (observe gen trust st input).2 rest

/-- The served responses over a window — each is exactly the proven reactor's. -/
def respWindow (gen : Trace.CorrId → Trace.CorrId) (trust : Trace.Trust)
    (st : ObsState) : List Bytes → List Bytes
  | [] => []
  | input :: rest =>
      (observe gen trust st input).1
        :: respWindow gen trust (observe gen trust st input).2 rest

/-! ## Observation is transparent — the served bytes are the reactor's own -/

/-- **Transparency (step).** The bytes `observe` returns are exactly the proven
reactor's `serve` output — the observation never rewrites the response. -/
theorem observe_transparent (gen : Trace.CorrId → Trace.CorrId) (trust : Trace.Trust)
    (st : ObsState) (input : Bytes) :
    (observe gen trust st input).1 = Reactor.serve input := rfl

/-- **Transparency (window).** Over a window the observed responses are exactly
`serve` mapped over the requests — observation is a pure side-channel that leaves
every served byte untouched. -/
theorem respWindow_eq_map_serve (gen : Trace.CorrId → Trace.CorrId)
    (trust : Trace.Trust) (st : ObsState) (inputs : List Bytes) :
    respWindow gen trust st inputs = inputs.map Reactor.serve := by
  induction inputs generalizing st with
  | nil => rfl
  | cons input rest ih =>
    show (observe gen trust st input).1
        :: respWindow gen trust (observe gen trust st input).2 rest
      = Reactor.serve input :: rest.map Reactor.serve
    rw [ih (observe gen trust st input).2]
    rfl

/-! ## Seam 1 — Metrics counts served requests exactly -/

/-- The registry after `n` request-counter increments from empty — the **real**
`Metrics` lib applied `n` times. -/
def metricsAfter : Nat → Metrics.Registry
  | 0 => Metrics.Registry.empty
  | n + 1 => (metricsAfter n).inc reqCounter 1

/-- The `n`-times-incremented counter reads `n` — the real `Metrics` exact-delta
identity (`inc_exact`) accumulated. -/
theorem metricsAfter_counter (n : Nat) :
    (metricsAfter n).counters reqCounter = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show ((metricsAfter k).inc reqCounter 1).counters reqCounter = k + 1
    rw [Metrics.inc_exact, ih]

/-- The reactor's request counter after a window grows by exactly the window
length — each observed step adds exactly one via the real `Metrics.inc_exact`. -/
theorem obsRun_metrics_counter (gen : Trace.CorrId → Trace.CorrId)
    (trust : Trace.Trust) (st : ObsState) (inputs : List Bytes) :
    (obsRun gen trust st inputs).metrics.counters reqCounter
      = st.metrics.counters reqCounter + inputs.length := by
  induction inputs generalizing st with
  | nil => rfl
  | cons input rest ih =>
    have hstep : obsRun gen trust st (input :: rest)
        = obsRun gen trust (observe gen trust st input).2 rest := rfl
    rw [hstep, ih (observe gen trust st input).2]
    show (st.metrics.inc reqCounter 1).counters reqCounter + rest.length
        = st.metrics.counters reqCounter + (input :: rest).length
    rw [Metrics.inc_exact]
    simp only [List.length_cons]
    omega

/-- **Seam theorem — `metrics_counts_requests`.** From a cold start, the reactor's
served-request counter after a window of `N` requests equals the **real** `Metrics`
counter incremented `N` times. This composes `Metrics.inc_exact` (accumulated in
`metricsAfter_counter`) with the reactor fold (`obsRun_metrics_counter`): a wrapper
that dropped or double-counted a served request would break the per-step exact
delta and fail this equality. Both sides are `inputs.length`. -/
theorem metrics_counts_requests (gen : Trace.CorrId → Trace.CorrId)
    (trust : Trace.Trust) (inputs : List Bytes) :
    (obsRun gen trust ObsState.init inputs).metrics.counters reqCounter
      = (metricsAfter inputs.length).counters reqCounter := by
  rw [obsRun_metrics_counter, metricsAfter_counter]
  show Metrics.Registry.empty.counters reqCounter + inputs.length = inputs.length
  simp [Metrics.Registry.empty]

/-! ## Seam 2 — the Tap gate is the sole path to the diagnostic sink -/

/-- The `Tap` event trace a window of requests denotes: each request is offered to
the gate as a `.pkt`. There are no control edges here — the gate is moved only by
an operator's explicit enable/disable, never by traffic. -/
def pktTrace (inputs : List Bytes) : List (Tap.Ev Bytes) :=
  inputs.map Tap.Ev.pkt

/-- The reactor's tap state after a window is exactly `Tap.run` over the denoted
packet trace — the observed step IS the real `Tap.step`, threaded. -/
theorem obsRun_tap (gen : Trace.CorrId → Trace.CorrId) (trust : Trace.Trust)
    (st : ObsState) (inputs : List Bytes) :
    (obsRun gen trust st inputs).tap = Tap.run st.tap (pktTrace inputs) := by
  induction inputs generalizing st with
  | nil => rfl
  | cons input rest ih =>
    have hstep : obsRun gen trust st (input :: rest)
        = obsRun gen trust (observe gen trust st input).2 rest := rfl
    rw [hstep, ih (observe gen trust st input).2]
    show Tap.run (Tap.step st.tap (Tap.Ev.pkt input)) (pktTrace rest)
        = Tap.run st.tap (pktTrace (input :: rest))
    rfl

/-- A request-only trace carries no `.enable` control edge — traffic cannot open
the gate. -/
theorem pktTrace_no_enable (inputs : List Bytes) :
    Tap.hasEnable (pktTrace inputs) = false := by
  induction inputs with
  | nil => rfl
  | cons a rest ih =>
    show Tap.hasEnable (Tap.Ev.pkt a :: pktTrace rest) = false
    exact ih

/-- A request-only trace carries no `.disable` control edge. -/
theorem pktTrace_no_disable (inputs : List Bytes) :
    Tap.hasDisable (pktTrace inputs) = false := by
  induction inputs with
  | nil => rfl
  | cons a rest ih =>
    show Tap.hasDisable (Tap.Ev.pkt a :: pktTrace rest) = false
    exact ih

/-- Every packet in a request-only trace is exactly the request that produced it,
in order. -/
theorem pktsOf_pktTrace (inputs : List Bytes) :
    Tap.pktsOf (pktTrace inputs) = inputs := by
  induction inputs with
  | nil => rfl
  | cons a rest ih =>
    show a :: Tap.pktsOf (pktTrace rest) = a :: rest
    rw [ih]

/-- **Seam theorem — `tap_gated_in_reactor` (PF-6, info-leak boundary).** From a
cold start (tap gate DISABLED, the default), over any window of served requests
the diagnostic sink stays EMPTY — not one request is copied. Because traffic never
moves the gate (`pktTrace_no_enable`), this is the real `Tap.no_copy_when_disabled`
composed with the reactor path (`obsRun_tap`): the reactor copies a request to the
sink ONLY when the gate has been explicitly enabled. -/
theorem tap_gated_in_reactor (gen : Trace.CorrId → Trace.CorrId)
    (trust : Trace.Trust) (inputs : List Bytes) :
    (obsRun gen trust ObsState.init inputs).tap.sink = [] := by
  rw [obsRun_tap]
  have h : ObsState.init.tap = (Tap.init : Tap.State Bytes) := rfl
  rw [h]
  exact Tap.no_copy_when_disabled (pktTrace inputs) (pktTrace_no_enable inputs)

/-- **Seam theorem — `tap_enabled_copies` (the other direction).** From a start
with the gate ENABLED, the diagnostic sink is EXACTLY the served requests, in
arrival order — no drop, no injection, no reorder. This is the real
`Tap.enabled_faithful` composed with the reactor path. Together with
`tap_gated_in_reactor` it pins the copy to the gate: sink non-empty ⟺ gate enabled. -/
theorem tap_enabled_copies (gen : Trace.CorrId → Trace.CorrId)
    (trust : Trace.Trust) (inputs : List Bytes) :
    (obsRun gen trust ObsState.initOn inputs).tap.sink = inputs := by
  rw [obsRun_tap]
  have h : ObsState.initOn.tap = (Tap.initOn : Tap.State Bytes) := rfl
  rw [h, Tap.enabled_faithful (pktTrace inputs) (pktTrace_no_disable inputs),
      pktsOf_pktTrace]

/-! ## Seam 3 — the correlation id is assigned and propagated faithfully -/

/-- The observed step records exactly the id the real `Trace` assigned — the id
on the running path is the request's correlation id (`corrOf`). -/
theorem observe_records_corr (gen : Trace.CorrId → Trace.CorrId)
    (trust : Trace.Trust) (st : ObsState) (input : Bytes) :
    (observe gen trust st input).2.corrs.head? = some (corrOf gen trust input) := rfl

/-- **Seam theorem — `reactor_corr_propagates`.** The correlation id the reactor
assigns to a request is exactly the id the upstream request (built by the real
`Trace.inject`) exposes — the propagation the upstream actually sees, not merely a
copied projection. This is `Trace.upstream_sees_request_corr` on the reactor's own
`inboundOf` request. -/
theorem reactor_corr_propagates (gen : Trace.CorrId → Trace.CorrId)
    (trust : Trace.Trust) (input : Bytes) :
    Trace.upstreamCorr (upstreamOf gen trust input) = some (corrOf gen trust input) :=
  Trace.upstream_sees_request_corr gen trust (inboundOf input)

/-! ## Demo instantiation + concrete sanity checks -/

/-- Demo id generator: identity on the seed (a pure function of the seed input). -/
def demoGen : Trace.CorrId → Trace.CorrId := id

/-- Demo assignment policy: do not trust client-supplied ids — always generate. -/
def demoTrust : Trace.Trust := false

/-- Three served requests bump the real request counter to exactly three. -/
example :
    (obsRun demoGen demoTrust ObsState.init [str "a", str "b", str "c"]).metrics.counters
        reqCounter = 3 := by
  rw [obsRun_metrics_counter]; rfl

/-- Default-disabled: nothing served leaks to the diagnostic sink. -/
example :
    (obsRun demoGen demoTrust ObsState.init [str "a", str "b"]).tap.sink = [] :=
  tap_gated_in_reactor demoGen demoTrust [str "a", str "b"]

/-- Gate enabled: the sink is exactly the served requests, in order. -/
example :
    (obsRun demoGen demoTrust ObsState.initOn [str "a", str "b"]).tap.sink
      = [str "a", str "b"] :=
  tap_enabled_copies demoGen demoTrust [str "a", str "b"]

/-- The served bytes are the proven reactor's own — observation changed nothing. -/
example :
    respWindow demoGen demoTrust ObsState.init [str "a", str "b"]
      = [Reactor.serve (str "a"), Reactor.serve (str "b")] := by
  rw [respWindow_eq_map_serve]; rfl

end Observe
end Reactor
