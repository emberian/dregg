import Reactor.Contract
import Proxy.Balance

/-!
# Reactor.Proxy — the reverse-proxy handler: a dispatched request picks a real upstream

This wires the **real** `Proxy` load-balancer (`Proxy.selectChain` over the tiered,
health-filtered selection algebra) into the reactor's submission vocabulary. It sits
*above* dispatch: the reactor emits `RingSubmission.dispatch req` for a parsed request
(`Reactor.Contract`); the reverse-proxy handler consumes that request and, instead of
answering it locally (the `Reactor.App` static-handler path), forwards it to an
upstream backend chosen by the LB.

The wiring, outside-in:

  * `ProxyPool` — a policy chain (`A else B else C`) plus a backend pool. The pool
    carries each `Proxy.Backend` with its live `healthy` verdict (produced by the
    `Proxy.Health` machine) and admin `status` snapshotted in.
  * `chooseUpstream` — the selection call: literally `Proxy.selectChain`, which runs
    each policy on the best-tier *eligible* (healthy ∧ active) pool. Nothing here
    re-implements selection; the reactor delegates to the proven algebra.
  * `proxyHandle` — turn the LB verdict into reactor submissions: on a chosen backend
    `b`, emit exactly `RingSubmission.connectUpstream ⟨b.id⟩` (the reactor's own
    upstream-connect submission from `Reactor.Contract`); on no eligible backend, emit
    nothing.
  * `proxyRelay` — once the upstream tunnel is up (an `fd` exists), relay request bytes
    with `RingSubmission.submitSendUpstream`. Relaying is a strictly *later* phase: it
    consumes an `fd`, which only a completed connect produces.
  * `onDispatch` — the hand-off itself: match the reactor's `RingSubmission.dispatch`
    and run `proxyHandle` on its request payload. This pins the handler onto the
    dispatch seam.

**Seam theorem — `proxy_selects_healthy`.** The upstream the reactor targets for a
proxied request (recovered from the emitted submissions by `targetedUpstream`) is
exactly `addrOf` of the backend the REAL `Proxy.selectChain` picked, and that backend
is a healthy, active member of the current pool sitting in the best nonempty tier
(`Proxy.selectChain_eligible`, transported through the reactor). A stubbed selector —
one that hardcoded a backend without consulting the health-filtered pool — would fail
the eligibility conjunct; `demo_*` below exhibits a concrete pool where the naive
"first backend" stub targets an *unhealthy* upstream while the real LB does not.

**No upstream traffic before a backend is chosen** — `proxy_no_upstream_without_choice`:
when the LB selects nothing (no eligible backend), `proxyHandle` emits the empty
submission list — neither a `connectUpstream` nor a `submitSendUpstream`. Relay
(`submitSendUpstream`) never appears in `proxyHandle` at all (`proxyHandle_no_relay`),
because it is gated behind a connect-produced `fd`.
-/

namespace Reactor.Proxy

open Proto (Bytes Request Addr)

/-! ## The pool and the selection call -/

/-- The upstream backend's connect address: its stable identity becomes the opaque
`Proto.Addr` the reactor's `connectUpstream` submission carries. -/
def addrOf (b : Proxy.Backend) : Addr := ⟨b.id⟩

/-- A reverse-proxy upstream pool: the policy chain (first-match fallback across
policies) and the snapshotted backend pool the chain selects over. -/
structure ProxyPool where
  /-- The selection policy chain (`A else B else C`), tried in order. -/
  policies : List Proxy.Policy
  /-- The backend pool, each with its live health verdict and admin status. -/
  backends : List Proxy.Backend

/-- **The selection call.** Delegate to the REAL `Proxy.selectChain`: run the policy
chain over the best-tier eligible (healthy ∧ active) subset of the pool. `none` iff
the pool has no eligible backend at all. -/
def chooseUpstream (pool : ProxyPool) (ctx : Proxy.Ctx) : Option Proxy.Backend :=
  Proxy.selectChain pool.policies ctx pool.backends

/-! ## The reactor submissions -/

/-- **The reverse-proxy handler.** Select an upstream over the healthy pool and emit
the reactor's upstream-connect submission targeting it; emit nothing when no backend
is eligible. -/
def proxyHandle (pool : ProxyPool) (ctx : Proxy.Ctx) (_req : Request) :
    List RingSubmission :=
  match chooseUpstream pool ctx with
  | some b => [RingSubmission.connectUpstream (addrOf b)]
  | none   => []

/-- **The relay step.** Once the upstream tunnel is established (the reactor holds an
`fd`), forward request bytes upstream. This is the post-connect phase: it *requires* an
`fd`, which only a completed connect produces, so no relay can precede a connect. -/
def proxyRelay (fd : Nat) (data : Bytes) : List RingSubmission :=
  [RingSubmission.submitSendUpstream fd data]

/-- The hand-off: the reverse-proxy handler sits on the reactor's `dispatch`
submission. A `dispatch req` becomes the proxied handling of `req`; every other
submission is not the proxy's concern. -/
def onDispatch (pool : ProxyPool) (ctx : Proxy.Ctx) :
    RingSubmission → List RingSubmission
  | .dispatch req => proxyHandle pool ctx req
  | _             => []

/-- The upstream the reactor targets, recovered from a submission list: the first
`connectUpstream`'s address. This reads the reactor's own output back out, which is
what lets the seam theorem speak about "the upstream the reactor targets". -/
def targetedUpstream : List RingSubmission → Option Addr
  | []                                    => none
  | RingSubmission.connectUpstream a :: _ => some a
  | _ :: rest                             => targetedUpstream rest

/-- Is this submission an upstream relay (`submitSendUpstream`)? -/
def RingSubmission.isSendUpstream : RingSubmission → Bool
  | .submitSendUpstream _ _ => true
  | _                       => false

/-! ## The seam theorems -/

/-- The reactor's targeted upstream is exactly `addrOf` of the LB's verdict — the
handler forwards the selector's choice unchanged, never a hardcoded target. -/
theorem proxy_target_eq (pool : ProxyPool) (ctx : Proxy.Ctx) (req : Request) :
    targetedUpstream (proxyHandle pool ctx req)
      = (chooseUpstream pool ctx).map addrOf := by
  cases hc : chooseUpstream pool ctx with
  | none   => simp [proxyHandle, hc, targetedUpstream]
  | some b => simp [proxyHandle, hc, targetedUpstream]

/-- **`proxy_selects_healthy` — the anti-island seam.** When the REAL
`Proxy.selectChain` picks backend `b`, the reactor targets exactly `addrOf b`, and `b`
is a healthy, administratively-active member of the current pool sitting in the
best (lowest-numbered) nonempty tier. The membership/eligibility/best-tier facts are
`Proxy.selectChain_eligible` transported through the reactor's submission list — a
selector that returned an unhealthy or non-pool backend would break the second
conjunct, and a handler that ignored the selector would break the first. -/
theorem proxy_selects_healthy (pool : ProxyPool) (ctx : Proxy.Ctx) (req : Request)
    {b : Proxy.Backend} (h : chooseUpstream pool ctx = some b) :
    targetedUpstream (proxyHandle pool ctx req) = some (addrOf b)
      ∧ b ∈ pool.backends
      ∧ b.eligible = true
      ∧ Proxy.bestTier pool.backends = some b.tier := by
  refine ⟨?_, Proxy.selectChain_eligible h⟩
  have ht := proxy_target_eq pool ctx req
  rw [h] at ht
  simpa using ht

/-- The targeted upstream lies in the *current healthy set* `Proxy.eligibleOf` of the
pool — the reactor never dials a backend the health machine has taken down. -/
theorem proxy_target_in_healthy_set (pool : ProxyPool) (ctx : Proxy.Ctx)
    {b : Proxy.Backend} (h : chooseUpstream pool ctx = some b) :
    b ∈ Proxy.eligibleOf pool.backends := by
  have hs := Proxy.selectChain_eligible h
  exact Proxy.mem_eligibleOf.mpr ⟨hs.1, hs.2.1⟩

/-- **No upstream traffic before a backend is chosen.** With no eligible backend the
LB selects nothing and the handler emits the empty submission list — no
`connectUpstream`, no `submitSendUpstream`. -/
theorem proxy_no_upstream_without_choice (pool : ProxyPool) (ctx : Proxy.Ctx)
    (req : Request) (h : chooseUpstream pool ctx = none) :
    proxyHandle pool ctx req = [] := by
  simp [proxyHandle, h]

/-- Corollary: nothing is targeted when nothing is selected. -/
theorem proxy_no_target_without_choice (pool : ProxyPool) (ctx : Proxy.Ctx)
    (req : Request) (h : chooseUpstream pool ctx = none) :
    targetedUpstream (proxyHandle pool ctx req) = none := by
  rw [proxy_no_upstream_without_choice pool ctx req h]; rfl

/-- **Relay is a strictly later phase.** `proxyHandle` never emits a `submitSendUpstream`
— the reverse-proxy handler only ever asks to *connect*; relaying is gated behind the
connect-produced `fd` in `proxyRelay`. So there is no upstream *send* before a connect,
in every branch. -/
theorem proxyHandle_no_relay (pool : ProxyPool) (ctx : Proxy.Ctx) (req : Request) :
    (proxyHandle pool ctx req).filter RingSubmission.isSendUpstream = [] := by
  cases hc : chooseUpstream pool ctx with
  | none   => simp [proxyHandle, hc]
  | some b => simp [proxyHandle, hc, RingSubmission.isSendUpstream]

/-- **Liveness companion — no proxied request is stuck when the pool has capacity.**
If the chain contains least-connections and some pool backend is eligible, the LB (and
hence the handler) always chooses an upstream. (`Proxy.selectChain_total` over
`Proxy.select_leastConn_total`.) -/
theorem proxy_total_when_eligible (pool : ProxyPool) (ctx : Proxy.Ctx)
    {w : Proxy.Backend} (hpol : Proxy.Policy.leastConnections ∈ pool.policies)
    (hmem : w ∈ pool.backends) (helig : w.eligible = true) :
    (chooseUpstream pool ctx).isSome :=
  Proxy.selectChain_total hpol (Proxy.select_leastConn_total hmem helig)

/-- The proxy really sits on the reactor's `dispatch` submission: dispatching `req`
runs the handler on it. -/
theorem onDispatch_runs_handler (pool : ProxyPool) (ctx : Proxy.Ctx) (req : Request) :
    onDispatch pool ctx (.dispatch req) = proxyHandle pool ctx req := rfl

/-! ## A concrete instantiation (driven by real data)

A three-backend pool: backend 0 is **unhealthy**, backends 1 and 2 are healthy with
different in-flight counts. Least-connections over the health-filtered pool must pick
backend 2 (fewest conns among the healthy). A naive "first backend" stub would target
backend 0 — unhealthy — and thus fail `proxy_selects_healthy`. -/

/-- Backend 0: unhealthy (health machine took it down). Ineligible. -/
def demoB0 : Proxy.Backend := ⟨0, 1, 0, 0, false, .active⟩
/-- Backend 1: healthy, 5 in-flight connections. -/
def demoB1 : Proxy.Backend := ⟨1, 1, 5, 0, true, .active⟩
/-- Backend 2: healthy, 3 in-flight connections (the least-conn winner). -/
def demoB2 : Proxy.Backend := ⟨2, 1, 3, 0, true, .active⟩

/-- The demo pool: a least-connections chain over the three backends. -/
def demoPool : ProxyPool :=
  { policies := [.leastConnections], backends := [demoB0, demoB1, demoB2] }

/-- A trivial selection context (least-connections consults neither round nor key). -/
def demoCtx : Proxy.Ctx := ⟨0, 0, fun _ _ => 0⟩

/-- The real LB picks the healthy least-loaded backend (id 2), skipping the unhealthy
id 0 entirely. -/
theorem demo_chooses_b2 : chooseUpstream demoPool demoCtx = some demoB2 := by decide

/-- The naive "first backend" stub would target id 0… -/
example : demoPool.backends.head?.map addrOf = some (addrOf demoB0) := by decide

/-- …but id 0 is ineligible (unhealthy), so that stub violates the eligibility
conjunct of `proxy_selects_healthy`. -/
example : demoB0.eligible = false := by decide

/-- The real LB's choice is eligible — the seam holds where the stub fails. -/
example : ∃ b, chooseUpstream demoPool demoCtx = some b ∧ b.eligible = true :=
  ⟨demoB2, demo_chooses_b2, by decide⟩

/-- The seam theorem at the concrete pool: the reactor targets the healthy backend the
real LB selected. -/
theorem demoPool_selects_healthy (req : Request) :
    targetedUpstream (proxyHandle demoPool demoCtx req) = some (addrOf demoB2)
      ∧ demoB2 ∈ demoPool.backends
      ∧ demoB2.eligible = true
      ∧ Proxy.bestTier demoPool.backends = some demoB2.tier :=
  proxy_selects_healthy demoPool demoCtx req demo_chooses_b2

end Reactor.Proxy
