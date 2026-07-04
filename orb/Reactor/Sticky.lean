import Reactor.ProxyServe
import Reactor.Serve
import Reactor.Bridge
import Sticky.Routing
import Sticky.Membership

/-!
# Reactor.Sticky — session affinity on the reverse-proxy reactor path

`Reactor.ProxyServe` wired the stateless load balancer onto the reactor's
`dispatch` seam: a proxy-routed request dials the backend `Proxy.selectChain`
picks. That choice is per-request — nothing pins a *session* to a backend. The
real `Sticky` library owns that layer: a stickiness table (`Sticky.Table`) pins
a session key to a backend id, `Sticky.route` honours a live pin and re-pins a
dead one from the rendezvous winner, and the Routing/Membership theorem files
prove stability, deterministic failover, and minimal disruption.

This file composes that library with the reactor's upstream choice, on the same
running path `ProxyServe` uses:

  * `upstreams` — the eligible (healthy ∧ active) list of a `ProxyPool`, via the
    real `Proxy.eligibleOf`. This is the eligible set `Sticky.route` is
    specified over ("passed in, snapshotted, exactly as the selection call sees
    it" — `Sticky.Basic`).
  * `stickyChoose` — the selection call: literally `Sticky.route` over the
    pool's eligible list. Nothing re-implements pin/lookup/rendezvous.
  * `stickyHandle` — turn the routed backend into the reactor's own
    `connectUpstream` submission (and thread the updated table out).
  * `serveStickyOn` — pin the sticky handler onto the reactor's `dispatch`
    submission, the same seam `Reactor.Serve` answers with a Response and
    `Reactor.ProxyServe` answers with LB submissions.
  * `serveSticky` — the running path: one recv completion through the PROVEN
    `Reactor.step` (`ProxyServe.reactorSubs`), then `serveStickyOn` its output.

**Seam theorem — `sticky_affinity_seam`.** Two requests carrying the same
session key, each flowing through the reactor's `dispatch`, target the *same*
backend: the first `serveSticky` emits `connectUpstream (addrOf b)` for the
backend `b` the real `Sticky.route` chose AND writes the pin `t' k = some b.id`
the real library computed; re-serving with the threaded table `t'` emits the
identical submission with the table untouched (`Sticky.sticky_stability`
composed through the reactor). The chosen backend is a healthy, active member of
the pool. A handler that re-picked per request (ignoring the table) would fail
the second-serve conjunct; one that pinned without consulting `Sticky.route`
would fail the pin conjunct.

**Failover — `sticky_failover_seam`.** Remove a backend `d` from the pool
(`removePoolBackend`, the real `Sticky.removeBackend` transition applied to the
pool). Every dispatched request whose session's chosen backend was NOT `d`
still targets exactly that backend (`Sticky.sticky_minimal_disruption` composed
through the reactor): failover disturbs only the departed backend's sessions.

The demo instantiates all of it over the real `Reactor.Proxy.demoPool`, whose
eligible list is `[demoB1, demoB2]` (backend 0 is unhealthy). Key 7 pins to
backend 2 and stays there across requests; removing the *unrelated* backend 1
leaves the pinned session undisturbed.

**The deployed path.** `Arena.Orb.main` runs `Reactor.Deploy.serveFull` /
`deployStep` over `deployConfig` — not `serve` over `demoConfig`. The submissions
the deployed reactor produces are `Reactor.Deploy.deploySubs`, and
`ProxyServe.reactorSubs Reactor.Deploy.deployConfig` IS `deploySubs`
definitionally. So running the sticky routing at `deployConfig`
(`serveSticky Reactor.Deploy.deployConfig`) routes exactly the deployed reactor's
own `dispatch`: `sticky_affinity_deployed` / `sticky_failover_deployed` state the
affinity and failover seams over `Reactor.Deploy.deploySubs`, the config `main`
actually serves. (The demo seam over `Config.demoConfig` still holds and produces
the same submissions — `Reactor.Bridge.deploySubs_eq_reactorSubs`.)
-/

namespace Reactor.Sticky

open Proto (Bytes Request)
open Reactor.Proxy (ProxyPool addrOf)

/-! ## The eligible upstream list of a pool -/

/-- The eligible upstream list `Sticky.route` selects over: the REAL
`Proxy.eligibleOf` (healthy ∧ active) subset of the pool, snapshotted exactly as
the selection call sees it. -/
def upstreams (pool : ProxyPool) : List Proxy.Backend :=
  Proxy.eligibleOf pool.backends

/-- Distinct pool ids survive the eligibility filter. -/
theorem upstreams_idsNodup {pool : ProxyPool}
    (hnd : Proxy.idsNodup pool.backends) : Proxy.idsNodup (upstreams pool) := by
  have hsub : List.Sublist ((upstreams pool).map Proxy.Backend.id)
      (pool.backends.map Proxy.Backend.id) :=
    (List.filter_sublist pool.backends).map Proxy.Backend.id
  exact hsub.nodup hnd

/-- The pool after backend `d` departs: the REAL `Sticky.removeBackend`
membership transition applied to the pool's backend list. -/
def removePoolBackend (d : Proxy.Backend) (pool : ProxyPool) : ProxyPool :=
  { pool with backends := Sticky.removeBackend d pool.backends }

/-! ## The selection call and the reactor submissions -/

/-- **The selection call.** Delegate to the REAL `Sticky.route`: honour a live
pin, re-pin a dead one from the rendezvous winner of the current eligible list.
Returns the updated table and the chosen backend. -/
def stickyChoose (hash : Nat → Nat → Nat) (pool : ProxyPool) (t : Sticky.Table)
    (k : Nat) : Sticky.Table × Option Proxy.Backend :=
  Sticky.route hash (upstreams pool) t k

/-- **The session-affine proxy handler.** Route the session key through the real
stickiness table and emit the reactor's `connectUpstream` submission to the
chosen backend (nothing when the eligible set is empty), threading the updated
table out. -/
def stickyHandle (hash : Nat → Nat → Nat) (pool : ProxyPool) (t : Sticky.Table)
    (k : Nat) (_req : Request) : Sticky.Table × List RingSubmission :=
  match stickyChoose hash pool t k with
  | (t', some b) => (t', [RingSubmission.connectUpstream (addrOf b)])
  | (t', none)   => (t', [])

/-- Pin the sticky handler onto the reactor's own `dispatch` submission: scan
the running reactor's submission list for its `dispatch`, extract the session
key with the caller's adapter `keyOf`, and route it through the table. The same
seam `Reactor.Serve` answers with a Response and `Reactor.ProxyServe` answers
with LB submissions. -/
def serveStickyOn (hash : Nat → Nat → Nat) (pool : ProxyPool) (t : Sticky.Table)
    (keyOf : Request → Nat) :
    List RingSubmission → Sticky.Table × List RingSubmission
  | [] => (t, [])
  | RingSubmission.dispatch req :: _ => stickyHandle hash pool t (keyOf req) req
  | _ :: rest => serveStickyOn hash pool t keyOf rest

/-- **The session-affine reverse proxy on the running reactor path.** One recv
completion through the PROVEN `Reactor.step` (`ProxyServe.reactorSubs`), then
route its `dispatch` through the real stickiness table. -/
def serveSticky (cfg : Proto.Config) (hash : Nat → Nat → Nat) (pool : ProxyPool)
    (t : Sticky.Table) (keyOf : Request → Nat) (input : Bytes) :
    Sticky.Table × List RingSubmission :=
  serveStickyOn hash pool t keyOf (ProxyServe.reactorSubs cfg input)

/-- `ProxyServe.reactorSubs` at `Config.demoConfig` IS `Reactor.reactorSubs`, the
test-view submission producer — same `Reactor.step`, same initial state, same
event. (`main` runs the deployed producer `Reactor.Deploy.deploySubs` over
`deployConfig`; the two producers agree, `Reactor.Bridge.deploySubs_eq_reactorSubs`.) -/
theorem reactorSubs_demoConfig (input : Bytes) :
    ProxyServe.reactorSubs Reactor.Config.demoConfig input
      = Reactor.reactorSubs input := rfl

/-! ## Composition lemmas -/

/-- `serveStickyOn` on a submission list headed by `dispatch req` runs the
sticky handler on that request's session key — the sticky proxy sits exactly on
the reactor's `dispatch` output. -/
theorem serveStickyOn_dispatch (hash : Nat → Nat → Nat) (pool : ProxyPool)
    (t : Sticky.Table) (keyOf : Request → Nat) (req : Request)
    (rest : List RingSubmission) :
    serveStickyOn hash pool t keyOf (RingSubmission.dispatch req :: rest)
      = stickyHandle hash pool t (keyOf req) req := rfl

/-- When the real `Sticky.route` returns `(t', some b)`, the handler emits
exactly the `connectUpstream` to `b` and threads out exactly `t'` — the
reactor forwards the library's verdict unchanged. -/
theorem stickyHandle_of_route {hash : Nat → Nat → Nat} {pool : ProxyPool}
    {t t' : Sticky.Table} {k : Nat} {b : Proxy.Backend} (req : Request)
    (hroute : Sticky.route hash (upstreams pool) t k = (t', some b)) :
    stickyHandle hash pool t k req
      = (t', [RingSubmission.connectUpstream (addrOf b)]) := by
  simp only [stickyHandle, stickyChoose, hroute]

/-- The handler's emitted submissions are decided by the real `Sticky.chosen`
(the assignment the request observes): a chosen backend is dialed. -/
theorem stickyHandle_targets {hash : Nat → Nat → Nat} {pool : ProxyPool}
    {t : Sticky.Table} {k : Nat} {b : Proxy.Backend} (req : Request)
    (hch : Sticky.chosen hash (upstreams pool) t k = some b) :
    (stickyHandle hash pool t k req).2
      = [RingSubmission.connectUpstream (addrOf b)] := by
  have hsnd : (Sticky.route hash (upstreams pool) t k).2 = some b := by
    rw [Sticky.route_snd_eq_chosen]; exact hch
  cases hr : Sticky.route hash (upstreams pool) t k with
  | mk t'' ob =>
    have hob : ob = some b := by rw [hr] at hsnd; exact hsnd
    subst hob
    simp only [stickyHandle, stickyChoose, hr]

/-! ## Route inversion: what a successful route pins -/

/-- Reduction: a live pin is honoured with the table untouched. -/
theorem route_of_pin {hash : Nat → Nat → Nat} {bs : List Proxy.Backend}
    {t : Sticky.Table} {k : Nat} {b : Proxy.Backend}
    (hp : Sticky.pinned bs t k = some b) :
    Sticky.route hash bs t k = (t, some b) := by
  simp only [Sticky.route, hp]

/-- Reduction: no live pin and a rendezvous winner ⇒ re-pin to the winner. -/
theorem route_of_no_pin {hash : Nat → Nat → Nat} {bs : List Proxy.Backend}
    {t : Sticky.Table} {k : Nat} {b : Proxy.Backend}
    (hp : Sticky.pinned bs t k = none)
    (hr : Proxy.rendezvous hash k bs = some b) :
    Sticky.route hash bs t k = (Sticky.update t k b.id, some b) := by
  simp only [Sticky.route, hp, hr]

/-- Reduction: no live pin and no winner (empty eligible set) ⇒ nothing. -/
theorem route_of_no_pin_none {hash : Nat → Nat → Nat} {bs : List Proxy.Backend}
    {t : Sticky.Table} {k : Nat}
    (hp : Sticky.pinned bs t k = none)
    (hr : Proxy.rendezvous hash k bs = none) :
    Sticky.route hash bs t k = (t, none) := by
  simp only [Sticky.route, hp, hr]

/-- A live pin names the pinned backend's id in the table. -/
theorem pinned_pin {bs : List Proxy.Backend} {t : Sticky.Table} {k : Nat}
    {pb : Proxy.Backend} (hp : Sticky.pinned bs t k = some pb) :
    t k = some pb.id := by
  cases htk : t k with
  | none =>
    rw [Sticky.pinned_none_of_unpinned htk] at hp
    cases hp
  | some bid =>
    unfold Sticky.pinned at hp
    rw [htk] at hp
    have hl : Sticky.lookupId bid bs = some pb := hp
    rw [Sticky.lookupId_id hl]

/-- **What a successful route pins.** Whenever `Sticky.route` returns
`(t', some b)`, the out-table records the session's pin: `t' k = some b.id` —
whether the pin was already live (table untouched) or freshly written from the
rendezvous winner. -/
theorem route_pin {hash : Nat → Nat → Nat} {bs : List Proxy.Backend}
    {t t' : Sticky.Table} {k : Nat} {b : Proxy.Backend}
    (h : Sticky.route hash bs t k = (t', some b)) :
    t' k = some b.id := by
  cases hp : Sticky.pinned bs t k with
  | some pb =>
    rw [route_of_pin hp] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, hpb⟩ := h
    cases Option.some.inj hpb
    exact pinned_pin hp
  | none =>
    cases hr : Proxy.rendezvous hash k bs with
    | none =>
      rw [route_of_no_pin_none hp hr] at h
      simp only [Prod.mk.injEq] at h
      exact Option.noConfusion h.2
    | some w =>
      rw [route_of_no_pin hp hr] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨ht, hw⟩ := h
      cases Option.some.inj hw
      rw [← ht]
      apply Sticky.update_self

/-- **Re-routing the pinned session is a fixed point.** After a successful route
`(t', some b)`, routing the same key over the same eligible set with the
threaded table reproduces `(t', some b)` exactly — the real library's
`sticky_stability`, packaged for the reactor composition. -/
theorem route_repeat {hash : Nat → Nat → Nat} {bs : List Proxy.Backend}
    {t t' : Sticky.Table} {k : Nat} {b : Proxy.Backend}
    (hnd : Proxy.idsNodup bs)
    (h : Sticky.route hash bs t k = (t', some b)) :
    Sticky.route hash bs t' k = (t', some b) := by
  have hpin : t' k = some b.id := route_pin h
  have hch : Sticky.chosen hash bs t k = some b := by
    rw [← Sticky.route_snd_eq_chosen, h]
  exact Sticky.sticky_stability hnd hpin (Sticky.chosen_mem hch) rfl

/-! ## The seam theorems -/

/-- **`sticky_affinity_seam` — session affinity on the running reactor path.**
Two inputs whose recv completions the PROVEN `Reactor.step` turns into
`dispatch req1` / `dispatch req2`, carrying the *same session key*, target the
*same upstream backend*, and that backend is the one the REAL `Sticky.route`
pins:

  * the first serve emits exactly `connectUpstream (addrOf b)` and threads out
    exactly the table `t'` the library computed;
  * `t' k = some b.id` — the pin recorded is the served backend's id
    (`route_pin`, real bookkeeping, not a side-channel);
  * the second serve, with the threaded table, emits the *identical* submission
    and leaves the table untouched (`Sticky.sticky_stability` composed through
    the reactor's dispatch seam);
  * `b` is a healthy, administratively active member of the pool
    (`Sticky.chosen_mem` + `Proxy.mem_eligibleOf`).

A handler that re-selected per request (ignoring the table) would break the
second-serve conjunct whenever the stateless winner differs; one that pinned
anything but the routed backend would break the pin conjunct. -/
theorem sticky_affinity_seam (cfg : Proto.Config) (hash : Nat → Nat → Nat)
    (pool : ProxyPool) (t t' : Sticky.Table) (keyOf : Request → Nat)
    (in1 in2 : Bytes) (req1 req2 : Request) (rest1 rest2 : List RingSubmission)
    {b : Proxy.Backend}
    (hnd : Proxy.idsNodup pool.backends)
    (hsub1 : ProxyServe.reactorSubs cfg in1 = RingSubmission.dispatch req1 :: rest1)
    (hsub2 : ProxyServe.reactorSubs cfg in2 = RingSubmission.dispatch req2 :: rest2)
    (hkey : keyOf req2 = keyOf req1)
    (hroute : Sticky.route hash (upstreams pool) t (keyOf req1) = (t', some b)) :
    serveSticky cfg hash pool t keyOf in1
        = (t', [RingSubmission.connectUpstream (addrOf b)])
      ∧ t' (keyOf req1) = some b.id
      ∧ serveSticky cfg hash pool t' keyOf in2
        = (t', [RingSubmission.connectUpstream (addrOf b)])
      ∧ b ∈ pool.backends
      ∧ b.eligible = true := by
  have hndU : Proxy.idsNodup (upstreams pool) := upstreams_idsNodup hnd
  have hfirst : serveSticky cfg hash pool t keyOf in1
      = (t', [RingSubmission.connectUpstream (addrOf b)]) := by
    unfold serveSticky
    rw [hsub1, serveStickyOn_dispatch]
    exact stickyHandle_of_route req1 hroute
  have hsecond : serveSticky cfg hash pool t' keyOf in2
      = (t', [RingSubmission.connectUpstream (addrOf b)]) := by
    unfold serveSticky
    rw [hsub2, serveStickyOn_dispatch, hkey]
    exact stickyHandle_of_route req2 (route_repeat hndU hroute)
  have hch : Sticky.chosen hash (upstreams pool) t (keyOf req1) = some b := by
    rw [← Sticky.route_snd_eq_chosen, hroute]
  have hmemE : b ∈ Proxy.eligibleOf pool.backends := Sticky.chosen_mem hch
  have hmem := Proxy.mem_eligibleOf.mp hmemE
  exact ⟨hfirst, route_pin hroute, hsecond, hmem.1, hmem.2⟩

/-- **`sticky_failover_seam` — minimal-disruption failover on the running
reactor path.** Backend `d` departs the pool (the real `Sticky.removeBackend`
membership transition). For any dispatched request whose session's observed
assignment (`Sticky.chosen`, live pin or rendezvous winner) was a backend `b`
other than `d`, the running path over the shrunken pool still emits exactly
`connectUpstream (addrOf b)` — the session is undisturbed. This is
`Sticky.sticky_minimal_disruption` composed through the reactor's dispatch
seam: only the departed backend's sessions can move. -/
theorem sticky_failover_seam (cfg : Proto.Config) (hash : Nat → Nat → Nat)
    (pool : ProxyPool) (t : Sticky.Table) (keyOf : Request → Nat)
    (input : Bytes) (req : Request) (rest : List RingSubmission)
    {b d : Proxy.Backend}
    (hnd : Proxy.idsNodup pool.backends)
    (hsub : ProxyServe.reactorSubs cfg input = RingSubmission.dispatch req :: rest)
    (hchosen : Sticky.chosen hash (upstreams pool) t (keyOf req) = some b)
    (hne : b.id ≠ d.id) :
    (serveSticky cfg hash (removePoolBackend d pool) t keyOf input).2
      = [RingSubmission.connectUpstream (addrOf b)] := by
  have hndR : Proxy.idsNodup (upstreams (removePoolBackend d pool)) :=
    upstreams_idsNodup (pool := removePoolBackend d pool)
      (Sticky.removeBackend_nodup hnd)
  have hsubset : ∀ c ∈ upstreams (removePoolBackend d pool), c ∈ upstreams pool := by
    intro c hc
    have hc' := Proxy.mem_eligibleOf.mp hc
    have hcb := Sticky.mem_removeBackend.mp hc'.1
    exact Proxy.mem_eligibleOf.mpr ⟨hcb.1, hc'.2⟩
  have hbe := Proxy.mem_eligibleOf.mp (Sticky.chosen_mem hchosen)
  have hbR : b ∈ upstreams (removePoolBackend d pool) :=
    Proxy.mem_eligibleOf.mpr ⟨Sticky.mem_removeBackend.mpr ⟨hbe.1, hne⟩, hbe.2⟩
  have hch' : Sticky.chosen hash (upstreams (removePoolBackend d pool)) t
      (keyOf req) = some b :=
    Sticky.sticky_minimal_disruption (upstreams_idsNodup hnd) hndR hsubset
      hchosen hbR
  unfold serveSticky
  rw [hsub, serveStickyOn_dispatch]
  exact stickyHandle_targets req hch'

/-! ## The demo: the real demo pool

`Config.demoConfig` is the config the test view `serve` runs; `Arena.Orb.main`
runs `Reactor.Deploy.serveFull` over `deployConfig`, whose reactor produces the
same submissions (`Reactor.Bridge.deploySubs_eq_reactorSubs`). The deployed-path
forms of the demo seams below are `sticky_affinity_deployed` /
`sticky_failover_deployed`. `Reactor.Proxy.demoPool` is the real three-backend
pool with backend 0 unhealthy.
Its eligible list is `[demoB1, demoB2]`; a fresh session (key 7) rendezvous-pins
to backend 2, stays there across requests, and survives the removal of the
unrelated backend 1. The session-key adapter is a parameter of the general
theorems; the demo fixes one session. -/

/-- A concrete (arbitrary) affinity hash: every theorem above holds for EVERY
hash, so the demo may fix the simplest one. -/
def demoHash : Nat → Nat → Nat := fun _ _ => 0

/-- The demo session-key adapter: one fixed session (key 7). -/
def demoKeyOf : Request → Nat := fun _ => 7

/-- The empty stickiness table: no session pinned yet. -/
def demoTable : Sticky.Table := fun _ => none

/-- The table after the first demo request: key 7 freshly pinned. -/
def demoTable' : Sticky.Table :=
  (Sticky.route demoHash (upstreams Reactor.Proxy.demoPool) demoTable 7).1

theorem demoPool_idsNodup : Proxy.idsNodup Reactor.Proxy.demoPool.backends := by
  show (Reactor.Proxy.demoPool.backends.map Proxy.Backend.id).Nodup
  decide

/-- The demo pool's eligible list: the unhealthy backend 0 is filtered out by
the real `Proxy.eligibleOf`. -/
theorem demo_upstreams :
    upstreams Reactor.Proxy.demoPool
      = [Reactor.Proxy.demoB1, Reactor.Proxy.demoB2] := by decide

/-- The real `Sticky.route` on the fresh table chooses backend 2 for key 7 (the
rendezvous tie-break: equal scores, higher id wins). -/
theorem demo_route_snd :
    (Sticky.route demoHash (upstreams Reactor.Proxy.demoPool) demoTable 7).2
      = some Reactor.Proxy.demoB2 := by decide

/-- …and writes the pin 7 ↦ 2 into the table. -/
theorem demo_route_pin : demoTable' 7 = some 2 := by decide

/-- The first demo route, as a pair. -/
theorem demo_route :
    Sticky.route demoHash (upstreams Reactor.Proxy.demoPool) demoTable 7
      = (demoTable', some Reactor.Proxy.demoB2) := by
  show Sticky.route demoHash (upstreams Reactor.Proxy.demoPool) demoTable 7
      = ((Sticky.route demoHash (upstreams Reactor.Proxy.demoPool) demoTable 7).1,
         some Reactor.Proxy.demoB2)
  rw [← demo_route_snd]

/-- **The affinity seam at the demo config (test view).** Any two inputs the
test-view reactor (`Reactor.reactorSubs` = `Reactor.step Config.demoConfig`)
turns into dispatches of the demo session both dial backend 2: the first serve
pins it (`demoTable'`), the second serve rides the pin, table untouched. The
deployed-path form (over `Reactor.Deploy.deploySubs`, the config `main` runs) is
`sticky_affinity_deployed`. -/
theorem demo_sticky_affinity (in1 in2 : Bytes) (req1 req2 : Request)
    (rest1 rest2 : List RingSubmission)
    (hsub1 : Reactor.reactorSubs in1 = RingSubmission.dispatch req1 :: rest1)
    (hsub2 : Reactor.reactorSubs in2 = RingSubmission.dispatch req2 :: rest2) :
    serveSticky Reactor.Config.demoConfig demoHash Reactor.Proxy.demoPool
        demoTable demoKeyOf in1
      = (demoTable',
         [RingSubmission.connectUpstream (addrOf Reactor.Proxy.demoB2)])
    ∧ demoTable' 7 = some Reactor.Proxy.demoB2.id
    ∧ serveSticky Reactor.Config.demoConfig demoHash Reactor.Proxy.demoPool
        demoTable' demoKeyOf in2
      = (demoTable',
         [RingSubmission.connectUpstream (addrOf Reactor.Proxy.demoB2)]) := by
  rw [← reactorSubs_demoConfig] at hsub1 hsub2
  have h := sticky_affinity_seam Reactor.Config.demoConfig demoHash
    Reactor.Proxy.demoPool demoTable demoTable' demoKeyOf in1 in2 req1 req2
    rest1 rest2 demoPool_idsNodup hsub1 hsub2 rfl demo_route
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- **Failover isolation at the deployed config.** Remove the *unrelated*
backend 1 from the demo pool: the pinned session (key 7 ↦ backend 2) is
undisturbed — the running path still dials backend 2. -/
theorem demo_failover_isolation (input : Bytes) (req : Request)
    (rest : List RingSubmission)
    (hsub : Reactor.reactorSubs input = RingSubmission.dispatch req :: rest) :
    (serveSticky Reactor.Config.demoConfig demoHash
        (removePoolBackend Reactor.Proxy.demoB1 Reactor.Proxy.demoPool)
        demoTable' demoKeyOf input).2
      = [RingSubmission.connectUpstream (addrOf Reactor.Proxy.demoB2)] := by
  rw [← reactorSubs_demoConfig] at hsub
  have hch : Sticky.chosen demoHash (upstreams Reactor.Proxy.demoPool)
      demoTable' 7 = some Reactor.Proxy.demoB2 := by decide
  have hne : Reactor.Proxy.demoB2.id ≠ Reactor.Proxy.demoB1.id := by decide
  exact sticky_failover_seam Reactor.Config.demoConfig demoHash
    Reactor.Proxy.demoPool demoTable' demoKeyOf input req rest
    demoPool_idsNodup hsub hch hne

/-! ## The deployed path — the affinity seam over `Reactor.Deploy.deploySubs`

`Arena.Orb.main` runs `Reactor.Deploy.serveFull` / `deployStep` over
`deployConfig`; the submissions its reactor produces are
`Reactor.Deploy.deploySubs`. Running the sticky routing at that config
(`serveSticky Reactor.Deploy.deployConfig`) routes precisely those submissions —
`ProxyServe.reactorSubs Reactor.Deploy.deployConfig` is `deploySubs`
definitionally (`deploy_reactorSubs`). The two theorems below are the demo
affinity/failover seams restated on the deployed reactor's own dispatch. -/

/-- `serveSticky` at the deployed config routes the deployed reactor's own
submissions: `ProxyServe.reactorSubs deployConfig` is `Reactor.Deploy.deploySubs`. -/
theorem deploy_reactorSubs (input : Bytes) :
    ProxyServe.reactorSubs Reactor.Deploy.deployConfig input
      = Reactor.Deploy.deploySubs input := rfl

/-- **`sticky_affinity_deployed` — session affinity on the deployed path.** Two
inputs the DEPLOYED reactor (`Reactor.Deploy.deploySubs`, the producer behind
`main`'s `serveFull`) turns into dispatches of the demo session both dial backend
2: the first serve pins it (`demoTable'`), the second rides the pin, table
untouched. `sticky_affinity_seam` at `deployConfig`, triggered on
`Reactor.Deploy.deploySubs`. -/
theorem sticky_affinity_deployed (in1 in2 : Bytes) (req1 req2 : Request)
    (rest1 rest2 : List RingSubmission)
    (hsub1 : Reactor.Deploy.deploySubs in1 = RingSubmission.dispatch req1 :: rest1)
    (hsub2 : Reactor.Deploy.deploySubs in2 = RingSubmission.dispatch req2 :: rest2) :
    serveSticky Reactor.Deploy.deployConfig demoHash Reactor.Proxy.demoPool
        demoTable demoKeyOf in1
      = (demoTable',
         [RingSubmission.connectUpstream (addrOf Reactor.Proxy.demoB2)])
    ∧ demoTable' 7 = some Reactor.Proxy.demoB2.id
    ∧ serveSticky Reactor.Deploy.deployConfig demoHash Reactor.Proxy.demoPool
        demoTable' demoKeyOf in2
      = (demoTable',
         [RingSubmission.connectUpstream (addrOf Reactor.Proxy.demoB2)]) := by
  rw [← deploy_reactorSubs] at hsub1 hsub2
  have h := sticky_affinity_seam Reactor.Deploy.deployConfig demoHash
    Reactor.Proxy.demoPool demoTable demoTable' demoKeyOf in1 in2 req1 req2
    rest1 rest2 demoPool_idsNodup hsub1 hsub2 rfl demo_route
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- **`sticky_failover_deployed` — minimal-disruption failover on the deployed
path.** Removing the *unrelated* backend 1 from the demo pool leaves the pinned
session (key 7 → backend 2) undisturbed: the DEPLOYED reactor's dispatch still
dials backend 2. `sticky_failover_seam` at `deployConfig`, triggered on
`Reactor.Deploy.deploySubs`. -/
theorem sticky_failover_deployed (input : Bytes) (req : Request)
    (rest : List RingSubmission)
    (hsub : Reactor.Deploy.deploySubs input = RingSubmission.dispatch req :: rest) :
    (serveSticky Reactor.Deploy.deployConfig demoHash
        (removePoolBackend Reactor.Proxy.demoB1 Reactor.Proxy.demoPool)
        demoTable' demoKeyOf input).2
      = [RingSubmission.connectUpstream (addrOf Reactor.Proxy.demoB2)] := by
  rw [← deploy_reactorSubs] at hsub
  have hch : Sticky.chosen demoHash (upstreams Reactor.Proxy.demoPool)
      demoTable' 7 = some Reactor.Proxy.demoB2 := by decide
  have hne : Reactor.Proxy.demoB2.id ≠ Reactor.Proxy.demoB1.id := by decide
  exact sticky_failover_seam Reactor.Deploy.deployConfig demoHash
    Reactor.Proxy.demoPool demoTable' demoKeyOf input req rest
    demoPool_idsNodup hsub hch hne

end Reactor.Sticky
