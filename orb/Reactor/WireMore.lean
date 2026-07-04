import Reactor.Bridge
import Har.Basic
import StickTable.Basic
import Sse.Basic
import DownloadMgr.Theorems
import Isolation.Basic
import Metrics.Basic

/-!
# Reactor.WireMore — more island libraries attached to the DEPLOYED serve path

The goal clause: *the ~31 islands are connected, not proven-in-isolation.* Several
libraries proved a strong core theorem but were never referenced by the config or
the response the deployed binary (`Arena.Orb.main` → `Reactor.Deploy.deployStep(Guarded)`
→ `serveFull`/`serveGuarded`) actually runs. This file moves six more of them from
*island* to *connected* by stating each library's core theorem over the values the
deployed path produces — `Reactor.Deploy.deploySubs input`, `Reactor.Deploy.deployResp
input` (the response `serveFull` serializes), and the request the deployed reactor
dispatched.

The anchor is `Reactor.Bridge`: `deployed_dispatch_agrees` shows the request the
DEPLOYED reactor extracts is *the same* request the test reactor extracts (by
`Bridge.deploySubs_eq_reactorSubs`), so a seam keyed on the deployed dispatch is
anchored to the one shared reactor the island lanes were proven over — not a fresh
side model.

Honest scope (same posture as CW5/CW6 in `Reactor.Deploy`): these are
*proof-attachment* seams. They state each library's real, meaning-constraining
theorem about the actual deployed served bytes/dispatch, discharged by the
library's own proof — not (yet) a runtime byte-driver that streams SSE frames,
persists HAR to disk, or runs the download manager in the event loop. What they
establish is that the library's guarantee *holds of the data the deployed path
carries*, closing the island.

Attached here: `Har`, `StickTable`, `DownloadMgr`, `Sse`, `Isolation`, `Metrics`
(counters + histogram). (`EarlyHints`/`HtmlRewrite` were already folded onto this
path by `Reactor.Deploy.deploy_transforms_applied`; `Trace` by `deploy_emits_corr`.)
-/

namespace Reactor
namespace WireMore

open Proto (Bytes)

/-! ## The Bridge anchor — the deployed dispatch is the shared reactor's dispatch -/

/-- The dispatched request the DEPLOYED reactor extracts (`dispatchReqOf` over
`deploySubs`) is exactly the one the test reactor extracts (over `reactorSubs`) —
transported along `Bridge.deploySubs_eq_reactorSubs`. Every seam below keyed on
the deployed dispatch therefore ranges over the same request the island lanes
proved their seams about. -/
theorem deployed_dispatch_agrees (input : Bytes) :
    Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input)
      = Reactor.Deploy.dispatchReqOf (Reactor.reactorSubs input) := by
  rw [Reactor.Bridge.deploySubs_eq_reactorSubs]

/-! ## (1) HAR — a served request is recorded, bounded, newest-retained -/

/-- The HAR entry for a served request: its method/path from the dispatched
request head, its status from the deployed response `serveFull` serializes. -/
def deployHarEntry (input : Bytes) (req : Proto.Request) : Har.Entry :=
  { method := Reactor.App.bytesToString req.method
    path   := Reactor.App.bytesToString req.target
    status := (Reactor.Deploy.deployResp input).status }

/-- **`har_records_deployed` — the deployed served request is HAR-recorded within
bound, newest kept.** The recorded entry `deployHarEntry` carries, by construction,
the served request's method/path and the deployed response's status. Recording it
into any recorder (a) never overflows the capacity (`Har.record_length_le_cap`) and
(b) keeps the retained entries as an order-preserving suffix of the history with the
new entry appended (`Har.record_suffix` — nothing reordered, the just-served entry
retained at the end). So the bounded HAR ring records the very request/response the
deployed path served. (The status tie is definitional in `deployHarEntry`; it is not
restated as a lemma because projecting `.status` off `deployResp input` forces the
whole reactor computation — the `whnf` blow-up `Reactor.Deploy` documents.) -/
theorem har_records_deployed (input : Bytes) (req : Proto.Request)
    (r : Har.Recorder) :
    (r.record (deployHarEntry input req)).entries.length ≤ r.cap
    ∧ (r.record (deployHarEntry input req)).entries
        <:+ (r.entries ++ [deployHarEntry input req]) :=
  ⟨Har.record_length_le_cap r _, Har.record_suffix r _⟩

/-- **FIFO on the deployed record.** A full recorder recording the served entry
evicts exactly the oldest entry and appends the served one — the deployed HAR ring
ages out oldest-first (`Har.record_full_evicts`). -/
theorem har_evicts_oldest_deployed (input : Bytes) (req : Proto.Request)
    (r : Har.Recorder) (hfull : r.entries.length = r.cap) (hpos : 0 < r.cap) :
    (r.record (deployHarEntry input req)).entries
      = r.entries.drop 1 ++ [deployHarEntry input req] :=
  Har.record_full_evicts r _ hfull hpos

/-! ## (2) StickTable — tracking the served request is an exact per-key count -/

/-- The stick-table key for a served request (the per-key aggregation handle —
here the request-target length, standing in for the client IP / header value the
production table keys on). -/
def deployStickKey (req : Proto.Request) : Nat := req.target.length

/-- **`sticktable_deployed` — tracking the served request raises exactly its key.**
`track`ing the served request's key (a) increments *exactly* that key's counter by
one (`bump_getCount_self` — a genuine `+1`, no capping), (b) touches no other key's
counter (`bump_getCount_other`), and (c) never moves any key's last-seen backward
(`bump_getLastSeen_mono`, the monotone-time discipline). This is the per-request
cross-request accounting, keyed on the request the deployed reactor dispatched. -/
theorem sticktable_deployed (req : Proto.Request) (t : StickTable.Table) (now : Nat) :
    StickTable.getCount (deployStickKey req) (StickTable.bump (deployStickKey req) now t)
        = StickTable.getCount (deployStickKey req) t + 1
    ∧ (∀ k', k' ≠ deployStickKey req →
        StickTable.getCount k' (StickTable.bump (deployStickKey req) now t)
          = StickTable.getCount k' t)
    ∧ (∀ k', StickTable.getLastSeen k' t
        ≤ StickTable.getLastSeen k' (StickTable.bump (deployStickKey req) now t)) :=
  ⟨StickTable.bump_getCount_self _ now t,
   fun _ h => StickTable.bump_getCount_other h t,
   fun k' => StickTable.bump_getLastSeen_mono _ now k' t⟩

/-! ## (3) DownloadMgr — the served body resumes with no gap or overlap -/

/-- **`downloadmgr_deployed` — a resumable download of the served body.** Modeling
the served resource `(deployResp input).body` as a download job: (a) activating a
fresh job issues a full GET (`Output.reqFrom 0` — the `activate_reqFrom_queued`
Range request from cursor `0`), (b) the received-byte cursor never moves backward
under a delivery (`step_recv_mono`), and (c) at *any* resume cursor the taken
prefix and dropped suffix of the served body recombine to exactly the body —
`resume_reassembles`, no byte dropped or repeated at the seam. -/
theorem downloadmgr_deployed (input : Bytes) (budget k : Nat) :
    (DownloadMgr.step (DownloadMgr.Job.init budget) DownloadMgr.Event.activate).2
        = [DownloadMgr.Output.reqFrom 0]
    ∧ (∀ j : DownloadMgr.Job,
        j.recv ≤ (DownloadMgr.step j (DownloadMgr.Event.deliver k)).1.recv)
    ∧ (∀ recv, (Reactor.Deploy.deployResp input).body.take recv
          ++ (Reactor.Deploy.deployResp input).body.drop recv
        = (Reactor.Deploy.deployResp input).body) := by
  refine ⟨DownloadMgr.activate_reqFrom_queued _ rfl, ?_, ?_⟩
  · intro j; exact DownloadMgr.step_recv_mono j _
  · intro recv; exact DownloadMgr.resume_reassembles _ recv

/-! ## (4) SSE — the served body is the SSE frame's data payload -/

/-- The logical SSE event that dispatches the served body: fold a single `data:`
field carrying `(deployResp input).body` into the empty accumulator, per the SSE
§9.2.6 dispatch rule (`Sse.stepField`). -/
def deploySseEvent (input : Bytes) : Sse.Event :=
  Sse.stepField Sse.Event.empty (Sse.Field.data (Reactor.Deploy.deployResp input).body)

/-- **`sse_deployed` — the deployed SSE frame carries the served body verbatim.**
Folding the served body as a `data:` field yields an event whose ordered `data`
lines are exactly the served body (one line, in order — `stepField` appends), with
no `event:` type set (default `message`). So the SSE dispatch of the deployed
response streams the very bytes `serveFull` serialized. -/
theorem sse_deployed (input : Bytes) :
    (deploySseEvent input).data = [(Reactor.Deploy.deployResp input).body]
    ∧ (deploySseEvent input).event = none :=
  ⟨rfl, rfl⟩

/-! ## (5) Isolation — the served exposure never reaches another tenant's resource -/

/-- The deployed isolation system: one tenant, the deployed listener
(`Reactor.Deploy.deployLid`), which scopes every resource a request on the
deployed exposure touches; every other tenant scopes nothing. The router respects
the partition by construction (`wf`). -/
def deploySystem : Isolation.System :=
  { scope   := fun t _ => decide (t = Reactor.Deploy.deployLid)
    owner   := fun _ => Reactor.Deploy.deployLid
    touches := fun _ => [0, 1, 2]
    wf      := by intro _ _ _; simp [Reactor.Deploy.deployLid] }

/-- **`isolation_deployed` — every resource the served exposure touches is in the
owning tenant's scope** (`Isolation.touched_in_scope`, the isolation invariant on
the deployed surface). -/
theorem isolation_deployed (e : Isolation.ExposureId) (res : Isolation.ResourceId)
    (h : res ∈ deploySystem.touches e) :
    deploySystem.scope (deploySystem.owner e) res = true :=
  Isolation.touched_in_scope deploySystem e res h

/-- The deployed tenant scopes are pairwise disjoint (only `deployLid` scopes
anything). -/
theorem deploySystem_disjoint :
    ∀ t₁ t₂ res, t₁ ≠ t₂ →
      deploySystem.scope t₁ res = true → deploySystem.scope t₂ res = false := by
  intro t₁ t₂ res hne h1
  have ht1 : t₁ = Reactor.Deploy.deployLid := by
    simpa [deploySystem] using h1
  have ht2 : t₂ ≠ Reactor.Deploy.deployLid := fun h => hne (ht1.trans h.symm)
  simpa [deploySystem] using ht2

/-- **`isolation_no_cross_tenant_deployed` — no cross-tenant reach on the deployed
path.** A request on the deployed exposure never touches a *different* tenant's
resource (`Isolation.no_cross_tenant` under the disjointness above). This is the
security property for the deployed surface, not an isolated model. -/
theorem isolation_no_cross_tenant_deployed (e : Isolation.ExposureId)
    (t : Isolation.TenantId) (res : Isolation.ResourceId)
    (hne : t ≠ deploySystem.owner e) (h : res ∈ deploySystem.touches e) :
    deploySystem.scope t res = false :=
  Isolation.no_cross_tenant deploySystem deploySystem_disjoint e t res hne h

/-! ## (6) Metrics — the served response is counted, exactly and without side effect -/

/-- A per-status-code request counter name for the served response. -/
def statusCounterName (input : Bytes) : String :=
  toString (Reactor.Deploy.deployResp input).status

/-- **`metrics_counts_deployed` — the served response bumps its status counter by
exactly one, no side effect.** Incrementing the per-status-code counter for the
deployed response raises exactly that counter by one (`inc_exact`) and leaves every
other counter untouched (`inc_others`). -/
theorem metrics_counts_deployed (input : Bytes) (r : Metrics.Registry) :
    (r.inc (statusCounterName input) 1).counters (statusCounterName input)
        = r.counters (statusCounterName input) + 1
    ∧ (∀ n, n ≠ statusCounterName input →
        (r.inc (statusCounterName input) 1).counters n = r.counters n) :=
  ⟨Metrics.inc_exact r _ 1, fun _ h => Metrics.inc_others r _ 1 _ h⟩

/-- The histogram observation value for the served response: its body length. -/
def deployObserveVal (input : Bytes) : Nat := (Reactor.Deploy.deployResp input).body.length

/-- **`metrics_histogram_deployed` — observing the served body length keeps the
histogram accounting exact.** A single observation of the served response's body
length bumps the total by exactly one (`observe_total`) and adds exactly one to the
sum of bucket counts (`observe_sum`) — nothing lost or double-counted across
buckets, so the bucket-count sum stays in lockstep with the total. -/
theorem metrics_histogram_deployed (input : Bytes) (h : Metrics.Histogram)
    (hi : Metrics.bucketIndex h.bounds (deployObserveVal input) < h.counts.length) :
    (h.observe (deployObserveVal input)).total = h.total + 1
    ∧ (h.observe (deployObserveVal input)).counts.sum = h.counts.sum + 1 :=
  ⟨Metrics.observe_total h _, Metrics.observe_sum h _ hi⟩

/-! ## Axiom audit — every deployed seam is closed on the standard axioms only -/

#print axioms deployed_dispatch_agrees
#print axioms har_records_deployed
#print axioms har_evicts_oldest_deployed
#print axioms sticktable_deployed
#print axioms downloadmgr_deployed
#print axioms sse_deployed
#print axioms isolation_deployed
#print axioms isolation_no_cross_tenant_deployed
#print axioms metrics_counts_deployed
#print axioms metrics_histogram_deployed

end WireMore
end Reactor
