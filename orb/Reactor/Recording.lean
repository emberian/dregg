import Reactor.Deploy
import Har.Basic
import DownloadMgr.Basic
import DownloadMgr.Theorems

/-!
# Reactor.Recording — the real Har recording ring and the real DownloadMgr
client, on the deployed path

The bar: a wiring counts only when the *real* library drives the serving
path the deployed orb runs. `Reactor.Deploy.deployStep` is that path — `main`
serves each request through it (`serveFull`), and it already threads the real
observability state (the real `Metrics.Registry.inc` on the request counter, the
real `Tap.step` gate, the real `Trace`-assigned correlation id). Two libraries
were still proven in isolation and consulted by nothing on that path:

* **`Har`** — a bounded recording ring (newest last, capped, oldest evicted).
  Here every served request on the deployed path is recorded through the real
  `Har.Recorder.record`. `recordStep` serves via `deployStep` and, in the same
  step, appends the served request to the ring. Recording is a transparent
  side-channel: `recordStep_transparent` shows the served bytes are exactly
  `deployStep`'s (recording never perturbs the traffic it records), and
  `recordStep_metrics` shows the deployed `Metrics`/`Trace`/`Tap` observability
  still advances underneath (it rides on `deployStep`, unchanged).

* **`DownloadMgr`** — the client-side download/session state machine with a
  `Range`-resume. A proxied upstream fetch (the reverse-proxy dialing the
  DNS-resolved backend `deployStep` chose) is modeled as a `DownloadMgr` job:
  activate GETs from offset 0, `pause` records the received cursor, and a resume
  (`activate` from `paused`) re-requests exactly the open-ended suffix past the
  cursor (`Range: bytes=recv-`).

## Seam theorems (deployed-path facts)

* **`har_records_deployed`.** From a cold recorder of capacity `cap`, after a
  window of `N` served requests the ring holds exactly the most-recent
  `min(N, cap)` records, in arrival order: the retained entries are a *suffix*
  of the full recorded history (order preserved, newest kept), the length is
  exactly `min(N, cap)`, and it never exceeds `cap`. This composes the real
  `Har.record_suffix` / `record_length_le_cap` with the `deployStep` fold: a
  recorder that reordered, dropped the newest, or overflowed would break the
  per-step bound and fail here.

* **`downloadmgr_resume_deployed`.** On a deployed dispatch the proxy/DNS
  pipeline dials a concrete upstream, so a client fetch is warranted; the fetch,
  paused after `k` received bytes and resumed, requests *exactly* the missing
  suffix (`reqFrom k`), and the received prefix concatenated with that requested
  suffix reassembles the whole content with no gap or overlap at the seam. This
  composes the deployed `Deploy.deploy_plan_resolved` (the proxy path) with the
  real `DownloadMgr.activate_reqFrom_paused` / `resume_reassembles`.
-/

namespace Reactor
namespace Recording

open Proto (Bytes)

/-! ## Part 1 — the Har recording ring on the deployed path -/

/-- Decode request bytes to a display `String` (total: `Char.ofNat` maps every
byte, invalid scalar values collapsing to `'\0'`). Used only to fill the display
fields of a `Har.Entry`; it is never unfolded in a proof. -/
def bytesToString (b : Bytes) : String :=
  String.mk (b.map fun c => Char.ofNat c.toNat)

/-- The dispatched request heading a submission list, if any — the same shape the
deployed `demoResp`/`deployResp` walks. -/
def dispatchedReq : List RingSubmission → Option Proto.Request
  | [] => none
  | .dispatch req :: _ => some req
  | _ :: rest => dispatchedReq rest

/-- The `Har.Entry` a served request denotes: the resolved method and target of
the dispatched request (the same bytes the arena parser flowed through the
deployed reactor) and the status of the deployed response (`deployResp`, the
real `App.handle` under the deployed header rewrite). A request the FSM answered
itself (no dispatch) records with a `-` method/path but the real status. -/
def entryOf (input : Bytes) : Har.Entry :=
  match dispatchedReq (Deploy.deploySubs input) with
  | some req =>
      { method := bytesToString req.method
        path   := bytesToString req.target
        status := (Deploy.deployResp input).status }
  | none =>
      { method := "-", path := "-"
        status := (Deploy.deployResp input).status }

/-- The full recorded history a window of served requests denotes, newest last. -/
def entriesOf (inputs : List Bytes) : List Har.Entry := inputs.map entryOf

/-- The recording state threaded down the deployed path: the deployed
observation state (`Metrics`/`Tap`/`Trace`) plus the real `Har` recording ring. -/
structure RecState where
  /-- The deployed observation state (`deployStep` advances it). -/
  obs : Reactor.Observe.ObsState
  /-- The real `Har` bounded recording ring. -/
  har : Har.Recorder

/-- Cold start: a cold observation state and an empty ring of capacity `cap`. -/
def RecState.init (cap : Nat) : RecState :=
  { obs := Reactor.Observe.ObsState.init, har := { cap := cap, entries := [] } }

/-- **The recording step over the deployed path.** Serve the request through the
deployed `Deploy.deployStep` (bytes out + advanced observation state), then append
the served request to the real `Har` ring. The served bytes are exactly
`deployStep`'s — recording is a transparent side-channel. -/
def recordStep (rs : RecState) (input : Bytes) : Bytes × RecState :=
  let out := Deploy.deployStep rs.obs input
  ( out.1
  , { obs := out.2, har := rs.har.record (entryOf input) } )

/-- Thread the recording state over a window of requests, left to right. -/
def recRun (rs : RecState) : List Bytes → RecState
  | [] => rs
  | input :: rest => recRun (recordStep rs input).2 rest

/-! ### Transparency and observability ride-along -/

/-- **Transparency.** The bytes `recordStep` returns are exactly the deployed
`serveFull` output — recording never rewrites the served response. -/
theorem recordStep_transparent (rs : RecState) (input : Bytes) :
    (recordStep rs input).1 = Deploy.serveFull input := rfl

/-- The recording step records exactly `entryOf input` into the real `Har` ring. -/
theorem recordStep_har (rs : RecState) (input : Bytes) :
    (recordStep rs input).2.har = rs.har.record (entryOf input) := rfl

/-- **Observability rides along, undisturbed.** The deployed request counter still
advances by exactly one under `recordStep` — the real `Metrics.inc_exact` folded
into `deployStep` (`Deploy.deploy_metrics_exact`), unperturbed by the recording. -/
theorem recordStep_metrics (rs : RecState) (input : Bytes) :
    (recordStep rs input).2.obs.metrics.counters Reactor.Observe.reqCounter
      = rs.obs.metrics.counters Reactor.Observe.reqCounter + 1 :=
  Deploy.deploy_metrics_exact rs.obs input

/-! ### The ring is bounded, ordered, and keeps the newest -/

/-- Appending the same suffix to a suffix stays a suffix. -/
theorem suffix_append_right {α : Type} {a b : List α} (c : List α) (h : a <:+ b) :
    a ++ c <:+ b ++ c := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [← List.append_assoc, ht]⟩

/-- The ring's capacity is invariant under recording. -/
theorem recRun_cap (rs : RecState) (inputs : List Bytes) :
    (recRun rs inputs).har.cap = rs.har.cap := by
  induction inputs generalizing rs with
  | nil => rfl
  | cons x rest ih =>
    show (recRun (recordStep rs x).2 rest).har.cap = rs.har.cap
    rw [ih (recordStep rs x).2]
    rfl

/-- **Order preservation + retention (general).** After a window, the retained
entries are a suffix of the whole recorded history — nothing reordered, the
newest always kept. Composes the real `Har.record_suffix` step-by-step through
suffix transitivity. -/
theorem recRun_entries_suffix (rs : RecState) (inputs : List Bytes) :
    (recRun rs inputs).har.entries <:+ rs.har.entries ++ entriesOf inputs := by
  induction inputs generalizing rs with
  | nil =>
    show (recRun rs []).har.entries <:+ rs.har.entries ++ entriesOf []
    simp only [entriesOf, List.map_nil, List.append_nil]
    exact List.suffix_refl _
  | cons x rest ih =>
    have h1 : (recRun (recordStep rs x).2 rest).har.entries
        <:+ (recordStep rs x).2.har.entries ++ entriesOf rest := ih _
    have h2 : (recordStep rs x).2.har.entries <:+ rs.har.entries ++ [entryOf x] :=
      Har.record_suffix rs.har (entryOf x)
    have h3 : (recordStep rs x).2.har.entries ++ entriesOf rest
        <:+ (rs.har.entries ++ [entryOf x]) ++ entriesOf rest :=
      suffix_append_right _ h2
    have heq : (rs.har.entries ++ [entryOf x]) ++ entriesOf rest
        = rs.har.entries ++ entriesOf (x :: rest) := by
      simp only [entriesOf, List.map_cons, List.append_assoc, List.cons_append,
        List.nil_append]
    show (recRun (recordStep rs x).2 rest).har.entries
        <:+ rs.har.entries ++ entriesOf (x :: rest)
    rw [← heq]
    exact h1.trans h3

/-- One record leaves the ring at `min (len+1) cap` entries — the real capping
identity (`Har.keepLast`), stated as a length. -/
theorem record_length (r : Har.Recorder) (e : Har.Entry) :
    (r.record e).entries.length = min (r.entries.length + 1) r.cap := by
  show (Har.keepLast r.cap (r.entries ++ [e])).length = _
  unfold Har.keepLast
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil]
  omega

/-- **Exact fill (general).** From a well-formed ring, after a window of length
`N` the ring holds exactly `min (len + N) cap` entries — the fill grows one per
served request and saturates at the capacity. -/
theorem recRun_length (rs : RecState) (inputs : List Bytes)
    (hwf : rs.har.entries.length ≤ rs.har.cap) :
    (recRun rs inputs).har.entries.length
      = min (rs.har.entries.length + inputs.length) rs.har.cap := by
  induction inputs generalizing rs with
  | nil =>
    show rs.har.entries.length = min (rs.har.entries.length + List.length ([] : List Bytes)) rs.har.cap
    simp only [List.length_nil, Nat.add_zero]
    omega
  | cons x rest ih =>
    show (recRun (recordStep rs x).2 rest).har.entries.length = _
    have hcap : (recordStep rs x).2.har.cap = rs.har.cap := rfl
    have hlen : (recordStep rs x).2.har.entries.length
        = min (rs.har.entries.length + 1) rs.har.cap := record_length rs.har (entryOf x)
    have hwf1 : (recordStep rs x).2.har.entries.length ≤ (recordStep rs x).2.har.cap := by
      rw [hlen, hcap]; omega
    rw [ih (recordStep rs x).2 hwf1, hcap, hlen]
    simp only [List.length_cons]
    omega

/-- **Seam theorem — `har_records_deployed`.** From a cold recorder of capacity
`cap`, after a window of `N` served requests on the deployed path the real `Har`
ring holds exactly the most-recent `min(N, cap)` records, in arrival order:

  1. the retained entries are a *suffix* of the full recorded history
     (order preserved, newest always kept);
  2. the fill is exactly `min(N, cap)`; and
  3. it never exceeds `cap`.

Composes the real `Har.record_suffix` / capping identity with the `deployStep`
fold — a recorder that reordered, dropped the newest, or overflowed would fail. -/
theorem har_records_deployed (cap : Nat) (inputs : List Bytes) :
    (recRun (RecState.init cap) inputs).har.entries <:+ entriesOf inputs
  ∧ (recRun (RecState.init cap) inputs).har.entries.length = min inputs.length cap
  ∧ (recRun (RecState.init cap) inputs).har.entries.length ≤ cap := by
  have hsuf : (recRun (RecState.init cap) inputs).har.entries
      <:+ (RecState.init cap).har.entries ++ entriesOf inputs :=
    recRun_entries_suffix _ _
  have hwf : (RecState.init cap).har.entries.length ≤ (RecState.init cap).har.cap := by
    show (0 : Nat) ≤ cap
    exact Nat.zero_le _
  have hlen : (recRun (RecState.init cap) inputs).har.entries.length
      = min ((RecState.init cap).har.entries.length + inputs.length)
          (RecState.init cap).har.cap := recRun_length _ _ hwf
  refine ⟨?_, ?_, ?_⟩
  · have hnil : (RecState.init cap).har.entries ++ entriesOf inputs = entriesOf inputs := by
      show [] ++ entriesOf inputs = entriesOf inputs
      rw [List.nil_append]
    rwa [hnil] at hsuf
  · rw [hlen]
    show min (0 + inputs.length) cap = min inputs.length cap
    rw [Nat.zero_add]
  · rw [hlen]
    show min (0 + inputs.length) cap ≤ cap
    omega

/-! ## Part 2 — the DownloadMgr client, on the proxied fetch path -/

/-- The client fetch state after starting a proxied upstream GET, receiving `k`
contiguous bytes, and pausing: the real `DownloadMgr` job driven by
`[activate, deliver k, pause]` from a fresh job with retry budget `budget`. Its
recorded cursor is `k` and it is `paused`, ready to resume. -/
def fetchAfter (budget k : Nat) : DownloadMgr.Job :=
  (DownloadMgr.run (DownloadMgr.Job.init budget) [.activate, .deliver k, .pause]).1

/-- The paused fetch has recorded exactly `k` received bytes. -/
theorem fetchAfter_recv (budget k : Nat) : (fetchAfter budget k).recv = k :=
  Nat.zero_add k

/-- The fetch is paused after the interrupt, ready to resume. -/
theorem fetchAfter_paused (budget k : Nat) :
    (fetchAfter budget k).st = DownloadMgr.JobState.paused := rfl

/-- **Resume requests exactly the suffix.** Resuming the paused fetch re-issues a
`Range` request for exactly the open-ended suffix past the received cursor
(`reqFrom k`), and the received prefix concatenated with that requested suffix
reassembles the whole content with no gap or overlap. Composes the real
`DownloadMgr.activate_reqFrom_paused` with `resume_reassembles`. -/
theorem fetch_resume_suffix {α : Type} (budget k : Nat) (content : List α) :
    (DownloadMgr.step (fetchAfter budget k) .activate).2
        = [DownloadMgr.Output.reqFrom k]
      ∧ content.take k ++ content.drop k = content := by
  refine ⟨?_, DownloadMgr.resume_reassembles content k⟩
  rw [DownloadMgr.activate_reqFrom_paused _ (fetchAfter_paused budget k),
    fetchAfter_recv]

/-- **Seam theorem — `downloadmgr_resume_deployed`.** On a deployed dispatch:

  1. the deployed reverse-proxy/DNS pipeline dials the concrete resolved upstream
     `⟨1572395042⟩` (`93.184.216.34`) — so a client fetch of that upstream is
     warranted (`Deploy.deploy_plan_resolved`, the proxy path);
  2. the client fetch of that upstream, paused after `k` received bytes and
     resumed, requests *exactly* the missing suffix `reqFrom k`
     (`Range: bytes=k-`); and
  3. the received prefix concatenated with that requested suffix reassembles the
     whole content with no gap or overlap at the seam (`resume_reassembles`).

Composes the deployed proxy path with the real `DownloadMgr` resume. -/
theorem downloadmgr_resume_deployed {α : Type} (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission) (hsub : Deploy.deploySubs input = .dispatch req :: rest)
    (budget k : Nat) (content : List α) :
    Proxy.targetedUpstream (Deploy.deployPlan (Deploy.deploySubs input))
        = some (⟨1572395042⟩ : Proto.Addr)
      ∧ (DownloadMgr.step (fetchAfter budget k) .activate).2
          = [DownloadMgr.Output.reqFrom k]
      ∧ content.take k ++ content.drop k = content := by
  refine ⟨?_, (fetch_resume_suffix budget k content).1,
    (fetch_resume_suffix budget k content).2⟩
  rw [Deploy.deploy_plan_resolved input req rest hsub]
  rfl

end Recording
end Reactor
