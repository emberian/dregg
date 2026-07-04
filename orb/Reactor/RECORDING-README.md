# Reactor.Recording — Har ring + DownloadMgr client, on the deployed path

`Reactor/Recording.lean` wires two libraries that were proven in isolation but
consulted by nothing that serves onto the **deployed** request path
(`Reactor.Deploy.deployStep`, the function `Arena.Orb.main` runs via
`serveFull`). The recording is a transparent side-channel: the served bytes are
exactly `deployStep`'s, and the deployed `Metrics`/`Trace`/`Tap` observability
already folded into `deployStep` keeps advancing underneath.

## What is wired

### 1. Har bounded recording ring

`recordStep : RecState → Bytes → Bytes × RecState` serves a request through
`Deploy.deployStep` and, in the same step, appends the served request to the
**real** `Har.Recorder.record` (newest last, capped at `cap`, oldest evicted).

- `entryOf input` records the resolved method/target of the dispatched request
  (the bytes the arena parser flowed through the deployed reactor) and the
  status of the deployed response (`Deploy.deployResp`, the real `App.handle`
  under the deployed header rewrite).
- `recordStep_transparent` : the returned bytes are exactly `Deploy.serveFull input`.
- `recordStep_metrics` : the deployed request counter still advances by exactly
  one (`Deploy.deploy_metrics_exact`) — recording does not disturb it.

### 2. DownloadMgr client (proxied fetch with Range-resume)

A proxied upstream fetch — the reverse-proxy dialing the DNS-resolved backend
`deployStep` chose — is modeled as a **real** `DownloadMgr` job.
`fetchAfter budget k` is the job after `[activate, deliver k, pause]`: cursor at
`k`, `paused`, ready to resume.

## Seam theorems

### `har_records_deployed`

From a cold recorder of capacity `cap`, after a window of `N` served requests on
the deployed path the ring holds exactly the most-recent `min(N, cap)` records,
in arrival order:

1. **order + retention** — the retained entries are a *suffix* of the full
   recorded history (`recRun_entries_suffix`, composing `Har.record_suffix`
   through suffix transitivity);
2. **exact fill** — the length is exactly `min(N, cap)` (`recRun_length`,
   composing the `Har.keepLast` capping identity `record_length`);
3. **bounded** — it never exceeds `cap`.

A recorder that reordered, dropped the newest, or overflowed would break the
per-step bound and fail this theorem.

### `downloadmgr_resume_deployed`

On a deployed dispatch (`deploySubs input = .dispatch req :: rest`):

1. the deployed reverse-proxy/DNS pipeline dials the concrete resolved upstream
   `⟨1572395042⟩` = `93.184.216.34` (`Deploy.deploy_plan_resolved`, the proxy
   path) — so a client fetch of that upstream is warranted;
2. the client fetch, paused after `k` received bytes and resumed, requests
   *exactly* the missing suffix `reqFrom k` (`Range: bytes=k-`) via the real
   `DownloadMgr.activate_reqFrom_paused`;
3. the received prefix ++ the requested suffix reassembles the whole content
   with no gap or overlap at the seam (`DownloadMgr.resume_reassembles`).

This composes the deployed proxy path with the real `DownloadMgr` resume.

## Build / verification

- `lake build Reactor.Recording` — green.
- Zero `sorry`, zero unclosed goals.
- `#print axioms` for `har_records_deployed`, `downloadmgr_resume_deployed`,
  `recordStep_transparent`, `recordStep_metrics` ⊆ `{propext, Quot.sound,
  Classical.choice}`.

## Ownership / notes

- Registered via one added import line in `Reactor.lean` (`import Reactor.Recording`).
- The recording layer wraps `deployStep` rather than living inside it (the same
  pattern `Reactor.Observe` uses to wrap `Reactor.serve`); `main` runs
  `deployStep`, and `recordStep` is the recording view over it. The served bytes
  are provably identical, so the wrapper is faithful.
- The full `Reactor` target may show an unrelated red in a sibling file
  (`Reactor.RespTransform`) during independent development; that file is not part
  of this module's scope and is untouched here.
