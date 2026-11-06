# Streaming receipts over a live Claude Code transcript

Initiative 11. Theory: `metatheory/Dregg2/Stream/` (grounding: `docs/stream/GROUNDING.md`).

    ./run.sh <transcript.jsonl> <out_dir> [every=100] [follow_s=60]

- **producer**: `stream-monitor run` (Rust, `dregg-query/src/bin/stream-monitor.rs`) tails the transcript,
  appends each complete line to an MMR (dregg-query's, `ArityBlake3` hasher, incremental `Frontier`), cuts
  a window every N lines into `<out>/windows/wNNNNNN.jsonl`, and runs `stream-check produce` (Lean) to
  write receipt k to `<out>/receipts/rNNNNNN.json` (temp file, then rename). It compares the Lean root with its own after every window
  and stops on a disagreement.
- **follower**: `stream-check follow` (Lean, `metatheory/StreamCheck.lean`) starts at genesis and accepts
  receipt k iff `Policy.checkWindow` holds for window k against its own state after k-1: work
  O(window + log n), nothing about the prefix. One JSON line per window: verdict, state, Büchi visit
  count, last marked position, hash calls, bytes, microseconds.
- **publisher / anchor**: an independent read of the source transcript's first n lines
  (`stream-check root`) gives the root a log owner would publish. `stream-check verify --anchor R`
  requires the chain to end there (`anchored_is_genuine`): the chain check alone ties receipts to the
  windows it is shown; the anchor ties them to the source.
- **auditor**: `stream-monitor audit --lo I --hi J --root R` opens positions against the published root
  alone with dregg-query's `verify_range` (the Rust embodiment of `RVerifies`, documented, not proved);
  an omitted position and a shifted answer are refused.
- **tamper**: (1) a line deleted from window 1 under the honest receipts, (2) windows 1 and 2 swapped:
  the chain check refuses both; (3) the producer deletes a line before windowing and recomputes every
  receipt: the chain check accepts, the anchor refuses.

Policy (`Dregg2/Stream/ClaudeCore.lean`): safety, no Bash call runs `git stash`, `git add -A|--all`,
`pkill -f`, `killall`, `kill -u` as a command segment; liveness (Büchi), every human prompt is eventually
followed by assistant text. Verdicts: `viol` (final, a bad prefix) or `unknown`; the liveness half never
yields a verdict on a finite prefix (`respLive_is_liveness`), its receipts carry the visit count and the
last marked position instead.

Transcripts are private by default: receipts carry roots, states and counts only; the window files hold
the raw lines and stay local.
