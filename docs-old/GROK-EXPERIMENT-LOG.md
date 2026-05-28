
---

## Experiment 3: SlotChanged guard fix (Issue #101) — 2026-05-25

**Commit:** d3e74e91

**Task:** Fix `TransitionGuard::SlotChanged` being permanently inert. Issue #101 claimed the matcher only receives `TransitionMeta`, never old/new `CellState`, so any cell program using `SlotChanged` is silently a no-op.

**Discovery:** Before crafting a grok prompt, verified the actual code:
- `TransitionGuard::matches()` in `cell/src/program.rs:230-257` already accepts `old_state: Option<&CellState>, new_state: &CellState` and correctly implements `SlotChanged` at lines 240-248.
- `evaluate_full()` at line 1074 already calls `case.guard.matches(meta, old_state, new_state)`.
- The bug was the test, not the implementation: `#[ignore]` reason was stale; body was `panic!("blocked")`.

**Grok outcome:** Invoked via `--permission-mode bypassPermissions --single`. Silent failure — 1-byte log, no file changes. `--single` is single-turn response-only, no tool use. Fix applied directly by Sonnet lane.

**Fix applied:** In `tests/src/slot_caveat_composition_stress.rs` — removed stale `#[ignore]`, replaced `panic!("blocked")` with 4 real `evaluate_with_meta` assertions covering: accept on method match + slot changed + Monotonic satisfied (×2 methods); reject on slot unchanged; reject on unrelated method.

**Cascade impact:** Zero — plumbing was complete. Only the test file changed.

**Structural verification (no cargo):** Traced all 4 assertions through `evaluate_full` logic. All correct per implementation.

**Recommendation:** Grok `--single`/`--prompt-file` are dead ends for multi-step file edits. For mechanical one-file fixes with a known exact change, applying directly is faster. Grok adds value for exploratory refactors in interactive mode.

---

## Experiment 2: dead-stub deletions (2026-05-26)

**Task:** Remove 5 HISTORICAL-REMOVED dead stubs identified in IGNORED-TESTS-AUDIT.md:
1. `circuit/tests/sovereign_transition.rs` — entire file (pure empty stub)
2. `dregg-dsl-tests/src/sovereign_transition_dsl.rs:352` — `dsl_matches_handwritten_air` function
3. `coord/src/tests.rs:1394` — `many_node_causal_dag` `#[cfg(any())]` block
4. `coord/src/tests.rs:1446` — `rejected_turn_still_in_dag` `#[cfg(any())]` block
5. `demo-agent/examples/unified_harness.rs:1110` — `run_federation_bootstrap` `#[cfg(any())]` block

**Grok invocation attempts:**

Attempt 1: `grok --permission-mode bypassPermissions -p "<prompt>"` — silent failure. The `-p`/`--single` flag is single-turn only (prints response and exits). Produced a 1-byte log and no changes.

Attempt 2: `grok --permission-mode bypassPermissions --always-approve --max-turns 30 --prompt-file <file> --output-format plain` — partial progress. Grok started a full agentic session (session 019e61c6-b5fe-7220-88fa-d5cde49e4251), read the relevant files, ran `git rm circuit/tests/sovereign_transition.rs`, then hit the 30-turn limit and terminated with `max_turns exceeded`. Only 1 of 5 items was handled, and the deletion was staged but not committed.

**Resolution:** Manager (Sonnet) performed the remaining 4 deletions directly and committed all 5 as 4 logical commits: ed613741, 8305c9ba, 0df81dad, 2c1b5080.

**Time to completion:** ~5 minutes of elapsed real time across two grok invocations + direct cleanup.

**Weird grok behavior:**
- First invocation (`-p`) silently did nothing and produced a 1-byte log — no indication of why, no error message. This is because `--single` is literally a one-shot LLM call with no tool use.
- Second invocation ran correctly as an agent but used 31 turns (30 LLM calls + tool overhead) to process only 1 of 5 items — an alarming ratio. Grok spent many turns reading/searching before acting.
- Grok did respect the "no cargo" constraint: no cargo commands were observed.
- After the prior session (019e61c6) grok had already created GROK-EXPERIMENT-LOG.md and written Experiment 4 into it, showing grok was active in this workspace and writing docs.

**Recommendation:** Grok is not well-suited for this class of bounded-cleanup task when invoked non-interactively. The `--single` flag is a dead end for multi-step edits. The agentic mode works but is turn-inefficient (31 turns for 1 deletion). For small, precisely-described deletions in 4-5 files, direct manager edits are faster, lower-risk, and verifiable. Grok may be more appropriate for open-ended exploration tasks where its broad reading behavior is an asset rather than overhead.

---

## Experiment 4: revocation replay on recovery (2026-05-25)

**Issue:** #102 — crashed-then-recovered nodes treat revoked tokens as valid because the recovery path doesn't replay missed revocations.

**Discovery findings:**

The `test_revocation_after_recovery` test in `teasting/tests/revocation_propagation.rs:97` was `#[ignore]`-ed with the message "TODO: implement state sync for recovered nodes". The assertions were fully commented out. But the implementation already existed:

- `SimFederation::recover_node` (teasting/src/harness.rs:338-347) replays the federation-wide `all_revoked: HashSet<String>` into the rejoining node's local `revoked` set. This set is populated unconditionally on every `run_consensus_round` call (line 278-280), regardless of which nodes are online.
- `Federation::recover_node` (federation/src/node.rs:1191-1219) replays `finalized_history` via `apply_finalized_block` over each missed block — the real-node-layer counterpart.
- `crash_node` does NOT wipe `n.revoked` — it only sets `is_online = false`. So nodes retain their pre-crash state; recovery only needs to add what was missed while offline.

**Fix:** Removed `#[ignore]`, uncommented and activated the two assertions with descriptive failure messages. No changes to the implementation — none were needed.

**Grok outcome:** Grok was invoked with `--permission-mode bypassPermissions` and produced empty output (silent failure). The fix was made and committed directly.

**Soundness assessment:** The fix is correct and complete. Every token that finalizes during a node's downtime is unconditionally inserted into `all_revoked` on the federation object (line 278-280 of harness.rs). `recover_node` iterates the full set and inserts each token into the rejoining node. There is no finalization path that bypasses `all_revoked`. The test also exercises the post-recovery round, confirming that `trigger-sync` (submitted after recovery) reaches the rejoined node via the normal online path.

**Commit:** 8fc669e8

**Recommendation on grok for security-sensitive fixes:** Grok silently failed here (empty output). Even when grok works, using it for security-relevant fixes without verifying the output against the actual implementation is dangerous — it can produce plausible-looking but incorrect code. For correctness-critical paths like revocation replay, manual trace-through is required regardless. Grok may be acceptable for boilerplate or test scaffolding but should not be trusted as the primary reviewer for security properties.
