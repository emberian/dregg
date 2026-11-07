# GROUNDING: a stranger verifies a real Claude Code session through R0-R3

Initiative 10 (whatember/INITIATIVES.md). Written before building. This file covers what exists,
what is reused, what is replaced and why, the measured gap, and where the bar is wrong.

## What exists (read, with the load-bearing facts)

| piece | where | what it actually does today |
|---|---|---|
| R0 | `grain-verify/src/lib.rs` `GrainAttestation::verify` | composes `dregg_agent::verify_agent_run`: an ed25519 receipt chain (prev-hash linked, seq-ordered, one signer) plus per-step budget teeth. The host holds the signing seed. |
| R1 | same, `GenesisPin`, `RenterCheckpoint`, `CountersignedCheckpoint`, `verify_for_renter` | the renter countersigns `(head_root, num_turns)` with a key the host lacks: anti-truncation (shown >= acknowledged) and anti-rewrite (receipt at position n hashes to head_root). Its own doc says the genesis nonce is *not* forced into the chain's cryptographic genesis. |
| R2 | `grain-turn/src/lib.rs` `ToolGatewayMinter` (the one real `GrainTurnMinter`), `verify_r2_for_renter` | every admitted action becomes a committed `ToolGateway::invoke` executor turn on a grain worker cell: slot 3 `HISTORY_ROOT_SLOT` = Blake3 MMR over prior turn receipts, 4 `calls_made` (executor-enforced `FieldLte`+`Monotonic`), 5 consumed, 6 heap root, 7 `action_commit(label,cost)`. The receipt carries `turn_receipt_hash`; R2 checks it against the committed-turn manifest (which the stranger must take from the executor host). |
| R3 adapter | `grain-turn/src/finalize.rs` `finalize_grain_turn` / `finalize_session` | mints rotated wide-anchored EffectVM legs from captured `(before_cell, effects, after_cell)`. **One grain turn is about 5 legs** (one homogeneous cohort per SetField slot). **A multi-turn session does not fold.** The EffectVM ticks the nonce once per effect and the executor ticks it once per turn, so turn t+1's real pre-cell is not turn t's EffectVM head. The file names the fix: "single-nonce-tick multi-field grain rotated descriptor, a new circuit descriptor + committed VK, ember-gated". The only passing R3 over grain legs is the `#[ignore]`d one-turn test `grain-turn/tests/r3_grain_adapter.rs`. |
| R3 decision | `grain-verify/src/r3.rs` `r3_verify`, Lean `Dregg2/Grain/R3Verify.lean` `r3VerifyCore`, `@[export] dregg_grain_r3_verify` | Rust folds and light-verifies, then puts a 33-int wire `(verified, presentedVk8, expectedVk8, aggHead8, anchoredHead8)` to the Lean core. Its `"1"` is the accept. `r3VerifyCore` is `verified && presented = expected && aggHead = anchoredHead`. `r3_unfoolable` reduces to the carried `RecursiveAggregation.EngineSound` (FRI and recursion legs proved outside Lean). **`r3_verify` takes the legs and re-proves the fold inside the verifier**, so a stranger would be re-running the prover. |
| aggregate wire | `circuit-prove/src/ivc_turn_chain.rs` `WholeChainProofBytes` (v6), `verify_whole_chain_proof_bytes(bytes, expected_vk)` | a verify-only envelope: genesis_root8, final_root8, chain_digest8, num_turns u32. The VK fingerprint is a function of shape (num_turns, leaf trace heights), so it has to come from an honest setup party. It is never taken from the artifact (wound #22). |
| Lean link | `dregg-lean-ffi` | a 178 MB seed archive (mathlib closure). The Mac seed (2026-08-07 09:18) exports `dregg_grain_r3_verify`. **No Linux seed is published** (404 on the `lean-seed` release), so bb2 can prove but cannot render the Lean decision through the FFI. |
| cv | `/Users/ember/dev/cv`, `cv export --format json --redact` (OpenSession 0.3) | reproducible: the root export of `e3ba49ed` today has sha256 `feb91909...`, the same digest demo (b) recorded. cv has no hook that records tool calls. Its hooks are compact/start/lane/decisions/edit/retired. |
| demo (b) | `demo/datalog-governance/project_transcript.py`, `data/transcript.json` | the published projection: per call agent, seq, tool, use_id, ts, file path (file tools), spawned id. No text, inputs or outputs. Whether `transcript.json` goes on public GitHub is still ember's open decision (initiative 1), and emberian/dregg is public. |
| microsite | `/Users/ember/src/dregg-microsites/prove-the-turn`, `governance-receipt` | the dark masthead style. governance-receipt already shows this session forest's Datalog receipt. |
| the critique | `degg-research/research/governance-foundations-critique.md` W10 (l.363-386), lattice X-3/X-5/X-6 | "non-omission is a property of logs, completeness is a property of where the log is written". Coverage needs a chokepoint (`CommitStep.lean` `commit_before_forward`), and the premise that every frame passes the port is an installation claim. X-3 (no consistency-proof theorem) and X-5 (no witness cosigning) are open. |

## Prior art (helper lane, sources in its report)

CT/RFC 9162, C2SP tlog-witness/cosignature, Rekor v2 tiles, and the 2026 IETF agent-receipt drafts
(noa-scitt §5: "tail truncation only against an authenticated checkpoint ... does NOT detect equivocation").
Products: Sello (arXiv 2606.04193, receiver-signed receipts on a witness-cosigned log; "completeness of
retrieval is a separate property"), VET (2512.15892, per-call execution attestation) and NovaFabric
(measured completeness 0.652).
- **What they all give:** inclusion, plus append-only history (consistency). With witnesses, they also stop a log from showing different histories to different readers (split view).
- **What none of them proves:** completeness.
- **What we add:** an aggregate that is Lean-reduced to `EngineSound` and checks the whole history in one step, an anchor the renter holds, and a commit-before-forward point at the hook.
- **What we lack:** witness gossip/cosigning (a host can show two renters two histories; one renter's countersignature only binds that renter's view), consistency proofs between checkpoints, and standard formats.

## Measured: the non-omission gap on session e3ba49ed (root + 72 sub-agents)

Measured with `python3 -I gap.py` over the raw `~/.claude/projects/.../e3ba49ed*.jsonl` against demo (b)'s projection:

| quantity | count |
|---|---|
| tool-call occurrences in the cv projection | 3,382 |
| distinct `tool_use` ids | 3,254 (128 occurrences are fork-inherited prefixes in 7 fork transcripts) |
| raw jsonl tool_use ids not in cv export / cv ids not in raw | 0 / 0 |
| tool_use with no tool_result | 0 |
| distinct calls with a PreToolUse `hook_success` record | 3,249 (5 without: 4 Bash, 1 Edit) |
| calls with no PostToolUse success | 121 (112 Bash, 8 Read, 1 Edit) |
| hook executions that are not tool calls and that no receipt covers | 6,907 hook_success records, all `~/.config/iterm2/cc-status` |
| `run_in_background` Bash calls (effects outlive the call) | 5 |

Reading: cv loses nothing relative to the harness's own log. The transcript layer is complete.
The gap is below it.
- The transcript is written by the host.
- One Bash receipt covers whatever that shell did.
- Hooks run host code outside any tool call.
- A PreToolUse hook already fires on 99.85% of calls. This makes a hook-written receipt practical, and the 5 misses are the number to drive to 0 (or explain).

## The design (what is reused, what is new, what is replaced)

1. **Replayer, `grain-session` (new crate, adapter only).**
   - **Bundle input.** `cv export --redact` goes in and is projected exactly as demo (b) projects it. Per distinct call there is a hiding commitment `c = BLAKE3(domain, salt, canonical(input), canonical(result))`. The salts stay with ember (they open any single call later), and without them the low-entropy inputs cannot be brute-forced.
   - **Windows.** Calls are grouped into windows of W. Each window is ONE dregg-agent `AgentAction::Invoke` driven through the real `Session::run_goal_minted` with the real `ToolGatewayMinter`. Its label carries the window's MMR root over call leaves, so `ACTION_SLOT` commits it inside the kernel turn.
   - **Genesis.** Window 0's label carries the renter nonce, which forces the nonce into the chain genesis and closes R1's own stated caveat without a dregg-agent change.
   - **Why windows.** R3 costs about 5 leg proves per turn. 3,254 turns would be about 16k proves plus a fold. With windows, every call is bound to a committed kernel turn by MMR inclusion. Per-call receipts would make R0-R2 cheap but R3 infeasible. W is set from measurement (below).
2. **R3 fold across turns.** This is a new `finalize_session_threaded` in grain-turn. It threads the EffectVM state across turns, so the chain closes at the EffectVM-model head, and it is tested against the real turn data.
   - **Residual, stated in code and on the page.** The bound head is the model head. Its nonce counts field writes instead of turns; precisely what else it carries (and does not check) is in `finalize_session_threaded`'s doc.
   - The faithful fix (the single-tick multi-field descriptor and a VK change) stays ember's decision. I do not build a new VK.
3. **Verify-only R3.** This is a new `grain_verify::r3::r3_verify_aggregate(bytes, anchored_head, expected_vk)`. It takes the `WholeChainProofBytes` and does no proving. It reuses `r3_wire` and the same FFI call, so the decision is still the Lean core's `"1"`.
   - The anchored head comes from a renter-countersigned statement. That statement extends the R1 checkpoint with (genesis8, head8, vk, num_windows, calls root).
4. **VK without host trust.** `grain-session setup --synthetic <shape>` folds a public, content-free session of the same shape (window count and slot pattern) and returns the anchor. A stranger can mint it themselves (cost measured). The bundle's VK is only a claim.
5. **Verifier CLI.** `grain-session verify <bundle> --renter <pub>` runs R0 → R1 → R2 (manifest and inclusion of every call) → non-omission (calls == leaves, ordered, no extras) → R3 via Lean. There are refusal tests on the real bundle for truncation, rewrite, reorder and an unreceipted call.
6. **Closing non-omission for live sessions (cv).** A `cv hook receipt` PreToolUse, matcher `*`. It appends the call leaf to the session's receipt log and fsyncs before returning, which is the commit-before-forward point. A PostToolUse hook binds the result hash. The replayer then consumes the hook log instead of the transcript. The verifier measures and refuses on transcript calls with no hook leaf.

## Where the bar is wrong, and the better bar

- **"No host trust" is not reachable for a replayed past session.** The replay host (ember's Mac) mints the receipts from a transcript that same host wrote.
  - **What the stranger gets:** that this exact projected history was committed, kernel-turned, folded, and acknowledged by a key they hold, and that no call was dropped, reordered, rewritten or added after the fact.
  - **What the stranger cannot get:** that the transcript matches what happened. Only the live hook (6) moves the commit point to before the forward. Even then the hook is host code (an installation claim, as in W10).
  - **Better bar:** the stranger trusts exactly the transcript writer (or, live, the hook), plus `EngineSound`, plus their own key custody. The page says that sentence.
- **"R3 one recursive aggregate" for 3,254 calls must be windowed.** Per-call R3 is about 16k proves and is not runnable as a stranger-reproducible artifact. Windowing does not weaken binding: inclusion is by a Blake3 MMR (the Lean model's `mroot_binds_or_collides`, MMR.lean:488: a different leaf list gives a different root unless there is a collision).
- **The multi-turn head gap is upstream and named.** The microsite says "model head" until ember decides the descriptor.
- **Split view is out of scope.** It needs witnesses (X-5).

## Findings while building (appended 2026-11-06)

- **Executor turns need the linked Lean archive.** `ToolGatewayMinter::mint_turn` is refused fail-closed
  ("dregg_deleg_admit ... reached NO VERDICT: Lean static lib not linked") without it. dregg-lean-ffi's
  provenance gate also refuses to link a seed that was not built from this checkout's Lean source.
  The 2026-08-07 Mac seed is therefore unusable, and producing needs a current-source archive. That
  archive is being bootstrapped on bb2 (`scripts/bootstrap.sh` under swarm-build, own clone
  `/home/build/sessreceipt/bs`).
- **R3 binds each 32-byte slot value at one limb.** The EffectVM state block carries a written field
  as `field_limbs9(value)[0]` (`sdk/src/cipherclerk.rs` `field_element_to_bb`), which is one BabyBear
  limb. The folded history therefore binds the window root in `ACTION_SLOT` at about 30 bits, not
  256.
  - **What binds the calls instead:** the full-width binding of calls to windows is the R0/R1 chain,
    which is BLAKE3 receipts countersigned by the renter.
  - **What R3 adds:** that a continuous executed history of grain turns, in this order and this
    count, reaches the countersigned head. It does not add a 256-bit binding of each window's
    content.
  - The page states this. Widening it is the felt-width programme (`WOUND-felt-width-*`), not this
    lane.

## Refocus (2026-11-06, ember via root)

ember dropped "a stranger verifies it" as the bar: "if they care about our system they'll just run
it themselves; focus on features and functionality and maturity and performance". The
initiative is now three things:

1. SET_FIELD graduated properly into `CUTOVER_READY_SELECTORS`.
2. R3 holding over real multi-turn grain sessions on main (the threaded fold).
3. `cv hook receipt` working as a feature.

The microsite, the stranger-mintable VK rehearsal and the publication work are dropped. The
`grain-session` verifier stays as the end-to-end consumer of the ladder.

What the probes established on bb2 (debug test profile, workspace deps at opt-level 3):

- **Why SET_FIELD was refused.** `verify_descriptor_participant` refused every setField leg because
  SET_FIELD was not cutover-ready. Even the `#[ignore]`d single-turn `r3_grain_adapter` failed on
  main. Graduation is now done:
  - SET_FIELD is in the list.
  - Per-slot names resolve to it.
  - `every_setfield_slot_member_carries_exactly_one_selector_gate` covers all 8 slots in both
    registries.
  - The existing gate-alone forgery tooth still holds.
- **Threading the fold.** It needed three things:
  - one receipt context (`iroot`) for the whole session;
  - continued turns witnessed over the pre-cell with the model nonce and the turn-0 balance;
  - cumulative full-width cell witnesses per cohort run. A second grain turn witnessed over its
    untouched pre-cell fails fields-canonicity constraints #87-#93 and #118.
- **Two turns: 10 legs and 0 seam breaks** (the naive chaining breaks once).
  - Finalize takes about 18 s per leg.
  - The fold takes 454 s and produces a 799 KB aggregate.
  - Verification takes 0.43 s.
- **The head opens.** The aggregate's `final_root` equals the chip-faithful 8-felt commitment of
  the last ledger cell, under the session receipt context, with the model nonce and the turn-0
  balance. Of six candidates measured, it is the only one that matches.
