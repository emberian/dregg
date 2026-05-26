# Ignored Tests Audit

Audited: 2026-05-25  
Auditor: Sonnet audit+fix lane

## Summary Counts

| Metric | Count |
|---|---|
| `#[ignore]` count **before** audit | 162 |
| `#[cfg(any())]` disabled blocks | 3 (coord×2, demo-agent×1) |
| Bare `#[ignore]` (no reason string) fixed | 18 |
| `#[ignore]` count **after** audit | 160 (2 were in deleted file `apps/gallery/src/private_vickrey.rs`) |

---

## Classification Legend

- **SLOW** — test is structurally correct but generates real proofs; too slow for CI
- **FLAKY-FRI** — probabilistic: FRI sampling can miss a single tampered row on a short trace (task #90)
- **KNOWN-GAP** — precise structural gap documented with `REVIEW[gap-name]` tag
- **REAL-BUG-HIDDEN** — test would catch a genuine current bug if un-ignored
- **SUPERSEDED** — replaced by a different architecture; test is dead code
- **HISTORICAL-REMOVED** — module was deleted; test body is a stub or empty
- **FUTURE-LANE** — test is a future-state shape for a named workstream lane; body is `panic!("blocked")`

---

## Per-Test Table

### circuit/src/plonky3_prover.rs — 13 tests

| Line | Test name | Classification | Action |
|---|---|---|---|
| 657 | `plonky3_prove_verify_basic` | SLOW | Added reason string |
| 710 | `plonky3_prove_membership_end_to_end` | SLOW | Added reason string |
| 727 | `plonky3_depth_8` | SLOW | Added reason string |
| 740 | `plonky3_forged_parent_rejected` | SLOW+RELEASE-ONLY | Added reason string; release-only because debug prover panics |
| 879 | `plonky3_minimal_degree7_prove_verify` | SLOW | Added reason string |
| 906 | `plonky3_minimal_degree7_more_rows` | SLOW | Added reason string |
| 953 | `plonky3_mulair7_our_config` | SLOW | Added reason string |
| 1005 | `plonky3_minimal_degree2` | SLOW | Added reason string |
| 1030 | `plonky3_minimal_degree3` | SLOW | Added reason string |
| 1055 | `plonky3_minimal_degree4` | SLOW | Added reason string |
| 1072 | `plonky3_minimal_degree5` | SLOW | Added reason string |
| 1089 | `plonky3_minimal_degree6` | SLOW | Added reason string |
| 1106 | `plonky3_non_power_of_2_depth` | SLOW | Added reason string |

Note: `plonky3_forged_parent_rejected` is a **soundness test** — it verifies the Poseidon2 inline constraint rejects a forged parent hash. It should be run in release CI or as a manual soundness gate.

### circuit/src/plonky3_recursion.rs — 3 tests

| Line | Test name | Classification | Action |
|---|---|---|---|
| 335 | `recursive_proof_two_proofs` | SLOW | Added reason string |
| 356 | `recursive_proof_four_proofs` | SLOW | Added reason string |
| 379 | `aggregate_pair_works` | SLOW | Added reason string |

### circuit/src/poseidon2_air.rs — 1 test

| Line | Test name | Classification | Action |
|---|---|---|---|
| 1102 | `merkle_poseidon2_forged_proof_with_wrong_hash_fails_stark` | SLOW | Added reason string; this is a soundness test |

### circuit/src/backends/plonky3.rs — 1 test

| Line | Test name | Classification | Action |
|---|---|---|---|
| 1506 | `membership_prove_verify_plonky3` | SLOW | Upgraded inline comment to full reason string |

### circuit/src/backends/mina/tests.rs — 1 test

| Line | Test name | Classification | Action |
|---|---|---|---|
| 560 | `test_standalone_recursive_step_end_to_end` | SUPERSEDED | Already has `REVIEW` reason: "SUPERSEDED by dual-curve Step/Wrap architecture" — no change needed |

### circuit/src/effect_vm/tests.rs — 9 tests

All in the `FLAKY-FRI` or `KNOWN-GAP` category. Reason strings are already present.

| Line | Test name | Classification | Gap tag |
|---|---|---|---|
| 258 | `test_wrong_state_transition_stark_rejects` | FLAKY-FRI | `REVIEW[fri-single-row-gap]` — task #90 |
| 1368 | `test_create_obligation_wrong_amount_caught` | FLAKY-FRI | `REVIEW[stage2-fri-single-row-gap]` |
| 1396 | `test_fulfill_obligation_wrong_return_caught` | FLAKY-FRI | `REVIEW[stage2-fri-single-row-gap]` |
| 1707 | `test_captp_export_tampered_swiss_caught` | FLAKY-FRI | "flaky: relies on FRI sampling" |
| 1751 | `test_soundness_non_boolean_delta_sign_rejected` | FLAKY-FRI | `REVIEW[fri-single-row-gap]` — ~8% miss rate |
| 2538 | `test_soundness_p0_1_net_delta_sign_flip_rejected` | FLAKY-FRI | `REVIEW[stage2-fri-single-row-gap]` |
| 2563 | `test_soundness_p0_1_net_delta_magnitude_lie_rejected` | FLAKY-FRI | `REVIEW[stage2-fri-single-row-gap]` |

**REAL-BUG-HIDDEN**: These 7+ tests (especially `test_soundness_non_boolean_delta_sign_rejected`) expose the FRI single-row gap. The AIR constraint IS algebraically correct; the soundness gap is in the FRI parameter config (80 queries / blowup-4 / 8-row trace → ~8% miss rate per run). The fix is: increase minimum trace size to ≥64 rows OR widen FRI query count. Tracked as task #90.

### circuit/tests/sovereign_transition.rs — 1 test

| Line | Test name | Classification | Action |
|---|---|---|---|
| 7 | `sovereign_transition_tests_disabled` | HISTORICAL-REMOVED | Module `sovereign_transition_air` was deleted in favor of EffectVmAir; stub test; no change needed |

### circuit/tests/state_constraint_air_teeth.rs — 6 tests

All `FUTURE-LANE` (KNOWN-GAP with clear blocker):

| Line | Test name | Classification | Blocker |
|---|---|---|---|
| 377 | `monotonic_accepts_non_decrease` | FUTURE-LANE | 32-byte AIR state (Block 3 second wave) |
| 386 | `strict_monotonic_rejects_equal` | FUTURE-LANE | Same as above |
| 390 | `sender_authorized_accepts_member` | FUTURE-LANE | Merkle-membership gadget |
| 394 | `sender_authorized_blinded_accepts_non_revoked` | FUTURE-LANE | Non-revocation accumulator AIR |
| 398 | `allowed_transitions_accepts_listed_pair` | FUTURE-LANE | Merkle-membership of (old,new) tuple |
| 402 | `field_gte_accepts_greater_or_equal` | FUTURE-LANE | 32-byte AIR state |

### commit/src/poseidon2_tree.rs — 1 test

| Line | Test name | Classification | Action |
|---|---|---|---|
| 544 | `end_to_end_note_spending_stark_from_real_tree` | KNOWN-GAP | `REVIEW[stage2-canonical-vs-poseidon-mismatch]` — already documented |

### dregg-dsl-tests/src/sovereign_transition_dsl.rs — 1 test

| Line | Test name | Classification | Action |
|---|---|---|---|
| 352 | `dsl_matches_handwritten_air` | HISTORICAL-REMOVED | Module removed; stub body; no change |

### turn/src/tests.rs — 3 tests

All `KNOWN-GAP[stage2-canonical-vs-poseidon-mismatch]` — trace gen uses Poseidon2 commitment hash, verifier path uses Blake3 canonical hash; the two are not byte-identical.

| Line | Test name | Classification | Gap |
|---|---|---|---|
| 7802 | `test_proof_carrying_turn_accepted` | REAL-BUG-HIDDEN | canonical-vs-poseidon mismatch (alignment work needed) |
| 7904 | `test_proof_carrying_turn_wrong_effects_hash` | REAL-BUG-HIDDEN | same gap |
| 8307 | `test_default_air_still_works_without_vk_hash` | REAL-BUG-HIDDEN | same gap |

**Task: canonical-vs-poseidon-mismatch** — Align `generate_valid_sovereign_proof_with_new_commit` so the 4-felt commitment form matches the in-AIR state encoding that `canonical_32_to_felts_4` produces. Two options: (a) trace gen accepts Cell-canonical 4-felt form as input; (b) verifier recomputes `compute_commitment_4` from cell state rather than calling `canonical_32_to_felts_4`. Multi-file Stage 2 work.

### teasting/tests/revocation_propagation.rs — 1 test

| Line | Test name | Classification | Action |
|---|---|---|---|
| 98 | `test_revocation_after_recovery` | REAL-BUG-HIDDEN | "TODO: implement state sync for recovered nodes" — assertions are commented out, confirms the feature is genuinely unimplemented |

**Task: state-sync-after-recovery** — `crash_node`/`recover_node` exist in the harness but recovered nodes do not replay missed blocks. After recovery, the node should sync revocations that occurred while it was down. The test body is ready (assertions commented out); unblock by implementing the state sync protocol in the federation harness.

### teasting/tests/bridge_four_phase_extended.rs — 3 tests

| Line | Test name | Classification | Blocker |
|---|---|---|---|
| 347 | `refund_releases_pending_set_for_re_lock` | REAL-BUG-HIDDEN | `PendingBridgeSet::clear_after_refund` API missing; the pending set is not coupled to the phase log Refunded admission |
| 387 | `cross_federation_transfer_binds_transfer_id_and_bridge_id_jointly` | FUTURE-LANE | γ.2 Phase 1 + bridge phase log composition |
| 397 | `bridge_phase3_finalize_produces_federation_receipt_with_bridge_id` | FUTURE-LANE | `FederationReceipt` not wired into bridge path (AUDIT-federation.md F7) |

**Task: pending-bridge-set-refund-api** — After a Phase-4 Refund, the pending bridge lock must be released so the same nullifier can be re-bridged. Design `PendingBridgeSet::clear_after_refund` and couple it to the phase log `Refunded` admission path.

### tests/src/executor_honesty_threats.rs — 22 tests

All `FUTURE-LANE` blocked on specific `EXECUTOR-HONESTY-AUDIT.md` threats (T1–T13) and Stage 7 cont. PIcking the most critical:

| Line | Test name | Gap |
|---|---|---|
| 108 | `reordered_effects_proof_rejected` | T1: EFFECTS_HASH_BASE row-0 boundary constraint |
| 141 | `unchecked_authorization_not_reachable_from_verify_path` | T2: verify path is THE ONLY way into TurnExecutor |
| 151 | `omitted_effect_breaks_hash_chain` | T1 termination: EFFECTS_HASH_GLOBAL must terminate |
| 204 | `wrong_pre_state_proof_rejected` | T4: STATE_BEFORE_BASE row-0 AIR boundary |
| 214 | `action_signed_for_wrong_federation_rejected` | T6: canonical signing message must include federation_id |

### tests/src/sovereign_witness_threats.rs — 20 tests

All `FUTURE-LANE` blocked on `SOVEREIGN-WITNESS-AIR-DESIGN.md` Phase 1 teeth. Most critical:

| Line | Test name | Gap |
|---|---|---|
| 25 | `sovereign_witness_tampered_key_rejects` | AIR does not yet algebraically constrain sovereign witness |
| 51 | `turn_against_sovereign_cell_without_witness_rejected` | T9: no-witness must reject |
| 109 | `sovereign_witness_cross_cell_reuse_rejected` | AIR-side: witness for cell A on turn for cell B |

### tests/src/gamma2_bilateral_binding.rs — 20 tests

All `FUTURE-LANE` blocked on γ.2 Phase 1/2 wiring. Most critical:

| Line | Test name | Gap |
|---|---|---|
| 154 | `transfer_bilateral_binding_roundtrip` | γ.2 Phase 1 PI extension: transfer_id at canonical PI offset |
| 168 | `bilateral_amount_mismatch_rejected` | off-AIR verifier joins sender + receiver |
| 176 | `bilateral_transfer_id_tamper_rejected` | AIR-side binding of transfer_id |
| 355 | `direction_bit_both_claim_outflow_rejected` | γ.2 direction_bit consistency check |

### tests/src/witnessed_predicate_kinds.rs — 19 tests

All `FUTURE-LANE` blocked on `WitnessedPredicateRegistry` dispatch (CAVEAT-LAYER-COVERAGE.md §5, §6.6). Every kind — Dfa, Temporal, MerklePoseidon2, BlindedSet, Predicate, Bridge, Pedersen, Custom — lacks registry dispatch wiring.

### tests/src/state_constraint_variants.rs — 18 tests

All `FUTURE-LANE` blocked on caveat-correctness lane. Key gaps: BlindedSet non-revocation, sender_epoch_count plumbing, Poseidon2 PreimageGate stub, TemporalPredicate dispatch, BoundDelta peer-mismatch, DFA registry.

### tests/src/state_constraint_executor.rs — 7 tests

All `FUTURE-LANE` blocked on caveat-correctness lane. Key gaps: `sender_epoch_count` in `EvalContext`, `revealed_preimage` from `action.witness_blobs`, MerkleMembership via `WitnessedPredicateRegistry`.

### tests/src/state_constraint_composition.rs — 7 tests

All `FUTURE-LANE` blocked on caveat-correctness + γ.2 + sovereign witness composition.

### tests/src/authorization_variants.rs — 8 tests

All `FUTURE-LANE` blocked on `AUTHORIZATION-CUSTOM-DESIGN` (Auth::Custom predicate dispatch, federation_id binding audit).

### tests/src/slot_caveat_composition_stress.rs — 3 tests

| Line | Test name | Classification | Blocker |
|---|---|---|---|
| 444 | `cases_with_compound_transition_guards` | REAL-BUG-HIDDEN | `TransitionGuard::SlotChanged` needs old+new state visible to guard matcher — currently uses `TransitionMeta` only |
| 508 | `sentinel_variant_inside_long_conjunction_accepts_when_witness_verifies` | FUTURE-LANE | INVERTED form: unblock when caveat-correctness lane lands |
| 518 | `all_21_state_constraint_variants_declared_and_satisfied` | FUTURE-LANE | caveat-correctness lane full conjunction |

**Task: transition-guard-slot-changed** — `TransitionGuard::SlotChanged { index }` calls `matches()` using only `TransitionMeta`. The guard needs the old and new `CellState` to compare slot values. Wire the full state plumb-through into the guard matcher.

### tests/src/every_variant_roundtrip.rs — 2 tests

| Line | Test name | Classification | Blocker |
|---|---|---|---|
| 851 | `every_effect_variant_round_trips_through_projection` | REAL-BUG-HIDDEN | 31 of 41 effect variants project to `VmEffect::NoOp` (projection is lossy) |
| 901 | `every_effect_variant_has_provable_air` | REAL-BUG-HIDDEN | per-variant AIRs not yet landed (EFFECT-VM-SHAPE-A Stages 3-6) |

**Task: effect-vm-shape-a-projection** — `AgentCipherclerk::convert_effects_to_vm` collapses 31/41 effect variants to `VmEffect::NoOp`. Each effect kind needs a real projection into typed `VmEffect` variants. Block: EFFECT-VM-SHAPE-A Stages 3-6.

### coord/src/tests.rs — 2 `#[cfg(any())]` blocks

| Lines | Test name | Classification | Reason |
|---|---|---|---|
| 1394 | `many_node_causal_dag` | HISTORICAL-REMOVED | `CausalLedger`/`CausalTurn` removed from `dregg_coord::causal`; needs port to new causal surface (causal-test-port lane) |
| 1446 | `rejected_turn_still_in_dag` | HISTORICAL-REMOVED | Same reason |

### demo-agent/examples/unified_harness.rs — 1 `#[cfg(any())]`

| Lines | Item | Classification | Reason |
|---|---|---|---|
| 1110 | `run_federation_bootstrap` | HISTORICAL-REMOVED | API drift: `Federation::new` no longer accepts `&[&str]`; needs port to `verifier_only(members, epoch, threshold)` |

---

## Tasks for REAL-BUG-HIDDEN Tests (not yet fixed)

### TASK-1: `fri-single-row-gap` — FRI soundness on short traces (task #90)
**File:** `circuit/src/effect_vm/tests.rs`, lines 258, 1368, 1396, 1707, 1751, 2538, 2563  
**Nature:** FRI probabilistic sampling can miss a single tampered row on a 2–8 row trace. ~8% miss rate per run on a 2-row trace with 80 queries/blowup-4. The AIR constraints ARE algebraically correct. The gap is the FRI parameter config.  
**Fix:** Increase minimum trace length to ≥64 rows OR increase FRI query count in `create_config()`. After fix, remove ignores and let tests run.

### TASK-2: `stage2-canonical-vs-poseidon-mismatch` — commitment hash misalignment
**File:** `turn/src/tests.rs` lines 7802, 7904, 8307; `commit/src/poseidon2_tree.rs` line 544  
**Nature:** Trace generation produces a Poseidon2-based commitment; the verifier path calls `canonical_32_to_felts_4` on the stored Blake3 commitment. The two 4-felt representations differ. Proof-carrying turns fail because `new_commitment` from trace ≠ stored commitment encoding.  
**Fix:** Either (a) trace gen accepts Cell-canonical 4-felt form as input, embedding it in the continuity column, OR (b) verifier recomputes `compute_commitment_4` from cell state instead of `canonical_32_to_felts_4`. Multi-file Stage 2 alignment work.

### TASK-3: `state-sync-after-recovery` — revocation propagation to recovered nodes
**File:** `teasting/tests/revocation_propagation.rs` line 98  
**Nature:** `test_revocation_after_recovery` confirms that nodes do NOT currently sync revocations that occurred while they were crashed. The test asserts are commented out because the sync protocol is missing.  
**Fix:** Implement block-replay state sync in the federation harness's `recover_node` path.

### TASK-4: `pending-bridge-set-refund-api` — PendingBridgeSet not coupled to phase log
**File:** `teasting/tests/bridge_four_phase_extended.rs` line 347  
**Nature:** After a Phase-4 Refund, the `PendingBridgeSet` lock persists because there is no `clear_after_refund` API. A re-bridge attempt after refund would hit `AlreadyBridged`.  
**Fix:** Add `PendingBridgeSet::clear_after_refund(bridge_id)`, wire it to the phase log `Refunded` admission path.

### TASK-5: `transition-guard-slot-changed` — guard matcher missing state plumb-through
**File:** `tests/src/slot_caveat_composition_stress.rs` line 444  
**Nature:** `TransitionGuard::SlotChanged { index }` in `matches()` receives only `TransitionMeta` — no old/new `CellState`. The guard can never fire correctly. Executor-side test confirms this structural gap.  
**Fix:** Thread the old and new `CellState` references into the `matches()` call or a new `matches_with_state()` variant.

### TASK-6: `effect-vm-shape-a-projection` — 31/41 effect variants collapse to NoOp
**File:** `tests/src/every_variant_roundtrip.rs` lines 851, 901  
**Nature:** `AgentCipherclerk::convert_effects_to_vm` maps the majority of effect variants to `VmEffect::NoOp`. Any turn exercising those effects produces no provable constraint. EFFECT-VM-SHAPE-A Stages 3-6 are the named workstream.  
**Fix:** Implement per-variant projections from `dregg_turn::Effect` to `dregg_circuit::effect_vm::Effect` variants for all non-NoOp cases.

---

## Pattern Observations

1. **Largest cluster: caveat-correctness lane** — ~100 tests across `tests/src/` are blocked on the caveat-correctness workstream (registry dispatch, `WitnessedPredicateRegistry`, `EvalContext` plumbing). This is the single biggest source of ignored tests.

2. **Second cluster: FRI single-row gap** — 7 tests in `circuit/src/effect_vm/tests.rs` are probabilistically flaky due to FRI sampling on short traces. Same root cause as task #90. These are the only tests that are probabilistically (not deterministically) ignoring real bugs.

3. **Third cluster: stage2-canonical-vs-poseidon-mismatch** — 4 tests blocked on commitment hash format mismatch between trace gen and verifier path. Structural 2-file fix.

4. **Circuit prover SLOW tests** — 18 tests (plonky3_prover ×13, plonky3_recursion ×3, poseidon2_air ×1, backends/plonky3 ×1) had bare `#[ignore]` with no reason. All were structurally sound proof-generation tests ignored purely for speed. All now have reason strings. These should be wired into a weekly/release CI job.

5. **Historical stubs cluster** — `sovereign_transition.rs`, `dregg-dsl-tests/sovereign_transition_dsl.rs`, `coord/src/tests.rs` (×2), `demo-agent/unified_harness.rs` all have dead tests from removed modules. The `#[cfg(any())]` pattern (coord, demo-agent) is more honest than `#[ignore]` for truly dead code.

6. **No ignore is older than the last major refactor** — the git log shows ignores were introduced alongside the active workstream lanes (stage2, caveat-correctness, γ.2, sovereign-witness, bridge), not as technical debt from 2+ years ago. The cluster pattern exactly mirrors the Silver Vision workstream decomposition.

---

## Top 5 Most Concerning REAL-BUG-HIDDEN Tests

1. **`test_soundness_non_boolean_delta_sign_rejected`** (`circuit/src/effect_vm/tests.rs:1751`) — A prover can set `net_delta_sign = 2` (non-boolean). The AIR constraint `sign*(sign-1)==0` should reject this, but with an 8% miss rate per CI run. Any deployment using a 2-row trace for single-Transfer turns exposes this soundness gap.

2. **`test_proof_carrying_turn_accepted`** (`turn/src/tests.rs:7802`) — The happy-path proof-carrying turn test does NOT pass. This means sovereign cells cannot actually be proven in the current executor: trace gen and verifier produce incompatible commitment encodings.

3. **`every_effect_variant_round_trips_through_projection`** (`tests/src/every_variant_roundtrip.rs:851`) — 31 of 41 effect variants produce `VmEffect::NoOp` projections. Turns exercising those effects carry no cryptographic constraint at all.

4. **`cases_with_compound_transition_guards`** (`tests/src/slot_caveat_composition_stress.rs:444`) — `TransitionGuard::SlotChanged` is permanently false because the guard matcher lacks old/new state access. Any cell program relying on `SlotChanged` guards is silently misconfigured.

5. **`test_revocation_after_recovery`** (`teasting/tests/revocation_propagation.rs:98`) — Nodes that crash and recover do NOT sync revocations from while they were down. A recovered node believes a revoked token is still valid.

## Top 5 Stalest HISTORICAL-NO-LONGER-RELEVANT Removals

1. `circuit/tests/sovereign_transition.rs:7` — `sovereign_transition_air` module removed; entire test file is one empty stub. Safe to delete the file.
2. `dregg-dsl-tests/src/sovereign_transition_dsl.rs:352` — `dsl_matches_handwritten_air` stub with empty body; module removed.
3. `coord/src/tests.rs:1394` (`many_node_causal_dag`) — `CausalLedger`/`CausalTurn` removed; `#[cfg(any())]` correctly gates it.
4. `coord/src/tests.rs:1446` (`rejected_turn_still_in_dag`) — same removal event.
5. `demo-agent/examples/unified_harness.rs:1110` (`run_federation_bootstrap`) — `Federation::new` API changed; `#[cfg(any())]` correctly gates it.
