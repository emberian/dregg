# Circuit / Verifier Test Audit

Date: 2026-05-25
Files surveyed: `circuit/src/effect_vm/tests.rs` (3 369 LOC),
`circuit/src/soundness_tests.rs`, `circuit/src/tests.rs`,
`verifier/src/lib.rs` (in-file tests), `verifier/tests/integration.rs`,
`verifier/tests/bilateral_pair_demo.rs`, `verifier/tests/utilities.rs`,
and all four existing `circuit/tests/*.rs` integration files.

---

## Test-category inventory

### Real (prove-then-verify or forged-proof-rejected)

These tests exercise the full `stark::prove` → `stark::verify` pipeline,
or call `verify_effect_vm_proof` / `replay_chain` with real proof bytes.

| File | Test | Notes |
|------|------|-------|
| `effect_vm/tests.rs` | `test_single_transfer_outgoing` | prove+verify, checks delta |
| `effect_vm/tests.rs` | `test_single_transfer_incoming` | prove+verify |
| `effect_vm/tests.rs` | `test_multi_effect_turn` | prove+verify |
| `effect_vm/tests.rs` | `test_wrong_state_transition_caught` | AIR-level check + FRI (see gap note) |
| `effect_vm/tests.rs` | `test_invalid_selector_two_active_caught` | prove → verify must error |
| `effect_vm/tests.rs` | `test_nonce_gap_caught` | prove → verify must error |
| `effect_vm/tests.rs` | `test_conservation_violation_caught` | PI tamper → reject |
| `effect_vm/tests.rs` | `test_note_spend_and_create` | prove+verify |
| `effect_vm/tests.rs` | `test_stage3_multi_variant_compose` | 23-effect turn, prove+verify |
| `effect_vm/tests.rs` | `test_balance_debit_variants_verify` | CreateEscrow, BridgeLock |
| `effect_vm/tests.rs` | `test_passthrough_variants_verify` | CreateSealPair, RefreshDelegation, RevokeDelegation |
| `effect_vm/tests.rs` | `test_four_effect_stark_roundtrip` | prove+verify |
| `effect_vm/tests.rs` | `test_integration_real_multi_effect_turn` | prove+verify + commitment check |
| `effect_vm/tests.rs` | `test_integration_obligation_lifecycle` | prove+verify |
| `effect_vm/tests.rs` | `test_ivc_compression_sequential_turns` | `prove_ivc_stark` + `verify_ivc_stark` |
| `effect_vm/tests.rs` | `test_noop_state_commitment_tamper_caught` | prove → verify must error |
| `effect_vm/tests.rs` | `test_integration_8_effect_sovereign_turn` | prove+verify |
| `effect_vm/tests.rs` | `test_commitment_chain_continuity` | 3-turn chain, each proven |
| `effect_vm/tests.rs` | `test_effects_hash_prevents_subset_attack` | PI tamper → reject |
| `effect_vm/tests.rs` | `test_proof_size_measurement` | prove+serialise+deserialise+verify |
| `effect_vm/tests.rs` | `test_captp_export_sturdy_ref` | roundtrip helper (prove+verify) |
| `effect_vm/tests.rs` | `test_captp_enliven_ref` | roundtrip |
| `effect_vm/tests.rs` | `test_captp_drop_ref` | roundtrip |
| `effect_vm/tests.rs` | `test_captp_multi_effect_turn` | prove+verify |
| `effect_vm/tests.rs` | `test_storage_allocate_queue` | roundtrip |
| `effect_vm/tests.rs` | `test_storage_enqueue_message` | roundtrip |
| `effect_vm/tests.rs` | `test_storage_dequeue_message` | roundtrip |
| `effect_vm/tests.rs` | `test_storage_multi_effect_queue_lifecycle` | roundtrip |
| `effect_vm/tests.rs` | `test_storage_resize_queue` | roundtrip |
| `effect_vm/tests.rs` | `test_enqueue_with_program_validation_stark_roundtrip` | prove+verify |
| `effect_vm/tests.rs` | `test_storage_atomic_queue_tx` | roundtrip |
| `effect_vm/tests.rs` | `test_storage_pipeline_step` | roundtrip |
| `effect_vm/tests.rs` | `test_storage_pipeline_step_wrong_pipeline_id_fails` | PI tamper → reject |
| `effect_vm/tests.rs` | `test_sovereign_cell_enqueue_with_proof_verifies` | roundtrip |
| `effect_vm/tests.rs` | `test_sovereign_cell_atomic_tx_with_deposits_verifies` | roundtrip |
| `effect_vm/tests.rs` | all `test_soundness_p0_*` tests | PI/balance tampers → reject |
| `effect_vm/tests.rs` | `test_stage2_*` adversarial tests | AIR-level constraint rejection |
| `effect_vm/tests.rs` | `test_stage7_actor_nonce_*` | prove+verify / reject |
| `effect_vm/tests.rs` | `test_captp_adversarial_tamper_cases` | AIR-level rejection (eval_constraints) |
| `effect_vm/tests.rs` | `test_captp_validate_handoff_adversarial_*` | AIR-level rejection |
| `soundness_tests.rs` | `poseidon2_air_wrong_output_bit_flip_rejected` | prove → verify must error |
| `verifier/tests/integration.rs` | `test_verify_known_good_proof_accepted` | verify via verifier crate |
| `verifier/tests/integration.rs` | `test_verify_tampered_proof_rejected` | byte-flip → reject |
| `verifier/tests/integration.rs` | `test_verify_wrong_pi_rejected` | PI tamper → reject |
| `verifier/tests/integration.rs` | `test_canonical_vk_hash_accepted` | VK hash path |
| `verifier/tests/integration.rs` | `test_verify_multi_effect_turn_accepted` | multi-effect |
| `verifier/src/lib.rs` (in-file) | `pi_binding_rejects_tampered_turn_hash` | check_receipt_pi_binding |
| `verifier/src/lib.rs` (in-file) | `pi_binding_rejects_tampered_previous_receipt_hash` | |
| `verifier/src/lib.rs` (in-file) | `pi_binding_rejects_tampered_is_agent_cell` | |
| `verifier/src/lib.rs` (in-file) | `pi_binding_rejects_chain_walk_break` | |
| `verifier/src/lib.rs` (in-file) | `replay_chain_detects_witness_hash_tamper` | |

### Trace-only (witness built, no proof)

Tests that construct a trace and call `eval_constraints` directly but
never call `stark::prove` / `stark::verify`.

| File | Test | Gap |
|------|------|-----|
| `effect_vm/tests.rs` | `test_setfield_correct` | calls `eval_constraints` only |
| `effect_vm/tests.rs` | `test_single_row_constraint_eval` | calls `eval_constraints` only |
| `effect_vm/tests.rs` | `test_constraint_evaluation_all_zeros_valid_trace` | eval only |
| `effect_vm/tests.rs` | `test_interior_noop_state_change_caught` | eval only (intentional — FRI gap) |
| `effect_vm/tests.rs` | `test_basic_effect_constraints` | uses `assert_single_effect_roundtrip` (does prove+verify) — **actually Real** |
| `effect_vm/tests.rs` | `test_padding_rows_valid` | trace shape only |
| `effect_vm/tests.rs` | `test_stage2_reserved_bit_decomposition_tamper_rejected` | eval only |
| `effect_vm/tests.rs` | `test_stage2_create_obligation_beneficiary_tamper_rejected` | eval only |
| `effect_vm/tests.rs` | `test_stage2_make_sovereign_double_transition_rejected` | eval only |
| `effect_vm/tests.rs` | `test_stage2_resize_queue_*` | eval only |
| `effect_vm/tests.rs` | `test_stage2_setfield_on_sealed_field_rejected` | eval only |
| `effect_vm/tests.rs` | `test_storage_atomic_queue_tx_tampered_new_root_fails` | eval only |
| `effect_vm/tests.rs` | `test_enqueue_program_invalid_validation_hash_fails` | eval only |
| `circuit/tests/state_constraint_air_teeth.rs` | all | PI-layer only; no STARK |

### Schema-only / hash-comparison (no proving)

| File | Test |
|------|------|
| `effect_vm/tests.rs` | `test_noop_padding_cannot_be_exploited` | hash comparison |
| `effect_vm/tests.rs` | `test_effect_reordering_detected` | hash comparison |
| `effect_vm/tests.rs` | `test_soundness_wrapped_balance_different_commitment` | commitment comparison |
| `circuit/tests/value_truncation_fix.rs` | `value_limbs_roundtrip_full_u64_range` | limb math |
| `circuit/tests/value_truncation_fix.rs` | `high_bit_distinct_values_produce_distinct_pi_limbs` | PI comparison |

### Mock / stub verifiers

None found in the surveyed files.  The in-file `verifier/src/lib.rs` tests
call `replay_chain` with structurally empty proof bytes (empty `Vec<u8>`) for
negative-path tests — this is intentional and not a mock, because the empty
bytes exercise the "STARK verify fails → Rejected" branch at step 1.

### Tautology (compute twice, compare)

| File | Test | Issue |
|------|------|-------|
| `verifier/src/lib.rs` | `pi_binding_accepts_consistent_pi` | Calls `entry_with_pi_from_receipt` which builds PI *from* the receipt and then checks the PI matches the receipt. It is a round-trip identity, not an adversarial test. Structurally sound but not adversarial. |

---

## Issues / FIXME inventory

### `#[ignore]` with explicit reason (acceptable)

- `test_create_obligation_wrong_amount_caught` — `REVIEW[stage2-fri-single-row-gap]`
- `test_fulfill_obligation_wrong_return_caught` — same reason
- `test_soundness_non_boolean_delta_sign_rejected` — same reason
- `test_captp_export_tampered_swiss_caught` — same reason

All four share a documented reason (FRI single-row gap on small 2-row traces).
The reason is valid and the AIR-level correctness is separately verified.

### `assert!(result.is_ok())` without inspecting the result

Throughout `tests.rs` many tests end with:
```rust
assert!(result.is_ok(), "...: {:?}", result.err());
```
This pattern is fine — the error type is printed in the failure message. No
blind `assert!(result.is_ok())` calls found.

### `// FIXME` near assertions

One found: `test_wrong_state_transition_caught` (lines 177-256 in `tests.rs`).
The comment reads: `REVIEW[stage2-fri-single-row-gap]` and explicitly documents
that the STARK may not reject a single-row tamper on a small trace. The
assertion is guarded: the test neither asserts `is_err()` blindly nor ignores
the result; it emits an `eprintln!` if the STARK accepts. This is a documented
gap, not a silent bug.

### In `soundness_tests.rs`

`poseidon2_air_wrong_output_bit_flip_rejected`: calls `prove` on a tampered
trace and asserts `is_err()`. Structurally correct. However, `bad_pi = bad_trace[0].clone()`
(line 60) — the public inputs are derived from the *tampered* trace row, so
the proof is generated with a consistent (tampered) PI. This means the test
verifies that the tampered trace+PI combination fails STARK verification, which
is correct. Not a bug.

### `verifier/src/lib.rs` — tautology in `pi_binding_accepts_consistent_pi`

`entry_with_pi_from_receipt` constructs a PI vector by reading exactly the
same fields it will later check. While not wrong (it confirms the helper
doesn't silently zero-out fields), it does not exercise an adversary.  A
supplementary test that independently builds the PI from the receipt fields
would be more convincing.

### Missing coverage areas before this audit

1. No integration test exercised `replay_chain` with a **real STARK proof** —
   all existing `replay_chain` tests in `verifier/src/lib.rs` use empty proof
   bytes that fail at scope-1 before reaching scope-2.
2. No test verified `verify_effect_vm_proof` with **corrupted FRI bytes** on a
   multi-effect (> 2-row) trace.
3. The `non_membership` / `NonMembershipProver` API had no end-to-end
   prove+verify test in any test file.
4. No IVC test for 3+ steps.
5. No test for the serialisation round-trip (prove → `proof_to_bytes` →
   `proof_from_bytes` → verify) in the external integration test suite.

---

## New test files added

| File | Tests | Category |
|------|-------|----------|
| `circuit/tests/common/mod.rs` | shared helpers | — |
| `circuit/tests/integration_effect_vm_prove_verify.rs` | 7 | Real |
| `circuit/tests/integration_recursive_chain.rs` | 5 | Real (IVC) |
| `verifier/tests/integration_forged_proofs.rs` | 14 | Real (forged-proof rejection) |
| `verifier/tests/integration_non_membership.rs` | 7 | Real (non-membership) |
| `verifier/tests/integration_replay_chain.rs` | 7 | Real (replay chain) |

**Total new tests: 40**

### Notable additions

- `all_schema_variants_prove_and_verify` sweeps every named `Effect` variant
  through `prove+verify` individually — closes the gap where variants existed
  in the source but were only covered by the `stage3_multi_variant_compose`
  bulk test.
- `commitment_chain_three_turns_verifies_and_swap_detected` adds the
  proof-swap adversarial angle (absent from the existing commitment-chain test).
- `net_delta_pi_forgery_rejected_end_to_end` upgrades three existing
  hash-comparison-only tests to full STARK rejections.
- `single_entry_real_proof_verifies` and `two_entry_chain_with_correct_link_verifies`
  are the first `replay_chain` tests that use a genuine STARK proof (not empty
  bytes) at scope-1.
- `scope2_tampered_trace_row_rejected_by_constraint_walk` exercises the
  scope-2 row-walk path in `replay_one_with_prev` with a valid scope-1 proof
  and a corrupted witness bundle.
- `multi_effect_pi_tamper_battery` runs 7 PI-slot tamper cases on a single
  multi-effect proof with one call to `make_proof_and_pi`.
