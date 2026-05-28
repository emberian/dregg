# Cell / Turn Test Audit

Audit date: 2026-05-25. Scope: `cell/src/tests.rs`, `cell/src/lifecycle.rs` (inline tests),
`cell/tests/proptest_nullifier.rs`, `turn/src/tests.rs`, `turn/tests/proptest_invariants.rs`,
`turn/tests/witnessed_predicate_dispatch.rs`.

---

## Seeming Tests Identified

A "seeming test" is one that validates structure, not behaviour: it exercises
the test framework, round-trips bytes, or asserts things that cannot falsify
the invariant it names.

| # | File | Function | Classification | Issue |
|---|------|----------|----------------|-------|
| 1 | `cell/src/tests.rs` | `cell_id_derive_deterministic` | Serialization round-trip | Calls `derive_raw` twice with the same inputs and asserts equality. Falsifies nothing about the semantic content of the ID. |
| 2 | `cell/src/tests.rs` | `cell_id_display_debug` | Vacuous / structural | Asserts `!display.is_empty()` and `debug.contains("CellId(")` — tests the test framework's Display impl, not any semantic behaviour. |
| 3 | `cell/src/tests.rs` | `cell_id_zero_is_zero` | Trivial constant check | Asserts `ZERO.as_bytes() == [0; 32]`. This is a constant equality on a hard-coded value. Cannot fail unless the constant is edited. |
| 4 | `cell/src/tests.rs` | `ledger_root_deterministic` | Round-trip without adversarial case | Two ledgers built identically have the same root. No adversarial case (e.g. different insertion order, interleaved creates/removes) verifying the root *differs* when operations differ. |
| 5 | `cell/src/lifecycle.rs` (inline) | `death_certificate_hash_is_deterministic` | Serialization round-trip | Calls `certificate_hash()` twice on the same struct. Falsifies nothing about the hash content. |
| 6 | `cell/src/lifecycle.rs` (inline) | `discriminants_are_distinct` | Structural / meta-test | Tests that an ad-hoc switch statement assigns different constants. The real question (does the commitment path branch on discriminant?) is not tested. |
| 7 | `turn/src/tests.rs` | `test_simple_set_field` | Happy-path only | No adversarial case: what happens if the field index is out of bounds? If the cell is Sealed? These are missing counterparts. |
| 8 | `turn/src/tests.rs` (lines 10800–11130) | Burn / lifecycle adversarial block | Partially real, but lives in the internal `src/tests.rs` module | Good adversarial content, but uses `new_unchecked_for_tests` and `TurnBuilder` from inside the crate. No external integration test verifies these from the crate boundary. |
| 9 | `turn/tests/witnessed_predicate_dispatch.rs` | All tests | Real but registry-only | Tests the registry dispatch surface correctly, but no test submits a full turn that evaluates a witnessed precondition end-to-end (executor → predicate registry → commit/reject). |
| 10 | `turn/tests/proptest_invariants.rs` | `proptest_delegation_snapshot_correctness` | Partially structural | The `revoke_before_refresh` arm verifies `child.delegation.is_none()` after revocation but never attempts to exercise the revoked child delegation (which should be rejected). The adversarial path is asserted but not exercised. |

**Total seeming tests identified: 10**

---

## New Integration Tests Added

All new files live in `turn/tests/` or `cell/tests/` (external integration test crates,
not appended to any existing module).

### `turn/tests/integration_lifecycle.rs` (8 tests)

| Test | What it covers | Adversarial? |
|------|----------------|--------------|
| `lifecycle_seal_transitions_to_sealed` | Full turn → executor → lifecycle == Sealed, reason_hash bound | Happy path |
| `lifecycle_post_seal_effect_rejected` | SetField on Sealed cell rejected, field unchanged | Adversarial |
| `lifecycle_seal_then_unseal_restores_live` | Seal → Unseal roundtrip; effects accepted again | Happy path |
| `lifecycle_unseal_of_live_cell_rejected` | Unseal on Live cell rejected | Adversarial |
| `lifecycle_destroy_with_certificate_then_terminal` | Destroy with valid cert; subsequent SetField rejected | Happy + adversarial |
| `lifecycle_destroy_certificate_mismatch_rejected` | Wrong cell_id in cert → reject, still Live | Adversarial |
| `lifecycle_double_seal_rejected` | Second seal rejected; original reason_hash preserved | Adversarial |
| `lifecycle_destroy_of_destroyed_cell_rejected` | Second destroy on a Destroyed cell rejected | Adversarial |

### `turn/tests/integration_burn_receipt.rs` (6 tests)

| Test | What it covers | Adversarial? |
|------|----------------|--------------|
| `burn_reduces_balance_and_sets_was_burn_flag` | Burn amount deducted; receipt.was_burn = true | Happy path |
| `receipt_hash_binds_was_burn_flag` | receipt_hash changes when was_burn differs (bit genuinely bound) | Adversarial |
| `burn_exceeding_balance_rejected_balance_preserved` | Burn > balance rejected; balance unchanged | Adversarial |
| `burn_non_zero_slot_rejected` | Slot ≠ 0 rejected | Adversarial |
| `plain_transfer_does_not_set_was_burn` | Control case: Transfer sets was_burn = false | Control |
| `burn_entire_balance_leaves_zero` | Full burn → balance 0, was_burn = true | Boundary |

### `turn/tests/integration_attenuate_capability.rs` (5 tests)

| Test | What it covers | Adversarial? |
|------|----------------|--------------|
| `attenuate_from_either_to_signature_accepted` | Either→Signature narrowing; post-state cap has Signature | Happy path |
| `attenuate_widening_rejected` | Signature→Either widening rejected; cap unchanged | Adversarial |
| `attenuate_nonexistent_slot_rejected` | Non-existent slot rejected | Adversarial |
| `attenuate_other_actors_cap_rejected` | Actor cannot narrow a different actor's c-list slot | Adversarial |
| `attenuate_chained_narrowing_accepted` | Either→Signature→Impossible; each step accepted | Happy path |

### `cell/tests/integration_destroy_terminal.rs` (6 tests)

| Test | What it covers | Adversarial? |
|------|----------------|--------------|
| `destroy_transitions_to_destroyed_and_rejects_effects` | Cell-layer: destroy → Destroyed, accepts_effects = false | Happy path |
| `destroy_changes_state_commitment` | state_commitment changes after destroy | Semantic |
| `all_transitions_after_destroy_return_terminal` | Every subsequent transition rejected | Adversarial |
| `destroy_certificate_wrong_cell_id_rejected` | CertificateMismatch for wrong cell_id | Adversarial |
| `death_certificate_hash_binds_all_fields` | Every field mutation changes cert hash | Adversarial |
| `destroy_reflected_in_ledger_after_update_with` | Ledger reflects Destroyed after update_with | Integration |

### `cell/tests/integration_attestation_archive.rs` (9 tests)

| Test | What it covers | Adversarial? |
|------|----------------|--------------|
| `archive_transitions_to_archived_and_cell_remains_live` | Archived lifecycle, accepts_effects = true | Happy path |
| `archival_checkpoint_hash_binds_all_fields` | Every field mutation changes checkpoint_hash | Adversarial |
| `archive_on_sealed_cell_rejected` | SealedCannotArchive error | Adversarial |
| `archive_on_destroyed_cell_rejected` | Terminal error | Adversarial |
| `archive_certificate_mismatch_rejected` | CertificateMismatch for wrong cell_id | Adversarial |
| `archive_non_monotone_cutover_rejected` | ArchiveNotMonotone for regressing end_height | Adversarial |
| `archive_zero_blob_hash_rejected` | InvalidAttestation for zero blob | Adversarial |
| `archived_cell_accepts_effects_and_supports_extended_archive` | Extended archive advances archived_through | Happy path |
| `archive_reflected_in_ledger_after_update_with` | Ledger reflects Archived after update_with | Integration |

**Total new integration tests: 34** (8 + 6 + 5 + 6 + 9)

---

## Top 3 Issues with the Current Test Approach

### 1. Internal unit tests for executor-visible behaviour (highest priority)

`turn/src/tests.rs` is 10,776 lines of `#[cfg(test)] mod tests` inside the crate.
At this scale the tests freely reach `pub(crate)` helpers (`ActionBuilder::new_unchecked_for_tests`,
direct ledger mutation, `execute_chained`) that are invisible from outside the crate boundary.
This means a refactor that changes the internal API surface can silently hollow out the
tests without breaking any `cargo test` invocation the user would notice. External integration
tests in `turn/tests/` are the immune check.

### 2. Happy-path dominance in the scenario tests

The "Integration / scenario tests" block in `cell/src/tests.rs` (lines 1270–1534) covers
`agent_lifecycle`, `capability_delegation_chain`, `zkapp_cell_with_verification_key`, etc.
Every scenario test ends with a commit. There is no scenario where the test *deliberately
constructs an invalid operation in the context of an otherwise valid multi-step flow* and
verifies the reject-and-rollback path. The proptest coverage catches some of this, but
proptest does not describe *why* a property holds.

### 3. Lifecycle effects not tested end-to-end before this audit

`Effect::CellSeal`, `Effect::CellUnseal`, `Effect::CellDestroy`, `Effect::Burn`,
`Effect::AttenuateCapability`, and `Effect::ReceiptArchive` were shipped in the executor
(`turn/src/executor/apply.rs`) with no external integration tests that exercise them through
a real `TurnExecutor::execute` call. The adversarial block at line 10800 of `turn/src/tests.rs`
exists but lives entirely inside the internal test module and uses the `new_unchecked_for_tests`
escape hatch — not a genuine integration-boundary test.

---

## Recommendations

- Extract `execute_chained` / `make_open_cell` / `zero_cost_executor` helpers into
  `turn/tests/common/mod.rs` to avoid duplication between `integration_lifecycle.rs`,
  `integration_burn_receipt.rs`, and `integration_attenuate_capability.rs` once all three
  files have been validated. (Not done in this pass to keep changes surgical.)
- Add `#[ignore = "reason"]` to any test in `turn/src/tests.rs` with an unexplained
  `#[ignore]` attribute (none found in this audit, but worth future verification as the
  file grows).
- Consider splitting `turn/src/tests.rs` into per-subsystem files once it approaches
  12,000 lines.
