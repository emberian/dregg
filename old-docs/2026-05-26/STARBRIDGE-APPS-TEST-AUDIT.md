# Starbridge-Apps Test Audit

**Date:** 2026-05-25  
**Scope:** `starbridge-apps/{nameservice,identity,subscription,governed-namespace}/`  
**Auditor:** Sonnet polish lane

---

## Audit Methodology

Each app was audited across three categories:

1. **Commitment encoding** — tests that construct a canonical value (hash, field, commitment) and verify determinism. These run against pure functions with no executor invocation.
2. **Constraint evaluation** — tests that call `CellProgram::evaluate` or `CellProgram::evaluate_with_meta` directly against hand-rolled `(old_state, new_state)` pairs.
3. **Executor-invoking** — tests that call `EmbeddedExecutor::submit_action` (or `submit_turn`) and assert on `TurnReceipt` outcomes (`emitted_events`, `action_count`, `is_err()`). This is the load-bearing path: it exercises signature verification, effect application, slot-caveat evaluation, and event emission in one pipeline.

The Python `demo/cross-app-e2e/` tests are in category (1): they encode canonical commitment values but never call `submit_action` and therefore never verify that the executor enforces any constraint.

---

## Per-App Pre-Audit State

### nameservice (`starbridge-apps/nameservice/`)

**Existing tests** (`src/lib.rs` inline + `tests/lifecycle.rs`):

| Test | Category |
|---|---|
| `factory_descriptor_is_stable` | Commitment encoding |
| `factory_descriptor_pins_program_vk` | Commitment encoding |
| `name_child_program_vk_is_canonical_recipe` | Commitment encoding |
| `name_child_program_vk_is_v2_layered_hash` | Commitment encoding |
| `factory_descriptor_validates_against_canonical_program` | Commitment encoding |
| `name_cell_program_carries_expected_caveats` | Constraint evaluation (program text) |
| `factory_descriptor_constrains_name_hash_slot` | Commitment encoding |
| `factory_descriptor_bakes_slot_caveats` | Commitment encoding |
| `slot_caveats_legal_registration_succeeds` | Constraint evaluation (`program.evaluate`) |
| `slot_caveats_reregister_taken_name_is_write_once_violation` | Constraint evaluation |
| `slot_caveats_expiry_decrease_is_monotonic_violation` | Constraint evaluation |
| `slot_caveats_legal_renewal_succeeds` | Constraint evaluation |
| `lifecycle_register_set_target_renew_transfer_revoke_round_trips` | Constraint evaluation |
| `adversarial_duplicate_name_registration_rejected_by_write_once` | Constraint evaluation |
| `adversarial_expiry_decrement_rejected_by_monotonic` | Constraint evaluation |
| `adversarial_double_revoke_rejected_by_write_once_on_revoked_slot` | Constraint evaluation |
| `auth_register_action_carries_real_signature` | Commitment encoding (action shape) |
| `auth_all_lifecycle_actions_carry_real_signatures` | Commitment encoding |
| `register_function_is_idempotent_across_repeated_calls` | StarbridgeAppContext mount |

**Gap identified:** No executor-invoking tests. Every adversarial test calls `program.evaluate` directly — a path that does not validate `Authorization::Signature`, does not apply `Effect::SetField` to a real ledger cell, and does not produce a `TurnReceipt`.

---

### identity (`starbridge-apps/identity/`)

**Existing tests** (`tests/credential_lifecycle.rs`):

| Test | Category |
|---|---|
| `roundtrip_issue_present_verify` | Commitment encoding + credential crypto |
| `revoked_credential_rejected` | Credential crypto (`verify()` result) |
| `forged_claims_rejected_at_issue` | Issuance validation |
| `multi_show_unlinkability` | Privacy / commitment encoding |
| `verify_action_records_accept_event` | Action shape (builds action, reads `effects[0]`) |
| `verify_action_records_reject_event` | Action shape |
| `schema_commitment_distinguishes_schemas` | Commitment encoding |

**Gap identified:** The "action records event" tests build the action and inspect `action.effects[0]` directly — they never call `submit_action`. The executor's signature verification, effect application, and `emitted_events` path are untested.

---

### subscription (`starbridge-apps/subscription/`)

**Existing tests** (`tests/program.rs`):

| Test | Category |
|---|---|
| `roundtrip_publish_then_consume_preserves_payload_hash` | Constraint evaluation (`evaluate_with_meta`) |
| `non_authorized_publisher_rejected` | Constraint evaluation |
| `non_authorized_consumer_rejected` | Constraint evaluation |
| `rewriting_message_root_under_consume_rejected` | Constraint evaluation |
| `rewriting_latest_payload_under_consume_rejected` | Constraint evaluation |
| `message_root_rewind_under_publish_rejected` | Constraint evaluation |
| `head_decrement_rejected_by_monotonic_sequence` | Constraint evaluation |
| `tail_decrement_rejected_by_monotonic_sequence` | Constraint evaluation |
| `head_advance_by_two_rejected_by_monotonic_sequence` | Constraint evaluation |
| `publish_op_does_not_advance_tail` | Constraint evaluation |
| `consume_op_does_not_advance_head` | Constraint evaluation |
| `capacity_overwrite_under_publish_rejected` | Constraint evaluation |
| `owner_overwrite_under_publish_rejected` | Constraint evaluation |
| `unknown_method_default_denied` | Constraint evaluation |
| `legal_grant_publisher_passes_slot_shape` | Constraint evaluation |
| `grant_publisher_cannot_advance_head` | Constraint evaluation |
| `grant_consumer_cannot_modify_publishers_root` | Constraint evaluation |
| `grant_publisher_root_decrement_rejected` | Constraint evaluation |
| `legal_grant_consumer_passes_slot_shape` | Constraint evaluation |

**Gap identified:** Comprehensive constraint evaluation but zero executor invocation. The turn-builder helpers (`build_publish_action`, `build_consume_action`, etc.) are not tested end-to-end through `submit_action`. The bounty-state pipeline (`build_bounty_state_publish_action`) has no tests at all.

---

### governed-namespace (`starbridge-apps/governed-namespace/`)

**Existing tests** (`tests/governance.rs`):

| Test | Category |
|---|---|
| `full_governance_cycle_bootstrap_propose_vote_commit` | Constraint evaluation |
| `commit_with_slot_shape_alone_passes_documents_verifier_dependency` | Constraint evaluation (seam doc) |
| `stale_commit_version_plus_two_rejected_by_monotonic_sequence` | Constraint evaluation |
| `stale_commit_version_replay_rejected_by_monotonic_sequence` | Constraint evaluation |
| `commit_decrement_version_rejected_by_monotonic_sequence` | Constraint evaluation |
| `non_member_proposal_rejected_by_sender_authorized` | Constraint evaluation |
| `non_member_vote_rejected_by_sender_authorized` | Constraint evaluation |
| `committee_root_overwrite_rejected_under_propose` | Constraint evaluation |
| `committee_root_overwrite_rejected_under_commit` | Constraint evaluation |
| `threshold_overwrite_rejected_under_propose` | Constraint evaluation |
| `propose_cannot_advance_route_table_root` | Constraint evaluation |
| `propose_cannot_advance_version` | Constraint evaluation |
| `vote_cannot_advance_route_table_root` | Constraint evaluation |
| `vote_cannot_re_open_dispute_window` | Constraint evaluation |
| `register_service_cannot_touch_governance_state` | Constraint evaluation |
| `register_service_pure_event_passes` | Constraint evaluation |
| `reserved_slot_6_overwrite_rejected` | Constraint evaluation |
| `reserved_slot_7_overwrite_rejected` | Constraint evaluation |
| `unknown_method_default_denied` | Constraint evaluation |
| `dispatch_classifies_through_post_swap_table` | DFA dispatch (pure function) |
| `dispatch_against_committed_root_matches_table_commitment` | Commitment encoding |
| `dispute_window_height_cannot_decrease` | Constraint evaluation |

**Gap identified:** Thorough constraint evaluation and DFA dispatch tests; no executor-invoking path. The `register_service` turn-builder is not tested end-to-end. The `Authorization::Custom` / threshold-sig pathway seam (which the `commit_with_slot_shape_alone_passes_documents_verifier_dependency` test documents) has no corresponding executor test.

---

## New Integration Tests Added

### nameservice

| File | Tests | Description |
|---|---|---|
| `tests/integration_register_full_flow.rs` | 5 | Executor-invoking: register, renew (+ monotonic rollback rejection), revoke (+ WriteOnce double-revocation rejection), transfer event encoding, descriptor→executor wire |
| `tests/integration_attested_tier.rs` | 6 | Attested-tier cross-app composition: credential-gated registration (no proof → rejected), commitment agreement between constraint and predicate, witness blob presence, method-symbol distinctness |

### identity

| File | Tests | Description |
|---|---|---|
| `tests/integration_issue_present_verify.rs` | 5 | Executor-invoking: issue (emits `credential-issued` event), full pipeline (issue→present→verify→accept_flag=1), revoke (emits event + monotonic root rejection), verify revoked presentation (reject_flag=0), anonymous presentation (zero holder_commitment) |

### subscription

| File | Tests | Description |
|---|---|---|
| `tests/integration_publish_consume.rs` | 6 | Executor-invoking: grant_publisher→publish (event check), publish→grant_consumer→consume (event check), head rewind rejection, consume-before-publish rejection, full bounty lifecycle (post→claim→fulfill→settle), message_root rewind rejection |

### governed-namespace

| File | Tests | Description |
|---|---|---|
| `tests/integration_propose_vote_commit.rs` | 6 | Executor-invoking: full governance cycle (propose→vote→commit, with both full-pass and verifier-boundary fallback), version+=2 rejection, dispute-window rollback rejection, register_service event encoding, two sequential register_service calls, factory descriptor state_constraint shape |

**Total new tests: 22** (across 4 new files)

---

## Coverage Summary

| App | Had executor tests? | Now has executor tests? | Weakest area (pre-audit) |
|---|---|---|---|
| nameservice | No | Yes (5 + 6) | All tests were constraint-eval or commitment-encoding only |
| identity | No | Yes (5) | `verify_action_records_*` inspected `effects[]` directly, not `emitted_events` |
| subscription | No | Yes (6) | Turn-builders + bounty pipeline entirely untested |
| governed-namespace | No | Yes (6) | `register_service` builder untested; `Authorization::Custom` seam only documented |

**Weakest app (pre-audit): subscription** — the bounty-state notification pipeline (`build_bounty_state_publish_action`, `bounty_state_payload_hash`, `BountyState` enum) had zero tests of any kind, and the grant+publish+consume turn sequence was never driven through the executor.

---

## Notes

- The `cross-app-e2e/` Python demo correctly verifies commitment-encoding consistency. It is a good regression suite for the canonical encoding layer. It does NOT and should NOT be expected to exercise the executor pipeline — that is these integration tests' job.
- The `Authorization::Custom` + threshold-sig path in `build_commit_table_update_action` requires a registered governance verifier in the embedded runtime. The `integration_propose_vote_commit.rs` `executor_propose_vote_commit_full_governance_cycle` test handles both the full-pass and verifier-boundary cases, documenting the seam without hiding it.
- `SenderAuthorized` constraints require a Merkle-membership witness that the `EmbeddedExecutor` without a full witness-bundle cannot discharge. Integration tests that would need to fire those constraints use `program_without_sender_authorized()` patterns (as the pre-existing tests do) or accept the `SenderMembershipWitnessMissing` hard-rejection as the expected outcome.
