# Test Quality Audit: `dregg-turn` + `dregg-verifier`

**Scope:** `turn/src/tests.rs`, `turn/src/executor/atomic.rs`, `turn/src/executor/migration.rs`, `verifier/src/lib.rs`, `verifier/src/bilateral_pair.rs`, `verifier/src/aggregated_bundle.rs`, `verifier/tests/integration.rs`, `verifier/tests/bilateral_pair_demo.rs`

**Method:** Read-only static analysis. No compilation executed.

**Inventory:** ~168 tests in `turn/src/tests.rs`, 17 in `turn/src/executor/atomic.rs`, 9 in `turn/src/executor/migration.rs`, 19 in `verifier/src/lib.rs`, ~10 in `verifier/src/bilateral_pair.rs`, 1 in `verifier/src/aggregated_bundle.rs`, 8 in `verifier/tests/integration.rs`, 2 in `verifier/tests/bilateral_pair_demo.rs`.

---

## 1. Tautological Tests

Tests that assert mathematical or structural properties so obvious that a correct implementation and a broken implementation are equally likely to pass.

| # | File | Test Name | Confidence | Rationale | Recommendation |
|---|------|-----------|------------|-----------|----------------|
| 1.1 | `turn/src/tests.rs` | `test_effect_hash_determinism` | **High** | Asserts `hash(a) == hash(a)`. This is a property of any correct hash function, not of the effect system. | **Delete** or merge into a single "hash sanity" smoke test. |
| 1.2 | `turn/src/tests.rs` | `test_action_hash_sensitivity` | **High** | Asserts `hash(a) != hash(b)` for different inputs. Same reasoning as 1.1. | **Delete** or merge into the same smoke test. |
| 1.3 | `turn/src/tests.rs` | `test_call_forest_hash` | **Medium** | Hardcodes an expected forest hash and asserts equality. This is a snapshot test disguised as a unit test; it will break on any harmless serialization change. | **Replace** with a property-based test (e.g. forest hash changes when any leaf changes) or delete. |
| 1.4 | `turn/src/tests.rs` | `test_receipt_deterministic` | **Low** | Asserts that executing the same turn twice yields the same receipt. This is a legitimate regression test for non-determinism bugs. | Keep (downgraded from preliminary flag). |

## 2. Constructor / Structural Tests

Tests whose entire purpose is to verify that a builder/constructor sets fields equal to the arguments passed in, or that a trivial structural property (count, depth) holds.

| # | File | Test Name | Confidence | Rationale | Recommendation |
|---|------|-----------|------------|-----------|----------------|
| 2.1 | `turn/src/tests.rs` | `test_builder_memo_and_valid_until` | **High** | Builds a `Turn` and asserts `turn.memo == Some(...)` and `turn.valid_until == Some(...)`. Tests only field assignment. | **Delete**. If builder logic regresses, every downstream integration test will fail. |
| 2.2 | `turn/src/tests.rs` | `test_call_tree_depth` | **High** | Manually nests `CallTree` to depth 3 and asserts `depth() == 3`. Tests a trivial recursive counter. | **Delete** or replace with a property-based depth test. |
| 2.3 | `turn/src/tests.rs` | `test_forest_total_effects` | **High** | Creates a forest with N effects and asserts `total_effects() == N`. Trivial structural counting. | **Delete**. |
| 2.4 | `turn/src/tests.rs` | `test_program_none_backward_compat` | **Medium** | Verifies that a Turn with no program constraint is accepted. Tests the *absence* of a check rather than the presence of behavior. | **Improve** by adding an assertion that the receipt is committed with correct state, or merge into a broader backward-compat test. |

## 3. Tests Asserting Implementation Details

Tests that will break if the internal algorithm or data structure changes, even when the external behavior remains correct.

| # | File | Test Name | Confidence | Rationale | Recommendation |
|---|------|-----------|------------|-----------|----------------|
| 3.1 | `turn/src/tests.rs` | `test_call_forest_dfs_iteration` | **High** | Asserts the exact DFS visit order of `CallForest` iteration. Any change to internal tree layout (e.g. BFS, parallel traversal, or storing children in a different order) breaks this test even if all observable behavior is identical. | **Delete** or replace with a property test ("every node visited exactly once"). |

## 4. Roundtrip Tests Without Edge Cases

Tests that serialize → deserialize → assert equality, but never exercise malformed, oversized, or boundary inputs.

| # | File | Test Name | Confidence | Rationale | Recommendation |
|---|------|-----------|------------|-----------|----------------|
| 4.1 | `verifier/src/bilateral_pair.rs` | `json_roundtrip_and_verify` | **Medium** | Serializes a valid bundle to JSON, deserializes, and verifies. Only tests the happy path. Does not test: missing fields, extra fields, wrong types, UTF-8 edge cases, or max-size payloads. | **Improve** by adding at least one malformed-JSON rejection case and a max-field-length case. |
| 4.2 | `verifier/tests/integration.rs` | `binary_cli_accept` | **Medium** | Invokes the verifier binary via subprocess with valid inputs. Only happy path. | **Improve** by adding a CLI test with tampered stdin, missing args, or invalid JSON. |
| 4.3 | `verifier/tests/integration.rs` | `stdin_json_accept` | **Medium** | Same as 4.2 but via stdin. Happy path only. | **Improve** — merge with 4.2 into a single CLI test module that includes negative cases. |
| 4.4 | `verifier/src/aggregated_bundle.rs` | `cli_verdict_happy_path` | **Low** | Thin wrapper over `verify_aggregated_bundle_json`. Happy path only, but the underlying function is already heavily tested elsewhere. | Keep, or **delete** if integration tests already cover the JSON path. |

## 5. Duplicate / Near-Duplicate Test Clusters

Multiple tests that exercise the same code path with only trivially different constants or configurations.

### 5.1 Fee Distribution Cluster (`turn/src/tests.rs`)

**Tests:** `test_fee_distribution_basic`, `test_fee_distribution_minimum_fee`, `test_fee_distribution_no_proposer_all_burned`, `test_fee_distribution_proposer_only`, `test_fee_distribution_missing_proposer_cell_in_ledger`, `test_fee_distribution_not_on_failure`

- **Confidence:** **High**
- **Rationale:** All 6 tests call the same `distribute_fees` helper with different `FeeDistributionConfig` constants. The core distribution algorithm is identical; only the boundary conditions (min fee, missing proposer, failure mode) vary. Each test re-implements the same ledger setup and receipt construction.
- **Recommendation:** **Merge** into a single parameterized test (table-driven) with 6 rows of config + expected outcome. Saves ~300 lines of boilerplate.

### 5.2 Introduction Permission Cluster (`turn/src/tests.rs`)

**Tests:** `test_introduction_basic_success`, `test_introduction_fails_without_cap_to_target`, `test_introduction_fails_without_cap_to_recipient`, `test_introduction_fails_with_amplification`

- **Confidence:** **Medium**
- **Rationale:** All 4 tests use the identical 3-cell setup (introducer, recipient, target). Only the permission bits and expected result differ. The setup code (~40 lines each) is copy-pasted.
- **Recommendation:** **Merge** into a single table-driven test with 4 rows: `(permissions, expected_result)`.

### 5.3 Note Conservation Cluster (`turn/src/tests.rs`)

**Tests:** `test_note_spend_and_create_conservation`, `test_note_conservation_violated`, `test_note_nft_transfer`, `test_note_multiple_asset_types_conservation`, `test_note_cross_asset_conservation_fails`

- **Confidence:** **Medium**
- **Rationale:** All 5 tests exercise the same note conservation check with different asset combinations. The setup code (creating cells, notes, proof bundles) is largely duplicated.
- **Recommendation:** **Merge** into a parameterized test module with shared setup.

### 5.4 Escrow Predicate Cluster (`turn/src/tests.rs`)

**Tests:** `test_escrow_create_and_release_with_predicate`, `test_escrow_create_and_timeout_refund`, `test_escrow_release_without_valid_proof_fails`, `test_escrow_double_release_fails`, `test_escrow_create_insufficient_balance`, `test_escrow_release_with_proof_verifier`, `test_escrow_release_proof_rejected_by_verifier`

- **Confidence:** **Low-Medium**
- **Rationale:** 7 tests around escrow lifecycle. Some test genuinely different paths (timeout vs. release), but the ledger setup and cell creation are nearly identical across all 7. `test_escrow_create_and_release_with_predicate` and `test_escrow_release_with_proof_verifier` overlap significantly.
- **Recommendation:** **Refactor** into a shared `EscrowTestContext` helper to remove setup duplication, or merge happy-path + proof variants.

## 6. Tests with Weak / No Meaningful Assertions

Tests that run code but make assertions so weak that many broken implementations would pass.

| # | File | Test Name | Confidence | Rationale | Recommendation |
|---|------|-----------|------------|-----------|----------------|
| 6.1 | `turn/src/tests.rs` | `test_receipt_state_hashes` | **High** | Asserts only that `pre_state_hash != post_state_hash` and both are non-zero. Does not verify the hashes are *correct* (i.e., derived from the actual pre/post ledger state). A broken hasher that always returns `[1; 32]` would pass. | **Improve** by asserting the hash matches a manually-computed expected value, or delete if covered by receipt-determinism tests. |
| 6.2 | `verifier/src/bilateral_pair.rs` | `unilateral_forged_sender_rejects` | **High** | Builds two `UnilateralAttestation` structs with different `sender` fields and asserts they are not equal. **This test does not invoke the verifier at all** — it tests the test helper's inequality, not the verifier's rejection of a forged sender. | **Delete** or rewrite to pass a forged attestation through `verify_bilateral_bundle` and assert rejection. |

## 7. Helper-Level Tests (Testing Utilities, Not the SUT)

Small tests that exercise internal utility functions rather than the crate's public behavior. These are not inherently bad but represent coverage inflation if counted as feature tests.

| # | File | Test Name | Confidence | Rationale | Recommendation |
|---|------|-----------|------------|-----------|----------------|
| 7.1 | `verifier/src/lib.rs` | `test_parse_public_inputs_json` | **Medium** | Tests a 4-line JSON-parsing utility `parse_public_inputs_json`. | Keep but **relocate** to a `util` test module; do not count toward verifier coverage. |
| 7.2 | `verifier/src/lib.rs` | `test_parse_public_inputs_json_rejects_float` | **Medium** | Tests the same parser's error path. | Keep but relocate as above. |
| 7.3 | `verifier/src/lib.rs` | `test_resolve_vk_hash_auto` | **Medium** | Tests that `"auto"` returns `None` from a string→AIR-name lookup table. | Keep but relocate. |
| 7.4 | `verifier/src/lib.rs` | `test_resolve_vk_hash_known` | **Medium** | Tests known VK hash lookup. | Keep but relocate. |
| 7.5 | `verifier/src/lib.rs` | `test_resolve_vk_hash_air_name_encoded` | **Medium** | Tests hex-encoded AIR name lookup. | Keep but relocate. |

---

## Summary by Action

| Action | Count | Test Names / Clusters |
|--------|-------|----------------------|
| **Delete** | 7 | `test_effect_hash_determinism`, `test_action_hash_sensitivity`, `test_builder_memo_and_valid_until`, `test_call_tree_depth`, `test_forest_total_effects`, `test_call_forest_dfs_iteration`, `unilateral_forged_sender_rejects` |
| **Merge** | 17 | Fee distribution (6), Introduction permission (4), Note conservation (5), Escrow predicate (7 — some overlap, net ~17 unique after dedup) |
| **Improve** | 6 | `test_receipt_state_hashes`, `json_roundtrip_and_verify`, `binary_cli_accept`/`stdin_json_accept`, `test_program_none_backward_compat` |
| **Relocate** | 5 | `test_parse_public_inputs_json` (×2), `test_resolve_vk_hash_*` (×3) |
| **Keep as-is** | ~170 | All adversarial/rejection tests, state-machine transitions, auth cascade tests, atomic rollback tests, PI binding tests, migration tests, receipt-chain tests, signature tests, delegation tests, queue tests, capability tests, etc. |

## Net Assessment

**Good coverage density:** The crates have strong adversarial testing — nearly every major feature has at least one rejection path (tampered proof, wrong PI, unauthorized action, timeout, rollback, invalid transition). The `turn/src/executor/atomic.rs` hardening tests in particular are high-quality security regression tests (replay protection, migration freezing, unauthorized transfer blocking, atomic rollback, signature population).

**Main quality drains:**
1. **Boilerplate duplication** in `turn/src/tests.rs` — many tests manually construct full `Turn` structs field-by-field instead of using shared builders. This leads to copy-paste clusters (fee distribution, introduction, escrow, notes).
2. **Hash determinism tests** — three tests that assert properties of the hash function rather than the business logic.
3. **Structural tests** — three tests that assert trivial counting/assignment properties.
4. **One verifier test** (`unilateral_forged_sender_rejects`) that doesn't actually invoke the verifier.

**Estimated line savings if recommendations applied:** ~600–800 lines from merging duplicate clusters and deleting tautological/structural tests.
