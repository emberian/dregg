# Intent / Bridge Test Audit

**Date:** 2026-05-25  
**Scope:** `intent/src/*.rs`, `bridge/src/*.rs` (and their inline `#[cfg(test)]` modules)

---

## Existing test coverage classification

### `intent/src/trustless.rs` (inline module, ~21 tests)

| Test | Classification | Notes |
|------|----------------|-------|
| `test_encrypted_intents_opaque_before_decrypt` | **Real** | Confirms raw ciphertext bytes don't deserialize as plaintext Intent |
| `test_batch_boundary_deterministic` | **Real** | Verifies state machine correctly rejects post-close submissions |
| `test_higher_score_wins` | **Stub-dependent** | Uses `witnessed_predicate: None`; passes because default verifier is permissive-stub |
| `test_challenge_replaces_winner` | **Stub-dependent** | Same — no predicate, permissive path |
| `test_challenge_lower_score_rejected` | **Real** | Score comparison is structural; doesn't touch verifier |
| `test_invalid_proof_rejected` | **Real** | Empty-proof guard fires before stub can accept |
| `test_score_mismatch_rejected` | **Real** | Structural check catches sum mismatch |
| `test_intent_not_in_batch_rejected` | **Real** | Structural check: intent ID not in decrypted set |
| `test_duplicate_intent_usage_rejected` | **Real** | Structural check: same ID in two rings |
| `test_settlement_atomic` | **Stub-dependent** | Relies on permissive stub to accept the submission |
| `test_cannot_finalize_during_challenge` | **Real** | State-machine only |
| `test_insufficient_bond_rejected` | **Real** | Bond check precedes verifier call |
| `test_duplicate_encrypted_intent_rejected` | **Real** | Content-ID dedup in submit_encrypted |
| `test_full_protocol_flow` | **Stub-dependent** | Happy path; no predicate; permissive stub |
| `test_threshold_not_reached` | **Real** | Counts shares accurately |
| `test_challenge_window_expiry` | **Real** | Height arithmetic |
| `test_duplicate_validator_share_rejected` | **Real** | Share-dedup logic |
| `test_tampered_share_rejected` | **Real** | MAC verification in `combine_shares` |
| `test_share_for_unknown_ciphertext_rejected` | **Real** | ciphertext_id set membership |
| `witnessed_verifier_accepts_dfa_kind_with_stub_registry` | **Stub-dependent** | Stub Dfa verifier accepts any non-empty bytes |
| `witnessed_verifier_rejects_unknown_custom_vk_hash` | **Real** | KindNotRegistered surfaces correctly |
| `witnessed_verifier_accepts_registered_custom_vk_hash` | **Real** | Registry dispatch works |
| `witnessed_verifier_rejects_tampered_batch_binding` | **Real** | Audience binding check |
| `witnessed_verifier_rejects_empty_proof_bytes` | **Real** | Empty-proof guard |
| `witnessed_verifier_strict_mode_rejects_missing_predicate` | **Real** | Strict posture |
| `witnessed_verifier_rejects_signing_message_input_outside_action_context` | **Real** | InputRef shape check |
| `batch_binding_is_deterministic_and_order_independent` | **Round-trip-only** | No adversarial inputs |

### `intent/src/lib.rs` (inline module)

All tests are **round-trip-only** or **happy-path-only**: `intent_id_is_deterministic`, expiry, nullifier uniqueness, stake proof round-trips. No adversarial inputs.

### `bridge/src/tests.rs` (module)

| Test | Classification | Notes |
|------|----------------|-------|
| `test_end_to_end_macaroon_to_zk_proof` | **Real** | Full STARK path including `prove()` |
| `test_end_to_end_denial` | **Real** | Wrong-app is rejected |
| `test_conversion_preserves_semantics` | **Round-trip-only** | Checks fact count only |
| `test_fold_chain_verification` | **Real** | `apply_and_verify()` is non-trivial |
| `test_authorization_trace_generation` | **Real** | Trace Datalog evaluation |
| `test_circuit_fold_proofs` | **Real** | AIR constraint verification |
| `test_service_scoped_full_pipeline` | **Real** | Cross-rule assertion |
| `test_unrestricted_token_proof` | **Happy-path-only** | No denial case |
| `test_issuer_membership_circuit_rejects_wrong_federation_root` | **Real** | Forged-issuer rejected |
| `test_presentation_air_full_verification` | **Happy-path-only** | No adversarial case |
| `test_proof_metadata` | **Round-trip-only** | Field value checks |
| `test_deterministic_verification` | **Round-trip-only** | Two identical runs |
| `test_fact_set_merkle_commitment` | **Real** | Membership proof verifies |
| `test_fold_delta_from_raw_states` | **Real** | Delta reconstruction |

---

## Audit finding #82 — stub registry in `TrustlessIntentEngine::Default`

`TrustlessIntentEngine::new` wires `WitnessedProofVerifier::with_stub_registry()`. The stub registry's built-in kind verifiers (`Dfa`, `Temporal`, `MerkleMembership`, etc.) accept **any non-empty proof bytes**. This means:

- Submissions **without** `witnessed_predicate` pass on the permissive fallback path.
- Submissions **with** a stub-handled kind (e.g. `Dfa`) also pass with garbage proof bytes.

**Impact:** 10 of the 27 existing trustless tests are classified stub-dependent. They would all pass even if the underlying constraint system were replaced with a no-op. They are therefore NOT regression tests for the cryptographic soundness of solver proof verification.

**Fix posture (post-#82):** Replace the stub registry with real STARK/Schnorr/Bulletproof verifiers and flip the stub-dependent tests to assert rejection of garbage proofs.

---

## MockProofVerifier usage

`MockProofVerifier` (deprecated since 0.2.0) is retained in `trustless.rs` but is **not used in any test**. No production path reaches it. It is dead code and may be removed after #82 lands.

`WitnessedProofVerifier::with_stub_registry()` is the new name for the same semantics. It appears in:
- `TrustlessIntentEngine::new` (default path)
- `witnessed_verifier_accepts_dfa_kind_with_stub_registry` (test; explicit)

---

## New integration tests added

| File | Tests | What they verify |
|------|-------|-----------------|
| `intent/tests/integration_trustless_predicate_real.rs` | 4 | AcceptAll/RejectAll custom verifiers are actually dispatched; tampered batch binding rejected; strict mode; pre-#82 characterization |
| `intent/tests/integration_batch_lifecycle.rs` | 6 | Replay rejection, out-of-range validator, bond conservation, finalize-before-window rejected, post-settlement fresh batch, strict mode rejects plain sub, phantom intent rejected |
| `intent/tests/integration_cross_fed_match.rs` | 8 | CrossFedRingTrade labeling, CrossFederationSolver ring detection across feds, incompatible-intent non-ring, expired intent filtering, solve_cross_fed_only filter |
| `bridge/tests/integration_present_credential.rs` | 6 | Valid credential, forged issuer, expired credential, wrong app, wire proof strips trace, wrong user |
| `bridge/tests/integration_action_binding.rs` | 8 | Round-trip verify, tampered nullifier/recipient/dest/amount rejected, corrupted/empty proof bytes rejected, zero and u64::MAX amounts |
| `bridge/tests/integration_midnight_bridge.rs` | 8 | Attestation round-trip, wrong pubkey, short pubkey, tampered amount breaks self-consistency, dedup key semantics, epoch key lookup, canonical payload determinism |

**Total new tests: 40**

---

## Gaps not covered by new tests (deferred)

- `bridge::present` bridge-predicate proof (`BridgePredicateProof`) adversarial inputs — requires mocking the circuit STARK prover; deferred.
- `intent::fulfillment` / `commit_reveal_fulfillment` — no new tests; existing coverage is happy-path-only.
- `cell::unilateral` attestation binding (referenced in task spec) — lives in the `cell` crate, out of scope for this lane.
