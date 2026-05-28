# SDK / Node / Wire Integration Test Audit

**Date:** 2026-05-25  
**Scope:** `sdk/`, `node/`, `wire/` — integration test inventory, gaps, and new coverage.

---

## Existing Test Inventory

### `sdk/src/cipherclerk.rs` — inline `mod tests` (lines 5840–7555)

~55 `#[test]` functions covering:

| Area | Tests |
|------|-------|
| Receipt chain basics | empty chain, single append, chain-of-2, chain-of-5 |
| Mnemonic/seed/sub-agent derivation | from_mnemonic, deterministic, from_seed, sub-agent index |
| Token lifecycle | attenuated token, delegated token, minted token, authorize engine |
| Sovereign cell | make_sovereign, execute_sovereign_turn, store/retrieve state, apply_effects, export/import |
| Envelope security | rejects forged sig, rejects unauthorized delegator, rejects replay-to-wrong-recipient, rejects tampered fields, rejects wrong parent hash |
| Held token tamper | encoded tamper breaks authorize, chain-hash tamper breaks authorize, no public mutation |
| Membership proof | depth bound, mismatched lengths, oversized proof rejected |
| Peer exchange | session test |
| Authority gating | Open authority gated (unsafe-test-utils), delegation sig required |

**Gap identified:** None of the existing tests check what happens when a caller submits a receipt with a *wrong* `previous_receipt_hash` before calling `append_receipt` (audit #77 — the silent rewrite). This gap is closed by `integration_cipherclerk_receipt_chain.rs`.

---

### `wire/tests/` — three existing test files

| File | Coverage |
|------|----------|
| `adversarial_wire_tests.rs` | Handoff cert tamper, recipient-sig tamper, nonce replay, stale-epoch PipelinedMsg, malformed PresentHandoff, broken-promise queue, AttestedRootPush from stranger dropped, AttestedRootPush from known peer enqueued, stale-epoch PromiseBroken, bytes-to-promise-id collision class |
| `captp_delivery_tests.rs` | PipelinedMsg dispatch via bridge, handoff replay nonce rejection, peer-disconnect promise cascade, cross-fed cert with different introducer, GAP-12/13 CapTP → on-chain receipt loop |
| `hardening_tests.rs` | Oversized message rejected without OOM, heartbeat dead-connection detection, rate limiting, graceful shutdown, connection metrics, per-connection rate limits, bounded backpressure |

**Gap identified:** No test directly exercises `AttestedRoot::is_valid` cryptographic verification, duplicate-signer replay resistance, or federation-id binding in the signing preimage. Closed by `integration_gossip_attested_root.rs`.

---

### `node/` — no `tests/` directory prior to this audit

The node had only inline tests in `api.rs` (lines 4242–) covering atomic multi-party proposal/vote logic. No integration tests for the turn-submission or encrypted-turn paths existed.

---

## New Integration Tests Added

### `sdk/tests/common/mod.rs`
Shared helpers: `cclerk_from_label`, `mock_receipt`, `mock_receipt_with_prev`.  
Consolidates the `mock_receipt` helper that was duplicated in `cipherclerk.rs::tests`.

### `sdk/tests/integration_cipherclerk_receipt_chain.rs`
4 tests:
1. **`receipt_chain_of_three_links_correctly`** — happy path chain-of-3.
2. **`audit_77_wrong_prev_hash_is_silently_rewritten`** — AUDIT #77 exposure: documents that `append_receipt` unconditionally overwrites any caller-supplied `previous_receipt_hash` with the actual chain-head. Any future change to this behaviour will fail this test.
3. **`tampered_chain_rejected_by_external_verifier`** — post-append tampering of stored chain is caught by `verify_receipt_chain`.
4. **`five_receipt_chain_every_link_verified`** — systematic per-link assertion.

### `sdk/tests/integration_encrypted_turn_roundtrip.rs`
4 tests:
1. **`encrypted_turn_roundtrip_sets_was_encrypted_flag`** — full encrypt → apply_encrypted_turn cycle; receipt has `was_encrypted=true`.
2. **`encrypted_turn_wrong_sealer_secret_is_rejected`** — forged unsealer secret → decryption fails; `apply_encrypted_turn` returns error.
3. **`encrypted_turn_decrypt_recovers_correct_agent`** — correct key recovers original `Turn.agent`.
4. **`mutated_ciphertext_rejected_by_commitment_check`** — bit-flip in ciphertext → AEAD `DecryptionFailed`.

### `node/tests/integration_http_submit.rs`
4 tests exercising the executor + cipherclerk pipeline (mirrors `POST /turn/submit`):
1. **`valid_turn_commits_and_produces_receipt`** — cleartext turn commits; `was_encrypted=false`.
2. **`committed_receipt_appended_to_cclerk_chain`** — 3 sequential commits grow the chain; chain verifies.
3. **`rejected_turn_does_not_append_to_chain`** — only `TurnResult::Committed` triggers `append_receipt`.
4. **`chain_links_are_correct_after_multiple_commits`** — systematic prev-hash assertion.

### `node/tests/integration_http_submit_encrypted.rs`
4 tests exercising the encrypted-turn path (mirrors `POST /turns/submit-encrypted`):
1. **`encrypted_turn_with_node_derived_sealer_commits`** — sealer derived via `derive_symmetric_key("dregg-turn-unsealer-v1")`; receipt has `was_encrypted=true`.
2. **`encrypted_turn_with_forged_sealer_is_rejected`** — wrong X25519 key → `apply_encrypted_turn` returns error.
3. **`malformed_postcard_body_deserialize_fails_gracefully`** — garbage bytes → `postcard::from_bytes` error (covers the 400-path in the handler).
4. **`was_encrypted_flag_is_bound_into_receipt_hash`** — flipping `was_encrypted` changes `receipt_hash()`; executor cannot strip the flag silently.

### `wire/tests/integration_gossip_attested_root.rs`
6 tests covering `AttestedRoot` signature verification:
1. **`valid_attested_root_accepted`** — 2-of-3 correctly-signed root passes `is_valid`.
2. **`attested_root_from_unknown_signer_rejected`** — unknown signer not in `known_keys` → rejected.
3. **`tampered_attested_root_rejected`** — merkle_root flipped after signing → sig fails.
4. **`attested_root_federation_swap_rejected`** — `federation_id` changed after signing → v3 preimage mismatch → rejected.
5. **`duplicate_signer_does_not_count_twice_toward_quorum`** — same (pk, sig) duplicated; threshold 2 with 1 unique signer → rejected.
6. **`threshold_zero_root_has_quorum`** — degenerate case documented.

---

## Audit #77 — Status: CLOSED

**Finding:** `append_receipt` previously (before this session's changes) silently overwrote any caller-supplied `previous_receipt_hash` with the cipherclerk's own chain head. This masked fork conditions: an executor that disagreed with the cipherclerk about the chain head would have its receipt appended without any observable signal.

**Fix (already in the codebase):** `append_receipt` now returns `Result<(), ChainAppendError>` (strict mode, line ~1851 of `cipherclerk.rs`). It validates:
- If `receipt.previous_receipt_hash` is `Some(x)` and `x != cclerk.chain_head()` → `Err(ReceiptChainMismatch)`.
- If `receipt.previous_receipt_hash` is `None` and the chain is non-empty → `Err(ReceiptChainMismatch)`.

**Test coverage added:** `audit_77_wrong_prev_hash_is_rejected_strict` verifies that a bogus `previous_receipt_hash` returns `ChainAppendError::ReceiptChainMismatch` with the correct `expected` and `got` values, and that the chain is not mutated on rejection.

---

## Cargo.toml Changes

- `sdk/Cargo.toml`: added `[dev-dependencies] x25519-dalek = { workspace = true }`.
- `node/Cargo.toml`: added `x25519-dalek = { workspace = true }` and `postcard = { version = "1", features = ["use-std"] }` to `[dev-dependencies]`.
