# Wallet Security Audit — `sdk/src/wallet.rs`

**Auditor model:** Claude Opus 4.7
**Date:** 2026-05-23
**Scope:** `sdk/src/wallet.rs` (6911 lines), cross-referenced with `sdk/src/runtime.rs`, `bridge/src/present.rs`, and `apps/{lending,subscription,privacy-voting}`.
**Sibling-agent note:** `verify_delegation_envelope_v2` was already `pub` at audit time; `verify_envelope_signature` is a public wrapper. No conflict.

## Verdict: **OK-WITH-FOLLOWUPS**

No CRITICAL break of the documented authority/binding model was found. The two recent rounds of reactive fixes (envelope-v2 mandatory signature; sealed-field HeldToken + `reverify_delegation_binding`) are real and substantively correct. The adversarial test suite is genuine (it exercises post-receive tampering through test-only setters, not compile-time tautologies). However, there are real **P1** sub-agent runtime-layer issues, several **P1/P2** API surface ergonomic footguns, and multiple **P2** hygiene items that the user should address before treating this file as "done."

## Summary

The wallet draws three trust boundaries: (1) **wallet ↔ same-process app code** — same address space, but the wallet sealing pattern protects authority-bearing fields from being mutated except through approved constructors; (2) **wallet ↔ peer over wire** (`DelegatedToken`, signed turns) — every authority-affecting field is in the signed v2 payload, plus a separate authority policy decides which delegator keys are admissible; (3) **wallet ↔ STARK verifier** — the wallet emits proofs whose public inputs commit to revealed facts via Poseidon2. The most important invariant is **durable signature binding**: any HeldToken whose origin is `receive_*_delegation` carries a private `DelegationBinding` that is re-verified on every `prove_authorization_*`/`authorize_private`/`extract_caveat_set_for_proof` call against the *current* field values, so post-receive tampering of `encoded`, `caveat_chain_hash`, or membership leaf is detected.

The v2 signing-message construction (`compute_delegation_signing_message_v2`) is well-formed: it uses `blake3::derive_key` for domain separation, length-prefixes variable-length fields, uses presence tags for `Option<[u8;32]>` to disambiguate `Some([0;32])` from `None`, and binds `delegator_public_key` into the payload (so a malicious holder can't swap signer identity). Local delegations use a distinct context tag (`pyana-delegation-local-v1`), preventing cross-confusion. Authority policy variants are sensible; `Open` is correctly gated behind `cfg(any(test, feature = "unsafe-test-utils"))`.

The biggest residual concerns are: (a) the `SubAgent` shadow-token in `runtime.rs:378` bypasses durable binding because `HeldToken::new_attenuated` produces a token with no `delegation_binding`, while the *actual* delegated token sits in `sub_wallet.tokens[0]`; (b) DoS surfaces from `.expect()` calls on `postcard` and `rmp-serde` serializations of attacker-influenced types; (c) several public fields on `SubAgent` (already documented in an `AUDIT[P2]` comment); (d) a number of authority-bearing operations are reachable through `pub` methods that probably want `pub(crate)`.

---

## Findings

### P0 — must fix before shipping

**None.** The two previously-flagged P0s (optional-signature delegation; mutable HeldToken fields) are correctly fixed.

### P1 — should fix

**P1-1. `SubAgent.token` shadow copy bypasses `DelegationBinding`.**
`sdk/src/runtime.rs:378-384` constructs `delegated_token = HeldToken::new_attenuated(...)` with no `delegation_binding` field, then *separately* drives `sub_wallet.receive_local_delegation(local, &parent_pubkey)` at line 418. Result: `SubAgent.token` (a `pub` field on `SubAgent`, exposed widely) is a HeldToken whose `delegation_binding` is `None`, so `reverify_delegation_binding` is a no-op for it. Any code path that passes `&sub_agent.token` to `wallet.authorize` or `prove_authorization_with_issuer_key` will skip the durable-binding check that the sibling token in `sub_wallet.tokens[0]` has. The token still has the issuer_key, so it CAN generate proofs — meaning a same-process attacker who can mutate `SubAgent.token.encoded` (via the test-only helper or by reconstructing the struct) gets free authorization. Mitigation: have `spawn_sub_agent` clone `sub_wallet.tokens[0]` into `SubAgent.token` so the binding travels with it, OR remove `SubAgent.token` and require callers to go through `sub_wallet.tokens()`.

**P1-2. `SubAgent` fields are all `pub`.** `sdk/src/runtime.rs:480-507`. Already flagged in an `AUDIT[P2]` comment in the file. The `pub federation_id: [u8; 32]` is used as the domain separator in `SubAgent::execute`'s `compute_signing_message` (`runtime.rs:553`). An external `&mut SubAgent` holder can rewrite it post-construct, inducing cross-federation signature replay vectors. Also `pub wallet: Arc<AgentWallet>` and `pub token: HeldToken` are needlessly broad. Fix: make all fields private with read-only accessors.

**P1-3. `expect()` on adversary-influenced `rmp-serde` serialization in `compute_caveat_chain_hash` (line 3795).** The caveats slice comes from `MacaroonToken::from_encoded(&token.encoded, [0u8;32])` — i.e. an attacker-controlled string passed through receive_signed_delegation. Although postcard/rmp-serde of a typed `Vec<Caveat>` "should not fail" under normal Rust expectations, a malformed `Caveat` (e.g. with non-UTF8 String content fabricated through internal mutation) could trigger a panic at this site, which is reachable inside `delegate*` and the delegator's pre-delegation path. Fix: propagate as `SdkError::Wire` instead of panic.

**P1-4. `compute_delegation_signing_message_v2` and `compute_local_delegation_signing_message` both `.expect()` postcard serialization of `Attenuation`** (lines 2555 and 2670). Same shape as P1-3; if a delegator constructed an `Attenuation` containing non-serializable nested data (today there is none, but the type is open to future field additions), this panics at signing time on attacker-influenced input. Fix: return Result and bubble the error.

**P1-5. `verify_token` returns `false` on decode error (line 1406-1410).** Decode-error → `false` is semantically "not authorized," which is safe, but masks a structural error from the caller. More importantly, `SubAgent::can_authorize` uses this method on a token whose root_key is zeroed → `decode()` will work but `verify()` requires the real root key, which is always absent for delegated tokens. So `can_authorize` *always returns false* for any sub-agent's delegated token. This is a correctness-rather-than-security bug, but it's load-bearing in the public API. Fix: document the limitation, or make `can_authorize` go through `wallet.authorize(...)` instead.

**P1-6. `compute_root_from_membership_proof` (line 3804) trusts the proof's path length without bounds checking.** If a maliciously-deserialized `MerkleProof` contained, e.g., a `path_indices.len() = usize::MAX`, the loop would spin. There's a memory bound elsewhere (64 KiB on token bytes), but the membership proof is a separate field with no explicit length cap. Combined with `MAX_DELEGATED_TOKEN_SIZE` only covering `token_bytes`, this is a moderate DoS vector. Fix: bound proof depth (e.g. <= 64) at receive time.

**P1-7. `authorize_trusted` does NOT call `reverify_delegation_binding`.** Line 1923-1935. The `extract_caveat_set` path (line 2234) requires `token.root_key` to verify HMAC, which only locally-minted tokens have, so this path is only reachable for locally-minted/-attenuated tokens that have no `delegation_binding` anyway. Therefore the omission is currently safe by accident — but the contract is fragile: if a future change introduces a path where a delegation-bound token reaches `authorize_trusted`, the durable binding would be skipped. Fix: add a defensive `token.reverify_delegation_binding()?` at the top of `authorize_trusted`.

### P2 — would-be-nice / hygiene

**P2-1. `authorize_selective` does not invoke `extract_caveat_set_for_proof` for the can_mint() branch.** Line 1943-1997. When `token.can_mint()`, it calls `extract_caveat_set_for_proof` (which DOES call reverify), but the subsequent `prove_authorization_selective` (line 2891) does NOT call reverify itself. Symmetry break with `prove_authorization_with_issuer_key`. Today this is fine because can_mint() => no binding, but again fragile. Fix: defensive reverify at every `prove_authorization_*` entry, even on the no-binding branch.

**P2-2. `Drop` for `AgentWallet` does not zeroize `signing_key`** (line 5553-5563). It zeroizes `seed` and `mnemonic_phrase` but the in-memory `ed25519_dalek::SigningKey` is dropped without zeroization. `SigningKey` does implement `ZeroizeOnDrop` upstream, so this is *probably* safe in practice, but the code does not document the reliance.

**P2-3. `set_captp_client` is `pub` and takes `&mut self`** (line 5244). Lets any holder of `&mut wallet` swap the CapTP client. Fine for now (single-tenant wallet), but in any multi-component setting this is a foot-gun.

**P2-4. `export_seed` and `export_mnemonic` return references with `&mut self`** (line 1049, 1069). The `&mut self` requirement is documented as preventing extraction via shared refs, but a `&mut wallet` callsite can still log/copy/transmit the returned `&str`/`&[u8]`. The `must_use` attribute helps. Consider returning `Zeroizing` wrappers.

**P2-5. `convert_effects_to_vm` truncates 32-byte values to 4 bytes** (lines 4359-4368). Collisions in `field_element_to_bb` and `hash_to_bb` are inevitable for any non-trivial value space. This is in the sovereign-cell proof generation path. If the executor side does the same truncation it's consistent, but the truncation loses domain separation between distinct hashes that happen to share the first 4 bytes. Fix: at least document; ideally migrate to `Self::bytes_to_babybear` which does Poseidon2-based compression.

**P2-6. `extract_fact_value` clamps `Const(sym)` to 4 bytes mod BABYBEAR_P** (line 2189). Same truncation concern — predicate proofs operate over a small numeric subset of fact values. Documented but worth re-reviewing.

**P2-7. `compute_federation_root_bb` uses a synthetic Merkle path** (line 3731). Documented as "in production this would come from the federation registry." If any production callpath ever calls this without a real registry, the resulting proof is verifiable only against the synthetically-derived root — non-interoperable. Today, `prove_authorization_with_issuer_key` (line 2856) correctly prefers `compute_root_from_membership_proof` when a `membership_proof` is available. Hygiene: add a `tracing::warn!` when falling back to synthetic root in production builds.

**P2-8. `find_token` / `find_token_by_id` linear scan** (line 1122-1129). Fine for small token sets; trivial DoS if a caller holds many tokens and queries hot-path. Low priority.

**P2-9. `import_sovereign_state` overwrites existing keys silently** (line 4552). Merge semantics not documented; an adversary who can hand the wallet a serialized blob can overwrite local sovereign state.

**P2-10. `compute_turn_bytes` does not include `turn.conservation_proof` / `sovereign_witnesses` / `execution_proof` / `custom_program_proofs`** (line 3680-3724). Documented as covering "all semantically-relevant fields," but executor-side fields like `execution_proof_new_commitment` are missing from the signing message. If an attacker can swap a different `execution_proof_new_commitment` after the wallet signs, the signature still verifies. This requires write access to the SignedTurn struct in flight (which is `pub` by design), but it's an implicit trust assumption worth documenting OR closing.

### P3 — notes / future direction

**P3-1. No explicit clock injection.** `receive_signed_delegation` uses `std::time::SystemTime::now()` for expiry checks (line 1480). Tests would benefit from a `Clock` trait; safety would benefit from monotonic-clock semantics.

**P3-2. `prove_fast` is `#[deprecated]` but still `pub`** (line 2996). Consider removing.

**P3-3. `Sealed-value` doc on `HeldToken` is excellent.** Worth importing as a project doc.

**P3-4. `DelegationAuthority::Open` is well-handled** but consider an additional `Forbidden` variant that rejects every envelope as a safer default than nothing.

**P3-5. `hex_decode_bytes` returns `Err(())`** (line 5526). Use a real error type.

**P3-6. `build_authorized_turn`** (line 2385) hard-codes `nonce: 0` and `previous_receipt_hash: None`. Documented as "Caller should set appropriately or use a TurnBuilder" but a user reading the example may not notice. Replay risk if used naïvely. Promote to a `TurnBuilder`-only API.

---

## Test coverage table

| Invariant | Test (file:line) | Real or tautological? |
|---|---|---|
| Envelope rejects attacker-forged signature | `wallet.rs:6393` `test_envelope_rejects_attacker_forged_signature` | Real (ed25519 verification under wrong key). |
| Envelope rejects unauthorized delegator | `wallet.rs:6439` `test_envelope_rejects_unauthorized_delegator` | Real (authority policy). |
| Envelope rejects replay to wrong recipient | `wallet.rs:6470` `test_envelope_rejects_replay_to_wrong_recipient` | Real (binding check + signature). |
| Tampered restrictions/service/id rejected | `wallet.rs:6509` `test_envelope_rejects_tampered_fields` | Real. |
| Chain delegation rejects wrong parent hash | `wallet.rs:6559` `test_envelope_chain_rejects_wrong_parent_hash` | Real. |
| No unsigned envelope constructor | `wallet.rs:6630` `test_envelope_has_no_unsigned_constructor` | **Tautological** (only round-trips serde, doesn't actually try to construct unsigned). The compile-fail guarantee is in the type, not in this test. |
| Open policy still verifies signature | `wallet.rs:6654` `test_envelope_open_policy_still_verifies_signature` | Real. |
| Local delegation requires signature | `wallet.rs:6684` `test_local_delegation_signature_required` | Real — tests the expected-parent-pubkey mismatch path. Could be stronger: doesn't test signature mutation independent of expected_parent. |
| **Durable binding: tamper `encoded` after receive breaks authorize** | `wallet.rs:6769` `test_held_token_tamper_encoded_breaks_authorize` | **Real** — uses `test_only_tamper_encoded` + asserts `Err(InvalidDelegation)` from `authorize`. Load-bearing. |
| Durable binding: tamper `caveat_chain_hash` after receive breaks authorize | `wallet.rs:6819` `test_held_token_tamper_chain_hash_breaks_authorize` | Real. |
| HeldToken has no public field mutation | `wallet.rs:6859` `test_held_token_no_public_field_mutation` | **Tautological** — the comment acknowledges that the compile-fail is what enforces it; the test only verifies that the read-only accessor returns the right value. |
| Open policy is feature-gated | `wallet.rs:6896` `test_open_authority_gated` | Tautological (runs inside cfg(test), where the variant trivially exists). The cfg gate is what enforces production exclusion. |
| Membership-proof swap detected at reverify | (implicit in P0 tests above) | Real — line 597-601 checks `current_membership_leaf != binding.membership_leaf`. |
| Attenuated tokens carry only derived issuer_key | `wallet.rs:5761` `test_attenuated_token_has_zeroed_root_key` | Real. |
| Delegated tokens carry derived proof_key not root | `wallet.rs:6013` `test_delegated_token_can_prove_with_proof_key` | Real. |
| Delegated tokens marked unverified | `wallet.rs:5855` `test_receive_delegation_marks_unverified` | Real. |

**Missing tests (P2-level coverage gaps):**
- No test exercises `SubAgent.token` tampering (would catch P1-1).
- No test for membership_proof depth bounds (P1-6).
- No test that `prove_authorization_selective` rejects a tampered binding-bound token via the can_mint() branch (P2-1).
- No test that `Drop` zeroizes `signing_key`.

---

## API surface review (selected `pub fn` on `AgentWallet`)

Trust classes: **A** = app-callable, **R** = runtime-internal, **P** = peer-wire entry-point, **K** = key-export sensitive, **C** = CapTP.

| Function | line | Trust class | Visibility match? |
|---|---|---|---|
| `new`, `from_key_bytes`, `from_mnemonic`, `from_seed`, `derive_sub_agent` | 924/941/976/987/1024 | K | OK (`&mut self` where extracts). |
| `export_mnemonic`, `export_seed` | 1049/1069 | K | OK (`&mut self`, `must_use`). |
| `derive_symmetric_key`, `gossip_signing_key` | 1094/1102 | A/R | `gossip_signing_key` clones the signing key bytes; **P2** consider `pub(crate)`. |
| `mint_token`, `attenuate`, `delegate`, `delegate_with_*` | 1148/1182/1229/1243/1324/1335 | A | OK. |
| `verify_token` | 1406 | A | OK; semantic limit (see P1-5). |
| `receive_signed_delegation` | 1458 | P | OK. |
| `receive_local_delegation` | 1569 | R | OK; only callable via the typed `LocalDelegation` (no serde). |
| `authorize`, `authorize_with_disclosure` | 1907/2038 | A | OK. |
| `verify_envelope_signature`, `verify_delegation_envelope_v2` | 2585/2595 | P | OK (signature-only; explicitly documented). |
| `make_local_delegation` | 2682 | R | `pub(crate)` — correct. |
| `prove_authorization`, `prove_authorization_with_issuer_key`, `prove_with_chain` | 2744/2819/3015 | A | OK; all gated on reverify. |
| `prove_predicate`, `prove_arithmetic`, `prove_relational`, `prove_committed_threshold`, `prove_program`, `prove_program_full`, `prove_for_intent_predicates` | 3109/3174/3269/3322/3383/3426/3493 | A | OK but **P2**: none call `reverify_delegation_binding`. These take an HeldToken and use it for `_decoded` validity check only. If the token was delegated and tampered, you can still prove a predicate over it. The proof is independent of the macaroon, but the state-root derivation uses `derive_proof_key(token.root_key())` which is zero for delegated tokens → state-root collapses to a deterministic value. Consequence: predicate proofs from delegated tokens won't be bound to a meaningful state root. Recommend documenting or rejecting. |
| `fulfill_and_collect` | 3612 | A | OK. |
| `sign_turn`, `sign_bytes` | 2327/2340 | A | `sign_bytes` is a generic signing oracle — caller controls the message bytes entirely. Domain-separation prefix is NOT applied. Could be cross-protocol-replayed. **P2**: rename / document / restrict. |
| `build_authorized_turn` | 2385 | A | See P3-6. |
| `submit_pipeline`, `eventual_ref` | 3843/3868 | A | OK. |
| `build_committed_transfer`, `private_transfer` | 3894/4013 | A | OK. |
| `make_sovereign`, `execute_sovereign_turn`, `execute_sovereign_turn_with_proof` | 4060/4112/4204 | A | OK. |
| `convert_effects_to_vm` | 4351 | R | `pub` but appears to be an internal helper exposed for circuit testing; **P2**: `pub(crate)`. |
| `compress_sovereign_history`, `verify_compressed_history` | 4589/4649 | A | `verify_compressed_history` reconstructs PIs from the proof itself (line 4675) — comment acknowledges this needs production hardening. **P3**. |
| `register_with_federation`, `deregister_from_federation`, `deploy_program` | 4907/4979/5039 | P | Feature-gated, OK. |
| `execute_with_program` | 5117 | A | OK. |
| `share_capability`, `accept_capability`, `delegate_offline`, `set_captp_client`, `captp_client(_mut)` | 5177/5198/5220/5244/5249/5254 | C | OK; `set_captp_client` see P2-3. |
| `allocate_queue`, `enqueue_message`, `dequeue_message`, `atomic_queue_tx` | 5276/5342/5408/5465 | A | All hard-code `nonce: 0` and `previous_receipt_hash: None` — same risk as `build_authorized_turn` P3-6. The caller is presumably expected to overwrite these, but the API doesn't make that clear. **P2**. |

---

## Open questions for the user

1. **`SubAgent.token` clone — kill or fix?** P1-1 is the most material finding. Do you want me to (a) remove the field entirely and require callers to go through `sub_wallet.tokens()`, or (b) clone the bound token in from `sub_wallet.tokens[0]` so the binding travels with it? Option (b) is less invasive but the token would have a binding signed by the parent wallet, which the same parent re-verifies when they call `authorize` on the sub-agent's wallet — that's the desired behavior. Recommend (b).

2. **`sign_bytes` general oracle — restrict?** Currently any caller with `&AgentWallet` can sign arbitrary bytes with the wallet's identity key. There's no domain prefix. Within a single process this is fine, but if `sign_bytes` is exposed via any RPC surface it's a cross-protocol replay vector. Want me to add a mandatory domain-tag parameter?

3. **Membership proof depth bound** (P1-6) — what's the right cap? Federation tree is currently 8 levels in `compute_federation_root_bb`. A cap of 64 would be generous.

4. **Predicate-proof state root for delegated tokens** (P2 note on `prove_predicate*`) — should these functions reject `!token.can_mint()` outright, or accept the issuer_key-derived state-root with documentation?

5. **`extract_caveat_set_structural` security model** — the comment (line 2252) argues that ZK proof replaces HMAC chain integrity for the verifier, but `caveat_chain_hash` enforcement only happens inside `prove_authorization_*_with_issuer_key` (lines 2844, 2951). The selective-disclosure path with `can_mint()` (line 1978) takes the *full HMAC* path through `prove_authorization_selective`, so an attacker with a tampered delegation can't reach `extract_caveat_set_structural` with an arbitrary caveat set. This is consistent but the reasoning chain is subtle. Want a doc clarification?

6. The audit found no CRITICAL break of the documented model. Are there specific attack scenarios you have in mind that the test suite doesn't yet cover and that you want me to construct adversarial tests for?
