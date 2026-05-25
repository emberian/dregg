# Unlinkability Properties in Pyana

## 1. Multi-show Unlinkability (Credential Presentation)

**Implemented.** `presentation_tag = Poseidon2(final_root, presentation_randomness, verifier_nonce)` with fresh randomness per show (`generate_presentation_randomness()` in `bridge/src/present.rs:1229`). The `final_root` and `initial_root` are private witness; only the tag is public.

**Effective when:** randomness is truly fresh (getrandom), verifier_nonce is unique per session (prevents replay but also prevents tag reuse). The composition commitment binds the tag to all sub-proofs.

**Leaks:** (a) Federation root is public -- reveals which federation the presenter belongs to. (b) Proof size varies with tree depth (8-level Merkle = fixed, but fold chain length leaked in non-IVC proofs via `fold_proofs.len()`). (c) `WirePresentationProof` strips `chain_length` and `final_state_root` (Phase 2 design, line 286 of bridge/src/present.rs), but the circuit_proof still contains N fold sub-proofs unless IVC is used. (d) Timestamp is public.

**Break it:** If `presentation_randomness` is reused (RNG failure), two shows produce the same tag. Also, BabyBear field (p=2013265921, ~31 bits) means birthday collisions at ~2^15.5 presentations per token -- realistic for high-frequency tokens.

**Improve:** Move to a 256-bit field for the tag, or use Poseidon2 over multiple field elements. Use the IVC path (constant-size) to hide chain length.

## 2. Issuer Unlinkability (Ring Membership)

**Implemented.** `BlindedMerklePoseidon2StarkAir` produces `blinded_leaf = hash_2_to_1(leaf_hash, blinding_factor)` with fresh blinding per presentation (`generate_blinding_factor()`, present.rs:1229). Public inputs are `[blinded_leaf, root]` -- verifier cannot determine which leaf.

**Anonymity set:** Federation member count. A 4-member federation gives k=4. A 1000-member federation gives k=1000.

**Break it:** (a) If the federation has few members and the verifier knows the member list, timing/behavioral analysis narrows it. (b) A stale or unique federation root pins the presentation to a narrow time window when that root was valid. (c) The composition_commitment and action_binding are appended to the STARK's public inputs (lines 1486-1495 of presentation.rs) -- these don't leak the issuer but do bind the proof to a specific action.

**Improve:** Larger federations, root rotation batching (many members join/leave per epoch so root freshness is less identifying).

## 3. Sender/Receiver Unlinkability in Transfers

**Partially implemented.** Notes use commitments (sender hidden) and nullifiers (spend hidden). The `NoteCommitment` includes random blinding (`cell/src/note.rs:162`). The nullifier is derived from intrinsic data only (no tree position, line 179), making double-spend detection global.

**Critical gap:** The executor processes `NoteSpend` + `NoteCreate` in the same turn (`executor.rs:1875-1948`). The `check_note_conservation` function (line 3086) collects ALL NoteSpend/NoteCreate effects from a single turn and checks sum-balance per asset type. This means **the executor sees which inputs map to which outputs** because they are in the same atomic turn. This is weaker than Zcash's shielded pool where the miner sees nothing about the mapping.

**Anonymity set for external observers:** The note tree is append-only per federation. All notes from all users in one federation share a single tree. External observers see only nullifiers (spend) and commitments (create) appearing on-chain, but the turn executor is a privileged observer.

**Break it:** The executor (turn processor) is the critical trust point. It sees the full turn including NoteSpend nullifiers + NoteCreate commitments + conservation check. A malicious executor can link sender to receiver trivially.

**Improve:** Split NoteSpend and NoteCreate into separate turns with a time delay, or use a ZK proving layer over the conservation check so the executor only verifies a proof that "sum inputs = sum outputs" without seeing which.

## 4. Transaction Graph Unlinkability

**Weak.** Notes live in a per-federation tree (not a global pool). The anonymity set for a given note is bounded by the federation's total note count. There is no inter-federation shared pool.

The nullifier set (`cell/src/nullifier_set.rs`) is a sorted append-only list with Merkle proofs. Observers of the nullifier set see the temporal ordering of spends. Combined with the note tree's append order, timing correlation is feasible.

**Break it:** Low-volume federations (few notes) make timing analysis trivial. Each spend reveals a unique nullifier that permanently marks the note as consumed -- an observer tracking all nullifiers can build a complete spend graph.

**Improve:** Decoy nullifiers (like Monero's ring signatures), shared cross-federation note pools, or batched epoch reveals where many nullifiers are published simultaneously.

## 5. Intent Unlinkability

**Partially implemented.** Intents are PUBLIC (gossip.rs line 9: "Intents themselves are PUBLIC: everyone sees 'someone needs X'"). The creator is identified only by a `CommitmentId` (anonymous commitment). Epoch-scoped nullifiers (`compute_stake_nullifier(commitment, epoch, counter)`, gossip.rs:239) ensure a stake can only publish K intents per epoch, and different epochs produce different nullifiers.

**Link "intent published" to "fulfillment completed":** Yes, a solver who fulfills an intent knows the `intent_id` and the `fulfiller` CommitmentId. The intent creator receives the fulfillment directly (not broadcast), but the commit-reveal protocol (gossip.rs:132-155) means the commitment is visible before the reveal. A passive observer sees: commitment published -> reveal after 5s -> intent removed. This links the timeline.

**Break it:** The `CommitmentId` is reused across intents from the same cclerk. Multiple intents from the same `CommitmentId` in one epoch are linkable (they share the same stake commitment). Rate limiting (10/min/creator) reveals activity patterns.

**Improve:** Per-intent ephemeral CommitmentIds (stealth addresses for intents), or blind the CommitmentId with epoch-specific randomness.

## 6. Network-Level Unlinkability

**Not implemented.** No Tor/mixnet integration visible in the codebase. The wire server (`wire/src/server.rs`) uses direct TCP/TLS connections. IP addresses are logged (`ServerEvent::ConnectionAccepted { remote }`). STARK proof generation takes measurable CPU time (~milliseconds) which creates timing fingerprints. Proof sizes vary by tree depth and fold chain length (variable-size messages).

**Break it:** Network observer correlates IP + timing + message size to deanonymize. TLS hides content but not metadata (connection timing, message sizes).

**Improve:** Tor integration, fixed-size proof padding, batched submission through relay nodes.

## 7. Cross-Federation Unlinkability

**Partially implemented.** The bridge uses `PortableProof` with a `source_root` field. The destination federation verifies the portable proof against `trusted_federation_roots` (executor.rs:132-137). The destination sees the source federation root (reveals which federation the note came from) but not the specific sender within that federation.

The nullifier is federation-independent by design (note.rs:13: "no tree position" in derivation), so cross-federation double-spend detection works without revealing the source identity.

**Break it:** If only one user bridges from federation A to federation B in a time window, the bridge transaction is trivially deanonymized by elimination.

**Improve:** Bridge relay pools that batch multiple cross-federation transfers, or zero-knowledge bridge proofs that hide the source federation.

## Missing from Academic Literature

| Technique | Status | Value |
|-----------|--------|-------|
| Decoy outputs (Monero-style) | Missing | Would expand anonymity set for note spends |
| Stealth addresses | Missing | Would give per-transaction receiver addresses |
| Differential privacy noise | Missing | Could add dummy intents/nullifiers |
| Mixnet delay | Missing | Would break timing correlation |
| k-anonymity verification | Missing | No mechanism to verify minimum anonymity set |
| Rerandomizable proofs | Partial | Blinding factor achieves this for membership |

## Summary Assessment

The strongest unlinkability is in credential presentation (multi-show + issuer blinding). The weakest is at the network layer (no metadata protection) and in the note transfer model (executor sees full turns). The intent layer is pseudonymous rather than anonymous. Cross-federation bridges leak source federation identity.
