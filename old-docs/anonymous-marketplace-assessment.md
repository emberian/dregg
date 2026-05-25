# Anonymous Marketplace Assessment

Assessment of pyana's infrastructure for a TRUE anonymous marketplace (buyer/seller identity hidden, amounts hidden, purchases hidden, unlinkable, disputable without deanonymization, private price discovery).

## 1. Buyer Anonymity

**Browsing:** PIR (2-server IT-PIR over BabyBear) allows querying the intent index without revealing which capability tag is sought. Sufficient for private listing discovery IF two non-colluding servers are available. Single-server deployment breaks this entirely.

**Ordering:** Orders use `CommitmentId` (pseudonymous). However, the compute-exchange app stores `consumer: CellId` in cleartext in the `Order` struct. The commit-reveal protocol hides order details temporarily but reveals them fully at reveal time. The marketplace operator sees the consumer identity after reveal.

**Post-purchase:** The settlement stores `consumer` and `provider` CellIds in cleartext. The escrow stores both parties. Seller trivially learns buyer identity through the settlement record.

**Verdict: INSUFFICIENT.** PIR covers discovery only. The entire order/settlement path is cleartext.

## 2. Seller Anonymity

**Listing:** Offerings store `provider: CellId` in cleartext. The qualification proof is verified against a federation root (proving capacity) but the provider identity is visible to all via `/offerings` endpoint.

**Post-purchase:** Same settlement cleartext issue. Buyer knows seller.

**Verdict: INSUFFICIENT.** No mechanism to list anonymously. Ring membership (BlindedMerklePoseidon2StarkAir) exists for credential presentation but is not wired into the marketplace offering path.

## 3. Payment Privacy (Amount Hidden)

**Pedersen commitments exist** with full homomorphic arithmetic, per-asset generators, conservation proofs (Schnorr binding signature), and CommittedNote abstraction. The RangeProof trait is defined but not implemented (no Bulletproofs backend yet).

**NOT wired into executor.** The executor's `check_note_conservation` sums cleartext values. The compute-exchange settlement stores `payment_amount: u64` and `sla_bond_amount: u64` in cleartext.

**Garbled circuit comparison** can compare values privately (neither party learns the other's input). Useful for "is my bid above the ask?" without revealing exact numbers. But the output label reveals the comparison result, and the circuit commitment is public.

**Verdict: PRIMITIVES EXIST, NOT INTEGRATED.** Conservation proof math works. Missing: range proofs, executor integration, settlement rewrite to use commitments.

## 4. Purchase Privacy (What Was Bought Hidden)

**Order details visible to operator.** The reveal phase exposes gpu_type, duration, rate, and fill constraints in cleartext. The `GET /offerings` endpoint is public.

**Sealed boxes** (in `cell/src/seal.rs`) provide X25519+ChaCha20-Poly1305 encryption. Could encrypt order details to only the matched provider. Not currently used in the exchange.

**Oblivious transfer** (1-of-N) allows selecting an offering without revealing which one. The protocol is complete and tested. Not integrated into the marketplace.

**Verdict: INSUFFICIENT.** OT and sealed boxes exist but the marketplace operates in cleartext. An observer or the operator sees all order details.

## 5. Unlinkability

**Presentation tags** give unlinkable multi-show for credentials (fresh randomness per presentation, blinded leaf). This is the strongest privacy property in the system.

**Intent CommitmentIds are reused** across intents from the same cclerk. Multiple orders from the same consumer in one epoch are linkable via shared CellId.

**Nullifiers** are globally unique but positionally independent. Note spends are unlinkable across federations. However, the marketplace does not use the note system for orders.

**Verdict: PARTIALLY AVAILABLE.** Credential presentations are unlinkable. Marketplace interactions are fully linkable (CellId reuse, cleartext settlement records).

## 6. Dispute Resolution

**Escrow exists** with `ProofPresented` and `SignedByAll` conditions plus timeout-based refund. Provider proves delivery via ZK proof to claim payment.

**NOT private.** Settlement stores both parties' CellIds. Disputes store `initiator: CellId` and `reason: String` in cleartext. A third-party arbiter would see both identities.

**What would be needed:** The delivery proof is already ZK (STARK). An arbiter could verify the proof without knowing who generated it IF the settlement were restructured to use commitment-based identity (blinded escrows where release conditions reference proof verification keys rather than party identities).

**Verdict: MECHANISM EXISTS, NOT PRIVATE.** The cryptographic machinery for proof-based dispute resolution is present. The data model leaks identities.

## 7. Price Discovery

**PIR** allows querying price information without revealing what you want (tag-based lookup). Effective for "what GPUs are available at what rate?" without revealing intent.

**Commit-reveal** prevents frontrunning: others see "someone committed" but not the price/details until reveal. After reveal, the price is public.

**Garbled circuits** could enable private price negotiation (compare bid vs ask without revealing either). The garbled_air.rs proves correct evaluation of comparison circuits.

**Verdict: PARTIALLY SUFFICIENT.** PIR + commit-reveal + garbled comparison covers most price discovery needs. Gap: post-reveal price exposure to the operator.

## Gaps for a True Anonymous Marketplace

| Gap | Primitive Needed | Closest Existing | Complexity |
|-----|-----------------|------------------|------------|
| Cleartext identities in settlement | Commitment-based escrow (parties identified only by blinded keys) | BlindedMerkle + presentation_tag | Medium: rewrite Settlement/Escrow structs |
| Executor sees amounts | Integrate ValueCommitment + ConservationProof into executor | value_commitment.rs (complete) | Medium-High: executor rewrite, range proof impl |
| Order details visible to operator | Encrypt orders to matched counterparty only (sealed box + OT selection) | seal.rs + oblivious_transfer.rs | Medium: compose existing primitives |
| CellId reuse across purchases | Per-interaction ephemeral identities (stealth addresses) | presentation_randomness pattern | Low-Medium: derive per-order ephemeral IDs |
| Offerings list provider identity | Ring membership for providers (prove "I have N GPUs" without revealing who) | BlindedMerklePoseidon2StarkAir | Medium: extend qualification to hide provider |
| Arbiter sees dispute parties | Blinded escrow with proof-only release conditions | garbled_air + delivery VK derivation | Medium: restructure escrow condition model |
| Range proofs not implemented | Bulletproofs or STARK bit-decomposition | RangeProof trait defined, no backend | Medium: implement Bulletproofs over Ristretto |
| Single-server PIR breaks privacy | Either deploy 2-server or move to computational PIR (lattice-based) | 2-server IT-PIR complete | Low (deployment) or High (cPIR impl) |

## Summary

Pyana has approximately 60-70% of the cryptographic primitives needed. The core gaps are integration, not invention: Pedersen commitments exist but the executor ignores them; OT and sealed boxes exist but the marketplace uses cleartext; ring membership proofs exist but offerings/settlements identify parties directly. The hardest missing piece is the range proof implementation (needed to prevent hidden inflation with committed values). The architectural gap is larger than the cryptographic gap: the compute-exchange app was built for correctness and liveness, not for privacy, and would need a near-complete rewrite of its data model to achieve true anonymity.
