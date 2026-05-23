# Committed Payments: Full Execution Path Integration

## 1. Executor Changes (`turn/src/executor.rs`)

The dispatcher (`check_note_conservation`) already routes between cleartext and committed modes via `detect_commitment_mode`. The remaining work:

**`check_committed_conservation`** currently deserializes a `ConservationProof` (Schnorr excess only). Upgrade to `FullConservationProof`:

```rust
fn check_committed_conservation(turn: &Turn) -> Result<(), TurnError> {
    let proof: FullConservationProof = postcard::from_bytes(
        turn.conservation_proof.as_ref().ok_or(/* ... */)?
    )?;
    let (inputs, outputs) = Self::collect_committed_notes(&turn.call_forest)?;
    let turn_hash = turn.hash();
    // Schnorr excess check (sum(inputs) - sum(outputs) == 0)
    verify_conservation_full(&inputs, &outputs, &proof, &turn_hash)?;
    // Range proofs on outputs (already called via verify_output_range_proofs)
    Ok(())
}
```

Replace `ConservationProof` with `FullConservationProof` in the deserialization. The `verify_conservation_full` function checks the Schnorr excess signature AND validates each output's Bulletproof range proof in a single pass. No new fields on `Turn` are needed; the existing `conservation_proof: Option<Vec<u8>>` carries the serialized `FullConservationProof`.

**Mixed-mode rejection** is already handled (`NoteCommitmentMode::Mixed => Err(...)`). No change needed.

## 2. Committed Note Tree (`store/src/note_tree.rs`)

The existing `NoteTree` stores `NoteCommitment` values (32-byte hashes). For committed notes, the leaf is `CommittedNote::note_commitment` -- same 32-byte type, same append-only semantics. Therefore:

- **No separate tree required.** The `note_commitment` field of `CommittedNote` is computed as `BLAKE3("pyana-committed-note v1", owner || vc_bytes || asset_type || nonce || rcm)`, which is already a 32-byte value compatible with the existing `NoteCommitment` type.
- The dual BLAKE3/Poseidon2 tree continues to work unchanged: committed note commitments are appended exactly like cleartext note commitments.
- The nullifier derivation path is identical: `nullifier = H(spending_key || position)`.

The trees are not "mixed" in any problematic sense -- both committed and cleartext note commitments are just 32-byte leaves. What matters for conservation is whether the *effects in a single turn* are all-committed or all-cleartext, which the executor already enforces.

## 3. Conservation Proof Verification Flow

```
Client constructs turn:
  1. For each input:  NoteSpend { value_commitment: Some(vc_bytes), ... }
  2. For each output: NoteCreate { value_commitment: Some(vc_bytes), range_proof: Some(bp), ... }
  3. Compute excess = sum(output_blindings) - sum(input_blindings)
  4. Sign excess with Schnorr over turn_hash
  5. Attach conservation_proof = postcard::to_vec(&FullConservationProof { schnorr_sig, range_proofs })

Executor verifies:
  1. detect_commitment_mode -> Committed
  2. Deserialize FullConservationProof from conservation_proof bytes
  3. Reconstruct commitment points from value_commitment bytes on each effect
  4. verify_conservation_full: check excess Schnorr signature binds to turn_hash
  5. verify_output_range_proofs: each output's Bulletproof is valid for its commitment
```

## 4. Spending Proof Binding (`circuit/src/note_spending_air.rs`)

The `NoteSpendingAir` currently takes `(value, asset_type)` as public inputs. For committed notes:

- Public inputs become: `(value_commitment_bytes, asset_type, nullifier, note_tree_root)`
- The witness (private) includes: `(value, blinding, owner, rcm, nonce, merkle_path)`
- The circuit proves:
  1. `value_commitment == value * V_asset + blinding * R` (commitment opening)
  2. `note_commitment == H(owner || value_commitment || asset_type || nonce || rcm)` (preimage)
  3. `note_commitment in tree at note_tree_root` (Merkle membership)
  4. `nullifier == H(spending_key || position)` (correct nullifier derivation)

This replaces the cleartext value binding with a commitment binding. The conservation proof then operates on the commitment points without needing to know the values.

## 5. SDK / Wallet Changes (`intent/src/fulfillment.rs`)

`execute_fulfillment_flow_with_key` currently builds cleartext `NoteSpend`/`NoteCreate` effects. Add a parallel path:

```rust
pub fn execute_committed_fulfillment_flow(
    wallet: &WalletState,  // holds openings for owned notes
    intent: &Intent,
    fulfillment: &Fulfillment,
    executor: &TurnExecutor,
) -> Result<TurnReceipt, FulfillmentError> {
    // 1. Select input notes, retrieve their CommittedNoteOpenings
    // 2. Generate output CommittedNoteOpenings (new blinding factors)
    // 3. Build NoteSpend effects with value_commitment = Some(...)
    // 4. Build NoteCreate effects with value_commitment + range_proof
    // 5. Compute FullConservationProof (Schnorr excess + Bulletproofs)
    // 6. Assemble Turn with conservation_proof = Some(serialized_proof)
    // 7. Submit to executor
}
```

The wallet must track `CommittedNoteOpening` for each owned note (stored encrypted locally). The SDK exposes `CommittedTurnBuilder` that handles blinding factor arithmetic and proof generation.

## 6. Cross-Federation Bridging

Committed notes compose with the existing bridge protocol:

- **Lock phase**: source federation appends a `BridgeLock` with the committed note's `value_commitment`. The commitment is re-blinded: `vc' = vc + r_bridge * R`.
- **Mint phase**: destination federation mints with `vc'`. Conservation at the destination is proven using `vc'` directly.
- **Algebraic composability**: `sum(inputs) == sum(outputs)` holds across re-blinding because the bridge protocol transfers the blinding offset out-of-band to the recipient.

## 7. Performance Impact

| Operation | Latency | Size |
|-----------|---------|------|
| Bulletproof range proof (per output) | ~5ms | 672 bytes |
| Schnorr excess signature (per turn) | ~1ms | 64 bytes |
| Commitment point computation | ~0.1ms | 32 bytes |
| Spending proof (STARK, per input) | ~200ms | ~50KB |

A typical 2-input 2-output committed turn adds ~12ms and 1.4KB over the cleartext path. The STARK spending proofs dominate latency regardless.

## 8. Migration Path

| Phase | Behavior |
|-------|----------|
| Phase 1 (current) | Committed effects exist; executor routes per-turn. Opt-in. |
| Phase 2 | Default to committed for new turns. Cleartext accepted but deprecated. |
| Phase 3 | Cleartext removed. All conservation via FullConservationProof. |

Phase 1 requires no protocol-breaking changes -- the `value_commitment` field is already `Option` on both `NoteSpend` and `NoteCreate`, and the mode detection is live in the executor.
