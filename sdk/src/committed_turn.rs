//! Committed payment turn builder: constructs turns with Pedersen-committed note
//! values and conservation proofs.
//!
//! The [`CommittedTurnBuilder`] assembles a turn whose note effects carry
//! value commitments (hiding amounts) rather than cleartext values. It generates:
//! - Per-output Bulletproof range proofs (proving values in [0, 2^64))
//! - A Schnorr conservation proof (proving inputs and outputs balance)
//!
//! The resulting turn is accepted by the executor's committed conservation path
//! (`detect_commitment_mode -> Committed`).

use curve25519_dalek::scalar::Scalar;

use pyana_cell::CellId;
use pyana_cell::note::{NoteCommitment, Nullifier};
use pyana_cell::{BulletproofRangeProof, ValueCommitment, prove_conservation_with_range};
use pyana_turn::Turn;
use pyana_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, symbol};
use pyana_turn::forest::CallForest;

use crate::error::SdkError;

// =============================================================================
// Types
// =============================================================================

/// A committed note input (a note being spent).
///
/// The spender knows the value and blinding factor from their local opening.
/// The spending proof demonstrates Merkle membership and nullifier correctness
/// without revealing the value.
#[derive(Clone, Debug)]
pub struct CommittedNoteInput {
    /// The nullifier (reveals the note is spent, not which note).
    pub nullifier: Nullifier,
    /// Root of the note Merkle tree at proof-generation time.
    pub merkle_root: [u8; 32],
    /// The plaintext value (known to spender, hidden from executor).
    pub value: u64,
    /// The blinding factor from the value commitment opening.
    pub blinding: Scalar,
    /// Asset type identifier.
    pub asset_type: u64,
    /// Serialized STARK spending proof (proves ownership + Merkle membership).
    pub spending_proof: Vec<u8>,
}

/// A committed note output (a note being created).
///
/// Output blindings are generated fresh by the builder.
#[derive(Clone, Debug)]
pub struct CommittedNoteOutput {
    /// The value to commit (known to builder, hidden from executor).
    pub value: u64,
    /// Asset type identifier.
    pub asset_type: u64,
    /// Recipient's public key (or stealth address).
    pub recipient: [u8; 32],
}

/// Builder for turns with committed (privacy-preserving) note effects.
///
/// Accumulates inputs and outputs, then generates the full conservation proof
/// and value commitments in a single `build()` call.
pub struct CommittedTurnBuilder {
    inputs: Vec<CommittedNoteInput>,
    outputs: Vec<CommittedNoteOutput>,
}

impl CommittedTurnBuilder {
    /// Create a new empty builder.
    pub fn new() -> Self {
        Self {
            inputs: Vec::new(),
            outputs: Vec::new(),
        }
    }

    /// Add a committed note input (a note being spent).
    pub fn add_input(&mut self, input: CommittedNoteInput) -> &mut Self {
        self.inputs.push(input);
        self
    }

    /// Add a committed note output (a note being created).
    pub fn add_output(&mut self, output: CommittedNoteOutput) -> &mut Self {
        self.outputs.push(output);
        self
    }

    /// Build the turn with conservation proof.
    ///
    /// Steps:
    /// 1. Generate fresh output blindings.
    /// 2. Compute value commitments for all inputs and outputs.
    /// 3. Generate Bulletproof range proofs for outputs.
    /// 4. Compute excess blinding (sum_input - sum_output).
    /// 5. Generate FullConservationProof (Schnorr + range proofs).
    /// 6. Assemble NoteSpend effects with `value_commitment: Some(...)`.
    /// 7. Assemble NoteCreate effects with `value_commitment` + `range_proof`.
    /// 8. Set `turn.conservation_proof` to the serialized proof.
    ///
    /// # Arguments
    ///
    /// * `agent_cell` - The agent's cell ID (turn initiator).
    /// * `nonce` - Replay-protection nonce.
    /// * `fee` - Computron fee for this turn.
    pub fn build(&self, agent_cell: CellId, nonce: u64, fee: u64) -> Result<Turn, SdkError> {
        if self.inputs.is_empty() && self.outputs.is_empty() {
            return Err(SdkError::InvalidWitness(
                "committed turn must have at least one input or output".into(),
            ));
        }

        // 1. Generate fresh output blindings.
        let output_blindings: Vec<Scalar> = self
            .outputs
            .iter()
            .map(|_| {
                let mut bytes = [0u8; 64];
                getrandom::fill(&mut bytes).expect("getrandom failed");
                Scalar::from_bytes_mod_order_wide(&bytes)
            })
            .collect();

        // 2. Compute value commitments.
        //    We use the default (non-asset-specific) generator because the current
        //    BulletproofRangeProof implementation uses fixed PedersenGens(value_generator, R).
        //    Asset type discrimination is enforced by the spending proof binding, not
        //    by the commitment generator. Once STARK-based range proofs are available,
        //    this can migrate to asset-specific generators.
        let input_commitments: Vec<ValueCommitment> = self
            .inputs
            .iter()
            .map(|inp| ValueCommitment::commit(inp.value, &inp.blinding))
            .collect();

        let output_commitments: Vec<ValueCommitment> = self
            .outputs
            .iter()
            .zip(output_blindings.iter())
            .map(|(out, blinding)| ValueCommitment::commit(out.value, blinding))
            .collect();

        // 3. Compute excess blinding: sum(input_blindings) - sum(output_blindings).
        let sum_input_blindings = self
            .inputs
            .iter()
            .fold(Scalar::ZERO, |acc, inp| acc + inp.blinding);
        let sum_output_blindings = output_blindings.iter().fold(Scalar::ZERO, |acc, b| acc + b);
        let excess_blinding = sum_input_blindings - sum_output_blindings;

        // 4. Build the turn hash message for binding the conservation proof.
        //    We use a placeholder here and rebind after constructing the turn.
        //    Actually: the conservation proof message is the turn hash, but we don't
        //    have the turn hash yet. The design spec says to use the turn hash.
        //    We construct the turn first without the proof, compute hash, then
        //    generate the proof bound to that hash, and attach it.
        //    BUT: the turn hash includes the conservation_proof field being None vs Some.
        //    Looking at Turn::hash() — it does NOT hash conservation_proof (it hashes
        //    the call_forest which contains the effects). So we can compute the hash
        //    from the partial turn and then attach the proof.

        // 5. Build NoteSpend effects.
        let spend_effects: Vec<Effect> = self
            .inputs
            .iter()
            .zip(input_commitments.iter())
            .map(|(inp, vc)| Effect::NoteSpend {
                nullifier: inp.nullifier,
                note_tree_root: inp.merkle_root,
                value: inp.value,
                asset_type: inp.asset_type,
                spending_proof: inp.spending_proof.clone(),
                value_commitment: Some(vc.to_bytes().0),
            })
            .collect();

        // 6. Build NoteCreate effects.
        //    We need note commitments. For committed notes, the commitment is
        //    H(recipient || vc_bytes || asset_type || creation_nonce || rcm).
        //    We generate fresh randomness for each output.
        let create_effects: Vec<(Effect, BulletproofRangeProof)> = self
            .outputs
            .iter()
            .zip(output_commitments.iter())
            .zip(output_blindings.iter())
            .map(|((out, vc), blinding)| {
                let mut creation_nonce = [0u8; 32];
                getrandom::fill(&mut creation_nonce).expect("getrandom failed");
                let mut note_randomness = [0u8; 32];
                getrandom::fill(&mut note_randomness).expect("getrandom failed");

                // Compute the note commitment.
                let note_commitment = compute_committed_note_commitment(
                    &out.recipient,
                    vc,
                    out.asset_type,
                    &creation_nonce,
                    &note_randomness,
                );

                // Generate range proof.
                let range_proof = BulletproofRangeProof::prove_range(out.value, blinding);

                // Build encrypted note (placeholder: just the recipient + nonce for now).
                // In production this would be an ECIES-encrypted payload.
                let mut encrypted_note = Vec::with_capacity(64);
                encrypted_note.extend_from_slice(&out.recipient);
                encrypted_note.extend_from_slice(&creation_nonce);

                let effect = Effect::NoteCreate {
                    commitment: NoteCommitment(note_commitment),
                    value: out.value,
                    asset_type: out.asset_type,
                    encrypted_note,
                    value_commitment: Some(vc.to_bytes().0),
                    range_proof: Some(postcard::to_stdvec(&range_proof).unwrap_or_default()),
                };

                (effect, range_proof)
            })
            .collect();

        // 7. Assemble the action with all effects.
        let mut all_effects: Vec<Effect> = spend_effects;
        all_effects.extend(create_effects.into_iter().map(|(e, _rp)| e));

        let action = Action {
            target: agent_cell,
            method: symbol("committed_transfer"),
            args: Vec::new(),
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: all_effects,
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let mut call_forest = CallForest::new();
        call_forest.add_root(action);

        // 8. Build partial turn (without conservation_proof) to get the hash.
        let partial_turn = Turn {
            agent: agent_cell,
            nonce,
            call_forest,
            fee,
            memo: Some("committed transfer".into()),
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
        };

        let turn_hash = partial_turn.hash();

        // 9. Generate the FullConservationProof bound to the turn hash.
        let output_values: Vec<u64> = self.outputs.iter().map(|o| o.value).collect();
        let full_proof = prove_conservation_with_range(
            &input_commitments,
            &output_commitments,
            &output_values,
            &output_blindings,
            &excess_blinding,
            &turn_hash,
        );

        // 10. Serialize and attach.
        let proof_bytes = postcard::to_stdvec(&full_proof)
            .map_err(|e| SdkError::Wire(format!("failed to serialize conservation proof: {e}")))?;

        let turn = Turn {
            conservation_proof: Some(proof_bytes),
            ..partial_turn
        };

        Ok(turn)
    }
}

impl Default for CommittedTurnBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Compute the note commitment for a committed note.
///
/// ```text
/// H("pyana-committed-note v1", owner || vc_bytes || asset_type_le || creation_nonce || rcm)
/// ```
fn compute_committed_note_commitment(
    owner: &[u8; 32],
    value_commitment: &ValueCommitment,
    asset_type: u64,
    creation_nonce: &[u8; 32],
    note_randomness: &[u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-committed-note v1");
    hasher.update(owner);
    hasher.update(&value_commitment.to_bytes().0);
    hasher.update(&asset_type.to_le_bytes());
    hasher.update(creation_nonce);
    hasher.update(note_randomness);
    *hasher.finalize().as_bytes()
}

// =============================================================================
// Owned note helper (for wallet integration)
// =============================================================================

/// A note owned by this wallet with full opening data.
///
/// This is the minimum information needed to spend a committed note.
#[derive(Clone, Debug)]
pub struct OwnedNote {
    /// The nullifier for this note (pre-computed).
    pub nullifier: Nullifier,
    /// The Merkle root at the time of note creation (or a recent snapshot).
    pub merkle_root: [u8; 32],
    /// Plaintext value (private to the holder).
    pub value: u64,
    /// Blinding factor (private to the holder).
    pub blinding: Scalar,
    /// Asset type.
    pub asset_type: u64,
    /// Pre-generated spending proof (STARK).
    pub spending_proof: Vec<u8>,
}

impl From<&OwnedNote> for CommittedNoteInput {
    fn from(note: &OwnedNote) -> Self {
        CommittedNoteInput {
            nullifier: note.nullifier,
            merkle_root: note.merkle_root,
            value: note.value,
            blinding: note.blinding,
            asset_type: note.asset_type,
            spending_proof: note.spending_proof.clone(),
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_cell::{FullConservationProof, ValueCommitment, verify_conservation_with_range};

    /// Deterministic scalar for testing.
    fn test_scalar(seed: u8) -> Scalar {
        let mut bytes = [0u8; 64];
        bytes[0] = seed;
        bytes[1] = seed.wrapping_mul(37);
        Scalar::from_bytes_mod_order_wide(&bytes)
    }

    #[test]
    fn test_committed_turn_builder_basic() {
        let agent_cell = CellId([0xAA; 32]);

        let input = CommittedNoteInput {
            nullifier: Nullifier([0x11; 32]),
            merkle_root: [0x22; 32],
            value: 1000,
            blinding: test_scalar(1),
            asset_type: 1,
            spending_proof: vec![0xDE, 0xAD],
        };

        let output = CommittedNoteOutput {
            value: 1000,
            asset_type: 1,
            recipient: [0xBB; 32],
        };

        let mut builder = CommittedTurnBuilder::new();
        builder.add_input(input);
        builder.add_output(output);

        let turn = builder.build(agent_cell, 0, 0).unwrap();

        // The turn should have a conservation proof.
        assert!(turn.conservation_proof.is_some());

        // The call forest should have effects with value_commitment set.
        let effects = &turn.call_forest.roots[0].action.effects;
        assert_eq!(effects.len(), 2); // 1 spend + 1 create

        // Check that the spend effect has a value_commitment.
        match &effects[0] {
            Effect::NoteSpend {
                value_commitment, ..
            } => {
                assert!(value_commitment.is_some());
            }
            other => panic!("expected NoteSpend, got {:?}", other),
        }

        // Check that the create effect has a value_commitment and range_proof.
        match &effects[1] {
            Effect::NoteCreate {
                value_commitment,
                range_proof,
                ..
            } => {
                assert!(value_commitment.is_some());
                assert!(range_proof.is_some());
            }
            other => panic!("expected NoteCreate, got {:?}", other),
        }
    }

    #[test]
    fn test_committed_turn_conservation_proof_verifies() {
        let agent_cell = CellId([0xAA; 32]);
        let blinding_in = test_scalar(10);

        // 1000 in, 600 + 400 out (conservation holds).
        let input = CommittedNoteInput {
            nullifier: Nullifier([0x11; 32]),
            merkle_root: [0x22; 32],
            value: 1000,
            blinding: blinding_in,
            asset_type: 1,
            spending_proof: vec![0x01],
        };

        let output1 = CommittedNoteOutput {
            value: 600,
            asset_type: 1,
            recipient: [0xBB; 32],
        };
        let output2 = CommittedNoteOutput {
            value: 400,
            asset_type: 1,
            recipient: [0xCC; 32],
        };

        let mut builder = CommittedTurnBuilder::new();
        builder.add_input(input.clone());
        builder.add_output(output1);
        builder.add_output(output2);

        let turn = builder.build(agent_cell, 1, 0).unwrap();

        // Deserialize the conservation proof.
        let proof_bytes = turn.conservation_proof.as_ref().unwrap();
        let full_proof: FullConservationProof =
            postcard::from_bytes(proof_bytes).expect("deserialize proof");

        // Reconstruct the commitments from effects to verify.
        let mut input_vcs = Vec::new();
        let mut output_vcs = Vec::new();

        for effect in &turn.call_forest.roots[0].action.effects {
            match effect {
                Effect::NoteSpend {
                    value_commitment: Some(vc_bytes),
                    ..
                } => {
                    let vc =
                        ValueCommitment::from_bytes(&pyana_cell::ValueCommitmentBytes(*vc_bytes))
                            .unwrap();
                    input_vcs.push(vc);
                }
                Effect::NoteCreate {
                    value_commitment: Some(vc_bytes),
                    ..
                } => {
                    let vc =
                        ValueCommitment::from_bytes(&pyana_cell::ValueCommitmentBytes(*vc_bytes))
                            .unwrap();
                    output_vcs.push(vc);
                }
                _ => {}
            }
        }

        // Verify the conservation proof.
        let turn_hash = turn.hash();
        let result =
            verify_conservation_with_range(&input_vcs, &output_vcs, &full_proof, &turn_hash);
        assert!(
            result.is_ok(),
            "conservation proof should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_committed_turn_imbalanced_fails_verification() {
        let agent_cell = CellId([0xAA; 32]);
        let blinding_in = test_scalar(20);

        // 1000 in, 1001 out (imbalanced).
        let input = CommittedNoteInput {
            nullifier: Nullifier([0x33; 32]),
            merkle_root: [0x44; 32],
            value: 1000,
            blinding: blinding_in,
            asset_type: 1,
            spending_proof: vec![0x02],
        };

        let output = CommittedNoteOutput {
            value: 1001, // More than input!
            asset_type: 1,
            recipient: [0xDD; 32],
        };

        let mut builder = CommittedTurnBuilder::new();
        builder.add_input(input);
        builder.add_output(output);

        let turn = builder.build(agent_cell, 2, 0).unwrap();

        // Deserialize and verify -- should FAIL because values don't balance.
        let proof_bytes = turn.conservation_proof.as_ref().unwrap();
        let full_proof: FullConservationProof =
            postcard::from_bytes(proof_bytes).expect("deserialize proof");

        let mut input_vcs = Vec::new();
        let mut output_vcs = Vec::new();
        for effect in &turn.call_forest.roots[0].action.effects {
            match effect {
                Effect::NoteSpend {
                    value_commitment: Some(vc_bytes),
                    ..
                } => {
                    let vc =
                        ValueCommitment::from_bytes(&pyana_cell::ValueCommitmentBytes(*vc_bytes))
                            .unwrap();
                    input_vcs.push(vc);
                }
                Effect::NoteCreate {
                    value_commitment: Some(vc_bytes),
                    ..
                } => {
                    let vc =
                        ValueCommitment::from_bytes(&pyana_cell::ValueCommitmentBytes(*vc_bytes))
                            .unwrap();
                    output_vcs.push(vc);
                }
                _ => {}
            }
        }

        let turn_hash = turn.hash();
        let result =
            verify_conservation_with_range(&input_vcs, &output_vcs, &full_proof, &turn_hash);
        assert!(result.is_err(), "imbalanced turn should fail verification");
    }

    #[test]
    fn test_committed_turn_empty_rejected() {
        let agent_cell = CellId([0xAA; 32]);
        let builder = CommittedTurnBuilder::new();
        let result = builder.build(agent_cell, 0, 0);
        assert!(result.is_err());
    }

    #[test]
    fn test_committed_turn_multi_input_multi_output() {
        let agent_cell = CellId([0xAA; 32]);

        // 300 + 700 = 1000 in, 400 + 600 = 1000 out.
        let inputs = vec![
            CommittedNoteInput {
                nullifier: Nullifier([0x01; 32]),
                merkle_root: [0x10; 32],
                value: 300,
                blinding: test_scalar(30),
                asset_type: 1,
                spending_proof: vec![0x03],
            },
            CommittedNoteInput {
                nullifier: Nullifier([0x02; 32]),
                merkle_root: [0x10; 32],
                value: 700,
                blinding: test_scalar(31),
                asset_type: 1,
                spending_proof: vec![0x04],
            },
        ];
        let outputs = vec![
            CommittedNoteOutput {
                value: 400,
                asset_type: 1,
                recipient: [0xEE; 32],
            },
            CommittedNoteOutput {
                value: 600,
                asset_type: 1,
                recipient: [0xFF; 32],
            },
        ];

        let mut builder = CommittedTurnBuilder::new();
        for inp in &inputs {
            builder.add_input(inp.clone());
        }
        for out in &outputs {
            builder.add_output(out.clone());
        }

        let turn = builder.build(agent_cell, 3, 0).unwrap();
        assert!(turn.conservation_proof.is_some());

        // Verify.
        let proof_bytes = turn.conservation_proof.as_ref().unwrap();
        let full_proof: FullConservationProof =
            postcard::from_bytes(proof_bytes).expect("deserialize proof");

        let mut input_vcs = Vec::new();
        let mut output_vcs = Vec::new();
        for effect in &turn.call_forest.roots[0].action.effects {
            match effect {
                Effect::NoteSpend {
                    value_commitment: Some(vc_bytes),
                    ..
                } => {
                    let vc =
                        ValueCommitment::from_bytes(&pyana_cell::ValueCommitmentBytes(*vc_bytes))
                            .unwrap();
                    input_vcs.push(vc);
                }
                Effect::NoteCreate {
                    value_commitment: Some(vc_bytes),
                    ..
                } => {
                    let vc =
                        ValueCommitment::from_bytes(&pyana_cell::ValueCommitmentBytes(*vc_bytes))
                            .unwrap();
                    output_vcs.push(vc);
                }
                _ => {}
            }
        }

        let turn_hash = turn.hash();
        let result =
            verify_conservation_with_range(&input_vcs, &output_vcs, &full_proof, &turn_hash);
        assert!(
            result.is_ok(),
            "multi-input/output should verify: {:?}",
            result.err()
        );
    }
}
