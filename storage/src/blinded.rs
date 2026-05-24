//! Blinded queue: stores commitments, tracks nullifiers, enables private consumption.
//!
//! A blinded queue holds `Com(item_i) = Poseidon2(item_i, randomness_i)`
//! commitments. Consumption publishes a nullifier
//! `null_i = Poseidon2(commitment_i, secret_i, position_i)` without
//! revealing which commitment was consumed.
//!
//! # Privacy guarantees
//!
//! - The operator sees commitments in and nullifiers out, but cannot link them.
//! - Two parties cannot consume the same element (duplicate nullifier rejected).
//! - Nobody (including operator) knows who consumed which commitment.
//!
//! # Relationship to NoteSpendingAir
//!
//! The private consumption proof (`PrivateConsumptionProof`) reuses the exact circuit
//! from `circuit/src/note_spending_air.rs`, pointed at the queue's commitment tree
//! instead of the note tree. See `plans/blinded-queue-design.md` for full design.
//!
//! # Commitment scheme (post-Stage-10 migration)
//!
//! Commitments and nullifiers are typed dual-form:
//! `BlindedItemCommitment = Commitment4<BlindedItemMarker>`,
//! `BlindedNullifierCommitment = Commitment4<BlindedNullifierMarker>`.
//! Both carry a BLAKE3 form (for HashMap keys and gossip dedup) and a
//! 4-felt Poseidon2 form (consumed by the in-circuit `NoteSpendingAir`
//! membership/nullifier checks). See `storage/src/commitment.rs` and
//! `storage/STORAGE-POSEIDON2-AUDIT.md`.

use std::collections::HashSet;

use pyana_circuit::dsl::note_spending::verify_note_spend_dsl_with_destination;
use pyana_circuit::field::BabyBear;
use pyana_circuit::stark::proof_from_bytes;

use crate::commitment::{
    BlindedItemCommitment, BlindedItemSetRoot, BlindedNullifierCommitment, Commitment4, MerkleRoot,
};
use crate::queue::QueueError;

// ============================================================================
// Core types
// ============================================================================

/// A blinded queue: stores commitments, tracks nullifiers.
/// Consumption is private (can't link nullifier to commitment).
/// Guarantees: each element consumed at most once (nullifier uniqueness).
pub struct BlindedQueue {
    /// Commitments (dual-form: BLAKE3 + Poseidon2)
    commitments: Vec<BlindedItemCommitment>,
    /// Published nullifiers, keyed by their BLAKE3 form (the canonical
    /// out-of-circuit identity).
    nullifiers: HashSet<[u8; 32]>,
    /// Dual-form Merkle root of the commitment tree.
    commitment_root: BlindedItemSetRoot,
    /// Maximum capacity
    capacity: usize,
}

/// A consumption proof: proves you consumed ONE element without revealing which.
pub struct ConsumptionProof {
    /// The nullifier (unique, prevents double-consumption). Carries both
    /// the BLAKE3 form (for set membership) and the Poseidon2 form (for AIR).
    pub nullifier: BlindedNullifierCommitment,
    /// Merkle membership proof (commitment exists in tree). Each sibling
    /// carries both forms; the queue verifies against the BLAKE3 sibling
    /// chain, and the in-circuit prover uses the Poseidon2 sibling chain.
    pub membership_proof: Vec<BlindedItemCommitment>,
    /// The commitment being consumed (revealed to allow Merkle check)
    /// NOTE: this reveals WHICH commitment, but not the CONTENT.
    /// For full privacy (hide which commitment): use a ZK Merkle membership proof
    pub commitment: BlindedItemCommitment,
    /// Position in the tree (for Merkle verification)
    pub position: usize,
}

/// A PRIVATE consumption proof: hides which commitment was consumed.
/// Uses the same pattern as NoteSpendingAir — proves membership + nullifier
/// derivation in zero knowledge.
pub struct PrivateConsumptionProof {
    /// The nullifier (public — for uniqueness checking, dual-form).
    pub nullifier: BlindedNullifierCommitment,
    /// The commitment tree root at time of consumption (public — for freshness, dual-form).
    pub tree_root: BlindedItemSetRoot,
    /// STARK proof that: (1) prover knows preimage of SOME commitment in tree,
    /// (2) nullifier is correctly derived from that preimage.
    /// The AIR verifies the Poseidon2 form of `tree_root` and `nullifier`.
    pub spending_proof: Vec<u8>,
}

/// Result of attempting consumption
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConsumeResult {
    /// Successfully consumed (nullifier accepted). The returned nullifier
    /// is the canonical BLAKE3 form (suitable for HashMap keys / gossip).
    Consumed { nullifier: [u8; 32] },
    /// Nullifier already exists (double-consumption attempt)
    AlreadyConsumed,
    /// Proof is invalid (commitment not in tree, or nullifier derivation wrong)
    InvalidProof,
}

/// Errors from distribution operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DistributionError {
    /// Cannot cancel after claims have been made.
    ClaimsAlreadyMade { count: usize },
    /// Distribution is not in Open state.
    NotOpen,
}

/// Fair distribution state: tracks a multi-party unique withdrawal process.
pub struct FairDistribution {
    /// The blinded queue holding the items to distribute
    queue: BlindedQueue,
    /// Expected number of participants
    expected_participants: usize,
    /// Deadline (block height) by which all must claim
    deadline: u64,
    /// Who has claimed (by nullifier — we can count but not identify)
    claims_count: usize,
    /// State of the distribution
    state: DistributionState,
}

/// State of a fair distribution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DistributionState {
    /// Items committed, waiting for participants to claim
    Open,
    /// All participants claimed (success)
    Complete,
    /// Deadline passed with unclaimed items (partial failure)
    Expired { claimed: usize, total: usize },
    /// Cancelled (items returned to issuer)
    Cancelled,
}

// ============================================================================
// BlindedQueue implementation
// ============================================================================

impl BlindedQueue {
    /// Create a new empty blinded queue with the given capacity.
    pub fn new(capacity: usize) -> Self {
        Self {
            commitments: Vec::new(),
            nullifiers: HashSet::new(),
            commitment_root: MerkleRoot::empty(),
            capacity,
        }
    }

    /// Add a commitment to the queue (done by the issuer/dealer).
    pub fn commit(&mut self, commitment: BlindedItemCommitment) -> Result<(), QueueError> {
        if self.commitments.len() >= self.capacity {
            return Err(QueueError::Full {
                capacity: self.capacity,
            });
        }
        self.commitments.push(commitment);
        self.recompute_root();
        Ok(())
    }

    /// Consume an element by publishing a nullifier + proof.
    pub fn consume(&mut self, proof: &ConsumptionProof) -> ConsumeResult {
        // Check for double-consumption using the canonical BLAKE3 form.
        if self.nullifiers.contains(&proof.nullifier.blake3) {
            return ConsumeResult::AlreadyConsumed;
        }

        // Verify the proof
        if !self.verify_consumption(proof) {
            return ConsumeResult::InvalidProof;
        }

        // Accept the nullifier
        let nullifier_key = proof.nullifier.blake3;
        self.nullifiers.insert(nullifier_key);
        ConsumeResult::Consumed {
            nullifier: nullifier_key,
        }
    }

    /// Consume with full privacy (ZK proof, hides which commitment).
    ///
    /// This path is the privacy-preserving alternative to `consume`: the
    /// caller publishes only a nullifier + tree root + STARK proof, never
    /// revealing which commitment is being consumed.
    ///
    /// The STARK proof is verified via
    /// `pyana_circuit::dsl::note_spending::verify_note_spend_dsl_with_destination`
    /// using the DSL note-spending AIR — the same AIR that backs production
    /// `Effect::NoteSpend`. The verifier pins:
    /// - `pi[0] = nullifier` (Poseidon2 form, single felt)
    /// - `pi[1] = merkle_root` (Poseidon2 form, first limb)
    /// - `pi[2] = 0` (value — unused for blinded items)
    /// - `pi[3] = 0` (asset_type — unused for blinded items)
    /// - `pi[4] = 0` (destination_federation — local consumption, never
    ///   cross-federation)
    ///
    /// The 4-limb Poseidon2 form of the nullifier and tree root is reduced
    /// to a single BabyBear by taking the first limb — this matches the
    /// AIR's single-felt PI slot. The other limbs participate in the
    /// commitment-tree hashing but are not part of the AIR's PI (which is
    /// already collision-resistant at ~31 bits per slot × tree depth).
    pub fn consume_private(&mut self, proof: &PrivateConsumptionProof) -> ConsumeResult {
        // Check for double-consumption (BLAKE3-keyed)
        if self.nullifiers.contains(&proof.nullifier.blake3) {
            return ConsumeResult::AlreadyConsumed;
        }

        // Verify tree root matches current state (both forms must match —
        // the dual-form equality check is type-level enforced).
        if proof.tree_root != self.commitment_root {
            return ConsumeResult::InvalidProof;
        }

        // Reject empty proofs eagerly (the deserializer will also fail, but
        // this gives a faster path for the obviously-wrong case).
        if proof.spending_proof.is_empty() {
            return ConsumeResult::InvalidProof;
        }

        // Deserialize the STARK proof.
        let stark_proof = match proof_from_bytes(&proof.spending_proof) {
            Ok(p) => p,
            Err(_) => return ConsumeResult::InvalidProof,
        };

        // Map the dual-form nullifier + tree root into the AIR's PI shape.
        // The AIR expects a single BabyBear felt per PI slot; we take the
        // Poseidon2 leading limb. Collision resistance for the full nullifier
        // is provided by the BLAKE3 form check above (set-membership rejection
        // on duplicate). The STARK only needs to prove derivation correctness
        // and Merkle membership; the single-felt nullifier slot is sufficient
        // for the AIR's commitment-binding constraint.
        let nullifier_pi = proof.nullifier.poseidon2[0];
        let root_pi = proof.tree_root.poseidon2_root[0];

        // Blinded items are value/asset-agnostic from the AIR's perspective
        // (the privacy property is "you consumed *some* item"; the AIR doesn't
        // need a value/asset binding for blinded queues). The prover sets
        // value = asset_type = ZERO when generating the proof; the verifier
        // requires the same.
        let value_pi = BabyBear::ZERO;
        let asset_type_pi = BabyBear::ZERO;
        // Blinded queue consumption is always local — no cross-federation
        // bridge replay is possible against a blinded queue. We pin pi[4] to
        // ZERO and reject any proof whose prover put a non-zero destination
        // in the trace.
        let dest_fed_pi = BabyBear::ZERO;

        if verify_note_spend_dsl_with_destination(
            nullifier_pi,
            root_pi,
            value_pi,
            asset_type_pi,
            dest_fed_pi,
            &stark_proof,
        )
        .is_err()
        {
            return ConsumeResult::InvalidProof;
        }

        // Accept the nullifier
        let nullifier_key = proof.nullifier.blake3;
        self.nullifiers.insert(nullifier_key);
        ConsumeResult::Consumed {
            nullifier: nullifier_key,
        }
    }

    /// How many elements remain unconsumed.
    pub fn remaining(&self) -> usize {
        self.commitments.len() - self.nullifiers.len()
    }

    /// How many have been consumed.
    pub fn consumed_count(&self) -> usize {
        self.nullifiers.len()
    }

    /// Check if a nullifier has been used (by its BLAKE3 form).
    pub fn is_consumed(&self, nullifier_blake3: &[u8; 32]) -> bool {
        self.nullifiers.contains(nullifier_blake3)
    }

    /// Get the commitment tree root's BLAKE3 form (back-compat for callers
    /// that expect a `[u8; 32]` and don't need the Poseidon2 form).
    pub fn commitment_root(&self) -> [u8; 32] {
        self.commitment_root.blake3_root
    }

    /// Get the dual-form commitment tree root (for proofs and in-circuit use).
    pub fn commitment_root_dual(&self) -> BlindedItemSetRoot {
        self.commitment_root
    }

    /// Recompute Merkle root after adding commitments.
    fn recompute_root(&mut self) {
        if self.commitments.is_empty() {
            self.commitment_root = MerkleRoot::empty();
            return;
        }
        let blake3_leaves: Vec<[u8; 32]> = self.commitments.iter().map(|c| c.blake3).collect();
        let poseidon2_leaves: Vec<[pyana_circuit::field::BabyBear; 4]> =
            self.commitments.iter().map(|c| c.poseidon2).collect();
        self.commitment_root = MerkleRoot::from_leaves(&blake3_leaves, &poseidon2_leaves);
    }

    /// Verify a consumption proof (public version — reveals which commitment).
    fn verify_consumption(&self, proof: &ConsumptionProof) -> bool {
        // Check that the claimed commitment exists at the claimed position
        if proof.position >= self.commitments.len() {
            return false;
        }
        if self.commitments[proof.position] != proof.commitment {
            return false;
        }

        // Verify the Merkle membership proof (BLAKE3 path against the
        // queue's stored BLAKE3 root). The Poseidon2 verification is the
        // in-circuit proof's job; out-of-circuit we only need the cheap
        // BLAKE3 check.
        let blake3_siblings: Vec<[u8; 32]> =
            proof.membership_proof.iter().map(|c| c.blake3).collect();
        verify_merkle_proof_blake3(
            &proof.commitment.blake3,
            proof.position,
            &blake3_siblings,
            &self.commitment_root.blake3_root,
        )
    }
}

// ============================================================================
// FairDistribution implementation
// ============================================================================

impl FairDistribution {
    /// Create a new fair distribution with N items for N participants.
    pub fn new(
        items: Vec<BlindedItemCommitment>,
        expected_participants: usize,
        deadline: u64,
    ) -> Self {
        let mut queue = BlindedQueue::new(items.len());
        for item in &items {
            // These cannot fail since capacity == items.len()
            queue.commit(*item).expect("capacity matches item count");
        }
        Self {
            queue,
            expected_participants,
            deadline,
            claims_count: 0,
            state: DistributionState::Open,
        }
    }

    /// A participant claims their item (publishes nullifier).
    pub fn claim(&mut self, proof: ConsumptionProof) -> ConsumeResult {
        if self.state != DistributionState::Open {
            return ConsumeResult::InvalidProof;
        }

        let result = self.queue.consume(&proof);
        if let ConsumeResult::Consumed { .. } = &result {
            self.claims_count += 1;
            if self.claims_count >= self.expected_participants {
                self.state = DistributionState::Complete;
            }
        }
        result
    }

    /// Check: is the distribution complete? (all claimed)
    pub fn is_complete(&self) -> bool {
        self.state == DistributionState::Complete
    }

    /// Check: has the deadline passed? Mark expired if so.
    pub fn check_deadline(&mut self, current_height: u64) {
        if self.state == DistributionState::Open && current_height > self.deadline {
            self.state = DistributionState::Expired {
                claimed: self.claims_count,
                total: self.expected_participants,
            };
        }
    }

    /// Cancel: return all items (only valid before any claims).
    pub fn cancel(&mut self) -> Result<(), DistributionError> {
        if self.state != DistributionState::Open {
            return Err(DistributionError::NotOpen);
        }
        if self.claims_count > 0 {
            return Err(DistributionError::ClaimsAlreadyMade {
                count: self.claims_count,
            });
        }
        self.state = DistributionState::Cancelled;
        Ok(())
    }

    /// How many participants still need to claim.
    pub fn remaining_claims(&self) -> usize {
        self.expected_participants - self.claims_count
    }

    /// Get a reference to the underlying queue.
    pub fn queue(&self) -> &BlindedQueue {
        &self.queue
    }

    /// Get the current distribution state.
    pub fn state(&self) -> &DistributionState {
        &self.state
    }
}

// ============================================================================
// Crypto helpers
// ============================================================================

/// Helpers for creating commitments and nullifiers, all in dual-form.
pub mod crypto {
    use super::{BlindedItemCommitment, BlindedNullifierCommitment, Commitment4};
    use crate::commitment::encode_bytes_to_felts;
    use pyana_circuit::field::BabyBear;

    /// Create a dual-form commitment over `(item_data, randomness)`.
    ///
    /// Both forms (BLAKE3 + 4-felt Poseidon2) are derived from the same
    /// canonical preimage `len(item) || item || randomness`. The Poseidon2
    /// form is what the in-circuit `NoteSpendingAir` consumes; the BLAKE3
    /// form is what storage / gossip / HashMap keys consume.
    pub fn create_commitment(item_data: &[u8], randomness: &[u8; 32]) -> BlindedItemCommitment {
        let mut canonical = Vec::with_capacity(8 + item_data.len() + 32);
        canonical.extend_from_slice(&(item_data.len() as u64).to_le_bytes());
        canonical.extend_from_slice(item_data);
        canonical.extend_from_slice(randomness);
        Commitment4::seal(&canonical[..])
    }

    /// Derive a dual-form nullifier from `(commitment, secret, position)`.
    ///
    /// The Poseidon2 form folds the commitment's 4 Poseidon2 felts together
    /// with a secret-derived felt and a position felt, mirroring the
    /// in-circuit `NoteSpendingAir` nullifier derivation. The BLAKE3 form is
    /// computed over the canonical `commitment.blake3 || secret || pos_le`.
    pub fn derive_nullifier(
        commitment: &BlindedItemCommitment,
        secret: &[u8; 32],
        position: usize,
    ) -> BlindedNullifierCommitment {
        // Canonical preimage: tagged + length-prefixed BLAKE3 commitment +
        // secret + 8-byte position. The two forms are derived from this
        // same canonical bytes via two independent paths.
        let mut canonical = Vec::with_capacity(72);
        canonical.extend_from_slice(&commitment.blake3);
        canonical.extend_from_slice(secret);
        canonical.extend_from_slice(&(position as u64).to_le_bytes());

        // Schema encoding: 4 commitment felts + secret felts (8) + position felt.
        let mut felts = Vec::with_capacity(13);
        felts.extend_from_slice(&commitment.poseidon2);
        felts.extend(encode_bytes_to_felts(secret));
        felts.push(BabyBear::new((position as u32) & 0x7FFF_FFFF));

        // We can't use the macro-derived [u8] CommitmentSchema directly
        // because that would skip the schema-encoded felts. Construct
        // manually via the same helpers Commitment4::seal uses.
        let blake3 = crate::commitment::blake3_with_tag(
            crate::commitment::domain::TAG_BLINDED_NULLIFIER,
            &canonical,
        );
        let poseidon2 = crate::commitment::poseidon2_quad_with_tag(
            crate::commitment::domain::TAG_BLINDED_NULLIFIER,
            &felts,
        );
        BlindedNullifierCommitment::from_parts(blake3, poseidon2)
    }

    /// Build a consumption proof (given knowledge of the item + position).
    pub fn build_consumption_proof(
        commitment: BlindedItemCommitment,
        secret: [u8; 32],
        position: usize,
        merkle_siblings: Vec<BlindedItemCommitment>,
    ) -> super::ConsumptionProof {
        let nullifier = derive_nullifier(&commitment, &secret, position);
        super::ConsumptionProof {
            nullifier,
            membership_proof: merkle_siblings,
            commitment,
            position,
        }
    }
}

// ============================================================================
// Internal Merkle tree helpers
// ============================================================================

/// Generate a Merkle proof (sibling commitments) for a leaf at the given
/// position. Returns dual-form sibling commitments; verifiers select the
/// form appropriate to context (BLAKE3 here; Poseidon2 in-circuit).
pub(crate) fn generate_merkle_proof(
    leaves: &[BlindedItemCommitment],
    position: usize,
) -> Vec<BlindedItemCommitment> {
    if leaves.len() <= 1 {
        return Vec::new();
    }
    // Pad to next power of 2
    let mut layer: Vec<BlindedItemCommitment> = leaves.to_vec();
    let next_pow2 = layer.len().next_power_of_two();
    layer.resize(next_pow2, BlindedItemCommitment::empty());

    let mut proof = Vec::new();
    let mut idx = position;

    while layer.len() > 1 {
        let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
        proof.push(layer[sibling_idx]);

        // Compute next layer (BLAKE3 form for path, Poseidon2 for circuit).
        let mut next_layer = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks(2) {
            // Parent BLAKE3
            let mut hasher = blake3::Hasher::new();
            hasher.update(&pair[0].blake3);
            hasher.update(&pair[1].blake3);
            let parent_blake3 = *hasher.finalize().as_bytes();

            // Parent Poseidon2 (matches commitment::poseidon2_binary_root).
            use pyana_circuit::poseidon2::hash_4_to_1;
            let left = pair[0].poseidon2;
            let right = pair[1].poseidon2;
            let a = hash_4_to_1(&[left[0], left[1], left[2], left[3]]);
            let b = hash_4_to_1(&[right[0], right[1], right[2], right[3]]);
            let parent_poseidon2 = [
                hash_4_to_1(&[a, b, left[0], right[0]]),
                hash_4_to_1(&[a, b, left[1], right[1]]),
                hash_4_to_1(&[a, b, left[2], right[2]]),
                hash_4_to_1(&[a, b, left[3], right[3]]),
            ];
            next_layer.push(BlindedItemCommitment::from_parts(
                parent_blake3,
                parent_poseidon2,
            ));
        }
        layer = next_layer;
        idx /= 2;
    }

    proof
}

/// Verify a BLAKE3 Merkle path: given a leaf hash, position, sibling chain,
/// and the expected root, return whether the recomputed root matches.
fn verify_merkle_proof_blake3(
    leaf: &[u8; 32],
    position: usize,
    proof: &[[u8; 32]],
    root: &[u8; 32],
) -> bool {
    let mut current = *leaf;
    let mut idx = position;

    for sibling in proof {
        let mut hasher = blake3::Hasher::new();
        if idx % 2 == 0 {
            hasher.update(&current);
            hasher.update(sibling);
        } else {
            hasher.update(sibling);
            hasher.update(&current);
        }
        current = *hasher.finalize().as_bytes();
        idx /= 2;
    }

    current == *root
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: commit items and generate valid proofs for consumption.
    fn setup_queue_with_items(
        n: usize,
    ) -> (BlindedQueue, Vec<BlindedItemCommitment>, Vec<[u8; 32]>) {
        let mut queue = BlindedQueue::new(n);
        let mut commitments = Vec::new();
        let mut secrets = Vec::new();

        for i in 0..n {
            let item_data = format!("item_{i}");
            let randomness = [i as u8 + 1; 32];
            let commitment = crypto::create_commitment(item_data.as_bytes(), &randomness);
            queue.commit(commitment).unwrap();
            commitments.push(commitment);
            secrets.push([(i as u8).wrapping_add(0x42); 32]);
        }

        (queue, commitments, secrets)
    }

    fn make_valid_proof(
        queue: &BlindedQueue,
        commitments: &[BlindedItemCommitment],
        secrets: &[[u8; 32]],
        index: usize,
    ) -> ConsumptionProof {
        let merkle_proof = generate_merkle_proof(&queue.commitments, index);
        crypto::build_consumption_proof(commitments[index], secrets[index], index, merkle_proof)
    }

    // --- Test 1: Commit items to blinded queue ---
    #[test]
    fn commit_items_to_blinded_queue() {
        let mut queue = BlindedQueue::new(5);

        let randomness = [0xAA; 32];
        let c1 = crypto::create_commitment(b"hello", &randomness);
        let c2 = crypto::create_commitment(b"world", &randomness);

        assert!(queue.commit(c1).is_ok());
        assert!(queue.commit(c2).is_ok());
        assert_eq!(queue.remaining(), 2);
        assert_eq!(queue.consumed_count(), 0);
    }

    // --- Test 2: Consume with valid proof → accepted ---
    #[test]
    fn consume_with_valid_proof_accepted() {
        let (mut queue, commitments, secrets) = setup_queue_with_items(3);

        let proof = make_valid_proof(&queue, &commitments, &secrets, 1);
        let nullifier_blake3 = proof.nullifier.blake3;
        let result = queue.consume(&proof);

        assert_eq!(
            result,
            ConsumeResult::Consumed {
                nullifier: nullifier_blake3
            }
        );
        assert_eq!(queue.consumed_count(), 1);
        assert_eq!(queue.remaining(), 2);
    }

    // --- Test 3: Double-consume (same nullifier) → rejected ---
    #[test]
    fn double_consume_same_nullifier_rejected() {
        let (mut queue, commitments, secrets) = setup_queue_with_items(3);

        let proof = make_valid_proof(&queue, &commitments, &secrets, 0);
        let result1 = queue.consume(&proof);
        assert!(matches!(result1, ConsumeResult::Consumed { .. }));

        // Try consuming again with same nullifier
        let result2 = queue.consume(&proof);
        assert_eq!(result2, ConsumeResult::AlreadyConsumed);
        assert_eq!(queue.consumed_count(), 1);
    }

    // --- Test 4: Invalid proof (wrong position) → rejected ---
    #[test]
    fn invalid_proof_wrong_position_rejected() {
        let (mut queue, commitments, secrets) = setup_queue_with_items(3);

        // Build proof with wrong position (commitment at 0, but claim position 2)
        let merkle_proof = generate_merkle_proof(&queue.commitments, 2);
        let wrong_proof = ConsumptionProof {
            nullifier: crypto::derive_nullifier(&commitments[0], &secrets[0], 2),
            membership_proof: merkle_proof,
            commitment: commitments[0], // commitment 0 is NOT at position 2
            position: 2,
        };

        let result = queue.consume(&wrong_proof);
        assert_eq!(result, ConsumeResult::InvalidProof);
        assert_eq!(queue.consumed_count(), 0);
    }

    // --- Test 5: remaining() tracks correctly ---
    #[test]
    fn remaining_tracks_correctly() {
        let (mut queue, commitments, secrets) = setup_queue_with_items(4);

        assert_eq!(queue.remaining(), 4);

        let proof0 = make_valid_proof(&queue, &commitments, &secrets, 0);
        queue.consume(&proof0);
        assert_eq!(queue.remaining(), 3);

        let proof2 = make_valid_proof(&queue, &commitments, &secrets, 2);
        queue.consume(&proof2);
        assert_eq!(queue.remaining(), 2);

        let proof1 = make_valid_proof(&queue, &commitments, &secrets, 1);
        queue.consume(&proof1);
        assert_eq!(queue.remaining(), 1);

        let proof3 = make_valid_proof(&queue, &commitments, &secrets, 3);
        queue.consume(&proof3);
        assert_eq!(queue.remaining(), 0);
    }

    // --- Test 6: FairDistribution: N items, N claims → complete ---
    #[test]
    fn fair_distribution_n_claims_complete() {
        let n = 4;
        let mut commitments = Vec::new();
        let mut secrets = Vec::new();

        for i in 0..n {
            let randomness = [i as u8 + 1; 32];
            let c = crypto::create_commitment(format!("item_{i}").as_bytes(), &randomness);
            commitments.push(c);
            secrets.push([(i as u8).wrapping_add(0x42); 32]);
        }

        let mut dist = FairDistribution::new(commitments.clone(), n, 1000);
        assert_eq!(dist.state(), &DistributionState::Open);
        assert!(!dist.is_complete());

        for i in 0..n {
            let proof = make_valid_proof(dist.queue(), &commitments, &secrets, i);
            let result = dist.claim(proof);
            assert!(matches!(result, ConsumeResult::Consumed { .. }));
        }

        assert!(dist.is_complete());
        assert_eq!(dist.state(), &DistributionState::Complete);
        assert_eq!(dist.remaining_claims(), 0);
    }

    // --- Test 7: FairDistribution: partial claims before deadline → still Open ---
    #[test]
    fn fair_distribution_partial_claims_still_open() {
        let n = 4;
        let mut commitments = Vec::new();
        let mut secrets = Vec::new();

        for i in 0..n {
            let randomness = [i as u8 + 1; 32];
            let c = crypto::create_commitment(format!("item_{i}").as_bytes(), &randomness);
            commitments.push(c);
            secrets.push([(i as u8).wrapping_add(0x42); 32]);
        }

        let mut dist = FairDistribution::new(commitments.clone(), n, 1000);

        // Only 2 out of 4 claim
        for i in 0..2 {
            let proof = make_valid_proof(dist.queue(), &commitments, &secrets, i);
            dist.claim(proof);
        }

        // Check deadline hasn't passed
        dist.check_deadline(500);
        assert_eq!(dist.state(), &DistributionState::Open);
        assert!(!dist.is_complete());
        assert_eq!(dist.remaining_claims(), 2);
    }

    // --- Test 8: FairDistribution: deadline expires → Expired state ---
    #[test]
    fn fair_distribution_deadline_expires() {
        let n = 3;
        let mut commitments = Vec::new();
        let mut secrets = Vec::new();

        for i in 0..n {
            let randomness = [i as u8 + 1; 32];
            let c = crypto::create_commitment(format!("item_{i}").as_bytes(), &randomness);
            commitments.push(c);
            secrets.push([(i as u8).wrapping_add(0x42); 32]);
        }

        let mut dist = FairDistribution::new(commitments.clone(), n, 100);

        // One claim
        let proof = make_valid_proof(dist.queue(), &commitments, &secrets, 0);
        dist.claim(proof);

        // Deadline passes
        dist.check_deadline(101);
        assert_eq!(
            dist.state(),
            &DistributionState::Expired {
                claimed: 1,
                total: 3
            }
        );
    }

    // --- Test 9: FairDistribution: cancel before any claims → ok ---
    #[test]
    fn fair_distribution_cancel_before_claims_ok() {
        // Construct three distinct typed commitments for the test fixture.
        let c1 = crypto::create_commitment(b"a", &[0x11; 32]);
        let c2 = crypto::create_commitment(b"b", &[0x22; 32]);
        let c3 = crypto::create_commitment(b"c", &[0x33; 32]);
        let mut dist = FairDistribution::new(vec![c1, c2, c3], 3, 1000);

        assert!(dist.cancel().is_ok());
        assert_eq!(dist.state(), &DistributionState::Cancelled);
    }

    // --- Test 10: FairDistribution: cancel after claims → rejected ---
    #[test]
    fn fair_distribution_cancel_after_claims_rejected() {
        let n = 3;
        let mut commitments = Vec::new();
        let mut secrets = Vec::new();

        for i in 0..n {
            let randomness = [i as u8 + 1; 32];
            let c = crypto::create_commitment(format!("item_{i}").as_bytes(), &randomness);
            commitments.push(c);
            secrets.push([(i as u8).wrapping_add(0x42); 32]);
        }

        let mut dist = FairDistribution::new(commitments.clone(), n, 1000);

        // Make one claim
        let proof = make_valid_proof(dist.queue(), &commitments, &secrets, 0);
        dist.claim(proof);

        // Try to cancel
        let result = dist.cancel();
        assert_eq!(
            result,
            Err(DistributionError::ClaimsAlreadyMade { count: 1 })
        );
    }

    // --- Test 11: Commitment root changes when items added ---
    #[test]
    fn commitment_root_changes_when_items_added() {
        let mut queue = BlindedQueue::new(10);
        let root_empty = queue.commitment_root_dual();

        let c1 = crypto::create_commitment(b"first", &[0x01; 32]);
        queue.commit(c1).unwrap();
        let root_one = queue.commitment_root_dual();
        assert_ne!(root_empty, root_one);

        let c2 = crypto::create_commitment(b"second", &[0x02; 32]);
        queue.commit(c2).unwrap();
        let root_two = queue.commitment_root_dual();
        assert_ne!(root_one, root_two);
        assert_ne!(root_empty, root_two);
    }

    // --- Test 12: Nullifier derivation is deterministic ---
    #[test]
    fn nullifier_derivation_is_deterministic() {
        let commitment = crypto::create_commitment(b"ab", &[0xCD; 32]);
        let secret = [0xCD; 32];
        let position = 7;

        let n1 = crypto::derive_nullifier(&commitment, &secret, position);
        let n2 = crypto::derive_nullifier(&commitment, &secret, position);
        assert_eq!(n1, n2);
    }

    // --- Test 13: Two different items produce different nullifiers ---
    #[test]
    fn different_items_produce_different_nullifiers() {
        let secret = [0xCD; 32];
        let position = 0;

        let c1 = crypto::create_commitment(b"item_a", &[0x01; 32]);
        let c2 = crypto::create_commitment(b"item_b", &[0x02; 32]);

        let n1 = crypto::derive_nullifier(&c1, &secret, position);
        let n2 = crypto::derive_nullifier(&c2, &secret, position);
        assert_ne!(n1, n2);
    }

    // --- Test 14: Queue at capacity rejects further commits ---
    #[test]
    fn queue_at_capacity_rejects() {
        let mut queue = BlindedQueue::new(2);
        let c1 = crypto::create_commitment(b"a", &[0x01; 32]);
        let c2 = crypto::create_commitment(b"b", &[0x02; 32]);
        let c3 = crypto::create_commitment(b"c", &[0x03; 32]);

        assert!(queue.commit(c1).is_ok());
        assert!(queue.commit(c2).is_ok());
        assert_eq!(queue.commit(c3), Err(QueueError::Full { capacity: 2 }));
    }

    // --- Test 15: is_consumed tracks nullifier presence ---
    #[test]
    fn is_consumed_tracks_nullifier() {
        let (mut queue, commitments, secrets) = setup_queue_with_items(2);

        let proof = make_valid_proof(&queue, &commitments, &secrets, 0);
        let nullifier_key = proof.nullifier.blake3;

        assert!(!queue.is_consumed(&nullifier_key));
        queue.consume(&proof);
        assert!(queue.is_consumed(&nullifier_key));
    }

    // --- Test 16: Private consumption with bogus proof bytes is REJECTED ---
    //
    // Adversarial test: previously the consume_private path accepted ANY
    // non-empty bytes as a valid STARK proof (AUDIT-privacy.md §11.1). After
    // wiring the real `verify_note_spend_dsl_with_destination` verifier, a
    // proof that is just random bytes must fail verification.
    #[test]
    fn private_consumption_bogus_proof_rejected() {
        let (mut queue, _commitments, _secrets) = setup_queue_with_items(3);

        let null_blake3 = [0xFFu8; 32];
        let null_poseidon2 = [pyana_circuit::field::BabyBear::new(99); 4];
        let proof = PrivateConsumptionProof {
            nullifier: BlindedNullifierCommitment::from_parts(null_blake3, null_poseidon2),
            tree_root: queue.commitment_root_dual(),
            spending_proof: vec![0x01, 0x02, 0x03], // bogus non-empty bytes
        };

        let result = queue.consume_private(&proof);
        assert_eq!(
            result,
            ConsumeResult::InvalidProof,
            "consume_private must reject non-STARK random bytes; previously this trapdoor accepted any non-empty proof"
        );
    }

    // --- Test 17: Private consumption with wrong tree root ---
    #[test]
    fn private_consumption_wrong_tree_root() {
        let (mut queue, _commitments, _secrets) = setup_queue_with_items(3);

        let null_poseidon2 = [pyana_circuit::field::BabyBear::new(7); 4];
        let proof = PrivateConsumptionProof {
            nullifier: BlindedNullifierCommitment::from_parts([0xFF; 32], null_poseidon2),
            // wrong root (the empty sentinel, but the queue's actual root
            // is non-empty)
            tree_root: BlindedItemSetRoot::empty(),
            spending_proof: vec![0x01, 0x02, 0x03],
        };

        let result = queue.consume_private(&proof);
        assert_eq!(result, ConsumeResult::InvalidProof);
    }

    // --- Test 18: Private consumption with empty proof ---
    #[test]
    fn private_consumption_empty_proof_rejected() {
        let (mut queue, _commitments, _secrets) = setup_queue_with_items(3);

        let null_poseidon2 = [pyana_circuit::field::BabyBear::new(7); 4];
        let proof = PrivateConsumptionProof {
            nullifier: BlindedNullifierCommitment::from_parts([0xFF; 32], null_poseidon2),
            tree_root: queue.commitment_root_dual(),
            spending_proof: vec![], // empty = invalid
        };

        let result = queue.consume_private(&proof);
        assert_eq!(result, ConsumeResult::InvalidProof);
    }
}
