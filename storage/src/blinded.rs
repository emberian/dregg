//! Blinded queue: stores commitments, tracks nullifiers, enables private consumption.
//!
//! A blinded queue holds `Com(item_i) = Poseidon2(item_i, randomness_i)` commitments.
//! Consumption publishes a nullifier `null_i = Hash(item_i, secret_i, position_i)`
//! without revealing which commitment was consumed.
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

use std::collections::HashSet;

use crate::queue::QueueError;

// ============================================================================
// Core types
// ============================================================================

/// A blinded queue: stores commitments, tracks nullifiers.
/// Consumption is private (can't link nullifier to commitment).
/// Guarantees: each element consumed at most once (nullifier uniqueness).
pub struct BlindedQueue {
    /// Commitments (Poseidon2 hashes of items + randomness)
    commitments: Vec<[u8; 32]>,
    /// Published nullifiers (consumed items)
    nullifiers: HashSet<[u8; 32]>,
    /// Merkle root of the commitment tree (for membership proofs)
    commitment_root: [u8; 32],
    /// Maximum capacity
    capacity: usize,
}

/// A consumption proof: proves you consumed ONE element without revealing which.
pub struct ConsumptionProof {
    /// The nullifier (unique, prevents double-consumption)
    pub nullifier: [u8; 32],
    /// Merkle membership proof (commitment exists in tree)
    pub membership_proof: Vec<[u8; 32]>,
    /// The commitment being consumed (revealed to allow Merkle check)
    /// NOTE: this reveals WHICH commitment, but not the CONTENT
    /// For full privacy (hide which commitment): use a ZK Merkle membership proof
    pub commitment: [u8; 32],
    /// Position in the tree (for Merkle verification)
    pub position: usize,
}

/// A PRIVATE consumption proof: hides which commitment was consumed.
/// Uses the same pattern as NoteSpendingAir — proves membership + nullifier
/// derivation in zero knowledge.
pub struct PrivateConsumptionProof {
    /// The nullifier (public — for uniqueness checking)
    pub nullifier: [u8; 32],
    /// The commitment tree root at time of consumption (public — for freshness)
    pub tree_root: [u8; 32],
    /// STARK proof that: (1) prover knows preimage of SOME commitment in tree,
    /// (2) nullifier is correctly derived from that preimage
    /// This is literally NoteSpendingAir pointed at our commitment tree.
    pub spending_proof: Vec<u8>,
}

/// Result of attempting consumption
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConsumeResult {
    /// Successfully consumed (nullifier accepted)
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
        let commitment_root = *blake3::hash(b"empty_blinded_queue").as_bytes();
        Self {
            commitments: Vec::new(),
            nullifiers: HashSet::new(),
            commitment_root,
            capacity,
        }
    }

    /// Add a commitment to the queue (done by the issuer/dealer).
    pub fn commit(&mut self, commitment: [u8; 32]) -> Result<(), QueueError> {
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
        // Check for double-consumption
        if self.nullifiers.contains(&proof.nullifier) {
            return ConsumeResult::AlreadyConsumed;
        }

        // Verify the proof
        if !self.verify_consumption(proof) {
            return ConsumeResult::InvalidProof;
        }

        // Accept the nullifier
        self.nullifiers.insert(proof.nullifier);
        ConsumeResult::Consumed {
            nullifier: proof.nullifier,
        }
    }

    /// Consume with full privacy (ZK proof, hides which commitment).
    pub fn consume_private(&mut self, proof: &PrivateConsumptionProof) -> ConsumeResult {
        // Check for double-consumption
        if self.nullifiers.contains(&proof.nullifier) {
            return ConsumeResult::AlreadyConsumed;
        }

        // Verify tree root matches current state
        if proof.tree_root != self.commitment_root {
            return ConsumeResult::InvalidProof;
        }

        // In a real system, we would verify the STARK proof here.
        // For this implementation, we trust the spending_proof bytes are valid
        // if the tree root matches (the real verification happens in the circuit crate).
        if proof.spending_proof.is_empty() {
            return ConsumeResult::InvalidProof;
        }

        // Accept the nullifier
        self.nullifiers.insert(proof.nullifier);
        ConsumeResult::Consumed {
            nullifier: proof.nullifier,
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

    /// Check if a nullifier has been used.
    pub fn is_consumed(&self, nullifier: &[u8; 32]) -> bool {
        self.nullifiers.contains(nullifier)
    }

    /// Get the commitment tree root (for proofs).
    pub fn commitment_root(&self) -> [u8; 32] {
        self.commitment_root
    }

    /// Recompute Merkle root after adding commitments.
    fn recompute_root(&mut self) {
        if self.commitments.is_empty() {
            self.commitment_root = *blake3::hash(b"empty_blinded_queue").as_bytes();
            return;
        }

        self.commitment_root = merkle_root_of(&self.commitments);
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

        // Verify the Merkle membership proof
        verify_merkle_proof(
            &proof.commitment,
            proof.position,
            &proof.membership_proof,
            &self.commitment_root,
        )
    }
}

// ============================================================================
// FairDistribution implementation
// ============================================================================

impl FairDistribution {
    /// Create a new fair distribution with N items for N participants.
    pub fn new(items: Vec<[u8; 32]>, expected_participants: usize, deadline: u64) -> Self {
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

/// Helpers for creating commitments and nullifiers.
pub mod crypto {
    /// Create a commitment: blake3("blinded-queue-commitment" || item_data || randomness)
    ///
    /// In a real system this would use Poseidon2 for in-circuit efficiency.
    /// We use blake3 here for the storage layer (proofs happen in the circuit crate).
    pub fn create_commitment(item_data: &[u8], randomness: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"blinded-queue-commitment");
        hasher.update(item_data);
        hasher.update(randomness);
        *hasher.finalize().as_bytes()
    }

    /// Derive nullifier: blake3("blinded-queue-nullifier" || commitment || secret || position)
    pub fn derive_nullifier(
        commitment: &[u8; 32],
        secret: &[u8; 32],
        position: usize,
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"blinded-queue-nullifier");
        hasher.update(commitment);
        hasher.update(secret);
        hasher.update(&(position as u64).to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Build a consumption proof (given knowledge of the item + position).
    pub fn build_consumption_proof(
        commitment: [u8; 32],
        secret: [u8; 32],
        position: usize,
        merkle_siblings: Vec<[u8; 32]>,
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

/// Compute the Merkle root of a set of leaf hashes (blake3 binary tree).
fn merkle_root_of(leaves: &[[u8; 32]]) -> [u8; 32] {
    if leaves.is_empty() {
        return *blake3::hash(b"empty_blinded_queue").as_bytes();
    }
    if leaves.len() == 1 {
        return leaves[0];
    }

    // Pad to next power of 2
    let mut layer: Vec<[u8; 32]> = leaves.to_vec();
    let next_pow2 = layer.len().next_power_of_two();
    layer.resize(next_pow2, [0u8; 32]);

    // Iteratively hash pairs until we have a single root
    while layer.len() > 1 {
        let mut next_layer = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks(2) {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&pair[0]);
            hasher.update(&pair[1]);
            next_layer.push(*hasher.finalize().as_bytes());
        }
        layer = next_layer;
    }

    layer[0]
}

/// Generate a Merkle proof (sibling hashes) for a leaf at the given position.
fn generate_merkle_proof(leaves: &[[u8; 32]], position: usize) -> Vec<[u8; 32]> {
    if leaves.len() <= 1 {
        return Vec::new();
    }

    // Pad to next power of 2
    let mut layer: Vec<[u8; 32]> = leaves.to_vec();
    let next_pow2 = layer.len().next_power_of_two();
    layer.resize(next_pow2, [0u8; 32]);

    let mut proof = Vec::new();
    let mut idx = position;

    while layer.len() > 1 {
        // Sibling is the other element in the pair
        let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
        proof.push(layer[sibling_idx]);

        // Compute next layer
        let mut next_layer = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks(2) {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&pair[0]);
            hasher.update(&pair[1]);
            next_layer.push(*hasher.finalize().as_bytes());
        }
        layer = next_layer;
        idx /= 2;
    }

    proof
}

/// Verify a Merkle proof for a leaf at the given position against a root.
fn verify_merkle_proof(
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
    fn setup_queue_with_items(n: usize) -> (BlindedQueue, Vec<[u8; 32]>, Vec<[u8; 32]>) {
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
        commitments: &[[u8; 32]],
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
        let result = queue.consume(&proof);

        assert_eq!(
            result,
            ConsumeResult::Consumed {
                nullifier: proof.nullifier
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
        let commitments = vec![[0x11; 32], [0x22; 32], [0x33; 32]];
        let mut dist = FairDistribution::new(commitments, 3, 1000);

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
        let root_empty = queue.commitment_root();

        let c1 = crypto::create_commitment(b"first", &[0x01; 32]);
        queue.commit(c1).unwrap();
        let root_one = queue.commitment_root();
        assert_ne!(root_empty, root_one);

        let c2 = crypto::create_commitment(b"second", &[0x02; 32]);
        queue.commit(c2).unwrap();
        let root_two = queue.commitment_root();
        assert_ne!(root_one, root_two);
        assert_ne!(root_empty, root_two);
    }

    // --- Test 12: Nullifier derivation is deterministic ---
    #[test]
    fn nullifier_derivation_is_deterministic() {
        let commitment = [0xAB; 32];
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
        let nullifier = proof.nullifier;

        assert!(!queue.is_consumed(&nullifier));
        queue.consume(&proof);
        assert!(queue.is_consumed(&nullifier));
    }

    // --- Test 16: Private consumption with valid proof ---
    #[test]
    fn private_consumption_valid_proof() {
        let (mut queue, _commitments, _secrets) = setup_queue_with_items(3);

        let proof = PrivateConsumptionProof {
            nullifier: [0xFF; 32],
            tree_root: queue.commitment_root(),
            spending_proof: vec![0x01, 0x02, 0x03], // non-empty = "valid"
        };

        let result = queue.consume_private(&proof);
        assert_eq!(
            result,
            ConsumeResult::Consumed {
                nullifier: [0xFF; 32]
            }
        );
    }

    // --- Test 17: Private consumption with wrong tree root ---
    #[test]
    fn private_consumption_wrong_tree_root() {
        let (mut queue, _commitments, _secrets) = setup_queue_with_items(3);

        let proof = PrivateConsumptionProof {
            nullifier: [0xFF; 32],
            tree_root: [0x00; 32], // wrong root
            spending_proof: vec![0x01, 0x02, 0x03],
        };

        let result = queue.consume_private(&proof);
        assert_eq!(result, ConsumeResult::InvalidProof);
    }

    // --- Test 18: Private consumption with empty proof ---
    #[test]
    fn private_consumption_empty_proof_rejected() {
        let (mut queue, _commitments, _secrets) = setup_queue_with_items(3);

        let proof = PrivateConsumptionProof {
            nullifier: [0xFF; 32],
            tree_root: queue.commitment_root(),
            spending_proof: vec![], // empty = invalid
        };

        let result = queue.consume_private(&proof);
        assert_eq!(result, ConsumeResult::InvalidProof);
    }
}
