//! Strand-based addressing for the unified fabric (Phase 6).
//!
//! In the unified lace, the primary address is a STRAND (a public key that produces blocks).
//! A "group" is a set of strands with shared ordering. Groups can overlap.
//! This replaces FederationId as the routing target.
//!
//! # Addressing Modes
//!
//! - **Strand**: address a specific block-producing entity (direct messaging)
//! - **Group**: address any member of a reference group (multicast)
//! - **Capability**: address by swiss number (whoever holds it)
//! - **Federation**: legacy backward-compat addressing
//!
//! # Per-Group Checkpoints
//!
//! Checkpoint proofs are scoped to a single reference group. They prove:
//! "at height H, the state of group G was commitment C, and all turns up to H
//! were valid." This enables pruning of the blocklace below the checkpoint.
//!
//! # Intra-Fabric Migration
//!
//! Since all groups share one DAG, migrating a strand between groups is simply
//! changing which group includes that strand in its tau computation. No state
//! export is needed -- the strand's blocks remain in the shared DAG.

use serde::{Deserialize, Serialize};

use crate::Blocklace;
use crate::constitution::GovernedReferenceGroup;
use crate::ordering::ReferenceGroup;

// =============================================================================
// Core Address Types
// =============================================================================

/// A strand address: the public key of a block-producing entity.
pub type StrandId = [u8; 32];

/// A group address: content-hash of the group's reference set.
/// Deterministic: same participants (sorted) = same group address.
pub type GroupId = [u8; 32];

/// A federation ID (backward compat re-export from the addressing layer).
/// In the unified model, a FederationId IS just a GroupId with legacy semantics.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FederationId(pub [u8; 32]);

impl std::fmt::Debug for FederationId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "FedId({})",
            self.0[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

impl std::fmt::Display for FederationId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0[..8]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

// =============================================================================
// Fabric Address
// =============================================================================

/// Addressing modes in the unified fabric.
///
/// Replaces the old model where everything was addressed by FederationId.
/// The fabric supports multiple addressing modes depending on the use case.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FabricAddress {
    /// Address a specific strand (direct, like sending to a person).
    Strand(StrandId),
    /// Address a group (deliver to any member who can process it).
    Group(GroupId),
    /// Address by capability (whoever holds this swiss number).
    Capability { swiss: [u8; 32] },
    /// Legacy: federation-based addressing (backward compat).
    Federation(FederationId),
}

impl FabricAddress {
    /// Create a strand address from a public key.
    pub fn strand(key: [u8; 32]) -> Self {
        Self::Strand(key)
    }

    /// Create a group address from a reference group.
    pub fn group(group: &ReferenceGroup) -> Self {
        Self::Group(group.compute_id())
    }

    /// Create a capability address from a swiss number.
    pub fn capability(swiss: [u8; 32]) -> Self {
        Self::Capability { swiss }
    }

    /// Create a federation address (legacy).
    pub fn federation(id: FederationId) -> Self {
        Self::Federation(id)
    }

    /// Returns true if this is a strand address.
    pub fn is_strand(&self) -> bool {
        matches!(self, Self::Strand(_))
    }

    /// Returns true if this is a group address.
    pub fn is_group(&self) -> bool {
        matches!(self, Self::Group(_))
    }

    /// Returns true if this is a capability address.
    pub fn is_capability(&self) -> bool {
        matches!(self, Self::Capability { .. })
    }

    /// Returns true if this is a legacy federation address.
    pub fn is_federation(&self) -> bool {
        matches!(self, Self::Federation(_))
    }
}

// =============================================================================
// Per-Group Checkpoint Proofs
// =============================================================================

/// An attestation: a participant's signature over a checkpoint hash.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Attestation {
    /// The signer's public key (must be in the participant set).
    pub signer: [u8; 32],
    /// The Ed25519 signature over the checkpoint hash.
    pub signature: [u8; 64],
}

impl Serialize for Attestation {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTuple;
        let mut tup = serializer.serialize_tuple(2)?;
        tup.serialize_element(&self.signer)?;
        tup.serialize_element(&self.signature.as_ref())?;
        tup.end()
    }
}

impl<'de> Deserialize<'de> for Attestation {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let (signer, sig_bytes): ([u8; 32], Vec<u8>) = Deserialize::deserialize(deserializer)?;
        let signature: [u8; 64] = sig_bytes
            .try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for signature"))?;
        Ok(Attestation { signer, signature })
    }
}

/// A checkpoint proof for a specific reference group.
///
/// Proves: "at height H, the state of group G was commitment C,
/// and all turns up to H were valid."
///
/// Checkpoints enable:
/// - Blocklace pruning (history below the checkpoint is compressed into the IVC proof)
/// - Light client verification (only need the checkpoint, not full history)
/// - Migration source proofs (proves state at the point of migration)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GroupCheckpoint {
    /// Which group this checkpoint covers.
    pub group_id: GroupId,
    /// The participants at checkpoint time.
    pub participants: Vec<StrandId>,
    /// Height at which the checkpoint was taken.
    pub height: u64,
    /// Combined state commitment (Merkle root of all cells in this group).
    pub state_commitment: [u8; 32],
    /// IVC proof covering all turns from genesis (or last checkpoint) to here.
    pub ivc_proof: Option<Vec<u8>>,
    /// Signatures from threshold of participants attesting to this checkpoint.
    pub attestations: Vec<Attestation>,
}

impl GroupCheckpoint {
    /// Create a new checkpoint for a group at the given height.
    pub fn new(group: &ReferenceGroup, height: u64, state_commitment: [u8; 32]) -> Self {
        GroupCheckpoint {
            group_id: group.compute_id(),
            participants: group.participants.clone(),
            height,
            state_commitment,
            ivc_proof: None,
            attestations: Vec::new(),
        }
    }

    /// Attach an IVC proof to this checkpoint.
    pub fn with_ivc_proof(mut self, proof: Vec<u8>) -> Self {
        self.ivc_proof = Some(proof);
        self
    }

    /// Add an attestation (signature from a participant).
    pub fn add_attestation(&mut self, signer: [u8; 32], signature: [u8; 64]) {
        self.attestations.push(Attestation { signer, signature });
    }

    /// Verify the checkpoint is attested by at least `threshold` participants.
    ///
    /// Checks that:
    /// 1. At least `threshold` distinct participants have signed.
    /// 2. All signers are in the participant set.
    ///
    /// Note: This does NOT verify the actual signatures (Ed25519 verification
    /// would require the full block to sign over). It verifies the structural
    /// requirement that enough distinct valid participants have attested.
    pub fn verify_attestations(&self, threshold: usize) -> bool {
        if self.attestations.len() < threshold {
            return false;
        }

        let participant_set: std::collections::HashSet<[u8; 32]> =
            self.participants.iter().copied().collect();

        // Count distinct valid signers.
        let distinct_signers: std::collections::HashSet<[u8; 32]> = self
            .attestations
            .iter()
            .filter(|a| participant_set.contains(&a.signer))
            .map(|a| a.signer)
            .collect();

        distinct_signers.len() >= threshold
    }

    /// Prune blocklace below this checkpoint (safe -- all history compressed into IVC).
    ///
    /// Removes blocks from the given participants that are at heights below this
    /// checkpoint. Returns the number of blocks pruned.
    ///
    /// Safety: only prune if the checkpoint has been verified (attestations + IVC proof).
    pub fn prune_below(&self, blocklace: &mut Blocklace) -> usize {
        let participant_set: std::collections::HashSet<[u8; 32]> =
            self.participants.iter().copied().collect();

        // Collect block IDs to remove: blocks from participants that are
        // causally "below" this checkpoint height.
        // We use a simple heuristic: blocks with sequence < height from participants.
        let to_remove: Vec<[u8; 32]> = blocklace
            .blocks
            .iter()
            .filter(|(_, block)| {
                participant_set.contains(&block.creator) && block.sequence < self.height
            })
            .map(|(id, _)| *id)
            .collect();

        let count = to_remove.len();
        for id in &to_remove {
            blocklace.blocks.remove(id);
        }
        count
    }

    /// Compute the checkpoint hash (for signing / attestation binding).
    pub fn checkpoint_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-group-checkpoint-v1");
        hasher.update(&self.group_id);
        hasher.update(&self.height.to_le_bytes());
        hasher.update(&self.state_commitment);
        hasher.update(&(self.participants.len() as u32).to_le_bytes());
        for p in &self.participants {
            hasher.update(p);
        }
        *hasher.finalize().as_bytes()
    }
}

// =============================================================================
// Intra-Fabric Migration
// =============================================================================

/// Error type for migration operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MigrationError {
    /// The strand is not a member of the source group.
    NotInSourceGroup,
    /// The strand is already a member of the destination group.
    AlreadyInDestination,
    /// The state proof is invalid or missing.
    InvalidStateProof,
}

impl std::fmt::Display for MigrationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotInSourceGroup => write!(f, "strand is not a member of the source group"),
            Self::AlreadyInDestination => {
                write!(f, "strand is already a member of the destination group")
            }
            Self::InvalidStateProof => write!(f, "invalid or missing state proof"),
        }
    }
}

impl std::error::Error for MigrationError {}

/// Migrate a cell from one reference group to another within the same fabric.
///
/// Much simpler than cross-federation migration (no separate DAGs to bridge):
/// the cell's strand just changes which group it's ordered with.
///
/// In the unified model, migration is JUST changing references:
/// - Source group members stop including this strand in their tau
/// - Destination group members start including it
/// - No state export needed (the state is IN the strand's blocks, which are in the shared DAG)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct IntraFabricMigration {
    /// The strand being migrated.
    pub strand: StrandId,
    /// Source group (leaving).
    pub from_group: GroupId,
    /// Destination group (joining).
    pub to_group: GroupId,
    /// State proof at migration point (IVC covering history in source group).
    pub state_proof: Vec<u8>,
    /// Height in source group at migration.
    pub migration_height: u64,
}

impl IntraFabricMigration {
    /// Create a new migration record.
    pub fn new(
        strand: StrandId,
        from_group: GroupId,
        to_group: GroupId,
        state_proof: Vec<u8>,
        migration_height: u64,
    ) -> Self {
        IntraFabricMigration {
            strand,
            from_group,
            to_group,
            state_proof,
            migration_height,
        }
    }

    /// Perform the migration: remove from source group, add to destination.
    ///
    /// In the unified model this is JUST changing references:
    /// - Source group members stop including this strand in their tau
    /// - Destination group members start including it
    /// - No state export needed (the state is IN the strand's blocks, which are in the shared DAG)
    pub fn execute(
        &self,
        source: &mut GovernedReferenceGroup,
        destination: &mut GovernedReferenceGroup,
    ) -> Result<(), MigrationError> {
        // Verify the strand is in the source group.
        if !source.is_member(&self.strand) {
            return Err(MigrationError::NotInSourceGroup);
        }

        // Verify the strand is NOT already in the destination.
        if destination.is_member(&self.strand) {
            return Err(MigrationError::AlreadyInDestination);
        }

        // Remove from source group.
        source.group.participants.retain(|k| k != &self.strand);
        source.group.threshold =
            crate::ordering::supermajority_threshold(source.group.participants.len());

        // Add to destination group.
        destination.group.participants.push(self.strand);
        destination.group.participants.sort();
        destination.group.threshold =
            crate::ordering::supermajority_threshold(destination.group.participants.len());

        Ok(())
    }
}

// =============================================================================
// Backward Compatibility Layer
// =============================================================================

/// Translate a legacy FederationId to a FabricAddress.
///
/// A FederationId maps directly to the `Federation` variant, preserving
/// backward compatibility with old CapTP and wire protocol code.
pub fn federation_to_fabric(fed_id: &FederationId) -> FabricAddress {
    FabricAddress::Federation(*fed_id)
}

/// Attempt to extract a FederationId from a FabricAddress.
///
/// - `Federation(id)` -> Some(id)
/// - `Group(id)` -> Some(FederationId(id))  (groups can be treated as federations)
/// - Other variants -> None
pub fn fabric_to_federation(addr: &FabricAddress) -> Option<FederationId> {
    match addr {
        FabricAddress::Federation(id) => Some(*id),
        FabricAddress::Group(id) => Some(FederationId(*id)),
        _ => None,
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constitution::GovernedReferenceGroup;
    use crate::ordering::ReferenceGroup;

    fn make_key(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    // ─── FabricAddress Tests ────────────────────────────────────────────────

    #[test]
    fn fabric_address_strand_creation_and_matching() {
        let key = make_key(1);
        let addr = FabricAddress::strand(key);
        assert!(addr.is_strand());
        assert!(!addr.is_group());
        assert!(!addr.is_capability());
        assert!(!addr.is_federation());
        match addr {
            FabricAddress::Strand(k) => assert_eq!(k, key),
            _ => panic!("expected Strand variant"),
        }
    }

    #[test]
    fn fabric_address_group_computed_from_reference_group_is_deterministic() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let group = ReferenceGroup::new(participants.clone(), 10);

        let addr1 = FabricAddress::group(&group);
        let addr2 = FabricAddress::group(&group);

        assert_eq!(addr1, addr2);
        assert!(addr1.is_group());

        // Same participants in different order should produce the same group ID
        // (compute_id sorts internally).
        let group_reordered = ReferenceGroup::new(vec![make_key(3), make_key(1), make_key(2)], 10);
        let addr3 = FabricAddress::group(&group_reordered);
        assert_eq!(addr1, addr3);
    }

    #[test]
    fn fabric_address_capability_creation() {
        let swiss = [0xAB; 32];
        let addr = FabricAddress::capability(swiss);
        assert!(addr.is_capability());
        match addr {
            FabricAddress::Capability { swiss: s } => assert_eq!(s, swiss),
            _ => panic!("expected Capability variant"),
        }
    }

    #[test]
    fn fabric_address_federation_creation() {
        let fed = FederationId([0xFE; 32]);
        let addr = FabricAddress::federation(fed);
        assert!(addr.is_federation());
        match addr {
            FabricAddress::Federation(f) => assert_eq!(f, fed),
            _ => panic!("expected Federation variant"),
        }
    }

    // ─── GroupId Determinism Tests ──────────────────────────────────────────

    #[test]
    fn group_id_same_participants_regardless_of_order() {
        // This is the key invariant: sorted internally, so order doesn't matter.
        let g1 = ReferenceGroup::new(vec![make_key(5), make_key(3), make_key(1)], 10);
        let g2 = ReferenceGroup::new(vec![make_key(1), make_key(3), make_key(5)], 10);
        let g3 = ReferenceGroup::new(vec![make_key(3), make_key(5), make_key(1)], 10);

        let id1 = g1.compute_id();
        let id2 = g2.compute_id();
        let id3 = g3.compute_id();

        assert_eq!(id1, id2);
        assert_eq!(id2, id3);
    }

    #[test]
    fn group_id_differs_for_different_participants() {
        let g1 = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);
        let g2 = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(4)], 10);

        assert_ne!(g1.compute_id(), g2.compute_id());
    }

    // ─── GroupCheckpoint Tests ──────────────────────────────────────────────

    #[test]
    fn group_checkpoint_creation_and_attestation_verification() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let group = ReferenceGroup::new(participants.clone(), 10);
        let state = [0xCC; 32];

        let mut checkpoint = GroupCheckpoint::new(&group, 100, state);
        assert_eq!(checkpoint.height, 100);
        assert_eq!(checkpoint.state_commitment, state);
        assert_eq!(checkpoint.group_id, group.compute_id());

        // Add attestations from all 3 participants.
        checkpoint.add_attestation(make_key(1), [0x11; 64]);
        checkpoint.add_attestation(make_key(2), [0x22; 64]);
        checkpoint.add_attestation(make_key(3), [0x33; 64]);

        // With threshold 3 (supermajority of 3), all 3 attestations should pass.
        assert!(checkpoint.verify_attestations(3));
        // Threshold of 2 should also pass.
        assert!(checkpoint.verify_attestations(2));
        // Threshold of 1 should pass.
        assert!(checkpoint.verify_attestations(1));
    }

    #[test]
    fn checkpoint_with_insufficient_attestations_fails() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let group = ReferenceGroup::new(participants, 10);

        let mut checkpoint = GroupCheckpoint::new(&group, 50, [0xDD; 32]);

        // Only 1 attestation.
        checkpoint.add_attestation(make_key(1), [0x11; 64]);

        // Threshold of 2 should fail.
        assert!(!checkpoint.verify_attestations(2));
        // Threshold of 3 should fail.
        assert!(!checkpoint.verify_attestations(3));
        // Threshold of 1 should pass.
        assert!(checkpoint.verify_attestations(1));
    }

    #[test]
    fn checkpoint_attestation_from_non_participant_not_counted() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let group = ReferenceGroup::new(participants, 10);

        let mut checkpoint = GroupCheckpoint::new(&group, 75, [0xEE; 32]);

        // Add attestation from a non-participant.
        checkpoint.add_attestation(make_key(99), [0x99; 64]);
        // Add attestation from one valid participant.
        checkpoint.add_attestation(make_key(1), [0x11; 64]);

        // Only 1 valid attestation, so threshold 2 should fail.
        assert!(!checkpoint.verify_attestations(2));
        // Threshold 1 should pass (one valid signer).
        assert!(checkpoint.verify_attestations(1));
    }

    #[test]
    fn checkpoint_prune_removes_old_blocks() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let group = ReferenceGroup::new(participants.clone(), 10);

        let mut blocklace = Blocklace::new();

        // Insert some blocks with low sequence numbers.
        let b1 = crate::Block::new(make_key(1), 0, vec![], vec![1]);
        let b1_id = b1.id();
        blocklace.insert(b1).unwrap();

        let b2 = crate::Block::new(make_key(2), 0, vec![], vec![2]);
        let b2_id = b2.id();
        blocklace.insert(b2).unwrap();

        // Insert a block with high sequence (above checkpoint height).
        let b3 = crate::Block::new(make_key(1), 100, vec![b1_id], vec![3]);
        let b3_id = b3.id();
        blocklace.insert(b3).unwrap();

        assert_eq!(blocklace.len(), 3);

        // Create checkpoint at height 50.
        let checkpoint = GroupCheckpoint::new(&group, 50, [0xFF; 32]);

        // Prune below height 50: blocks with sequence < 50 from participants.
        let pruned = checkpoint.prune_below(&mut blocklace);

        // b1 (seq 0) and b2 (seq 0) should be pruned.
        assert_eq!(pruned, 2);
        // b3 (seq 100) should remain.
        assert!(blocklace.contains(&b3_id));
        assert!(!blocklace.contains(&b1_id));
        assert!(!blocklace.contains(&b2_id));
    }

    // ─── IntraFabricMigration Tests ─────────────────────────────────────────

    #[test]
    fn intra_fabric_migration_strand_moves_from_group_a_to_group_b() {
        let mut source =
            GovernedReferenceGroup::open(vec![make_key(1), make_key(2), make_key(3)], 10);
        let mut dest = GovernedReferenceGroup::open(vec![make_key(4), make_key(5)], 10);

        let migration = IntraFabricMigration::new(
            make_key(2),
            source.reference_group().compute_id(),
            dest.reference_group().compute_id(),
            vec![0xAA; 32], // dummy state proof
            50,
        );

        assert!(source.is_member(&make_key(2)));
        assert!(!dest.is_member(&make_key(2)));

        let result = migration.execute(&mut source, &mut dest);
        assert!(result.is_ok());

        // Source no longer includes the strand.
        assert!(!source.is_member(&make_key(2)));
        // Destination now includes it.
        assert!(dest.is_member(&make_key(2)));
    }

    #[test]
    fn migration_source_group_no_longer_includes_strand_in_ordering() {
        let mut source =
            GovernedReferenceGroup::open(vec![make_key(1), make_key(2), make_key(3)], 10);
        let mut dest = GovernedReferenceGroup::open(vec![make_key(4), make_key(5)], 10);

        let migration = IntraFabricMigration::new(
            make_key(3),
            source.reference_group().compute_id(),
            dest.reference_group().compute_id(),
            vec![],
            25,
        );

        migration.execute(&mut source, &mut dest).unwrap();

        // Source participants should be [1, 2] (3 removed).
        assert_eq!(source.member_count(), 2);
        assert!(source.is_member(&make_key(1)));
        assert!(source.is_member(&make_key(2)));
        assert!(!source.is_member(&make_key(3)));
    }

    #[test]
    fn migration_destination_group_includes_strand_in_ordering() {
        let mut source =
            GovernedReferenceGroup::open(vec![make_key(1), make_key(2), make_key(3)], 10);
        let mut dest = GovernedReferenceGroup::open(vec![make_key(4), make_key(5)], 10);

        let migration = IntraFabricMigration::new(
            make_key(1),
            source.reference_group().compute_id(),
            dest.reference_group().compute_id(),
            vec![],
            10,
        );

        migration.execute(&mut source, &mut dest).unwrap();

        // Destination should now have [1, 4, 5] (sorted).
        assert_eq!(dest.member_count(), 3);
        assert!(dest.is_member(&make_key(1)));
        assert!(dest.is_member(&make_key(4)));
        assert!(dest.is_member(&make_key(5)));
    }

    #[test]
    fn migration_strand_blocks_still_exist_in_dag() {
        // After migration, the strand's blocks remain in the shared DAG.
        // They don't get moved or deleted -- only the GROUP membership changes.
        let mut blocklace = Blocklace::new();

        // Strand 2 produces some blocks.
        let b1 = crate::Block::new(make_key(2), 0, vec![], b"before-migration".to_vec());
        let b1_id = b1.id();
        blocklace.insert(b1).unwrap();

        let b2 = crate::Block::new(make_key(2), 1, vec![b1_id], b"also-before".to_vec());
        let b2_id = b2.id();
        blocklace.insert(b2).unwrap();

        // Perform migration (group changes, not the DAG).
        let mut source =
            GovernedReferenceGroup::open(vec![make_key(1), make_key(2), make_key(3)], 10);
        let mut dest = GovernedReferenceGroup::open(vec![make_key(4), make_key(5)], 10);

        let migration = IntraFabricMigration::new(
            make_key(2),
            source.reference_group().compute_id(),
            dest.reference_group().compute_id(),
            vec![],
            5,
        );
        migration.execute(&mut source, &mut dest).unwrap();

        // Blocks are STILL in the DAG (shared, not moved).
        assert!(blocklace.contains(&b1_id));
        assert!(blocklace.contains(&b2_id));
        assert_eq!(blocklace.get(&b1_id).unwrap().creator, make_key(2));
    }

    #[test]
    fn migration_not_in_source_group_fails() {
        let mut source = GovernedReferenceGroup::open(vec![make_key(1), make_key(2)], 10);
        let mut dest = GovernedReferenceGroup::open(vec![make_key(3), make_key(4)], 10);

        let migration = IntraFabricMigration::new(
            make_key(99), // not in source
            source.reference_group().compute_id(),
            dest.reference_group().compute_id(),
            vec![],
            5,
        );

        let result = migration.execute(&mut source, &mut dest);
        assert_eq!(result, Err(MigrationError::NotInSourceGroup));
    }

    #[test]
    fn migration_already_in_destination_fails() {
        let mut source =
            GovernedReferenceGroup::open(vec![make_key(1), make_key(2), make_key(3)], 10);
        let mut dest = GovernedReferenceGroup::open(
            vec![make_key(2), make_key(4)], // key 2 already here
            10,
        );

        let migration = IntraFabricMigration::new(
            make_key(2),
            source.reference_group().compute_id(),
            dest.reference_group().compute_id(),
            vec![],
            5,
        );

        let result = migration.execute(&mut source, &mut dest);
        assert_eq!(result, Err(MigrationError::AlreadyInDestination));
    }

    // ─── Backward Compatibility Tests ───────────────────────────────────────

    #[test]
    fn backward_compat_federation_to_fabric_roundtrip() {
        let fed = FederationId([0xAB; 32]);
        let addr = federation_to_fabric(&fed);

        match &addr {
            FabricAddress::Federation(f) => assert_eq!(*f, fed),
            _ => panic!("expected Federation variant"),
        }

        let back = fabric_to_federation(&addr).unwrap();
        assert_eq!(back, fed);
    }

    #[test]
    fn backward_compat_group_to_federation() {
        // A group address can be treated as a federation (for legacy code).
        let group_id = [0xCD; 32];
        let addr = FabricAddress::Group(group_id);
        let fed = fabric_to_federation(&addr).unwrap();
        assert_eq!(fed.0, group_id);
    }

    #[test]
    fn backward_compat_strand_has_no_federation_equivalent() {
        let addr = FabricAddress::strand(make_key(5));
        assert_eq!(fabric_to_federation(&addr), None);
    }

    #[test]
    fn backward_compat_capability_has_no_federation_equivalent() {
        let addr = FabricAddress::capability([0x77; 32]);
        assert_eq!(fabric_to_federation(&addr), None);
    }

    // ─── Checkpoint Hash Determinism ────────────────────────────────────────

    #[test]
    fn checkpoint_hash_is_deterministic() {
        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);
        let cp1 = GroupCheckpoint::new(&group, 100, [0xAA; 32]);
        let cp2 = GroupCheckpoint::new(&group, 100, [0xAA; 32]);

        assert_eq!(cp1.checkpoint_hash(), cp2.checkpoint_hash());
    }

    #[test]
    fn checkpoint_hash_varies_on_height() {
        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);
        let cp1 = GroupCheckpoint::new(&group, 100, [0xAA; 32]);
        let cp2 = GroupCheckpoint::new(&group, 101, [0xAA; 32]);

        assert_ne!(cp1.checkpoint_hash(), cp2.checkpoint_hash());
    }
}
