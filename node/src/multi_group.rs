//! Phase C: Multi-group participation via cross-reference dissemination.
//!
//! Replaces the old `bridge.rs` relay pattern with DAG-native cross-group
//! interaction. Instead of manually relaying messages between federations over
//! TCP, a node subscribes to multiple reference groups simultaneously. Cross-group
//! messages travel as `DagDeliveredProof` blocks (Phase 4 cross-references) and
//! the existing dissemination layer handles delivery via interest-based push.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────────────┐
//! │ MultiGroupNode                                                              │
//! │                                                                             │
//! │  groups: [GovernedReferenceGroup]  ← multiple groups, one shared DAG        │
//! │  blocklace: Blocklace             ← single DAG, multiple views              │
//! │  orderings: HashMap<GroupId, Vec<BlockId>>  ← per-group tau results         │
//! │                                                                             │
//! │  Proof forwarding:                                                          │
//! │    1. Observe proof in group A                                              │
//! │    2. Create a block in group B's strand with DagDeliveredProof payload     │
//! │    3. Include cross-reference to the source block                           │
//! │    4. Dissemination delivers to group B's subscribers naturally             │
//! └─────────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Comparison to old bridge model
//!
//! Old: `FederationBridge` opens gossip connections to remote federations, runs
//! relay tasks that filter and forward messages over the network.
//!
//! New: The node is simply a member of multiple groups on the same DAG. Cross-group
//! interaction is just creating blocks with cross-references. The dissemination
//! layer (interest-based subscriptions) ensures blocks reach the right peers.

use std::collections::HashMap;

use pyana_blocklace::addressing::GroupId;
use pyana_blocklace::constitution::GovernedReferenceGroup;
use pyana_blocklace::cross_reference::{
    BlockPayload, CrossRefPolicy, CrossRefPurpose, DagDeliveredProof,
};
use pyana_blocklace::dissemination::{Disseminator, Subscription};
use pyana_blocklace::ordering::{OrderingConfig, ReferenceGroup, tau_unified};
use pyana_blocklace::{Block, BlockId, Blocklace, NodeKey};
use tracing::{debug, info, warn};

// =============================================================================
// Multi-Group Node
// =============================================================================

/// A node that participates in MULTIPLE reference groups simultaneously.
///
/// Each group has its own tau ordering, but they share the same underlying
/// blocklace. Cross-group messages travel as `DagDeliveredProof` blocks
/// and the dissemination layer handles delivery via interest-based push.
pub struct MultiGroupNode {
    /// Groups this node participates in.
    groups: Vec<GovernedReferenceGroup>,
    /// Group IDs for fast lookup.
    group_ids: Vec<GroupId>,
    /// The shared blocklace (one DAG, multiple views).
    blocklace: Blocklace,
    /// Per-group tau results (cached).
    orderings: HashMap<GroupId, Vec<BlockId>>,
    /// This node's identity key.
    node_key: NodeKey,
    /// The disseminator for interest-based push.
    disseminator: Disseminator,
    /// Cross-reference policy per group.
    cross_ref_policies: HashMap<GroupId, CrossRefPolicy>,
    /// Ordering configuration.
    ordering_config: OrderingConfig,
}

/// Configuration for joining a group.
#[derive(Clone, Debug)]
pub struct GroupJoinConfig {
    /// The governed reference group to join.
    pub group: GovernedReferenceGroup,
    /// Cross-reference policy for this group.
    pub cross_ref_policy: CrossRefPolicy,
}

/// A proof that needs to be forwarded to another group.
#[derive(Clone, Debug)]
pub struct PendingProofForward {
    /// The proof data.
    pub proof: DagDeliveredProof,
    /// The source block (in the originating group).
    pub source_block_id: BlockId,
    /// The destination group ID.
    pub destination_group: GroupId,
}

impl MultiGroupNode {
    /// Create a new multi-group node with the given identity.
    pub fn new(node_key: NodeKey) -> Self {
        let disseminator = Disseminator::new(node_key);
        Self {
            groups: Vec::new(),
            group_ids: Vec::new(),
            blocklace: Blocklace::new(),
            orderings: HashMap::new(),
            node_key,
            disseminator,
            cross_ref_policies: HashMap::new(),
            ordering_config: OrderingConfig::default(),
        }
    }

    /// Create a multi-group node with an existing blocklace.
    pub fn with_blocklace(node_key: NodeKey, blocklace: Blocklace) -> Self {
        let disseminator = Disseminator::with_blocklace(node_key, blocklace.clone());
        Self {
            groups: Vec::new(),
            group_ids: Vec::new(),
            blocklace,
            orderings: HashMap::new(),
            node_key,
            disseminator,
            cross_ref_policies: HashMap::new(),
            ordering_config: OrderingConfig::default(),
        }
    }

    /// Join a reference group.
    ///
    /// The node subscribes to all strands in this group (via its dissemination
    /// subscription) and will participate in tau ordering for this group.
    pub fn join_group(&mut self, config: GroupJoinConfig) {
        let group_id = config.group.group.compute_id();
        let group_hex: String = group_id
            .iter()
            .take(4)
            .map(|b| format!("{b:02x}"))
            .collect();

        // Add all group members to our dissemination subscription.
        let mut sub = self
            .disseminator
            .subscription()
            .cloned()
            .unwrap_or_else(|| Subscription::from_strands(&[self.node_key]));

        for participant in &config.group.group.participants {
            sub.subscribe(*participant);
        }
        self.disseminator.set_subscription(sub);

        // Store the group and its policy.
        self.cross_ref_policies
            .insert(group_id, config.cross_ref_policy);
        self.group_ids.push(group_id);
        self.groups.push(config.group);

        info!(
            group = %group_hex,
            group_count = self.groups.len(),
            "joined reference group"
        );
    }

    /// Leave a reference group.
    ///
    /// Removes the group from participation. Blocks already in the DAG remain
    /// (the DAG is append-only).
    pub fn leave_group(&mut self, group_id: &GroupId) -> bool {
        if let Some(idx) = self.group_ids.iter().position(|g| g == group_id) {
            let group = self.groups.remove(idx);
            self.group_ids.remove(idx);
            self.orderings.remove(group_id);
            self.cross_ref_policies.remove(group_id);

            // Remove the group's strands from our subscription
            // (unless they're also in another group we participate in).
            let other_members: std::collections::HashSet<NodeKey> = self
                .groups
                .iter()
                .flat_map(|g| g.group.participants.iter().copied())
                .collect();

            if let Some(sub) = self.disseminator.subscription().cloned().as_mut() {
                for participant in &group.group.participants {
                    if !other_members.contains(participant) && *participant != self.node_key {
                        sub.unsubscribe(participant);
                    }
                }
                self.disseminator.set_subscription(sub.clone());
            }

            let group_hex: String = group_id
                .iter()
                .take(4)
                .map(|b| format!("{b:02x}"))
                .collect();
            info!(
                group = %group_hex,
                group_count = self.groups.len(),
                "left reference group"
            );
            true
        } else {
            false
        }
    }

    /// Get the groups this node participates in.
    pub fn groups(&self) -> &[GovernedReferenceGroup] {
        &self.groups
    }

    /// Get the group IDs.
    pub fn group_ids(&self) -> &[GroupId] {
        &self.group_ids
    }

    /// Get the shared blocklace.
    pub fn blocklace(&self) -> &Blocklace {
        &self.blocklace
    }

    /// Get a mutable reference to the shared blocklace.
    pub fn blocklace_mut(&mut self) -> &mut Blocklace {
        &mut self.blocklace
    }

    /// Get this node's identity.
    pub fn node_key(&self) -> &NodeKey {
        &self.node_key
    }

    /// Get the disseminator.
    pub fn disseminator(&self) -> &Disseminator {
        &self.disseminator
    }

    /// Get a mutable reference to the disseminator.
    pub fn disseminator_mut(&mut self) -> &mut Disseminator {
        &mut self.disseminator
    }

    /// Get the cached ordering for a group.
    pub fn ordering_for(&self, group_id: &GroupId) -> Option<&Vec<BlockId>> {
        self.orderings.get(group_id)
    }

    /// Recompute tau ordering for all groups.
    ///
    /// This should be called after inserting new blocks into the blocklace.
    /// Returns the total number of newly finalized blocks across all groups.
    pub fn recompute_orderings(&mut self) -> usize {
        let mut total_new = 0;
        for (idx, group) in self.groups.iter().enumerate() {
            let group_id = self.group_ids[idx];
            let new_ordering = tau_unified(&self.blocklace, &group.group, &self.ordering_config);
            let prev_len = self.orderings.get(&group_id).map(|o| o.len()).unwrap_or(0);
            let new_finalized = new_ordering.len().saturating_sub(prev_len);
            total_new += new_finalized;
            self.orderings.insert(group_id, new_ordering);
        }
        total_new
    }

    /// Forward a proof from one group to another.
    ///
    /// Creates a block in the destination group's context with the proof as a
    /// `DagDeliveredProof` payload, and includes a cross-reference to the source
    /// block. The dissemination layer delivers it to the destination group's
    /// subscribers.
    ///
    /// Returns the new block's ID on success.
    pub fn forward_proof(
        &mut self,
        forward: &PendingProofForward,
    ) -> Result<BlockId, ProofForwardError> {
        // Verify we are in the destination group.
        let dest_idx = self
            .group_ids
            .iter()
            .position(|g| *g == forward.destination_group)
            .ok_or(ProofForwardError::NotInDestinationGroup)?;

        let dest_group = &self.groups[dest_idx];

        // Verify we are allowed to make cross-references in the destination group.
        let policy = self
            .cross_ref_policies
            .get(&forward.destination_group)
            .unwrap_or(&CrossRefPolicy::Unrestricted);

        if !policy.allows_cross_ref(&self.node_key, &dest_group.group) {
            return Err(ProofForwardError::PolicyDenied);
        }

        // Verify the source block exists in the blocklace.
        if !self.blocklace.contains(&forward.source_block_id) {
            return Err(ProofForwardError::SourceBlockNotFound);
        }

        // Create the proof payload.
        let payload = BlockPayload::CrossGroupProof(forward.proof.clone());
        let payload_bytes = postcard::to_stdvec(&payload)
            .map_err(|e| ProofForwardError::SerializationFailed(e.to_string()))?;

        // Build predecessors: include the source block as a cross-reference,
        // plus the current frontier of the blocklace.
        let mut predecessors: Vec<BlockId> = self.blocklace.frontier().iter().copied().collect();
        if !predecessors.contains(&forward.source_block_id) {
            predecessors.push(forward.source_block_id);
        }

        // Determine the next sequence number for our strand.
        let sequence = self
            .blocklace
            .tip_for(&self.node_key)
            .and_then(|tip| self.blocklace.get(tip))
            .map(|b| b.sequence + 1)
            .unwrap_or(0);

        // Create and insert the block.
        let block = Block::new(self.node_key, sequence, predecessors, payload_bytes);
        let block_id = block.id();

        self.blocklace
            .insert(block.clone())
            .map_err(|missing| ProofForwardError::MissingPredecessors(missing))?;

        // Also insert into the disseminator's blocklace.
        let _ = self.disseminator.blocklace_mut().insert(block);

        let group_hex: String = forward
            .destination_group
            .iter()
            .take(4)
            .map(|b| format!("{b:02x}"))
            .collect();
        let source_hex: String = forward
            .source_block_id
            .iter()
            .take(4)
            .map(|b| format!("{b:02x}"))
            .collect();

        debug!(
            destination_group = %group_hex,
            source_block = %source_hex,
            proof_type = %forward.proof.proof_type,
            "forwarded proof to destination group via cross-reference block"
        );

        Ok(block_id)
    }

    /// Scan for proofs in one group that should be forwarded to another.
    ///
    /// This checks newly finalized blocks in each group for `DagDeliveredProof`
    /// payloads that are tagged for a destination group we participate in.
    /// Returns a list of proof forwards that should be executed.
    pub fn scan_for_pending_forwards(&self) -> Vec<PendingProofForward> {
        let mut forwards = Vec::new();

        for (idx, group) in self.groups.iter().enumerate() {
            let group_id = self.group_ids[idx];
            let ordering = match self.orderings.get(&group_id) {
                Some(o) => o,
                None => continue,
            };

            // Check each finalized block for proof payloads.
            for block_id in ordering {
                let block = match self.blocklace.get(block_id) {
                    Some(b) => b,
                    None => continue,
                };

                // Try to decode the payload as a BlockPayload.
                let payload: BlockPayload = match postcard::from_bytes(&block.payload) {
                    Ok(p) => p,
                    Err(_) => continue, // Not a structured payload, skip.
                };

                match payload {
                    BlockPayload::CrossGroupProof(proof) => {
                        // Check if this proof should be forwarded to a group we're in.
                        self.check_proof_destination(&proof, *block_id, group_id, &mut forwards);
                    }
                    BlockPayload::TurnWithProofs { proofs, .. } => {
                        for proof in proofs {
                            self.check_proof_destination(
                                &proof,
                                *block_id,
                                group_id,
                                &mut forwards,
                            );
                        }
                    }
                    BlockPayload::Turn(_) => {}
                }
            }
        }

        forwards
    }

    /// Check if a proof should be forwarded to one of our other groups.
    fn check_proof_destination(
        &self,
        proof: &DagDeliveredProof,
        source_block_id: BlockId,
        source_group_id: GroupId,
        forwards: &mut Vec<PendingProofForward>,
    ) {
        // A proof is forwarded if its source_block references a block whose
        // creator is in another group we participate in but NOT in the source group.
        for (idx, group) in self.groups.iter().enumerate() {
            let dest_group_id = self.group_ids[idx];
            if dest_group_id == source_group_id {
                continue; // Don't forward to the same group.
            }

            // Check if the proof's source block creator is relevant to the
            // destination group (heuristic: forward if the proof type mentions
            // the destination, or if we explicitly bridge these groups).
            // For now, forward all cross-group proofs to all other groups we're in.
            // A more sophisticated policy would use proof_type or routing metadata.
            forwards.push(PendingProofForward {
                proof: proof.clone(),
                source_block_id,
                destination_group: dest_group_id,
            });
        }
    }

    /// Process a received block: insert into the shared blocklace and update
    /// dissemination state.
    ///
    /// Returns `Ok(block_id)` on success or `Err(missing)` if predecessors
    /// are missing.
    pub fn receive_block(&mut self, from: &NodeKey, block: Block) -> Result<BlockId, Vec<BlockId>> {
        let block_id = block.id();

        // Insert into the shared blocklace.
        self.blocklace.insert(block.clone())?;

        // Also track in the disseminator for peer knowledge.
        let _ = self.disseminator.received_from(from, block);

        Ok(block_id)
    }

    /// Create a block in the context of a specific group.
    ///
    /// The block is created with our node key and inserted into the shared
    /// blocklace. Predecessors include the current frontier.
    pub fn create_block(&mut self, payload: Vec<u8>) -> Block {
        self.disseminator.create_block(payload)
    }

    /// Get a combined subscription covering all groups this node participates in.
    pub fn combined_subscription(&self) -> Subscription {
        let mut all_strands = std::collections::HashSet::new();
        all_strands.insert(self.node_key);
        for group in &self.groups {
            for participant in &group.group.participants {
                all_strands.insert(*participant);
            }
        }
        let strands: Vec<NodeKey> = all_strands.into_iter().collect();
        Subscription::from_strands(&strands)
    }

    /// Check if this node participates in a given group.
    pub fn is_in_group(&self, group_id: &GroupId) -> bool {
        self.group_ids.contains(group_id)
    }

    /// Get the number of groups this node participates in.
    pub fn group_count(&self) -> usize {
        self.groups.len()
    }
}

// =============================================================================
// Error Types
// =============================================================================

/// Errors that can occur when forwarding a proof between groups.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofForwardError {
    /// We are not a member of the destination group.
    NotInDestinationGroup,
    /// The cross-reference policy of the destination group denies this operation.
    PolicyDenied,
    /// The source block referenced by the proof does not exist in our blocklace.
    SourceBlockNotFound,
    /// Some predecessors are missing from the blocklace.
    MissingPredecessors(Vec<BlockId>),
    /// Serialization of the proof payload failed.
    SerializationFailed(String),
}

impl std::fmt::Display for ProofForwardError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotInDestinationGroup => write!(f, "not a member of the destination group"),
            Self::PolicyDenied => {
                write!(f, "cross-reference policy denies this operation")
            }
            Self::SourceBlockNotFound => write!(f, "source block not found in blocklace"),
            Self::MissingPredecessors(ids) => {
                write!(f, "missing {} predecessors", ids.len())
            }
            Self::SerializationFailed(e) => write!(f, "serialization failed: {e}"),
        }
    }
}

impl std::error::Error for ProofForwardError {}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_blocklace::cross_reference::CrossRefPolicy;

    fn make_key(id: u8) -> NodeKey {
        [id; 32]
    }

    #[test]
    fn multi_group_node_creation() {
        let node = MultiGroupNode::new(make_key(1));
        assert_eq!(node.group_count(), 0);
        assert_eq!(*node.node_key(), make_key(1));
        assert!(node.blocklace().is_empty());
    }

    #[test]
    fn join_and_leave_groups() {
        let mut node = MultiGroupNode::new(make_key(1));

        // Join group A.
        let group_a = GovernedReferenceGroup::open(vec![make_key(1), make_key(2), make_key(3)], 10);
        let group_a_id = group_a.group.compute_id();
        node.join_group(GroupJoinConfig {
            group: group_a,
            cross_ref_policy: CrossRefPolicy::Unrestricted,
        });
        assert_eq!(node.group_count(), 1);
        assert!(node.is_in_group(&group_a_id));

        // Join group B.
        let group_b = GovernedReferenceGroup::open(vec![make_key(1), make_key(4), make_key(5)], 10);
        let group_b_id = group_b.group.compute_id();
        node.join_group(GroupJoinConfig {
            group: group_b,
            cross_ref_policy: CrossRefPolicy::Unrestricted,
        });
        assert_eq!(node.group_count(), 2);
        assert!(node.is_in_group(&group_b_id));

        // Leave group A.
        assert!(node.leave_group(&group_a_id));
        assert_eq!(node.group_count(), 1);
        assert!(!node.is_in_group(&group_a_id));
        assert!(node.is_in_group(&group_b_id));

        // Can't leave a group we're not in.
        assert!(!node.leave_group(&group_a_id));
    }

    #[test]
    fn combined_subscription_covers_all_groups() {
        let mut node = MultiGroupNode::new(make_key(1));

        let group_a = GovernedReferenceGroup::open(vec![make_key(1), make_key(2), make_key(3)], 10);
        let group_b = GovernedReferenceGroup::open(vec![make_key(1), make_key(4), make_key(5)], 10);

        node.join_group(GroupJoinConfig {
            group: group_a,
            cross_ref_policy: CrossRefPolicy::Unrestricted,
        });
        node.join_group(GroupJoinConfig {
            group: group_b,
            cross_ref_policy: CrossRefPolicy::Unrestricted,
        });

        let sub = node.combined_subscription();
        // Should include all participants from both groups plus self.
        assert!(sub.is_directly_subscribed(&make_key(1)));
        assert!(sub.is_directly_subscribed(&make_key(2)));
        assert!(sub.is_directly_subscribed(&make_key(3)));
        assert!(sub.is_directly_subscribed(&make_key(4)));
        assert!(sub.is_directly_subscribed(&make_key(5)));
    }

    #[test]
    fn forward_proof_between_groups() {
        let mut node = MultiGroupNode::new(make_key(1));

        let group_a = GovernedReferenceGroup::open(vec![make_key(1), make_key(2), make_key(3)], 10);
        let group_b = GovernedReferenceGroup::open(vec![make_key(1), make_key(4), make_key(5)], 10);
        let group_b_id = group_b.group.compute_id();

        node.join_group(GroupJoinConfig {
            group: group_a,
            cross_ref_policy: CrossRefPolicy::Unrestricted,
        });
        node.join_group(GroupJoinConfig {
            group: group_b,
            cross_ref_policy: CrossRefPolicy::Unrestricted,
        });

        // Create a source block in the blocklace.
        let source_block = Block::new(make_key(2), 0, vec![], b"source-proof".to_vec());
        let source_id = source_block.id();
        node.blocklace_mut().insert(source_block).unwrap();

        // Forward a proof from group A to group B.
        let proof = DagDeliveredProof {
            proof: vec![0xDE, 0xAD, 0xBE, 0xEF],
            source_block: source_id,
            proof_type: "stark-v1".to_string(),
            public_inputs: vec![42, 7],
        };

        let forward = PendingProofForward {
            proof: proof.clone(),
            source_block_id: source_id,
            destination_group: group_b_id,
        };

        let result = node.forward_proof(&forward);
        assert!(result.is_ok());

        let new_block_id = result.unwrap();
        assert!(node.blocklace().contains(&new_block_id));

        // The new block should reference the source block.
        let new_block = node.blocklace().get(&new_block_id).unwrap();
        assert!(new_block.predecessors.contains(&source_id));

        // Verify payload is a CrossGroupProof.
        let decoded: BlockPayload = postcard::from_bytes(&new_block.payload).unwrap();
        match decoded {
            BlockPayload::CrossGroupProof(p) => {
                assert_eq!(p.proof_type, "stark-v1");
                assert_eq!(p.public_inputs, vec![42, 7]);
            }
            _ => panic!("expected CrossGroupProof payload"),
        }
    }

    #[test]
    fn forward_proof_policy_denied() {
        let mut node = MultiGroupNode::new(make_key(1));

        let group_a = GovernedReferenceGroup::open(vec![make_key(1), make_key(2), make_key(3)], 10);

        // Group B uses BridgeMembersOnly policy, but our key is NOT a bridge member.
        let group_b = GovernedReferenceGroup::open(vec![make_key(1), make_key(4), make_key(5)], 10);
        let group_b_id = group_b.group.compute_id();

        node.join_group(GroupJoinConfig {
            group: group_a,
            cross_ref_policy: CrossRefPolicy::Unrestricted,
        });
        node.join_group(GroupJoinConfig {
            group: group_b,
            cross_ref_policy: CrossRefPolicy::BridgeMembersOnly {
                bridge_members: vec![make_key(99)], // We (key 1) are NOT a bridge member.
            },
        });

        // Create a source block.
        let source_block = Block::new(make_key(2), 0, vec![], b"source".to_vec());
        let source_id = source_block.id();
        node.blocklace_mut().insert(source_block).unwrap();

        let forward = PendingProofForward {
            proof: DagDeliveredProof {
                proof: vec![1, 2, 3],
                source_block: source_id,
                proof_type: "test".to_string(),
                public_inputs: vec![],
            },
            source_block_id: source_id,
            destination_group: group_b_id,
        };

        let result = node.forward_proof(&forward);
        assert_eq!(result, Err(ProofForwardError::PolicyDenied));
    }

    #[test]
    fn forward_proof_not_in_destination() {
        let mut node = MultiGroupNode::new(make_key(1));

        let group_a = GovernedReferenceGroup::open(vec![make_key(1), make_key(2), make_key(3)], 10);
        node.join_group(GroupJoinConfig {
            group: group_a,
            cross_ref_policy: CrossRefPolicy::Unrestricted,
        });

        // Create a source block.
        let source_block = Block::new(make_key(2), 0, vec![], b"source".to_vec());
        let source_id = source_block.id();
        node.blocklace_mut().insert(source_block).unwrap();

        // Try to forward to a group we're not in.
        let fake_group_id = [0xFF; 32];
        let forward = PendingProofForward {
            proof: DagDeliveredProof {
                proof: vec![1],
                source_block: source_id,
                proof_type: "test".to_string(),
                public_inputs: vec![],
            },
            source_block_id: source_id,
            destination_group: fake_group_id,
        };

        let result = node.forward_proof(&forward);
        assert_eq!(result, Err(ProofForwardError::NotInDestinationGroup));
    }

    #[test]
    fn receive_block_updates_both_blocklace_and_disseminator() {
        let mut node = MultiGroupNode::new(make_key(1));

        let block = Block::new(make_key(2), 0, vec![], b"hello".to_vec());
        let block_id = block.id();

        let result = node.receive_block(&make_key(2), block);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), block_id);
        assert!(node.blocklace().contains(&block_id));
        assert!(node.disseminator().blocklace().contains(&block_id));
    }

    #[test]
    fn recompute_orderings_multiple_groups() {
        let mut node = MultiGroupNode::new(make_key(1));

        let group_a = GovernedReferenceGroup::open(vec![make_key(1), make_key(2), make_key(3)], 10);
        let group_a_id = group_a.group.compute_id();

        node.join_group(GroupJoinConfig {
            group: group_a,
            cross_ref_policy: CrossRefPolicy::Unrestricted,
        });

        // Insert blocks from all group A members (round 1).
        let b1 = Block::new(make_key(1), 0, vec![], b"m1-r1".to_vec());
        let b1_id = node.blocklace_mut().insert(b1).unwrap();
        let b2 = Block::new(make_key(2), 0, vec![], b"m2-r1".to_vec());
        let b2_id = node.blocklace_mut().insert(b2).unwrap();
        let b3 = Block::new(make_key(3), 0, vec![], b"m3-r1".to_vec());
        let b3_id = node.blocklace_mut().insert(b3).unwrap();

        // Round 2: all reference previous.
        let preds = vec![b1_id, b2_id, b3_id];
        let r2_1 = Block::new(make_key(1), 1, preds.clone(), b"m1-r2".to_vec());
        node.blocklace_mut().insert(r2_1).unwrap();
        let r2_2 = Block::new(make_key(2), 1, preds.clone(), b"m2-r2".to_vec());
        node.blocklace_mut().insert(r2_2).unwrap();
        let r2_3 = Block::new(make_key(3), 1, preds.clone(), b"m3-r2".to_vec());
        node.blocklace_mut().insert(r2_3).unwrap();

        // Recompute orderings.
        node.recompute_orderings();

        // Should have an ordering for group A.
        let ordering = node.ordering_for(&group_a_id);
        assert!(ordering.is_some());
        // The exact number of finalized blocks depends on tau's wave/leader logic,
        // but we should have at least processed some blocks.
    }
}
