//! Phase 4: Cross-group references as first-class primitives.
//!
//! Blocks can reference external strands (creators not in their reference group),
//! and the group learns about them through causal context. CapTP becomes OPTIONAL
//! for simple acknowledgment/proof exchange.
//!
//! Cross-references enable:
//! - Causal acknowledgment of events on other strands (no CapTP needed)
//! - Proof delivery via the DAG (embed proof in block, reference source)
//! - Interest discovery (notice new strands, potentially subscribe)
//! - Causal dependencies across groups (this turn depends on that event)

use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::dissemination::Disseminator;
use crate::ordering::ReferenceGroup;
use crate::{Block, BlockId, Blocklace, NodeKey};

// =============================================================================
// Cross-Reference Metadata
// =============================================================================

/// Metadata for a block that references strands outside its reference group.
/// This is informational — it helps peers understand WHY an external block
/// was pulled into their causal context.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrossReference {
    /// The external block being referenced.
    pub external_block: BlockId,
    /// The creator of the external block (not in our reference group).
    pub external_creator: NodeKey,
    /// Why this reference exists.
    pub purpose: CrossRefPurpose,
}

/// Why a cross-reference exists.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CrossRefPurpose {
    /// Acknowledging an event on another strand (causal proof).
    Acknowledgment,
    /// Importing a proof from another strand (proof delivery).
    ProofImport { proof_type: String },
    /// Establishing a causal dependency (this turn depends on that event).
    CausalDependency,
    /// Discovery (we noticed this strand, might want to subscribe).
    Discovery,
}

// =============================================================================
// Cross-Group Proof Delivery (no CapTP needed)
// =============================================================================

/// A proof delivered via the DAG (no CapTP session needed).
/// The proof is embedded in a block's payload, and the cross-reference
/// points to the block that GENERATED the proof (causal link).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DagDeliveredProof {
    /// The proof bytes (STARK proof).
    pub proof: Vec<u8>,
    /// The block that produced this proof (cross-referenced).
    pub source_block: BlockId,
    /// What this proof proves (for routing to the right verifier).
    pub proof_type: String,
    /// Public inputs.
    pub public_inputs: Vec<u32>,
}

/// Payload variant for blocks that carry cross-group proofs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BlockPayload {
    /// Normal turn data.
    Turn(Vec<u8>),
    /// A proof from another group (delivered via DAG, no CapTP needed).
    CrossGroupProof(DagDeliveredProof),
    /// Both (a turn that also acknowledges external proofs).
    TurnWithProofs {
        turn: Vec<u8>,
        proofs: Vec<DagDeliveredProof>,
    },
}

// =============================================================================
// Cross-Reference Policy
// =============================================================================

/// Policy for how a group handles cross-references.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CrossRefPolicy {
    /// Allow any member to cross-reference (open groups).
    Unrestricted,
    /// Only designated "bridge" members can cross-reference (controlled groups).
    BridgeMembersOnly { bridge_members: Vec<NodeKey> },
    /// Cross-references require group approval (strict groups).
    RequiresApproval,
    /// No cross-references allowed (isolated groups).
    Forbidden,
}

impl CrossRefPolicy {
    /// Check if a given creator is allowed to make cross-references under this policy.
    pub fn allows_cross_ref(&self, creator: &NodeKey, _group: &ReferenceGroup) -> bool {
        match self {
            CrossRefPolicy::Unrestricted => true,
            CrossRefPolicy::BridgeMembersOnly { bridge_members } => {
                bridge_members.contains(creator)
            }
            CrossRefPolicy::RequiresApproval => false, // needs explicit approval flow
            CrossRefPolicy::Forbidden => false,
        }
    }
}

// =============================================================================
// Cross-Reference Tracking on Blocklace
// =============================================================================

/// Extension trait for cross-reference queries on the Blocklace.
impl Blocklace {
    /// Get all cross-references in a block (predecessors from non-group creators).
    ///
    /// A cross-reference is any predecessor whose creator is NOT a member of
    /// the given reference group.
    pub fn cross_references(
        &self,
        block_id: &BlockId,
        group: &ReferenceGroup,
    ) -> Vec<CrossReference> {
        let block = match self.get(block_id) {
            Some(b) => b,
            None => return vec![],
        };

        let mut refs = Vec::new();
        for pred_id in &block.predecessors {
            if let Some(pred_block) = self.get(pred_id) {
                if !group.is_member(&pred_block.creator) {
                    refs.push(CrossReference {
                        external_block: *pred_id,
                        external_creator: pred_block.creator,
                        purpose: CrossRefPurpose::CausalDependency,
                    });
                }
            }
        }
        refs
    }

    /// Get all external blocks in this group's causal past.
    ///
    /// Walks the causal past of all current tips from group members and
    /// collects block IDs whose creators are NOT in the reference group.
    pub fn external_causal_context(&self, group: &ReferenceGroup) -> Vec<BlockId> {
        let mut external = Vec::new();
        let mut visited = HashSet::new();

        // Gather all blocks in the causal past of group members' tips.
        for (creator, tip_id) in self.tips() {
            if !group.is_member(creator) {
                continue;
            }
            let past = self.causal_past(tip_id);
            for bid in past {
                if visited.insert(bid) {
                    if let Some(block) = self.get(&bid) {
                        if !group.is_member(&block.creator) {
                            external.push(bid);
                        }
                    }
                }
            }
        }
        external
    }

    /// Check if a block has any cross-references.
    pub fn has_cross_references(&self, block_id: &BlockId, group: &ReferenceGroup) -> bool {
        let block = match self.get(block_id) {
            Some(b) => b,
            None => return false,
        };

        block.predecessors.iter().any(|pred_id| {
            self.get(pred_id)
                .map(|pred_block| !group.is_member(&pred_block.creator))
                .unwrap_or(false)
        })
    }
}

// =============================================================================
// Dissemination Integration
// =============================================================================

impl Disseminator {
    /// When we create a block with cross-references, ensure the referenced
    /// external blocks are included in our push set to group members.
    ///
    /// This computes the set of external block IDs that should be included
    /// for causal closure when pushing to group subscribers.
    pub fn cross_reference_blocks_for_push(
        &self,
        block: &Block,
        group: &ReferenceGroup,
    ) -> Vec<BlockId> {
        let mut external_blocks = Vec::new();
        for pred_id in &block.predecessors {
            if let Some(pred_block) = self.blocklace().get(pred_id) {
                if !group.is_member(&pred_block.creator) {
                    external_blocks.push(*pred_id);
                }
            }
        }
        external_blocks
    }
}

// =============================================================================
// Helper: Validate cross-reference against policy
// =============================================================================

/// Validate that a block's cross-references comply with the group's policy.
///
/// Returns `Ok(())` if compliant, or `Err` with a description of the violation.
pub fn validate_cross_references(
    blocklace: &Blocklace,
    block_id: &BlockId,
    group: &ReferenceGroup,
    policy: &CrossRefPolicy,
) -> Result<(), String> {
    let block = blocklace
        .get(block_id)
        .ok_or_else(|| "block not found".to_string())?;

    // Check if this block has any cross-references.
    let cross_refs = blocklace.cross_references(block_id, group);
    if cross_refs.is_empty() {
        return Ok(()); // No cross-references, always valid.
    }

    // Check if the creator is allowed to make cross-references.
    if !policy.allows_cross_ref(&block.creator, group) {
        return Err(format!(
            "creator {:?} is not allowed to make cross-references under {:?} policy",
            &block.creator[..4],
            policy
        ));
    }

    Ok(())
}

// =============================================================================
// Helper: Annotate cross-references with purposes
// =============================================================================

/// Annotate cross-references with specific purposes (for richer metadata).
///
/// The caller provides the purpose for each external block. This is used
/// when creating blocks to attach semantic meaning to cross-references.
pub fn annotate_cross_references(
    external_blocks: &[(BlockId, NodeKey, CrossRefPurpose)],
) -> Vec<CrossReference> {
    external_blocks
        .iter()
        .map(|(block_id, creator, purpose)| CrossReference {
            external_block: *block_id,
            external_creator: *creator,
            purpose: purpose.clone(),
        })
        .collect()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ordering::OrderingConfig;

    fn make_key(id: u8) -> NodeKey {
        [id; 32]
    }

    fn make_block(creator: u8, seq: u64, preds: Vec<BlockId>, payload: &[u8]) -> Block {
        Block::new(make_key(creator), seq, preds, payload.to_vec())
    }

    // ─── Test 1: Block with cross-reference correctly identified ────────────

    #[test]
    fn cross_reference_correctly_identified() {
        let mut lace = Blocklace::new();

        // Group members: 1, 2, 3
        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);

        // External block from creator 10 (not in group).
        let ext_block = make_block(10, 0, vec![], b"external");
        let ext_id = lace.insert(ext_block).unwrap();

        // Group member 1 creates a block referencing the external block.
        let member_block = make_block(1, 0, vec![ext_id], b"refs-external");
        let member_id = lace.insert(member_block).unwrap();

        // Should detect the cross-reference.
        let cross_refs = lace.cross_references(&member_id, &group);
        assert_eq!(cross_refs.len(), 1);
        assert_eq!(cross_refs[0].external_block, ext_id);
        assert_eq!(cross_refs[0].external_creator, make_key(10));
    }

    // ─── Test 2: Cross-reference purpose tagging works ──────────────────────

    #[test]
    fn cross_reference_purpose_tagging() {
        let ext_id: BlockId = [0xAA; 32];
        let ext_creator = make_key(50);

        let annotations = annotate_cross_references(&[
            (ext_id, ext_creator, CrossRefPurpose::Acknowledgment),
            (
                [0xBB; 32],
                make_key(51),
                CrossRefPurpose::ProofImport {
                    proof_type: "stark".to_string(),
                },
            ),
            ([0xCC; 32], make_key(52), CrossRefPurpose::Discovery),
        ]);

        assert_eq!(annotations.len(), 3);
        assert_eq!(annotations[0].purpose, CrossRefPurpose::Acknowledgment);
        assert_eq!(
            annotations[1].purpose,
            CrossRefPurpose::ProofImport {
                proof_type: "stark".to_string()
            }
        );
        assert_eq!(annotations[2].purpose, CrossRefPurpose::Discovery);
    }

    // ─── Test 3: External block included in causal closure push ─────────────

    #[test]
    fn external_block_included_in_causal_closure_push() {
        let key_a = make_key(1);
        let mut node = Disseminator::new(key_a);

        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);

        // Insert an external block from creator 10.
        let ext_block = Block::new(make_key(10), 0, vec![], b"external-data".to_vec());
        let ext_id = ext_block.id();
        node.blocklace_mut().insert(ext_block.clone()).unwrap();

        // Create a member block that references the external block.
        let member_block = Block::new(key_a, 0, vec![ext_id], b"refs-external".to_vec());
        node.blocklace_mut().insert(member_block.clone()).unwrap();

        // The push should include the external block for causal closure.
        let external_for_push = node.cross_reference_blocks_for_push(&member_block, &group);
        assert_eq!(external_for_push.len(), 1);
        assert_eq!(external_for_push[0], ext_id);
    }

    // ─── Test 4: External block does NOT appear in tau_unified output ────────

    #[test]
    fn external_block_not_in_tau_unified_output() {
        let members = vec![make_key(1), make_key(2), make_key(3)];
        let group = ReferenceGroup::new(members.clone(), 10);
        let config = OrderingConfig::default();

        let mut lace = Blocklace::new();

        // External block.
        let ext_block = make_block(10, 0, vec![], b"ext");
        let ext_id = lace.insert(ext_block).unwrap();

        // Round 1: all members create blocks, member 1 also references external.
        let b1 = make_block(1, 0, vec![ext_id], b"m1-r1");
        let b1_id = lace.insert(b1).unwrap();
        let b2 = make_block(2, 0, vec![], b"m2-r1");
        let b2_id = lace.insert(b2).unwrap();
        let b3 = make_block(3, 0, vec![], b"m3-r1");
        let b3_id = lace.insert(b3).unwrap();

        // Round 2: all reference previous round's member blocks.
        let preds_r2 = vec![b1_id, b2_id, b3_id];
        let r2_1 = make_block(1, 1, preds_r2.clone(), b"m1-r2");
        let r2_1_id = lace.insert(r2_1).unwrap();
        let r2_2 = make_block(2, 1, preds_r2.clone(), b"m2-r2");
        let r2_2_id = lace.insert(r2_2).unwrap();
        let r2_3 = make_block(3, 1, preds_r2.clone(), b"m3-r2");
        let r2_3_id = lace.insert(r2_3).unwrap();

        // Round 3.
        let preds_r3 = vec![r2_1_id, r2_2_id, r2_3_id];
        let r3_1 = make_block(1, 2, preds_r3.clone(), b"m1-r3");
        lace.insert(r3_1).unwrap();
        let r3_2 = make_block(2, 2, preds_r3.clone(), b"m2-r3");
        lace.insert(r3_2).unwrap();
        let r3_3 = make_block(3, 2, preds_r3.clone(), b"m3-r3");
        lace.insert(r3_3).unwrap();

        // Run tau_unified.
        let result = crate::ordering::tau_unified(&lace, &group, &config);

        // External block should NOT appear in the output.
        assert!(
            !result.contains(&ext_id),
            "external block should not be in tau_unified output"
        );

        // All output should be from group members.
        for &bid in &result {
            let block = lace.get(&bid).unwrap();
            assert!(
                group.is_member(&block.creator),
                "all tau_unified output should be from group members"
            );
        }

        // Should still finalize member blocks.
        assert_eq!(result.len(), 9, "should finalize all 9 member blocks");
    }

    // ─── Test 5: Cross-group proof delivery via DAG ─────────────────────────

    #[test]
    fn cross_group_proof_delivery_via_dag() {
        let mut lace = Blocklace::new();
        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);

        // External prover (creator 20) produces a proof block.
        let proof_data = DagDeliveredProof {
            proof: vec![0xDE, 0xAD, 0xBE, 0xEF],
            source_block: [0x11; 32],
            proof_type: "stark-v1".to_string(),
            public_inputs: vec![42, 7, 13],
        };

        let proof_payload =
            postcard::to_stdvec(&BlockPayload::CrossGroupProof(proof_data.clone())).unwrap();
        let ext_proof_block = make_block(20, 0, vec![], &proof_payload);
        let ext_proof_id = lace.insert(ext_proof_block).unwrap();

        // Group member imports the proof by referencing the external proof block.
        let member_block = make_block(1, 0, vec![ext_proof_id], b"import-proof");
        let member_id = lace.insert(member_block).unwrap();

        // Verify the cross-reference exists.
        let cross_refs = lace.cross_references(&member_id, &group);
        assert_eq!(cross_refs.len(), 1);
        assert_eq!(cross_refs[0].external_block, ext_proof_id);
        assert_eq!(cross_refs[0].external_creator, make_key(20));

        // Verify we can deserialize the proof from the external block's payload.
        let ext_block = lace.get(&ext_proof_id).unwrap();
        let decoded_payload: BlockPayload = postcard::from_bytes(&ext_block.payload).unwrap();
        match decoded_payload {
            BlockPayload::CrossGroupProof(proof) => {
                assert_eq!(proof.proof_type, "stark-v1");
                assert_eq!(proof.public_inputs, vec![42, 7, 13]);
                assert_eq!(proof.proof, vec![0xDE, 0xAD, 0xBE, 0xEF]);
            }
            _ => panic!("expected CrossGroupProof payload"),
        }
    }

    // ─── Test 6: Policy: Unrestricted allows any cross-ref ──────────────────

    #[test]
    fn policy_unrestricted_allows_any_cross_ref() {
        let mut lace = Blocklace::new();
        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);
        let policy = CrossRefPolicy::Unrestricted;

        // External block.
        let ext = make_block(10, 0, vec![], b"ext");
        let ext_id = lace.insert(ext).unwrap();

        // Member 1 references external.
        let m1 = make_block(1, 0, vec![ext_id], b"m1");
        let m1_id = lace.insert(m1).unwrap();

        // Member 2 references external.
        let m2 = make_block(2, 0, vec![ext_id], b"m2");
        let m2_id = lace.insert(m2).unwrap();

        // Both should be valid under Unrestricted policy.
        assert!(validate_cross_references(&lace, &m1_id, &group, &policy).is_ok());
        assert!(validate_cross_references(&lace, &m2_id, &group, &policy).is_ok());
    }

    // ─── Test 7: Policy: BridgeMembersOnly rejects non-bridge cross-refs ────

    #[test]
    fn policy_bridge_members_only_rejects_non_bridge() {
        let mut lace = Blocklace::new();
        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);

        // Only member 1 is a bridge member.
        let policy = CrossRefPolicy::BridgeMembersOnly {
            bridge_members: vec![make_key(1)],
        };

        // External block.
        let ext = make_block(10, 0, vec![], b"ext");
        let ext_id = lace.insert(ext).unwrap();

        // Member 1 (bridge) references external — should be OK.
        let m1 = make_block(1, 0, vec![ext_id], b"m1-bridge");
        let m1_id = lace.insert(m1).unwrap();
        assert!(validate_cross_references(&lace, &m1_id, &group, &policy).is_ok());

        // Member 2 (not bridge) references external — should be REJECTED.
        let m2 = make_block(2, 0, vec![ext_id], b"m2-not-bridge");
        let m2_id = lace.insert(m2).unwrap();
        assert!(validate_cross_references(&lace, &m2_id, &group, &policy).is_err());

        // Member 3 (not bridge) references external — should be REJECTED.
        let m3 = make_block(3, 0, vec![ext_id], b"m3-not-bridge");
        let m3_id = lace.insert(m3).unwrap();
        assert!(validate_cross_references(&lace, &m3_id, &group, &policy).is_err());
    }

    // ─── Test 8: Policy: Forbidden rejects all cross-refs ───────────────────

    #[test]
    fn policy_forbidden_rejects_all_cross_refs() {
        let mut lace = Blocklace::new();
        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);
        let policy = CrossRefPolicy::Forbidden;

        // External block.
        let ext = make_block(10, 0, vec![], b"ext");
        let ext_id = lace.insert(ext).unwrap();

        // Any member referencing external should be rejected.
        let m1 = make_block(1, 0, vec![ext_id], b"m1");
        let m1_id = lace.insert(m1).unwrap();
        assert!(validate_cross_references(&lace, &m1_id, &group, &policy).is_err());

        // But a block with no cross-references should be fine.
        let m2 = make_block(2, 0, vec![], b"m2-no-crossref");
        let m2_id = lace.insert(m2).unwrap();
        assert!(validate_cross_references(&lace, &m2_id, &group, &policy).is_ok());
    }

    // ─── Test 9: Multiple cross-references in one block ─────────────────────

    #[test]
    fn multiple_cross_references_in_one_block() {
        let mut lace = Blocklace::new();
        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);

        // Multiple external blocks from different creators.
        let ext_a = make_block(10, 0, vec![], b"ext-a");
        let ext_a_id = lace.insert(ext_a).unwrap();
        let ext_b = make_block(11, 0, vec![], b"ext-b");
        let ext_b_id = lace.insert(ext_b).unwrap();
        let ext_c = make_block(12, 0, vec![], b"ext-c");
        let ext_c_id = lace.insert(ext_c).unwrap();

        // Member 1 references all three external blocks.
        let m1 = make_block(1, 0, vec![ext_a_id, ext_b_id, ext_c_id], b"multi-ref");
        let m1_id = lace.insert(m1).unwrap();

        // Should detect all three cross-references.
        let cross_refs = lace.cross_references(&m1_id, &group);
        assert_eq!(cross_refs.len(), 3);

        let external_creators: HashSet<NodeKey> =
            cross_refs.iter().map(|r| r.external_creator).collect();
        assert!(external_creators.contains(&make_key(10)));
        assert!(external_creators.contains(&make_key(11)));
        assert!(external_creators.contains(&make_key(12)));

        // has_cross_references should also return true.
        assert!(lace.has_cross_references(&m1_id, &group));
    }

    // ─── Test 10: Discovery via cross-reference (interest discovery) ────────

    #[test]
    fn discovery_via_cross_reference() {
        use crate::dissemination::{InterestDiscovery, Subscription};

        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);
        let sub = Subscription::from_reference_group(&group);
        let mut discovery = InterestDiscovery::new(2); // auto-subscribe after 2 references

        let mut lace = Blocklace::new();

        // External block from strand 50.
        let ext = make_block(50, 0, vec![], b"ext-discovery");
        let ext_id = lace.insert(ext).unwrap();

        // Member 1 references external strand 50.
        let m1 = make_block(1, 0, vec![ext_id], b"m1-discovers");
        let m1_id = lace.insert(m1).unwrap();

        // Detect cross-references and feed into interest discovery.
        let cross_refs = lace.cross_references(&m1_id, &group);
        for cr in &cross_refs {
            discovery.record_reference(cr.external_creator, &sub);
        }

        // First reference: not yet at threshold.
        assert!(discovery.discovered.contains(&make_key(50)));
        assert_eq!(discovery.reference_counts[&make_key(50)], 1);
        assert!(discovery.strands_to_auto_subscribe().is_empty());

        // Member 2 also references the same external strand.
        let m2 = make_block(2, 0, vec![ext_id], b"m2-also-discovers");
        let m2_id = lace.insert(m2).unwrap();

        let cross_refs_2 = lace.cross_references(&m2_id, &group);
        for cr in &cross_refs_2 {
            discovery.record_reference(cr.external_creator, &sub);
        }

        // Second reference: crossed threshold (2).
        assert_eq!(discovery.reference_counts[&make_key(50)], 2);
        let auto_subs = discovery.strands_to_auto_subscribe();
        assert!(
            auto_subs.contains(&make_key(50)),
            "strand 50 should be auto-subscribed after 2 references"
        );
    }

    // ─── Test 11: has_cross_references returns false for internal-only ──────

    #[test]
    fn has_cross_references_false_for_internal_only() {
        let mut lace = Blocklace::new();
        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);

        // Only internal references.
        let b1 = make_block(1, 0, vec![], b"m1");
        let b1_id = lace.insert(b1).unwrap();
        let b2 = make_block(2, 0, vec![b1_id], b"m2-refs-m1");
        let b2_id = lace.insert(b2).unwrap();

        assert!(!lace.has_cross_references(&b2_id, &group));
        assert!(lace.cross_references(&b2_id, &group).is_empty());
    }

    // ─── Test 12: external_causal_context finds all external blocks ─────────

    #[test]
    fn external_causal_context_finds_all_external_blocks() {
        let mut lace = Blocklace::new();
        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);

        // Several external blocks.
        let ext1 = make_block(10, 0, vec![], b"ext1");
        let ext1_id = lace.insert(ext1).unwrap();
        let ext2 = make_block(11, 0, vec![], b"ext2");
        let ext2_id = lace.insert(ext2).unwrap();

        // Member 1 references ext1.
        let m1 = make_block(1, 0, vec![ext1_id], b"m1");
        let m1_id = lace.insert(m1).unwrap();

        // Member 2 references ext2 and m1.
        let m2 = make_block(2, 0, vec![ext2_id, m1_id], b"m2");
        lace.insert(m2).unwrap();

        // Member 3 references m1 (no direct external ref, but ext1 is in causal past).
        let m3 = make_block(3, 0, vec![m1_id], b"m3");
        lace.insert(m3).unwrap();

        let externals = lace.external_causal_context(&group);
        let ext_set: HashSet<BlockId> = externals.into_iter().collect();

        // Both ext1 and ext2 should be in the external causal context.
        assert!(
            ext_set.contains(&ext1_id),
            "ext1 should be in external causal context"
        );
        assert!(
            ext_set.contains(&ext2_id),
            "ext2 should be in external causal context"
        );
    }

    // ─── Test 13: DagDeliveredProof serialization roundtrip ─────────────────

    #[test]
    fn dag_delivered_proof_serialization_roundtrip() {
        let proof = DagDeliveredProof {
            proof: vec![1, 2, 3, 4, 5],
            source_block: [0xAB; 32],
            proof_type: "plonky3-recursive".to_string(),
            public_inputs: vec![100, 200, 300],
        };

        let payload = BlockPayload::CrossGroupProof(proof.clone());
        let bytes = postcard::to_stdvec(&payload).unwrap();
        let decoded: BlockPayload = postcard::from_bytes(&bytes).unwrap();

        match decoded {
            BlockPayload::CrossGroupProof(decoded_proof) => {
                assert_eq!(decoded_proof.proof, proof.proof);
                assert_eq!(decoded_proof.source_block, proof.source_block);
                assert_eq!(decoded_proof.proof_type, proof.proof_type);
                assert_eq!(decoded_proof.public_inputs, proof.public_inputs);
            }
            _ => panic!("expected CrossGroupProof"),
        }
    }

    // ─── Test 14: TurnWithProofs payload ────────────────────────────────────

    #[test]
    fn turn_with_proofs_payload_roundtrip() {
        let proof1 = DagDeliveredProof {
            proof: vec![0xDE, 0xAD],
            source_block: [0x11; 32],
            proof_type: "stark".to_string(),
            public_inputs: vec![1],
        };
        let proof2 = DagDeliveredProof {
            proof: vec![0xBE, 0xEF],
            source_block: [0x22; 32],
            proof_type: "groth16".to_string(),
            public_inputs: vec![2, 3],
        };

        let payload = BlockPayload::TurnWithProofs {
            turn: b"execute-something".to_vec(),
            proofs: vec![proof1, proof2],
        };

        let bytes = postcard::to_stdvec(&payload).unwrap();
        let decoded: BlockPayload = postcard::from_bytes(&bytes).unwrap();

        match decoded {
            BlockPayload::TurnWithProofs { turn, proofs } => {
                assert_eq!(turn, b"execute-something");
                assert_eq!(proofs.len(), 2);
                assert_eq!(proofs[0].proof_type, "stark");
                assert_eq!(proofs[1].proof_type, "groth16");
            }
            _ => panic!("expected TurnWithProofs"),
        }
    }

    // ─── Test 15: Policy RequiresApproval rejects cross-refs ────────────────

    #[test]
    fn policy_requires_approval_rejects_cross_refs() {
        let mut lace = Blocklace::new();
        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);
        let policy = CrossRefPolicy::RequiresApproval;

        let ext = make_block(10, 0, vec![], b"ext");
        let ext_id = lace.insert(ext).unwrap();

        let m1 = make_block(1, 0, vec![ext_id], b"m1");
        let m1_id = lace.insert(m1).unwrap();

        // RequiresApproval rejects (approval flow not implemented here).
        assert!(validate_cross_references(&lace, &m1_id, &group, &policy).is_err());
    }
}
