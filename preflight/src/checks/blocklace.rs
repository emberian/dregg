//! Blocklace consensus checks: block creation, merge, equivocation detection,
//! finality progression, and constitution membership changes.

use dregg_blocklace::constitution::{ConstitutionManager, MembershipProposal, MembershipVote};
use dregg_blocklace::finality::{
    Block, BlockError, BlockId, Blocklace, EquivocationProof, FinalityLevel, FinalityTracker,
    Payload,
};
use ed25519_dalek::SigningKey;

use crate::report::{CheckResult, run_check};

fn make_key(seed: &[u8]) -> SigningKey {
    let hash = blake3::hash(seed);
    SigningKey::from_bytes(hash.as_bytes())
}

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("create_block", check_create_block),
        run_check("merge", check_merge),
        run_check("equivocation", check_equivocation_detection),
        run_check("finality", check_finality_progression),
        run_check("constitution", check_constitution_membership),
    ]
}

/// Verify block creation: signed, unique IDs, predecessors tracked.
fn check_create_block() -> Result<(), String> {
    let key = make_key(b"blocklace-node-1");
    let mut lace = Blocklace::new_simple(key.clone());

    // Create first block.
    let block1 = lace.add_block(Payload::Data(b"hello".to_vec()));
    block1
        .verify_signature()
        .map_err(|e| format!("block1 sig invalid: {e}"))?;

    if lace.len() != 1 {
        return Err(format!("expected 1 block, got {}", lace.len()));
    }

    // Create second block: should reference block1 as predecessor.
    let block2 = lace.add_block(Payload::Data(b"world".to_vec()));
    block2
        .verify_signature()
        .map_err(|e| format!("block2 sig invalid: {e}"))?;

    if block2.predecessors.is_empty() {
        return Err("block2 should have predecessors".into());
    }
    if !block2.predecessors.contains(&block1.id()) {
        return Err("block2 should reference block1 as predecessor".into());
    }

    // Block IDs must be unique.
    if block1.id() == block2.id() {
        return Err("distinct blocks should have distinct IDs".into());
    }

    // Serialization round-trip.
    let bytes = block1.to_bytes();
    let restored = Block::from_bytes(&bytes).ok_or("block deserialization failed")?;
    if restored.id() != block1.id() {
        return Err("deserialized block should have same ID".into());
    }

    Ok(())
}

/// Verify CRDT delta-merge: receiving blocks from another node.
fn check_merge() -> Result<(), String> {
    let key_a = make_key(b"blocklace-merge-a");
    let key_b = make_key(b"blocklace-merge-b");

    let mut lace_a = Blocklace::new(key_a.clone(), 2);
    let mut lace_b = Blocklace::new(key_b.clone(), 2);

    // Node A creates a block.
    let block_a = lace_a.add_block(Payload::Data(b"from-a".to_vec()));

    // Node B receives block from A.
    lace_b
        .receive_block(block_a.clone())
        .map_err(|e| format!("receive_block failed: {e}"))?;

    if lace_b.len() != 1 {
        return Err(format!("B should have 1 block, got {}", lace_b.len()));
    }

    // Node B creates its own block (should see A's block as predecessor).
    let block_b = lace_b.add_block(Payload::Ack);
    if !block_b.predecessors.contains(&block_a.id()) {
        return Err("B's block should reference A's block".into());
    }

    // Node A receives B's ack; needs A's block as a prerequisite.
    lace_a
        .receive_block(block_b.clone())
        .map_err(|e| format!("A receiving B's block failed: {e}"))?;

    // Both nodes now have 2 blocks.
    if lace_a.len() != 2 {
        return Err(format!("A should have 2 blocks, got {}", lace_a.len()));
    }

    // Merge with causally-closed delta into a fresh node.
    let key_c = make_key(b"blocklace-merge-c");
    let mut lace_c = Blocklace::new(key_c.clone(), 2);
    // Merge both blocks into C.
    lace_c
        .merge(vec![block_a.clone(), block_b.clone()])
        .map_err(|e| format!("merge failed: {e}"))?;

    if lace_c.len() != 2 {
        return Err(format!("C should have 2 blocks, got {}", lace_c.len()));
    }

    Ok(())
}

/// Verify equivocation detection: two conflicting blocks from same creator at same seq.
fn check_equivocation_detection() -> Result<(), String> {
    let key_honest = make_key(b"blocklace-honest");
    let key_evil = make_key(b"blocklace-evil");

    let mut lace = Blocklace::new(key_honest.clone(), 2);

    // Evil node creates TWO blocks at seq 1 with different payloads.
    let evil_block_1 = Block::new(&key_evil, 1, Payload::Data(b"version-A".to_vec()), vec![]);
    let evil_block_2 = Block::new(&key_evil, 1, Payload::Data(b"version-B".to_vec()), vec![]);

    // Both blocks should have valid signatures but different IDs.
    evil_block_1
        .verify_signature()
        .map_err(|e| format!("evil_block_1 sig invalid: {e}"))?;
    evil_block_2
        .verify_signature()
        .map_err(|e| format!("evil_block_2 sig invalid: {e}"))?;

    if evil_block_1.id() == evil_block_2.id() {
        return Err("conflicting blocks should have different IDs".into());
    }

    // Receive first block: should succeed.
    lace.receive_block(evil_block_1.clone())
        .map_err(|e| format!("first evil block should be accepted: {e}"))?;

    // Receive second conflicting block: should detect equivocation.
    let result = lace.receive_block(evil_block_2.clone());
    match result {
        Err(BlockError::Equivocation { creator, seq, .. }) => {
            if creator != key_evil.verifying_key().to_bytes() {
                return Err("equivocation proof should identify the evil creator".into());
            }
            if seq != 1 {
                return Err(format!("equivocation seq should be 1, got {seq}"));
            }
        }
        Ok(()) => {
            return Err("second conflicting block should be REJECTED as equivocation".into());
        }
        Err(other) => {
            return Err(format!("unexpected error (expected equivocation): {other}"));
        }
    }

    // The equivocator should be recorded.
    if !lace
        .equivocators()
        .contains(&key_evil.verifying_key().to_bytes())
    {
        return Err("evil node should be in equivocators set".into());
    }

    Ok(())
}

/// Verify finality progression: Local -> Bilateral -> Attested -> Ordered.
fn check_finality_progression() -> Result<(), String> {
    let quorum = 3; // 2f+1 where f=1
    let mut tracker = FinalityTracker::new(quorum);

    let block_id = BlockId(*blake3::hash(b"test-block").as_bytes());

    // Initially: Local.
    let level = tracker.finality_of(&block_id);
    if level != FinalityLevel::Local {
        return Err(format!("should start as Local, got {:?}", level));
    }

    // One ack: Bilateral.
    let acker_1 = *blake3::hash(b"acker-1").as_bytes();
    let new_level = tracker.record_ack(block_id, acker_1);
    if new_level != FinalityLevel::Bilateral {
        return Err(format!(
            "one ack should give Bilateral, got {:?}",
            new_level
        ));
    }

    // Second ack: still Bilateral (need 3 for quorum).
    let acker_2 = *blake3::hash(b"acker-2").as_bytes();
    let new_level = tracker.record_ack(block_id, acker_2);
    if new_level != FinalityLevel::Bilateral {
        return Err(format!(
            "two acks should still be Bilateral, got {:?}",
            new_level
        ));
    }

    // Third ack: Attested (quorum reached).
    let acker_3 = *blake3::hash(b"acker-3").as_bytes();
    let new_level = tracker.record_ack(block_id, acker_3);
    if new_level != FinalityLevel::Attested {
        return Err(format!(
            "three acks should reach Attested, got {:?}",
            new_level
        ));
    }

    // Mark as ordered.
    tracker.mark_ordered(block_id);
    let final_level = tracker.finality_of(&block_id);
    if final_level != FinalityLevel::Ordered {
        return Err(format!(
            "after mark_ordered should be Ordered, got {:?}",
            final_level
        ));
    }

    // Duplicate ack should not regress finality.
    let _ = tracker.record_ack(block_id, acker_1);
    let still_ordered = tracker.finality_of(&block_id);
    if still_ordered != FinalityLevel::Ordered {
        return Err("finality should never regress".into());
    }

    Ok(())
}

/// Verify constitution membership change: propose, vote, apply, auto-evict.
fn check_constitution_membership() -> Result<(), String> {
    let participants: Vec<[u8; 32]> = (0..4)
        .map(|i| *blake3::hash(format!("participant-{i}").as_bytes()).as_bytes())
        .collect();

    let mut manager = ConstitutionManager::from_participants(participants.clone(), 10);

    if manager.participants().len() != 4 {
        return Err(format!(
            "expected 4 participants, got {}",
            manager.participants().len()
        ));
    }

    // Propose adding a new member.
    let new_member = *blake3::hash(b"new-member").as_bytes();
    let proposal = MembershipProposal::Join {
        node_key: new_member,
        justification: b"stake-proof-bytes".to_vec(),
    };
    let proposal_block = BlockId(*blake3::hash(b"proposal-block-id").as_bytes());

    let registered = manager.submit_proposal(proposal_block, proposal.clone());
    if !registered {
        return Err("submit_proposal should succeed".into());
    }

    // Vote from each participant (need threshold for approval).
    let threshold = manager.threshold();
    for i in 0..threshold {
        let vote = MembershipVote {
            proposal_block,
            approve: true,
        };
        manager.submit_vote(&vote, participants[i]);
    }

    // Apply the proposal.
    let applied = manager.apply_if_passed(&proposal_block);
    if !applied {
        return Err("proposal should pass after threshold votes".into());
    }

    // New member should be in the constitution now.
    if manager.participants().len() != 5 {
        return Err(format!(
            "after join, expected 5 participants, got {}",
            manager.participants().len()
        ));
    }

    // Auto-evict via equivocation proof.
    let equivocator = participants[0];
    let evil_key = make_key(format!("participant-0").as_bytes());
    let proof = EquivocationProof {
        creator: equivocator,
        block_a: Block::new(&evil_key, 1, Payload::Data(b"a".to_vec()), vec![]),
        block_b: Block::new(&evil_key, 1, Payload::Data(b"b".to_vec()), vec![]),
    };

    let evicted = manager.auto_evict(&proof);
    if !evicted {
        return Err("equivocator should be auto-evicted".into());
    }

    if manager.participants().len() != 4 {
        return Err(format!(
            "after eviction, expected 4 participants, got {}",
            manager.participants().len()
        ));
    }

    // Version should have advanced.
    if manager.version() < 2 {
        return Err(format!(
            "version should be >= 2 after changes, got {}",
            manager.version()
        ));
    }

    Ok(())
}
