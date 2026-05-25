//! Federation checks: block advancement, root changes, nullifiers, note tree.

use pyana_cell::{Note, NullifierSet};
use pyana_circuit::BabyBear;
use pyana_commit::poseidon2_tree::Poseidon2MerkleTree;
use pyana_sdk::{EngineConfig, PyanaEngine};

use crate::report::{CheckResult, run_check};

fn test_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("preflight-fed:{name}").as_bytes()).as_bytes()
}

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("blocks", check_block_advancement),
        run_check("roots", check_root_changes),
        run_check("nullifiers", check_nullifier_double_spend),
        run_check("note_tree", check_note_tree_updates),
        run_check("bls_threshold_aggregation", check_bls_threshold_aggregation),
        run_check(
            "bls_below_threshold_rejects",
            check_bls_below_threshold_rejects,
        ),
        run_check("bls_wrong_message_rejects", check_bls_wrong_message_rejects),
    ]
}

fn check_bls_threshold_aggregation() -> Result<(), String> {
    use pyana_federation::threshold::generate_test_committee;
    let (committee, members) =
        generate_test_committee(4, 3).map_err(|e| format!("committee creation failed: {e:?}"))?;
    let msg = b"preflight-bls-happy-path";
    let shares: Vec<_> = members
        .iter()
        .take(3)
        .map(|m| (m.index, committee.sign_share(m, msg)))
        .collect();
    let qc = committee
        .aggregate(&shares, msg)
        .map_err(|e| format!("aggregate failed: {e:?}"))?;
    committee
        .verify(&qc, msg)
        .map_err(|e| format!("verify failed: {e:?}"))?;
    Ok(())
}

fn check_bls_below_threshold_rejects() -> Result<(), String> {
    use pyana_federation::threshold::generate_test_committee;
    let (committee, members) =
        generate_test_committee(4, 3).map_err(|e| format!("committee creation failed: {e:?}"))?;
    let msg = b"preflight-bls-below-threshold";
    let shares: Vec<_> = members
        .iter()
        .take(2) // below threshold
        .map(|m| (m.index, committee.sign_share(m, msg)))
        .collect();
    match committee.aggregate(&shares, msg) {
        Err(_) => Ok(()),
        Ok(_) => Err("below-threshold aggregate MUST fail".into()),
    }
}

fn check_bls_wrong_message_rejects() -> Result<(), String> {
    use pyana_federation::threshold::generate_test_committee;
    let (committee, members) =
        generate_test_committee(4, 3).map_err(|e| format!("committee creation failed: {e:?}"))?;
    let msg = b"preflight-bls-msg";
    let wrong = b"preflight-bls-other";
    let shares: Vec<_> = members
        .iter()
        .take(3)
        .map(|m| (m.index, committee.sign_share(m, msg)))
        .collect();
    let qc = committee
        .aggregate(&shares, msg)
        .map_err(|e| format!("aggregate: {e:?}"))?;
    match committee.verify(&qc, wrong) {
        Err(_) => Ok(()),
        Ok(_) => Err("QC MUST NOT verify against the wrong message".into()),
    }
}

fn check_block_advancement() -> Result<(), String> {
    let mut engine = PyanaEngine::new(EngineConfig::for_testing());

    // Simulate block advancement
    for h in 1..=10u64 {
        engine.set_block_height(h);
        engine.set_timestamp(h as i64 * 12); // 12s blocks
    }

    if engine.executor().block_height != 10 {
        return Err(format!(
            "expected height 10, got {}",
            engine.executor().block_height
        ));
    }
    if engine.executor().current_timestamp != 120 {
        return Err(format!(
            "expected timestamp 120, got {}",
            engine.executor().current_timestamp
        ));
    }

    Ok(())
}

fn check_root_changes() -> Result<(), String> {
    let mut engine = PyanaEngine::new(EngineConfig::for_testing());

    let root1 = [0x01u8; 32];
    engine.set_federation_root(root1);
    if engine.federation_root() != root1 {
        return Err("root should be root1".into());
    }

    // Root changes when new block finalizes
    let root2 = [0x02u8; 32];
    engine.set_federation_root(root2);
    if engine.federation_root() != root2 {
        return Err("root should update to root2".into());
    }

    // Old root should not be current
    if engine.federation_root() == root1 {
        return Err("root should have changed from root1".into());
    }

    Ok(())
}

fn check_nullifier_double_spend() -> Result<(), String> {
    let mut nullifier_set = NullifierSet::new();

    let spending_key = test_key("spender");
    let note = Note::with_randomness(
        test_key("owner"),
        [100, 0, 0, 0, 0, 0, 0, 0],
        test_key("randomness"),
    );

    let nullifier = note.nullifier(&spending_key);

    // First spend: should succeed
    nullifier_set
        .insert(nullifier)
        .map_err(|e| format!("first insert failed: {e:?}"))?;

    if !nullifier_set.contains(&nullifier) {
        return Err("nullifier should be in set after insert".into());
    }

    // Double spend: should fail
    let result = nullifier_set.insert(nullifier);
    match result {
        Err(pyana_cell::NoteError::DoubleSpend { .. }) => {
            // Correct: double spend prevented
        }
        Ok(()) => return Err("double spend should be rejected".into()),
        Err(other) => return Err(format!("unexpected error: {other:?}")),
    }

    Ok(())
}

fn check_note_tree_updates() -> Result<(), String> {
    let mut note_tree = Poseidon2MerkleTree::with_depth(4);

    // Insert notes and track root history
    let mut root_history: Vec<BabyBear> = Vec::new();

    for i in 0..4u32 {
        let commitment = BabyBear::new(10000 + i);
        note_tree.append(commitment);

        let mut tree_copy = note_tree.clone();
        let root = tree_copy.root();
        root_history.push(root);
    }

    // Verify roots are all different (tree changes with each insertion)
    for i in 0..root_history.len() {
        for j in (i + 1)..root_history.len() {
            if root_history[i] == root_history[j] {
                return Err(format!("roots at position {i} and {j} should differ"));
            }
        }
    }

    // Verify membership proof for an earlier leaf still works against current root
    let mut final_tree = note_tree.clone();
    let final_root = final_tree.root();

    let proof = note_tree
        .prove_membership(0)
        .ok_or("should have proof for leaf 0")?;
    let leaf_0 = BabyBear::new(10000);
    if !Poseidon2MerkleTree::verify_membership(final_root, leaf_0, &proof) {
        return Err("membership proof for leaf 0 should verify against current root".into());
    }

    Ok(())
}
