//! Custom assertion helpers for distributed state verification.
//!
//! These go beyond simple `assert_eq!` to provide domain-specific failure messages
//! that make debugging integration test failures tractable.

use pyana_bridge::BridgePresentationProof;
#[allow(deprecated)] // test helpers intentionally use the simpler legacy verification API
use pyana_bridge::present::verify_presentation;
use pyana_circuit::BabyBear;
use pyana_circuit::predicate_air::PredicateProof;

/// Assert that a presentation proof is structurally valid (all sub-proofs present and consistent).
pub fn assert_proof_valid(proof: &BridgePresentationProof) {
    assert!(
        proof.is_valid(),
        "Presentation proof failed validity check: constraint_checked={}, fold_count={}",
        proof.is_constraint_checked(),
        proof.chain_length,
    );
}

/// Assert that a presentation proof verifies against a given federation root.
#[allow(deprecated)]
pub fn assert_proof_verifies(proof: &BridgePresentationProof, federation_root: &[u8; 32]) {
    assert!(
        verify_presentation(proof, federation_root),
        "Presentation proof failed verification against federation root {:?}",
        &federation_root[..8],
    );
}

/// Assert that a presentation proof does NOT verify (expected failure case).
#[allow(deprecated)]
pub fn assert_proof_rejects(proof: &BridgePresentationProof, federation_root: &[u8; 32]) {
    assert!(
        !verify_presentation(proof, federation_root),
        "Presentation proof SHOULD have been rejected but was accepted",
    );
}

/// Assert that a predicate proof verifies against expected public inputs.
pub fn assert_predicate_verifies(
    proof: &PredicateProof,
    threshold: BabyBear,
    fact_commitment: BabyBear,
) {
    use pyana_circuit::predicate_air::verify_predicate;
    assert!(
        verify_predicate(proof, threshold, fact_commitment).is_ok(),
        "Predicate proof failed verification: threshold={:?}, fact_commitment={:?}",
        threshold,
        fact_commitment,
    );
}

/// Assert that a predicate proof does NOT verify (forge detection).
pub fn assert_predicate_rejects(
    proof: &PredicateProof,
    threshold: BabyBear,
    fact_commitment: BabyBear,
) {
    use pyana_circuit::predicate_air::verify_predicate;
    assert!(
        verify_predicate(proof, threshold, fact_commitment).is_err(),
        "Predicate proof SHOULD have been rejected but passed verification",
    );
}

/// Assert that two byte slices are NOT equal (unlinkability check).
pub fn assert_unlinkable(a: &[u8], b: &[u8], context: &str) {
    assert_ne!(
        a, b,
        "Unlinkability violation in {}: two values that should differ are identical",
        context,
    );
}

/// Assert that all nodes in a federation agree on state.
pub fn assert_federation_consistent(
    harness: &mut crate::harness::SimulationHarness,
    fed_idx: usize,
) {
    harness.assert_all_nodes_agree(fed_idx);
}

// =============================================================================
// Invariant Checkers
// =============================================================================

use pyana_captp::{CapSession, ExportGcManager};
use pyana_cell::{CellId, Ledger, Nullifier, NullifierSet};
use std::collections::{HashMap, HashSet};

/// Conservation invariant: total computrons across all cells must equal
/// (initial + minted - burned). Since the ledger does not track mint/burn history,
/// this checks that the sum of all cell balances matches the expected total.
///
/// After any sequence of transfers, balance must be conserved (no creation/destruction).
pub fn assert_conservation_invariant(ledger: &Ledger, expected_total: u64) {
    let actual_total: u64 = ledger.iter().map(|(_, cell)| cell.state.balance).sum();
    assert_eq!(
        actual_total,
        expected_total,
        "Conservation invariant violated: expected total={}, actual total={}. \
         Difference = {} computrons {} from nothing.",
        expected_total,
        actual_total,
        if actual_total > expected_total {
            actual_total - expected_total
        } else {
            expected_total - actual_total
        },
        if actual_total > expected_total {
            "created"
        } else {
            "destroyed"
        },
    );
}

/// Nonce monotonicity: for every cell, the nonce must be >= any previously observed nonce.
/// Caller provides a map of previously observed nonces; this function updates it and panics
/// if any nonce went backward.
pub fn assert_nonce_monotonicity(ledger: &Ledger, observed_nonces: &mut HashMap<CellId, u64>) {
    for (cell_id, cell) in ledger.iter() {
        let current_nonce = cell.state.nonce;
        if let Some(&prev_nonce) = observed_nonces.get(cell_id) {
            assert!(
                current_nonce >= prev_nonce,
                "Nonce monotonicity violated for cell {:?}: previous nonce={}, current nonce={}. \
                 Time went backward.",
                cell_id,
                prev_nonce,
                current_nonce,
            );
        }
        observed_nonces.insert(*cell_id, current_nonce);
    }
}

/// GC consistency: if ExportGcManager says refcount=0 for a cell, no session should
/// hold a live import reference to it.
pub fn assert_gc_consistency(
    export_gc: &ExportGcManager,
    sessions: &[CapSession],
    zero_ref_cells: &[CellId],
) {
    for cell_id in zero_ref_cells {
        // Verify the export GC agrees it has zero refs
        if let Some(entry) = export_gc.get(cell_id) {
            assert_eq!(
                entry.total_refs, 0,
                "GC consistency check: cell {:?} expected zero refs but ExportGcManager says total_refs={}",
                cell_id, entry.total_refs,
            );
        }

        // Check no session has a live import for this cell
        for session in sessions {
            if let Some(import) = session.imports.get(cell_id) {
                assert!(
                    !import.live,
                    "GC consistency violated: cell {:?} has refcount=0 in ExportGcManager, \
                     but session with peer {:02x}{:02x}... still holds a LIVE import.",
                    cell_id, session.peer_id[0], session.peer_id[1],
                );
            }
        }
    }
}

/// Constitution consistency: threshold <= participant count, participants sorted and deduped,
/// version increments exactly once per applied proposal.
pub fn assert_constitution_valid(
    threshold: usize,
    participants: &[[u8; 32]],
    version: u64,
    expected_version: u64,
) {
    // Threshold must be <= participant count
    assert!(
        threshold <= participants.len(),
        "Constitution invariant violated: threshold ({}) > participant count ({})",
        threshold,
        participants.len(),
    );

    // Threshold must be > 0 (at least one signer required)
    assert!(
        threshold > 0,
        "Constitution invariant violated: threshold is 0 (no signers required)",
    );

    // Participants must be sorted
    for i in 1..participants.len() {
        assert!(
            participants[i - 1] < participants[i],
            "Constitution invariant violated: participants not sorted at index {}. \
             {:02x}{:02x}... >= {:02x}{:02x}...",
            i,
            participants[i - 1][0],
            participants[i - 1][1],
            participants[i][0],
            participants[i][1],
        );
    }

    // Version must match expected
    assert_eq!(
        version, expected_version,
        "Constitution invariant violated: expected version={}, actual version={}",
        expected_version, version,
    );
}

/// Nullifier uniqueness: a nullifier can appear at most once. Attempts to insert a
/// duplicate must fail. This function verifies that a set of nullifiers has no duplicates
/// and checks insertion of each one.
pub fn assert_no_double_spend(nullifiers_seen: &[[u8; 32]], nullifier_set: &NullifierSet) {
    let mut seen = HashSet::new();
    for nullifier in nullifiers_seen {
        assert!(
            seen.insert(*nullifier),
            "Double-spend invariant violated: nullifier {:02x}{:02x}{:02x}{:02x}... \
             appeared more than once in federation history.",
            nullifier[0],
            nullifier[1],
            nullifier[2],
            nullifier[3],
        );
        assert!(
            nullifier_set.contains(&Nullifier(*nullifier)),
            "Nullifier {:02x}{:02x}{:02x}{:02x}... was recorded in history but is NOT \
             in the NullifierSet (inconsistent state).",
            nullifier[0],
            nullifier[1],
            nullifier[2],
            nullifier[3],
        );
    }
}

/// Directory version monotonicity: directory entry versions only go up.
/// Caller provides a map of previously observed versions; this updates and checks.
pub fn assert_directory_version_monotonicity(
    entries: &HashMap<[u8; 32], u64>,
    observed_versions: &mut HashMap<[u8; 32], u64>,
) {
    for (key, &version) in entries {
        if let Some(&prev_version) = observed_versions.get(key) {
            assert!(
                version >= prev_version,
                "Directory version monotonicity violated for entry {:02x}{:02x}...: \
                 previous version={}, current version={}",
                key[0],
                key[1],
                prev_version,
                version,
            );
        }
        observed_versions.insert(*key, version);
    }
}
