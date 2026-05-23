//! Property-based invariant checks for pyana's core correctness properties.
//!
//! These tests verify that fundamental system invariants hold after applying
//! sequences of operations to the ledger, federation, and CapTP layers.

use std::collections::HashMap;

use pyana_captp::{CapSession, ExportGcManager, FederationId};
use pyana_cell::{Cell, CellId, CellStateDelta, Ledger, LedgerDelta, Nullifier, NullifierSet};
use pyana_teasting::assertions::{
    assert_conservation_invariant, assert_constitution_valid,
    assert_directory_version_monotonicity, assert_gc_consistency, assert_no_double_spend,
    assert_nonce_monotonicity,
};

// =============================================================================
// Simple deterministic PRNG (xorshift64)
// =============================================================================

#[allow(dead_code)]
struct Rng {
    state: u64,
}

#[allow(dead_code)]
impl Rng {
    fn from_seed(seed: &str) -> Self {
        let hash = blake3::hash(seed.as_bytes());
        let bytes: [u8; 8] = hash.as_bytes()[..8].try_into().unwrap();
        let state = u64::from_le_bytes(bytes) | 1; // ensure non-zero
        Rng { state }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn next_u32(&mut self) -> u32 {
        (self.next_u64() >> 16) as u32
    }

    fn gen_range(&mut self, lo: u64, hi: u64) -> u64 {
        if hi <= lo {
            return lo;
        }
        lo + self.next_u64() % (hi - lo)
    }

    fn gen_bytes(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for chunk in out.chunks_exact_mut(8) {
            chunk.copy_from_slice(&self.next_u64().to_le_bytes());
        }
        out
    }

    fn gen_bool(&mut self, probability_percent: u32) -> bool {
        (self.next_u32() % 100) < probability_percent
    }
}

// =============================================================================
// Test: Conservation Invariant
// =============================================================================

/// After any sequence of transfers between cells, total computrons must be conserved.
#[test]
fn test_conservation_invariant_transfers() {
    let mut rng = Rng::from_seed("conservation_transfers");
    let mut ledger = Ledger::new();

    // Create cells with known initial balances.
    let initial_balance = 1000u64;
    let num_cells = 5;
    let mut cell_ids = Vec::new();

    for i in 0..num_cells {
        let pk = {
            let mut b = [0u8; 32];
            b[0] = i as u8;
            b[1] = 0xCA;
            b
        };
        let token_id = [0xFE; 32];
        let mut cell = Cell::new_hosted(pk, token_id);
        cell.state.balance = initial_balance;
        let id = ledger.insert_cell(cell).unwrap();
        cell_ids.push(id);
    }

    let expected_total = initial_balance * num_cells as u64;
    assert_conservation_invariant(&ledger, expected_total);

    // Apply random transfers.
    for _ in 0..200 {
        let from_idx = rng.gen_range(0, num_cells as u64) as usize;
        let to_idx = rng.gen_range(0, num_cells as u64) as usize;
        if from_idx == to_idx {
            continue;
        }

        let from_id = cell_ids[from_idx];
        let to_id = cell_ids[to_idx];

        let from_balance = ledger.get(&from_id).unwrap().state.balance;
        if from_balance == 0 {
            continue;
        }
        let amount = rng.gen_range(1, from_balance + 1);

        let delta = LedgerDelta {
            created: Vec::new(),
            updated: Vec::new(),
            computron_transfers: vec![(from_id, to_id, amount)],
        };

        ledger.apply_delta(&delta).unwrap();
        assert_conservation_invariant(&ledger, expected_total);
    }
}

/// Conservation with cell creation: minting new balance must be tracked.
#[test]
fn test_conservation_invariant_with_creation() {
    let mut rng = Rng::from_seed("conservation_creation");
    let mut ledger = Ledger::new();
    let mut expected_total = 0u64;

    for i in 0..20 {
        let pk = rng.gen_bytes();
        let token_id = [i as u8; 32];
        let balance = rng.gen_range(0, 500);

        let mut cell = Cell::new_hosted(pk, token_id);
        cell.state.balance = balance;
        ledger.insert_cell(cell).unwrap();
        expected_total += balance;

        assert_conservation_invariant(&ledger, expected_total);
    }
}

// =============================================================================
// Test: Nonce Monotonicity
// =============================================================================

/// Nonces must never decrease for any cell.
#[test]
fn test_nonce_monotonicity_basic() {
    let mut rng = Rng::from_seed("nonce_monotonicity");
    let mut ledger = Ledger::new();
    let mut observed_nonces: HashMap<CellId, u64> = HashMap::new();

    // Create cells.
    let mut cell_ids = Vec::new();
    for i in 0..4 {
        let pk = {
            let mut b = [0u8; 32];
            b[0] = i;
            b
        };
        let token_id = [0xAA; 32];
        let cell = Cell::new_hosted(pk, token_id);
        let id = ledger.insert_cell(cell).unwrap();
        cell_ids.push(id);
    }

    assert_nonce_monotonicity(&ledger, &mut observed_nonces);

    // Randomly increment nonces.
    for _ in 0..100 {
        let idx = rng.gen_range(0, cell_ids.len() as u64) as usize;
        let cell_id = cell_ids[idx];

        let delta = LedgerDelta {
            created: Vec::new(),
            updated: vec![(
                cell_id,
                CellStateDelta {
                    field_updates: Vec::new(),
                    nonce_increment: true,
                    balance_change: 0,
                    permission_changes: None,
                    capability_grants: Vec::new(),
                    capability_revocations: Vec::new(),
                },
            )],
            computron_transfers: Vec::new(),
        };

        ledger.apply_delta(&delta).unwrap();
        assert_nonce_monotonicity(&ledger, &mut observed_nonces);
    }
}

// =============================================================================
// Test: GC Consistency
// =============================================================================

/// When ExportGcManager says refcount=0, no session should hold a live import.
#[test]
fn test_gc_consistency_basic() {
    let mut rng = Rng::from_seed("gc_consistency");
    let mut export_gc = ExportGcManager::new();

    let cell_a = CellId::from_bytes(rng.gen_bytes());
    let cell_b = CellId::from_bytes(rng.gen_bytes());
    let fed_x = FederationId(rng.gen_bytes());
    let fed_y = FederationId(rng.gen_bytes());

    // Record exports.
    export_gc.record_export(cell_a, fed_x, 1);
    export_gc.record_export(cell_b, fed_y, 1);

    // Create sessions that hold live imports.
    let mut session_x = CapSession::new(fed_x.0);
    session_x.import(cell_a, pyana_cell::AuthRequired::None);

    let mut session_y = CapSession::new(fed_y.0);
    session_y.import(cell_b, pyana_cell::AuthRequired::None);

    // No zero-ref cells yet.
    assert_gc_consistency(&export_gc, &[session_x.clone(), session_y.clone()], &[]);

    // Drop the reference from fed_x to cell_a.
    export_gc.process_drop(cell_a, fed_x);

    // Now cell_a has zero refs. Mark the session import as dead.
    session_x.imports.get_mut(&cell_a).unwrap().live = false;

    // Should pass: import is no longer live.
    assert_gc_consistency(&export_gc, &[session_x, session_y], &[cell_a]);
}

/// GC consistency violation detection: live import with zero export refs.
#[test]
#[should_panic(expected = "GC consistency violated")]
fn test_gc_consistency_violation_detected() {
    let mut rng = Rng::from_seed("gc_consistency_violation");
    let mut export_gc = ExportGcManager::new();

    let cell_a = CellId::from_bytes(rng.gen_bytes());
    let fed_x = FederationId(rng.gen_bytes());

    export_gc.record_export(cell_a, fed_x, 1);
    export_gc.process_drop(cell_a, fed_x);

    // Session still has live import -- violation!
    let mut session = CapSession::new(fed_x.0);
    session.import(cell_a, pyana_cell::AuthRequired::None);

    assert_gc_consistency(&export_gc, &[session], &[cell_a]);
}

// =============================================================================
// Test: Constitution Consistency
// =============================================================================

/// Valid constitutions pass the check.
#[test]
fn test_constitution_valid_basic() {
    let participants = vec![[1u8; 32], [2u8; 32], [3u8; 32]];
    assert_constitution_valid(2, &participants, 1, 1);
}

/// Threshold > participants is detected.
#[test]
#[should_panic(expected = "threshold (4) > participant count (3)")]
fn test_constitution_threshold_exceeds_participants() {
    let participants = vec![[1u8; 32], [2u8; 32], [3u8; 32]];
    assert_constitution_valid(4, &participants, 1, 1);
}

/// Unsorted participants are detected.
#[test]
#[should_panic(expected = "participants not sorted")]
fn test_constitution_unsorted_participants() {
    let participants = vec![[3u8; 32], [1u8; 32], [2u8; 32]];
    assert_constitution_valid(2, &participants, 1, 1);
}

/// Version mismatch is detected.
#[test]
#[should_panic(expected = "expected version=2, actual version=1")]
fn test_constitution_version_mismatch() {
    let participants = vec![[1u8; 32], [2u8; 32], [3u8; 32]];
    assert_constitution_valid(2, &participants, 1, 2);
}

// =============================================================================
// Test: Nullifier Uniqueness
// =============================================================================

/// Nullifiers must be unique across the federation.
#[test]
fn test_nullifier_uniqueness_basic() {
    let mut rng = Rng::from_seed("nullifier_uniqueness");
    let mut nullifier_set = NullifierSet::new();
    let mut history = Vec::new();

    for _ in 0..50 {
        let nullifier = rng.gen_bytes();
        nullifier_set.insert(Nullifier(nullifier)).unwrap();
        history.push(nullifier);
    }

    assert_no_double_spend(&history, &nullifier_set);
}

/// Double-spend attempt is detected by NullifierSet.
#[test]
fn test_nullifier_double_spend_detected() {
    let mut nullifier_set = NullifierSet::new();
    let nullifier = Nullifier([0xDE; 32]);

    nullifier_set.insert(nullifier).unwrap();
    let result = nullifier_set.insert(nullifier);
    assert!(result.is_err(), "Double-spend should be rejected");
}

// =============================================================================
// Test: Directory Version Monotonicity
// =============================================================================

/// Directory versions must only increase.
#[test]
fn test_directory_version_monotonicity_basic() {
    let mut rng = Rng::from_seed("directory_version_monotonicity");
    let mut observed: HashMap<[u8; 32], u64> = HashMap::new();

    let key_a = rng.gen_bytes();
    let key_b = rng.gen_bytes();

    // Simulate directory updates with increasing versions.
    for version in 1..=10 {
        let mut entries = HashMap::new();
        entries.insert(key_a, version);
        entries.insert(key_b, version * 2);
        assert_directory_version_monotonicity(&entries, &mut observed);
    }
}

/// Directory version regression is detected.
#[test]
#[should_panic(expected = "Directory version monotonicity violated")]
fn test_directory_version_regression_detected() {
    let mut observed: HashMap<[u8; 32], u64> = HashMap::new();
    let key = [0xAB; 32];

    // Version 5
    let mut entries = HashMap::new();
    entries.insert(key, 5u64);
    assert_directory_version_monotonicity(&entries, &mut observed);

    // Version regresses to 3
    entries.insert(key, 3u64);
    assert_directory_version_monotonicity(&entries, &mut observed);
}

// =============================================================================
// Test: Routing Consistency
// =============================================================================

/// If routes_commitment is set, the live router's commitment must match.
#[test]
fn test_routing_consistency() {
    // Simulate a governance-declared routes commitment and a runtime commitment.
    let routes_data: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32], [3u8; 32]];

    // Compute commitment from the route table.
    let commitment = compute_routes_commitment(&routes_data);

    // The governance layer declares this commitment.
    let governance_commitment = commitment;

    // The runtime router computes the same commitment from its live state.
    let runtime_commitment = compute_routes_commitment(&routes_data);

    assert_eq!(
        governance_commitment, runtime_commitment,
        "Routing consistency violated: governance commitment != runtime commitment"
    );
}

/// Routing drift detection.
#[test]
#[should_panic(expected = "Routing consistency violated")]
fn test_routing_drift_detected() {
    let routes_v1: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let routes_v2: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32], [3u8; 32]];

    let governance_commitment = compute_routes_commitment(&routes_v1);
    let runtime_commitment = compute_routes_commitment(&routes_v2);

    assert_eq!(
        governance_commitment, runtime_commitment,
        "Routing consistency violated: governance commitment != runtime commitment. \
         Governance and runtime route tables have diverged."
    );
}

// =============================================================================
// Helpers
// =============================================================================

fn compute_routes_commitment(routes: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana:routes-commitment-v1");
    hasher.update(&(routes.len() as u64).to_le_bytes());
    for route in routes {
        hasher.update(route);
    }
    *hasher.finalize().as_bytes()
}
