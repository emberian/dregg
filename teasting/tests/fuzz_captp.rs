//! Randomized CapTP fuzzer: stress-tests GC consistency under random session operations.
//!
//! Randomly creates/tears down sessions, exports/enlivens/drops capabilities,
//! and verifies GC consistency after every action.

use std::collections::HashMap;

use pyana_captp::sturdy::SwissTable;
use pyana_captp::{
    CapSession, ExportGcManager, FederationId, HandoffCertificate, HandoffPresentation,
    validate_handoff,
};
use pyana_cell::{AuthRequired, CellId};
use pyana_teasting::assertions::assert_gc_consistency;
use pyana_types::{PublicKey, Signature};

// =============================================================================
// Deterministic PRNG (xorshift64)
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
        let state = u64::from_le_bytes(bytes) | 1;
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
// CapTP Actions
// =============================================================================

#[derive(Debug)]
enum CapAction {
    /// Create a new session with a random peer.
    CreateSession,
    /// Tear down (remove) a random session.
    TeardownSession { session_idx: usize },
    /// Export a cell to a random session peer.
    Export { session_idx: usize, cell_id: CellId },
    /// Drop (release) an export from a random session.
    DropExport { session_idx: usize, cell_id: CellId },
    /// Enliven (import) a cell from a remote peer into a random session.
    Enliven { session_idx: usize, cell_id: CellId },
    /// Drop a live import from a session.
    DropImport { session_idx: usize, cell_id: CellId },
}

// =============================================================================
// State Tracker
// =============================================================================

struct CapState {
    sessions: Vec<CapSession>,
    export_gc: ExportGcManager,
    federation_ids: Vec<FederationId>,
    /// All cells that have been exported, to track what to drop.
    exported_cells: Vec<CellId>,
    /// Map from cell_id to which federation_ids hold refs.
    export_holders: HashMap<CellId, Vec<FederationId>>,
    block_height: u64,
}

impl CapState {
    fn new() -> Self {
        CapState {
            sessions: Vec::new(),
            export_gc: ExportGcManager::new(),
            federation_ids: Vec::new(),
            exported_cells: Vec::new(),
            export_holders: HashMap::new(),
            block_height: 1,
        }
    }

    fn verify_gc_consistency(&self) {
        // Find all cells with zero total refs in the export GC.
        let zero_ref_cells: Vec<CellId> = self
            .exported_cells
            .iter()
            .filter(|cell_id| {
                match self.export_gc.get(cell_id) {
                    Some(entry) => entry.total_refs == 0,
                    None => true, // Not in export table at all = zero refs.
                }
            })
            .copied()
            .collect();

        assert_gc_consistency(&self.export_gc, &self.sessions, &zero_ref_cells);
    }
}

fn generate_action(rng: &mut Rng, state: &CapState) -> CapAction {
    if state.sessions.is_empty() {
        return CapAction::CreateSession;
    }

    match rng.next_u32() % 6 {
        0 => CapAction::CreateSession,
        1 => {
            let idx = rng.gen_range(0, state.sessions.len() as u64) as usize;
            CapAction::TeardownSession { session_idx: idx }
        }
        2 => {
            let idx = rng.gen_range(0, state.sessions.len() as u64) as usize;
            let cell_id = CellId::from_bytes(rng.gen_bytes());
            CapAction::Export {
                session_idx: idx,
                cell_id,
            }
        }
        3 => {
            // Try to drop an existing export.
            let idx = rng.gen_range(0, state.sessions.len() as u64) as usize;
            let cell_id = if state.exported_cells.is_empty() {
                CellId::from_bytes(rng.gen_bytes()) // random, will be a no-op
            } else {
                let cell_idx = rng.gen_range(0, state.exported_cells.len() as u64) as usize;
                state.exported_cells[cell_idx]
            };
            CapAction::DropExport {
                session_idx: idx,
                cell_id,
            }
        }
        4 => {
            let idx = rng.gen_range(0, state.sessions.len() as u64) as usize;
            let cell_id = CellId::from_bytes(rng.gen_bytes());
            CapAction::Enliven {
                session_idx: idx,
                cell_id,
            }
        }
        _ => {
            // Drop a live import.
            let idx = rng.gen_range(0, state.sessions.len() as u64) as usize;
            let cell_id = if state.sessions[idx].imports.is_empty() {
                CellId::from_bytes(rng.gen_bytes())
            } else {
                let import_ids: Vec<CellId> = state.sessions[idx].imports.keys().copied().collect();
                let pick = rng.gen_range(0, import_ids.len() as u64) as usize;
                import_ids[pick]
            };
            CapAction::DropImport {
                session_idx: idx,
                cell_id,
            }
        }
    }
}

fn apply_action(state: &mut CapState, action: &CapAction, rng: &mut Rng) {
    match action {
        CapAction::CreateSession => {
            let peer_id = rng.gen_bytes();
            let fed_id = FederationId(peer_id);
            state.sessions.push(CapSession::new(peer_id));
            state.federation_ids.push(fed_id);
        }
        CapAction::TeardownSession { session_idx } => {
            if *session_idx >= state.sessions.len() {
                return;
            }

            // Collect IDs before mutating.
            let import_ids: Vec<CellId> = state.sessions[*session_idx]
                .imports
                .keys()
                .copied()
                .collect();
            let exported: Vec<CellId> = state.sessions[*session_idx]
                .exports
                .keys()
                .copied()
                .collect();
            let fed_id = state.federation_ids[*session_idx];

            // Mark all imports from this session as dead.
            for cell_id in &import_ids {
                if let Some(import) = state.sessions[*session_idx].imports.get_mut(cell_id) {
                    import.live = false;
                }
            }

            // Process drops for all exports TO this session's peer.
            for cell_id in &exported {
                state.export_gc.process_drop(*cell_id, fed_id);
                // Remove from holders tracking.
                if let Some(holders) = state.export_holders.get_mut(cell_id) {
                    holders.retain(|f| *f != fed_id);
                }
            }

            state.sessions.remove(*session_idx);
            state.federation_ids.remove(*session_idx);
        }
        CapAction::Export {
            session_idx,
            cell_id,
        } => {
            if *session_idx >= state.sessions.len() {
                return;
            }
            let fed_id = state.federation_ids[*session_idx];

            // Export to the session.
            state.sessions[*session_idx].export(*cell_id, AuthRequired::None);

            // Record in GC.
            state.block_height += 1;
            state
                .export_gc
                .record_export(*cell_id, fed_id, state.block_height);

            // Track.
            if !state.exported_cells.contains(cell_id) {
                state.exported_cells.push(*cell_id);
            }
            state
                .export_holders
                .entry(*cell_id)
                .or_default()
                .push(fed_id);
        }
        CapAction::DropExport {
            session_idx,
            cell_id,
        } => {
            if *session_idx >= state.sessions.len() {
                return;
            }
            let fed_id = state.federation_ids[*session_idx];

            // Release from session.
            state.sessions[*session_idx].release_export(cell_id);

            // Process drop in GC.
            state.export_gc.process_drop(*cell_id, fed_id);

            // Update holders tracking.
            if let Some(holders) = state.export_holders.get_mut(cell_id) {
                if let Some(pos) = holders.iter().position(|f| *f == fed_id) {
                    holders.remove(pos);
                }
            }
        }
        CapAction::Enliven {
            session_idx,
            cell_id,
        } => {
            if *session_idx >= state.sessions.len() {
                return;
            }
            state.sessions[*session_idx].import(*cell_id, AuthRequired::None);
        }
        CapAction::DropImport {
            session_idx,
            cell_id,
        } => {
            if *session_idx >= state.sessions.len() {
                return;
            }
            if let Some(import) = state.sessions[*session_idx].imports.get_mut(cell_id) {
                import.live = false;
            }
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

/// Run 500 random CapTP actions and verify GC consistency after each.
#[test]
fn test_fuzz_captp_gc_500_actions() {
    let mut rng = Rng::from_seed("fuzz_captp_gc_500");
    let mut state = CapState::new();

    for _i in 0..500 {
        let action = generate_action(&mut rng, &state);
        apply_action(&mut state, &action, &mut rng);
        state.verify_gc_consistency();
    }
}

/// Fuzz with many exports and drops to stress refcounting.
#[test]
fn test_fuzz_captp_heavy_export_drop() {
    let mut rng = Rng::from_seed("fuzz_captp_heavy_export_drop");
    let mut state = CapState::new();

    // Create 4 sessions.
    for _ in 0..4 {
        apply_action(&mut state, &CapAction::CreateSession, &mut rng);
    }

    // Export many cells.
    let mut cells: Vec<CellId> = Vec::new();
    for _ in 0..100 {
        let cell_id = CellId::from_bytes(rng.gen_bytes());
        cells.push(cell_id);
        let session_idx = rng.gen_range(0, 4) as usize;
        apply_action(
            &mut state,
            &CapAction::Export {
                session_idx,
                cell_id,
            },
            &mut rng,
        );
        state.verify_gc_consistency();
    }

    // Drop them in random order.
    let mut remaining = cells.clone();
    while !remaining.is_empty() {
        let idx = rng.gen_range(0, remaining.len() as u64) as usize;
        let cell_id = remaining.remove(idx);

        // Find a session that holds this export.
        let holders = state
            .export_holders
            .get(&cell_id)
            .cloned()
            .unwrap_or_default();
        if holders.is_empty() {
            continue;
        }
        let fed_id = holders[0];
        let session_idx = state.federation_ids.iter().position(|f| *f == fed_id);
        if let Some(session_idx) = session_idx {
            apply_action(
                &mut state,
                &CapAction::DropExport {
                    session_idx,
                    cell_id,
                },
                &mut rng,
            );
            state.verify_gc_consistency();
        }
    }
}

/// Fuzz session teardown: tearing down a session must release all its exports.
#[test]
fn test_fuzz_captp_session_teardown_releases_exports() {
    let mut rng = Rng::from_seed("fuzz_captp_session_teardown");
    let mut state = CapState::new();

    // Create sessions and export cells.
    for _ in 0..5 {
        apply_action(&mut state, &CapAction::CreateSession, &mut rng);
    }

    for _ in 0..50 {
        let session_idx = rng.gen_range(0, state.sessions.len() as u64) as usize;
        let cell_id = CellId::from_bytes(rng.gen_bytes());
        apply_action(
            &mut state,
            &CapAction::Export {
                session_idx,
                cell_id,
            },
            &mut rng,
        );
    }

    state.verify_gc_consistency();

    // Tear down all sessions one by one.
    while !state.sessions.is_empty() {
        apply_action(
            &mut state,
            &CapAction::TeardownSession { session_idx: 0 },
            &mut rng,
        );
        state.verify_gc_consistency();
    }
}

/// Fuzz: random interleaving of imports and exports.
#[test]
fn test_fuzz_captp_interleaved_import_export() {
    let mut rng = Rng::from_seed("fuzz_captp_interleaved");
    let mut state = CapState::new();

    // Create 3 sessions.
    for _ in 0..3 {
        apply_action(&mut state, &CapAction::CreateSession, &mut rng);
    }

    for _ in 0..300 {
        let action = generate_action(&mut rng, &state);
        apply_action(&mut state, &action, &mut rng);
        state.verify_gc_consistency();
    }
}

/// Test handoff certificate validation: invalid certificates must be rejected.
#[test]
fn test_fuzz_handoff_invalid_certificates() {
    let mut rng = Rng::from_seed("fuzz_handoff_invalid");

    let mut swiss_table = SwissTable::new();
    let introducer_pk = PublicKey(rng.gen_bytes());
    let trusted_federations: Vec<FederationId> = vec![FederationId(rng.gen_bytes())];

    // Generate random bogus certificates and presentations.
    for _ in 0..100 {
        let mut sig_bytes = [0u8; 64];
        for chunk in sig_bytes.chunks_exact_mut(8) {
            chunk.copy_from_slice(&rng.next_u64().to_le_bytes());
        }

        let cert = HandoffCertificate {
            introducer: FederationId(rng.gen_bytes()),
            introducer_signature: Signature(sig_bytes),
            target_federation: FederationId(rng.gen_bytes()),
            target_cell: CellId::from_bytes(rng.gen_bytes()),
            recipient_pk: rng.gen_bytes(),
            permissions: AuthRequired::None,
            allowed_effects: None,
            expires_at: Some(rng.gen_range(0, 1000)),
            max_uses: Some(1),
            nonce: rng.gen_bytes(),
            swiss: rng.gen_bytes(),
        };

        let mut recipient_sig_bytes = [0u8; 64];
        for chunk in recipient_sig_bytes.chunks_exact_mut(8) {
            chunk.copy_from_slice(&rng.next_u64().to_le_bytes());
        }

        let presentation = HandoffPresentation {
            certificate: cert,
            recipient_signature: Signature(recipient_sig_bytes),
        };

        // Validation should always fail for random garbage certificates.
        let result = validate_handoff(
            &presentation,
            &introducer_pk,
            &mut swiss_table,
            &trusted_federations,
            rng.gen_range(0, 500),
        );
        assert!(
            result.is_err(),
            "Random garbage certificate should not validate"
        );
    }
}

/// Test: valid operations always succeed (export then drop).
#[test]
fn test_captp_valid_operations_succeed() {
    let mut rng = Rng::from_seed("captp_valid_ops_succeed");
    let mut export_gc = ExportGcManager::new();

    for _ in 0..50 {
        let cell_id = CellId::from_bytes(rng.gen_bytes());
        let fed_id = FederationId(rng.gen_bytes());

        // Export.
        export_gc.record_export(cell_id, fed_id, 1);
        let entry = export_gc.get(&cell_id).unwrap();
        assert_eq!(entry.total_refs, 1, "After export, refs should be 1");

        // Drop.
        let result = export_gc.process_drop(cell_id, fed_id);
        assert_eq!(
            result,
            pyana_captp::DropResult::CanRevoke,
            "Drop after single export should yield CanRevoke"
        );
    }
}

/// Test: invalid operations always fail (double-drop, drop from wrong federation).
#[test]
fn test_captp_invalid_operations_fail() {
    let mut rng = Rng::from_seed("captp_invalid_ops_fail");
    let mut export_gc = ExportGcManager::new();

    let cell_id = CellId::from_bytes(rng.gen_bytes());
    let fed_a = FederationId(rng.gen_bytes());
    let fed_b = FederationId(rng.gen_bytes());

    // Export to fed_a.
    export_gc.record_export(cell_id, fed_a, 1);

    // Drop from wrong federation.
    let result = export_gc.process_drop(cell_id, fed_b);
    assert_eq!(
        result,
        pyana_captp::DropResult::Invalid,
        "Drop from wrong federation should be Invalid"
    );

    // Valid drop.
    let result = export_gc.process_drop(cell_id, fed_a);
    assert_eq!(result, pyana_captp::DropResult::CanRevoke);

    // Double-drop: cell no longer has entry (already at zero, was cleaned).
    let result = export_gc.process_drop(cell_id, fed_a);
    assert_eq!(
        result,
        pyana_captp::DropResult::Invalid,
        "Double-drop should be Invalid"
    );
}
