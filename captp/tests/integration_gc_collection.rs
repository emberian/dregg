//! Integration: distributed GC lifecycle — acquire, drop, reclaim, stale-ref fails.
//!
//! Covers:
//! - Full export → import → drop cycle across two sides
//! - gc_sweep removes zero-ref entries and the slot is gone
//! - Stale reference (enliven after GC sweep of swiss entry) fails
//! - Session-aware GC: wrong-session drop is rejected
//! - Multi-holder independence: only last holder triggers CanRevoke
//! - Import side: multiple local holders; DropMessage sent only on final release

use pyana_captp::{
    DropResult, ExportGcManager, FederationId, ImportGcManager, SwissTable,
};
use pyana_cell::AuthRequired;
use pyana_types::CellId;

fn fed(b: u8) -> FederationId {
    FederationId([b; 32])
}

fn cell(b: u8) -> CellId {
    CellId([b; 32])
}

// =============================================================================
// Full cycle: export → import → drop → GC sweep → stale-ref fails
// =============================================================================

#[test]
fn export_import_drop_sweep_stale_ref_fails() {
    // Seller (A) exports a cap to Buyer (B).
    let mut export_gc = ExportGcManager::new();
    let mut import_gc = ImportGcManager::new();
    let mut swiss_table = SwissTable::new();

    let cap = cell(0x42);
    let fed_a = fed(0xAA);
    let fed_b = fed(0xBB);

    // A: register in swiss table and GC.
    let swiss = swiss_table.export(cap, AuthRequired::Signature, 100, None);
    export_gc.record_export(cap, fed_b, 100);
    assert_eq!(export_gc.get(&cap).unwrap().total_refs, 1);

    // B: enliven and track import.
    let entry = swiss_table.enliven(&swiss, 100).unwrap();
    import_gc.record_import(fed_a, entry.cell_id);
    assert_eq!(import_gc.get(&fed_a, &cap).unwrap().local_refs, 1);

    // B: drop all local refs → DropMessage generated.
    let drop_msg = import_gc.local_ref_dropped(fed_a, cap);
    assert!(drop_msg.is_some());
    assert_eq!(drop_msg.unwrap().target_federation, fed_a);
    assert!(import_gc.is_empty());

    // A: process the drop → CanRevoke.
    let result = export_gc.process_drop(cap, fed_b);
    assert_eq!(result, DropResult::CanRevoke);
    assert_eq!(export_gc.get(&cap).unwrap().total_refs, 0);

    // A: GC sweep removes the zero-ref entry.
    let swept = export_gc.gc_sweep();
    assert!(swept.contains(&cap));
    assert!(export_gc.get(&cap).is_none());

    // A: revoke the swiss entry (cleanup on CanRevoke).
    assert!(swiss_table.revoke(&swiss));

    // Stale reference: B tries to use the same swiss number after revocation.
    let err = swiss_table.enliven(&swiss, 200).expect_err("stale ref must fail");
    assert_eq!(err, pyana_captp::EnlivenError::NotFound);
}

// =============================================================================
// Session-aware GC: wrong session drop is rejected
// =============================================================================

#[test]
fn session_aware_gc_wrong_session_rejected() {
    let mut export_gc = ExportGcManager::new();
    let cap = cell(0x99);
    let holder = fed(0xCC);

    export_gc.record_export_with_session(cap, holder, 100, 7);

    // Wrong session ID → rejected.
    let r = export_gc.process_drop_with_session(cap, holder, 42);
    assert_eq!(r, DropResult::Invalid);
    assert_eq!(export_gc.get(&cap).unwrap().total_refs, 1); // unchanged

    // Correct session → accepted.
    let r = export_gc.process_drop_with_session(cap, holder, 7);
    assert_eq!(r, DropResult::CanRevoke);
}

// =============================================================================
// Multi-holder: three federations, CanRevoke only on last drop
// =============================================================================

#[test]
fn multi_holder_last_drop_triggers_can_revoke() {
    let mut export_gc = ExportGcManager::new();
    let cap = cell(0x10);

    export_gc.record_export(cap, fed(0x01), 100);
    export_gc.record_export(cap, fed(0x02), 100);
    export_gc.record_export(cap, fed(0x03), 100);
    assert_eq!(export_gc.get(&cap).unwrap().total_refs, 3);

    assert_eq!(export_gc.process_drop(cap, fed(0x01)), DropResult::StillHeld);
    assert_eq!(export_gc.process_drop(cap, fed(0x02)), DropResult::StillHeld);
    assert_eq!(export_gc.process_drop(cap, fed(0x03)), DropResult::CanRevoke);

    // Drop from an already-dropped federation → Invalid.
    assert_eq!(export_gc.process_drop(cap, fed(0x01)), DropResult::Invalid);
}

// =============================================================================
// Import side: multiple local holders — DropMessage only on final release
// =============================================================================

#[test]
fn import_multiple_local_holders_drop_message_on_final() {
    let mut import_gc = ImportGcManager::new();
    let remote = fed(0xEE);
    let cap = cell(0x55);

    // Three local components hold a reference to the same import.
    import_gc.record_import(remote, cap);
    import_gc.record_import(remote, cap);
    import_gc.record_import(remote, cap);
    assert_eq!(import_gc.get(&remote, &cap).unwrap().local_refs, 3);

    // First two drops: no DropMessage (still locally referenced).
    assert!(import_gc.local_ref_dropped(remote, cap).is_none());
    assert!(import_gc.local_ref_dropped(remote, cap).is_none());
    assert_eq!(import_gc.get(&remote, &cap).unwrap().local_refs, 1);

    // Final drop: DropMessage is generated.
    let msg = import_gc.local_ref_dropped(remote, cap);
    assert!(msg.is_some());
    assert_eq!(msg.unwrap().cell_id, cap);
    assert!(import_gc.is_empty());
}

// =============================================================================
// Stale-export detection via stale_exports()
// =============================================================================

#[test]
fn stale_export_identified_after_idle_blocks() {
    let mut export_gc = ExportGcManager::new();

    let active = cell(0xA0);
    let idle = cell(0xA1);

    // Both exported at height 100.
    export_gc.record_export(active, fed(0x01), 100);
    export_gc.record_export(idle, fed(0x02), 100);

    // At height 1000, only the active cap was touched again (re-exported at 900).
    export_gc.record_export(active, fed(0x01), 900);

    // max_idle = 500 blocks, current = 1000:
    // active: last_activity=900, idle for 100 → NOT stale
    // idle: last_activity=100, idle for 900 → stale
    let stale = export_gc.stale_exports(500, 1000);
    assert_eq!(stale.len(), 1);
    assert!(stale.contains(&idle));
    assert!(!stale.contains(&active));
}

// =============================================================================
// GC sweep is idempotent (double-sweep safe)
// =============================================================================

#[test]
fn gc_sweep_idempotent() {
    let mut export_gc = ExportGcManager::new();
    let cap = cell(0xBB);

    export_gc.record_export(cap, fed(0x10), 1);
    export_gc.process_drop(cap, fed(0x10));

    let first = export_gc.gc_sweep();
    assert!(first.contains(&cap));

    let second = export_gc.gc_sweep();
    assert!(second.is_empty());
    assert!(export_gc.is_empty());
}
