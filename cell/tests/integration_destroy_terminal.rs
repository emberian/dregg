//! Integration tests: cell destroy → terminal permanence.
//!
//! Exercises `Cell::destroy` directly (cell-layer, no executor) plus
//! `Ledger` to anchor the cell's identity:
//!
//! - `destroy` with a valid certificate → lifecycle == Destroyed.
//! - State-commitment changes after destroy (death_certificate_hash is bound).
//! - Subsequent `seal`, `unseal`, `archive`, and `destroy` calls are all
//!   rejected with `LifecycleTransitionError::Terminal`.
//! - `accepts_effects()` returns false for Destroyed.
//! - `certificate_hash()` binds every field of the DeathCertificate.

use pyana_cell::{
    Cell, CellId, Ledger,
    lifecycle::{
        ArchivalAttestation, CellLifecycle, DeathCertificate, DeathReason,
        LifecycleTransitionError,
    },
};

fn make_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    Cell::with_balance(pk, [0u8; 32], balance)
}

fn valid_cert(cell: &Cell) -> DeathCertificate {
    DeathCertificate {
        cell_id: cell.id(),
        last_receipt_hash: [0x01u8; 32],
        final_state_commitment: cell.state_commitment(),
        destroyed_at_height: 100,
        reason: DeathReason::Voluntary,
    }
}

// ---------------------------------------------------------------------------
// Test 1 (happy path): destroy with valid cert → Destroyed, effects rejected.
// ---------------------------------------------------------------------------

#[test]
fn destroy_transitions_to_destroyed_and_rejects_effects() {
    let mut cell = make_cell(1, 500);
    assert_eq!(cell.lifecycle, CellLifecycle::Live);
    assert!(cell.accepts_effects());

    let cert = valid_cert(&cell);
    let cert_hash = cert.certificate_hash();
    cell.destroy(&cert).expect("destroy must succeed on a Live cell");

    assert!(cell.lifecycle.is_destroyed(), "lifecycle must be Destroyed");
    assert!(!cell.accepts_effects(), "Destroyed cell must not accept effects");

    match &cell.lifecycle {
        CellLifecycle::Destroyed { death_certificate_hash, destroyed_at } => {
            assert_eq!(
                *death_certificate_hash, cert_hash,
                "death_certificate_hash must equal cert.certificate_hash()"
            );
            assert_eq!(*destroyed_at, 100, "destroyed_at must match the certificate height");
        }
        other => panic!("expected Destroyed, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Test 2: state_commitment changes after destroy (cert hash is bound).
// ---------------------------------------------------------------------------

#[test]
fn destroy_changes_state_commitment() {
    let mut cell = make_cell(2, 100);
    let commitment_before = cell.state_commitment();
    let cert = valid_cert(&cell);
    cell.destroy(&cert).unwrap();
    let commitment_after = cell.state_commitment();

    assert_ne!(
        commitment_before, commitment_after,
        "state_commitment must change when lifecycle transitions to Destroyed"
    );
}

// ---------------------------------------------------------------------------
// Test 3 (adversarial): Every subsequent transition after destroy returns Terminal.
// ---------------------------------------------------------------------------

#[test]
fn all_transitions_after_destroy_return_terminal() {
    let mut cell = make_cell(3, 200);
    let cert = valid_cert(&cell);
    cell.destroy(&cert).unwrap();
    assert!(cell.lifecycle.is_terminal());

    // Seal.
    assert_eq!(
        cell.seal([0xAA; 32], 200).unwrap_err(),
        LifecycleTransitionError::Terminal,
        "seal after destroy must return Terminal"
    );

    // Unseal.
    assert_eq!(
        cell.unseal().unwrap_err(),
        LifecycleTransitionError::NotSealed,
        "unseal on a destroyed cell returns NotSealed (it is not sealed)"
    );

    // Destroy again.
    let cert2 = DeathCertificate {
        cell_id: cell.id(),
        last_receipt_hash: [0x02u8; 32],
        final_state_commitment: cell.state_commitment(),
        destroyed_at_height: 200,
        reason: DeathReason::Forced,
    };
    assert_eq!(
        cell.destroy(&cert2).unwrap_err(),
        LifecycleTransitionError::Terminal,
        "second destroy must return Terminal"
    );

    // Archive.
    let attest = ArchivalAttestation {
        cell_id: cell.id(),
        archive_start_height: 0,
        archive_end_height: 50,
        archive_blob_hash: [1u8; 32],
        archive_terminal_commitment: [2u8; 32],
        archive_terminal_receipt_hash: [3u8; 32],
    };
    assert_eq!(
        cell.archive(&attest).unwrap_err(),
        LifecycleTransitionError::Terminal,
        "archive on destroyed cell must return Terminal"
    );
}

// ---------------------------------------------------------------------------
// Test 4 (adversarial): destroy with certificate for wrong cell_id rejected.
// ---------------------------------------------------------------------------

#[test]
fn destroy_certificate_wrong_cell_id_rejected() {
    let mut cell = make_cell(4, 100);
    let wrong_id = CellId::derive_raw(&[0xFFu8; 32], &[0u8; 32]);
    assert_ne!(wrong_id, cell.id());

    let bad_cert = DeathCertificate {
        cell_id: wrong_id,
        last_receipt_hash: [0u8; 32],
        final_state_commitment: [0u8; 32],
        destroyed_at_height: 1,
        reason: DeathReason::Voluntary,
    };
    assert_eq!(
        cell.destroy(&bad_cert).unwrap_err(),
        LifecycleTransitionError::CertificateMismatch,
        "destroy with wrong cell_id must return CertificateMismatch"
    );
    // Still Live.
    assert_eq!(cell.lifecycle, CellLifecycle::Live);
}

// ---------------------------------------------------------------------------
// Test 5: certificate_hash binds every field — any mutation changes the hash.
// ---------------------------------------------------------------------------

#[test]
fn death_certificate_hash_binds_all_fields() {
    let cell = make_cell(5, 0);
    let base = DeathCertificate {
        cell_id: cell.id(),
        last_receipt_hash: [1u8; 32],
        final_state_commitment: [2u8; 32],
        destroyed_at_height: 42,
        reason: DeathReason::Voluntary,
    };
    let base_hash = base.certificate_hash();

    let mut variant = base.clone();
    variant.last_receipt_hash = [9u8; 32];
    assert_ne!(variant.certificate_hash(), base_hash, "last_receipt_hash must bind");

    let mut variant = base.clone();
    variant.final_state_commitment = [9u8; 32];
    assert_ne!(variant.certificate_hash(), base_hash, "final_state_commitment must bind");

    let mut variant = base.clone();
    variant.destroyed_at_height = 43;
    assert_ne!(variant.certificate_hash(), base_hash, "destroyed_at_height must bind");

    let mut variant = base.clone();
    variant.reason = DeathReason::Forced;
    assert_ne!(variant.certificate_hash(), base_hash, "reason discriminant must bind");
}

// ---------------------------------------------------------------------------
// Test 6: Destroy via ledger delta round-trip — Ledger reflects Destroyed state.
// ---------------------------------------------------------------------------

#[test]
fn destroy_reflected_in_ledger_after_update_with() {
    let cell = make_cell(6, 300);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let cert = {
        let c = ledger.get(&cell_id).unwrap();
        valid_cert(c)
    };

    ledger
        .update_with(&cell_id, |c| {
            c.destroy(&cert).unwrap();
        })
        .expect("update_with must succeed");

    let cell = ledger.get(&cell_id).unwrap();
    assert!(cell.lifecycle.is_destroyed(), "ledger must reflect Destroyed after update_with");
    assert!(!cell.accepts_effects());
}
