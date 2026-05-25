//! Integration: swiss table issue → use → revoke → reject flow.
//!
//! Covers:
//! - Issue a cap, use it, revoke it, verify use fails post-revoke
//! - Attempt to delegate an already-revoked cap via handoff → swiss not found
//! - Use-count limit: at-limit cap cannot be re-used
//! - Revoked cap not found by peek-then-revoke (double-revoke semantics)
//! - Expired cap rejected even before revoke

use pyana_captp::{
    FederationId, HandoffCertificate, HandoffError, HandoffPresentation, SwissTable,
    validate_handoff,
};
use pyana_cell::AuthRequired;
use pyana_types::{CellId, generate_keypair};

fn cell(b: u8) -> CellId {
    CellId([b; 32])
}

// =============================================================================
// Issue → use → revoke → use fails
// =============================================================================

#[test]
fn issue_use_revoke_use_fails() {
    let mut table = SwissTable::new();
    let c = cell(0xAA);

    // Issue (unlimited uses, no expiry)
    let swiss = table.export(c, AuthRequired::Signature, 100, None);
    assert!(table.contains(&swiss));

    // Use: succeeds, increments use_count
    let entry = table.enliven(&swiss, 100).expect("first enliven must succeed");
    assert_eq!(entry.cell_id, c);
    assert_eq!(entry.use_count, 1);

    // Revoke
    assert!(table.revoke(&swiss));
    assert!(!table.contains(&swiss));

    // Use after revoke: NotFound
    let err = table.enliven(&swiss, 101).expect_err("must fail after revoke");
    assert_eq!(err, pyana_captp::EnlivenError::NotFound);

    // Double-revoke returns false (idempotent)
    assert!(!table.revoke(&swiss));
}

// =============================================================================
// Attempt to delegate an already-revoked cap → SwissNotFound at target
// =============================================================================

#[test]
fn delegate_revoked_cap_rejected_at_target() {
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);

    let (bob_sk, bob_pk) = generate_keypair();
    let carol_fed = FederationId([0xCA; 32]);
    let carol_cell = cell(0xCA);

    // Carol pre-registers a swiss entry.
    let mut carol_swiss = SwissTable::new();
    let swiss = carol_swiss.export(carol_cell, AuthRequired::Signature, 100, None);

    // Alice mints the cert referencing that swiss number.
    let cert = HandoffCertificate::create(
        &alice_sk,
        alice_fed,
        carol_fed,
        carol_cell,
        bob_pk.0,
        AuthRequired::Signature,
        None,
        None,
        None,
        swiss,
    );
    let compact = cert.to_compact_string();

    // Carol revokes the swiss entry before Bob presents.
    assert!(carol_swiss.revoke(&swiss));

    // Bob decodes the cert and presents — should be rejected (swiss not in table).
    let decoded = HandoffCertificate::from_compact_string(&compact).unwrap();
    let presentation = HandoffPresentation::create(decoded, &bob_sk);
    let known = vec![alice_fed];
    let err = validate_handoff(&presentation, &alice_pk, &mut carol_swiss, &known, 200)
        .expect_err("revoked swiss must be rejected");

    assert_eq!(err, HandoffError::SwissNotFound);
}

// =============================================================================
// Use-count exhausted: at limit, next use fails
// =============================================================================

#[test]
fn max_uses_boundary() {
    let mut table = SwissTable::new();
    let c = cell(0x11);

    // max_uses = 2
    let swiss =
        table.export_with_options(c, AuthRequired::Signature, 10, None, None, Some(2));

    // First use: OK
    let e = table.enliven(&swiss, 100).unwrap();
    assert_eq!(e.use_count, 1);

    // Second use: OK (at limit)
    let e = table.enliven(&swiss, 101).unwrap();
    assert_eq!(e.use_count, 2);

    // Third use: ExhaustedUses (over limit)
    let err = table.enliven(&swiss, 102).expect_err("must fail at exhaustion");
    assert_eq!(err, pyana_captp::EnlivenError::ExhaustedUses);

    // Entry is still in the table (not automatically removed); explicit revoke removes it.
    assert!(table.contains(&swiss));
    table.revoke(&swiss);
    assert!(!table.contains(&swiss));
}

// =============================================================================
// Expired cap rejected before explicit revoke
// =============================================================================

#[test]
fn expired_cap_rejected_then_revoke_cleans_up() {
    let mut table = SwissTable::new();
    let c = cell(0x22);

    // expires_at = 200
    let swiss = table.export(c, AuthRequired::Signature, 100, Some(200));

    // At height 200 (boundary): still valid.
    let e = table.enliven(&swiss, 200).unwrap();
    assert_eq!(e.use_count, 1);

    // At height 201: expired.
    let err = table.enliven(&swiss, 201).expect_err("must be expired");
    assert_eq!(err, pyana_captp::EnlivenError::Expired);

    // Entry is still present (expiry doesn't auto-remove).
    assert!(table.contains(&swiss));

    // Explicit revoke removes it.
    table.revoke(&swiss);
    assert!(!table.contains(&swiss));
    assert!(table.is_empty());
}

// =============================================================================
// Effect-mask attenuation survives revocation
// =============================================================================

#[test]
fn attenuated_cap_revoke_clears_mask() {
    let mut table = SwissTable::new();
    let c = cell(0x33);

    let mask: pyana_cell::EffectMask = 0b0000_0110;
    let swiss = table.export_with_options(c, AuthRequired::None, 10, None, Some(mask), None);

    let e = table.enliven(&swiss, 10).unwrap();
    assert_eq!(e.allowed_effects, Some(mask));

    table.revoke(&swiss);
    assert!(table.enliven(&swiss, 11).is_err());
}

// =============================================================================
// URI round-trip: exported cap survives pyana:// serialization
// =============================================================================

#[test]
fn exported_cap_uri_round_trip_then_revoke() {
    use pyana_captp::PyanaUri;

    let mut table = SwissTable::new();
    let c = cell(0x55);
    let fed_bytes = [0xFE; 32];

    let swiss = table.export(c, AuthRequired::Signature, 1, None);
    let uri = table.make_uri(fed_bytes, &swiss).unwrap();

    // Round-trip through string.
    let uri_str = uri.to_uri_string();
    let parsed: PyanaUri = PyanaUri::parse(&uri_str).unwrap();
    assert_eq!(parsed.swiss, swiss);

    // Enliven using the parsed swiss number.
    let e = table.enliven(&parsed.swiss, 1).unwrap();
    assert_eq!(e.cell_id, c);

    // Revoke and confirm stale URI reference fails.
    table.revoke(&parsed.swiss);
    assert!(table.enliven(&parsed.swiss, 2).is_err());
}
