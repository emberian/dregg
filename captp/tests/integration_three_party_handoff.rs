//! Integration: three-party handoff (A introduces B to C).
//!
//! Covers:
//! - Full signed-cert flow across distinct introducer / target federations
//! - Negative: forged introducer signature rejected
//! - Negative: wrong recipient (impostor) rejected
//! - Negative: untrusted introducer rejected
//! - Positive: cert round-tripped through compact string still validates
//! - GC integration: after handoff, import tracked and DropRef generated on release

use pyana_captp::{
    ExportGcManager, FederationId, HandoffCertificate, HandoffError, HandoffPresentation,
    ImportGcManager, SwissTable, validate_handoff,
};
use pyana_cell::AuthRequired;
use pyana_types::{CellId, generate_keypair};

fn fed(b: u8) -> FederationId {
    FederationId([b; 32])
}

fn cell(b: u8) -> CellId {
    CellId([b; 32])
}

// =============================================================================
// Happy-path: Alice introduces Bob to Carol's swiss table
// =============================================================================

#[test]
fn three_party_full_flow_alice_introduces_bob_to_carol() {
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);

    let (bob_sk, bob_pk) = generate_keypair();

    let carol_fed = fed(0xCA);
    let carol_cell = cell(0x42);

    // Carol pre-registers the swiss entry at her federation.
    let mut carol_swiss = SwissTable::new();
    let swiss = carol_swiss.export(carol_cell, AuthRequired::Signature, 100, None);

    // Alice mints a cert directing Bob at Carol's cell.
    let cert = HandoffCertificate::create(
        &alice_sk,
        alice_fed,
        carol_fed,
        carol_cell,
        bob_pk.0,
        AuthRequired::Signature,
        None,
        None,         // no expiry
        Some(3),      // up to 3 uses
        swiss,
    );

    // Introducer != target — the cross-federation property.
    assert_ne!(cert.introducer, cert.target_federation);

    // Bob signs a presentation proving he owns the named recipient key.
    let presentation = HandoffPresentation::create(cert.clone(), &bob_sk);

    // Carol validates and accepts.
    let known = vec![alice_fed];
    let acceptance = validate_handoff(&presentation, &alice_pk, &mut carol_swiss, &known, 150)
        .expect("valid three-party cert must be accepted");

    assert_eq!(acceptance.cell_id, carol_cell);
    assert_eq!(acceptance.permissions, AuthRequired::Signature);
    assert!(!acceptance.routing_token.iter().all(|&b| b == 0));
}

// =============================================================================
// Negative: forged introducer signature
// =============================================================================

#[test]
fn forged_introducer_signature_rejected() {
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);

    let (bob_sk, bob_pk) = generate_keypair();
    let carol_fed = fed(0xCA);
    let carol_cell = cell(0x42);

    let mut carol_swiss = SwissTable::new();
    let swiss = carol_swiss.export(carol_cell, AuthRequired::Signature, 100, None);

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

    // Bob presents the cert but Carol verifies with a *wrong* Alice key.
    let presentation = HandoffPresentation::create(cert, &bob_sk);

    let (_, wrong_pk) = generate_keypair();
    let known = vec![alice_fed];
    let err = validate_handoff(&presentation, &wrong_pk, &mut carol_swiss, &known, 150)
        .expect_err("forged introducer signature must be rejected");

    assert_eq!(err, HandoffError::InvalidIntroducerSignature);
}

// =============================================================================
// Negative: impostor (wrong recipient key) rejected
// =============================================================================

#[test]
fn wrong_recipient_rejected() {
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);

    let (_bob_sk, bob_pk) = generate_keypair();
    let carol_fed = fed(0xCA);
    let carol_cell = cell(0x42);

    let mut carol_swiss = SwissTable::new();
    let swiss = carol_swiss.export(carol_cell, AuthRequired::Signature, 100, None);

    // Cert names Bob as recipient.
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

    // Mallory intercepts and presents with her own key.
    let (mallory_sk, _) = generate_keypair();
    let forged_pres = HandoffPresentation::create(cert, &mallory_sk);

    let known = vec![alice_fed];
    let err = validate_handoff(&forged_pres, &alice_pk, &mut carol_swiss, &known, 150)
        .expect_err("impostor must be rejected");

    assert_eq!(err, HandoffError::InvalidRecipientSignature);
}

// =============================================================================
// Negative: untrusted introducer
// =============================================================================

#[test]
fn untrusted_introducer_rejected() {
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);

    let (bob_sk, bob_pk) = generate_keypair();
    let carol_fed = fed(0xCA);
    let carol_cell = cell(0x42);

    let mut carol_swiss = SwissTable::new();
    let swiss = carol_swiss.export(carol_cell, AuthRequired::Signature, 100, None);

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
    let presentation = HandoffPresentation::create(cert, &bob_sk);

    // Carol's known_federations is empty — Alice is not trusted.
    let known: Vec<FederationId> = vec![];
    let err = validate_handoff(&presentation, &alice_pk, &mut carol_swiss, &known, 150)
        .expect_err("untrusted introducer must be rejected");

    assert_eq!(err, HandoffError::UntrustedIntroducer);
}

// =============================================================================
// Positive: compact-string round-trip preserves validity
// =============================================================================

#[test]
fn cert_compact_string_roundtrip_still_validates() {
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);

    let (bob_sk, bob_pk) = generate_keypair();
    let carol_fed = fed(0xCA);
    let carol_cell = cell(0x42);

    let mut carol_swiss = SwissTable::new();
    let swiss = carol_swiss.export(carol_cell, AuthRequired::Signature, 100, None);

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

    // Simulate out-of-band transport: encode to compact string, then decode.
    let compact = cert.to_compact_string();
    assert!(compact.starts_with("pyana-handoff:"));
    let decoded_cert = HandoffCertificate::from_compact_string(&compact)
        .expect("compact string must deserialize");

    let presentation = HandoffPresentation::create(decoded_cert, &bob_sk);
    let known = vec![alice_fed];
    let acceptance = validate_handoff(&presentation, &alice_pk, &mut carol_swiss, &known, 200)
        .expect("cert after compact round-trip must still validate");

    assert_eq!(acceptance.cell_id, carol_cell);
}

// =============================================================================
// GC integration: handoff followed by import tracking → DropRef on release
// =============================================================================

#[test]
fn handoff_followed_by_gc_lifecycle() {
    let (alice_sk, alice_pk) = generate_keypair();
    let alice_fed = FederationId(alice_pk.0);

    let (bob_sk, bob_pk) = generate_keypair();
    let carol_fed = fed(0xCA);
    let carol_cell = cell(0x42);

    let mut carol_swiss = SwissTable::new();
    let swiss = carol_swiss.export(carol_cell, AuthRequired::Signature, 100, None);

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

    let presentation = HandoffPresentation::create(cert, &bob_sk);
    let known = vec![alice_fed];
    let acceptance = validate_handoff(&presentation, &alice_pk, &mut carol_swiss, &known, 150)
        .expect("handoff must succeed");

    // Bob now holds a reference to carol_cell@carol_fed.
    // Alice's export-GC records that carol_fed holds a ref.
    let mut alice_export_gc = ExportGcManager::new();
    alice_export_gc.record_export(carol_cell, carol_fed, 100);

    // Bob's import-GC records that he holds a ref from carol_fed.
    let mut bob_import_gc = ImportGcManager::new();
    bob_import_gc.record_import(carol_fed, acceptance.cell_id);

    assert_eq!(
        bob_import_gc.get(&carol_fed, &acceptance.cell_id).unwrap().local_refs,
        1
    );

    // Bob releases his reference → should generate a DropMessage to carol_fed.
    let drop_msg = bob_import_gc.local_ref_dropped(carol_fed, acceptance.cell_id);
    assert!(drop_msg.is_some(), "release must produce a DropMessage");
    assert_eq!(drop_msg.unwrap().target_federation, carol_fed);
    assert!(bob_import_gc.is_empty());

    // Carol's side processes the drop → CanRevoke.
    let drop_result = alice_export_gc.process_drop(carol_cell, carol_fed);
    assert_eq!(drop_result, pyana_captp::DropResult::CanRevoke);
}
