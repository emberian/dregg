//! End-to-end credential-lifecycle tests for `starbridge-identity`.
//!
//! These tests exercise the four canonical credential operations through
//! the `starbridge-identity` turn-builders, against the underlying
//! `pyana-credentials` primitives. The crypto heavy-lifting lives in the
//! credentials crate; these tests verify the userspace composition.
//!
//! Coverage:
//!
//! 1. `roundtrip_issue_present_verify` — happy-path: issue a credential,
//!    present it with selective disclosure and a predicate, verify
//!    accept.
//! 2. `revoked_credential_rejected` — adversarial: a revoked credential's
//!    presentation is rejected at verify.
//! 3. `forged_claims_rejected_at_issue` — adversarial: an issuer cannot
//!    bind an attribute that isn't in the credential's schema.
//! 4. `multi_show_unlinkability` — privacy: same credential presented
//!    twice anonymously produces different revealed-facts commitments
//!    (per `BOUNDARIES.md` §2.11).
//! 5. `verify_action_records_accept_event` — userspace composition: the
//!    `build_verify_presentation_action` builder runs verify and emits
//!    an `presentation-accepted` event on accept.
//! 6. `verify_action_records_reject_event` — userspace composition: a
//!    forged predicate is rejected and the builder emits a
//!    `presentation-rejected` event.

use pyana_app_framework::{AgentCipherclerk, AppCipherclerk, CellId, Effect};
use pyana_token::AuthRequest;

use starbridge_identity::{
    AttrValue, CredentialAttributes, IssuerKeys, Predicate, PredicateRequest, PresentationOptions,
    RevocationRegistry, VerificationOptions, build_issue_credential_action,
    build_present_credential_action, build_revoke_credential_action,
    build_verify_presentation_action, issue, kyc_schema, present, present_anonymous, revoke,
    schema_commitment, verify,
};

fn fixture_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
}

fn fixture_cell(seed: u8) -> CellId {
    CellId::from_bytes([seed; 32])
}

fn fixture_issuer() -> IssuerKeys {
    IssuerKeys::new(
        [100u8; 32],
        [50u8; 32],
        b"starbridge-identity-test",
        "starbridge-identity",
    )
}

fn fixture_request() -> AuthRequest {
    AuthRequest {
        action: Some("read".into()),
        app_id: Some("starbridge-identity-test".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    }
}

fn fixture_attributes() -> CredentialAttributes {
    CredentialAttributes::new()
        .with("given_name", AttrValue::Text("Alice".into()))
        .with("family_name", AttrValue::Text("Doe".into()))
        .with("dob", AttrValue::Date(10_000))
        .with("verification_level", AttrValue::Integer(2))
}

// =============================================================================
// 1. Round-trip: issue → present → verify (predicate-based selective
//    disclosure).
// =============================================================================

#[test]
fn roundtrip_issue_present_verify() {
    let issuer = fixture_issuer();
    let schema = kyc_schema();
    let attrs = fixture_attributes();
    let holder = [9u8; 32];

    // Issue a credential.
    let credential =
        issue(&issuer, &schema, holder, attrs, 1_700_000_000, None).expect("issuance must succeed");

    // Userspace anchor: emit the issuance action on the issuer cell.
    let cipherclerk = fixture_cipherclerk();
    let issuer_cell = fixture_cell(1);
    let action =
        build_issue_credential_action(&cipherclerk, issuer_cell, &credential, 1, [0u8; 32]);
    assert_eq!(action.effects.len(), 3, "expected 3 effects");
    // First effect bumps the issuance counter (slot 3).
    match &action.effects[0] {
        Effect::SetField { index, .. } => assert_eq!(*index, 3),
        other => panic!("expected SetField, got {other:?}"),
    }

    // Present with selective disclosure of `verification_level` and a
    // predicate proof that `verification_level >= 1`.
    let options = PresentationOptions::new()
        .disclose("verification_level")
        .predicate(PredicateRequest::new(
            "verification_level",
            Predicate::Gte(1),
        ));
    let presentation =
        present(&credential, &fixture_request(), &options).expect("presentation must succeed");

    // Userspace anchor: holder records the presentation on their cell.
    let holder_cell = fixture_cell(9);
    let pres_action = build_present_credential_action(&cipherclerk, holder_cell, &presentation);
    assert_eq!(pres_action.effects.len(), 1);

    // Verify the presentation against the verifier's expectations.
    let verify_opts = VerificationOptions {
        expected_schema: Some(schema),
        expected_disclosure: vec!["verification_level".into()],
        expected_predicates: vec![PredicateRequest::new(
            "verification_level",
            Predicate::Gte(1),
        )],
        ..Default::default()
    };
    let verified = verify(&presentation, &verify_opts).expect("verification must succeed");
    assert_eq!(verified.disclosed.len(), 1);
    assert_eq!(verified.disclosed[0].0, "verification_level");
}

// =============================================================================
// 2. Adversarial: present a revoked credential → verify rejects.
// =============================================================================

#[test]
fn revoked_credential_rejected() {
    let issuer = fixture_issuer();
    let schema = kyc_schema();
    let credential = issue(
        &issuer,
        &schema,
        [9u8; 32],
        fixture_attributes(),
        1_700_000_000,
        None,
    )
    .unwrap();

    // Revoke the credential.
    let registry = RevocationRegistry::new();
    let revocation_proof = revoke(&registry, &credential);
    assert!(revocation_proof.revoked, "credential must be revoked");

    // Userspace anchor: record revocation on the issuer cell.
    let cipherclerk = fixture_cipherclerk();
    let issuer_cell = fixture_cell(1);
    let rev_action =
        build_revoke_credential_action(&cipherclerk, issuer_cell, credential.id(), registry.root());
    assert_eq!(rev_action.effects.len(), 2);

    // Holder presents the revoked credential.
    let presentation = present(&credential, &fixture_request(), &PresentationOptions::new())
        .expect("presentation must succeed (the holder doesn't yet know it's revoked)");

    // Verifier supplies the non-revocation proof from the registry —
    // verification must reject.
    let verify_opts = VerificationOptions {
        revocation: Some(revocation_proof),
        ..Default::default()
    };
    let result = verify(&presentation, &verify_opts);
    assert!(
        result.is_err(),
        "verification of revoked credential must fail; got {result:?}"
    );

    // The verifier turn-builder records the rejection on the verifier cell.
    let verifier_cell = fixture_cell(2);
    let action =
        build_verify_presentation_action(&cipherclerk, verifier_cell, &presentation, &verify_opts);
    match &action.effects[0] {
        Effect::EmitEvent { event, .. } => {
            // Event topic is "presentation-rejected" — encoded as a symbol,
            // so we cannot match the string directly. We do check that the
            // accept flag is false (third field = 0).
            assert_eq!(event.data.len(), 3, "expected three event fields");
            assert_eq!(event.data[1][31], 0, "accept flag must be zero on reject");
        }
        other => panic!("expected EmitEvent, got {other:?}"),
    }
}

// =============================================================================
// 3. Adversarial: an issuer cannot bind an attribute that isn't in the
//    schema. The macaroon signature backs the binding; the schema check
//    is the first line of defense.
// =============================================================================

#[test]
fn forged_claims_rejected_at_issue() {
    let issuer = fixture_issuer();
    let schema = kyc_schema();
    let attrs = CredentialAttributes::new()
        .with("given_name", AttrValue::Text("Eve".into()))
        // "secret_admin_role" is not in the kyc schema — issuance must reject.
        .with("secret_admin_role", AttrValue::Text("root".into()));

    let result = issue(&issuer, &schema, [9u8; 32], attrs, 1_700_000_000, None);
    assert!(
        result.is_err(),
        "forged attribute outside schema must be rejected at issuance"
    );
}

// =============================================================================
// 4. Privacy: multi-show unlinkability (BOUNDARIES.md §2.11).
// =============================================================================
//
// Same credential presented twice in anonymous mode must produce different
// revealed-facts commitments (modulo no revealed attributes). The
// underlying mechanism is the per-presentation `presentation_randomness`
// in the bridge's `BridgePresentationProof`; the credentials crate
// exposes this as `present_anonymous`.

#[test]
fn multi_show_unlinkability() {
    let issuer = fixture_issuer();
    let schema = kyc_schema();
    let credential = issue(
        &issuer,
        &schema,
        [9u8; 32],
        fixture_attributes(),
        1_700_000_000,
        None,
    )
    .unwrap();

    // Two anonymous presentations of the same credential, with the same
    // disclosure set. The disclosed `verification_level` is the same in
    // both, but the bridge's nullifier / blinded-leaf must differ.
    let options = PresentationOptions::new().disclose("verification_level");

    let p1 = present_anonymous(&credential, &fixture_request(), &options)
        .expect("anonymous presentation 1 must succeed");
    let p2 = present_anonymous(&credential, &fixture_request(), &options)
        .expect("anonymous presentation 2 must succeed");

    // The disclosed values must be identical (the user revealed the same
    // attribute set both times) — this is the comparator we're proving
    // un-linkability against.
    assert_eq!(p1.disclosed, p2.disclosed);

    // The presentation's composition commitment binds the
    // per-presentation randomness (via `compute_presentation_tag`); two
    // anonymous shows of the same credential must produce different
    // composition commitments. This is the BOUNDARIES.md §2.11
    // "multi-show unlinkability" surface — an observer cannot link the
    // two presentations through the proof material.
    //
    // The composition_commitment is a WideHash; we extract its four
    // BabyBear limbs and compare.
    let c1 = p1.proof.composition_commitment.as_slice();
    let c2 = p2.proof.composition_commitment.as_slice();
    assert_ne!(
        c1, c2,
        "multi-show unlinkability requires fresh composition commitment per presentation"
    );
}

// =============================================================================
// 5. Userspace composition: verify-action emits an "accepted" event when
//    verification succeeds.
// =============================================================================

#[test]
fn verify_action_records_accept_event() {
    let issuer = fixture_issuer();
    let schema = kyc_schema();
    let credential = issue(
        &issuer,
        &schema,
        [9u8; 32],
        fixture_attributes(),
        1_700_000_000,
        None,
    )
    .unwrap();

    let presentation = present(
        &credential,
        &fixture_request(),
        &PresentationOptions::new().disclose("verification_level"),
    )
    .unwrap();

    let verify_opts = VerificationOptions {
        expected_schema: Some(schema),
        expected_disclosure: vec!["verification_level".into()],
        ..Default::default()
    };
    let cipherclerk = fixture_cipherclerk();
    let action = build_verify_presentation_action(
        &cipherclerk,
        fixture_cell(2),
        &presentation,
        &verify_opts,
    );
    match &action.effects[0] {
        Effect::EmitEvent { event, .. } => {
            assert_eq!(event.data.len(), 3);
            assert_eq!(event.data[1][31], 1, "accept flag must be 1 on success");
            // Predicate count is zero (no predicate requests).
            assert_eq!(event.data[2][31], 0);
        }
        other => panic!("expected EmitEvent, got {other:?}"),
    }
}

// =============================================================================
// 6. Userspace composition: verify-action emits a "rejected" event when
//    the verifier asks for a predicate that wasn't proven.
// =============================================================================

#[test]
fn verify_action_records_reject_event() {
    let issuer = fixture_issuer();
    let schema = kyc_schema();
    let credential = issue(
        &issuer,
        &schema,
        [9u8; 32],
        fixture_attributes(),
        1_700_000_000,
        None,
    )
    .unwrap();

    // Holder presents with no predicates.
    let presentation =
        present(&credential, &fixture_request(), &PresentationOptions::new()).unwrap();

    // Verifier asks for a predicate that the holder didn't prove.
    let verify_opts = VerificationOptions {
        expected_predicates: vec![PredicateRequest::new(
            "verification_level",
            Predicate::Gte(99),
        )],
        ..Default::default()
    };
    let cipherclerk = fixture_cipherclerk();
    let action = build_verify_presentation_action(
        &cipherclerk,
        fixture_cell(2),
        &presentation,
        &verify_opts,
    );
    match &action.effects[0] {
        Effect::EmitEvent { event, .. } => {
            assert_eq!(event.data[1][31], 0, "accept flag must be zero on reject");
        }
        other => panic!("expected EmitEvent, got {other:?}"),
    }
}

// =============================================================================
// 7. Schema commitment binds the issuer cell to its schema.
// =============================================================================

#[test]
fn schema_commitment_distinguishes_schemas() {
    let kyc = schema_commitment(&kyc_schema());
    let gov_id = schema_commitment(&starbridge_identity::gov_id_schema());
    let employment = schema_commitment(&starbridge_identity::employment_schema());
    assert_ne!(kyc, gov_id);
    assert_ne!(kyc, employment);
    assert_ne!(gov_id, employment);
}
