//! End-to-end integration test: issue → present → verify → revoke.
//!
//! Exercises the four canonical credential operations against the
//! bridge-backed presentation pipeline. Uses the `prove_local_constraint_check_only`
//! path (the fast-but-not-cryptographic verification mode) so the test
//! completes in ~1s instead of ~30s. The cryptographic-quality path is
//! identical apart from the `prove()` call; see `bridge/src/tests.rs`
//! for the end-to-end STARK timings.

use pyana_credentials::{
    AttrValue, CredentialAttributes, CredentialSchema, IssuerKeys, Predicate, PredicateRequest,
    PresentationOptions, RevocationRegistry, VerificationOptions, issue, present, revoke, verify,
};
use pyana_token::AuthRequest;

fn fixture_issuer() -> IssuerKeys {
    IssuerKeys::new(
        [42u8; 32],
        [7u8; 32],
        b"test-issuer-kid",
        "credentials-test",
    )
}

fn fixture_schema() -> CredentialSchema {
    CredentialSchema::new(
        "test-schema-v1",
        vec!["age".into(), "country".into(), "kyc_level".into()],
    )
}

fn fixture_attributes() -> CredentialAttributes {
    CredentialAttributes::new()
        .with("age", AttrValue::Integer(25))
        .with("country", AttrValue::Text("US".into()))
        .with("kyc_level", AttrValue::Integer(2))
}

#[test]
fn issue_present_verify_roundtrip() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attributes();
    let holder = [9u8; 32];

    let cred =
        issue(&issuer, &schema, holder, attrs, 1_700_000_000, None).expect("issuance must succeed");

    // The credential token round-trips through the macaroon encoding.
    let token = cred.token().expect("token reconstruction must succeed");
    assert_eq!(
        token.verify(&AuthRequest::default()).err().is_none(),
        true,
        "root token must verify against default request"
    );

    // Present with selective disclosure of `country`.
    let options = PresentationOptions::new().disclose("country");
    let request = AuthRequest {
        action: Some("read".into()),
        app_id: Some("test-app".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    };
    let presentation = present(&cred, &request, &options).expect("presentation must succeed");

    // Verify.
    let verify_options = VerificationOptions {
        expected_schema: Some(schema.clone()),
        expected_disclosure: vec!["country".into()],
        ..Default::default()
    };
    let verified = verify(&presentation, &verify_options).expect("verification must succeed");
    assert_eq!(verified.disclosed.len(), 1);
    assert_eq!(verified.disclosed[0].0, "country");
    match &verified.disclosed[0].1 {
        AttrValue::Text(s) => assert_eq!(s, "US"),
        other => panic!("expected Text, got {other:?}"),
    }
}

#[test]
fn unknown_attribute_rejected_at_issue() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = CredentialAttributes::new().with("not_in_schema", AttrValue::Integer(1));
    let holder = [9u8; 32];

    let result = issue(&issuer, &schema, holder, attrs, 1_700_000_000, None);
    assert!(result.is_err(), "unknown attribute must be rejected");
}

#[test]
fn revocation_marks_credential_revoked() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attributes();
    let holder = [9u8; 32];

    let cred = issue(&issuer, &schema, holder, attrs, 1_700_000_000, None).unwrap();

    let registry = RevocationRegistry::new();
    assert!(!registry.is_revoked(&cred.id()));

    let proof = revoke(&registry, &cred);
    assert!(proof.revoked, "post-revoke proof must say revoked");
    assert!(registry.is_revoked(&cred.id()));
}

#[test]
fn verify_rejects_revoked_presentation() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attributes();
    let holder = [9u8; 32];

    let cred = issue(&issuer, &schema, holder, attrs, 1_700_000_000, None).unwrap();
    let registry = RevocationRegistry::new();
    let revocation_proof = revoke(&registry, &cred);

    let options = PresentationOptions::new();
    let request = AuthRequest {
        action: Some("read".into()),
        app_id: Some("test-app".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    };
    let presentation = present(&cred, &request, &options).expect("present must succeed");

    let verify_options = VerificationOptions {
        revocation: Some(revocation_proof),
        ..Default::default()
    };
    let result = verify(&presentation, &verify_options);
    assert!(
        result.is_err(),
        "verification of revoked credential must fail"
    );
}

#[test]
fn predicate_request_attaches_predicate_proof() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attributes();
    let holder = [9u8; 32];

    let cred = issue(&issuer, &schema, holder, attrs, 1_700_000_000, None).unwrap();

    // Prove age >= 18 without revealing age.
    let options =
        PresentationOptions::new().predicate(PredicateRequest::new("age", Predicate::Gte(18)));
    let request = AuthRequest {
        action: Some("read".into()),
        app_id: Some("test-app".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    };
    let presentation = present(&cred, &request, &options).expect("present must succeed");

    assert_eq!(presentation.predicate_proofs.len(), 1);
    assert_eq!(presentation.predicate_proofs[0].attribute, "age");

    // Verifier asks for an `age >= 18` predicate proof.
    let verify_options = VerificationOptions {
        expected_predicates: vec![PredicateRequest::new("age", Predicate::Gte(18))],
        ..Default::default()
    };
    verify(&presentation, &verify_options).expect("verification must succeed");
}

#[test]
fn missing_expected_disclosure_rejected() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attributes();
    let holder = [9u8; 32];

    let cred = issue(&issuer, &schema, holder, attrs, 1_700_000_000, None).unwrap();
    let options = PresentationOptions::new(); // disclose nothing
    let request = AuthRequest {
        action: Some("read".into()),
        app_id: Some("test-app".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    };
    let presentation = present(&cred, &request, &options).unwrap();

    let verify_options = VerificationOptions {
        expected_disclosure: vec!["country".into()],
        ..Default::default()
    };
    let result = verify(&presentation, &verify_options);
    assert!(result.is_err(), "missing disclosure must be rejected");
}

#[test]
fn missing_predicate_rejected() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let attrs = fixture_attributes();
    let holder = [9u8; 32];

    let cred = issue(&issuer, &schema, holder, attrs, 1_700_000_000, None).unwrap();
    let options = PresentationOptions::new();
    let request = AuthRequest {
        action: Some("read".into()),
        app_id: Some("test-app".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    };
    let presentation = present(&cred, &request, &options).unwrap();

    let verify_options = VerificationOptions {
        expected_predicates: vec![PredicateRequest::new("age", Predicate::Gte(18))],
        ..Default::default()
    };
    let result = verify(&presentation, &verify_options);
    assert!(result.is_err(), "missing predicate must be rejected");
}
