//! Adversarial tests for the credential anonymity-soundness fixes.
//!
//! These are FAIL-before / PASS-after tests for the four holes a prior
//! audit found in `credentials/src/{presentation,verification}.rs`:
//!
//! (a) `verify_anonymous` must REJECT non-cryptographic `LocalOnly` proofs.
//! (b) Predicate proofs must be bound cryptographically to the proven
//!     statement, not matched by attribute NAME only.
//! (c) Two anonymous presentations of the same credential must be
//!     unlinkable (different `blinded_leaf` public inputs).
//! (d) A revoked credential must be rejected by a real non-membership
//!     check (not a self-asserted `revoked` boolean).

use dregg_credentials::{
    AttrValue, CredentialAttributes, CredentialSchema, IssuerKeys, Predicate, PredicateRequest,
    PresentationOptions, RevocationRegistry, VerificationOptions, issue, present,
    present_anonymous, revoke, verify, verify_anonymous,
};
use dregg_token::AuthRequest;

// ── fixtures ─────────────────────────────────────────────────────────────────

fn fixture_issuer() -> IssuerKeys {
    IssuerKeys::new(
        [11u8; 32],
        [
            33, 181, 62, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0,
        ],
        b"anonymity-soundness-kid",
        "anonymity-soundness-issuer",
    )
}

fn fixture_schema() -> CredentialSchema {
    CredentialSchema::new(
        "employee-v1",
        vec![
            "age".into(),
            "department".into(),
            "clearance_level".into(),
            "active".into(),
        ],
    )
}

fn fixture_attrs() -> CredentialAttributes {
    CredentialAttributes::new()
        .with("age", AttrValue::Integer(32))
        .with("department", AttrValue::Text("Engineering".into()))
        .with("clearance_level", AttrValue::Integer(3))
        .with("active", AttrValue::Bool(true))
}

fn fixture_request() -> AuthRequest {
    AuthRequest {
        action: Some("api:read".into()),
        app_id: Some("employee-portal".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    }
}

fn holder() -> [u8; 32] {
    [77u8; 32]
}

/// Extract the issuer-membership `blinded_leaf` public input (pi[0]) from
/// a real STARK presentation proof. Two presentations of the same
/// credential must produce different values for unlinkability.
fn blinded_leaf(p: &dregg_credentials::Presentation) -> u32 {
    let real = p
        .proof
        .real_stark_proof
        .as_ref()
        .expect("anonymous presentation must carry a real STARK proof");
    real.issuer_membership_stark_proof.public_inputs[0]
}

// ── (a) LocalOnly rejected for anonymous verification ─────────────────────────

#[test]
fn local_only_proof_rejected_by_verify_anonymous() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();

    // A NON-anonymous presentation uses the fast `prove_local_constraint_check_only`
    // path → `LocalOnly` verification (no cryptographic backing, no blinded leaf).
    let opts = PresentationOptions::new().disclose("active");
    let local_only = present(&cred, &fixture_request(), &opts).unwrap();
    assert!(
        !local_only.anonymous,
        "non-anonymous present() must not be marked anonymous"
    );

    // Asking for an anonymous verification of a LocalOnly proof must FAIL:
    // the unlinkability guarantee was never cryptographically proven.
    let verify_opts = VerificationOptions {
        require_anonymous: true,
        ..Default::default()
    };
    let result = verify_anonymous(&local_only, &verify_opts);
    assert!(
        result.is_err(),
        "verify_anonymous must reject a non-cryptographic LocalOnly proof"
    );
    match result.unwrap_err() {
        dregg_credentials::VerificationError::AnonymityMismatch
        | dregg_credentials::VerificationError::LocalOnlyRejected => {}
        other => panic!("expected LocalOnlyRejected/AnonymityMismatch, got {other:?}"),
    }
}

#[test]
fn real_anonymous_proof_accepted_by_verify_anonymous() {
    // Positive control: the genuine ring-blinded anonymous path passes.
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();

    let opts = PresentationOptions::new().disclose("active");
    let p = present_anonymous(&cred, &fixture_request(), &opts).unwrap();
    assert!(p.anonymous);

    let verify_opts = VerificationOptions {
        require_anonymous: true,
        ..Default::default()
    };
    verify_anonymous(&p, &verify_opts).expect("real anonymous proof must verify");
}

// ── (b) name-only predicate spoof rejected ────────────────────────────────────

#[test]
fn name_only_predicate_spoof_rejected() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();

    // Holder proves a WEAK statement about `age` (age >= 1, trivially true)
    // but the verifier requires `age >= 18`. With name-only matching this
    // would have passed (attribute "age" is present); with cryptographic
    // binding the proven statement (Gte(1)) ≠ requested (Gte(18)) → reject.
    let opts =
        PresentationOptions::new().predicate(PredicateRequest::new("age", Predicate::Gte(1)));
    let presentation = present(&cred, &fixture_request(), &opts).unwrap();
    assert_eq!(presentation.predicate_proofs.len(), 1);
    assert_eq!(presentation.predicate_proofs[0].attribute, "age");

    let verify_opts = VerificationOptions {
        expected_predicates: vec![PredicateRequest::new("age", Predicate::Gte(18))],
        ..Default::default()
    };
    let result = verify(&presentation, &verify_opts);
    assert!(
        result.is_err(),
        "a predicate proof for a different statement must be rejected, not matched by name"
    );
    match result.unwrap_err() {
        dregg_credentials::VerificationError::PredicateMismatch { attribute } => {
            assert_eq!(attribute, "age");
        }
        other => panic!("expected PredicateMismatch(age), got {other:?}"),
    }
}

#[test]
fn relabelled_predicate_proof_rejected() {
    // Stronger spoof: take a genuine proof generated for `clearance_level`
    // and relabel its NamedPredicateProof.attribute to "age". The verifier
    // asks for `age >= 18`. Name-only matching would accept (the relabelled
    // attribute is "age"); cryptographic binding rejects because the proven
    // statement is Gte(1) (clearance proof) ≠ the requested Gte(18), and the
    // STARK is bound to clearance_level's fact commitment, not age's.
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();

    let opts = PresentationOptions::new()
        .predicate(PredicateRequest::new("clearance_level", Predicate::Gte(1)));
    let mut presentation = present(&cred, &fixture_request(), &opts).unwrap();

    // Relabel the attribute name to "age" — a pure-string forgery.
    presentation.predicate_proofs[0].attribute = "age".to_string();

    let verify_opts = VerificationOptions {
        expected_predicates: vec![PredicateRequest::new("age", Predicate::Gte(18))],
        ..Default::default()
    };
    let result = verify(&presentation, &verify_opts);
    assert!(
        result.is_err(),
        "a relabelled predicate proof must be rejected by cryptographic binding"
    );
}

#[test]
fn matching_predicate_proof_accepted() {
    // Positive control: a genuine `age >= 18` proof for the matching request
    // verifies cryptographically.
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();

    let opts =
        PresentationOptions::new().predicate(PredicateRequest::new("age", Predicate::Gte(18)));
    let presentation = present(&cred, &fixture_request(), &opts).unwrap();

    let verify_opts = VerificationOptions {
        expected_predicates: vec![PredicateRequest::new("age", Predicate::Gte(18))],
        ..Default::default()
    };
    verify(&presentation, &verify_opts).expect("genuine matching predicate proof must verify");
}

// ── (c) two anonymous presentations are unlinkable ────────────────────────────

#[test]
fn two_anonymous_presentations_are_unlinkable() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();

    let opts = PresentationOptions::new().disclose("active");
    let p1 = present_anonymous(&cred, &fixture_request(), &opts).unwrap();
    let p2 = present_anonymous(&cred, &fixture_request(), &opts).unwrap();

    let leaf1 = blinded_leaf(&p1);
    let leaf2 = blinded_leaf(&p2);

    assert_ne!(
        leaf1, leaf2,
        "two anonymous shows of the SAME credential must produce different blinded leaves (unlinkable)"
    );

    // Both must still verify as anonymous.
    let verify_opts = VerificationOptions {
        require_anonymous: true,
        ..Default::default()
    };
    verify_anonymous(&p1, &verify_opts).expect("first anonymous show must verify");
    verify_anonymous(&p2, &verify_opts).expect("second anonymous show must verify");
}

// ── (d) revoked credential rejected by a real non-membership check ────────────

#[test]
fn revoked_credential_rejected_by_real_non_membership() {
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();
    let registry = RevocationRegistry::new();

    let presentation = present(&cred, &fixture_request(), &PresentationOptions::new()).unwrap();

    // Before revocation: a non-revocation proof must let verification pass,
    // anchored against the registry's published root.
    let pre_proof = registry.prove_non_revocation(cred.id());
    let pre_opts = VerificationOptions {
        revocation: Some(pre_proof),
        expected_revocation_root: Some(registry.root()),
        ..Default::default()
    };
    verify(&presentation, &pre_opts).expect("pre-revocation verification must succeed");

    // Revoke, then verify against the new root: must fail with Revoked.
    let post_proof = revoke(&registry, &cred);
    assert!(post_proof.revoked);
    let post_opts = VerificationOptions {
        revocation: Some(post_proof),
        expected_revocation_root: Some(registry.root()),
        ..Default::default()
    };
    let result = verify(&presentation, &post_opts);
    assert!(result.is_err(), "revoked credential must be rejected");
    match result.unwrap_err() {
        dregg_credentials::VerificationError::Revoked => {}
        other => panic!("expected Revoked, got {other:?}"),
    }
}

#[test]
fn revocation_witness_tamper_rejected() {
    // A holder cannot escape revocation by dropping their own id from the
    // witness set: the recomputed root then no longer matches the claimed
    // root (or the trusted expected root), so the proof is rejected rather
    // than silently treated as non-revoked.
    let issuer = fixture_issuer();
    let schema = fixture_schema();
    let h = holder();
    let cred = issue(&issuer, &schema, h, fixture_attrs(), 1_700_000_000, None).unwrap();
    let registry = RevocationRegistry::new();

    let presentation = present(&cred, &fixture_request(), &PresentationOptions::new()).unwrap();

    // Revoke this credential and capture the published (trusted) root.
    let mut tampered = revoke(&registry, &cred);
    let trusted_root = registry.root();

    // Holder tampers: removes its own id from the witness to fake absence,
    // but leaves the (real, revoked) root claimed.
    tampered.revoked_set.retain(|id| id != &cred.id());
    tampered.revoked = false; // and flips the convenience flag

    let opts = VerificationOptions {
        revocation: Some(tampered),
        expected_revocation_root: Some(trusted_root),
        ..Default::default()
    };
    let result = verify(&presentation, &opts);
    assert!(
        result.is_err(),
        "a tampered non-revocation witness must be rejected (root no longer binds)"
    );
}
