//! Full lifecycle tests for the identity and verifiable credentials system.

use crate::AttributeValue;
use crate::anonymous::AnonymousRegistry;
use crate::credential::Credential;
use crate::holder::CredentialWallet;
use crate::issuer::IssuerRegistry;
use crate::presentation::{self, PresentationBuilder};
use crate::revocation::RevocationManager;
use crate::verifier::{VerificationPolicy, VerificationResult};
use pyana_circuit::dsl::predicates::PredicateType;
use pyana_circuit::field::BabyBear;
use std::collections::BTreeMap;

/// Helper: create test issuer and holder IDs.
fn test_ids() -> ([u8; 32], [u8; 32]) {
    let issuer_id = *blake3::hash(b"test-issuer-government").as_bytes();
    let holder_id = *blake3::hash(b"test-holder-alice").as_bytes();
    (issuer_id, holder_id)
}

/// Helper: create a government ID credential for Alice (born 1990-01-15).
fn create_government_id(issuer: &mut IssuerRegistry, holder_id: [u8; 32]) -> Credential {
    let mut attrs = BTreeMap::new();
    attrs.insert(
        "name".to_string(),
        AttributeValue::Text("Alice".to_string()),
    );
    // Birth date as days since epoch: 1990-01-15 ~ 7319 days since 1970-01-01
    attrs.insert("birth_date".to_string(), AttributeValue::Date(7319));
    attrs.insert(
        "country".to_string(),
        AttributeValue::Text("US".to_string()),
    );
    attrs.insert("age".to_string(), AttributeValue::Integer(34));

    issuer
        .issue("GovernmentID", holder_id, attrs, 20000, 0)
        .expect("issue government ID")
}

/// Helper: create an employment credential for Alice.
fn create_employment_cert(issuer: &mut IssuerRegistry, holder_id: [u8; 32]) -> Credential {
    let mut attrs = BTreeMap::new();
    attrs.insert(
        "name".to_string(),
        AttributeValue::Text("Alice Smith".to_string()),
    );
    attrs.insert(
        "role".to_string(),
        AttributeValue::Text("Engineer".to_string()),
    );
    attrs.insert("salary".to_string(), AttributeValue::Integer(85000));
    attrs.insert("start_date".to_string(), AttributeValue::Date(19000));
    attrs.insert(
        "department".to_string(),
        AttributeValue::Text("Engineering".to_string()),
    );

    issuer
        .issue("EmploymentCert", holder_id, attrs, 20000, 0)
        .expect("issue employment cert")
}

/// Helper: create a bank statement credential.
fn create_bank_statement(issuer: &mut IssuerRegistry, holder_id: [u8; 32]) -> Credential {
    let mut attrs = BTreeMap::new();
    attrs.insert("balance".to_string(), AttributeValue::Integer(50000));
    attrs.insert(
        "account_type".to_string(),
        AttributeValue::Text("savings".to_string()),
    );

    issuer
        .issue("BankStatement", holder_id, attrs, 20000, 0)
        .expect("issue bank statement")
}

// ============================================================================
// Test: Issue credential -> holder stores
// ============================================================================

#[test]
fn test_issue_and_store() {
    let (issuer_id, holder_id) = test_ids();
    let mut issuer = IssuerRegistry::new(issuer_id);
    let mut wallet = CredentialWallet::new(holder_id);

    let cred = create_government_id(&mut issuer, holder_id);

    // Credential has correct fields.
    assert_eq!(cred.schema_name, "GovernmentID");
    assert_eq!(cred.issuer_id, issuer_id);
    assert_eq!(cred.holder_id, holder_id);
    assert!(cred.get_attribute("age").is_some());
    assert_eq!(
        cred.get_attribute("age"),
        Some(&AttributeValue::Integer(34))
    );

    // Store in wallet.
    wallet.store(cred.clone());
    assert_eq!(wallet.len(), 1);
    assert!(wallet.get(&cred.id).is_some());
}

// ============================================================================
// Test: Present with selective disclosure -> verifier accepts
// ============================================================================

#[test]
fn test_selective_disclosure() {
    let (issuer_id, holder_id) = test_ids();
    let mut issuer = IssuerRegistry::new(issuer_id);

    let cred = create_employment_cert(&mut issuer, holder_id);

    // Holder reveals only "role", hides salary/name/etc.
    let mut builder = PresentationBuilder::new();
    let idx = builder.add_credential(cred.clone());
    builder.reveal_attribute(idx, "role");

    let presentation = builder.build().expect("build presentation");

    // Only role is revealed.
    assert_eq!(presentation.revealed_attributes.len(), 1);
    assert!(presentation.revealed_attributes.contains_key("role"));
    assert_eq!(
        presentation.revealed_attributes.get("role"),
        Some(&AttributeValue::Text("Engineer".to_string()))
    );
    // Salary is NOT revealed.
    assert!(!presentation.revealed_attributes.contains_key("salary"));
}

// ============================================================================
// Test: Predicate proof (age >= 18) -> passes
// ============================================================================

#[test]
fn test_predicate_age_gte_18_passes() {
    let (issuer_id, holder_id) = test_ids();
    let mut issuer = IssuerRegistry::new(issuer_id);

    let cred = create_government_id(&mut issuer, holder_id);
    // age = 34

    let mut builder = PresentationBuilder::new();
    let idx = builder.add_credential(cred);
    builder.add_predicate(idx, "age", PredicateType::Gte, 18);

    let presentation = builder.build().expect("build presentation");

    // Age is NOT revealed.
    assert!(!presentation.revealed_attributes.contains_key("age"));
    // Predicate proof verifies.
    assert_eq!(presentation.predicate_results.len(), 1);
    let result = &presentation.predicate_results[0];
    assert_eq!(result.attribute_name, "age");
    assert_eq!(result.predicate_type, PredicateType::Gte);
    assert_eq!(result.threshold, 18);
    assert!(result.verified, "age >= 18 should verify (age is 34)");
}

// ============================================================================
// Test: Predicate proof (age >= 65 when holder is 30) -> fails
// ============================================================================

#[test]
fn test_predicate_age_gte_65_fails() {
    let (issuer_id, holder_id) = test_ids();
    let mut issuer = IssuerRegistry::new(issuer_id);

    // Create a credential with age = 30.
    let mut attrs = BTreeMap::new();
    attrs.insert("age".to_string(), AttributeValue::Integer(30));
    let cred = issuer
        .issue("GovernmentID", holder_id, attrs, 20000, 0)
        .expect("issue");

    let mut builder = PresentationBuilder::new();
    let idx = builder.add_credential(cred);
    builder.add_predicate(idx, "age", PredicateType::Gte, 65);

    let presentation = builder.build().expect("build presentation");

    // Predicate proof should fail (30 < 65).
    assert_eq!(presentation.predicate_results.len(), 1);
    let result = &presentation.predicate_results[0];
    assert!(!result.verified, "age >= 65 should NOT verify (age is 30)");
}

// ============================================================================
// Test: Revoked credential -> presentation rejected
// ============================================================================

#[test]
fn test_revoked_credential_rejected() {
    let (issuer_id, holder_id) = test_ids();
    let mut issuer = IssuerRegistry::new(issuer_id);

    let cred = create_government_id(&mut issuer, holder_id);
    let cred_id = cred.id;

    // Initially not revoked.
    assert!(!issuer.is_revoked(&cred_id));

    // Revoke the credential.
    assert!(issuer.revoke(&cred_id));
    assert!(issuer.is_revoked(&cred_id));

    // Try to generate non-revocation proof -> should fail.
    let non_rev = presentation::prove_non_revocation(&cred, issuer.revocation_tree());
    assert!(
        !non_rev.is_valid,
        "Non-revocation proof should be invalid for revoked credential"
    );

    // Build presentation with invalid non-revocation.
    let mut builder = PresentationBuilder::new();
    let idx = builder.add_credential(cred);
    builder.add_predicate(idx, "age", PredicateType::Gte, 18);
    builder.set_non_revocation(non_rev);

    let presentation = builder.build().expect("build presentation");
    assert!(
        !presentation.non_revocation_valid,
        "Presentation should mark non-revocation as invalid"
    );

    // Verifier rejects.
    let federation_root = BabyBear::new(999);
    let policy = VerificationPolicy::new("age-check", federation_root, issuer.revocation_root())
        .require_predicate("age", PredicateType::Gte, 18)
        .with_non_revocation(true);

    let result = policy.verify_presentation(&presentation);
    assert_eq!(
        result,
        VerificationResult::Rejected {
            reason: "Non-revocation proof missing or invalid".to_string()
        }
    );
}

// ============================================================================
// Test: Non-revoked credential -> non-revocation proof succeeds
// ============================================================================

#[test]
fn test_non_revoked_credential_proof_succeeds() {
    let (issuer_id, holder_id) = test_ids();
    let mut issuer = IssuerRegistry::new(issuer_id);

    let cred = create_government_id(&mut issuer, holder_id);

    // Revoke some OTHER credentials (but not ours).
    let other_id = *blake3::hash(b"other-credential-1").as_bytes();
    issuer.revoke(&other_id);
    let other_id2 = *blake3::hash(b"other-credential-2").as_bytes();
    issuer.revoke(&other_id2);

    // Our credential should still have a valid non-revocation proof.
    assert!(!issuer.is_revoked(&cred.id));
    let non_rev = presentation::prove_non_revocation(&cred, issuer.revocation_tree());
    assert!(
        non_rev.is_valid,
        "Non-revocation proof should be valid for non-revoked credential"
    );
}

// ============================================================================
// Test: Anonymous presentation -> unlinkable across verifiers
// ============================================================================

#[test]
fn test_anonymous_presentation_unlinkable() {
    let (issuer_id, holder_id) = test_ids();
    let mut issuer = IssuerRegistry::new(issuer_id);

    // Create multiple credentials for different holders.
    let cred_alice = create_government_id(&mut issuer, holder_id);

    let holder2 = *blake3::hash(b"test-holder-bob").as_bytes();
    let mut attrs2 = BTreeMap::new();
    attrs2.insert("age".to_string(), AttributeValue::Integer(25));
    let cred_bob = issuer
        .issue("GovernmentID", holder2, attrs2, 20000, 0)
        .expect("issue bob");

    let holder3 = *blake3::hash(b"test-holder-carol").as_bytes();
    let mut attrs3 = BTreeMap::new();
    attrs3.insert("age".to_string(), AttributeValue::Integer(40));
    let cred_carol = issuer
        .issue("GovernmentID", holder3, attrs3, 20000, 0)
        .expect("issue carol");

    // Build anonymous registry.
    let commitments = vec![
        cred_alice.commitment,
        cred_bob.commitment,
        cred_carol.commitment,
    ];
    let registry = AnonymousRegistry::new(commitments, 2);

    // Alice proves membership with two different blinding factors.
    let blinding_1 = BabyBear::new(111111);
    let blinding_2 = BabyBear::new(222222);

    let proof1 = registry
        .prove_anonymous_membership(&cred_alice, blinding_1)
        .expect("anonymous proof 1");
    let proof2 = registry
        .prove_anonymous_membership(&cred_alice, blinding_2)
        .expect("anonymous proof 2");

    // Both proofs are valid.
    assert!(proof1.verify(registry.root()));
    assert!(proof2.verify(registry.root()));

    // But the blinded leaves are different (unlinkable).
    assert_ne!(
        proof1.blinded_leaf, proof2.blinded_leaf,
        "Different blinding factors must produce unlinkable presentations"
    );
}

// ============================================================================
// Test: Multi-credential composition -> single verification
// ============================================================================

#[test]
fn test_multi_credential_composition() {
    let (issuer_id, holder_id) = test_ids();
    let mut gov_issuer = IssuerRegistry::new(issuer_id);

    let employer_id = *blake3::hash(b"test-issuer-employer").as_bytes();
    let mut emp_issuer = IssuerRegistry::new(employer_id);

    let bank_id = *blake3::hash(b"test-issuer-bank").as_bytes();
    let mut bank_issuer = IssuerRegistry::new(bank_id);

    // Issue credentials from different issuers.
    let gov_cred = create_government_id(&mut gov_issuer, holder_id);
    let emp_cred = create_employment_cert(&mut emp_issuer, holder_id);
    let bank_cred = create_bank_statement(&mut bank_issuer, holder_id);

    // Build individual presentations.
    let mut builder1 = PresentationBuilder::new();
    let idx = builder1.add_credential(gov_cred);
    builder1.add_predicate(idx, "age", PredicateType::Gte, 18);
    let pres1 = builder1.build().expect("gov presentation");

    let mut builder2 = PresentationBuilder::new();
    let idx = builder2.add_credential(emp_cred);
    builder2.add_predicate(idx, "salary", PredicateType::Gte, 50000);
    builder2.reveal_attribute(idx, "role");
    let pres2 = builder2.build().expect("emp presentation");

    let mut builder3 = PresentationBuilder::new();
    let idx = builder3.add_credential(bank_cred);
    builder3.add_predicate(idx, "balance", PredicateType::Gte, 10000);
    let pres3 = builder3.build().expect("bank presentation");

    // Compose into single presentation.
    let composed = presentation::compose_presentations(vec![pres1, pres2, pres3]);

    // Verify: age >= 18 (passed), salary >= 50000 (passed), balance >= 10000 (passed).
    assert_eq!(composed.predicate_results.len(), 3);
    assert!(composed.predicate_results[0].verified); // age >= 18
    assert!(composed.predicate_results[1].verified); // salary >= 50000
    assert!(composed.predicate_results[2].verified); // balance >= 10000

    // Role is revealed.
    assert_eq!(
        composed.revealed_attributes.get("role"),
        Some(&AttributeValue::Text("Engineer".to_string()))
    );

    // Three credential IDs involved.
    assert_eq!(composed.credential_ids.len(), 3);
}

// ============================================================================
// Test: Verification policy acceptance
// ============================================================================

#[test]
fn test_verification_policy_accepts() {
    let (issuer_id, holder_id) = test_ids();
    let mut issuer = IssuerRegistry::new(issuer_id);

    let cred = create_government_id(&mut issuer, holder_id);

    // Non-revocation proof.
    let non_rev = presentation::prove_non_revocation(&cred, issuer.revocation_tree());
    assert!(non_rev.is_valid);

    // Build presentation.
    let mut builder = PresentationBuilder::new();
    let idx = builder.add_credential(cred);
    builder.add_predicate(idx, "age", PredicateType::Gte, 18);
    builder.reveal_attribute(idx, "name");
    builder.set_non_revocation(non_rev);

    let presentation = builder.build().expect("build");

    // Policy: require age >= 18 + name revealed + non-revocation.
    let policy = VerificationPolicy::new("basic-kyc", BabyBear::new(999), issuer.revocation_root())
        .require_predicate("age", PredicateType::Gte, 18)
        .require_reveal("name")
        .with_non_revocation(true);

    let result = policy.verify_presentation(&presentation);
    assert!(
        result.is_accepted(),
        "Policy should accept valid presentation: {:?}",
        result
    );
}

// ============================================================================
// Test: Verification policy rejects missing attribute
// ============================================================================

#[test]
fn test_verification_policy_rejects_missing_reveal() {
    let (issuer_id, holder_id) = test_ids();
    let mut issuer = IssuerRegistry::new(issuer_id);

    let cred = create_government_id(&mut issuer, holder_id);
    let non_rev = presentation::prove_non_revocation(&cred, issuer.revocation_tree());

    // Holder does NOT reveal "name".
    let mut builder = PresentationBuilder::new();
    let idx = builder.add_credential(cred);
    builder.add_predicate(idx, "age", PredicateType::Gte, 18);
    builder.set_non_revocation(non_rev);
    let presentation = builder.build().expect("build");

    // Policy requires name to be revealed.
    let policy =
        VerificationPolicy::new("require-name", BabyBear::new(999), issuer.revocation_root())
            .require_reveal("name")
            .with_non_revocation(true);

    let result = policy.verify_presentation(&presentation);
    assert!(!result.is_accepted());
}

// ============================================================================
// Test: Salary predicate (selective disclosure variant)
// ============================================================================

#[test]
fn test_salary_predicate_selective_disclosure() {
    let (_issuer_id, holder_id) = test_ids();
    let employer_id = *blake3::hash(b"test-issuer-employer").as_bytes();
    let mut issuer = IssuerRegistry::new(employer_id);

    let cred = create_employment_cert(&mut issuer, holder_id);
    // salary = 85000

    // Holder reveals role, proves salary >= 50000 without revealing exact salary.
    let mut builder = PresentationBuilder::new();
    let idx = builder.add_credential(cred);
    builder.reveal_attribute(idx, "role");
    builder.add_predicate(idx, "salary", PredicateType::Gte, 50000);

    let presentation = builder.build().expect("build");

    // Role revealed.
    assert_eq!(
        presentation.revealed_attributes.get("role"),
        Some(&AttributeValue::Text("Engineer".to_string()))
    );
    // Salary NOT revealed.
    assert!(!presentation.revealed_attributes.contains_key("salary"));
    // Salary predicate passed.
    assert!(presentation.predicate_results[0].verified);
}

// ============================================================================
// Test: Revocation manager standalone
// ============================================================================

#[test]
fn test_revocation_manager() {
    let mut mgr = RevocationManager::new(4);

    let hash1 = BabyBear::new(12345);
    let hash2 = BabyBear::new(67890);
    let _hash3 = BabyBear::new(11111);

    // Initially empty.
    assert!(!mgr.is_revoked(&hash1));
    assert_eq!(mgr.num_revoked(), 0);

    // Revoke hash1.
    mgr.revoke(hash1);
    assert!(mgr.is_revoked(&hash1));
    assert!(!mgr.is_revoked(&hash2));
    assert_eq!(mgr.num_revoked(), 1);

    // Non-revocation proof for hash2 succeeds.
    let proof = mgr.prove_non_revocation(hash2);
    assert!(proof.is_some());
    assert!(mgr.verify_proof(proof.as_ref().unwrap()));

    // Non-revocation proof for hash1 fails (it's revoked).
    let proof_revoked = mgr.prove_non_revocation(hash1);
    assert!(proof_revoked.is_none());
}

// ============================================================================
// Test: Credential wallet operations
// ============================================================================

#[test]
fn test_wallet_operations() {
    let (issuer_id, holder_id) = test_ids();
    let mut issuer = IssuerRegistry::new(issuer_id);
    let mut wallet = CredentialWallet::new(holder_id);

    assert!(wallet.is_empty());

    let cred1 = create_government_id(&mut issuer, holder_id);
    let cred2 = create_employment_cert(&mut issuer, holder_id);

    wallet.store(cred1.clone());
    wallet.store(cred2.clone());

    assert_eq!(wallet.len(), 2);
    assert!(!wallet.is_empty());

    // Find by schema.
    let gov_creds = wallet.find_by_schema("GovernmentID");
    assert_eq!(gov_creds.len(), 1);

    // Find by issuer.
    let issuer_creds = wallet.find_by_issuer(&issuer_id);
    assert_eq!(issuer_creds.len(), 2);

    // Remove.
    wallet.remove(&cred1.id);
    assert_eq!(wallet.len(), 1);
    assert!(wallet.get(&cred1.id).is_none());
}
