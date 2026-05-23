//! KYC Demo: prove age + residency + non-blacklisted.
//!
//! Demonstrates a complete identity verification flow:
//! 1. Government issues an ID credential to Alice
//! 2. Alice proves she is >= 18, resides in "US", and is not blacklisted
//! 3. The verifier accepts the proof without learning Alice's exact age or full credential

use pyana_circuit::dsl::predicates::PredicateType;
use pyana_circuit::field::BabyBear;
use pyana_identity::AttributeValue;
use pyana_identity::issuer::IssuerRegistry;
use pyana_identity::presentation::{self, PresentationBuilder};
use pyana_identity::verifier::{VerificationPolicy, VerificationResult};
use std::collections::BTreeMap;

fn main() {
    println!("=== Pyana Identity: KYC Verification Demo ===\n");

    // --- Setup: Government issuer ---
    let gov_id = *blake3::hash(b"government-issuer-usa").as_bytes();
    let mut government = IssuerRegistry::new(gov_id);

    // --- Setup: Holder (Alice) ---
    let alice_id = *blake3::hash(b"holder-alice").as_bytes();

    // --- Step 1: Issue credential ---
    println!("Step 1: Government issues ID credential to Alice");
    let mut attrs = BTreeMap::new();
    attrs.insert(
        "name".to_string(),
        AttributeValue::Text("Alice Johnson".to_string()),
    );
    attrs.insert("age".to_string(), AttributeValue::Integer(28));
    attrs.insert(
        "country".to_string(),
        AttributeValue::Text("US".to_string()),
    );
    attrs.insert(
        "state".to_string(),
        AttributeValue::Text("California".to_string()),
    );
    attrs.insert(
        "id_number".to_string(),
        AttributeValue::Text("X12345678".to_string()),
    );

    let credential = government
        .issue("GovernmentID", alice_id, attrs, 20440, 0)
        .expect("Failed to issue credential");

    println!(
        "  Credential issued: schema={}, attributes={}",
        credential.schema_name,
        credential.attributes.len()
    );
    println!(
        "  Credential commitment: {}",
        credential.commitment.as_u32()
    );
    println!();

    // --- Step 2: Revoke some other credentials (not Alice's) ---
    println!("Step 2: Government revokes some other credentials (not Alice's)");
    let blacklisted_1 = *blake3::hash(b"criminal-credential-1").as_bytes();
    let blacklisted_2 = *blake3::hash(b"criminal-credential-2").as_bytes();
    government.revoke(&blacklisted_1);
    government.revoke(&blacklisted_2);
    println!("  Revoked {} credentials", government.num_revoked());
    println!(
        "  Alice is NOT revoked: {}",
        !government.is_revoked(&credential.id)
    );
    println!();

    // --- Step 3: Alice builds a presentation ---
    println!("Step 3: Alice builds KYC presentation");
    println!("  - Proves: age >= 18 (without revealing exact age)");
    println!("  - Reveals: country (selective disclosure)");
    println!("  - Proves: not blacklisted (non-revocation proof)");
    println!();

    // Generate non-revocation proof.
    let non_rev = presentation::prove_non_revocation(&credential, government.revocation_tree());
    println!("  Non-revocation proof valid: {}", non_rev.is_valid);

    // Build the presentation.
    let mut builder = PresentationBuilder::new();
    let idx = builder.add_credential(credential.clone());
    builder.add_predicate(idx, "age", PredicateType::Gte, 18);
    builder.reveal_attribute(idx, "country");
    builder.set_non_revocation(non_rev);

    let presentation = builder.build().expect("Failed to build presentation");

    println!("  Presentation built successfully:");
    println!(
        "    Revealed attributes: {:?}",
        presentation.revealed_attributes.keys().collect::<Vec<_>>()
    );
    println!(
        "    Predicate proofs: {} (all verified: {})",
        presentation.predicate_results.len(),
        presentation.predicate_results.iter().all(|p| p.verified)
    );
    println!(
        "    Non-revocation valid: {}",
        presentation.non_revocation_valid
    );
    println!();

    // --- Step 4: Verifier checks the presentation ---
    println!("Step 4: Verifier checks KYC presentation against policy");

    let policy = VerificationPolicy::new(
        "kyc-age-residency",
        BabyBear::new(999), // federation root (simplified for demo)
        government.revocation_root(),
    )
    .require_predicate("age", PredicateType::Gte, 18)
    .require_reveal("country")
    .with_non_revocation(true);

    let result = policy.verify_presentation(&presentation);

    match &result {
        VerificationResult::Accepted => {
            println!("  ACCEPTED: Alice passes KYC verification");
            println!("  Verifier learned:");
            println!("    - Alice is >= 18 years old (exact age hidden)");
            println!(
                "    - Alice resides in: {}",
                presentation
                    .revealed_attributes
                    .get("country")
                    .map(|v| format!("{:?}", v))
                    .unwrap_or_default()
            );
            println!("    - Alice's credential is not blacklisted");
            println!("  Verifier did NOT learn:");
            println!("    - Alice's exact age");
            println!("    - Alice's name, ID number, or state");
        }
        VerificationResult::Rejected { reason } => {
            println!("  REJECTED: {}", reason);
        }
    }
    println!();

    // --- Step 5: Demonstrate that a false claim fails ---
    println!("Step 5: Demonstrate that a false predicate claim fails");
    println!("  Attempting to prove age >= 65 (Alice is 28)...");

    let mut builder2 = PresentationBuilder::new();
    let idx2 = builder2.add_credential(credential);
    builder2.add_predicate(idx2, "age", PredicateType::Gte, 65);

    let presentation2 = builder2.build().expect("build");
    let age_result = &presentation2.predicate_results[0];
    println!(
        "  Predicate 'age >= 65' verified: {} (correctly fails!)",
        age_result.verified
    );

    println!("\n=== Demo Complete ===");
}
