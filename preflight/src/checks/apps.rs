//! App integration checks: gallery, identity.
//!
//! Each check imports and exercises the ACTUAL app crate's public API rather than
//! reimplementing domain logic with raw TurnBuilder calls. This ensures that:
//! - App public APIs are ergonomic and compile correctly
//! - Core domain invariants hold end-to-end
//! - Circuit integration (prove + verify) works for apps that have it
//!
//! Gallery depends on pyana-app-framework (which depends on pyana-sdk). When
//! pyana-sdk is broken, the gallery check is gated behind the `apps-sdk`
//! feature and reported as ignored when disabled.
//!
//! Identity compiles independently and always runs.
//!
//! NOTE: stablecoin / amm / orderbook / lending / dao-treasury / prediction-market
//! were retired in the `apps/ → starbridge-apps/` migration; see
//! `STARBRIDGE-APPS-PLAN.md` §4.1 for the rationale.

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    let mut checks = Vec::new();

    // SDK-dependent app checks (gallery).
    #[cfg(feature = "apps-sdk")]
    {
        checks.push(run_check("gallery", check_gallery_logic));
    }
    #[cfg(not(feature = "apps-sdk"))]
    {
        // IGNORED: pyana-sdk is broken (missing `custom_program_proofs` field in Turn).
        // This check requires pyana-app-framework -> pyana-sdk to compile.
        checks.push(run_check("gallery", || {
            Err("IGNORED: pyana-sdk broken (custom_program_proofs missing)".into())
        }));
    }

    // Independent app checks (always compile).
    checks.push(run_check("identity", check_identity_logic));

    checks
}

// =============================================================================
// Gallery
// =============================================================================

#[cfg(feature = "apps-sdk")]
fn check_gallery_logic() -> Result<(), String> {
    // Gallery's ArtworkRegistry.register() is async and requires a PyanaEngine,
    // so we test the domain primitives that work without an engine:
    // - Artwork ID computation
    // - Bid commitment / reveal cycle
    // - Auction phase validation
    use pyana_gallery::{
        AuctionPhase, compute_artwork_id, compute_bid_commitment, verify_bid_reveal,
    };

    // 1. Artwork ID is deterministic and content-addressed.
    let artist = pyana_types::CellId([0xAA; 32]);
    let image_hash = *blake3::hash(b"digital-painting-bytes").as_bytes();
    let artwork_id = compute_artwork_id(&artist, "Test Artwork", &image_hash);
    let artwork_id_2 = compute_artwork_id(&artist, "Test Artwork", &image_hash);
    if artwork_id != artwork_id_2 {
        return Err("artwork ID should be deterministic".into());
    }

    // Different title => different ID.
    let artwork_id_3 = compute_artwork_id(&artist, "Different Title", &image_hash);
    if artwork_id == artwork_id_3 {
        return Err("different titles should produce different artwork IDs".into());
    }

    // 2. Bid commitment / reveal: commit-reveal integrity.
    let bidder = pyana_types::CellId([0xBB; 32]);
    let amount = 5000u64;
    let nonce = *blake3::hash(b"bid-nonce-secret").as_bytes();

    let commitment = compute_bid_commitment(&bidder, amount, &nonce);

    // Valid reveal should verify.
    if !verify_bid_reveal(&commitment, &bidder, amount, &nonce) {
        return Err("valid bid reveal should pass verification".into());
    }

    // Wrong amount should fail.
    if verify_bid_reveal(&commitment, &bidder, amount + 1, &nonce) {
        return Err("bid reveal with wrong amount should fail".into());
    }

    // Wrong nonce should fail.
    let wrong_nonce = [0u8; 32];
    if verify_bid_reveal(&commitment, &bidder, amount, &wrong_nonce) {
        return Err("bid reveal with wrong nonce should fail".into());
    }

    // 3. AuctionPhase equality checks (ensures serde/types work).
    let phase = AuctionPhase::Bidding;
    if phase != AuctionPhase::Bidding {
        return Err("phase equality broken".into());
    }
    if phase == AuctionPhase::Reveal {
        return Err("bidding should not equal reveal".into());
    }

    Ok(())
}

// =============================================================================
// Identity
// =============================================================================

fn check_identity_logic() -> Result<(), String> {
    use pyana_circuit::field::BabyBear;
    use pyana_identity::AttributeValue;
    use pyana_identity::credential::CredentialSchema;
    use pyana_identity::holder::CredentialWallet;
    use pyana_identity::issuer::IssuerRegistry;
    use pyana_identity::presentation::PresentationBuilder;
    use pyana_identity::revocation::NonRevocationProof;
    use pyana_identity::verifier::VerificationPolicy;
    use std::collections::BTreeMap;

    let issuer_id = [0x11u8; 32];
    let holder_id = [0x22u8; 32];

    // 1. Create an issuer and register a schema.
    let mut issuer = IssuerRegistry::new(issuer_id);

    let schema = CredentialSchema {
        name: "GovernmentID".to_string(),
        issuer_id,
        attributes: vec!["name".into(), "age".into(), "country".into()],
    };
    issuer.register_schema(schema);

    // 2. Issue a credential to a holder.
    let mut attributes = BTreeMap::new();
    attributes.insert("name".into(), AttributeValue::Text("Alice".into()));
    attributes.insert("age".into(), AttributeValue::Integer(25));
    attributes.insert("country".into(), AttributeValue::Text("US".into()));

    let credential = issuer
        .issue("GovernmentID", holder_id, attributes, 1000, 2000)
        .ok_or("issuance failed")?;

    if credential.schema_name != "GovernmentID" {
        return Err("credential schema name mismatch".into());
    }
    if credential.issuer_id != issuer_id {
        return Err("credential issuer_id mismatch".into());
    }
    if credential.holder_id != holder_id {
        return Err("credential holder_id mismatch".into());
    }

    let cred_id = credential.id;

    // 3. Store credential in a cclerk.
    let mut cclerk = CredentialWallet::new(holder_id);
    cclerk.store(credential.clone());

    if cclerk.len() != 1 {
        return Err(format!(
            "cclerk should have 1 credential, got {}",
            cclerk.len()
        ));
    }
    if cclerk.get(&cred_id).is_none() {
        return Err("cclerk should find stored credential".into());
    }

    // 4. Build a presentation with selective disclosure.
    let mut builder = PresentationBuilder::new();
    let cred_idx = builder.add_credential(credential.clone());
    builder.reveal_attribute(cred_idx, "name");

    // Attach a valid non-revocation proof (credential is NOT revoked).
    let non_rev_proof = NonRevocationProof {
        revocation_root: issuer.revocation_root(),
        is_valid: true,
    };
    builder.set_non_revocation(non_rev_proof);

    let presentation = builder.build().ok_or("presentation build failed")?;

    // Verify: name should be revealed.
    if !presentation.revealed_attributes.contains_key("name") {
        return Err("name should be in revealed attributes".into());
    }
    // Age should NOT be revealed (selective disclosure).
    if presentation.revealed_attributes.contains_key("age") {
        return Err("age should NOT be revealed".into());
    }

    // 5. Verification policy checks.
    let policy = VerificationPolicy::new(
        "AgeCheck",
        BabyBear::ZERO, // federation root (simplified)
        issuer.revocation_root(),
    )
    .require_reveal("name")
    .with_non_revocation(true);

    let result = policy.verify_presentation(&presentation);
    if !result.is_accepted() {
        return Err(format!("presentation should be accepted, got {:?}", result));
    }

    // 6. Missing required attribute fails verification.
    let strict_policy =
        VerificationPolicy::new("StrictCheck", BabyBear::ZERO, issuer.revocation_root())
            .require_reveal("age") // age was not revealed
            .with_non_revocation(true);

    let strict_result = strict_policy.verify_presentation(&presentation);
    if strict_result.is_accepted() {
        return Err("policy requiring unrevealed 'age' should reject".into());
    }

    // 7. Revocation: revoke the credential and verify it's detected.
    let revoked = issuer.revoke(&cred_id);
    if !revoked {
        return Err("revocation should succeed".into());
    }
    if !issuer.is_revoked(&cred_id) {
        return Err("credential should show as revoked".into());
    }

    // A presentation with invalid non-revocation proof should be rejected.
    let mut builder2 = PresentationBuilder::new();
    let cred_idx2 = builder2.add_credential(credential.clone());
    builder2.reveal_attribute(cred_idx2, "name");
    // Don't set non-revocation proof (simulates revoked credential).
    let presentation2 = builder2.build().ok_or("presentation2 build failed")?;

    let revoke_policy =
        VerificationPolicy::new("RevokeCheck", BabyBear::ZERO, issuer.revocation_root())
            .require_reveal("name")
            .with_non_revocation(true);

    let revoke_result = revoke_policy.verify_presentation(&presentation2);
    if revoke_result.is_accepted() {
        return Err("revoked credential without non-revocation proof should be rejected".into());
    }

    // 8. Double revocation returns false (already revoked).
    let double_revoke = issuer.revoke(&cred_id);
    if double_revoke {
        return Err("double revocation should return false".into());
    }

    Ok(())
}
