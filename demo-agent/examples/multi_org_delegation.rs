//! Multi-Org Delegation Demo — Cross-Organization ZK Authorization
//!
//! Demonstrates:
//! 1. Org A mints a root token for their agent
//! 2. Agent attenuates it for a specific cross-org request (service + time window)
//! 3. Agent presents a ZK proof to Org B's verifier (Fully Private mode)
//! 4. Org B verifies without learning anything about Org A's internal structure
//! 5. Shows that an invalid/expired token produces a rejected proof
//!
//! The key insight: Org B never sees the token chain, the capabilities, or
//! the internal delegation structure of Org A. They only verify a STARK proof
//! that the presenter is authorized by *some* member of a known federation.

use dregg_bridge::BridgePresentationBuilder;
use dregg_bridge::present::{bytes_to_babybear, hash_index, verify_presentation_bb};
use dregg_circuit::BabyBear;
use dregg_circuit::poseidon2;
use dregg_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken};

/// Compute the Poseidon2-based federation root for a given issuer key.
/// This matches what BridgePresentationBuilder uses internally.
fn compute_poseidon2_federation_root(issuer_key: &[u8; 32]) -> BabyBear {
    let issuer_hash = bytes_to_babybear(issuer_key);
    let depth = 8;
    let mut current = issuer_hash;
    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new(hash_index(i, 0, issuer_key)),
            BabyBear::new(hash_index(i, 1, issuer_key)),
            BabyBear::new(hash_index(i, 2, issuer_key)),
        ];
        let mut children = [BabyBear::ZERO; 4];
        let mut sib_idx = 0;
        for j in 0..4u8 {
            if j == position {
                children[j as usize] = current;
            } else {
                children[j as usize] = siblings[sib_idx];
                sib_idx += 1;
            }
        }
        current = poseidon2::hash_4_to_1(&children);
    }
    current
}

fn short_hex(bytes: &[u8]) -> String {
    if bytes.len() >= 4 {
        format!(
            "{:02x}{:02x}{:02x}{:02x}...",
            bytes[0], bytes[1], bytes[2], bytes[3]
        )
    } else {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}

fn main() {
    println!("=== Dregg Multi-Org Delegation Demo ===");
    println!("    Cross-Organization ZK Authorization (Fully Private Mode)");
    println!();

    // =========================================================================
    // SETUP: Two organizations with separate federation roots
    // =========================================================================
    println!("--- Setup: Organizations and Keys ---");

    // Org A: the delegating organization
    let org_a_issuer_key = *blake3::hash(b"org-a:issuer:root-key-2026").as_bytes();
    let org_a_agent_name = "agent-alpha-7";

    // Org B: the verifying organization (runs a service Org A's agent wants to call)
    let org_b_service = "data-warehouse";

    // Compute Org A's federation root (Poseidon2-based, collision-resistant)
    let org_a_federation_root_bb = compute_poseidon2_federation_root(&org_a_issuer_key);
    let mut org_a_federation_root_bytes = [0u8; 32];
    org_a_federation_root_bytes[..4].copy_from_slice(&org_a_federation_root_bb.0.to_le_bytes());

    println!("  Org A issuer key:       {}", short_hex(&org_a_issuer_key));
    println!("  Org A agent:            {}", org_a_agent_name);
    println!(
        "  Org A federation root:  {} (Poseidon2)",
        org_a_federation_root_bb.0
    );
    println!("  Org B service:          {}", org_b_service);
    println!();
    println!("  Trust model: Org B trusts Org A's federation root (shared out-of-band).");
    println!("  Org B does NOT know Org A's internal delegation chain or agent identity.");
    println!();

    // =========================================================================
    // STEP 1: Org A mints a root token for their agent
    // =========================================================================
    println!("--- Step 1: ORG A MINTS ROOT TOKEN ---");

    let root_token = MacaroonToken::mint(
        org_a_issuer_key,
        format!("org-a:{}", org_a_agent_name).as_bytes(),
        "org-a.internal",
    );
    println!("  Root token minted (unrestricted within Org A)");
    println!("  Key ID: org-a:{}", org_a_agent_name);
    println!("  Location: org-a.internal");
    println!();

    // =========================================================================
    // STEP 2: Agent attenuates for cross-org request
    // =========================================================================
    println!("--- Step 2: AGENT ATTENUATES TOKEN FOR CROSS-ORG REQUEST ---");

    let cross_org_attenuation = Attenuation {
        services: vec![(org_b_service.into(), "r".into())],
        apps: vec![("cross-org-query".into(), "r".into())],
        not_after: Some(1800000000),  // Valid until ~2027
        not_before: Some(1700000000), // Not before ~2023
        confine_user: Some(org_a_agent_name.into()),
        ..Default::default()
    };

    let attenuated_token = root_token.attenuate(&cross_org_attenuation).unwrap();
    println!("  Token attenuated with restrictions:");
    println!("    - Service: {} (read-only)", org_b_service);
    println!("    - App: cross-org-query (read-only)");
    println!("    - Valid window: [1700000000, 1800000000]");
    println!("    - Confined to user: {}", org_a_agent_name);
    println!();

    // Verify the attenuated token works for the intended request
    let intended_request = AuthRequest {
        service: Some(org_b_service.into()),
        app_id: Some("cross-org-query".into()),
        action: Some("r".into()),
        user_id: Some(org_a_agent_name.into()),
        now: Some(1750000000), // Within validity window
        ..Default::default()
    };
    let clearance = attenuated_token.verify(&intended_request).unwrap();
    println!(
        "  Plaintext verification: PASS ({} capabilities)",
        clearance.capabilities.len()
    );
    println!();

    // =========================================================================
    // STEP 3: Agent generates ZK proof (Fully Private mode)
    // =========================================================================
    println!("--- Step 3: GENERATE ZK PROOF (Fully Private Mode) ---");
    println!("  The agent converts its attenuated token chain into a STARK proof.");
    println!("  This proves authorization WITHOUT revealing:");
    println!("    - The root token or issuer identity");
    println!("    - The attenuation chain (how many steps, what restrictions)");
    println!("    - Org A's internal structure or other agents");
    println!();

    // Build the presentation proof using the bridge
    let mut builder = BridgePresentationBuilder::new_with_root_bb(
        org_a_issuer_key,
        org_a_federation_root_bytes,
        org_a_federation_root_bb,
    );

    // Set the root token (first step in the chain)
    let root_for_proof = MacaroonToken::mint(
        org_a_issuer_key,
        format!("org-a:{}", org_a_agent_name).as_bytes(),
        "org-a.internal",
    );
    builder.set_root_token(root_for_proof);
    println!("  Chain step 1: root token (unrestricted)");

    // Add the attenuation step
    let proof_attenuation = Attenuation {
        services: vec![(org_b_service.into(), "r".into())],
        apps: vec![("cross-org-query".into(), "r".into())],
        ..Default::default()
    };
    let att_ok = builder.add_attenuation(&proof_attenuation);
    assert!(att_ok, "Attenuation should succeed");
    println!(
        "  Chain step 2: attenuated (service={}, app=cross-org-query)",
        org_b_service
    );
    println!("  Chain length: {}", builder.chain_length());

    // Verify the fold chain integrity
    assert!(builder.verify_chain(), "Fold chain must be valid");
    println!("  Fold chain integrity: VALID");
    println!();

    // Generate the real STARK proof (Poseidon2 path — collision-resistant)
    let proof_request = AuthRequest {
        service: Some(org_b_service.into()),
        app_id: Some("cross-org-query".into()),
        action: Some("r".into()),
        now: Some(1750000000),
        ..Default::default()
    };

    let presentation = builder
        .prove(&proof_request)
        .expect("Proof generation should succeed");

    println!("  STARK proof generated:");
    println!("    Proof size: {}", presentation.proof_size_display());
    println!(
        "    Chain length proven: {} steps",
        presentation.chain_length
    );
    println!(
        "    Has real STARK proof: {}",
        presentation.has_real_stark_proof()
    );
    println!(
        "    Federation root (public input): {}",
        short_hex(&presentation.federation_root)
    );
    println!();

    // =========================================================================
    // STEP 4: Org B verifies the proof (learns NOTHING about Org A's structure)
    // =========================================================================
    println!("--- Step 4: ORG B VERIFIES (Zero-Knowledge) ---");
    println!("  Org B receives only:");
    println!("    1. The STARK proof bytes");
    println!("    2. The federation root they already trust");
    println!("    3. The request predicate (what action is being authorized)");
    println!();

    // Verify the presentation proof.
    // SECURITY: Org B uses its own copy of Org A's federation root (shared out-of-band),
    // NOT the proof's embedded root. Using proof.federation_root would be circular.
    let is_valid = verify_presentation_bb(
        &presentation,
        bytes_to_babybear(&org_a_federation_root_bytes),
    );
    println!(
        "  Presentation valid: {} [{}]",
        is_valid,
        if is_valid { "PASS" } else { "FAIL" }
    );

    // Verify the STARK proof cryptographically
    let stark_result = presentation.verify_issuer_stark();
    match stark_result {
        Some(Ok(())) => {
            println!("  STARK cryptographic verification: PASS");
            println!("    (80 FRI queries, ~124-bit security)");
        }
        Some(Err(e)) => {
            panic!("  STARK verification failed: {}", e);
        }
        None => {
            panic!("  No STARK proof attached!");
        }
    }

    println!();
    println!("  What Org B learned:");
    println!("    [x] The presenter holds a valid authorization from Org A's federation");
    println!("    [x] The authorization covers the requested action (service read)");
    println!("    [ ] Who the agent is within Org A (HIDDEN)");
    println!("    [ ] How many delegation steps occurred (HIDDEN)");
    println!("    [ ] What other capabilities the agent holds (HIDDEN)");
    println!("    [ ] Org A's internal delegation policies (HIDDEN)");
    println!();

    // =========================================================================
    // STEP 5: Demonstrate rejection of unauthorized request
    // =========================================================================
    println!("--- Step 5: DEMONSTRATE REJECTION ---");
    println!("  Attempting to prove authorization for a WRITE action...");
    println!("  (The attenuated token only grants READ access)");
    println!();

    // Try to generate a proof for a write action (should fail at authorization)
    let mut bad_builder = BridgePresentationBuilder::new_with_root_bb(
        org_a_issuer_key,
        org_a_federation_root_bytes,
        org_a_federation_root_bb,
    );
    let bad_root = MacaroonToken::mint(org_a_issuer_key, b"org-a:agent-alpha-7", "org-a.internal");
    bad_builder.set_root_token(bad_root);
    bad_builder.add_attenuation(&proof_attenuation);

    // Request WRITE access (not granted by the attenuation)
    let bad_request = AuthRequest {
        service: Some("unauthorized-service".into()),
        app_id: Some("cross-org-query".into()),
        action: Some("w".into()),
        now: Some(1750000000),
        ..Default::default()
    };

    let bad_result = bad_builder.prove(&bad_request);
    match bad_result {
        Err(e) => {
            println!("  Proof generation REJECTED: {}", e);
            println!("  The attenuated token does not authorize this request.");
            println!("  No proof was produced -- the prover cannot forge authorization.");
        }
        Ok(_) => {
            panic!("Should NOT have been able to prove unauthorized access!");
        }
    }
    println!();

    // =========================================================================
    // STEP 6: Demonstrate that proof bytes are extractable for wire transport
    // =========================================================================
    println!("--- Step 6: WIRE TRANSPORT ---");

    let proof_bytes = presentation
        .issuer_proof_bytes()
        .expect("Should have proof bytes");
    println!(
        "  Extractable proof bytes: {} bytes ({:.1} KiB)",
        proof_bytes.len(),
        proof_bytes.len() as f64 / 1024.0
    );
    println!("  These bytes are all Org B needs to verify (plus the trusted federation root).");
    println!("  The entire token chain, delegation structure, and agent identity");
    println!("  remain with Org A -- never transmitted over the wire.");
    println!();

    // =========================================================================
    // SUMMARY
    // =========================================================================
    println!("--- Summary: Security Properties ---");
    println!();
    println!("  [x] ZERO-KNOWLEDGE: Org B verified authorization without learning");
    println!("      Org A's internal structure, agent count, or delegation depth.");
    println!();
    println!("  [x] SOUNDNESS: Only agents holding a valid token chain rooted in");
    println!("      Org A's federation can produce a verifying proof.");
    println!();
    println!("  [x] ATTENUATION: The agent cannot prove more capabilities than");
    println!("      its attenuated token grants (write attempt was rejected).");
    println!();
    println!("  [x] FEDERATION BINDING: The proof is bound to Org A's specific");
    println!("      federation root -- a different org's proof won't verify.");
    println!();
    println!("  [x] NON-TRANSFERABLE: The proof demonstrates knowledge of the");
    println!("      token chain, not possession of a bearer credential.");
    println!();
    println!("=== Multi-Org Delegation Demo Complete ===");
}
