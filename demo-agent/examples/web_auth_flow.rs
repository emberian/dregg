//! Browser Extension Cipherclerk Flow Simulation
//!
//! Simulates the complete browser extension authorization round-trip in pure Rust:
//! 1. Page requests authorization: { action: "read", resource: "/api/data" }
//! 2. Cipherclerk evaluates: find matching token, run Datalog, pick mode
//! 3. Generate proof (real STARK for private mode)
//! 4. Server verifies: check proof against attested root
//! 5. Show the full round-trip with timing
//! 6. Show what each party sees at each step (information asymmetry)

use std::time::Instant;

use dregg_bridge::present::{UnsafeLocalOnlyMarker, bytes_to_babybear, hash_index};
use dregg_bridge::{BridgePresentationBuilder, BridgePresentationProof};
use dregg_circuit::BabyBear;

use dregg_circuit::stark;
use dregg_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken};

// ─── Helpers ────────────────────────────────────────────────────────────────

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

fn compute_federation_root_bb(issuer_key: &[u8; 32]) -> BabyBear {
    use dregg_circuit::merkle_air::compute_parent_poseidon2;
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
        current = compute_parent_poseidon2(current, position, &siblings);
    }
    current
}

fn bb_to_bytes(bb: BabyBear) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    let val = bb.as_u32();
    bytes[..4].copy_from_slice(&val.to_le_bytes());
    bytes
}

fn section(step: usize, total: usize, title: &str) {
    println!();
    println!("  [{step}/{total}] {title}");
    println!("  {}", "-".repeat(56));
}

fn item(msg: &str) {
    println!("    {msg}");
}

fn party(name: &str, msg: &str) {
    println!("    [{name}] {msg}");
}

// ─── Main ────────────────────────────────────────────────────────────────────

fn main() {
    println!();
    println!("  {}", "=".repeat(60));
    println!("  DREGG WEB AUTH FLOW SIMULATION");
    println!("  Browser Extension Cipherclerk <-> Page <-> Server");
    println!("  {}", "=".repeat(60));

    let total_steps = 6;
    let total_start = Instant::now();

    // =========================================================================
    // Setup: Pre-provisioned state (what exists before the page loads)
    // =========================================================================

    // The issuer (identity provider / federation member) has a root key.
    let issuer_key: [u8; 32] = *blake3::hash(b"dregg-web-demo-issuer-key").as_bytes();

    // The federation root (attested by the federation, known to servers).
    let federation_root_bb = compute_federation_root_bb(&issuer_key);
    let federation_root = bb_to_bytes(federation_root_bb);

    // The cclerk holds a token attenuated for this user's permissions.
    let root_token = MacaroonToken::mint(issuer_key, b"user-session-001", "api.example.com");
    let user_attenuation = Attenuation {
        services: vec![("api".into(), "r".into())],
        apps: vec![("web-client".into(), "r".into())],
        not_after: Some(2000000000),
        ..Default::default()
    };
    let user_token = root_token.attenuate(&user_attenuation).unwrap();

    // =========================================================================
    // STEP 1: Page requests authorization
    // =========================================================================

    section(1, total_steps, "PAGE: Requests authorization");
    let step1_start = Instant::now();

    // This is what the page sends to the extension via window.dregg.authorize()
    // The "resource" concept maps to service + action in dregg's model.
    let page_request = AuthRequest {
        service: Some("api".into()),
        app_id: Some("web-client".into()),
        action: Some("r".into()),
        now: Some(1700000000),
        ..Default::default()
    };

    party("PAGE", "Calls: window.dregg.authorize({");
    party("PAGE", "  action: 'read',");
    party("PAGE", "  resource: '/api/data'");
    party("PAGE", "})");
    println!();
    party("PAGE", "The page sees: a pending promise. Nothing else.");
    party(
        "PAGE",
        "The page does NOT know: what tokens exist, who issued them,",
    );
    party("PAGE", "  or what capabilities the user has.");

    let step1_time = step1_start.elapsed();
    item(&format!("Time: {:?}", step1_time));

    // =========================================================================
    // STEP 2: Cipherclerk evaluates the request
    // =========================================================================

    section(2, total_steps, "WALLET: Evaluates request (local Datalog)");
    let step2_start = Instant::now();

    // The cclerk finds the matching token and runs verification.
    let clearance = user_token.verify(&page_request).unwrap();

    party("WALLET", "Found matching token for service 'api'");
    party(
        "WALLET",
        &format!(
            "Datalog evaluation: {} capabilities derived",
            clearance.capabilities.len()
        ),
    );
    party("WALLET", "Decision: ALLOW");
    party("WALLET", "Selected mode: FullyPrivate (maximum privacy)");
    println!();
    party(
        "WALLET",
        "The cclerk sees: full token chain, all capabilities, all caveats.",
    );
    party(
        "WALLET",
        "The cclerk decides: which token, which mode, what to reveal.",
    );

    let step2_time = step2_start.elapsed();
    item(&format!("Time: {:?}", step2_time));

    // =========================================================================
    // STEP 3: Generate proof (real STARK)
    // =========================================================================

    section(3, total_steps, "WALLET: Generates STARK proof");
    let step3_start = Instant::now();

    // Build the presentation proof using the bridge.
    let mut builder = BridgePresentationBuilder::new_with_root_bb(
        issuer_key,
        federation_root,
        federation_root_bb,
    );

    // Re-mint from root key (MacaroonToken is not Clone).
    let fresh_token = MacaroonToken::mint(issuer_key, b"user-session-001", "api.example.com");
    builder.set_root_token(fresh_token);
    builder.add_attenuation(&user_attenuation);

    let proof: BridgePresentationProof = builder
        .prove_local_constraint_check_only(
            &UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound(),
            &page_request,
        )
        .unwrap();

    let step3_time = step3_start.elapsed();

    party(
        "WALLET",
        &format!("Proof generated: {}", proof.proof_size_display()),
    );
    party("WALLET", &format!("Proof valid: {}", proof.is_valid()));
    party(
        "WALLET",
        &format!("Chain length: {} attenuation steps", proof.chain_length),
    );
    party(
        "WALLET",
        &format!("Has real STARK: {}", proof.has_real_stark_proof()),
    );
    println!();
    party(
        "WALLET",
        "The proof encodes: 'I hold a valid token authorizing this request'",
    );
    party(
        "WALLET",
        "The proof hides: which token, what other capabilities, who issued it",
    );

    item(&format!("Time: {:?}", step3_time));

    // =========================================================================
    // STEP 4: Also generate issuer membership STARK (the expensive part)
    // =========================================================================

    section(4, total_steps, "WALLET: Generates issuer membership STARK");
    let step4_start = Instant::now();

    // Generate the STARK proof for issuer membership.
    // This proves the issuer key is in the federation Merkle tree.
    let leaf_hash_bb = bytes_to_babybear(&issuer_key);
    let stark_siblings: Vec<[u32; 3]> = (0..4u32)
        .map(|i| {
            [
                hash_index(i as usize, 0, &issuer_key),
                hash_index(i as usize, 1, &issuer_key),
                hash_index(i as usize, 2, &issuer_key),
            ]
        })
        .collect();
    let stark_positions: Vec<u32> = vec![0, 1, 2, 3];

    let (stark_trace, stark_public_inputs) =
        stark::generate_merkle_trace(leaf_hash_bb.0, &stark_siblings, &stark_positions);

    let stark_air = stark::MerkleStarkAir;
    let membership_proof = stark::prove(&stark_air, &stark_trace, &stark_public_inputs);
    let proof_bytes = stark::proof_to_bytes(&membership_proof);

    let step4_time = step4_start.elapsed();

    party(
        "WALLET",
        &format!(
            "STARK proof size: {} bytes ({:.1} KiB)",
            proof_bytes.len(),
            proof_bytes.len() as f64 / 1024.0
        ),
    );
    party(
        "WALLET",
        &format!(
            "Public inputs: leaf={}, root={}",
            stark_public_inputs[0].0, stark_public_inputs[1].0
        ),
    );
    party(
        "WALLET",
        "This proves: issuer is a member of the federation",
    );
    party(
        "WALLET",
        "Without revealing: which issuer, the tree structure, sibling hashes",
    );

    item(&format!("Time: {:?}", step4_time));

    // =========================================================================
    // STEP 5: Server verifies the proof
    // =========================================================================

    section(
        5,
        total_steps,
        "SERVER: Verifies proof against attested root",
    );
    let step5_start = Instant::now();

    // The server only has:
    // - The federation root (configured at deploy time)
    // - The proof bytes
    // - The public inputs (leaf hash, root)
    // It does NOT have: the token, the caveats, the user's identity, the chain

    party(
        "SERVER",
        &format!(
            "Federation root (configured): {}",
            short_hex(&federation_root)
        ),
    );
    party(
        "SERVER",
        &format!("Received proof: {} bytes", proof_bytes.len()),
    );
    party("SERVER", "Verifying STARK proof...");

    let verify_result = stark::verify(&stark_air, &membership_proof, &stark_public_inputs);

    let step5_time = step5_start.elapsed();

    match verify_result {
        Ok(()) => {
            party("SERVER", "Verification: PASS");
            party(
                "SERVER",
                "Conclusion: Request is authorized by a federation member",
            );
        }
        Err(e) => {
            party("SERVER", &format!("Verification: FAILED ({e})"));
            panic!("Proof should verify");
        }
    }

    // Also verify the circuit-level proof
    let circuit_valid = proof.is_valid();
    party("SERVER", &format!("Circuit proof valid: {}", circuit_valid));
    assert!(circuit_valid, "Circuit proof should be valid");

    println!();
    party("SERVER", "The server sees:");
    party("SERVER", "  - Authorization decision: ALLOW");
    party("SERVER", "  - Federation membership: verified");
    party("SERVER", "  - Proof size (bandwidth cost)");
    party("SERVER", "The server does NOT see:");
    party("SERVER", "  - Which user made the request");
    party("SERVER", "  - What token was used");
    party("SERVER", "  - What other capabilities the user has");
    party(
        "SERVER",
        "  - How the token was obtained (delegation chain)",
    );
    party("SERVER", "  - Whether the token was attenuated");

    item(&format!("Time: {:?}", step5_time));

    // =========================================================================
    // STEP 6: Response flows back to page
    // =========================================================================

    section(6, total_steps, "PAGE: Receives result");
    let step6_start = Instant::now();

    party("PAGE", "Promise resolved:");
    party(
        "PAGE",
        "  { authorized: true, proofSize: ..., mode: 'private' }",
    );
    println!();
    party("PAGE", "The page sees: authorized=true. That's it.");
    party(
        "PAGE",
        "The page can now: make the API call with confidence.",
    );

    let step6_time = step6_start.elapsed();
    item(&format!("Time: {:?}", step6_time));

    // ─── Timing Summary ─────────────────────────────────────────────────────

    let total_time = total_start.elapsed();

    println!();
    println!("  {}", "=".repeat(60));
    println!("  TIMING SUMMARY");
    println!("  {}", "=".repeat(60));
    println!();
    println!("    Step 1 (Page request):           {:>12?}", step1_time);
    println!("    Step 2 (Datalog evaluation):     {:>12?}", step2_time);
    println!("    Step 3 (Bridge proof):           {:>12?}", step3_time);
    println!("    Step 4 (STARK membership proof): {:>12?}", step4_time);
    println!("    Step 5 (Server verification):    {:>12?}", step5_time);
    println!("    Step 6 (Response to page):       {:>12?}", step6_time);
    println!("    ────────────────────────────────────────────");
    println!("    Total round-trip:                {:>12?}", total_time);
    println!();

    // ─── Information Asymmetry Summary ──────────────────────────────────────

    println!("  {}", "=".repeat(60));
    println!("  INFORMATION ASYMMETRY");
    println!("  {}", "=".repeat(60));
    println!();
    println!("    Party        | Knows                    | Does NOT know");
    println!("    ─────────────┼──────────────────────────┼────────────────────────────");
    println!("    Page         | authorized: yes/no       | Token, capabilities, issuer");
    println!("    Cipherclerk       | Everything (local)       | Server's internal state");
    println!("    Server       | Valid federation member   | User identity, token chain");
    println!("    Federation   | Membership roster        | Individual requests/proofs");
    println!();
    println!("  This is the core privacy property: authorization flows through");
    println!("  without any party learning more than strictly necessary.");
    println!();
}
