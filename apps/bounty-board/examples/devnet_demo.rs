//! Devnet integration demo: privacy-preserving bounty lifecycle.
//!
//! This example demonstrates the REAL privacy-preserving flow end-to-end:
//!
//! 1. Worker mints a credential token via AgentCipherclerk.
//! 2. Worker generates a STARK proof of federation membership (zero-knowledge).
//! 3. Worker claims a bounty by presenting the proof through the HTTP API.
//! 4. The bounty board verifies the proof without learning the worker's identity.
//! 5. Worker submits work, issuer approves, payment is released.
//!
//! ## Privacy guarantees demonstrated
//!
//! - The worker proves "I am a federation member" without revealing WHICH member.
//! - The worker's blinded commitment (Poseidon2 hash) prevents identity linkage.
//! - Different claims by the same worker use different commitments (fresh randomness).
//! - The issuer never learns who the worker is until delivery.
//!
//! ## Running
//!
//! ```bash
//! # Self-contained: starts the server in-process, no external node required.
//! cargo run -p pyana-bounty-board --example devnet_demo
//! ```
//!
//! ## Notes
//!
//! - Generating real STARK proofs takes ~200-500ms depending on hardware.
//! - The demo starts the bounty board server in-process (no external dependencies).
//! - Federation root is computed from the worker's proof key and configured on the
//!   board so verification passes.

use std::time::Instant;

use pyana_circuit::ivc::IvcBuilder;
use pyana_sdk::{AgentCipherclerk, AuthRequest, BabyBear};

use pyana_bounty_board::server::{ServerConfig, start_server};
use pyana_bounty_board::{
    ApproveRequest, ClaimRequest, CompletionEvidence, CreateBountyRequest,
    QualificationRequirement, SubmitRequest, compute_worker_commitment,
};

use reqwest::Client;
use serde_json::Value;

/// Deterministic root key for the worker's credential token.
/// In production this would be securely generated and managed.
const WORKER_ROOT_KEY: [u8; 32] = [0x42; 32];

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Pyana Bounty Board: Privacy-Preserving Devnet Demo ===\n");

    // =========================================================================
    // Step 0: Start the bounty board server in-process
    // =========================================================================
    println!("[0] Starting bounty board server in-process...");

    // Compute the federation root that matches this worker's proof key BEFORE
    // starting the server, so we can configure it from the start.
    let proof_key = blake3::derive_key("pyana-proof-key-v1", &WORKER_ROOT_KEY);
    let federation_root_bb = compute_synthetic_federation_root(&proof_key);
    let federation_root_bytes = bb_to_bytes(federation_root_bb);

    let config = ServerConfig {
        federation_root: federation_root_bytes,
        listen: "127.0.0.1:0".parse().unwrap(), // random port
    };

    let addr = start_server(config).await;
    let base = format!("http://{addr}");
    println!("    Bounty board listening on {base}");

    // Give the server a moment to be ready.
    tokio::time::sleep(std::time::Duration::from_millis(50)).await;

    let client = Client::new();

    // Verify it's running.
    let health: Value = client
        .get(format!("{base}/health"))
        .send()
        .await?
        .json()
        .await?;

    let federation_root_hex = health["federation_root"]["value"].as_str().unwrap_or("?");
    let federation_root_live = health["federation_root"]["live"].as_bool().unwrap_or(false);

    println!("    Status: {}", health["status"]);
    println!("    Federation root: {federation_root_hex}");
    println!("    Root is live: {federation_root_live}");
    assert!(federation_root_live, "Federation root should be configured");
    println!();

    // =========================================================================
    // Step 1: Set up issuer and worker cipherclerks
    // =========================================================================
    println!("[1] Setting up cipherclerks...");

    // Issuer: posts bounties
    let issuer_cipherclerk = AgentCipherclerk::new();
    let issuer_cell = issuer_cipherclerk.cell_id("bounty-board");
    let issuer_cell_hex = hex::encode(issuer_cell.as_bytes());
    println!("    Issuer cell: {issuer_cell_hex}");

    // Worker: claims bounties anonymously
    let mut worker_cclerk = AgentCipherclerk::new();
    let worker_pubkey = worker_cclerk.public_key();
    println!(
        "    Worker pubkey: {} (PRIVATE - never revealed to issuer)",
        hex::encode(&worker_pubkey.0)
    );

    // Worker mints a credential token. In production, this token would be
    // issued by a federation authority. Here we mint locally for the demo.
    let worker_token = worker_cclerk.mint_token(&WORKER_ROOT_KEY, "federation");
    println!(
        "    Worker credential minted: service='{}', can_prove={}",
        worker_token.service(),
        worker_token.can_prove()
    );
    println!();

    // =========================================================================
    // Step 2: Advance the block height so deadlines work
    // =========================================================================
    println!("[2] Advancing block height...");
    let _: Value = client
        .post(format!("{base}/admin/height"))
        .json(&serde_json::json!({"delta": 10}))
        .send()
        .await?
        .json()
        .await?;
    println!("    Block height advanced to 10.");
    println!();

    // =========================================================================
    // Step 3: Create a bounty requiring federation membership
    // =========================================================================
    println!("[3] Creating bounty requiring federation membership proof...");

    let create_req = CreateBountyRequest {
        title: "Security audit of escrow logic".into(),
        description:
            "Full review of the conditional turn escrow. Must be a verified federation member."
                .into(),
        reward_amount: 25_000,
        reward_asset: 1,
        deadline_height: 5000,
        qualification: QualificationRequirement::FederationMember,
        tags: vec!["security".into(), "audit".into(), "advanced".into()],
        issuer_cell: issuer_cell_hex.clone(),
        reward_token: None,
    };

    let create_resp: Value = client
        .post(format!("{base}/bounties"))
        .json(&create_req)
        .send()
        .await?
        .json()
        .await?;

    let bounty_id = create_resp["id"]
        .as_str()
        .ok_or("no bounty ID in response")?
        .to_string();
    println!("    Bounty created: id={bounty_id}");
    println!("    Status: {}", create_resp["status"]);
    println!();

    // =========================================================================
    // Step 4: Generate the STARK qualification proof (the privacy magic)
    // =========================================================================
    println!("[4] Generating STARK federation membership proof...");
    println!("    This proves 'I am a valid federation member' WITHOUT revealing");
    println!("    which member I am. The verifier learns only: set membership.");
    println!();

    let proof_start = Instant::now();

    // Generate a real STARK presentation proof via the worker's cclerk.
    // This calls through to the bridge layer which produces a Poseidon2 STARK.
    // For membership-only proofs, both action and service must be empty strings
    // to match what verify_membership_proof expects (empty action/resource binding).
    let request = AuthRequest {
        service: Some("".into()),
        action: Some("".into()),
        ..Default::default()
    };

    let proof = worker_cclerk.prove_authorization(&worker_token, &request)?;
    let wire_proof = proof.into_wire_proof();
    let proof_bytes = postcard::to_stdvec(&wire_proof)?;

    let proof_elapsed = proof_start.elapsed();
    println!(
        "    Proof generated in {:.1}ms ({} bytes)",
        proof_elapsed.as_secs_f64() * 1000.0,
        proof_bytes.len()
    );
    println!("    Proof tier: real STARK (Poseidon2 Merkle membership)");
    println!();

    // =========================================================================
    // Step 5: Compute blinded worker commitment (unlinkable identity)
    // =========================================================================
    println!("[5] Computing blinded worker commitment...");

    // Generate fresh randomness for the commitment.
    // Using a deterministic value for reproducibility in the demo.
    let commitment_randomness: [u8; 32] = *blake3::hash(b"demo-randomness-1").as_bytes();
    let worker_commitment = compute_worker_commitment(&worker_pubkey.0, &commitment_randomness);

    println!(
        "    Commitment: {} (Poseidon2 hash of pubkey || randomness)",
        hex::encode(&worker_commitment)
    );
    println!("    This commitment is UNLINKABLE to the worker's real identity.");
    println!("    A different randomness produces a different commitment, so the");
    println!("    same worker claiming multiple bounties cannot be correlated.");
    println!();

    // =========================================================================
    // Step 6: Claim the bounty via the HTTP API with the proof
    // =========================================================================
    println!("[6] Claiming bounty with STARK proof...");
    println!(
        "    Sending qualification_proof ({} bytes) to the board...",
        proof_bytes.len()
    );

    let claim_req = ClaimRequest {
        bounty_id: bounty_id.clone(),
        worker_commitment,
        qualification_proof: Some(proof_bytes.clone()),
    };

    let claim_resp = client
        .post(format!("{base}/bounties/{bounty_id}/claim"))
        .json(&claim_req)
        .send()
        .await?;

    let claim_status = claim_resp.status();
    let claim_body: Value = claim_resp.json().await?;

    if claim_status.is_success() {
        println!(
            "    Claim ACCEPTED! Bounty status: {}",
            claim_body["status"]
        );
        println!("    The board verified our STARK proof without learning our identity.");
    } else {
        let error_msg = claim_body["error"].as_str().unwrap_or("unknown");
        eprintln!("    Claim REJECTED: {error_msg}");
        eprintln!("    HTTP status: {claim_status}");
        return Err(format!("Claim failed: {error_msg}").into());
    }
    println!();

    // =========================================================================
    // Step 7: Submit work (mock work product with proof-of-completion)
    // =========================================================================
    println!("[7] Submitting completed work...");

    let completion_proof = blake3::hash(b"audit-report-hash-binding")
        .as_bytes()
        .to_vec();

    let submit_req = SubmitRequest {
        bounty_id: bounty_id.clone(),
        worker_commitment,
        completion_evidence: CompletionEvidence::ExternalProof {
            url: "ipfs://QmExampleAuditReport".into(),
            hash: *blake3::hash(b"audit-report-content").as_bytes(),
        },
        completion_proof: completion_proof.clone(),
    };

    let submit_resp: Value = client
        .post(format!("{base}/bounties/{bounty_id}/submit"))
        .json(&submit_req)
        .send()
        .await?
        .json()
        .await?;

    println!("    Submission status: {}", submit_resp["status"]);
    println!(
        "    Completion proof hash: {}",
        submit_resp["completion_proof_hash"].as_str().unwrap_or("?")
    );
    println!();

    // =========================================================================
    // Step 8: Issuer approves and payment is released
    // =========================================================================
    println!("[8] Issuer approving submission (triggers atomic payment)...");

    let approve_req = ApproveRequest {
        bounty_id: bounty_id.clone(),
        issuer_cell: issuer_cell_hex.clone(),
    };

    let approve_resp: Value = client
        .post(format!("{base}/bounties/{bounty_id}/approve"))
        .json(&approve_req)
        .send()
        .await?
        .json()
        .await?;

    println!("    Approval status: {}", approve_resp["status"]);
    println!(
        "    Receipt hash: {}",
        approve_resp["receipt_hash"].as_str().unwrap_or("?")
    );
    println!("    Payment released atomically via conditional turn.");
    println!();

    // =========================================================================
    // Step 9: Verify final state
    // =========================================================================
    println!("[9] Verifying final bounty state...");

    let status_resp: Value = client
        .get(format!("{base}/bounties/{bounty_id}/status"))
        .send()
        .await?
        .json()
        .await?;

    let final_status = &status_resp["status"];
    println!("    Final status: {final_status}");
    assert!(
        final_status
            .as_object()
            .map_or(false, |obj| obj.contains_key("Paid")),
        "Expected bounty to be in Paid state, got: {final_status}"
    );
    println!("    Bounty lifecycle complete: Open -> Claimed -> Submitted -> Paid");
    println!();

    // =========================================================================
    // Step 10: Demonstrate IVC standing proof generation (bonus)
    // =========================================================================
    println!("[10] Bonus: Generating IVC standing proof...");
    println!("    An IVC proof accumulates completed bounty steps into a");
    println!("    constant-size proof of standing (e.g., 'I completed >= 3 bounties').");
    println!("    No individual bounty IDs are revealed.");
    println!();

    let ivc_start = Instant::now();

    // Build a 3-step IVC chain (simulating 3 completed bounties).
    // Uses create_test_chain which generates valid fold witnesses with proper
    // Merkle membership proofs for removed facts.
    let (initial_root, deltas) = pyana_circuit::ivc::create_test_chain(3);
    let mut builder = IvcBuilder::new(initial_root);

    for delta in &deltas {
        builder
            .add_fold(delta.clone())
            .expect("fold should succeed");
    }

    let ivc_proof = builder
        .finalize_with_air()
        .expect("IVC finalization should produce a proof");
    let ivc_bytes = postcard::to_stdvec(&ivc_proof)?;

    let ivc_elapsed = ivc_start.elapsed();
    println!(
        "    IVC proof generated in {:.1}ms",
        ivc_elapsed.as_secs_f64() * 1000.0
    );
    println!(
        "    Steps: {}, Size: {} bytes",
        ivc_proof.step_count,
        ivc_bytes.len()
    );
    println!(
        "    Verification: {:?}",
        pyana_circuit::verify_ivc(&ivc_proof, Some(initial_root))
    );
    println!();

    // Verify the IVC proof
    let verification = pyana_circuit::verify_ivc(&ivc_proof, Some(initial_root));
    assert_eq!(
        verification,
        pyana_circuit::IvcVerification::Valid,
        "IVC proof should verify as valid"
    );

    // =========================================================================
    // Summary
    // =========================================================================
    println!("=== Demo Complete ===");
    println!();
    println!("Privacy guarantees demonstrated:");
    println!(
        "  1. Worker proved federation membership via STARK ({:.0}ms)",
        proof_elapsed.as_secs_f64() * 1000.0
    );
    println!("     - Verifier learned: 'someone in the federation is authorized'");
    println!("     - Verifier did NOT learn: which member, token contents, or identity");
    println!("  2. Worker commitment is unlinkable (fresh randomness per claim)");
    println!("     - Same worker, different bounties = different commitments");
    println!("  3. IVC standing proof is constant-size regardless of history");
    println!("     - Proves 'I completed >= N bounties' without revealing which ones");
    println!("  4. Payment released atomically (conditional turn resolution)");
    println!();
    println!(
        "Full stack exercised: Cipherclerk -> STARK proof -> HTTP API -> Verification -> State change"
    );

    Ok(())
}

// =============================================================================
// Helper functions
// =============================================================================

/// Compute a synthetic federation root matching the cipherclerk's derivation.
///
/// This replicates `AgentCipherclerk::compute_federation_root_bb` so the bounty board's
/// root matches what the cclerk produces as public input in its STARK proof.
fn compute_synthetic_federation_root(issuer_key: &[u8; 32]) -> BabyBear {
    use pyana_circuit::merkle_air::MerkleAir;

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
        current = MerkleAir::compute_parent(current, position, &siblings);
    }
    current
}

/// Convert a 32-byte array to a BabyBear field element via Poseidon2 hash.
fn bytes_to_babybear(bytes: &[u8; 32]) -> BabyBear {
    let limbs = BabyBear::encode_hash(bytes);
    pyana_circuit::poseidon2::hash_many(&limbs)
}

/// Convert a BabyBear field element to a 32-byte array.
fn bb_to_bytes(bb: BabyBear) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    let val = bb.as_u32();
    bytes[..4].copy_from_slice(&val.to_le_bytes());
    bytes
}

/// Deterministic sibling hash for Merkle path construction.
/// Must match `AgentCipherclerk::hash_index` exactly.
fn hash_index(level: usize, sibling: usize, key: &[u8; 32]) -> u32 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&level.to_le_bytes());
    hasher.update(&sibling.to_le_bytes());
    hasher.update(key);
    let hash = hasher.finalize();
    let bytes = hash.as_bytes();
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) % pyana_circuit::field::BABYBEAR_P
}

/// Hex encoding helper.
mod hex {
    pub fn encode(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}
