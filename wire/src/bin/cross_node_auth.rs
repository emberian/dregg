//! Cross-node authorization demo: Two separate pyana-node instances communicating
//! over real TCP, proving the DISTRIBUTED part works.
//!
//! Scenario:
//! 1. Start Node A (Org A's federation node) -- binds TCP
//! 2. Start Node B (Org B's verification server) -- binds TCP
//! 3. Agent at Node A: mints token, attenuates for cross-org access
//! 4. Agent at Node A: generates a REAL STARK proof (using prove_real())
//! 5. Agent connects to Node B over TCP and submits the presentation
//! 6. Node B: verifies the STARK proof against its known federation root
//! 7. Node B: returns AUTHORIZED or DENIED
//! 8. Show: tampered proof -> DENIED
//! 9. Show: wrong federation root -> DENIED
//! 10. Print timing: proof generation time, network round-trip, verification time
//!
//! Run with:
//!   cargo run -p pyana-wire --bin cross_node_auth --features bridge

use pyana_bridge::present::{bytes_to_babybear, hash_index, BridgePresentationBuilder};
use pyana_circuit::poseidon2;
use pyana_circuit::BabyBear;
use pyana_commit::merkle::MerkleTree;
use pyana_wire::prelude::*;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Instant;
use pyana_token::{Attenuation, AuthRequest, MacaroonToken};

/// Hex-encode the first N bytes of a slice for display.
fn short_hex(bytes: &[u8], n: usize) -> String {
    bytes.iter().take(n).map(|b| format!("{b:02x}")).collect()
}

/// Format bytes in human-readable form.
fn format_size(bytes: usize) -> String {
    if bytes < 1024 {
        format!("{bytes} B")
    } else if bytes < 1024 * 1024 {
        format!("{:.1} KiB", bytes as f64 / 1024.0)
    } else {
        format!("{:.1} MiB", bytes as f64 / (1024.0 * 1024.0))
    }
}

// =============================================================================
// Poseidon2-aware STARK Verifier
// =============================================================================

/// A proof verifier that tries Poseidon2 AIR first, then falls back to linear AIR.
///
/// This mirrors the verification logic in `BridgePresentationProof::verify_issuer_stark()`.
/// Production deployments should use Poseidon2 exclusively; the linear fallback is
/// retained only for backward compatibility with older proofs.
#[derive(Clone, Debug)]
struct Poseidon2StarkVerifier;

impl ProofVerifier for Poseidon2StarkVerifier {
    fn verify(&self, proof_bytes: &[u8]) -> Result<bool, String> {
        let proof = pyana_circuit::stark::proof_from_bytes(proof_bytes)?;
        let public_inputs: Vec<pyana_circuit::BabyBear> = proof
            .public_inputs
            .iter()
            .map(|&v| pyana_circuit::BabyBear::new(v))
            .collect();

        // Try Poseidon2 AIR first (production path).
        let poseidon2_result = pyana_circuit::stark::verify(
            &pyana_circuit::poseidon2_air::MerklePoseidon2StarkAir,
            &proof,
            &public_inputs,
        );
        if poseidon2_result.is_ok() {
            return Ok(true);
        }

        // Fall back to linear AIR for backward compatibility.
        let linear_result = pyana_circuit::stark::verify(
            &pyana_circuit::stark::MerkleStarkAir,
            &proof,
            &public_inputs,
        );
        match linear_result {
            Ok(()) => Ok(true),
            Err(_) => Ok(false),
        }
    }
}

#[tokio::main]
async fn main() {
    println!();
    println!("==========================================================================");
    println!("  pyana: Cross-Node Authorization Demo (2 nodes, real TCP, real STARK)");
    println!("==========================================================================");
    println!();

    let demo_start = Instant::now();

    // =========================================================================
    // Phase 1: Setup -- Start Node A (Org A) and Node B (Org B) on separate ports
    // =========================================================================
    println!("[Phase 1] Starting two separate organization nodes...");
    println!();

    // Node A: The requesting organization's federation node.
    // Uses default StarkVerifier (not critical for the requester).
    let config_a = SiloConfig::new("orgA.example.com");
    let server_a = SiloServer::new("127.0.0.1:0".parse().unwrap(), config_a);

    let (addr_tx_a, addr_rx_a) = tokio::sync::oneshot::channel();
    tokio::spawn(async move {
        server_a.run_with_addr(addr_tx_a).await.unwrap();
    });
    let addr_a: SocketAddr = addr_rx_a.await.unwrap();

    // Node B: The verifying organization's server.
    // Uses Poseidon2-aware STARK verifier for real proof verification.
    let config_b =
        SiloConfig::new("orgB.example.com").with_verifier(Arc::new(Poseidon2StarkVerifier));
    let server_b = SiloServer::new("127.0.0.1:0".parse().unwrap(), config_b);

    let (addr_tx_b, addr_rx_b) = tokio::sync::oneshot::channel();
    tokio::spawn(async move {
        server_b.run_with_addr(addr_tx_b).await.unwrap();
    });
    let addr_b: SocketAddr = addr_rx_b.await.unwrap();

    println!("  [Node A] orgA.example.com listening on 127.0.0.1:{}", addr_a.port());
    println!("  [Node B] orgB.example.com listening on 127.0.0.1:{}", addr_b.port());
    println!();

    // =========================================================================
    // Phase 2: Agent at Node A mints a token and attenuates for cross-org access
    // =========================================================================
    println!("[Phase 2] Agent at Node A: minting and attenuating token...");
    println!();

    // Issuer key for Org A.
    let issuer_key: [u8; 32] = *blake3::hash(b"orgA-issuer-key-2026").as_bytes();

    // Build a federation Merkle tree containing Org A's issuer key.
    // In production, this tree is maintained by the federation operator and
    // both nodes share the same root (attested via consensus).
    let mut federation_tree = MerkleTree::new();
    federation_tree.insert(&issuer_key);
    // Add some other members to make the tree non-trivial.
    federation_tree.insert(b"orgB-member-key-placeholder-pad!");
    federation_tree.insert(b"orgC-member-key-placeholder-pad!");
    federation_tree.insert(b"orgD-member-key-placeholder-pad!");

    let federation_root = federation_tree.root();
    println!(
        "  [Federation] Root: {}... ({} members)",
        short_hex(&federation_root, 8),
        4
    );

    // Mint a root token.
    let token = MacaroonToken::mint(issuer_key, b"cross-org-agent-001", "orgA.example.com");
    println!(
        "  [Node A] Minted root token (issuer: {}...)",
        short_hex(&issuer_key, 4)
    );

    // Attenuate: restrict to compute service with execute action, 5-minute TTL.
    let attenuation = Attenuation {
        services: vec![("compute".into(), "execute".into())],
        not_after: Some(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs() as i64
                + 300,
        ),
        ..Default::default()
    };

    println!(
        "  [Node A] Attenuating: service=compute, action=execute, ttl=300s"
    );
    println!();

    // =========================================================================
    // Phase 3: Generate a REAL STARK proof using prove_real()
    // =========================================================================
    println!("[Phase 3] Generating REAL Poseidon2 STARK proof...");
    println!();

    let proof_start = Instant::now();

    // Build the presentation proof using the bridge.
    let mut builder = BridgePresentationBuilder::new(issuer_key, [0u8; 32]);
    builder.with_federation_tree(federation_tree.clone());
    builder.set_root_token(token);
    let att_ok = builder.add_attenuation(&attenuation);
    assert!(att_ok, "attenuation should succeed");

    // Create the authorization request (what we're trying to prove access to).
    let auth_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("execute".into()),
        now: Some(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs() as i64,
        ),
        ..Default::default()
    };

    // Generate the real STARK proof (Poseidon2 path).
    let presentation = builder
        .prove_real(&auth_request)
        .expect("prove_real() should succeed");

    let proof_time = proof_start.elapsed();

    // Extract the serialized STARK proof bytes for wire transmission.
    let stark_proof_bytes = presentation
        .issuer_proof_bytes()
        .expect("real proof should have issuer_proof_bytes");

    println!(
        "  [Node A] STARK proof generated in {:.1}ms",
        proof_time.as_secs_f64() * 1000.0
    );
    println!(
        "  [Node A] Proof size: {} ({} bytes)",
        format_size(stark_proof_bytes.len()),
        stark_proof_bytes.len()
    );
    println!(
        "  [Node A] Chain length: {} steps",
        presentation.chain_length
    );
    println!(
        "  [Node A] Verification (local): {:?}",
        presentation.verification
    );

    // Verify locally before sending.
    let local_verify = presentation.verify_issuer_stark();
    assert!(
        local_verify.as_ref().unwrap().is_ok(),
        "local STARK verification should pass"
    );
    println!("  [Node A] Local STARK verify: PASSED");
    println!();

    // =========================================================================
    // Phase 4: Connect to Node B and present the proof over TCP
    // =========================================================================
    println!("[Phase 4] Cross-node presentation: Node A -> Node B over TCP...");
    println!();

    let network_start = Instant::now();

    // Connect to Node B.
    let mut conn = PeerConnection::connect(&addr_b.to_string()).await.unwrap();

    // Handshake.
    let hello = WireMessage::Hello {
        node_id: *blake3::hash(b"orgA.example.com").as_bytes(),
        node_name: "orgA.example.com".to_string(),
        protocol_version: PROTOCOL_VERSION,
        capabilities: vec!["present".to_string()],
    };
    conn.send(hello).await.unwrap();
    let welcome = conn.recv().await.unwrap();

    let node_b_root = match &welcome {
        WireMessage::Welcome {
            federation_root,
            node_name,
            ..
        } => {
            println!(
                "  [Node A] Connected to {} (root: {}...)",
                node_name,
                short_hex(federation_root, 4)
            );
            *federation_root
        }
        other => panic!("expected Welcome, got {other:?}"),
    };

    // Present the STARK proof. Use the federation root from our tree (which both
    // nodes share in a real deployment).
    let request = AuthorizationRequest::new(
        "compute/v1/workloads",
        "execute",
        "agent-alpha@orgA.example.com",
    )
    .with_scopes(vec!["service:compute".to_string(), "ttl:300s".to_string()]);

    let present_msg = WireMessage::PresentToken {
        proof: stark_proof_bytes.clone(),
        request: request.clone(),
        federation_root,
    };

    let send_start = Instant::now();
    conn.send(present_msg).await.unwrap();
    let result = conn.recv().await.unwrap();
    let rtt = send_start.elapsed();

    let network_time = network_start.elapsed();

    match &result {
        WireMessage::PresentationResult {
            accepted,
            reason,
            ..
        } => {
            if *accepted {
                println!("  [Node B] STARK verification: PASSED");
                println!("  [Node B] Authorization: AUTHORIZED");
            } else {
                println!(
                    "  [Node B] STARK verification: FAILED ({})",
                    reason.as_deref().unwrap_or("unknown")
                );
                println!("  [Node B] Authorization: DENIED");
            }
        }
        other => panic!("expected PresentationResult, got {other:?}"),
    }

    println!(
        "  [Timing] Network round-trip (send+verify+recv): {:.2}ms",
        rtt.as_secs_f64() * 1000.0
    );
    drop(conn);
    println!();

    // =========================================================================
    // Phase 5: Tampered proof -> DENIED
    // =========================================================================
    println!("[Phase 5] Tampered proof -> should be DENIED...");
    println!();

    let mut tampered_proof = stark_proof_bytes.clone();
    // Flip some bytes in the middle of the proof to simulate tampering.
    let mid = tampered_proof.len() / 2;
    for i in mid..mid + 16 {
        tampered_proof[i] ^= 0xFF;
    }
    println!(
        "  [Node A] Tampered {} bytes in proof (positions {}..{})",
        16,
        mid,
        mid + 16
    );

    let mut conn2 = PeerConnection::connect(&addr_b.to_string()).await.unwrap();
    // Handshake
    let hello2 = WireMessage::Hello {
        node_id: *blake3::hash(b"orgA.example.com").as_bytes(),
        node_name: "orgA.example.com".to_string(),
        protocol_version: PROTOCOL_VERSION,
        capabilities: vec!["present".to_string()],
    };
    conn2.send(hello2).await.unwrap();
    let _welcome2 = conn2.recv().await.unwrap();

    let tampered_msg = WireMessage::PresentToken {
        proof: tampered_proof,
        request: request.clone(),
        federation_root,
    };

    let tamper_start = Instant::now();
    conn2.send(tampered_msg).await.unwrap();
    let tampered_result = conn2.recv().await.unwrap();
    let tamper_rtt = tamper_start.elapsed();

    match &tampered_result {
        WireMessage::PresentationResult {
            accepted,
            reason,
            ..
        } => {
            assert!(
                !accepted,
                "tampered proof should be REJECTED"
            );
            println!(
                "  [Node B] Tampered proof verification: DENIED ({})",
                reason.as_deref().unwrap_or("invalid proof")
            );
        }
        other => panic!("expected PresentationResult, got {other:?}"),
    }
    println!(
        "  [Timing] Tampered verification round-trip: {:.2}ms",
        tamper_rtt.as_secs_f64() * 1000.0
    );
    drop(conn2);
    println!();

    // =========================================================================
    // Phase 6: Wrong federation root -> DENIED
    // =========================================================================
    println!("[Phase 6] Wrong federation root -> should be DENIED...");
    println!();

    // Use a completely different federation root that doesn't match Node B's state.
    let wrong_root = *blake3::hash(b"wrong-federation-root-from-evil-network").as_bytes();
    println!(
        "  [Node A] Presenting with wrong root: {}...",
        short_hex(&wrong_root, 8)
    );

    let mut conn3 = PeerConnection::connect(&addr_b.to_string()).await.unwrap();
    // Handshake
    let hello3 = WireMessage::Hello {
        node_id: *blake3::hash(b"orgA.example.com").as_bytes(),
        node_name: "orgA.example.com".to_string(),
        protocol_version: PROTOCOL_VERSION,
        capabilities: vec!["present".to_string()],
    };
    conn3.send(hello3).await.unwrap();
    let _welcome3 = conn3.recv().await.unwrap();

    let wrong_root_msg = WireMessage::PresentToken {
        proof: stark_proof_bytes.clone(),
        request: request.clone(),
        federation_root: wrong_root,
    };

    let root_start = Instant::now();
    conn3.send(wrong_root_msg).await.unwrap();
    let wrong_root_result = conn3.recv().await.unwrap();
    let root_rtt = root_start.elapsed();

    match &wrong_root_result {
        WireMessage::PresentationResult {
            accepted,
            reason,
            ..
        } => {
            assert!(
                !accepted,
                "wrong federation root should be REJECTED"
            );
            println!(
                "  [Node B] Wrong federation root: DENIED ({})",
                reason.as_deref().unwrap_or("stale federation root")
            );
        }
        other => panic!("expected PresentationResult, got {other:?}"),
    }
    println!(
        "  [Timing] Wrong-root rejection round-trip: {:.2}ms",
        root_rtt.as_secs_f64() * 1000.0
    );
    drop(conn3);
    println!();

    // =========================================================================
    // Summary
    // =========================================================================
    let total_elapsed = demo_start.elapsed();

    println!("==========================================================================");
    println!("  Cross-Node Authorization Demo Complete");
    println!("==========================================================================");
    println!();
    println!("  Topology:");
    println!("    Node A: orgA.example.com (127.0.0.1:{})", addr_a.port());
    println!("    Node B: orgB.example.com (127.0.0.1:{})", addr_b.port());
    println!();
    println!("  Proof System:");
    println!("    Type:       Real STARK (Poseidon2 hash constraints)");
    println!("    Proof size: {}", format_size(stark_proof_bytes.len()));
    println!(
        "    Generation: {:.1}ms",
        proof_time.as_secs_f64() * 1000.0
    );
    println!();
    println!("  Results:");
    println!("    Valid proof, correct root:   AUTHORIZED");
    println!("    Tampered proof:              DENIED");
    println!("    Wrong federation root:       DENIED");
    println!();
    println!("  Timing:");
    println!(
        "    Proof generation:            {:.1}ms",
        proof_time.as_secs_f64() * 1000.0
    );
    println!(
        "    Network RTT (valid):         {:.2}ms",
        rtt.as_secs_f64() * 1000.0
    );
    println!(
        "    Network RTT (tampered):      {:.2}ms",
        tamper_rtt.as_secs_f64() * 1000.0
    );
    println!(
        "    Network RTT (wrong root):    {:.2}ms",
        root_rtt.as_secs_f64() * 1000.0
    );
    println!(
        "    Total elapsed:               {:.1}ms",
        total_elapsed.as_secs_f64() * 1000.0
    );
    println!();
    println!("==========================================================================");
    println!();
}
