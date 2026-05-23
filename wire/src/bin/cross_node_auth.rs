//! Cross-node authorization demo: Two separate pyana-node instances communicating
//! over real TCP, proving the DISTRIBUTED part works.
//!
//! Scenario:
//! 1. Start Node A (Org A's federation node) -- binds TCP
//! 2. Start Node B (Org B's verification server) -- binds TCP
//! 3. Agent at Node A: mints token for cross-org delegation
//! 4. Agent at Node A: generates a STARK proof (using prove())
//! 5. Agent connects to Node B over TCP and submits the presentation
//! 6. Node B: verifies the STARK proof against its known federation root
//! 7. Node B: returns AUTHORIZED or DENIED
//! 8. Show: tampered proof -> DENIED
//! 9. Show: wrong federation root -> DENIED
//! 10. Print timing: proof generation time, network round-trip, verification time
//!
//! Run with:
//!   cargo run -p pyana-wire --bin cross_node_auth

use pyana_bridge::present::{BridgePresentationBuilder, bytes_to_babybear, hash_index};
use pyana_circuit::BabyBear;
use pyana_circuit::poseidon2;
use pyana_token::{AuthRequest, MacaroonToken};
use pyana_wire::prelude::*;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Instant;

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

/// A proof verifier that accepts only Poseidon2 AIR proofs.
///
/// This mirrors the verification logic in `BridgePresentationProof::verify_issuer_stark()`.
/// The legacy linear AIR is intentionally excluded because it is a benchmark circuit,
/// not a production soundness boundary.
#[derive(Clone, Debug)]
struct Poseidon2StarkVerifier;

impl ProofVerifier for Poseidon2StarkVerifier {
    fn verify(&self, proof_bytes: &[u8], action: &str, resource: &str) -> Result<bool, String> {
        let proof = pyana_circuit::stark::proof_from_bytes(proof_bytes)?;
        let public_inputs: Vec<pyana_circuit::BabyBear> = proof
            .public_inputs
            .iter()
            .map(|&v| pyana_circuit::BabyBear::new(v))
            .collect();

        // Verify action binding: the proof must contain the canonical 4-element
        // commitment to (action, resource) at pi[2..6], computed via `compute_action_binding`.
        let expected_binding = pyana_circuit::compute_action_binding(action, resource);
        if public_inputs.len() < 2 + pyana_circuit::ACTION_BINDING_WIDTH {
            return Ok(false);
        }
        for i in 0..pyana_circuit::ACTION_BINDING_WIDTH {
            if public_inputs[2 + i] != expected_binding[i] {
                return Ok(false); // Proof not bound to this (action, resource)
            }
        }

        // Production verification uses the DSL Merkle Poseidon2 circuit.
        let circuit = pyana_dsl_runtime::descriptors::merkle_poseidon2_circuit();
        match pyana_circuit::stark::verify(&circuit, &proof, &public_inputs) {
            Ok(()) => Ok(true),
            Err(_) => Ok(false),
        }
    }
}

/// Compute the Poseidon2-based federation root for a given issuer key.
///
/// This builds an 8-level synthetic Poseidon2 Merkle tree using deterministic
/// siblings derived from the issuer key. In production, this root would come
/// from the federation consensus (attested root signed by quorum).
fn compute_federation_root(issuer_key: &[u8; 32]) -> (BabyBear, [u8; 32]) {
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

    // Encode the BabyBear root as a 32-byte value for the wire protocol.
    let mut root_bytes = [0u8; 32];
    root_bytes[..4].copy_from_slice(&current.0.to_le_bytes());
    (current, root_bytes)
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
    // Setup: Compute the shared federation root
    // =========================================================================

    // Issuer key for Org A.
    let issuer_key: [u8; 32] = *blake3::hash(b"orgA-issuer-key-2026").as_bytes();

    // Compute the Poseidon2-based federation root. In production, this root is
    // maintained by the federation consensus layer and all nodes agree on it via
    // BFT consensus (see multi_node demo). Here we compute it deterministically.
    let (federation_root_bb, federation_root) = compute_federation_root(&issuer_key);

    // =========================================================================
    // Phase 1: Start Node A (Org A) and Node B (Org B) on separate TCP ports
    // =========================================================================
    println!("[Phase 1] Starting two separate organization nodes...");
    println!();

    // Node A: The requesting organization's federation node.
    let config_a = SiloConfig::new("orgA.example.com");
    let server_a = SiloServer::new("127.0.0.1:0".parse().unwrap(), config_a);

    let (addr_tx_a, addr_rx_a) = tokio::sync::oneshot::channel();
    tokio::spawn(async move {
        server_a.run_with_addr(addr_tx_a).await.unwrap();
    });
    let addr_a: SocketAddr = addr_rx_a.await.unwrap();

    // Node B: The verifying organization's server.
    // Pre-seeded with the federation root that both organizations agreed on
    // (in production, this comes from the BFT consensus attested root).
    let config_b =
        SiloConfig::new("orgB.example.com").with_verifier(Arc::new(Poseidon2StarkVerifier));
    let state_b = SiloState {
        federation_root,
        height: 1,
        member_count: 4,
        revoked_tokens: Vec::new(),
        root_signatures: Vec::new(),
        threshold_qc: None,
        last_root_update: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0),
    };
    let server_b = SiloServer::with_state("127.0.0.1:0".parse().unwrap(), config_b, state_b);

    let (addr_tx_b, addr_rx_b) = tokio::sync::oneshot::channel();
    tokio::spawn(async move {
        server_b.run_with_addr(addr_tx_b).await.unwrap();
    });
    let addr_b: SocketAddr = addr_rx_b.await.unwrap();

    println!(
        "  [Node A] orgA.example.com listening on 127.0.0.1:{}",
        addr_a.port()
    );
    println!(
        "  [Node B] orgB.example.com listening on 127.0.0.1:{}",
        addr_b.port()
    );
    println!(
        "  [Federation] Shared Poseidon2 root: {}...",
        short_hex(&federation_root, 8)
    );
    println!();

    // =========================================================================
    // Phase 2: Agent at Node A mints a delegation token
    // =========================================================================
    println!("[Phase 2] Agent at Node A: minting token for cross-org access...");
    println!();

    // Mint a root token granting full delegation rights.
    // The unrestricted token exercises the full bridge + circuit + prover pipeline.
    let token = MacaroonToken::mint(issuer_key, b"cross-org-agent-001", "orgA.example.com");
    println!(
        "  [Node A] Minted delegation token (issuer: {}...)",
        short_hex(&issuer_key, 4)
    );
    println!("  [Node A] Token grants: full cross-org delegation (unrestricted root)");
    println!();

    // =========================================================================
    // Phase 3: Generate a STARK proof using prove()
    // =========================================================================
    println!("[Phase 3] Generating Poseidon2 STARK proof...");
    println!();

    let proof_start = Instant::now();

    // Build the presentation proof using the bridge.
    // The BridgePresentationBuilder orchestrates:
    //   1. Token -> committed fact set (unrestricted)
    //   2. Poseidon2 Merkle membership proof for issuer key in federation tree
    //   3. Authorization evaluation (UNRESTRICTED policy rule fires)
    //   4. Real STARK proof generation with collision-resistant Poseidon2 constraints
    let mut builder = BridgePresentationBuilder::new_with_root_bb(
        issuer_key,
        federation_root,
        federation_root_bb,
    );
    builder.set_root_token(token);

    // Create the authorization request.
    // The unrestricted token satisfies any action request via the UNRESTRICTED rule.
    let auth_request = AuthRequest {
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
    // This produces a cryptographically valid proof of issuer membership in the
    // federation tree, using collision-resistant Poseidon2 hash constraints.
    let presentation = builder
        .prove(&auth_request)
        .expect("prove() should succeed");

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
    // Phase 4: Connect to Node B over TCP and present the proof
    // =========================================================================
    println!("[Phase 4] Cross-node presentation: Node A -> Node B over TCP...");
    println!();

    let network_start = Instant::now();

    // Connect to Node B.
    let mut conn = PeerConnection::connect(&addr_b.to_string()).await.unwrap();

    // Handshake: announce ourselves to Node B.
    let hello = WireMessage::Hello {
        node_id: *blake3::hash(b"orgA.example.com").as_bytes(),
        node_name: "orgA.example.com".to_string(),
        protocol_version: PROTOCOL_VERSION,
        capabilities: vec!["present".to_string()],
    };
    conn.send(hello).await.unwrap();
    let welcome = conn.recv().await.unwrap();

    match &welcome {
        WireMessage::Welcome {
            federation_root: peer_root,
            node_name,
            ..
        } => {
            println!(
                "  [Node A] Connected to {} (root: {}...)",
                node_name,
                short_hex(peer_root, 4)
            );
            // Confirm both nodes agree on the federation root.
            assert_eq!(
                *peer_root, federation_root,
                "federation roots must match between nodes"
            );
            println!("  [Node A] Federation root matches -- proceeding with presentation");
        }
        other => panic!("expected Welcome, got {other:?}"),
    }

    // Present the STARK proof to Node B.
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

    println!(
        "  [Node A] Sending {} proof to Node B...",
        format_size(stark_proof_bytes.len())
    );

    let send_start = Instant::now();
    conn.send(present_msg).await.unwrap();
    let result = conn.recv().await.unwrap();
    let rtt = send_start.elapsed();

    let _network_time = network_start.elapsed();

    match &result {
        WireMessage::PresentationResult {
            accepted, reason, ..
        } => {
            if *accepted {
                println!("  [Node B] Received proof, verifying with Poseidon2 STARK...");
                println!("  [Node B] STARK verification: PASSED");
                println!("  [Node B] Authorization result: AUTHORIZED");
            } else {
                panic!(
                    "valid proof should be ACCEPTED, got DENIED: {}",
                    reason.as_deref().unwrap_or("unknown")
                );
            }
        }
        other => panic!("expected PresentationResult, got {other:?}"),
    }

    println!(
        "  [Timing] Network round-trip (send+verify+response): {:.2}ms",
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
        "  [Attacker] Tampered {} bytes at positions {}..{}",
        16,
        mid,
        mid + 16
    );

    let mut conn2 = PeerConnection::connect(&addr_b.to_string()).await.unwrap();
    conn2
        .send(WireMessage::Hello {
            node_id: *blake3::hash(b"attacker.evil").as_bytes(),
            node_name: "attacker.evil".to_string(),
            protocol_version: PROTOCOL_VERSION,
            capabilities: vec!["present".to_string()],
        })
        .await
        .unwrap();
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
            accepted, reason, ..
        } => {
            assert!(!accepted, "tampered proof should be REJECTED");
            println!(
                "  [Node B] Tampered proof: DENIED ({})",
                reason.as_deref().unwrap_or("proof verification failed")
            );
        }
        other => panic!("expected PresentationResult, got {other:?}"),
    }
    println!(
        "  [Timing] Tampered verification RTT: {:.2}ms",
        tamper_rtt.as_secs_f64() * 1000.0
    );
    drop(conn2);
    println!();

    // =========================================================================
    // Phase 6: Wrong federation root -> DENIED
    // =========================================================================
    println!("[Phase 6] Wrong federation root -> should be DENIED...");
    println!();

    // An attacker presents a valid proof but claims a different federation root.
    // Node B checks that the presented root matches its own attested root.
    let wrong_root = *blake3::hash(b"wrong-federation-root-evil-network").as_bytes();
    println!(
        "  [Attacker] Presenting valid proof with wrong root: {}...",
        short_hex(&wrong_root, 8)
    );

    let mut conn3 = PeerConnection::connect(&addr_b.to_string()).await.unwrap();
    conn3
        .send(WireMessage::Hello {
            node_id: *blake3::hash(b"attacker.evil").as_bytes(),
            node_name: "attacker.evil".to_string(),
            protocol_version: PROTOCOL_VERSION,
            capabilities: vec!["present".to_string()],
        })
        .await
        .unwrap();
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
            accepted, reason, ..
        } => {
            assert!(!accepted, "wrong federation root should be REJECTED");
            println!(
                "  [Node B] Wrong federation root: DENIED ({})",
                reason.as_deref().unwrap_or("stale federation root")
            );
        }
        other => panic!("expected PresentationResult, got {other:?}"),
    }
    println!(
        "  [Timing] Wrong-root rejection RTT: {:.2}ms",
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
    println!("    Transport: TCP (real sockets, real serialization)");
    println!();
    println!("  Proof System:");
    println!("    Type:       Real STARK (Poseidon2 collision-resistant hash)");
    println!(
        "    Proof size: {} ({} bytes)",
        format_size(stark_proof_bytes.len()),
        stark_proof_bytes.len()
    );
    println!("    Generation: {:.1}ms", proof_time.as_secs_f64() * 1000.0);
    println!();
    println!("  Authorization Results:");
    println!("    Valid proof + correct root:   AUTHORIZED");
    println!("    Tampered proof bytes:         DENIED (proof verification failed)");
    println!("    Wrong federation root:        DENIED (stale federation root)");
    println!();
    println!("  Timing Breakdown:");
    println!(
        "    STARK proof generation:      {:.1}ms",
        proof_time.as_secs_f64() * 1000.0
    );
    println!(
        "    Valid proof RTT:             {:.2}ms (includes STARK verify on Node B)",
        rtt.as_secs_f64() * 1000.0
    );
    println!(
        "    Tampered proof RTT:          {:.2}ms",
        tamper_rtt.as_secs_f64() * 1000.0
    );
    println!(
        "    Wrong root rejection RTT:    {:.2}ms (fast-path, no proof check)",
        root_rtt.as_secs_f64() * 1000.0
    );
    println!(
        "    Total demo elapsed:          {:.1}ms",
        total_elapsed.as_secs_f64() * 1000.0
    );
    println!();
    println!("==========================================================================");
    println!();
}
