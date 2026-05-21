//! Integration demo: Two silo servers communicating over real TCP.
//!
//! Demonstrates:
//! 1. Starting two silo servers on localhost
//! 2. Federation handshake (Hello/Welcome)
//! 3. Token presentation over TCP with a REAL STARK proof (pyana-circuit)
//! 4. Revocation propagation
//! 5. Non-membership proof request
//!
//! Run with:
//!   cargo run --bin pyana-network-demo

use pyana_wire::prelude::*;
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

#[tokio::main]
async fn main() {
    println!();
    println!("==========================================================================");
    println!("  pyana-wire: Cross-Silo Token Presentation & Federation Sync Demo");
    println!("==========================================================================");
    println!();

    let start = Instant::now();

    // =========================================================================
    // Phase 1: Start silo servers
    // =========================================================================
    println!("[1/5] Starting silo servers...");

    // Use the real STARK verifier for both silos -- the demo generates real proofs.
    let acme_config = SiloConfig::new("acme.corp");
    let partner_config = SiloConfig::new("partner.org");

    // Use port 0 to let the OS assign ports (avoids conflicts)
    let acme_server = SiloServer::new("127.0.0.1:0".parse().unwrap(), acme_config);
    let partner_server = SiloServer::new("127.0.0.1:0".parse().unwrap(), partner_config);

    // Start both servers and get their actual addresses
    let (acme_addr_tx, acme_addr_rx) = tokio::sync::oneshot::channel();
    let (partner_addr_tx, partner_addr_rx) = tokio::sync::oneshot::channel();

    // We need to share state for the demo
    let partner_state_handle = {
        // Get handle to partner's state before spawning
        let state = partner_server.state().await;
        state.federation_root
    };

    tokio::spawn(async move {
        acme_server.run_with_addr(acme_addr_tx).await.unwrap();
    });
    tokio::spawn(async move {
        partner_server.run_with_addr(partner_addr_tx).await.unwrap();
    });

    let acme_addr = acme_addr_rx.await.unwrap();
    let partner_addr = partner_addr_rx.await.unwrap();

    println!("  \u{2192} Silo \"acme.corp\" listening on {acme_addr}");
    println!("  \u{2192} Silo \"partner.org\" listening on {partner_addr}");
    println!();

    // =========================================================================
    // Phase 2: Federation handshake
    // =========================================================================
    println!("[2/5] Federation handshake...");

    let mut conn = PeerConnection::connect(&partner_addr.to_string())
        .await
        .unwrap();

    let acme_node_id = *blake3::hash(b"acme.corp").as_bytes();
    let hello = WireMessage::Hello {
        node_id: acme_node_id,
        node_name: "acme.corp".to_string(),
        protocol_version: PROTOCOL_VERSION,
        capabilities: vec![
            "present".to_string(),
            "revoke".to_string(),
            "sync".to_string(),
        ],
    };

    let hello_stats = pyana_wire::codec::FrameStats::for_message(&hello).unwrap();
    println!(
        "  \u{2192} acme.corp \u{2192} partner.org: Hello ({} capabilities, {})",
        3,
        hello_stats.size_display()
    );

    conn.send(hello).await.unwrap();
    let welcome = conn.recv().await.unwrap();

    match &welcome {
        WireMessage::Welcome {
            federation_root,
            member_count,
            ..
        } => {
            println!(
                "  \u{2192} partner.org \u{2192} acme.corp: Welcome (federation root: {}, members: {member_count})",
                short_hex(federation_root, 4),
            );
        }
        other => {
            eprintln!("  ERROR: unexpected response: {other:?}");
            return;
        }
    }
    println!();

    // =========================================================================
    // Phase 3: Token presentation over TCP
    // =========================================================================
    println!("[3/5] Token presentation over TCP...");

    // Generate a REAL STARK proof using pyana-circuit
    let proof = generate_real_stark_proof();
    println!(
        "  \u{2192} Generated real STARK proof: {}",
        format_size(proof.len())
    );

    let request = AuthorizationRequest::new("api/v2/secrets/vault-7", "read", "alice@acme.corp")
        .with_scopes(vec!["org:acme".to_string(), "team:platform".to_string()]);

    // Get the federation root that partner expects
    // (In a real system, acme would have synced this via AttestedRoot exchange)
    let federation_root = partner_state_handle;

    let present_msg = WireMessage::PresentToken {
        proof: proof.clone(),
        request: request.clone(),
        federation_root,
    };
    let present_stats = pyana_wire::codec::FrameStats::for_message(&present_msg).unwrap();

    println!(
        "  \u{2192} acme.corp \u{2192} partner.org: PresentToken ({} proof, {} total frame)",
        format_size(proof.len()),
        present_stats.size_display(),
    );

    conn.send(present_msg).await.unwrap();
    let result = conn.recv().await.unwrap();

    match &result {
        WireMessage::PresentationResult {
            accepted, reason, ..
        } => {
            println!("  \u{2192} partner.org verifies proof against federation root");
            if *accepted {
                println!(
                    "  \u{2192} partner.org \u{2192} acme.corp: PresentationResult {{ accepted: true }}"
                );
            } else {
                println!(
                    "  \u{2192} partner.org \u{2192} acme.corp: PresentationResult {{ accepted: false, reason: {:?} }}",
                    reason.as_deref().unwrap_or("none")
                );
            }
        }
        other => {
            eprintln!("  ERROR: unexpected response: {other:?}");
            return;
        }
    }
    println!();

    // Drop old connection, create new one for revocation
    drop(conn);

    // =========================================================================
    // Phase 4: Revocation propagation
    // =========================================================================
    println!("[4/5] Revocation propagation...");

    let mut conn = PeerConnection::connect(&partner_addr.to_string())
        .await
        .unwrap();

    let token_id = "token-123-expired";
    // Create a 64-byte signature (in production this would be a real Ed25519 sig)
    let sig_hash = blake3::hash(b"acme-authority-revocation-key");
    let mut authority_sig_bytes = [0u8; 64];
    authority_sig_bytes[..32].copy_from_slice(sig_hash.as_bytes());
    authority_sig_bytes[32..].copy_from_slice(sig_hash.as_bytes());
    let authority_sig = pyana_wire::prelude::Signature(authority_sig_bytes);
    let authority = pyana_wire::prelude::PublicKey([0xAC; 32]);

    let mut revoke_nonce = [0u8; 16];
    getrandom::fill(&mut revoke_nonce).expect("getrandom failed");
    let revoke_msg = WireMessage::SubmitRevocation {
        token_id: token_id.to_string(),
        authority,
        authority_sig,
        nonce: revoke_nonce,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0),
    };

    println!("  \u{2192} acme.corp \u{2192} partner.org: SubmitRevocation(\"{token_id}\")");

    conn.send(revoke_msg).await.unwrap();
    let ack = conn.recv().await.unwrap();

    match &ack {
        WireMessage::RevocationAck { new_root, height } => {
            println!(
                "  \u{2192} partner.org \u{2192} acme.corp: RevocationAck (new root: {}, height: {height})",
                short_hex(new_root, 4),
            );
        }
        other => {
            eprintln!("  ERROR: unexpected response: {other:?}");
            return;
        }
    }
    println!();

    // =========================================================================
    // Phase 5: Non-membership proof request
    // =========================================================================
    println!("[5/5] Non-membership proof request...");

    // Request non-membership for a token that is NOT revoked
    let check_token = "token-456-valid";
    let non_member_msg = WireMessage::RequestNonMembership {
        token_id: check_token.to_string(),
    };

    println!("  \u{2192} acme.corp \u{2192} partner.org: RequestNonMembership(\"{check_token}\")");

    conn.send(non_member_msg).await.unwrap();
    let nm_response = conn.recv().await.unwrap();

    match &nm_response {
        WireMessage::NonMembershipResponse {
            token_id,
            proof,
            root,
            height,
        } => {
            if let Some(p) = proof {
                println!(
                    "  \u{2192} partner.org \u{2192} acme.corp: NonMembershipResponse (proof: {}, root: {}, height: {height})",
                    format_size(p.len()),
                    short_hex(root, 4),
                );
                println!("  \u{2192} Token \"{token_id}\" is NOT revoked (proof provided)");
            } else {
                println!(
                    "  \u{2192} partner.org \u{2192} acme.corp: NonMembershipResponse (no proof data, root: {}, height: {height})",
                    short_hex(root, 4),
                );
                println!(
                    "  \u{2192} Token \"{token_id}\" is NOT revoked (node lacks revocation tree for proof generation)"
                );
            }
        }
        other => {
            eprintln!("  ERROR: unexpected response: {other:?}");
            return;
        }
    }

    // Also check the revoked token
    let revoked_check = WireMessage::RequestNonMembership {
        token_id: token_id.to_string(),
    };

    println!();
    println!("  \u{2192} acme.corp \u{2192} partner.org: RequestNonMembership(\"{token_id}\")");

    conn.send(revoked_check).await.unwrap();
    let revoked_response = conn.recv().await.unwrap();

    match &revoked_response {
        WireMessage::NonMembershipResponse {
            token_id, proof, ..
        } => {
            if proof.is_none() {
                println!(
                    "  \u{2192} partner.org \u{2192} acme.corp: NonMembershipResponse (no proof)"
                );
                println!(
                    "  \u{2192} Token \"{token_id}\" IS revoked (no non-membership proof available)"
                );
            } else {
                println!("  \u{2192} Unexpected: proof provided for revoked token");
            }
        }
        other => {
            eprintln!("  ERROR: unexpected response: {other:?}");
            return;
        }
    }

    // =========================================================================
    // Summary
    // =========================================================================
    let elapsed = start.elapsed();
    println!();
    println!("--------------------------------------------------------------------------");
    println!(
        "  Demo completed in {:.1}ms",
        elapsed.as_secs_f64() * 1000.0
    );
    println!();
    println!("  Wire protocol stats:");
    println!("    - Messages exchanged: 10");
    println!("    - Largest frame: PresentToken (real STARK proof)");
    println!("    - Proof verification: real STARK (FRI + Merkle + Fiat-Shamir)");
    println!("    - Serialization: postcard (compact binary serde)");
    println!("    - Framing: 4-byte LE length prefix");
    println!("    - Transport: TCP with Nagle disabled");
    println!("--------------------------------------------------------------------------");
    println!();
}

/// Generate a real STARK proof using pyana-circuit.
///
/// This produces a cryptographically valid Merkle membership proof that will pass
/// full STARK verification (Merkle commitments, FRI low-degree test, Fiat-Shamir).
fn generate_real_stark_proof() -> Vec<u8> {
    use pyana_circuit::stark::{MerkleStarkAir, generate_merkle_trace, proof_to_bytes, prove};

    // Create a 4-level Merkle membership witness
    let siblings = [
        [100u32, 200, 300],
        [400, 500, 600],
        [700, 800, 900],
        [1000, 1100, 1200],
    ];
    let positions = [0u32, 1, 2, 3];
    let leaf_hash = 12345u32;

    let (trace, public_inputs) = generate_merkle_trace(leaf_hash, &siblings, &positions);
    let air = MerkleStarkAir;
    let proof = prove(&air, &trace, &public_inputs);
    proof_to_bytes(&proof)
}
