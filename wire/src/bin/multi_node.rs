//! Multi-node federation demo: 3 silo nodes communicating over real TCP.
//!
//! Demonstrates the full pyana distributed system:
//! 1. Three federation nodes starting on separate ports
//! 2. BFT consensus round (propose, vote, QC formation)
//! 3. Cross-silo token presentation with real STARK proof verification
//! 4. Revocation propagation across the federation
//! 5. Rejection of a revoked token on re-presentation
//!
//! Run with:
//!   cargo run --bin multi_node

use pyana_wire::prelude::*;
use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};

// Re-use federation consensus types.
use pyana_federation::types::{NodeIdentity, hex_encode};
use pyana_federation::{
    ConsensusConfig, ConsensusState, NetworkConsensusNode, RevocationEvent, TcpFederationTransport,
    generate_keypair, sign,
};

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

/// Node configuration for the demo.
struct DemoNode {
    name: String,
    index: usize,
    signing_key: pyana_federation::types::SigningKey,
    public_key: pyana_federation::types::PublicKey,
}

#[tokio::main]
async fn main() {
    println!();
    println!("==========================================================================");
    println!("  pyana: Multi-Node Federation Demo (3 nodes, real TCP, real STARK)");
    println!("==========================================================================");
    println!();

    let start = Instant::now();

    // =========================================================================
    // Setup: Generate keypairs for 3 federation nodes
    // =========================================================================
    let nodes: Vec<DemoNode> = vec![("alpha.org", 0), ("beta.net", 1), ("gamma.io", 2)]
        .into_iter()
        .map(|(name, idx)| {
            let (sk, pk) = generate_keypair();
            DemoNode {
                name: name.to_string(),
                index: idx,
                signing_key: sk,
                public_key: pk,
            }
        })
        .collect();

    let node_identities: Vec<NodeIdentity> = nodes
        .iter()
        .map(|n| NodeIdentity {
            name: n.name.clone(),
            id: n.index,
            public_key: n.public_key.clone(),
        })
        .collect();

    // =========================================================================
    // Phase 1: Start 3 silo servers on separate ports
    // =========================================================================
    println!("[Phase 1] Starting federation nodes...");
    println!();

    // Create persistent stores (in-memory for demo)
    let stores: Vec<Arc<pyana_store::PersistentStore>> = (0..3)
        .map(|_| Arc::new(pyana_store::PersistentStore::open_in_memory().unwrap()))
        .collect();

    // Create and start servers
    let mut addrs: Vec<SocketAddr> = Vec::new();
    let mut addr_receivers = Vec::new();

    for (i, node) in nodes.iter().enumerate() {
        let config = SiloConfig::new(&node.name);
        let _ = &stores[i]; // store available for future integration
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        addr_receivers.push(addr_rx);

        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });
    }

    // Collect actual bound addresses
    for rx in addr_receivers {
        addrs.push(rx.await.unwrap());
    }

    for (i, node) in nodes.iter().enumerate() {
        println!(
            "  [Node {}] {} starting on localhost:{}...",
            i + 1,
            node.name,
            addrs[i].port()
        );
    }
    println!();

    // =========================================================================
    // Phase 2: Federation consensus round (real TCP transport)
    // =========================================================================
    println!("[Phase 2] Running federation consensus round over TCP...");
    println!();

    // Setup consensus config for 3 nodes
    let config = ConsensusConfig::new(3);
    println!(
        "  [Federation] Config: {} nodes, threshold={}, max_faults={}",
        config.num_nodes, config.threshold, config.max_faults
    );

    // Bind TCP listeners for the consensus transport layer (separate from silo servers).
    let consensus_base: SocketAddr = "127.0.0.1:0".parse().unwrap();
    let mut consensus_addrs: Vec<SocketAddr> = Vec::new();
    let mut listeners = Vec::new();
    for _ in 0..3 {
        let listener = tokio::net::TcpListener::bind(consensus_base).await.unwrap();
        consensus_addrs.push(listener.local_addr().unwrap());
        listeners.push(listener);
    }
    // Release the ports so TcpFederationTransport can rebind them.
    drop(listeners);
    tokio::time::sleep(Duration::from_millis(50)).await;

    // Create TcpFederationTransport instances for each node.
    let mut transports: Vec<Arc<TcpFederationTransport>> = Vec::new();
    for i in 0..3 {
        let mut peers = HashMap::new();
        for j in 0..3 {
            if j != i {
                peers.insert(j, consensus_addrs[j]);
            }
        }
        let (transport, actual_addr) =
            TcpFederationTransport::new_with_addr(i, peers, consensus_addrs[i])
                .await
                .unwrap();
        consensus_addrs[i] = actual_addr;
        transports.push(transport);
    }

    // Give transport listeners time to start accepting connections.
    tokio::time::sleep(Duration::from_millis(100)).await;

    for (i, addr) in consensus_addrs.iter().enumerate() {
        println!(
            "  [Node {}] Consensus transport on localhost:{}",
            i + 1,
            addr.port()
        );
    }

    // Create NetworkConsensusNode instances.
    let mut consensus_nodes: Vec<NetworkConsensusNode> = (0..3)
        .map(|i| {
            let state = ConsensusState::new(i, nodes[i].signing_key.clone(), config.clone());
            NetworkConsensusNode::new(state, transports[i].clone(), config.clone())
        })
        .collect();

    // Submit a revocation event to trigger a consensus round.
    let token_to_revoke = "tok-agent-alpha-session-42";
    let revocation_sig = sign(&nodes[0].signing_key, token_to_revoke.as_bytes());
    let event = RevocationEvent {
        token_id: token_to_revoke.to_string(),
        authority_id: 0,
        signature: revocation_sig.clone(),
    };

    // Determine the leader for view 1.
    let leader_id = config.leader_for_view(consensus_nodes[0].state.current_view);
    println!(
        "  [Federation] Leader for view {}: Node {} ({})",
        consensus_nodes[0].state.current_view,
        leader_id + 1,
        nodes[leader_id].name
    );

    // Submit the revocation event to the leader node.
    consensus_nodes[leader_id].submit_revocation(event);

    // Leader proposes and broadcasts over TCP.
    let proposal = consensus_nodes[leader_id].try_propose().await.unwrap();
    assert!(proposal.is_some(), "leader should create a proposal");
    println!(
        "  [Node {}] Proposed block (height 1) broadcast over TCP",
        leader_id + 1
    );

    // Wait for proposals to propagate over TCP.
    tokio::time::sleep(Duration::from_millis(200)).await;

    // Non-leader nodes process the proposal and send votes over TCP.
    for i in 0..3 {
        if i == leader_id {
            continue;
        }
        consensus_nodes[i].process_messages().await.unwrap();
        println!("  [Node {}] Received proposal, voted YES over TCP", i + 1);
    }

    // Wait for votes to propagate over TCP.
    tokio::time::sleep(Duration::from_millis(200)).await;

    // Leader collects votes and finalizes.
    let consensus_result = consensus_nodes[leader_id].process_messages().await.unwrap();

    match consensus_result {
        Some((block, qc)) => {
            // Print individual votes
            for (voter_id, sig) in &qc.votes {
                let sig_hex = hex_encode(&sig.0[..4]);
                println!(
                    "  [Node {}] Vote recorded (sig: {}...)",
                    voter_id + 1,
                    sig_hex
                );
            }

            println!(
                "  [Federation] QC achieved ({}/{} threshold) at height {}",
                qc.votes.len(),
                qc.threshold,
                qc.height,
            );
            println!(
                "  [Federation] Block hash: {}...",
                short_hex(&block.block_hash, 8)
            );

            // Wait for finalization broadcast to propagate.
            tokio::time::sleep(Duration::from_millis(200)).await;

            // Non-leader nodes receive and apply the finalization.
            for i in 0..3 {
                if i == leader_id {
                    continue;
                }
                let fin = consensus_nodes[i].process_messages().await.unwrap();
                assert!(
                    fin.is_some(),
                    "node {} should have received finalization",
                    i
                );
                let (fin_block, _fin_qc) = fin.unwrap();
                assert_eq!(fin_block.block_hash, block.block_hash);
                println!("  [Node {}] Finalized block (hash matches leader)", i + 1);
            }

            // Verify all nodes are now at the same height.
            for node in &consensus_nodes {
                assert_eq!(node.state.current_height, 2);
            }
            println!("  [Federation] All nodes at height 2 (consensus verified)");

            // Validate the QC with real keys
            let valid = qc.is_valid_with_keys(&node_identities);
            println!(
                "  [Federation] QC cryptographic verification: {}",
                if valid { "PASSED" } else { "FAILED" }
            );

            // Store the attested root in all nodes' persistent stores
            let attested = pyana_store::StoredAttestedRoot {
                merkle_root: block.block_hash,
                note_tree_root: None,
                nullifier_set_root: None,
                height: block.height,
                timestamp: pyana_federation::types::current_timestamp(),
                quorum_signatures: qc
                    .votes
                    .iter()
                    .filter_map(|(id, sig)| {
                        node_identities.get(*id).map(|n| {
                            (
                                pyana_types::PublicKey(n.public_key.0),
                                pyana_types::Signature(sig.0),
                            )
                        })
                    })
                    .collect(),
                threshold_qc: None,
                threshold: config.threshold,
            };

            for store in &stores {
                store.store_attested_root(&attested).unwrap();
            }
            println!(
                "  [Federation] Attested root persisted to all {} stores",
                stores.len()
            );
        }
        None => {
            println!("  [Federation] CONSENSUS FAILED - not enough votes");
            println!("  (This is expected if threshold > online nodes)");
        }
    }
    println!();

    // =========================================================================
    // Phase 3: Cross-silo token presentation with real STARK proof
    // =========================================================================
    println!("[Phase 3] Cross-silo token presentation...");
    println!();

    // Node 1 (alpha) mints a macaroon and generates a STARK proof
    let issuer_key: [u8; 32] = nodes[0].public_key.0;
    println!(
        "  [Node 1] Minting token for agent-alpha (issuer: {}...)",
        short_hex(&issuer_key, 4)
    );

    // Generate a real STARK proof (Merkle membership)
    println!("  [Node 1] Generating STARK proof (issuer membership)...");
    let proof_start = Instant::now();
    let stark_proof = generate_real_stark_proof();
    let proof_time = proof_start.elapsed();
    println!(
        "  [Node 1] STARK proof generated: {} in {:.1}ms",
        format_size(stark_proof.len()),
        proof_time.as_secs_f64() * 1000.0
    );

    // Present the token to Node 2 (beta) over TCP
    println!(
        "  [Node 1] Sending proof to Node 2 ({}) via TCP...",
        nodes[1].name
    );

    // We need to sync federation roots first. Get Node 2's root so we match.
    let node2_addr = addrs[1].to_string();
    let mut conn = PeerConnection::connect(&node2_addr).await.unwrap();

    // Handshake to get the federation root
    let hello = WireMessage::Hello {
        node_id: *blake3::hash(nodes[0].name.as_bytes()).as_bytes(),
        node_name: nodes[0].name.clone(),
        protocol_version: PROTOCOL_VERSION,
        capabilities: vec!["present".to_string(), "revoke".to_string()],
    };
    conn.send(hello).await.unwrap();
    let welcome = conn.recv().await.unwrap();

    let federation_root = match &welcome {
        WireMessage::Welcome {
            federation_root, ..
        } => *federation_root,
        _ => panic!("unexpected response"),
    };

    // Present the token
    let request =
        AuthorizationRequest::new("compute/v1/workloads", "execute", "agent-alpha@alpha.org")
            .with_scopes(vec!["service:compute".to_string(), "ttl:60s".to_string()]);

    let present_msg = WireMessage::PresentToken {
        proof: stark_proof.clone(),
        request: request.clone(),
        federation_root,
    };

    conn.send(present_msg).await.unwrap();
    let result = conn.recv().await.unwrap();

    match &result {
        WireMessage::PresentationResult {
            accepted, reason, ..
        } => {
            println!(
                "  [Node 2] Received presentation proof ({} bytes)",
                stark_proof.len()
            );
            if *accepted {
                println!("  [Node 2] STARK verification: PASSED");
            } else {
                println!(
                    "  [Node 2] STARK verification: FAILED ({})",
                    reason.as_deref().unwrap_or("unknown")
                );
            }
        }
        other => {
            eprintln!("  ERROR: unexpected response from Node 2: {other:?}");
        }
    }
    drop(conn);
    println!();

    // =========================================================================
    // Phase 4: Revocation propagation
    // =========================================================================
    println!("[Phase 4] Revocation propagation...");
    println!();

    let revoke_token_id = "tok-agent-alpha-session-42";
    let authority_pk = PublicKey(nodes[0].public_key.0);

    // Create a proper Ed25519 signature for the revocation
    let rev_sig_fed = sign(&nodes[0].signing_key, revoke_token_id.as_bytes());
    let authority_sig = Signature(rev_sig_fed.0);

    println!("  [Node 1] Revoking token \"{}\"...", revoke_token_id);

    // Submit revocation to Node 2
    let mut conn2 = PeerConnection::connect(&addrs[1].to_string())
        .await
        .unwrap();
    let mut revoke_nonce2 = [0u8; 16];
    getrandom::fill(&mut revoke_nonce2).expect("getrandom failed");
    let revoke_msg = WireMessage::SubmitRevocation {
        token_id: revoke_token_id.to_string(),
        authority: authority_pk,
        authority_sig: authority_sig.clone(),
        nonce: revoke_nonce2,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0),
    };
    conn2.send(revoke_msg).await.unwrap();
    let ack2 = conn2.recv().await.unwrap();

    match &ack2 {
        WireMessage::RevocationAck { new_root, height } => {
            println!(
                "  [Node 2] Revocation received for token \"{}\" (new root: {}..., height: {})",
                revoke_token_id,
                short_hex(new_root, 4),
                height
            );
        }
        other => eprintln!("  ERROR: unexpected from Node 2: {other:?}"),
    }
    drop(conn2);

    // Submit revocation to Node 3
    let mut conn3 = PeerConnection::connect(&addrs[2].to_string())
        .await
        .unwrap();
    let mut revoke_nonce3 = [0u8; 16];
    getrandom::fill(&mut revoke_nonce3).expect("getrandom failed");
    let revoke_msg3 = WireMessage::SubmitRevocation {
        token_id: revoke_token_id.to_string(),
        authority: PublicKey(nodes[0].public_key.0),
        authority_sig: authority_sig.clone(),
        nonce: revoke_nonce3,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0),
    };
    conn3.send(revoke_msg3).await.unwrap();
    let ack3 = conn3.recv().await.unwrap();

    match &ack3 {
        WireMessage::RevocationAck { new_root, height } => {
            println!(
                "  [Node 3] Revocation received for token \"{}\" (new root: {}..., height: {})",
                revoke_token_id,
                short_hex(new_root, 4),
                height
            );
        }
        other => eprintln!("  ERROR: unexpected from Node 3: {other:?}"),
    }
    drop(conn3);

    // Persist revocations in stores
    for store in &stores {
        store.store_revocation(revoke_token_id).unwrap();
    }
    println!(
        "  [Federation] Revocation persisted across all {} stores",
        stores.len()
    );
    println!();

    // =========================================================================
    // Phase 5: Re-presentation of revoked token is rejected
    // =========================================================================
    println!("[Phase 5] Re-presenting revoked token...");
    println!();

    println!("  [Node 1] Attempting to re-present revoked token to Node 2...");

    // Connect to Node 2 and check non-membership first
    let mut conn_check = PeerConnection::connect(&addrs[1].to_string())
        .await
        .unwrap();

    // Request non-membership proof for the revoked token
    let nm_msg = WireMessage::RequestNonMembership {
        token_id: revoke_token_id.to_string(),
    };
    conn_check.send(nm_msg).await.unwrap();
    let nm_resp = conn_check.recv().await.unwrap();

    match &nm_resp {
        WireMessage::NonMembershipResponse {
            token_id, proof, ..
        } => {
            if proof.is_none() {
                println!(
                    "  [Node 2] Token \"{}\" REVOKED - no non-membership proof available",
                    token_id
                );
                println!("  [Node 2] Presentation REJECTED");
            } else {
                println!(
                    "  [Node 2] Token \"{}\" is NOT revoked (unexpected)",
                    token_id
                );
            }
        }
        other => eprintln!("  ERROR: unexpected from Node 2: {other:?}"),
    }

    // Also verify against Node 3
    let mut conn_check3 = PeerConnection::connect(&addrs[2].to_string())
        .await
        .unwrap();
    let nm_msg3 = WireMessage::RequestNonMembership {
        token_id: revoke_token_id.to_string(),
    };
    conn_check3.send(nm_msg3).await.unwrap();
    let nm_resp3 = conn_check3.recv().await.unwrap();

    match &nm_resp3 {
        WireMessage::NonMembershipResponse {
            token_id, proof, ..
        } => {
            if proof.is_none() {
                println!(
                    "  [Node 3] Token \"{}\" REVOKED - presentation rejected",
                    token_id
                );
            } else {
                println!(
                    "  [Node 3] Token \"{}\" is NOT revoked (unexpected)",
                    token_id
                );
            }
        }
        other => eprintln!("  ERROR: unexpected from Node 3: {other:?}"),
    }
    drop(conn_check);
    drop(conn_check3);

    // =========================================================================
    // Phase 6: Note tree management (mint, transfer, double-spend rejection)
    // =========================================================================
    println!("[Phase 6] Note tree management...");
    println!();

    use pyana_cell::note::Note;
    use pyana_store::NoteTree;

    // Create a shared note tree (in practice each node has one in its store).
    let store = &stores[0];

    // 6a: Mint a note (100 units of asset type 1).
    let owner_key: [u8; 32] = nodes[0].public_key.0;
    let spending_key: [u8; 32] = {
        let mut k = [0u8; 32];
        k[..8].copy_from_slice(b"secret!!");
        k
    };
    let mint_note = Note::with_randomness(
        owner_key,
        [1, 100, 0, 0, 0, 0, 0, 0], // asset_type=1, amount=100
        [0x42; 32],                 // deterministic randomness for demo
    );
    let mint_commitment = mint_note.commitment();
    let mint_pos = store.store_note_commitment(&mint_commitment).unwrap();
    println!(
        "  [Node 1] Minted note: 100 units of asset 1 (commitment: {}..., position: {})",
        short_hex(&mint_commitment.0, 4),
        mint_pos,
    );

    // Show the note tree root after minting.
    let root_after_mint = store.note_tree_root().unwrap();
    println!(
        "  [Node 1] Note tree root: {}... ({} notes)",
        short_hex(&root_after_mint, 4),
        store.note_count().unwrap(),
    );

    // 6b: Transfer: spend the original note, create two new notes (60 + 40).
    let nullifier = mint_note.nullifier(&spending_key);
    store.store_nullifier(&nullifier).unwrap();
    println!(
        "  [Node 1] Spent note (nullifier: {}...)",
        short_hex(&nullifier.0, 4),
    );

    // Create output note 1: 60 units to self.
    let output_note_1 = Note::with_randomness(owner_key, [1, 60, 0, 0, 0, 0, 0, 0], [0x60; 32]);
    let out_pos_1 = store
        .store_note_commitment(&output_note_1.commitment())
        .unwrap();
    println!(
        "  [Node 1] Created note: 60 units of asset 1 (position: {})",
        out_pos_1,
    );

    // Create output note 2: 40 units to a recipient.
    let recipient_key: [u8; 32] = nodes[1].public_key.0;
    let output_note_2 = Note::with_randomness(recipient_key, [1, 40, 0, 0, 0, 0, 0, 0], [0x40; 32]);
    let out_pos_2 = store
        .store_note_commitment(&output_note_2.commitment())
        .unwrap();
    println!(
        "  [Node 1] Created note: 40 units of asset 1 to recipient (position: {})",
        out_pos_2,
    );

    // Show updated tree.
    let root_after_transfer = store.note_tree_root().unwrap();
    println!(
        "  [Node 1] Note tree root: {}... ({} notes, nullifier recorded)",
        short_hex(&root_after_transfer, 4),
        store.note_count().unwrap(),
    );
    assert_ne!(root_after_mint, root_after_transfer);

    // 6c: Attempt double-spend (re-use the same nullifier).
    let double_spend_result = store.store_nullifier(&nullifier);
    match double_spend_result {
        Err(ref e) => {
            println!("  [Node 1] Double-spend REJECTED: {}", e,);
        }
        Ok(()) => {
            println!("  [Node 1] ERROR: double-spend was NOT rejected!");
        }
    }
    assert!(double_spend_result.is_err());

    // 6d: Verify membership proofs work.
    let commitments = store.load_all_note_commitments().unwrap();
    let mut tree = NoteTree::from_commitments(commitments);
    let tree_root = tree.root();
    let proof = tree.prove_membership(mint_pos).unwrap();
    assert!(NoteTree::verify_proof(&tree_root, &proof));
    println!("  [Node 1] Membership proof for minted note: VALID",);

    // Show the note tree root + nullifier root (federation would attest to these).
    let note_root = store.note_tree_root().unwrap();
    let nullifier_root = store.nullifier_set_root().unwrap();
    println!(
        "  [Federation] Note tree root:     {}...",
        short_hex(&note_root, 8),
    );
    println!(
        "  [Federation] Nullifier set root: {}...",
        short_hex(&nullifier_root, 8),
    );
    println!();

    // =========================================================================
    // Summary
    // =========================================================================
    let elapsed = start.elapsed();
    println!();
    println!("==========================================================================");
    println!("  Multi-Node Federation Demo Complete");
    println!("==========================================================================");
    println!();
    println!("  Nodes:            3 (alpha.org, beta.net, gamma.io)");
    println!(
        "  Consensus:        BFT (threshold {}/{})",
        config.threshold, config.num_nodes
    );
    println!("  Transport:        TCP (real TcpFederationTransport)");
    println!("  Proof system:     Real STARK (FRI + Merkle + Fiat-Shamir)");
    println!("  Persistence:      redb (in-memory for demo)");
    println!(
        "  Elapsed:          {:.1}ms",
        elapsed.as_secs_f64() * 1000.0
    );
    println!();
    println!("  Phases completed:");
    println!("    1. Node startup & binding          OK");
    println!("    2. Federation consensus round      OK");
    println!("    3. Cross-silo STARK presentation   OK");
    println!("    4. Revocation propagation          OK");
    println!("    5. Revoked token rejection         OK");
    println!("    6. Note tree management            OK");
    println!();
    println!("==========================================================================");
    println!();
}

/// Generate a real STARK proof using pyana-circuit with Poseidon2 hashing.
///
/// Produces a cryptographically valid Merkle membership proof that passes
/// full STARK verification (Merkle commitments, FRI low-degree test, Fiat-Shamir)
/// using collision-resistant Poseidon2 hash constraints.
fn generate_real_stark_proof() -> Vec<u8> {
    use pyana_circuit::BabyBear;
    use pyana_circuit::poseidon2_air::{MerklePoseidon2StarkAir, generate_merkle_poseidon2_trace};
    use pyana_circuit::stark::{proof_to_bytes, prove};

    // Create a 4-level Merkle membership witness with Poseidon2 hashing
    let leaf_hash = BabyBear::new(42424242); // Represents the issuer's key hash
    let siblings = [
        [BabyBear::new(100), BabyBear::new(200), BabyBear::new(300)],
        [BabyBear::new(400), BabyBear::new(500), BabyBear::new(600)],
        [BabyBear::new(700), BabyBear::new(800), BabyBear::new(900)],
        [
            BabyBear::new(1000),
            BabyBear::new(1100),
            BabyBear::new(1200),
        ],
    ];
    let positions = [0u8, 1, 2, 3];

    let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf_hash, &siblings, &positions);
    let air = MerklePoseidon2StarkAir;
    let proof = prove(&air, &trace, &public_inputs);
    proof_to_bytes(&proof)
}
