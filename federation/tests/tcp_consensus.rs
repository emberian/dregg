//! Integration test: 3 federation nodes on localhost achieve consensus over TCP.
//!
//! This test verifies that the `TcpFederationTransport` can drive a full
//! propose -> vote -> finalize round across real TCP connections.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

use pyana_federation::{ConsensusConfig, ConsensusState};
use pyana_federation::transport::{NetworkConsensusNode, TcpFederationTransport};
use pyana_federation::types::*;

/// Run 3 federation nodes on localhost, submit a revocation, and confirm
/// that consensus produces a valid QC.
#[tokio::test]
async fn three_node_tcp_consensus() {
    let num_nodes = 3;
    let config = ConsensusConfig::new(num_nodes);

    // Generate keypairs for all nodes.
    let keys: Vec<(SigningKey, PublicKey)> = (0..num_nodes).map(|_| generate_keypair()).collect();

    // Bind all listeners first to get actual addresses (port 0 -> OS picks).
    let base_addr: std::net::SocketAddr = "127.0.0.1:0".parse().unwrap();

    // Create transports. We need to know all addresses before creating,
    // so we use a two-phase approach.
    let mut transports: Vec<Arc<TcpFederationTransport>> = Vec::new();
    let mut addrs: Vec<std::net::SocketAddr> = Vec::new();

    // Phase 1: Bind listeners to get addresses.
    let mut listeners = Vec::new();
    for _ in 0..num_nodes {
        let listener = tokio::net::TcpListener::bind(base_addr).await.unwrap();
        let addr = listener.local_addr().unwrap();
        addrs.push(addr);
        listeners.push(listener);
    }
    drop(listeners); // Release the ports so TcpFederationTransport can bind them.

    // Give the OS a moment to release the ports.
    tokio::time::sleep(Duration::from_millis(50)).await;

    // Phase 2: Create transports with known peer addresses.
    for i in 0..num_nodes {
        let mut peers = HashMap::new();
        for j in 0..num_nodes {
            if j != i {
                peers.insert(j, addrs[j]);
            }
        }
        let (transport, actual_addr) = TcpFederationTransport::new_with_addr(i, peers, addrs[i])
            .await
            .unwrap();
        // Update address in case it changed (shouldn't with SO_REUSEADDR, but be safe).
        addrs[i] = actual_addr;
        transports.push(transport);
    }

    // Give listeners time to start.
    tokio::time::sleep(Duration::from_millis(100)).await;

    // Create consensus nodes.
    let mut nodes: Vec<NetworkConsensusNode> = (0..num_nodes)
        .map(|i| {
            let state = ConsensusState::new(i, keys[i].0.clone(), config.clone());
            NetworkConsensusNode::new(state, transports[i].clone(), config.clone())
        })
        .collect();

    // Submit a revocation to the leader.
    let leader_id = config.leader_for_view(1);
    let event = RevocationEvent {
        token_id: "tcp-test-token-1".to_string(),
        authority_id: leader_id,
        signature: Signature([0xDE; 64]),
    };
    nodes[leader_id].submit_revocation(event);

    // Leader proposes.
    let proposal = nodes[leader_id].try_propose().await.unwrap();
    assert!(proposal.is_some(), "leader should create a proposal");

    // Wait for proposals to reach peers.
    tokio::time::sleep(Duration::from_millis(200)).await;

    // Peers process proposals and send votes.
    for i in 0..num_nodes {
        if i == leader_id {
            continue;
        }
        nodes[i].process_messages().await.unwrap();
    }

    // Wait for votes to reach the leader.
    tokio::time::sleep(Duration::from_millis(200)).await;

    // Leader processes votes -> should reach quorum.
    let result = nodes[leader_id].process_messages().await.unwrap();
    assert!(
        result.is_some(),
        "leader should achieve quorum and finalize"
    );

    let (block, qc) = result.unwrap();
    assert_eq!(block.height, 1);
    assert_eq!(block.events.len(), 1);
    assert_eq!(block.events[0].token_id, "tcp-test-token-1");
    assert!(qc.is_valid());
    assert!(
        qc.votes.len() >= config.threshold,
        "QC should have at least {} votes, got {}",
        config.threshold,
        qc.votes.len()
    );

    // Wait for finalization broadcast.
    tokio::time::sleep(Duration::from_millis(200)).await;

    // Non-leader nodes should receive the finalization.
    for i in 0..num_nodes {
        if i == leader_id {
            continue;
        }
        let fin = nodes[i].process_messages().await.unwrap();
        assert!(
            fin.is_some(),
            "node {i} should have received the finalization"
        );
        let (fin_block, fin_qc) = fin.unwrap();
        assert_eq!(fin_block.block_hash, block.block_hash);
        assert!(fin_qc.is_valid());
    }

    // All nodes should now be at height 2 (next block).
    for node in &nodes {
        assert_eq!(node.state.current_height, 2);
    }
}

/// Test that consensus still works with 4 nodes and 1 non-voting node.
#[tokio::test]
async fn four_node_tcp_with_one_offline() {
    let num_nodes = 4;
    let config = ConsensusConfig::new(num_nodes);

    let keys: Vec<(SigningKey, PublicKey)> = (0..num_nodes).map(|_| generate_keypair()).collect();
    let base_addr: std::net::SocketAddr = "127.0.0.1:0".parse().unwrap();

    // Create transports.
    let mut addrs = Vec::new();
    let mut transports: Vec<Arc<TcpFederationTransport>> = Vec::new();

    for _i in 0..num_nodes {
        // First pass: determine addresses.
        let listener = tokio::net::TcpListener::bind(base_addr).await.unwrap();
        addrs.push(listener.local_addr().unwrap());
        drop(listener);
    }

    tokio::time::sleep(Duration::from_millis(50)).await;

    for i in 0..num_nodes {
        let mut peers = HashMap::new();
        for j in 0..num_nodes {
            if j != i {
                peers.insert(j, addrs[j]);
            }
        }
        let (transport, actual_addr) = TcpFederationTransport::new_with_addr(i, peers, addrs[i])
            .await
            .unwrap();
        addrs[i] = actual_addr;
        transports.push(transport);
    }

    tokio::time::sleep(Duration::from_millis(100)).await;

    let mut nodes: Vec<NetworkConsensusNode> = (0..num_nodes)
        .map(|i| {
            let state = ConsensusState::new(i, keys[i].0.clone(), config.clone());
            NetworkConsensusNode::new(state, transports[i].clone(), config.clone())
        })
        .collect();

    // Node 3 is "offline" — it won't process messages.
    let leader_id = config.leader_for_view(1);
    let event = RevocationEvent {
        token_id: "tcp-bft-token".to_string(),
        authority_id: 0,
        signature: Signature([0xAB; 64]),
    };
    nodes[leader_id].submit_revocation(event);

    // Leader proposes.
    nodes[leader_id].try_propose().await.unwrap();
    tokio::time::sleep(Duration::from_millis(200)).await;

    // Only nodes 0-2 vote (node 3 "offline").
    for i in 0..num_nodes {
        if i == leader_id || i == 3 {
            continue;
        }
        nodes[i].process_messages().await.unwrap();
    }

    tokio::time::sleep(Duration::from_millis(200)).await;

    // Leader collects votes. Threshold for 4 nodes is 3, so 3 votes
    // (leader + 2 others, excluding node 3) should suffice.
    let result = nodes[leader_id].process_messages().await.unwrap();
    assert!(
        result.is_some(),
        "should still achieve consensus with 3/4 nodes voting"
    );

    let (_block, qc) = result.unwrap();
    assert!(qc.is_valid());
}
