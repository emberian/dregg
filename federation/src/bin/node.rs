//! Federation consensus node binary.
//!
//! A single federation node that:
//! - Takes a config (own keypair, peer addresses, threshold)
//! - Starts a TCP listener for incoming federation messages
//! - Starts consensus with TcpFederationTransport
//! - Runs periodic consensus rounds
//! - Prints attested roots as they're produced
//!
//! Usage:
//!   pyana-federation-node --id 0 --peers "1=127.0.0.1:9001,2=127.0.0.1:9002" --listen 127.0.0.1:9000
//!
//! Or for a quick 3-node local demo:
//!   pyana-federation-node --local-demo

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;

use pyana_federation::{ConsensusConfig, ConsensusState};
use pyana_federation::transport::{NetworkConsensusNode, TcpFederationTransport};
use pyana_federation::types::*;

/// Simple argument parsing (no external dep).
struct NodeConfig {
    node_id: usize,
    listen_addr: SocketAddr,
    peers: HashMap<usize, SocketAddr>,
    num_nodes: usize,
    round_interval: Duration,
}

fn parse_args() -> Result<NodeConfig, String> {
    let args: Vec<String> = std::env::args().collect();

    // Check for --local-demo mode.
    if args.iter().any(|a| a == "--local-demo") {
        return Err("local-demo".to_string());
    }

    let mut node_id = None;
    let mut listen_addr = None;
    let mut peers = HashMap::new();
    let mut num_nodes = None;
    let mut round_interval = Duration::from_secs(5);

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--id" => {
                i += 1;
                node_id = Some(args[i].parse::<usize>().map_err(|e| e.to_string())?);
            }
            "--listen" => {
                i += 1;
                listen_addr = Some(args[i].parse::<SocketAddr>().map_err(|e| e.to_string())?);
            }
            "--peers" => {
                i += 1;
                for entry in args[i].split(',') {
                    let parts: Vec<&str> = entry.split('=').collect();
                    if parts.len() != 2 {
                        return Err(format!("invalid peer format: {entry}"));
                    }
                    let id = parts[0].parse::<usize>().map_err(|e| e.to_string())?;
                    let addr = parts[1].parse::<SocketAddr>().map_err(|e| e.to_string())?;
                    peers.insert(id, addr);
                }
            }
            "--num-nodes" => {
                i += 1;
                num_nodes = Some(args[i].parse::<usize>().map_err(|e| e.to_string())?);
            }
            "--interval" => {
                i += 1;
                let secs = args[i].parse::<u64>().map_err(|e| e.to_string())?;
                round_interval = Duration::from_secs(secs);
            }
            other => return Err(format!("unknown argument: {other}")),
        }
        i += 1;
    }

    let node_id = node_id.ok_or("--id required")?;
    let listen_addr = listen_addr.ok_or("--listen required")?;
    let num_nodes = num_nodes.unwrap_or(peers.len() + 1);

    Ok(NodeConfig {
        node_id,
        listen_addr,
        peers,
        num_nodes,
        round_interval,
    })
}

#[tokio::main]
async fn main() {
    match parse_args() {
        Ok(config) => run_node(config).await,
        Err(ref e) if e == "local-demo" => run_local_demo().await,
        Err(e) => {
            eprintln!("Error: {e}");
            eprintln!();
            eprintln!("Usage:");
            eprintln!(
                "  pyana-federation-node --id <N> --listen <ADDR> --peers <ID=ADDR,...> [--num-nodes <N>] [--interval <SECS>]"
            );
            eprintln!();
            eprintln!("  pyana-federation-node --local-demo");
            std::process::exit(1);
        }
    }
}

async fn run_node(config: NodeConfig) {
    println!(
        "[node {}] Starting federation node on {}",
        config.node_id, config.listen_addr
    );
    println!(
        "[node {}] Federation: {} nodes, threshold={}",
        config.node_id,
        config.num_nodes,
        ConsensusConfig::new(config.num_nodes).threshold
    );
    println!("[node {}] Peers: {:?}", config.node_id, config.peers);

    let consensus_config = ConsensusConfig::new(config.num_nodes);
    let (signing_key, public_key) = generate_keypair();

    println!(
        "[node {}] Public key: {}",
        config.node_id,
        public_key.short_hex()
    );

    // Create the TCP transport.
    let (transport, actual_addr) =
        TcpFederationTransport::new_with_addr(config.node_id, config.peers, config.listen_addr)
            .await
            .expect("failed to start transport");

    println!("[node {}] Listening on {actual_addr}", config.node_id);

    // Create the consensus state and node.
    let state = ConsensusState::new(config.node_id, signing_key, consensus_config.clone());
    let mut node = NetworkConsensusNode::new(state, transport, consensus_config.clone());

    println!(
        "[node {}] Ready. Running consensus rounds every {:?}",
        config.node_id, config.round_interval
    );

    // Main loop: periodically attempt to propose and process messages.
    let mut round = 0u64;
    loop {
        round += 1;

        // Process any pending incoming messages.
        match node.process_messages().await {
            Ok(Some((block, qc))) => {
                println!(
                    "[node {}] FINALIZED block height={} view={} events={} qc_votes={}",
                    config.node_id,
                    block.height,
                    block.view,
                    block.events.len(),
                    qc.votes.len()
                );
                for event in &block.events {
                    println!("[node {}]   revoked: {}", config.node_id, event.token_id);
                }
            }
            Ok(None) => {}
            Err(e) => {
                eprintln!("[node {}] Error processing messages: {e}", config.node_id);
            }
        }

        // If we're the leader and have pending events, try to propose.
        if node.state.is_leader() && !node.state.pending_events.is_empty() {
            match node.try_propose().await {
                Ok(Some(block)) => {
                    println!(
                        "[node {}] PROPOSED block height={} view={} events={}",
                        config.node_id,
                        block.height,
                        block.view,
                        block.events.len()
                    );
                }
                Ok(None) => {}
                Err(e) => {
                    eprintln!("[node {}] Error proposing: {e}", config.node_id);
                }
            }
        }

        // Periodically inject a test revocation (for demo purposes, every 10 rounds).
        if round % 10 == 0 && node.state.is_leader() {
            let token_id = format!("demo-token-{round}");
            let event = RevocationEvent {
                token_id: token_id.clone(),
                authority_id: config.node_id,
                signature: Signature([0x42; 64]),
            };
            node.submit_revocation(event);
            println!(
                "[node {}] Submitted revocation for {token_id}",
                config.node_id
            );
        }

        tokio::time::sleep(config.round_interval).await;
    }
}

/// Run a 3-node local demo in a single process.
async fn run_local_demo() {
    println!("=== Federation Local Demo (3 nodes) ===");
    println!();

    let num_nodes = 3;
    let config = ConsensusConfig::new(num_nodes);
    println!(
        "Configuration: {} nodes, threshold={}, max_faults={}",
        config.num_nodes, config.threshold, config.max_faults
    );
    println!();

    // Create transports on localhost.
    let base: SocketAddr = "127.0.0.1:0".parse().unwrap();
    let mut addrs = Vec::new();

    // Allocate ports.
    for _ in 0..num_nodes {
        let listener = tokio::net::TcpListener::bind(base).await.unwrap();
        addrs.push(listener.local_addr().unwrap());
        drop(listener);
    }

    tokio::time::sleep(Duration::from_millis(50)).await;

    let mut transports: Vec<Arc<TcpFederationTransport>> = Vec::new();
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

    println!("Nodes:");
    let mut keys = Vec::new();
    for i in 0..num_nodes {
        let (sk, pk) = generate_keypair();
        println!("  node {i}: {} (key={})", addrs[i], pk.short_hex());
        keys.push((sk, pk));
    }
    println!();

    tokio::time::sleep(Duration::from_millis(100)).await;

    // Create consensus nodes.
    let mut nodes: Vec<NetworkConsensusNode> = (0..num_nodes)
        .map(|i| {
            let state = ConsensusState::new(i, keys[i].0.clone(), config.clone());
            NetworkConsensusNode::new(state, transports[i].clone(), config.clone())
        })
        .collect();

    // Run 3 consensus rounds.
    for round in 1..=3 {
        println!("--- Round {round} ---");

        let leader_id = config.leader_for_view(nodes[0].state.current_view);
        println!("  Leader: node {leader_id}");

        // Submit a revocation to the leader.
        let token_id = format!("token-round-{round}");
        let event = RevocationEvent {
            token_id: token_id.clone(),
            authority_id: leader_id,
            signature: Signature([round as u8; 64]),
        };
        nodes[leader_id].submit_revocation(event);
        println!("  Submitted revocation for: {token_id}");

        // Leader proposes.
        let proposal = nodes[leader_id].try_propose().await.unwrap();
        if let Some(ref block) = proposal {
            println!(
                "  Leader proposed: height={} events={}",
                block.height,
                block.events.len()
            );
        }

        // Wait for broadcast.
        tokio::time::sleep(Duration::from_millis(100)).await;

        // Peers vote.
        for i in 0..num_nodes {
            if i == leader_id {
                continue;
            }
            nodes[i].process_messages().await.unwrap();
        }

        // Wait for votes.
        tokio::time::sleep(Duration::from_millis(100)).await;

        // Leader collects votes.
        let result = nodes[leader_id].process_messages().await.unwrap();
        match result {
            Some((block, qc)) => {
                println!(
                    "  FINALIZED: height={} votes={} valid={}",
                    block.height,
                    qc.votes.len(),
                    qc.is_valid()
                );
                println!("  Block hash: {}", hex_encode(&block.block_hash[..8]));

                // Wait for finalization broadcast.
                tokio::time::sleep(Duration::from_millis(100)).await;

                // Other nodes apply finalization.
                for i in 0..num_nodes {
                    if i == leader_id {
                        continue;
                    }
                    nodes[i].process_messages().await.unwrap();
                }
            }
            None => {
                println!("  FAILED: consensus not reached");
            }
        }
        println!();
    }

    println!("=== Demo Complete ===");
    println!("All nodes at height: {}", nodes[0].state.current_height);
}
