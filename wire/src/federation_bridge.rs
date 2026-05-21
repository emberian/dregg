//! Bridge between the wire server and the federation consensus engine.
//!
//! This module provides [`FederationBridge`], which connects a [`SiloServer`] to
//! a [`NetworkConsensusNode`] so that:
//!
//! - Revocations received over the wire are submitted to the federation for consensus.
//! - The wire server can serve fresh attested roots produced by the federation.
//! - Attested roots received from peer silos are verified against federation state.
//!
//! # Usage
//!
//! ```no_run
//! use pyana_wire::federation_bridge::FederationBridge;
//! use pyana_federation::{NetworkConsensusNode, ConsensusState, ConsensusConfig, LocalTransport, generate_keypair};
//! use std::sync::Arc;
//! use tokio::sync::Mutex;
//!
//! # async fn example() {
//! let config = ConsensusConfig::new(4);
//! let transports = LocalTransport::create_network(4);
//! let (sk, _pk) = generate_keypair();
//! let state = ConsensusState::new(0, sk, config.clone());
//! let node = NetworkConsensusNode::new(state, transports[0].clone(), config.clone());
//! let node = Arc::new(Mutex::new(node));
//!
//! let bridge = FederationBridge::new(node);
//! // Use bridge as a RevocationHandler on SiloServer
//! # }
//! ```

use std::collections::HashSet;
use std::sync::Arc;

use tokio::sync::Mutex;

use pyana_federation::{
    AttestedRoot, NetworkConsensusNode, QuorumCertificate, RevocationEvent, Signature,
};

use crate::server::RevocationHandler;

// =============================================================================
// FederationBridge
// =============================================================================

/// Bridges wire protocol operations to the federation consensus engine.
///
/// Holds a shared reference to a [`NetworkConsensusNode`] and implements
/// [`RevocationHandler`] so it can be plugged into a [`SiloServer`].
///
/// The bridge also exposes methods to query the latest attested root from
/// the consensus engine, which the wire server uses when responding to
/// `RequestAttestedRoot` messages.
pub struct FederationBridge {
    /// The consensus node, behind a Mutex since `NetworkConsensusNode` requires
    /// `&mut self` for most operations.
    node: Arc<Mutex<NetworkConsensusNode>>,
    /// Cached latest attested root, updated after each finalization.
    latest_root: Arc<std::sync::RwLock<Option<CachedAttestedRoot>>>,
    /// Local index of revoked token IDs, updated on each submit_revocation call.
    revoked_tokens: Arc<std::sync::RwLock<HashSet<String>>>,
}

/// A cached snapshot of the latest attested root from the federation.
#[derive(Clone, Debug)]
pub struct CachedAttestedRoot {
    /// The Merkle root hash.
    pub root: [u8; 32],
    /// The block height at which this root was finalized.
    pub height: u64,
    /// Unix timestamp when the root was produced.
    pub timestamp: i64,
    /// The quorum certificate that attests to this root.
    pub qc: QuorumCertificate,
}

impl FederationBridge {
    /// Create a new bridge wrapping a shared consensus node.
    pub fn new(node: Arc<Mutex<NetworkConsensusNode>>) -> Self {
        Self {
            node,
            latest_root: Arc::new(std::sync::RwLock::new(None)),
            revoked_tokens: Arc::new(std::sync::RwLock::new(HashSet::new())),
        }
    }

    /// Get the latest attested root (if any finalized block exists).
    pub fn latest_attested_root(&self) -> Option<CachedAttestedRoot> {
        self.latest_root.read().unwrap().clone()
    }

    /// Get the current federation root hash.
    ///
    /// This returns the `block_hash` from the last finalized consensus block,
    /// which incorporates the `RevocationTree` Merkle root as computed by
    /// `pyana-federation`. This is the **canonical** revocation root that should
    /// be used by the wire protocol — it supersedes both the standalone BLAKE3
    /// hash-chain in `DefaultRevocationHandler` and the raw `RevocationTree::root()`
    /// (since the block hash additionally commits to height, timestamp, and QC).
    ///
    /// Falls back to the genesis hash (`[0u8; 32]`) if nothing has been finalized yet.
    pub fn current_root(&self) -> [u8; 32] {
        self.latest_root
            .read()
            .unwrap()
            .as_ref()
            .map(|r| r.root)
            .unwrap_or([0u8; 32])
    }

    /// Get the current height.
    pub fn current_height(&self) -> u64 {
        self.latest_root
            .read()
            .unwrap()
            .as_ref()
            .map(|r| r.height)
            .unwrap_or(0)
    }

    /// Submit a revocation event to the federation consensus engine.
    ///
    /// This enqueues the event for inclusion in the next consensus round.
    /// The revocation is not final until a quorum agrees on a block containing it.
    pub async fn submit_revocation_async(
        &self,
        token_id: &str,
        authority_id: usize,
        signature: Signature,
    ) {
        let event = RevocationEvent {
            token_id: token_id.to_string(),
            authority_id,
            signature,
        };
        let mut node = self.node.lock().await;
        node.submit_revocation(event);
    }

    /// Drive one tick of the consensus engine: try to propose and process messages.
    ///
    /// Returns `Some(CachedAttestedRoot)` if a new block was finalized in this tick.
    pub async fn tick(&self) -> Option<CachedAttestedRoot> {
        let mut node = self.node.lock().await;

        // Try to propose if we're the leader with pending events.
        let _ = node.try_propose().await;

        // Process incoming messages (votes, proposals, finalizations).
        let result = node.process_messages().await.ok()?;

        if let Some((block, qc)) = result {
            let cached = CachedAttestedRoot {
                root: block.block_hash,
                height: block.height,
                timestamp: pyana_federation::types::current_timestamp(),
                qc,
            };
            *self.latest_root.write().unwrap() = Some(cached.clone());
            Some(cached)
        } else {
            None
        }
    }

    /// Convert the latest cached root into an [`AttestedRoot`] suitable for
    /// wire protocol responses.
    ///
    /// This converts the QC's votes into `(PublicKey, Signature)` pairs using
    /// the provided node identity table.
    pub fn to_attested_root(
        &self,
        nodes: &[pyana_federation::NodeIdentity],
    ) -> Option<AttestedRoot> {
        let cached = self.latest_root.read().unwrap().clone()?;
        let quorum_signatures = cached.qc.quorum_signatures(nodes);
        Some(AttestedRoot {
            merkle_root: cached.root,
            note_tree_root: None,
            nullifier_set_root: None,
            height: cached.height,
            timestamp: cached.timestamp,
            threshold_qc: cached
                .qc
                .aggregate_qc
                .as_ref()
                .map(|q| pyana_types::ThresholdQC(q.to_bytes())),
            quorum_signatures,
            threshold: cached.qc.threshold,
        })
    }
}

// =============================================================================
// RevocationHandler impl (synchronous interface for SiloServer)
// =============================================================================

impl RevocationHandler for FederationBridge {
    fn submit_revocation(&self, token_id: &str, sig: &[u8; 64]) -> bool {
        // Track revocation locally for O(1) is_revoked queries.
        self.revoked_tokens
            .write()
            .unwrap()
            .insert(token_id.to_string());

        let event = RevocationEvent {
            token_id: token_id.to_string(),
            authority_id: 0, // Wire protocol doesn't carry authority_id; default to 0
            signature: Signature(*sig),
        };
        // We need to submit without an async context. Use try_lock to avoid
        // blocking, and spawn a background task if that fails.
        match self.node.try_lock() {
            Ok(mut node) => {
                node.submit_revocation(event);
                true
            }
            Err(_) => {
                // Node is busy (e.g., processing messages). Enqueue via a
                // spawned task. The revocation will be picked up on the next
                // consensus round.
                let node = Arc::clone(&self.node);
                tokio::spawn(async move {
                    let mut n = node.lock().await;
                    n.submit_revocation(event);
                });
                true
            }
        }
    }

    fn is_revoked(&self, token_id: &str) -> bool {
        self.revoked_tokens.read().unwrap().contains(token_id)
    }

    fn current_root(&self) -> [u8; 32] {
        FederationBridge::current_root(self)
    }
}

impl std::fmt::Debug for FederationBridge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FederationBridge")
            .field(
                "latest_root",
                &self.latest_root.read().unwrap().as_ref().map(|r| r.height),
            )
            .finish()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_federation::{
        ConsensusConfig, ConsensusState, LocalTransport, NetworkConsensusNode, generate_keypair,
    };

    /// Helper: set up a 4-node federation with local transports.
    fn setup_federation() -> (
        ConsensusConfig,
        Vec<Arc<Mutex<NetworkConsensusNode>>>,
        Vec<Arc<FederationBridge>>,
    ) {
        let config = ConsensusConfig::new(4);
        let transports = LocalTransport::create_network(4);

        let mut nodes = Vec::new();
        let mut bridges = Vec::new();

        for i in 0..4 {
            let (sk, _pk) = generate_keypair();
            let state = ConsensusState::new(i, sk, config.clone());
            let node = NetworkConsensusNode::new(state, transports[i].clone(), config.clone());
            let node = Arc::new(Mutex::new(node));
            let bridge = Arc::new(FederationBridge::new(Arc::clone(&node)));
            nodes.push(node);
            bridges.push(bridge);
        }

        (config, nodes, bridges)
    }

    #[tokio::test]
    async fn bridge_submit_and_tick_produces_qc() {
        let (config, _nodes, bridges) = setup_federation();

        // Submit a revocation to node 0's bridge.
        bridges[0]
            .submit_revocation_async("tok-bridge-1", 0, Signature([0x42; 64]))
            .await;

        // Determine leader for view 1.
        let leader_id = config.leader_for_view(1);

        // If the leader isn't node 0, forward the event.
        if leader_id != 0 {
            bridges[leader_id]
                .submit_revocation_async("tok-bridge-1", 0, Signature([0x42; 64]))
                .await;
        }

        // Leader proposes.
        let proposed = bridges[leader_id].tick().await;
        // The leader's tick should broadcast a proposal (no finalization yet
        // because other nodes haven't voted).
        // After the leader ticks, it has self-voted but needs threshold votes.

        // Other nodes process the proposal and vote.
        for i in 0..4 {
            if i == leader_id {
                continue;
            }
            bridges[i].tick().await;
        }

        // Leader collects votes and should finalize.
        let finalized = bridges[leader_id].tick().await;
        assert!(
            finalized.is_some(),
            "leader should finalize after collecting threshold votes"
        );

        let root = finalized.unwrap();
        assert_eq!(root.height, 1);
        assert!(root.qc.is_valid());

        // Verify the cached root is accessible.
        let cached = bridges[leader_id].latest_attested_root();
        assert!(cached.is_some());
        assert_eq!(cached.unwrap().height, 1);
    }

    #[tokio::test]
    async fn bridge_current_root_updates_after_finalization() {
        let (config, _nodes, bridges) = setup_federation();

        // Initially, root is zeros (nothing finalized).
        assert_eq!(bridges[0].current_root(), [0u8; 32]);
        assert_eq!(bridges[0].current_height(), 0);

        let leader_id = config.leader_for_view(1);

        // Submit and run a round.
        bridges[leader_id]
            .submit_revocation_async("tok-root-test", 0, Signature([0xAA; 64]))
            .await;

        // Leader proposes.
        bridges[leader_id].tick().await;

        // Others vote.
        for i in 0..4 {
            if i == leader_id {
                continue;
            }
            bridges[i].tick().await;
        }

        // Leader finalizes.
        bridges[leader_id].tick().await;

        // Now the leader's bridge should have a non-zero root.
        assert_ne!(bridges[leader_id].current_root(), [0u8; 32]);
        assert_eq!(bridges[leader_id].current_height(), 1);
    }

    #[tokio::test]
    async fn bridge_as_revocation_handler() {
        let (_config, _nodes, bridges) = setup_federation();

        // Use the RevocationHandler trait interface (synchronous).
        let handler: &dyn RevocationHandler = bridges[0].as_ref();
        let accepted = handler.submit_revocation("tok-sync", &[0xBB; 64]);
        assert!(accepted);

        // The revocation is now pending in the node's queue.
        let node = bridges[0].node.lock().await;
        assert!(!node.state.pending_events.is_empty());
        assert_eq!(node.state.pending_events[0].token_id, "tok-sync");
    }

    #[tokio::test]
    async fn federation_qc_served_via_wire_server() {
        use crate::connection::PeerConnection;
        use crate::message::{PROTOCOL_VERSION, WireMessage};
        use crate::server::{NoopVerifier, SiloConfig, SiloServer};

        let (config, _nodes, bridges) = setup_federation();
        let leader_id = config.leader_for_view(1);

        // Run a consensus round to produce a QC.
        bridges[leader_id]
            .submit_revocation_async("tok-wire-serve", 0, Signature([0xCC; 64]))
            .await;
        bridges[leader_id].tick().await;
        for i in 0..4 {
            if i == leader_id {
                continue;
            }
            bridges[i].tick().await;
        }
        let finalized = bridges[leader_id].tick().await;
        assert!(finalized.is_some(), "should have finalized");

        // Create a SiloServer with the federation bridge as its revocation handler.
        let silo_config = SiloConfig::new("federation-silo").with_verifier(Arc::new(NoopVerifier));
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), silo_config)
            .with_revocation_handler(bridges[leader_id].clone() as Arc<dyn RevocationHandler>);

        // Update the server's state with the federation root.
        let root = bridges[leader_id].current_root();
        let height = bridges[leader_id].current_height();
        server.set_federation_root(root, height).await;

        // Start the server.
        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });
        let addr = addr_rx.await.unwrap();

        // Connect a client and request the attested root.
        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();
        client.send(WireMessage::RequestAttestedRoot).await.unwrap();

        let response = client.recv().await.unwrap();
        match response {
            WireMessage::AttestedRoot {
                root: served_root,
                height: served_height,
                ..
            } => {
                assert_eq!(served_root, root);
                assert_eq!(served_height, height);
                assert_ne!(served_root, [0u8; 32], "root should not be genesis zeros");
            }
            other => panic!("expected AttestedRoot, got {other:?}"),
        }
    }
}
