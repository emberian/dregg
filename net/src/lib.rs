//! Pyana peer-to-peer networking via QUIC.
//!
//! This crate provides P2P connectivity for pyana nodes using quinn's QUIC transport.
//! It implements:
//!
//! - Direct peer-to-peer QUIC connections with self-signed certificate identity.
//! - Topic-based gossip (eager-push) for broadcasting turns and revocations.
//! - A causal DAG for tracking happened-before ordering between turns.
//!
//! # Architecture
//!
//! - [`PeerNode`] wraps a quinn `Endpoint` for direct QUIC connections between pyana nodes.
//! - [`GossipNetwork`] provides topic-based pub/sub using simple eager-push gossip.
//! - [`CausalDag`] tracks happened-before ordering between turns.
//! - [`PeerMessage`] defines the wire protocol for pyana-specific exchanges.
//!
//! # Note on iroh
//!
//! This crate was designed for the iroh P2P library, but iroh 0.96 has pre-release
//! dependency conflicts (ed25519-dalek 3.0.0-pre.1 vs pkcs8) that prevent compilation
//! with current toolchains. Quinn provides equivalent QUIC transport; the gossip layer
//! implements the same semantics with a simpler protocol.

pub mod causal;
pub mod gossip;
pub mod message;
pub mod node;

pub use causal::{CausalDag, CausalError, DagEntry, HashMismatch};
pub use gossip::{GossipEvent, GossipNetwork, MessagePhase, MessageStream, TopicHandle};
pub use message::PeerMessage;
pub use node::{
    AllowlistVerifier, ConnectionRateLimiter, NodeId, PeerConnection, PeerNode, PeerNodeConfig,
};
