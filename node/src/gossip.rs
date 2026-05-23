//! Federation sync topic constants and gossip handle.
//!
//! This module provides the shared topic names and `GossipHandle` struct used by
//! both `blocklace_sync` and `bridge` modules.

use std::sync::Arc;

use pyana_net::PeerMessage;
use pyana_net::gossip::{GossipNetwork, TopicHandle};
use tracing::warn;

// ─── Topic name constants ────────────────────────────────────────────────────

pub const TOPIC_TURNS: &str = "pyana/turns/v1";
pub const TOPIC_REVOCATIONS: &str = "pyana/revocations/v1";
pub const TOPIC_INTENTS: &str = "pyana/intents/v1";
pub const TOPIC_ROOTS: &str = "pyana/roots/v1";
pub const TOPIC_CHECKPOINTS: &str = "pyana/checkpoints/v1";
pub const TOPIC_DECRYPTION_SHARES: &str = "pyana/decryption-shares/v1";
pub const TOPIC_BUDGET: &str = "pyana/budget/v1";

// ─── GossipHandle ────────────────────────────────────────────────────────────

/// A handle to the gossip network with pre-joined topic handles for publishing.
#[derive(Clone)]
pub struct GossipHandle {
    pub network: Arc<GossipNetwork>,
    pub topic_turns: TopicHandle,
    pub topic_revocations: TopicHandle,
    pub topic_intents: TopicHandle,
    pub topic_roots: TopicHandle,
    pub topic_checkpoints: TopicHandle,
    pub topic_decryption_shares: TopicHandle,
    pub topic_budget: TopicHandle,
}

impl GossipHandle {
    /// Publish a signed turn to the turns topic.
    pub async fn gossip_turn(&self, turn_hash: [u8; 32], turn_data: Vec<u8>) {
        let msg = PeerMessage::PublishTurn {
            turn_hash,
            turn_data,
            causal_deps: vec![],
        };
        if let Err(e) = self.network.publish(&self.topic_turns, &msg).await {
            warn!(error = %e, "failed to gossip turn");
        }
    }

    /// Publish an intent (as JSON value) to the intents topic.
    pub async fn gossip_intent(&self, intent: &serde_json::Value) {
        let intent_data = serde_json::to_vec(intent).unwrap_or_default();
        let intent_hash = *blake3::hash(&intent_data).as_bytes();
        let msg = PeerMessage::PublishIntent {
            intent_hash,
            intent_data,
        };
        if let Err(e) = self.network.publish(&self.topic_intents, &msg).await {
            warn!(error = %e, "failed to gossip intent");
        }
    }

    /// Publish an encrypted intent to the intents topic.
    pub async fn gossip_encrypted_intent(&self, enc: &pyana_intent::sse::EncryptedIntent) {
        let intent_data = postcard::to_stdvec(enc).unwrap_or_default();
        let intent_hash = *blake3::hash(&intent_data).as_bytes();
        let msg = PeerMessage::PublishIntent {
            intent_hash,
            intent_data,
        };
        if let Err(e) = self.network.publish(&self.topic_intents, &msg).await {
            warn!(error = %e, "failed to gossip encrypted intent");
        }
    }

    /// Publish an attested root update to the roots topic.
    pub async fn gossip_root(&self, root_data: Vec<u8>) {
        let msg = PeerMessage::AttestedRootUpdate { root: root_data };
        if let Err(e) = self.network.publish(&self.topic_roots, &msg).await {
            warn!(error = %e, "failed to gossip root");
        }
    }

    /// Publish a revocation to the revocations topic.
    pub async fn gossip_revocation(&self, token_id: String, signature: Vec<u8>) {
        let msg = PeerMessage::RevocationGossip {
            token_id,
            signature,
        };
        if let Err(e) = self.network.publish(&self.topic_revocations, &msg).await {
            warn!(error = %e, "failed to gossip revocation");
        }
    }
}
