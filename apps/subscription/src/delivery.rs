//! Store-and-forward content delivery.
//!
//! When a creator publishes content, the delivery layer:
//!
//! 1. Looks up every active subscriber of the target tier.
//! 2. Encrypts the content to each subscriber's `recv_pubkey` using
//!    [`crate::crypto::encrypt_for`] (a fresh ephemeral keypair per
//!    subscriber, per push — perfect forward secrecy across subscribers).
//! 3. Pushes the ciphertext into the shared `CapInbox` as
//!    `InboxMessage::Encrypted { ciphertext, sender }`.
//!
//! The receiver (subscriber) drains the inbox out-of-band, retrieves the
//! ciphertext, and runs [`crate::crypto::decrypt_with`] using their X25519
//! private key.
//!
//! # Caveat about CapInbox's read_next
//!
//! `CapInbox::read_next` returns only `(QueueEntry, DequeueProof)` — it does
//! NOT return the original message body. The body is content-addressed
//! through `entry.content_hash`. For tests we therefore retain the pushed
//! ciphertext in a side-channel `PushedContent` log keyed by content_hash;
//! this also doubles as a re-delivery mechanism. See REVIEW[P1].
//!
//! # REVIEW
//!
// REVIEW[P1]: `CapInbox::read_next` exposes only metadata, so a real
// subscriber today can't retrieve a delivered ciphertext via the inbox HTTP
// route alone — they need a separate content-fetch endpoint keyed by
// `content_hash`. The framework gap is: `CapInbox` should grow a
// `read_next_with_message` accessor, or the inbox should store the full
// message bytes (not just their hash). Until then we keep a side-log in
// `DeliveryLog` that the server exposes via `GET /content/{hash}`.

use std::collections::HashMap;
use std::sync::Arc;

use pyana_storage::QuotaId;
use pyana_storage::inbox::{CapInbox, InboxError, InboxMessage};
use pyana_types::PublicKey;
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tokio::sync::Mutex;

use crate::creator::{ContentItem, Creator};
use crate::crypto::encrypt_for;
use crate::subscriber::SubscriberRegistry;

/// One delivery: encrypted bytes that were pushed to a subscriber.
///
/// Stored both for re-fetch (because CapInbox doesn't return message bodies)
/// and for audit.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PushedContent {
    pub content_hash: [u8; 32],
    pub subscriber: PublicKey,
    pub ciphertext: Vec<u8>,
    pub epoch: u64,
}

#[derive(Debug, Error)]
pub enum DeliveryError {
    #[error("tier {0:?} not offered by creator")]
    UnknownTier(String),
    #[error("inbox rejected message: {0:?}")]
    InboxRejected(InboxError),
}

/// Side-log holding the actual ciphertext bodies of pushed content. Indexed
/// by `(subscriber, content_hash)` so subscribers can fetch their own
/// ciphertexts after the fact.
#[derive(Default)]
pub struct DeliveryLog {
    pub items: HashMap<(PublicKey, [u8; 32]), PushedContent>,
}

impl DeliveryLog {
    pub fn new() -> Self {
        Self::default()
    }

    /// Fetch a ciphertext by (subscriber, content_hash).
    pub fn get(&self, subscriber: PublicKey, content_hash: &[u8; 32]) -> Option<&PushedContent> {
        self.items.get(&(subscriber, *content_hash))
    }

    pub fn record(&mut self, push: PushedContent) {
        self.items
            .insert((push.subscriber, push.content_hash), push);
    }
}

/// Build a new `CapInbox` with subscription-app defaults. Used by the server
/// to construct the shared subscriber inbox.
pub fn new_subscriber_inbox(capacity: usize) -> CapInbox {
    CapInbox::new(QuotaId(0), capacity, 0)
}

/// Publish a creator's content item to all matching subscribers.
///
/// For each active subscriber of `item.tier_id` belonging to `creator`:
/// 1. Encrypts `item.body` to the subscriber's `recv_pubkey`.
/// 2. Calls `CapInbox::receive` with `InboxMessage::Encrypted { ciphertext, sender }`.
/// 3. Records the ciphertext in `delivery_log` so the subscriber can fetch it.
///
/// Returns the list of pushed content (one entry per subscriber successfully
/// delivered to).
pub async fn publish_to_subscribers(
    creator: &Creator,
    item: &ContentItem,
    registry: &SubscriberRegistry,
    inbox: &Arc<Mutex<CapInbox>>,
    delivery_log: &Arc<Mutex<DeliveryLog>>,
) -> Result<Vec<PushedContent>, DeliveryError> {
    let _tier = creator
        .tier(&item.tier_id)
        .ok_or_else(|| DeliveryError::UnknownTier(item.tier_id.clone()))?;

    let subscribers = registry.subscribers_of(creator.identity, &item.tier_id);
    let mut pushed = Vec::with_capacity(subscribers.len());

    // We hold the inbox lock across the whole loop. This is fine because
    // each iteration only does a small amount of work (encrypt + enqueue).
    let mut inbox_guard = inbox.lock().await;
    let mut log_guard = delivery_log.lock().await;

    for sub in subscribers {
        if sub.recv_pubkey == [0u8; 32] {
            // No published recv key; skip (can't encrypt to them).
            continue;
        }
        let ciphertext = encrypt_for(&sub.recv_pubkey, &item.body);
        let msg = InboxMessage::Encrypted {
            ciphertext: ciphertext.clone(),
            sender: creator.identity.0,
        };
        // Push to inbox. If full, skip this subscriber (REVIEW[P3]: should
        // surface a per-subscriber error instead of swallowing).
        match inbox_guard.receive_at(msg, 0, item.epoch) {
            Ok(_root) => {
                let push = PushedContent {
                    content_hash: item.content_hash,
                    subscriber: sub.subscriber,
                    ciphertext,
                    epoch: item.epoch,
                };
                log_guard.record(push.clone());
                pushed.push(push);
            }
            Err(InboxError::Full { .. }) => {
                continue;
            }
            Err(e) => {
                return Err(DeliveryError::InboxRejected(e));
            }
        }
    }
    Ok(pushed)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::creator::{Creator, Tier};
    use crate::crypto::{decrypt_with, pubkey_from_privkey};
    use crate::subscriber::{SubscriberRegistry, deterministic_cclerk};

    fn cclerk(seed: u8) -> pyana_sdk::AgentCipherclerk {
        let mut s = [0u8; 32];
        s[0] = seed;
        s[31] = seed.wrapping_mul(13);
        deterministic_cclerk(s)
    }

    /// ADVERSARIAL: published content lands in the inbox as ciphertext that
    /// does NOT equal the plaintext, and Alice's privkey decrypts it.
    #[tokio::test]
    async fn publish_encrypts_then_alice_decrypts() {
        let mut reg = SubscriberRegistry::new();
        let alice = cclerk(1);
        let creator_w = cclerk(2);

        let alice_priv = {
            let mut k = [0u8; 32];
            k[0] = 0xA1;
            k[31] = 0xA2;
            k
        };
        let alice_recv_pub = pubkey_from_privkey(&alice_priv);
        reg.register_subscriber(alice.public_key(), alice_recv_pub);

        let mut creator = Creator::new(creator_w.public_key());
        creator.add_tier(Tier::free("free", "F", 1));
        reg.subscribe(
            alice.public_key(),
            creator_w.public_key(),
            creator.tier("free").unwrap(),
            None,
        )
        .unwrap();

        let plaintext = b"Secret newsletter contents".to_vec();
        let hash = creator.publish("free", plaintext.clone(), 1);
        let item = creator
            .published
            .iter()
            .find(|i| i.content_hash == hash)
            .unwrap()
            .clone();

        let inbox = Arc::new(Mutex::new(new_subscriber_inbox(32)));
        let log = Arc::new(Mutex::new(DeliveryLog::new()));

        let pushed = publish_to_subscribers(&creator, &item, &reg, &inbox, &log)
            .await
            .unwrap();
        assert_eq!(pushed.len(), 1);
        let ct = &pushed[0].ciphertext;

        // Ciphertext must NOT equal the plaintext.
        assert_ne!(ct.as_slice(), plaintext.as_slice());
        // Plaintext bytes do not appear in ciphertext.
        assert!(!ct.windows(plaintext.len()).any(|w| w == plaintext));

        // Alice decrypts.
        let recovered = decrypt_with(&alice_priv, ct).unwrap();
        assert_eq!(recovered, plaintext);
    }

    /// ADVERSARIAL: Bob (wrong recipient) cannot decrypt content pushed to Alice.
    #[tokio::test]
    async fn bob_cannot_decrypt_alices_content() {
        let mut reg = SubscriberRegistry::new();
        let alice = cclerk(3);
        let creator_w = cclerk(4);

        let alice_priv = [0xA3u8; 32];
        let bob_priv = [0xB3u8; 32];
        let alice_recv_pub = pubkey_from_privkey(&alice_priv);
        reg.register_subscriber(alice.public_key(), alice_recv_pub);

        let mut creator = Creator::new(creator_w.public_key());
        creator.add_tier(Tier::free("free", "F", 1));
        reg.subscribe(
            alice.public_key(),
            creator_w.public_key(),
            creator.tier("free").unwrap(),
            None,
        )
        .unwrap();

        let plaintext = b"Top secret".to_vec();
        let hash = creator.publish("free", plaintext.clone(), 1);
        let item = creator
            .published
            .iter()
            .find(|i| i.content_hash == hash)
            .unwrap()
            .clone();

        let inbox = Arc::new(Mutex::new(new_subscriber_inbox(32)));
        let log = Arc::new(Mutex::new(DeliveryLog::new()));
        let pushed = publish_to_subscribers(&creator, &item, &reg, &inbox, &log)
            .await
            .unwrap();

        let ct = &pushed[0].ciphertext;
        let result = decrypt_with(&bob_priv, ct);
        assert!(result.is_err(), "Bob must not be able to decrypt");
    }

    /// Inbox actually has a pending message after publish (verifies the
    /// store-and-forward leg).
    #[tokio::test]
    async fn inbox_has_pending_after_publish() {
        let mut reg = SubscriberRegistry::new();
        let alice = cclerk(5);
        let creator_w = cclerk(6);
        let alice_priv = [0xC1u8; 32];
        reg.register_subscriber(alice.public_key(), pubkey_from_privkey(&alice_priv));

        let mut creator = Creator::new(creator_w.public_key());
        creator.add_tier(Tier::free("free", "F", 1));
        reg.subscribe(
            alice.public_key(),
            creator_w.public_key(),
            creator.tier("free").unwrap(),
            None,
        )
        .unwrap();

        let hash = creator.publish("free", b"hi".to_vec(), 0);
        let item = creator
            .published
            .iter()
            .find(|i| i.content_hash == hash)
            .unwrap()
            .clone();

        let inbox = Arc::new(Mutex::new(new_subscriber_inbox(32)));
        let log = Arc::new(Mutex::new(DeliveryLog::new()));
        publish_to_subscribers(&creator, &item, &reg, &inbox, &log)
            .await
            .unwrap();

        let status = inbox.lock().await.status();
        assert_eq!(status.pending_messages, 1);
    }

    /// Subscriber with no recv key registered is skipped (no panic).
    #[tokio::test]
    async fn subscriber_without_recv_key_is_skipped() {
        let mut reg = SubscriberRegistry::new();
        let alice = cclerk(7);
        let creator_w = cclerk(8);

        // NOTE: don't call register_subscriber, so recv_pubkey is [0; 32].
        let mut creator = Creator::new(creator_w.public_key());
        creator.add_tier(Tier::free("free", "F", 1));
        reg.subscribe(
            alice.public_key(),
            creator_w.public_key(),
            creator.tier("free").unwrap(),
            None,
        )
        .unwrap();

        let hash = creator.publish("free", b"hi".to_vec(), 0);
        let item = creator
            .published
            .iter()
            .find(|i| i.content_hash == hash)
            .unwrap()
            .clone();

        let inbox = Arc::new(Mutex::new(new_subscriber_inbox(32)));
        let log = Arc::new(Mutex::new(DeliveryLog::new()));
        let pushed = publish_to_subscribers(&creator, &item, &reg, &inbox, &log)
            .await
            .unwrap();
        assert_eq!(pushed.len(), 0);
    }
}
