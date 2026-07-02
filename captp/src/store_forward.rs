//! Store-and-forward netlayer for offline-first mobile operation.
//!
//! When a destination node is offline, capability messages are encrypted to the
//! destination's public key and queued on a relay (or directly in the blocklace DAG).
//! When the destination comes online, it retrieves and decrypts pending messages,
//! processing them in causal order.
//!
//! # Encryption
//!
//! Messages are end-to-end encrypted using X25519 Diffie-Hellman key agreement
//! with ChaCha20-Poly1305 authenticated encryption. The relay cannot read message
//! contents.
//!
//! # Blocklace Integration
//!
//! The blocklace itself serves as the store-and-forward layer: encrypted messages
//! are stored as blocks with opaque payloads. When the destination syncs the DAG
//! (frontier exchange), it naturally receives queued messages and decrypts them.

use std::collections::{HashMap, VecDeque};

use serde::{Deserialize, Serialize};

// TODO(unified-lace): migrate FederationId to StrandId/FabricAddress.
// Destinations should be FabricAddress; queues should be keyed by StrandId.
use crate::FederationId;

// =============================================================================
// Types
// =============================================================================

/// Priority level for store-and-forward messages.
///
/// Relays may use this to decide eviction order under storage pressure:
/// low-priority messages are evicted first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum MessagePriority {
    /// Low priority (GC notifications, non-urgent housekeeping).
    Low = 0,
    /// Normal priority (capability exercise, state updates).
    Normal = 1,
    /// High priority (payments, time-sensitive obligations).
    High = 2,
}

/// A queued message encrypted to its destination.
///
/// The relay stores these opaquely; only the destination can decrypt the payload.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QueuedMessage {
    /// Who this message is destined for.
    pub destination: FederationId,
    /// Encrypted payload (ChaCha20-Poly1305 ciphertext). Only the destination can decrypt.
    pub encrypted_payload: Vec<u8>,
    /// Ephemeral X25519 public key used for DH key agreement.
    /// The destination combines this with their secret key to derive the decryption key.
    pub sender_ephemeral_pk: [u8; 32],
    /// Causal sequence number. Messages MUST be processed in this order per-sender.
    pub causal_sequence: u64,
    /// Block height at which this message was queued (for TTL computation).
    pub queued_at: u64,
    /// Time-to-live in blocks. If not delivered within this window, the message
    /// is dropped by the relay during expiry sweeps.
    pub ttl_blocks: u64,
    /// Message priority hint for relay eviction policy.
    pub priority: MessagePriority,
}

// =============================================================================
// Errors
// =============================================================================

/// Errors returned by the relay when enqueuing messages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RelayError {
    /// The destination's queue has reached max depth (DoS protection).
    QueueFull {
        destination: FederationId,
        max: usize,
    },
    /// The relay's total storage capacity has been reached.
    StorageFull { max_total: usize },
    /// TTL is zero or invalid.
    InvalidTtl,
}

impl std::fmt::Display for RelayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RelayError::QueueFull { destination, max } => {
                write!(f, "queue full for {destination} (max {max})")
            }
            RelayError::StorageFull { max_total } => {
                write!(f, "relay storage full (max {max_total} messages)")
            }
            RelayError::InvalidTtl => write!(f, "invalid TTL (must be > 0)"),
        }
    }
}

impl std::error::Error for RelayError {}

/// Errors when decrypting incoming messages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecryptError {
    /// The shared secret derivation failed (invalid ephemeral key).
    InvalidEphemeralKey,
    /// AEAD decryption failed (wrong key, tampered ciphertext, or wrong nonce).
    DecryptionFailed,
    /// The ciphertext is too short to contain a valid AEAD tag.
    CiphertextTooShort,
}

impl std::fmt::Display for DecryptError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DecryptError::InvalidEphemeralKey => write!(f, "invalid ephemeral public key"),
            DecryptError::DecryptionFailed => write!(f, "AEAD decryption failed"),
            DecryptError::CiphertextTooShort => write!(f, "ciphertext too short"),
        }
    }
}

impl std::error::Error for DecryptError {}

/// Result of attempting to send a message.
#[derive(Clone, Debug)]
pub enum SendResult {
    /// Delivered directly to the destination (which was online).
    Direct {
        /// Whether the destination acknowledged receipt.
        acknowledged: bool,
    },
    /// Queued on a relay (destination was offline).
    Queued {
        /// Which relay is holding the message.
        relay: FederationId,
        /// The causal sequence number assigned to this message.
        sequence: u64,
    },
    /// Sending failed entirely (no relay available, all queues full, etc.).
    Failed {
        /// Human-readable failure reason.
        reason: String,
    },
}

// =============================================================================
// Encryption primitives
// =============================================================================
//
// Real, vetted AEAD stack (replaces the prior BLAKE3-XOR keystream spike):
//
//   X25519 ECDH  (x25519-dalek, constant-time Montgomery ladder)
//     -> HKDF-SHA256 extract+expand  (hkdf + sha2, RFC 5869)
//        -> ChaCha20-Poly1305 AEAD  (chacha20poly1305, RFC 8439)
//
// Sender-anonymous, forward-secret box: each message uses a *fresh* ephemeral
// X25519 keypair, so the relay (which holds only ciphertext + ephemeral public
// key) cannot read, forge, or tamper with messages — it can only delay or drop.
// Compromise of a long-term destination secret does not retroactively expose
// past traffic beyond the messages still derivable from that one static key;
// the ephemeral-static design gives recipient forward secrecy against ephemeral
// compromise and unlinkable sender anonymity.
//
// # Key derivation transcript binding
//
// The HKDF `info` string binds the derived key to the full handshake transcript
// (domain tag || ephemeral_pk || dest_pk). The ephemeral and destination public
// keys are *also* fed as ChaCha20-Poly1305 associated data, so a relay cannot
// splice a ciphertext onto a different ephemeral key or re-address it to another
// recipient without the AEAD tag failing.
//
// # Nonce
//
// A fixed all-zero 96-bit nonce is used. This is safe — and standard for
// ephemeral-static ECIES-style boxes — because the AEAD key is derived from a
// *unique* per-message ephemeral keypair, so no (key, nonce) pair is ever reused.

use chacha20poly1305::aead::{Aead, KeyInit, Payload};
use chacha20poly1305::{ChaCha20Poly1305, Nonce};
use hkdf::Hkdf;
use sha2::Sha256;
use x25519_dalek::{PublicKey, StaticSecret};
use zeroize::Zeroize;

/// ChaCha20-Poly1305 authentication tag length (RFC 8439).
const POLY1305_TAG_LEN: usize = 16;

/// HKDF domain-separation / version tag. Bump on any wire-format change.
const HKDF_DOMAIN: &[u8] = b"dregg-store-forward-v2-x25519-hkdf-sha256-chacha20poly1305";

/// Derive the per-message AEAD key from the DH shared secret, binding it to the
/// full handshake transcript via HKDF-SHA256 (RFC 5869).
///
/// `salt` and `info` carry the domain tag and both public keys so the derived
/// key is unique to this (ephemeral, destination) pair and version.
fn derive_aead_key(
    shared_secret: &[u8; 32],
    ephemeral_pk: &[u8; 32],
    dest_pk: &[u8; 32],
) -> [u8; 32] {
    // Salt = domain tag (RFC 5869 allows a fixed non-secret salt).
    let hk = Hkdf::<Sha256>::new(Some(HKDF_DOMAIN), shared_secret);

    // info = domain || ephemeral_pk || dest_pk  (transcript binding).
    let mut info = Vec::with_capacity(HKDF_DOMAIN.len() + 64);
    info.extend_from_slice(HKDF_DOMAIN);
    info.extend_from_slice(ephemeral_pk);
    info.extend_from_slice(dest_pk);

    let mut key = [0u8; 32];
    hk.expand(&info, &mut key)
        .expect("HKDF-SHA256 expand of 32 bytes never fails");
    key
}

/// Associated data bound into the AEAD tag: both public keys. A relay cannot
/// re-address or splice the ciphertext onto another ephemeral key without the
/// Poly1305 tag failing.
fn aead_associated_data(ephemeral_pk: &[u8; 32], dest_pk: &[u8; 32]) -> [u8; 64] {
    let mut ad = [0u8; 64];
    ad[..32].copy_from_slice(ephemeral_pk);
    ad[32..].copy_from_slice(dest_pk);
    ad
}

/// Encrypt a payload for a specific destination using X25519 -> HKDF-SHA256 ->
/// ChaCha20-Poly1305.
///
/// Returns `(ephemeral_public_key, ciphertext)`. The ciphertext is the
/// ChaCha20-Poly1305 output with the 16-byte Poly1305 tag appended.
///
/// The `_our_identity_secret` parameter is retained for API compatibility but is
/// intentionally unused: store-and-forward boxes are *sender-anonymous* (a fresh
/// ephemeral key per message), which is the correct privacy posture for relayed
/// traffic — the relay learns nothing about the sender.
///
/// # Algorithm
///
/// 1. Generate a fresh ephemeral X25519 keypair `(e, E = e·B)`.
/// 2. DH shared secret `s = e · dest_pk`.
/// 3. `key = HKDF-SHA256(salt=domain, ikm=s, info=domain||E||dest_pk)`.
/// 4. `ct = ChaCha20Poly1305(key, nonce=0, ad=E||dest_pk).encrypt(payload)`.
/// 5. Return `(E, ct||tag)`.
pub fn encrypt_for_destination(
    payload: &[u8],
    dest_pk: &[u8; 32],
    _our_identity_secret: &[u8; 32],
) -> ([u8; 32], Vec<u8>) {
    // Step 1: fresh ephemeral X25519 keypair (StaticSecret so we can zeroize it;
    // it is used exactly once and dropped, so it is still ephemeral in effect).
    let mut eph_bytes = [0u8; 32];
    getrandom::fill(&mut eph_bytes).expect("getrandom failed");
    let ephemeral_secret = StaticSecret::from(eph_bytes);
    eph_bytes.zeroize();
    let ephemeral_public = PublicKey::from(&ephemeral_secret);
    let ephemeral_pk: [u8; 32] = *ephemeral_public.as_bytes();

    // Step 2: DH shared secret = ephemeral_secret · dest_pk.
    let dest_public = PublicKey::from(*dest_pk);
    let shared = ephemeral_secret.diffie_hellman(&dest_public);
    let shared_bytes: [u8; 32] = *shared.as_bytes();

    // Step 3: HKDF-SHA256 -> AEAD key, transcript-bound.
    let mut key = derive_aead_key(&shared_bytes, &ephemeral_pk, dest_pk);

    // Step 4: ChaCha20-Poly1305 with a zero nonce (unique key per message).
    let cipher = ChaCha20Poly1305::new((&key).into());
    let nonce = Nonce::default(); // 96-bit all-zero
    let ad = aead_associated_data(&ephemeral_pk, dest_pk);
    let ciphertext = cipher
        .encrypt(
            &nonce,
            Payload {
                msg: payload,
                aad: &ad,
            },
        )
        .expect("ChaCha20-Poly1305 encryption never fails");

    key.zeroize();

    (ephemeral_pk, ciphertext)
}

/// Decrypt a message using our X25519 secret key and the sender's ephemeral
/// public key.
///
/// `our_secret` is our raw (un-clamped) 32-byte X25519 secret; `x25519-dalek`
/// performs clamping internally.
///
/// # Algorithm
///
/// 1. DH shared secret `s = our_secret · sender_ephemeral_pk`.
/// 2. `key = HKDF-SHA256(salt=domain, ikm=s, info=domain||E||our_pk)`.
/// 3. `ChaCha20Poly1305(key, nonce=0, ad=E||our_pk).decrypt(ciphertext)`.
///
/// Returns [`DecryptError::DecryptionFailed`] on any AEAD failure (wrong key,
/// tampered ciphertext/AD, or wrong nonce).
pub fn decrypt_from_sender(
    ciphertext: &[u8],
    sender_ephemeral_pk: &[u8; 32],
    our_secret: &[u8; 32],
) -> Result<Vec<u8>, DecryptError> {
    if ciphertext.len() < POLY1305_TAG_LEN {
        return Err(DecryptError::CiphertextTooShort);
    }

    // Our static keypair: derive our public key so the transcript binding (info +
    // associated data) matches what the sender computed against `dest_pk`.
    let our_static = StaticSecret::from(*our_secret);
    let our_public = PublicKey::from(&our_static);
    let our_pk: [u8; 32] = *our_public.as_bytes();

    // Step 1: DH shared secret.
    let sender_eph_public = PublicKey::from(*sender_ephemeral_pk);
    let shared = our_static.diffie_hellman(&sender_eph_public);
    let shared_bytes: [u8; 32] = *shared.as_bytes();

    // Reject contributory-behaviour low-order points (all-zero shared secret).
    // x25519-dalek does not reject these at the API level; an all-zero shared
    // secret means the sender used a low-order ephemeral point.
    if !shared.was_contributory() {
        return Err(DecryptError::InvalidEphemeralKey);
    }

    // Step 2: HKDF-SHA256 -> AEAD key (bound to our own public key as recipient).
    let mut key = derive_aead_key(&shared_bytes, sender_ephemeral_pk, &our_pk);

    // Step 3: ChaCha20-Poly1305 decrypt + verify.
    let cipher = ChaCha20Poly1305::new((&key).into());
    let nonce = Nonce::default();
    let ad = aead_associated_data(sender_ephemeral_pk, &our_pk);
    let result = cipher
        .decrypt(
            &nonce,
            Payload {
                msg: ciphertext,
                aad: &ad,
            },
        )
        .map_err(|_| DecryptError::DecryptionFailed);

    key.zeroize();
    result
}

/// Generate an X25519 keypair `(secret, public)` for use with
/// [`encrypt_for_destination`] / [`decrypt_from_sender`].
///
/// The returned secret is the raw 32-byte scalar; clamping is performed
/// internally by `x25519-dalek` on use. The public key is `secret · B`.
pub fn generate_x25519_keypair() -> ([u8; 32], [u8; 32]) {
    let mut secret_bytes = [0u8; 32];
    getrandom::fill(&mut secret_bytes).expect("getrandom failed");
    let secret = StaticSecret::from(secret_bytes);
    let public = PublicKey::from(&secret);
    let pk = *public.as_bytes();
    let sk = secret.to_bytes();
    secret_bytes.zeroize();
    (sk, pk)
}

// =============================================================================
// MessageRelay: server-side message queue
// =============================================================================

/// A relay node's message queue for offline destinations.
///
/// The relay stores encrypted messages until the destination comes online
/// and drains its queue. Storage limits prevent DoS.
#[derive(Clone, Debug)]
pub struct MessageRelay {
    /// Per-destination message queues.
    queues: HashMap<FederationId, VecDeque<QueuedMessage>>,
    /// Maximum messages per single destination (prevents one party from hogging storage).
    max_queue_depth: usize,
    /// Maximum total messages across all destinations.
    max_total_messages: usize,
    /// Current total message count.
    total_messages: usize,
}

impl MessageRelay {
    /// Create a new relay with the given storage limits.
    pub fn new(max_queue_depth: usize, max_total_messages: usize) -> Self {
        Self {
            queues: HashMap::new(),
            max_queue_depth,
            max_total_messages,
            total_messages: 0,
        }
    }

    /// Queue a message for an offline destination.
    ///
    /// Fails if the destination's queue is full or the relay's total capacity is exhausted.
    pub fn enqueue(&mut self, msg: QueuedMessage) -> Result<(), RelayError> {
        if msg.ttl_blocks == 0 {
            return Err(RelayError::InvalidTtl);
        }

        // Check total storage
        if self.total_messages >= self.max_total_messages {
            return Err(RelayError::StorageFull {
                max_total: self.max_total_messages,
            });
        }

        // Check per-destination depth
        let queue = self.queues.entry(msg.destination).or_default();
        if queue.len() >= self.max_queue_depth {
            return Err(RelayError::QueueFull {
                destination: msg.destination,
                max: self.max_queue_depth,
            });
        }

        queue.push_back(msg);
        self.total_messages += 1;
        Ok(())
    }

    /// Accept custody of a message AND return a SIGNED [`CustodyReceipt`] binding the
    /// relay to it.
    ///
    /// This is the accountability seam: unlike [`Self::enqueue`] (which returns nothing
    /// and leaves a drop unprovable), `accept_custody` makes the relay SIGN a receipt over
    /// `(relay, content_hash, inbox_owner, old_root, new_root, accept_by)` — so a later
    /// drop is convictable against this relay by its own signature, while an honest
    /// delivery/refund acquits it (see [`crate::custody`], the Rust realization of
    /// `Dregg2.Exec.Custody`).
    ///
    /// * `relay_id` / `relay_key` — the operator's identity and Ed25519 signing key. In
    ///   the unified-lace model `relay_id` IS the relay's public key; the receipt is only
    ///   well-formed if they match.
    /// * `old_root` / `new_root` — the inbox-root transition the relay PROMISES to effect
    ///   on delivery (the queue head root before/after appending this box).
    /// * `accept_by` — the deadline height: deliver or refund by here, else dropped.
    ///
    /// On enqueue failure the relay accepted nothing, so NO receipt is minted (the error
    /// is propagated). On success the box is queued and the signed receipt is returned to
    /// the sender.
    #[allow(clippy::too_many_arguments)]
    pub fn accept_custody(
        &mut self,
        msg: QueuedMessage,
        relay_id: FederationId,
        relay_key: &dregg_types::SigningKey,
        inbox_owner: FederationId,
        old_root: [u8; 32],
        new_root: [u8; 32],
        accept_by: u64,
    ) -> Result<crate::custody::CustodyReceipt, RelayError> {
        // Content-address the box exactly as the relay stores it: BLAKE3 over the
        // ciphertext envelope the relay holds (the bytes the receipt commits to).
        let content_hash = *blake3::hash(&msg.encrypted_payload).as_bytes();

        // Enqueue first: only mint a receipt if custody was actually taken.
        self.enqueue(msg)?;

        Ok(crate::custody::CustodyReceipt::sign(
            relay_id,
            relay_key,
            content_hash,
            inbox_owner,
            old_root,
            new_root,
            accept_by,
        ))
    }

    /// Destination comes online: drain all pending messages.
    ///
    /// Returns messages in FIFO order (earliest queued first). The queue for this
    /// destination is cleared.
    pub fn drain(&mut self, destination: &FederationId) -> Vec<QueuedMessage> {
        let messages: Vec<QueuedMessage> = self
            .queues
            .remove(destination)
            .unwrap_or_default()
            .into_iter()
            .collect();
        self.total_messages -= messages.len();
        messages
    }

    /// Pop a SINGLE pending message (FIFO: earliest queued) for a destination,
    /// leaving the rest queued. `None` if the queue is empty. Used by a delivery
    /// path that witnesses one box at a time as it hands it to a consumer (so the
    /// spool drains in lockstep with delivery instead of all-at-once).
    pub fn drain_one(&mut self, destination: &FederationId) -> Option<QueuedMessage> {
        let queue = self.queues.get_mut(destination)?;
        let msg = queue.pop_front();
        if msg.is_some() {
            self.total_messages -= 1;
        }
        if queue.is_empty() {
            self.queues.remove(destination);
        }
        msg
    }

    /// Expire messages whose TTL has been exceeded.
    ///
    /// Removes any message where `current_height - queued_at >= ttl_blocks`.
    /// Returns the number of messages expired.
    pub fn expire(&mut self, current_height: u64) -> usize {
        let mut expired = 0;
        let mut empty_keys = Vec::new();

        for (dest, queue) in self.queues.iter_mut() {
            let before = queue.len();
            queue.retain(|msg| current_height.saturating_sub(msg.queued_at) < msg.ttl_blocks);
            let removed = before - queue.len();
            expired += removed;
            if queue.is_empty() {
                empty_keys.push(*dest);
            }
        }

        // Remove empty queues
        for key in empty_keys {
            self.queues.remove(&key);
        }

        self.total_messages -= expired;
        expired
    }

    /// How many messages are pending for a specific destination.
    pub fn pending_count(&self, destination: &FederationId) -> usize {
        self.queues.get(destination).map_or(0, |q| q.len())
    }

    /// Total messages stored across all destinations.
    pub fn total_stored(&self) -> usize {
        self.total_messages
    }

    /// Number of destinations with pending messages.
    pub fn active_destinations(&self) -> usize {
        self.queues.len()
    }
}

// =============================================================================
// StoreForwardClient: sender/receiver side
// =============================================================================

/// Information about a known relay node.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RelayInfo {
    /// The relay's federation identity.
    pub federation_id: FederationId,
    /// Network endpoint for reaching this relay (URL, multiaddr, etc.).
    pub endpoint: String,
    /// Advertised remaining capacity (messages).
    pub capacity: usize,
}

/// Client-side store-and-forward manager.
///
/// Handles encrypting and routing messages through relays when the destination
/// is offline, and picking up/decrypting messages queued for us.
#[derive(Clone, Debug)]
pub struct StoreForwardClient {
    /// Our federation identity.
    pub our_federation: FederationId,
    /// Known relay nodes we can use for store-and-forward.
    relays: Vec<RelayInfo>,
    /// Messages we've sent that haven't been acknowledged by the destination.
    /// Keyed by (destination, sequence).
    unacknowledged: HashMap<(FederationId, u64), QueuedMessage>,
    /// Next causal sequence number per destination.
    sequences: HashMap<FederationId, u64>,
}

impl StoreForwardClient {
    /// Create a new store-and-forward client.
    pub fn new(our_federation: FederationId, relays: Vec<RelayInfo>) -> Self {
        Self {
            our_federation,
            relays,
            unacknowledged: HashMap::new(),
            sequences: HashMap::new(),
        }
    }

    /// Get the next sequence number for a destination (and advance the counter).
    fn next_sequence(&mut self, destination: &FederationId) -> u64 {
        let seq = self.sequences.entry(*destination).or_insert(0);
        let current = *seq;
        *seq += 1;
        current
    }

    /// Prepare a message for sending: encrypt the payload and construct a `QueuedMessage`.
    ///
    /// This does NOT perform delivery; it only prepares the encrypted message.
    /// The caller is responsible for routing it (direct or via relay).
    pub fn prepare_message(
        &mut self,
        destination: FederationId,
        payload: &[u8],
        dest_pk: &[u8; 32],
        our_secret: &[u8; 32],
        priority: MessagePriority,
        ttl_blocks: u64,
        current_height: u64,
    ) -> QueuedMessage {
        let sequence = self.next_sequence(&destination);
        let (ephemeral_pk, encrypted_payload) =
            encrypt_for_destination(payload, dest_pk, our_secret);

        QueuedMessage {
            destination,
            encrypted_payload,
            sender_ephemeral_pk: ephemeral_pk,
            causal_sequence: sequence,
            queued_at: current_height,
            ttl_blocks,
            priority,
        }
    }

    /// Attempt to send a message, falling back to relay if destination is offline.
    ///
    /// Since actual network connectivity is external to this module, this method
    /// prepares the message and queues it on the first available relay. The caller
    /// should attempt direct delivery first and only call this for relay fallback.
    pub fn queue_on_relay(&mut self, msg: QueuedMessage, relay: &mut MessageRelay) -> SendResult {
        let sequence = msg.causal_sequence;
        let destination = msg.destination;

        // Track for acknowledgment
        self.unacknowledged
            .insert((destination, sequence), msg.clone());

        match relay.enqueue(msg) {
            Ok(()) => SendResult::Queued {
                relay: self
                    .relays
                    .first()
                    .map_or(FederationId([0; 32]), |r| r.federation_id),
                sequence,
            },
            Err(e) => {
                // Remove from unacknowledged since it wasn't actually queued
                self.unacknowledged.remove(&(destination, sequence));
                SendResult::Failed {
                    reason: e.to_string(),
                }
            }
        }
    }

    /// Mark a message as acknowledged (destination confirmed receipt).
    pub fn acknowledge(&mut self, destination: &FederationId, sequence: u64) -> bool {
        self.unacknowledged
            .remove(&(*destination, sequence))
            .is_some()
    }

    /// How many unacknowledged messages are outstanding.
    pub fn unacknowledged_count(&self) -> usize {
        self.unacknowledged.len()
    }

    /// Decrypt and causally-order a batch of incoming messages.
    ///
    /// Messages are decrypted using the recipient's X25519 secret key, then sorted
    /// by causal_sequence to ensure correct processing order.
    ///
    /// Returns `(causal_sequence, plaintext)` pairs in ascending causal order.
    pub fn process_incoming(
        messages: Vec<QueuedMessage>,
        our_secret: &[u8; 32],
    ) -> Result<Vec<(u64, Vec<u8>)>, DecryptError> {
        let mut results = Vec::with_capacity(messages.len());

        for msg in messages {
            let plaintext =
                decrypt_from_sender(&msg.encrypted_payload, &msg.sender_ephemeral_pk, our_secret)?;
            results.push((msg.causal_sequence, plaintext));
        }

        // Sort by causal sequence for correct processing order
        results.sort_by_key(|(seq, _)| *seq);
        Ok(results)
    }

    /// Add a relay to the known relays list.
    pub fn add_relay(&mut self, relay: RelayInfo) {
        self.relays.push(relay);
    }

    /// Get known relays.
    pub fn relays(&self) -> &[RelayInfo] {
        &self.relays
    }
}

// =============================================================================
// Blocklace integration
// =============================================================================

/// Envelope wrapping an encrypted message for storage in the blocklace.
///
/// When stored as a block's payload, the blocklace acts as the store-and-forward
/// layer: the destination receives encrypted blocks during normal DAG sync and
/// decrypts them locally.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BlocklaceEnvelope {
    /// Magic bytes for identifying store-forward payloads in the blocklace.
    /// Always `b"pysf"` (dregg store-forward).
    pub magic: [u8; 4],
    /// The intended recipient (so nodes know which blocks to attempt decryption on).
    pub destination: FederationId,
    /// The encrypted payload.
    pub encrypted_payload: Vec<u8>,
    /// Ephemeral public key for decryption.
    pub sender_ephemeral_pk: [u8; 32],
    /// Causal sequence for ordering.
    pub causal_sequence: u64,
}

impl BlocklaceEnvelope {
    /// Magic bytes identifying a store-forward envelope in the blocklace.
    pub const MAGIC: [u8; 4] = *b"pysf";

    /// Create an envelope from a prepared queued message.
    pub fn from_queued_message(msg: &QueuedMessage) -> Self {
        Self {
            magic: Self::MAGIC,
            destination: msg.destination,
            encrypted_payload: msg.encrypted_payload.clone(),
            sender_ephemeral_pk: msg.sender_ephemeral_pk,
            causal_sequence: msg.causal_sequence,
        }
    }

    /// Serialize to bytes for use as a blocklace block payload.
    pub fn to_payload(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("envelope serialization failed")
    }

    /// Attempt to deserialize from a block payload.
    ///
    /// Returns `None` if the payload doesn't start with the magic bytes or
    /// cannot be deserialized.
    pub fn from_payload(payload: &[u8]) -> Option<Self> {
        if payload.len() < 4 || payload[..4] != Self::MAGIC {
            return None;
        }
        let envelope: Self = postcard::from_bytes(payload).ok()?;
        if envelope.magic != Self::MAGIC {
            return None;
        }
        Some(envelope)
    }

    /// Check if this envelope is addressed to us.
    pub fn is_for(&self, our_federation: &FederationId) -> bool {
        self.destination == *our_federation
    }

    /// Decrypt this envelope's payload using our secret key.
    pub fn decrypt(&self, our_secret: &[u8; 32]) -> Result<Vec<u8>, DecryptError> {
        decrypt_from_sender(
            &self.encrypted_payload,
            &self.sender_ephemeral_pk,
            our_secret,
        )
    }
}

/// Queue an encrypted message via the blocklace (no separate relay protocol needed).
///
/// Creates a serialized `BlocklaceEnvelope` that can be inserted as a block payload.
/// The destination will receive it during normal frontier-exchange-based DAG sync
/// and can decrypt it locally.
///
/// Returns the serialized payload bytes ready to be passed to `Block::new(...)`.
pub fn queue_via_blocklace(
    destination: FederationId,
    payload: &[u8],
    dest_pk: &[u8; 32],
    our_secret: &[u8; 32],
    causal_sequence: u64,
) -> Vec<u8> {
    let (ephemeral_pk, encrypted_payload) = encrypt_for_destination(payload, dest_pk, our_secret);

    let envelope = BlocklaceEnvelope {
        magic: BlocklaceEnvelope::MAGIC,
        destination,
        encrypted_payload,
        sender_ephemeral_pk: ephemeral_pk,
        causal_sequence,
    };

    envelope.to_payload()
}

/// Scan a set of block payloads for messages addressed to us, decrypt and order them.
///
/// This is what a mobile client does after syncing the blocklace: scan all new blocks
/// for envelopes addressed to our federation, decrypt them, and return in causal order.
pub fn scan_and_decrypt_blocklace(
    payloads: &[Vec<u8>],
    our_federation: &FederationId,
    our_secret: &[u8; 32],
) -> Result<Vec<(u64, Vec<u8>)>, DecryptError> {
    let mut results = Vec::new();

    for payload in payloads {
        if let Some(envelope) = BlocklaceEnvelope::from_payload(payload)
            && envelope.is_for(our_federation)
        {
            let plaintext = envelope.decrypt(our_secret)?;
            results.push((envelope.causal_sequence, plaintext));
        }
    }

    // Sort by causal sequence
    results.sort_by_key(|(seq, _)| *seq);
    Ok(results)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn fed_alice() -> FederationId {
        FederationId([0xAA; 32])
    }

    fn fed_bob() -> FederationId {
        FederationId([0xBB; 32])
    }

    fn fed_relay() -> FederationId {
        FederationId([0xCC; 32])
    }

    /// Generate a test X25519 keypair (secret, public).
    fn test_x25519_keypair() -> ([u8; 32], [u8; 32]) {
        generate_x25519_keypair()
    }

    // --- Relay tests ---

    #[test]
    fn enqueue_and_drain() {
        let mut relay = MessageRelay::new(100, 1000);
        let dest = fed_bob();

        let msg = QueuedMessage {
            destination: dest,
            encrypted_payload: vec![1, 2, 3, 4],
            sender_ephemeral_pk: [0x11; 32],
            causal_sequence: 0,
            queued_at: 100,
            ttl_blocks: 50,
            priority: MessagePriority::Normal,
        };

        relay.enqueue(msg.clone()).unwrap();
        assert_eq!(relay.pending_count(&dest), 1);
        assert_eq!(relay.total_stored(), 1);

        let drained = relay.drain(&dest);
        assert_eq!(drained.len(), 1);
        assert_eq!(drained[0].encrypted_payload, vec![1, 2, 3, 4]);
        assert_eq!(drained[0].causal_sequence, 0);
        assert_eq!(relay.pending_count(&dest), 0);
        assert_eq!(relay.total_stored(), 0);
    }

    #[test]
    fn ttl_expiry() {
        let mut relay = MessageRelay::new(100, 1000);
        let dest = fed_bob();

        // Message with TTL of 10 blocks, queued at height 100
        let msg1 = QueuedMessage {
            destination: dest,
            encrypted_payload: vec![1],
            sender_ephemeral_pk: [0x11; 32],
            causal_sequence: 0,
            queued_at: 100,
            ttl_blocks: 10,
            priority: MessagePriority::Normal,
        };

        // Message with TTL of 50 blocks, queued at height 100
        let msg2 = QueuedMessage {
            destination: dest,
            encrypted_payload: vec![2],
            sender_ephemeral_pk: [0x22; 32],
            causal_sequence: 1,
            queued_at: 100,
            ttl_blocks: 50,
            priority: MessagePriority::High,
        };

        relay.enqueue(msg1).unwrap();
        relay.enqueue(msg2).unwrap();
        assert_eq!(relay.total_stored(), 2);

        // At height 109: neither expired (10 - 1 = 9 elapsed < 10)
        let expired = relay.expire(109);
        assert_eq!(expired, 0);

        // At height 110: first message expired (110 - 100 = 10 >= 10)
        let expired = relay.expire(110);
        assert_eq!(expired, 1);
        assert_eq!(relay.total_stored(), 1);

        // At height 150: second message expired (150 - 100 = 50 >= 50)
        let expired = relay.expire(150);
        assert_eq!(expired, 1);
        assert_eq!(relay.total_stored(), 0);
    }

    #[test]
    fn queue_depth_limit() {
        let mut relay = MessageRelay::new(2, 1000); // max 2 per destination
        let dest = fed_bob();

        let make_msg = |seq| QueuedMessage {
            destination: dest,
            encrypted_payload: vec![seq as u8],
            sender_ephemeral_pk: [0x11; 32],
            causal_sequence: seq,
            queued_at: 100,
            ttl_blocks: 50,
            priority: MessagePriority::Normal,
        };

        relay.enqueue(make_msg(0)).unwrap();
        relay.enqueue(make_msg(1)).unwrap();

        // Third message should fail
        let result = relay.enqueue(make_msg(2));
        assert!(matches!(result, Err(RelayError::QueueFull { .. })));
        assert_eq!(relay.total_stored(), 2);
    }

    #[test]
    fn total_storage_limit() {
        let mut relay = MessageRelay::new(100, 2); // max 2 total
        let alice = fed_alice();
        let bob = fed_bob();

        let msg_for_alice = QueuedMessage {
            destination: alice,
            encrypted_payload: vec![1],
            sender_ephemeral_pk: [0x11; 32],
            causal_sequence: 0,
            queued_at: 100,
            ttl_blocks: 50,
            priority: MessagePriority::Normal,
        };

        let msg_for_bob = QueuedMessage {
            destination: bob,
            encrypted_payload: vec![2],
            sender_ephemeral_pk: [0x22; 32],
            causal_sequence: 0,
            queued_at: 100,
            ttl_blocks: 50,
            priority: MessagePriority::Normal,
        };

        relay.enqueue(msg_for_alice).unwrap();
        relay.enqueue(msg_for_bob).unwrap();

        // Third message to anyone should fail
        let msg3 = QueuedMessage {
            destination: alice,
            encrypted_payload: vec![3],
            sender_ephemeral_pk: [0x33; 32],
            causal_sequence: 1,
            queued_at: 100,
            ttl_blocks: 50,
            priority: MessagePriority::Normal,
        };
        let result = relay.enqueue(msg3);
        assert!(matches!(result, Err(RelayError::StorageFull { .. })));
    }

    #[test]
    fn causal_ordering_preserved() {
        let mut relay = MessageRelay::new(100, 1000);
        let dest = fed_bob();

        // Enqueue out of order
        for seq in [3u64, 1, 4, 0, 2] {
            let msg = QueuedMessage {
                destination: dest,
                encrypted_payload: vec![seq as u8],
                sender_ephemeral_pk: [seq as u8; 32],
                causal_sequence: seq,
                queued_at: 100,
                ttl_blocks: 50,
                priority: MessagePriority::Normal,
            };
            relay.enqueue(msg).unwrap();
        }

        let mut drained = relay.drain(&dest);
        // Drain returns FIFO order (insertion order), but the client sorts by causal_sequence
        drained.sort_by_key(|m| m.causal_sequence);

        let sequences: Vec<u64> = drained.iter().map(|m| m.causal_sequence).collect();
        assert_eq!(sequences, vec![0, 1, 2, 3, 4]);
    }

    // --- Encryption tests ---

    #[test]
    fn encrypt_decrypt_various_payloads() {
        let (bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _alice_public) = test_x25519_keypair();

        let cases: Vec<Vec<u8>> = vec![
            b"hello capability world".to_vec(),
            b"".to_vec(),
            (0..256).map(|i| i as u8).collect(),
        ];

        for plaintext in &cases {
            let (ephemeral_pk, ciphertext) =
                encrypt_for_destination(plaintext, &bob_public, &alice_secret);

            let decrypted = decrypt_from_sender(&ciphertext, &ephemeral_pk, &bob_secret).unwrap();
            assert_eq!(decrypted, plaintext.as_slice());
        }
    }

    #[test]
    fn wrong_key_decryption_fails() {
        let (_bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _alice_public) = test_x25519_keypair();
        let (eve_secret, _eve_public) = test_x25519_keypair();

        let plaintext = b"secret capability message";

        let (ephemeral_pk, ciphertext) =
            encrypt_for_destination(plaintext, &bob_public, &alice_secret);

        // Eve tries to decrypt with her key — should fail
        let result = decrypt_from_sender(&ciphertext, &ephemeral_pk, &eve_secret);
        assert!(result.is_err() || result.unwrap() != plaintext);
    }

    #[test]
    fn ciphertext_too_short() {
        let (bob_secret, _) = test_x25519_keypair();
        let short = vec![0u8; 5]; // Less than POLY1305_TAG_LEN
        let result = decrypt_from_sender(&short, &[0; 32], &bob_secret);
        assert_eq!(result.unwrap_err(), DecryptError::CiphertextTooShort);
    }

    #[test]
    fn tampered_ciphertext_fails() {
        let (bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _) = test_x25519_keypair();

        let plaintext = b"do not tamper";
        let (ephemeral_pk, mut ciphertext) =
            encrypt_for_destination(plaintext, &bob_public, &alice_secret);

        // Flip a bit in the ciphertext body (before the tag)
        if !ciphertext.is_empty() {
            ciphertext[0] ^= 0xFF;
        }

        let result = decrypt_from_sender(&ciphertext, &ephemeral_pk, &bob_secret);
        assert!(matches!(result, Err(DecryptError::DecryptionFailed)));
    }

    #[test]
    fn tampered_tag_fails() {
        let (bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _) = test_x25519_keypair();

        let plaintext = b"integrity-protected";
        let (ephemeral_pk, mut ciphertext) =
            encrypt_for_destination(plaintext, &bob_public, &alice_secret);

        // Flip a bit in the Poly1305 tag (last 16 bytes).
        let last = ciphertext.len() - 1;
        ciphertext[last] ^= 0x01;

        let result = decrypt_from_sender(&ciphertext, &ephemeral_pk, &bob_secret);
        assert!(matches!(result, Err(DecryptError::DecryptionFailed)));
    }

    #[test]
    fn readdressed_ephemeral_key_rejected() {
        // A relay must not be able to swap the advertised ephemeral public key:
        // it is bound into both the HKDF transcript and the AEAD associated data.
        let (bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _) = test_x25519_keypair();

        let plaintext = b"do not re-address";
        let (_ephemeral_pk, ciphertext) =
            encrypt_for_destination(plaintext, &bob_public, &alice_secret);

        // Present a *different* (valid) ephemeral key alongside the real ciphertext.
        let (_attacker_secret, attacker_eph) = test_x25519_keypair();
        let result = decrypt_from_sender(&ciphertext, &attacker_eph, &bob_secret);
        assert!(result.is_err());
    }

    #[test]
    fn relay_sees_only_ciphertext() {
        // What a relay actually holds is a QueuedMessage: destination + opaque
        // ciphertext + ephemeral pk + routing metadata. It never holds a key
        // capable of decryption, and the plaintext must not appear in the box.
        let (bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _) = test_x25519_keypair();

        let plaintext = b"PLAINTEXT-NEEDLE-capability-grant";
        let mut client = StoreForwardClient::new(fed_alice(), vec![]);
        let msg = client.prepare_message(
            fed_bob(),
            plaintext,
            &bob_public,
            &alice_secret,
            MessagePriority::Normal,
            100,
            10,
        );

        // The relay's stored bytes must not contain the plaintext anywhere.
        let needle = b"PLAINTEXT-NEEDLE";
        assert!(
            !msg.encrypted_payload
                .windows(needle.len())
                .any(|w| w == needle),
            "plaintext leaked into the relay-visible ciphertext"
        );

        // The relay has no secret key; it can only move opaque bytes. Confirm the
        // ciphertext is genuinely opaque to anyone without bob's secret: a fresh
        // (relay-style) keypair cannot decrypt.
        let (relay_secret, _relay_public) = test_x25519_keypair();
        assert!(
            decrypt_from_sender(
                &msg.encrypted_payload,
                &msg.sender_ephemeral_pk,
                &relay_secret
            )
            .is_err(),
            "a party without bob's secret could decrypt"
        );

        // The legitimate recipient still recovers the plaintext.
        let recovered = decrypt_from_sender(
            &msg.encrypted_payload,
            &msg.sender_ephemeral_pk,
            &bob_secret,
        )
        .unwrap();
        assert_eq!(recovered, plaintext);
    }

    #[test]
    fn fresh_ephemeral_key_per_message() {
        // Forward secrecy / unlinkability: each message uses a distinct ephemeral
        // public key, and the same plaintext encrypts to distinct ciphertexts.
        let (_bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _) = test_x25519_keypair();

        let plaintext = b"same plaintext twice";
        let (eph1, ct1) = encrypt_for_destination(plaintext, &bob_public, &alice_secret);
        let (eph2, ct2) = encrypt_for_destination(plaintext, &bob_public, &alice_secret);

        assert_ne!(eph1, eph2, "ephemeral keys must be fresh per message");
        assert_ne!(
            ct1, ct2,
            "ciphertexts must not be identical (no nonce reuse leak)"
        );
    }

    // --- Client tests ---

    #[test]
    fn client_prepare_and_process() {
        let (bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _alice_public) = test_x25519_keypair();

        let mut client = StoreForwardClient::new(
            fed_alice(),
            vec![RelayInfo {
                federation_id: fed_relay(),
                endpoint: "relay.example.com".into(),
                capacity: 1000,
            }],
        );

        let messages_to_send = vec![
            b"first capability invocation".to_vec(),
            b"second capability invocation".to_vec(),
            b"third capability invocation".to_vec(),
        ];

        let mut queued_messages = Vec::new();
        for payload in &messages_to_send {
            let msg = client.prepare_message(
                fed_bob(),
                payload,
                &bob_public,
                &alice_secret,
                MessagePriority::Normal,
                100,
                500,
            );
            queued_messages.push(msg);
        }

        // Verify sequence numbers are monotonically increasing
        assert_eq!(queued_messages[0].causal_sequence, 0);
        assert_eq!(queued_messages[1].causal_sequence, 1);
        assert_eq!(queued_messages[2].causal_sequence, 2);

        // Bob processes the incoming messages
        let results = StoreForwardClient::process_incoming(queued_messages, &bob_secret).unwrap();

        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (0, b"first capability invocation".to_vec()));
        assert_eq!(results[1], (1, b"second capability invocation".to_vec()));
        assert_eq!(results[2], (2, b"third capability invocation".to_vec()));
    }

    #[test]
    fn client_queue_on_relay() {
        let (_bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _) = test_x25519_keypair();

        let mut client = StoreForwardClient::new(fed_alice(), vec![]);
        let mut relay = MessageRelay::new(100, 1000);

        let msg = client.prepare_message(
            fed_bob(),
            b"offline message",
            &bob_public,
            &alice_secret,
            MessagePriority::High,
            50,
            200,
        );

        let result = client.queue_on_relay(msg, &mut relay);
        assert!(matches!(result, SendResult::Queued { sequence: 0, .. }));
        assert_eq!(client.unacknowledged_count(), 1);
        assert_eq!(relay.pending_count(&fed_bob()), 1);

        // Acknowledge
        client.acknowledge(&fed_bob(), 0);
        assert_eq!(client.unacknowledged_count(), 0);
    }

    // --- Blocklace integration tests ---

    #[test]
    fn blocklace_envelope_roundtrip() {
        let (bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _) = test_x25519_keypair();

        let plaintext = b"capability message via blocklace";
        let payload_bytes =
            queue_via_blocklace(fed_bob(), plaintext, &bob_public, &alice_secret, 42);

        // Simulate: block is stored in blocklace, destination syncs and scans
        let envelope = BlocklaceEnvelope::from_payload(&payload_bytes).unwrap();
        assert!(envelope.is_for(&fed_bob()));
        assert!(!envelope.is_for(&fed_alice()));
        assert_eq!(envelope.causal_sequence, 42);

        // Decrypt
        let decrypted = envelope.decrypt(&bob_secret).unwrap();
        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn scan_and_decrypt_multiple() {
        let (bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _) = test_x25519_keypair();

        let messages = [
            (b"msg-zero".as_slice(), 0u64),
            (b"msg-one".as_slice(), 1u64),
            (b"msg-two".as_slice(), 2u64),
        ];

        // Create payloads (simulating blocks in the blocklace)
        let mut payloads: Vec<Vec<u8>> = Vec::new();

        // Add some non-store-forward payloads (should be skipped)
        payloads.push(b"random blocklace data".to_vec());
        payloads.push(vec![0xDE, 0xAD, 0xBE, 0xEF]);

        // Add store-forward envelopes (intentionally out of causal order)
        for (msg, seq) in messages.iter().rev() {
            payloads.push(queue_via_blocklace(
                fed_bob(),
                msg,
                &bob_public,
                &alice_secret,
                *seq,
            ));
        }

        // Also add a message for someone else (should be skipped)
        let (_other_secret, other_pk) = test_x25519_keypair();
        payloads.push(queue_via_blocklace(
            fed_alice(),
            b"not for bob",
            &other_pk,
            &alice_secret,
            99,
        ));

        // Bob scans the blocklace
        let results = scan_and_decrypt_blocklace(&payloads, &fed_bob(), &bob_secret).unwrap();

        assert_eq!(results.len(), 3);
        // Should be in causal order
        assert_eq!(results[0], (0, b"msg-zero".to_vec()));
        assert_eq!(results[1], (1, b"msg-one".to_vec()));
        assert_eq!(results[2], (2, b"msg-two".to_vec()));
    }

    #[test]
    fn blocklace_bad_magic_is_skipped_without_decrypt_error() {
        let (bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _) = test_x25519_keypair();

        let mut payload_bytes =
            queue_via_blocklace(fed_bob(), b"secret", &bob_public, &alice_secret, 7);
        payload_bytes[0] ^= 0x01;

        assert!(BlocklaceEnvelope::from_payload(&payload_bytes).is_none());

        let results = scan_and_decrypt_blocklace(&[payload_bytes], &fed_bob(), &bob_secret)
            .expect("bad magic should be skipped before decrypt");
        assert!(results.is_empty());
    }

    #[test]
    fn blocklace_wrong_key_fails() {
        let (_bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _) = test_x25519_keypair();
        let (eve_secret, _) = test_x25519_keypair();

        let payload_bytes =
            queue_via_blocklace(fed_bob(), b"secret", &bob_public, &alice_secret, 0);

        let envelope = BlocklaceEnvelope::from_payload(&payload_bytes).unwrap();

        // Eve tries to decrypt
        let result = envelope.decrypt(&eve_secret);
        // Should either error or produce wrong plaintext
        match result {
            Err(_) => {}                                       // Good: decryption failed
            Ok(plaintext) => assert_ne!(plaintext, b"secret"), // Also acceptable: wrong output
        }
    }

    #[test]
    fn invalid_ttl_rejected() {
        let mut relay = MessageRelay::new(100, 1000);

        let msg = QueuedMessage {
            destination: fed_bob(),
            encrypted_payload: vec![1, 2, 3],
            sender_ephemeral_pk: [0x11; 32],
            causal_sequence: 0,
            queued_at: 100,
            ttl_blocks: 0, // Invalid!
            priority: MessagePriority::Normal,
        };

        let result = relay.enqueue(msg);
        assert_eq!(result.unwrap_err(), RelayError::InvalidTtl);
    }
}
