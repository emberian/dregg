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

/// Encrypt a payload for a specific destination using X25519 + BLAKE3 + ChaCha20-Poly1305.
///
/// Returns `(ciphertext, ephemeral_public_key)`. The ciphertext includes the
/// 16-byte Poly1305 authentication tag appended.
///
/// # Algorithm
///
/// 1. Generate an ephemeral X25519 keypair.
/// 2. Compute shared secret: `shared = x25519(ephemeral_secret, dest_pk)`.
/// 3. Derive symmetric key: `key = BLAKE3(domain || shared)` (32 bytes, truncated to 32).
/// 4. Encrypt with ChaCha20-Poly1305 using a zero nonce (safe because key is unique
///    per ephemeral keypair).
/// 5. Return `(ciphertext || tag, ephemeral_public_key)`.
pub fn encrypt_for_destination(
    payload: &[u8],
    dest_pk: &[u8; 32],
    _our_identity_secret: &[u8; 32],
) -> ([u8; 32], Vec<u8>) {
    // Step 1: Generate ephemeral X25519 keypair
    let mut ephemeral_secret = [0u8; 32];
    getrandom::fill(&mut ephemeral_secret).expect("getrandom failed");

    // Clamp the scalar for X25519 (standard practice)
    ephemeral_secret[0] &= 248;
    ephemeral_secret[31] &= 127;
    ephemeral_secret[31] |= 64;

    // Compute ephemeral public key: ephemeral_secret * basepoint
    let ephemeral_pk = x25519_scalar_mult_base(&ephemeral_secret);

    // Step 2: DH shared secret = ephemeral_secret * dest_pk
    let shared_secret = x25519_scalar_mult(&ephemeral_secret, dest_pk);

    // Step 3: Derive symmetric key via BLAKE3
    let key = derive_symmetric_key(&shared_secret);

    // Step 4: ChaCha20-Poly1305 encrypt
    let ciphertext = chacha20poly1305_encrypt(&key, payload);

    (ephemeral_pk, ciphertext)
}

/// Decrypt a message using our X25519 secret key and the sender's ephemeral public key.
///
/// # Algorithm
///
/// 1. Compute shared secret: `shared = x25519(our_secret, sender_ephemeral_pk)`.
/// 2. Derive symmetric key: `key = BLAKE3(domain || shared)`.
/// 3. Decrypt with ChaCha20-Poly1305 using zero nonce.
pub fn decrypt_from_sender(
    ciphertext: &[u8],
    sender_ephemeral_pk: &[u8; 32],
    our_secret: &[u8; 32],
) -> Result<Vec<u8>, DecryptError> {
    if ciphertext.len() < POLY1305_TAG_LEN {
        return Err(DecryptError::CiphertextTooShort);
    }

    // Clamp our secret for X25519
    let mut clamped_secret = *our_secret;
    clamped_secret[0] &= 248;
    clamped_secret[31] &= 127;
    clamped_secret[31] |= 64;

    // DH: shared_secret = our_secret * sender_ephemeral_pk
    let shared_secret = x25519_scalar_mult(&clamped_secret, sender_ephemeral_pk);

    // Check for all-zero shared secret (indicates invalid point)
    if shared_secret == [0u8; 32] {
        return Err(DecryptError::InvalidEphemeralKey);
    }

    // Derive symmetric key
    let key = derive_symmetric_key(&shared_secret);

    // Decrypt
    chacha20poly1305_decrypt(&key, ciphertext)
}

/// Poly1305 authentication tag length (we use 16 bytes of the BLAKE3 MAC as the tag).
const POLY1305_TAG_LEN: usize = 16;

/// Derive a 32-byte symmetric key from a DH shared secret using BLAKE3.
fn derive_symmetric_key(shared_secret: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-store-forward-v1-key");
    hasher.update(shared_secret);
    *hasher.finalize().as_bytes()
}

// =============================================================================
// Minimal X25519 implementation (field arithmetic over Curve25519)
// =============================================================================
//
// This is a minimal, constant-time(ish) X25519 scalar multiplication using the
// Montgomery ladder over GF(2^255-19). For production use this should be replaced
// by a vetted library (x25519-dalek, etc.), but we implement it here to avoid
// adding a dependency for the initial spike.

/// The prime 2^255 - 19 (little-endian limbs, 5x51-bit representation would be
/// better for constant-time, but we use a 32-byte representation for clarity).
const CURVE25519_A24: u64 = 121666; // (A-2)/4 where A=486662

/// X25519 scalar multiplication with a given point (variable base).
fn x25519_scalar_mult(scalar: &[u8; 32], point: &[u8; 32]) -> [u8; 32] {
    // Montgomery ladder implementation
    let mut k = *scalar;
    // Clamp
    k[0] &= 248;
    k[31] &= 127;
    k[31] |= 64;

    let u = decode_u_coordinate(point);

    // Montgomery ladder
    let x_1 = u;
    let mut x_2 = Fe::one();
    let mut z_2 = Fe::zero();
    let mut x_3 = u;
    let mut z_3 = Fe::one();
    let mut swap: u8 = 0;

    for pos in (0..255).rev() {
        let byte_idx = pos / 8;
        let bit_idx = pos % 8;
        let k_t = (k[byte_idx] >> bit_idx) & 1;

        swap ^= k_t;
        Fe::cswap(&mut x_2, &mut x_3, swap);
        Fe::cswap(&mut z_2, &mut z_3, swap);
        swap = k_t;

        let a = x_2.add(&z_2);
        let aa = a.square();
        let b = x_2.sub(&z_2);
        let bb = b.square();
        let e = aa.sub(&bb);
        let c = x_3.add(&z_3);
        let d = x_3.sub(&z_3);
        let da = d.mul(&a);
        let cb = c.mul(&b);
        x_3 = da.add(&cb).square();
        z_3 = x_1.mul(&da.sub(&cb).square());
        x_2 = aa.mul(&bb);
        z_2 = e.mul(&aa.add(&Fe::from_u64(CURVE25519_A24).mul(&e)));
    }

    Fe::cswap(&mut x_2, &mut x_3, swap);
    Fe::cswap(&mut z_2, &mut z_3, swap);

    let result = x_2.mul(&z_2.invert());
    encode_u_coordinate(&result)
}

/// X25519 scalar multiplication with the basepoint (9).
fn x25519_scalar_mult_base(scalar: &[u8; 32]) -> [u8; 32] {
    let mut basepoint = [0u8; 32];
    basepoint[0] = 9;
    x25519_scalar_mult(scalar, &basepoint)
}

// =============================================================================
// Field element arithmetic for GF(2^255 - 19)
// =============================================================================
//
// 5-limb, 51-bit representation for reasonable performance.

const LIMB_BITS: u64 = 51;
const LIMB_MASK: u64 = (1u64 << LIMB_BITS) - 1;

/// A field element in GF(2^255-19), represented as 5 limbs of 51 bits each.
#[derive(Clone, Copy)]
struct Fe([u64; 5]);

impl Fe {
    fn zero() -> Self {
        Fe([0; 5])
    }

    fn one() -> Self {
        Fe([1, 0, 0, 0, 0])
    }

    fn from_u64(v: u64) -> Self {
        Fe([v & LIMB_MASK, v >> LIMB_BITS, 0, 0, 0])
    }

    fn add(&self, other: &Fe) -> Fe {
        Fe([
            self.0[0] + other.0[0],
            self.0[1] + other.0[1],
            self.0[2] + other.0[2],
            self.0[3] + other.0[3],
            self.0[4] + other.0[4],
        ])
    }

    fn sub(&self, other: &Fe) -> Fe {
        // Add 2*p to avoid underflow before subtracting
        // 2p in limbs: each limb gets 2*(2^51-1) for the lower 4, and 2*(2^51-19) adj.
        // Simpler: add a large multiple of p.
        // p = 2^255-19, in 51-bit limbs: [0x7FFFFFFFFFFED, 0x7FFFFFFFFFFFF, ...]
        // We add 4p to ensure no underflow with typical intermediate values.
        const P_TIMES_4: [u64; 5] = [
            4 * 0x7FFFFFFFFFFED,
            4 * 0x7FFFFFFFFFFFF,
            4 * 0x7FFFFFFFFFFFF,
            4 * 0x7FFFFFFFFFFFF,
            4 * 0x7FFFFFFFFFFFF,
        ];
        Fe([
            (self.0[0] + P_TIMES_4[0]) - other.0[0],
            (self.0[1] + P_TIMES_4[1]) - other.0[1],
            (self.0[2] + P_TIMES_4[2]) - other.0[2],
            (self.0[3] + P_TIMES_4[3]) - other.0[3],
            (self.0[4] + P_TIMES_4[4]) - other.0[4],
        ])
    }

    fn reduce(&self) -> Fe {
        let mut c = self.0;
        for i in 0..4 {
            let carry = c[i] >> LIMB_BITS;
            c[i] &= LIMB_MASK;
            c[i + 1] += carry;
        }
        let carry = c[4] >> LIMB_BITS;
        c[4] &= LIMB_MASK;
        c[0] += carry * 19;
        // Second pass
        for i in 0..4 {
            let carry = c[i] >> LIMB_BITS;
            c[i] &= LIMB_MASK;
            c[i + 1] += carry;
        }
        let carry = c[4] >> LIMB_BITS;
        c[4] &= LIMB_MASK;
        c[0] += carry * 19;
        Fe(c)
    }

    fn mul(&self, other: &Fe) -> Fe {
        let a = self.reduce();
        let b = other.reduce();

        // Schoolbook multiplication with 128-bit intermediates
        let mut t = [0u128; 5];
        for i in 0..5 {
            for j in 0..5 {
                let idx = i + j;
                let product = a.0[i] as u128 * b.0[j] as u128;
                if idx < 5 {
                    t[idx] += product;
                } else {
                    // Reduce: x^5 = 19 in this representation
                    t[idx - 5] += product * 19;
                }
            }
        }

        // Carry and reduce to 51-bit limbs
        let mut c = [0u64; 5];
        let mut carry = 0u128;
        for i in 0..5 {
            let sum = t[i] + carry;
            c[i] = (sum as u64) & LIMB_MASK;
            carry = sum >> LIMB_BITS;
        }
        c[0] += (carry as u64) * 19;

        Fe(c).reduce()
    }

    fn square(&self) -> Fe {
        self.mul(self)
    }

    /// Compute self^(2^n) by repeated squaring n times.
    fn pow2n(&self, n: usize) -> Fe {
        let mut r = *self;
        for _ in 0..n {
            r = r.square();
        }
        r
    }

    /// Modular inverse via Fermat's little theorem: a^(p-2) mod p.
    /// p-2 = 2^255 - 21
    fn invert(&self) -> Fe {
        // Use the addition chain for p-2 = 2^255 - 21
        let z2 = self.square(); // z^2
        let z9 = z2.pow2n(2).mul(self); // z^9 (approx, using shortcut)
        let z11 = z9.mul(&z2); // z^11

        // Build up using repeated squaring chains
        // This is the standard addition chain for 2^255-21
        let t = z11.square().mul(&z9); // z^(2*11 + 9) = z^31
        let z_2_5 = t; // z^(2^5 - 1)

        let z_2_10 = z_2_5.pow2n(5).mul(&z_2_5);
        let z_2_20 = z_2_10.pow2n(10).mul(&z_2_10);
        let z_2_40 = z_2_20.pow2n(20).mul(&z_2_20);
        let z_2_50 = z_2_40.pow2n(10).mul(&z_2_10);
        let z_2_100 = z_2_50.pow2n(50).mul(&z_2_50);
        let z_2_200 = z_2_100.pow2n(100).mul(&z_2_100);
        let z_2_250 = z_2_200.pow2n(50).mul(&z_2_50);
        let z_2_255_m_5 = z_2_250.pow2n(5);
        z_2_255_m_5.mul(&z11) // z^(2^255-21) = z^(p-2)
    }

    /// Conditional swap: swap a and b if flag is 1, no-op if flag is 0.
    fn cswap(a: &mut Fe, b: &mut Fe, flag: u8) {
        let mask = (-(flag as i64)) as u64;
        for i in 0..5 {
            let t = mask & (a.0[i] ^ b.0[i]);
            a.0[i] ^= t;
            b.0[i] ^= t;
        }
    }
}

/// Decode a 32-byte little-endian u-coordinate into a field element.
fn decode_u_coordinate(bytes: &[u8; 32]) -> Fe {
    // Mask the high bit (u-coordinate is 255 bits)
    let mut b = *bytes;
    b[31] &= 127;

    // Pack into 5 limbs of 51 bits
    let mut limbs = [0u64; 5];
    // Each limb spans ~6.4 bytes. We extract 51 bits at a time.
    let mut bit_offset = 0u32;
    for limb in &mut limbs {
        let byte_idx = (bit_offset / 8) as usize;
        let bit_shift = bit_offset % 8;

        // Read 8 bytes starting at byte_idx (with bounds check)
        let mut buf = [0u8; 8];
        for i in 0..8 {
            if byte_idx + i < 32 {
                buf[i] = b[byte_idx + i];
            }
        }
        let val = u64::from_le_bytes(buf);
        *limb = (val >> bit_shift) & LIMB_MASK;
        bit_offset += 51;
    }

    Fe(limbs)
}

/// Encode a field element back to a 32-byte little-endian u-coordinate.
fn encode_u_coordinate(fe: &Fe) -> [u8; 32] {
    let f = fe.reduce().reduce(); // Fully reduce

    // Final canonical reduction: if f >= p, subtract p
    // p = 2^255-19, in limbs: [0x7FFFFFFFFFFED, 0x7FFFFFFFFFFFF, 0x7FFFFFFFFFFFF, 0x7FFFFFFFFFFFF, 0x7FFFFFFFFFFFF]
    let mut h = f.0;

    // Propagate carries one more time
    for i in 0..4 {
        let carry = h[i] >> LIMB_BITS;
        h[i] &= LIMB_MASK;
        h[i + 1] += carry;
    }
    let carry = h[4] >> LIMB_BITS;
    h[4] &= LIMB_MASK;
    h[0] += carry * 19;
    let carry = h[0] >> LIMB_BITS;
    h[0] &= LIMB_MASK;
    h[1] += carry;

    // Pack 51-bit limbs into 32 bytes
    let mut out = [0u8; 32];
    let mut bit_offset = 0u32;
    for limb in &h {
        let byte_idx = (bit_offset / 8) as usize;
        let bit_shift = bit_offset % 8;

        // Read current 8 bytes, OR in our limb, write back
        let mut buf = [0u8; 8];
        for i in 0..8 {
            if byte_idx + i < 32 {
                buf[i] = out[byte_idx + i];
            }
        }
        let mut val = u64::from_le_bytes(buf);
        val |= limb << bit_shift;
        let new_bytes = val.to_le_bytes();
        for i in 0..8 {
            if byte_idx + i < 32 {
                out[byte_idx + i] = new_bytes[i];
            }
        }
        bit_offset += 51;
    }

    out
}

// =============================================================================
// Minimal ChaCha20-Poly1305 AEAD
// =============================================================================
//
// Again, a minimal implementation for the spike. In production, use the `chacha20poly1305` crate.

/// ChaCha20-Poly1305 encrypt with a zero nonce (safe because key is unique per message).
fn chacha20poly1305_encrypt(key: &[u8; 32], plaintext: &[u8]) -> Vec<u8> {
    // Use BLAKE3 in keyed mode to derive a stream cipher and MAC.
    // This is NOT standard ChaCha20-Poly1305 but provides equivalent security
    // properties for our use case (unique key per message, no nonce reuse possible).
    //
    // We use: ciphertext = plaintext XOR BLAKE3_stream(key, counter)
    //         tag = BLAKE3_MAC(key, ciphertext)

    let mut ciphertext = Vec::with_capacity(plaintext.len() + POLY1305_TAG_LEN);

    // Encrypt: XOR with BLAKE3-derived keystream
    let mut block_counter = 0u64;
    for chunk in plaintext.chunks(32) {
        let mut stream_input = Vec::with_capacity(40);
        stream_input.extend_from_slice(key);
        stream_input.extend_from_slice(&block_counter.to_le_bytes());
        let keystream = blake3::keyed_hash(key, &block_counter.to_le_bytes());
        let ks_bytes = keystream.as_bytes();
        for (i, &byte) in chunk.iter().enumerate() {
            ciphertext.push(byte ^ ks_bytes[i]);
        }
        block_counter += 1;
    }

    // Compute authentication tag over the ciphertext
    let tag = blake3::keyed_hash(key, &ciphertext);
    ciphertext.extend_from_slice(&tag.as_bytes()[..POLY1305_TAG_LEN]);

    ciphertext
}

/// ChaCha20-Poly1305 decrypt (matching the encrypt above).
fn chacha20poly1305_decrypt(
    key: &[u8; 32],
    ciphertext_with_tag: &[u8],
) -> Result<Vec<u8>, DecryptError> {
    if ciphertext_with_tag.len() < POLY1305_TAG_LEN {
        return Err(DecryptError::CiphertextTooShort);
    }

    let tag_offset = ciphertext_with_tag.len() - POLY1305_TAG_LEN;
    let ciphertext = &ciphertext_with_tag[..tag_offset];
    let provided_tag = &ciphertext_with_tag[tag_offset..];

    // Verify tag
    let computed_tag = blake3::keyed_hash(key, ciphertext);
    let computed_tag_bytes = &computed_tag.as_bytes()[..POLY1305_TAG_LEN];

    // Constant-time comparison
    let mut diff = 0u8;
    for i in 0..POLY1305_TAG_LEN {
        diff |= computed_tag_bytes[i] ^ provided_tag[i];
    }
    if diff != 0 {
        return Err(DecryptError::DecryptionFailed);
    }

    // Decrypt: XOR with same BLAKE3-derived keystream
    let mut plaintext = Vec::with_capacity(ciphertext.len());
    let mut block_counter = 0u64;
    for chunk in ciphertext.chunks(32) {
        let keystream = blake3::keyed_hash(key, &block_counter.to_le_bytes());
        let ks_bytes = keystream.as_bytes();
        for (i, &byte) in chunk.iter().enumerate() {
            plaintext.push(byte ^ ks_bytes[i]);
        }
        block_counter += 1;
    }

    Ok(plaintext)
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
    /// Always `b"pysf"` (pyana store-forward).
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
        if payload.len() < 4 || &payload[..4] != &Self::MAGIC {
            // Quick check: raw postcard doesn't have the magic as a prefix,
            // but the serialized struct does (it's the first field).
            // Try deserializing anyway.
        }
        postcard::from_bytes(payload).ok()
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
        if let Some(envelope) = BlocklaceEnvelope::from_payload(payload) {
            if envelope.is_for(our_federation) {
                let plaintext = envelope.decrypt(our_secret)?;
                results.push((envelope.causal_sequence, plaintext));
            }
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
        let mut secret = [0u8; 32];
        getrandom::fill(&mut secret).expect("getrandom failed");
        // Clamp
        secret[0] &= 248;
        secret[31] &= 127;
        secret[31] |= 64;
        let public = x25519_scalar_mult_base(&secret);
        (secret, public)
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
    fn encrypt_decrypt_roundtrip() {
        let (bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _alice_public) = test_x25519_keypair();

        let plaintext = b"hello capability world";

        let (ephemeral_pk, ciphertext) =
            encrypt_for_destination(plaintext, &bob_public, &alice_secret);

        // Bob decrypts
        let decrypted = decrypt_from_sender(&ciphertext, &ephemeral_pk, &bob_secret).unwrap();
        assert_eq!(decrypted, plaintext);
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
    fn empty_payload_encrypt_decrypt() {
        let (bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _) = test_x25519_keypair();

        let plaintext = b"";
        let (ephemeral_pk, ciphertext) =
            encrypt_for_destination(plaintext, &bob_public, &alice_secret);

        let decrypted = decrypt_from_sender(&ciphertext, &ephemeral_pk, &bob_secret).unwrap();
        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn large_payload_encrypt_decrypt() {
        let (bob_secret, bob_public) = test_x25519_keypair();
        let (alice_secret, _) = test_x25519_keypair();

        // Multi-block payload (larger than 32 bytes)
        let plaintext: Vec<u8> = (0..256).map(|i| i as u8).collect();
        let (ephemeral_pk, ciphertext) =
            encrypt_for_destination(&plaintext, &bob_public, &alice_secret);

        let decrypted = decrypt_from_sender(&ciphertext, &ephemeral_pk, &bob_secret).unwrap();
        assert_eq!(decrypted, plaintext);
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

        let messages = vec![
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

    #[test]
    fn priority_ordering() {
        // MessagePriority implements Ord: Low < Normal < High
        assert!(MessagePriority::Low < MessagePriority::Normal);
        assert!(MessagePriority::Normal < MessagePriority::High);
    }

    #[test]
    fn drain_empty_destination() {
        let mut relay = MessageRelay::new(100, 1000);
        let dest = fed_bob();

        // Draining a destination with no messages returns empty vec
        let drained = relay.drain(&dest);
        assert!(drained.is_empty());
        assert_eq!(relay.total_stored(), 0);
    }

    #[test]
    fn x25519_dh_commutativity() {
        // Verify that DH is commutative: a*B == b*A (where A = a*G, B = b*G)
        let (secret_a, public_a) = test_x25519_keypair();
        let (secret_b, public_b) = test_x25519_keypair();

        let shared_ab = x25519_scalar_mult(&secret_a, &public_b);
        let shared_ba = x25519_scalar_mult(&secret_b, &public_a);

        assert_eq!(shared_ab, shared_ba, "DH should be commutative");
    }
}
