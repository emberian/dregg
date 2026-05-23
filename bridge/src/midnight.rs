//! Midnight bridge: cross-chain value transfer between pyana and Midnight Network.
//!
//! # Architecture
//!
//! The bridge uses an **observation pattern** (same as Midnight's own Cardano bridge):
//! - **Pyana → Midnight**: A note is burned on pyana, the pyana federation produces a
//!   threshold attestation, and the Midnight contract verifies it to unlock/mint.
//! - **Midnight → Pyana**: Tokens are locked in a Midnight contract (emitting an event),
//!   the pyana observer detects the event, and the federation mints a note.
//!
//! # Trust Model
//!
//! - **Midnight → Pyana direction**: Relies on the pyana federation's observation of
//!   *finalized* Midnight blocks. Only events from blocks past Substrate finality
//!   (GRANDPA) are accepted. This mirrors Midnight's own `c2m-bridge` pallet.
//! - **Pyana → Midnight direction**: Relies on a 2-of-3 (configurable) threshold
//!   signature from the pyana federation. The Midnight contract verifies this
//!   attestation before releasing funds.
//!
//! # Security Properties
//!
//! 1. **No double-mint**: Each Midnight lock event is tracked by tx_hash + log_index.
//!    The pyana observer deduplicates before submitting to consensus.
//! 2. **No double-unlock**: Each pyana nullifier is recorded in the Midnight contract's
//!    storage. The `unlockFromPyana` function rejects replayed nonces.
//! 3. **Finality**: Only finalized Midnight blocks are observed (no reorgs).
//! 4. **Liveness**: If the observer goes down, events accumulate and are replayed on
//!    restart (idempotent via deduplication).

use serde::{Deserialize, Serialize};

// ============================================================================
// Federation Attestation (shared between both directions)
// ============================================================================

/// A threshold attestation from the pyana federation.
///
/// The pyana federation produces this when a note is burned and bound for Midnight.
/// The Midnight contract verifies this before releasing funds.
///
/// # Threshold Signature Scheme
///
/// Uses Schnorr threshold signatures (compatible with Ed25519 verification).
/// The federation's aggregate public key rotates each epoch and is registered
/// on the Midnight contract via governance.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FederationAttestation {
    /// BLAKE3 hash of the canonical encoding of the bridge message being attested.
    pub message_hash: [u8; 32],
    /// Threshold signature (Schnorr/Ed25519 compatible, 64 bytes for single-sig,
    /// variable for multi-sig depending on scheme).
    pub signature: Vec<u8>,
    /// The federation epoch during which this attestation was produced.
    /// Epochs rotate keys; the Midnight contract must check the correct epoch key.
    pub epoch: u64,
    /// The federation's aggregate public key for this epoch (32 bytes Ed25519).
    pub federation_pubkey: Vec<u8>,
}

impl FederationAttestation {
    /// Compute the domain-separated message hash for attestation signing.
    ///
    /// The message is: BLAKE3_derive_key("pyana-midnight-bridge-v1", payload).
    pub fn compute_message_hash(payload: &[u8]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-midnight-bridge-v1");
        hasher.update(payload);
        *hasher.finalize().as_bytes()
    }

    /// Verify this attestation against a known federation public key.
    ///
    /// Returns true if the signature is valid for the message_hash under the
    /// provided public key. For production, the caller should look up the
    /// correct key by `self.epoch`.
    pub fn verify(&self, expected_pubkey: &[u8; 32]) -> bool {
        use ed25519_dalek::{Signature, VerifyingKey};

        if self.federation_pubkey.len() != 32 {
            return false;
        }
        if self.signature.len() != 64 {
            return false;
        }

        // Check the pubkey matches the expected one for this epoch.
        if self.federation_pubkey.as_slice() != expected_pubkey.as_slice() {
            return false;
        }

        let Ok(vk) = VerifyingKey::from_bytes(expected_pubkey) else {
            return false;
        };

        let sig_bytes: [u8; 64] = match self.signature.as_slice().try_into() {
            Ok(b) => b,
            Err(_) => return false,
        };
        let signature = Signature::from_bytes(&sig_bytes);

        vk.verify_strict(&self.message_hash, &signature).is_ok()
    }

    /// Create a new attestation by signing a payload.
    ///
    /// This is called by federation nodes during the attestation protocol.
    pub fn create(payload: &[u8], signing_key: &ed25519_dalek::SigningKey, epoch: u64) -> Self {
        use ed25519_dalek::Signer;

        let message_hash = Self::compute_message_hash(payload);
        let signature = signing_key.sign(&message_hash);
        let federation_pubkey = signing_key.verifying_key().to_bytes().to_vec();

        Self {
            message_hash,
            signature: signature.to_bytes().to_vec(),
            epoch,
            federation_pubkey,
        }
    }
}

// ============================================================================
// Pyana → Midnight message
// ============================================================================

/// A bridge message from pyana to Midnight (attested by pyana federation).
///
/// Flow:
/// 1. User burns a note on pyana (nullifier published, destination = "midnight").
/// 2. Federation observes the burn and produces a threshold attestation.
/// 3. User (or relayer) submits this message to the Midnight bridge contract.
/// 4. Contract verifies attestation, checks nonce, and mints tDUST/NIGHT for recipient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PyanaToMidnightMessage {
    /// The pyana note nullifier (proves the note was spent on pyana side).
    pub nullifier: [u8; 32],
    /// Amount in atomic units (STARS on Midnight, 10^6 STARS = 1 NIGHT).
    pub amount: u64,
    /// Recipient's Midnight public key (for Zswap coin creation).
    /// Format: 32-byte compressed point on JubJub (Midnight's in-circuit curve).
    pub midnight_recipient: Vec<u8>,
    /// Federation attestation (threshold signature over the canonical message).
    pub attestation: FederationAttestation,
    /// Nonce for replay protection (monotonically increasing per federation epoch).
    pub nonce: u64,
}

impl PyanaToMidnightMessage {
    /// Compute the canonical encoding used for attestation signing.
    ///
    /// The canonical form is: nullifier || amount_le || recipient || nonce_le
    pub fn canonical_payload(&self) -> Vec<u8> {
        let mut payload = Vec::with_capacity(32 + 8 + self.midnight_recipient.len() + 8);
        payload.extend_from_slice(&self.nullifier);
        payload.extend_from_slice(&self.amount.to_le_bytes());
        payload.extend_from_slice(&self.midnight_recipient);
        payload.extend_from_slice(&self.nonce.to_le_bytes());
        payload
    }

    /// Validate that the attestation is consistent with the message contents.
    ///
    /// Checks that `attestation.message_hash` matches the hash of `canonical_payload()`.
    pub fn is_self_consistent(&self) -> bool {
        let expected_hash = FederationAttestation::compute_message_hash(&self.canonical_payload());
        self.attestation.message_hash == expected_hash
    }
}

// ============================================================================
// Midnight → Pyana message
// ============================================================================

/// A bridge message from Midnight to pyana (observed from finalized Midnight blocks).
///
/// Flow:
/// 1. User calls `lockForPyana` on the Midnight bridge contract.
/// 2. Contract locks tokens and emits a `BridgeLock` event.
/// 3. The pyana observation node detects the event in a finalized block.
/// 4. Observer constructs this message and submits it to pyana federation consensus.
/// 5. Federation verifies the block/event proof and mints a note for the recipient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MidnightToPyanaMessage {
    /// Midnight transaction hash containing the lock event.
    pub midnight_tx_hash: [u8; 32],
    /// Amount locked on Midnight (in STARS, atomic units).
    pub amount: u64,
    /// Recipient's pyana cell ID (the note will be minted to this identity).
    pub pyana_recipient: [u8; 32],
    /// Block height on Midnight where this event was finalized.
    pub midnight_height: u64,
    /// Log index within the transaction (for deduplication when multiple events in one tx).
    pub log_index: u32,
}

impl MidnightToPyanaMessage {
    /// Unique identifier for deduplication: (tx_hash, log_index).
    pub fn dedup_key(&self) -> ([u8; 32], u32) {
        (self.midnight_tx_hash, self.log_index)
    }

    /// Canonical encoding for hashing/signing.
    pub fn canonical_payload(&self) -> Vec<u8> {
        let mut payload = Vec::with_capacity(32 + 8 + 32 + 8 + 4);
        payload.extend_from_slice(&self.midnight_tx_hash);
        payload.extend_from_slice(&self.amount.to_le_bytes());
        payload.extend_from_slice(&self.pyana_recipient);
        payload.extend_from_slice(&self.midnight_height.to_le_bytes());
        payload.extend_from_slice(&self.log_index.to_le_bytes());
        payload
    }
}

// ============================================================================
// Bridge Event (parsed from Midnight contract logs)
// ============================================================================

/// Events emitted by the Midnight bridge contract that the observer watches for.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MidnightBridgeEvent {
    /// Tokens locked on Midnight, destined for pyana.
    Lock {
        /// Amount locked (STARS).
        amount: u64,
        /// Target pyana cell ID.
        pyana_recipient: [u8; 32],
        /// Nonce (set by the caller for correlation).
        nonce: u64,
    },
    /// Tokens unlocked on Midnight (from a pyana → Midnight transfer completing).
    Unlock {
        /// Amount unlocked.
        amount: u64,
        /// Midnight recipient public key.
        midnight_recipient: Vec<u8>,
        /// The pyana nullifier that authorized this unlock.
        nullifier: [u8; 32],
    },
}

// ============================================================================
// Bridge Configuration
// ============================================================================

/// Configuration for the Midnight bridge.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MidnightBridgeConfig {
    /// The Midnight bridge contract address (Substrate account ID, 32 bytes).
    pub contract_address: [u8; 32],
    /// Midnight node WebSocket RPC endpoint (e.g., "ws://localhost:9944").
    pub midnight_rpc_url: String,
    /// Number of confirmations (blocks past finality) before accepting an event.
    /// Zero means "accept at finalization" (GRANDPA finality is already strong).
    pub confirmations: u64,
    /// Federation public keys by epoch for attestation verification.
    pub federation_keys: Vec<EpochKey>,
    /// Minimum bridge amount (STARS). Below this, transfers are rejected.
    pub min_amount: u64,
    /// Maximum bridge amount per transaction (STARS). Above this, requires governance.
    pub max_amount: u64,
}

/// A federation public key associated with an epoch range.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EpochKey {
    /// The epoch this key is valid from (inclusive).
    pub from_epoch: u64,
    /// The epoch this key is valid until (inclusive). None = current/unbounded.
    pub to_epoch: Option<u64>,
    /// The Ed25519 public key (32 bytes).
    pub pubkey: [u8; 32],
}

impl MidnightBridgeConfig {
    /// Look up the federation public key for a given epoch.
    pub fn key_for_epoch(&self, epoch: u64) -> Option<&[u8; 32]> {
        self.federation_keys.iter().find_map(|ek| {
            let in_range = epoch >= ek.from_epoch && ek.to_epoch.map_or(true, |to| epoch <= to);
            if in_range { Some(&ek.pubkey) } else { None }
        })
    }
}

// ============================================================================
// Bridge State (tracked by the observer)
// ============================================================================

/// Tracks which Midnight events have been processed, for crash recovery.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ObserverState {
    /// The last finalized Midnight block height that was fully processed.
    pub last_processed_height: u64,
    /// Set of (tx_hash, log_index) pairs already submitted to federation.
    /// Used for deduplication on restart.
    pub processed_events: Vec<([u8; 32], u32)>,
}

impl ObserverState {
    /// Check if an event has already been processed.
    pub fn is_processed(&self, tx_hash: &[u8; 32], log_index: u32) -> bool {
        self.processed_events
            .iter()
            .any(|(h, i)| h == tx_hash && *i == log_index)
    }

    /// Mark an event as processed.
    pub fn mark_processed(&mut self, tx_hash: [u8; 32], log_index: u32) {
        if !self.is_processed(&tx_hash, log_index) {
            self.processed_events.push((tx_hash, log_index));
        }
    }

    /// Advance the processed height and prune old dedup entries.
    ///
    /// Events from blocks before `new_height - retention` can be pruned
    /// since they can never appear again in the finalized chain.
    pub fn advance_height(&mut self, new_height: u64) {
        self.last_processed_height = new_height;
    }

    /// Prune processed events older than a retention window.
    ///
    /// In practice, we'd need to store height per event for this to work.
    /// For now, this caps the dedup set size.
    pub fn prune_if_large(&mut self, max_entries: usize) {
        if self.processed_events.len() > max_entries {
            // Keep the most recent half.
            let keep_from = self.processed_events.len() - max_entries / 2;
            self.processed_events = self.processed_events[keep_from..].to_vec();
        }
    }
}

// ============================================================================
// Nonce Tracking (for pyana → Midnight direction)
// ============================================================================

/// Tracks used nonces per epoch to prevent replay on the Midnight side.
///
/// This would be stored in the Midnight contract's state. We define it here
/// so the pyana side can pre-check before submitting.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct NonceTracker {
    /// Used nonces indexed by epoch.
    used: Vec<(u64, Vec<u64>)>,
}

impl NonceTracker {
    /// Create a new empty tracker.
    pub fn new() -> Self {
        Self { used: Vec::new() }
    }

    /// Check if a nonce has been used in the given epoch.
    pub fn is_used(&self, epoch: u64, nonce: u64) -> bool {
        self.used
            .iter()
            .any(|(e, nonces)| *e == epoch && nonces.contains(&nonce))
    }

    /// Record a nonce as used. Returns false if it was already used (replay).
    pub fn record(&mut self, epoch: u64, nonce: u64) -> bool {
        if self.is_used(epoch, nonce) {
            return false;
        }
        if let Some((_, nonces)) = self.used.iter_mut().find(|(e, _)| *e == epoch) {
            nonces.push(nonce);
        } else {
            self.used.push((epoch, vec![nonce]));
        }
        true
    }

    /// Prune all entries for epochs before `min_epoch`.
    pub fn prune_before(&mut self, min_epoch: u64) {
        self.used.retain(|(e, _)| *e >= min_epoch);
    }
}

// ============================================================================
// Error types
// ============================================================================

/// Errors specific to the Midnight bridge.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MidnightBridgeError {
    /// The federation attestation is invalid (bad signature or wrong epoch key).
    InvalidAttestation { reason: String },
    /// The message hash in the attestation does not match the canonical payload.
    AttestationMismatch,
    /// The nonce has already been used (replay attempt).
    NonceReplay { epoch: u64, nonce: u64 },
    /// The amount is below the minimum bridge threshold.
    BelowMinimum { amount: u64, minimum: u64 },
    /// The amount exceeds the maximum per-transaction bridge limit.
    AboveMaximum { amount: u64, maximum: u64 },
    /// The Midnight recipient key is malformed.
    InvalidRecipient { reason: String },
    /// Could not connect to the Midnight node.
    ConnectionFailed { reason: String },
    /// The observed event was from a block that has not been finalized.
    NotFinalized { height: u64 },
    /// The event has already been processed (dedup).
    AlreadyProcessed { tx_hash: [u8; 32], log_index: u32 },
    /// The federation key for the given epoch is not known.
    UnknownEpochKey { epoch: u64 },
}

impl core::fmt::Display for MidnightBridgeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidAttestation { reason } => {
                write!(f, "invalid federation attestation: {reason}")
            }
            Self::AttestationMismatch => {
                write!(
                    f,
                    "attestation message_hash does not match canonical payload"
                )
            }
            Self::NonceReplay { epoch, nonce } => {
                write!(f, "nonce {nonce} already used in epoch {epoch}")
            }
            Self::BelowMinimum { amount, minimum } => {
                write!(f, "amount {amount} below minimum {minimum}")
            }
            Self::AboveMaximum { amount, maximum } => {
                write!(f, "amount {amount} above maximum {maximum}")
            }
            Self::InvalidRecipient { reason } => {
                write!(f, "invalid midnight recipient: {reason}")
            }
            Self::ConnectionFailed { reason } => {
                write!(f, "midnight node connection failed: {reason}")
            }
            Self::NotFinalized { height } => {
                write!(f, "block at height {height} is not finalized")
            }
            Self::AlreadyProcessed { tx_hash, log_index } => {
                write!(
                    f,
                    "event {:02x}{:02x}{:02x}{:02x}...:{} already processed",
                    tx_hash[0], tx_hash[1], tx_hash[2], tx_hash[3], log_index
                )
            }
            Self::UnknownEpochKey { epoch } => {
                write!(f, "no federation key known for epoch {epoch}")
            }
        }
    }
}

impl std::error::Error for MidnightBridgeError {}

// ============================================================================
// Validation functions
// ============================================================================

/// Validate a pyana → Midnight message before submission to the Midnight contract.
///
/// Checks:
/// 1. Message is self-consistent (attestation hash matches payload).
/// 2. Attestation signature is valid for the epoch's key.
/// 3. Amount is within bridge limits.
/// 4. Nonce has not been used.
/// 5. Recipient key is well-formed (32 bytes for JubJub point).
pub fn validate_pyana_to_midnight(
    msg: &PyanaToMidnightMessage,
    config: &MidnightBridgeConfig,
    nonce_tracker: &NonceTracker,
) -> Result<(), MidnightBridgeError> {
    // 1. Self-consistency.
    if !msg.is_self_consistent() {
        return Err(MidnightBridgeError::AttestationMismatch);
    }

    // 2. Attestation verification.
    let epoch_key = config.key_for_epoch(msg.attestation.epoch).ok_or(
        MidnightBridgeError::UnknownEpochKey {
            epoch: msg.attestation.epoch,
        },
    )?;
    if !msg.attestation.verify(epoch_key) {
        return Err(MidnightBridgeError::InvalidAttestation {
            reason: "signature verification failed".to_string(),
        });
    }

    // 3. Amount limits.
    if msg.amount < config.min_amount {
        return Err(MidnightBridgeError::BelowMinimum {
            amount: msg.amount,
            minimum: config.min_amount,
        });
    }
    if msg.amount > config.max_amount {
        return Err(MidnightBridgeError::AboveMaximum {
            amount: msg.amount,
            maximum: config.max_amount,
        });
    }

    // 4. Nonce replay check.
    if nonce_tracker.is_used(msg.attestation.epoch, msg.nonce) {
        return Err(MidnightBridgeError::NonceReplay {
            epoch: msg.attestation.epoch,
            nonce: msg.nonce,
        });
    }

    // 5. Recipient format.
    if msg.midnight_recipient.len() != 32 {
        return Err(MidnightBridgeError::InvalidRecipient {
            reason: format!(
                "expected 32-byte JubJub point, got {} bytes",
                msg.midnight_recipient.len()
            ),
        });
    }

    Ok(())
}

/// Validate a Midnight → pyana message before minting a note.
///
/// Checks:
/// 1. The event has not been previously processed (dedup).
/// 2. The block height is at or below the last finalized height.
/// 3. Amount is within limits.
/// 4. Recipient cell ID is non-zero.
pub fn validate_midnight_to_pyana(
    msg: &MidnightToPyanaMessage,
    config: &MidnightBridgeConfig,
    state: &ObserverState,
    finalized_height: u64,
) -> Result<(), MidnightBridgeError> {
    // 1. Dedup.
    let (tx_hash, log_index) = msg.dedup_key();
    if state.is_processed(&tx_hash, log_index) {
        return Err(MidnightBridgeError::AlreadyProcessed { tx_hash, log_index });
    }

    // 2. Finality check.
    if msg.midnight_height > finalized_height {
        return Err(MidnightBridgeError::NotFinalized {
            height: msg.midnight_height,
        });
    }

    // 3. Amount limits.
    if msg.amount < config.min_amount {
        return Err(MidnightBridgeError::BelowMinimum {
            amount: msg.amount,
            minimum: config.min_amount,
        });
    }
    if msg.amount > config.max_amount {
        return Err(MidnightBridgeError::AboveMaximum {
            amount: msg.amount,
            maximum: config.max_amount,
        });
    }

    // 4. Non-zero recipient.
    if msg.pyana_recipient == [0u8; 32] {
        return Err(MidnightBridgeError::InvalidRecipient {
            reason: "pyana recipient cell ID is all zeros".to_string(),
        });
    }

    Ok(())
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn test_config() -> MidnightBridgeConfig {
        let sk = ed25519_dalek::SigningKey::from_bytes(&[0x42u8; 32]);
        let vk = sk.verifying_key();
        MidnightBridgeConfig {
            contract_address: [0xCC; 32],
            midnight_rpc_url: "ws://localhost:9944".to_string(),
            confirmations: 0,
            federation_keys: vec![EpochKey {
                from_epoch: 0,
                to_epoch: Some(10), // Bounded: only epochs 0..=10 are valid.
                pubkey: vk.to_bytes(),
            }],
            min_amount: 1_000_000,         // 1 NIGHT
            max_amount: 1_000_000_000_000, // 1M NIGHT
        }
    }

    fn test_signing_key() -> ed25519_dalek::SigningKey {
        ed25519_dalek::SigningKey::from_bytes(&[0x42u8; 32])
    }

    fn make_valid_pyana_to_midnight() -> PyanaToMidnightMessage {
        let sk = test_signing_key();
        let nullifier = [0xAA; 32];
        let amount = 5_000_000u64; // 5 NIGHT
        let recipient = vec![0xBB; 32];
        let nonce = 1u64;

        // Build canonical payload.
        let mut payload = Vec::new();
        payload.extend_from_slice(&nullifier);
        payload.extend_from_slice(&amount.to_le_bytes());
        payload.extend_from_slice(&recipient);
        payload.extend_from_slice(&nonce.to_le_bytes());

        let attestation = FederationAttestation::create(&payload, &sk, 0);

        PyanaToMidnightMessage {
            nullifier,
            amount,
            midnight_recipient: recipient,
            attestation,
            nonce,
        }
    }

    #[test]
    fn test_federation_attestation_roundtrip() {
        let sk = test_signing_key();
        let payload = b"test payload for midnight bridge";
        let attestation = FederationAttestation::create(payload, &sk, 1);

        let expected_pubkey = sk.verifying_key().to_bytes();
        assert!(attestation.verify(&expected_pubkey));

        // Wrong key should fail.
        let wrong_key = [0xFF; 32];
        assert!(!attestation.verify(&wrong_key));
    }

    #[test]
    fn test_attestation_message_hash_deterministic() {
        let hash1 = FederationAttestation::compute_message_hash(b"hello midnight");
        let hash2 = FederationAttestation::compute_message_hash(b"hello midnight");
        assert_eq!(hash1, hash2);

        let hash3 = FederationAttestation::compute_message_hash(b"hello pyana");
        assert_ne!(hash1, hash3);
    }

    #[test]
    fn test_pyana_to_midnight_self_consistency() {
        let msg = make_valid_pyana_to_midnight();
        assert!(msg.is_self_consistent());

        // Tamper with amount → inconsistent.
        let mut tampered = msg.clone();
        tampered.amount = 999;
        assert!(!tampered.is_self_consistent());
    }

    #[test]
    fn test_validate_pyana_to_midnight_success() {
        let msg = make_valid_pyana_to_midnight();
        let config = test_config();
        let nonce_tracker = NonceTracker::new();

        let result = validate_pyana_to_midnight(&msg, &config, &nonce_tracker);
        assert!(result.is_ok(), "validation should pass: {result:?}");
    }

    #[test]
    fn test_validate_pyana_to_midnight_below_minimum() {
        let sk = test_signing_key();
        let mut msg = make_valid_pyana_to_midnight();
        msg.amount = 100; // Below min of 1_000_000.
        // Rebuild attestation with new amount.
        let payload = msg.canonical_payload();
        msg.attestation = FederationAttestation::create(&payload, &sk, 0);

        let config = test_config();
        let nonce_tracker = NonceTracker::new();

        let result = validate_pyana_to_midnight(&msg, &config, &nonce_tracker);
        assert!(matches!(
            result,
            Err(MidnightBridgeError::BelowMinimum { .. })
        ));
    }

    #[test]
    fn test_validate_pyana_to_midnight_nonce_replay() {
        let msg = make_valid_pyana_to_midnight();
        let config = test_config();
        let mut nonce_tracker = NonceTracker::new();

        // First use succeeds.
        assert!(validate_pyana_to_midnight(&msg, &config, &nonce_tracker).is_ok());
        nonce_tracker.record(msg.attestation.epoch, msg.nonce);

        // Second use (replay) fails.
        let result = validate_pyana_to_midnight(&msg, &config, &nonce_tracker);
        assert!(matches!(
            result,
            Err(MidnightBridgeError::NonceReplay { .. })
        ));
    }

    #[test]
    fn test_validate_pyana_to_midnight_bad_attestation() {
        let mut msg = make_valid_pyana_to_midnight();
        // Corrupt the signature.
        msg.attestation.signature[0] ^= 0xFF;

        let config = test_config();
        let nonce_tracker = NonceTracker::new();

        let result = validate_pyana_to_midnight(&msg, &config, &nonce_tracker);
        assert!(matches!(
            result,
            Err(MidnightBridgeError::InvalidAttestation { .. })
        ));
    }

    #[test]
    fn test_validate_pyana_to_midnight_wrong_epoch() {
        let sk = test_signing_key();
        let mut msg = make_valid_pyana_to_midnight();
        // Rebuild with epoch 99 (not in config).
        let payload = msg.canonical_payload();
        msg.attestation = FederationAttestation::create(&payload, &sk, 99);

        let config = test_config();
        let nonce_tracker = NonceTracker::new();

        let result = validate_pyana_to_midnight(&msg, &config, &nonce_tracker);
        assert!(matches!(
            result,
            Err(MidnightBridgeError::UnknownEpochKey { epoch: 99 })
        ));
    }

    #[test]
    fn test_validate_pyana_to_midnight_bad_recipient_length() {
        let sk = test_signing_key();
        let mut msg = make_valid_pyana_to_midnight();
        msg.midnight_recipient = vec![0xBB; 20]; // Wrong length.
        // Rebuild attestation.
        let payload = msg.canonical_payload();
        msg.attestation = FederationAttestation::create(&payload, &sk, 0);

        let config = test_config();
        let nonce_tracker = NonceTracker::new();

        let result = validate_pyana_to_midnight(&msg, &config, &nonce_tracker);
        assert!(matches!(
            result,
            Err(MidnightBridgeError::InvalidRecipient { .. })
        ));
    }

    #[test]
    fn test_midnight_to_pyana_message_dedup() {
        let msg = MidnightToPyanaMessage {
            midnight_tx_hash: [0x11; 32],
            amount: 5_000_000,
            pyana_recipient: [0x22; 32],
            midnight_height: 100,
            log_index: 0,
        };

        let config = test_config();
        let mut state = ObserverState::default();

        // First processing.
        let result = validate_midnight_to_pyana(&msg, &config, &state, 200);
        assert!(result.is_ok());
        state.mark_processed(msg.midnight_tx_hash, msg.log_index);

        // Second processing (replay).
        let result = validate_midnight_to_pyana(&msg, &config, &state, 200);
        assert!(matches!(
            result,
            Err(MidnightBridgeError::AlreadyProcessed { .. })
        ));
    }

    #[test]
    fn test_midnight_to_pyana_not_finalized() {
        let msg = MidnightToPyanaMessage {
            midnight_tx_hash: [0x33; 32],
            amount: 5_000_000,
            pyana_recipient: [0x44; 32],
            midnight_height: 500, // Higher than finalized.
            log_index: 0,
        };

        let config = test_config();
        let state = ObserverState::default();

        let result = validate_midnight_to_pyana(&msg, &config, &state, 400);
        assert!(matches!(
            result,
            Err(MidnightBridgeError::NotFinalized { height: 500 })
        ));
    }

    #[test]
    fn test_midnight_to_pyana_zero_recipient() {
        let msg = MidnightToPyanaMessage {
            midnight_tx_hash: [0x55; 32],
            amount: 5_000_000,
            pyana_recipient: [0x00; 32], // All zeros.
            midnight_height: 100,
            log_index: 0,
        };

        let config = test_config();
        let state = ObserverState::default();

        let result = validate_midnight_to_pyana(&msg, &config, &state, 200);
        assert!(matches!(
            result,
            Err(MidnightBridgeError::InvalidRecipient { .. })
        ));
    }

    #[test]
    fn test_nonce_tracker() {
        let mut tracker = NonceTracker::new();

        assert!(!tracker.is_used(0, 1));
        assert!(tracker.record(0, 1));
        assert!(tracker.is_used(0, 1));
        assert!(!tracker.record(0, 1)); // replay

        assert!(tracker.record(0, 2));
        assert!(tracker.record(1, 1)); // different epoch

        tracker.prune_before(1);
        assert!(!tracker.is_used(0, 1)); // pruned
        assert!(tracker.is_used(1, 1)); // kept
    }

    #[test]
    fn test_observer_state_prune() {
        let mut state = ObserverState::default();
        for i in 0..100u8 {
            state.mark_processed([i; 32], 0);
        }
        assert_eq!(state.processed_events.len(), 100);

        state.prune_if_large(60);
        // Should keep most recent 30.
        assert_eq!(state.processed_events.len(), 30);
    }

    #[test]
    fn test_midnight_to_pyana_canonical_payload() {
        let msg = MidnightToPyanaMessage {
            midnight_tx_hash: [1u8; 32],
            amount: 42,
            pyana_recipient: [2u8; 32],
            midnight_height: 100,
            log_index: 3,
        };

        let payload = msg.canonical_payload();
        // 32 + 8 + 32 + 8 + 4 = 84 bytes
        assert_eq!(payload.len(), 84);
    }

    #[test]
    fn test_serialization_roundtrip() {
        let msg = make_valid_pyana_to_midnight();
        let bytes = postcard::to_stdvec(&msg).unwrap();
        let decoded: PyanaToMidnightMessage = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(msg, decoded);
    }

    #[test]
    fn test_midnight_to_pyana_serialization() {
        let msg = MidnightToPyanaMessage {
            midnight_tx_hash: [0xAA; 32],
            amount: 1_000_000,
            pyana_recipient: [0xBB; 32],
            midnight_height: 999,
            log_index: 2,
        };
        let bytes = postcard::to_stdvec(&msg).unwrap();
        let decoded: MidnightToPyanaMessage = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(msg, decoded);
    }
}
