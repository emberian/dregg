//! Peer-to-peer state exchange protocol for sovereign cells.
//!
//! Enables direct state transition exchange between two cells that already know
//! each other, without contacting the federation. Each party maintains a view of
//! the other's state commitment and verifies transitions via Ed25519 signatures.

use std::collections::HashMap;

use ed25519_dalek::{Signer, Verifier};
use serde::{Deserialize, Serialize};

use crate::CellId;

/// Serde helper for `[u8; 64]` (Ed25519 signatures).
mod sig_serde {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], ser: S) -> Result<S::Ok, S::Error> {
        bytes.as_slice().serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(de: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Vec::deserialize(de)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for signature"))
    }
}

// =============================================================================
// Types
// =============================================================================

/// A signed state transition for peer-to-peer exchange (no federation).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PeerStateTransition {
    pub cell_id: CellId,
    pub old_commitment: [u8; 32],
    pub new_commitment: [u8; 32],
    /// BLAKE3 hash of the effects applied in this transition.
    pub effects_hash: [u8; 32],
    pub timestamp: i64,
    /// Monotonic counter per cell (no gaps allowed).
    pub sequence: u64,
    /// Ed25519 signature over (old, new, effects_hash, timestamp, sequence).
    #[serde(with = "sig_serde")]
    pub signature: [u8; 64],
}

/// A peer's view of another cell's state.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PeerCellView {
    pub cell_id: CellId,
    pub last_known_commitment: [u8; 32],
    pub last_sequence: u64,
    pub last_updated: i64,
}

/// Errors produced during peer exchange verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PeerExchangeError {
    InvalidSignature,
    CommitmentMismatch { expected: [u8; 32], got: [u8; 32] },
    SequenceGap { expected: u64, got: u64 },
    TimestampRegression,
    UnknownPeer(CellId),
}

impl std::fmt::Display for PeerExchangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSignature => write!(f, "invalid Ed25519 signature"),
            Self::CommitmentMismatch { expected, got } => {
                write!(
                    f,
                    "commitment mismatch: expected {:?}, got {:?}",
                    &expected[..4],
                    &got[..4]
                )
            }
            Self::SequenceGap { expected, got } => {
                write!(f, "sequence gap: expected {}, got {}", expected, got)
            }
            Self::TimestampRegression => write!(f, "timestamp regression"),
            Self::UnknownPeer(id) => write!(f, "unknown peer: {}", id),
        }
    }
}

impl std::error::Error for PeerExchangeError {}

// =============================================================================
// PeerExchange
// =============================================================================

/// A peer exchange session between two sovereign cells.
///
/// Maintains a local signing identity and a set of peer views that track
/// the last-known commitment, sequence, and timestamp for each peer.
pub struct PeerExchange {
    my_cell: CellId,
    my_signing_key: ed25519_dalek::SigningKey,
    my_sequence: u64,
    peer_views: HashMap<CellId, PeerCellView>,
}

impl PeerExchange {
    /// Create a new peer exchange session.
    ///
    /// # Arguments
    /// * `cell_id` - This cell's identity.
    /// * `signing_key` - 32-byte Ed25519 secret key for signing transitions.
    pub fn new(cell_id: CellId, signing_key: [u8; 32]) -> Self {
        let sk = ed25519_dalek::SigningKey::from_bytes(&signing_key);
        Self {
            my_cell: cell_id,
            my_signing_key: sk,
            my_sequence: 0,
            peer_views: HashMap::new(),
        }
    }

    /// Register a peer with an initial commitment.
    ///
    /// Must be called before `verify_transition` will accept transitions from this peer.
    pub fn register_peer(&mut self, cell_id: CellId, initial_commitment: [u8; 32]) {
        self.peer_views.insert(
            cell_id,
            PeerCellView {
                cell_id,
                last_known_commitment: initial_commitment,
                last_sequence: 0,
                last_updated: 0,
            },
        );
    }

    /// Create a signed state transition after local execution.
    ///
    /// Increments the internal sequence counter and signs the canonical
    /// representation of the transition fields.
    pub fn create_transition(
        &mut self,
        old_commitment: [u8; 32],
        new_commitment: [u8; 32],
        effects_hash: [u8; 32],
    ) -> PeerStateTransition {
        self.my_sequence += 1;
        let timestamp = current_timestamp();

        let message = canonical_message(
            &old_commitment,
            &new_commitment,
            &effects_hash,
            timestamp,
            self.my_sequence,
        );
        let sig = self.my_signing_key.sign(&message);

        PeerStateTransition {
            cell_id: self.my_cell,
            old_commitment,
            new_commitment,
            effects_hash,
            timestamp,
            sequence: self.my_sequence,
            signature: sig.to_bytes(),
        }
    }

    /// Verify and accept a transition from a peer.
    ///
    /// Checks:
    /// 1. Signature valid (Ed25519 over canonical fields)
    /// 2. `old_commitment` matches our `last_known_commitment` for this peer
    /// 3. `sequence == last_sequence + 1` (monotonic, no skips)
    /// 4. `timestamp >= last_updated` (no going back in time)
    ///
    /// If all pass, updates `peer_views` with the new state.
    pub fn verify_transition(
        &mut self,
        transition: &PeerStateTransition,
        peer_pubkey: &[u8; 32],
    ) -> Result<(), PeerExchangeError> {
        // Look up the peer view.
        let view = self
            .peer_views
            .get(&transition.cell_id)
            .ok_or(PeerExchangeError::UnknownPeer(transition.cell_id))?;

        // 1. Verify signature.
        let verifying_key = ed25519_dalek::VerifyingKey::from_bytes(peer_pubkey)
            .map_err(|_| PeerExchangeError::InvalidSignature)?;
        let message = canonical_message(
            &transition.old_commitment,
            &transition.new_commitment,
            &transition.effects_hash,
            transition.timestamp,
            transition.sequence,
        );
        let signature = ed25519_dalek::Signature::from_bytes(&transition.signature);
        verifying_key
            .verify(&message, &signature)
            .map_err(|_| PeerExchangeError::InvalidSignature)?;

        // 2. Check old_commitment matches what we last saw.
        if transition.old_commitment != view.last_known_commitment {
            return Err(PeerExchangeError::CommitmentMismatch {
                expected: view.last_known_commitment,
                got: transition.old_commitment,
            });
        }

        // 3. Check sequence is monotonic with no gaps.
        let expected_seq = view.last_sequence + 1;
        if transition.sequence != expected_seq {
            return Err(PeerExchangeError::SequenceGap {
                expected: expected_seq,
                got: transition.sequence,
            });
        }

        // 4. Check timestamp does not regress.
        if transition.timestamp < view.last_updated {
            return Err(PeerExchangeError::TimestampRegression);
        }

        // All checks pass — update our view.
        let view = self.peer_views.get_mut(&transition.cell_id).unwrap();
        view.last_known_commitment = transition.new_commitment;
        view.last_sequence = transition.sequence;
        view.last_updated = transition.timestamp;

        Ok(())
    }

    /// Get our current view of a peer's state commitment.
    pub fn peer_commitment(&self, peer: &CellId) -> Option<[u8; 32]> {
        self.peer_views
            .get(peer)
            .map(|v| v.last_known_commitment)
    }

    /// Get this cell's ID.
    pub fn cell_id(&self) -> CellId {
        self.my_cell
    }

    /// Get the current sequence number.
    pub fn sequence(&self) -> u64 {
        self.my_sequence
    }

    /// Get the public key corresponding to this exchange's signing key.
    pub fn public_key(&self) -> [u8; 32] {
        self.my_signing_key.verifying_key().to_bytes()
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Compute the canonical signing message for a state transition.
///
/// Layout: old_commitment || new_commitment || effects_hash || timestamp (8 LE) || sequence (8 LE)
fn canonical_message(
    old: &[u8; 32],
    new: &[u8; 32],
    effects_hash: &[u8; 32],
    timestamp: i64,
    sequence: u64,
) -> Vec<u8> {
    let mut msg = Vec::with_capacity(32 + 32 + 32 + 8 + 8);
    msg.extend_from_slice(old);
    msg.extend_from_slice(new);
    msg.extend_from_slice(effects_hash);
    msg.extend_from_slice(&timestamp.to_le_bytes());
    msg.extend_from_slice(&sequence.to_le_bytes());
    msg
}

/// Get the current Unix timestamp in seconds.
fn current_timestamp() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn test_signing_key(seed: u8) -> [u8; 32] {
        let mut key = [0u8; 32];
        key[0] = seed;
        // Use BLAKE3 to expand to a proper key from the seed byte.
        *blake3::hash(&key).as_bytes()
    }

    fn test_cell_id(seed: u8) -> CellId {
        let mut bytes = [0u8; 32];
        bytes[0] = seed;
        bytes[31] = seed.wrapping_mul(7);
        CellId::from_bytes(bytes)
    }

    #[test]
    fn create_and_verify_transition() {
        let alice_key = test_signing_key(1);
        let bob_key = test_signing_key(2);
        let alice_cell = test_cell_id(1);
        let bob_cell = test_cell_id(2);

        let mut alice = PeerExchange::new(alice_cell, alice_key);
        let mut bob = PeerExchange::new(bob_cell, bob_key);

        // Bob registers Alice with an initial commitment.
        let initial_commitment = [0xAA; 32];
        bob.register_peer(alice_cell, initial_commitment);

        // Alice creates a transition.
        let new_commitment = [0xBB; 32];
        let effects_hash = *blake3::hash(b"transfer 100").as_bytes();
        let transition =
            alice.create_transition(initial_commitment, new_commitment, effects_hash);

        // Bob verifies it.
        let alice_pubkey = alice.public_key();
        let result = bob.verify_transition(&transition, &alice_pubkey);
        assert!(result.is_ok());

        // Bob's view should now reflect the new state.
        assert_eq!(bob.peer_commitment(&alice_cell), Some(new_commitment));
    }

    #[test]
    fn reject_invalid_signature() {
        let alice_key = test_signing_key(1);
        let bob_key = test_signing_key(2);
        let alice_cell = test_cell_id(1);
        let bob_cell = test_cell_id(2);

        let mut alice = PeerExchange::new(alice_cell, alice_key);
        let mut bob = PeerExchange::new(bob_cell, bob_key);

        let initial_commitment = [0xAA; 32];
        bob.register_peer(alice_cell, initial_commitment);

        let mut transition =
            alice.create_transition(initial_commitment, [0xBB; 32], [0xCC; 32]);

        // Corrupt the signature.
        transition.signature[0] ^= 0xFF;

        let alice_pubkey = alice.public_key();
        let result = bob.verify_transition(&transition, &alice_pubkey);
        assert_eq!(result, Err(PeerExchangeError::InvalidSignature));
    }

    #[test]
    fn reject_commitment_mismatch() {
        let alice_key = test_signing_key(1);
        let bob_key = test_signing_key(2);
        let alice_cell = test_cell_id(1);
        let bob_cell = test_cell_id(2);

        let mut alice = PeerExchange::new(alice_cell, alice_key);
        let mut bob = PeerExchange::new(bob_cell, bob_key);

        // Bob thinks Alice's commitment is 0xAA..
        let initial_commitment = [0xAA; 32];
        bob.register_peer(alice_cell, initial_commitment);

        // But Alice signs a transition from 0x11.. (wrong old commitment).
        let wrong_old = [0x11; 32];
        let transition = alice.create_transition(wrong_old, [0xBB; 32], [0xCC; 32]);

        let alice_pubkey = alice.public_key();
        let result = bob.verify_transition(&transition, &alice_pubkey);
        assert_eq!(
            result,
            Err(PeerExchangeError::CommitmentMismatch {
                expected: initial_commitment,
                got: wrong_old,
            })
        );
    }

    #[test]
    fn reject_sequence_gap() {
        let alice_key = test_signing_key(1);
        let bob_key = test_signing_key(2);
        let alice_cell = test_cell_id(1);
        let bob_cell = test_cell_id(2);

        let mut alice = PeerExchange::new(alice_cell, alice_key);
        let mut bob = PeerExchange::new(bob_cell, bob_key);

        let c0 = [0xAA; 32];
        let c1 = [0xBB; 32];
        let c2 = [0xCC; 32];
        bob.register_peer(alice_cell, c0);

        // First transition should succeed (sequence 1).
        let t1 = alice.create_transition(c0, c1, [0x01; 32]);
        let alice_pubkey = alice.public_key();
        assert!(bob.verify_transition(&t1, &alice_pubkey).is_ok());

        // Skip a transition: create sequence 2, then create sequence 3 without
        // submitting 2 to bob. We simulate this by creating two transitions on
        // Alice's side and only submitting the second.
        let _t2 = alice.create_transition(c1, c2, [0x02; 32]);
        let t3 = alice.create_transition(c2, [0xDD; 32], [0x03; 32]);

        // Bob expects sequence 2, but gets 3.
        let result = bob.verify_transition(&t3, &alice_pubkey);
        assert_eq!(
            result,
            Err(PeerExchangeError::SequenceGap {
                expected: 2,
                got: 3
            })
        );
    }

    #[test]
    fn reject_timestamp_regression() {
        let alice_key = test_signing_key(1);
        let bob_key = test_signing_key(2);
        let alice_cell = test_cell_id(1);
        let bob_cell = test_cell_id(2);

        let mut alice = PeerExchange::new(alice_cell, alice_key);
        let mut bob = PeerExchange::new(bob_cell, bob_key);

        let c0 = [0xAA; 32];
        bob.register_peer(alice_cell, c0);

        // First transition (timestamp will be "now").
        let t1 = alice.create_transition(c0, [0xBB; 32], [0x01; 32]);
        let alice_pubkey = alice.public_key();
        assert!(bob.verify_transition(&t1, &alice_pubkey).is_ok());

        // Manually craft a transition with a timestamp in the past.
        let old_commitment = [0xBB; 32];
        let new_commitment = [0xCC; 32];
        let effects_hash = [0x02; 32];
        let past_timestamp: i64 = 1; // Unix epoch + 1 second
        let sequence = 2u64;

        let message =
            canonical_message(&old_commitment, &new_commitment, &effects_hash, past_timestamp, sequence);
        let sig = alice.my_signing_key.sign(&message);

        let backdated = PeerStateTransition {
            cell_id: alice_cell,
            old_commitment,
            new_commitment,
            effects_hash,
            timestamp: past_timestamp,
            sequence,
            signature: sig.to_bytes(),
        };

        let result = bob.verify_transition(&backdated, &alice_pubkey);
        assert_eq!(result, Err(PeerExchangeError::TimestampRegression));
    }

    #[test]
    fn unknown_peer_rejected() {
        let bob_key = test_signing_key(2);
        let alice_key = test_signing_key(1);
        let alice_cell = test_cell_id(1);
        let bob_cell = test_cell_id(2);

        let mut alice = PeerExchange::new(alice_cell, alice_key);
        let mut bob = PeerExchange::new(bob_cell, bob_key);

        // Bob does NOT register Alice.
        let transition = alice.create_transition([0xAA; 32], [0xBB; 32], [0xCC; 32]);
        let alice_pubkey = alice.public_key();
        let result = bob.verify_transition(&transition, &alice_pubkey);
        assert_eq!(result, Err(PeerExchangeError::UnknownPeer(alice_cell)));
    }

    #[test]
    fn multiple_sequential_transitions() {
        let alice_key = test_signing_key(1);
        let bob_key = test_signing_key(2);
        let alice_cell = test_cell_id(1);
        let bob_cell = test_cell_id(2);

        let mut alice = PeerExchange::new(alice_cell, alice_key);
        let mut bob = PeerExchange::new(bob_cell, bob_key);

        let c0 = [0x00; 32];
        bob.register_peer(alice_cell, c0);

        let alice_pubkey = alice.public_key();

        // Chain of 5 transitions.
        let mut prev = c0;
        for i in 1..=5u8 {
            let next = [i; 32];
            let effects = *blake3::hash(&[i]).as_bytes();
            let t = alice.create_transition(prev, next, effects);
            assert!(bob.verify_transition(&t, &alice_pubkey).is_ok());
            assert_eq!(bob.peer_commitment(&alice_cell), Some(next));
            prev = next;
        }

        assert_eq!(alice.sequence(), 5);
    }
}
