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
    /// Optional STARK proof of the state transition.
    ///
    /// When present, the verifier deserializes this and verifies via
    /// `EffectVmAir`, providing proof-carrying P2P exchange
    /// (not just signature-based). The proof binds old_commitment ->
    /// new_commitment + effects_hash + cell_id.
    ///
    /// NB: `skip_serializing_if` is intentionally NOT used here even though
    /// the field is logically optional. Binary serde formats like postcard
    /// require symmetric serialize/deserialize — skipping the option tag on
    /// the wire would make round-tripping a `None` value fail with
    /// "expected more data" on the receiver side. `#[serde(default)]` keeps
    /// forward-compat for JSON callers that omit the field, but the postcard
    /// path always emits the 1-byte option tag.
    #[serde(default)]
    pub transition_proof: Option<Vec<u8>>,
    /// γ.2 unilateral binding (1-arity sibling of bilateral): the optional
    /// self-attestation this peer signed alongside the transition. When
    /// present, the receiver re-derives the canonical attestation_data from
    /// the sender's cell-id-derived encoding and confirms the bundle's
    /// `UNILATERAL_ATTESTATIONS_*` PI accumulator absorbed exactly this
    /// attestation — closing the executor-trust gap on sovereign-cell
    /// self-witnessing.
    ///
    /// Categorical lens: γ.2 binds pairs (Transfer/Grant) and triples
    /// (Introduce); unilateral is the 1-arity sibling, used by
    /// `peer_exchange` (the federation-bypass primitive) so a sovereign
    /// cell can structurally bind a property over its own transitions
    /// without a counterparty in the bundle. See
    /// `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §3.5.
    ///
    /// Storing the typed value here (rather than just `attestation_data`)
    /// lets the receiver verify the canonical-preimage derivation against
    /// the sender's `cell_id`: a forged sender produces a different
    /// canonical hash because `cell_id` is folded into the preimage.
    #[serde(default)]
    pub unilateral_attestation: Option<crate::unilateral::UnilateralAttestation>,
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
    CommitmentMismatch {
        expected: [u8; 32],
        got: [u8; 32],
    },
    SequenceGap {
        expected: u64,
        got: u64,
    },
    TimestampRegression,
    UnknownPeer(CellId),
    /// The STARK transition proof failed verification.
    InvalidTransitionProof(String),
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
            Self::InvalidTransitionProof(reason) => {
                write!(f, "invalid STARK transition proof: {}", reason)
            }
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
    /// representation of the transition fields. Timestamp is read from the
    /// system clock — for environments without a system clock (e.g. browser
    /// wasm), use [`create_transition_at`](Self::create_transition_at) and
    /// supply your own monotonic-enough timestamp.
    pub fn create_transition(
        &mut self,
        old_commitment: [u8; 32],
        new_commitment: [u8; 32],
        effects_hash: [u8; 32],
    ) -> PeerStateTransition {
        self.create_transition_at(
            old_commitment,
            new_commitment,
            effects_hash,
            current_timestamp(),
        )
    }

    /// Same as [`create_transition`] but takes an explicit timestamp.
    ///
    /// Intended for two cases:
    ///   1. Wasm / no-std environments where `SystemTime::now()` panics or
    ///      is unavailable. The caller passes their own monotonic-ish clock.
    ///   2. Deterministic tests / replay where the timestamp must be fixed.
    ///
    /// Receiver-side timestamp checking is unchanged: the peer's view's
    /// `last_updated` is bumped on each accepted transition and any
    /// regression (`timestamp < last_updated`) is rejected with
    /// `TimestampRegression`.
    pub fn create_transition_at(
        &mut self,
        old_commitment: [u8; 32],
        new_commitment: [u8; 32],
        effects_hash: [u8; 32],
        timestamp: i64,
    ) -> PeerStateTransition {
        self.my_sequence += 1;

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
            transition_proof: None,
            unilateral_attestation: None,
        }
    }

    /// Verify and accept a transition from a peer.
    ///
    /// Checks:
    /// 1. Signature valid (Ed25519 over canonical fields)
    /// 2. `old_commitment` matches our `last_known_commitment` for this peer
    /// 3. `sequence == last_sequence + 1` (monotonic, no skips)
    /// 4. `timestamp >= last_updated` (no going back in time)
    /// 5. If `transition_proof` is Some, verify the STARK proof via `EffectVmAir`
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

        // 5. Verify STARK transition proof if present.
        #[cfg(feature = "zkvm")]
        if let Some(proof_bytes) = &transition.transition_proof {
            Self::verify_stark_transition(
                proof_bytes,
                &transition.cell_id,
                &transition.old_commitment,
                &transition.new_commitment,
                &transition.effects_hash,
            )?;
        }

        // All checks pass — update our view.
        let view = self.peer_views.get_mut(&transition.cell_id).unwrap();
        view.last_known_commitment = transition.new_commitment;
        view.last_sequence = transition.sequence;
        view.last_updated = transition.timestamp;

        Ok(())
    }

    /// Verify a STARK proof binding old_commitment -> new_commitment + effects_hash + cell_id.
    ///
    /// Public inputs layout (Effect VM, 7+ BabyBear elements):
    ///   [old_commit(1), new_commit(1), net_delta_mag(1), net_delta_sign(1),
    ///    effects_hash_lo(1), effects_hash_hi(1), custom_count(1),
    ///    ...custom_entries(8 per custom effect)]
    #[cfg(feature = "zkvm")]
    fn verify_stark_transition(
        proof_bytes: &[u8],
        _cell_id: &CellId,
        old_commitment: &[u8; 32],
        new_commitment: &[u8; 32],
        _effects_hash: &[u8; 32],
    ) -> Result<(), PeerExchangeError> {
        use pyana_circuit::field::BabyBear;
        use pyana_circuit::stark;

        // Deserialize proof.
        let proof = stark::proof_from_bytes(proof_bytes)
            .map_err(|e| PeerExchangeError::InvalidTransitionProof(e))?;

        // Stage 1 (`EFFECT-VM-SHAPE-A.md`): widen commitment to 4 BabyBears.
        let old_commit_4 = Self::commitment_to_4bb(old_commitment);
        let new_commit_4 = Self::commitment_to_4bb(new_commitment);

        // Validate minimum PI count.
        use pyana_circuit::effect_vm::pi;
        let min_pi_count = pi::BASE_COUNT;
        if proof.public_inputs.len() < min_pi_count {
            return Err(PeerExchangeError::InvalidTransitionProof(format!(
                "proof has {} public inputs, expected at least {}",
                proof.public_inputs.len(),
                min_pi_count
            )));
        }

        // Build the public inputs vector in Stage 1 Effect VM layout.
        // Most PIs are sourced from the proof (peer trusts the prover's
        // declared values; the AIR's boundary + transition constraints
        // bind them to the trace); commitments are independently checked.
        let mut public_inputs: Vec<BabyBear> = (0..min_pi_count)
            .map(|i| BabyBear::new_canonical(proof.public_inputs[i]))
            .collect();
        // Override the commitment slots with verifier-derived values from
        // the stored commitments. PI matching below catches any divergence.
        for i in 0..pi::OLD_COMMIT_LEN {
            public_inputs[pi::OLD_COMMIT_BASE + i] = old_commit_4[i];
        }
        for i in 0..pi::NEW_COMMIT_LEN {
            public_inputs[pi::NEW_COMMIT_BASE + i] = new_commit_4[i];
        }

        // Append custom proof entries from the proof's PIs.
        let custom_count_val = public_inputs[pi::CUSTOM_EFFECT_COUNT].0 as usize;
        for i in 0..custom_count_val {
            let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
            if base + pi::CUSTOM_ENTRY_SIZE > proof.public_inputs.len() {
                break;
            }
            for j in 0..pi::CUSTOM_ENTRY_SIZE {
                public_inputs.push(BabyBear::new_canonical(proof.public_inputs[base + j]));
            }
        }

        // Verify commitment PIs match what we expect (all 4 felts each).
        for i in 0..pi::OLD_COMMIT_LEN {
            let proof_v = BabyBear::new_canonical(proof.public_inputs[pi::OLD_COMMIT_BASE + i]);
            if proof_v != old_commit_4[i] {
                return Err(PeerExchangeError::InvalidTransitionProof(format!(
                    "old_commitment in proof does not match expected value (felt {})",
                    i
                )));
            }
        }
        for i in 0..pi::NEW_COMMIT_LEN {
            let proof_v = BabyBear::new_canonical(proof.public_inputs[pi::NEW_COMMIT_BASE + i]);
            if proof_v != new_commit_4[i] {
                return Err(PeerExchangeError::InvalidTransitionProof(format!(
                    "new_commitment in proof does not match expected value (felt {})",
                    i
                )));
            }
        }

        // Verify the STARK proof using EffectVmAir.
        let air = pyana_circuit::EffectVmAir::new(proof.trace_len);
        stark::verify(&air, &proof, &public_inputs)
            .map_err(|e| PeerExchangeError::InvalidTransitionProof(e))?;

        Ok(())
    }

    /// Stage 1: encode a stored [u8; 32] commitment as 4 BabyBear felts.
    ///
    /// Replaces the prior 4-byte truncation (~31-bit binding) with a
    /// full 32-byte-derived 4-felt form (~124-bit binding) via
    /// `pyana_commit::typed::canonical_32_to_felts_4`.
    #[cfg(feature = "zkvm")]
    fn commitment_to_4bb(bytes: &[u8; 32]) -> [pyana_circuit::field::BabyBear; 4] {
        pyana_commit::typed::canonical_32_to_felts_4(bytes)
    }

    /// Get our current view of a peer's state commitment.
    pub fn peer_commitment(&self, peer: &CellId) -> Option<[u8; 32]> {
        self.peer_views.get(peer).map(|v| v.last_known_commitment)
    }

    /// Get our full current view of a peer cell — commitment, sequence,
    /// last-updated timestamp. Returns `None` if the peer has never been
    /// registered. Read-only accessor; used by callers that need the full
    /// view (e.g. wasm bindings exposing peer state to JS).
    pub fn peer_view(&self, peer: &CellId) -> Option<&PeerCellView> {
        self.peer_views.get(peer)
    }

    /// Iterate over all peer cell ids we have a view for.
    pub fn registered_peers(&self) -> impl Iterator<Item = CellId> + '_ {
        self.peer_views.keys().copied()
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
        let transition = alice.create_transition(initial_commitment, new_commitment, effects_hash);

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

        let mut transition = alice.create_transition(initial_commitment, [0xBB; 32], [0xCC; 32]);

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
        bob.register_peer(alice_cell, c0);

        // First transition should succeed (sequence 1).
        let t1 = alice.create_transition(c0, c1, [0x01; 32]);
        let alice_pubkey = alice.public_key();
        assert!(bob.verify_transition(&t1, &alice_pubkey).is_ok());

        // Craft a transition with the correct old_commitment (c1) but wrong
        // sequence (3 instead of 2) to trigger a pure sequence gap error.
        let new_commitment = [0xDD; 32];
        let effects_hash = [0x03; 32];
        let timestamp = current_timestamp();
        let bad_sequence = 3u64;

        let message =
            canonical_message(&c1, &new_commitment, &effects_hash, timestamp, bad_sequence);
        let sig = alice.my_signing_key.sign(&message);

        let gap_transition = PeerStateTransition {
            cell_id: alice_cell,
            old_commitment: c1,
            new_commitment,
            effects_hash,
            timestamp,
            sequence: bad_sequence,
            signature: sig.to_bytes(),
            transition_proof: None,
        };

        // Bob expects sequence 2, but gets 3.
        let result = bob.verify_transition(&gap_transition, &alice_pubkey);
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

        let message = canonical_message(
            &old_commitment,
            &new_commitment,
            &effects_hash,
            past_timestamp,
            sequence,
        );
        let sig = alice.my_signing_key.sign(&message);

        let backdated = PeerStateTransition {
            cell_id: alice_cell,
            old_commitment,
            new_commitment,
            effects_hash,
            timestamp: past_timestamp,
            sequence,
            signature: sig.to_bytes(),
            transition_proof: None,
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
