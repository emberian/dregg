//! Encrypted turn: a turn whose content is hidden from the federation during ordering.
//!
//! An `EncryptedTurn` bundles:
//! - The encrypted turn body (ChaCha20-Poly1305)
//! - A commitment to the plaintext turn (BLAKE3 hash)
//! - A conflict set (Bloom filter over accessed cells)
//! - A validity proof (STARK proving nonce + fee sufficiency without revealing content)
//!
//! The federation can order encrypted turns by:
//! 1. Verifying the validity proof (agent can pay, nonce is fresh)
//! 2. Detecting conflicts via Bloom filter overlap
//! 3. Serializing conflicting turns, parallelizing non-conflicting ones
//!
//! After ordering is finalized, the turn is revealed (either by the agent publishing
//! the decryption key, or via threshold decryption by the validator set).
//!
//! # Cryptography
//!
//! `EncryptedTurn::encrypt_for_executor(turn, recipient_pub)`:
//! - generates a fresh X25519 ephemeral keypair,
//! - performs X25519 DH with the executor's public key,
//! - derives a 32-byte ChaCha20-Poly1305 key via BLAKE3-derive_key,
//! - encrypts `serde_json::to_vec(turn)` with a fresh 12-byte nonce,
//! - records both `ephemeral_public` and `nonce` in the struct so the
//!   executor can later DH + decrypt with its static unsealer key.
//!
//! The `turn_commitment` is computed over the plaintext bytes so the
//! validator can also bind the proof to the same commit pre-encryption, and
//! the executor can verify post-decryption that the decrypted bytes hash to
//! the same commitment.
//!
//! # Why JSON, not postcard?
//!
//! `Turn` carries many `#[serde(default, skip_serializing_if = "…")]` fields.
//! Self-describing formats (JSON) tolerate field omission via the named-field
//! map; positional formats (postcard, bincode) read fields one-by-one and
//! error with "expected more data" when a skipped field is missing on
//! deserialize. JSON is slightly larger on the wire but is the only format
//! that round-trips the current `Turn` schema. (See
//! `tests::privacy_wiring::encrypted_turn_decrypts_to_original`.)

use pyana_cell::CellId;
use serde::{Deserialize, Serialize};

use crate::conflict::ConflictSet;
use crate::turn::Turn;

/// An encrypted turn submission for privacy-preserving federation ordering.
///
/// The federation orders these without seeing their content. The validity proof
/// guarantees the enclosed turn is well-formed and payable.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EncryptedTurn {
    /// The agent submitting this turn (public — needed for nonce/fee lookup).
    /// This is the ONE piece of metadata that remains visible.
    pub agent: CellId,

    /// Sender's ephemeral X25519 public key (32 bytes).
    /// Combined with the executor's static X25519 secret, this gives the
    /// ChaCha20-Poly1305 key via X25519 DH + BLAKE3-derive_key.
    pub ephemeral_public: [u8; 32],

    /// ChaCha20-Poly1305 nonce (12 bytes).
    pub nonce: [u8; 12],

    /// Encrypted turn body (ChaCha20-Poly1305 ciphertext + 16-byte authentication tag).
    pub ciphertext: Vec<u8>,

    /// BLAKE3 hash of the plaintext turn (for binding the proof to specific content).
    /// After decryption, validators check that BLAKE3(decrypted) == turn_commitment.
    pub turn_commitment: [u8; 32],

    /// Bloom filter over the read/write cell set.
    /// Used for conflict detection without revealing specific cell IDs.
    pub conflict_set: ConflictSet,

    /// STARK proof that this encrypted turn is valid.
    /// Proves: nonce correctness + fee sufficiency (Phase 1).
    /// Future: + conservation + authorization.
    pub validity_proof: TurnValidityProof,

    /// Submission timestamp (for ordering within conflict buckets).
    pub submitted_at: i64,
}

/// A STARK proof that an encrypted turn is valid without revealing its content.
///
/// Phase 1 proves:
/// - The prover knows a Turn T such that BLAKE3(T) = turn_commitment
/// - T.agent = claimed agent (binding)
/// - T.nonce = current nonce for agent cell (replay protection)
/// - agent_cell.balance >= T.fee (fee sufficiency)
///
/// Future phases will add conservation and authorization proofs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TurnValidityProof {
    /// The STARK proof bytes (serialized StarkProof from pyana-circuit).
    pub proof_bytes: Vec<u8>,

    /// Public inputs to the STARK (what the verifier checks against):
    /// - [0]: turn_commitment (as BabyBear field element)
    /// - [1]: agent_id_commitment (hash of agent CellId, as field element)
    /// - [2]: claimed_nonce (the nonce this turn uses)
    /// - [3]: min_fee (minimum fee this turn will pay — may be a lower bound)
    pub public_inputs: TurnValidityPublicInputs,
}

/// Public inputs for the turn validity STARK.
///
/// These are the values that the verifier can see and check against on-chain state.
/// Everything else (turn content, effects, targets) remains private.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TurnValidityPublicInputs {
    /// Commitment to the turn body: BLAKE3(serialize(turn)).
    /// Binds the proof to a specific (unknown) turn.
    pub turn_commitment: [u8; 32],

    /// Commitment to the agent identity: BLAKE3("agent" || agent.as_bytes()).
    /// The verifier checks this matches the claimed agent.
    pub agent_commitment: [u8; 32],

    /// The nonce this turn claims to use.
    /// The verifier checks: agent_cell.nonce == claimed_nonce.
    pub claimed_nonce: u64,

    /// Minimum fee this turn will pay (proven lower bound).
    /// The verifier checks: agent_cell.balance >= min_fee.
    /// This may be lower than the actual fee (privacy: exact fee is hidden).
    pub min_fee: u64,

    /// Commitment to the conflict set: BLAKE3(conflict_set.filter).
    /// Binds the conflict set to the validity proof (prevents conflict set swapping).
    pub conflict_set_commitment: [u8; 32],
}

impl TurnValidityPublicInputs {
    /// Compute the agent commitment from a CellId.
    pub fn compute_agent_commitment(agent: &CellId) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-agent-commitment-v1");
        hasher.update(agent.as_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Verify that the claimed agent matches the public inputs.
    pub fn verify_agent(&self, agent: &CellId) -> bool {
        self.agent_commitment == Self::compute_agent_commitment(agent)
    }

    /// Verify that the conflict set matches the commitment in the public inputs.
    pub fn verify_conflict_set(&self, conflict_set: &ConflictSet) -> bool {
        self.conflict_set_commitment == conflict_set.commitment()
    }
}

/// Derive the symmetric ChaCha20-Poly1305 key from an X25519 DH shared secret.
///
/// Both encrypt and decrypt sides MUST compute the same key. We use BLAKE3 in
/// derive_key mode with the domain string `"pyana-encrypted-turn-key v1"`,
/// hashing `shared_secret || ephemeral_public || recipient_public`. Mixing all
/// three values gives:
/// - shared_secret: the actual DH output (mutual knowledge of secret)
/// - ephemeral_public: binds the key to this specific ephemeral
/// - recipient_public: binds the key to this specific executor (no key reuse
///   across deployments)
fn derive_turn_key(
    shared_secret: &[u8; 32],
    ephemeral_public: &[u8; 32],
    recipient_public: &[u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-encrypted-turn-key v1");
    hasher.update(shared_secret);
    hasher.update(ephemeral_public);
    hasher.update(recipient_public);
    *hasher.finalize().as_bytes()
}

impl EncryptedTurn {
    /// Encrypt a `Turn` for a specific executor (identified by their X25519 public key).
    ///
    /// Generates a fresh X25519 ephemeral keypair, performs DH with the
    /// executor's public key, derives the symmetric key, and encrypts the
    /// `postcard`-serialized turn under ChaCha20-Poly1305.
    ///
    /// The caller is responsible for supplying a well-formed `validity_proof`
    /// (or a placeholder for testing) and a `conflict_set` that the validity
    /// proof's public inputs bind to.
    pub fn encrypt_for_executor(
        turn: &Turn,
        agent: CellId,
        recipient_public: &[u8; 32],
        conflict_set: ConflictSet,
        validity_proof: TurnValidityProof,
        submitted_at: i64,
    ) -> Result<Self, EncryptedTurnError> {
        use chacha20poly1305::aead::{Aead, KeyInit};
        use chacha20poly1305::{ChaCha20Poly1305, Nonce};
        use x25519_dalek::{PublicKey, StaticSecret};

        let plaintext = serde_json::to_vec(turn)
            .map_err(|e| EncryptedTurnError::SerializationFailed(e.to_string()))?;
        let turn_commitment = {
            let mut hasher = blake3::Hasher::new_derive_key("pyana-encrypted-turn-commitment v1");
            hasher.update(&plaintext);
            *hasher.finalize().as_bytes()
        };

        let mut eph_secret_bytes = [0u8; 32];
        getrandom::fill(&mut eph_secret_bytes)
            .map_err(|e| EncryptedTurnError::RandomFailed(e.to_string()))?;
        let eph_secret = StaticSecret::from(eph_secret_bytes);
        let eph_public = PublicKey::from(&eph_secret);

        let recipient = PublicKey::from(*recipient_public);
        let shared = eph_secret.diffie_hellman(&recipient);
        let key = derive_turn_key(shared.as_bytes(), eph_public.as_bytes(), recipient_public);

        let mut nonce_bytes = [0u8; 12];
        getrandom::fill(&mut nonce_bytes)
            .map_err(|e| EncryptedTurnError::RandomFailed(e.to_string()))?;
        let cipher = ChaCha20Poly1305::new((&key).into());
        let nonce = Nonce::from_slice(&nonce_bytes);
        let ciphertext = cipher
            .encrypt(nonce, plaintext.as_slice())
            .map_err(|_| EncryptedTurnError::EncryptionFailed)?;

        Ok(EncryptedTurn {
            agent,
            ephemeral_public: *eph_public.as_bytes(),
            nonce: nonce_bytes,
            ciphertext,
            turn_commitment,
            conflict_set,
            validity_proof,
            submitted_at,
        })
    }

    /// Decrypt this encrypted turn using the executor's static X25519 secret.
    ///
    /// Returns the recovered `Turn`. After decryption, the BLAKE3 commitment
    /// of the plaintext is recomputed and compared against `self.turn_commitment`;
    /// a mismatch indicates a corrupted ciphertext or a wrong recipient key.
    ///
    /// This is the executor-side counterpart of `encrypt_for_executor`. Both
    /// sides MUST use the same recipient public key — passing a stale or
    /// mismatched public key here will produce `DecryptionFailed`.
    pub fn decrypt_for_executor(
        &self,
        recipient_secret: &[u8; 32],
        recipient_public: &[u8; 32],
    ) -> Result<Turn, EncryptedTurnError> {
        use chacha20poly1305::aead::{Aead, KeyInit};
        use chacha20poly1305::{ChaCha20Poly1305, Nonce};
        use x25519_dalek::{PublicKey, StaticSecret};

        let secret = StaticSecret::from(*recipient_secret);
        let eph_public = PublicKey::from(self.ephemeral_public);
        let shared = secret.diffie_hellman(&eph_public);
        let key = derive_turn_key(shared.as_bytes(), &self.ephemeral_public, recipient_public);

        let cipher = ChaCha20Poly1305::new((&key).into());
        let nonce = Nonce::from_slice(&self.nonce);
        let plaintext = cipher
            .decrypt(nonce, self.ciphertext.as_slice())
            .map_err(|_| EncryptedTurnError::DecryptionFailed)?;

        let expected_commitment = {
            let mut hasher = blake3::Hasher::new_derive_key("pyana-encrypted-turn-commitment v1");
            hasher.update(&plaintext);
            *hasher.finalize().as_bytes()
        };
        if expected_commitment != self.turn_commitment {
            return Err(EncryptedTurnError::CommitmentVerificationFailed);
        }

        let turn: Turn = serde_json::from_slice(&plaintext)
            .map_err(|e| EncryptedTurnError::SerializationFailed(e.to_string()))?;
        Ok(turn)
    }

    /// Verify the encrypted turn's metadata consistency (without decryption).
    ///
    /// This checks:
    /// 1. The validity proof's agent commitment matches the claimed agent
    /// 2. The conflict set commitment in the proof matches the actual conflict set
    /// 3. The turn commitment in the proof matches the one in the header
    ///
    /// It does NOT verify the STARK proof itself — that requires the circuit verifier.
    pub fn verify_metadata(&self) -> Result<(), EncryptedTurnError> {
        // Check agent binding.
        if !self.validity_proof.public_inputs.verify_agent(&self.agent) {
            return Err(EncryptedTurnError::AgentMismatch);
        }

        // Check conflict set binding.
        if !self
            .validity_proof
            .public_inputs
            .verify_conflict_set(&self.conflict_set)
        {
            return Err(EncryptedTurnError::ConflictSetMismatch);
        }

        // Check turn commitment binding.
        if self.validity_proof.public_inputs.turn_commitment != self.turn_commitment {
            return Err(EncryptedTurnError::TurnCommitmentMismatch);
        }

        Ok(())
    }

    /// Check if this encrypted turn might conflict with another.
    ///
    /// Uses the Bloom filter conflict sets. False positives are possible
    /// (two non-conflicting turns flagged as conflicting) but false negatives are not.
    pub fn may_conflict_with(&self, other: &EncryptedTurn) -> bool {
        self.conflict_set.may_conflict_with(&other.conflict_set)
    }
}

/// Errors in encrypted turn validation (metadata-level, no decryption).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncryptedTurnError {
    /// The agent commitment in the validity proof doesn't match the claimed agent.
    AgentMismatch,
    /// The conflict set commitment in the validity proof doesn't match the conflict set.
    ConflictSetMismatch,
    /// The turn commitment in the validity proof doesn't match the header commitment.
    TurnCommitmentMismatch,
    /// The validity STARK proof failed verification.
    InvalidValidityProof(String),
    /// Decryption failed (wrong key or tampered ciphertext).
    DecryptionFailed,
    /// Decrypted turn doesn't match the commitment.
    CommitmentVerificationFailed,
    /// AEAD encryption failed.
    EncryptionFailed,
    /// Postcard serialize/deserialize failed.
    SerializationFailed(String),
    /// `getrandom` failed (extremely rare; OS entropy source unavailable).
    RandomFailed(String),
    /// Executor has no decryption key configured.
    NoDecryptionKey,
}

/// Result of ordering a batch of encrypted turns.
///
/// The federation produces this after consensus. It contains the ordering
/// (which turns go in which positions) and conflict bucketing.
#[derive(Clone, Debug)]
pub struct TurnOrdering {
    /// Turns grouped by conflict bucket. Turns in different buckets can execute in parallel.
    /// Turns within the same bucket must execute sequentially.
    pub buckets: Vec<ConflictBucket>,
}

/// A group of turns that potentially conflict and must be serialized.
#[derive(Clone, Debug)]
pub struct ConflictBucket {
    /// Turn commitments in execution order within this bucket.
    pub turn_commitments: Vec<[u8; 32]>,
}

/// Order a batch of encrypted turns into conflict-aware buckets.
///
/// Algorithm: greedy graph coloring on the conflict graph.
/// Each turn is a node; edges connect turns whose Bloom filters overlap.
/// Each color (bucket) contains non-conflicting turns that can parallelize.
pub fn order_encrypted_turns(turns: &[EncryptedTurn]) -> TurnOrdering {
    if turns.is_empty() {
        return TurnOrdering {
            buckets: Vec::new(),
        };
    }

    let n = turns.len();
    let mut bucket_assignments: Vec<Option<usize>> = vec![None; n];
    let mut buckets: Vec<ConflictBucket> = Vec::new();

    for i in 0..n {
        // Find the first bucket where this turn doesn't conflict with any existing member.
        let mut assigned = false;
        for (bucket_idx, bucket) in buckets.iter().enumerate() {
            let conflicts_with_bucket = bucket.turn_commitments.iter().any(|existing_commit| {
                // Find the turn with this commitment and check conflict.
                turns
                    .iter()
                    .any(|t| t.turn_commitment == *existing_commit && turns[i].may_conflict_with(t))
            });

            if !conflicts_with_bucket {
                bucket_assignments[i] = Some(bucket_idx);
                assigned = true;
                break;
            }
        }

        if !assigned {
            // Create a new bucket.
            bucket_assignments[i] = Some(buckets.len());
            buckets.push(ConflictBucket {
                turn_commitments: Vec::new(),
            });
        }

        // Add to the assigned bucket.
        let bucket_idx = bucket_assignments[i].unwrap();
        buckets[bucket_idx]
            .turn_commitments
            .push(turns[i].turn_commitment);
    }

    TurnOrdering { buckets }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_cell_id(seed: u8) -> CellId {
        let mut bytes = [0u8; 32];
        bytes[0] = seed;
        CellId::from_bytes(bytes)
    }

    fn dummy_encrypted_turn(agent_seed: u8, cells: &[u8]) -> EncryptedTurn {
        let agent = make_cell_id(agent_seed);
        let mut conflict_set = ConflictSet::new();
        for &c in cells {
            conflict_set.insert(&make_cell_id(c));
        }

        let turn_commitment = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&[agent_seed]);
            *hasher.finalize().as_bytes()
        };

        let agent_commitment = TurnValidityPublicInputs::compute_agent_commitment(&agent);
        let conflict_set_commitment = conflict_set.commitment();

        EncryptedTurn {
            agent,
            ephemeral_public: [0u8; 32], // dummy
            nonce: [0u8; 12],            // dummy
            ciphertext: vec![0u8; 64],   // dummy
            turn_commitment,
            conflict_set,
            validity_proof: TurnValidityProof {
                proof_bytes: Vec::new(), // dummy
                public_inputs: TurnValidityPublicInputs {
                    turn_commitment,
                    agent_commitment,
                    claimed_nonce: 0,
                    min_fee: 100,
                    conflict_set_commitment,
                },
            },
            submitted_at: 0,
        }
    }

    #[test]
    fn metadata_verification_passes_for_consistent_turn() {
        let et = dummy_encrypted_turn(1, &[10, 20, 30]);
        assert_eq!(et.verify_metadata(), Ok(()));
    }

    #[test]
    fn metadata_verification_fails_on_agent_mismatch() {
        let mut et = dummy_encrypted_turn(1, &[10, 20, 30]);
        et.agent = make_cell_id(99); // mismatch
        assert_eq!(et.verify_metadata(), Err(EncryptedTurnError::AgentMismatch));
    }

    #[test]
    fn non_conflicting_turns_in_separate_buckets_or_same() {
        // Two turns accessing completely different cells should be in the same bucket
        // (they can parallelize).
        let t1 = dummy_encrypted_turn(1, &[10, 11]);
        let t2 = dummy_encrypted_turn(2, &[20, 21]);

        // They shouldn't conflict (different cells, Bloom filter should separate them).
        // Note: there's a tiny chance of false positive, but with k=8, m=256, n=2 it's negligible.
        if !t1.may_conflict_with(&t2) {
            let ordering = order_encrypted_turns(&[t1, t2]);
            // Should be 1 bucket (both can parallelize).
            assert_eq!(ordering.buckets.len(), 1);
            assert_eq!(ordering.buckets[0].turn_commitments.len(), 2);
        }
    }

    #[test]
    fn conflicting_turns_in_different_buckets() {
        // Two turns accessing the same cell must be in different buckets.
        let t1 = dummy_encrypted_turn(1, &[10]);
        let t2 = dummy_encrypted_turn(2, &[10]); // same cell

        assert!(t1.may_conflict_with(&t2));
        let ordering = order_encrypted_turns(&[t1, t2]);
        assert_eq!(ordering.buckets.len(), 2);
    }
}
