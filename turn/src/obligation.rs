//! ProofObligation: bonded commitment to produce a proof.
//!
//! The categorical dual of ConditionalTurn:
//! - ConditionalTurn says: "I'll execute when you prove X."
//! - ProofObligation says: "I commit to proving X, and I've locked stake against failure."
//!
//! This closes the compact closure in the categorical structure and eliminates the
//! "free option" problem. Without obligations, a party can create a ConditionalTurn
//! and never deliver the proof — wasting the other party's locked resources for free.
//! With a bonded obligation, failure to deliver forfeits real stake.
//!
//! # Cross-Federation Atomic Swap Pattern
//!
//! 1. Alice creates ProofObligation (bonded to deliver proof of her transfer)
//! 2. Bob creates ProofObligation (bonded to deliver proof of his transfer)
//! 3. Both create ConditionalTurns conditioned on the other's obligation being fulfilled
//! 4. Both deliver proofs -> both turns execute + both stakes returned
//! 5. If one fails -> their stake is slashed to the other party (compensation)

use pyana_cell::{CellId, NoteCommitment};
use serde::{Deserialize, Serialize};

use crate::conditional::{ConditionProof, ConditionalResult, ProofCondition, resolve_condition};

/// Maximum allowed deadline for proof obligations (in blocks from current height).
pub const MAX_OBLIGATION_DEADLINE: u64 = 10_000;

/// Validate that an obligation deadline is within acceptable bounds.
///
/// Returns `Ok(())` if `deadline_height - current_height <= MAX_OBLIGATION_DEADLINE`,
/// otherwise returns an error string.
pub fn validate_obligation_deadline(
    deadline_height: u64,
    current_height: u64,
) -> Result<(), String> {
    if deadline_height <= current_height {
        return Err("deadline must be in the future".to_string());
    }
    let span = deadline_height - current_height;
    if span > MAX_OBLIGATION_DEADLINE {
        return Err(format!(
            "obligation deadline {} exceeds maximum {}",
            span, MAX_OBLIGATION_DEADLINE
        ));
    }
    Ok(())
}

/// Errors arising from obligation lifecycle operations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ObligationError {
    /// The obligation has already been fulfilled.
    AlreadyFulfilled { id: [u8; 32] },
    /// The obligation has already been slashed.
    AlreadySlashed { id: [u8; 32] },
    /// The obligation has already been cancelled.
    AlreadyCancelled { id: [u8; 32] },
    /// The proof was presented after the deadline.
    DeadlinePassed {
        id: [u8; 32],
        deadline: u64,
        current_height: u64,
    },
    /// Cannot slash before deadline.
    DeadlineNotReached {
        id: [u8; 32],
        deadline: u64,
        current_height: u64,
    },
    /// The presented proof is invalid.
    InvalidProof { id: [u8; 32], reason: String },
}

impl core::fmt::Display for ObligationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ObligationError::AlreadyFulfilled { id } => {
                write!(f, "obligation {:02x}{:02x}... already fulfilled", id[0], id[1])
            }
            ObligationError::AlreadySlashed { id } => {
                write!(f, "obligation {:02x}{:02x}... already slashed", id[0], id[1])
            }
            ObligationError::AlreadyCancelled { id } => {
                write!(
                    f,
                    "obligation {:02x}{:02x}... already cancelled",
                    id[0], id[1]
                )
            }
            ObligationError::DeadlinePassed {
                id,
                deadline,
                current_height,
            } => {
                write!(
                    f,
                    "obligation {:02x}{:02x}... deadline passed: deadline={}, current={}",
                    id[0], id[1], deadline, current_height
                )
            }
            ObligationError::DeadlineNotReached {
                id,
                deadline,
                current_height,
            } => {
                write!(
                    f,
                    "obligation {:02x}{:02x}... deadline not yet reached: deadline={}, current={}",
                    id[0], id[1], deadline, current_height
                )
            }
            ObligationError::InvalidProof { id, reason } => {
                write!(
                    f,
                    "obligation {:02x}{:02x}... invalid proof: {}",
                    id[0], id[1], reason
                )
            }
        }
    }
}

impl std::error::Error for ObligationError {}

/// A bonded commitment to produce a proof satisfying a condition.
///
/// The obligor locks stake; if they fail to deliver before the deadline,
/// the stake is forfeit (slashed to the beneficiary).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProofObligation {
    /// Unique ID for this obligation (BLAKE3 hash of creation parameters).
    pub id: [u8; 32],
    /// Who is obligated to produce the proof.
    pub obligor: CellId,
    /// Who benefits if the proof is delivered (or receives stake on failure).
    pub beneficiary: CellId,
    /// What must be proven.
    pub condition: ProofCondition,
    /// Deadline (federation height). Proof must arrive before this.
    pub deadline_height: u64,
    /// Stake locked by the obligor (note commitment).
    pub stake: NoteCommitment,
    /// When this obligation was created (federation height).
    pub created_at: u64,
}

impl ProofObligation {
    /// Compute a unique hash identifying this obligation.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-proof-obligation-v1");
        hasher.update(&self.id);
        hasher.update(self.obligor.as_bytes());
        hasher.update(self.beneficiary.as_bytes());
        hasher.update(&self.deadline_height.to_le_bytes());
        hasher.update(&self.stake.0);
        hasher.update(&self.created_at.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Check if this obligation has expired at the given height.
    pub fn is_expired(&self, current_height: u64) -> bool {
        current_height > self.deadline_height
    }
}

/// The result of an obligation lifecycle.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ObligationOutcome {
    /// Proof delivered before deadline — obligation fulfilled, stake returned to obligor.
    Fulfilled { proof: ConditionProof },
    /// Deadline passed without proof — stake slashed to beneficiary.
    Slashed,
    /// Obligation cancelled by mutual agreement (both parties sign).
    Cancelled,
}

/// Create a proof obligation (locks stake).
///
/// The returned obligation has a deterministic ID derived from its creation parameters.
/// The caller is responsible for ensuring the stake note commitment exists and
/// marking it as committed (preventing double-use).
pub fn create_obligation(
    obligor: CellId,
    beneficiary: CellId,
    condition: ProofCondition,
    deadline_height: u64,
    stake: NoteCommitment,
) -> ProofObligation {
    // Derive a deterministic obligation ID from its parameters.
    let mut hasher = blake3::Hasher::new_derive_key("pyana-obligation-id-v1");
    hasher.update(obligor.as_bytes());
    hasher.update(beneficiary.as_bytes());
    hasher.update(&deadline_height.to_le_bytes());
    hasher.update(&stake.0);
    // Include condition discriminant for uniqueness.
    match &condition {
        ProofCondition::HashPreimage { hash } => {
            hasher.update(&[0u8]);
            hasher.update(hash);
        }
        ProofCondition::RemoteProof {
            federation_root,
            expected_air,
            expected_conclusion,
        } => {
            hasher.update(&[1u8]);
            hasher.update(federation_root);
            hasher.update(expected_air.as_bytes());
            hasher.update(&expected_conclusion.to_le_bytes());
        }
        ProofCondition::LocalProof {
            expected_air,
            expected_public_inputs,
        } => {
            hasher.update(&[2u8]);
            hasher.update(expected_air.as_bytes());
            for pi in expected_public_inputs {
                hasher.update(&pi.to_le_bytes());
            }
        }
        ProofCondition::TurnExecuted { turn_hash } => {
            hasher.update(&[3u8]);
            hasher.update(turn_hash);
        }
    }
    let id = *hasher.finalize().as_bytes();

    // Use a fixed created_at of 0 — the executor will set the real height.
    // We use the current parameters to derive the ID deterministically.
    ProofObligation {
        id,
        obligor,
        beneficiary,
        condition,
        deadline_height,
        stake,
        created_at: 0,
    }
}

/// Fulfill an obligation by presenting the required proof.
///
/// Checks:
/// 1. The deadline has not passed.
/// 2. The proof satisfies the condition (using the same resolution logic as ConditionalTurn).
///
/// On success, returns `ObligationOutcome::Fulfilled` — the executor should return
/// the locked stake to the obligor.
pub fn fulfill_obligation(
    obligation: &ProofObligation,
    proof: &ConditionProof,
    current_height: u64,
    trusted_roots: &[[u8; 32]],
) -> Result<ObligationOutcome, ObligationError> {
    // Check deadline.
    if current_height > obligation.deadline_height {
        return Err(ObligationError::DeadlinePassed {
            id: obligation.id,
            deadline: obligation.deadline_height,
            current_height,
        });
    }

    // Resolve the condition using the same logic as ConditionalTurn.
    let result = resolve_condition(
        &obligation.condition,
        proof,
        current_height,
        obligation.deadline_height,
        trusted_roots,
    );

    match result {
        ConditionalResult::Resolved => Ok(ObligationOutcome::Fulfilled {
            proof: proof.clone(),
        }),
        ConditionalResult::InvalidProof(reason) => Err(ObligationError::InvalidProof {
            id: obligation.id,
            reason,
        }),
        ConditionalResult::Expired => Err(ObligationError::DeadlinePassed {
            id: obligation.id,
            deadline: obligation.deadline_height,
            current_height,
        }),
        ConditionalResult::Pending => Err(ObligationError::InvalidProof {
            id: obligation.id,
            reason: "condition is still pending (proof insufficient)".to_string(),
        }),
    }
}

/// Check if an obligation has expired (deadline passed without fulfillment).
///
/// Returns `Some(ObligationOutcome::Slashed)` if the deadline has passed,
/// meaning the stake should be transferred to the beneficiary.
/// Returns `None` if the obligation is still within its deadline.
pub fn check_expiry(
    obligation: &ProofObligation,
    current_height: u64,
) -> Option<ObligationOutcome> {
    if current_height > obligation.deadline_height {
        Some(ObligationOutcome::Slashed)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn alice() -> CellId {
        CellId([1u8; 32])
    }

    fn bob() -> CellId {
        CellId([2u8; 32])
    }

    fn test_stake() -> NoteCommitment {
        NoteCommitment([0xAA; 32])
    }

    #[test]
    fn test_create_and_fulfill_obligation() {
        let preimage = [42u8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();

        let condition = ProofCondition::HashPreimage { hash };
        let obligation = create_obligation(alice(), bob(), condition, 100, test_stake());

        // Verify creation.
        assert_eq!(obligation.obligor, alice());
        assert_eq!(obligation.beneficiary, bob());
        assert_eq!(obligation.deadline_height, 100);
        assert_eq!(obligation.stake, test_stake());

        // Fulfill with valid proof before deadline.
        let proof = ConditionProof::Preimage(preimage);
        let mut nullifiers = HashSet::new();
        let result = fulfill_obligation(&obligation, &proof, 50, &[], DEFAULT_MAX_ROOT_AGE, &mut nullifiers);
        assert!(result.is_ok());
        assert!(matches!(result.unwrap(), ObligationOutcome::Fulfilled { .. }));
    }

    #[test]
    fn test_obligation_expires_stake_slashed() {
        let preimage = [42u8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();

        let condition = ProofCondition::HashPreimage { hash };
        let obligation = create_obligation(alice(), bob(), condition, 100, test_stake());

        // Check before deadline — not expired.
        assert!(check_expiry(&obligation, 50).is_none());
        assert!(check_expiry(&obligation, 100).is_none());

        // Check after deadline — slashed.
        let outcome = check_expiry(&obligation, 101);
        assert!(outcome.is_some());
        assert!(matches!(outcome.unwrap(), ObligationOutcome::Slashed));
    }

    #[test]
    fn test_fulfill_after_deadline_rejected() {
        let preimage = [42u8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();

        let condition = ProofCondition::HashPreimage { hash };
        let obligation = create_obligation(alice(), bob(), condition, 100, test_stake());

        // Try to fulfill after deadline.
        let proof = ConditionProof::Preimage(preimage);
        let result = fulfill_obligation(&obligation, &proof, 101, &[]);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            ObligationError::DeadlinePassed {
                deadline: 100,
                current_height: 101,
                ..
            }
        ));
    }

    #[test]
    fn test_slash_before_deadline_not_possible() {
        let preimage = [42u8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();

        let condition = ProofCondition::HashPreimage { hash };
        let obligation = create_obligation(alice(), bob(), condition, 100, test_stake());

        // Cannot slash before deadline — check_expiry returns None.
        assert!(check_expiry(&obligation, 50).is_none());
        assert!(check_expiry(&obligation, 99).is_none());
        assert!(check_expiry(&obligation, 100).is_none());
    }

    #[test]
    fn test_invalid_proof_rejected_obligation_still_pending() {
        let preimage = [42u8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();

        let condition = ProofCondition::HashPreimage { hash };
        let obligation = create_obligation(alice(), bob(), condition, 100, test_stake());

        // Present wrong preimage.
        let wrong_proof = ConditionProof::Preimage([99u8; 32]);
        let result = fulfill_obligation(&obligation, &wrong_proof, 50, &[]);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            ObligationError::InvalidProof { .. }
        ));

        // Obligation is still pending — can still be fulfilled with correct proof.
        let correct_proof = ConditionProof::Preimage(preimage);
        let result = fulfill_obligation(&obligation, &correct_proof, 60, &[]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_obligation_with_remote_proof_condition() {
        let fed_root = [0xFE; 32];
        let condition = ProofCondition::RemoteProof {
            federation_root: fed_root,
            expected_air: "transfer_air".to_string(),
            expected_conclusion: 1,
        };

        let obligation = create_obligation(alice(), bob(), condition, 200, test_stake());

        // Fulfill with valid STARK proof.
        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xDE, 0xAD, 0xBE, 0xEF],
            federation_root: fed_root,
            public_outputs: vec![1],
        };

        let trusted = [fed_root];
        let result = fulfill_obligation(&obligation, &proof, 150, &trusted);
        assert!(result.is_ok());
    }

    #[test]
    fn test_obligation_id_deterministic() {
        let hash = [0xBB; 32];
        let condition = ProofCondition::HashPreimage { hash };

        let ob1 = create_obligation(alice(), bob(), condition.clone(), 100, test_stake());
        let ob2 = create_obligation(alice(), bob(), condition, 100, test_stake());

        assert_eq!(ob1.id, ob2.id);
    }

    #[test]
    fn test_obligation_id_unique_per_params() {
        let hash = [0xBB; 32];
        let condition = ProofCondition::HashPreimage { hash };

        let ob1 = create_obligation(alice(), bob(), condition.clone(), 100, test_stake());
        let ob2 = create_obligation(alice(), bob(), condition, 200, test_stake()); // different deadline

        assert_ne!(ob1.id, ob2.id);
    }

    #[test]
    fn test_obligation_hash_stable() {
        let hash = [0xBB; 32];
        let condition = ProofCondition::HashPreimage { hash };
        let obligation = create_obligation(alice(), bob(), condition, 100, test_stake());

        let h1 = obligation.hash();
        let h2 = obligation.hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_proof_type_mismatch_rejected() {
        let hash = [0xBB; 32];
        let condition = ProofCondition::HashPreimage { hash };
        let obligation = create_obligation(alice(), bob(), condition, 100, test_stake());

        // Present a STARK proof for a hash preimage condition.
        let wrong_type_proof = ConditionProof::StarkProof {
            proof_bytes: vec![1, 2, 3],
            federation_root: [0u8; 32],
            public_outputs: vec![1],
        };

        let result = fulfill_obligation(&obligation, &wrong_type_proof, 50, &[]);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            ObligationError::InvalidProof { .. }
        ));
    }
}
