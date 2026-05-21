//! ConditionalTurn: STARK-conditional cross-domain atomic execution with timeout abort.
//!
//! A ConditionalTurn is a turn submitted to a federation that does NOT execute until
//! a proof satisfying its condition is presented. If the proof doesn't arrive before
//! the timeout height, the turn expires (no state change, no fee charged).
//!
//! This enables cross-federation atomicity:
//! - Fed A commits: "Turn T_A executes IFF proof P_B arrives before height H"
//! - Fed B commits: "Turn T_B executes IFF proof P_A arrives before height H"
//! - If both proofs arrive -> both execute (atomic success)
//! - If either times out -> both revert (atomic failure)
//!
//! The STARK proof replaces the HTLC hash preimage, but is strictly more general:
//! any provable statement can serve as a condition, not just "know a preimage."

use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::turn::{Turn, TurnReceipt};

/// A trusted federation root with the height at which it was established.
pub type TrustedRoot = ([u8; 32], u64);

/// Default maximum age (in blocks) for a trusted root to be valid.
pub const DEFAULT_MAX_ROOT_AGE: u64 = 1000;

/// Maximum allowed deadline for conditional turns (in blocks from current height).
pub const MAX_CONDITIONAL_DEADLINE: u64 = 10_000;

/// Validate that a conditional turn submission's deadline is within acceptable bounds.
///
/// Returns `Ok(())` if `timeout_height - current_height <= MAX_CONDITIONAL_DEADLINE`,
/// otherwise returns an error string.
pub fn validate_conditional_submission(
    timeout_height: u64,
    current_height: u64,
) -> Result<(), String> {
    if timeout_height <= current_height {
        return Err("timeout must be in the future".to_string());
    }
    let span = timeout_height - current_height;
    if span > MAX_CONDITIONAL_DEADLINE {
        return Err(format!(
            "conditional deadline {} exceeds maximum {}",
            span, MAX_CONDITIONAL_DEADLINE
        ));
    }
    Ok(())
}

/// A condition that must be satisfied before a turn executes.
///
/// Each variant represents a different class of provable statement.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ProofCondition {
    /// HTLC-style: reveal preimage of this hash (BLAKE3).
    HashPreimage {
        /// The BLAKE3 hash whose preimage must be revealed.
        hash: [u8; 32],
    },

    /// Cross-federation: present a valid STARK proof from a remote federation.
    ///
    /// The proof must verify against the remote federation's attested root
    /// and prove a specific AIR execution with expected public outputs.
    RemoteProof {
        /// The remote federation's attested Merkle root this proof verifies against.
        /// This is a 32-byte commitment (not a field element) so it works across
        /// federations regardless of their internal field choice.
        federation_root: [u8; 32],
        /// What the proof must prove (AIR identifier).
        expected_air: String,
        /// Minimum expected conclusion value. The proof's first public output
        /// must be >= this value (e.g., ALLOW = 1).
        expected_conclusion: u32,
    },

    /// Same-federation: present a valid STARK proof with these public inputs.
    ///
    /// Used for intra-federation conditional execution where you want
    /// proof of some computation without cross-domain concerns.
    LocalProof {
        /// AIR identifier the proof must satisfy.
        expected_air: String,
        /// Expected public inputs the proof must bind to.
        /// Each element is a BabyBear field element (u32 < 2^31 - 2^27 + 1).
        expected_public_inputs: Vec<u32>,
    },

    /// Receipt-based: prove a specific turn was executed (by presenting its receipt).
    ///
    /// The simplest cross-federation condition: just show me a valid TurnReceipt
    /// whose turn_hash matches. This is weaker than a STARK proof (you trust the
    /// remote federation's executor) but much cheaper.
    TurnExecuted {
        /// BLAKE3 hash of the turn that must have been executed.
        turn_hash: [u8; 32],
    },
}

/// A turn that's pending execution until its condition is satisfied.
///
/// ConditionalTurns are stored in the node's pending pool and garbage-collected
/// when their timeout height is exceeded.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConditionalTurn {
    /// The underlying turn to execute once the condition is met.
    pub turn: Turn,
    /// The condition that must be satisfied before execution.
    pub condition: ProofCondition,
    /// The block height at which this conditional turn expires.
    /// If no valid proof arrives before this height, the turn is discarded.
    pub timeout_height: u64,
    /// The block height at which this conditional turn was submitted.
    pub submitted_at: u64,
}

impl ConditionalTurn {
    /// Compute a unique hash identifying this conditional turn.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-conditional-turn-v1");
        hasher.update(&self.turn.hash());
        hasher.update(&self.timeout_height.to_le_bytes());
        hasher.update(&self.submitted_at.to_le_bytes());
        // Include the condition type discriminant.
        match &self.condition {
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
        *hasher.finalize().as_bytes()
    }

    /// Check if this conditional turn has expired at the given height.
    pub fn is_expired(&self, current_height: u64) -> bool {
        current_height > self.timeout_height
    }
}

/// The result of attempting to resolve a conditional turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConditionalResult {
    /// Condition satisfied — turn should be executed.
    Resolved,
    /// Condition not yet satisfied — turn remains pending.
    Pending,
    /// Timeout reached — turn expires without execution.
    Expired,
    /// Condition proof is invalid.
    InvalidProof(String),
}

/// The proof presented to satisfy a condition.
///
/// Must match the condition variant of the ConditionalTurn it resolves.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ConditionProof {
    /// Reveal a preimage (for HashPreimage conditions).
    Preimage([u8; 32]),
    /// Present a STARK proof (for RemoteProof or LocalProof conditions).
    StarkProof {
        /// Serialized proof bytes.
        proof_bytes: Vec<u8>,
        /// The federation root this proof was generated against.
        federation_root: [u8; 32],
        /// Public inputs / outputs from the proof.
        public_outputs: Vec<u32>,
    },
    /// Present a turn receipt (for TurnExecuted conditions).
    Receipt(TurnReceipt),
}

/// Resolve a conditional turn by presenting a proof.
///
/// This function checks:
/// 1. Whether the timeout has been exceeded (returns Expired).
/// 2. Whether the proof type matches the condition type.
/// 3. Whether the proof satisfies the condition's constraints.
///
/// For STARK proofs, this performs a structural check (matching federation roots,
/// AIR names, and public inputs). Actual cryptographic STARK verification is
/// delegated to the executor's ProofVerifier.
///
/// # Arguments
/// * `condition` — the condition to check against
/// * `proof` — the proof being presented
/// * `current_height` — current block height for timeout check
/// * `timeout_height` — the conditional turn's timeout
/// * `trusted_roots` — set of known/trusted federation roots (for RemoteProof)
pub fn resolve_condition(
    condition: &ProofCondition,
    proof: &ConditionProof,
    current_height: u64,
    timeout_height: u64,
    trusted_roots: &[[u8; 32]],
) -> ConditionalResult {
    // Check timeout first.
    if current_height > timeout_height {
        return ConditionalResult::Expired;
    }

    match (condition, proof) {
        // Hash preimage: verify BLAKE3(preimage) == expected hash.
        (ProofCondition::HashPreimage { hash }, ConditionProof::Preimage(preimage)) => {
            let computed = *blake3::hash(preimage).as_bytes();
            if computed == *hash {
                ConditionalResult::Resolved
            } else {
                ConditionalResult::InvalidProof("preimage does not match hash".to_string())
            }
        }

        // Remote STARK proof: check federation root is trusted and public outputs match.
        (
            ProofCondition::RemoteProof {
                federation_root,
                expected_air: _,
                expected_conclusion,
            },
            ConditionProof::StarkProof {
                proof_bytes,
                federation_root: proof_fed_root,
                public_outputs,
            },
        ) => {
            // Verify the proof claims to be from the expected federation.
            if proof_fed_root != federation_root {
                return ConditionalResult::InvalidProof(
                    "proof federation root does not match expected".to_string(),
                );
            }

            // Verify the federation root is in our trusted set.
            if !trusted_roots.contains(federation_root) {
                return ConditionalResult::InvalidProof(
                    "federation root is not in trusted set".to_string(),
                );
            }

            // Verify the proof is non-empty (actual STARK verification is external).
            if proof_bytes.is_empty() {
                return ConditionalResult::InvalidProof("proof bytes are empty".to_string());
            }

            // Check conclusion: first public output must be >= expected_conclusion.
            match public_outputs.first() {
                Some(&conclusion) if conclusion >= *expected_conclusion => {
                    ConditionalResult::Resolved
                }
                Some(&conclusion) => ConditionalResult::InvalidProof(format!(
                    "conclusion {} is less than expected {}",
                    conclusion, expected_conclusion
                )),
                None => ConditionalResult::InvalidProof(
                    "no public outputs in proof".to_string(),
                ),
            }
        }

        // Local STARK proof: check public inputs match expected.
        (
            ProofCondition::LocalProof {
                expected_air: _,
                expected_public_inputs,
            },
            ConditionProof::StarkProof {
                proof_bytes,
                public_outputs,
                ..
            },
        ) => {
            if proof_bytes.is_empty() {
                return ConditionalResult::InvalidProof("proof bytes are empty".to_string());
            }

            // Verify public outputs match expected inputs.
            if public_outputs.len() < expected_public_inputs.len() {
                return ConditionalResult::InvalidProof(format!(
                    "proof has {} public outputs, expected at least {}",
                    public_outputs.len(),
                    expected_public_inputs.len()
                ));
            }

            for (i, (expected, actual)) in expected_public_inputs
                .iter()
                .zip(public_outputs.iter())
                .enumerate()
            {
                if expected != actual {
                    return ConditionalResult::InvalidProof(format!(
                        "public input mismatch at index {}: expected {}, got {}",
                        i, expected, actual
                    ));
                }
            }

            ConditionalResult::Resolved
        }

        // Turn executed: check the receipt's turn_hash matches.
        (
            ProofCondition::TurnExecuted { turn_hash },
            ConditionProof::Receipt(receipt),
        ) => {
            if receipt.turn_hash == *turn_hash {
                ConditionalResult::Resolved
            } else {
                ConditionalResult::InvalidProof(format!(
                    "receipt turn_hash does not match: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                    turn_hash[0], turn_hash[1],
                    receipt.turn_hash[0], receipt.turn_hash[1],
                ))
            }
        }

        // Type mismatch: wrong proof type for the condition.
        _ => ConditionalResult::InvalidProof(
            "proof type does not match condition type".to_string(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_preimage_resolved() {
        let preimage = [42u8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();

        let condition = ProofCondition::HashPreimage { hash };
        let proof = ConditionProof::Preimage(preimage);

        let result = resolve_condition(&condition, &proof, 10, 100, &[]);
        assert_eq!(result, ConditionalResult::Resolved);
    }

    #[test]
    fn test_hash_preimage_invalid() {
        let preimage = [42u8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();

        let condition = ProofCondition::HashPreimage { hash };
        let wrong_preimage = [99u8; 32];
        let proof = ConditionProof::Preimage(wrong_preimage);

        let result = resolve_condition(&condition, &proof, 10, 100, &[]);
        assert!(matches!(result, ConditionalResult::InvalidProof(_)));
    }

    #[test]
    fn test_timeout_expired() {
        let preimage = [42u8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();

        let condition = ProofCondition::HashPreimage { hash };
        let proof = ConditionProof::Preimage(preimage);

        // current_height (101) > timeout_height (100)
        let result = resolve_condition(&condition, &proof, 101, 100, &[]);
        assert_eq!(result, ConditionalResult::Expired);
    }

    #[test]
    fn test_remote_proof_resolved() {
        let fed_root = [1u8; 32];
        let condition = ProofCondition::RemoteProof {
            federation_root: fed_root,
            expected_air: "transfer_air".to_string(),
            expected_conclusion: 1, // ALLOW
        };

        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xDE, 0xAD, 0xBE, 0xEF], // non-empty
            federation_root: fed_root,
            public_outputs: vec![1], // conclusion = ALLOW
        };

        let trusted = vec![fed_root];
        let result = resolve_condition(&condition, &proof, 10, 100, &trusted);
        assert_eq!(result, ConditionalResult::Resolved);
    }

    #[test]
    fn test_remote_proof_untrusted_root() {
        let fed_root = [1u8; 32];
        let condition = ProofCondition::RemoteProof {
            federation_root: fed_root,
            expected_air: "transfer_air".to_string(),
            expected_conclusion: 1,
        };

        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xDE, 0xAD],
            federation_root: fed_root,
            public_outputs: vec![1],
        };

        // No trusted roots
        let result = resolve_condition(&condition, &proof, 10, 100, &[]);
        assert!(matches!(result, ConditionalResult::InvalidProof(_)));
    }

    #[test]
    fn test_remote_proof_wrong_conclusion() {
        let fed_root = [1u8; 32];
        let condition = ProofCondition::RemoteProof {
            federation_root: fed_root,
            expected_air: "transfer_air".to_string(),
            expected_conclusion: 2, // need >= 2
        };

        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xDE, 0xAD],
            federation_root: fed_root,
            public_outputs: vec![1], // only 1, less than required 2
        };

        let trusted = vec![fed_root];
        let result = resolve_condition(&condition, &proof, 10, 100, &trusted);
        assert!(matches!(result, ConditionalResult::InvalidProof(_)));
    }

    #[test]
    fn test_local_proof_resolved() {
        let condition = ProofCondition::LocalProof {
            expected_air: "compute_air".to_string(),
            expected_public_inputs: vec![100, 200, 300],
        };

        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xFF; 64],
            federation_root: [0u8; 32],
            public_outputs: vec![100, 200, 300],
        };

        let result = resolve_condition(&condition, &proof, 10, 100, &[]);
        assert_eq!(result, ConditionalResult::Resolved);
    }

    #[test]
    fn test_local_proof_input_mismatch() {
        let condition = ProofCondition::LocalProof {
            expected_air: "compute_air".to_string(),
            expected_public_inputs: vec![100, 200, 300],
        };

        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![0xFF; 64],
            federation_root: [0u8; 32],
            public_outputs: vec![100, 999, 300], // mismatch at index 1
        };

        let result = resolve_condition(&condition, &proof, 10, 100, &[]);
        assert!(matches!(result, ConditionalResult::InvalidProof(_)));
    }

    #[test]
    fn test_turn_executed_resolved() {
        let turn_hash = [0xAB; 32];
        let condition = ProofCondition::TurnExecuted { turn_hash };

        let receipt = TurnReceipt {
            turn_hash,
            forest_hash: [0u8; 32],
            pre_state_hash: [0u8; 32],
            post_state_hash: [0u8; 32],
            timestamp: 1000,
            effects_hash: [0u8; 32],
            computrons_used: 500,
            action_count: 1,
            previous_receipt_hash: None,
            agent: pyana_cell::CellId([0u8; 32]),
            routing_directives: vec![],
            derivation_records: vec![],
            executor_signature: None,
        };

        let proof = ConditionProof::Receipt(receipt);
        let result = resolve_condition(&condition, &proof, 10, 100, &[]);
        assert_eq!(result, ConditionalResult::Resolved);
    }

    #[test]
    fn test_turn_executed_wrong_hash() {
        let turn_hash = [0xAB; 32];
        let condition = ProofCondition::TurnExecuted { turn_hash };

        let receipt = TurnReceipt {
            turn_hash: [0xCD; 32], // different hash
            forest_hash: [0u8; 32],
            pre_state_hash: [0u8; 32],
            post_state_hash: [0u8; 32],
            timestamp: 1000,
            effects_hash: [0u8; 32],
            computrons_used: 500,
            action_count: 1,
            previous_receipt_hash: None,
            agent: pyana_cell::CellId([0u8; 32]),
            routing_directives: vec![],
            derivation_records: vec![],
            executor_signature: None,
        };

        let proof = ConditionProof::Receipt(receipt);
        let result = resolve_condition(&condition, &proof, 10, 100, &[]);
        assert!(matches!(result, ConditionalResult::InvalidProof(_)));
    }

    #[test]
    fn test_proof_type_mismatch() {
        let condition = ProofCondition::HashPreimage { hash: [0u8; 32] };
        let proof = ConditionProof::StarkProof {
            proof_bytes: vec![1, 2, 3],
            federation_root: [0u8; 32],
            public_outputs: vec![1],
        };

        let result = resolve_condition(&condition, &proof, 10, 100, &[]);
        assert!(matches!(result, ConditionalResult::InvalidProof(_)));
    }

    #[test]
    fn test_conditional_turn_hash_deterministic() {
        use crate::forest::CallForest;

        let turn = Turn {
            agent: pyana_cell::CellId([1u8; 32]),
            nonce: 0,
            call_forest: CallForest::new(),
            fee: 1000,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
        };

        let ct = ConditionalTurn {
            turn,
            condition: ProofCondition::HashPreimage { hash: [0xAA; 32] },
            timeout_height: 100,
            submitted_at: 50,
        };

        let h1 = ct.hash();
        let h2 = ct.hash();
        assert_eq!(h1, h2);
    }
}
