//! Queue program registry: maps queue_id -> QueueProgram for validation.
//!
//! When the Effect VM processes an `EnqueueMessage` effect targeting a queue
//! that has an attached program, the executor validates the enqueue against
//! the program's constraints BEFORE accepting the effect. The validation
//! result is hashed and bound to the STARK proof via the
//! `program_validation_hash` auxiliary column.
//!
//! This mirrors the `CellProgram` pattern from `circuit/src/dsl/circuit.rs`
//! where a `ProgramRegistry` maps VK hashes to programs. Here, we map
//! queue identifiers to their attached validation programs.

use std::collections::HashMap;

use pyana_circuit::field::BabyBear;
use pyana_circuit::poseidon2::hash_2_to_1;

// ============================================================================
// Queue Program Types
// ============================================================================

/// A queue program that validates enqueue operations.
///
/// This is a lightweight representation suitable for the turn executor.
/// The full program definition lives in `storage/src/programmable.rs`;
/// this type captures the validation-relevant subset.
#[derive(Clone, Debug)]
pub struct QueueProgram {
    /// Content-addressed identity of this program (hash of constraints).
    pub vk_hash: [u8; 32],
    /// Human-readable name.
    pub name: String,
    /// The validation constraints.
    pub constraints: Vec<QueueConstraint>,
}

/// Constraints for queue enqueue validation.
///
/// Mirrors the constraint types from `storage/src/programmable.rs` but
/// uses BabyBear field elements for circuit compatibility.
#[derive(Clone, Debug)]
pub enum QueueConstraint {
    /// Minimum deposit amount (in computrons).
    MinDeposit { amount: u64 },
    /// Sender must be in an authorized set (identified by Merkle root).
    SenderAuthorized {
        /// Merkle root of the authorized sender set.
        authorized_set_root: BabyBear,
        /// Known authorized senders (for executor-side validation).
        authorized_senders: Vec<BabyBear>,
    },
    /// Rate limit: max N enqueues per sender per epoch.
    RateLimit { max_per_epoch: u32 },
    /// Maximum message size constraint.
    MaxSize { max_bytes: u32 },
}

/// Context for validating an enqueue operation.
#[derive(Clone, Debug)]
pub struct EnqueueValidationContext {
    /// The sender's identity (as BabyBear field element).
    pub sender_id: BabyBear,
    /// Deposit amount being paid.
    pub deposit_amount: u32,
    /// Message hash being enqueued.
    pub message_hash: BabyBear,
    /// Current queue length.
    pub queue_len: u32,
    /// Sender's enqueue count this epoch (for rate limiting).
    pub sender_epoch_count: u32,
    /// Message size in bytes (for size constraints).
    pub message_size: u32,
}

/// Result of queue program validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidationResult {
    /// Whether validation passed.
    pub valid: bool,
    /// Hash binding the validation to the proof.
    /// Computed as hash(queue_vk_hash_as_field, hash(sender_id, message_hash)).
    pub validation_hash: BabyBear,
}

/// Error from queue program validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QueueProgramError {
    /// Deposit is below the minimum required by the program.
    InsufficientDeposit { required: u64, provided: u64 },
    /// Sender is not in the authorized set.
    UnauthorizedSender,
    /// Rate limit exceeded for this sender in the current epoch.
    RateLimitExceeded { max: u32, current: u32 },
    /// Message exceeds maximum size.
    MessageTooLarge { max: u32, actual: u32 },
    /// Queue program not found for the given queue.
    ProgramNotFound { queue_id: BabyBear },
}

impl std::fmt::Display for QueueProgramError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InsufficientDeposit { required, provided } => {
                write!(
                    f,
                    "insufficient deposit: required {}, provided {}",
                    required, provided
                )
            }
            Self::UnauthorizedSender => write!(f, "sender not in authorized set"),
            Self::RateLimitExceeded { max, current } => {
                write!(f, "rate limit exceeded: max {}, current {}", max, current)
            }
            Self::MessageTooLarge { max, actual } => {
                write!(f, "message too large: max {} bytes, actual {}", max, actual)
            }
            Self::ProgramNotFound { queue_id } => {
                write!(f, "no program found for queue {:?}", queue_id)
            }
        }
    }
}

// ============================================================================
// Queue Program Registry
// ============================================================================

/// Registry mapping queue identifiers to their attached programs.
///
/// The queue ID is derived from the queue's field[4] root or an explicit
/// identifier. When the executor processes an `EnqueueMessage` effect,
/// it looks up the target queue here to determine if program validation
/// is required.
#[derive(Clone, Debug, Default)]
pub struct QueueProgramRegistry {
    /// Map from queue_id (BabyBear field element) to program.
    programs: HashMap<u32, QueueProgram>,
}

impl QueueProgramRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        Self {
            programs: HashMap::new(),
        }
    }

    /// Register a queue program for a given queue ID.
    ///
    /// The queue_id corresponds to the queue's identifier in the cell state.
    /// If a program already exists for this queue, it is replaced.
    pub fn register(&mut self, queue_id: BabyBear, program: QueueProgram) {
        self.programs.insert(queue_id.0, program);
    }

    /// Look up the program for a queue.
    ///
    /// Returns `None` if the queue has no attached program (permissionless queue).
    pub fn get(&self, queue_id: BabyBear) -> Option<&QueueProgram> {
        self.programs.get(&queue_id.0)
    }

    /// Check if a queue has an attached program.
    pub fn has_program(&self, queue_id: BabyBear) -> bool {
        self.programs.contains_key(&queue_id.0)
    }

    /// Number of registered programs.
    pub fn len(&self) -> usize {
        self.programs.len()
    }

    /// Whether the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.programs.is_empty()
    }

    /// Remove a program from the registry.
    pub fn remove(&mut self, queue_id: BabyBear) -> Option<QueueProgram> {
        self.programs.remove(&queue_id.0)
    }
}

// ============================================================================
// Validation Logic
// ============================================================================

/// Validate an enqueue operation against a queue program.
///
/// Returns the validation result including a hash suitable for binding
/// to the STARK proof. If the queue has no program, returns a "pass"
/// result with a zero validation hash (backward compatible).
pub fn validate_enqueue(
    program: &QueueProgram,
    context: &EnqueueValidationContext,
) -> Result<ValidationResult, QueueProgramError> {
    // Check each constraint.
    for constraint in &program.constraints {
        match constraint {
            QueueConstraint::MinDeposit { amount } => {
                if (context.deposit_amount as u64) < *amount {
                    return Err(QueueProgramError::InsufficientDeposit {
                        required: *amount,
                        provided: context.deposit_amount as u64,
                    });
                }
            }
            QueueConstraint::SenderAuthorized {
                authorized_senders, ..
            } => {
                if !authorized_senders.contains(&context.sender_id) {
                    return Err(QueueProgramError::UnauthorizedSender);
                }
            }
            QueueConstraint::RateLimit { max_per_epoch } => {
                if context.sender_epoch_count >= *max_per_epoch {
                    return Err(QueueProgramError::RateLimitExceeded {
                        max: *max_per_epoch,
                        current: context.sender_epoch_count,
                    });
                }
            }
            QueueConstraint::MaxSize { max_bytes } => {
                if context.message_size > *max_bytes {
                    return Err(QueueProgramError::MessageTooLarge {
                        max: *max_bytes,
                        actual: context.message_size,
                    });
                }
            }
        }
    }

    // All constraints passed. Compute the validation hash.
    let validation_hash = compute_validation_hash(program, context);
    Ok(ValidationResult {
        valid: true,
        validation_hash,
    })
}

/// Compute the validation hash that binds program validation to the STARK proof.
///
/// validation_hash = hash(vk_hash_as_field, hash(sender_id, message_hash))
///
/// This hash is stored in aux[2] of the EnqueueMessage row and constrained
/// in the circuit to equal the expected value derived from the params.
pub fn compute_validation_hash(
    program: &QueueProgram,
    context: &EnqueueValidationContext,
) -> BabyBear {
    // Convert VK hash prefix to a field element (first 4 bytes, little-endian).
    let vk_field = vk_hash_to_field(&program.vk_hash);
    let inner = hash_2_to_1(context.sender_id, context.message_hash);
    hash_2_to_1(vk_field, inner)
}

/// Convert a 32-byte VK hash to a BabyBear field element.
/// Uses the first 4 bytes (little-endian), reduced mod p.
pub fn vk_hash_to_field(vk_hash: &[u8; 32]) -> BabyBear {
    let val = u32::from_le_bytes([vk_hash[0], vk_hash[1], vk_hash[2], vk_hash[3]]);
    BabyBear::new(val % pyana_circuit::field::BABYBEAR_P)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_program(name: &str, min_deposit: u64) -> QueueProgram {
        let mut vk_bytes = [0u8; 32];
        let hash = blake3::hash(name.as_bytes());
        vk_bytes.copy_from_slice(hash.as_bytes());
        QueueProgram {
            vk_hash: vk_bytes,
            name: name.to_string(),
            constraints: vec![QueueConstraint::MinDeposit {
                amount: min_deposit,
            }],
        }
    }

    fn make_acl_program(authorized: &[BabyBear], min_deposit: u64) -> QueueProgram {
        let mut vk_bytes = [0u8; 32];
        let hash = blake3::hash(b"acl_program");
        vk_bytes.copy_from_slice(hash.as_bytes());
        QueueProgram {
            vk_hash: vk_bytes,
            name: "acl".to_string(),
            constraints: vec![
                QueueConstraint::SenderAuthorized {
                    authorized_set_root: BabyBear::new(0xAC1),
                    authorized_senders: authorized.to_vec(),
                },
                QueueConstraint::MinDeposit {
                    amount: min_deposit,
                },
            ],
        }
    }

    fn default_context() -> EnqueueValidationContext {
        EnqueueValidationContext {
            sender_id: BabyBear::new(0x5E),
            deposit_amount: 100,
            message_hash: BabyBear::new(0xDEAD),
            queue_len: 0,
            sender_epoch_count: 0,
            message_size: 64,
        }
    }

    // --- Test: Registry lookup ---
    #[test]
    fn registry_lookup_found_and_not_found() {
        let mut registry = QueueProgramRegistry::new();
        let queue_id = BabyBear::new(42);
        let program = make_program("test_queue", 50);

        registry.register(queue_id, program.clone());

        assert!(registry.has_program(queue_id));
        assert!(!registry.has_program(BabyBear::new(99)));

        let found = registry.get(queue_id).unwrap();
        assert_eq!(found.name, "test_queue");
    }

    // --- Test: Valid enqueue accepted ---
    #[test]
    fn valid_enqueue_accepted() {
        let program = make_program("deposit_check", 50);
        let context = default_context(); // deposit=100, min=50

        let result = validate_enqueue(&program, &context);
        assert!(result.is_ok());
        let v = result.unwrap();
        assert!(v.valid);
        assert_ne!(v.validation_hash, BabyBear::ZERO);
    }

    // --- Test: Insufficient deposit rejected ---
    #[test]
    fn insufficient_deposit_rejected() {
        let program = make_program("high_deposit", 200);
        let context = default_context(); // deposit=100, min=200

        let result = validate_enqueue(&program, &context);
        assert_eq!(
            result,
            Err(QueueProgramError::InsufficientDeposit {
                required: 200,
                provided: 100,
            })
        );
    }

    // --- Test: Unauthorized sender rejected ---
    #[test]
    fn unauthorized_sender_rejected() {
        let authorized = vec![BabyBear::new(0xAA), BabyBear::new(0xBB)];
        let program = make_acl_program(&authorized, 10);
        let context = default_context(); // sender=0x5E, not in authorized

        let result = validate_enqueue(&program, &context);
        assert_eq!(result, Err(QueueProgramError::UnauthorizedSender));
    }

    // --- Test: Authorized sender accepted ---
    #[test]
    fn authorized_sender_accepted() {
        let authorized = vec![BabyBear::new(0x5E), BabyBear::new(0xBB)];
        let program = make_acl_program(&authorized, 10);
        let context = default_context(); // sender=0x5E, IS in authorized

        let result = validate_enqueue(&program, &context);
        assert!(result.is_ok());
    }

    // --- Test: Rate limit exceeded ---
    #[test]
    fn rate_limit_exceeded() {
        let mut vk_bytes = [0u8; 32];
        vk_bytes[0] = 0x42;
        let program = QueueProgram {
            vk_hash: vk_bytes,
            name: "rate_limited".to_string(),
            constraints: vec![QueueConstraint::RateLimit { max_per_epoch: 3 }],
        };
        let mut context = default_context();
        context.sender_epoch_count = 3; // at limit

        let result = validate_enqueue(&program, &context);
        assert_eq!(
            result,
            Err(QueueProgramError::RateLimitExceeded { max: 3, current: 3 })
        );
    }

    // --- Test: Rate limit within bounds accepted ---
    #[test]
    fn rate_limit_within_bounds_accepted() {
        let mut vk_bytes = [0u8; 32];
        vk_bytes[0] = 0x42;
        let program = QueueProgram {
            vk_hash: vk_bytes,
            name: "rate_limited".to_string(),
            constraints: vec![QueueConstraint::RateLimit { max_per_epoch: 3 }],
        };
        let mut context = default_context();
        context.sender_epoch_count = 2; // below limit

        let result = validate_enqueue(&program, &context);
        assert!(result.is_ok());
    }

    // --- Test: Validation hash is deterministic ---
    #[test]
    fn validation_hash_deterministic() {
        let program = make_program("stable", 10);
        let context = default_context();

        let h1 = compute_validation_hash(&program, &context);
        let h2 = compute_validation_hash(&program, &context);
        assert_eq!(h1, h2);
        assert_ne!(h1, BabyBear::ZERO);
    }

    // --- Test: Different programs produce different hashes ---
    #[test]
    fn different_programs_different_hashes() {
        let program_a = make_program("alpha", 10);
        let program_b = make_program("beta", 10);
        let context = default_context();

        let h_a = compute_validation_hash(&program_a, &context);
        let h_b = compute_validation_hash(&program_b, &context);
        assert_ne!(h_a, h_b);
    }

    // --- Test: Queue without program always passes (backward compat) ---
    #[test]
    fn queue_without_program_no_validation() {
        let registry = QueueProgramRegistry::new();
        let queue_id = BabyBear::new(999);

        // No program registered -> no validation needed.
        assert!(!registry.has_program(queue_id));
        assert!(registry.get(queue_id).is_none());
    }
}
