//! Programmable queues: queues with attached DSL programs that validate every operation.
//!
//! A `ProgrammableQueue` is a `MerkleQueue` paired with a `QueueProgram` that
//! cryptographically enforces enqueue/dequeue rules. The queue becomes a programmable
//! channel where operations are validated against constraints before mutation.
//!
//! # Design
//!
//! - The program is proven in-circuit: invalid operations produce invalid proofs.
//! - Each queue has a content-addressed identity (`program_vk_hash`) derived from its rules.
//! - Programs support lookup tables (for ACL membership, rate limits, etc.).
//! - A `QueueFactory` governs which programs can be instantiated.
//!
//! # Integration
//!
//! - Composes with the Effect VM's `Custom` effect dispatch (circuit/src/effect_vm.rs).
//! - Follows the `CellProgram` pattern from turn/src/executor.rs.
//! - Uses `CircuitDescriptor`-style constraint expressions (circuit/src/dsl/circuit.rs).

use crate::queue::{DequeueProof, MerkleQueue, QueueEntry, QueueError};

// ============================================================================
// Core types
// ============================================================================

/// A queue with an attached validation program (QueueProgram).
/// Every enqueue/dequeue must satisfy the program's constraints.
/// The program is proven in-circuit — invalid operations produce invalid proofs.
#[derive(Debug, Clone)]
pub struct ProgrammableQueue {
    /// The underlying Merkle queue.
    queue: MerkleQueue,
    /// The validation program for enqueue operations.
    enqueue_program: QueueProgram,
    /// Optional validation program for dequeue conditions.
    dequeue_program: Option<QueueProgram>,
    /// Content-addressed identity of this queue's rules.
    program_vk_hash: [u8; 32],
    /// Queue metadata.
    name: String,
    /// Owner identity (public key).
    owner: [u8; 32],
    /// Sequence counter for MonotonicSequence constraint.
    next_sequence: u64,
}

/// A queue validation program expressed as constraints.
/// This is a simplified CircuitDescriptor specialized for queue operations.
#[derive(Debug, Clone)]
pub struct QueueProgram {
    /// Human-readable name.
    pub name: String,
    /// The constraints that must be satisfied for each operation.
    pub constraints: Vec<QueueConstraint>,
    /// Lookup tables (for ACL membership, rate limits, etc.)
    pub lookup_tables: Vec<QueueLookupTable>,
}

/// Constraints specific to queue operations.
#[derive(Debug, Clone)]
pub enum QueueConstraint {
    /// Sender must be in an authorized set (Merkle membership via lookup).
    SenderAuthorized { authorized_set_root: [u8; 32] },
    /// Message content hash must satisfy a pattern (e.g., type prefix).
    ContentPattern { required_prefix: Vec<u8> },
    /// Minimum deposit amount.
    MinDeposit { amount: u64 },
    /// Maximum message size (bytes).
    MaxSize { bytes: usize },
    /// Rate limit: max N enqueues per sender per epoch.
    RateLimit { max_per_epoch: u32, epoch_duration: u64 },
    /// Sequence number must be monotonically increasing.
    MonotonicSequence,
    /// Temporal gate: operation only valid after/before a height.
    TemporalGate { not_before: Option<u64>, not_after: Option<u64> },
    /// Conditional dequeue: requires knowledge of a preimage.
    PreimageGate { commitment: [u8; 32] },
    /// Custom (arbitrary constraint expression — full DSL power).
    Custom { expr: String, description: String },
}

/// A lookup table for queue program validation (e.g., authorized sender set).
#[derive(Debug, Clone)]
pub struct QueueLookupTable {
    pub name: String,
    pub entries: Vec<[u8; 32]>,
}

/// Context passed to validation (block height, sender info, etc.)
#[derive(Debug, Clone)]
pub struct ValidationContext {
    /// The sender's identity (public key).
    pub sender: [u8; 32],
    /// Current block height.
    pub current_height: u64,
    /// Current epoch number.
    pub current_epoch: u64,
    /// Sender's enqueue count this epoch (for rate limiting).
    pub sender_epoch_count: u32,
    /// Optional preimage (for conditional dequeue).
    pub preimage: Option<[u8; 32]>,
    /// Sequence number for this message (for monotonic ordering).
    pub sequence: Option<u64>,
}

// ============================================================================
// Errors
// ============================================================================

/// Errors from programmable queue operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProgramError {
    /// A constraint was violated.
    ConstraintViolation { constraint: String, detail: String },
    /// The underlying queue returned an error.
    QueueError(QueueError),
    /// The dequeue program rejected the operation.
    DequeueRejected { reason: String },
}

impl From<QueueError> for ProgramError {
    fn from(e: QueueError) -> Self {
        ProgramError::QueueError(e)
    }
}

/// Errors from the queue factory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FactoryError {
    /// The program exceeds factory limits.
    TooManyConstraints { count: usize, max: usize },
    /// A lookup table is too large.
    LookupTableTooLarge { table: String, entries: usize, max: usize },
    /// A disallowed constraint type was used.
    DisallowedConstraint { kind: ConstraintKind },
    /// Program has no constraints.
    EmptyProgram,
}

/// Kind tag for constraint types (used by factory whitelist).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintKind {
    SenderAuthorized,
    ContentPattern,
    MinDeposit,
    MaxSize,
    RateLimit,
    MonotonicSequence,
    TemporalGate,
    PreimageGate,
    Custom,
}

impl QueueConstraint {
    /// Get the kind tag for this constraint.
    pub fn kind(&self) -> ConstraintKind {
        match self {
            QueueConstraint::SenderAuthorized { .. } => ConstraintKind::SenderAuthorized,
            QueueConstraint::ContentPattern { .. } => ConstraintKind::ContentPattern,
            QueueConstraint::MinDeposit { .. } => ConstraintKind::MinDeposit,
            QueueConstraint::MaxSize { .. } => ConstraintKind::MaxSize,
            QueueConstraint::RateLimit { .. } => ConstraintKind::RateLimit,
            QueueConstraint::MonotonicSequence => ConstraintKind::MonotonicSequence,
            QueueConstraint::TemporalGate { .. } => ConstraintKind::TemporalGate,
            QueueConstraint::PreimageGate { .. } => ConstraintKind::PreimageGate,
            QueueConstraint::Custom { .. } => ConstraintKind::Custom,
        }
    }
}

// ============================================================================
// ProgrammableQueue implementation
// ============================================================================

impl ProgrammableQueue {
    /// Create a new programmable queue with the given program and capacity.
    pub fn new(
        name: String,
        owner: [u8; 32],
        enqueue_program: QueueProgram,
        dequeue_program: Option<QueueProgram>,
        capacity: usize,
    ) -> Self {
        let program_vk_hash = compute_vk_hash(&enqueue_program, dequeue_program.as_ref());
        Self {
            queue: MerkleQueue::new(capacity),
            enqueue_program,
            dequeue_program,
            program_vk_hash,
            name,
            owner,
            next_sequence: 0,
        }
    }

    /// Validate then enqueue. Returns error if program constraints violated.
    pub fn enqueue_validated(
        &mut self,
        entry: QueueEntry,
        context: &ValidationContext,
    ) -> Result<[u8; 32], ProgramError> {
        self.validate_enqueue(&entry, context)?;
        // If MonotonicSequence is in constraints, advance counter.
        if self.enqueue_program.constraints.iter().any(|c| matches!(c, QueueConstraint::MonotonicSequence)) {
            self.next_sequence += 1;
        }
        let root = self.queue.enqueue(entry)?;
        Ok(root)
    }

    /// Validate then dequeue. Returns error if dequeue conditions not met.
    pub fn dequeue_validated(
        &mut self,
        context: &ValidationContext,
    ) -> Result<(QueueEntry, DequeueProof), ProgramError> {
        // Validate dequeue program if present.
        if let Some(ref dequeue_prog) = self.dequeue_program {
            validate_dequeue_constraints(dequeue_prog, context)?;
        }
        let (entry, proof) = self.queue.dequeue()?;
        Ok((entry, proof))
    }

    /// Check if an enqueue WOULD be valid (dry run, no mutation).
    pub fn validate_enqueue(
        &self,
        entry: &QueueEntry,
        context: &ValidationContext,
    ) -> Result<(), ProgramError> {
        validate_enqueue_constraints(
            &self.enqueue_program,
            entry,
            context,
            self.next_sequence,
        )
    }

    /// Get the program VK hash (for composition with Effect VM).
    pub fn vk_hash(&self) -> [u8; 32] {
        self.program_vk_hash
    }

    /// Get the current queue root.
    pub fn root(&self) -> [u8; 32] {
        self.queue.root()
    }

    /// Number of pending entries.
    pub fn len(&self) -> usize {
        self.queue.len()
    }

    /// Whether the queue is empty.
    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    /// Queue name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Queue owner.
    pub fn owner(&self) -> [u8; 32] {
        self.owner
    }
}

// ============================================================================
// QueueFactory
// ============================================================================

/// Factory that creates programmable queues with validated program constraints.
/// The factory itself has rules about what programs are allowed.
#[derive(Debug, Clone)]
pub struct QueueFactory {
    /// Maximum allowed constraints per program.
    pub max_constraints: usize,
    /// Maximum lookup table entries per table.
    pub max_lookup_entries: usize,
    /// Allowed constraint types (whitelist).
    pub allowed_constraints: Vec<ConstraintKind>,
    /// Factory VK hash (content-addresses the factory's rules).
    pub factory_vk: [u8; 32],
}

impl QueueFactory {
    /// Create a queue through this factory, validating the program against factory rules.
    pub fn create_queue(
        &self,
        name: String,
        owner: [u8; 32],
        program: QueueProgram,
        capacity: usize,
    ) -> Result<ProgrammableQueue, FactoryError> {
        self.validate_program(&program)?;
        Ok(ProgrammableQueue::new(name, owner, program, None, capacity))
    }

    /// Validate a program against factory rules.
    pub fn validate_program(&self, program: &QueueProgram) -> Result<(), FactoryError> {
        // Check constraint count.
        if program.constraints.is_empty() {
            return Err(FactoryError::EmptyProgram);
        }
        if program.constraints.len() > self.max_constraints {
            return Err(FactoryError::TooManyConstraints {
                count: program.constraints.len(),
                max: self.max_constraints,
            });
        }

        // Check allowed constraint types.
        for constraint in &program.constraints {
            let kind = constraint.kind();
            if !self.allowed_constraints.contains(&kind) {
                return Err(FactoryError::DisallowedConstraint { kind });
            }
        }

        // Check lookup table sizes.
        for table in &program.lookup_tables {
            if table.entries.len() > self.max_lookup_entries {
                return Err(FactoryError::LookupTableTooLarge {
                    table: table.name.clone(),
                    entries: table.entries.len(),
                    max: self.max_lookup_entries,
                });
            }
        }

        Ok(())
    }
}

// ============================================================================
// Predefined programs
// ============================================================================

/// Predefined queue programs for common patterns.
pub mod programs {
    use super::*;

    /// Open queue: anyone can enqueue (just deposit check).
    pub fn open(min_deposit: u64) -> QueueProgram {
        QueueProgram {
            name: "open".to_string(),
            constraints: vec![QueueConstraint::MinDeposit { amount: min_deposit }],
            lookup_tables: Vec::new(),
        }
    }

    /// ACL queue: only authorized senders.
    pub fn acl(authorized: &[[u8; 32]], min_deposit: u64) -> QueueProgram {
        // Compute the authorized set root (Merkle root of authorized senders).
        let root = compute_authorized_set_root(authorized);
        QueueProgram {
            name: "acl".to_string(),
            constraints: vec![
                QueueConstraint::SenderAuthorized { authorized_set_root: root },
                QueueConstraint::MinDeposit { amount: min_deposit },
            ],
            lookup_tables: vec![QueueLookupTable {
                name: "authorized_senders".to_string(),
                entries: authorized.to_vec(),
            }],
        }
    }

    /// Rate-limited: max N per sender per epoch.
    pub fn rate_limited(max_per_epoch: u32, epoch_duration: u64, min_deposit: u64) -> QueueProgram {
        QueueProgram {
            name: "rate_limited".to_string(),
            constraints: vec![
                QueueConstraint::RateLimit { max_per_epoch, epoch_duration },
                QueueConstraint::MinDeposit { amount: min_deposit },
            ],
            lookup_tables: Vec::new(),
        }
    }

    /// Timed: only accepts between height A and height B.
    pub fn timed(not_before: u64, not_after: u64) -> QueueProgram {
        QueueProgram {
            name: "timed".to_string(),
            constraints: vec![QueueConstraint::TemporalGate {
                not_before: Some(not_before),
                not_after: Some(not_after),
            }],
            lookup_tables: Vec::new(),
        }
    }

    /// Secret-gated dequeue: requires preimage of commitment.
    pub fn secret_gated(commitment: [u8; 32]) -> QueueProgram {
        QueueProgram {
            name: "secret_gated".to_string(),
            constraints: vec![QueueConstraint::PreimageGate { commitment }],
            lookup_tables: Vec::new(),
        }
    }

    /// Typed: only messages matching a content prefix.
    pub fn typed(prefix: &[u8], min_deposit: u64) -> QueueProgram {
        QueueProgram {
            name: "typed".to_string(),
            constraints: vec![
                QueueConstraint::ContentPattern { required_prefix: prefix.to_vec() },
                QueueConstraint::MinDeposit { amount: min_deposit },
            ],
            lookup_tables: Vec::new(),
        }
    }
}

// ============================================================================
// Constraint validation logic
// ============================================================================

/// Validate all enqueue constraints for a program.
fn validate_enqueue_constraints(
    program: &QueueProgram,
    entry: &QueueEntry,
    context: &ValidationContext,
    next_sequence: u64,
) -> Result<(), ProgramError> {
    for constraint in &program.constraints {
        match constraint {
            QueueConstraint::SenderAuthorized { authorized_set_root: _ } => {
                // Check sender is in lookup table.
                let authorized = program
                    .lookup_tables
                    .iter()
                    .any(|t| t.entries.contains(&context.sender));
                if !authorized {
                    return Err(ProgramError::ConstraintViolation {
                        constraint: "SenderAuthorized".to_string(),
                        detail: "sender not in authorized set".to_string(),
                    });
                }
            }
            QueueConstraint::ContentPattern { required_prefix } => {
                // The content hash must start with the required prefix.
                // In practice, the raw message bytes are checked against the prefix
                // before hashing. Here we check the hash prefix as a proxy for
                // typed messages where the content_hash incorporates the prefix.
                if entry.content_hash.len() < required_prefix.len() {
                    return Err(ProgramError::ConstraintViolation {
                        constraint: "ContentPattern".to_string(),
                        detail: "content hash shorter than required prefix".to_string(),
                    });
                }
                if &entry.content_hash[..required_prefix.len()] != required_prefix.as_slice() {
                    return Err(ProgramError::ConstraintViolation {
                        constraint: "ContentPattern".to_string(),
                        detail: format!(
                            "content hash prefix does not match required pattern (expected {:?})",
                            required_prefix
                        ),
                    });
                }
            }
            QueueConstraint::MinDeposit { amount } => {
                if entry.deposit < *amount {
                    return Err(ProgramError::ConstraintViolation {
                        constraint: "MinDeposit".to_string(),
                        detail: format!(
                            "deposit {} below minimum {}",
                            entry.deposit, amount
                        ),
                    });
                }
            }
            QueueConstraint::MaxSize { bytes } => {
                if entry.size > *bytes {
                    return Err(ProgramError::ConstraintViolation {
                        constraint: "MaxSize".to_string(),
                        detail: format!("size {} exceeds max {}", entry.size, bytes),
                    });
                }
            }
            QueueConstraint::RateLimit { max_per_epoch, epoch_duration: _ } => {
                if context.sender_epoch_count >= *max_per_epoch {
                    return Err(ProgramError::ConstraintViolation {
                        constraint: "RateLimit".to_string(),
                        detail: format!(
                            "sender has {} enqueues this epoch, max is {}",
                            context.sender_epoch_count, max_per_epoch
                        ),
                    });
                }
            }
            QueueConstraint::MonotonicSequence => {
                if let Some(seq) = context.sequence {
                    if seq != next_sequence {
                        return Err(ProgramError::ConstraintViolation {
                            constraint: "MonotonicSequence".to_string(),
                            detail: format!(
                                "expected sequence {}, got {}",
                                next_sequence, seq
                            ),
                        });
                    }
                } else {
                    return Err(ProgramError::ConstraintViolation {
                        constraint: "MonotonicSequence".to_string(),
                        detail: "no sequence number provided".to_string(),
                    });
                }
            }
            QueueConstraint::TemporalGate { not_before, not_after } => {
                if let Some(nb) = not_before {
                    if context.current_height < *nb {
                        return Err(ProgramError::ConstraintViolation {
                            constraint: "TemporalGate".to_string(),
                            detail: format!(
                                "current height {} before not_before {}",
                                context.current_height, nb
                            ),
                        });
                    }
                }
                if let Some(na) = not_after {
                    if context.current_height > *na {
                        return Err(ProgramError::ConstraintViolation {
                            constraint: "TemporalGate".to_string(),
                            detail: format!(
                                "current height {} after not_after {}",
                                context.current_height, na
                            ),
                        });
                    }
                }
            }
            QueueConstraint::PreimageGate { .. } => {
                // PreimageGate is a dequeue constraint; skip during enqueue validation.
            }
            QueueConstraint::Custom { expr: _, description } => {
                // Custom constraints require external evaluation.
                // For now, they always pass during local validation.
                // In-circuit, the proof must satisfy the constraint expression.
                let _ = description;
            }
        }
    }
    Ok(())
}

/// Validate dequeue constraints for a program.
fn validate_dequeue_constraints(
    program: &QueueProgram,
    context: &ValidationContext,
) -> Result<(), ProgramError> {
    for constraint in &program.constraints {
        match constraint {
            QueueConstraint::PreimageGate { commitment } => {
                // Dequeue requires knowledge of the preimage.
                let preimage = context.preimage.ok_or_else(|| ProgramError::DequeueRejected {
                    reason: "no preimage provided for secret-gated dequeue".to_string(),
                })?;
                // Verify: blake3(preimage) == commitment.
                let hash = *blake3::hash(&preimage).as_bytes();
                if hash != *commitment {
                    return Err(ProgramError::DequeueRejected {
                        reason: "preimage does not match commitment".to_string(),
                    });
                }
            }
            QueueConstraint::TemporalGate { not_before, not_after } => {
                if let Some(nb) = not_before {
                    if context.current_height < *nb {
                        return Err(ProgramError::DequeueRejected {
                            reason: format!(
                                "current height {} before not_before {}",
                                context.current_height, nb
                            ),
                        });
                    }
                }
                if let Some(na) = not_after {
                    if context.current_height > *na {
                        return Err(ProgramError::DequeueRejected {
                            reason: format!(
                                "current height {} after not_after {}",
                                context.current_height, na
                            ),
                        });
                    }
                }
            }
            // Other constraints are enqueue-time; skip during dequeue.
            _ => {}
        }
    }
    Ok(())
}

// ============================================================================
// Helpers
// ============================================================================

/// Compute the VK hash for a queue program (content-addressed identity).
fn compute_vk_hash(enqueue: &QueueProgram, dequeue: Option<&QueueProgram>) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"queue_program_vk_v1");
    hasher.update(enqueue.name.as_bytes());

    // Hash each constraint type and parameters.
    for constraint in &enqueue.constraints {
        hash_constraint(&mut hasher, constraint);
    }

    // Hash lookup tables.
    for table in &enqueue.lookup_tables {
        hasher.update(table.name.as_bytes());
        for entry in &table.entries {
            hasher.update(entry);
        }
    }

    // Hash dequeue program if present.
    if let Some(deq) = dequeue {
        hasher.update(b"dequeue:");
        hasher.update(deq.name.as_bytes());
        for constraint in &deq.constraints {
            hash_constraint(&mut hasher, constraint);
        }
    }

    *hasher.finalize().as_bytes()
}

/// Hash a single constraint into a hasher.
fn hash_constraint(hasher: &mut blake3::Hasher, constraint: &QueueConstraint) {
    match constraint {
        QueueConstraint::SenderAuthorized { authorized_set_root } => {
            hasher.update(b"sender_authorized");
            hasher.update(authorized_set_root);
        }
        QueueConstraint::ContentPattern { required_prefix } => {
            hasher.update(b"content_pattern");
            hasher.update(required_prefix);
        }
        QueueConstraint::MinDeposit { amount } => {
            hasher.update(b"min_deposit");
            hasher.update(&amount.to_le_bytes());
        }
        QueueConstraint::MaxSize { bytes } => {
            hasher.update(b"max_size");
            hasher.update(&(*bytes as u64).to_le_bytes());
        }
        QueueConstraint::RateLimit { max_per_epoch, epoch_duration } => {
            hasher.update(b"rate_limit");
            hasher.update(&max_per_epoch.to_le_bytes());
            hasher.update(&epoch_duration.to_le_bytes());
        }
        QueueConstraint::MonotonicSequence => {
            hasher.update(b"monotonic_sequence");
        }
        QueueConstraint::TemporalGate { not_before, not_after } => {
            hasher.update(b"temporal_gate");
            hasher.update(&not_before.unwrap_or(0).to_le_bytes());
            hasher.update(&not_after.unwrap_or(u64::MAX).to_le_bytes());
        }
        QueueConstraint::PreimageGate { commitment } => {
            hasher.update(b"preimage_gate");
            hasher.update(commitment);
        }
        QueueConstraint::Custom { expr, description } => {
            hasher.update(b"custom");
            hasher.update(expr.as_bytes());
            hasher.update(description.as_bytes());
        }
    }
}

/// Compute a Merkle root over a set of authorized sender keys.
fn compute_authorized_set_root(authorized: &[[u8; 32]]) -> [u8; 32] {
    if authorized.is_empty() {
        return *blake3::hash(b"empty_authorized_set").as_bytes();
    }
    if authorized.len() == 1 {
        return *blake3::hash(&authorized[0]).as_bytes();
    }

    let mut leaves: Vec<[u8; 32]> = authorized
        .iter()
        .map(|k| *blake3::hash(k).as_bytes())
        .collect();

    // Pad to next power of 2.
    let next_pow2 = leaves.len().next_power_of_two();
    leaves.resize(next_pow2, [0u8; 32]);

    // Iteratively hash pairs.
    while leaves.len() > 1 {
        let mut next_layer = Vec::with_capacity(leaves.len() / 2);
        for pair in leaves.chunks(2) {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&pair[0]);
            hasher.update(&pair[1]);
            next_layer.push(*hasher.finalize().as_bytes());
        }
        leaves = next_layer;
    }

    leaves[0]
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_entry(content: &[u8], sender: [u8; 32], deposit: u64, size: usize) -> QueueEntry {
        QueueEntry {
            content_hash: *blake3::hash(content).as_bytes(),
            sender,
            deposit,
            enqueued_at: 100,
            size,
        }
    }

    fn make_entry_with_prefix(prefix: &[u8], sender: [u8; 32], deposit: u64) -> QueueEntry {
        // Create an entry whose content_hash starts with the given prefix.
        let mut content_hash = [0u8; 32];
        content_hash[..prefix.len()].copy_from_slice(prefix);
        QueueEntry {
            content_hash,
            sender,
            deposit,
            enqueued_at: 100,
            size: 64,
        }
    }

    fn default_context(sender: [u8; 32]) -> ValidationContext {
        ValidationContext {
            sender,
            current_height: 100,
            current_epoch: 10,
            sender_epoch_count: 0,
            preimage: None,
            sequence: None,
        }
    }

    // --- Test 1: Open program — any message accepted with valid deposit ---
    #[test]
    fn open_program_accepts_valid_deposit() {
        let program = programs::open(100);
        let mut queue = ProgrammableQueue::new(
            "open_queue".to_string(),
            [0x01; 32],
            program,
            None,
            10,
        );

        let entry = make_entry(b"hello", [0xAA; 32], 200, 32);
        let ctx = default_context([0xAA; 32]);

        let result = queue.enqueue_validated(entry, &ctx);
        assert!(result.is_ok());
        assert_eq!(queue.len(), 1);
    }

    #[test]
    fn open_program_rejects_insufficient_deposit() {
        let program = programs::open(100);
        let mut queue = ProgrammableQueue::new(
            "open_queue".to_string(),
            [0x01; 32],
            program,
            None,
            10,
        );

        let entry = make_entry(b"hello", [0xAA; 32], 50, 32); // deposit < 100
        let ctx = default_context([0xAA; 32]);

        let result = queue.enqueue_validated(entry, &ctx);
        assert!(matches!(result, Err(ProgramError::ConstraintViolation { .. })));
        assert_eq!(queue.len(), 0);
    }

    // --- Test 2: ACL program — authorized sender accepted ---
    #[test]
    fn acl_program_authorized_sender_accepted() {
        let authorized = [[0xAA; 32], [0xBB; 32], [0xCC; 32]];
        let program = programs::acl(&authorized, 50);
        let mut queue = ProgrammableQueue::new(
            "acl_queue".to_string(),
            [0x01; 32],
            program,
            None,
            10,
        );

        let entry = make_entry(b"message", [0xBB; 32], 100, 32);
        let ctx = default_context([0xBB; 32]);

        let result = queue.enqueue_validated(entry, &ctx);
        assert!(result.is_ok());
    }

    // --- Test 3: ACL program — unauthorized sender rejected ---
    #[test]
    fn acl_program_unauthorized_sender_rejected() {
        let authorized = [[0xAA; 32], [0xBB; 32]];
        let program = programs::acl(&authorized, 50);
        let mut queue = ProgrammableQueue::new(
            "acl_queue".to_string(),
            [0x01; 32],
            program,
            None,
            10,
        );

        let entry = make_entry(b"message", [0xFF; 32], 100, 32);
        let ctx = default_context([0xFF; 32]); // Not in authorized set

        let result = queue.enqueue_validated(entry, &ctx);
        assert!(matches!(result, Err(ProgramError::ConstraintViolation { .. })));
    }

    // --- Test 4: ACL program — sender not in lookup table → rejected ---
    #[test]
    fn acl_program_sender_not_in_lookup_table_rejected() {
        let authorized = [[0x11; 32], [0x22; 32], [0x33; 32]];
        let program = programs::acl(&authorized, 50);
        let mut queue = ProgrammableQueue::new(
            "acl_queue".to_string(),
            [0x01; 32],
            program,
            None,
            10,
        );

        // A sender that is close to but not in the set.
        let mut almost = [0x11; 32];
        almost[31] = 0xFF;
        let entry = make_entry(b"msg", almost, 100, 32);
        let ctx = default_context(almost);

        let result = queue.enqueue_validated(entry, &ctx);
        assert!(matches!(result, Err(ProgramError::ConstraintViolation { .. })));
    }

    // --- Test 5: Rate limit — within limit accepted, over limit rejected ---
    #[test]
    fn rate_limit_within_accepted_over_rejected() {
        let program = programs::rate_limited(3, 100, 50);
        let mut queue = ProgrammableQueue::new(
            "rate_queue".to_string(),
            [0x01; 32],
            program,
            None,
            10,
        );

        let sender = [0xAA; 32];

        // Within limit (count = 2, max = 3).
        let entry = make_entry(b"msg1", sender, 100, 32);
        let ctx = ValidationContext {
            sender,
            current_height: 100,
            current_epoch: 10,
            sender_epoch_count: 2,
            preimage: None,
            sequence: None,
        };
        assert!(queue.enqueue_validated(entry, &ctx).is_ok());

        // Over limit (count = 3, max = 3).
        let entry2 = make_entry(b"msg2", sender, 100, 32);
        let ctx_over = ValidationContext {
            sender,
            current_height: 100,
            current_epoch: 10,
            sender_epoch_count: 3,
            preimage: None,
            sequence: None,
        };
        let result = queue.enqueue_validated(entry2, &ctx_over);
        assert!(matches!(result, Err(ProgramError::ConstraintViolation { .. })));
    }

    // --- Test 6: Rate limit — new epoch resets count ---
    #[test]
    fn rate_limit_new_epoch_resets() {
        let program = programs::rate_limited(2, 100, 50);
        let mut queue = ProgrammableQueue::new(
            "rate_queue".to_string(),
            [0x01; 32],
            program,
            None,
            10,
        );

        let sender = [0xAA; 32];

        // Epoch 10, at the limit.
        let entry = make_entry(b"msg_epoch10", sender, 100, 32);
        let ctx_at_limit = ValidationContext {
            sender,
            current_height: 100,
            current_epoch: 10,
            sender_epoch_count: 2, // at max
            preimage: None,
            sequence: None,
        };
        assert!(queue.enqueue_validated(entry, &ctx_at_limit).is_err());

        // New epoch 11, count reset to 0.
        let entry2 = make_entry(b"msg_epoch11", sender, 100, 32);
        let ctx_new_epoch = ValidationContext {
            sender,
            current_height: 200,
            current_epoch: 11,
            sender_epoch_count: 0, // reset
            preimage: None,
            sequence: None,
        };
        assert!(queue.enqueue_validated(entry2, &ctx_new_epoch).is_ok());
    }

    // --- Test 7: Temporal gate — before not_before rejected, after accepted ---
    #[test]
    fn temporal_gate_before_not_before_rejected() {
        let program = programs::timed(50, 200);
        let mut queue = ProgrammableQueue::new(
            "timed_queue".to_string(),
            [0x01; 32],
            program,
            None,
            10,
        );

        let sender = [0xAA; 32];
        let entry = make_entry(b"too_early", sender, 100, 32);

        // Before not_before (height 30 < 50).
        let ctx_early = ValidationContext {
            sender,
            current_height: 30,
            current_epoch: 1,
            sender_epoch_count: 0,
            preimage: None,
            sequence: None,
        };
        assert!(queue.enqueue_validated(entry.clone(), &ctx_early).is_err());

        // After not_before (height 60 >= 50).
        let ctx_ok = ValidationContext {
            sender,
            current_height: 60,
            current_epoch: 2,
            sender_epoch_count: 0,
            preimage: None,
            sequence: None,
        };
        assert!(queue.enqueue_validated(entry, &ctx_ok).is_ok());
    }

    // --- Test 8: Temporal gate — after not_after rejected ---
    #[test]
    fn temporal_gate_after_not_after_rejected() {
        let program = programs::timed(50, 200);
        let mut queue = ProgrammableQueue::new(
            "timed_queue".to_string(),
            [0x01; 32],
            program,
            None,
            10,
        );

        let sender = [0xAA; 32];
        let entry = make_entry(b"too_late", sender, 100, 32);

        // After not_after (height 250 > 200).
        let ctx_late = ValidationContext {
            sender,
            current_height: 250,
            current_epoch: 25,
            sender_epoch_count: 0,
            preimage: None,
            sequence: None,
        };
        let result = queue.enqueue_validated(entry, &ctx_late);
        assert!(matches!(result, Err(ProgramError::ConstraintViolation { .. })));
    }

    // --- Test 9: Monotonic sequence — out-of-order rejected ---
    #[test]
    fn monotonic_sequence_out_of_order_rejected() {
        let program = QueueProgram {
            name: "monotonic".to_string(),
            constraints: vec![QueueConstraint::MonotonicSequence],
            lookup_tables: Vec::new(),
        };
        let mut queue = ProgrammableQueue::new(
            "seq_queue".to_string(),
            [0x01; 32],
            program,
            None,
            10,
        );

        let sender = [0xAA; 32];

        // First message: sequence 0.
        let entry0 = make_entry(b"msg0", sender, 100, 32);
        let ctx0 = ValidationContext {
            sender,
            current_height: 100,
            current_epoch: 10,
            sender_epoch_count: 0,
            preimage: None,
            sequence: Some(0),
        };
        assert!(queue.enqueue_validated(entry0, &ctx0).is_ok());

        // Second message: sequence 1 (correct).
        let entry1 = make_entry(b"msg1", sender, 100, 32);
        let ctx1 = ValidationContext {
            sender,
            current_height: 101,
            current_epoch: 10,
            sender_epoch_count: 1,
            preimage: None,
            sequence: Some(1),
        };
        assert!(queue.enqueue_validated(entry1, &ctx1).is_ok());

        // Third message: sequence 5 (out-of-order, should be 2).
        let entry_bad = make_entry(b"msg_bad", sender, 100, 32);
        let ctx_bad = ValidationContext {
            sender,
            current_height: 102,
            current_epoch: 10,
            sender_epoch_count: 2,
            preimage: None,
            sequence: Some(5),
        };
        let result = queue.enqueue_validated(entry_bad, &ctx_bad);
        assert!(matches!(result, Err(ProgramError::ConstraintViolation { .. })));
    }

    // --- Test 10: Secret-gated dequeue — wrong preimage rejected, correct accepted ---
    #[test]
    fn secret_gated_dequeue_preimage_check() {
        let secret = [0x42; 32];
        let commitment = *blake3::hash(&secret).as_bytes();

        let enqueue_prog = programs::open(50);
        let dequeue_prog = programs::secret_gated(commitment);

        let mut queue = ProgrammableQueue::new(
            "secret_queue".to_string(),
            [0x01; 32],
            enqueue_prog,
            Some(dequeue_prog),
            10,
        );

        // Enqueue something.
        let entry = make_entry(b"secret_msg", [0xAA; 32], 100, 32);
        let ctx = default_context([0xAA; 32]);
        queue.enqueue_validated(entry, &ctx).unwrap();

        // Dequeue with wrong preimage.
        let wrong_ctx = ValidationContext {
            sender: [0xBB; 32],
            current_height: 100,
            current_epoch: 10,
            sender_epoch_count: 0,
            preimage: Some([0xFF; 32]), // wrong!
            sequence: None,
        };
        let result = queue.dequeue_validated(&wrong_ctx);
        assert!(matches!(result, Err(ProgramError::DequeueRejected { .. })));

        // Dequeue with correct preimage.
        let correct_ctx = ValidationContext {
            sender: [0xBB; 32],
            current_height: 100,
            current_epoch: 10,
            sender_epoch_count: 0,
            preimage: Some(secret),
            sequence: None,
        };
        let result = queue.dequeue_validated(&correct_ctx);
        assert!(result.is_ok());
    }

    // --- Test 11: Content pattern — matching prefix accepted, non-matching rejected ---
    #[test]
    fn content_pattern_prefix_matching() {
        let prefix = vec![0xDE, 0xAD];
        let program = programs::typed(&prefix, 50);
        let mut queue = ProgrammableQueue::new(
            "typed_queue".to_string(),
            [0x01; 32],
            program,
            None,
            10,
        );

        let sender = [0xAA; 32];

        // Entry with matching prefix in content_hash.
        let matching_entry = make_entry_with_prefix(&[0xDE, 0xAD], sender, 100);
        let ctx = default_context(sender);
        assert!(queue.enqueue_validated(matching_entry, &ctx).is_ok());

        // Entry with non-matching prefix.
        let non_matching = make_entry_with_prefix(&[0xCA, 0xFE], sender, 100);
        let result = queue.enqueue_validated(non_matching, &ctx);
        assert!(matches!(result, Err(ProgramError::ConstraintViolation { .. })));
    }

    // --- Test 12: Factory — valid program accepted, oversized rejected ---
    #[test]
    fn factory_validates_program_size() {
        let factory = QueueFactory {
            max_constraints: 3,
            max_lookup_entries: 10,
            allowed_constraints: vec![
                ConstraintKind::MinDeposit,
                ConstraintKind::MaxSize,
                ConstraintKind::RateLimit,
                ConstraintKind::SenderAuthorized,
            ],
            factory_vk: [0xFF; 32],
        };

        // Valid program (2 constraints, within limit).
        let valid_program = programs::open(100);
        assert!(factory.validate_program(&valid_program).is_ok());

        // Oversized program (4 constraints, exceeds limit of 3).
        let oversized = QueueProgram {
            name: "too_many".to_string(),
            constraints: vec![
                QueueConstraint::MinDeposit { amount: 10 },
                QueueConstraint::MaxSize { bytes: 1024 },
                QueueConstraint::RateLimit { max_per_epoch: 5, epoch_duration: 100 },
                QueueConstraint::MinDeposit { amount: 20 },
            ],
            lookup_tables: Vec::new(),
        };
        let result = factory.validate_program(&oversized);
        assert!(matches!(result, Err(FactoryError::TooManyConstraints { .. })));
    }

    // --- Test 13: Factory — disallowed constraint type rejected ---
    #[test]
    fn factory_rejects_disallowed_constraint() {
        let factory = QueueFactory {
            max_constraints: 10,
            max_lookup_entries: 100,
            allowed_constraints: vec![
                ConstraintKind::MinDeposit,
                ConstraintKind::MaxSize,
            ],
            factory_vk: [0xFF; 32],
        };

        // Program with Custom constraint (not in allowed list).
        let program = QueueProgram {
            name: "custom_prog".to_string(),
            constraints: vec![
                QueueConstraint::MinDeposit { amount: 50 },
                QueueConstraint::Custom {
                    expr: "x > 0".to_string(),
                    description: "positive values only".to_string(),
                },
            ],
            lookup_tables: Vec::new(),
        };

        let result = factory.validate_program(&program);
        assert_eq!(
            result,
            Err(FactoryError::DisallowedConstraint { kind: ConstraintKind::Custom })
        );
    }

    // --- Test 14: VK hash is deterministic (same program → same hash) ---
    #[test]
    fn vk_hash_deterministic() {
        let program1 = programs::acl(&[[0xAA; 32], [0xBB; 32]], 100);
        let program2 = programs::acl(&[[0xAA; 32], [0xBB; 32]], 100);

        let queue1 = ProgrammableQueue::new(
            "q1".to_string(),
            [0x01; 32],
            program1,
            None,
            10,
        );
        let queue2 = ProgrammableQueue::new(
            "q2".to_string(),
            [0x01; 32],
            program2,
            None,
            10,
        );

        // Same program → same VK hash (regardless of queue name).
        assert_eq!(queue1.vk_hash(), queue2.vk_hash());

        // Different program → different VK hash.
        let program3 = programs::open(200);
        let queue3 = ProgrammableQueue::new(
            "q3".to_string(),
            [0x01; 32],
            program3,
            None,
            10,
        );
        assert_ne!(queue1.vk_hash(), queue3.vk_hash());
    }

    // --- Test 15: Predefined programs work correctly (factory create + enqueue) ---
    #[test]
    fn predefined_programs_end_to_end() {
        let factory = QueueFactory {
            max_constraints: 10,
            max_lookup_entries: 100,
            allowed_constraints: vec![
                ConstraintKind::MinDeposit,
                ConstraintKind::MaxSize,
                ConstraintKind::RateLimit,
                ConstraintKind::SenderAuthorized,
                ConstraintKind::TemporalGate,
                ConstraintKind::ContentPattern,
            ],
            factory_vk: [0xFF; 32],
        };

        // Create an open queue via factory.
        let mut queue = factory
            .create_queue("test_open".to_string(), [0x01; 32], programs::open(50), 5)
            .unwrap();

        // Enqueue with valid deposit.
        let entry = make_entry(b"hello", [0xAA; 32], 100, 32);
        let ctx = default_context([0xAA; 32]);
        assert!(queue.enqueue_validated(entry, &ctx).is_ok());

        // Create a rate-limited queue via factory.
        let mut rl_queue = factory
            .create_queue(
                "test_rl".to_string(),
                [0x02; 32],
                programs::rate_limited(1, 100, 50),
                5,
            )
            .unwrap();

        // First enqueue succeeds.
        let entry1 = make_entry(b"first", [0xBB; 32], 100, 32);
        let ctx1 = ValidationContext {
            sender: [0xBB; 32],
            current_height: 100,
            current_epoch: 10,
            sender_epoch_count: 0,
            preimage: None,
            sequence: None,
        };
        assert!(rl_queue.enqueue_validated(entry1, &ctx1).is_ok());

        // Second enqueue from same sender in same epoch rejected.
        let entry2 = make_entry(b"second", [0xBB; 32], 100, 32);
        let ctx2 = ValidationContext {
            sender: [0xBB; 32],
            current_height: 101,
            current_epoch: 10,
            sender_epoch_count: 1,
            preimage: None,
            sequence: None,
        };
        assert!(rl_queue.enqueue_validated(entry2, &ctx2).is_err());
    }

    // --- Test 16: Secret-gated dequeue — no preimage provided → rejected ---
    #[test]
    fn secret_gated_no_preimage_rejected() {
        let secret = [0x99; 32];
        let commitment = *blake3::hash(&secret).as_bytes();

        let enqueue_prog = programs::open(50);
        let dequeue_prog = programs::secret_gated(commitment);

        let mut queue = ProgrammableQueue::new(
            "secret_queue".to_string(),
            [0x01; 32],
            enqueue_prog,
            Some(dequeue_prog),
            10,
        );

        // Enqueue.
        let entry = make_entry(b"gated_msg", [0xAA; 32], 100, 32);
        let ctx = default_context([0xAA; 32]);
        queue.enqueue_validated(entry, &ctx).unwrap();

        // Dequeue without providing preimage.
        let no_preimage_ctx = ValidationContext {
            sender: [0xBB; 32],
            current_height: 100,
            current_epoch: 10,
            sender_epoch_count: 0,
            preimage: None,
            sequence: None,
        };
        let result = queue.dequeue_validated(&no_preimage_ctx);
        assert!(matches!(result, Err(ProgramError::DequeueRejected { .. })));
    }
}
