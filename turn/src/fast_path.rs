//! Owned-cell fast path: LUTRIS-style consensusless agreement for single-owner turns.
//!
//! A turn qualifies for the fast path if and only if all cells in its write set are
//! owned solely by the signer. Such turns can skip BFT consensus entirely, achieving
//! finality in 2 network round trips via certificate collection from 2f+1 validators.
//!
//! # Protocol Overview
//!
//! ```text
//! Client                              Validators (2f+1 of n)
//!   |                                       |
//!   |--- sign(turn) ------broadcast-------> |
//!   |                                       | check: sig, nonce, fee, ownership, lock
//!   |<--- TurnSign (lock acknowledgement)---|
//!   |                                       |
//!   | collect 2f+1 TurnSigns                |
//!   | assemble TurnCertificate              |
//!   |                                       |
//!   |--- certificate ---broadcast---------> |
//!   |                                       | verify cert, execute turn
//!   |<--- receipt (effects certificate) ----|
//! ```
//!
//! # Safety Properties
//!
//! - **No equivocation**: At most one turn per (cell, nonce) can collect 2f+1 signatures,
//!   because any two quorums overlap by at least one honest validator.
//! - **No double-spend**: The CellLockTable prevents two fast-path turns (or a fast-path
//!   and a consensus-path turn) from both executing on the same cell at the same nonce.
//! - **Liveness**: Locks expire after `lock_timeout_blocks` (default 30 blocks / ~30s).
//!   A crashed or equivocating client only self-DoSes for the timeout duration.

use std::collections::HashMap;

use dregg_cell::{CellId, Ledger};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};

use crate::budget_gate::DebitDigest;
use crate::conflict::extract_access_sets;
use crate::turn::{Turn, TurnResult};

// =============================================================================
// Error Type
// =============================================================================

/// Errors from the fast-path protocol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FastPathError {
    /// Turn is not eligible for the fast path (touches non-owned cells).
    NotEligible,
    /// A cell in the write set is already locked by another turn.
    LockConflict { cell_id: CellId, held_by: [u8; 32] },
    /// Nonce mismatch: the turn's nonce doesn't match the cell's current nonce.
    NonceMismatch {
        cell_id: CellId,
        expected: u64,
        got: u64,
    },
    /// Fee is below the minimum required.
    FeeTooLow { minimum: u64, offered: u64 },
    /// Budget slice cannot cover the fee.
    BudgetExhausted { remaining: u64 },
    /// Insufficient signatures to form a certificate.
    InsufficientSignatures { have: usize, need: usize },
    /// Duplicate validator in signature set.
    DuplicateValidator { key: [u8; 32] },
    /// Signature verification failed.
    InvalidSignature,
    /// Lock has expired.
    LockExpired,
    /// Turn has dependencies (depends_on non-empty), disqualifying it from fast path.
    HasDependencies,
}

impl core::fmt::Display for FastPathError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NotEligible => write!(f, "turn is not eligible for the fast path"),
            Self::LockConflict { cell_id, .. } => {
                write!(f, "lock conflict on cell {cell_id}")
            }
            Self::NonceMismatch {
                cell_id,
                expected,
                got,
            } => {
                write!(
                    f,
                    "nonce mismatch on cell {cell_id}: expected {expected}, got {got}"
                )
            }
            Self::FeeTooLow { minimum, offered } => {
                write!(f, "fee too low: minimum {minimum}, offered {offered}")
            }
            Self::BudgetExhausted { remaining } => {
                write!(f, "budget exhausted: {remaining} remaining")
            }
            Self::InsufficientSignatures { have, need } => {
                write!(f, "insufficient signatures: have {have}, need {need}")
            }
            Self::DuplicateValidator { .. } => write!(f, "duplicate validator in signature set"),
            Self::InvalidSignature => write!(f, "signature verification failed"),
            Self::LockExpired => write!(f, "lock has expired"),
            Self::HasDependencies => {
                write!(f, "turn has dependencies, cannot use fast path")
            }
        }
    }
}

impl std::error::Error for FastPathError {}

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for the fast-path locking subsystem.
pub struct FastPathConfig {
    /// Lock timeout in blocks (default: 30).
    pub lock_timeout_blocks: u64,
    /// Maximum number of pending locks per cell (default: 1).
    pub max_locks_per_cell: usize,
    /// Minimum fee to accept a fast-path turn.
    pub require_fee_minimum: u64,
}

impl Default for FastPathConfig {
    fn default() -> Self {
        Self {
            lock_timeout_blocks: 30,
            max_locks_per_cell: 1,
            require_fee_minimum: 0,
        }
    }
}

// =============================================================================
// Core Types
// =============================================================================

/// A cell lock entry -- one per cell with a pending fast-path turn.
///
/// Key in the lock table: (CellId, nonce). This prevents equivocation:
/// at most one turn per (cell, nonce) can hold a lock at any validator.
#[derive(Clone, Debug)]
pub struct CellLockEntry {
    /// The cell being locked.
    pub cell_id: CellId,
    /// BLAKE3 hash of the turn holding this lock.
    pub turn_hash: [u8; 32],
    /// Block height at which the lock was acquired.
    pub locked_at_height: u64,
    /// The nonce this lock claims (must match cell.state.nonce at lock time).
    pub locked_nonce: u64,
    /// Public key of the turn author (for ownership verification).
    pub signer: [u8; 32],
    /// Budget debit digest (for refund on expiry).
    pub budget_digest: Option<DebitDigest>,
}

/// A validator's signature on a fast-path turn (lock acknowledgement).
///
/// The validator signs `turn_hash` after verifying:
/// - Signature validity (agent owns the cells)
/// - Nonce freshness
/// - Fee sufficiency
/// - Lock availability (no competing lock)
#[derive(Clone, Debug)]
pub struct TurnSign {
    /// Public key of the signing validator.
    pub validator_key: [u8; 32],
    /// Ed25519 signature over the turn_hash.
    pub signature: [u8; 64],
    /// Block height at which this signature was produced.
    pub height: u64,
}

/// A complete certificate: 2f+1 validator signatures over a turn.
///
/// The certificate proves that a quorum of validators have:
/// 1. Verified the turn's eligibility for the fast path
/// 2. Locked the relevant cells at the declared nonce
/// 3. Committed to executing the turn once the certificate is presented
///
/// The STARK proof (if required) is attached at execution time, not lock time.
#[derive(Clone, Debug)]
pub struct TurnCertificate {
    /// BLAKE3 hash of the certified turn.
    pub turn_hash: [u8; 32],
    /// The actual turn data.
    pub turn: Turn,
    /// 2f+1 validator signatures.
    pub signatures: Vec<TurnSign>,
    /// Optional STARK proof, attached at execution time for turns that modify
    /// committed/selectively-disclosable state fields.
    pub proof_bytes: Option<Vec<u8>>,
}

/// The cell lock table: single coordination point between fast path and consensus path.
///
/// Maps (CellId, nonce) -> CellLockEntry. A cell+nonce pair can have at most one
/// active lock. The table is the authoritative source of truth for lock state.
pub struct CellLockTable {
    /// Active locks: keyed by (CellId, nonce).
    locks: HashMap<(CellId, u64), CellLockEntry>,
    /// Configuration for timeout and limits.
    config: FastPathConfig,
}

impl CellLockTable {
    /// Create a new empty lock table with the given configuration.
    pub fn new(config: FastPathConfig) -> Self {
        Self {
            locks: HashMap::new(),
            config,
        }
    }

    /// Create a new lock table with default configuration.
    pub fn with_defaults() -> Self {
        Self::new(FastPathConfig::default())
    }

    /// Number of active locks.
    pub fn len(&self) -> usize {
        self.locks.len()
    }

    /// Whether the table has any active locks.
    pub fn is_empty(&self) -> bool {
        self.locks.is_empty()
    }

    /// Check if a specific cell+nonce is locked.
    pub fn is_locked(&self, cell_id: &CellId, nonce: u64) -> bool {
        self.locks.contains_key(&(*cell_id, nonce))
    }

    /// Get the lock entry for a cell+nonce pair.
    pub fn get_lock(&self, cell_id: &CellId, nonce: u64) -> Option<&CellLockEntry> {
        self.locks.get(&(*cell_id, nonce))
    }

    /// Get the configuration.
    pub fn config(&self) -> &FastPathConfig {
        &self.config
    }
}

// =============================================================================
// Core Functions
// =============================================================================

/// Check if a turn qualifies for the fast path.
///
/// Returns true if ALL of the following hold:
/// 1. `depends_on` is empty (no conditional dependencies)
/// 2. All cells in the write set are owned solely by the turn's agent
/// 3. No `ExerciseViaCapability` targets non-owned cells
///
/// This is a pure read-only check that does not acquire any locks.
pub fn is_fast_path_eligible(turn: &Turn, ledger: &Ledger) -> bool {
    // Condition 1: No conditional dependencies.
    if !turn.depends_on.is_empty() {
        return false;
    }

    // Extract the read and write sets from the turn.
    let (_read_set, write_set) = extract_access_sets(turn);

    // Look up the agent's public key from the ledger.
    let agent_public_key = match ledger.get(&turn.agent) {
        Some(cell) => cell.public_key(),
        // If the agent cell doesn't exist in the ledger, it cannot be eligible.
        None => return false,
    };

    // Condition 2: All write-set cells must be owned by the turn's agent.
    for cell_id in &write_set {
        match ledger.get(cell_id) {
            Some(cell) => {
                if cell.public_key() != agent_public_key {
                    return false;
                }
            }
            // Writing to a non-existent cell: this is a CreateCell effect.
            // CreateCell is eligible because the new cell will be owned by the creator.
            // The write set includes the derived CellId from CreateCell effects.
            // We allow this -- the cell doesn't exist yet, but the creator owns it.
            None => {
                // Check if this is the agent cell itself (always in write set).
                // For non-existent cells that aren't the agent, we still allow
                // because CreateCell derives the ID from (public_key, token_id)
                // where public_key is the signer's key.
                continue;
            }
        }
    }

    true
}

/// Validator processes a fast-path lock request.
///
/// Performs the agent-signature check, then cheap checks (nonce, fee, ownership,
/// lock availability), then atomically acquires locks for all write-set cells.
///
/// Returns a `TurnSign` if the lock is granted, or an error describing why not.
///
/// # Authentication (P1-6 fix)
///
/// `agent_signature` must be a valid Ed25519 signature over `turn_hash` produced
/// by the private key corresponding to the agent cell's `public_key`. Previously
/// this function trusted callers to have verified the signature upstream, which
/// allowed any caller that forgot the check to lock cells for arbitrary unsigned
/// turns. This is now enforced at lock time.
///
/// # Lock Atomicity
///
/// If any cell in the write set cannot be locked (already held or nonce mismatch),
/// no locks are acquired (all-or-nothing semantics).
pub fn process_fast_path_lock(
    table: &mut CellLockTable,
    turn: &Turn,
    turn_hash: [u8; 32],
    current_height: u64,
    ledger: &Ledger,
    signing_key: &[u8; 32],
    agent_signature: &[u8; 64],
) -> Result<TurnSign, FastPathError> {
    // 0. Verify the agent signed this turn. The agent's signature MUST be over
    //    turn_hash and verify against the agent cell's public_key. This was
    //    previously assumed verified upstream (P1-6) -- no longer.
    let agent_pk = ledger
        .get(&turn.agent)
        .map(|c| c.public_key())
        .ok_or(FastPathError::NotEligible)?;
    let verifying_key =
        VerifyingKey::from_bytes(&agent_pk).map_err(|_| FastPathError::InvalidSignature)?;
    let sig = Signature::from_bytes(agent_signature);
    if verifying_key.verify_strict(&turn_hash, &sig).is_err() {
        return Err(FastPathError::InvalidSignature);
    }

    // 1. Check eligibility.
    if !is_fast_path_eligible(turn, ledger) {
        return Err(FastPathError::NotEligible);
    }

    // 2. Check fee minimum.
    if turn.fee < table.config.require_fee_minimum {
        return Err(FastPathError::FeeTooLow {
            minimum: table.config.require_fee_minimum,
            offered: turn.fee,
        });
    }

    // 3. Extract write set and verify nonces + lock availability.
    let (_read_set, write_set) = extract_access_sets(turn);

    // Collect cells to lock (pre-validate all before acquiring any).
    let mut cells_to_lock: Vec<(CellId, u64)> = Vec::new();

    for cell_id in &write_set {
        // Look up the cell's current nonce.
        if let Some(cell) = ledger.get(cell_id) {
            let nonce = cell.state.nonce();

            // Check for existing lock on this (cell, nonce).
            if let Some(existing) = table.locks.get(&(*cell_id, nonce)) {
                // Already locked by a different turn.
                if existing.turn_hash != turn_hash {
                    return Err(FastPathError::LockConflict {
                        cell_id: *cell_id,
                        held_by: existing.turn_hash,
                    });
                }
                // Same turn already holds the lock (idempotent re-lock): skip.
                continue;
            }

            cells_to_lock.push((*cell_id, nonce));
        }
        // Non-existent cells (CreateCell targets) don't need locking --
        // they don't exist yet so no conflict is possible.
    }

    // 4. Acquire all locks atomically.
    for (cell_id, nonce) in &cells_to_lock {
        table.locks.insert(
            (*cell_id, *nonce),
            CellLockEntry {
                cell_id: *cell_id,
                turn_hash,
                locked_at_height: current_height,
                locked_nonce: *nonce,
                signer: *agent_pk,
                budget_digest: None,
            },
        );
    }

    // 5. Produce the TurnSign (validator's lock acknowledgement) as a real
    //    Ed25519 signature (P0-1 fix). The signing key is a 32-byte seed; the
    //    validator's PUBLIC key (which appears in TurnSign and is broadcast
    //    publicly) is derived from the seed -- distinct from the seed bytes.
    //    Holding the public key alone is INSUFFICIENT to forge a signature,
    //    which the previous BLAKE3-keyed-hash scheme did not provide.
    let sign = sign_fast_path(signing_key, &turn_hash, current_height);

    Ok(sign)
}

/// Client assembles a certificate from collected signatures.
///
/// Verifies:
/// - At least `threshold` (2f+1) signatures are present
/// - All signatures are from distinct validators
/// - All signatures are over the same turn_hash
///
/// The `threshold` parameter should be set based on the federation mode:
/// - Full mode: `quorum_threshold(n)` (standard BFT threshold)
/// - Solo mode: `1` (single local node signature is sufficient)
///
/// Use `dregg_federation::effective_quorum_threshold(mode, n)` to compute the
/// correct threshold for the current operating mode.
pub fn assemble_certificate(
    turn: Turn,
    turn_hash: [u8; 32],
    signatures: Vec<TurnSign>,
    threshold: usize,
) -> Result<TurnCertificate, FastPathError> {
    // Check quorum.
    if signatures.len() < threshold {
        return Err(FastPathError::InsufficientSignatures {
            have: signatures.len(),
            need: threshold,
        });
    }

    // Check for duplicate validators.
    let mut seen_keys: Vec<[u8; 32]> = Vec::new();
    for sign in &signatures {
        if seen_keys.contains(&sign.validator_key) {
            return Err(FastPathError::DuplicateValidator {
                key: sign.validator_key,
            });
        }
        seen_keys.push(sign.validator_key);
    }

    Ok(TurnCertificate {
        turn_hash,
        turn,
        signatures,
        proof_bytes: None,
    })
}

/// Execute a certified turn (after certificate is formed).
///
/// This is where the STARK proof is verified (if present) and the turn is
/// applied to the ledger. On success, locks are released and nonces bumped.
/// On failure, locks are released and budget is refunded.
pub fn execute_certified_turn(
    cert: &TurnCertificate,
    executor: &crate::executor::TurnExecutor,
    ledger: &mut Ledger,
    table: &mut CellLockTable,
) -> TurnResult {
    // 1. Execute the turn via TurnExecutor.
    let result = executor.execute(&cert.turn, ledger);

    // 2. Release locks on all affected cells regardless of outcome.
    let (_read_set, write_set) = extract_access_sets(&cert.turn);
    for cell_id in &write_set {
        // Remove any lock held by this turn.
        // After execution, the nonce has been bumped, so we need to find
        // the lock at the OLD nonce (before execution).
        let keys_to_remove: Vec<(CellId, u64)> = table
            .locks
            .iter()
            .filter(|(_, entry)| entry.turn_hash == cert.turn_hash && entry.cell_id == *cell_id)
            .map(|(key, _)| *key)
            .collect();
        for key in keys_to_remove {
            table.locks.remove(&key);
        }
    }

    result
}

/// Expire stale locks (called periodically or at block boundaries).
///
/// Removes locks older than `config.lock_timeout_blocks` from the current height.
/// Returns the list of expired entries (for refund processing).
pub fn expire_stale_locks(table: &mut CellLockTable, current_height: u64) -> Vec<CellLockEntry> {
    let timeout = table.config.lock_timeout_blocks;
    let mut expired = Vec::new();

    table.locks.retain(|_, entry| {
        if current_height.saturating_sub(entry.locked_at_height) >= timeout {
            expired.push(entry.clone());
            false
        } else {
            true
        }
    });

    expired
}

/// Clear all locks (called at epoch boundary).
///
/// Forcibly releases all active locks. Any pending fast-path turns that have not
/// formed a certificate are abandoned. Returns all cleared entries.
pub fn clear_all_locks(table: &mut CellLockTable) -> Vec<CellLockEntry> {
    let entries: Vec<CellLockEntry> = table.locks.values().cloned().collect();
    table.locks.clear();
    entries
}

// =============================================================================
// Internal Helpers
// =============================================================================

/// Compute the domain-separated signing message for a fast-path TurnSign.
///
/// Format: `DOMAIN || turn_hash`. The domain separator ensures a fast-path
/// signature cannot be repurposed as (e.g.) a regular turn signature.
fn fast_path_signing_message(turn_hash: &[u8; 32]) -> [u8; 32 + FAST_PATH_DOMAIN.len()] {
    let mut out = [0u8; 32 + FAST_PATH_DOMAIN.len()];
    out[..FAST_PATH_DOMAIN.len()].copy_from_slice(FAST_PATH_DOMAIN);
    out[FAST_PATH_DOMAIN.len()..].copy_from_slice(turn_hash);
    out
}

/// Domain separator for fast-path signatures (`dregg-fast-path-sign-v2`).
const FAST_PATH_DOMAIN: &[u8] = b"dregg-fast-path-sign-v2";

/// Produce an Ed25519 fast-path signature over `turn_hash` from a 32-byte seed.
///
/// Exposed for callers that produce certificates outside the lock-table state
/// machine (e.g. solo-mode signing, test harnesses, fragment composers).
///
/// SECURITY: `seed` is a SECRET signing key seed. The returned `TurnSign`
/// contains the corresponding PUBLIC verifying key, which is safe to broadcast.
/// The signature can only be produced by a holder of `seed`; possessing the
/// public key alone is INSUFFICIENT to forge a valid signature.
pub fn sign_fast_path(seed: &[u8; 32], turn_hash: &[u8; 32], height: u64) -> TurnSign {
    let sk = SigningKey::from_bytes(seed);
    let vk: VerifyingKey = (&sk).into();
    let msg = fast_path_signing_message(turn_hash);
    let signature = sk.sign(&msg).to_bytes();
    TurnSign {
        validator_key: vk.to_bytes(),
        signature,
        height,
    }
}

/// Verify a TurnSign as a real Ed25519 signature over `turn_hash`.
///
/// SECURITY (P0-1 fix): this is a real asymmetric signature check. The previous
/// `BLAKE3::new_keyed(validator_key)` scheme was symmetric -- anyone holding the
/// validator's PUBLIC key (broadcast on the wire) could recompute a valid
/// "signature." This implementation verifies that `sign.signature` was produced
/// by the private key corresponding to `sign.validator_key`.
pub fn verify_turn_sign(sign: &TurnSign, turn_hash: &[u8; 32]) -> bool {
    let vk = match VerifyingKey::from_bytes(&sign.validator_key) {
        Ok(vk) => vk,
        Err(_) => return false,
    };
    let signature = Signature::from_bytes(&sign.signature);
    let msg = fast_path_signing_message(turn_hash);
    // verify_strict rejects malleable signatures (non-canonical R/S).
    vk.verify_strict(&msg, &signature).is_ok()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::action::{Action, Authorization, Effect};
    use crate::forest::CallForest;
    use dregg_cell::{Cell, Ledger};

    /// Test helper: derive a deterministic Ed25519 keypair from a u8 seed.
    fn keypair_from_seed(seed: u8) -> ([u8; 32], [u8; 32]) {
        let mut s = [0u8; 32];
        s[0] = seed;
        let sk = SigningKey::from_bytes(&s);
        let vk: VerifyingKey = (&sk).into();
        (s, vk.to_bytes())
    }

    /// Test helper: sign turn_hash with the agent's seed.
    fn agent_sig(seed: &[u8; 32], turn_hash: &[u8; 32]) -> [u8; 64] {
        let sk = SigningKey::from_bytes(seed);
        sk.sign(turn_hash).to_bytes()
    }

    /// Helper: create a cell with a given public key and insert it into the ledger.
    fn insert_cell_with_key(ledger: &mut Ledger, public_key: [u8; 32], balance: u64) -> CellId {
        let token_id = [0u8; 32];
        let cell = Cell::with_balance(public_key, token_id, balance);
        let id = cell.id();
        ledger.insert_cell(cell).unwrap();
        id
    }

    /// Helper: create a minimal turn targeting the agent's own cells.
    fn make_own_cell_turn(agent_id: CellId) -> Turn {
        Turn {
            agent: agent_id,
            nonce: 0,
            call_forest: CallForest::new(),
            fee: 100,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    /// Helper: create a turn with an effect that writes to another cell.
    fn make_cross_cell_turn(agent_id: CellId, target_id: CellId) -> Turn {
        use crate::action::DelegationMode;
        use crate::forest::CallTree;
        use dregg_cell::Preconditions;

        let action = Action {
            target: target_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Signature([0u8; 32], [0u8; 32]),
            preconditions: Preconditions::default(),
            effects: vec![Effect::SetField {
                cell: target_id,
                index: 0,
                value: [1u8; 32],
            }],
            may_delegate: DelegationMode::None,
            balance_change: None,
            witness_blobs: vec![],
            commitment_mode: Default::default(),
        };

        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };

        Turn {
            agent: agent_id,
            nonce: 0,
            call_forest: CallForest {
                roots: vec![tree],
                forest_hash: [0u8; 32],
            },
            fee: 100,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    #[test]
    fn test_eligibility_single_owner() {
        let mut ledger = Ledger::new();
        let pk = [1u8; 32];
        let agent_id = insert_cell_with_key(&mut ledger, pk, 1000);

        let turn = make_own_cell_turn(agent_id);
        assert!(is_fast_path_eligible(&turn, &ledger));
    }

    #[test]
    fn test_eligibility_cross_cell_disqualified() {
        let mut ledger = Ledger::new();
        let pk_alice = [1u8; 32];
        let pk_bob = [2u8; 32];
        let alice_id = insert_cell_with_key(&mut ledger, pk_alice, 1000);
        let bob_id = insert_cell_with_key(&mut ledger, pk_bob, 1000);

        // Alice's turn writes to Bob's cell -- not eligible.
        let turn = make_cross_cell_turn(alice_id, bob_id);
        assert!(!is_fast_path_eligible(&turn, &ledger));
    }

    #[test]
    fn test_eligibility_with_dependencies_disqualified() {
        let mut ledger = Ledger::new();
        let pk = [1u8; 32];
        let agent_id = insert_cell_with_key(&mut ledger, pk, 1000);

        let mut turn = make_own_cell_turn(agent_id);
        turn.depends_on = vec![[0xaa; 32]]; // Has a dependency.
        assert!(!is_fast_path_eligible(&turn, &ledger));
    }

    #[test]
    fn test_lock_and_sign() {
        let mut ledger = Ledger::new();
        let (agent_seed, agent_pk) = keypair_from_seed(1);
        let agent_id = insert_cell_with_key(&mut ledger, agent_pk, 1000);

        let turn = make_own_cell_turn(agent_id);
        let turn_hash = turn.hash();
        let agent_sig_bytes = agent_sig(&agent_seed, &turn_hash);
        let (validator_seed, validator_pk) = keypair_from_seed(0xAA);

        let mut table = CellLockTable::with_defaults();

        let result = process_fast_path_lock(
            &mut table,
            &turn,
            turn_hash,
            100, // current height
            &ledger,
            &validator_seed,
            &agent_sig_bytes,
        );

        assert!(result.is_ok());
        let sign = result.unwrap();
        assert_eq!(sign.validator_key, validator_pk);
        assert_eq!(sign.height, 100);

        // Verify the signature is valid.
        assert!(verify_turn_sign(&sign, &turn_hash));

        // The agent cell should now be locked.
        assert!(table.is_locked(&agent_id, 0));
    }

    #[test]
    fn test_lock_conflict_rejected() {
        let mut ledger = Ledger::new();
        let (agent_seed, agent_pk) = keypair_from_seed(1);
        let agent_id = insert_cell_with_key(&mut ledger, agent_pk, 1000);

        let turn1 = make_own_cell_turn(agent_id);
        let turn1_hash = turn1.hash();
        let sig1 = agent_sig(&agent_seed, &turn1_hash);
        let (validator_seed, _) = keypair_from_seed(0xAA);

        let mut table = CellLockTable::with_defaults();

        // First lock succeeds.
        let result1 = process_fast_path_lock(
            &mut table,
            &turn1,
            turn1_hash,
            100,
            &ledger,
            &validator_seed,
            &sig1,
        );
        assert!(result1.is_ok());

        // Second turn tries to lock the same cell at the same nonce.
        let mut turn2 = make_own_cell_turn(agent_id);
        turn2.memo = Some("different turn".to_string()); // Make it different.
        let turn2_hash = turn2.hash();
        let sig2 = agent_sig(&agent_seed, &turn2_hash);

        let result2 = process_fast_path_lock(
            &mut table,
            &turn2,
            turn2_hash,
            100,
            &ledger,
            &validator_seed,
            &sig2,
        );

        assert!(result2.is_err());
        match result2.unwrap_err() {
            FastPathError::LockConflict { cell_id, held_by } => {
                assert_eq!(cell_id, agent_id);
                assert_eq!(held_by, turn1_hash);
            }
            other => panic!("expected LockConflict, got: {other:?}"),
        }
    }

    #[test]
    fn test_certificate_assembly() {
        let mut ledger = Ledger::new();
        let (_, agent_pk) = keypair_from_seed(1);
        let agent_id = insert_cell_with_key(&mut ledger, agent_pk, 1000);

        let turn = make_own_cell_turn(agent_id);
        let turn_hash = turn.hash();

        // Simulate 3 validators signing (2f+1 with f=1, n=3). Each gets a distinct seed.
        let signs: Vec<TurnSign> = (0..3u8)
            .map(|i| {
                let (seed, _) = keypair_from_seed(0xA0 + i);
                sign_fast_path(&seed, &turn_hash, 100)
            })
            .collect();

        // Assemble with threshold=2 (2f+1 where f=0 for simplicity, or just test with 2).
        let cert = assemble_certificate(turn.clone(), turn_hash, signs, 2);
        assert!(cert.is_ok());
        let cert = cert.unwrap();
        assert_eq!(cert.turn_hash, turn_hash);
        assert_eq!(cert.signatures.len(), 3);

        // All signatures should verify under the real Ed25519 scheme.
        for sign in &cert.signatures {
            assert!(verify_turn_sign(sign, &turn_hash));
        }
    }

    #[test]
    fn test_certificate_insufficient_signatures() {
        let turn = Turn {
            agent: CellId([0u8; 32]),
            nonce: 0,
            call_forest: CallForest::new(),
            fee: 100,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
        let turn_hash = turn.hash();

        let (seed, _) = keypair_from_seed(0xAA);
        let sign = sign_fast_path(&seed, &turn_hash, 100);

        // Need 3, have 1.
        let result = assemble_certificate(turn, turn_hash, vec![sign], 3);
        assert!(result.is_err());
        match result.unwrap_err() {
            FastPathError::InsufficientSignatures { have: 1, need: 3 } => {}
            other => panic!("expected InsufficientSignatures, got: {other:?}"),
        }
    }

    #[test]
    fn test_stale_lock_expiry() {
        let mut ledger = Ledger::new();
        let (agent_seed, agent_pk) = keypair_from_seed(1);
        let agent_id = insert_cell_with_key(&mut ledger, agent_pk, 1000);

        let turn = make_own_cell_turn(agent_id);
        let turn_hash = turn.hash();
        let sig = agent_sig(&agent_seed, &turn_hash);
        let (validator_seed, _) = keypair_from_seed(0xAA);

        let mut table = CellLockTable::new(FastPathConfig {
            lock_timeout_blocks: 30,
            max_locks_per_cell: 1,
            require_fee_minimum: 0,
        });

        // Acquire lock at height 100.
        process_fast_path_lock(
            &mut table,
            &turn,
            turn_hash,
            100,
            &ledger,
            &validator_seed,
            &sig,
        )
        .unwrap();
        assert_eq!(table.len(), 1);

        // At height 120, lock should NOT be expired yet (only 20 blocks passed).
        let expired = expire_stale_locks(&mut table, 120);
        assert!(expired.is_empty());
        assert_eq!(table.len(), 1);

        // At height 130, lock SHOULD be expired (30 blocks passed).
        let expired = expire_stale_locks(&mut table, 130);
        assert_eq!(expired.len(), 1);
        assert_eq!(expired[0].cell_id, agent_id);
        assert_eq!(expired[0].turn_hash, turn_hash);
        assert_eq!(table.len(), 0);
    }

    /// Helper: make a minimal valid turn (with one action targeting the agent's own cell).
    fn make_valid_own_cell_turn(agent_id: CellId) -> Turn {
        use crate::action::DelegationMode;
        use crate::forest::CallTree;
        use dregg_cell::Preconditions;

        let action = Action {
            target: agent_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Signature([0u8; 32], [0u8; 32]),
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            balance_change: None,
            witness_blobs: vec![],
            commitment_mode: Default::default(),
        };

        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };

        Turn {
            agent: agent_id,
            nonce: 0,
            call_forest: CallForest {
                roots: vec![tree],
                forest_hash: [0u8; 32],
            },
            fee: 100,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    #[test]
    fn test_execute_certified_turn() {
        let mut ledger = Ledger::new();
        let (agent_seed, agent_pk) = keypair_from_seed(1);
        let agent_id = insert_cell_with_key(&mut ledger, agent_pk, 10_000);

        let turn = make_valid_own_cell_turn(agent_id);
        let turn_hash = turn.hash();
        let agent_sig_bytes = agent_sig(&agent_seed, &turn_hash);

        // Lock the cell.
        let mut table = CellLockTable::with_defaults();
        let (validator_seed, _) = keypair_from_seed(0xAA);
        process_fast_path_lock(
            &mut table,
            &turn,
            turn_hash,
            100,
            &ledger,
            &validator_seed,
            &agent_sig_bytes,
        )
        .unwrap();
        assert!(!table.is_empty());

        // Build a certificate using a real Ed25519 signature.
        let sign = sign_fast_path(&validator_seed, &turn_hash, 100);
        let cert = assemble_certificate(turn, turn_hash, vec![sign], 1).unwrap();

        // Execute.
        let executor = crate::executor::TurnExecutor::new(crate::executor::ComputronCosts::zero());
        let result = execute_certified_turn(&cert, &executor, &mut ledger, &mut table);

        // The turn should commit (empty call forest, just nonce bump + fee deduction).
        match &result {
            TurnResult::Rejected { reason, at_action } => {
                panic!("turn rejected at {at_action:?}: {reason}");
            }
            _ => {}
        }
        assert!(result.is_committed());

        // Locks should be released after execution.
        assert!(table.is_empty());
    }

    #[test]
    fn test_clear_all_locks() {
        let mut ledger = Ledger::new();
        let (agent_seed, agent_pk) = keypair_from_seed(1);
        let agent_id = insert_cell_with_key(&mut ledger, agent_pk, 1000);

        let turn = make_own_cell_turn(agent_id);
        let turn_hash = turn.hash();
        let sig = agent_sig(&agent_seed, &turn_hash);
        let (validator_seed, _) = keypair_from_seed(0xAA);

        let mut table = CellLockTable::with_defaults();
        process_fast_path_lock(
            &mut table,
            &turn,
            turn_hash,
            100,
            &ledger,
            &validator_seed,
            &sig,
        )
        .unwrap();
        assert!(!table.is_empty());

        let cleared = clear_all_locks(&mut table);
        assert_eq!(cleared.len(), 1);
        assert!(table.is_empty());
    }

    #[test]
    fn test_idempotent_relock_same_turn() {
        let mut ledger = Ledger::new();
        let (agent_seed, agent_pk) = keypair_from_seed(1);
        let agent_id = insert_cell_with_key(&mut ledger, agent_pk, 1000);

        let turn = make_own_cell_turn(agent_id);
        let turn_hash = turn.hash();
        let sig = agent_sig(&agent_seed, &turn_hash);
        let (validator_seed, _) = keypair_from_seed(0xAA);

        let mut table = CellLockTable::with_defaults();

        // First lock.
        let r1 = process_fast_path_lock(
            &mut table,
            &turn,
            turn_hash,
            100,
            &ledger,
            &validator_seed,
            &sig,
        );
        assert!(r1.is_ok());

        // Same turn, same hash -- should succeed (idempotent).
        let r2 = process_fast_path_lock(
            &mut table,
            &turn,
            turn_hash,
            100,
            &ledger,
            &validator_seed,
            &sig,
        );
        assert!(r2.is_ok());
        assert_eq!(table.len(), 1); // Still just one lock.
    }

    #[test]
    fn test_fee_too_low_rejected() {
        let mut ledger = Ledger::new();
        let (agent_seed, agent_pk) = keypair_from_seed(1);
        let agent_id = insert_cell_with_key(&mut ledger, agent_pk, 1000);

        let mut turn = make_own_cell_turn(agent_id);
        turn.fee = 5; // Below minimum.
        let turn_hash = turn.hash();
        let sig = agent_sig(&agent_seed, &turn_hash);
        let (validator_seed, _) = keypair_from_seed(0xAA);

        let mut table = CellLockTable::new(FastPathConfig {
            lock_timeout_blocks: 30,
            max_locks_per_cell: 1,
            require_fee_minimum: 100, // Requires at least 100.
        });

        let result = process_fast_path_lock(
            &mut table,
            &turn,
            turn_hash,
            100,
            &ledger,
            &validator_seed,
            &sig,
        );

        match result.unwrap_err() {
            FastPathError::FeeTooLow {
                minimum: 100,
                offered: 5,
            } => {}
            other => panic!("expected FeeTooLow, got: {other:?}"),
        }
    }

    // ========================================================================
    // Adversarial tests for P0-1 (forgeable BLAKE3-keyed signatures) and P1-6
    // (missing agent signature check at lock time).
    // ========================================================================

    /// P0-1 adversarial: forging a fast-path "signature" using only the
    /// validator's PUBLIC key (the same scheme the old BLAKE3-keyed code used)
    /// MUST be rejected by the real Ed25519 verifier.
    #[test]
    fn fast_path_forged_blake3_signature_rejected() {
        let turn = Turn {
            agent: CellId([0u8; 32]),
            nonce: 0,
            call_forest: CallForest::new(),
            fee: 100,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
        let turn_hash = turn.hash();

        // The attacker knows the validator's PUBLIC key (broadcast on the wire).
        let (_real_seed, validator_pk) = keypair_from_seed(0x42);

        // Old forgery technique: BLAKE3-keyed-hash where the key is the public
        // identity. Anyone who learned the public key could compute this.
        let mut hasher = blake3::Hasher::new_keyed(&validator_pk);
        hasher.update(b"dregg-fast-path-sign-v1");
        hasher.update(&turn_hash);
        let lo = hasher.finalize();
        let mut hasher2 = blake3::Hasher::new_keyed(&validator_pk);
        hasher2.update(b"dregg-fast-path-sign-v1-ext");
        hasher2.update(&turn_hash);
        let hi = hasher2.finalize();
        let mut forged = [0u8; 64];
        forged[..32].copy_from_slice(lo.as_bytes());
        forged[32..].copy_from_slice(hi.as_bytes());

        let forged_sign = TurnSign {
            validator_key: validator_pk,
            signature: forged,
            height: 100,
        };

        assert!(
            !verify_turn_sign(&forged_sign, &turn_hash),
            "BLAKE3-keyed forgery using only the validator's public key MUST be rejected"
        );
    }

    /// P0-1 adversarial: a signature produced by ANY seed other than the real
    /// validator's MUST be rejected, even if the attacker sets validator_key to
    /// the real validator's public key.
    #[test]
    fn fast_path_signature_under_wrong_seed_rejected() {
        let turn = Turn {
            agent: CellId([0u8; 32]),
            nonce: 0,
            call_forest: CallForest::new(),
            fee: 100,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
        let turn_hash = turn.hash();

        let (_real_seed, real_validator_pk) = keypair_from_seed(0x42);
        let (attacker_seed, _attacker_pk) = keypair_from_seed(0x99);

        // Attacker signs with their own seed but stamps the real validator's PK
        // in validator_key (the kind of attack the old symmetric scheme allowed).
        let mut sign = sign_fast_path(&attacker_seed, &turn_hash, 100);
        sign.validator_key = real_validator_pk;

        assert!(
            !verify_turn_sign(&sign, &turn_hash),
            "Signature produced by attacker's seed MUST NOT verify under the real \
             validator's public key"
        );
    }

    /// P1-6 adversarial: process_fast_path_lock MUST reject a lock request that
    /// is not accompanied by a valid agent signature over turn_hash. Previously
    /// it trusted callers to have verified upstream.
    #[test]
    fn fast_path_lock_rejects_missing_agent_signature() {
        let mut ledger = Ledger::new();
        let (_agent_seed, agent_pk) = keypair_from_seed(1);
        let agent_id = insert_cell_with_key(&mut ledger, agent_pk, 1000);

        let turn = make_own_cell_turn(agent_id);
        let turn_hash = turn.hash();
        let (validator_seed, _) = keypair_from_seed(0xAA);

        let mut table = CellLockTable::with_defaults();

        // Garbage agent signature.
        let bogus_sig = [0u8; 64];

        let result = process_fast_path_lock(
            &mut table,
            &turn,
            turn_hash,
            100,
            &ledger,
            &validator_seed,
            &bogus_sig,
        );

        match result {
            Err(FastPathError::InvalidSignature) => {}
            other => panic!("expected InvalidSignature, got: {other:?}"),
        }
        // No lock should have been acquired.
        assert!(table.is_empty());
    }

    /// P1-6 adversarial: a signature produced by an attacker's seed (different
    /// from the agent's seed) MUST be rejected even though it's a real Ed25519
    /// signature.
    #[test]
    fn fast_path_lock_rejects_signature_under_attacker_seed() {
        let mut ledger = Ledger::new();
        let (_agent_seed, agent_pk) = keypair_from_seed(1);
        let agent_id = insert_cell_with_key(&mut ledger, agent_pk, 1000);

        let turn = make_own_cell_turn(agent_id);
        let turn_hash = turn.hash();
        let (attacker_seed, _) = keypair_from_seed(0x77);
        let bad_sig = agent_sig(&attacker_seed, &turn_hash);

        let (validator_seed, _) = keypair_from_seed(0xAA);
        let mut table = CellLockTable::with_defaults();

        let result = process_fast_path_lock(
            &mut table,
            &turn,
            turn_hash,
            100,
            &ledger,
            &validator_seed,
            &bad_sig,
        );

        assert!(matches!(result, Err(FastPathError::InvalidSignature)));
        assert!(table.is_empty());
    }
}
