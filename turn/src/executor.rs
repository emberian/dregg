//! TurnExecutor: applies a turn to a ledger with full atomicity.
//!
//! # Trust Model
//!
//! This module operates at the **EXECUTOR-TRUSTED** trust level.
//!
//! - **Soundness**: Correct state transitions are guaranteed IF all federation members
//!   execute the same turns in the same order and reach consensus on the resulting state.
//!   A compromised executor can produce incorrect state that other honest members will
//!   reject during replication.
//! - **Assumptions**: At least 2f+1 honest federation members (BFT assumption). The
//!   executor correctly implements the turn semantics, precondition checks, and effect
//!   application. External parties trust the federation as a whole.
//! - **Verifiable by**: Other federation members via state replication. External parties
//!   trust the federation's attested root (not individually verifiable without re-execution).
//!
//! ## Trust-Critical Functions
//!
//! The following functions are trust-critical and are annotated individually:
//! - `execute()` — atomically applies a turn; if compromised, state diverges from consensus
//! - `verify_authorization()` — gates all state mutations; bypass = unauthorized writes
//! - `apply_effect()` — mutates ledger state; incorrect application = balance corruption
//! - `verify_and_commit_proof()` — bridges trustless (STARK) to executor; bypass = forged sovereign state
//! - `check_preconditions()` — temporal and state guards; bypass = expired/invalid actions succeed
//!
//! ## Path to Trustless
//!
//! Phase 3 (proof-carrying sovereign turns) already moves sovereign cells to the
//! trustless level: the executor merely verifies a STARK proof and updates a commitment.
//! The remaining executor-trusted path (Phase 2: classical call-forest execution) will
//! transition to trustless once the Effect VM circuit covers all effect types, allowing
//! every turn to carry a proof.
//!
//! The executor walks the call forest depth-first, checking preconditions,
//! verifying authorization, applying effects, and metering computrons at each step.
//! If any action fails, ALL effects are rolled back via journal replay (atomicity guarantee).

use std::collections::HashMap;
use std::sync::Mutex;

use ed25519_dalek::{Signature, VerifyingKey};
use pyana_cell::{
    AuthRequired, BulletproofRangeProof, Cell, CellId, CellStateDelta, Ledger, LedgerDelta,
    Preconditions, RevocationChannelSet, ValueCommitment, ValueCommitmentBytes,
    note_bridge::{BridgedNullifierSet, PendingBridgeSet},
    preconditions::EvalContext,
    state::STATE_SLOTS,
};
use pyana_types::AttestedRoot;
use serde::{Deserialize, Serialize};

use crate::action::{Action, Authorization, DelegationMode, Effect};
use crate::budget_gate::BudgetGate;
use crate::error::TurnError;
use crate::escrow::{CommittedEscrow, EscrowCondition, EscrowRecord, verify_escrow_claim};
use crate::forest::CallTree;
use crate::journal::{JournalEntry, LedgerJournal};
use crate::routing::RoutingDirective;
use crate::turn::{EmittedEvent, Turn, TurnReceipt, TurnResult};

use pyana_dsl_runtime::ProgramRegistry;

/// Whether note effects in a turn use Pedersen value commitments or cleartext values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NoteCommitmentMode {
    /// No note effects present in the turn.
    Empty,
    /// All note effects use cleartext values (legacy path).
    Cleartext,
    /// All note effects carry Pedersen value commitments (committed path).
    Committed,
    /// Some notes have commitments, some don't -- invalid (rejected).
    Mixed,
}

/// A record of an active obligation tracked by the executor for balance enforcement.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ObligationRecord {
    /// The obligor (who locked the stake).
    pub obligor: CellId,
    /// The beneficiary (who receives stake on slash).
    pub beneficiary: CellId,
    /// Federation height deadline.
    pub deadline_height: u64,
    /// Numeric stake amount locked from the obligor's balance.
    pub stake_amount: u64,
    /// Whether this obligation has been resolved (fulfilled or slashed).
    pub resolved: bool,
}

/// Trait for verifying ZK proofs. Implementations provide circuit-specific verification.
///
/// The executor is fail-closed: if no ProofVerifier is configured and a cell requires
/// proof authorization, the action is rejected.
pub trait ProofVerifier: Send + Sync {
    /// Verify a proof against public inputs and a verification key.
    ///
    /// Returns true if the proof is valid for the given public inputs and verification key.
    fn verify(&self, proof: &[u8], action: &str, resource: &str, vk: &[u8]) -> bool;
}

/// Cost configuration for computron metering.
///
/// Each operation has a base cost in computrons. The total cost of a turn
/// is the sum of all operation costs. If the agent's fee doesn't cover the
/// total, the turn is rejected.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ComputronCosts {
    /// Base cost per action in the forest.
    pub action_base: u64,
    /// Base cost per effect applied.
    pub effect_base: u64,
    /// Cost per computron transfer.
    pub transfer: u64,
    /// Cost for creating a new cell.
    pub create_cell: u64,
    /// Cost for verifying a ZK proof.
    pub proof_verify: u64,
    /// Cost for verifying a signature.
    pub signature_verify: u64,
    /// Cost per byte of data processed.
    pub per_byte: u64,
}

impl ComputronCosts {
    /// Default cost configuration (reasonable for testing).
    pub fn default_costs() -> Self {
        ComputronCosts {
            action_base: 100,
            effect_base: 50,
            transfer: 75,
            create_cell: 500,
            proof_verify: 1000,
            signature_verify: 200,
            per_byte: 1,
        }
    }

    /// Zero costs (for testing without metering).
    pub fn zero() -> Self {
        ComputronCosts {
            action_base: 0,
            effect_base: 0,
            transfer: 0,
            create_cell: 0,
            proof_verify: 0,
            signature_verify: 0,
            per_byte: 0,
        }
    }
}

impl Default for ComputronCosts {
    fn default() -> Self {
        Self::default_costs()
    }
}

// =============================================================================
// Cell Migration Two-Phase Commit
// =============================================================================

/// State of a cell migration operation (two-phase commit protocol).
///
/// Cell migration moves a cell from one federation to another. Without a two-phase
/// protocol, a network partition after the source freezes the cell but before the
/// target receives the bundle would leave the cell in limbo (source thinks it's
/// gone, target never received it).
///
/// The protocol:
/// 1. Source freezes the cell (prevents further turns) and transitions to `Frozen`.
/// 2. Source sends the migration bundle to the target.
/// 3. Target acknowledges receipt -> source transitions to `AwaitingReceipt`.
/// 4. On receipt confirmation, source permanently removes the cell (migration complete).
/// 5. On timeout without receipt: source unfreezes the cell (migration cancelled).
///
/// The target checks for cancellation before accepting: if the source cancelled,
/// the target must not accept the bundle (preventing double-existence).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MigrationState {
    /// No migration in progress for this cell.
    Idle,
    /// The cell is frozen for migration. No turns may execute against it.
    /// If `timeout` blocks elapse without transitioning to `AwaitingReceipt`,
    /// the migration is cancelled and the cell is unfrozen.
    Frozen {
        /// The cell being migrated.
        cell_id: CellId,
        /// The target federation receiving the cell.
        target: [u8; 32],
        /// Block height at which the cell was frozen.
        frozen_at: u64,
        /// Maximum blocks to wait before auto-cancellation.
        timeout: u64,
    },
    /// The migration bundle was sent and we are waiting for the target's receipt.
    /// If `timeout` blocks elapse without confirmation, migration is cancelled.
    AwaitingReceipt {
        /// The cell being migrated.
        cell_id: CellId,
        /// The target federation.
        target: [u8; 32],
        /// Block height at which the bundle was sent.
        sent_at: u64,
        /// Maximum blocks to wait for receipt confirmation.
        timeout: u64,
    },
    /// The migration completed successfully. The cell now lives on the target federation.
    Completed {
        /// The cell that was migrated.
        cell_id: CellId,
        /// The target federation that now owns the cell.
        target: [u8; 32],
        /// Block height at which the migration was confirmed.
        confirmed_at: u64,
    },
    /// The migration was cancelled (timeout or explicit cancel).
    /// The cell is unfrozen and available for local turns again.
    Cancelled {
        /// The cell whose migration was cancelled.
        cell_id: CellId,
        /// Reason for cancellation.
        reason: MigrationCancelReason,
    },
}

/// Reason a cell migration was cancelled.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MigrationCancelReason {
    /// Timed out waiting for the target to acknowledge the bundle.
    Timeout,
    /// Explicitly cancelled by the source (e.g., operator intervention).
    Explicit,
    /// The target rejected the migration bundle.
    TargetRejected,
}

/// Manages cell migration state for a federation's executor.
///
/// Tracks which cells are currently being migrated and enforces the two-phase
/// commit protocol with timeout-based cancellation.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CellMigrationManager {
    /// Active migration states, keyed by cell ID.
    migrations: HashMap<CellId, MigrationState>,
}

impl CellMigrationManager {
    /// Create a new empty migration manager.
    pub fn new() -> Self {
        Self {
            migrations: HashMap::new(),
        }
    }

    /// Begin a cell migration: freeze the cell for transfer to the target federation.
    ///
    /// Returns `Err` if the cell is already being migrated.
    pub fn begin_migration(
        &mut self,
        cell_id: CellId,
        target: [u8; 32],
        current_height: u64,
        timeout: u64,
    ) -> Result<(), MigrationError> {
        if let Some(state) = self.migrations.get(&cell_id) {
            match state {
                MigrationState::Idle | MigrationState::Cancelled { .. } => {
                    // Can start a new migration (previous was idle or cancelled)
                }
                _ => return Err(MigrationError::AlreadyMigrating),
            }
        }

        self.migrations.insert(
            cell_id,
            MigrationState::Frozen {
                cell_id,
                target,
                frozen_at: current_height,
                timeout,
            },
        );
        Ok(())
    }

    /// Record that the migration bundle was sent to the target.
    ///
    /// Transitions from `Frozen` to `AwaitingReceipt`.
    pub fn bundle_sent(
        &mut self,
        cell_id: CellId,
        current_height: u64,
        receipt_timeout: u64,
    ) -> Result<(), MigrationError> {
        let state = self
            .migrations
            .get(&cell_id)
            .ok_or(MigrationError::NotMigrating)?;

        match state {
            MigrationState::Frozen { target, .. } => {
                let target = *target;
                self.migrations.insert(
                    cell_id,
                    MigrationState::AwaitingReceipt {
                        cell_id,
                        target,
                        sent_at: current_height,
                        timeout: receipt_timeout,
                    },
                );
                Ok(())
            }
            _ => Err(MigrationError::InvalidTransition),
        }
    }

    /// Confirm that the target received and accepted the migration bundle.
    ///
    /// Transitions to `Completed`. After this, the cell can be removed from the
    /// local ledger.
    pub fn confirm_receipt(
        &mut self,
        cell_id: CellId,
        current_height: u64,
    ) -> Result<(), MigrationError> {
        let state = self
            .migrations
            .get(&cell_id)
            .ok_or(MigrationError::NotMigrating)?;

        match state {
            MigrationState::AwaitingReceipt { target, .. } => {
                let target = *target;
                self.migrations.insert(
                    cell_id,
                    MigrationState::Completed {
                        cell_id,
                        target,
                        confirmed_at: current_height,
                    },
                );
                Ok(())
            }
            _ => Err(MigrationError::InvalidTransition),
        }
    }

    /// Check for timed-out migrations and cancel them.
    ///
    /// Returns the cell IDs of migrations that were cancelled due to timeout.
    /// For each cancelled migration, the cell is unfrozen and available for local
    /// turns again.
    pub fn check_timeouts(&mut self, current_height: u64) -> Vec<CellId> {
        let mut cancelled = Vec::new();

        let timed_out: Vec<CellId> = self
            .migrations
            .iter()
            .filter_map(|(cell_id, state)| match state {
                MigrationState::Frozen {
                    frozen_at, timeout, ..
                } => {
                    if current_height.saturating_sub(*frozen_at) > *timeout {
                        Some(*cell_id)
                    } else {
                        None
                    }
                }
                MigrationState::AwaitingReceipt {
                    sent_at, timeout, ..
                } => {
                    if current_height.saturating_sub(*sent_at) > *timeout {
                        Some(*cell_id)
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .collect();

        for cell_id in timed_out {
            self.migrations.insert(
                cell_id,
                MigrationState::Cancelled {
                    cell_id,
                    reason: MigrationCancelReason::Timeout,
                },
            );
            cancelled.push(cell_id);
        }

        cancelled
    }

    /// Explicitly cancel a migration (e.g., operator intervention).
    ///
    /// The cell is unfrozen and available for local turns again.
    pub fn cancel(
        &mut self,
        cell_id: CellId,
        reason: MigrationCancelReason,
    ) -> Result<(), MigrationError> {
        let state = self
            .migrations
            .get(&cell_id)
            .ok_or(MigrationError::NotMigrating)?;

        match state {
            MigrationState::Frozen { .. } | MigrationState::AwaitingReceipt { .. } => {
                self.migrations
                    .insert(cell_id, MigrationState::Cancelled { cell_id, reason });
                Ok(())
            }
            _ => Err(MigrationError::InvalidTransition),
        }
    }

    /// Check if a cell is currently frozen for migration.
    ///
    /// Returns `true` if the cell is in `Frozen` or `AwaitingReceipt` state,
    /// meaning no local turns should execute against it.
    pub fn is_frozen(&self, cell_id: &CellId) -> bool {
        matches!(
            self.migrations.get(cell_id),
            Some(MigrationState::Frozen { .. } | MigrationState::AwaitingReceipt { .. })
        )
    }

    /// Check if a migration was cancelled (target should reject the bundle).
    pub fn is_cancelled(&self, cell_id: &CellId) -> bool {
        matches!(
            self.migrations.get(cell_id),
            Some(MigrationState::Cancelled { .. })
        )
    }

    /// Get the migration state for a cell.
    pub fn get(&self, cell_id: &CellId) -> Option<&MigrationState> {
        self.migrations.get(cell_id)
    }

    /// Remove completed or cancelled migration entries (cleanup).
    pub fn gc_completed(&mut self) -> Vec<CellId> {
        let removable: Vec<CellId> = self
            .migrations
            .iter()
            .filter_map(|(cell_id, state)| match state {
                MigrationState::Completed { .. } | MigrationState::Cancelled { .. } => {
                    Some(*cell_id)
                }
                _ => None,
            })
            .collect();

        for cell_id in &removable {
            self.migrations.remove(cell_id);
        }

        removable
    }
}

/// Errors that can occur during cell migration operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MigrationError {
    /// The cell is already being migrated.
    AlreadyMigrating,
    /// The cell is not currently in a migration state.
    NotMigrating,
    /// The requested state transition is not valid from the current state.
    InvalidTransition,
}

impl std::fmt::Display for MigrationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MigrationError::AlreadyMigrating => write!(f, "cell is already being migrated"),
            MigrationError::NotMigrating => write!(f, "cell is not in a migration state"),
            MigrationError::InvalidTransition => {
                write!(f, "invalid migration state transition")
            }
        }
    }
}

impl std::error::Error for MigrationError {}

/// The turn executor: applies turns to a ledger atomically.
pub struct TurnExecutor {
    /// Cost configuration for computron metering.
    pub costs: ComputronCosts,
    /// Program registry for custom cell programs (smart contract runtime).
    /// When a sovereign cell has a `verification_key_hash` set, the executor
    /// looks up the deployed program here and verifies proofs against it.
    /// Falls back to `EffectVmAir` if no program is found.
    pub program_registry: ProgramRegistry,
    /// Current timestamp for precondition evaluation.
    pub current_timestamp: i64,
    /// Current block height for precondition evaluation.
    pub block_height: u64,
    /// Optional ZK proof verifier. If None and a cell requires proof auth, the action is rejected.
    pub proof_verifier: Option<Box<dyn ProofVerifier>>,
    /// Optional budget gate (Stingray bounded counter).
    /// When present, the executor checks the silo's local budget slice before executing
    /// each turn. If the slice cannot cover the turn fee, the turn is rejected with
    /// `TurnError::BudgetExhausted`. On turn failure, the debit is refunded (fast unlock).
    ///
    /// Designed for single-silo-single-thread execution, but uses `Mutex` for interior
    /// mutability to remain sound under concurrent access (future-proofing for async
    /// execution or parallel turn processing).
    pub budget_gate: Option<Mutex<BudgetGate>>,
    /// Trusted federation roots for cross-federation note bridging.
    /// When a BridgeMint effect is processed, the portable proof's source root
    /// must be in this set. Empty = no cross-federation bridges accepted.
    pub trusted_federation_roots: Vec<AttestedRoot>,
    /// This federation's identity (genesis root hash or configured ID).
    /// Prevents cross-federation double-spend via destination binding.
    pub local_federation_id: [u8; 32],
    /// Bridged nullifier set: tracks nullifiers from OTHER federations that have
    /// been bridged into this one. Prevents the same note from being bridged twice.
    pub bridged_nullifiers: Mutex<BridgedNullifierSet>,
    /// Pending bridges: notes locked for cross-federation transfer (two-phase protocol).
    /// Tracks notes that are committed-to-burn but not yet permanently spent.
    pub pending_bridges: Mutex<PendingBridgeSet>,
    /// Trusted Ed25519 public keys for destination federation receipt verification.
    /// Used during BridgeFinalize to validate that the receipt was signed by a
    /// legitimate destination federation.
    pub trusted_destination_keys: Vec<[u8; 32]>,
    /// Block proposer cell (receives 50% of fees). If None, fees are 100% burned.
    pub proposer_cell: Option<CellId>,
    /// Federation treasury cell (receives 30% of fees). If None, that share is burned.
    pub treasury_cell: Option<CellId>,
    /// Maximum lifetime (in blocks) for capabilities introduced via three-party
    /// introduction. After `current_height + max_introduction_lifetime`, the routing
    /// directive expires and the introduced capability becomes stale.
    /// Default: 1000 blocks.
    pub max_introduction_lifetime: u64,
    /// Optional revocation channel set. When present, capability exercises and
    /// delegation access checks verify that gated capabilities haven't been revoked
    /// via their associated channel.
    pub revocation_channels: Option<RevocationChannelSet>,
    /// Active obligation records, keyed by obligation ID.
    /// Tracks locked stakes so that FulfillObligation and SlashObligation can
    /// enforce balance movement (return to obligor or transfer to beneficiary).
    pub obligations: Mutex<HashMap<[u8; 32], ObligationRecord>>,
    /// Active escrow records, keyed by escrow ID.
    /// Tracks locked funds for conditional settlement (release to recipient or refund to creator).
    pub escrows: Mutex<HashMap<[u8; 32], EscrowRecord>>,
    /// Active committed (privacy-preserving) escrow records, keyed by escrow ID.
    /// Tracks committed escrows where parties and amounts are hidden behind commitments.
    pub committed_escrows: Mutex<HashMap<[u8; 32], CommittedEscrow>>,
    /// Executor-internal side-table mapping committed escrow IDs to their locked amounts.
    /// This is needed for balance settlement (release/refund) since the committed escrow
    /// record intentionally does not store the cleartext amount. Only the executor knows
    /// this mapping; it is NOT exposed to observers.
    pub committed_escrow_amounts: Mutex<HashMap<[u8; 32], u64>>,
    /// Cell migration manager: tracks cells that are being migrated to other federations.
    /// Uses a two-phase commit protocol with timeout-based cancellation to prevent
    /// cells from being lost during network partitions.
    pub cell_migrations: Mutex<CellMigrationManager>,
    /// Factory registry: deployed factory descriptors and per-epoch creation counts.
    /// When a `CreateCellFromFactory` effect is processed, the factory's constraints
    /// are validated and budget is checked/recorded.
    /// Uses `RefCell` for interior mutability: `apply_effect` takes `&self` but
    /// factory validation needs `&mut` for recording budget usage.
    pub factory_registry: std::cell::RefCell<pyana_cell::FactoryRegistry>,
    /// Optional epoch minter for computron supply management.
    ///
    /// When configured, the executor calls `maybe_mint()` at each block to
    /// check for epoch boundaries and credit the treasury with newly minted
    /// computrons. This prevents the deflationary death spiral where all
    /// computrons are eventually burned.
    ///
    /// Uses `RefCell` for interior mutability since minting is called from
    /// within the execute path which takes `&self`.
    pub epoch_minter: Option<std::cell::RefCell<crate::economics::EpochMinter>>,
    /// Queue program registry: maps queue IDs to their attached validation programs.
    /// When an `EnqueueMessage` effect targets a queue with a registered program,
    /// the executor validates the enqueue against the program's constraints before
    /// accepting the effect. The validation result hash is bound to the STARK proof.
    pub queue_program_registry: crate::queue_programs::QueueProgramRegistry,
    /// Per-agent last receipt hash (P0-3 fix).
    ///
    /// On every successful turn commit, the agent's entry is set to the
    /// resulting receipt's `receipt_hash()`. Subsequent turns from the same
    /// agent must set `turn.previous_receipt_hash` to this value or be
    /// rejected with `TurnError::ReceiptChainMismatch`. An entry with no
    /// value means the agent has no committed turns and must submit with
    /// `previous_receipt_hash: None` (a "genesis" turn for that agent).
    ///
    /// Off-chain `verify::verify_receipt_chain` already enforces this when it
    /// has access to the full chain. This field enforces the same property
    /// AT WRITE TIME, removing the wallet's ability to silently break the
    /// chain by submitting every turn as if it were genesis.
    pub last_receipt_hash: Mutex<HashMap<CellId, [u8; 32]>>,
    /// Optional 32-byte Ed25519 signing key seed used to populate
    /// `TurnReceipt::executor_signature` on every committed receipt.
    ///
    /// When set, the executor signs each receipt's `receipt_hash()` and
    /// embeds the 64-byte signature in `receipt.executor_signature`. This is
    /// R-4 of `EFFECT-VM-SHAPE-A.md`: previously the field existed but was
    /// never populated, so the federation-exit path could not actually
    /// authenticate receipts as having come from a known executor.
    ///
    /// `None` reproduces the legacy behavior (receipts ship with
    /// `executor_signature = None`); existing chain-verification code
    /// (`verify_receipt_chain_with_keys`) treats absent signatures as a
    /// best-effort property, so the field is opt-in.
    pub executor_signing_key: Option<[u8; 32]>,
}

impl TurnExecutor {
    /// Create a new executor with the given cost configuration.
    pub fn new(costs: ComputronCosts) -> Self {
        TurnExecutor {
            costs,
            program_registry: ProgramRegistry::new(),
            current_timestamp: 0,
            block_height: 0,
            proof_verifier: None,
            budget_gate: None,
            trusted_federation_roots: Vec::new(),
            local_federation_id: [0u8; 32],
            bridged_nullifiers: Mutex::new(BridgedNullifierSet::new()),
            pending_bridges: Mutex::new(PendingBridgeSet::new()),
            trusted_destination_keys: Vec::new(),
            proposer_cell: None,
            treasury_cell: None,
            max_introduction_lifetime: 1000,
            revocation_channels: None,
            obligations: Mutex::new(HashMap::new()),
            escrows: Mutex::new(HashMap::new()),
            committed_escrows: Mutex::new(HashMap::new()),
            committed_escrow_amounts: Mutex::new(HashMap::new()),
            cell_migrations: Mutex::new(CellMigrationManager::new()),
            factory_registry: std::cell::RefCell::new(pyana_cell::FactoryRegistry::new()),
            epoch_minter: None,
            queue_program_registry: crate::queue_programs::QueueProgramRegistry::new(),
            last_receipt_hash: Mutex::new(HashMap::new()),
            executor_signing_key: None,
        }
    }

    /// Create a new executor with a budget gate (Stingray bounded counter).
    ///
    /// When a budget gate is set, the executor checks the silo's local budget
    /// slice before executing each turn. If the slice cannot cover the turn fee,
    /// the turn is rejected with `TurnError::BudgetExhausted`.
    pub fn with_budget_gate(costs: ComputronCosts, gate: BudgetGate) -> Self {
        TurnExecutor {
            costs,
            program_registry: ProgramRegistry::new(),
            current_timestamp: 0,
            block_height: 0,
            proof_verifier: None,
            budget_gate: Some(Mutex::new(gate)),
            trusted_federation_roots: Vec::new(),
            local_federation_id: [0u8; 32],
            bridged_nullifiers: Mutex::new(BridgedNullifierSet::new()),
            pending_bridges: Mutex::new(PendingBridgeSet::new()),
            trusted_destination_keys: Vec::new(),
            proposer_cell: None,
            treasury_cell: None,
            max_introduction_lifetime: 1000,
            revocation_channels: None,
            obligations: Mutex::new(HashMap::new()),
            escrows: Mutex::new(HashMap::new()),
            committed_escrows: Mutex::new(HashMap::new()),
            committed_escrow_amounts: Mutex::new(HashMap::new()),
            cell_migrations: Mutex::new(CellMigrationManager::new()),
            factory_registry: std::cell::RefCell::new(pyana_cell::FactoryRegistry::new()),
            epoch_minter: None,
            queue_program_registry: crate::queue_programs::QueueProgramRegistry::new(),
            last_receipt_hash: Mutex::new(HashMap::new()),
            executor_signing_key: None,
        }
    }

    /// Create a new executor with a proof verifier.
    pub fn with_proof_verifier(costs: ComputronCosts, verifier: Box<dyn ProofVerifier>) -> Self {
        TurnExecutor {
            costs,
            program_registry: ProgramRegistry::new(),
            current_timestamp: 0,
            block_height: 0,
            proof_verifier: Some(verifier),
            budget_gate: None,
            trusted_federation_roots: Vec::new(),
            local_federation_id: [0u8; 32],
            bridged_nullifiers: Mutex::new(BridgedNullifierSet::new()),
            pending_bridges: Mutex::new(PendingBridgeSet::new()),
            trusted_destination_keys: Vec::new(),
            proposer_cell: None,
            treasury_cell: None,
            max_introduction_lifetime: 1000,
            revocation_channels: None,
            obligations: Mutex::new(HashMap::new()),
            escrows: Mutex::new(HashMap::new()),
            committed_escrows: Mutex::new(HashMap::new()),
            committed_escrow_amounts: Mutex::new(HashMap::new()),
            cell_migrations: Mutex::new(CellMigrationManager::new()),
            factory_registry: std::cell::RefCell::new(pyana_cell::FactoryRegistry::new()),
            epoch_minter: None,
            queue_program_registry: crate::queue_programs::QueueProgramRegistry::new(),
            last_receipt_hash: Mutex::new(HashMap::new()),
            executor_signing_key: None,
        }
    }

    /// Set the budget gate.
    pub fn set_budget_gate(&mut self, gate: BudgetGate) {
        self.budget_gate = Some(Mutex::new(gate));
    }

    /// Set the proof verifier.
    pub fn set_proof_verifier(&mut self, verifier: Box<dyn ProofVerifier>) {
        self.proof_verifier = Some(verifier);
    }

    /// Equip the executor with an Ed25519 signing key (32-byte seed) used to
    /// populate `TurnReceipt::executor_signature` on every committed receipt.
    ///
    /// This is R-4 of `EFFECT-VM-SHAPE-A.md`. Until this builder is invoked,
    /// receipts ship with `executor_signature: None` (the legacy behavior);
    /// once set, every receipt produced by this executor — both the proof-
    /// carrying fast path and the standard execution path — is signed with
    /// the given key over the receipt's canonical `receipt_hash()`.
    ///
    /// Verification: `turn::verify::verify_receipt_chain_with_keys` walks the
    /// chain and accepts a receipt only if its `executor_signature` (when
    /// present) verifies against one of the caller-supplied executor public
    /// keys.
    pub fn with_executor_signing_key(mut self, signing_key_seed: [u8; 32]) -> Self {
        self.executor_signing_key = Some(signing_key_seed);
        self
    }

    /// Set the executor signing key after construction.
    pub fn set_executor_signing_key(&mut self, signing_key_seed: [u8; 32]) {
        self.executor_signing_key = Some(signing_key_seed);
    }

    /// Sign `receipt.receipt_hash()` with the executor's signing key if one
    /// is configured, returning the 64-byte signature bytes for embedding in
    /// `receipt.executor_signature`. Returns `None` when no key is set —
    /// callers should leave `executor_signature` as `None` in that case.
    fn maybe_sign_receipt(&self, receipt: &TurnReceipt) -> Option<Vec<u8>> {
        let seed = self.executor_signing_key.as_ref()?;
        let sk = ed25519_dalek::SigningKey::from_bytes(seed);
        // Stage 9 R-4: sign the canonical narrow message
        // (`executor-receipt-sig-v1:` || turn_hash || pre_state || post_state ||
        // timestamp), not the broader `receipt_hash()`. This keeps the
        // executor's claim recoverable by downstream verifiers that do not yet
        // understand the v2 receipt's auxiliary fields (routing directives,
        // derivation records, emitted events, finality). See
        // `TurnReceipt::canonical_executor_signed_message`.
        let msg = receipt.canonical_executor_signed_message();
        use ed25519_dalek::Signer;
        let sig = sk.sign(&msg);
        Some(sig.to_bytes().to_vec())
    }

    /// Set the current timestamp (used for expiration and precondition checks).
    ///
    /// P2-2: rejects backwards timestamp updates. The executor's clock must be
    /// monotonically non-decreasing; a stuck/backward clock allows expired
    /// turns to succeed and breaks `valid_until` enforcement. Backward-stepping
    /// `ts` values are silently ignored (no-op).
    pub fn set_timestamp(&mut self, ts: i64) {
        if ts >= self.current_timestamp {
            self.current_timestamp = ts;
        }
        // else: silently ignore (do not allow time to go backwards).
    }

    /// Get the per-agent last-known receipt hash, if any (P0-3 fix).
    ///
    /// Used by callers that need to construct a turn with the correct
    /// `previous_receipt_hash` value. Returns `None` if the agent has no
    /// committed turns on this executor.
    pub fn get_last_receipt_hash(&self, agent: &CellId) -> Option<[u8; 32]> {
        self.last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(agent)
            .copied()
    }

    /// Seed the receipt-chain head for an agent (for state recovery / loading).
    ///
    /// Use this when an executor is started against a ledger that already has
    /// history (e.g. after restart) so the receipt-chain check reflects the
    /// actual prior state. Without seeding, the first turn from an agent with
    /// pre-existing history would be rejected as `ReceiptChainMismatch`.
    pub fn set_last_receipt_hash(&self, agent: CellId, hash: [u8; 32]) {
        self.last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(agent, hash);
    }

    /// Clear the per-agent receipt-chain head (for tests and resets).
    pub fn reset_receipt_chain(&self) {
        self.last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clear();
    }

    /// Check whether a cell is frozen for migration (P0-4 fix).
    ///
    /// Returns `Err(TurnError::CellFrozen { cell })` if the cell is in
    /// `MigrationState::Frozen` or `AwaitingReceipt`; `Ok(())` otherwise.
    /// Called near the top of every turn-execution path that mutates state.
    fn check_not_frozen(&self, cell: &CellId) -> Result<(), TurnError> {
        if self
            .cell_migrations
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .is_frozen(cell)
        {
            Err(TurnError::CellFrozen { cell: *cell })
        } else {
            Ok(())
        }
    }

    /// Verify the agent's `previous_receipt_hash` matches the executor's
    /// stored head for that agent (P0-3 fix).
    fn check_previous_receipt_hash(
        &self,
        agent: &CellId,
        claimed: Option<[u8; 32]>,
    ) -> Result<(), TurnError> {
        let stored = self
            .last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(agent)
            .copied();
        if stored == claimed {
            Ok(())
        } else {
            Err(TurnError::ReceiptChainMismatch {
                expected: stored,
                got: claimed,
            })
        }
    }

    /// Record a receipt as the new chain-head for the agent.
    fn record_receipt_hash(&self, agent: CellId, receipt_hash: [u8; 32]) {
        self.last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(agent, receipt_hash);
    }

    /// Set the current block height (used for network preconditions).
    pub fn set_block_height(&mut self, height: u64) {
        self.block_height = height;
    }

    /// Set the block proposer cell (receives 50% of fees).
    ///
    /// When set, 50% of each turn's fee is credited to this cell's balance
    /// after successful execution. If the cell does not exist in the ledger at
    /// execution time, the proposer share is burned instead.
    pub fn set_proposer_cell(&mut self, cell_id: CellId) {
        self.proposer_cell = Some(cell_id);
    }

    /// Set the federation treasury cell (receives 30% of fees).
    ///
    /// When set, 30% of each turn's fee is credited to this cell's balance
    /// after successful execution. If the cell does not exist in the ledger at
    /// execution time, the treasury share is burned instead.
    pub fn set_treasury_cell(&mut self, cell_id: CellId) {
        self.treasury_cell = Some(cell_id);
    }

    /// Configure epoch-based computron minting to prevent deflationary deadlock.
    ///
    /// When set, the executor will mint new computrons to the treasury cell at
    /// epoch boundaries. Call [`apply_epoch_minting`](Self::apply_epoch_minting)
    /// at each block to trigger minting when appropriate.
    ///
    /// # Arguments
    ///
    /// * `minter` - The configured epoch minter with policy parameters.
    pub fn set_epoch_minter(&mut self, minter: crate::economics::EpochMinter) {
        self.epoch_minter = Some(std::cell::RefCell::new(minter));
    }

    /// Apply epoch-based minting if the current block height crosses an epoch boundary.
    ///
    /// Call this once per block (typically at block start, before processing turns).
    /// Returns `Some(MintResult)` if computrons were minted, `None` otherwise.
    ///
    /// This prevents the deflationary death spiral: since 20% of every fee is
    /// burned and no new supply is created, the system would eventually run out
    /// of computrons. Epoch minting provides controlled issuance to the treasury,
    /// which distributes via governance (staking rewards, grants, fee subsidies).
    pub fn apply_epoch_minting(
        &self,
        ledger: &mut pyana_cell::Ledger,
    ) -> Option<crate::economics::MintResult> {
        let minter_cell = self.epoch_minter.as_ref()?;
        let mut minter = minter_cell.borrow_mut();
        minter.maybe_mint(ledger, self.block_height)
    }

    /// Execute a conditional turn by first resolving its condition.
    ///
    /// This checks:
    /// 1. Whether the timeout has been exceeded (returns `TurnResult::Expired`)
    /// 2. Whether the proof satisfies the condition
    /// 3. If satisfied, executes the underlying turn normally
    ///
    /// No fee is charged if the turn expires or the condition is not met.
    pub fn execute_conditional(
        &self,
        conditional: &crate::conditional::ConditionalTurn,
        proof: &crate::conditional::ConditionProof,
        current_height: u64,
        trusted_roots: &[crate::conditional::TrustedRoot],
        max_root_age: u64,
        used_proof_hashes: &mut std::collections::HashSet<[u8; 32]>,
        ledger: &mut Ledger,
    ) -> TurnResult {
        // Check timeout.
        if current_height > conditional.timeout_height {
            return TurnResult::Expired;
        }

        // Resolve condition.
        match crate::conditional::resolve_condition(
            &conditional.condition,
            proof,
            current_height,
            conditional.timeout_height,
            trusted_roots,
            max_root_age,
            used_proof_hashes,
            &self.trusted_destination_keys,
        ) {
            crate::conditional::ConditionalResult::Resolved => {
                let result = self.execute(&conditional.turn, ledger);
                // On successful execution, refund the conditional deposit to the agent.
                if let TurnResult::Committed { .. } = &result {
                    if conditional.deposit_amount > 0 {
                        if let Some(cell) = ledger.get_mut(&conditional.turn.agent) {
                            cell.state.set_balance(cell.state.balance() + conditional.deposit_amount);
                        }
                    }
                }
                result
            }
            crate::conditional::ConditionalResult::Expired => TurnResult::Expired,
            crate::conditional::ConditionalResult::Pending => TurnResult::Pending,
            crate::conditional::ConditionalResult::InvalidProof(e) => TurnResult::Rejected {
                reason: TurnError::ConditionNotMet(e),
                at_action: vec![],
            },
        }
    }

    /// Set the trusted federation roots for cross-federation note bridging.
    ///
    /// Only portable note proofs whose source_root matches one of these roots
    /// will be accepted. Call this to configure which remote federations this
    /// executor trusts for bridge mints.
    pub fn set_trusted_federation_roots(&mut self, roots: Vec<AttestedRoot>) {
        self.trusted_federation_roots = roots;
    }

    /// Add a single trusted federation root.
    pub fn add_trusted_federation_root(&mut self, root: AttestedRoot) {
        self.trusted_federation_roots.push(root);
    }

    /// Set the local federation identity for cross-federation bridge verification.
    pub fn set_local_federation_id(&mut self, id: [u8; 32]) {
        self.local_federation_id = id;
    }

    /// Set the trusted destination federation keys for bridge receipt verification.
    ///
    /// These Ed25519 public keys are used during BridgeFinalize to verify that a
    /// receipt was signed by a legitimate destination federation.
    pub fn set_trusted_destination_keys(&mut self, keys: Vec<[u8; 32]>) {
        self.trusted_destination_keys = keys;
    }

    // ─── Unified Lace Aliases ──────────────────────────────────────────────
    //
    // In the unified blocklace model, a "federation" is a reference group (GroupId).
    // These aliases provide forward-compatible naming.

    /// Alias for [`set_trusted_federation_roots`](Self::set_trusted_federation_roots).
    /// In the unified lace model, "federation roots" are "group roots".
    pub fn set_trusted_group_roots(&mut self, roots: Vec<AttestedRoot>) {
        self.set_trusted_federation_roots(roots);
    }

    /// Alias for [`add_trusted_federation_root`](Self::add_trusted_federation_root).
    pub fn add_trusted_group_root(&mut self, root: AttestedRoot) {
        self.add_trusted_federation_root(root);
    }

    /// Alias for [`set_local_federation_id`](Self::set_local_federation_id).
    /// In the unified lace model, the "local federation ID" is the local group ID.
    pub fn set_local_group_id(&mut self, id: [u8; 32]) {
        self.set_local_federation_id(id);
    }

    /// Add a single trusted destination federation key.
    pub fn add_trusted_destination_key(&mut self, key: [u8; 32]) {
        self.trusted_destination_keys.push(key);
    }

    /// Set the revocation channel set for capability exercise checks.
    ///
    /// When present, the executor verifies that capabilities used via
    /// `ExerciseViaCapability` and delegation access checks are not gated
    /// by a tripped revocation channel.
    pub fn set_revocation_channels(&mut self, channels: RevocationChannelSet) {
        self.revocation_channels = Some(channels);
    }

    /// Set the program registry for custom cell program verification.
    ///
    /// When a sovereign cell has a `verification_key_hash` in its registration,
    /// proof-carrying turns are verified against the deployed program instead of
    /// the default `EffectVmAir`.
    pub fn set_program_registry(&mut self, registry: ProgramRegistry) {
        self.program_registry = registry;
    }

    /// Get a mutable reference to the program registry (for deploying programs).
    pub fn program_registry_mut(&mut self) -> &mut ProgramRegistry {
        &mut self.program_registry
    }

    /// Set the queue program registry for enqueue validation.
    ///
    /// When an `EnqueueMessage` effect targets a queue with a registered program,
    /// the executor validates the enqueue against the program's constraints before
    /// accepting the effect. Invalid enqueues are rejected.
    pub fn set_queue_program_registry(
        &mut self,
        registry: crate::queue_programs::QueueProgramRegistry,
    ) {
        self.queue_program_registry = registry;
    }

    /// Get a mutable reference to the queue program registry.
    pub fn queue_program_registry_mut(
        &mut self,
    ) -> &mut crate::queue_programs::QueueProgramRegistry {
        &mut self.queue_program_registry
    }

    /// Get a mutable reference to the factory registry (for deploying factories).
    pub fn factory_registry_mut(&mut self) -> std::cell::RefMut<'_, pyana_cell::FactoryRegistry> {
        self.factory_registry.borrow_mut()
    }

    /// Deploy a factory into the executor's registry.
    pub fn deploy_factory(&mut self, descriptor: pyana_cell::FactoryDescriptor) -> [u8; 32] {
        self.factory_registry.borrow_mut().deploy(descriptor)
    }

    /// TRUST-CRITICAL: This function bridges the TRUSTLESS layer (STARK proofs) into the
    /// executor. If compromised: forged sovereign state could be committed without valid proofs.
    /// However, this function is ALREADY close to trustless — it only verifies a proof and
    /// updates a commitment. The proof itself is independently verifiable.
    /// Future: expose proof verification as a standalone function that light clients can call
    /// directly, removing the executor from the trust path for sovereign cells entirely.
    ///
    /// Verify a STARK execution proof for a sovereign cell and update its commitment.
    ///
    /// This is the core of Phase 3: proof-carrying sovereign turns. The executor
    /// does ZERO state manipulation — it only:
    /// 1. Retrieves the stored commitment
    /// 2. Verifies the STARK proof (public inputs bind old -> new commitment + effects hash)
    /// 3. Updates the 32-byte commitment
    ///
    /// Public inputs layout (Effect VM, 7+ BabyBear elements):
    ///   [old_commit(1), new_commit(1), net_delta_mag(1), net_delta_sign(1),
    ///    effects_hash_lo(1), effects_hash_hi(1), custom_count(1),
    ///    ...custom_entries(8 per custom effect)]
    fn verify_and_commit_proof(
        &self,
        cell_id: &CellId,
        proof_bytes: &[u8],
        turn: &Turn,
        ledger: &mut Ledger,
    ) -> Result<(), TurnError> {
        use pyana_circuit::effect_vm;
        use pyana_circuit::field::BabyBear;
        use pyana_circuit::stark;

        // 1. Get stored commitment (check both legacy sovereign_commitments and registrations).
        let old_commitment = if let Some(c) = ledger.get_sovereign_commitment(cell_id) {
            *c
        } else if let Some(reg) = ledger.get_sovereign_registration(cell_id) {
            reg.commitment
        } else {
            return Err(TurnError::SovereignNotRegistered { cell: *cell_id });
        };

        // 2. Deserialize the STARK proof.
        let proof = stark::proof_from_bytes(proof_bytes)
            .map_err(|e| TurnError::InvalidExecutionProof(e))?;

        // 3. Get the new commitment from the turn.
        let new_commitment = turn.execution_proof_new_commitment.ok_or_else(|| {
            TurnError::InvalidExecutionProof(
                "execution_proof_new_commitment is required".to_string(),
            )
        })?;

        // 4. Reconstruct Effect VM public inputs (Stage 1 widened PI layout).
        //
        // OLD_COMMIT/NEW_COMMIT are 4 felts each, derived from the full 32-byte
        // canonical commitment via `commitment_to_4bb` (resolves
        // REVIEW[effect-vm-coord] / AUDIT P0-2: ~124-bit collision resistance,
        // replacing the prior 4-byte truncation).
        let old_commit_4 = Self::commitment_to_4bb(&old_commitment);
        let new_commit_4 = Self::commitment_to_4bb(&new_commitment);

        // 5. Compute effects hash using the circuit's Poseidon2-based hash
        // (Stage 1 widened to 4 felts).
        let vm_effects = Self::convert_turn_effects_to_vm(cell_id, turn);
        let effects_hash_4 = effect_vm::compute_effects_hash_4(&vm_effects);

        // 6. Compute balance delta from effects.
        let (delta_mag, delta_sign) = Self::compute_balance_delta_from_effects(cell_id, turn);

        // 7. Count custom effects.
        let custom_count = vm_effects
            .iter()
            .filter(|e| matches!(e, effect_vm::Effect::Custom { .. }))
            .count();

        // 8. Read per-cell `max_custom_effects` from the cell program
        // manifest. For now this comes from the sovereign registration's
        // optional field (Stage 1 added); falls back to the workspace
        // default if unset (legacy / hosted cells).
        let max_custom_effects = self.read_cell_max_custom_effects(cell_id, ledger);

        // 8b. Per-cell enforcement: the executor rejects turns whose
        // custom-effect count exceeds the cell's declared limit. The AIR's
        // sum-check (Group 7, Stage 1) makes the `PI[CUSTOM_EFFECT_COUNT]`
        // value algebraically binding; this executor check then enforces
        // the per-cell ceiling on top of that.
        if custom_count > max_custom_effects as usize {
            return Err(TurnError::InvalidExecutionProof(format!(
                "custom_count {} exceeds per-cell max_custom_effects {}",
                custom_count, max_custom_effects,
            )));
        }

        // Federation approved-handoffs root. Stage 1: empty sentinel; Stage 7
        // populates from federation state.
        let approved_handoffs_root: [BabyBear; 4] = self.read_approved_handoffs_root();

        // 9. Build the public inputs vector (Stage 1 Effect VM layout).
        let pi_len = effect_vm::pi::BASE_COUNT + custom_count * effect_vm::pi::CUSTOM_ENTRY_SIZE;
        let mut public_inputs: Vec<BabyBear> = vec![BabyBear::ZERO; pi_len];
        for i in 0..effect_vm::pi::OLD_COMMIT_LEN {
            public_inputs[effect_vm::pi::OLD_COMMIT_BASE + i] = old_commit_4[i];
        }
        for i in 0..effect_vm::pi::NEW_COMMIT_LEN {
            public_inputs[effect_vm::pi::NEW_COMMIT_BASE + i] = new_commit_4[i];
        }
        for i in 0..effect_vm::pi::EFFECTS_HASH_LEN {
            public_inputs[effect_vm::pi::EFFECTS_HASH_BASE + i] = effects_hash_4[i];
        }
        public_inputs[effect_vm::pi::INIT_BAL_LO] = BabyBear::ZERO; // pinned from trace
        public_inputs[effect_vm::pi::INIT_BAL_HI] = BabyBear::ZERO; // pinned from trace
        public_inputs[effect_vm::pi::FINAL_BAL_LO] = BabyBear::ZERO; // pinned from trace
        public_inputs[effect_vm::pi::FINAL_BAL_HI] = BabyBear::ZERO; // pinned from trace
        public_inputs[effect_vm::pi::NET_DELTA_MAG] = BabyBear::new(delta_mag);
        public_inputs[effect_vm::pi::NET_DELTA_SIGN] = BabyBear::new(delta_sign);
        public_inputs[effect_vm::pi::CURRENT_BLOCK_HEIGHT] =
            BabyBear::new((self.block_height & 0x7FFF_FFFF) as u32);
        public_inputs[effect_vm::pi::MAX_CUSTOM_EFFECTS] = BabyBear::new(max_custom_effects as u32);
        public_inputs[effect_vm::pi::CUSTOM_EFFECT_COUNT] = BabyBear::new(custom_count as u32);
        for i in 0..effect_vm::pi::APPROVED_HANDOFFS_LEN {
            public_inputs[effect_vm::pi::APPROVED_HANDOFFS_BASE + i] = approved_handoffs_root[i];
        }

        // Append custom proof entries (vk_hash + proof_commitment per custom effect).
        let mut custom_idx = 0;
        for effect in &vm_effects {
            if let effect_vm::Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } = effect
            {
                let base = effect_vm::pi::CUSTOM_PROOFS_BASE
                    + custom_idx * effect_vm::pi::CUSTOM_ENTRY_SIZE;
                for j in 0..4 {
                    public_inputs[base + j] = program_vk_hash[j];
                }
                for j in 0..4 {
                    public_inputs[base + 4 + j] = proof_commitment[j];
                }
                custom_idx += 1;
            }
        }

        // INIT/FINAL_BAL_* are sourced from the proof's PIs (the trace pins
        // them at boundaries and Group 6 binds them algebraically). We copy
        // them now so the PI matching loop below doesn't trip on zero.
        if proof.public_inputs.len() >= effect_vm::pi::BASE_COUNT {
            public_inputs[effect_vm::pi::INIT_BAL_LO] = BabyBear::new_canonical(
                proof.public_inputs[effect_vm::pi::INIT_BAL_LO],
            );
            public_inputs[effect_vm::pi::INIT_BAL_HI] = BabyBear::new_canonical(
                proof.public_inputs[effect_vm::pi::INIT_BAL_HI],
            );
            public_inputs[effect_vm::pi::FINAL_BAL_LO] = BabyBear::new_canonical(
                proof.public_inputs[effect_vm::pi::FINAL_BAL_LO],
            );
            public_inputs[effect_vm::pi::FINAL_BAL_HI] = BabyBear::new_canonical(
                proof.public_inputs[effect_vm::pi::FINAL_BAL_HI],
            );
        }

        // 9. Validate proof PI count and verify PI matching.
        let expected_pi_count = public_inputs.len();
        let vk_hash = self.get_cell_vk_hash(cell_id, ledger);
        let has_custom_program = vk_hash.is_some();

        // For the default EffectVmAir path, verify reconstructed PIs match the proof.
        // Custom programs have their own PI layout — skip this check for them.
        if !has_custom_program {
            if proof.public_inputs.len() < expected_pi_count {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "proof has {} public inputs, expected at least {}",
                    proof.public_inputs.len(),
                    expected_pi_count
                )));
            }

            for (i, expected_bb) in public_inputs.iter().enumerate() {
                let got = BabyBear::new_canonical(proof.public_inputs[i]);
                if got != *expected_bb {
                    // Stage 1: PI layout has 4-felt slots for OLD_COMMIT,
                    // NEW_COMMIT, EFFECTS_HASH; index ranges identify which.
                    if (effect_vm::pi::OLD_COMMIT_BASE
                        ..effect_vm::pi::OLD_COMMIT_BASE + effect_vm::pi::OLD_COMMIT_LEN)
                        .contains(&i)
                    {
                        return Err(TurnError::SovereignCommitmentMismatch {
                            cell: *cell_id,
                            expected: old_commitment,
                            got: new_commitment,
                        });
                    } else if (effect_vm::pi::NEW_COMMIT_BASE
                        ..effect_vm::pi::NEW_COMMIT_BASE + effect_vm::pi::NEW_COMMIT_LEN)
                        .contains(&i)
                    {
                        return Err(TurnError::InvalidExecutionProof(format!(
                            "new_commitment in proof does not match claimed value (felt {} of 4)",
                            i - effect_vm::pi::NEW_COMMIT_BASE,
                        )));
                    } else if (effect_vm::pi::EFFECTS_HASH_BASE
                        ..effect_vm::pi::EFFECTS_HASH_BASE + effect_vm::pi::EFFECTS_HASH_LEN)
                        .contains(&i)
                    {
                        return Err(TurnError::EffectsHashMismatch {
                            expected: Self::babybear_pair_to_bytes32(
                                effects_hash_4[0],
                                effects_hash_4[1],
                            ),
                            got: Self::babybear_pair_to_bytes32(
                                BabyBear::new_canonical(
                                    proof.public_inputs[effect_vm::pi::EFFECTS_HASH_BASE],
                                ),
                                BabyBear::new_canonical(
                                    proof.public_inputs[effect_vm::pi::EFFECTS_HASH_BASE + 1],
                                ),
                            ),
                        });
                    } else {
                        return Err(TurnError::InvalidExecutionProof(format!(
                            "public input mismatch at index {} (expected {:?}, got {:?})",
                            i, expected_bb, got
                        )));
                    }
                }
            }
        }

        // 11. Verify the STARK proof.
        if let Some(vk) = vk_hash {
            if let Some(program) = self.program_registry.get(&vk) {
                // Custom programs define their own PI layout. Extract PIs from
                // the proof itself (the program's verifier will check them).
                let custom_pis: Vec<BabyBear> = proof
                    .public_inputs
                    .iter()
                    .map(|&v| BabyBear::new_canonical(v))
                    .collect();
                program
                    .verify_transition(&custom_pis, proof_bytes)
                    .map_err(|e| TurnError::ProofVerificationFailed(e.to_string()))?;
            } else {
                return Err(TurnError::ProofVerificationFailed(format!(
                    "cell has verification_key_hash {:02x}{:02x}... but no matching program is deployed",
                    vk[0], vk[1]
                )));
            }
        } else {
            let air = pyana_circuit::EffectVmAir::new(proof.trace_len);
            stark::verify(&air, &proof, &public_inputs)
                .map_err(|e| TurnError::ProofVerificationFailed(e))?;
        }

        // 12. Verify custom program proofs (CellProgram dispatch).
        if let Some(custom_proofs) = turn.custom_program_proofs.as_ref() {
            let custom_commitments =
                pyana_circuit::extract_custom_proof_commitments(&public_inputs);
            if custom_commitments.len() != custom_proofs.len() {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "custom proof count mismatch: PI declares {}, turn provides {}",
                    custom_commitments.len(),
                    custom_proofs.len()
                )));
            }
            for (i, ((vk_hash_elems, proof_commit_elems), custom_proof)) in custom_commitments
                .iter()
                .zip(custom_proofs.iter())
                .enumerate()
            {
                let vk_hash_bytes = Self::babybear4_to_bytes16(vk_hash_elems);
                let actual_proof_hash = Self::hash_custom_proof(&custom_proof.proof_bytes);
                let expected_commit = Self::babybear4_to_bytes16(proof_commit_elems);
                if actual_proof_hash != expected_commit {
                    return Err(TurnError::CustomProofCommitmentMismatch {
                        index: i,
                        expected: expected_commit,
                        got: actual_proof_hash,
                    });
                }
                let full_vk_hash = Self::expand_vk_hash_16_to_32(&vk_hash_bytes);
                if let Some(program) = self.program_registry.get(&full_vk_hash) {
                    program
                        .verify_transition(
                            &custom_proof.public_inputs_babybear(),
                            &custom_proof.proof_bytes,
                        )
                        .map_err(|e| TurnError::CustomProgramVerificationFailed {
                            index: i,
                            program_vk: full_vk_hash,
                            reason: e.to_string(),
                        })?;
                } else {
                    return Err(TurnError::CustomProgramNotFound {
                        index: i,
                        vk_hash: full_vk_hash,
                    });
                }
            }
        } else {
            let custom_commitments =
                pyana_circuit::extract_custom_proof_commitments(&public_inputs);
            if !custom_commitments.is_empty() {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "Effect VM proof declares {} custom effects but turn provides no custom proofs",
                    custom_commitments.len()
                )));
            }
        }

        // 13. Update commitment. Try the legacy map first, then registrations.
        if ledger.is_sovereign(cell_id) {
            let _ = ledger.update_sovereign_commitment(cell_id, new_commitment);
        } else {
            let _ = ledger.update_sovereign_registration_commitment(
                cell_id,
                old_commitment,
                new_commitment,
                self.block_height,
            );
        }

        Ok(())
    }

    /// Read the per-cell `max_custom_effects` from the cell's program manifest.
    ///
    /// Per `DESIGN-max-custom-effects.md` §4. Falls back to
    /// [`pyana_circuit::effect_vm::pi::MAX_CUSTOM_EFFECTS_DEFAULT`] if the cell
    /// has no explicit declaration (hosted or legacy sovereign cells).
    ///
    /// Stage 1: looks at sovereign registration's `max_custom_effects` optional
    /// field (added in this stage). Stage 8 may move the source of truth into
    /// `cell::CellProgram::max_custom_effects` directly.
    fn read_cell_max_custom_effects(&self, cell_id: &CellId, ledger: &Ledger) -> u8 {
        if let Some(reg) = ledger.get_sovereign_registration(cell_id) {
            if let Some(m) = reg.max_custom_effects {
                return m;
            }
        }
        pyana_circuit::effect_vm::pi::MAX_CUSTOM_EFFECTS_DEFAULT
    }

    /// Read the federation-scoped `approved_handoffs_root` as 4 BabyBear felts.
    ///
    /// Stage 1: returns the empty-tree sentinel (`Commitment4::empty()`).
    /// Stage 7 populates this from federation state when CapTP runtime
    /// emitters land. Per `DESIGN-captp-integration.md` §4.2.
    fn read_approved_handoffs_root(&self) -> [pyana_circuit::field::BabyBear; 4] {
        [pyana_circuit::field::BabyBear::ZERO; 4]
    }

    /// Get the verification key hash for a sovereign cell, if one is set.
    ///
    /// Checks both the sovereign registration (which has an explicit `verification_key_hash`
    /// field) and the cell's `verification_key` (for hosted cells or legacy sovereign cells).
    fn get_cell_vk_hash(&self, cell_id: &CellId, ledger: &Ledger) -> Option<[u8; 32]> {
        // Check sovereign registration first (proof-carrying path).
        if let Some(reg) = ledger.get_sovereign_registration(cell_id) {
            if let Some(vk_hash) = reg.verification_key_hash {
                return Some(vk_hash);
            }
        }
        // Fallback: check if the cell itself has a verification_key with a hash.
        if let Some(cell) = ledger.get(cell_id) {
            if let Some(vk) = &cell.verification_key {
                return Some(vk.hash);
            }
        }
        None
    }

    /// Encode a 32-byte hash as 8 BabyBear field elements (4 bytes each, little-endian).
    fn bytes32_to_babybear(bytes: &[u8; 32]) -> Vec<pyana_circuit::field::BabyBear> {
        use pyana_circuit::field::BabyBear;
        let mut result = Vec::with_capacity(8);
        for chunk in bytes.chunks(4) {
            let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
            // Reduce mod BabyBear prime to ensure valid field element.
            result.push(BabyBear(val % pyana_circuit::field::BABYBEAR_P));
        }
        result
    }

    /// Decode 8 u32 values (from proof public_inputs) back into a 32-byte hash.
    fn babybear_slice_to_bytes32(values: &[u32]) -> [u8; 32] {
        let mut result = [0u8; 32];
        for (i, &val) in values.iter().take(8).enumerate() {
            result[i * 4..i * 4 + 4].copy_from_slice(&val.to_le_bytes());
        }
        result
    }

    /// Convert 4 BabyBear elements to a 16-byte array (for custom proof commitment matching).
    fn babybear4_to_bytes16(elems: &[pyana_circuit::field::BabyBear; 4]) -> [u8; 16] {
        let mut result = [0u8; 16];
        for (i, elem) in elems.iter().enumerate() {
            result[i * 4..i * 4 + 4].copy_from_slice(&elem.0.to_le_bytes());
        }
        result
    }

    /// Hash custom proof bytes to produce a 16-byte commitment (matching BabyBear[4]).
    fn hash_custom_proof(proof_bytes: &[u8]) -> [u8; 16] {
        let h = blake3::hash(proof_bytes);
        let bytes = h.as_bytes();
        let mut result = [0u8; 16];
        result.copy_from_slice(&bytes[..16]);
        result
    }

    /// Expand a 16-byte VK hash (from 4 BabyBear elements) to a 32-byte registry key.
    /// The upper 16 bytes are zero-padded (registry lookup uses the full 32 bytes).
    fn expand_vk_hash_16_to_32(short: &[u8; 16]) -> [u8; 32] {
        let mut result = [0u8; 32];
        result[..16].copy_from_slice(short);
        result
    }

    /// Decode a stored [u8; 32] commitment to a single BabyBear field element.
    ///
    /// The stored commitment encodes a Poseidon2 CellState commitment as a
    /// 32-byte BLAKE3-style canonical hash. See the cell crate's
    /// `compute_canonical_state_commitment` for the canonical encoding.
    ///
    /// STAGE 1 (resolves REVIEW[effect-vm-coord], P0-2 in AUDIT-turn-executor.md):
    /// the 4-byte truncation has been replaced with a 4-felt Poseidon2 form
    /// (~124-bit binding) via [`commitment_to_4bb`]. The legacy single-felt
    /// `commitment_to_babybear` retained here for backward-compat with
    /// callers that absorb commitments into Merkle leaves; it now derives
    /// the felt from the full 32-byte canonical commitment rather than a
    /// 4-byte truncation.
    pub fn commitment_to_babybear(bytes: &[u8; 32]) -> pyana_circuit::field::BabyBear {
        // Position 0 of the 4-felt form is the in-trace continuity binding.
        Self::commitment_to_4bb(bytes)[0]
    }

    /// Encode a 32-byte canonical state commitment as 4 BabyBear field
    /// elements (Stage 1 widening; ~124-bit collision resistance).
    ///
    /// Uses `pyana_commit::typed::canonical_32_to_felts_4`, which packs the
    /// 32 bytes into 8 BabyBears at 30 bits/limb (no truncation), then
    /// folds via two `hash_4_to_1` compressions to yield 4 felts.
    ///
    /// The 4 felts are the PI[OLD_COMMIT_BASE..+4] / PI[NEW_COMMIT_BASE..+4]
    /// values consumed by the Effect VM verifier. The verifier's PI matching
    /// loop ensures the proof's PI matches these felts byte-for-byte.
    pub fn commitment_to_4bb(bytes: &[u8; 32]) -> [pyana_circuit::field::BabyBear; 4] {
        pyana_commit::typed::canonical_32_to_felts_4(bytes)
    }

    /// Encode a BabyBear field element as a [u8; 32] stored commitment.
    ///
    /// Packs the u32 value into the first 4 bytes (LE), zeroes the rest.
    pub fn babybear_to_commitment(bb: pyana_circuit::field::BabyBear) -> [u8; 32] {
        let mut result = [0u8; 32];
        result[..4].copy_from_slice(&bb.0.to_le_bytes());
        result
    }

    /// Encode two BabyBear elements as a [u8; 32] for error reporting.
    fn babybear_pair_to_bytes32(
        lo: pyana_circuit::field::BabyBear,
        hi: pyana_circuit::field::BabyBear,
    ) -> [u8; 32] {
        let mut result = [0u8; 32];
        result[..4].copy_from_slice(&lo.0.to_le_bytes());
        result[4..8].copy_from_slice(&hi.0.to_le_bytes());
        result
    }

    /// Convert turn-level effects from the call forest into circuit-level Effect VM effects.
    ///
    /// Walks the call forest DFS and converts each effect targeting `cell_id` into the
    /// corresponding `effect_vm::Effect`. Effects not targeting this cell are skipped.
    fn convert_turn_effects_to_vm(
        cell_id: &CellId,
        turn: &Turn,
    ) -> Vec<pyana_circuit::effect_vm::Effect> {
        fn collect_effects(
            tree: &CallTree,
            cell_id: &CellId,
            vm_effects: &mut Vec<pyana_circuit::effect_vm::Effect>,
        ) {
            use pyana_circuit::effect_vm::Effect as VmEffect;
            use pyana_circuit::field::BabyBear;

            // REVIEW[effect-vm-coord]: Both helpers truncate 32-byte values to
            // 4 bytes (P1-2 in AUDIT-turn-executor.md). Many distinct effects
            // collapse to the same circuit-side identifier; the proof binds to
            // a coarse equivalence class rather than the specific effect.
            // The coordinated fix expands each per-effect PI slot (nullifier,
            // commitment, message_hash, pipeline_id, etc.) to 8 BabyBears via
            // `bytes32_to_babybear`, matching the executor's `compute_effects_hash`
            // which already hashes the full bytes. This is purely a circuit
            // PI-layout change on the runtime side, but the AIR's
            // domain-specific constraints over these slots must be widened in
            // tandem -- a single coordinated landing.
            fn hash_to_bb(h: &[u8; 32]) -> BabyBear {
                let val_u32 = u32::from_le_bytes([h[0], h[1], h[2], h[3]]);
                BabyBear::new(val_u32 % pyana_circuit::field::BABYBEAR_P)
            }

            fn field_element_to_bb(value: &[u8; 32]) -> BabyBear {
                let val_u32 = u32::from_le_bytes([value[0], value[1], value[2], value[3]]);
                BabyBear::new(val_u32 % pyana_circuit::field::BABYBEAR_P)
            }

            for effect in &tree.action.effects {
                match effect {
                    Effect::Transfer { from, to, amount } => {
                        if from == cell_id {
                            vm_effects.push(VmEffect::Transfer {
                                amount: *amount,
                                direction: 1,
                            });
                        } else if to == cell_id {
                            vm_effects.push(VmEffect::Transfer {
                                amount: *amount,
                                direction: 0,
                            });
                        }
                    }
                    Effect::SetField { cell, index, value } if cell == cell_id => {
                        vm_effects.push(VmEffect::SetField {
                            field_idx: *index as u32,
                            value: field_element_to_bb(value),
                        });
                    }
                    Effect::GrantCapability { to, cap, .. } if to == cell_id => {
                        let cap_hash = blake3::hash(&cap.slot.to_le_bytes());
                        vm_effects.push(VmEffect::GrantCapability {
                            cap_entry: hash_to_bb(cap_hash.as_bytes()),
                        });
                    }
                    Effect::NoteSpend {
                        nullifier, value, ..
                    } => {
                        vm_effects.push(VmEffect::NoteSpend {
                            nullifier: hash_to_bb(&nullifier.0),
                            value: *value,
                        });
                    }
                    Effect::NoteCreate {
                        commitment, value, ..
                    } => {
                        vm_effects.push(VmEffect::NoteCreate {
                            commitment: hash_to_bb(&commitment.0),
                            value: *value,
                        });
                    }
                    Effect::IncrementNonce { cell } if cell == cell_id => {
                        // Nonce increment is implicit in the VM (row-to-row).
                    }
                    Effect::QueueAllocate {
                        capacity,
                        program_vk: _,
                    } => {
                        // AllocateQueue: cost = capacity (1 computron per slot).
                        vm_effects.push(VmEffect::AllocateQueue {
                            capacity: *capacity as u32,
                            owner_quota_id: hash_to_bb(cell_id.as_bytes()),
                            cost_per_slot: 1,
                        });
                    }
                    Effect::QueueEnqueue {
                        queue,
                        message_hash,
                        deposit,
                    } => {
                        vm_effects.push(VmEffect::EnqueueMessage {
                            message_hash: hash_to_bb(message_hash),
                            deposit_amount: *deposit as u32,
                            sender_id: hash_to_bb(cell_id.as_bytes()),
                            queue_len: 0, // Actual length validated by executor; circuit uses hash chain.
                            program_vk: BabyBear::ZERO, // No program VK binding in basic enqueue.
                        });
                    }
                    Effect::QueueDequeue { queue } => {
                        // DequeueMessage: the expected_message_hash is the queue's head.
                        // The executor validates correctness; the circuit proves the hash chain.
                        // Use queue ID hash as a placeholder (actual message hash comes from state).
                        vm_effects.push(VmEffect::DequeueMessage {
                            expected_message_hash: hash_to_bb(queue.as_bytes()),
                            deposit_refund: 0, // Refund computed by executor at runtime.
                        });
                    }
                    Effect::QueueResize {
                        queue,
                        new_capacity,
                    } => {
                        vm_effects.push(VmEffect::ResizeQueue {
                            new_capacity: *new_capacity as u32,
                            queue_id: hash_to_bb(queue.as_bytes()),
                            cost_per_slot: 1,
                            old_capacity: 0, // Old capacity provided by executor at runtime.
                        });
                    }
                    Effect::QueueAtomicTx { operations } => {
                        // Compute net deposit: sum of enqueue deposits in the tx.
                        let mut net_deposit: u64 = 0;
                        for op in operations {
                            match op {
                                crate::action::QueueTxOp::Enqueue { deposit, .. } => {
                                    net_deposit += deposit;
                                }
                                crate::action::QueueTxOp::Dequeue { .. } => {
                                    // Refunds are runtime-computed; approximated as zero here.
                                }
                            }
                        }
                        // Build combined root hashes (binding the atomic transition).
                        let op_count = operations.len() as u32;
                        let tx_hash_input: Vec<u8> = operations
                            .iter()
                            .flat_map(|op| match op {
                                crate::action::QueueTxOp::Enqueue { message_hash, .. } => {
                                    message_hash.to_vec()
                                }
                                crate::action::QueueTxOp::Dequeue { queue } => {
                                    queue.as_bytes().to_vec()
                                }
                            })
                            .collect();
                        let tx_hash_bytes = blake3::hash(&tx_hash_input);
                        let tx_hash = hash_to_bb(tx_hash_bytes.as_bytes());
                        // Combined roots use cell_id field[4] as a stand-in.
                        let combined_root = hash_to_bb(cell_id.as_bytes());
                        vm_effects.push(VmEffect::AtomicQueueTx {
                            op_count,
                            tx_hash,
                            combined_old_root: combined_root,
                            combined_new_root: combined_root,
                            net_deposit: net_deposit as u32,
                        });
                    }
                    Effect::QueuePipelineStep {
                        pipeline_id,
                        source,
                        sinks,
                    } => {
                        let pipeline_bb = hash_to_bb(pipeline_id);
                        let source_root = hash_to_bb(source.as_bytes());
                        // Source new root = hash(source_old, message) — use a deterministic placeholder.
                        let msg_hash = hash_to_bb(pipeline_id);
                        let source_new =
                            pyana_circuit::poseidon2::hash_2_to_1(source_root, msg_hash);
                        let sink_root = if let Some(sink) = sinks.first() {
                            hash_to_bb(sink.as_bytes())
                        } else {
                            BabyBear::ZERO
                        };
                        let sink_new = pyana_circuit::poseidon2::hash_2_to_1(sink_root, msg_hash);
                        vm_effects.push(VmEffect::PipelineStep {
                            pipeline_id: pipeline_bb,
                            source_old_root: source_root,
                            source_new_root: source_new,
                            sink_new_root: sink_new,
                            message_hash: msg_hash,
                        });
                    }
                    // ====================================================
                    // Stage 1 (D): wire up the 7 runtime variants whose AIR
                    // counterparts already exist but were previously mapped
                    // to NoOp. The AIR enforces the per-effect arithmetic;
                    // the projection is no longer lossy for these.
                    // ====================================================
                    Effect::CreateObligation {
                        beneficiary,
                        stake_amount,
                        stake,
                        ..
                    } => {
                        // CreateObligation is emitted by the obligor; project
                        // when the cell is also the beneficiary (a self-bond)
                        // OR when the cell is a participant. The AIR variant
                        // currently treats this as a balance-debit + cap-root
                        // touch. We project for the executing cell.
                        let obligation_id_bytes = stake.0;
                        vm_effects.push(VmEffect::CreateObligation {
                            stake_amount: *stake_amount,
                            obligation_id: hash_to_bb(&obligation_id_bytes),
                            beneficiary_hash: hash_to_bb(beneficiary.as_bytes()),
                        });
                    }
                    Effect::FulfillObligation { obligation_id, .. } => {
                        vm_effects.push(VmEffect::FulfillObligation {
                            obligation_id: hash_to_bb(obligation_id),
                            // Stage 1: stake_return is not currently in the
                            // runtime variant; the AIR-side amount is wired
                            // by Stage 2's honesty pass once the obligation
                            // ledger is committed.
                            stake_return: 0,
                        });
                    }
                    Effect::SlashObligation { obligation_id } => {
                        vm_effects.push(VmEffect::SlashObligation {
                            obligation_id: hash_to_bb(obligation_id),
                            stake_amount: 0, // Stage 2 honesty pass
                            beneficiary_hash: hash_to_bb(cell_id.as_bytes()),
                        });
                    }
                    Effect::Seal {
                        pair_id,
                        ..
                    } => {
                        // Stage 1: the runtime variant doesn't carry an
                        // explicit field_idx; we use the low bits of
                        // pair_id as a placeholder. Stage 2 reworks the
                        // Seal/Unseal AIR to operate on sealed_field_mask
                        // rather than on a single field index.
                        vm_effects.push(VmEffect::Seal {
                            field_idx: (pair_id[0] as u32) & 0x7,
                        });
                    }
                    Effect::Unseal { sealed_box, .. } => {
                        let bytes = postcard::to_allocvec(sealed_box).unwrap_or_default();
                        let brand_hash = blake3::hash(&bytes);
                        let mut tag = [0u8; 32];
                        tag.copy_from_slice(brand_hash.as_bytes());
                        vm_effects.push(VmEffect::Unseal {
                            field_idx: (tag[0] as u32) & 0x7,
                            brand: hash_to_bb(&tag),
                        });
                    }
                    Effect::MakeSovereign { cell } if cell == cell_id => {
                        vm_effects.push(VmEffect::MakeSovereign);
                    }
                    Effect::CreateCellFromFactory {
                        factory_vk,
                        owner_pubkey,
                        ..
                    } => {
                        vm_effects.push(VmEffect::CreateCellFromFactory {
                            factory_vk: hash_to_bb(factory_vk),
                            child_vk_derived: hash_to_bb(owner_pubkey),
                        });
                    }

                    // ====================================================
                    // Stage 3 complete: the 22 runtime variants below all
                    // have real per-variant AIR coverage. Each projects to
                    // a real VmEffect with its own constraint shape
                    // (passthrough, balance debit/credit, or cap_root
                    // transition). See STAGE-3-AIR-PLAN.md for the per-
                    // variant rationale and EFFECT-VM-SHAPE-A.md for the
                    // master plan context.
                    // ====================================================
                    Effect::SetPermissions { cell, new_permissions } if cell == cell_id => {
                        // Stage 3: real AIR coverage. Permissions aren't in
                        // VM state; bind their hash into effects_hash.
                        let perm_bytes = postcard::to_allocvec(new_permissions)
                            .unwrap_or_default();
                        let perm_hash_bytes = blake3::hash(&perm_bytes);
                        vm_effects.push(VmEffect::SetPermissions {
                            permissions_hash: hash_to_bb(perm_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::SetVerificationKey { cell, new_vk } if cell == cell_id => {
                        // Stage 3: real AIR coverage. VK lives off-trace;
                        // bind its hash into effects_hash. None → 0.
                        let vk_hash = match new_vk {
                            Some(vk) => {
                                let bytes = postcard::to_allocvec(vk).unwrap_or_default();
                                let h = blake3::hash(&bytes);
                                hash_to_bb(h.as_bytes())
                            }
                            None => pyana_circuit::field::BabyBear::ZERO,
                        };
                        vm_effects.push(VmEffect::SetVerificationKey { vk_hash });
                    }
                    Effect::RevokeCapability { cell, slot } if cell == cell_id => {
                        // Stage 3: real AIR coverage. Mirrors GrantCapability.
                        // The slot's bytes are hashed and the result is mixed
                        // into capability_root deterministically by the AIR.
                        let slot_bytes = slot.to_le_bytes();
                        let slot_hash_bytes = blake3::hash(&slot_bytes);
                        vm_effects.push(VmEffect::RevokeCapability {
                            slot_hash: hash_to_bb(slot_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::CreateCell { public_key, token_id, balance } => {
                        // Stage 3: real AIR coverage. CreateCell rejects
                        // non-zero balance via executor, so the actor's
                        // balance doesn't change — passthrough is correct.
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(public_key);
                        hasher.update(token_id);
                        hasher.update(&balance.to_le_bytes());
                        let create_hash_bytes = hasher.finalize();
                        vm_effects.push(VmEffect::CreateCell {
                            create_hash: hash_to_bb(create_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::CreateSealPair { sealer_holder, unsealer_holder } => {
                        // Stage 3: real AIR coverage. Hash both holders into
                        // a single pair_hash bound via effects_hash.
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(sealer_holder.as_bytes());
                        hasher.update(unsealer_holder.as_bytes());
                        let pair_hash_bytes = hasher.finalize();
                        vm_effects.push(VmEffect::CreateSealPair {
                            pair_hash: hash_to_bb(pair_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::EmitEvent { cell, event } if cell == cell_id => {
                        // Stage 3: real AIR coverage. event_hash binds the
                        // topic + data into effects_hash; no state changes.
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(&event.topic);
                        for d in &event.data {
                            hasher.update(d);
                        }
                        let event_hash_bytes = hasher.finalize();
                        vm_effects.push(VmEffect::EmitEvent {
                            event_hash: hash_to_bb(event_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::SpawnWithDelegation { child_public_key, child_token_id, max_staleness } => {
                        // Stage 3: real AIR coverage. Passthrough — the
                        // child cell is its own entity; actor's state
                        // doesn't change.
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(child_public_key);
                        hasher.update(child_token_id);
                        hasher.update(&max_staleness.to_le_bytes());
                        let spawn_hash_bytes = hasher.finalize();
                        vm_effects.push(VmEffect::SpawnWithDelegation {
                            spawn_hash: hash_to_bb(spawn_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::RefreshDelegation => {
                        // Stage 3: real AIR coverage. No params on the
                        // runtime side; selector alone records intent.
                        vm_effects.push(VmEffect::RefreshDelegation);
                    }
                    Effect::RevokeDelegation { child } => {
                        // Stage 3: real AIR coverage. child_hash binds the
                        // target cell into effects_hash.
                        vm_effects.push(VmEffect::RevokeDelegation {
                            child_hash: hash_to_bb(child.as_bytes()),
                        });
                    }
                    Effect::IncrementNonce { cell } if cell == cell_id => {
                        // No AIR effect needed — nonce increments are implicit
                        // in the row-to-row continuity. Skip to avoid a NoOp.
                    }
                    Effect::BridgeMint { portable_proof } => {
                        // Stage 3: real AIR coverage. Balance credit by the
                        // proof's value field. mint_hash binds the proof's
                        // public-input shape (nullifier, root, dest fed,
                        // asset_type) so the prover commits to which bridge
                        // mint event was processed.
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(&portable_proof.nullifier);
                        // AttestedRoot is structured; serialize it for hashing.
                        let root_bytes = postcard::to_allocvec(&portable_proof.source_root)
                            .unwrap_or_default();
                        hasher.update(&root_bytes);
                        hasher.update(&portable_proof.destination_federation);
                        hasher.update(&portable_proof.asset_type.to_le_bytes());
                        let mint_hash_bytes = hasher.finalize();
                        let value_lo = pyana_circuit::field::BabyBear::new(
                            (portable_proof.value & ((1u64 << 30) - 1)) as u32,
                        );
                        vm_effects.push(VmEffect::BridgeMint {
                            value_lo,
                            mint_hash: hash_to_bb(mint_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::BridgeLock { nullifier, destination, value, asset_type, .. } => {
                        // Stage 3: real AIR coverage. Balance debit.
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(nullifier);
                        hasher.update(destination);
                        hasher.update(&asset_type.to_le_bytes());
                        let lock_hash_bytes = hasher.finalize();
                        let value_lo = pyana_circuit::field::BabyBear::new(
                            (*value & ((1u64 << 30) - 1)) as u32,
                        );
                        vm_effects.push(VmEffect::BridgeLock {
                            value_lo,
                            lock_hash: hash_to_bb(lock_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::BridgeFinalize { nullifier, receipt } => {
                        // Stage 3: passthrough. Mint vs lock outcome lives
                        // in the bridge state lookup (executor's job).
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(nullifier);
                        let receipt_bytes = postcard::to_allocvec(receipt)
                            .unwrap_or_default();
                        hasher.update(&receipt_bytes);
                        let finalize_hash_bytes = hasher.finalize();
                        vm_effects.push(VmEffect::BridgeFinalize {
                            finalize_hash: hash_to_bb(finalize_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::BridgeCancel { nullifier } => {
                        // Stage 3: real AIR coverage. Passthrough — bridge
                        // state lives off-trace; nullifier binds intent.
                        vm_effects.push(VmEffect::BridgeCancel {
                            nullifier_hash: hash_to_bb(nullifier),
                        });
                    }
                    Effect::Introduce { introducer, recipient, target, permissions } => {
                        // Stage 3: real AIR coverage. Passthrough from the
                        // introducer's POV; recipient-side cap_root update
                        // happens when this turn is replayed against the
                        // recipient cell (separate projection).
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(introducer.as_bytes());
                        hasher.update(recipient.as_bytes());
                        hasher.update(target.as_bytes());
                        let perm_byte: u8 = match permissions {
                            pyana_cell::AuthRequired::None => 0,
                            pyana_cell::AuthRequired::Signature => 1,
                            pyana_cell::AuthRequired::Proof => 2,
                            pyana_cell::AuthRequired::Either => 3,
                            pyana_cell::AuthRequired::Impossible => 4,
                        };
                        hasher.update(&[perm_byte]);
                        let intro_hash_bytes = hasher.finalize();
                        vm_effects.push(VmEffect::Introduce {
                            intro_hash: hash_to_bb(intro_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::PipelinedSend { target, action } => {
                        // Stage 3: real AIR coverage. The dispatching cell
                        // doesn't change state; bind the deferred
                        // dispatch into effects_hash.
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(&target.source_turn);
                        hasher.update(&target.output_slot.to_le_bytes());
                        hasher.update(&action.hash());
                        let send_hash_bytes = hasher.finalize();
                        vm_effects.push(VmEffect::PipelinedSend {
                            send_hash: hash_to_bb(send_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::CreateEscrow { cell, recipient, amount, condition, .. } if cell == cell_id => {
                        // Stage 3: real AIR coverage. Mirror NoteCreate's
                        // balance debit constraint shape.
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(recipient.as_bytes());
                        let cond_bytes = postcard::to_allocvec(condition)
                            .unwrap_or_default();
                        hasher.update(&cond_bytes);
                        let escrow_hash_bytes = hasher.finalize();
                        // Truncate amount to u32 for the field element.
                        let amount_lo = pyana_circuit::field::BabyBear::new(
                            (*amount & ((1u64 << 30) - 1)) as u32,
                        );
                        vm_effects.push(VmEffect::CreateEscrow {
                            amount_lo,
                            escrow_hash: hash_to_bb(escrow_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::ReleaseEscrow { escrow_id, .. } => {
                        // Stage 3: passthrough. Amount resolution requires
                        // escrow_id lookup in the ledger (out of AIR scope).
                        vm_effects.push(VmEffect::ReleaseEscrow {
                            escrow_id_hash: hash_to_bb(escrow_id),
                        });
                    }
                    Effect::RefundEscrow { escrow_id, .. } => {
                        // Stage 3: passthrough. Same shape as ReleaseEscrow.
                        vm_effects.push(VmEffect::RefundEscrow {
                            escrow_id_hash: hash_to_bb(escrow_id),
                        });
                    }
                    Effect::CreateCommittedEscrow {
                        creator_commitment,
                        recipient_commitment,
                        value_commitment,
                        condition_commitment,
                        ..
                    } => {
                        // Stage 3: passthrough. Value is hidden in a Pedersen
                        // commitment that the AIR can't open; the executor
                        // verifies the range proof separately.
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(creator_commitment);
                        hasher.update(recipient_commitment);
                        hasher.update(&value_commitment.0);
                        hasher.update(condition_commitment);
                        let commit_hash_bytes = hasher.finalize();
                        vm_effects.push(VmEffect::CreateCommittedEscrow {
                            commit_hash: hash_to_bb(commit_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::ReleaseCommittedEscrow { escrow_id, recipient, .. } => {
                        // Stage 3: passthrough. Amount + binding to claim_auth
                        // is verified separately by executor.
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(escrow_id);
                        hasher.update(recipient.as_bytes());
                        let commit_hash_bytes = hasher.finalize();
                        vm_effects.push(VmEffect::ReleaseCommittedEscrow {
                            commit_hash: hash_to_bb(commit_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::RefundCommittedEscrow { escrow_id, creator, .. } => {
                        // Stage 3: passthrough. Same shape with creator.
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(escrow_id);
                        hasher.update(creator.as_bytes());
                        let commit_hash_bytes = hasher.finalize();
                        vm_effects.push(VmEffect::RefundCommittedEscrow {
                            commit_hash: hash_to_bb(commit_hash_bytes.as_bytes()),
                        });
                    }
                    Effect::ExerciseViaCapability { cap_slot, inner_effects } => {
                        // Stage 3: real AIR coverage. From the actor's POV
                        // this is passthrough — the inner_effects act on
                        // the target cell. Bind (cap_slot, inner_effects)
                        // via effects_hash so the prover can't swap them.
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(&cap_slot.to_le_bytes());
                        for inner in inner_effects {
                            hasher.update(&inner.hash());
                        }
                        let exercise_hash_bytes = hasher.finalize();
                        vm_effects.push(VmEffect::ExerciseViaCapability {
                            exercise_hash: hash_to_bb(exercise_hash_bytes.as_bytes()),
                        });
                    }

                    // ────────────────────────────────────────────────────
                    // Stage 7 / P1.A: CapTP runtime effect projections.
                    // Each runtime variant maps to its AIR counterpart
                    // (selectors 14..17). The AIR params are bound into
                    // effects_hash via `compute_effects_hash`, so the
                    // prover commits to the specific CapTP operation.
                    // The richer Merkle-proof witnesses required to make
                    // the AIR non-tautological are added in P1.C.
                    // ────────────────────────────────────────────────────
                    Effect::ExportSturdyRef { swiss_number, target } if target == cell_id => {
                        // Project: AIR's ExportSturdyRef proves
                        //   swiss = hash(cell_id, hash(random_seed, counter))
                        // To keep the AIR constraint satisfiable from
                        // off-trace data, we project with the cell's
                        // current field[7] (export counter) and a
                        // random_seed value such that the AIR's swiss
                        // derivation matches the provided swiss_number.
                        // For now, we collapse: random_seed = first 4
                        // bytes of swiss_number; the executor will set
                        // aux[0] to whatever the AIR-side derivation
                        // would compute — the AIR self-consistency check
                        // is what's enforced. Permissions are not
                        // carried by the runtime variant, so we use
                        // ZERO (Stage 2 / P1.C tightens this to bind a
                        // real permissions mask via the swiss table).
                        let cell_id_bb = hash_to_bb(target.as_bytes());
                        let random_seed_bb = hash_to_bb(swiss_number);
                        // Counter would be read from cell.state.fields[7];
                        // 0 is safe here because convert_turn_effects_to_vm
                        // is static and the AIR only checks self-
                        // consistency of the derivation.
                        vm_effects.push(VmEffect::ExportSturdyRef {
                            cell_id: cell_id_bb,
                            permissions: BabyBear::ZERO,
                            random_seed: random_seed_bb,
                            export_counter: 0,
                        });
                    }
                    Effect::EnlivenRef { swiss_number, bearer } if bearer == cell_id => {
                        // Project: AIR's EnlivenRef proves swiss-table
                        // membership of the entry. The presenter is the
                        // bearer cell. P1.C will tighten this to a real
                        // Merkle membership proof against the target
                        // cell's swiss_table_root.
                        let swiss_bb = hash_to_bb(swiss_number);
                        let presenter_bb = hash_to_bb(bearer.as_bytes());
                        vm_effects.push(VmEffect::EnlivenRef {
                            swiss_number: swiss_bb,
                            presenter_id: presenter_bb,
                            expected_cell_id: presenter_bb,
                            expected_permissions: BabyBear::ZERO,
                        });
                    }
                    Effect::DropRef { ref_id } => {
                        // Project: AIR's DropRef proves refcount > 0 and
                        // decrements. The cell_id and holder_federation
                        // are bound; the AIR currently treats refcount
                        // as the cell's field[5]. We pass a non-zero
                        // refcount; the executor's apply_effect verifies
                        // the actual stored refcount.
                        let cell_id_bb = hash_to_bb(cell_id.as_bytes());
                        let ref_id_bb = hash_to_bb(ref_id);
                        vm_effects.push(VmEffect::DropRef {
                            cell_id: cell_id_bb,
                            holder_federation: ref_id_bb,
                            current_refcount: 1,
                        });
                    }
                    Effect::ValidateHandoff { cert_hash } => {
                        // Project: AIR's ValidateHandoff proves
                        // cert_hash ∈ approved_handoffs_root. P1.C
                        // tightens to a real Merkle membership proof.
                        // The recipient/introducer pubkeys are not in
                        // the minimal runtime variant; we collapse to
                        // ZERO (consume-on-use binding happens at the
                        // executor's apply_effect).
                        let cert_bb = hash_to_bb(cert_hash);
                        vm_effects.push(VmEffect::ValidateHandoff {
                            certificate_hash: cert_bb,
                            recipient_pk: BabyBear::ZERO,
                            introducer_pk: BabyBear::ZERO,
                            // Position 0 of the federation's approved
                            // handoffs root; matches the verifier's PI
                            // read in `read_approved_handoffs_root`.
                            approved_set_root: BabyBear::ZERO,
                        });
                    }

                    _ => {
                        // Effects not targeting `cell_id` or arms covered by
                        // explicit guards above (e.g., a cross-cell effect
                        // whose other end isn't us) are silently skipped —
                        // they're not part of this cell's proof.
                    }
                }
            }
            for child in &tree.children {
                collect_effects(child, cell_id, vm_effects);
            }
        }

        // Stage 3 complete: push_pending_shim was the temporary scaffolding
        // for the 22 variants without dedicated AIR coverage. All 22 now
        // have real per-variant AIR variants, so the shim is removed.
        // The `effect-vm-pending-shim` feature flag is no longer used.

        let mut vm_effects = Vec::new();
        for root in &turn.call_forest.roots {
            collect_effects(root, cell_id, &mut vm_effects);
        }

        // Must have at least one effect for the VM.
        if vm_effects.is_empty() {
            vm_effects.push(pyana_circuit::effect_vm::Effect::NoOp);
        }
        vm_effects
    }

    /// Compute the balance delta (magnitude, sign) from the turn's effects for a cell.
    ///
    /// Returns (magnitude_u32, sign_u32) where sign=0 means positive/incoming,
    /// sign=1 means negative/outgoing.
    fn compute_balance_delta_from_effects(cell_id: &CellId, turn: &Turn) -> (u32, u32) {
        fn walk_delta(tree: &CallTree, cell_id: &CellId, net: &mut i64) {
            for effect in &tree.action.effects {
                match effect {
                    Effect::Transfer { from, to, amount } => {
                        if from == cell_id {
                            *net -= *amount as i64;
                        }
                        if to == cell_id {
                            *net += *amount as i64;
                        }
                    }
                    Effect::NoteSpend { value, .. } => {
                        *net += *value as i64;
                    }
                    Effect::NoteCreate { value, .. } => {
                        *net -= *value as i64;
                    }
                    // Stage 3 honest projections: AIR enforces balance changes
                    // for these variants, so they must contribute to net_delta
                    // for the PI-to-trace consistency constraint to hold.
                    Effect::CreateEscrow { cell, amount, .. } => {
                        if cell == cell_id {
                            *net -= *amount as i64;
                        }
                    }
                    Effect::BridgeLock { value, .. } => {
                        // BridgeLock is always emitted by the actor cell, so
                        // it always debits the actor's balance. (Unlike
                        // Transfer, there's no separate `from` field — the
                        // turn's agent is the locker.)
                        *net -= *value as i64;
                    }
                    Effect::BridgeMint { portable_proof } => {
                        // BridgeMint credits the actor's balance with the
                        // portable proof's declared value.
                        *net += portable_proof.value as i64;
                    }
                    _ => {}
                }
            }
            for child in &tree.children {
                walk_delta(child, cell_id, net);
            }
        }

        let mut net_delta: i64 = 0;
        for root in &turn.call_forest.roots {
            walk_delta(root, cell_id, &mut net_delta);
        }

        if net_delta < 0 {
            ((-net_delta) as u32, 1u32)
        } else {
            (net_delta as u32, 0u32)
        }
    }

    /// Compute a BLAKE3 hash of the turn's effects for proof-carrying verification.
    ///
    /// This hashes all effects in the call forest deterministically (DFS order).
    fn compute_turn_effects_hash(&self, turn: &Turn) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-sovereign-effects-v1:");
        for root in &turn.call_forest.roots {
            Self::hash_tree_effects(root, &mut hasher);
        }
        *hasher.finalize().as_bytes()
    }

    /// Recursively hash effects from a call tree into a hasher.
    fn hash_tree_effects(tree: &CallTree, hasher: &mut blake3::Hasher) {
        for effect in &tree.action.effects {
            hasher.update(&effect.hash());
        }
        for child in &tree.children {
            Self::hash_tree_effects(child, hasher);
        }
    }

    /// Execute a turn against a ledger, returning the result.
    ///
    /// This is the main entry point. The executor:
    /// 1. Validates turn-level conditions (expiration, nonce, fee).
    /// 2. Creates a journal for efficient rollback (no full ledger clone).
    /// 3. Walks the call forest depth-first.
    /// 4. For each action: checks preconditions, verifies authorization, applies effects.
    /// 5. Meters computrons at each step.
    /// 6. If any action fails: replays journal in reverse to roll back ALL effects.
    /// 7. If successful: produces a TurnReceipt with Merkle hashes.
    /// TRUST-CRITICAL: This function is the sole entry point for all ledger state mutations.
    /// If compromised: arbitrary state changes bypass authorization, preconditions, and fee metering.
    /// The federation's replicated execution ensures all members execute identically; divergence
    /// triggers consensus failure and halts the federation.
    /// Future: once Effect VM covers all effect types, every turn will carry a STARK proof,
    /// making this function a thin verify-and-commit wrapper (trustless).
    pub fn execute(&self, turn: &Turn, ledger: &mut Ledger) -> TurnResult {
        // Phase 0: basic validation.
        if turn.call_forest.is_empty() {
            return TurnResult::Rejected {
                reason: TurnError::EmptyForest,
                at_action: vec![],
            };
        }

        // Check expiration.
        if let Some(valid_until) = turn.valid_until {
            if self.current_timestamp > valid_until {
                return TurnResult::Rejected {
                    reason: TurnError::Expired {
                        valid_until,
                        now: self.current_timestamp,
                    },
                    at_action: vec![],
                };
            }
        }

        // Check agent cell exists.
        let agent_cell = match ledger.get(&turn.agent) {
            Some(cell) => cell,
            None => {
                return TurnResult::Rejected {
                    reason: TurnError::CellNotFound { id: turn.agent },
                    at_action: vec![],
                };
            }
        };

        // Check nonce.
        if agent_cell.state.nonce() != turn.nonce {
            return TurnResult::Rejected {
                reason: TurnError::NonceReplay {
                    expected: agent_cell.state.nonce(),
                    got: turn.nonce,
                },
                at_action: vec![],
            };
        }

        // Check fee coverage (agent must have enough balance for the fee).
        if agent_cell.state.balance() < turn.fee {
            return TurnResult::Rejected {
                reason: TurnError::InsufficientBalance {
                    cell: turn.agent,
                    required: turn.fee,
                    available: agent_cell.state.balance(),
                },
                at_action: vec![],
            };
        }

        // P0-4: Reject turns whose agent cell is frozen for migration. A frozen
        // cell may not initiate any turn.
        if let Err(e) = self.check_not_frozen(&turn.agent) {
            return TurnResult::Rejected {
                reason: e,
                at_action: vec![],
            };
        }
        // Also reject if any cell touched in the call-forest write set is
        // frozen. Per-effect freezing checks are also applied inside
        // `apply_effect` as defence in depth.
        {
            let (_read_set, write_set) = crate::conflict::extract_access_sets(turn);
            for cell_id in &write_set {
                if let Err(e) = self.check_not_frozen(cell_id) {
                    return TurnResult::Rejected {
                        reason: e,
                        at_action: vec![],
                    };
                }
            }
        }

        // P0-3: Receipt-chain self-binding. The agent's claimed
        // `previous_receipt_hash` must match the executor's stored head for
        // this agent. Genesis turns (the agent's first) must use `None`.
        //
        // REVIEW[wallet-coord]: AUDIT-wallet.md P3-6 reports that
        // `build_authorized_turn`, `allocate_queue`, `enqueue_message`,
        // `dequeue_message`, and `atomic_queue_tx` all hardcode
        // `previous_receipt_hash: None`. After this fix, every non-first turn
        // from those paths will be rejected with `ReceiptChainMismatch`. The
        // wallet must be updated to plumb the prior receipt hash (track per
        // agent, populate on build, advance on commit). This check should NOT
        // be relaxed; the wallet is the side that needs to catch up.
        if let Err(e) = self.check_previous_receipt_hash(&turn.agent, turn.previous_receipt_hash) {
            return TurnResult::Rejected {
                reason: e,
                at_action: vec![],
            };
        }

        // =====================================================================
        // BUDGET GATE: Check silo's bounded-counter slice (Stingray).
        // BEFORE Phase 1 — if the silo's budget slice cannot cover the turn fee,
        // reject without charging the agent (pre-flight check). The budget gate is
        // a silo-level resource limit: exhaustion is not the agent's fault.
        // On subsequent forest failure (Phase 2), the debit is refunded (fast unlock).
        // =====================================================================
        let budget_debit_digest = if let Some(gate_cell) = &self.budget_gate {
            let turn_hash = turn.hash();
            let mut gate = gate_cell.lock().unwrap();
            match gate.try_debit(turn.fee, &turn_hash) {
                Ok(digest) => Some((digest, turn.fee)),
                Err(remaining) => {
                    return TurnResult::Rejected {
                        reason: TurnError::BudgetExhausted {
                            silo_id: gate.silo_id,
                            requested: turn.fee,
                            remaining,
                        },
                        at_action: vec![],
                    };
                }
            }
        } else {
            None
        };

        // Compute pre-state hash before any mutations.
        let pre_state_hash = ledger.root();

        // =====================================================================
        // PHASE 1: Commit fee + nonce (NEVER rolled back).
        // This prevents DoS via expensive-but-failing turns that never pay.
        // =====================================================================
        {
            let agent = ledger.get_mut(&turn.agent).unwrap();
            agent.state.set_balance(agent.state.balance() - turn.fee);
            agent.state.increment_nonce();
        }

        // =====================================================================
        // PHASE 3: PROOF-CARRYING SOVEREIGN TURN (fastest path)
        // When execution_proof is present, the executor does ZERO state
        // manipulation. It verifies the STARK proof and updates one 32-byte
        // commitment. This makes sovereign cells scalable — constant work
        // regardless of internal state complexity.
        // =====================================================================
        if let Some(proof_bytes) = &turn.execution_proof {
            let cell_id = match &turn.execution_proof_cell {
                Some(id) => *id,
                None => {
                    // Refund budget debit if we short-circuit.
                    if let (Some(gate_cell), Some((digest, fee))) =
                        (&self.budget_gate, &budget_debit_digest)
                    {
                        gate_cell.lock().unwrap().fast_unlock(*fee, digest);
                    }
                    return TurnResult::Rejected {
                        reason: TurnError::InvalidExecutionProof(
                            "execution_proof present but execution_proof_cell is None".to_string(),
                        ),
                        at_action: vec![],
                    };
                }
            };

            // Check that the cell is sovereign (either in sovereign_commitments or sovereign_registrations).
            if !ledger.is_sovereign(&cell_id) && !ledger.is_sovereign_registered(&cell_id) {
                if let (Some(gate_cell), Some((digest, fee))) =
                    (&self.budget_gate, &budget_debit_digest)
                {
                    gate_cell.lock().unwrap().fast_unlock(*fee, digest);
                }
                return TurnResult::Rejected {
                    reason: TurnError::ProofCarryingRequiresSovereign { cell: cell_id },
                    at_action: vec![],
                };
            }

            match self.verify_and_commit_proof(&cell_id, proof_bytes, turn, ledger) {
                Ok(()) => {
                    // Budget gate: commit the debit after successful proof verification.
                    if let (Some(gate_cell), Some((digest, _fee))) =
                        (&self.budget_gate, &budget_debit_digest)
                    {
                        gate_cell.lock().unwrap().commit_debit(digest);
                    }

                    let post_state_hash = ledger.root();
                    let turn_hash = turn.hash();
                    let forest_hash = turn.call_forest.compute_hash();

                    // Proof-carrying turns use a minimal receipt (zero computrons,
                    // zero effects enumeration — the proof IS the validation).
                    let effects_hash = self.compute_effects_hash(&[]);

                    let mut receipt = TurnReceipt {
                        turn_hash,
                        forest_hash,
                        pre_state_hash,
                        post_state_hash,
                        timestamp: self.current_timestamp,
                        effects_hash,
                        computrons_used: 0,
                        action_count: 0,
                        previous_receipt_hash: turn.previous_receipt_hash,
                        agent: turn.agent,
                        federation_id: self.local_federation_id,
                        routing_directives: vec![],
                        introduction_exports: vec![],
                        derivation_records: vec![],
                        emitted_events: vec![],
                        executor_signature: None,
                        finality: crate::turn::Finality::Final,
                    };
                    // R-4: sign the receipt over its canonical hash if the
                    // executor has been configured with a signing key.
                    receipt.executor_signature = self.maybe_sign_receipt(&receipt);

                    // Fee distribution (same as normal path).
                    let proposer_share = turn.fee / 2;
                    let treasury_share = turn.fee * 3 / 10;
                    if let Some(proposer_id) = &self.proposer_cell {
                        if let Some(proposer) = ledger.get_mut(proposer_id) {
                            proposer.state.set_balance(proposer.state.balance() + proposer_share);
                        }
                    }
                    if let Some(treasury_id) = &self.treasury_cell {
                        if let Some(treasury) = ledger.get_mut(treasury_id) {
                            treasury.state.set_balance(treasury.state.balance() + treasury_share);
                        }
                    }

                    let mut delta = pyana_cell::LedgerDelta::new();
                    let mut agent_delta = pyana_cell::CellStateDelta::empty();
                    agent_delta.balance_change = -(turn.fee as i64);
                    agent_delta.nonce_increment = true;
                    delta.updated.push((turn.agent, agent_delta));

                    // P0-3: record the new chain-head for this agent.
                    self.record_receipt_hash(turn.agent, receipt.receipt_hash());

                    return TurnResult::Committed {
                        ledger_delta: delta,
                        receipt,
                        computrons_used: 0,
                    };
                }
                Err(err) => {
                    // Refund budget debit on proof verification failure.
                    if let (Some(gate_cell), Some((digest, fee))) =
                        (&self.budget_gate, &budget_debit_digest)
                    {
                        gate_cell.lock().unwrap().fast_unlock(*fee, digest);
                    }
                    return TurnResult::Rejected {
                        reason: err,
                        at_action: vec![],
                    };
                }
            }
        }

        // =====================================================================
        // SOVEREIGN CELL WITNESS INJECTION
        // Validate witnesses for sovereign cells referenced in this turn and
        // temporarily inject them into the ledger so the executor can operate
        // on them as if they were hosted. After execution, new commitments are
        // computed and the cells are removed from the hosted store.
        // =====================================================================
        let mut sovereign_cell_ids: Vec<CellId> = Vec::new();
        for (cell_id, witness) in &turn.sovereign_witnesses {
            // Verify the cell is actually sovereign in the ledger.
            let stored_commitment = match ledger.get_sovereign_commitment(cell_id) {
                Some(c) => *c,
                None => {
                    return TurnResult::Rejected {
                        reason: TurnError::InvalidEffect {
                            reason: format!(
                                "sovereign witness provided for non-sovereign cell {}",
                                cell_id
                            ),
                        },
                        at_action: vec![],
                    };
                }
            };
            // Verify the witness state_proof matches the cell's state_commitment.
            let computed_commitment = witness.cell_state.state_commitment();
            if witness.state_proof != computed_commitment {
                return TurnResult::Rejected {
                    reason: TurnError::SovereignCommitmentMismatch {
                        cell: *cell_id,
                        expected: computed_commitment,
                        got: witness.state_proof,
                    },
                    at_action: vec![],
                };
            }
            // Verify the computed commitment matches the stored one.
            if computed_commitment != stored_commitment {
                return TurnResult::Rejected {
                    reason: TurnError::SovereignCommitmentMismatch {
                        cell: *cell_id,
                        expected: stored_commitment,
                        got: computed_commitment,
                    },
                    at_action: vec![],
                };
            }
            // Verify the witness cell ID matches.
            if witness.cell_state.id() != *cell_id {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!(
                            "sovereign witness cell ID mismatch: expected {}, got {}",
                            cell_id, witness.cell_state.id()
                        ),
                    },
                    at_action: vec![],
                };
            }
            // Temporarily inject the witnessed cell into the ledger for execution.
            // If the cell already exists in the hosted table (e.g., because the
            // sovereign cell IS the agent and was looked up for fee/nonce), replace
            // it with the witnessed state (which is authoritative after commitment check).
            if ledger.get(cell_id).is_some() {
                // Cell already in hosted table (agent = sovereign cell case).
                // Replace with witnessed state to ensure executor operates on correct state.
                if let Some(existing) = ledger.get_mut(cell_id) {
                    *existing = witness.cell_state.clone();
                }
            } else if let Err(_) = ledger.insert_cell(witness.cell_state.clone()) {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!("failed to inject sovereign witness for cell {}", cell_id),
                    },
                    at_action: vec![],
                };
            }
            sovereign_cell_ids.push(*cell_id);
        }

        // =====================================================================
        // PHASE 2: Execute call forest (rolled back on failure).
        // The journal only records forest effects — fee/nonce are already final.
        // =====================================================================
        let mut journal = LedgerJournal::with_capacity(16);
        let mut computrons_used: u64 = 0;
        let mut all_effects_hashes: Vec<[u8; 32]> = Vec::new();
        let mut excess: i64 = 0; // Mina-style excess: must be zero at turn end.

        for (root_idx, root_tree) in turn.call_forest.roots.iter().enumerate() {
            let result = self.execute_tree(
                root_tree,
                ledger,
                &turn.agent,
                // Top-level: agent owns all its capabilities. This value propagates
                // through Inherit and gates child cross-cell targeting (line ~738),
                // but chain-walking (ParentsOwn vs None) is not yet implemented.
                DelegationMode::ParentsOwn,
                &mut computrons_used,
                turn.fee,
                &mut all_effects_hashes,
                vec![root_idx],
                &mut journal,
                &mut excess,
                turn.nonce,
            );

            if let Err((error, path)) = result {
                // Rollback: replay journal in reverse to restore ledger.
                // Also removes any obligation/escrow/nullifier insertions from
                // the executor's in-memory maps (prevents phantom record attacks).
                journal.rollback(
                    ledger,
                    &self.obligations,
                    &self.escrows,
                    &self.bridged_nullifiers,
                    &self.committed_escrows,
                    &self.committed_escrow_amounts,
                );
                // Remove temporarily-injected sovereign cells on rollback.
                for cell_id in &sovereign_cell_ids {
                    ledger.remove(cell_id);
                }
                // Fast unlock: refund the budget debit on turn failure.
                if let (Some(gate_cell), Some((digest, fee))) =
                    (&self.budget_gate, &budget_debit_digest)
                {
                    gate_cell.lock().unwrap().fast_unlock(*fee, digest);
                }
                return TurnResult::Rejected {
                    reason: error,
                    at_action: path,
                };
            }
        }

        // Check total cost against fee.
        if computrons_used > turn.fee {
            journal.rollback(
                ledger,
                &self.obligations,
                &self.escrows,
                &self.bridged_nullifiers,
                &self.committed_escrows,
                &self.committed_escrow_amounts,
            );
            for cell_id in &sovereign_cell_ids {
                ledger.remove(cell_id);
            }
            if let (Some(gate_cell), Some((digest, fee))) =
                (&self.budget_gate, &budget_debit_digest)
            {
                gate_cell.lock().unwrap().fast_unlock(*fee, digest);
            }
            return TurnResult::Rejected {
                reason: TurnError::BudgetExceeded {
                    limit: turn.fee,
                    used: computrons_used,
                },
                at_action: vec![],
            };
        }

        // Check note conservation: for each asset type, sum of spent values must
        // equal sum of created values. This is checked independently of the cell
        // balance excess (notes are a separate value domain).
        if let Err(error) = self.check_note_conservation(turn) {
            journal.rollback(
                ledger,
                &self.obligations,
                &self.escrows,
                &self.bridged_nullifiers,
                &self.committed_escrows,
                &self.committed_escrow_amounts,
            );
            for cell_id in &sovereign_cell_ids {
                ledger.remove(cell_id);
            }
            if let (Some(gate_cell), Some((digest, fee))) =
                (&self.budget_gate, &budget_debit_digest)
            {
                gate_cell.lock().unwrap().fast_unlock(*fee, digest);
            }
            return TurnResult::Rejected {
                reason: TurnError::NoteConservationViolation {
                    asset_type: error.0,
                    inputs: error.1,
                    outputs: error.2,
                },
                at_action: vec![],
            };
        }

        // Check excess conservation law: must be zero at turn end.
        if excess != 0 {
            journal.rollback(
                ledger,
                &self.obligations,
                &self.escrows,
                &self.bridged_nullifiers,
                &self.committed_escrows,
                &self.committed_escrow_amounts,
            );
            for cell_id in &sovereign_cell_ids {
                ledger.remove(cell_id);
            }
            if let (Some(gate_cell), Some((digest, fee))) =
                (&self.budget_gate, &budget_debit_digest)
            {
                gate_cell.lock().unwrap().fast_unlock(*fee, digest);
            }
            return TurnResult::Rejected {
                reason: TurnError::ExcessNotZero { excess },
                at_action: vec![],
            };
        }

        // =====================================================================
        // SOVEREIGN CELL POST-EXECUTION: Compute new commitments and remove
        // the temporarily-injected cells from the hosted store.
        // The federation stores only the updated 32-byte commitment.
        // =====================================================================
        for cell_id in &sovereign_cell_ids {
            if let Some(cell) = ledger.remove(cell_id) {
                let new_commitment = cell.state_commitment();
                // Update the sovereign commitment in the ledger.
                let _ = ledger.update_sovereign_commitment(cell_id, new_commitment);
            }
        }

        // =====================================================================
        // BUDGET GATE: Commit the debit after successful execution.
        // The tentative debit is now permanent — it can no longer be refunded.
        // =====================================================================
        if let (Some(gate_cell), Some((digest, _fee))) = (&self.budget_gate, &budget_debit_digest) {
            gate_cell.lock().unwrap().commit_debit(digest);
        }

        // =====================================================================
        // PHASE 3: Fee distribution (50% proposer / 30% treasury / 20% burned).
        // Only executed after successful forest execution. If neither proposer
        // nor treasury is configured, all fees are burned (backward compatible).
        // =====================================================================
        let proposer_share = turn.fee / 2; // 50%
        let treasury_share = turn.fee * 3 / 10; // 30%
        // burned = fee - proposer_share - treasury_share (the remaining 20%)

        if let Some(proposer_id) = &self.proposer_cell {
            if let Some(proposer) = ledger.get_mut(proposer_id) {
                proposer.state.set_balance(proposer.state.balance() + proposer_share);
            }
            // If proposer cell doesn't exist in ledger, share is burned.
        }

        if let Some(treasury_id) = &self.treasury_cell {
            if let Some(treasury) = ledger.get_mut(treasury_id) {
                treasury.state.set_balance(treasury.state.balance() + treasury_share);
            }
            // If treasury cell doesn't exist in ledger, share is burned.
        }

        // Phase 4: Compute receipt.
        let post_state_hash = ledger.root();
        let effects_hash = self.compute_effects_hash(&all_effects_hashes);

        // Compute turn hash.
        let turn_hash = turn.hash();
        let forest_hash = turn.call_forest.compute_hash();

        // Build ledger delta from the journal, Phase 1 (fee + nonce), and Phase 3 (distribution).
        let delta = Self::compute_delta_from_journal_with_fee(
            &journal,
            ledger,
            &turn.agent,
            turn.fee,
            self.proposer_cell.as_ref(),
            self.treasury_cell.as_ref(),
        );

        let mut receipt = TurnReceipt {
            turn_hash,
            forest_hash,
            pre_state_hash,
            post_state_hash,
            timestamp: self.current_timestamp,
            effects_hash,
            computrons_used,
            action_count: turn.call_forest.action_count(),
            previous_receipt_hash: turn.previous_receipt_hash,
            agent: turn.agent,
            federation_id: self.local_federation_id,
            routing_directives: Self::collect_routing_directives(
                &turn.call_forest,
                &turn_hash,
                self.block_height,
                self.max_introduction_lifetime,
            ),
            introduction_exports: Self::collect_introduction_exports(
                &turn.call_forest,
                &turn_hash,
                self.block_height,
                self.max_introduction_lifetime,
            ),
            derivation_records: Self::collect_derivation_records(
                &turn.call_forest,
                self.current_timestamp as u64,
            ),
            emitted_events: Self::collect_emitted_events(&journal),
            executor_signature: None,
            finality: crate::turn::Finality::Final,
        };
        // R-4: sign the receipt over its canonical hash if the executor has
        // been configured with a signing key (`with_executor_signing_key`).
        receipt.executor_signature = self.maybe_sign_receipt(&receipt);

        // P0-3: record the new chain-head for this agent.
        self.record_receipt_hash(turn.agent, receipt.receipt_hash());

        TurnResult::Committed {
            ledger_delta: delta,
            receipt,
            computrons_used,
        }
    }

    // -----------------------------------------------------------------------
    // WitnessedReceipt v1 capture hook
    // -----------------------------------------------------------------------
    //
    // The canonical Effect-VM prove site today lives outside this crate
    // (`node/src/mcp.rs::generate_effect_vm_proof`). That site holds the
    // trace + public_inputs + proof_bytes together — exactly the inputs
    // a WitnessedReceipt needs. This helper is the lane-agnostic factory:
    // any caller that already has those inputs plus a committed
    // TurnReceipt can lift them into a scope-(2) replay artifact in one
    // call.
    //
    // We intentionally do NOT prove inside `execute` (the executor remains
    // proof-agnostic on the classical path); we just expose the wrapper
    // so the prove site can call into us without taking a turn-crate
    // refactor as a dependency. See WITNESSED-RECEIPT-CHAIN-DESIGN.md §8.

    /// Wrap a committed receipt with the prove-site's trace + proof bytes
    /// into a [`crate::WitnessedReceipt`].
    ///
    /// Pass `trace = Some(&trace)` to produce a scope-(2) replay artifact
    /// (the trace becomes an inline witness bundle, witness_hash committed).
    /// Pass `trace = None` to produce a scope-(1) artifact (proof + PI
    /// only; witness_hash is all-zeros).
    pub fn wrap_witnessed(
        receipt: crate::turn::TurnReceipt,
        proof_bytes: Vec<u8>,
        public_inputs: Vec<u32>,
        trace: Option<&[Vec<pyana_circuit::field::BabyBear>]>,
    ) -> crate::WitnessedReceipt {
        crate::WitnessedReceipt::from_components(receipt, proof_bytes, public_inputs, trace)
    }

    /// Estimate the computron cost of a turn without applying it.
    pub fn estimate_cost(&self, turn: &Turn) -> u64 {
        let mut total: u64 = 0;
        for root in &turn.call_forest.roots {
            total = total.saturating_add(self.estimate_tree_cost(root));
        }
        total
    }

    /// Validate a turn without applying it. Returns Ok(()) if it would succeed,
    /// or the first error that would be encountered.
    pub fn validate_without_apply(&self, turn: &Turn, ledger: &Ledger) -> Result<(), TurnError> {
        if turn.call_forest.is_empty() {
            return Err(TurnError::EmptyForest);
        }

        if let Some(valid_until) = turn.valid_until {
            if self.current_timestamp > valid_until {
                return Err(TurnError::Expired {
                    valid_until,
                    now: self.current_timestamp,
                });
            }
        }

        let agent_cell = ledger
            .get(&turn.agent)
            .ok_or(TurnError::CellNotFound { id: turn.agent })?;

        if agent_cell.state.nonce() != turn.nonce {
            return Err(TurnError::NonceReplay {
                expected: agent_cell.state.nonce(),
                got: turn.nonce,
            });
        }

        if agent_cell.state.balance() < turn.fee {
            return Err(TurnError::InsufficientBalance {
                cell: turn.agent,
                required: turn.fee,
                available: agent_cell.state.balance(),
            });
        }

        // Estimate cost.
        let estimated = self.estimate_cost(turn);
        if estimated > turn.fee {
            return Err(TurnError::BudgetExceeded {
                limit: turn.fee,
                used: estimated,
            });
        }

        Ok(())
    }

    /// Execute a single tree node and its children recursively.
    ///
    /// Returns Ok(()) on success or Err((TurnError, path)) on failure.
    fn execute_tree(
        &self,
        tree: &CallTree,
        ledger: &mut Ledger,
        parent_cell: &CellId,
        parent_delegation: DelegationMode,
        computrons_used: &mut u64,
        budget: u64,
        effects_hashes: &mut Vec<[u8; 32]>,
        path: Vec<usize>,
        journal: &mut LedgerJournal,
        excess: &mut i64,
        turn_nonce: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let action = &tree.action;

        // Meter the action base cost.
        *computrons_used = computrons_used.saturating_add(self.costs.action_base);
        if *computrons_used > budget {
            return Err((
                TurnError::BudgetExceeded {
                    limit: budget,
                    used: *computrons_used,
                },
                path,
            ));
        }

        // Check target cell exists.
        if ledger.get(&action.target).is_none() {
            return Err((TurnError::CellNotFound { id: action.target }, path.clone()));
        }

        // Check capability: does the parent have access to the target?
        // The agent (top-level parent) implicitly has access to itself.
        // For other cells, the parent must hold a capability.
        // Bearer authorization bypasses this check: bearer caps carry their own
        // delegation proof that validates authority without requiring a c-list entry.
        let is_bearer_auth = matches!(&action.authorization, Authorization::Bearer(_));
        if &action.target != parent_cell && !is_bearer_auth {
            let parent = ledger
                .get(parent_cell)
                .ok_or_else(|| (TurnError::CellNotFound { id: *parent_cell }, path.clone()))?;

            let has_capability =
                Self::has_access_including_delegation_at(parent, &action.target, self.block_height);

            // Check delegation mode: if parent_delegation is None, child actions cannot
            // use the parent's capabilities to reach non-parent cells.
            if !has_capability {
                // TODO: DelegationMode::ParentsOwn and Inherit are not yet implemented.
                // Currently all modes fall through to direct capability check.
                // Use Effect::Introduce for explicit capability transfer between cells.
                match parent_delegation {
                    DelegationMode::None => {
                        return Err((
                            TurnError::CapabilityNotHeld {
                                actor: *parent_cell,
                                target: action.target,
                            },
                            path,
                        ));
                    }
                    DelegationMode::ParentsOwn | DelegationMode::Inherit => {
                        // ParentsOwn and Inherit are deprecated; behave like None.
                        return Err((
                            TurnError::CapabilityNotHeld {
                                actor: *parent_cell,
                                target: action.target,
                            },
                            path,
                        ));
                    }
                    DelegationMode::SnapshotRefresh => {
                        // Walk the delegation chain from parent_cell upward to find
                        // an ancestor that holds the capability to action.target.
                        // If found, create a DelegatedRef snapshot on the child cell,
                        // giving it a frozen view of the ancestor's capabilities.
                        let found_ancestor = Self::walk_delegation_chain_for_capability(
                            ledger,
                            parent_cell,
                            &action.target,
                            self.block_height,
                        );
                        if let Some(ancestor_id) = found_ancestor {
                            let ancestor = ledger.get(&ancestor_id).unwrap();
                            let snapshot: Vec<pyana_cell::CapabilityRef> =
                                ancestor.capabilities.iter().cloned().collect();
                            let delegation_epoch = ancestor.state.delegation_epoch();
                            let now = self.current_timestamp as u64;
                            let max_staleness = self.max_introduction_lifetime;

                            // Set up a DelegatedRef on the acting child cell so it can
                            // use the ancestor's capabilities for this and future actions.
                            let child_cell = ledger.get_mut(parent_cell).unwrap();
                            if child_cell.delegation.is_none() {
                                journal.record_set_delegation(*parent_cell, None);
                                let clist_bytes =
                                    postcard::to_allocvec(&snapshot).unwrap_or_default();
                                let clist_commitment =
                                    pyana_cell::DelegatedRef::compute_clist_commitment(
                                        &clist_bytes,
                                    );
                                child_cell.delegation = Some(pyana_cell::DelegatedRef::new(
                                    ancestor_id,
                                    *parent_cell,
                                    snapshot,
                                    delegation_epoch,
                                    now,
                                    max_staleness,
                                    clist_commitment,
                                    [0u8; 64], // Executor-internal delegation, signature verified by execution authority.
                                ));
                            }
                            // Re-check access now that the delegation snapshot is set.
                            let child_cell_ref = ledger.get(parent_cell).unwrap();
                            if !Self::has_access_including_delegation_at(
                                child_cell_ref,
                                &action.target,
                                self.block_height,
                            ) {
                                return Err((
                                    TurnError::CapabilityNotHeld {
                                        actor: *parent_cell,
                                        target: action.target,
                                    },
                                    path,
                                ));
                            }
                        } else {
                            return Err((
                                TurnError::CapabilityNotHeld {
                                    actor: *parent_cell,
                                    target: action.target,
                                },
                                path,
                            ));
                        }
                    }
                }
            }
        }

        // Re-fetch target_cell after potential delegation mutations above.
        let target_cell = ledger
            .get(&action.target)
            .ok_or_else(|| (TurnError::CellNotFound { id: action.target }, path.clone()))?;

        // Check preconditions.
        self.check_preconditions(&action.preconditions, target_cell, &path)?;

        // Verify authorization (including signature/proof verification).
        self.verify_authorization(action, target_cell, ledger, parent_cell, &path, turn_nonce)?;

        // Meter authorization cost.
        let auth_cost = match &action.authorization {
            Authorization::Signature(_, _) => self.costs.signature_verify,
            Authorization::Proof { .. } => self.costs.proof_verify,
            Authorization::Breadstuff(_) => self.costs.signature_verify / 2, // cheaper
            Authorization::Bearer(_) => self.costs.signature_verify, // sig verification + delegation check
            Authorization::Unchecked => 0,
        };
        *computrons_used = computrons_used.saturating_add(auth_cost);
        if *computrons_used > budget {
            return Err((
                TurnError::BudgetExceeded {
                    limit: budget,
                    used: *computrons_used,
                },
                path,
            ));
        }

        // Capture the target cell's state before effects are applied (for program enforcement).
        let old_target_state = ledger.get(&action.target).map(|c| c.state.clone());

        // =====================================================================
        // PERMISSION UPDATE ORDERING (Fix 2):
        // Split effects into regular effects and permission-changing effects.
        // Regular effects are applied first, permission effects are applied LAST.
        // All permission checks use the ORIGINAL permissions (already verified above
        // in verify_authorization which ran before any effects were applied).
        // This prevents an action from SetPermissions -> exploit weakened perms.
        // =====================================================================
        let (regular_effects, permission_effects): (Vec<&Effect>, Vec<&Effect>) = action
            .effects
            .iter()
            .partition(|e| !e.is_permission_effect());

        // Apply effects, tracking which cells have fields set (for proved_state).
        let is_proof_auth = matches!(&action.authorization, Authorization::Proof { .. });
        let mut proof_field_sets: std::collections::HashMap<
            CellId,
            std::collections::HashSet<usize>,
        > = std::collections::HashMap::new();
        let mut non_proof_field_cells: std::collections::HashSet<CellId> =
            std::collections::HashSet::new();

        // Apply regular effects first.
        for effect in &regular_effects {
            let effect_cost = self.compute_effect_cost(effect);
            *computrons_used = computrons_used.saturating_add(effect_cost);
            if *computrons_used > budget {
                return Err((
                    TurnError::BudgetExceeded {
                        limit: budget,
                        used: *computrons_used,
                    },
                    path.clone(),
                ));
            }

            // Track SetField effects for proved_state logic.
            if let Effect::SetField { cell, index, .. } = effect {
                if is_proof_auth {
                    proof_field_sets.entry(*cell).or_default().insert(*index);
                } else {
                    non_proof_field_cells.insert(*cell);
                }
            }

            self.apply_effect(effect, ledger, &path, &action.target, parent_cell, journal)?;
            effects_hashes.push(effect.hash());
        }

        // Apply permission-changing effects LAST.
        for effect in &permission_effects {
            let effect_cost = self.compute_effect_cost(effect);
            *computrons_used = computrons_used.saturating_add(effect_cost);
            if *computrons_used > budget {
                return Err((
                    TurnError::BudgetExceeded {
                        limit: budget,
                        used: *computrons_used,
                    },
                    path.clone(),
                ));
            }

            self.apply_effect(effect, ledger, &path, &action.target, parent_cell, journal)?;
            effects_hashes.push(effect.hash());
        }

        // Update proved_state based on authorization type and fields touched.
        if is_proof_auth {
            // If ALL 8 fields were set by this proof-authorized action, proved_state = true.
            for (cell_id, indices) in &proof_field_sets {
                if indices.len() == STATE_SLOTS {
                    if let Some(c) = ledger.get_mut(cell_id) {
                        if !c.state.proved_state() {
                            journal.record_set_proved_state(*cell_id, c.state.proved_state());
                            c.state.set_proved_state(true);
                        }
                    }
                }
            }
        } else {
            // Non-proof authorization: if any field was modified, proved_state = false.
            for cell_id in &non_proof_field_cells {
                if let Some(c) = ledger.get_mut(cell_id) {
                    if c.state.proved_state() {
                        journal.record_set_proved_state(*cell_id, c.state.proved_state());
                        c.state.set_proved_state(false);
                    }
                }
            }
        }

        // Apply balance_change (Mina-style excess tracking).
        if let Some(delta) = action.balance_change {
            let target = ledger
                .get(&action.target)
                .ok_or_else(|| (TurnError::CellNotFound { id: action.target }, path.clone()))?;
            let current_balance = target.state.balance();

            // Check for underflow on withdrawal (negative delta).
            if delta < 0 {
                let abs_delta = delta.unsigned_abs();
                if current_balance < abs_delta {
                    return Err((
                        TurnError::BalanceChangeUnderflow {
                            cell: action.target,
                            current: current_balance,
                            delta,
                        },
                        path.clone(),
                    ));
                }
            } else {
                // Check for overflow on deposit (positive delta).
                let abs_delta = delta as u64;
                if current_balance.checked_add(abs_delta).is_none() {
                    return Err((
                        TurnError::BalanceOverflow {
                            cell: action.target,
                        },
                        path.clone(),
                    ));
                }
            }

            // Record old balance for rollback and apply the delta.
            let cell_mut = ledger.get_mut(&action.target).unwrap();
            journal.record_set_balance(action.target, cell_mut.state.balance());
            if delta < 0 {
                cell_mut.state.set_balance(cell_mut.state.balance() - delta.unsigned_abs());
            } else {
                cell_mut.state.set_balance(cell_mut.state.balance() + delta as u64);
            }

            // Update excess: withdrawal (negative delta) PRODUCES excess (adds to excess),
            // deposit (positive delta) CONSUMES excess (subtracts from excess).
            // excess += -delta
            *excess = excess.checked_sub(delta).ok_or_else(|| {
                (
                    TurnError::BalanceOverflow {
                        cell: action.target,
                    },
                    path.clone(),
                )
            })?;
        }

        // Enforce cell program constraints on the post-transition state.
        if let Some(target_cell) = ledger.get(&action.target) {
            if !target_cell.program.is_none() {
                // For Circuit programs, the action must carry a proof (already verified above).
                // For Predicate programs, evaluate constraints against new state.
                if !target_cell.program.requires_proof() {
                    let result = target_cell
                        .program
                        .evaluate(&target_cell.state, old_target_state.as_ref());
                    if let Err(e) = result {
                        return Err((
                            TurnError::ProgramViolation {
                                cell: action.target,
                                reason: e.to_string(),
                            },
                            path,
                        ));
                    }
                }
                // Circuit programs: we rely on the proof verification done in verify_authorization.
                // The cell's verification_key corresponds to the circuit. If the proof passed
                // verification, the state transition is valid by construction.
            }
        }

        // Recurse into children.
        // NOTE: This resolution determines whether children can target *different* cells.
        // DelegationMode::None prevents cross-cell targeting (enforced below).
        // ParentsOwn and Inherit are deprecated — they behave identically to None.
        // Use Effect::Introduce or SnapshotRefresh for explicit capability delegation.
        let child_delegation = match action.may_delegate {
            DelegationMode::None => DelegationMode::None,
            DelegationMode::ParentsOwn => DelegationMode::None, // deprecated: same as None
            DelegationMode::Inherit => DelegationMode::None,    // deprecated: same as None
            DelegationMode::SnapshotRefresh => DelegationMode::SnapshotRefresh,
        };

        for (child_idx, child) in tree.children.iter().enumerate() {
            // Check delegation permission: None means children must target same cell as parent.
            if child_delegation == DelegationMode::None && child.action.target != action.target {
                return Err((
                    TurnError::DelegationDenied {
                        parent: action.target,
                        child_target: child.action.target,
                    },
                    {
                        let mut p = path.clone();
                        p.push(child_idx);
                        p
                    },
                ));
            }

            let mut child_path = path.clone();
            child_path.push(child_idx);

            self.execute_tree(
                child,
                ledger,
                &action.target, // current action's target becomes the parent for children
                child_delegation,
                computrons_used,
                budget,
                effects_hashes,
                child_path,
                journal,
                excess,
                turn_nonce,
            )?;
        }

        Ok(())
    }

    /// Check preconditions against the target cell's state.
    /// TRUST-CRITICAL: This function enforces temporal and state-based guards on actions.
    /// If compromised: expired turns could execute, balance thresholds could be bypassed,
    /// and block-height-locked actions could fire prematurely.
    /// Future: precondition evaluation will be proven inside the Effect VM circuit,
    /// allowing verifiers to confirm guards were checked without trusting the executor.
    fn check_preconditions(
        &self,
        preconditions: &Preconditions,
        target_cell: &Cell,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let ctx = EvalContext {
            block_height: self.block_height,
            timestamp: self.current_timestamp,
        };

        preconditions
            .evaluate(&target_cell.state, &ctx)
            .map_err(|e| {
                (
                    TurnError::PreconditionFailed {
                        description: format!("{e:?}"),
                    },
                    path.to_vec(),
                )
            })
    }

    /// TRUST-CRITICAL: This function gates ALL state mutations behind authorization checks.
    /// If compromised: unauthorized parties can modify any cell's state, transfer balances,
    /// or forge delegations. This is the primary access control enforcement point.
    /// Future: move to trustless by requiring all authorizations to be STARK-proven
    /// (currently signature auth is verified classically by the executor).
    ///
    /// Verify that the action's authorization satisfies the target cell's permission requirements.
    ///
    /// This checks ALL required permissions for ALL effects in the action independently.
    /// Each permission requirement is verified separately against the provided authorization,
    /// avoiding the partial-order problem where Signature vs Proof are incomparable
    /// (is_narrower_or_equal returns false in both directions for those).
    ///
    /// For signature auth: verifies the Ed25519 signature against the cell's public key.
    /// For proof auth: delegates to the configured ProofVerifier (fail-closed if none set).
    fn verify_authorization(
        &self,
        action: &Action,
        target_cell: &Cell,
        ledger: &Ledger,
        actor_cell_id: &CellId,
        path: &[usize],
        turn_nonce: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Bearer caps carry their own delegation proof and MUST always be verified,
        // regardless of target cell permission level.
        if let Authorization::Bearer(bearer_proof) = &action.authorization {
            self.verify_bearer_cap(bearer_proof, ledger, path)?;

            // Enforce bearer facet: if the bearer proof has an allowed_effects mask,
            // verify that all effects in the action are within it.
            // If the bearer proof has no explicit mask, check whether the delegator's
            // capability has a facet constraint (inherited facet).
            let effective_mask = bearer_proof.allowed_effects.or_else(|| {
                // Look up the delegator's capability to see if it has a facet.
                // For SignedDelegation, we can find the delegator by pk.
                match &bearer_proof.delegation_proof {
                    crate::action::DelegationProofData::SignedDelegation {
                        delegator_pk, ..
                    } => ledger
                        .iter()
                        .find(|(_, cell)| *cell.public_key() == *delegator_pk)
                        .and_then(|(_, cell)| {
                            cell.capabilities
                                .capabilities_for(&bearer_proof.target)
                                .into_iter()
                                .find(|cap| cap.permissions != AuthRequired::Impossible)
                                .and_then(|cap| cap.allowed_effects)
                        }),
                    // For STARK delegations, the delegator is anonymous — facet must be
                    // explicitly specified in the bearer proof if needed.
                    crate::action::DelegationProofData::StarkDelegation { .. } => None,
                }
            });

            if let Some(mask) = effective_mask {
                if mask != 0 {
                    let effects_mask = action
                        .effects
                        .iter()
                        .fold(0u32, |acc, e| acc | e.effect_kind_mask());
                    if effects_mask != 0 && effects_mask & mask != effects_mask {
                        return Err((
                            TurnError::BearerCapFacetViolation {
                                target: bearer_proof.target,
                                attempted_effects_mask: effects_mask,
                                allowed_mask: mask,
                            },
                            path.to_vec(),
                        ));
                    }
                }
            }

            return Ok(());
        }

        // Determine ALL required permissions for this action's effects.
        let required_actions = self.determine_required_permissions(action);

        // If no effects produced any specific permission, check general access.
        if required_actions.is_empty() {
            let access_req = target_cell
                .permissions
                .for_action(pyana_cell::permissions::Action::Access);
            self.check_single_auth_requirement(
                action,
                target_cell,
                ledger,
                actor_cell_id,
                access_req,
                "Access",
                path,
                turn_nonce,
            )?;
        } else {
            // Check EACH permission requirement independently. This avoids the
            // is_narrower_or_equal partial-order problem where Signature vs Proof
            // are incomparable and the "most restrictive" finder could pick wrong.
            for (perm_action, action_name) in &required_actions {
                let auth_req = target_cell.permissions.for_action(*perm_action);
                self.check_single_auth_requirement(
                    action,
                    target_cell,
                    ledger,
                    actor_cell_id,
                    auth_req,
                    action_name,
                    path,
                    turn_nonce,
                )?;
            }
        }

        // Additionally, check Receive permission on transfer destinations.
        for effect in &action.effects {
            if let Effect::Transfer { to, .. } = effect {
                if let Some(dest_cell) = ledger.get(to) {
                    let receive_req = dest_cell
                        .permissions
                        .for_action(pyana_cell::permissions::Action::Receive);
                    if matches!(receive_req, AuthRequired::Impossible) {
                        return Err((
                            TurnError::PermissionDenied {
                                cell: *to,
                                action: "Receive".to_string(),
                                required: AuthRequired::Impossible,
                            },
                            path.to_vec(),
                        ));
                    }
                    if !matches!(receive_req, AuthRequired::None) {
                        return Err((
                            TurnError::PermissionDenied {
                                cell: *to,
                                action: "Receive".to_string(),
                                required: receive_req.clone(),
                            },
                            path.to_vec(),
                        ));
                    }
                }
            }
        }

        Ok(())
    }

    /// Check a single auth requirement against an action's authorization.
    fn check_single_auth_requirement(
        &self,
        action: &Action,
        target_cell: &Cell,
        ledger: &Ledger,
        actor_cell_id: &CellId,
        auth_required: &AuthRequired,
        action_name: &str,
        path: &[usize],
        turn_nonce: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        match auth_required {
            AuthRequired::None => Ok(()),
            AuthRequired::Impossible => Err((
                TurnError::PermissionDenied {
                    cell: action.target,
                    action: action_name.to_string(),
                    required: AuthRequired::Impossible,
                },
                path.to_vec(),
            )),
            AuthRequired::Signature => match &action.authorization {
                Authorization::Signature(r, s) => {
                    self.verify_ed25519_signature(action, target_cell, r, s, path, turn_nonce)
                }
                Authorization::Breadstuff(token) => {
                    let effects_mask = action
                        .effects
                        .iter()
                        .fold(0u32, |acc, e| acc | e.effect_kind_mask());
                    self.check_breadstuff(
                        ledger,
                        actor_cell_id,
                        token,
                        action_name,
                        auth_required,
                        path,
                        action.target,
                        effects_mask,
                    )
                }
                _ => Err((
                    TurnError::PermissionDenied {
                        cell: action.target,
                        action: action_name.to_string(),
                        required: AuthRequired::Signature,
                    },
                    path.to_vec(),
                )),
            },
            // NOTE on revocation checking for Proof auth:
            // ZK proofs are anonymous — the verifier cannot determine WHICH capability
            // the prover used, so per-capability revocation cannot be enforced at
            // verification time. Revocation for ZK-authorized actions must be proven
            // at proof-generation time (the circuit must include a non-revocation check
            // as part of its public inputs). This is an inherent limitation of the
            // ZK auth model and is by design.
            AuthRequired::Proof => match &action.authorization {
                Authorization::Proof {
                    proof_bytes,
                    bound_action,
                    bound_resource,
                } => self.verify_zk_proof(
                    target_cell,
                    proof_bytes,
                    bound_action,
                    bound_resource,
                    path,
                ),
                _ => Err((
                    TurnError::PermissionDenied {
                        cell: action.target,
                        action: action_name.to_string(),
                        required: AuthRequired::Proof,
                    },
                    path.to_vec(),
                )),
            },
            AuthRequired::Either => match &action.authorization {
                Authorization::Signature(r, s) => {
                    self.verify_ed25519_signature(action, target_cell, r, s, path, turn_nonce)
                }
                Authorization::Proof {
                    proof_bytes,
                    bound_action,
                    bound_resource,
                } => self.verify_zk_proof(
                    target_cell,
                    proof_bytes,
                    bound_action,
                    bound_resource,
                    path,
                ),
                Authorization::Breadstuff(token) => {
                    let effects_mask = action
                        .effects
                        .iter()
                        .fold(0u32, |acc, e| acc | e.effect_kind_mask());
                    self.check_breadstuff(
                        ledger,
                        actor_cell_id,
                        token,
                        action_name,
                        auth_required,
                        path,
                        action.target,
                        effects_mask,
                    )
                }
                Authorization::Bearer(proof) => self.verify_bearer_cap(proof, ledger, path),
                Authorization::Unchecked => Err((
                    TurnError::PermissionDenied {
                        cell: action.target,
                        action: action_name.to_string(),
                        required: AuthRequired::Either,
                    },
                    path.to_vec(),
                )),
            },
        }
    }

    /// Verify an Ed25519 signature against the target cell's public key.
    ///
    /// When the action uses `CommitmentMode::Partial`, the signing message is computed
    /// via `compute_partial_signing_message` (action hash + position + federation_id + nonce).
    /// This allows composed turns with partial signers to be verified correctly by the executor.
    fn verify_ed25519_signature(
        &self,
        action: &Action,
        target_cell: &Cell,
        r: &[u8; 32],
        s: &[u8; 32],
        path: &[usize],
        turn_nonce: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        use crate::action::CommitmentMode;

        let message = match action.commitment_mode {
            CommitmentMode::Partial => {
                // For partial commitment, the signer committed to their action hash + position
                // + federation_id + turn_nonce.
                // The position is encoded in the path (root index).
                let position = path.first().copied().unwrap_or(0);
                Self::compute_partial_signing_message(
                    action,
                    position,
                    &self.local_federation_id,
                    turn_nonce,
                )
            }
            CommitmentMode::Full => {
                Self::compute_signing_message(action, &self.local_federation_id)
            }
        };

        let mut sig_bytes = [0u8; 64];
        sig_bytes[..32].copy_from_slice(r);
        sig_bytes[32..].copy_from_slice(s);

        let signature = Signature::from_bytes(&sig_bytes);

        let verifying_key = VerifyingKey::from_bytes(&target_cell.public_key()).map_err(|_| {
            (
                TurnError::InvalidAuthorization {
                    reason: "cell public key is not a valid Ed25519 point".to_string(),
                },
                path.to_vec(),
            )
        })?;

        verifying_key
            .verify_strict(&message, &signature)
            .map_err(|_| {
                (
                    TurnError::InvalidAuthorization {
                        reason: "Ed25519 signature verification failed".to_string(),
                    },
                    path.to_vec(),
                )
            })
    }

    /// Verify a ZK proof against the target cell's verification key.
    ///
    /// Uses the `bound_action` and `bound_resource` that were committed to at
    /// proving time (carried in the `Authorization::Proof` variant) rather than
    /// deriving from the action's method/target. This ensures the verifier checks
    /// against the same binding the prover created.
    fn verify_zk_proof(
        &self,
        target_cell: &Cell,
        proof_bytes: &[u8],
        bound_action: &str,
        bound_resource: &str,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if proof_bytes.is_empty() {
            return Err((
                TurnError::InvalidAuthorization {
                    reason: "proof bytes are empty".to_string(),
                },
                path.to_vec(),
            ));
        }
        if proof_bytes.len() > 65536 {
            return Err((
                TurnError::InvalidAuthorization {
                    reason: format!("proof too large: {} bytes (max 65536)", proof_bytes.len()),
                },
                path.to_vec(),
            ));
        }

        let vk = target_cell.verification_key.as_ref().ok_or_else(|| {
            (
                TurnError::InvalidAuthorization {
                    reason: "cell requires proof but has no verification key".to_string(),
                },
                path.to_vec(),
            )
        })?;

        let verifier = self.proof_verifier.as_ref().ok_or_else(|| {
            (
                TurnError::InvalidAuthorization {
                    reason: "no proof verifier configured (fail-closed)".to_string(),
                },
                path.to_vec(),
            )
        })?;

        if verifier.verify(proof_bytes, bound_action, bound_resource, &vk.data) {
            Ok(())
        } else {
            Err((
                TurnError::InvalidAuthorization {
                    reason: "ZK proof verification failed".to_string(),
                },
                path.to_vec(),
            ))
        }
    }

    /// Check breadstuff (capability token) authorization.
    ///
    /// The breadstuff token must be held in the ACTOR's (parent cell's) capability
    /// list, not the target's. The actor presents a breadstuff token they hold as
    /// proof of their authority to act on the target cell. The matching capability
    /// must also reference the action's target cell (target-scoped).
    ///
    /// Beyond existence, this now enforces:
    /// - Expiry: the capability's `expires_at` must not have passed.
    /// - Revocation: if the capability's breadstuff matches a revocation channel, it
    ///   must not be tripped.
    /// - Facets: if the capability has `allowed_effects`, the action's effects must
    ///   be within the mask.
    fn check_breadstuff(
        &self,
        ledger: &Ledger,
        actor_cell_id: &CellId,
        token: &[u8; 32],
        action_name: &str,
        auth_required: &AuthRequired,
        path: &[usize],
        target_id: CellId,
        effects_mask: pyana_cell::EffectMask,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let actor_cell = ledger.get(actor_cell_id).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: *actor_cell_id },
                path.to_vec(),
            )
        })?;

        // Find the SPECIFIC matching capability (not just any-match).
        let matching_cap = actor_cell
            .capabilities
            .iter()
            .find(|cap| cap.breadstuff.as_ref() == Some(token) && cap.target == target_id);

        let cap = matching_cap.ok_or_else(|| {
            (
                TurnError::PermissionDenied {
                    cell: target_id,
                    action: action_name.to_string(),
                    required: auth_required.clone(),
                },
                path.to_vec(),
            )
        })?;

        // Check expiry: if the capability has an expires_at, it must not have passed.
        if let Some(expires_at) = cap.expires_at {
            if self.block_height > expires_at {
                return Err((
                    TurnError::BreadstuffExpired {
                        actor: *actor_cell_id,
                        target: target_id,
                        expires_at,
                        current_height: self.block_height,
                    },
                    path.to_vec(),
                ));
            }
        }

        // Check facet (allowed_effects): if the capability restricts effects, the
        // action's combined effects mask must be within the allowed set.
        if let Some(mask) = cap.allowed_effects {
            if mask != 0 && effects_mask != 0 {
                // Any bit in effects_mask that is NOT in the cap's mask is a violation.
                if effects_mask & mask != effects_mask {
                    return Err((
                        TurnError::BreadstuffFacetViolation {
                            actor: *actor_cell_id,
                            target: target_id,
                            attempted_effects_mask: effects_mask,
                            allowed_mask: mask,
                        },
                        path.to_vec(),
                    ));
                }
            }
        }

        // Check revocation channel: if the breadstuff matches a registered revocation
        // channel, verify the channel hasn't been tripped.
        if let Some(ref channels) = self.revocation_channels {
            if let Err(_) = channels.check_exercise_permitted(
                token,
                self.block_height,
                self.block_height,
                self.max_introduction_lifetime,
            ) {
                // Only reject if this is actually a registered channel (not just any breadstuff).
                if channels.get(token).is_some() {
                    return Err((
                        TurnError::BreadstuffRevoked {
                            actor: *actor_cell_id,
                            target: target_id,
                            channel_id: *token,
                        },
                        path.to_vec(),
                    ));
                }
            }
        }

        Ok(())
    }

    /// Verify a bearer capability proof: the parallel authorization path for capabilities
    /// NOT in the actor's c-list but proven via delegation chain.
    pub fn verify_bearer_cap(
        &self,
        proof: &crate::action::BearerCapProof,
        ledger: &Ledger,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        use crate::action::DelegationProofData;
        if self.block_height > proof.expires_at {
            return Err((
                TurnError::BearerCapExpired {
                    target: proof.target,
                    expires_at: proof.expires_at,
                    current_height: self.block_height,
                },
                path.to_vec(),
            ));
        }
        if let Some(channel_id) = &proof.revocation_channel {
            if let Some(ref channels) = self.revocation_channels {
                if channels
                    .check_exercise_permitted(
                        channel_id,
                        self.block_height,
                        self.block_height,
                        self.max_introduction_lifetime,
                    )
                    .is_err()
                {
                    return Err((
                        TurnError::BearerCapRevoked {
                            target: proof.target,
                            channel_id: *channel_id,
                        },
                        path.to_vec(),
                    ));
                }
            } else {
                return Err((
                    TurnError::BearerCapRevoked {
                        target: proof.target,
                        channel_id: *channel_id,
                    },
                    path.to_vec(),
                ));
            }
        }
        match &proof.delegation_proof {
            DelegationProofData::SignedDelegation {
                delegator_pk,
                signature,
                bearer_pk,
            } => {
                let message = Self::compute_bearer_delegation_message(
                    &proof.target,
                    &proof.permissions,
                    bearer_pk,
                    proof.expires_at,
                    &self.local_federation_id,
                );
                let vk = VerifyingKey::from_bytes(delegator_pk).map_err(|_| {
                    (
                        TurnError::BearerCapInvalidProof {
                            target: proof.target,
                            reason: "invalid delegator public key".to_string(),
                        },
                        path.to_vec(),
                    )
                })?;
                let sig = Signature::from_bytes(signature);
                vk.verify_strict(&message, &sig).map_err(|_| {
                    (
                        TurnError::BearerCapInvalidProof {
                            target: proof.target,
                            reason: "delegation signature verification failed".to_string(),
                        },
                        path.to_vec(),
                    )
                })?;
                let delegator_cell = ledger
                    .iter()
                    .find(|(_, cell)| *cell.public_key() == *delegator_pk)
                    .map(|(_, cell)| cell);
                let delegator_cell = delegator_cell.ok_or_else(|| {
                    (
                        TurnError::BearerCapDelegatorLacksCapability {
                            delegator: CellId::from_bytes(*delegator_pk),
                            target: proof.target,
                        },
                        path.to_vec(),
                    )
                })?;
                if !Self::has_access_including_delegation_at(
                    delegator_cell,
                    &proof.target,
                    self.block_height,
                ) {
                    return Err((
                        TurnError::BearerCapDelegatorLacksCapability {
                            delegator: delegator_cell.id(),
                            target: proof.target,
                        },
                        path.to_vec(),
                    ));
                }
                let delegator_cap = delegator_cell
                    .capabilities
                    .capabilities_for(&proof.target)
                    .into_iter()
                    .find(|cap| cap.permissions != AuthRequired::Impossible);
                if let Some(cap) = delegator_cap {
                    if !proof.permissions.is_narrower_or_equal(&cap.permissions) {
                        return Err((
                            TurnError::BearerCapAmplification {
                                target: proof.target,
                                delegator_permissions: cap.permissions.clone(),
                                bearer_permissions: proof.permissions.clone(),
                            },
                            path.to_vec(),
                        ));
                    }

                    // Facet attenuation check: if the delegator's capability has a facet
                    // restriction, the bearer's facet (if any) must be a subset.
                    // If the bearer doesn't specify a facet, it inherits the delegator's.
                    // If the delegator has no facet, the bearer can specify any facet.
                    if let Some(delegator_mask) = cap.allowed_effects {
                        if delegator_mask != 0 {
                            if let Some(bearer_mask) = proof.allowed_effects {
                                // Bearer specifies a facet — it must be a subset of delegator's.
                                if !pyana_cell::is_facet_attenuation(delegator_mask, bearer_mask) {
                                    return Err((
                                        TurnError::BearerCapFacetAmplification {
                                            target: proof.target,
                                            delegator_mask,
                                            bearer_mask,
                                        },
                                        path.to_vec(),
                                    ));
                                }
                            }
                            // If bearer doesn't specify a facet (None), it inherits the
                            // delegator's mask. The effective facet is enforced at execution
                            // time via the returned Ok + caller checking proof.allowed_effects
                            // OR delegator_cap.allowed_effects.
                        }
                    }
                }
                Ok(())
            }
            DelegationProofData::StarkDelegation {
                proof_bytes,
                root_issuer_commitment,
            } => {
                use pyana_circuit::field::BabyBear;
                use pyana_circuit::stark;
                let stark_proof = stark::proof_from_bytes(proof_bytes).map_err(|e| {
                    (
                        TurnError::BearerCapInvalidProof {
                            target: proof.target,
                            reason: format!("STARK proof deserialization failed: {e}"),
                        },
                        path.to_vec(),
                    )
                })?;
                let mut public_inputs: Vec<BabyBear> = Vec::new();
                public_inputs.extend(Self::bytes32_to_babybear(root_issuer_commitment));
                public_inputs.extend(Self::bytes32_to_babybear(proof.target.as_bytes()));
                if stark_proof.public_inputs.len() < public_inputs.len() {
                    return Err((
                        TurnError::BearerCapInvalidProof {
                            target: proof.target,
                            reason: format!(
                                "STARK proof has {} public inputs, expected at least {}",
                                stark_proof.public_inputs.len(),
                                public_inputs.len()
                            ),
                        },
                        path.to_vec(),
                    ));
                }
                for (i, expected) in public_inputs.iter().enumerate() {
                    if BabyBear(stark_proof.public_inputs[i]) != *expected {
                        return Err((
                            TurnError::BearerCapInvalidProof {
                                target: proof.target,
                                reason: format!("STARK public input mismatch at index {i}"),
                            },
                            path.to_vec(),
                        ));
                    }
                }
                let air = pyana_circuit::EffectVmAir::new(stark_proof.trace_len);
                stark::verify(&air, &stark_proof, &public_inputs).map_err(|e| {
                    (
                        TurnError::BearerCapInvalidProof {
                            target: proof.target,
                            reason: format!("STARK proof verification failed: {e}"),
                        },
                        path.to_vec(),
                    )
                })?;
                Ok(())
            }
        }
    }

    /// Compute the delegation message signed by a delegator for a bearer capability.
    pub fn compute_bearer_delegation_message(
        target: &CellId,
        permissions: &AuthRequired,
        bearer_pk: &[u8; 32],
        expires_at: u64,
        federation_id: &[u8; 32],
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-bearer-delegation-v1:");
        hasher.update(federation_id);
        hasher.update(target.as_bytes());
        let perm_byte = match permissions {
            AuthRequired::None => 0u8,
            AuthRequired::Signature => 1u8,
            AuthRequired::Proof => 2u8,
            AuthRequired::Either => 3u8,
            AuthRequired::Impossible => 4u8,
        };
        hasher.update(&[perm_byte]);
        hasher.update(bearer_pk);
        hasher.update(&expires_at.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Compute the message that should be signed for an action.
    ///
    /// For actions with `CommitmentMode::Full`, this produces the standard signing
    /// message based on the action's content. For `CommitmentMode::Partial`, use
    /// [`compute_partial_signing_message`] which includes position, federation_id, and nonce.
    ///
    /// The `federation_id` binds the signature to a specific federation, preventing
    /// cross-federation replay where a valid signature from federation A could be
    /// submitted to federation B.
    pub fn compute_signing_message(action: &Action, federation_id: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        // Domain separation: version-bumped to v2 when federation binding was added.
        hasher.update(b"pyana-action-sig-v2:");
        hasher.update(federation_id);
        hasher.update(action.target.as_bytes());
        hasher.update(&action.method);
        for arg in &action.args {
            hasher.update(arg);
        }
        for effect in &action.effects {
            hasher.update(&effect.hash());
        }
        hasher.update(&[action.may_delegate as u8]);
        // Include commitment_mode to prevent an attacker from changing the mode
        // (e.g., switching Full to Partial) and using the signature in a different context.
        hasher.update(&[action.commitment_mode as u8]);
        // Include balance_change to prevent malleability: without this, an attacker
        // could take a signed action and modify the balance_change field to drain funds.
        match action.balance_change {
            Some(delta) => {
                hasher.update(&[1u8]); // discriminant: Some
                hasher.update(&delta.to_le_bytes());
            }
            None => {
                hasher.update(&[0u8]); // discriminant: None
            }
        }
        // Include preconditions hash to prevent downgrade attacks where an attacker
        // removes preconditions (e.g., minimum balance guards) from a signed action.
        // Hash preconditions inline: use their serialized form for binding.
        let preconds_bytes = postcard::to_allocvec(&action.preconditions).unwrap_or_default();
        hasher.update(&preconds_bytes);
        *hasher.finalize().as_bytes()
    }

    /// Compute the signing message for an action in partial commitment mode.
    ///
    /// The signer commits to:
    /// - The action's own content hash (what they are doing)
    /// - Their position index in the forest (where they are)
    /// - The federation identity (prevents cross-federation replay)
    /// - The turn nonce (prevents replay within the same federation across turns)
    ///
    /// The forest root is NOT included because it creates a chicken-and-egg problem:
    /// the forest root is only computable after all fragments are assembled, but signers
    /// need to sign before assembly. Instead, the coordinator signs the full composed
    /// turn (including the forest root) via `coordinator_signature` on the composed Turn.
    ///
    /// This allows a party to sign their part without knowing about other actions,
    /// enabling multi-party composition (DEX fills, atomic swaps, etc.)
    pub fn compute_partial_signing_message(
        action: &Action,
        position: usize,
        federation_id: &[u8; 32],
        turn_nonce: u64,
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        // Domain separation: version-bumped to v2 when federation/nonce binding was added.
        hasher.update(b"pyana-partial-sig-v2:");
        hasher.update(federation_id);
        hasher.update(&action.hash());
        hasher.update(&(position as u64).to_le_bytes());
        hasher.update(&turn_nonce.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Determine ALL required permissions for an action based on its effects.
    fn determine_required_permissions(
        &self,
        action: &Action,
    ) -> Vec<(pyana_cell::permissions::Action, &'static str)> {
        let mut result = Vec::new();
        let mut has_send = false;
        let mut has_set_state = false;
        let mut has_increment_nonce = false;
        let mut has_delegate = false;

        // A negative balance_change (withdrawal) requires Send permission.
        if let Some(delta) = action.balance_change {
            if delta < 0 && !has_send {
                result.push((pyana_cell::permissions::Action::Send, "Send"));
                has_send = true;
            }
        }

        for effect in &action.effects {
            match effect {
                Effect::Transfer { from, .. } if from == &action.target && !has_send => {
                    result.push((pyana_cell::permissions::Action::Send, "Send"));
                    has_send = true;
                }
                Effect::SetField { .. } if !has_set_state => {
                    result.push((pyana_cell::permissions::Action::SetState, "SetState"));
                    has_set_state = true;
                }
                Effect::IncrementNonce { .. } if !has_increment_nonce => {
                    result.push((
                        pyana_cell::permissions::Action::IncrementNonce,
                        "IncrementNonce",
                    ));
                    has_increment_nonce = true;
                }
                Effect::GrantCapability { .. } if !has_delegate => {
                    result.push((pyana_cell::permissions::Action::Delegate, "Delegate"));
                    has_delegate = true;
                }
                Effect::RevokeCapability { .. } if !has_delegate => {
                    result.push((pyana_cell::permissions::Action::Delegate, "Delegate"));
                    has_delegate = true;
                }
                Effect::SetPermissions { .. } => {
                    result.push((
                        pyana_cell::permissions::Action::SetPermissions,
                        "SetPermissions",
                    ));
                }
                Effect::SetVerificationKey { .. } => {
                    result.push((
                        pyana_cell::permissions::Action::SetVerificationKey,
                        "SetVerificationKey",
                    ));
                }
                // Locking funds in an escrow or obligation stake is equivalent to
                // sending value out — require Send permission on the source cell.
                Effect::CreateEscrow { .. }
                | Effect::CreateCommittedEscrow { .. }
                | Effect::CreateObligation { .. }
                    if !has_send =>
                {
                    result.push((pyana_cell::permissions::Action::Send, "Send"));
                    has_send = true;
                }
                // Settlement actions (release/refund/fulfill/slash) are checked for
                // creator/beneficiary authorization in the handler, but still require
                // at least Access permission to be mapped so that cells with
                // Access: None cannot be targeted.
                Effect::ReleaseEscrow { .. }
                | Effect::RefundEscrow { .. }
                | Effect::ReleaseCommittedEscrow { .. }
                | Effect::RefundCommittedEscrow { .. }
                | Effect::FulfillObligation { .. }
                | Effect::SlashObligation { .. } => {
                    result.push((pyana_cell::permissions::Action::Access, "Access"));
                }
                _ => {}
            }
        }

        result
    }

    /// Apply a single effect to the ledger, recording undo entries in the journal.
    ///
    /// SECURITY: For any effect that names a cell other than `action_target`,
    /// we verify that the actor holds a capability to that cell AND that the
    /// relevant permission on that cell allows the operation.
    /// TRUST-CRITICAL: This function directly mutates ledger state (balances, fields, cells).
    /// If compromised: balance inflation/deflation, unauthorized state overwrites, or
    /// cell creation without proper authorization. All mutations are journaled for rollback.
    /// Future: replace with verified effect application via Effect VM STARK proof for all
    /// effect types (currently only sovereign cells use proof-carrying effects).
    fn apply_effect(
        &self,
        effect: &Effect,
        ledger: &mut Ledger,
        path: &[usize],
        action_target: &CellId,
        actor: &CellId,
        journal: &mut LedgerJournal,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        match effect {
            Effect::SetField { cell, index, value } => {
                if *index >= STATE_SLOTS {
                    return Err((
                        TurnError::InvalidFieldIndex {
                            cell: *cell,
                            index: *index,
                        },
                        path.to_vec(),
                    ));
                }
                if cell != action_target {
                    self.check_cross_cell_permission(
                        ledger,
                        actor,
                        cell,
                        pyana_cell::permissions::Action::SetState,
                        "SetState",
                        path,
                    )?;
                }
                let c = ledger
                    .get_mut(cell)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
                journal.record_set_field(*cell, *index, c.state.fields[*index]);
                c.state.fields[*index] = *value;
                // Invalidate stale field commitment (the old hash no longer matches).
                if c.state.commitments[*index].is_some() {
                    c.state.commitments[*index] = None;
                }
                Ok(())
            }

            Effect::Transfer { from, to, amount } => {
                if from != action_target {
                    self.check_cross_cell_permission(
                        ledger,
                        actor,
                        from,
                        pyana_cell::permissions::Action::Send,
                        "Send",
                        path,
                    )?;
                }
                let from_cell = ledger
                    .get(from)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *from }, path.to_vec()))?;
                if from_cell.state.balance() < *amount {
                    return Err((
                        TurnError::InsufficientBalance {
                            cell: *from,
                            required: *amount,
                            available: from_cell.state.balance(),
                        },
                        path.to_vec(),
                    ));
                }
                if ledger.get(to).is_none() {
                    return Err((TurnError::TransferDestNotFound { id: *to }, path.to_vec()));
                }
                let to_balance = ledger.get(to).unwrap().state.balance();
                if to_balance.checked_add(*amount).is_none() {
                    return Err((TurnError::BalanceOverflow { cell: *to }, path.to_vec()));
                }
                // Record old balances, then apply.
                let old_from_balance = ledger.get(from).unwrap().state.balance();
                let old_to_balance = ledger.get(to).unwrap().state.balance();
                journal.record_set_balance(*from, old_from_balance);
                journal.record_set_balance(*to, old_to_balance);
                ledger.get_mut(from).unwrap().state.set_balance(old_from_balance - *amount);
                ledger.get_mut(to).unwrap().state.set_balance(old_to_balance + *amount);
                Ok(())
            }

            Effect::GrantCapability { from, to, cap } => {
                if from != action_target {
                    self.check_cross_cell_permission(
                        ledger,
                        actor,
                        from,
                        pyana_cell::permissions::Action::Delegate,
                        "Delegate",
                        path,
                    )?;
                }

                let from_cell = ledger
                    .get(from)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *from }, path.to_vec()))?;

                // A cell implicitly holds the strongest capability over itself:
                // granting access to its own cell is authorized by the signed
                // action (the cell's owner consents). For cross-cell grants the
                // granter must hold an explicit c-list entry pointing at the
                // target.
                if cap.target == *from {
                    // Self-grant: skip c-list lookup; the signature on the
                    // action proves the cell owner consents to share access
                    // to their own cell. Attenuation against an implicit
                    // self-cap is always satisfied (the implicit cap is the
                    // strongest possible).
                } else {
                    let held_cap = from_cell
                        .capabilities
                        .lookup_by_target(&cap.target)
                        .ok_or_else(|| {
                            (
                                TurnError::CapabilityNotHeld {
                                    actor: *from,
                                    target: cap.target,
                                },
                                path.to_vec(),
                            )
                        })?;

                    if !pyana_cell::is_attenuation(&held_cap.permissions, &cap.permissions) {
                        return Err((
                            TurnError::DelegationDenied {
                                parent: *from,
                                child_target: *to,
                            },
                            path.to_vec(),
                        ));
                    }
                }

                let to_cell = ledger
                    .get_mut(to)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *to }, path.to_vec()))?;
                let granted_slot = to_cell
                    .capabilities
                    .grant_with_breadstuff(cap.target, cap.permissions.clone(), cap.breadstuff)
                    .ok_or_else(|| {
                        (
                            TurnError::CapabilitySlotOverflow { cell: *to },
                            path.to_vec(),
                        )
                    })?;
                journal.record_grant_capability(*to, granted_slot);
                Ok(())
            }

            Effect::RevokeCapability { cell, slot } => {
                if cell != action_target {
                    self.check_cross_cell_permission(
                        ledger,
                        actor,
                        cell,
                        pyana_cell::permissions::Action::Delegate,
                        "Delegate",
                        path,
                    )?;
                }
                let c = ledger
                    .get_mut(cell)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
                if let Some(old_cap) = c.capabilities.lookup(*slot).cloned() {
                    journal.record_revoke_capability(*cell, old_cap);
                }
                c.capabilities.revoke(*slot);
                Ok(())
            }

            Effect::EmitEvent { cell, event } => {
                if ledger.get(cell).is_none() {
                    return Err((TurnError::CellNotFound { id: *cell }, path.to_vec()));
                }
                // Record the event in the journal so it appears in the turn receipt.
                journal.record_event_emitted(*cell, event.topic, event.data.clone());
                Ok(())
            }

            Effect::IncrementNonce { cell } => {
                if cell != action_target {
                    self.check_cross_cell_permission(
                        ledger,
                        actor,
                        cell,
                        pyana_cell::permissions::Action::IncrementNonce,
                        "IncrementNonce",
                        path,
                    )?;
                }
                let c = ledger
                    .get_mut(cell)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
                journal.record_set_nonce(*cell, c.state.nonce());
                c.state.increment_nonce();
                Ok(())
            }

            Effect::CreateCell {
                public_key,
                token_id,
                balance,
            } => {
                if *balance != 0 {
                    return Err((
                        TurnError::CreateCellNonZeroBalance {
                            cell: CellId::derive_raw(public_key, token_id),
                            balance: *balance,
                        },
                        path.to_vec(),
                    ));
                }
                let new_cell = Cell::with_balance(*public_key, *token_id, 0);
                let id = new_cell.id();
                ledger
                    .insert_cell(new_cell)
                    .map_err(|_| (TurnError::CellAlreadyExists { id }, path.to_vec()))?;
                journal.record_create_cell(id);
                Ok(())
            }

            Effect::SetPermissions {
                cell,
                new_permissions,
            } => {
                if cell != action_target {
                    self.check_cross_cell_permission(
                        ledger,
                        actor,
                        cell,
                        pyana_cell::permissions::Action::SetPermissions,
                        "SetPermissions",
                        path,
                    )?;
                }
                let c = ledger
                    .get_mut(cell)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
                journal.record_set_permissions(*cell, c.permissions.clone());
                c.permissions = new_permissions.clone();
                Ok(())
            }

            Effect::SetVerificationKey { cell, new_vk } => {
                if cell != action_target {
                    self.check_cross_cell_permission(
                        ledger,
                        actor,
                        cell,
                        pyana_cell::permissions::Action::SetVerificationKey,
                        "SetVerificationKey",
                        path,
                    )?;
                }
                let c = ledger
                    .get_mut(cell)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
                journal.record_set_verification_key(*cell, c.verification_key.clone());
                c.verification_key = new_vk.clone();
                Ok(())
            }

            // Note effects: validate structure and record for the note layer to
            // process after the turn commits (nullifier set / note tree updates).
            Effect::NoteSpend {
                nullifier,
                note_tree_root,
                spending_proof,
                value,
                asset_type,
                ..
            } => {
                // Validate nullifier is well-formed (non-zero).
                if nullifier.0.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "null nullifier in NoteSpend".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Validate note_tree_root is non-zero (must reference a real tree state).
                if note_tree_root.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "null note_tree_root in NoteSpend".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the ZK spending proof: proves the spender knows the note's
                // opening, the nullifier is correctly derived, and the note commitment
                // exists in the note tree at the given root.
                if spending_proof.is_empty() {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "NoteSpend missing spending proof".into(),
                        },
                        path.to_vec(),
                    ));
                }
                let verifier = self.proof_verifier.as_ref().ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "no proof verifier configured for note spend verification"
                                .into(),
                        },
                        path.to_vec(),
                    )
                })?;
                // Public inputs for the note spending STARK:
                // nullifier || note_tree_root || value || asset_type
                //
                // SECURITY: value and asset_type are now included in the public inputs.
                // The STARK proof binds these via boundary constraints to the actual
                // note preimage columns. A spender cannot claim a different value/asset_type
                // than what is committed in the note — the proof verification will fail.
                // The conservation check uses these STARK-proven values, not the declared
                // effect fields (which are now the same thing, cryptographically bound).
                let mut public_inputs = Vec::with_capacity(80);
                public_inputs.extend_from_slice(&nullifier.0);
                public_inputs.extend_from_slice(note_tree_root);
                public_inputs.extend_from_slice(&value.to_le_bytes());
                public_inputs.extend_from_slice(&asset_type.to_le_bytes());
                if !verifier.verify(spending_proof, "note-spend", "note-tree", &public_inputs) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "NoteSpend spending proof verification failed".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Record for the note layer to process after turn commits.
                journal.record_note_spend(*nullifier);
                Ok(())
            }
            Effect::NoteCreate { commitment, .. } => {
                // Validate commitment is well-formed (non-zero).
                if commitment.0.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "null commitment in NoteCreate".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Note: zero-value notes are legitimate (e.g., NFTs where asset_type
                // is the unique identifier and value=0 represents ownership).
                // Record for the note layer to process after turn commits.
                journal.record_note_create(*commitment);
                Ok(())
            }

            // BridgeMint: verify the portable proof against trusted federation roots
            // and track the nullifier to prevent double-bridge attacks.
            // The destination_federation in the proof must match our local_federation_id
            // to prevent cross-federation replay (inflation bug).
            Effect::BridgeMint { portable_proof } => {
                let verify_stark = |nullifier: &[u8; 32],
                                    root: &[u8; 32],
                                    dest_federation: &[u8; 32],
                                    value: u64,
                                    asset_type: u64,
                                    proof_bytes: &[u8]|
                 -> Result<(), String> {
                    match &self.proof_verifier {
                        Some(verifier) => {
                            let mut public_inputs = Vec::with_capacity(112);
                            public_inputs.extend_from_slice(nullifier);
                            public_inputs.extend_from_slice(root);
                            public_inputs.extend_from_slice(dest_federation);
                            public_inputs.extend_from_slice(&value.to_le_bytes());
                            public_inputs.extend_from_slice(&asset_type.to_le_bytes());
                            // Use well-known constants for bridge-mint proofs so the
                            // verifier can distinguish them from authorization proofs.
                            // action = "bridge-mint", resource = hex(destination_federation).
                            let dest_hex: String =
                                dest_federation.iter().map(|b| format!("{b:02x}")).collect();
                            if verifier.verify(
                                proof_bytes,
                                "bridge-mint",
                                &dest_hex,
                                &public_inputs,
                            ) {
                                Ok(())
                            } else {
                                Err("STARK spending proof verification failed".to_string())
                            }
                        }
                        None => {
                            Err("no proof verifier configured for bridge mint verification"
                                .to_string())
                        }
                    }
                };

                pyana_cell::note_bridge::verify_portable_note(
                    portable_proof,
                    &self.local_federation_id,
                    &self.trusted_federation_roots,
                    verify_stark,
                )
                .map_err(|e| {
                    (
                        TurnError::BridgeMintFailed {
                            reason: e.to_string(),
                        },
                        path.to_vec(),
                    )
                })?;

                self.bridged_nullifiers
                    .lock()
                    .unwrap()
                    .insert(portable_proof.nullifier)
                    .map_err(|e| {
                        (
                            TurnError::BridgeMintFailed {
                                reason: e.to_string(),
                            },
                            path.to_vec(),
                        )
                    })?;

                // Record the insertion so it can be rolled back on turn failure.
                // Without this, an attacker could craft a turn with BridgeMint +
                // deliberate failure to permanently burn a nullifier without minting.
                journal.record_bridged_nullifier_inserted(portable_proof.nullifier);

                Ok(())
            }

            // BridgeLock: Phase 1 — lock a note for conditional cross-federation transfer.
            // The note's nullifier is committed-to but NOT added to the permanent set.
            // Instead a PendingBridge record is created in pending_bridges.
            Effect::BridgeLock {
                nullifier,
                destination,
                value,
                asset_type,
                timeout_height,
                spending_proof,
            } => {
                let mut pending = self.pending_bridges.lock().unwrap();
                pyana_cell::note_bridge::initiate_bridge(
                    *nullifier,
                    *destination,
                    *value,
                    *asset_type,
                    *timeout_height,
                    spending_proof.clone(),
                    &mut pending,
                )
                .map_err(|e| {
                    (
                        TurnError::BridgeLockFailed {
                            reason: e.to_string(),
                        },
                        path.to_vec(),
                    )
                })?;
                Ok(())
            }

            // BridgeFinalize: Phase 3 — present a destination receipt to finalize the burn.
            Effect::BridgeFinalize { nullifier, receipt } => {
                let mut pending = self.pending_bridges.lock().unwrap();
                let mut bridged = self.bridged_nullifiers.lock().unwrap();
                pyana_cell::note_bridge::finalize_bridge(
                    nullifier,
                    receipt,
                    &self.trusted_destination_keys,
                    &mut pending,
                    &mut bridged,
                )
                .map_err(|e| {
                    (
                        TurnError::BridgeFinalizeFailed {
                            reason: e.to_string(),
                        },
                        path.to_vec(),
                    )
                })?;
                Ok(())
            }

            // BridgeCancel: Phase 4 — cancel a bridge after timeout (value returned to owner).
            Effect::BridgeCancel { nullifier } => {
                let mut pending = self.pending_bridges.lock().unwrap();
                pyana_cell::note_bridge::cancel_bridge(nullifier, self.block_height, &mut pending)
                    .map_err(|e| {
                        (
                            TurnError::BridgeCancelFailed {
                                reason: e.to_string(),
                            },
                            path.to_vec(),
                        )
                    })?;
                Ok(())
            }

            // Obligation effects: validate structure, enforce balance movement,
            // and record for the obligation registry.
            Effect::CreateObligation {
                beneficiary,
                condition: _,
                deadline_height,
                stake,
                stake_amount,
            } => {
                // Validate beneficiary cell exists.
                if ledger.get(beneficiary).is_none() {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "obligation beneficiary cell not found".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Validate deadline is in the future.
                if *deadline_height <= self.block_height {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "obligation deadline must be in the future".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Validate deadline is within acceptable bounds.
                if let Err(reason) = crate::obligation::validate_obligation_deadline(
                    *deadline_height,
                    self.block_height,
                ) {
                    return Err((TurnError::InvalidEffect { reason }, path.to_vec()));
                }
                // Validate stake commitment is non-zero.
                if stake.0.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "obligation stake commitment is null".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Validate stake_amount is non-zero.
                if *stake_amount == 0 {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "obligation stake_amount must be non-zero".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Lock stake_amount from the obligor's (action_target's) balance.
                let obligor_cell = ledger.get(action_target).ok_or_else(|| {
                    (
                        TurnError::CellNotFound { id: *action_target },
                        path.to_vec(),
                    )
                })?;
                if obligor_cell.state.balance() < *stake_amount {
                    return Err((
                        TurnError::InsufficientBalance {
                            cell: *action_target,
                            required: *stake_amount,
                            available: obligor_cell.state.balance(),
                        },
                        path.to_vec(),
                    ));
                }
                let old_balance = obligor_cell.state.balance();
                journal.record_set_balance(*action_target, old_balance);
                ledger.get_mut(action_target).unwrap().state.set_balance(old_balance - *stake_amount);

                // Derive obligation ID and store in registry.
                let obligation_id = {
                    let mut hasher = blake3::Hasher::new_derive_key("pyana-obligation-id-v1");
                    hasher.update(action_target.as_bytes());
                    hasher.update(beneficiary.as_bytes());
                    hasher.update(&deadline_height.to_le_bytes());
                    hasher.update(&stake.0);
                    *hasher.finalize().as_bytes()
                };
                {
                    let mut obligations = self.obligations.lock().unwrap();
                    obligations.insert(
                        obligation_id,
                        ObligationRecord {
                            obligor: *action_target,
                            beneficiary: *beneficiary,
                            deadline_height: *deadline_height,
                            stake_amount: *stake_amount,
                            resolved: false,
                        },
                    );
                }
                // Record the insertion so it is rolled back on turn failure.
                journal.record_obligation_inserted(obligation_id);

                // The actor (action_target) is the obligor.
                journal.record_obligation_created(
                    *action_target,
                    *beneficiary,
                    *deadline_height,
                    *stake,
                );
                Ok(())
            }
            Effect::FulfillObligation {
                obligation_id,
                proof,
            } => {
                // Validate obligation_id is non-zero.
                if obligation_id.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "null obligation_id in FulfillObligation".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Look up the obligation and return the locked stake to the obligor.
                let record = {
                    let obligations = self.obligations.lock().unwrap();
                    obligations.get(obligation_id).cloned()
                };
                let record = record.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "obligation not found".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                if record.resolved {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "obligation already resolved".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // ACCESS CONTROL: Only the obligor (original creator) can fulfill
                // their own obligation. Without this check, anyone could fulfill
                // and return the stake to the obligor, defeating the obligation's purpose.
                if *action_target != record.obligor {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "only the obligor can fulfill their own obligation".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the deadline has not passed (fulfillment must be before deadline).
                if self.block_height > record.deadline_height {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "obligation deadline has passed, cannot fulfill".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the fulfillment proof if a proof verifier is configured and
                // a STARK proof is provided in the ConditionProof.
                if let crate::conditional::ConditionProof::StarkProof { proof_bytes, .. } = proof {
                    if !proof_bytes.is_empty() {
                        if let Some(verifier) = &self.proof_verifier {
                            if !verifier.verify(
                                proof_bytes,
                                "obligation-fulfill",
                                "obligation",
                                obligation_id,
                            ) {
                                return Err((
                                    TurnError::InvalidEffect {
                                        reason: "obligation fulfillment proof verification failed"
                                            .into(),
                                    },
                                    path.to_vec(),
                                ));
                            }
                        }
                        // If no verifier configured but proof is provided, that's acceptable
                        // (fail-open for the proof, but access control still enforced above).
                    }
                }
                // Return locked stake to the obligor.
                let obligor_cell = ledger.get(&record.obligor).ok_or_else(|| {
                    (
                        TurnError::CellNotFound { id: record.obligor },
                        path.to_vec(),
                    )
                })?;
                let old_balance = obligor_cell.state.balance();
                journal.record_set_balance(record.obligor, old_balance);
                ledger.get_mut(&record.obligor).unwrap().state.set_balance(old_balance + record.stake_amount);
                // Mark as resolved.
                {
                    let mut obligations = self.obligations.lock().unwrap();
                    if let Some(ob) = obligations.get_mut(obligation_id) {
                        ob.resolved = true;
                    }
                }
                journal.record_obligation_fulfilled(*obligation_id);
                Ok(())
            }
            Effect::SlashObligation { obligation_id } => {
                // Validate obligation_id is non-zero.
                if obligation_id.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "null obligation_id in SlashObligation".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Look up the obligation and transfer the locked stake to the beneficiary.
                let record = {
                    let obligations = self.obligations.lock().unwrap();
                    obligations.get(obligation_id).cloned()
                };
                let record = record.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "obligation not found".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                if record.resolved {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "obligation already resolved".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Slashing is only valid after the deadline has passed.
                if self.block_height <= record.deadline_height {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "obligation deadline has not passed, cannot slash".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Transfer locked stake to beneficiary.
                let beneficiary_cell = ledger.get(&record.beneficiary).ok_or_else(|| {
                    (
                        TurnError::CellNotFound {
                            id: record.beneficiary,
                        },
                        path.to_vec(),
                    )
                })?;
                let old_ben_balance = beneficiary_cell.state.balance();
                journal.record_set_balance(record.beneficiary, old_ben_balance);
                ledger.get_mut(&record.beneficiary).unwrap().state.set_balance(old_ben_balance + record.stake_amount);
                // Mark as resolved.
                {
                    let mut obligations = self.obligations.lock().unwrap();
                    if let Some(ob) = obligations.get_mut(obligation_id) {
                        ob.resolved = true;
                    }
                }
                journal.record_obligation_slashed(*obligation_id);
                Ok(())
            }

            // Escrow effects: conditional settlement with timeout refund.
            Effect::CreateEscrow {
                cell,
                recipient,
                amount,
                condition,
                timeout_height,
                escrow_id,
            } => {
                // SECURITY: The cell field must match action_target to prevent
                // locking someone else's funds via an action targeting a different cell.
                if cell != action_target {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "CreateEscrow cell must match action target".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Validate recipient cell exists.
                if ledger.get(recipient).is_none() {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "escrow recipient cell not found".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Validate timeout is in the future.
                if *timeout_height <= self.block_height {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "escrow timeout_height must be in the future".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Validate amount is non-zero.
                if *amount == 0 {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "escrow amount must be non-zero".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Validate escrow_id is non-zero.
                if escrow_id.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "escrow_id is null".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Check escrow_id is not already in use.
                {
                    let escrows = self.escrows.lock().unwrap();
                    if escrows.contains_key(escrow_id) {
                        return Err((
                            TurnError::InvalidEffect {
                                reason: "escrow_id already exists".into(),
                            },
                            path.to_vec(),
                        ));
                    }
                }
                // Validate the creator cell exists and has sufficient balance.
                let creator_cell = ledger
                    .get(cell)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *cell }, path.to_vec()))?;
                if creator_cell.state.balance() < *amount {
                    return Err((
                        TurnError::InsufficientBalance {
                            cell: *cell,
                            required: *amount,
                            available: creator_cell.state.balance(),
                        },
                        path.to_vec(),
                    ));
                }
                // Lock the funds: subtract from creator.
                let old_balance = creator_cell.state.balance();
                journal.record_set_balance(*cell, old_balance);
                ledger.get_mut(cell).unwrap().state.set_balance(old_balance - *amount);

                // Store escrow record.
                {
                    let mut escrows = self.escrows.lock().unwrap();
                    escrows.insert(
                        *escrow_id,
                        EscrowRecord {
                            creator: *cell,
                            recipient: *recipient,
                            amount: *amount,
                            condition: condition.clone(),
                            timeout_height: *timeout_height,
                            resolved: false,
                        },
                    );
                }
                // Record the insertion so it is rolled back on turn failure.
                journal.record_escrow_inserted(*escrow_id);

                journal.record_escrow_created(*escrow_id, *cell, *recipient, *amount);
                Ok(())
            }

            Effect::ReleaseEscrow { escrow_id, proof } => {
                // Validate escrow_id is non-zero.
                if escrow_id.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "null escrow_id in ReleaseEscrow".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Look up the escrow.
                let record = {
                    let escrows = self.escrows.lock().unwrap();
                    escrows.get(escrow_id).cloned()
                };
                let record = record.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "escrow not found".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                if record.resolved {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "escrow already resolved".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the condition is met.
                match &record.condition {
                    EscrowCondition::ProofPresented { verification_key } => {
                        let proof_bytes = proof.as_ref().ok_or_else(|| {
                            (
                                TurnError::InvalidEffect {
                                    reason: "escrow release requires proof but none provided"
                                        .into(),
                                },
                                path.to_vec(),
                            )
                        })?;
                        if proof_bytes.is_empty() {
                            return Err((
                                TurnError::InvalidEffect {
                                    reason: "escrow release proof is empty".into(),
                                },
                                path.to_vec(),
                            ));
                        }
                        // Verify the proof using the configured verifier.
                        let verifier = self.proof_verifier.as_ref().ok_or_else(|| {
                            (
                                TurnError::InvalidEffect {
                                    reason: "no proof verifier configured for escrow release"
                                        .into(),
                                },
                                path.to_vec(),
                            )
                        })?;
                        if !verifier.verify(
                            proof_bytes,
                            "escrow-release",
                            "escrow",
                            verification_key,
                        ) {
                            return Err((
                                TurnError::InvalidEffect {
                                    reason: "escrow release proof verification failed".into(),
                                },
                                path.to_vec(),
                            ));
                        }
                    }
                    EscrowCondition::SignedByAll { signers } => {
                        // The proof field must contain concatenated 64-byte Ed25519 signatures
                        // (one per signer), each signing the escrow_id.
                        let proof_bytes = proof.as_ref().ok_or_else(|| {
                            (
                                TurnError::InvalidEffect {
                                    reason: "escrow release requires signatures but none provided"
                                        .into(),
                                },
                                path.to_vec(),
                            )
                        })?;
                        let expected_len = signers.len() * 64;
                        if proof_bytes.len() != expected_len {
                            return Err((
                                TurnError::InvalidEffect {
                                    reason: format!(
                                        "escrow release expected {} signature bytes, got {}",
                                        expected_len,
                                        proof_bytes.len()
                                    ),
                                },
                                path.to_vec(),
                            ));
                        }
                        // Verify each signature against the escrow_id.
                        for (i, signer_key) in signers.iter().enumerate() {
                            let sig_slice = &proof_bytes[i * 64..(i + 1) * 64];
                            let mut sig_bytes = [0u8; 64];
                            sig_bytes.copy_from_slice(sig_slice);
                            let signature = Signature::from_bytes(&sig_bytes);
                            let verifying_key =
                                VerifyingKey::from_bytes(signer_key).map_err(|_| {
                                    (
                                        TurnError::InvalidEffect {
                                            reason: format!(
                                                "invalid signer public key at index {}",
                                                i
                                            ),
                                        },
                                        path.to_vec(),
                                    )
                                })?;
                            use ed25519_dalek::Verifier;
                            verifying_key.verify(escrow_id, &signature).map_err(|_| {
                                (
                                    TurnError::InvalidEffect {
                                        reason: format!(
                                            "escrow release signature verification failed for signer {}",
                                            i
                                        ),
                                    },
                                    path.to_vec(),
                                )
                            })?;
                        }
                    }
                    EscrowCondition::PredicateSatisfied { predicate_hash } => {
                        // For predicate conditions, the proof must contain the 32-byte
                        // hash matching predicate_hash (simple equality check for now;
                        // in production this would invoke the predicate evaluator).
                        let proof_bytes = proof.as_ref().ok_or_else(|| {
                            (
                                TurnError::InvalidEffect {
                                    reason:
                                        "escrow release requires predicate proof but none provided"
                                            .into(),
                                },
                                path.to_vec(),
                            )
                        })?;
                        if proof_bytes.len() < 32 {
                            return Err((
                                TurnError::InvalidEffect {
                                    reason: "escrow predicate proof too short".into(),
                                },
                                path.to_vec(),
                            ));
                        }
                        let provided_hash: [u8; 32] = proof_bytes[..32].try_into().unwrap();
                        if provided_hash != *predicate_hash {
                            return Err((
                                TurnError::InvalidEffect {
                                    reason: "escrow predicate hash mismatch".into(),
                                },
                                path.to_vec(),
                            ));
                        }
                    }
                }
                // Condition satisfied: transfer amount to recipient.
                let recipient_cell = ledger.get(&record.recipient).ok_or_else(|| {
                    (
                        TurnError::CellNotFound {
                            id: record.recipient,
                        },
                        path.to_vec(),
                    )
                })?;
                let old_recipient_balance = recipient_cell.state.balance();
                journal.record_set_balance(record.recipient, old_recipient_balance);
                ledger.get_mut(&record.recipient).unwrap().state.set_balance(old_recipient_balance + record.amount);
                // Mark escrow as resolved.
                {
                    let mut escrows = self.escrows.lock().unwrap();
                    if let Some(esc) = escrows.get_mut(escrow_id) {
                        esc.resolved = true;
                    }
                }
                journal.record_escrow_released(*escrow_id);
                Ok(())
            }

            Effect::RefundEscrow { escrow_id } => {
                // Validate escrow_id is non-zero.
                if escrow_id.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "null escrow_id in RefundEscrow".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Look up the escrow.
                let record = {
                    let escrows = self.escrows.lock().unwrap();
                    escrows.get(escrow_id).cloned()
                };
                let record = record.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "escrow not found".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                if record.resolved {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "escrow already resolved".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Check timeout has passed.
                if self.block_height <= record.timeout_height {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "escrow timeout has not passed, cannot refund".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Return amount to creator.
                let creator_cell = ledger.get(&record.creator).ok_or_else(|| {
                    (
                        TurnError::CellNotFound { id: record.creator },
                        path.to_vec(),
                    )
                })?;
                let old_creator_balance = creator_cell.state.balance();
                journal.record_set_balance(record.creator, old_creator_balance);
                ledger.get_mut(&record.creator).unwrap().state.set_balance(old_creator_balance + record.amount);
                // Mark escrow as resolved.
                {
                    let mut escrows = self.escrows.lock().unwrap();
                    if let Some(esc) = escrows.get_mut(escrow_id) {
                        esc.resolved = true;
                    }
                }
                journal.record_escrow_refunded(*escrow_id);
                Ok(())
            }

            // Committed escrow effects: privacy-preserving conditional settlement.
            Effect::CreateCommittedEscrow {
                creator_commitment,
                recipient_commitment,
                value_commitment,
                condition_commitment,
                timeout_height,
                escrow_id,
                range_proof,
                amount,
            } => {
                // Validate escrow_id is non-zero.
                if escrow_id.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow_id is null".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Validate timeout is in the future.
                if *timeout_height <= self.block_height {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow timeout_height must be in the future".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Validate amount is non-zero.
                if *amount == 0 {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow amount must be non-zero".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Validate commitments are non-zero (prevent trivial commitments).
                if creator_commitment.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow creator_commitment is null".into(),
                        },
                        path.to_vec(),
                    ));
                }
                if recipient_commitment.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow recipient_commitment is null".into(),
                        },
                        path.to_vec(),
                    ));
                }
                if condition_commitment.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow condition_commitment is null".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Validate range proof is present (non-empty).
                if range_proof.is_empty() {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow range_proof is empty".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the range proof if a proof verifier is configured.
                if let Some(verifier) = &self.proof_verifier {
                    if !verifier.verify(
                        range_proof,
                        "committed-escrow-range",
                        "value-commitment",
                        &value_commitment.0,
                    ) {
                        return Err((
                            TurnError::InvalidEffect {
                                reason: "committed escrow range proof verification failed".into(),
                            },
                            path.to_vec(),
                        ));
                    }
                }
                // Verify escrow_id is correctly derived from commitments.
                let expected_id = CommittedEscrow::compute_escrow_id(
                    creator_commitment,
                    recipient_commitment,
                    value_commitment,
                    condition_commitment,
                    *timeout_height,
                );
                if *escrow_id != expected_id {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow_id does not match derived value".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Check escrow_id is not already in use (in either escrow map).
                {
                    let escrows = self.escrows.lock().unwrap();
                    if escrows.contains_key(escrow_id) {
                        return Err((
                            TurnError::InvalidEffect {
                                reason: "escrow_id already exists (cleartext)".into(),
                            },
                            path.to_vec(),
                        ));
                    }
                }
                {
                    let committed = self.committed_escrows.lock().unwrap();
                    if committed.contains_key(escrow_id) {
                        return Err((
                            TurnError::InvalidEffect {
                                reason: "committed escrow_id already exists".into(),
                            },
                            path.to_vec(),
                        ));
                    }
                }
                // Lock the funds from the creator (action_target).
                let creator_cell = ledger.get(action_target).ok_or_else(|| {
                    (
                        TurnError::CellNotFound { id: *action_target },
                        path.to_vec(),
                    )
                })?;
                if creator_cell.state.balance() < *amount {
                    return Err((
                        TurnError::InsufficientBalance {
                            cell: *action_target,
                            required: *amount,
                            available: creator_cell.state.balance(),
                        },
                        path.to_vec(),
                    ));
                }
                let old_balance = creator_cell.state.balance();
                journal.record_set_balance(*action_target, old_balance);
                ledger.get_mut(action_target).unwrap().state.set_balance(old_balance - *amount);

                // Store committed escrow record.
                let record = CommittedEscrow {
                    creator_commitment: *creator_commitment,
                    recipient_commitment: *recipient_commitment,
                    value_commitment: value_commitment.clone(),
                    condition_commitment: *condition_commitment,
                    timeout_height: *timeout_height,
                    escrow_id: *escrow_id,
                    range_proof: range_proof.clone(),
                    resolved: false,
                };
                {
                    let mut committed = self.committed_escrows.lock().unwrap();
                    committed.insert(*escrow_id, record);
                }
                // Store the amount in the side-table for settlement.
                {
                    let mut amounts = self.committed_escrow_amounts.lock().unwrap();
                    amounts.insert(*escrow_id, *amount);
                }
                // Record insertion for rollback.
                journal.record_committed_escrow_inserted(*escrow_id);
                journal.record_committed_escrow_created(*escrow_id, *amount);
                Ok(())
            }

            Effect::ReleaseCommittedEscrow {
                escrow_id,
                claim_auth,
                recipient,
            } => {
                // Validate escrow_id is non-zero.
                if escrow_id.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "null escrow_id in ReleaseCommittedEscrow".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Look up the committed escrow.
                let record = {
                    let committed = self.committed_escrows.lock().unwrap();
                    committed.get(escrow_id).cloned()
                };
                let record = record.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "committed escrow not found".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                if record.resolved {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow already resolved".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the recipient cell matches the claim and exists in ledger.
                if *recipient != claim_auth.cell_id {
                    return Err((
                        TurnError::InvalidEffect {
                            reason:
                                "committed escrow release: recipient does not match claim cell_id"
                                    .into(),
                        },
                        path.to_vec(),
                    ));
                }
                let recipient_cell_ref = ledger
                    .get(recipient)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *recipient }, path.to_vec()))?;
                let recipient_pubkey = recipient_cell_ref.public_key();
                // Verify the claim_auth against the recipient_commitment.
                if !verify_escrow_claim(
                    claim_auth,
                    &record.recipient_commitment,
                    escrow_id,
                    &recipient_pubkey,
                ) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow release: claim authorization failed".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Retrieve the escrowed amount from the side-table.
                let amount = {
                    let amounts = self.committed_escrow_amounts.lock().unwrap();
                    amounts.get(escrow_id).copied()
                };
                let amount = amount.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "committed escrow amount not found (internal error)".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                // Credit the escrowed amount to the recipient.
                let recipient_cell = ledger.get(recipient).unwrap();
                let old_balance = recipient_cell.state.balance();
                journal.record_set_balance(*recipient, old_balance);
                ledger.get_mut(recipient).unwrap().state.set_balance(old_balance + amount);
                // Mark as resolved.
                {
                    let mut committed = self.committed_escrows.lock().unwrap();
                    if let Some(esc) = committed.get_mut(escrow_id) {
                        esc.resolved = true;
                    }
                }
                journal.record_committed_escrow_released(*escrow_id);
                Ok(())
            }

            Effect::RefundCommittedEscrow {
                escrow_id,
                claim_auth,
                creator,
            } => {
                // Validate escrow_id is non-zero.
                if escrow_id.iter().all(|&b| b == 0) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "null escrow_id in RefundCommittedEscrow".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Look up the committed escrow.
                let record = {
                    let committed = self.committed_escrows.lock().unwrap();
                    committed.get(escrow_id).cloned()
                };
                let record = record.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "committed escrow not found".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                if record.resolved {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow already resolved".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Check timeout has passed.
                if self.block_height <= record.timeout_height {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow timeout has not passed, cannot refund".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the creator cell matches the claim and exists in ledger.
                if *creator != claim_auth.cell_id {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow refund: creator does not match claim cell_id"
                                .into(),
                        },
                        path.to_vec(),
                    ));
                }
                let creator_cell_ref = ledger
                    .get(creator)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *creator }, path.to_vec()))?;
                let creator_pubkey = creator_cell_ref.public_key();
                // Verify the claim_auth against the creator_commitment.
                if !verify_escrow_claim(
                    claim_auth,
                    &record.creator_commitment,
                    escrow_id,
                    &creator_pubkey,
                ) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow refund: claim authorization failed".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Return the escrowed amount to the creator.
                let amount = {
                    let amounts = self.committed_escrow_amounts.lock().unwrap();
                    amounts.get(escrow_id).copied()
                };
                let amount = amount.ok_or_else(|| {
                    (
                        TurnError::InvalidEffect {
                            reason: "committed escrow amount not found (internal error)".into(),
                        },
                        path.to_vec(),
                    )
                })?;
                let creator_cell = ledger.get(creator).unwrap();
                let old_balance = creator_cell.state.balance();
                journal.record_set_balance(*creator, old_balance);
                ledger.get_mut(creator).unwrap().state.set_balance(old_balance + amount);
                // Mark as resolved.
                {
                    let mut committed = self.committed_escrows.lock().unwrap();
                    if let Some(esc) = committed.get_mut(escrow_id) {
                        esc.resolved = true;
                    }
                }
                journal.record_committed_escrow_refunded(*escrow_id);
                Ok(())
            }

            // ExerciseViaCapability: one-step evaluation map.
            // Look up cap_slot in actor's c-list, verify permissions, execute
            // inner_effects against the capability's target cell.
            Effect::ExerciseViaCapability {
                cap_slot,
                inner_effects,
            } => {
                let actor_cell = ledger
                    .get(actor)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;

                // Look up the capability by slot.
                let cap = actor_cell
                    .capabilities
                    .lookup(*cap_slot)
                    .cloned()
                    .ok_or_else(|| {
                        (
                            TurnError::CapabilityNotHeld {
                                actor: *actor,
                                target: CellId::from_bytes([0u8; 32]), // slot doesn't exist
                            },
                            path.to_vec(),
                        )
                    })?;

                let cap_target = cap.target;

                // Check capability expiry.
                if let Some(expires_at) = cap.expires_at {
                    if self.block_height > expires_at {
                        return Err((
                            TurnError::CapabilityNotHeld {
                                actor: *actor,
                                target: cap_target,
                            },
                            path.to_vec(),
                        ));
                    }
                }

                // Check revocation channel: if the capability has a breadstuff that
                // matches a revocation channel, verify the channel is still active.
                if let Some(ref channels) = self.revocation_channels {
                    if let Some(breadstuff) = &cap.breadstuff {
                        // Use the breadstuff as a potential channel_id (capabilities
                        // gated by a revocation channel store the channel_id as breadstuff).
                        if let Err(_) = channels.check_exercise_permitted(
                            breadstuff,
                            self.block_height,
                            self.block_height, // assume fresh check at current height
                            self.max_introduction_lifetime,
                        ) {
                            // Check if this is actually a registered channel (not just any breadstuff).
                            if channels.get(breadstuff).is_some() {
                                return Err((
                                    TurnError::CapabilityRevoked {
                                        actor: *actor,
                                        channel_id: *breadstuff,
                                        tripped_at: self.block_height,
                                    },
                                    path.to_vec(),
                                ));
                            }
                        }
                    }
                }

                // Verify the target cell exists.
                let target_cell_ref = ledger
                    .get(&cap_target)
                    .ok_or_else(|| (TurnError::CellNotFound { id: cap_target }, path.to_vec()))?;

                // Permission check: the capability's permissions must allow the operations.
                // If the capability requires Impossible, reject.
                if matches!(cap.permissions, pyana_cell::AuthRequired::Impossible) {
                    return Err((
                        TurnError::PermissionDenied {
                            cell: cap_target,
                            action: "ExerciseViaCapability".to_string(),
                            required: pyana_cell::AuthRequired::Impossible,
                        },
                        path.to_vec(),
                    ));
                }

                // Also check that the capability's permission level satisfies the
                // TARGET CELL's requirements for each inner effect's operation.
                // This prevents bypassing target cell permissions via capability exercise.
                for inner_effect in inner_effects.iter() {
                    let required_perm_action = match inner_effect {
                        Effect::SetField { .. } => {
                            Some((pyana_cell::permissions::Action::SetState, "SetState"))
                        }
                        Effect::Transfer { from, .. } if from == &cap_target => {
                            Some((pyana_cell::permissions::Action::Send, "Send"))
                        }
                        Effect::IncrementNonce { .. } => Some((
                            pyana_cell::permissions::Action::IncrementNonce,
                            "IncrementNonce",
                        )),
                        Effect::GrantCapability { .. } => {
                            Some((pyana_cell::permissions::Action::Delegate, "Delegate"))
                        }
                        Effect::RevokeCapability { .. } => {
                            Some((pyana_cell::permissions::Action::Delegate, "Delegate"))
                        }
                        Effect::SetPermissions { .. } => Some((
                            pyana_cell::permissions::Action::SetPermissions,
                            "SetPermissions",
                        )),
                        Effect::SetVerificationKey { .. } => Some((
                            pyana_cell::permissions::Action::SetVerificationKey,
                            "SetVerificationKey",
                        )),
                        _ => None,
                    };

                    if let Some((perm_action, action_name)) = required_perm_action {
                        let target_required = target_cell_ref.permissions.for_action(perm_action);
                        // The target cell's permission must be satisfiable by the capability's
                        // permission level. If the target requires Impossible, always reject.
                        // If the target requires Signature/Proof/Either but the capability only
                        // grants None-level access, that's insufficient.
                        if matches!(target_required, AuthRequired::Impossible) {
                            return Err((
                                TurnError::PermissionDenied {
                                    cell: cap_target,
                                    action: action_name.to_string(),
                                    required: target_required.clone(),
                                },
                                path.to_vec(),
                            ));
                        }
                        // If the target requires auth (Signature/Proof/Either) and the
                        // capability's permission level is weaker (None), reject.
                        // The capability permission acts as the auth level the actor provides.
                        if !matches!(target_required, AuthRequired::None) {
                            // The capability must be at least as strong as what the target requires.
                            if !cap.permissions.is_narrower_or_equal(target_required) {
                                return Err((
                                    TurnError::PermissionDenied {
                                        cell: cap_target,
                                        action: action_name.to_string(),
                                        required: target_required.clone(),
                                    },
                                    path.to_vec(),
                                ));
                            }
                        }
                    }
                }

                // Facet enforcement: if the capability has an allowed_effects mask,
                // verify that every inner effect's kind is permitted by the mask.
                // This implements E-language facets — a restricted view of the target
                // cell's interface through this capability.
                if let Some(mask) = cap.allowed_effects {
                    if mask != 0 {
                        for inner_effect in inner_effects.iter() {
                            let effect_bit = inner_effect.effect_kind_mask();
                            if effect_bit & mask == 0 {
                                return Err((
                                    TurnError::FacetViolation {
                                        actor: *actor,
                                        target: cap_target,
                                        cap_slot: *cap_slot,
                                        attempted_effect: format!(
                                            "{:?}",
                                            std::mem::discriminant(inner_effect)
                                        ),
                                        allowed_mask: mask,
                                    },
                                    path.to_vec(),
                                ));
                            }
                        }
                    }
                }

                // Execute each inner effect against the capability's target cell.
                for inner_effect in inner_effects {
                    self.apply_effect(inner_effect, ledger, path, &cap_target, actor, journal)?;
                }

                Ok(())
            }

            // PipelinedSend must be resolved by the pipeline executor's resolution pass
            // before the turn reaches apply_effect. If we get here, it means the turn
            // was executed outside of a pipeline without resolution — which is a bug.
            Effect::PipelinedSend { target, .. } => Err((
                TurnError::PreconditionFailed {
                    description: format!(
                        "unresolved PipelinedSend to EventualRef(source {:02x}{:02x}.., slot {}); \
                         turn must be executed within a pipeline",
                        target.source_turn[0], target.source_turn[1], target.output_slot
                    ),
                },
                path.to_vec(),
            )),

            // === Sealer/Unsealer effects (E-style rights amplification) ===
            Effect::CreateSealPair {
                sealer_holder,
                unsealer_holder,
            } => {
                if ledger.get(sealer_holder).is_none() {
                    return Err((
                        TurnError::CellNotFound { id: *sealer_holder },
                        path.to_vec(),
                    ));
                }
                if ledger.get(unsealer_holder).is_none() {
                    return Err((
                        TurnError::CellNotFound {
                            id: *unsealer_holder,
                        },
                        path.to_vec(),
                    ));
                }

                let pair = pyana_cell::SealPair::generate();

                // Grant sealer capability (breadstuff = sealer_key).
                let sealer_cap_id = Self::seal_capability_id(&pair.id, true);
                let sealer_cell = ledger.get_mut(sealer_holder).unwrap();
                let sealer_slot = sealer_cell
                    .capabilities
                    .grant_with_breadstuff(
                        sealer_cap_id,
                        pyana_cell::AuthRequired::None,
                        Some(pair.sealer_public),
                    )
                    .ok_or_else(|| {
                        (
                            TurnError::CapabilitySlotOverflow {
                                cell: *sealer_holder,
                            },
                            path.to_vec(),
                        )
                    })?;
                journal.record_grant_capability(*sealer_holder, sealer_slot);

                // Grant unsealer capability (breadstuff = sealer_key for symmetric decrypt).
                let unsealer_cap_id = Self::seal_capability_id(&pair.id, false);
                let unsealer_cell = ledger.get_mut(unsealer_holder).unwrap();
                let unsealer_slot = unsealer_cell
                    .capabilities
                    .grant_with_breadstuff(
                        unsealer_cap_id,
                        pyana_cell::AuthRequired::None,
                        Some(pair.unsealer_secret),
                    )
                    .ok_or_else(|| {
                        (
                            TurnError::CapabilitySlotOverflow {
                                cell: *unsealer_holder,
                            },
                            path.to_vec(),
                        )
                    })?;
                journal.record_grant_capability(*unsealer_holder, unsealer_slot);

                Ok(())
            }

            Effect::Seal {
                pair_id,
                capability,
            } => {
                let sealer_cap_id = Self::seal_capability_id(pair_id, true);
                let actor_cell = ledger
                    .get(actor)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
                let sealer_cap = actor_cell
                    .capabilities
                    .lookup_by_target(&sealer_cap_id)
                    .ok_or_else(|| {
                        (
                            TurnError::CapabilityNotHeld {
                                actor: *actor,
                                target: sealer_cap_id,
                            },
                            path.to_vec(),
                        )
                    })?;
                // Extract sealer public key from breadstuff and produce sealed box.
                let sealer_public = sealer_cap.breadstuff.ok_or_else(|| {
                    (
                        TurnError::InvalidAuthorization {
                            reason: "sealer capability missing key material".to_string(),
                        },
                        path.to_vec(),
                    )
                })?;
                let seal_pair = pyana_cell::SealPair::sealer_only(sealer_public);
                let sealed = seal_pair.seal(capability);
                // Store seal commitment in actor's field 7 for on-chain discoverability.
                let actor_mut = ledger
                    .get_mut(actor)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
                journal.record_set_field(*actor, 7, actor_mut.state.fields[7]);
                actor_mut.state.fields[7] = sealed.commitment;
                if actor_mut.state.commitments[7].is_some() {
                    actor_mut.state.commitments[7] = None;
                }
                Ok(())
            }

            Effect::Introduce {
                introducer,
                recipient,
                target,
                permissions,
            } => {
                let intro_cell = ledger
                    .get(introducer)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *introducer }, path.to_vec()))?;
                if !intro_cell.capabilities.has_access(recipient) {
                    return Err((
                        TurnError::IntroductionDenied {
                            introducer: *introducer,
                            recipient: *recipient,
                            target: *target,
                            reason: "introducer has no capability to recipient".to_string(),
                        },
                        path.to_vec(),
                    ));
                }
                let held_cap = intro_cell
                    .capabilities
                    .lookup_by_target(target)
                    .ok_or_else(|| {
                        (
                            TurnError::IntroductionDenied {
                                introducer: *introducer,
                                recipient: *recipient,
                                target: *target,
                                reason: "introducer has no capability to target".to_string(),
                            },
                            path.to_vec(),
                        )
                    })?;
                if !pyana_cell::is_attenuation(&held_cap.permissions, permissions) {
                    return Err((
                        TurnError::IntroductionDenied {
                            introducer: *introducer,
                            recipient: *recipient,
                            target: *target,
                            reason:
                                "granted permissions exceed introducer's own (amplification denied)"
                                    .to_string(),
                        },
                        path.to_vec(),
                    ));
                }
                // Consent check: the target cell must allow delegation (delegate != Impossible).
                let target_cell = ledger
                    .get(target)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
                if target_cell.permissions.delegate == pyana_cell::AuthRequired::Impossible {
                    return Err((
                        TurnError::IntroductionDenied {
                            introducer: *introducer,
                            recipient: *recipient,
                            target: *target,
                            reason: "target cell has delegate=Impossible (consent denied)"
                                .to_string(),
                        },
                        path.to_vec(),
                    ));
                }
                if ledger.get(recipient).is_none() {
                    return Err((TurnError::CellNotFound { id: *recipient }, path.to_vec()));
                }
                let recipient_cell = ledger.get_mut(recipient).unwrap();
                let expires_at = self.block_height + self.max_introduction_lifetime;
                let granted_slot = recipient_cell
                    .capabilities
                    .grant_with_expiry(*target, permissions.clone(), expires_at)
                    .ok_or_else(|| {
                        (
                            TurnError::CapabilitySlotOverflow { cell: *recipient },
                            path.to_vec(),
                        )
                    })?;
                journal.record_grant_capability(*recipient, granted_slot);
                Ok(())
            }

            Effect::Unseal {
                sealed_box,
                recipient,
            } => {
                if ledger.get(recipient).is_none() {
                    return Err((TurnError::CellNotFound { id: *recipient }, path.to_vec()));
                }

                let unsealer_cap_id = Self::seal_capability_id(&sealed_box.pair_id, false);
                let actor_cell = ledger
                    .get(actor)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
                let unsealer_cap = actor_cell
                    .capabilities
                    .lookup_by_target(&unsealer_cap_id)
                    .ok_or_else(|| {
                        (
                            TurnError::CapabilityNotHeld {
                                actor: *actor,
                                target: unsealer_cap_id,
                            },
                            path.to_vec(),
                        )
                    })?;
                let unsealer_secret = unsealer_cap.breadstuff.ok_or_else(|| {
                    (
                        TurnError::InvalidAuthorization {
                            reason: "unsealer capability missing key material".to_string(),
                        },
                        path.to_vec(),
                    )
                })?;

                let mut pair = pyana_cell::SealPair::from_keys([0u8; 32], unsealer_secret);
                pair.id = sealed_box.pair_id;

                match pair.unseal(sealed_box) {
                    Ok(cap) => {
                        let recipient_cell = ledger.get_mut(recipient).ok_or_else(|| {
                            (TurnError::CellNotFound { id: *recipient }, path.to_vec())
                        })?;
                        let granted_slot = recipient_cell
                            .capabilities
                            .grant_with_breadstuff(
                                cap.target,
                                cap.permissions.clone(),
                                cap.breadstuff,
                            )
                            .ok_or_else(|| {
                                (
                                    TurnError::CapabilitySlotOverflow { cell: *recipient },
                                    path.to_vec(),
                                )
                            })?;
                        journal.record_grant_capability(*recipient, granted_slot);
                        Ok(())
                    }
                    Err(_) => Err((
                        TurnError::InvalidAuthorization {
                            reason: "sealed box decryption/verification failed".to_string(),
                        },
                        path.to_vec(),
                    )),
                }
            }
            Effect::SpawnWithDelegation {
                child_public_key,
                child_token_id,
                max_staleness,
            } => {
                let parent_cell_data = ledger.get(action_target).ok_or_else(|| {
                    (
                        TurnError::CellNotFound { id: *action_target },
                        path.to_vec(),
                    )
                })?;
                let delegation_epoch = parent_cell_data.state.delegation_epoch();
                let now = self.current_timestamp as u64;
                let snapshot: Vec<pyana_cell::CapabilityRef> =
                    parent_cell_data.capabilities.iter().cloned().collect();

                let child_id = CellId::derive_raw(child_public_key, child_token_id);
                let mut child_cell = Cell::with_balance(*child_public_key, *child_token_id, 0);
                child_cell.delegate = Some(*action_target);
                let clist_bytes = postcard::to_allocvec(&snapshot).unwrap_or_default();
                let clist_commitment =
                    pyana_cell::DelegatedRef::compute_clist_commitment(&clist_bytes);
                child_cell.delegation = Some(pyana_cell::DelegatedRef::new(
                    *action_target,
                    child_id,
                    snapshot,
                    delegation_epoch,
                    now,
                    *max_staleness,
                    clist_commitment,
                    [0u8; 64], // Executor-internal delegation, signature verified by execution authority.
                ));

                ledger
                    .insert_cell(child_cell)
                    .map_err(|_| (TurnError::CellAlreadyExists { id: child_id }, path.to_vec()))?;
                journal.record_create_cell(child_id);
                Ok(())
            }

            Effect::RefreshDelegation => {
                let child_cell = ledger.get(action_target).ok_or_else(|| {
                    (
                        TurnError::CellNotFound { id: *action_target },
                        path.to_vec(),
                    )
                })?;
                let parent_id = child_cell.delegate.ok_or_else(|| {
                    (
                        TurnError::InvalidAuthorization {
                            reason: "cell has no delegate (parent) to refresh from".to_string(),
                        },
                        path.to_vec(),
                    )
                })?;
                let max_staleness = child_cell
                    .delegation
                    .as_ref()
                    .map(|d| d.max_staleness)
                    .unwrap_or(0);
                let old_delegation = child_cell.delegation.clone();

                let parent_cell_data = ledger
                    .get(&parent_id)
                    .ok_or_else(|| (TurnError::CellNotFound { id: parent_id }, path.to_vec()))?;
                let new_snapshot: Vec<pyana_cell::CapabilityRef> =
                    parent_cell_data.capabilities.iter().cloned().collect();
                let new_epoch = parent_cell_data.state.delegation_epoch();
                let now = self.current_timestamp as u64;

                let child_mut = ledger.get_mut(action_target).unwrap();
                journal.record_set_delegation(*action_target, old_delegation);
                let clist_bytes = postcard::to_allocvec(&new_snapshot).unwrap_or_default();
                let clist_commitment =
                    pyana_cell::DelegatedRef::compute_clist_commitment(&clist_bytes);
                child_mut.delegation = Some(pyana_cell::DelegatedRef::new(
                    parent_id,
                    *action_target,
                    new_snapshot,
                    new_epoch,
                    now,
                    max_staleness,
                    clist_commitment,
                    [0u8; 64], // Executor-internal delegation, signature verified by execution authority.
                ));
                Ok(())
            }

            Effect::RevokeDelegation { child } => {
                let child_cell = ledger
                    .get(child)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *child }, path.to_vec()))?;
                if child_cell.delegate != Some(*action_target) {
                    return Err((
                        TurnError::DelegationDenied {
                            parent: *action_target,
                            child_target: *child,
                        },
                        path.to_vec(),
                    ));
                }
                let old_child_delegation = child_cell.delegation.clone();

                let parent_mut = ledger.get_mut(action_target).unwrap();
                let old_epoch = parent_mut.state.delegation_epoch();
                journal.record_set_delegation_epoch(*action_target, old_epoch);
                parent_mut.state.bump_delegation_epoch();

                let child_mut = ledger.get_mut(child).unwrap();
                journal.record_set_delegation(*child, old_child_delegation);
                child_mut.delegation = None;
                Ok(())
            }

            Effect::MakeSovereign { cell } => {
                // Only the cell itself (as action target) can make itself sovereign.
                if cell != action_target {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "MakeSovereign cell must match action target".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Transition the cell from hosted to sovereign.
                ledger.make_sovereign(cell).map_err(|e| {
                    (
                        TurnError::InvalidEffect {
                            reason: format!("MakeSovereign failed: {e}"),
                        },
                        path.to_vec(),
                    )
                })?;
                Ok(())
            }

            Effect::CreateCellFromFactory {
                factory_vk,
                owner_pubkey,
                token_id,
                params,
            } => {
                // Validate the factory exists in the registry and the creation is within
                // the factory's declared constraints (program VK, capabilities, fields, mode, budget).
                //
                // For Derived/FromSet strategies, validate_and_record now checks that the
                // claimed program_vk is correctly derived or in the approved set.
                self.factory_registry
                    .borrow_mut()
                    .validate_and_record(factory_vk, params)
                    .map_err(|e| {
                        (
                            TurnError::InvalidEffect {
                                reason: format!("factory creation failed: {}", e),
                            },
                            path.to_vec(),
                        )
                    })?;

                // Determine the effective child VK to install.
                // For Derived strategy: compute the derived VK from factory_vk + params.
                // For FromSet strategy: use the claimed VK (already validated above).
                // For Fixed/None strategy: use params.program_vk as-is.
                let effective_vk = {
                    let registry = self.factory_registry.borrow();
                    let descriptor = registry.get(factory_vk);
                    match descriptor.and_then(|d| d.child_vk_strategy.as_ref()) {
                        Some(pyana_cell::factory::ChildVkStrategy::Derived { base_vk }) => {
                            let param_hash =
                                pyana_cell::factory::ChildVkStrategy::compute_param_hash(params);
                            Some(pyana_cell::factory::ChildVkStrategy::derive_child_vk(
                                base_vk,
                                &param_hash,
                            ))
                        }
                        Some(pyana_cell::factory::ChildVkStrategy::FromSet { .. }) => {
                            // Already validated; use the claimed VK.
                            params.program_vk
                        }
                        Some(pyana_cell::factory::ChildVkStrategy::Fixed(vk)) => *vk,
                        None => params.program_vk,
                    }
                };

                // Create the cell.
                let new_cell_id = CellId::derive_raw(owner_pubkey, token_id);
                let mut new_cell = match params.mode {
                    pyana_cell::CellMode::Hosted => Cell::new_hosted(*owner_pubkey, *token_id),
                    pyana_cell::CellMode::Sovereign => Cell::new(*owner_pubkey, *token_id),
                };

                // Set initial fields.
                for (idx, val) in &params.initial_fields {
                    let idx = *idx as usize;
                    if idx < pyana_cell::state::STATE_SLOTS {
                        // Zero-pad to 32 bytes.
                        let mut field = [0u8; 32];
                        field[..8].copy_from_slice(&val.to_le_bytes());
                        new_cell.state.fields[idx] = field;
                    }
                }

                // Install program VK — use effective_vk (which may be derived).
                if let Some(vk_hash) = &effective_vk {
                    new_cell.verification_key = Some(pyana_cell::VerificationKey::from_parts(
                        *vk_hash,
                        vk_hash.to_vec(), // Minimal VK data — the hash IS the identifier
                    ));
                }

                // Grant initial capabilities.
                for cap_grant in &params.initial_caps {
                    let target_id = match &cap_grant.target {
                        pyana_cell::factory::CapTarget::SelfCell => new_cell_id,
                        pyana_cell::factory::CapTarget::Specific(id) => *id,
                        pyana_cell::factory::CapTarget::Any => {
                            // "Any" in a grant means self for initial caps.
                            new_cell_id
                        }
                    };
                    new_cell
                        .capabilities
                        .grant(target_id, cap_grant.max_permissions.clone());
                }

                // Insert into ledger.
                ledger.insert_cell(new_cell).map_err(|_| {
                    (
                        TurnError::CellAlreadyExists { id: new_cell_id },
                        path.to_vec(),
                    )
                })?;
                journal.record_create_cell(new_cell_id);
                Ok(())
            }

            // ─── Queue Operations ─────────────────────────────────────────────
            Effect::QueueAllocate {
                capacity,
                program_vk,
            } => {
                // The queue cell is created with queue metadata encoded in state fields:
                //   field[0]: capacity (le bytes)
                //   field[1]: current length (0 initially)
                //   field[2]: owner cell id (action_target bytes)
                //   field[3]: program VK hash (if any)
                let cost = *capacity;
                let actor_cell = ledger
                    .get(actor)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
                if actor_cell.state.balance() < cost {
                    return Err((
                        TurnError::InsufficientBalance {
                            cell: *actor,
                            required: cost,
                            available: actor_cell.state.balance(),
                        },
                        path.to_vec(),
                    ));
                }

                // Derive a queue cell ID from the actor + capacity + nonce.
                let actor_nonce = ledger.get(actor).unwrap().state.nonce();
                let hash = blake3::hash(
                    &[
                        actor.as_bytes().as_slice(),
                        &capacity.to_le_bytes(),
                        &actor_nonce.to_le_bytes(),
                    ]
                    .concat(),
                );
                let queue_seed: [u8; 32] = *hash.as_bytes();
                let queue_token = [0u8; 32];
                let queue_id = CellId::derive_raw(&queue_seed, &queue_token);

                let mut queue_cell = pyana_cell::Cell::with_balance(queue_seed, queue_token, 0);
                // Encode capacity in field[0].
                queue_cell.state.fields[0][..8].copy_from_slice(&capacity.to_le_bytes());
                // field[1] = current length = 0 (already zero).
                // field[2] = owner (action_target).
                queue_cell.state.fields[2] = *action_target.as_bytes();
                // field[3] = program VK hash (if provided).
                if let Some(vk) = program_vk {
                    queue_cell.state.fields[3] = *vk;
                }
                // Open permissions on queue cell (managed by executor logic).
                queue_cell.permissions = pyana_cell::Permissions {
                    send: pyana_cell::AuthRequired::None,
                    receive: pyana_cell::AuthRequired::None,
                    set_state: pyana_cell::AuthRequired::None,
                    set_permissions: pyana_cell::AuthRequired::Impossible,
                    set_verification_key: pyana_cell::AuthRequired::Impossible,
                    increment_nonce: pyana_cell::AuthRequired::None,
                    delegate: pyana_cell::AuthRequired::None,
                    access: pyana_cell::AuthRequired::None,
                };

                ledger
                    .insert_cell(queue_cell)
                    .map_err(|_| (TurnError::CellAlreadyExists { id: queue_id }, path.to_vec()))?;
                journal.record_create_cell(queue_id);

                // Deduct the cost from the actor's balance.
                let old_balance = ledger.get(actor).unwrap().state.balance();
                journal.record_set_balance(*actor, old_balance);
                ledger.get_mut(actor).unwrap().state.set_balance(old_balance - cost);

                Ok(())
            }

            Effect::QueueEnqueue {
                queue,
                message_hash,
                deposit,
            } => {
                // Validate queue exists.
                let queue_cell = ledger
                    .get(queue)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *queue }, path.to_vec()))?;
                let capacity =
                    u64::from_le_bytes(queue_cell.state.fields[0][..8].try_into().unwrap());
                let current_len =
                    u64::from_le_bytes(queue_cell.state.fields[1][..8].try_into().unwrap());

                if current_len >= capacity {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: format!(
                                "queue {:?} is full ({}/{})",
                                queue, current_len, capacity
                            ),
                        },
                        path.to_vec(),
                    ));
                }

                // Check deposit: actor must have sufficient balance.
                let actor_cell = ledger
                    .get(actor)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
                if actor_cell.state.balance() < *deposit {
                    return Err((
                        TurnError::InsufficientBalance {
                            cell: *actor,
                            required: *deposit,
                            available: actor_cell.state.balance(),
                        },
                        path.to_vec(),
                    ));
                }

                // Deduct deposit from actor, credit to queue cell.
                let old_actor_balance = ledger.get(actor).unwrap().state.balance();
                let old_queue_balance = ledger.get(queue).unwrap().state.balance();
                journal.record_set_balance(*actor, old_actor_balance);
                journal.record_set_balance(*queue, old_queue_balance);
                ledger.get_mut(actor).unwrap().state.set_balance(old_actor_balance - *deposit);
                ledger.get_mut(queue).unwrap().state.set_balance(old_queue_balance + *deposit);

                // Increment queue length.
                let old_len_field = ledger.get(queue).unwrap().state.fields[1];
                let new_len = current_len + 1;
                journal.record_set_field(*queue, 1, old_len_field);
                let queue_mut = ledger.get_mut(queue).unwrap();
                queue_mut.state.fields[1][..8].copy_from_slice(&new_len.to_le_bytes());

                // Store the message hash in field[4] (latest enqueued message).
                let old_field4 = queue_mut.state.fields[4];
                journal.record_set_field(*queue, 4, old_field4);
                queue_mut.state.fields[4] = *message_hash;

                Ok(())
            }

            Effect::QueueDequeue { queue } => {
                let queue_cell = ledger
                    .get(queue)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *queue }, path.to_vec()))?;

                // Only the queue owner can dequeue.
                let owner_bytes = queue_cell.state.fields[2];
                if owner_bytes != *action_target.as_bytes() {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "only the queue owner can dequeue".to_string(),
                        },
                        path.to_vec(),
                    ));
                }

                let current_len =
                    u64::from_le_bytes(queue_cell.state.fields[1][..8].try_into().unwrap());
                if current_len == 0 {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "queue is empty, cannot dequeue".to_string(),
                        },
                        path.to_vec(),
                    ));
                }

                // Decrement queue length.
                let old_len_field = queue_cell.state.fields[1];
                let new_len = current_len - 1;
                journal.record_set_field(*queue, 1, old_len_field);
                let queue_mut = ledger.get_mut(queue).unwrap();
                queue_mut.state.fields[1][..8].copy_from_slice(&new_len.to_le_bytes());

                // Refund the deposit to the dequeuer.
                let queue_balance = queue_mut.state.balance();
                let refund = if current_len > 0 {
                    queue_balance / current_len
                } else {
                    0
                };
                if refund > 0 {
                    let old_queue_balance = queue_mut.state.balance();
                    journal.record_set_balance(*queue, old_queue_balance);
                    queue_mut.state.set_balance(old_queue_balance - refund);

                    let old_actor_balance = ledger.get(action_target).unwrap().state.balance();
                    journal.record_set_balance(*action_target, old_actor_balance);
                    ledger.get_mut(action_target).unwrap().state.set_balance(old_actor_balance + refund);
                }

                Ok(())
            }

            Effect::QueueResize {
                queue,
                new_capacity,
            } => {
                // Extract all needed data from immutable borrows first.
                let (owner_bytes, current_capacity, current_len, old_cap_field) = {
                    let queue_cell = ledger
                        .get(queue)
                        .ok_or_else(|| (TurnError::CellNotFound { id: *queue }, path.to_vec()))?;
                    (
                        queue_cell.state.fields[2],
                        u64::from_le_bytes(queue_cell.state.fields[0][..8].try_into().unwrap()),
                        u64::from_le_bytes(queue_cell.state.fields[1][..8].try_into().unwrap()),
                        queue_cell.state.fields[0],
                    )
                };

                // Only the queue owner can resize.
                if owner_bytes != *action_target.as_bytes() {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "only the queue owner can resize".to_string(),
                        },
                        path.to_vec(),
                    ));
                }

                if *new_capacity < current_len {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: format!(
                                "cannot shrink queue below current occupancy ({} < {})",
                                new_capacity, current_len
                            ),
                        },
                        path.to_vec(),
                    ));
                }

                // Growing costs additional computrons.
                if *new_capacity > current_capacity {
                    let additional = *new_capacity - current_capacity;
                    let actor_balance = ledger
                        .get(actor)
                        .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?
                        .state
                        .balance();
                    if actor_balance < additional {
                        return Err((
                            TurnError::InsufficientBalance {
                                cell: *actor,
                                required: additional,
                                available: actor_balance,
                            },
                            path.to_vec(),
                        ));
                    }
                    journal.record_set_balance(*actor, actor_balance);
                    ledger.get_mut(actor).unwrap().state.set_balance(actor_balance - additional);
                }

                // Update capacity field.
                journal.record_set_field(*queue, 0, old_cap_field);
                ledger.get_mut(queue).unwrap().state.fields[0][..8]
                    .copy_from_slice(&new_capacity.to_le_bytes());

                Ok(())
            }

            Effect::QueueAtomicTx { operations } => {
                // Execute all operations atomically. On any failure, the journal
                // handles rollback for the entire action.
                for op in operations {
                    match op {
                        crate::action::QueueTxOp::Enqueue {
                            queue,
                            message_hash,
                            deposit,
                        } => {
                            let queue_cell = ledger.get(queue).ok_or_else(|| {
                                (TurnError::CellNotFound { id: *queue }, path.to_vec())
                            })?;
                            let capacity = u64::from_le_bytes(
                                queue_cell.state.fields[0][..8].try_into().unwrap(),
                            );
                            let current_len = u64::from_le_bytes(
                                queue_cell.state.fields[1][..8].try_into().unwrap(),
                            );
                            if current_len >= capacity {
                                return Err((
                                    TurnError::InvalidEffect {
                                        reason: format!("atomic tx: queue {:?} is full", queue),
                                    },
                                    path.to_vec(),
                                ));
                            }
                            let actor_cell = ledger.get(actor).ok_or_else(|| {
                                (TurnError::CellNotFound { id: *actor }, path.to_vec())
                            })?;
                            if actor_cell.state.balance() < *deposit {
                                return Err((
                                    TurnError::InsufficientBalance {
                                        cell: *actor,
                                        required: *deposit,
                                        available: actor_cell.state.balance(),
                                    },
                                    path.to_vec(),
                                ));
                            }

                            let old_actor_balance = ledger.get(actor).unwrap().state.balance();
                            let old_queue_balance = ledger.get(queue).unwrap().state.balance();
                            journal.record_set_balance(*actor, old_actor_balance);
                            journal.record_set_balance(*queue, old_queue_balance);
                            ledger.get_mut(actor).unwrap().state.set_balance(old_actor_balance - *deposit);
                            ledger.get_mut(queue).unwrap().state.set_balance(old_queue_balance + *deposit);

                            let old_len_field = ledger.get(queue).unwrap().state.fields[1];
                            let new_len = current_len + 1;
                            journal.record_set_field(*queue, 1, old_len_field);
                            ledger.get_mut(queue).unwrap().state.fields[1][..8]
                                .copy_from_slice(&new_len.to_le_bytes());

                            let old_field4 = ledger.get(queue).unwrap().state.fields[4];
                            journal.record_set_field(*queue, 4, old_field4);
                            ledger.get_mut(queue).unwrap().state.fields[4] = *message_hash;
                        }
                        crate::action::QueueTxOp::Dequeue { queue } => {
                            let queue_cell = ledger.get(queue).ok_or_else(|| {
                                (TurnError::CellNotFound { id: *queue }, path.to_vec())
                            })?;
                            let owner_bytes = queue_cell.state.fields[2];
                            if owner_bytes != *action_target.as_bytes() {
                                return Err((
                                    TurnError::InvalidEffect {
                                        reason: "atomic tx: only the queue owner can dequeue"
                                            .to_string(),
                                    },
                                    path.to_vec(),
                                ));
                            }
                            let current_len = u64::from_le_bytes(
                                queue_cell.state.fields[1][..8].try_into().unwrap(),
                            );
                            if current_len == 0 {
                                return Err((
                                    TurnError::InvalidEffect {
                                        reason: "atomic tx: queue is empty, cannot dequeue"
                                            .to_string(),
                                    },
                                    path.to_vec(),
                                ));
                            }
                            let old_len_field = queue_cell.state.fields[1];
                            let new_len = current_len - 1;
                            journal.record_set_field(*queue, 1, old_len_field);
                            ledger.get_mut(queue).unwrap().state.fields[1][..8]
                                .copy_from_slice(&new_len.to_le_bytes());

                            // Refund deposit.
                            let queue_balance = ledger.get(queue).unwrap().state.balance();
                            let refund = if current_len > 0 {
                                queue_balance / current_len
                            } else {
                                0
                            };
                            if refund > 0 {
                                let old_q_bal = ledger.get(queue).unwrap().state.balance();
                                journal.record_set_balance(*queue, old_q_bal);
                                ledger.get_mut(queue).unwrap().state.set_balance(old_q_bal - refund);

                                let old_actor_bal =
                                    ledger.get(action_target).unwrap().state.balance();
                                journal.record_set_balance(*action_target, old_actor_bal);
                                ledger.get_mut(action_target).unwrap().state.set_balance(old_actor_bal + refund);
                            }
                        }
                    }
                }
                Ok(())
            }

            Effect::QueuePipelineStep {
                pipeline_id: _,
                source,
                sinks,
            } => {
                // Validate source queue exists and has messages.
                let source_cell = ledger
                    .get(source)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *source }, path.to_vec()))?;
                let source_owner = source_cell.state.fields[2];
                if source_owner != *action_target.as_bytes() {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "pipeline step: actor must own the source queue".to_string(),
                        },
                        path.to_vec(),
                    ));
                }
                let source_len =
                    u64::from_le_bytes(source_cell.state.fields[1][..8].try_into().unwrap());
                if source_len == 0 {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "pipeline step: source queue is empty".to_string(),
                        },
                        path.to_vec(),
                    ));
                }

                // Validate all sink queues exist and have capacity.
                for sink in sinks {
                    let sink_cell = ledger
                        .get(sink)
                        .ok_or_else(|| (TurnError::CellNotFound { id: *sink }, path.to_vec()))?;
                    let sink_capacity =
                        u64::from_le_bytes(sink_cell.state.fields[0][..8].try_into().unwrap());
                    let sink_len =
                        u64::from_le_bytes(sink_cell.state.fields[1][..8].try_into().unwrap());
                    if sink_len >= sink_capacity {
                        return Err((
                            TurnError::InvalidEffect {
                                reason: format!("pipeline step: sink queue {:?} is full", sink),
                            },
                            path.to_vec(),
                        ));
                    }
                }

                // Dequeue from source.
                let old_source_len_field = ledger.get(source).unwrap().state.fields[1];
                let new_source_len = source_len - 1;
                journal.record_set_field(*source, 1, old_source_len_field);
                ledger.get_mut(source).unwrap().state.fields[1][..8]
                    .copy_from_slice(&new_source_len.to_le_bytes());

                // Enqueue to each sink (fan-out).
                for sink in sinks {
                    let sink_len = u64::from_le_bytes(
                        ledger.get(sink).unwrap().state.fields[1][..8]
                            .try_into()
                            .unwrap(),
                    );
                    let old_sink_len_field = ledger.get(sink).unwrap().state.fields[1];
                    let new_sink_len = sink_len + 1;
                    journal.record_set_field(*sink, 1, old_sink_len_field);
                    ledger.get_mut(sink).unwrap().state.fields[1][..8]
                        .copy_from_slice(&new_sink_len.to_le_bytes());
                }

                Ok(())
            }

            // ─── CapTP runtime effects (Stage 7 / P1.A, P1.B) ─────────────
            //
            // Mirror the mutations that used to live at the wire layer
            // (`wire/src/server.rs` :2243-2350). The executor is now the
            // single source of truth for CapTP state transitions. The
            // wire layer constructs a Turn with these effects and runs
            // it through `TurnExecutor::execute`.
            Effect::ExportSturdyRef { swiss_number, target } => {
                if target != action_target {
                    self.check_cross_cell_permission(
                        ledger,
                        actor,
                        target,
                        pyana_cell::permissions::Action::Delegate,
                        "Delegate",
                        path,
                    )?;
                }
                let c = ledger
                    .get_mut(target)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *target }, path.to_vec()))?;
                // Bump field[7] (export counter) — mirrors the AIR's
                // ExportSturdyRef state transition.
                let mut counter_bytes = c.state.fields[7];
                let counter = u64::from_le_bytes(counter_bytes[..8].try_into().unwrap());
                journal.record_set_field(*target, 7, c.state.fields[7]);
                let new_counter = counter.saturating_add(1);
                counter_bytes[..8].copy_from_slice(&new_counter.to_le_bytes());
                c.state.fields[7] = counter_bytes;
                // The swiss_number is bound into the receipt via the
                // turn's effects_hash; the federation-level swiss table
                // mirror is updated by the wire layer's post-commit
                // hook (`process_introduction_exports`-style path).
                let _ = swiss_number;
                Ok(())
            }

            Effect::EnlivenRef { swiss_number, bearer } => {
                // The bearer cell gains a routing entry; for the
                // minimal P1.A shape we increment the target's
                // use_count (field[6]) on the bearer cell since that's
                // what the AIR projection records. P1.C tightens this
                // to a real Merkle membership check against the
                // exporter's swiss_table_root.
                let c = ledger
                    .get_mut(bearer)
                    .ok_or_else(|| (TurnError::CellNotFound { id: *bearer }, path.to_vec()))?;
                let mut use_count_bytes = c.state.fields[6];
                let use_count = u64::from_le_bytes(use_count_bytes[..8].try_into().unwrap());
                journal.record_set_field(*bearer, 6, c.state.fields[6]);
                let new_use_count = use_count.saturating_add(1);
                use_count_bytes[..8].copy_from_slice(&new_use_count.to_le_bytes());
                c.state.fields[6] = use_count_bytes;
                let _ = swiss_number;
                Ok(())
            }

            Effect::DropRef { ref_id } => {
                // Decrement field[5] (refcount) on the action target.
                // P1.C tightens this to a real refcount-table Merkle
                // proof keyed by ref_id.
                let c = ledger
                    .get_mut(action_target)
                    .ok_or_else(|| {
                        (
                            TurnError::CellNotFound { id: *action_target },
                            path.to_vec(),
                        )
                    })?;
                let mut rc_bytes = c.state.fields[5];
                let rc = u64::from_le_bytes(rc_bytes[..8].try_into().unwrap());
                if rc == 0 {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "DropRef: refcount is already zero".to_string(),
                        },
                        path.to_vec(),
                    ));
                }
                journal.record_set_field(*action_target, 5, c.state.fields[5]);
                let new_rc = rc - 1;
                rc_bytes[..8].copy_from_slice(&new_rc.to_le_bytes());
                c.state.fields[5] = rc_bytes;
                let _ = ref_id;
                Ok(())
            }

            Effect::ValidateHandoff { cert_hash } => {
                // Consume-on-use: a successful ValidateHandoff removes
                // `cert_hash` from the federation's approved-handoffs
                // mirror so a second presentation of the same cert
                // produces a non-membership witness at the AIR layer.
                //
                // The mirror lives in the executor's federation state
                // (per `DESIGN-captp-integration.md` §9.4). At this
                // stage we only verify the cell exists; the actual
                // mirror is the wire layer's `CapTpState` which the
                // post-commit hook updates. P1.C wires up Merkle proof
                // verification against `approved_handoffs_root`.
                if ledger.get(action_target).is_none() {
                    return Err((
                        TurnError::CellNotFound { id: *action_target },
                        path.to_vec(),
                    ));
                }
                let _ = cert_hash;
                Ok(())
            }
        }
    }

    /// Check if a cell has access to a target, considering both direct capabilities
    /// and delegated capability snapshots. Does NOT check expiry (use the height-aware
    /// version `has_access_including_delegation_at` during execution).
    fn has_access_including_delegation(cell: &Cell, target: &CellId) -> bool {
        // Direct capability
        if cell.capabilities.has_access(target) {
            return true;
        }
        // Delegated capability (from snapshot)
        if let Some(ref delegation) = cell.delegation {
            if delegation.has_capability(target) {
                return true;
            }
        }
        false
    }

    /// Height-aware check: does the cell have a non-expired capability to the target?
    ///
    /// Uses `has_access_at` to filter out capabilities whose `expires_at` has passed.
    fn has_access_including_delegation_at(
        cell: &Cell,
        target: &CellId,
        current_height: u64,
    ) -> bool {
        // A cell implicitly holds the strongest capability over itself. The
        // alternative — requiring an explicit c-list entry to one's own id —
        // forces every newly-created cell to insert a self-grant before it
        // can be bound into a bearer cap. Treat self-access as inherent.
        if cell.id() == *target {
            return true;
        }
        // Direct capability (height-aware)
        if cell.capabilities.has_access_at(target, current_height) {
            return true;
        }
        // Delegated capability (from snapshot)
        if let Some(ref delegation) = cell.delegation {
            if delegation.has_capability(target) {
                return true;
            }
        }
        false
    }

    /// Walk the delegation chain from `start_cell` upward (via `cell.delegate`)
    /// looking for an ancestor that holds a capability to `target`.
    ///
    /// Returns `Some(ancestor_id)` if an ancestor with the capability is found,
    /// `None` otherwise. Limits the walk to 16 hops to prevent infinite loops.
    fn walk_delegation_chain_for_capability(
        ledger: &Ledger,
        start_cell: &CellId,
        target: &CellId,
        current_height: u64,
    ) -> Option<CellId> {
        let mut current_id = *start_cell;
        let max_hops = 16;

        for _ in 0..max_hops {
            let cell = ledger.get(&current_id)?;
            // Check if this cell's delegate (parent) has the capability.
            let parent_id = cell.delegate?;
            let parent_cell = ledger.get(&parent_id)?;
            if Self::has_access_including_delegation_at(parent_cell, target, current_height) {
                return Some(parent_id);
            }
            current_id = parent_id;
        }

        None
    }

    /// SECURITY: Check that the actor holds a capability to the given cell AND that
    /// the cell's permission for the given action is not denied.
    fn check_cross_cell_permission(
        &self,
        ledger: &Ledger,
        actor: &CellId,
        target_cell_id: &CellId,
        permission_action: pyana_cell::permissions::Action,
        action_name: &str,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if actor != target_cell_id {
            let actor_cell = ledger
                .get(actor)
                .ok_or_else(|| (TurnError::CellNotFound { id: *actor }, path.to_vec()))?;
            if !Self::has_access_including_delegation_at(
                actor_cell,
                target_cell_id,
                self.block_height,
            ) {
                return Err((
                    TurnError::CapabilityNotHeld {
                        actor: *actor,
                        target: *target_cell_id,
                    },
                    path.to_vec(),
                ));
            }
        }

        let cell = ledger.get(target_cell_id).ok_or_else(|| {
            (
                TurnError::CellNotFound {
                    id: *target_cell_id,
                },
                path.to_vec(),
            )
        })?;
        let required = cell.permissions.for_action(permission_action);
        if matches!(required, AuthRequired::Impossible) {
            return Err((
                TurnError::PermissionDenied {
                    cell: *target_cell_id,
                    action: action_name.to_string(),
                    required: required.clone(),
                },
                path.to_vec(),
            ));
        }
        if !matches!(required, AuthRequired::None) {
            return Err((
                TurnError::PermissionDenied {
                    cell: *target_cell_id,
                    action: action_name.to_string(),
                    required: required.clone(),
                },
                path.to_vec(),
            ));
        }

        Ok(())
    }

    /// Compute the cost of a single effect.
    fn compute_effect_cost(&self, effect: &Effect) -> u64 {
        let base = self.costs.effect_base;
        let extra = match effect {
            Effect::Transfer { .. } => self.costs.transfer,
            Effect::CreateCell { .. } => self.costs.create_cell,
            Effect::SetField { .. } => 0,
            Effect::GrantCapability { .. } => self.costs.effect_base,
            Effect::RevokeCapability { .. } => 0,
            Effect::EmitEvent { event, .. } => (event.data.len() as u64) * self.costs.per_byte * 32,
            Effect::IncrementNonce { .. } => 0,
            Effect::SetPermissions { .. } => self.costs.effect_base,
            Effect::SetVerificationKey { .. } => self.costs.effect_base,
            Effect::NoteSpend { .. } => self.costs.proof_verify, // note spends carry a proof
            Effect::NoteCreate { .. } => self.costs.effect_base,
            Effect::BridgeMint { .. } => self.costs.proof_verify, // bridge mints verify a STARK proof
            Effect::PipelinedSend { .. } => self.costs.effect_base,
            Effect::CreateSealPair { .. } => self.costs.effect_base,
            Effect::Seal { .. } => self.costs.effect_base,
            Effect::Unseal { .. } => self.costs.effect_base,
            Effect::Introduce { .. } => self.costs.effect_base,
            Effect::SpawnWithDelegation { .. } => self.costs.create_cell,
            Effect::RefreshDelegation => self.costs.effect_base,
            Effect::RevokeDelegation { .. } => self.costs.effect_base,
            Effect::CreateObligation { .. } => self.costs.effect_base,
            Effect::FulfillObligation { .. } => self.costs.proof_verify,
            Effect::SlashObligation { .. } => self.costs.effect_base,
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                // Base cost + cost of each inner effect
                inner_effects
                    .iter()
                    .map(|e| self.compute_effect_cost(e))
                    .sum::<u64>()
            }
            Effect::BridgeLock { .. }
            | Effect::BridgeFinalize { .. }
            | Effect::BridgeCancel { .. } => self.costs.effect_base,
            Effect::CreateEscrow { .. }
            | Effect::ReleaseEscrow { .. }
            | Effect::RefundEscrow { .. }
            | Effect::CreateCommittedEscrow { .. }
            | Effect::ReleaseCommittedEscrow { .. }
            | Effect::RefundCommittedEscrow { .. } => self.costs.effect_base,
            Effect::MakeSovereign { .. } => self.costs.effect_base,
            Effect::CreateCellFromFactory { .. } => self.costs.create_cell,
            Effect::QueueAllocate { .. }
            | Effect::QueueEnqueue { .. }
            | Effect::QueueDequeue { .. }
            | Effect::QueueResize { .. }
            | Effect::QueueAtomicTx { .. }
            | Effect::QueuePipelineStep { .. } => self.costs.effect_base,
            // CapTP runtime effects (P1.A): each is a simple state bump
            // (counter / use_count / refcount) plus a federation-mirror
            // hook on commit; cost is one effect_base.
            Effect::ExportSturdyRef { .. }
            | Effect::EnlivenRef { .. }
            | Effect::DropRef { .. }
            | Effect::ValidateHandoff { .. } => self.costs.effect_base,
        };
        base.saturating_add(extra)
            .saturating_add((effect.data_bytes() as u64).saturating_mul(self.costs.per_byte))
    }

    /// Estimate the cost of a tree (without actually applying it).
    fn estimate_tree_cost(&self, tree: &CallTree) -> u64 {
        let mut total = self.costs.action_base;

        total = total.saturating_add(match &tree.action.authorization {
            Authorization::Signature(_, _) => self.costs.signature_verify,
            Authorization::Proof { .. } => self.costs.proof_verify,
            Authorization::Breadstuff(_) => self.costs.signature_verify / 2,
            Authorization::Bearer(_) => self.costs.signature_verify,
            Authorization::Unchecked => 0,
        });

        for effect in &tree.action.effects {
            total = total.saturating_add(self.compute_effect_cost(effect));
        }

        for child in &tree.children {
            total = total.saturating_add(self.estimate_tree_cost(child));
        }

        total
    }

    /// Compute a fresh state hash from the ledger by iterating all cells.
    #[allow(dead_code)]
    fn compute_state_hash(ledger: &Ledger) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        let mut entries: Vec<_> = ledger.iter().collect();
        entries.sort_by_key(|(id, _)| *id.as_bytes());
        for (id, cell) in entries {
            hasher.update(id.as_bytes());
            hasher.update(cell.public_key());
            hasher.update(cell.token_id());
            hasher.update(&cell.state.nonce().to_le_bytes());
            hasher.update(&cell.state.balance().to_le_bytes());
            for field in &cell.state.fields {
                hasher.update(field);
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Check note conservation across all effects in the turn.
    ///
    /// Dispatches between two paths:
    /// - **Cleartext path**: all notes lack `value_commitment` -- uses sum comparison.
    /// - **Committed path**: all notes have `value_commitment` -- uses Pedersen/Schnorr
    ///   algebraic verification via the turn's `conservation_proof`.
    /// - **Mixed**: some notes have commitments and some don't -- rejected.
    ///
    /// Returns Ok(()) if conservation holds, or Err((asset_type, inputs, outputs)).
    fn check_note_conservation(&self, turn: &Turn) -> Result<(), (u64, u64, u64)> {
        let mode = Self::detect_commitment_mode(&turn.call_forest);

        match mode {
            NoteCommitmentMode::Cleartext => {
                let mut inputs: std::collections::HashMap<u64, u64> =
                    std::collections::HashMap::new();
                let mut outputs: std::collections::HashMap<u64, u64> =
                    std::collections::HashMap::new();

                self.collect_note_effects(&turn.call_forest, &mut inputs, &mut outputs)?;

                let all_asset_types: std::collections::HashSet<u64> =
                    inputs.keys().chain(outputs.keys()).copied().collect();

                for asset_type in all_asset_types {
                    let input_total = inputs.get(&asset_type).copied().unwrap_or(0);
                    let output_total = outputs.get(&asset_type).copied().unwrap_or(0);
                    if input_total != output_total {
                        return Err((asset_type, input_total, output_total));
                    }
                }
                Ok(())
            }
            NoteCommitmentMode::Committed => {
                Self::check_committed_conservation(turn).map_err(|_| (0u64, 0u64, 0u64))
            }
            NoteCommitmentMode::Mixed => Err((0u64, 0u64, 0u64)),
            NoteCommitmentMode::Empty => Ok(()),
        }
    }

    /// Check conservation using the committed (Pedersen) path.
    fn check_committed_conservation(turn: &Turn) -> Result<(), TurnError> {
        let proof_bytes = turn.conservation_proof.as_ref().ok_or_else(|| {
            TurnError::CommittedConservationFailed {
                reason: "turn uses committed values but has no conservation_proof".into(),
            }
        })?;

        let proof: pyana_cell::ConservationProof =
            postcard::from_bytes(proof_bytes).map_err(|e| {
                TurnError::CommittedConservationFailed {
                    reason: format!("failed to deserialize conservation_proof: {e}"),
                }
            })?;

        let mut input_commitments: Vec<ValueCommitment> = Vec::new();
        let mut output_commitments: Vec<ValueCommitment> = Vec::new();
        Self::collect_committed_notes(
            &turn.call_forest,
            &mut input_commitments,
            &mut output_commitments,
        )?;

        let turn_hash = turn.hash();
        pyana_cell::verify_conservation(
            &input_commitments,
            &output_commitments,
            &proof,
            &turn_hash,
        )
        .map_err(|e| TurnError::CommittedConservationFailed {
            reason: format!("conservation proof invalid: {e}"),
        })?;

        Self::verify_output_range_proofs(&turn.call_forest)?;
        Ok(())
    }

    /// Collect ValueCommitment points from committed NoteSpend/NoteCreate effects.
    fn collect_committed_notes(
        forest: &crate::forest::CallForest,
        inputs: &mut Vec<ValueCommitment>,
        outputs: &mut Vec<ValueCommitment>,
    ) -> Result<(), TurnError> {
        for tree in &forest.roots {
            Self::collect_committed_notes_tree(tree, inputs, outputs)?;
        }
        Ok(())
    }

    fn collect_committed_notes_tree(
        tree: &CallTree,
        inputs: &mut Vec<ValueCommitment>,
        outputs: &mut Vec<ValueCommitment>,
    ) -> Result<(), TurnError> {
        for effect in &tree.action.effects {
            Self::collect_committed_notes_from_effect(effect, inputs, outputs)?;
        }
        for child in &tree.children {
            Self::collect_committed_notes_tree(child, inputs, outputs)?;
        }
        Ok(())
    }

    fn collect_committed_notes_from_effect(
        effect: &Effect,
        inputs: &mut Vec<ValueCommitment>,
        outputs: &mut Vec<ValueCommitment>,
    ) -> Result<(), TurnError> {
        match effect {
            Effect::NoteSpend {
                value_commitment: Some(vc_bytes),
                ..
            } => {
                let vc = ValueCommitment::from_bytes(&ValueCommitmentBytes(*vc_bytes)).ok_or_else(
                    || TurnError::CommittedConservationFailed {
                        reason: "NoteSpend value_commitment is not a valid Ristretto point".into(),
                    },
                )?;
                inputs.push(vc);
            }
            Effect::NoteCreate {
                value_commitment: Some(vc_bytes),
                ..
            } => {
                let vc = ValueCommitment::from_bytes(&ValueCommitmentBytes(*vc_bytes)).ok_or_else(
                    || TurnError::CommittedConservationFailed {
                        reason: "NoteCreate value_commitment is not a valid Ristretto point".into(),
                    },
                )?;
                outputs.push(vc);
            }
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    Self::collect_committed_notes_from_effect(inner, inputs, outputs)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Verify range proofs on NoteCreate outputs with value commitments.
    fn verify_output_range_proofs(forest: &crate::forest::CallForest) -> Result<(), TurnError> {
        for tree in &forest.roots {
            Self::verify_output_range_proofs_tree(tree)?;
        }
        Ok(())
    }

    fn verify_output_range_proofs_tree(tree: &CallTree) -> Result<(), TurnError> {
        for effect in &tree.action.effects {
            Self::verify_output_range_proof_effect(effect)?;
        }
        for child in &tree.children {
            Self::verify_output_range_proofs_tree(child)?;
        }
        Ok(())
    }

    fn verify_output_range_proof_effect(effect: &Effect) -> Result<(), TurnError> {
        match effect {
            Effect::NoteCreate {
                value_commitment: Some(vc_bytes),
                range_proof,
                ..
            } => {
                let rp =
                    range_proof
                        .as_ref()
                        .ok_or_else(|| TurnError::CommittedConservationFailed {
                            reason: "NoteCreate has value_commitment but no range_proof".into(),
                        })?;
                if rp.is_empty() {
                    return Err(TurnError::CommittedConservationFailed {
                        reason: "NoteCreate range_proof is empty".into(),
                    });
                }
                // Deserialize the value commitment from the 32-byte compressed point.
                let vc = ValueCommitment::from_bytes(&ValueCommitmentBytes(*vc_bytes)).ok_or_else(
                    || TurnError::CommittedConservationFailed {
                        reason: "NoteCreate value_commitment is not a valid Ristretto point".into(),
                    },
                )?;
                // Deserialize and verify the Bulletproof range proof.
                let bulletproof = BulletproofRangeProof {
                    proof_bytes: rp.clone(),
                };
                bulletproof.verify_range(&vc).map_err(|e| {
                    TurnError::CommittedConservationFailed {
                        reason: format!("NoteCreate range proof verification failed: {}", e),
                    }
                })?;
                Ok(())
            }
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    Self::verify_output_range_proof_effect(inner)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Detect whether the turn's notes use commitments, cleartext, or a mix.
    fn detect_commitment_mode(forest: &crate::forest::CallForest) -> NoteCommitmentMode {
        let mut has_committed = false;
        let mut has_cleartext = false;

        for tree in &forest.roots {
            Self::detect_commitment_mode_tree(tree, &mut has_committed, &mut has_cleartext);
        }

        match (has_committed, has_cleartext) {
            (false, false) => NoteCommitmentMode::Empty,
            (true, false) => NoteCommitmentMode::Committed,
            (false, true) => NoteCommitmentMode::Cleartext,
            (true, true) => NoteCommitmentMode::Mixed,
        }
    }

    fn detect_commitment_mode_tree(
        tree: &CallTree,
        has_committed: &mut bool,
        has_cleartext: &mut bool,
    ) {
        for effect in &tree.action.effects {
            Self::detect_commitment_mode_effect(effect, has_committed, has_cleartext);
        }
        for child in &tree.children {
            Self::detect_commitment_mode_tree(child, has_committed, has_cleartext);
        }
    }

    fn detect_commitment_mode_effect(
        effect: &Effect,
        has_committed: &mut bool,
        has_cleartext: &mut bool,
    ) {
        match effect {
            Effect::NoteSpend {
                value_commitment, ..
            } => {
                if value_commitment.is_some() {
                    *has_committed = true;
                } else {
                    *has_cleartext = true;
                }
            }
            Effect::NoteCreate {
                value_commitment, ..
            } => {
                if value_commitment.is_some() {
                    *has_committed = true;
                } else {
                    *has_cleartext = true;
                }
            }
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    Self::detect_commitment_mode_effect(inner, has_committed, has_cleartext);
                }
            }
            _ => {}
        }
    }

    /// Recursively collect NoteSpend/NoteCreate effects from the call forest.
    fn collect_note_effects(
        &self,
        forest: &crate::forest::CallForest,
        inputs: &mut std::collections::HashMap<u64, u64>,
        outputs: &mut std::collections::HashMap<u64, u64>,
    ) -> Result<(), (u64, u64, u64)> {
        for tree in &forest.roots {
            self.collect_note_effects_tree(tree, inputs, outputs)?;
        }
        Ok(())
    }

    /// Recursively collect note effects from a single tree.
    fn collect_note_effects_tree(
        &self,
        tree: &CallTree,
        inputs: &mut std::collections::HashMap<u64, u64>,
        outputs: &mut std::collections::HashMap<u64, u64>,
    ) -> Result<(), (u64, u64, u64)> {
        for effect in &tree.action.effects {
            Self::collect_note_effects_from_effect(effect, inputs, outputs)?;
        }
        for child in &tree.children {
            self.collect_note_effects_tree(child, inputs, outputs)?;
        }
        Ok(())
    }

    /// Collect note effects from a single effect, recursing into ExerciseViaCapability.
    fn collect_note_effects_from_effect(
        effect: &Effect,
        inputs: &mut std::collections::HashMap<u64, u64>,
        outputs: &mut std::collections::HashMap<u64, u64>,
    ) -> Result<(), (u64, u64, u64)> {
        match effect {
            Effect::NoteSpend {
                value, asset_type, ..
            } => {
                let entry = inputs.entry(*asset_type).or_insert(0);
                *entry = entry
                    .checked_add(*value)
                    .ok_or((*asset_type, u64::MAX, 0))?;
            }
            Effect::NoteCreate {
                value, asset_type, ..
            } => {
                let entry = outputs.entry(*asset_type).or_insert(0);
                *entry = entry
                    .checked_add(*value)
                    .ok_or((*asset_type, 0, u64::MAX))?;
            }
            Effect::BridgeMint { portable_proof } => {
                // BridgeMint contributes to BOTH sides of conservation:
                // it's an external input (from another federation) AND creates output.
                // For local conservation, bridge mints are treated as matching
                // input+output (self-balancing) since the value comes from outside.
                let entry = inputs.entry(portable_proof.asset_type).or_insert(0);
                *entry = entry.checked_add(portable_proof.value).ok_or((
                    portable_proof.asset_type,
                    u64::MAX,
                    0,
                ))?;
                let entry = outputs.entry(portable_proof.asset_type).or_insert(0);
                *entry = entry.checked_add(portable_proof.value).ok_or((
                    portable_proof.asset_type,
                    0,
                    u64::MAX,
                ))?;
            }
            // Recurse into ExerciseViaCapability inner effects to catch nested
            // NoteSpend/NoteCreate that would otherwise bypass the conservation check.
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    Self::collect_note_effects_from_effect(inner, inputs, outputs)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Compute the BLAKE3 hash of all effect hashes combined.
    fn compute_effects_hash(&self, effect_hashes: &[[u8; 32]]) -> [u8; 32] {
        if effect_hashes.is_empty() {
            return [0u8; 32];
        }
        let mut hasher = blake3::Hasher::new();
        for h in effect_hashes {
            hasher.update(h);
        }
        *hasher.finalize().as_bytes()
    }

    /// Compute a LedgerDelta from journal entries and the current (post-mutation) ledger.
    ///
    /// The journal records the old (pre-mutation) values. By comparing those to the
    /// current state in the ledger, we derive the delta without needing a full ledger snapshot.
    fn compute_delta_from_journal(journal: &LedgerJournal, ledger: &Ledger) -> LedgerDelta {
        use std::collections::{HashMap, HashSet};

        let mut delta = LedgerDelta::new();
        let mut created_cells: HashSet<CellId> = HashSet::new();
        let mut updated_cells: HashMap<CellId, CellStateDelta> = HashMap::new();

        // Track the FIRST old balance/nonce per cell (the pre-turn value).
        let mut first_balance: HashMap<CellId, u64> = HashMap::new();
        let mut first_nonce: HashMap<CellId, u64> = HashMap::new();
        let mut first_fields: HashMap<(CellId, usize), [u8; 32]> = HashMap::new();

        for entry in journal.entries() {
            match entry {
                JournalEntry::CreateCell { cell } => {
                    if let Some(c) = ledger.get(cell) {
                        delta.created.push(c.clone());
                        created_cells.insert(*cell);
                    }
                }
                JournalEntry::SetField {
                    cell,
                    index,
                    old_value,
                } => {
                    if !created_cells.contains(cell) {
                        first_fields.entry((*cell, *index)).or_insert(*old_value);
                    }
                }
                JournalEntry::SetBalance { cell, old_balance } => {
                    if !created_cells.contains(cell) {
                        first_balance.entry(*cell).or_insert(*old_balance);
                    }
                }
                JournalEntry::SetNonce { cell, old_nonce } => {
                    if !created_cells.contains(cell) {
                        first_nonce.entry(*cell).or_insert(*old_nonce);
                    }
                }
                JournalEntry::GrantCapability { cell, slot } => {
                    if !created_cells.contains(cell) {
                        if let Some(c) = ledger.get(cell) {
                            if let Some(cap_ref) = c.capabilities.lookup(*slot) {
                                let e = updated_cells
                                    .entry(*cell)
                                    .or_insert_with(CellStateDelta::empty);
                                e.capability_grants.push(cap_ref.clone());
                            }
                        }
                    }
                }
                JournalEntry::RevokeCapability { cell, old_cap } => {
                    if !created_cells.contains(cell) {
                        let e = updated_cells
                            .entry(*cell)
                            .or_insert_with(CellStateDelta::empty);
                        e.capability_revocations.push(old_cap.slot);
                    }
                }
                JournalEntry::SetProvedState { .. } => {
                    // proved_state changes are tracked implicitly through the cell's state;
                    // no separate delta field needed for now.
                }
                JournalEntry::SetPermissions { cell, .. } => {
                    if !created_cells.contains(cell) {
                        let e = updated_cells
                            .entry(*cell)
                            .or_insert_with(CellStateDelta::empty);
                        // Record that permissions changed (the new perms are on the cell now).
                        if let Some(c) = ledger.get(cell) {
                            e.permission_changes = Some(c.permissions.clone());
                        }
                    }
                }
                JournalEntry::SetVerificationKey { .. } => {
                    // Verification key changes don't have a delta field currently;
                    // tracked via the cell's state.
                }
                JournalEntry::SetDelegation { .. } | JournalEntry::SetDelegationEpoch { .. } => {}
                // Note/obligation/event/escrow entries don't affect the ledger delta directly.
                // Obligation/escrow/nullifier insertion entries are rollback-only bookkeeping.
                JournalEntry::NoteSpend { .. }
                | JournalEntry::NoteCreate { .. }
                | JournalEntry::ObligationCreated { .. }
                | JournalEntry::ObligationFulfilled { .. }
                | JournalEntry::ObligationSlashed { .. }
                | JournalEntry::EventEmitted { .. }
                | JournalEntry::EscrowCreated { .. }
                | JournalEntry::EscrowReleased { .. }
                | JournalEntry::EscrowRefunded { .. }
                | JournalEntry::ObligationInserted { .. }
                | JournalEntry::EscrowInserted { .. }
                | JournalEntry::BridgedNullifierInserted { .. }
                | JournalEntry::CommittedEscrowCreated { .. }
                | JournalEntry::CommittedEscrowReleased { .. }
                | JournalEntry::CommittedEscrowRefunded { .. }
                | JournalEntry::CommittedEscrowInserted { .. } => {}
            }
        }

        // Compute field/balance/nonce deltas from first-old vs current.
        for ((cell_id, index), old_value) in &first_fields {
            if let Some(c) = ledger.get(cell_id) {
                let new_value = c.state.fields[*index];
                if new_value != *old_value {
                    let e = updated_cells
                        .entry(*cell_id)
                        .or_insert_with(CellStateDelta::empty);
                    e.field_updates.push((*index, new_value));
                }
            }
        }

        for (cell_id, old_balance) in &first_balance {
            if let Some(c) = ledger.get(cell_id) {
                let diff = c.state.balance() as i128 - *old_balance as i128;
                if diff != 0 {
                    let e = updated_cells
                        .entry(*cell_id)
                        .or_insert_with(CellStateDelta::empty);
                    e.balance_change =
                        i64::try_from(diff).unwrap_or(if diff > 0 { i64::MAX } else { i64::MIN });
                }
            }
        }

        for (cell_id, old_nonce) in &first_nonce {
            if let Some(c) = ledger.get(cell_id) {
                if c.state.nonce() > *old_nonce {
                    let e = updated_cells
                        .entry(*cell_id)
                        .or_insert_with(CellStateDelta::empty);
                    e.nonce_increment = true;
                }
            }
        }

        // Collect non-empty cell deltas.
        for (cell_id, cell_delta) in updated_cells {
            if !cell_delta.field_updates.is_empty()
                || cell_delta.nonce_increment
                || cell_delta.balance_change != 0
                || cell_delta.permission_changes.is_some()
                || !cell_delta.capability_grants.is_empty()
                || !cell_delta.capability_revocations.is_empty()
            {
                delta.updated.push((cell_id, cell_delta));
            }
        }

        delta
    }

    /// Compute a LedgerDelta including the Phase 1 fee + nonce commitment and
    /// Phase 3 fee distribution (proposer/treasury credits).
    ///
    /// Since Phase 1 (fee/nonce) and Phase 3 (distribution) are committed outside
    /// the journal, we need to account for them separately in the delta. The agent's
    /// balance decreased by `fee` and nonce incremented by 1. The proposer receives
    /// 50% and treasury receives 30% (if configured and present in ledger).
    fn compute_delta_from_journal_with_fee(
        journal: &LedgerJournal,
        ledger: &Ledger,
        agent: &CellId,
        fee: u64,
        proposer_cell: Option<&CellId>,
        treasury_cell: Option<&CellId>,
    ) -> LedgerDelta {
        let mut delta = Self::compute_delta_from_journal(journal, ledger);

        // Check if the agent already appears in updated cells.
        let agent_already_updated = delta.updated.iter().any(|(id, _)| id == agent);

        if agent_already_updated {
            // Adjust the existing delta for the agent to include the fee.
            for (id, cell_delta) in &mut delta.updated {
                if id == agent {
                    cell_delta.balance_change -= fee as i64;
                    cell_delta.nonce_increment = true;
                    break;
                }
            }
        } else {
            // Agent only had Phase 1 changes (fee + nonce), add a new delta entry.
            let mut cell_delta = CellStateDelta::empty();
            cell_delta.balance_change = -(fee as i64);
            cell_delta.nonce_increment = true;
            delta.updated.push((*agent, cell_delta));
        }

        // Account for fee distribution credits (Phase 3).
        let proposer_share = fee / 2;
        let treasury_share = fee * 3 / 10;

        if let Some(proposer_id) = proposer_cell {
            // Only include in delta if proposer exists in ledger.
            if ledger.get(proposer_id).is_some() {
                let proposer_in_delta = delta.updated.iter_mut().find(|(id, _)| id == proposer_id);
                if let Some((_, cell_delta)) = proposer_in_delta {
                    cell_delta.balance_change += proposer_share as i64;
                } else {
                    let mut cell_delta = CellStateDelta::empty();
                    cell_delta.balance_change = proposer_share as i64;
                    delta.updated.push((*proposer_id, cell_delta));
                }
            }
        }

        if let Some(treasury_id) = treasury_cell {
            // Only include in delta if treasury exists in ledger.
            if ledger.get(treasury_id).is_some() {
                let treasury_in_delta = delta.updated.iter_mut().find(|(id, _)| id == treasury_id);
                if let Some((_, cell_delta)) = treasury_in_delta {
                    cell_delta.balance_change += treasury_share as i64;
                } else {
                    let mut cell_delta = CellStateDelta::empty();
                    cell_delta.balance_change = treasury_share as i64;
                    delta.updated.push((*treasury_id, cell_delta));
                }
            }
        }

        delta
    }

    /// Derive a synthetic CellId for a seal pair's sealer or unsealer capability.
    fn seal_capability_id(pair_id: &[u8; 32], is_sealer: bool) -> CellId {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-seal capability-id v1");
        hasher.update(pair_id);
        hasher.update(if is_sealer { b"sealer" } else { b"unsealer" });
        CellId::from_bytes(*hasher.finalize().as_bytes())
    }

    /// Collect emitted events from the journal for inclusion in the turn receipt.
    fn collect_emitted_events(journal: &LedgerJournal) -> Vec<EmittedEvent> {
        journal
            .entries()
            .iter()
            .filter_map(|entry| match entry {
                JournalEntry::EventEmitted { cell, topic, data } => Some(EmittedEvent {
                    cell: *cell,
                    topic: *topic,
                    data: data.clone(),
                }),
                _ => None,
            })
            .collect()
    }

    fn collect_routing_directives(
        forest: &crate::forest::CallForest,
        turn_hash: &[u8; 32],
        block_height: u64,
        max_introduction_lifetime: u64,
    ) -> Vec<RoutingDirective> {
        let mut directives = Vec::new();
        for tree in &forest.roots {
            Self::collect_routing_directives_tree(
                tree,
                turn_hash,
                block_height,
                max_introduction_lifetime,
                &mut directives,
            );
        }
        directives
    }

    fn collect_routing_directives_tree(
        tree: &CallTree,
        turn_hash: &[u8; 32],
        block_height: u64,
        max_introduction_lifetime: u64,
        directives: &mut Vec<RoutingDirective>,
    ) {
        for effect in &tree.action.effects {
            if let Effect::Introduce {
                recipient, target, ..
            } = effect
            {
                directives.push(RoutingDirective {
                    sender: *recipient,
                    target: *target,
                    authorizing_turn: *turn_hash,
                    expires: Some(block_height + max_introduction_lifetime),
                });
            }
        }
        for child in &tree.children {
            Self::collect_routing_directives_tree(
                child,
                turn_hash,
                block_height,
                max_introduction_lifetime,
                directives,
            );
        }
    }

    /// Collect GC export registrations from introductions in the call forest.
    ///
    /// For each `Effect::Introduce { target, recipient, .. }`, emits an
    /// `IntroductionExport` record. The node/server layer uses these to call
    /// `ExportGcManager::record_export(target, recipient_federation, height)`,
    /// ensuring that introduced capabilities participate in distributed GC.
    ///
    /// Without this, capabilities created via 3-party introductions bypass GC
    /// tracking entirely — no `DropRef` is ever fired, causing the export table
    /// to grow unboundedly.
    fn collect_introduction_exports(
        forest: &crate::forest::CallForest,
        turn_hash: &[u8; 32],
        block_height: u64,
        max_introduction_lifetime: u64,
    ) -> Vec<crate::routing::IntroductionExport> {
        let mut exports = Vec::new();
        for tree in &forest.roots {
            Self::collect_introduction_exports_tree(
                tree,
                turn_hash,
                block_height,
                max_introduction_lifetime,
                &mut exports,
            );
        }
        exports
    }

    fn collect_introduction_exports_tree(
        tree: &CallTree,
        turn_hash: &[u8; 32],
        block_height: u64,
        max_introduction_lifetime: u64,
        exports: &mut Vec<crate::routing::IntroductionExport>,
    ) {
        for effect in &tree.action.effects {
            if let Effect::Introduce {
                recipient, target, ..
            } = effect
            {
                exports.push(crate::routing::IntroductionExport {
                    target: *target,
                    recipient: *recipient,
                    authorizing_turn: *turn_hash,
                    expires: Some(block_height + max_introduction_lifetime),
                });
            }
        }
        for child in &tree.children {
            Self::collect_introduction_exports_tree(
                child,
                turn_hash,
                block_height,
                max_introduction_lifetime,
                exports,
            );
        }
    }

    /// Collect all capability derivation records from the call forest.
    ///
    /// Scans the forest for effects that create derivation edges:
    /// - GrantCapability: source grants to target
    /// - Introduce: introducer grants target access to recipient
    /// - SpawnWithDelegation: parent's c-list snapshot to child
    /// - Unseal: sealed capability recovered to recipient
    fn collect_derivation_records(
        forest: &crate::forest::CallForest,
        timestamp: u64,
    ) -> Vec<pyana_cell::DerivationRecord> {
        let mut records = Vec::new();
        let mut slot_counter: u32 = 0;
        for tree in &forest.roots {
            Self::collect_derivation_records_tree(tree, timestamp, &mut records, &mut slot_counter);
        }
        records
    }

    fn collect_derivation_records_tree(
        tree: &CallTree,
        timestamp: u64,
        records: &mut Vec<pyana_cell::DerivationRecord>,
        slot_counter: &mut u32,
    ) {
        for effect in &tree.action.effects {
            match effect {
                Effect::GrantCapability { from, to, cap } => {
                    records.push(pyana_cell::DerivationRecord {
                        target_cell: *to,
                        target_slot: *slot_counter,
                        edge: pyana_cell::DerivationEdge {
                            source_cell: *from,
                            source_slot: cap.slot,
                            derivation_type: pyana_cell::DerivationType::Grant,
                        },
                        created_at: timestamp,
                    });
                    *slot_counter += 1;
                }
                Effect::Introduce {
                    introducer,
                    recipient,
                    ..
                } => {
                    records.push(pyana_cell::DerivationRecord {
                        target_cell: *recipient,
                        target_slot: *slot_counter,
                        edge: pyana_cell::DerivationEdge {
                            source_cell: *introducer,
                            source_slot: 0,
                            derivation_type: pyana_cell::DerivationType::Introduce,
                        },
                        created_at: timestamp,
                    });
                    *slot_counter += 1;
                }
                Effect::SpawnWithDelegation {
                    child_public_key,
                    child_token_id,
                    ..
                } => {
                    let child_id = CellId::derive_raw(child_public_key, child_token_id);
                    records.push(pyana_cell::DerivationRecord {
                        target_cell: child_id,
                        target_slot: *slot_counter,
                        edge: pyana_cell::DerivationEdge {
                            source_cell: tree.action.target,
                            source_slot: 0,
                            derivation_type: pyana_cell::DerivationType::Delegate,
                        },
                        created_at: timestamp,
                    });
                    *slot_counter += 1;
                }
                Effect::Unseal { recipient, .. } => {
                    records.push(pyana_cell::DerivationRecord {
                        target_cell: *recipient,
                        target_slot: *slot_counter,
                        edge: pyana_cell::DerivationEdge {
                            source_cell: tree.action.target,
                            source_slot: 0,
                            derivation_type: pyana_cell::DerivationType::Unseal,
                        },
                        created_at: timestamp,
                    });
                    *slot_counter += 1;
                }
                _ => {}
            }
        }
        for child in &tree.children {
            Self::collect_derivation_records_tree(child, timestamp, records, slot_counter);
        }
    }
}

// ─── Pipeline Execution ──────────────────────────────────────────────────────

use crate::eventual::{EventualRef, Pipeline, PipelineError, PipelineResult, TurnOutput};

/// A resolution table mapping (turn_hash, output_slot) to concrete outputs.
pub type ResolutionTable = HashMap<([u8; 32], u32), TurnOutput>;

/// Resolve a `TurnOutput` to a concrete `CellId`.
///
/// - `CreatedCell` → the created cell's ID
/// - `GrantedCapability` → the target cell that received the capability
/// - `StateUpdate` → the cell whose state was updated
/// - `CreatedNote` → cannot be resolved to a CellId (returns error)
fn resolve_output_to_cell_id(
    output: &TurnOutput,
    eventual_ref: &EventualRef,
) -> Result<CellId, PipelineError> {
    match output {
        TurnOutput::CreatedCell { cell } => Ok(*cell),
        TurnOutput::GrantedCapability { target, .. } => Ok(*target),
        TurnOutput::StateUpdate { cell, .. } => Ok(*cell),
        TurnOutput::CreatedNote { .. } => Err(PipelineError::UnresolvedRef {
            eventual_ref: eventual_ref.clone(),
            reason: "CreatedNote output cannot be resolved to a CellId".to_string(),
        }),
    }
}

/// Resolve all `PipelinedSend` effects in a turn's call forest using the resolution table.
///
/// Each `PipelinedSend { target: EventualRef, action }` is resolved by:
/// 1. Looking up the EventualRef in the resolution table to get a concrete CellId
/// 2. Replacing the PipelinedSend effect with the inner action's effects,
///    re-targeted to the resolved CellId
/// 3. Adding the inner action as a new root in the call forest
///
/// Returns the resolved turn, or a PipelineError if resolution fails.
fn resolve_turn(turn: &Turn, table: &ResolutionTable) -> Result<Turn, PipelineError> {
    let mut resolved_turn = turn.clone();
    let mut new_roots: Vec<crate::forest::CallTree> = Vec::new();

    for root in &mut resolved_turn.call_forest.roots {
        resolve_tree_effects(root, table, &mut new_roots)?;
    }

    // Append any newly created roots from resolved PipelinedSend effects.
    for new_root in new_roots {
        resolved_turn.call_forest.roots.push(new_root);
    }

    Ok(resolved_turn)
}

/// Recursively resolve PipelinedSend effects in a call tree.
///
/// PipelinedSend effects are removed from the current tree's action and their
/// inner actions are added as new roots (with the resolved target).
///
/// Placeholder convention: if the inner action's target is `CellId::from_bytes([0u8; 32])`,
/// it is replaced with the resolved CellId. Similarly, effects referencing the
/// placeholder are rewritten to use the resolved CellId.
fn resolve_tree_effects(
    tree: &mut crate::forest::CallTree,
    table: &ResolutionTable,
    new_roots: &mut Vec<crate::forest::CallTree>,
) -> Result<(), PipelineError> {
    let mut remaining_effects: Vec<Effect> = Vec::new();

    for effect in std::mem::take(&mut tree.action.effects) {
        match effect {
            Effect::PipelinedSend {
                ref target,
                ref action,
            } => {
                // Resolve the EventualRef to a concrete CellId.
                let output = resolve_eventual_ref(target, table)?;
                let resolved_cell_id = resolve_output_to_cell_id(output, target)?;

                // Create a new action with the resolved target.
                let placeholder = CellId::from_bytes([0u8; 32]);
                let mut resolved_action = action.as_ref().clone();

                // If the inner action's target is the placeholder, replace it.
                if resolved_action.target == placeholder {
                    resolved_action.target = resolved_cell_id;
                }

                // Rewrite placeholder CellIds in effects.
                rewrite_effect_targets(
                    &mut resolved_action.effects,
                    &placeholder,
                    &resolved_cell_id,
                );

                // Add as a new root action in the forest.
                new_roots.push(crate::forest::CallTree::new(resolved_action));
            }
            other => {
                remaining_effects.push(other);
            }
        }
    }

    tree.action.effects = remaining_effects;

    // Recurse into children.
    for child in &mut tree.children {
        resolve_tree_effects(child, table, new_roots)?;
    }

    Ok(())
}

/// Rewrite placeholder CellIds in effects with the resolved concrete CellId.
///
/// This allows PipelinedSend inner actions to use `CellId::from_bytes([0u8; 32])`
/// as a placeholder meaning "the cell resolved from the EventualRef". After resolution,
/// all occurrences of the placeholder are replaced with the actual CellId.
fn rewrite_effect_targets(effects: &mut [Effect], placeholder: &CellId, resolved: &CellId) {
    for effect in effects.iter_mut() {
        match effect {
            Effect::SetField { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::Transfer { from, to, .. } => {
                if from == placeholder {
                    *from = *resolved;
                }
                if to == placeholder {
                    *to = *resolved;
                }
            }
            Effect::GrantCapability { from, to, cap } => {
                if from == placeholder {
                    *from = *resolved;
                }
                if to == placeholder {
                    *to = *resolved;
                }
                if cap.target == *placeholder {
                    cap.target = *resolved;
                }
            }
            Effect::RevokeCapability { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::EmitEvent { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::IncrementNonce { cell } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::SetPermissions { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::SetVerificationKey { cell, .. } => {
                if cell == placeholder {
                    *cell = *resolved;
                }
            }
            Effect::Introduce {
                introducer,
                recipient,
                target,
                ..
            } => {
                if introducer == placeholder {
                    *introducer = *resolved;
                }
                if recipient == placeholder {
                    *recipient = *resolved;
                }
                if target == placeholder {
                    *target = *resolved;
                }
            }
            Effect::CreateObligation { beneficiary, .. } => {
                if beneficiary == placeholder {
                    *beneficiary = *resolved;
                }
            }
            // ExerciseViaCapability: recurse into inner_effects for rewriting.
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                rewrite_effect_targets(inner_effects, placeholder, resolved);
            }
            // CapTP variants have mutable CellId fields (target, bearer):
            Effect::ExportSturdyRef { target, .. } => {
                if target == placeholder {
                    *target = *resolved;
                }
            }
            Effect::EnlivenRef { bearer, .. } => {
                if bearer == placeholder {
                    *bearer = *resolved;
                }
            }
            // These effects don't have mutable CellId fields needing rewrite:
            Effect::CreateCell { .. }
            | Effect::NoteSpend { .. }
            | Effect::NoteCreate { .. }
            | Effect::BridgeMint { .. }
            | Effect::CreateSealPair { .. }
            | Effect::Seal { .. }
            | Effect::Unseal { .. }
            | Effect::PipelinedSend { .. }
            | Effect::SpawnWithDelegation { .. }
            | Effect::RefreshDelegation
            | Effect::RevokeDelegation { .. }
            | Effect::FulfillObligation { .. }
            | Effect::SlashObligation { .. }
            | Effect::BridgeLock { .. }
            | Effect::BridgeFinalize { .. }
            | Effect::BridgeCancel { .. }
            | Effect::CreateEscrow { .. }
            | Effect::ReleaseEscrow { .. }
            | Effect::RefundEscrow { .. }
            | Effect::CreateCommittedEscrow { .. }
            | Effect::ReleaseCommittedEscrow { .. }
            | Effect::RefundCommittedEscrow { .. }
            | Effect::MakeSovereign { .. }
            | Effect::CreateCellFromFactory { .. }
            | Effect::QueueAllocate { .. }
            | Effect::QueueEnqueue { .. }
            | Effect::QueueDequeue { .. }
            | Effect::QueueResize { .. }
            | Effect::QueueAtomicTx { .. }
            | Effect::QueuePipelineStep { .. }
            | Effect::DropRef { .. }
            | Effect::ValidateHandoff { .. } => {}
        }
    }
}
/// Execute a batch of turns against a ledger in topological order.
///
/// Before executing each turn, any `PipelinedSend` effects are resolved using
/// the resolution table (built from outputs of previously-committed turns).
/// Turns can reference outputs of earlier turns via `EventualRef` (OutputRef),
/// and the batch executor resolves them in causal order.
///
/// Each turn's `depends_on` hashes are verified against the set of committed
/// receipt hashes within this batch. If a turn declares a dependency on a hash
/// that hasn't been committed, the turn is rejected.
pub fn execute_pipeline(
    pipeline: Pipeline,
    ledger: &mut Ledger,
    executor: &TurnExecutor,
) -> Vec<Result<TurnReceipt, PipelineError>> {
    let n = pipeline.turns.len();
    if n == 0 {
        return vec![];
    }

    let topo_order = match pipeline.topological_order() {
        Ok(order) => order,
        Err(cycle) => {
            return vec![Err(PipelineError::Cycle(cycle)); n];
        }
    };

    let mut results: Vec<Option<Result<TurnReceipt, PipelineError>>> = vec![None; n];
    let mut failed: Vec<bool> = vec![false; n];
    let mut resolution_table: ResolutionTable = HashMap::new();
    // Track committed turn hashes for depends_on verification.
    let mut committed_hashes: std::collections::HashSet<[u8; 32]> =
        std::collections::HashSet::new();

    // Pre-compute turn hashes for resolution table keying.
    let turn_hashes: Vec<[u8; 32]> = pipeline.turns.iter().map(|t| t.hash()).collect();

    for &idx in &topo_order {
        // Check explicit dependency edges (from add_dependency).
        let deps = pipeline.dependencies_of(idx);
        let mut dep_failed = None;
        for dep_idx in &deps {
            if failed[*dep_idx] {
                dep_failed = Some(*dep_idx);
                break;
            }
        }

        if let Some(failed_dep) = dep_failed {
            failed[idx] = true;
            results[idx] = Some(Err(PipelineError::DependencyFailed {
                failed_index: failed_dep,
                dependent_index: idx,
            }));
            continue;
        }

        // Verify depends_on hashes: all must be committed within this batch.
        let turn = &pipeline.turns[idx];
        let mut depends_on_unmet = false;
        for dep_hash in &turn.depends_on {
            if !committed_hashes.contains(dep_hash) {
                let dep_idx_opt = turn_hashes.iter().position(|h| h == dep_hash);
                if let Some(dep_idx) = dep_idx_opt {
                    failed[idx] = true;
                    results[idx] = Some(Err(PipelineError::DependencyFailed {
                        failed_index: dep_idx,
                        dependent_index: idx,
                    }));
                } else {
                    failed[idx] = true;
                    results[idx] = Some(Err(PipelineError::MissingDependency {
                        turn_index: idx,
                        missing_hash: *dep_hash,
                    }));
                }
                depends_on_unmet = true;
                break;
            }
        }
        if depends_on_unmet {
            continue;
        }

        // Resolve EventualRefs in this turn before executing it.
        let mut resolved_turn = match resolve_turn(turn, &resolution_table) {
            Ok(t) => t,
            Err(e) => {
                failed[idx] = true;
                results[idx] = Some(Err(e));
                continue;
            }
        };

        // P0-3: auto-chain previous_receipt_hash from the executor's per-agent
        // head when the turn doesn't already specify one. Pipeline turns are
        // commonly assembled before knowing the receipt-chain head, so the
        // pipeline executor fills it in here. Turns that explicitly set
        // `previous_receipt_hash` are NOT overridden -- the explicit value
        // will be checked against the head and rejected if mismatched.
        if resolved_turn.previous_receipt_hash.is_none() {
            if let Some(prev) = executor.get_last_receipt_hash(&resolved_turn.agent) {
                resolved_turn.previous_receipt_hash = Some(prev);
            }
        }

        let result = executor.execute(&resolved_turn, ledger);

        match result {
            TurnResult::Committed { receipt, .. } => {
                committed_hashes.insert(turn_hashes[idx]);
                let outputs = extract_turn_outputs(&resolved_turn, ledger);
                let turn_hash = turn_hashes[idx];
                for (slot, output) in outputs.into_iter().enumerate() {
                    resolution_table.insert((turn_hash, slot as u32), output);
                }
                results[idx] = Some(Ok(receipt));
            }
            TurnResult::Rejected { reason, .. } => {
                failed[idx] = true;
                results[idx] = Some(Err(PipelineError::TurnExecutionFailed {
                    index: idx,
                    reason: format!("{}", reason),
                }));
            }
            TurnResult::Expired | TurnResult::Pending => {
                failed[idx] = true;
                results[idx] = Some(Err(PipelineError::TurnExecutionFailed {
                    index: idx,
                    reason: "conditional turn not resolved in batch context".to_string(),
                }));
            }
        }
    }

    results
        .into_iter()
        .map(|r| r.unwrap_or(Err(PipelineError::Empty)))
        .collect()
}

/// Extract outputs from a committed turn's effects for the resolution table.
///
/// Output slots are assigned deterministically: effects are enumerated by DFS traversal
/// of the call forest (root 0 first, depth-first through children, then root 1, etc.).
/// Within each action node, effects are enumerated in declaration order. Only effects
/// that produce externally-referenceable outputs (CreateCell, GrantCapability, SetField,
/// NoteCreate, SpawnWithDelegation) receive a slot number.
fn extract_turn_outputs(turn: &Turn, ledger: &Ledger) -> Vec<TurnOutput> {
    let mut outputs = Vec::new();
    for root in &turn.call_forest.roots {
        extract_tree_outputs(root, ledger, &mut outputs);
    }
    outputs
}

fn extract_tree_outputs(
    tree: &crate::forest::CallTree,
    ledger: &Ledger,
    outputs: &mut Vec<TurnOutput>,
) {
    for effect in &tree.action.effects {
        match effect {
            crate::action::Effect::CreateCell {
                public_key,
                token_id,
                ..
            } => {
                let cell_id = pyana_cell::CellId::derive_raw(public_key, token_id);
                outputs.push(TurnOutput::CreatedCell { cell: cell_id });
            }
            crate::action::Effect::GrantCapability { to, .. } => {
                let slot = if let Some(cell) = ledger.get(to) {
                    cell.capabilities.len().saturating_sub(1) as u32
                } else {
                    0
                };
                outputs.push(TurnOutput::GrantedCapability { target: *to, slot });
            }
            crate::action::Effect::SetField { cell, index, value } => {
                outputs.push(TurnOutput::StateUpdate {
                    cell: *cell,
                    field: *index,
                    hash: *value,
                });
            }
            crate::action::Effect::NoteCreate { commitment, .. } => {
                outputs.push(TurnOutput::CreatedNote {
                    commitment: commitment.0,
                });
            }
            crate::action::Effect::SpawnWithDelegation {
                child_public_key,
                child_token_id,
                ..
            } => {
                let cell_id = pyana_cell::CellId::derive_raw(child_public_key, child_token_id);
                outputs.push(TurnOutput::CreatedCell { cell: cell_id });
            }
            _ => {}
        }
    }
    for child in &tree.children {
        extract_tree_outputs(child, ledger, outputs);
    }
}

/// Resolve an EventualRef against the resolution table.
pub fn resolve_eventual_ref<'a>(
    eventual_ref: &crate::eventual::EventualRef,
    table: &'a ResolutionTable,
) -> Result<&'a TurnOutput, PipelineError> {
    table
        .get(&(eventual_ref.source_turn, eventual_ref.output_slot))
        .ok_or_else(|| PipelineError::UnresolvedRef {
            eventual_ref: eventual_ref.clone(),
            reason: "output slot not found in resolution table".to_string(),
        })
}

/// Resolve an OutputRef against the resolution table (preferred alias).
pub fn resolve_output_ref<'a>(
    output_ref: &crate::eventual::EventualRef,
    table: &'a ResolutionTable,
) -> Result<&'a TurnOutput, PipelineError> {
    resolve_eventual_ref(output_ref, table)
}

/// Execute a pipeline with structured outcome (atomic + pending support).
pub fn execute_pipeline_result(
    pipeline: Pipeline,
    ledger: &mut Ledger,
    executor: &TurnExecutor,
) -> (Vec<Result<TurnReceipt, PipelineError>>, PipelineResult) {
    let n = pipeline.turns.len();
    if n == 0 {
        return (vec![], PipelineResult::AllCommitted { committed: vec![] });
    }
    let topo_order = match pipeline.topological_order() {
        Ok(order) => order,
        Err(cycle) => {
            let r = vec![Err(PipelineError::Cycle(cycle.clone())); n];
            let f: Vec<(usize, PipelineError)> = (0..n)
                .map(|i| (i, PipelineError::Cycle(cycle.clone())))
                .collect();
            return (
                r,
                PipelineResult::Failed {
                    committed: vec![],
                    failed: f,
                },
            );
        }
    };
    let ledger_snapshot = if pipeline.atomic {
        Some(ledger.clone())
    } else {
        None
    };
    let mut results: Vec<Option<Result<TurnReceipt, PipelineError>>> = vec![None; n];
    let mut failed: Vec<bool> = vec![false; n];
    let mut pending_flags: Vec<bool> = vec![false; n];
    let mut resolution_table: ResolutionTable = HashMap::new();
    let mut turn_hashes: Vec<[u8; 32]> = Vec::with_capacity(n);
    for turn in &pipeline.turns {
        turn_hashes.push(turn.hash());
    }
    for &idx in &topo_order {
        let deps = pipeline.dependencies_of(idx);
        let mut dep_failed = None;
        for dep_idx in &deps {
            if failed[*dep_idx] {
                dep_failed = Some(*dep_idx);
                break;
            }
        }
        if let Some(fd) = dep_failed {
            failed[idx] = true;
            results[idx] = Some(Err(PipelineError::DependencyFailed {
                failed_index: fd,
                dependent_index: idx,
            }));
            continue;
        }
        if deps.iter().any(|d| pending_flags[*d]) {
            pending_flags[idx] = true;
            results[idx] = Some(Err(PipelineError::TurnExecutionFailed {
                index: idx,
                reason: "dependency pending".to_string(),
            }));
            continue;
        }
        let turn = &pipeline.turns[idx];
        let mut resolved_turn = match resolve_turn(turn, &resolution_table) {
            Ok(t) => t,
            Err(e) => {
                failed[idx] = true;
                results[idx] = Some(Err(e));
                continue;
            }
        };
        // P0-3: auto-chain previous_receipt_hash for pipeline turns (see
        // execute_pipeline for rationale).
        if resolved_turn.previous_receipt_hash.is_none() {
            if let Some(prev) = executor.get_last_receipt_hash(&resolved_turn.agent) {
                resolved_turn.previous_receipt_hash = Some(prev);
            }
        }
        let result = executor.execute(&resolved_turn, ledger);
        match result {
            TurnResult::Committed { receipt, .. } => {
                let outputs = extract_turn_outputs(&resolved_turn, ledger);
                let th = turn_hashes[idx];
                for (slot, output) in outputs.into_iter().enumerate() {
                    resolution_table.insert((th, slot as u32), output);
                }
                results[idx] = Some(Ok(receipt));
            }
            TurnResult::Rejected { reason, .. } => {
                failed[idx] = true;
                results[idx] = Some(Err(PipelineError::TurnExecutionFailed {
                    index: idx,
                    reason: format!("{}", reason),
                }));
            }
            TurnResult::Expired => {
                failed[idx] = true;
                results[idx] = Some(Err(PipelineError::TurnExecutionFailed {
                    index: idx,
                    reason: "expired".to_string(),
                }));
            }
            TurnResult::Pending => {
                pending_flags[idx] = true;
                results[idx] = Some(Err(PipelineError::TurnExecutionFailed {
                    index: idx,
                    reason: "conditional pending".to_string(),
                }));
            }
        }
    }
    let ci: Vec<usize> = (0..n)
        .filter(|i| matches!(&results[*i], Some(Ok(_))))
        .collect();
    let fi: Vec<(usize, PipelineError)> = (0..n)
        .filter(|i| failed[*i])
        .filter_map(|i| {
            results[i]
                .as_ref()
                .and_then(|r| r.as_ref().err().cloned())
                .map(|e| (i, e))
        })
        .collect();
    let pi: Vec<usize> = (0..n).filter(|i| pending_flags[*i]).collect();
    if pipeline.atomic && !fi.is_empty() {
        if let Some(snap) = ledger_snapshot {
            *ledger = snap;
        }
        let mut ar: Vec<Result<TurnReceipt, PipelineError>> = Vec::with_capacity(n);
        for i in 0..n {
            if failed[i] || pending_flags[i] {
                ar.push(results[i].take().unwrap_or(Err(PipelineError::Empty)));
            } else {
                ar.push(Err(PipelineError::TurnExecutionFailed {
                    index: i,
                    reason: "atomic rollback".to_string(),
                }));
            }
        }
        return (
            ar,
            PipelineResult::Failed {
                committed: vec![],
                failed: fi,
            },
        );
    }
    let fr: Vec<Result<TurnReceipt, PipelineError>> = results
        .into_iter()
        .map(|r| r.unwrap_or(Err(PipelineError::Empty)))
        .collect();
    let outcome = if !fi.is_empty() {
        PipelineResult::Failed {
            committed: ci,
            failed: fi,
        }
    } else if !pi.is_empty() {
        PipelineResult::PartialWithPending {
            committed: ci,
            pending: pi,
        }
    } else {
        PipelineResult::AllCommitted { committed: ci }
    };
    (fr, outcome)
}

// =============================================================================
// Multi-Party Atomic Proofs
// =============================================================================

/// A single sovereign cell's proof entry in an atomic multi-party turn.
///
/// Each entry binds a cell to its STARK proof and commitment transition.
/// The `balance_delta` field is a PRE-FLIGHT HINT only: the authoritative delta
/// is EXTRACTED from the proof's public inputs by the verifier. This prevents
/// a submitter from lying about their balance change.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AtomicProofEntry {
    /// The sovereign cell ID.
    pub cell_id: CellId,
    /// The serialized STARK proof bytes.
    pub proof: Vec<u8>,
    /// The old state commitment (must match what the federation stores).
    pub old_commitment: [u8; 32],
    /// The new state commitment (will be stored after verification).
    pub new_commitment: [u8; 32],
    /// The BLAKE3 hash of effects this cell is applying.
    pub effects_hash: [u8; 32],
    /// Pre-flight hint of net balance change (positive = receives, negative = sends).
    /// NOT trusted by the executor: the real delta is extracted from PI[32..34] of the proof.
    /// This field exists for client-side pre-validation and routing hints only.
    pub balance_delta: i64,
}

/// A mixed atomic turn containing both sovereign (proof-carrying) and hosted
/// (federation-executed) cells in a single atomic operation.
///
/// Conservation is enforced across BOTH domains: sovereign deltas (extracted from
/// proofs) plus hosted deltas (computed from execution) must sum to zero.
///
/// SECURITY (C1 fix): the hosted side is now expressed as a `Vec<Action>` so
/// each hosted-side operation carries its own `Authorization` (Ed25519 sig,
/// proof, bearer cap, etc.). Each action's authorization is verified via the
/// standard `verify_authorization` pipeline before its effects are applied.
/// Previously `hosted_effects: Vec<(CellId, Vec<Effect>)>` had no
/// per-cell auth, which allowed any caller of `execute_mixed_atomic` to
/// mutate any hosted cell's balance.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MixedAtomicTurn {
    /// The agent submitting this turn (pays fee, provides nonce).
    pub agent: CellId,
    /// Nonce for replay protection.
    pub nonce: u64,
    /// Fee in computrons.
    pub fee: u64,
    /// Proof-carrying sovereign cell entries.
    pub sovereign_entries: Vec<AtomicProofEntry>,
    /// Hosted-side actions. Each `Action` carries its own authorization, which
    /// is verified before any of its effects apply.
    pub hosted_actions: Vec<crate::action::Action>,
}

/// Result of a successful mixed atomic turn execution.
#[derive(Clone, Debug)]
pub struct MixedAtomicResult {
    /// New commitments for sovereign cells (in order of sovereign_entries).
    pub sovereign_commitments: Vec<[u8; 32]>,
    /// Proven balance deltas for sovereign cells (extracted from proofs).
    pub sovereign_deltas: Vec<i64>,
    /// Computed balance deltas for hosted cells.
    pub hosted_deltas: Vec<i64>,
}

/// An atomic multi-party sovereign turn: multiple sovereign cells each provide
/// a STARK proof of their individual state transition. The executor verifies ALL
/// proofs atomically and checks cross-cell conservation (the sum of all balance
/// deltas must be zero).
///
/// This enables multi-party transactions (e.g., Alice sends to Bob) where each
/// party proves their own transition independently, and the federation verifies
/// that the overall conservation law holds.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AtomicSovereignTurn {
    /// The agent submitting this atomic turn (pays fee, provides nonce).
    pub agent: CellId,
    /// Nonce for replay protection (from the agent cell).
    pub nonce: u64,
    /// Fee in computrons (deducted from agent's balance).
    pub fee: u64,
    /// The proof entries: one per sovereign cell involved.
    pub proofs: Vec<AtomicProofEntry>,
}

/// Errors specific to atomic sovereign turn verification.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AtomicTurnError {
    /// No proof entries provided.
    EmptyProofs,
    /// A cell is not registered as sovereign.
    NotSovereign(CellId),
    /// The stored commitment does not match the entry's old_commitment.
    CommitmentMismatch {
        cell: CellId,
        expected: [u8; 32],
        got: [u8; 32],
    },
    /// A STARK proof failed verification.
    ProofFailed { cell: CellId, reason: String },
    /// Cross-cell conservation violated: balance deltas do not sum to zero.
    ConservationViolation { net_excess: i64 },
    /// Agent cell not found (for fee/nonce).
    AgentNotFound(CellId),
    /// Insufficient balance for fee.
    InsufficientFee { available: u64, required: u64 },
    /// Nonce mismatch.
    NonceMismatch { expected: u64, got: u64 },
    /// Duplicate cell in proof entries.
    DuplicateCell(CellId),
    /// A cell referenced by the atomic turn is frozen for migration (P0-4).
    FrozenCell(CellId),
    /// An action in the hosted side failed authorization (C1 fix).
    HostedAuthorizationFailed { cell: CellId, reason: String },
    /// An action in the hosted side failed preconditions or effect application.
    HostedApplyFailed { cell: CellId, reason: String },
}

impl core::fmt::Display for AtomicTurnError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EmptyProofs => write!(f, "atomic turn has no proof entries"),
            Self::NotSovereign(id) => write!(f, "cell {} is not sovereign", id),
            Self::CommitmentMismatch {
                cell,
                expected,
                got,
            } => write!(
                f,
                "commitment mismatch for cell {}: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                cell, expected[0], expected[1], got[0], got[1]
            ),
            Self::ProofFailed { cell, reason } => {
                write!(f, "proof failed for cell {}: {}", cell, reason)
            }
            Self::ConservationViolation { net_excess } => {
                write!(
                    f,
                    "cross-cell conservation violated: net excess = {}",
                    net_excess
                )
            }
            Self::AgentNotFound(id) => write!(f, "agent cell not found: {}", id),
            Self::InsufficientFee {
                available,
                required,
            } => {
                write!(
                    f,
                    "insufficient fee: available {}, required {}",
                    available, required
                )
            }
            Self::NonceMismatch { expected, got } => {
                write!(f, "nonce mismatch: expected {}, got {}", expected, got)
            }
            Self::DuplicateCell(id) => write!(f, "duplicate cell in proof entries: {}", id),
            Self::FrozenCell(id) => {
                write!(f, "cell {} is frozen for migration", id)
            }
            Self::HostedAuthorizationFailed { cell, reason } => {
                write!(f, "hosted action on cell {} failed authorization: {}", cell, reason)
            }
            Self::HostedApplyFailed { cell, reason } => {
                write!(f, "hosted action on cell {} failed to apply: {}", cell, reason)
            }
        }
    }
}

impl std::error::Error for AtomicTurnError {}

impl TurnExecutor {
    /// Execute an atomic multi-party sovereign turn.
    ///
    /// This verifies ALL proofs atomically and checks cross-cell conservation:
    /// the sum of all `balance_delta` values across entries must be zero.
    ///
    /// On success, all sovereign commitments are updated simultaneously.
    /// On failure (any proof invalid or conservation violated), no state changes.
    pub fn execute_atomic_sovereign(
        &self,
        atomic_turn: &AtomicSovereignTurn,
        ledger: &mut Ledger,
    ) -> Result<Vec<[u8; 32]>, AtomicTurnError> {
        use pyana_circuit::field::BabyBear;
        use pyana_circuit::stark;

        // 0. Basic validation.
        if atomic_turn.proofs.is_empty() {
            return Err(AtomicTurnError::EmptyProofs);
        }

        // Check for duplicate cells.
        let mut seen_cells = std::collections::HashSet::new();
        for entry in &atomic_turn.proofs {
            if !seen_cells.insert(entry.cell_id) {
                return Err(AtomicTurnError::DuplicateCell(entry.cell_id));
            }
        }

        // P0-4: reject any frozen agent or proof-entry cell.
        if self
            .cell_migrations
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .is_frozen(&atomic_turn.agent)
        {
            return Err(AtomicTurnError::FrozenCell(atomic_turn.agent));
        }
        {
            let mig = self
                .cell_migrations
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            for entry in &atomic_turn.proofs {
                if mig.is_frozen(&entry.cell_id) {
                    return Err(AtomicTurnError::FrozenCell(entry.cell_id));
                }
            }
        }

        // 1. Agent validation (fee + nonce).
        let agent_cell = ledger
            .get(&atomic_turn.agent)
            .ok_or(AtomicTurnError::AgentNotFound(atomic_turn.agent))?;
        if agent_cell.state.nonce() != atomic_turn.nonce {
            return Err(AtomicTurnError::NonceMismatch {
                expected: agent_cell.state.nonce(),
                got: atomic_turn.nonce,
            });
        }
        if agent_cell.state.balance() < atomic_turn.fee {
            return Err(AtomicTurnError::InsufficientFee {
                available: agent_cell.state.balance(),
                required: atomic_turn.fee,
            });
        }

        // 2. Verify each proof entry and extract proven balance deltas.
        let mut new_commitments: Vec<(CellId, [u8; 32])> =
            Vec::with_capacity(atomic_turn.proofs.len());
        let mut proven_deltas: Vec<i64> = Vec::with_capacity(atomic_turn.proofs.len());

        for entry in &atomic_turn.proofs {
            let stored_commitment = if let Some(c) = ledger.get_sovereign_commitment(&entry.cell_id)
            {
                *c
            } else if let Some(reg) = ledger.get_sovereign_registration(&entry.cell_id) {
                reg.commitment
            } else {
                return Err(AtomicTurnError::NotSovereign(entry.cell_id));
            };

            if entry.old_commitment != stored_commitment {
                return Err(AtomicTurnError::CommitmentMismatch {
                    cell: entry.cell_id,
                    expected: stored_commitment,
                    got: entry.old_commitment,
                });
            }

            let proof = stark::proof_from_bytes(&entry.proof).map_err(|e| {
                AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: e,
                }
            })?;

            // Stage 1: reconstruct Effect VM PI in the widened layout
            // (resolves REVIEW[effect-vm-coord]). Commitments are 4 felts
            // each; other PIs are forwarded from the proof and bound by
            // the AIR's boundary/transition constraints + the PI matching
            // loop below.
            let old_commit_4 = Self::commitment_to_4bb(&entry.old_commitment);
            let new_commit_4 = Self::commitment_to_4bb(&entry.new_commitment);

            use pyana_circuit::effect_vm::pi;
            let min_pi_count = pi::BASE_COUNT;
            if proof.public_inputs.len() < min_pi_count {
                return Err(AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: format!(
                        "proof has {} public inputs, expected at least {}",
                        proof.public_inputs.len(),
                        min_pi_count
                    ),
                });
            }

            // Forward all PI elements from the proof, then override
            // commitment slots with verifier-derived values.
            let mut public_inputs: Vec<BabyBear> = (0..min_pi_count)
                .map(|i| BabyBear::new_canonical(proof.public_inputs[i]))
                .collect();
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

            // Verify reconstructed commitment PIs match the proof's embedded PIs
            // (all 4 felts each, Stage 1 widening).
            for i in 0..pi::OLD_COMMIT_LEN {
                let proof_v =
                    BabyBear::new_canonical(proof.public_inputs[pi::OLD_COMMIT_BASE + i]);
                if proof_v != old_commit_4[i] {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "old_commitment in proof does not match stored value (felt {})",
                            i
                        ),
                    });
                }
            }
            for i in 0..pi::NEW_COMMIT_LEN {
                let proof_v =
                    BabyBear::new_canonical(proof.public_inputs[pi::NEW_COMMIT_BASE + i]);
                if proof_v != new_commit_4[i] {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "new_commitment in proof does not match claimed value (felt {})",
                            i
                        ),
                    });
                }
            }

            // Verify against custom program or default AIR (EffectVmAir).
            let vk_hash = self.get_cell_vk_hash(&entry.cell_id, ledger);
            if let Some(vk) = vk_hash {
                if let Some(program) = self.program_registry.get(&vk) {
                    program
                        .verify_transition(&public_inputs, &entry.proof)
                        .map_err(|e| AtomicTurnError::ProofFailed {
                            cell: entry.cell_id,
                            reason: e.to_string(),
                        })?;
                } else {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "cell has vk_hash {:02x}{:02x}... but no matching program",
                            vk[0], vk[1]
                        ),
                    });
                }
            } else {
                let air = pyana_circuit::EffectVmAir::new(proof.trace_len);
                stark::verify(&air, &proof, &public_inputs).map_err(|e| {
                    AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: e,
                    }
                })?;
            }

            // Extract proven balance delta from PI.
            let proven_delta =
                pyana_circuit::extract_net_delta(&public_inputs).ok_or_else(|| {
                    AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: "failed to extract balance_delta from proof PI".to_string(),
                    }
                })?;
            proven_deltas.push(proven_delta);
            new_commitments.push((entry.cell_id, entry.new_commitment));
        }

        // 3. Conservation check using PROVEN deltas (not declared entry.balance_delta).
        let net_excess: i64 = proven_deltas.iter().sum();
        if net_excess != 0 {
            return Err(AtomicTurnError::ConservationViolation { net_excess });
        }

        // 4. All proofs verified + conservation holds. Commit atomically.
        // Deduct fee and increment nonce.
        {
            let agent = ledger.get_mut(&atomic_turn.agent).unwrap();
            agent.state.set_balance(agent.state.balance() - atomic_turn.fee);
            agent.state.increment_nonce();
        }

        // Update all sovereign commitments.
        let mut resulting_commitments = Vec::with_capacity(new_commitments.len());
        for (cell_id, new_commitment) in &new_commitments {
            if ledger.is_sovereign(cell_id) {
                let _ = ledger.update_sovereign_commitment(cell_id, *new_commitment);
            } else {
                let old = ledger
                    .get_sovereign_registration(cell_id)
                    .map(|r| r.commitment)
                    .unwrap_or([0u8; 32]);
                let _ = ledger.update_sovereign_registration_commitment(
                    cell_id,
                    old,
                    *new_commitment,
                    self.block_height,
                );
            }
            resulting_commitments.push(*new_commitment);
        }

        Ok(resulting_commitments)
    }

    /// Execute a mixed atomic turn containing both sovereign (proof-carrying) and
    /// hosted (federation-executed) cells in a single atomic operation.
    ///
    /// Conservation is enforced across BOTH: sovereign deltas (extracted from proofs)
    /// plus hosted deltas (computed from execution) must sum to zero.
    ///
    /// SECURITY (C1 fix): every hosted action's authorization is verified through
    /// the standard `verify_authorization` pipeline before any of its effects
    /// apply, and ALL hosted mutations are journaled so that any subsequent
    /// failure (auth, precondition, effect-apply, conservation) rolls back the
    /// entire turn atomically. Previously the hosted side could mutate any
    /// cell's balance without authorization.
    pub fn execute_mixed_atomic(
        &self,
        mixed_turn: &MixedAtomicTurn,
        ledger: &mut Ledger,
    ) -> Result<MixedAtomicResult, AtomicTurnError> {
        use pyana_circuit::field::BabyBear;
        use pyana_circuit::stark;

        if mixed_turn.sovereign_entries.is_empty() && mixed_turn.hosted_actions.is_empty() {
            return Err(AtomicTurnError::EmptyProofs);
        }

        let agent_cell = ledger
            .get(&mixed_turn.agent)
            .ok_or(AtomicTurnError::AgentNotFound(mixed_turn.agent))?;
        if agent_cell.state.nonce() != mixed_turn.nonce {
            return Err(AtomicTurnError::NonceMismatch {
                expected: agent_cell.state.nonce(),
                got: mixed_turn.nonce,
            });
        }
        if agent_cell.state.balance() < mixed_turn.fee {
            return Err(AtomicTurnError::InsufficientFee {
                available: agent_cell.state.balance(),
                required: mixed_turn.fee,
            });
        }

        // P0-4: reject any frozen agent, sovereign-entry cell, or hosted-action
        // target cell.
        {
            let mig = self
                .cell_migrations
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            if mig.is_frozen(&mixed_turn.agent) {
                return Err(AtomicTurnError::FrozenCell(mixed_turn.agent));
            }
            for entry in &mixed_turn.sovereign_entries {
                if mig.is_frozen(&entry.cell_id) {
                    return Err(AtomicTurnError::FrozenCell(entry.cell_id));
                }
            }
            for action in &mixed_turn.hosted_actions {
                if mig.is_frozen(&action.target) {
                    return Err(AtomicTurnError::FrozenCell(action.target));
                }
            }
        }

        // Verify sovereign proofs and extract proven deltas.
        let mut sovereign_deltas: Vec<i64> = Vec::new();
        let mut new_commitments: Vec<(CellId, [u8; 32])> = Vec::new();

        for entry in &mixed_turn.sovereign_entries {
            let stored_commitment = if let Some(c) = ledger.get_sovereign_commitment(&entry.cell_id)
            {
                *c
            } else if let Some(reg) = ledger.get_sovereign_registration(&entry.cell_id) {
                reg.commitment
            } else {
                return Err(AtomicTurnError::NotSovereign(entry.cell_id));
            };

            if entry.old_commitment != stored_commitment {
                return Err(AtomicTurnError::CommitmentMismatch {
                    cell: entry.cell_id,
                    expected: stored_commitment,
                    got: entry.old_commitment,
                });
            }

            let proof = stark::proof_from_bytes(&entry.proof).map_err(|e| {
                AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: e,
                }
            })?;

            // Stage 1: reconstruct Effect VM PI in the widened layout
            // (resolves REVIEW[effect-vm-coord]).
            let old_commit_4 = Self::commitment_to_4bb(&entry.old_commitment);
            let new_commit_4 = Self::commitment_to_4bb(&entry.new_commitment);

            use pyana_circuit::effect_vm::pi;
            let min_pi_count = pi::BASE_COUNT;
            if proof.public_inputs.len() < min_pi_count {
                return Err(AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: format!(
                        "proof has {} public inputs, expected at least {}",
                        proof.public_inputs.len(),
                        min_pi_count
                    ),
                });
            }

            let mut public_inputs: Vec<BabyBear> = (0..min_pi_count)
                .map(|i| BabyBear::new_canonical(proof.public_inputs[i]))
                .collect();
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

            // Verify commitment PIs match (4 felts each).
            for i in 0..pi::OLD_COMMIT_LEN {
                let proof_v =
                    BabyBear::new_canonical(proof.public_inputs[pi::OLD_COMMIT_BASE + i]);
                if proof_v != old_commit_4[i] {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "old_commitment in proof does not match stored value (felt {})",
                            i
                        ),
                    });
                }
            }
            for i in 0..pi::NEW_COMMIT_LEN {
                let proof_v =
                    BabyBear::new_canonical(proof.public_inputs[pi::NEW_COMMIT_BASE + i]);
                if proof_v != new_commit_4[i] {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "new_commitment in proof does not match claimed value (felt {})",
                            i
                        ),
                    });
                }
            }

            // Verify against custom program or default EffectVmAir.
            let vk_hash = self.get_cell_vk_hash(&entry.cell_id, ledger);
            if let Some(vk) = vk_hash {
                if let Some(program) = self.program_registry.get(&vk) {
                    program
                        .verify_transition(&public_inputs, &entry.proof)
                        .map_err(|e| AtomicTurnError::ProofFailed {
                            cell: entry.cell_id,
                            reason: e.to_string(),
                        })?;
                } else {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: "program not found for vk_hash".to_string(),
                    });
                }
            } else {
                let air = pyana_circuit::EffectVmAir::new(proof.trace_len);
                stark::verify(&air, &proof, &public_inputs).map_err(|e| {
                    AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: e,
                    }
                })?;
            }

            let proven_delta =
                pyana_circuit::extract_net_delta(&public_inputs).ok_or_else(|| {
                    AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: "failed to extract balance_delta from proof PI".to_string(),
                    }
                })?;
            sovereign_deltas.push(proven_delta);
            new_commitments.push((entry.cell_id, entry.new_commitment));
        }

        // ====================================================================
        // HOSTED SIDE (C1 FIX): each hosted action is authorized via the same
        // `verify_authorization` pipeline as `execute()` and applied through
        // `apply_effect` with full journaling. On any failure (auth,
        // precondition, effect, conservation) the entire journal is rolled
        // back -- no partial state is left in the ledger.
        // ====================================================================
        let mut journal = LedgerJournal::with_capacity(16);
        let mut hosted_deltas: Vec<i64> = Vec::with_capacity(mixed_turn.hosted_actions.len());

        for (idx, action) in mixed_turn.hosted_actions.iter().enumerate() {
            // 1. Target cell must exist.
            let target_cell = match ledger.get(&action.target) {
                Some(c) => c.clone(),
                None => {
                    journal.rollback(
                        ledger,
                        &self.obligations,
                        &self.escrows,
                        &self.bridged_nullifiers,
                        &self.committed_escrows,
                        &self.committed_escrow_amounts,
                    );
                    return Err(AtomicTurnError::HostedApplyFailed {
                        cell: action.target,
                        reason: format!("hosted action #{} target cell not found", idx),
                    });
                }
            };

            // 2. Authorization (the C1 fix). Use the same gate as `execute()`.
            let path = vec![idx];
            if let Err((err, _path)) = self.verify_authorization(
                action,
                &target_cell,
                ledger,
                &mixed_turn.agent,
                &path,
                mixed_turn.nonce,
            ) {
                journal.rollback(
                    ledger,
                    &self.obligations,
                    &self.escrows,
                    &self.bridged_nullifiers,
                    &self.committed_escrows,
                    &self.committed_escrow_amounts,
                );
                return Err(AtomicTurnError::HostedAuthorizationFailed {
                    cell: action.target,
                    reason: format!("{err}"),
                });
            }

            // 3. Preconditions.
            if let Err((err, _)) =
                self.check_preconditions(&action.preconditions, &target_cell, &path)
            {
                journal.rollback(
                    ledger,
                    &self.obligations,
                    &self.escrows,
                    &self.bridged_nullifiers,
                    &self.committed_escrows,
                    &self.committed_escrow_amounts,
                );
                return Err(AtomicTurnError::HostedApplyFailed {
                    cell: action.target,
                    reason: format!("{err}"),
                });
            }

            // 4. Apply each effect via apply_effect (which is journaled).
            // Compute the net Transfer delta for this hosted entry for the
            // conservation check after-the-fact.
            let mut net_delta: i64 = 0;
            for effect in &action.effects {
                if let crate::action::Effect::Transfer { from, to, amount } = effect {
                    if from == &action.target {
                        net_delta -= *amount as i64;
                    }
                    if to == &action.target {
                        net_delta += *amount as i64;
                    }
                }
                if let Err((err, _)) = self.apply_effect(
                    effect,
                    ledger,
                    &path,
                    &action.target,
                    &mixed_turn.agent,
                    &mut journal,
                ) {
                    journal.rollback(
                        ledger,
                        &self.obligations,
                        &self.escrows,
                        &self.bridged_nullifiers,
                        &self.committed_escrows,
                        &self.committed_escrow_amounts,
                    );
                    return Err(AtomicTurnError::HostedApplyFailed {
                        cell: action.target,
                        reason: format!("{err}"),
                    });
                }
            }
            hosted_deltas.push(net_delta);
        }

        // Cross-domain conservation: sovereign + hosted must sum to zero.
        let total_delta: i64 =
            sovereign_deltas.iter().sum::<i64>() + hosted_deltas.iter().sum::<i64>();
        if total_delta != 0 {
            // Roll back ALL hosted mutations before returning.
            journal.rollback(
                ledger,
                &self.obligations,
                &self.escrows,
                &self.bridged_nullifiers,
                &self.committed_escrows,
                &self.committed_escrow_amounts,
            );
            return Err(AtomicTurnError::ConservationViolation {
                net_excess: total_delta,
            });
        }

        // ====================================================================
        // COMMIT: hosted mutations are already in place (in `ledger`) via
        // apply_effect; we just commit fee, nonce, and sovereign commitment
        // updates. We deliberately do NOT call rollback on the journal -- we
        // want to keep the mutations; the journal is dropped on success.
        // ====================================================================
        {
            let agent = ledger.get_mut(&mixed_turn.agent).unwrap();
            agent.state.set_balance(agent.state.balance() - mixed_turn.fee);
            agent.state.increment_nonce();
        }

        for (cell_id, new_commitment) in &new_commitments {
            if ledger.is_sovereign(cell_id) {
                let _ = ledger.update_sovereign_commitment(cell_id, *new_commitment);
            } else {
                let old = ledger
                    .get_sovereign_registration(cell_id)
                    .map(|r| r.commitment)
                    .unwrap_or([0u8; 32]);
                let _ = ledger.update_sovereign_registration_commitment(
                    cell_id,
                    old,
                    *new_commitment,
                    self.block_height,
                );
            }
        }

        Ok(MixedAtomicResult {
            sovereign_commitments: new_commitments.iter().map(|(_, c)| *c).collect(),
            sovereign_deltas,
            hosted_deltas,
        })
    }
}

// =============================================================================
// Cell Migration Tests
// =============================================================================

#[cfg(test)]
mod migration_tests {
    use super::*;

    fn test_cell() -> CellId {
        CellId([0xCC; 32])
    }

    fn target_federation() -> [u8; 32] {
        [0xDD; 32]
    }

    #[test]
    fn migration_happy_path() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();
        let target = target_federation();

        // Begin migration: freeze the cell
        mgr.begin_migration(cell, target, 100, 50).unwrap();
        assert!(mgr.is_frozen(&cell));
        assert!(!mgr.is_cancelled(&cell));

        // Bundle sent
        mgr.bundle_sent(cell, 105, 30).unwrap();
        assert!(mgr.is_frozen(&cell)); // Still frozen while awaiting receipt

        // Receipt confirmed
        mgr.confirm_receipt(cell, 110).unwrap();
        assert!(!mgr.is_frozen(&cell)); // No longer frozen after completion

        // Verify final state
        match mgr.get(&cell) {
            Some(MigrationState::Completed {
                confirmed_at,
                target: t,
                ..
            }) => {
                assert_eq!(*confirmed_at, 110);
                assert_eq!(*t, target);
            }
            other => panic!("expected Completed, got {:?}", other),
        }
    }

    #[test]
    fn migration_timeout_during_freeze_cancels() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();

        // Freeze with timeout of 50 blocks
        mgr.begin_migration(cell, target_federation(), 100, 50)
            .unwrap();
        assert!(mgr.is_frozen(&cell));

        // At height 140 (40 blocks elapsed): not yet timed out
        let cancelled = mgr.check_timeouts(140);
        assert!(cancelled.is_empty());
        assert!(mgr.is_frozen(&cell));

        // At height 160 (60 blocks elapsed > 50 timeout): should cancel
        let cancelled = mgr.check_timeouts(160);
        assert_eq!(cancelled, vec![cell]);
        assert!(!mgr.is_frozen(&cell));
        assert!(mgr.is_cancelled(&cell));

        match mgr.get(&cell) {
            Some(MigrationState::Cancelled { reason, .. }) => {
                assert_eq!(*reason, MigrationCancelReason::Timeout);
            }
            other => panic!("expected Cancelled, got {:?}", other),
        }
    }

    #[test]
    fn migration_timeout_during_awaiting_receipt_cancels() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();

        mgr.begin_migration(cell, target_federation(), 100, 50)
            .unwrap();
        mgr.bundle_sent(cell, 110, 20).unwrap(); // receipt timeout = 20 blocks

        // At height 125 (15 blocks since send): not timed out
        let cancelled = mgr.check_timeouts(125);
        assert!(cancelled.is_empty());

        // At height 135 (25 blocks since send > 20 timeout): cancel
        let cancelled = mgr.check_timeouts(135);
        assert_eq!(cancelled, vec![cell]);
        assert!(!mgr.is_frozen(&cell));
        assert!(mgr.is_cancelled(&cell));
    }

    #[test]
    fn migration_cannot_start_while_already_migrating() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();

        mgr.begin_migration(cell, target_federation(), 100, 50)
            .unwrap();

        // Second migration attempt fails
        let err = mgr.begin_migration(cell, [0xEE; 32], 105, 50).unwrap_err();
        assert_eq!(err, MigrationError::AlreadyMigrating);
    }

    #[test]
    fn migration_can_restart_after_cancellation() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();

        // First attempt: times out
        mgr.begin_migration(cell, target_federation(), 100, 10)
            .unwrap();
        mgr.check_timeouts(120);
        assert!(mgr.is_cancelled(&cell));

        // Can start a new migration after cancellation
        mgr.begin_migration(cell, [0xEE; 32], 130, 50).unwrap();
        assert!(mgr.is_frozen(&cell));
        assert!(!mgr.is_cancelled(&cell));
    }

    #[test]
    fn migration_explicit_cancel() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();

        mgr.begin_migration(cell, target_federation(), 100, 50)
            .unwrap();
        mgr.cancel(cell, MigrationCancelReason::Explicit).unwrap();

        assert!(!mgr.is_frozen(&cell));
        assert!(mgr.is_cancelled(&cell));
    }

    #[test]
    fn migration_invalid_transitions_rejected() {
        let mut mgr = CellMigrationManager::new();
        let cell = test_cell();

        // Can't send bundle before freezing
        assert_eq!(
            mgr.bundle_sent(cell, 100, 20),
            Err(MigrationError::NotMigrating)
        );

        // Can't confirm receipt before sending bundle
        mgr.begin_migration(cell, target_federation(), 100, 50)
            .unwrap();
        assert_eq!(
            mgr.confirm_receipt(cell, 105),
            Err(MigrationError::InvalidTransition)
        );
    }

    #[test]
    fn migration_gc_removes_terminal_states() {
        let mut mgr = CellMigrationManager::new();
        let cell1 = CellId([0x11; 32]);
        let cell2 = CellId([0x22; 32]);
        let cell3 = CellId([0x33; 32]);

        // cell1: completed
        mgr.begin_migration(cell1, target_federation(), 100, 50)
            .unwrap();
        mgr.bundle_sent(cell1, 105, 30).unwrap();
        mgr.confirm_receipt(cell1, 110).unwrap();

        // cell2: cancelled
        mgr.begin_migration(cell2, target_federation(), 100, 10)
            .unwrap();
        mgr.check_timeouts(120);

        // cell3: still frozen (active)
        mgr.begin_migration(cell3, target_federation(), 100, 50)
            .unwrap();

        // GC should remove completed and cancelled, keep active
        let removed = mgr.gc_completed();
        assert_eq!(removed.len(), 2);
        assert!(removed.contains(&cell1));
        assert!(removed.contains(&cell2));
        assert!(mgr.is_frozen(&cell3)); // still tracked
        assert!(mgr.get(&cell1).is_none()); // cleaned up
    }
}

// =============================================================================
// Adversarial Tests for CRITICAL/P0 fixes (C1, P0-3, P0-4)
// =============================================================================

#[cfg(test)]
mod hardening_tests {
    use super::*;
    use crate::action::{Action, Authorization, DelegationMode, Effect};
    use crate::forest::{CallForest, CallTree};
    use crate::turn::Turn;
    use pyana_cell::permissions::{AuthRequired, Permissions};
    use pyana_cell::{Cell, Preconditions};

    fn permissive() -> Permissions {
        Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    fn make_permissive_cell(seed: u8, balance: u64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        let token = [0u8; 32];
        let mut cell = Cell::with_balance(pk, token, balance);
        cell.permissions = permissive();
        cell
    }

    fn make_signed_cell(seed: u8, balance: u64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        let token = [0u8; 32];
        // Default permissions: Signature required.
        Cell::with_balance(pk, token, balance)
    }

    fn build_noop_turn(agent: CellId, nonce: u64) -> Turn {
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
        };
        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };
        Turn {
            agent,
            nonce,
            call_forest: CallForest {
                roots: vec![tree],
                forest_hash: [0u8; 32],
            },
            fee: 0,
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
        }
    }

    // ---------------- P0-3: previous_receipt_hash enforcement ----------------

    /// Submit two turns with the same nonce=0 and `previous_receipt_hash: None`.
    /// The second MUST be rejected -- without the P0-3 fix the executor would
    /// accept both because it never bound the receipt chain at write time.
    #[test]
    fn previous_receipt_hash_replay_blocked() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let turn1 = build_noop_turn(agent_id, 0);
        let r1 = executor.execute(&turn1, &mut ledger);
        assert!(r1.is_committed(), "first turn should commit: {:?}", r1);

        // Second turn from same agent with previous_receipt_hash: None.
        // Reset nonce by building with nonce 1 (which is the actual next nonce).
        let turn2 = build_noop_turn(agent_id, 1);
        let r2 = executor.execute(&turn2, &mut ledger);
        match r2 {
            TurnResult::Rejected {
                reason: TurnError::ReceiptChainMismatch { expected, got },
                ..
            } => {
                assert!(expected.is_some(), "expected = Some(prev_receipt_hash)");
                assert!(got.is_none(), "got = None (the bug pattern)");
            }
            other => panic!("expected ReceiptChainMismatch, got: {:?}", other),
        }
    }

    /// Submit a non-genesis turn whose `previous_receipt_hash` doesn't match
    /// the prior receipt -- MUST be rejected (no rebranching the chain).
    #[test]
    fn previous_receipt_hash_wrong_chain_rejected() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let turn1 = build_noop_turn(agent_id, 0);
        let r1 = executor.execute(&turn1, &mut ledger);
        assert!(r1.is_committed());

        // Build turn2 with WRONG previous_receipt_hash.
        let mut turn2 = build_noop_turn(agent_id, 1);
        turn2.previous_receipt_hash = Some([0xAB; 32]);
        let r2 = executor.execute(&turn2, &mut ledger);
        match r2 {
            TurnResult::Rejected {
                reason: TurnError::ReceiptChainMismatch { expected, got },
                ..
            } => {
                assert!(expected.is_some());
                assert_eq!(got, Some([0xAB; 32]));
            }
            other => panic!("expected ReceiptChainMismatch, got: {:?}", other),
        }
    }

    /// Properly chained sequential turns MUST commit.
    #[test]
    fn previous_receipt_hash_correct_chain_accepted() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let turn1 = build_noop_turn(agent_id, 0);
        let (_, receipt1, _) = executor.execute(&turn1, &mut ledger).unwrap_committed();

        let mut turn2 = build_noop_turn(agent_id, 1);
        turn2.previous_receipt_hash = Some(receipt1.receipt_hash());
        let r2 = executor.execute(&turn2, &mut ledger);
        assert!(r2.is_committed(), "correctly-chained turn must commit: {:?}", r2);
    }

    /// A turn that claims a prior receipt when the executor has none on file
    /// MUST be rejected (a wallet can't fake an established chain).
    #[test]
    fn previous_receipt_hash_genesis_with_some_rejected() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let mut turn = build_noop_turn(agent_id, 0);
        turn.previous_receipt_hash = Some([0x42; 32]);
        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::ReceiptChainMismatch { expected, got },
                ..
            } => {
                assert!(expected.is_none(), "executor has no prior receipt");
                assert_eq!(got, Some([0x42; 32]));
            }
            other => panic!("expected ReceiptChainMismatch, got: {:?}", other),
        }
    }

    // ---------------- P0-4: CellMigrationManager enforcement ----------------

    /// A turn whose agent cell is frozen for migration MUST be rejected.
    #[test]
    fn migration_frozen_agent_blocks_execute() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Freeze the agent cell for migration.
        executor
            .cell_migrations
            .lock()
            .unwrap()
            .begin_migration(agent_id, [0xDD; 32], 0, 100)
            .unwrap();

        let turn = build_noop_turn(agent_id, 0);
        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::CellFrozen { cell },
                ..
            } => assert_eq!(cell, agent_id),
            other => panic!("expected CellFrozen, got: {:?}", other),
        }
    }

    /// A turn that transfers TO a frozen cell MUST be rejected.
    #[test]
    fn migration_frozen_target_blocks_transfer() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 10_000);
        let agent_id = agent.id();
        let target = make_permissive_cell(2, 0);
        let target_id = target.id();
        // Grant agent capability to target so cross-cell check passes.
        let mut a = agent;
        a.capabilities.grant(target_id, AuthRequired::None);
        ledger.insert_cell(a).unwrap();
        ledger.insert_cell(target).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        executor
            .cell_migrations
            .lock()
            .unwrap()
            .begin_migration(target_id, [0xDD; 32], 0, 100)
            .unwrap();

        // Build a transfer turn (agent -> target).
        let action = Action {
            target: agent_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount: 100,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
        };
        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };
        let mut turn = build_noop_turn(agent_id, 0);
        turn.call_forest = CallForest {
            roots: vec![tree],
            forest_hash: [0u8; 32],
        };
        turn.fee = 0;

        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::CellFrozen { cell },
                ..
            } => assert_eq!(cell, target_id),
            other => panic!("expected CellFrozen(target), got: {:?}", other),
        }
    }

    /// `execute_atomic_sovereign` MUST reject when a sovereign-entry cell is
    /// frozen.
    #[test]
    fn migration_frozen_blocks_atomic_sovereign() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        let frozen_id = CellId([0xCC; 32]);
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        executor
            .cell_migrations
            .lock()
            .unwrap()
            .begin_migration(frozen_id, [0xDD; 32], 0, 100)
            .unwrap();

        let atomic = AtomicSovereignTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            proofs: vec![AtomicProofEntry {
                cell_id: frozen_id,
                proof: vec![1, 2, 3, 4],
                old_commitment: [0u8; 32],
                new_commitment: [1u8; 32],
                effects_hash: [0u8; 32],
                balance_delta: 0,
            }],
        };

        let r = executor.execute_atomic_sovereign(&atomic, &mut ledger);
        match r {
            Err(AtomicTurnError::FrozenCell(cell)) => assert_eq!(cell, frozen_id),
            other => panic!("expected FrozenCell, got: {:?}", other),
        }
    }

    // ---------------- CRITICAL C1: execute_mixed_atomic auth ----------------

    /// The CRITICAL fix: a hosted action targeting a cell the caller has no
    /// authority over MUST be rejected by `execute_mixed_atomic`. Without the
    /// fix, the call would mutate the target cell's balance.
    #[test]
    fn mixed_atomic_hosted_unauthorized_rejected() {
        let mut ledger = Ledger::new();
        // Agent (attacker) and victim cell both exist; victim REQUIRES Signature.
        let agent = make_permissive_cell(0xAA, 1000);
        let agent_id = agent.id();
        let victim = make_signed_cell(0xBB, 1000);
        let victim_id = victim.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(victim.clone()).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Attacker constructs a hosted action that targets the victim cell but
        // provides `Authorization::Unchecked` (no signature). The victim cell's
        // default permissions require Signature for SetField; verify_authorization
        // MUST reject.
        let malicious_action = Action {
            target: victim_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::SetField {
                cell: victim_id,
                index: 0,
                value: [0xFF; 32],
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
        };

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![malicious_action],
        };

        let r = executor.execute_mixed_atomic(&mixed, &mut ledger);
        assert!(
            matches!(r, Err(AtomicTurnError::HostedAuthorizationFailed { cell, .. }) if cell == victim_id),
            "expected HostedAuthorizationFailed on victim cell, got: {:?}",
            r
        );

        // Victim's state MUST be unchanged.
        let v = ledger.get(&victim_id).unwrap();
        assert_eq!(v.state.fields[0], pyana_cell::state::FIELD_ZERO);
    }

    /// C1 / P1-7: a later hosted-action failure MUST roll back earlier hosted
    /// mutations within the same `execute_mixed_atomic` call.
    #[test]
    fn mixed_atomic_late_failure_rolls_back_hosted_mutations() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0xAA, 100);
        let agent_id = agent.id();
        let cell_b = make_permissive_cell(0xBB, 1_000);
        let cell_b_id = cell_b.id();
        let cell_c = make_permissive_cell(0xCC, 50);
        let cell_c_id = cell_c.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(cell_b).unwrap();
        ledger.insert_cell(cell_c).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Action 1: B sends 100 to C (succeeds; both permissive).
        let a1 = Action {
            target: cell_b_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: cell_b_id,
                to: cell_c_id,
                amount: 100,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
        };
        // Action 2: C sends 999_999 to B (FAILS: insufficient balance after first
        // action). Journal MUST roll back action 1.
        let a2 = Action {
            target: cell_c_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: cell_c_id,
                to: cell_b_id,
                amount: 999_999,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
        };

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![a1, a2],
        };

        let r = executor.execute_mixed_atomic(&mixed, &mut ledger);
        assert!(r.is_err(), "expected late failure, got: {:?}", r);

        // Balances MUST be unchanged (rollback worked).
        assert_eq!(ledger.get(&cell_b_id).unwrap().state.balance(), 1_000);
        assert_eq!(ledger.get(&cell_c_id).unwrap().state.balance(), 50);
    }

    /// P2-2: set_timestamp MUST silently ignore backwards-in-time updates.
    #[test]
    fn set_timestamp_backwards_no_op() {
        let mut executor = TurnExecutor::new(ComputronCosts::zero());
        executor.set_timestamp(100);
        assert_eq!(executor.current_timestamp, 100);
        executor.set_timestamp(50); // backwards
        assert_eq!(executor.current_timestamp, 100, "must not go backwards");
        executor.set_timestamp(100); // same
        assert_eq!(executor.current_timestamp, 100);
        executor.set_timestamp(200); // forward
        assert_eq!(executor.current_timestamp, 200);
    }

    /// A hosted Transfer from a victim's cell MUST be rejected (the attacker
    /// has no Signature for the victim's Send permission).
    #[test]
    fn mixed_atomic_hosted_unauthorized_transfer_blocked() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0xAA, 100);
        let agent_id = agent.id();
        let victim = make_signed_cell(0xBB, 10_000);
        let victim_id = victim.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(victim).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Malicious hosted action: transfer from victim -> agent.
        let action = Action {
            target: victim_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: victim_id,
                to: agent_id,
                amount: 5_000,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
        };

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![action],
        };

        let r = executor.execute_mixed_atomic(&mixed, &mut ledger);
        assert!(matches!(r, Err(AtomicTurnError::HostedAuthorizationFailed { .. })));

        // Both balances UNCHANGED.
        assert_eq!(ledger.get(&victim_id).unwrap().state.balance(), 10_000);
        assert_eq!(ledger.get(&agent_id).unwrap().state.balance(), 100);
    }

    // ---------------- R-4: executor_signature actually populated -----------
    //
    // EFFECT-VM-SHAPE-A.md R-4: previously TurnReceipt.executor_signature was
    // never set, so the federation-exit path could not authenticate receipts
    // as having come from a known executor. These tests pin the new behavior:
    //
    //   1. Without a signing key configured, receipts keep the legacy None.
    //   2. With a signing key configured (via `with_executor_signing_key`),
    //      every committed receipt is signed over receipt_hash().
    //   3. The signature verifies under the executor's matching public key
    //      and is rejected under any other key.

    #[test]
    fn executor_signature_default_none() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(7, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let turn = build_noop_turn(agent_id, 0);
        let result = executor.execute(&turn, &mut ledger);
        match result {
            TurnResult::Committed { receipt, .. } => {
                assert!(
                    receipt.executor_signature.is_none(),
                    "without with_executor_signing_key, executor_signature must remain None"
                );
            }
            other => panic!("expected Committed, got {:?}", other),
        }
    }

    #[test]
    fn executor_signature_populated_and_verifies() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(11, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        // Deterministic key seed for the test.
        let seed: [u8; 32] = *b"pyana-test-executor-sk-r4-fix!!!";
        let sk = ed25519_dalek::SigningKey::from_bytes(&seed);
        let pk_bytes = sk.verifying_key().to_bytes();

        let executor = TurnExecutor::new(ComputronCosts::zero()).with_executor_signing_key(seed);
        let turn = build_noop_turn(agent_id, 0);

        let result = executor.execute(&turn, &mut ledger);
        let receipt = match result {
            TurnResult::Committed { receipt, .. } => receipt,
            other => panic!("expected Committed, got {:?}", other),
        };

        // Signature is present and exactly 64 bytes.
        let sig_bytes = receipt
            .executor_signature
            .as_ref()
            .expect("executor_signature must be populated when signing key configured");
        assert_eq!(sig_bytes.len(), 64);

        // Chain verification accepts the receipt under the matching key.
        crate::verify::verify_receipt_chain_with_keys(&[receipt.clone()], &[pk_bytes])
            .expect("receipt chain must verify under the executor's public key");

        // ...and rejects it under any other key.
        let mut wrong_key = pk_bytes;
        wrong_key[0] ^= 0x80;
        let err = crate::verify::verify_receipt_chain_with_keys(&[receipt], &[wrong_key])
            .expect_err("verification must fail under a foreign key");
        assert!(
            matches!(err, crate::verify::VerifyError::ExecutorSignatureInvalid { .. }),
            "expected ExecutorSignatureInvalid, got {:?}",
            err
        );
    }
}
