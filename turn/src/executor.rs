//! TurnExecutor: applies a turn to a ledger with full atomicity.
//!
//! The executor walks the call forest depth-first, checking preconditions,
//! verifying authorization, applying effects, and metering computrons at each step.
//! If any action fails, ALL effects are rolled back via journal replay (atomicity guarantee).

use std::collections::HashMap;
use std::sync::Mutex;

use ed25519_dalek::{Signature, VerifyingKey};
use pyana_cell::{
    AuthRequired, Cell, CellId, CellStateDelta, Ledger, LedgerDelta, Preconditions,
    RevocationChannelSet, ValueCommitment, ValueCommitmentBytes,
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

/// The turn executor: applies turns to a ledger atomically.
pub struct TurnExecutor {
    /// Cost configuration for computron metering.
    pub costs: ComputronCosts,
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
}

impl TurnExecutor {
    /// Create a new executor with the given cost configuration.
    pub fn new(costs: ComputronCosts) -> Self {
        TurnExecutor {
            costs,
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
        }
    }

    /// Create a new executor with a proof verifier.
    pub fn with_proof_verifier(costs: ComputronCosts, verifier: Box<dyn ProofVerifier>) -> Self {
        TurnExecutor {
            costs,
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

    /// Set the current timestamp (used for expiration and precondition checks).
    pub fn set_timestamp(&mut self, ts: i64) {
        self.current_timestamp = ts;
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
                            cell.state.balance += conditional.deposit_amount;
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
        if agent_cell.state.nonce != turn.nonce {
            return TurnResult::Rejected {
                reason: TurnError::NonceReplay {
                    expected: agent_cell.state.nonce,
                    got: turn.nonce,
                },
                at_action: vec![],
            };
        }

        // Check fee coverage (agent must have enough balance for the fee).
        if agent_cell.state.balance < turn.fee {
            return TurnResult::Rejected {
                reason: TurnError::InsufficientBalance {
                    cell: turn.agent,
                    required: turn.fee,
                    available: agent_cell.state.balance,
                },
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
            agent.state.balance -= turn.fee;
            agent.state.increment_nonce();
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
                proposer.state.balance += proposer_share;
            }
            // If proposer cell doesn't exist in ledger, share is burned.
        }

        if let Some(treasury_id) = &self.treasury_cell {
            if let Some(treasury) = ledger.get_mut(treasury_id) {
                treasury.state.balance += treasury_share;
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

        let receipt = TurnReceipt {
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
            derivation_records: Self::collect_derivation_records(
                &turn.call_forest,
                self.current_timestamp as u64,
            ),
            emitted_events: Self::collect_emitted_events(&journal),
            executor_signature: None,
        };

        TurnResult::Committed {
            ledger_delta: delta,
            receipt,
            computrons_used,
        }
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

        if agent_cell.state.nonce != turn.nonce {
            return Err(TurnError::NonceReplay {
                expected: agent_cell.state.nonce,
                got: turn.nonce,
            });
        }

        if agent_cell.state.balance < turn.fee {
            return Err(TurnError::InsufficientBalance {
                cell: turn.agent,
                required: turn.fee,
                available: agent_cell.state.balance,
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
        if &action.target != parent_cell {
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
                            let delegation_epoch = ancestor.state.delegation_epoch;
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
                        if !c.state.proved_state {
                            journal.record_set_proved_state(*cell_id, c.state.proved_state);
                            c.state.proved_state = true;
                        }
                    }
                }
            }
        } else {
            // Non-proof authorization: if any field was modified, proved_state = false.
            for cell_id in &non_proof_field_cells {
                if let Some(c) = ledger.get_mut(cell_id) {
                    if c.state.proved_state {
                        journal.record_set_proved_state(*cell_id, c.state.proved_state);
                        c.state.proved_state = false;
                    }
                }
            }
        }

        // Apply balance_change (Mina-style excess tracking).
        if let Some(delta) = action.balance_change {
            let target = ledger
                .get(&action.target)
                .ok_or_else(|| (TurnError::CellNotFound { id: action.target }, path.clone()))?;
            let current_balance = target.state.balance;

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
            journal.record_set_balance(action.target, cell_mut.state.balance);
            if delta < 0 {
                cell_mut.state.balance -= delta.unsigned_abs();
            } else {
                cell_mut.state.balance += delta as u64;
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
                Authorization::Breadstuff(token) => self.check_breadstuff(
                    ledger,
                    actor_cell_id,
                    token,
                    action_name,
                    auth_required,
                    path,
                    action.target,
                ),
                _ => Err((
                    TurnError::PermissionDenied {
                        cell: action.target,
                        action: action_name.to_string(),
                        required: AuthRequired::Signature,
                    },
                    path.to_vec(),
                )),
            },
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
                Authorization::Breadstuff(token) => self.check_breadstuff(
                    ledger,
                    actor_cell_id,
                    token,
                    action_name,
                    auth_required,
                    path,
                    action.target,
                ),
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

        let verifying_key = VerifyingKey::from_bytes(&target_cell.public_key).map_err(|_| {
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
    fn check_breadstuff(
        &self,
        ledger: &Ledger,
        actor_cell_id: &CellId,
        token: &[u8; 32],
        action_name: &str,
        auth_required: &AuthRequired,
        path: &[usize],
        target_id: CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let actor_cell = ledger.get(actor_cell_id).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: *actor_cell_id },
                path.to_vec(),
            )
        })?;
        let has_matching = actor_cell
            .capabilities
            .iter()
            .any(|cap| cap.breadstuff.as_ref() == Some(token) && cap.target == target_id);
        if has_matching {
            Ok(())
        } else {
            Err((
                TurnError::PermissionDenied {
                    cell: target_id,
                    action: action_name.to_string(),
                    required: auth_required.clone(),
                },
                path.to_vec(),
            ))
        }
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
                if from_cell.state.balance < *amount {
                    return Err((
                        TurnError::InsufficientBalance {
                            cell: *from,
                            required: *amount,
                            available: from_cell.state.balance,
                        },
                        path.to_vec(),
                    ));
                }
                if ledger.get(to).is_none() {
                    return Err((TurnError::TransferDestNotFound { id: *to }, path.to_vec()));
                }
                let to_balance = ledger.get(to).unwrap().state.balance;
                if to_balance.checked_add(*amount).is_none() {
                    return Err((TurnError::BalanceOverflow { cell: *to }, path.to_vec()));
                }
                // Record old balances, then apply.
                let old_from_balance = ledger.get(from).unwrap().state.balance;
                let old_to_balance = ledger.get(to).unwrap().state.balance;
                journal.record_set_balance(*from, old_from_balance);
                journal.record_set_balance(*to, old_to_balance);
                ledger.get_mut(from).unwrap().state.balance -= *amount;
                ledger.get_mut(to).unwrap().state.balance += *amount;
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
                journal.record_set_nonce(*cell, c.state.nonce);
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
                let id = new_cell.id;
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
                if obligor_cell.state.balance < *stake_amount {
                    return Err((
                        TurnError::InsufficientBalance {
                            cell: *action_target,
                            required: *stake_amount,
                            available: obligor_cell.state.balance,
                        },
                        path.to_vec(),
                    ));
                }
                let old_balance = obligor_cell.state.balance;
                journal.record_set_balance(*action_target, old_balance);
                ledger.get_mut(action_target).unwrap().state.balance -= *stake_amount;

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
                let old_balance = obligor_cell.state.balance;
                journal.record_set_balance(record.obligor, old_balance);
                ledger.get_mut(&record.obligor).unwrap().state.balance += record.stake_amount;
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
                let old_ben_balance = beneficiary_cell.state.balance;
                journal.record_set_balance(record.beneficiary, old_ben_balance);
                ledger.get_mut(&record.beneficiary).unwrap().state.balance += record.stake_amount;
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
                if creator_cell.state.balance < *amount {
                    return Err((
                        TurnError::InsufficientBalance {
                            cell: *cell,
                            required: *amount,
                            available: creator_cell.state.balance,
                        },
                        path.to_vec(),
                    ));
                }
                // Lock the funds: subtract from creator.
                let old_balance = creator_cell.state.balance;
                journal.record_set_balance(*cell, old_balance);
                ledger.get_mut(cell).unwrap().state.balance -= *amount;

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
                let old_recipient_balance = recipient_cell.state.balance;
                journal.record_set_balance(record.recipient, old_recipient_balance);
                ledger.get_mut(&record.recipient).unwrap().state.balance += record.amount;
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
                let old_creator_balance = creator_cell.state.balance;
                journal.record_set_balance(record.creator, old_creator_balance);
                ledger.get_mut(&record.creator).unwrap().state.balance += record.amount;
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
                if creator_cell.state.balance < *amount {
                    return Err((
                        TurnError::InsufficientBalance {
                            cell: *action_target,
                            required: *amount,
                            available: creator_cell.state.balance,
                        },
                        path.to_vec(),
                    ));
                }
                let old_balance = creator_cell.state.balance;
                journal.record_set_balance(*action_target, old_balance);
                ledger.get_mut(action_target).unwrap().state.balance -= *amount;

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
                // Verify the claim_auth against the recipient_commitment.
                if !verify_escrow_claim(claim_auth, &record.recipient_commitment, escrow_id) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow release: claim authorization failed".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the recipient cell exists and matches the claim.
                if ledger.get(recipient).is_none() {
                    return Err((
                        TurnError::CellNotFound { id: *recipient },
                        path.to_vec(),
                    ));
                }
                // Verify that the claimed recipient CellId matches the public_key in claim_auth.
                let expected_recipient = CellId::from_bytes(claim_auth.public_key);
                if *recipient != expected_recipient {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow release: recipient does not match claim key"
                                .into(),
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
                let old_balance = recipient_cell.state.balance;
                journal.record_set_balance(*recipient, old_balance);
                ledger.get_mut(recipient).unwrap().state.balance += amount;
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
                            reason: "committed escrow timeout has not passed, cannot refund"
                                .into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the claim_auth against the creator_commitment.
                if !verify_escrow_claim(claim_auth, &record.creator_commitment, escrow_id) {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow refund: claim authorization failed".into(),
                        },
                        path.to_vec(),
                    ));
                }
                // Verify the creator cell exists and matches the claim.
                if ledger.get(creator).is_none() {
                    return Err((
                        TurnError::CellNotFound { id: *creator },
                        path.to_vec(),
                    ));
                }
                let expected_creator = CellId::from_bytes(claim_auth.public_key);
                if *creator != expected_creator {
                    return Err((
                        TurnError::InvalidEffect {
                            reason: "committed escrow refund: creator does not match claim key"
                                .into(),
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
                let old_balance = creator_cell.state.balance;
                journal.record_set_balance(*creator, old_balance);
                ledger.get_mut(creator).unwrap().state.balance += amount;
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
                let delegation_epoch = parent_cell_data.state.delegation_epoch;
                let now = self.current_timestamp as u64;
                let snapshot: Vec<pyana_cell::CapabilityRef> =
                    parent_cell_data.capabilities.iter().cloned().collect();

                let child_id = CellId::derive_raw(child_public_key, child_token_id);
                let mut child_cell = Cell::with_balance(*child_public_key, *child_token_id, 0);
                child_cell.id = child_id;
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
                let new_epoch = parent_cell_data.state.delegation_epoch;
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
                let old_epoch = parent_mut.state.delegation_epoch;
                journal.record_set_delegation_epoch(*action_target, old_epoch);
                parent_mut.state.bump_delegation_epoch();

                let child_mut = ledger.get_mut(child).unwrap();
                journal.record_set_delegation(*child, old_child_delegation);
                child_mut.delegation = None;
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
            hasher.update(&cell.public_key);
            hasher.update(&cell.token_id);
            hasher.update(&cell.state.nonce.to_le_bytes());
            hasher.update(&cell.state.balance.to_le_bytes());
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
                let vc = ValueCommitment::from_bytes(&ValueCommitmentBytes(*vc_bytes))
                    .ok_or_else(|| TurnError::CommittedConservationFailed {
                        reason: "NoteSpend value_commitment is not a valid Ristretto point".into(),
                    })?;
                inputs.push(vc);
            }
            Effect::NoteCreate {
                value_commitment: Some(vc_bytes),
                ..
            } => {
                let vc = ValueCommitment::from_bytes(&ValueCommitmentBytes(*vc_bytes))
                    .ok_or_else(|| TurnError::CommittedConservationFailed {
                        reason: "NoteCreate value_commitment is not a valid Ristretto point".into(),
                    })?;
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
    fn verify_output_range_proofs(
        forest: &crate::forest::CallForest,
    ) -> Result<(), TurnError> {
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
                value_commitment: Some(_),
                range_proof,
                ..
            } => {
                let rp = range_proof.as_ref().ok_or_else(|| {
                    TurnError::CommittedConservationFailed {
                        reason: "NoteCreate has value_commitment but no range_proof".into(),
                    }
                })?;
                if rp.is_empty() {
                    return Err(TurnError::CommittedConservationFailed {
                        reason: "NoteCreate range_proof is empty".into(),
                    });
                }
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
                | JournalEntry::BridgedNullifierInserted { .. } => {}
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
                let diff = c.state.balance as i128 - *old_balance as i128;
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
                if c.state.nonce > *old_nonce {
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

use crate::eventual::{
    EventualRef, Pipeline, PipelineError, PipelineResult, TurnOutput,
};

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
            | Effect::RefundCommittedEscrow { .. } => {}
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
        let resolved_turn = match resolve_turn(turn, &resolution_table) {
            Ok(t) => t,
            Err(e) => {
                failed[idx] = true;
                results[idx] = Some(Err(e));
                continue;
            }
        };

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
        let resolved_turn = match resolve_turn(turn, &resolution_table) {
            Ok(t) => t,
            Err(e) => {
                failed[idx] = true;
                results[idx] = Some(Err(e));
                continue;
            }
        };
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
