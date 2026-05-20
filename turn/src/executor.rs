//! TurnExecutor: applies a turn to a ledger with full atomicity.
//!
//! The executor walks the call forest depth-first, checking preconditions,
//! verifying authorization, applying effects, and metering computrons at each step.
//! If any action fails, ALL effects are rolled back via journal replay (atomicity guarantee).

use ed25519_dalek::{Signature, VerifyingKey};
use pyana_cell::{
    AuthRequired, Cell, CellId, CellStateDelta, Ledger, LedgerDelta,
    Preconditions,
    preconditions::EvalContext,
    state::STATE_SLOTS,
};
use serde::{Deserialize, Serialize};

use crate::action::{Action, Authorization, DelegationMode, Effect};
use crate::error::TurnError;
use crate::forest::CallTree;
use crate::journal::{JournalEntry, LedgerJournal};
use crate::turn::{Turn, TurnReceipt, TurnResult};

/// Trait for verifying ZK proofs. Implementations provide circuit-specific verification.
///
/// The executor is fail-closed: if no ProofVerifier is configured and a cell requires
/// proof authorization, the action is rejected.
pub trait ProofVerifier: Send + Sync {
    /// Verify a proof against public inputs and a verification key.
    ///
    /// Returns true if the proof is valid for the given public inputs and verification key.
    fn verify(&self, proof: &[u8], public_inputs: &[u8], vk: &[u8]) -> bool;
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
}

impl TurnExecutor {
    /// Create a new executor with the given cost configuration.
    pub fn new(costs: ComputronCosts) -> Self {
        TurnExecutor {
            costs,
            current_timestamp: 0,
            block_height: 0,
            proof_verifier: None,
        }
    }

    /// Create a new executor with a proof verifier.
    pub fn with_proof_verifier(costs: ComputronCosts, verifier: Box<dyn ProofVerifier>) -> Self {
        TurnExecutor {
            costs,
            current_timestamp: 0,
            block_height: 0,
            proof_verifier: Some(verifier),
        }
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
                DelegationMode::ParentsOwn, // top-level: agent owns all its capabilities
                &mut computrons_used,
                turn.fee,
                &mut all_effects_hashes,
                vec![root_idx],
                &mut journal,
                &mut excess,
            );

            if let Err((error, path)) = result {
                // Rollback: replay journal in reverse to restore ledger.
                journal.rollback(ledger);
                return TurnResult::Rejected {
                    reason: error,
                    at_action: path,
                };
            }
        }

        // Check total cost against fee.
        if computrons_used > turn.fee {
            journal.rollback(ledger);
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
            journal.rollback(ledger);
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
            journal.rollback(ledger);
            return TurnResult::Rejected {
                reason: TurnError::ExcessNotZero { excess },
                at_action: vec![],
            };
        }

        // Phase 4: Compute receipt.
        let post_state_hash = ledger.root();
        let effects_hash = self.compute_effects_hash(&all_effects_hashes);

        // Compute turn hash (we need a mutable clone for hashing).
        let mut turn_clone = turn.clone();
        let turn_hash = turn_clone.hash();
        let forest_hash = turn_clone.call_forest.forest_hash;

        // Build ledger delta from the journal and Phase 1 (fee + nonce) commitment.
        let delta = Self::compute_delta_from_journal_with_fee(&journal, ledger, &turn.agent, turn.fee);

        let receipt = TurnReceipt {
            turn_hash,
            forest_hash,
            pre_state_hash,
            post_state_hash,
            timestamp: self.current_timestamp,
            effects_hash,
            computrons_used,
            action_count: turn.call_forest.action_count(),
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

        let agent_cell = ledger.get(&turn.agent).ok_or(TurnError::CellNotFound { id: turn.agent })?;

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
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let action = &tree.action;

        // Meter the action base cost.
        *computrons_used = computrons_used.saturating_add(self.costs.action_base);
        if *computrons_used > budget {
            return Err((
                TurnError::BudgetExceeded { limit: budget, used: *computrons_used },
                path,
            ));
        }

        // Check target cell exists.
        let target_cell = ledger.get(&action.target).ok_or_else(|| {
            (TurnError::CellNotFound { id: action.target }, path.clone())
        })?;

        // Check capability: does the parent have access to the target?
        // The agent (top-level parent) implicitly has access to itself.
        // For other cells, the parent must hold a capability.
        if &action.target != parent_cell {
            let parent = ledger.get(parent_cell).ok_or_else(|| {
                (TurnError::CellNotFound { id: *parent_cell }, path.clone())
            })?;

            let has_capability = parent.capabilities.has_access(&action.target);

            // Check delegation mode: if parent_delegation is None, child actions cannot
            // use the parent's capabilities to reach non-parent cells.
            if !has_capability {
                // Check if delegation allows reaching this target.
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
                        // Still need the capability to be held by someone in the chain.
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

        // Check preconditions.
        self.check_preconditions(&action.preconditions, target_cell, &path)?;

        // Verify authorization (including signature/proof verification).
        self.verify_authorization(action, target_cell, ledger, &path)?;

        // Meter authorization cost.
        let auth_cost = match &action.authorization {
            Authorization::Signature(_, _) => self.costs.signature_verify,
            Authorization::Proof(_) => self.costs.proof_verify,
            Authorization::Breadstuff(_) => self.costs.signature_verify / 2, // cheaper
            Authorization::None => 0,
        };
        *computrons_used = computrons_used.saturating_add(auth_cost);
        if *computrons_used > budget {
            return Err((
                TurnError::BudgetExceeded { limit: budget, used: *computrons_used },
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
        let (regular_effects, permission_effects): (Vec<&Effect>, Vec<&Effect>) =
            action.effects.iter().partition(|e| !e.is_permission_effect());

        // Apply effects, tracking which cells have fields set (for proved_state).
        let is_proof_auth = matches!(&action.authorization, Authorization::Proof(_));
        let mut proof_field_sets: std::collections::HashMap<CellId, std::collections::HashSet<usize>> =
            std::collections::HashMap::new();
        let mut non_proof_field_cells: std::collections::HashSet<CellId> =
            std::collections::HashSet::new();

        // Apply regular effects first.
        for effect in &regular_effects {
            let effect_cost = self.compute_effect_cost(effect);
            *computrons_used = computrons_used.saturating_add(effect_cost);
            if *computrons_used > budget {
                return Err((
                    TurnError::BudgetExceeded { limit: budget, used: *computrons_used },
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
                    TurnError::BudgetExceeded { limit: budget, used: *computrons_used },
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
            let target = ledger.get(&action.target).ok_or_else(|| {
                (TurnError::CellNotFound { id: action.target }, path.clone())
            })?;
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
                        TurnError::BalanceOverflow { cell: action.target },
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
            *excess = excess.saturating_sub(delta);
        }

        // Enforce cell program constraints on the post-transition state.
        if let Some(target_cell) = ledger.get(&action.target) {
            if !target_cell.program.is_none() {
                // For Circuit programs, the action must carry a proof (already verified above).
                // For Predicate programs, evaluate constraints against new state.
                if !target_cell.program.requires_proof() {
                    let result = target_cell.program.evaluate(
                        &target_cell.state,
                        old_target_state.as_ref(),
                    );
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
        let child_delegation = match action.may_delegate {
            DelegationMode::None => DelegationMode::None,
            DelegationMode::ParentsOwn => DelegationMode::ParentsOwn,
            DelegationMode::Inherit => parent_delegation,
        };

        for (child_idx, child) in tree.children.iter().enumerate() {
            // Check delegation permission.
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

        preconditions.evaluate(&target_cell.state, &ctx).map_err(|e| {
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
    /// This checks ALL required permissions for ALL effects in the action (not just the first).
    /// For signature auth: verifies the Ed25519 signature against the cell's public key.
    /// For proof auth: delegates to the configured ProofVerifier (fail-closed if none set).
    fn verify_authorization(
        &self,
        action: &Action,
        target_cell: &Cell,
        ledger: &Ledger,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Determine ALL required permissions for this action's effects.
        let required_actions = self.determine_required_permissions(action);

        // Find the most restrictive auth requirement across all permissions.
        let mut most_restrictive = &AuthRequired::None;
        let mut most_restrictive_action_name = "Access";

        for (perm_action, action_name) in &required_actions {
            let auth_req = target_cell.permissions.for_action(*perm_action);
            if auth_req.is_narrower_or_equal(most_restrictive) {
                most_restrictive = auth_req;
                most_restrictive_action_name = action_name;
            }
        }

        // If no effects produced any specific permission, check general access.
        if required_actions.is_empty() {
            most_restrictive = target_cell.permissions.for_action(pyana_cell::permissions::Action::Access);
            most_restrictive_action_name = "Access";
        }

        // Now verify the authorization against the most restrictive requirement.
        self.check_single_auth_requirement(
            action,
            target_cell,
            most_restrictive,
            most_restrictive_action_name,
            path,
        )?;

        // Additionally, check Receive permission on transfer destinations.
        for effect in &action.effects {
            if let Effect::Transfer { to, .. } = effect {
                if let Some(dest_cell) = ledger.get(to) {
                    let receive_req = dest_cell.permissions.for_action(pyana_cell::permissions::Action::Receive);
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
        auth_required: &AuthRequired,
        action_name: &str,
        path: &[usize],
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
                    self.verify_ed25519_signature(action, target_cell, r, s, path)
                }
                Authorization::Breadstuff(token) => {
                    self.check_breadstuff(target_cell, token, action_name, auth_required, path, action.target)
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
            AuthRequired::Proof => match &action.authorization {
                Authorization::Proof(proof_bytes) => {
                    self.verify_zk_proof(action, target_cell, proof_bytes, path)
                }
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
                    self.verify_ed25519_signature(action, target_cell, r, s, path)
                }
                Authorization::Proof(proof_bytes) => {
                    self.verify_zk_proof(action, target_cell, proof_bytes, path)
                }
                Authorization::Breadstuff(token) => {
                    self.check_breadstuff(target_cell, token, action_name, auth_required, path, action.target)
                }
                Authorization::None => Err((
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
    fn verify_ed25519_signature(
        &self,
        action: &Action,
        target_cell: &Cell,
        r: &[u8; 32],
        s: &[u8; 32],
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let message = Self::compute_signing_message(action);

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

        use ed25519_dalek::Verifier;
        verifying_key.verify(&message, &signature).map_err(|_| {
            (
                TurnError::InvalidAuthorization {
                    reason: "Ed25519 signature verification failed".to_string(),
                },
                path.to_vec(),
            )
        })
    }

    /// Verify a ZK proof against the target cell's verification key.
    fn verify_zk_proof(
        &self,
        action: &Action,
        target_cell: &Cell,
        proof_bytes: &[u8],
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

        let public_inputs = Self::compute_signing_message(action);

        if verifier.verify(proof_bytes, &public_inputs, &vk.data) {
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
    fn check_breadstuff(
        &self,
        target_cell: &Cell,
        token: &[u8; 32],
        action_name: &str,
        auth_required: &AuthRequired,
        path: &[usize],
        target_id: CellId,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let has_matching = target_cell.capabilities.iter().any(|cap| {
            cap.breadstuff.as_ref() == Some(token)
        });
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
    /// [`compute_partial_signing_message`] which includes position and forest root.
    pub fn compute_signing_message(action: &Action) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(action.target.as_bytes());
        hasher.update(&action.method);
        for arg in &action.args {
            hasher.update(arg);
        }
        for effect in &action.effects {
            hasher.update(&effect.hash());
        }
        hasher.update(&[action.may_delegate as u8]);
        *hasher.finalize().as_bytes()
    }

    /// Compute the signing message for an action in partial commitment mode.
    ///
    /// The signer commits to:
    /// - The action's own content hash (what they are doing)
    /// - Their position index in the forest (where they are)
    /// - The forest root hash (binding to the overall structure)
    ///
    /// This allows a party to sign their part without knowing about other actions,
    /// enabling multi-party composition (DEX fills, atomic swaps, etc.)
    pub fn compute_partial_signing_message(
        action: &Action,
        position: usize,
        forest_root_hash: &[u8; 32],
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(&action.hash());
        hasher.update(&(position as u64).to_le_bytes());
        hasher.update(forest_root_hash);
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
                    result.push((pyana_cell::permissions::Action::IncrementNonce, "IncrementNonce"));
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
                    result.push((pyana_cell::permissions::Action::SetPermissions, "SetPermissions"));
                }
                Effect::SetVerificationKey { .. } => {
                    result.push((pyana_cell::permissions::Action::SetVerificationKey, "SetVerificationKey"));
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
                        TurnError::InvalidFieldIndex { cell: *cell, index: *index },
                        path.to_vec(),
                    ));
                }
                if cell != action_target {
                    self.check_cross_cell_permission(
                        ledger, actor, cell,
                        pyana_cell::permissions::Action::SetState, "SetState", path,
                    )?;
                }
                let c = ledger.get_mut(cell).ok_or_else(|| {
                    (TurnError::CellNotFound { id: *cell }, path.to_vec())
                })?;
                journal.record_set_field(*cell, *index, c.state.fields[*index]);
                c.state.fields[*index] = *value;
                Ok(())
            }

            Effect::Transfer { from, to, amount } => {
                if from != action_target {
                    self.check_cross_cell_permission(
                        ledger, actor, from,
                        pyana_cell::permissions::Action::Send, "Send", path,
                    )?;
                }
                let from_cell = ledger.get(from).ok_or_else(|| {
                    (TurnError::CellNotFound { id: *from }, path.to_vec())
                })?;
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
                    return Err((
                        TurnError::TransferDestNotFound { id: *to },
                        path.to_vec(),
                    ));
                }
                let to_balance = ledger.get(to).unwrap().state.balance;
                if to_balance.checked_add(*amount).is_none() {
                    return Err((
                        TurnError::BalanceOverflow { cell: *to },
                        path.to_vec(),
                    ));
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
                        ledger, actor, from,
                        pyana_cell::permissions::Action::Delegate, "Delegate", path,
                    )?;
                }

                let from_cell = ledger.get(from).ok_or_else(|| {
                    (TurnError::CellNotFound { id: *from }, path.to_vec())
                })?;

                let held_cap = from_cell.capabilities.lookup_by_target(&cap.target)
                    .ok_or_else(|| {
                        (TurnError::CapabilityNotHeld { actor: *from, target: cap.target }, path.to_vec())
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

                let to_cell = ledger.get_mut(to).ok_or_else(|| {
                    (TurnError::CellNotFound { id: *to }, path.to_vec())
                })?;
                let granted_slot = to_cell.capabilities.grant_with_breadstuff(
                    cap.target,
                    cap.permissions.clone(),
                    cap.breadstuff,
                );
                journal.record_grant_capability(*to, granted_slot);
                Ok(())
            }

            Effect::RevokeCapability { cell, slot } => {
                if cell != action_target {
                    self.check_cross_cell_permission(
                        ledger, actor, cell,
                        pyana_cell::permissions::Action::Delegate, "Delegate", path,
                    )?;
                }
                let c = ledger.get_mut(cell).ok_or_else(|| {
                    (TurnError::CellNotFound { id: *cell }, path.to_vec())
                })?;
                if let Some(old_cap) = c.capabilities.lookup(*slot).cloned() {
                    journal.record_revoke_capability(*cell, old_cap);
                }
                c.capabilities.revoke(*slot);
                Ok(())
            }

            Effect::EmitEvent { cell, .. } => {
                if ledger.get(cell).is_none() {
                    return Err((
                        TurnError::CellNotFound { id: *cell },
                        path.to_vec(),
                    ));
                }
                Ok(())
            }

            Effect::IncrementNonce { cell } => {
                if cell != action_target {
                    self.check_cross_cell_permission(
                        ledger, actor, cell,
                        pyana_cell::permissions::Action::IncrementNonce, "IncrementNonce", path,
                    )?;
                }
                let c = ledger.get_mut(cell).ok_or_else(|| {
                    (TurnError::CellNotFound { id: *cell }, path.to_vec())
                })?;
                journal.record_set_nonce(*cell, c.state.nonce);
                c.state.increment_nonce();
                Ok(())
            }

            Effect::CreateCell { public_key, token_id, balance } => {
                let new_cell = Cell::with_balance(*public_key, *token_id, *balance);
                let id = new_cell.id;
                ledger.insert_cell(new_cell).map_err(|_| {
                    (TurnError::CellAlreadyExists { id }, path.to_vec())
                })?;
                journal.record_create_cell(id);
                Ok(())
            }

            Effect::SetPermissions { cell, new_permissions } => {
                if cell != action_target {
                    self.check_cross_cell_permission(
                        ledger, actor, cell,
                        pyana_cell::permissions::Action::SetPermissions, "SetPermissions", path,
                    )?;
                }
                let c = ledger.get_mut(cell).ok_or_else(|| {
                    (TurnError::CellNotFound { id: *cell }, path.to_vec())
                })?;
                journal.record_set_permissions(*cell, c.permissions.clone());
                c.permissions = new_permissions.clone();
                Ok(())
            }

            Effect::SetVerificationKey { cell, new_vk } => {
                if cell != action_target {
                    self.check_cross_cell_permission(
                        ledger, actor, cell,
                        pyana_cell::permissions::Action::SetVerificationKey, "SetVerificationKey", path,
                    )?;
                }
                let c = ledger.get_mut(cell).ok_or_else(|| {
                    (TurnError::CellNotFound { id: *cell }, path.to_vec())
                })?;
                journal.record_set_verification_key(*cell, c.verification_key.clone());
                c.verification_key = new_vk.clone();
                Ok(())
            }

            // Note effects are recorded for conservation checking but do not
            // modify the cell ledger directly. The note tree and nullifier set
            // are updated by the note layer above the executor.
            Effect::NoteSpend { .. } => Ok(()),
            Effect::NoteCreate { .. } => Ok(()),
        }
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
            let actor_cell = ledger.get(actor).ok_or_else(|| {
                (TurnError::CellNotFound { id: *actor }, path.to_vec())
            })?;
            if !actor_cell.capabilities.has_access(target_cell_id) {
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
            (TurnError::CellNotFound { id: *target_cell_id }, path.to_vec())
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
            Effect::EmitEvent { event, .. } => {
                (event.data.len() as u64) * self.costs.per_byte * 32
            }
            Effect::IncrementNonce { .. } => 0,
            Effect::SetPermissions { .. } => self.costs.effect_base,
            Effect::SetVerificationKey { .. } => self.costs.effect_base,
            Effect::NoteSpend { .. } => self.costs.proof_verify, // note spends carry a proof
            Effect::NoteCreate { .. } => self.costs.effect_base,
        };
        base.saturating_add(extra).saturating_add(
            (effect.data_bytes() as u64).saturating_mul(self.costs.per_byte),
        )
    }

    /// Estimate the cost of a tree (without actually applying it).
    fn estimate_tree_cost(&self, tree: &CallTree) -> u64 {
        let mut total = self.costs.action_base;

        total = total.saturating_add(match &tree.action.authorization {
            Authorization::Signature(_, _) => self.costs.signature_verify,
            Authorization::Proof(_) => self.costs.proof_verify,
            Authorization::Breadstuff(_) => self.costs.signature_verify / 2,
            Authorization::None => 0,
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
    /// For each asset type that appears in NoteSpend/NoteCreate effects,
    /// the total value spent must equal the total value created.
    /// Returns Ok(()) if conservation holds, or Err((asset_type, inputs, outputs)).
    fn check_note_conservation(&self, turn: &Turn) -> Result<(), (u64, u64, u64)> {
        let mut inputs: std::collections::HashMap<u64, u64> = std::collections::HashMap::new();
        let mut outputs: std::collections::HashMap<u64, u64> = std::collections::HashMap::new();

        self.collect_note_effects(&turn.call_forest, &mut inputs, &mut outputs);

        // Check conservation for each asset type.
        let all_asset_types: std::collections::HashSet<u64> = inputs.keys()
            .chain(outputs.keys())
            .copied()
            .collect();

        for asset_type in all_asset_types {
            let input_total = inputs.get(&asset_type).copied().unwrap_or(0);
            let output_total = outputs.get(&asset_type).copied().unwrap_or(0);
            if input_total != output_total {
                return Err((asset_type, input_total, output_total));
            }
        }

        Ok(())
    }

    /// Recursively collect NoteSpend/NoteCreate effects from the call forest.
    fn collect_note_effects(
        &self,
        forest: &crate::forest::CallForest,
        inputs: &mut std::collections::HashMap<u64, u64>,
        outputs: &mut std::collections::HashMap<u64, u64>,
    ) {
        for tree in &forest.roots {
            self.collect_note_effects_tree(tree, inputs, outputs);
        }
    }

    /// Recursively collect note effects from a single tree.
    fn collect_note_effects_tree(
        &self,
        tree: &CallTree,
        inputs: &mut std::collections::HashMap<u64, u64>,
        outputs: &mut std::collections::HashMap<u64, u64>,
    ) {
        for effect in &tree.action.effects {
            match effect {
                Effect::NoteSpend { value, asset_type, .. } => {
                    *inputs.entry(*asset_type).or_insert(0) += value;
                }
                Effect::NoteCreate { value, asset_type, .. } => {
                    *outputs.entry(*asset_type).or_insert(0) += value;
                }
                _ => {}
            }
        }
        for child in &tree.children {
            self.collect_note_effects_tree(child, inputs, outputs);
        }
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
                JournalEntry::SetField { cell, index, old_value } => {
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
                                let e = updated_cells.entry(*cell).or_insert_with(CellStateDelta::empty);
                                e.capability_grants.push(cap_ref.clone());
                            }
                        }
                    }
                }
                JournalEntry::RevokeCapability { cell, old_cap } => {
                    if !created_cells.contains(cell) {
                        let e = updated_cells.entry(*cell).or_insert_with(CellStateDelta::empty);
                        e.capability_revocations.push(old_cap.slot);
                    }
                }
                JournalEntry::SetProvedState { .. } => {
                    // proved_state changes are tracked implicitly through the cell's state;
                    // no separate delta field needed for now.
                }
                JournalEntry::SetPermissions { cell, .. } => {
                    if !created_cells.contains(cell) {
                        let e = updated_cells.entry(*cell).or_insert_with(CellStateDelta::empty);
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
            }
        }

        // Compute field/balance/nonce deltas from first-old vs current.
        for ((cell_id, index), old_value) in &first_fields {
            if let Some(c) = ledger.get(cell_id) {
                let new_value = c.state.fields[*index];
                if new_value != *old_value {
                    let e = updated_cells.entry(*cell_id).or_insert_with(CellStateDelta::empty);
                    e.field_updates.push((*index, new_value));
                }
            }
        }

        for (cell_id, old_balance) in &first_balance {
            if let Some(c) = ledger.get(cell_id) {
                let diff = c.state.balance as i128 - *old_balance as i128;
                if diff != 0 {
                    let e = updated_cells.entry(*cell_id).or_insert_with(CellStateDelta::empty);
                    e.balance_change = diff as i64;
                }
            }
        }

        for (cell_id, old_nonce) in &first_nonce {
            if let Some(c) = ledger.get(cell_id) {
                if c.state.nonce > *old_nonce {
                    let e = updated_cells.entry(*cell_id).or_insert_with(CellStateDelta::empty);
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

    /// Compute a LedgerDelta including the Phase 1 fee + nonce commitment.
    ///
    /// Since Phase 1 (fee/nonce) is committed outside the journal, we need to
    /// account for it separately in the delta. The agent's balance decreased by
    /// `fee` and nonce incremented by 1 in addition to any journal-recorded changes.
    fn compute_delta_from_journal_with_fee(
        journal: &LedgerJournal,
        ledger: &Ledger,
        agent: &CellId,
        fee: u64,
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

        delta
    }
}
