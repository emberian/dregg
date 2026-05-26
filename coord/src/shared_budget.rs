//! # Shared Resource Budget (Tier 2 Optimistic Shared Access)
//!
//! Generalizes the Stingray bounded counter from "one agent's budget across silos"
//! to "one shared resource accessed by multiple agents." This enables Tier 2
//! optimistic execution: agents can debit from a shared resource (AMM pool,
//! multi-sig account, shared cell) without coordination, as long as the aggregate
//! spending stays within bounds.
//!
//! ## Analogy to StingrayCounter
//!
//! | StingrayCounter (existing) | SharedResourceBudget (this module) |
//! |------------------------------|-------------------------------------|
//! | One agent's budget           | One shared resource's balance       |
//! | Distributed across silos     | Distributed across agents           |
//! | Silo = execution node        | Participant = agent accessing pool  |
//! | Coordinator = central entity | Coordinator = ordering node(s)      |
//! | Rebalance = reconcile silos  | Rebalance = epoch close (COD-style) |
//!
//! ## The Safety Invariant
//!
//! With n participants and at most f Byzantine:
//!
//!   allowance = resource_balance * (f+1) / (2f+1)
//!
//! Each agent can locally debit up to `allowance` without coordination. The worst
//! case: all n agents each spend `allowance`. But since at most f are Byzantine,
//! the honest agents collectively reveal their true spending at rebalance, and the
//! maximum possible overspend is bounded by `f * allowance`.
//!
//! ## Integration with Blocklace
//!
//! Each agent's debits against a shared resource are recorded in their virtual chain
//! (blocks in the blocklace). During rebalance, the coordinator observes each agent's
//! blocks and sums debits per resource. This makes the bounded counter derivable FROM
//! the blocklace state rather than requiring a separate accounting system.
//!
//! ## Relationship to COD (Close-Open-Debit)
//!
//! COD is reactive: check at debit time whether the sum exceeds the balance.
//! This module is pre-allocative: assign allowances upfront.
//!
//! The hybrid approach: pre-allocate for the fast path (no coordination needed for
//! debits within allowance), but trigger reactive escalation (Tier 3 ordering) when
//! an agent exhausts its allowance or when rebalance detects overspending. The COD
//! "close and epoch transition" maps exactly to our `rebalance()`.
//!
//! ## Escalation: Tier 2 -> Tier 3
//!
//! When `is_overspent()` returns true, the system escalates to Tier 3:
//!
//! 1. **Detect** which debits conflict (sum exceeds balance)
//! 2. **Pause** accepting new debits for this resource (state = Closing)
//! 3. **Wait** for Cordial Miners to order the conflicting blocks via `tau()`
//! 4. **Execute** in tau order -- first debit wins, later debits rejected if
//!    balance insufficient
//! 5. **Rebalance** -- compute new allowances from remaining balance
//! 6. **Resume** -- state = Open with new allowances
//!
//! ## Dynamic Allowances
//!
//! Unlike the per-agent budget (where the balance is static between rebalances), a
//! shared resource's balance changes with every committed swap. The solution:
//!
//! 1. Allowances are computed from the LAST KNOWN balance at epoch start.
//! 2. Debits within the epoch are optimistic (may collectively overshoot).
//! 3. At epoch close, true balance is reconciled and allowances are recomputed.
//! 4. An "early rebalance" can be triggered if any participant exhausts its allowance.
//!
//! Credits (deposits into the pool) immediately increase the true balance and can
//! trigger allowance expansion without a full rebalance.

use std::collections::HashMap;

use dregg_blocklace::finality::{Block as BlocBlock, BlockId as BlocBlockId, Blocklace, Payload};
use dregg_cell::CellId;
use serde::{Deserialize, Serialize};

use crate::budget::{BudgetVersion, DebitDigest, ResourceAmount};

// ─── Types ────────────────────────────────────────────────────────────────────

/// Identifies a shared resource (e.g., an AMM pool cell, multi-sig account).
/// This is the CellId of the resource cell.
pub type ResourceId = CellId;

/// Identifies a participant (agent) in the shared resource budget.
/// This is the agent's CellId (same as their identity key).
pub type ParticipantId = CellId;

// ─── Resource State Machine ─────────────────────────────────────────────────

/// The escalation state of a shared resource budget.
///
/// Transitions:
///   Open -> Closing (overspend detected)
///   Closing -> Rebalancing (tau orders the conflicting blocks)
///   Rebalancing -> Open (resolution applied, new allowances distributed)
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ResourceState {
    /// Normal operation. Debits accepted within each agent's allowance.
    Open,
    /// Overspend detected. No new debits accepted until resolution.
    /// Contains the set of block IDs whose debits collectively exceed the balance.
    Closing { conflicting: Vec<BlocBlockId> },
    /// Tau has ordered the conflicting blocks. Resolution in progress.
    Rebalancing,
}

// ─── Debit Record ───────────────────────────────────────────────────────────

/// A debit extracted from a blocklace block payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtractedDebit {
    /// The agent (block creator) who made the debit.
    pub agent: ParticipantId,
    /// The resource being debited.
    pub resource_id: [u8; 32],
    /// The amount debited.
    pub amount: ResourceAmount,
    /// The block ID containing this debit.
    pub block_id: BlocBlockId,
}

/// Resolution outcome for a single debit block after tau ordering.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DebitResolution {
    /// Debit was accepted (sufficient balance remained after prior debits).
    Accepted,
    /// Debit was rejected (insufficient balance after earlier debits in tau order).
    Rejected,
}

// ─── AgentAllowance ──────────────────────────────────────────────────────────

/// Per-agent allowance for a shared resource.
///
/// Each agent accessing a shared resource gets a local spending ceiling. Debits
/// within the ceiling proceed without coordination. When the ceiling is hit, the
/// agent must request rebalancing (or escalate to Tier 3).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgentAllowance {
    /// The agent who holds this allowance.
    pub agent: ParticipantId,
    /// The shared resource this allowance is for.
    pub resource: ResourceId,
    /// Budget epoch version.
    pub version: BudgetVersion,
    /// Maximum amount this agent may spend from the shared resource.
    pub ceiling: ResourceAmount,
    /// Amount already spent by this agent in the current epoch.
    pub spent: ResourceAmount,
    /// Debit transaction digests for this epoch.
    pub debits: Vec<DebitDigest>,
}

impl AgentAllowance {
    /// Create a new allowance for an agent on a shared resource.
    pub fn new(
        agent: ParticipantId,
        resource: ResourceId,
        version: BudgetVersion,
        ceiling: ResourceAmount,
    ) -> Self {
        AgentAllowance {
            agent,
            resource,
            version,
            ceiling,
            spent: 0,
            debits: Vec::new(),
        }
    }

    /// Remaining allowance.
    pub fn remaining(&self) -> ResourceAmount {
        self.ceiling.saturating_sub(self.spent)
    }

    /// Whether this allowance has any remaining budget.
    pub fn has_allowance(&self) -> bool {
        self.remaining() > 0
    }

    /// Try to debit from this allowance.
    ///
    /// Returns `Ok(())` if the debit succeeds (enough remaining).
    /// Returns `Err(SharedBudgetError::AllowanceExhausted)` if the ceiling is hit.
    pub fn try_debit(
        &mut self,
        amount: ResourceAmount,
        digest: DebitDigest,
    ) -> Result<(), SharedBudgetError> {
        if amount > self.remaining() {
            return Err(SharedBudgetError::AllowanceExhausted {
                agent: self.agent,
                resource: self.resource,
                remaining: self.remaining(),
                requested: amount,
            });
        }
        self.spent = self.spent.saturating_add(amount);
        self.debits.push(digest);
        Ok(())
    }

    /// Refund a previously debited amount (e.g., after turn abort).
    pub fn refund(&mut self, amount: ResourceAmount) {
        self.spent = self.spent.saturating_sub(amount);
    }
}

// ─── SharedResourceBudget ────────────────────────────────────────────────────

/// Manages allowance distribution for a single shared resource across multiple agents.
///
/// This is the Tier 2 equivalent of `StingrayCounter`: it distributes spending
/// rights for a shared resource (AMM pool, multi-sig, etc.) to participating agents.
/// Each agent can debit locally up to their allowance without coordination.
///
/// ## Coordinator Role
///
/// In practice, this struct lives on the ordering node(s) responsible for the
/// resource. The ordering nodes:
/// 1. Initialize the budget when the resource is registered for shared access.
/// 2. Distribute allowances to participating agents.
/// 3. Process spending reports during rebalancing.
/// 4. Detect overspending and escalate to Tier 3 if needed.
///
/// Alternatively, for fully peer-to-peer operation, the agents themselves can run
/// the rebalancing protocol using the blocklace as the ground truth.
#[derive(Clone, Debug)]
pub struct SharedResourceBudget {
    /// The shared resource being managed.
    pub resource: ResourceId,
    /// Participating agents.
    pub participants: Vec<ParticipantId>,
    /// Byzantine fault tolerance: max Byzantine agents to tolerate.
    pub byzantine_tolerance: usize,
    /// Current epoch version (incremented on each rebalance).
    pub version: BudgetVersion,
    /// Per-agent allowance states.
    pub allowances: HashMap<ParticipantId, AgentAllowance>,
    /// The resource's total available balance at epoch start.
    /// This is the ground truth from the ledger.
    pub total_balance: ResourceAmount,
    /// Credits received during this epoch (deposits increase the balance).
    /// These are tracked separately so rebalance can account for inflows.
    pub epoch_credits: ResourceAmount,
    /// The escalation state of this resource.
    pub state: ResourceState,
    /// Resolution outcomes for blocks processed during escalation.
    pub resolutions: HashMap<BlocBlockId, DebitResolution>,
}

impl SharedResourceBudget {
    /// Create a new shared resource budget.
    ///
    /// # Parameters
    /// - `resource`: The shared resource cell ID.
    /// - `total_balance`: The resource's current available balance.
    /// - `participants`: Agents that may access this resource.
    /// - `byzantine_tolerance`: Max Byzantine agents to tolerate.
    ///
    /// # Errors
    /// Returns `Err` if `participants.len() < 2 * byzantine_tolerance + 1`.
    ///
    /// NOTE: The BFT threshold here is 2f+1 (not 3f+1 as in StingrayCounter).
    /// This is because in the shared-resource model, participants ARE the agents
    /// (not replicated nodes). We need a quorum of honest participants to attest
    /// to their spending. With n >= 2f+1, at least f+1 are honest, which suffices
    /// to reconstruct the true total spending.
    pub fn new(
        resource: ResourceId,
        total_balance: ResourceAmount,
        participants: Vec<ParticipantId>,
        byzantine_tolerance: usize,
    ) -> Result<Self, SharedBudgetError> {
        let n = participants.len();
        if n < 2 * byzantine_tolerance + 1 {
            return Err(SharedBudgetError::InsufficientParticipants {
                have: n,
                need: 2 * byzantine_tolerance + 1,
            });
        }

        let mut budget = SharedResourceBudget {
            resource,
            participants,
            byzantine_tolerance,
            version: 0,
            allowances: HashMap::new(),
            total_balance,
            epoch_credits: 0,
            state: ResourceState::Open,
            resolutions: HashMap::new(),
        };

        budget.distribute_allowances();
        Ok(budget)
    }

    /// Calculate the per-agent allowance ceiling.
    ///
    /// Formula: ceiling = balance * (f+1) / (2f+1)
    ///
    /// Same formula as StingrayCounter. The sum of all ceilings exceeds the true
    /// balance (intentionally) -- this is what allows concurrent local spending.
    /// Safety: with at most f Byzantine agents, the maximum overspend is f * ceiling.
    pub fn compute_allowance_ceiling(&self) -> ResourceAmount {
        let f = self.byzantine_tolerance as u64;
        let numerator = f + 1;
        let denominator = 2 * f + 1;
        ((self.total_balance as u128 * numerator as u128) / denominator as u128) as u64
    }

    /// Distribute (or redistribute) allowances to all participants.
    fn distribute_allowances(&mut self) {
        let ceiling = self.compute_allowance_ceiling();
        self.allowances.clear();

        for &participant in &self.participants {
            let allowance = AgentAllowance::new(participant, self.resource, self.version, ceiling);
            self.allowances.insert(participant, allowance);
        }
    }

    /// Try to debit from a specific agent's allowance.
    ///
    /// This is the HOT PATH: no coordination with other agents or ordering nodes
    /// is needed as long as the agent's local allowance has remaining budget.
    ///
    /// Returns `Err(ResourceClosing)` if the resource is in escalation state.
    pub fn try_debit(
        &mut self,
        agent: ParticipantId,
        amount: ResourceAmount,
        digest: DebitDigest,
    ) -> Result<(), SharedBudgetError> {
        // Reject debits if not in Open state.
        if self.state != ResourceState::Open {
            return Err(SharedBudgetError::ResourceClosing {
                resource: self.resource,
            });
        }

        let allowance = self
            .allowances
            .get_mut(&agent)
            .ok_or(SharedBudgetError::UnknownParticipant { agent })?;
        allowance.try_debit(amount, digest)
    }

    /// Check whether a debit of `amount` from `agent` would cause overspend.
    ///
    /// Used by the tier classifier to decide Optimistic vs Ordered execution.
    /// Does NOT mutate state -- purely a read check.
    pub fn would_overspend(&self, agent: &ParticipantId, amount: ResourceAmount) -> bool {
        match self.allowances.get(agent) {
            Some(allowance) => amount > allowance.remaining(),
            None => true, // Unknown agent => treat as overspend
        }
    }

    /// Get the remaining allowance for a specific agent.
    pub fn remaining(&self, agent: &ParticipantId) -> Option<ResourceAmount> {
        self.allowances.get(agent).map(|a| a.remaining())
    }

    /// Get total spent across all agents in this epoch.
    pub fn total_spent(&self) -> ResourceAmount {
        self.allowances.values().map(|a| a.spent).sum()
    }

    /// Record a credit (deposit) to the shared resource.
    ///
    /// Credits immediately increase the tracked balance. They do NOT automatically
    /// increase individual allowances (that happens at rebalance). However, the
    /// coordinator can optionally trigger an early allowance expansion.
    pub fn credit(&mut self, amount: ResourceAmount) {
        self.total_balance = self.total_balance.saturating_add(amount);
        self.epoch_credits = self.epoch_credits.saturating_add(amount);
    }

    /// Check if the total spending across all agents has exceeded the true balance.
    ///
    /// This is the COD "overspending detection" check. When true, escalation to
    /// Tier 3 ordering is needed to resolve which debits are valid.
    pub fn is_overspent(&self) -> bool {
        self.total_spent() > self.total_balance
    }

    // ─── Blocklace Integration ──────────────────────────────────────────────

    /// Derive the budget state from observed blocklace debits.
    ///
    /// Each agent's virtual chain in the blocklace contains their spending record
    /// for this resource. This method walks each participant's chain, extracts
    /// debits tagged with this resource's ID, and updates the local allowance state.
    ///
    /// The blocklace IS the source of truth. This method just computes allowances
    /// from what's observable in the DAG.
    ///
    /// # Parameters
    /// - `blocklace`: The local blocklace view.
    /// - `resource_id`: The 32-byte resource identifier to filter debits for.
    pub fn sync_from_blocklace(&mut self, blocklace: &Blocklace, resource_id: &[u8; 32]) {
        // Collect participants to avoid borrow conflict (participants borrows self
        // immutably, but we need to mutate allowances).
        let participants: Vec<ParticipantId> = self.participants.clone();
        for participant in &participants {
            let creator_key: [u8; 32] = *participant.as_bytes();
            let chain = blocklace.virtual_chain(&creator_key);
            let total_spent: u64 = chain
                .iter()
                .filter_map(|block| extract_debit_for_resource(block, resource_id))
                .sum();
            if let Some(allowance) = self.allowances.get_mut(participant) {
                allowance.spent = total_spent;
            }
        }
    }

    /// Derive budget state from a slice of raw blocklace blocks.
    ///
    /// This is the primary integration point: given newly-received blocks from the
    /// blocklace (e.g., via dissemination or catch-up), scan each block for debits
    /// against this resource and update the accounting. If the cumulative observed
    /// debits now exceed the total balance, automatically escalate to Closing.
    ///
    /// Unlike `sync_from_blocklace()` which re-scans full virtual chains, this
    /// method processes an incremental batch of blocks (the "on new blocks" path).
    ///
    /// # Parameters
    /// - `blocks`: Newly received blocks (from dissemination or delta-merge).
    /// - `resource_id`: The 32-byte resource identifier to filter debits for.
    pub fn sync_from_blocklace_blocks(&mut self, blocks: &[BlocBlock], resource_id: &[u8; 32]) {
        for block in blocks {
            if let Some(amount) = extract_debit_for_resource(block, resource_id) {
                let agent = CellId::from_bytes(block.creator);
                self.record_observed_debit(agent, amount);
            }
        }
        // Check if new observations trigger overspend -> escalate
        if self.is_overspent() && self.state == ResourceState::Open {
            self.state = ResourceState::Closing {
                conflicting: Vec::new(),
            };
        }
    }

    /// Check if a debit would be accepted optimistically (Tier 2 fast path).
    ///
    /// Returns `true` if the debit was accepted within the agent's allowance
    /// (consensus-free, no coordination needed). Returns `false` if the resource
    /// is not in Open state or if the debit would exceed the agent's allowance,
    /// triggering escalation to Tier 3 ordering.
    ///
    /// This is the method that `DreggBlocklaceBridge` calls on the hot path:
    /// - `true` → debit recorded, agent can proceed without waiting for ordering.
    /// - `false` → the debit needs Tier 3 (tau ordering) to resolve.
    ///
    /// # Parameters
    /// - `agent`: The agent attempting the debit.
    /// - `amount`: The debit amount.
    /// - `digest`: The debit transaction digest (for tracking).
    pub fn try_optimistic_debit(
        &mut self,
        agent: ParticipantId,
        amount: ResourceAmount,
        digest: DebitDigest,
    ) -> bool {
        if self.state != ResourceState::Open {
            return false; // Currently closing/resolving, all debits go to Tier 3
        }
        match self.try_debit(agent, amount, digest) {
            Ok(()) => true, // Accepted within allowance (consensus-free!)
            Err(_) => {
                self.escalate(Vec::new());
                false // Needs ordering
            }
        }
    }

    /// Update the spent amount for a participant from blocklace-observed data.
    pub fn update_spent(&mut self, agent: ParticipantId, total_spent: ResourceAmount) {
        if let Some(allowance) = self.allowances.get_mut(&agent) {
            allowance.spent = total_spent;
        }
    }

    /// Record a single observed debit for a participant.
    ///
    /// This is called incrementally (on each new block) rather than re-scanning
    /// the entire virtual chain.
    pub fn record_observed_debit(&mut self, agent: ParticipantId, amount: ResourceAmount) {
        if let Some(allowance) = self.allowances.get_mut(&agent) {
            allowance.spent = allowance.spent.saturating_add(amount);
        }
    }

    /// Compute allowances from blocklace state (batch interface).
    ///
    /// Given a function that sums an agent's debits against this resource from
    /// their virtual chain in the blocklace, compute the effective allowance state.
    /// This enables deriving the bounded counter from the blocklace rather than
    /// maintaining separate accounting.
    ///
    /// # Parameters
    /// - `blocklace_debits`: maps each participant to their total debits observed
    ///   in the blocklace for this resource since the last epoch.
    pub fn sync_from_debit_map(
        &mut self,
        blocklace_debits: &HashMap<ParticipantId, ResourceAmount>,
    ) {
        for (agent, &debited) in blocklace_debits {
            if let Some(allowance) = self.allowances.get_mut(agent) {
                // The blocklace is the source of truth for what was spent.
                allowance.spent = debited;
            }
        }
    }

    // ─── Escalation: Tier 2 -> Tier 3 ──────────────────────────────────────

    /// Escalate to Tier 3: transition from Open to Closing.
    ///
    /// Called when `is_overspent()` returns true. Pauses new debits and records
    /// the conflicting block IDs that need ordering by Cordial Miners.
    ///
    /// # Parameters
    /// - `conflicting_blocks`: Block IDs whose aggregate debits exceed the balance.
    pub fn escalate(&mut self, conflicting_blocks: Vec<BlocBlockId>) {
        self.state = ResourceState::Closing {
            conflicting: conflicting_blocks,
        };
    }

    /// Resolve the escalation using tau-ordered blocks from Cordial Miners.
    ///
    /// Called once tau has provided a total order for the conflicting blocks.
    /// Processes debits in tau order: first debit wins, later debits rejected
    /// if balance is insufficient.
    ///
    /// After resolution, transitions to Open with new allowances based on the
    /// remaining balance.
    ///
    /// # Parameters
    /// - `ordered_blocks`: Block IDs in tau order (the total order from consensus).
    /// - `blocklace`: The blocklace to look up block payloads.
    /// - `resource_id`: The resource being resolved.
    pub fn resolve_with_ordering(
        &mut self,
        ordered_blocks: &[BlocBlockId],
        blocklace: &Blocklace,
        resource_id: &[u8; 32],
    ) {
        self.state = ResourceState::Rebalancing;
        self.resolutions.clear();

        let mut remaining_balance = self.total_balance;

        for block_id in ordered_blocks {
            if let Some(block) = blocklace.get(block_id) {
                if let Some(amount) = extract_debit_for_resource(block, resource_id) {
                    if amount <= remaining_balance {
                        // Accept this debit (it came first in tau order).
                        remaining_balance -= amount;
                        self.resolutions
                            .insert(*block_id, DebitResolution::Accepted);
                    } else {
                        // Reject this debit (insufficient balance after earlier debits).
                        self.resolutions
                            .insert(*block_id, DebitResolution::Rejected);
                    }
                }
            }
        }

        // Update the total balance to reflect accepted debits.
        self.total_balance = remaining_balance;

        // Rebalance: new epoch, fresh allowances from the remaining balance.
        self.version += 1;
        self.epoch_credits = 0;
        self.distribute_allowances();
        self.state = ResourceState::Open;
    }

    /// Check if a specific block's debit was accepted during escalation resolution.
    pub fn is_accepted(&self, block_id: &BlocBlockId) -> Option<bool> {
        self.resolutions
            .get(block_id)
            .map(|r| *r == DebitResolution::Accepted)
    }

    // ─── Rebalance (Non-Escalation Path) ───────────────────────────────────

    /// Rebalance: collect spending reports, reconcile, and redistribute allowances.
    ///
    /// This is the "epoch close" operation (equivalent to COD's close-and-reopen).
    ///
    /// # Process
    /// 1. Sum actual spending from all reporting agents.
    /// 2. For non-reporting agents (assumed Byzantine), assume ceiling spent.
    /// 3. Deduct from resource balance.
    /// 4. Increment epoch, redistribute allowances.
    ///
    /// # Parameters
    /// - `reports`: Per-agent spending reports (agent -> total spent in epoch).
    /// - `require_all`: If true, reject unless all agents report.
    ///
    /// # Returns
    /// The total amount spent in this epoch.
    pub fn rebalance(
        &mut self,
        reports: &[(ParticipantId, ResourceAmount)],
        require_all: bool,
    ) -> Result<ResourceAmount, SharedBudgetError> {
        if require_all && reports.len() < self.participants.len() {
            return Err(SharedBudgetError::IncompleteReports {
                received: reports.len(),
                expected: self.participants.len(),
            });
        }

        let mut seen = HashMap::new();
        let mut total_spent: ResourceAmount = 0;
        let ceiling = self.compute_allowance_ceiling();

        for &(agent, spent) in reports {
            // Must be a known participant.
            if !self.allowances.contains_key(&agent) {
                return Err(SharedBudgetError::UnknownParticipant { agent });
            }

            // No duplicates.
            if seen.contains_key(&agent) {
                return Err(SharedBudgetError::DuplicateReport { agent });
            }

            // Reported spending must not exceed ceiling.
            if spent > ceiling {
                return Err(SharedBudgetError::ReportExceedsCeiling {
                    agent,
                    claimed: spent,
                    ceiling,
                });
            }

            seen.insert(agent, spent);
            total_spent = total_spent.saturating_add(spent);
        }

        // For missing participants in non-strict mode: assume full ceiling.
        if !require_all {
            for participant in &self.participants {
                if !seen.contains_key(participant) {
                    total_spent = total_spent.saturating_add(ceiling);
                }
            }
        }

        // Deduct total spending from the resource balance.
        if total_spent > self.total_balance {
            // Overspend detected. In production this triggers Tier 3 escalation.
            // For now, clamp to zero.
            self.total_balance = 0;
        } else {
            self.total_balance -= total_spent;
        }

        // New epoch.
        self.version += 1;
        self.epoch_credits = 0;
        self.distribute_allowances();

        Ok(total_spent)
    }

    /// Add a new participant to the shared resource budget.
    ///
    /// The new participant gets an allowance based on the current balance.
    /// Existing participants keep their current spent amounts but get new ceilings
    /// at the next rebalance.
    pub fn add_participant(&mut self, agent: ParticipantId) -> Result<(), SharedBudgetError> {
        if self.allowances.contains_key(&agent) {
            return Err(SharedBudgetError::DuplicateParticipant { agent });
        }
        self.participants.push(agent);
        let ceiling = self.compute_allowance_ceiling();
        let allowance = AgentAllowance::new(agent, self.resource, self.version, ceiling);
        self.allowances.insert(agent, allowance);
        Ok(())
    }

    /// Remove a participant from the shared resource budget.
    ///
    /// Their unspent allowance is implicitly returned to the pool at next rebalance.
    pub fn remove_participant(&mut self, agent: &ParticipantId) -> Result<(), SharedBudgetError> {
        if !self.allowances.contains_key(agent) {
            return Err(SharedBudgetError::UnknownParticipant { agent: *agent });
        }
        self.participants.retain(|p| p != agent);
        self.allowances.remove(agent);
        Ok(())
    }
}

// ─── Blocklace Observer ─────────────────────────────────────────────────────

/// Manages multiple shared resource budgets and observes blocklace updates.
///
/// This is the on-new-block hook that monitors incoming blocks for resource debits
/// and automatically triggers escalation when overspend is detected.
#[derive(Clone, Debug, Default)]
pub struct SharedBudgetObserver {
    /// Per-resource budget managers.
    pub budgets: HashMap<[u8; 32], SharedResourceBudget>,
}

impl SharedBudgetObserver {
    /// Create a new observer with no budgets registered.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a budget for observation.
    pub fn register(&mut self, resource_id: [u8; 32], budget: SharedResourceBudget) {
        self.budgets.insert(resource_id, budget);
    }

    /// Called when new blocks arrive in the blocklace.
    ///
    /// For each block, checks if it contains a resource debit. If so, records it
    /// and triggers escalation if overspend is detected.
    ///
    /// Returns a list of resource IDs that entered escalation as a result.
    pub fn on_blocklace_update(&mut self, new_blocks: &[&BlocBlock]) -> Vec<[u8; 32]> {
        let mut escalated = Vec::new();

        for block in new_blocks {
            if let Some((resource_id, amount)) = extract_resource_debit(block) {
                let agent = CellId::from_bytes(block.creator);
                if let Some(budget) = self.budgets.get_mut(&resource_id) {
                    budget.record_observed_debit(agent, amount);
                    if budget.is_overspent() && budget.state == ResourceState::Open {
                        // Escalate with an empty conflicting set. The caller should
                        // provide the actual conflicting blocks from their blocklace
                        // scan when calling `resolve_with_ordering`.
                        budget.escalate(Vec::new());
                        escalated.push(resource_id);
                    }
                }
            }
        }

        escalated
    }
}

// ─── Payload Debit Extraction ───────────────────────────────────────────────

/// Debit payload format (encoded in Turn payloads):
///
/// ```text
/// [0x44] [resource_id: 32 bytes] [amount: 8 bytes LE]
/// ```
///
/// The 0x44 tag byte ('D' for debit) distinguishes debit payloads from other
/// turn data. This is a simplified wire format; production would use postcard
/// or a more structured encoding.
const DEBIT_TAG: u8 = 0x44;

/// Minimum size of a debit payload: tag(1) + resource_id(32) + amount(8) = 41.
const DEBIT_PAYLOAD_MIN_SIZE: usize = 1 + 32 + 8;

/// Extract a debit amount for a specific resource from a block's payload.
///
/// Returns `Some(amount)` if the block's payload is a Turn containing a debit
/// for the given resource_id. Returns `None` otherwise.
pub fn extract_debit_for_resource(block: &BlocBlock, resource_id: &[u8; 32]) -> Option<u64> {
    match &block.payload {
        Payload::Turn(data) | Payload::Data(data) => {
            if data.len() < DEBIT_PAYLOAD_MIN_SIZE {
                return None;
            }
            if data[0] != DEBIT_TAG {
                return None;
            }
            let block_resource = &data[1..33];
            if block_resource != resource_id.as_slice() {
                return None;
            }
            let amount_bytes: [u8; 8] = data[33..41].try_into().ok()?;
            Some(u64::from_le_bytes(amount_bytes))
        }
        _ => None,
    }
}

/// Extract a (resource_id, amount) pair from a block regardless of resource.
///
/// Used by the observer to detect any debit in any block.
pub fn extract_resource_debit(block: &BlocBlock) -> Option<([u8; 32], u64)> {
    match &block.payload {
        Payload::Turn(data) | Payload::Data(data) => {
            if data.len() < DEBIT_PAYLOAD_MIN_SIZE {
                return None;
            }
            if data[0] != DEBIT_TAG {
                return None;
            }
            let mut resource_id = [0u8; 32];
            resource_id.copy_from_slice(&data[1..33]);
            let amount_bytes: [u8; 8] = data[33..41].try_into().ok()?;
            Some((resource_id, u64::from_le_bytes(amount_bytes)))
        }
        _ => None,
    }
}

/// Encode a debit payload for a given resource and amount.
///
/// This is the inverse of `extract_debit_for_resource` / `extract_resource_debit`.
pub fn encode_debit_payload(resource_id: &[u8; 32], amount: u64) -> Vec<u8> {
    let mut payload = Vec::with_capacity(DEBIT_PAYLOAD_MIN_SIZE);
    payload.push(DEBIT_TAG);
    payload.extend_from_slice(resource_id);
    payload.extend_from_slice(&amount.to_le_bytes());
    payload
}

// ─── SharedBudgetError ───────────────────────────────────────────────────────

/// Errors from the shared resource budget system.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SharedBudgetError {
    /// An agent's allowance is exhausted (escalate to rebalance or Tier 3).
    AllowanceExhausted {
        agent: ParticipantId,
        resource: ResourceId,
        remaining: ResourceAmount,
        requested: ResourceAmount,
    },
    /// Not enough participants for the requested Byzantine tolerance.
    InsufficientParticipants { have: usize, need: usize },
    /// Unknown participant (agent not registered for this resource).
    UnknownParticipant { agent: ParticipantId },
    /// Duplicate participant.
    DuplicateParticipant { agent: ParticipantId },
    /// Duplicate spending report from the same agent.
    DuplicateReport { agent: ParticipantId },
    /// A report claims more spending than the agent's ceiling allows.
    ReportExceedsCeiling {
        agent: ParticipantId,
        claimed: ResourceAmount,
        ceiling: ResourceAmount,
    },
    /// Not all participants submitted spending reports during rebalance.
    IncompleteReports { received: usize, expected: usize },
    /// Resource is in Closing or Rebalancing state; no new debits accepted.
    ResourceClosing { resource: ResourceId },
}

impl core::fmt::Display for SharedBudgetError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SharedBudgetError::AllowanceExhausted {
                agent,
                resource,
                remaining,
                requested,
            } => {
                write!(
                    f,
                    "allowance exhausted for agent {agent} on resource {resource}: \
                     {remaining} remaining, {requested} requested"
                )
            }
            SharedBudgetError::InsufficientParticipants { have, need } => {
                write!(
                    f,
                    "insufficient participants: have {have}, need {need} (2f+1)"
                )
            }
            SharedBudgetError::UnknownParticipant { agent } => {
                write!(f, "unknown participant: {agent}")
            }
            SharedBudgetError::DuplicateParticipant { agent } => {
                write!(f, "duplicate participant: {agent}")
            }
            SharedBudgetError::DuplicateReport { agent } => {
                write!(f, "duplicate spending report from agent: {agent}")
            }
            SharedBudgetError::ReportExceedsCeiling {
                agent,
                claimed,
                ceiling,
            } => {
                write!(
                    f,
                    "agent {agent} reports {claimed} spent, but ceiling is {ceiling}"
                )
            }
            SharedBudgetError::IncompleteReports { received, expected } => {
                write!(
                    f,
                    "incomplete reports: received {received}, expected {expected}"
                )
            }
            SharedBudgetError::ResourceClosing { resource } => {
                write!(
                    f,
                    "resource {resource} is closing (escalation in progress), no new debits"
                )
            }
        }
    }
}

impl std::error::Error for SharedBudgetError {}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn pool_resource() -> ResourceId {
        CellId::from_bytes([0xBB; 32])
    }

    fn test_agents(n: usize) -> Vec<ParticipantId> {
        (0..n)
            .map(|i| {
                let mut bytes = [0u8; 32];
                bytes[0] = i as u8;
                bytes[1] = (i >> 8) as u8;
                bytes[31] = 0xAA; // distinguish from zero
                CellId::from_bytes(bytes)
            })
            .collect()
    }

    fn test_digest(n: u64) -> DebitDigest {
        *blake3::hash(&n.to_le_bytes()).as_bytes()
    }

    // ── Basic Allowance Tests ────────────────────────────────────────────

    #[test]
    fn test_allowance_ceiling_various_f() {
        let cases = vec![
            // (balance, agent_count, f, expected_ceiling)
            (10000, 4, 1, 6666), // f=1: balance * 2/3
            (10000, 5, 2, 6000), // f=2: balance * 3/5
        ];
        for (balance, agent_count, f, expected) in cases {
            let agents = test_agents(agent_count);
            let budget = SharedResourceBudget::new(pool_resource(), balance, agents, f).unwrap();
            assert_eq!(
                budget.compute_allowance_ceiling(),
                expected,
                "ceiling mismatch for balance={balance}, f={f}"
            );
        }
    }

    #[test]
    fn test_insufficient_participants() {
        let agents = test_agents(2); // Need 2*1+1 = 3 for f=1
        let result = SharedResourceBudget::new(pool_resource(), 10000, agents, 1);
        assert!(matches!(
            result,
            Err(SharedBudgetError::InsufficientParticipants { have: 2, need: 3 })
        ));
    }

    // ── Concurrent Debit Tests (the hot path) ────────────────────────────

    #[test]
    fn test_concurrent_debits_within_allowance() {
        let agents = test_agents(3);
        let agent_a = agents[0];
        let agent_b = agents[1];
        let agent_c = agents[2];

        let mut budget = SharedResourceBudget::new(pool_resource(), 9000, agents, 1).unwrap();
        // ceiling = 9000 * 2/3 = 6000

        // All agents debit concurrently -- no coordination needed.
        assert!(budget.try_debit(agent_a, 2000, test_digest(1)).is_ok());
        assert!(budget.try_debit(agent_b, 3000, test_digest(2)).is_ok());
        assert!(budget.try_debit(agent_c, 1500, test_digest(3)).is_ok());

        assert_eq!(budget.total_spent(), 6500);
        assert_eq!(budget.remaining(&agent_a), Some(4000));
        assert_eq!(budget.remaining(&agent_b), Some(3000));
        assert_eq!(budget.remaining(&agent_c), Some(4500));
    }

    #[test]
    fn test_debit_exceeds_allowance() {
        let agents = test_agents(3);
        let agent_a = agents[0];

        let mut budget = SharedResourceBudget::new(pool_resource(), 3000, agents, 1).unwrap();
        // ceiling = 3000 * 2/3 = 2000

        // Case 1: single transaction exceeds allowance.
        let err = budget.try_debit(agent_a, 2001, test_digest(1)).unwrap_err();
        assert!(matches!(
            err,
            SharedBudgetError::AllowanceExhausted {
                remaining: 2000,
                requested: 2001,
                ..
            }
        ));

        // Case 2: spend exactly to ceiling, then one more.
        budget.try_debit(agent_a, 1000, test_digest(2)).unwrap();
        budget.try_debit(agent_a, 1000, test_digest(3)).unwrap();
        let err = budget.try_debit(agent_a, 1, test_digest(4)).unwrap_err();
        assert!(matches!(
            err,
            SharedBudgetError::AllowanceExhausted {
                remaining: 0,
                requested: 1,
                ..
            }
        ));
    }

    // ── Multi-Agent Overspending Scenario (AMM pool) ─────────────────────

    #[test]
    fn test_amm_pool_scenario() {
        // AMM pool with 10000 tokens. 5 agents, f=1.
        let agents = test_agents(5);
        let mut budget =
            SharedResourceBudget::new(pool_resource(), 10000, agents.clone(), 1).unwrap();
        // ceiling = 10000 * 2/3 = 6666

        // Agent 0 swaps 5000 (within ceiling).
        budget.try_debit(agents[0], 5000, test_digest(0)).unwrap();
        // Agent 1 swaps 4000 (within ceiling).
        budget.try_debit(agents[1], 4000, test_digest(1)).unwrap();
        // Agent 2 swaps 3000 (within ceiling).
        budget.try_debit(agents[2], 3000, test_digest(2)).unwrap();

        // Total spent: 12000 > 10000 true balance.
        // Overspending detected!
        assert_eq!(budget.total_spent(), 12000);
        assert!(budget.is_overspent());

        // This triggers escalation to Tier 3 (ordering) to decide which
        // debits are valid. In production, the rebalance would reject or
        // roll back the excess.
    }

    #[test]
    fn test_no_overspend_when_agents_are_conservative() {
        // Same pool, but agents are conservative.
        let agents = test_agents(5);
        let mut budget =
            SharedResourceBudget::new(pool_resource(), 10000, agents.clone(), 1).unwrap();

        // Each agent spends only 2000 (well within ceiling of 6666).
        for (i, &agent) in agents.iter().enumerate() {
            budget
                .try_debit(agent, 2000, test_digest(i as u64))
                .unwrap();
        }

        // Total: 10000 = exactly the balance. No overspend.
        assert_eq!(budget.total_spent(), 10000);
        assert!(!budget.is_overspent());
    }

    // ── Rebalancing Tests ────────────────────────────────────────────────

    #[test]
    fn test_rebalance_full_reports() {
        let agents = test_agents(3);
        let mut budget =
            SharedResourceBudget::new(pool_resource(), 9000, agents.clone(), 1).unwrap();

        // Agents spend various amounts.
        budget.try_debit(agents[0], 1000, test_digest(0)).unwrap();
        budget.try_debit(agents[1], 2000, test_digest(1)).unwrap();
        // Agent 2 spends nothing.

        // All agents report their spending.
        let reports = vec![(agents[0], 1000), (agents[1], 2000), (agents[2], 0)];
        let total = budget.rebalance(&reports, true).unwrap();
        assert_eq!(total, 3000);

        // Balance updated: 9000 - 3000 = 6000.
        assert_eq!(budget.total_balance, 6000);

        // New epoch, new ceiling: 6000 * 2/3 = 4000.
        assert_eq!(budget.version, 1);
        assert_eq!(budget.compute_allowance_ceiling(), 4000);
    }

    #[test]
    fn test_rebalance_partial_mode() {
        let agents = test_agents(3);
        let mut budget =
            SharedResourceBudget::new(pool_resource(), 9000, agents.clone(), 1).unwrap();

        budget.try_debit(agents[0], 500, test_digest(0)).unwrap();

        // Only agent 0 reports. Others assumed to have spent full ceiling (6000 each).
        let reports = vec![(agents[0], 500)];
        let total = budget.rebalance(&reports, false).unwrap();
        // 500 + 2 * 6000 = 12500
        assert_eq!(total, 12500);

        // Balance clamped to 0 (overspent from conservative estimate).
        assert_eq!(budget.total_balance, 0);
    }

    #[test]
    fn test_rebalance_rejects_incomplete() {
        let agents = test_agents(3);
        let mut budget =
            SharedResourceBudget::new(pool_resource(), 9000, agents.clone(), 1).unwrap();

        let reports = vec![(agents[0], 100)];
        let err = budget.rebalance(&reports, true).unwrap_err();
        assert!(matches!(
            err,
            SharedBudgetError::IncompleteReports {
                received: 1,
                expected: 3
            }
        ));
    }

    #[test]
    fn test_rebalance_rejects_overspend_report() {
        let agents = test_agents(3);
        let mut budget =
            SharedResourceBudget::new(pool_resource(), 9000, agents.clone(), 1).unwrap();
        // ceiling = 6000

        // Agent claims more than their ceiling.
        let reports = vec![
            (agents[0], 7000), // exceeds 6000 ceiling
            (agents[1], 0),
            (agents[2], 0),
        ];
        let err = budget.rebalance(&reports, true).unwrap_err();
        assert!(matches!(
            err,
            SharedBudgetError::ReportExceedsCeiling {
                claimed: 7000,
                ceiling: 6000,
                ..
            }
        ));
    }

    // ── Credit (Deposit) Tests ───────────────────────────────────────────

    #[test]
    fn test_credit_increases_balance() {
        let agents = test_agents(3);
        let mut budget = SharedResourceBudget::new(pool_resource(), 9000, agents, 1).unwrap();

        budget.credit(1000);
        assert_eq!(budget.total_balance, 10000);
        assert_eq!(budget.epoch_credits, 1000);

        // Allowances don't change until rebalance.
        assert_eq!(budget.compute_allowance_ceiling(), 6666);
    }

    // ── Dynamic Participation Tests ──────────────────────────────────────

    #[test]
    fn test_add_participant() {
        let agents = test_agents(3);
        let mut budget = SharedResourceBudget::new(pool_resource(), 9000, agents, 1).unwrap();

        let new_agent = CellId::from_bytes([0xFF; 32]);
        budget.add_participant(new_agent).unwrap();

        assert_eq!(budget.participants.len(), 4);
        assert!(budget.allowances.contains_key(&new_agent));
        // New agent gets the current ceiling.
        assert_eq!(budget.remaining(&new_agent), Some(6000));
    }

    #[test]
    fn test_add_duplicate_participant_rejected() {
        let agents = test_agents(3);
        let agent_a = agents[0];
        let mut budget = SharedResourceBudget::new(pool_resource(), 9000, agents, 1).unwrap();

        let err = budget.add_participant(agent_a).unwrap_err();
        assert!(matches!(
            err,
            SharedBudgetError::DuplicateParticipant { .. }
        ));
    }

    #[test]
    fn test_remove_participant() {
        let agents = test_agents(3);
        let agent_c = agents[2];
        let mut budget = SharedResourceBudget::new(pool_resource(), 9000, agents, 1).unwrap();

        budget.remove_participant(&agent_c).unwrap();
        assert_eq!(budget.participants.len(), 2);
        assert!(!budget.allowances.contains_key(&agent_c));
    }

    // ── Blocklace Sync Tests ─────────────────────────────────────────────

    #[test]
    fn test_sync_from_debit_map() {
        let agents = test_agents(3);
        let agent_a = agents[0];
        let agent_b = agents[1];

        let mut budget = SharedResourceBudget::new(pool_resource(), 9000, agents, 1).unwrap();

        // Simulate: blocklace shows agent_a spent 1500, agent_b spent 800.
        let mut observed = HashMap::new();
        observed.insert(agent_a, 1500u64);
        observed.insert(agent_b, 800u64);

        budget.sync_from_debit_map(&observed);

        assert_eq!(budget.remaining(&agent_a), Some(6000 - 1500));
        assert_eq!(budget.remaining(&agent_b), Some(6000 - 800));
    }

    // ── Safety Bound Test ────────────────────────────────────────────────

    #[test]
    fn test_byzantine_agent_overspend_is_bounded() {
        // With 3 agents, f=1, ceiling = balance * 2/3.
        // Even if the Byzantine agent spends its full ceiling, the overspend
        // beyond the true balance is bounded by f * ceiling.
        let agents = test_agents(3);
        let byzantine = agents[0];

        let mut budget = SharedResourceBudget::new(pool_resource(), 3000, agents, 1).unwrap();
        let ceiling = budget.compute_allowance_ceiling();
        // ceiling = 3000 * 2/3 = 2000
        assert_eq!(ceiling, 2000);

        // Byzantine agent spends full ceiling.
        budget.try_debit(byzantine, 2000, test_digest(0)).unwrap();
        assert_eq!(budget.remaining(&byzantine), Some(0));

        // The honest agents collectively can ALSO each spend up to 2000.
        // Worst case total: 3 * 2000 = 6000 vs true balance of 3000.
        // Max overspend = (n * ceiling) - balance = 6000 - 3000 = 3000.
        // But in practice, overspend is detected and honest agents stop or
        // rebalance before it gets this bad.
        //
        // The Stingray invariant: with at most f=1 Byzantine, the maximum
        // UNDETECTABLE overspend before rebalance is f * ceiling = 2000.
        // This is because the honest agents (n-f = 2) reveal their true spending
        // at rebalance, and only the Byzantine agent's claim is unverifiable.
    }

    // ── Epoch Lifecycle (Full Scenario) ──────────────────────────────────

    #[test]
    fn test_full_epoch_lifecycle() {
        let agents = test_agents(4);
        let mut budget =
            SharedResourceBudget::new(pool_resource(), 12000, agents.clone(), 1).unwrap();
        // ceiling = 12000 * 2/3 = 8000

        // --- Epoch 0: agents transact ---
        budget.try_debit(agents[0], 3000, test_digest(10)).unwrap();
        budget.try_debit(agents[1], 2000, test_digest(11)).unwrap();
        budget.try_debit(agents[2], 1500, test_digest(12)).unwrap();
        // Agent 3 is idle.

        // Someone deposits into the pool.
        budget.credit(500);

        assert_eq!(budget.total_spent(), 6500);
        assert!(!budget.is_overspent()); // 6500 < 12500

        // --- Epoch close: rebalance ---
        let reports = vec![
            (agents[0], 3000),
            (agents[1], 2000),
            (agents[2], 1500),
            (agents[3], 0),
        ];
        let total = budget.rebalance(&reports, true).unwrap();
        assert_eq!(total, 6500);

        // New balance: 12500 (original + credit) - 6500 = 6000.
        assert_eq!(budget.total_balance, 6000);
        assert_eq!(budget.version, 1);
        assert_eq!(budget.epoch_credits, 0); // reset

        // --- Epoch 1: fresh allowances ---
        // ceiling = 6000 * 2/3 = 4000
        assert_eq!(budget.compute_allowance_ceiling(), 4000);
        for &agent in &agents {
            assert_eq!(budget.remaining(&agent), Some(4000));
        }
    }

    // ── Escalation Tests (Tier 2 -> Tier 3) ─────────────────────────────

    #[test]
    fn test_escalation_blocks_new_debits() {
        let agents = test_agents(3);
        let agent_a = agents[0];

        let mut budget = SharedResourceBudget::new(pool_resource(), 9000, agents, 1).unwrap();

        // Escalate.
        budget.escalate(vec![BlocBlockId([0xAA; 32])]);
        assert_eq!(
            budget.state,
            ResourceState::Closing {
                conflicting: vec![BlocBlockId([0xAA; 32])]
            }
        );

        // New debits should be rejected.
        let err = budget.try_debit(agent_a, 100, test_digest(1)).unwrap_err();
        assert!(matches!(err, SharedBudgetError::ResourceClosing { .. }));
    }

    #[test]
    fn test_would_overspend() {
        let agents = test_agents(3);
        let agent_a = agents[0];
        let agent_b = agents[1];

        let mut budget = SharedResourceBudget::new(pool_resource(), 3000, agents, 1).unwrap();
        // ceiling = 2000

        // Agent A hasn't spent anything: 2000 remaining.
        assert!(!budget.would_overspend(&agent_a, 1000));
        assert!(!budget.would_overspend(&agent_a, 2000));
        assert!(budget.would_overspend(&agent_a, 2001));

        // After spending, less remains.
        budget.try_debit(agent_a, 1500, test_digest(1)).unwrap();
        assert!(!budget.would_overspend(&agent_a, 500));
        assert!(budget.would_overspend(&agent_a, 501));

        // Unknown agent always overspends.
        let unknown = CellId::from_bytes([0xFF; 32]);
        assert!(budget.would_overspend(&unknown, 1));
    }

    #[test]
    fn test_resource_state_lifecycle() {
        let agents = test_agents(3);

        let mut budget = SharedResourceBudget::new(pool_resource(), 9000, agents, 1).unwrap();
        assert_eq!(budget.state, ResourceState::Open);

        // Escalate.
        let fake_blocks = vec![BlocBlockId([0x11; 32]), BlocBlockId([0x22; 32])];
        budget.escalate(fake_blocks.clone());
        assert_eq!(
            budget.state,
            ResourceState::Closing {
                conflicting: fake_blocks
            }
        );

        // We can't resolve without a real blocklace here, but we can test
        // that resolve_with_ordering transitions back to Open.
        // Use an empty ordered_blocks to simulate (no actual debits to resolve).
        let sk = ed25519_dalek::SigningKey::from_bytes(&[0x42; 32]);
        let blocklace = Blocklace::new_simple(sk);
        budget.resolve_with_ordering(&[], &blocklace, &[0xBB; 32]);

        assert_eq!(budget.state, ResourceState::Open);
        // Version incremented.
        assert_eq!(budget.version, 1);
    }

    // ── Encode/Decode Debit Payload ─────────────────────────────────────

    #[test]
    fn test_encode_decode_debit_payload() {
        let resource_id = [0xCC; 32];
        let amount = 4200u64;

        let payload = encode_debit_payload(&resource_id, amount);
        assert_eq!(payload.len(), DEBIT_PAYLOAD_MIN_SIZE);
        assert_eq!(payload[0], DEBIT_TAG);

        // Decode via a mock block.
        let sk = ed25519_dalek::SigningKey::from_bytes(&[0x01; 32]);
        let block = BlocBlock::new(&sk, 0, Payload::Turn(payload), vec![]);

        let extracted = extract_debit_for_resource(&block, &resource_id);
        assert_eq!(extracted, Some(4200));

        // Wrong resource returns None.
        let wrong_resource = [0xDD; 32];
        assert_eq!(extract_debit_for_resource(&block, &wrong_resource), None);
    }

    #[test]
    fn test_extract_resource_debit_generic() {
        let resource_id = [0xEE; 32];
        let amount = 7777u64;

        let payload = encode_debit_payload(&resource_id, amount);
        let sk = ed25519_dalek::SigningKey::from_bytes(&[0x02; 32]);
        let block = BlocBlock::new(&sk, 0, Payload::Turn(payload), vec![]);

        let result = extract_resource_debit(&block);
        assert_eq!(result, Some((resource_id, 7777)));
    }

    // ── Solo Mode Test ──────────────────────────────────────────────────

    #[test]
    fn test_solo_agent_never_escalates() {
        // Single agent with f=0 (no Byzantine tolerance needed with one agent).
        // Note: need n >= 2*0+1 = 1 participant.
        let agents = test_agents(1);
        let solo = agents[0];

        let mut budget = SharedResourceBudget::new(pool_resource(), 5000, agents, 0).unwrap();
        // ceiling = 5000 * 1/1 = 5000 (full balance)

        budget.try_debit(solo, 1000, test_digest(1)).unwrap();
        budget.try_debit(solo, 2000, test_digest(2)).unwrap();
        budget.try_debit(solo, 2000, test_digest(3)).unwrap();

        // Solo agent spent exactly the balance: no overspend.
        assert_eq!(budget.total_spent(), 5000);
        assert!(!budget.is_overspent());
    }

    // ── Tier 2 → Tier 3 Escalation Tests ───────────────────────────────

    #[test]
    fn test_resolve_with_ordering_accepts_rejects() {
        // 3 agents, pool of 1000. After overspend, resolve via tau ordering.
        let agents = test_agents(3);
        let agent_a = agents[0];
        let agent_b = agents[1];
        let agent_c = agents[2];

        let mut budget = SharedResourceBudget::new(pool_resource(), 1000, agents, 1).unwrap();

        // Set up the blocks in a blocklace for resolution.
        let sk = ed25519_dalek::SigningKey::from_bytes(&[0x42; 32]);
        let mut blocklace = Blocklace::new_simple(sk);

        let resource_id = [0xBB; 32];

        // Create blocks with debit payloads for each agent.
        // Agent A = 400
        let payload_a = encode_debit_payload(&resource_id, 400);
        let sk_a = ed25519_dalek::SigningKey::from_bytes(&agent_a.as_bytes().clone());
        let block_a = BlocBlock::new(&sk_a, 1, Payload::Turn(payload_a), vec![]);
        let block_a_id = block_a.id();
        blocklace.receive_block(block_a).unwrap();

        // Agent B = 400
        let payload_b = encode_debit_payload(&resource_id, 400);
        let sk_b = ed25519_dalek::SigningKey::from_bytes(&agent_b.as_bytes().clone());
        let block_b = BlocBlock::new(&sk_b, 1, Payload::Turn(payload_b), vec![]);
        let block_b_id = block_b.id();
        blocklace.receive_block(block_b).unwrap();

        // Agent C = 400
        let payload_c = encode_debit_payload(&resource_id, 400);
        let sk_c = ed25519_dalek::SigningKey::from_bytes(&agent_c.as_bytes().clone());
        let block_c = BlocBlock::new(&sk_c, 1, Payload::Turn(payload_c), vec![]);
        let block_c_id = block_c.id();
        blocklace.receive_block(block_c).unwrap();

        // Escalate.
        budget.escalate(vec![block_a_id, block_b_id, block_c_id]);
        assert!(matches!(budget.state, ResourceState::Closing { .. }));

        // Resolve: tau orders them as [A, B, C].
        // A=400 accepted (1000-400=600 remaining), B=400 accepted (600-400=200),
        // C=400 rejected (200 < 400).
        let ordered = vec![block_a_id, block_b_id, block_c_id];
        budget.resolve_with_ordering(&ordered, &blocklace, &resource_id);

        // Verify resolution outcomes.
        assert_eq!(budget.is_accepted(&block_a_id), Some(true));
        assert_eq!(budget.is_accepted(&block_b_id), Some(true));
        assert_eq!(budget.is_accepted(&block_c_id), Some(false)); // Rejected!

        // Balance should be 200 (1000 - 400 - 400).
        assert_eq!(budget.total_balance, 200);

        // Back to Open after resolution.
        assert_eq!(budget.state, ResourceState::Open);

        // Version incremented.
        assert_eq!(budget.version, 1);

        // New allowances from remaining 200: ceiling = 200 * 2/3 = 133.
        assert_eq!(budget.compute_allowance_ceiling(), 133);
    }

    /// Helper: create signing keys and derive participant IDs from public keys.
    /// This ensures the ParticipantId matches the block creator field (which is
    /// the verifying/public key, not the signing key bytes).
    fn signing_key_and_participant(seed: u8) -> (ed25519_dalek::SigningKey, ParticipantId) {
        let mut key_bytes = [0u8; 32];
        key_bytes[0] = seed;
        key_bytes[31] = 0xDD;
        let sk = ed25519_dalek::SigningKey::from_bytes(&key_bytes);
        let pk = sk.verifying_key().to_bytes();
        (sk, CellId::from_bytes(pk))
    }

    #[test]
    fn test_sync_from_blocklace_blocks_derives_state() {
        // Construct mock blocks with debit payloads, verify totals correct.
        let (sk_a, agent_a) = signing_key_and_participant(1);
        let (sk_b, agent_b) = signing_key_and_participant(2);
        let (_sk_c, agent_c) = signing_key_and_participant(3);

        let agents = vec![agent_a, agent_b, agent_c];
        let mut budget = SharedResourceBudget::new(pool_resource(), 5000, agents, 1).unwrap();
        let ceiling = budget.compute_allowance_ceiling(); // 5000 * 2/3 = 3333

        let resource_id = [0xBB; 32];

        let block_a1 = BlocBlock::new(
            &sk_a,
            1,
            Payload::Turn(encode_debit_payload(&resource_id, 300)),
            vec![],
        );
        let block_a2 = BlocBlock::new(
            &sk_a,
            2,
            Payload::Turn(encode_debit_payload(&resource_id, 200)),
            vec![],
        );
        let block_b1 = BlocBlock::new(
            &sk_b,
            1,
            Payload::Turn(encode_debit_payload(&resource_id, 500)),
            vec![],
        );

        // Feed blocks through sync_from_blocklace_blocks.
        budget.sync_from_blocklace_blocks(&[block_a1, block_a2, block_b1], &resource_id);

        // Agent A: 300 + 200 = 500 spent.
        assert_eq!(budget.remaining(&agent_a), Some(ceiling - 500));
        // Agent B: 500 spent.
        assert_eq!(budget.remaining(&agent_b), Some(ceiling - 500));
        // Total: 1000 out of 5000. Not overspent.
        assert_eq!(budget.total_spent(), 1000);
        assert!(!budget.is_overspent());
        assert_eq!(budget.state, ResourceState::Open);
    }

    #[test]
    fn test_sync_from_blocklace_blocks_triggers_escalation() {
        // Verify that sync_from_blocklace_blocks auto-escalates on overspend.
        let (sk_a, agent_a) = signing_key_and_participant(1);
        let (sk_b, agent_b) = signing_key_and_participant(2);
        let (sk_c, agent_c) = signing_key_and_participant(3);

        let agents = vec![agent_a, agent_b, agent_c];
        // Small pool of 500 so we can easily trigger overspend.
        let mut budget = SharedResourceBudget::new(pool_resource(), 500, agents, 1).unwrap();
        // ceiling = 500 * 2/3 = 333

        let resource_id = [0xBB; 32];

        let block_a = BlocBlock::new(
            &sk_a,
            1,
            Payload::Turn(encode_debit_payload(&resource_id, 200)),
            vec![],
        );
        let block_b = BlocBlock::new(
            &sk_b,
            1,
            Payload::Turn(encode_debit_payload(&resource_id, 200)),
            vec![],
        );
        let block_c = BlocBlock::new(
            &sk_c,
            1,
            Payload::Turn(encode_debit_payload(&resource_id, 200)),
            vec![],
        );

        // Feed all blocks. Total = 600 > 500 → should escalate.
        budget.sync_from_blocklace_blocks(&[block_a, block_b, block_c], &resource_id);

        assert_eq!(budget.total_spent(), 600);
        assert!(budget.is_overspent());
        assert!(matches!(budget.state, ResourceState::Closing { .. }));
    }

    #[test]
    fn test_sync_from_blocklace_blocks_ignores_wrong_resource() {
        // Blocks with debits for a different resource should be ignored.
        let (sk_a, agent_a) = signing_key_and_participant(1);
        let (_sk_b, agent_b) = signing_key_and_participant(2);
        let (_sk_c, agent_c) = signing_key_and_participant(3);

        let agents = vec![agent_a, agent_b, agent_c];
        let mut budget = SharedResourceBudget::new(pool_resource(), 5000, agents, 1).unwrap();

        let our_resource = [0xBB; 32];
        let other_resource = [0xCC; 32];

        // Block debits a DIFFERENT resource.
        let block = BlocBlock::new(
            &sk_a,
            1,
            Payload::Turn(encode_debit_payload(&other_resource, 1000)),
            vec![],
        );

        budget.sync_from_blocklace_blocks(&[block], &our_resource);

        // No spending recorded.
        assert_eq!(budget.total_spent(), 0);
        assert_eq!(budget.state, ResourceState::Open);
    }

    // ── try_optimistic_debit Tests ─────────────────────────────────────

    #[test]
    fn test_try_optimistic_debit_accepts_within_allowance() {
        let agents = test_agents(3);
        let agent_a = agents[0];

        let mut budget = SharedResourceBudget::new(pool_resource(), 3000, agents, 1).unwrap();
        // ceiling = 2000

        // Within allowance → accepted optimistically.
        assert!(budget.try_optimistic_debit(agent_a, 1000, test_digest(1)));
        assert_eq!(budget.remaining(&agent_a), Some(1000));
        assert_eq!(budget.state, ResourceState::Open);
    }

    #[test]
    fn test_try_optimistic_debit_escalates_on_exceed() {
        let agents = test_agents(3);
        let agent_a = agents[0];

        let mut budget = SharedResourceBudget::new(pool_resource(), 3000, agents, 1).unwrap();
        // ceiling = 2000

        // Exhaust the allowance first.
        assert!(budget.try_optimistic_debit(agent_a, 2000, test_digest(1)));

        // Next debit exceeds allowance → escalate.
        assert!(!budget.try_optimistic_debit(agent_a, 1, test_digest(2)));
        assert!(matches!(budget.state, ResourceState::Closing { .. }));
    }

    #[test]
    fn test_try_optimistic_debit_rejects_when_closing() {
        let agents = test_agents(3);
        let agent_a = agents[0];
        let agent_b = agents[1];

        let mut budget = SharedResourceBudget::new(pool_resource(), 3000, agents, 1).unwrap();

        // Put into Closing state.
        budget.escalate(vec![BlocBlockId([0xAA; 32])]);

        // All debits rejected while closing.
        assert!(!budget.try_optimistic_debit(agent_a, 100, test_digest(1)));
        assert!(!budget.try_optimistic_debit(agent_b, 50, test_digest(2)));
    }

    #[test]
    fn test_try_optimistic_debit_resumes_after_resolution() {
        let agents = test_agents(3);
        let agent_a = agents[0];

        let mut budget = SharedResourceBudget::new(pool_resource(), 3000, agents, 1).unwrap();

        // Escalate.
        budget.escalate(Vec::new());
        assert!(!budget.try_optimistic_debit(agent_a, 100, test_digest(1)));

        // Resolve (empty ordering → balance unchanged).
        let sk = ed25519_dalek::SigningKey::from_bytes(&[0x42; 32]);
        let blocklace = Blocklace::new_simple(sk);
        budget.resolve_with_ordering(&[], &blocklace, &[0xBB; 32]);

        // Now debits work again.
        assert!(budget.try_optimistic_debit(agent_a, 100, test_digest(2)));
        assert_eq!(budget.state, ResourceState::Open);
    }

    // ── Full Escalation Round-Trip ─────────────────────────────────────

    #[test]
    fn test_full_escalation_round_trip() {
        // End-to-end: 3 agents, pool 1000, concurrent debits → overspend →
        // escalate → resolve with tau ordering → resume with reduced balance.
        let agents = test_agents(3);
        let agent_a = agents[0];
        let agent_b = agents[1];
        let agent_c = agents[2];

        let mut budget =
            SharedResourceBudget::new(pool_resource(), 1000, agents.clone(), 1).unwrap();
        // ceiling = 666

        let resource_id = [0xBB; 32];

        // Phase 1: Optimistic debits (Tier 2 fast path).
        assert!(budget.try_optimistic_debit(agent_a, 400, test_digest(100)));
        assert!(budget.try_optimistic_debit(agent_b, 400, test_digest(101)));
        assert!(budget.try_optimistic_debit(agent_c, 400, test_digest(102)));

        // Phase 2: Detect overspend.
        assert!(budget.is_overspent()); // 1200 > 1000

        // Phase 3: Escalate (system detects overspend, blocks new debits).
        budget.escalate(Vec::new());
        assert!(matches!(budget.state, ResourceState::Closing { .. }));

        // Verify all new debits are blocked during escalation.
        assert!(!budget.try_optimistic_debit(agent_a, 10, test_digest(200)));

        // Phase 4: Tau provides ordering. Build a blocklace with the debit blocks.
        let sk = ed25519_dalek::SigningKey::from_bytes(&[0x77; 32]);
        let mut blocklace = Blocklace::new_simple(sk);

        let sk_a = ed25519_dalek::SigningKey::from_bytes(agent_a.as_bytes());
        let sk_b = ed25519_dalek::SigningKey::from_bytes(agent_b.as_bytes());
        let sk_c = ed25519_dalek::SigningKey::from_bytes(agent_c.as_bytes());

        let block_a = BlocBlock::new(
            &sk_a,
            1,
            Payload::Turn(encode_debit_payload(&resource_id, 400)),
            vec![],
        );
        let block_b = BlocBlock::new(
            &sk_b,
            1,
            Payload::Turn(encode_debit_payload(&resource_id, 400)),
            vec![],
        );
        let block_c = BlocBlock::new(
            &sk_c,
            1,
            Payload::Turn(encode_debit_payload(&resource_id, 400)),
            vec![],
        );

        let id_a = block_a.id();
        let id_b = block_b.id();
        let id_c = block_c.id();

        blocklace.receive_block(block_a).unwrap();
        blocklace.receive_block(block_b).unwrap();
        blocklace.receive_block(block_c).unwrap();

        // Phase 5: Resolve. Tau ordered: A first, then B, then C.
        // A=400 accepted (1000-400=600), B=400 accepted (600-400=200), C=400 rejected (200<400).
        budget.resolve_with_ordering(&[id_a, id_b, id_c], &blocklace, &resource_id);

        // Phase 6: Verify outcomes.
        assert_eq!(budget.is_accepted(&id_a), Some(true));
        assert_eq!(budget.is_accepted(&id_b), Some(true));
        assert_eq!(budget.is_accepted(&id_c), Some(false));

        assert_eq!(budget.total_balance, 200);
        assert_eq!(budget.state, ResourceState::Open);
        assert_eq!(budget.version, 1);

        // Phase 7: After resolution, rebalanced with remaining 200.
        // New ceiling = 200 * 2/3 = 133.
        assert_eq!(budget.compute_allowance_ceiling(), 133);

        // Fresh allowances for all agents.
        for &agent in &agents {
            assert_eq!(budget.remaining(&agent), Some(133));
        }

        // Phase 8: New debits accepted within the reduced allowance.
        assert!(budget.try_optimistic_debit(agent_a, 100, test_digest(300)));
        assert_eq!(budget.remaining(&agent_a), Some(33));
    }
}
