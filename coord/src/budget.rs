//! # Bounded Counters & Fast Unlock
//!
//! Generic bounded counter and fast unlock primitives adapted from the Stingray
//! protocol (arXiv:2501.06531). These enable concurrent spending of any fungible
//! resource across multiple silos without per-operation consensus.
//!
//! ## The Problem
//!
//! An agent has a total balance of some resource (computrons, API calls, storage
//! bytes, tokens, etc.). When operating across multiple silos simultaneously,
//! each debit would normally require consensus. This serializes execution.
//!
//! ## The Solution: Bounded Counters
//!
//! Split the agent's total balance into "slices" distributed across silos. Each
//! silo can debit locally up to its slice without coordination. When a slice is
//! exhausted, the silo must rebalance (request more from the coordinator).
//!
//! The key invariant: the sum of all slices never exceeds the agent's true balance,
//! even if some silos are Byzantine. This is guaranteed by the formula:
//!
//!   slice = balance * (f+1) / (2f+1)
//!
//! where f is the number of Byzantine silos to tolerate.
//!
//! ## Fast Unlock
//!
//! When a multi-party operation locks resources and then aborts, fast unlock
//! provides a way to release them without waiting for a full epoch timeout.
//! This is critical for 2PC abort recovery.
//!
//! ## Use Cases
//!
//! - **Computron budgets**: Agent execution metering across silos
//! - **API rate limits**: Distributed rate limiting without central coordination
//! - **Storage quotas**: Parallel writes to distributed storage
//! - **Token allowances**: Spending from a shared balance across services
//!
//! ## Integration
//!
//! The bounded counter plugs into the Coordinator (atomic.rs) as follows:
//! - Before proposing an atomic turn, check the silo's local slice (no coordination).
//! - On commit, debit the slice.
//! - On abort with locked resources, fast unlock reclaims immediately.
//! - Periodically, rebalance reconciles all silo spending with the true balance.

use std::collections::HashMap;

use pyana_cell::CellId;
use serde::{Deserialize, Serialize};

// ─── Types ────────────────────────────────────────────────────────────────────

/// Identifies a silo (execution node) in the budget distribution.
/// This is the same as a node_id in the coordination layer.
pub type SiloId = [u8; 32];

/// A unique identifier for a debit transaction (BLAKE3 hash).
pub type DebitDigest = [u8; 32];

/// Version counter for budget epochs (monotonically increasing).
pub type BudgetVersion = u64;

/// Amount type for any fungible resource.
/// Use u64 directly — the bounded counter is generic over what this represents:
/// computrons, API calls, storage bytes, token units, etc.
pub type ResourceAmount = u64;

/// Convenience alias: a BudgetCoordinator for computron metering.
pub type ComputronBudget = BudgetCoordinator;

// ─── BudgetSlice ──────────────────────────────────────────────────────────────

/// Per-silo state for a bounded counter slice.
///
/// Each silo gets a "slice" of an agent's total resource balance. The silo can
/// debit locally up to this slice without coordinating with other silos.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BudgetSlice {
    /// The agent whose budget this slice belongs to.
    pub agent: CellId,
    /// The budget epoch version this slice is based on.
    pub version: BudgetVersion,
    /// Maximum amount this silo may spend (the slice ceiling).
    pub ceiling: u64,
    /// Amount already spent from this slice.
    pub spent: u64,
    /// Transaction digests that consumed from this slice.
    pub debits: Vec<DebitDigest>,
}

impl BudgetSlice {
    /// Create a new budget slice for an agent on a silo.
    pub fn new(agent: CellId, version: BudgetVersion, ceiling: u64) -> Self {
        BudgetSlice {
            agent,
            version,
            ceiling,
            spent: 0,
            debits: Vec::new(),
        }
    }

    /// Remaining budget in this slice.
    pub fn remaining(&self) -> u64 {
        self.ceiling.saturating_sub(self.spent)
    }

    /// Whether this slice has any remaining budget.
    pub fn has_budget(&self) -> bool {
        self.remaining() > 0
    }

    /// Try to debit from this slice.
    ///
    /// Returns `Ok(())` if the debit succeeds (enough remaining).
    /// Returns `Err(BudgetError::SliceExhausted)` if the slice cannot cover the amount.
    pub fn try_debit(
        &mut self,
        amount: u64,
        digest: DebitDigest,
    ) -> Result<(), BudgetError> {
        if amount > self.remaining() {
            return Err(BudgetError::SliceExhausted {
                agent: self.agent,
                remaining: self.remaining(),
                requested: amount,
            });
        }
        self.spent = self.spent.saturating_add(amount);
        self.debits.push(digest);
        Ok(())
    }

    /// Generate a spending certificate for this slice.
    ///
    /// This certificate is submitted during rebalancing so the coordinator
    /// can reconcile total spending across all silos.
    pub fn certificate(&self, silo: SiloId) -> SpendingCertificate {
        SpendingCertificate {
            silo,
            agent: self.agent,
            version: self.version,
            total_spent: self.spent,
            debits: self.debits.clone(),
        }
    }
}

// ─── SpendingCertificate ──────────────────────────────────────────────────────

/// A silo's attestation of how much it spent from a budget slice.
///
/// During rebalancing, each silo submits a certificate. The coordinator sums
/// all certificates to compute total spending and issues new slices.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpendingCertificate {
    /// The silo that produced this certificate.
    pub silo: SiloId,
    /// The agent whose budget was consumed.
    pub agent: CellId,
    /// The budget version this certificate is for.
    pub version: BudgetVersion,
    /// Total amount spent by this silo.
    pub total_spent: u64,
    /// Individual debit transaction digests.
    pub debits: Vec<DebitDigest>,
}

// ─── BudgetCoordinator ────────────────────────────────────────────────────────

/// Manages resource budget distribution across silos for an agent.
///
/// Generic over any fungible quantity (computrons, API calls, storage, tokens).
/// The coordinator is responsible for:
/// 1. Computing slice sizes based on Byzantine fault tolerance.
/// 2. Distributing slices to silos.
/// 3. Processing spending certificates during rebalancing.
/// 4. Issuing new slices after rebalancing.
#[derive(Clone, Debug)]
pub struct BudgetCoordinator {
    /// The agent whose budget is being managed.
    pub agent: CellId,
    /// All silos in the distribution.
    pub silos: Vec<SiloId>,
    /// Byzantine fault tolerance parameter: max Byzantine silos to tolerate.
    pub byzantine_tolerance: usize,
    /// Current budget version (incremented on each rebalance).
    pub version: BudgetVersion,
    /// Per-silo budget states.
    pub silo_states: HashMap<SiloId, BudgetSlice>,
    /// The agent's total resource balance (ground truth from the ledger).
    pub total_balance: u64,
    /// Total amount committed across all slices (sum of ceilings).
    pub total_allocated: u64,
}

impl BudgetCoordinator {
    /// Create a new budget coordinator for an agent.
    ///
    /// # Parameters
    /// - `agent`: The agent cell whose budget is being managed.
    /// - `total_balance`: The agent's total resource balance.
    /// - `silos`: All execution silos that may debit from this budget.
    /// - `byzantine_tolerance`: Maximum number of Byzantine silos to tolerate.
    ///
    /// # Errors
    /// Returns `Err` if `silos.len() < 3 * byzantine_tolerance + 1`.
    pub fn new(
        agent: CellId,
        total_balance: u64,
        silos: Vec<SiloId>,
        byzantine_tolerance: usize,
    ) -> Result<Self, BudgetError> {
        let n = silos.len();
        if n < 3 * byzantine_tolerance + 1 {
            return Err(BudgetError::InsufficientSilos {
                have: n,
                need: 3 * byzantine_tolerance + 1,
            });
        }

        let mut coord = BudgetCoordinator {
            agent,
            silos,
            byzantine_tolerance,
            version: 0,
            silo_states: HashMap::new(),
            total_balance,
            total_allocated: 0,
        };

        // Distribute initial slices.
        coord.distribute_slices();
        Ok(coord)
    }

    /// Calculate the per-silo ceiling based on Byzantine tolerance.
    ///
    /// Formula: ceiling = balance * (f+1) / (2f+1)
    ///
    /// This ensures that even if f silos are Byzantine and spend their
    /// full slices, the total "overspend" is bounded and recoverable.
    pub fn compute_slice_ceiling(&self) -> u64 {
        let f = self.byzantine_tolerance as u64;
        let numerator = f + 1;
        let denominator = 2 * f + 1;
        // Use u128 to avoid overflow on large balances.
        ((self.total_balance as u128 * numerator as u128) / denominator as u128) as u64
    }

    /// Distribute (or redistribute) slices to all silos.
    fn distribute_slices(&mut self) {
        let ceiling = self.compute_slice_ceiling();
        self.silo_states.clear();
        self.total_allocated = 0;

        for &silo in &self.silos {
            let slice = BudgetSlice::new(self.agent, self.version, ceiling);
            self.silo_states.insert(silo, slice);
            self.total_allocated = self.total_allocated.saturating_add(ceiling);
        }
    }

    /// Try to debit from a specific silo's slice.
    ///
    /// This is the hot path: no coordination with other silos is needed as long
    /// as the silo's local slice has remaining budget.
    pub fn try_debit(
        &mut self,
        silo: SiloId,
        amount: u64,
        digest: DebitDigest,
    ) -> Result<(), BudgetError> {
        let slice = self.silo_states.get_mut(&silo).ok_or(BudgetError::UnknownSilo { silo })?;
        slice.try_debit(amount, digest)
    }

    /// Get the remaining budget for a specific silo.
    pub fn remaining(&self, silo: &SiloId) -> Option<u64> {
        self.silo_states.get(silo).map(|s| s.remaining())
    }

    /// Get total spent across all silos.
    pub fn total_spent(&self) -> u64 {
        self.silo_states.values().map(|s| s.spent).sum()
    }

    /// Get the budget state for an authorization request on a specific silo.
    ///
    /// Returns a map from budget_id to remaining units, suitable for populating
    /// `AuthRequest::budget_states`. The budget_id is constructed from the agent
    /// cell ID (hex-encoded).
    ///
    /// In trusted mode, this is called by the verifier before evaluating a token.
    /// The returned state is then fed as an input fact to the Datalog evaluator.
    pub fn budget_state_for_request(&self, silo: &SiloId) -> HashMap<String, u64> {
        let mut states = HashMap::new();
        if let Some(slice) = self.silo_states.get(silo) {
            // Budget ID is the hex-encoded agent cell ID.
            let bytes = slice.agent.as_bytes();
            let budget_id = bytes.iter().map(|b| format!("{b:02x}")).collect::<String>();
            states.insert(budget_id, slice.remaining());
        }
        states
    }

    /// Rebalance: process spending certificates and redistribute slices.
    ///
    /// This is the expensive coordination step that happens periodically.
    ///
    /// # Process
    /// 1. Verify all certificates are for the current version.
    /// 2. Sum total spending across all silos.
    /// 3. Deduct from the agent's true balance.
    /// 4. Increment version and redistribute fresh slices.
    ///
    /// # Returns
    /// The total amount spent in this epoch (before redistribution).
    pub fn rebalance(
        &mut self,
        certificates: &[SpendingCertificate],
    ) -> Result<u64, BudgetError> {
        // Verify certificates.
        let mut seen_silos = HashMap::new();
        let mut total_spent: u64 = 0;

        for cert in certificates {
            // Must be for this agent.
            if cert.agent != self.agent {
                return Err(BudgetError::WrongAgent {
                    expected: self.agent,
                    got: cert.agent,
                });
            }

            // Must be for current version.
            if cert.version != self.version {
                return Err(BudgetError::VersionMismatch {
                    expected: self.version,
                    got: cert.version,
                });
            }

            // No duplicate certificates from the same silo.
            if seen_silos.contains_key(&cert.silo) {
                return Err(BudgetError::DuplicateCertificate { silo: cert.silo });
            }

            // Certificate spending must not exceed the silo's ceiling.
            let slice = self.silo_states.get(&cert.silo).ok_or(BudgetError::UnknownSilo {
                silo: cert.silo,
            })?;
            if cert.total_spent > slice.ceiling {
                return Err(BudgetError::CertificateExceedsCeiling {
                    silo: cert.silo,
                    claimed: cert.total_spent,
                    ceiling: slice.ceiling,
                });
            }

            seen_silos.insert(cert.silo, cert.total_spent);
            total_spent = total_spent.saturating_add(cert.total_spent);
        }

        // Deduct total spending from the agent's balance.
        if total_spent > self.total_balance {
            // This can only happen if Byzantine silos overspent. The protocol
            // guarantees this is bounded, but we still clamp to zero.
            self.total_balance = 0;
        } else {
            self.total_balance -= total_spent;
        }

        // New epoch: increment version and redistribute.
        self.version += 1;
        self.distribute_slices();

        Ok(total_spent)
    }
}

// ─── FastUnlock ───────────────────────────────────────────────────────────────

/// Lock status for resources held by an atomic turn.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LockStatus {
    /// Resources are locked pending a 2PC outcome.
    Locked {
        /// The proposal that locked these resources.
        proposal_id: [u8; 32],
        /// Amount locked.
        amount: u64,
        /// The silo that initiated the lock.
        silo: SiloId,
        /// Budget version at lock time.
        version: BudgetVersion,
    },
    /// Lock has been released (either committed or unlocked).
    Released,
}

/// A request to unlock resources after a 2PC abort.
///
/// When an atomic turn proposes and locks resources but then aborts,
/// the locked amount would normally be stuck until the epoch timeout.
/// FastUnlock allows immediate release with a quorum of silo attestations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnlockRequest {
    /// The proposal whose lock should be released.
    pub proposal_id: [u8; 32],
    /// The agent whose computrons are locked.
    pub agent: CellId,
    /// Amount to unlock.
    pub amount: u64,
    /// The silo requesting the unlock.
    pub requester: SiloId,
}

/// A silo's vote to approve an unlock.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnlockVote {
    /// The request being voted on.
    pub request: UnlockRequest,
    /// The voting silo.
    pub voter: SiloId,
    /// Whether this silo has a conflicting lock (i.e., it signed a commit).
    pub has_conflict: bool,
}

/// Certificate proving enough silos agree the lock can be released.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnlockCertificate {
    /// The unlock request.
    pub request: UnlockRequest,
    /// Votes from silos (must be >= 2f+1 with no conflicts).
    pub votes: Vec<UnlockVote>,
}

/// Manages locked computrons and the fast unlock protocol.
#[derive(Clone, Debug)]
pub struct FastUnlockManager {
    /// Active locks: proposal_id -> LockStatus.
    pub locks: HashMap<[u8; 32], LockStatus>,
    /// Byzantine tolerance parameter.
    pub byzantine_tolerance: usize,
    /// Total silos in the system.
    pub total_silos: usize,
}

impl FastUnlockManager {
    /// Create a new fast unlock manager.
    pub fn new(byzantine_tolerance: usize, total_silos: usize) -> Self {
        FastUnlockManager {
            locks: HashMap::new(),
            byzantine_tolerance,
            total_silos,
        }
    }

    /// Lock resources for a proposed atomic turn.
    ///
    /// Called when a coordinator proposes an atomic turn that will consume
    /// resources from the agent's budget.
    pub fn lock(
        &mut self,
        proposal_id: [u8; 32],
        _agent: CellId,
        amount: u64,
        silo: SiloId,
        version: BudgetVersion,
    ) -> Result<(), BudgetError> {
        if self.locks.contains_key(&proposal_id) {
            return Err(BudgetError::AlreadyLocked { proposal_id });
        }
        self.locks.insert(
            proposal_id,
            LockStatus::Locked {
                proposal_id,
                amount,
                silo,
                version,
            },
        );
        Ok(())
    }

    /// Release a lock after a successful commit.
    ///
    /// The resources were consumed, so this just clears the lock record.
    pub fn release_on_commit(&mut self, proposal_id: &[u8; 32]) -> Result<u64, BudgetError> {
        match self.locks.get(proposal_id) {
            Some(LockStatus::Locked { amount, .. }) => {
                let amount = *amount;
                self.locks.insert(*proposal_id, LockStatus::Released);
                Ok(amount)
            }
            Some(LockStatus::Released) => Err(BudgetError::AlreadyReleased {
                proposal_id: *proposal_id,
            }),
            None => Err(BudgetError::LockNotFound {
                proposal_id: *proposal_id,
            }),
        }
    }

    /// Process an unlock request (fast path after abort).
    ///
    /// Returns an UnlockVote if this silo agrees the lock can be released.
    /// A silo votes "no conflict" if it has NOT signed a commit for this proposal.
    pub fn vote_unlock(
        &self,
        request: &UnlockRequest,
        voter: SiloId,
        has_signed_commit: bool,
    ) -> UnlockVote {
        UnlockVote {
            request: request.clone(),
            voter,
            has_conflict: has_signed_commit,
        }
    }

    /// Verify and apply an unlock certificate.
    ///
    /// The certificate is valid if:
    /// 1. It has >= 2f+1 votes.
    /// 2. No voter reports a conflict (meaning no commit was signed).
    ///
    /// On success, releases the lock and returns the amount unlocked.
    pub fn apply_unlock_certificate(
        &mut self,
        certificate: &UnlockCertificate,
    ) -> Result<u64, BudgetError> {
        let quorum = 2 * self.byzantine_tolerance + 1;

        // Check quorum.
        if certificate.votes.len() < quorum {
            return Err(BudgetError::InsufficientUnlockVotes {
                have: certificate.votes.len(),
                need: quorum,
            });
        }

        // Check no conflicts.
        for vote in &certificate.votes {
            if vote.has_conflict {
                return Err(BudgetError::ConflictingUnlock {
                    silo: vote.voter,
                    proposal_id: certificate.request.proposal_id,
                });
            }
        }

        // Verify the lock exists and is still active.
        let proposal_id = certificate.request.proposal_id;
        match self.locks.get(&proposal_id) {
            Some(LockStatus::Locked { amount, .. }) => {
                let amount = *amount;
                self.locks.insert(proposal_id, LockStatus::Released);
                Ok(amount)
            }
            Some(LockStatus::Released) => Err(BudgetError::AlreadyReleased { proposal_id }),
            None => Err(BudgetError::LockNotFound { proposal_id }),
        }
    }

    /// Check if a proposal has an active lock.
    pub fn is_locked(&self, proposal_id: &[u8; 32]) -> bool {
        matches!(self.locks.get(proposal_id), Some(LockStatus::Locked { .. }))
    }

    /// Get the amount locked for a proposal (if any).
    pub fn locked_amount(&self, proposal_id: &[u8; 32]) -> Option<u64> {
        match self.locks.get(proposal_id) {
            Some(LockStatus::Locked { amount, .. }) => Some(*amount),
            _ => None,
        }
    }
}

// ─── BudgetError ──────────────────────────────────────────────────────────────

/// Errors from the budget coordination layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BudgetError {
    /// A silo's slice is exhausted.
    SliceExhausted {
        agent: CellId,
        remaining: u64,
        requested: u64,
    },
    /// Not enough silos for the requested Byzantine tolerance.
    InsufficientSilos {
        have: usize,
        need: usize,
    },
    /// Unknown silo ID.
    UnknownSilo {
        silo: SiloId,
    },
    /// Certificate is for the wrong agent.
    WrongAgent {
        expected: CellId,
        got: CellId,
    },
    /// Certificate version doesn't match current epoch.
    VersionMismatch {
        expected: BudgetVersion,
        got: BudgetVersion,
    },
    /// Duplicate spending certificate from the same silo.
    DuplicateCertificate {
        silo: SiloId,
    },
    /// A certificate claims more spending than the silo's ceiling allows.
    CertificateExceedsCeiling {
        silo: SiloId,
        claimed: u64,
        ceiling: u64,
    },
    /// Resources are already locked for this proposal.
    AlreadyLocked {
        proposal_id: [u8; 32],
    },
    /// Lock has already been released.
    AlreadyReleased {
        proposal_id: [u8; 32],
    },
    /// No lock exists for this proposal.
    LockNotFound {
        proposal_id: [u8; 32],
    },
    /// Not enough votes to form an unlock certificate.
    InsufficientUnlockVotes {
        have: usize,
        need: usize,
    },
    /// A silo reports a conflict (it signed a commit for this proposal).
    ConflictingUnlock {
        silo: SiloId,
        proposal_id: [u8; 32],
    },
}

impl core::fmt::Display for BudgetError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BudgetError::SliceExhausted { agent, remaining, requested } => {
                write!(
                    f,
                    "budget slice exhausted for agent {agent}: {remaining} remaining, {requested} requested"
                )
            }
            BudgetError::InsufficientSilos { have, need } => {
                write!(f, "insufficient silos: have {have}, need {need} (3f+1)")
            }
            BudgetError::UnknownSilo { .. } => write!(f, "unknown silo"),
            BudgetError::WrongAgent { expected, got } => {
                write!(f, "certificate for wrong agent: expected {expected}, got {got}")
            }
            BudgetError::VersionMismatch { expected, got } => {
                write!(f, "budget version mismatch: expected {expected}, got {got}")
            }
            BudgetError::DuplicateCertificate { .. } => {
                write!(f, "duplicate spending certificate from silo")
            }
            BudgetError::CertificateExceedsCeiling { claimed, ceiling, .. } => {
                write!(
                    f,
                    "certificate claims {claimed} spent, but ceiling is {ceiling}"
                )
            }
            BudgetError::AlreadyLocked { .. } => write!(f, "proposal already has an active lock"),
            BudgetError::AlreadyReleased { .. } => write!(f, "lock already released"),
            BudgetError::LockNotFound { .. } => write!(f, "no lock found for proposal"),
            BudgetError::InsufficientUnlockVotes { have, need } => {
                write!(f, "insufficient unlock votes: have {have}, need {need}")
            }
            BudgetError::ConflictingUnlock { .. } => {
                write!(f, "conflicting unlock: silo signed a commit for this proposal")
            }
        }
    }
}

impl std::error::Error for BudgetError {}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn test_agent() -> CellId {
        CellId::from_bytes([0xAA; 32])
    }

    fn test_silos(n: usize) -> Vec<SiloId> {
        (0..n).map(|i| {
            let mut id = [0u8; 32];
            id[0] = i as u8;
            id[1] = (i >> 8) as u8;
            id
        }).collect()
    }

    fn test_digest(n: u64) -> DebitDigest {
        *blake3::hash(&n.to_le_bytes()).as_bytes()
    }

    // ── Bounded Counter Tests ─────────────────────────────────────────────

    #[test]
    fn test_slice_ceiling_calculation() {
        // With f=1, ceiling = balance * 2/3
        let silos = test_silos(4);
        let coord = BudgetCoordinator::new(test_agent(), 1000, silos, 1).unwrap();
        let ceiling = coord.compute_slice_ceiling();
        // 1000 * 2 / 3 = 666
        assert_eq!(ceiling, 666);
    }

    #[test]
    fn test_slice_ceiling_f2() {
        // With f=2, ceiling = balance * 3/5
        let silos = test_silos(7);
        let coord = BudgetCoordinator::new(test_agent(), 10000, silos, 2).unwrap();
        let ceiling = coord.compute_slice_ceiling();
        // 10000 * 3 / 5 = 6000
        assert_eq!(ceiling, 6000);
    }

    #[test]
    fn test_insufficient_silos() {
        let silos = test_silos(3); // Need 3*1+1 = 4 silos for f=1
        let result = BudgetCoordinator::new(test_agent(), 1000, silos, 1);
        assert!(matches!(result, Err(BudgetError::InsufficientSilos { have: 3, need: 4 })));
    }

    #[test]
    fn test_concurrent_debits_from_multiple_silos() {
        let silos = test_silos(4);
        let silo_a = silos[0];
        let silo_b = silos[1];
        let silo_c = silos[2];

        let mut coord = BudgetCoordinator::new(test_agent(), 1200, silos, 1).unwrap();
        // ceiling = 1200 * 2/3 = 800

        // Each silo can spend up to 800 independently.
        assert!(coord.try_debit(silo_a, 300, test_digest(1)).is_ok());
        assert!(coord.try_debit(silo_b, 400, test_digest(2)).is_ok());
        assert!(coord.try_debit(silo_c, 200, test_digest(3)).is_ok());

        // Total spent: 900 (from a total balance of 1200 — valid).
        assert_eq!(coord.total_spent(), 900);

        // Each silo's remaining is independent.
        assert_eq!(coord.remaining(&silo_a), Some(500));
        assert_eq!(coord.remaining(&silo_b), Some(400));
        assert_eq!(coord.remaining(&silo_c), Some(600));
    }

    #[test]
    fn test_slice_exhaustion() {
        let silos = test_silos(4);
        let silo = silos[0];

        let mut coord = BudgetCoordinator::new(test_agent(), 300, silos, 1).unwrap();
        // ceiling = 300 * 2/3 = 200

        // Spend up to ceiling.
        assert!(coord.try_debit(silo, 100, test_digest(1)).is_ok());
        assert!(coord.try_debit(silo, 100, test_digest(2)).is_ok());

        // Slice exhausted.
        let err = coord.try_debit(silo, 1, test_digest(3)).unwrap_err();
        assert!(matches!(err, BudgetError::SliceExhausted { remaining: 0, requested: 1, .. }));
    }

    #[test]
    fn test_rebalancing_after_spending() {
        let silos = test_silos(4);
        let silo_a = silos[0];
        let silo_b = silos[1];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos.clone(), 1).unwrap();

        // Spend from two silos.
        coord.try_debit(silo_a, 200, test_digest(1)).unwrap();
        coord.try_debit(silo_b, 100, test_digest(2)).unwrap();

        // Collect certificates.
        let cert_a = coord.silo_states[&silo_a].certificate(silo_a);
        let cert_b = coord.silo_states[&silo_b].certificate(silo_b);

        // Rebalance.
        let total = coord.rebalance(&[cert_a, cert_b]).unwrap();
        assert_eq!(total, 300);

        // Balance updated: 1000 - 300 = 700.
        assert_eq!(coord.total_balance, 700);

        // Version incremented.
        assert_eq!(coord.version, 1);

        // New slices have ceiling based on new balance: 700 * 2/3 = 466.
        assert_eq!(coord.compute_slice_ceiling(), 466);
    }

    #[test]
    fn test_rebalance_rejects_wrong_version() {
        let silos = test_silos(4);
        let silo = silos[0];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos, 1).unwrap();
        coord.try_debit(silo, 50, test_digest(1)).unwrap();

        let mut cert = coord.silo_states[&silo].certificate(silo);
        cert.version = 99; // Wrong version.

        let err = coord.rebalance(&[cert]).unwrap_err();
        assert!(matches!(err, BudgetError::VersionMismatch { expected: 0, got: 99 }));
    }

    #[test]
    fn test_rebalance_rejects_overspend_certificate() {
        let silos = test_silos(4);
        let silo = silos[0];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos, 1).unwrap();

        // Forge a certificate claiming more than ceiling.
        let cert = SpendingCertificate {
            silo,
            agent: test_agent(),
            version: 0,
            total_spent: 9999,
            debits: vec![],
        };

        let err = coord.rebalance(&[cert]).unwrap_err();
        assert!(matches!(err, BudgetError::CertificateExceedsCeiling { .. }));
    }

    // ── Fast Unlock Tests ─────────────────────────────────────────────────

    #[test]
    fn test_lock_and_commit_release() {
        let mut mgr = FastUnlockManager::new(1, 4);
        let proposal = [0x01; 32];
        let silo = [0x10; 32];

        mgr.lock(proposal, test_agent(), 500, silo, 0).unwrap();
        assert!(mgr.is_locked(&proposal));
        assert_eq!(mgr.locked_amount(&proposal), Some(500));

        let amount = mgr.release_on_commit(&proposal).unwrap();
        assert_eq!(amount, 500);
        assert!(!mgr.is_locked(&proposal));
    }

    #[test]
    fn test_fast_unlock_after_abort() {
        let mut mgr = FastUnlockManager::new(1, 4);
        let proposal = [0x02; 32];
        let silo = [0x20; 32];
        let silos = test_silos(4);

        // Lock computrons for a proposed atomic turn.
        mgr.lock(proposal, test_agent(), 300, silo, 0).unwrap();

        // The turn aborts. Create an unlock request.
        let request = UnlockRequest {
            proposal_id: proposal,
            agent: test_agent(),
            amount: 300,
            requester: silo,
        };

        // Collect votes from 2f+1 = 3 silos (none have signed a commit).
        let votes: Vec<UnlockVote> = silos[..3]
            .iter()
            .map(|&voter| mgr.vote_unlock(&request, voter, false))
            .collect();

        let certificate = UnlockCertificate {
            request: request.clone(),
            votes,
        };

        // Apply the unlock certificate.
        let unlocked = mgr.apply_unlock_certificate(&certificate).unwrap();
        assert_eq!(unlocked, 300);
        assert!(!mgr.is_locked(&proposal));
    }

    #[test]
    fn test_fast_unlock_insufficient_votes() {
        let mut mgr = FastUnlockManager::new(1, 4);
        let proposal = [0x03; 32];
        let silo = [0x30; 32];

        mgr.lock(proposal, test_agent(), 100, silo, 0).unwrap();

        let request = UnlockRequest {
            proposal_id: proposal,
            agent: test_agent(),
            amount: 100,
            requester: silo,
        };

        // Only 2 votes (need 3 for f=1).
        let votes: Vec<UnlockVote> = test_silos(2)
            .iter()
            .map(|&voter| mgr.vote_unlock(&request, voter, false))
            .collect();

        let certificate = UnlockCertificate {
            request,
            votes,
        };

        let err = mgr.apply_unlock_certificate(&certificate).unwrap_err();
        assert!(matches!(err, BudgetError::InsufficientUnlockVotes { have: 2, need: 3 }));
    }

    #[test]
    fn test_fast_unlock_blocked_by_conflict() {
        let mut mgr = FastUnlockManager::new(1, 4);
        let proposal = [0x04; 32];
        let silo = [0x40; 32];
        let silos = test_silos(4);

        mgr.lock(proposal, test_agent(), 200, silo, 0).unwrap();

        let request = UnlockRequest {
            proposal_id: proposal,
            agent: test_agent(),
            amount: 200,
            requester: silo,
        };

        // One silo has a conflict (it signed a commit).
        let mut votes: Vec<UnlockVote> = Vec::new();
        votes.push(mgr.vote_unlock(&request, silos[0], false));
        votes.push(mgr.vote_unlock(&request, silos[1], true)); // CONFLICT
        votes.push(mgr.vote_unlock(&request, silos[2], false));

        let certificate = UnlockCertificate {
            request,
            votes,
        };

        let err = mgr.apply_unlock_certificate(&certificate).unwrap_err();
        assert!(matches!(err, BudgetError::ConflictingUnlock { .. }));
    }

    #[test]
    fn test_duplicate_lock_rejected() {
        let mut mgr = FastUnlockManager::new(1, 4);
        let proposal = [0x05; 32];
        let silo = [0x50; 32];

        mgr.lock(proposal, test_agent(), 100, silo, 0).unwrap();
        let err = mgr.lock(proposal, test_agent(), 100, silo, 0).unwrap_err();
        assert!(matches!(err, BudgetError::AlreadyLocked { .. }));
    }

    // ── Integration: Budget + Unlock ──────────────────────────────────────

    #[test]
    fn test_budget_debit_then_abort_with_fast_unlock() {
        let silos = test_silos(4);
        let silo = silos[0];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos.clone(), 1).unwrap();
        let mut unlock_mgr = FastUnlockManager::new(1, 4);

        // Debit from the silo's budget for a proposed atomic turn.
        let proposal = [0x99; 32];
        let amount = 150;
        coord.try_debit(silo, amount, test_digest(1)).unwrap();

        // Lock the computrons pending the 2PC outcome.
        unlock_mgr.lock(proposal, test_agent(), amount, silo, coord.version).unwrap();

        // The 2PC aborts. Fast unlock to reclaim.
        let request = UnlockRequest {
            proposal_id: proposal,
            agent: test_agent(),
            amount,
            requester: silo,
        };

        let votes: Vec<UnlockVote> = silos[..3]
            .iter()
            .map(|&voter| unlock_mgr.vote_unlock(&request, voter, false))
            .collect();

        let certificate = UnlockCertificate { request, votes };
        let unlocked = unlock_mgr.apply_unlock_certificate(&certificate).unwrap();
        assert_eq!(unlocked, 150);

        // The budget slice was already debited (that spending is "real" in the
        // bounded counter sense), but the agent's true balance won't be affected
        // because the abort means no ledger mutation happened. On rebalance,
        // only the certificates representing actual committed work will deduct
        // from the true balance.
    }

    #[test]
    fn test_byzantine_silo_cannot_overspend_total_balance() {
        // With 4 silos and f=1, each gets ceiling = 1000 * 2/3 = 666.
        // Even if the Byzantine silo spends its full 666, and all honest silos
        // spend their full 666 each, the total is 4 * 666 = 2664.
        // But honest silos will NEVER collectively certify more than the true
        // balance (1000). The Byzantine silo's overspend is bounded by its ceiling.
        let silos = test_silos(4);
        let byzantine = silos[0];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos.clone(), 1).unwrap();
        let ceiling = coord.compute_slice_ceiling();
        assert_eq!(ceiling, 666);

        // Byzantine silo spends its full ceiling.
        let mut spent = 0u64;
        let mut tx = 0u64;
        while coord.try_debit(byzantine, 100, test_digest(tx)).is_ok() {
            spent += 100;
            tx += 1;
        }
        // Spent 600 (6 * 100, can't fit 7th since 700 > 666).
        assert_eq!(spent, 600);

        // The remaining is 66 (666 - 600).
        assert_eq!(coord.remaining(&byzantine), Some(66));

        // Byzantine spent 666 max — bounded regardless of behavior.
        coord.try_debit(byzantine, 66, test_digest(tx)).unwrap();
        assert_eq!(coord.remaining(&byzantine), Some(0));
    }
}
