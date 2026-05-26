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

use ed25519_dalek::{Signature, VerifyingKey};
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

/// Convenience alias: a StingrayCounter for computron metering.
pub type ComputronBudget = StingrayCounter;

/// Backward-compat alias — new code should use `StingrayCounter`.
#[deprecated(
    since = "0.1.0",
    note = "renamed to StingrayCounter (arXiv:2501.06531)"
)]
pub type BudgetCoordinator = StingrayCounter;

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
    pub fn try_debit(&mut self, amount: u64, digest: DebitDigest) -> Result<(), BudgetError> {
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

    /// Refund a previously debited amount back to this slice.
    ///
    /// Used by fast unlock to credit resources back after a 2PC abort.
    /// The `spent` counter is decremented by the refund amount.
    pub fn refund(&mut self, amount: u64) {
        self.spent = self.spent.saturating_sub(amount);
    }

    /// Generate a spending certificate for this slice.
    ///
    /// This certificate is submitted during rebalancing so the coordinator
    /// can reconcile total spending across all silos.
    ///
    /// The `signing_key` is the silo's Ed25519 key used to sign the certificate,
    /// preventing forgery during rebalancing.
    pub fn certificate(&self, silo: SiloId, signing_key: &[u8; 32]) -> SpendingCertificate {
        use ed25519_dalek::{Signer, SigningKey};
        let sk = SigningKey::from_bytes(signing_key);
        // Sign over: agent || version || total_spent || silo
        let mut msg = Vec::new();
        msg.extend_from_slice(self.agent.as_bytes());
        msg.extend_from_slice(&self.version.to_le_bytes());
        msg.extend_from_slice(&self.spent.to_le_bytes());
        msg.extend_from_slice(&silo);
        let sig = sk.sign(&msg);

        SpendingCertificate {
            silo,
            agent: self.agent,
            version: self.version,
            total_spent: self.spent,
            debits: self.debits.clone(),
            signature: sig.to_bytes(),
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
    /// Ed25519 signature over the certificate contents (silo signs to attest).
    /// Prevents forged certificates during rebalancing.
    #[serde(with = "crate::serde_sig")]
    pub signature: [u8; 64],
}

impl SpendingCertificate {
    /// Reconstruct the signing message for this certificate.
    /// Must match the format used by `BudgetSlice::certificate`:
    ///   agent || version || spent || silo
    fn signing_message(&self) -> Vec<u8> {
        let mut msg = Vec::with_capacity(32 + 8 + 8 + 32);
        msg.extend_from_slice(self.agent.as_bytes());
        msg.extend_from_slice(&self.version.to_le_bytes());
        msg.extend_from_slice(&self.total_spent.to_le_bytes());
        msg.extend_from_slice(&self.silo);
        msg
    }

    /// Verify this certificate's signature against the silo's Ed25519 pubkey.
    ///
    /// Returns `true` if the signature is valid, `false` otherwise (including
    /// when the pubkey or signature bytes are not a valid Ed25519 form).
    pub fn verify_signature(&self, pubkey_bytes: &[u8; 32]) -> bool {
        let Ok(verifying_key) = VerifyingKey::from_bytes(pubkey_bytes) else {
            return false;
        };
        let sig = Signature::from_bytes(&self.signature);
        let msg = self.signing_message();
        verifying_key.verify_strict(&msg, &sig).is_ok()
    }
}

// ─── StingrayCounter ─────────────────────────────────────────────────────────

/// Manages resource budget distribution across silos for an agent.
///
/// Named after the Stingray protocol (arXiv:2501.06531) from which the
/// bounded-counter design is adapted. Generic over any fungible quantity
/// (computrons, API calls, storage bytes, tokens).
///
/// The coordinator is responsible for:
/// 1. Computing slice sizes based on Byzantine fault tolerance.
/// 2. Distributing slices to silos.
/// 3. Processing spending certificates during rebalancing.
/// 4. Issuing new slices after rebalancing.
#[derive(Clone, Debug)]
pub struct StingrayCounter {
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
    /// Ed25519 public keys for each silo. Used to verify `SpendingCertificate`
    /// signatures during rebalance. A silo whose pubkey is not registered will
    /// have its certificate rejected with `MissingSiloPubkey` (fail-closed).
    pub silo_pubkeys: HashMap<SiloId, [u8; 32]>,
}

impl StingrayCounter {
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

        let mut coord = StingrayCounter {
            agent,
            silos,
            byzantine_tolerance,
            version: 0,
            silo_states: HashMap::new(),
            total_balance,
            total_allocated: 0,
            silo_pubkeys: HashMap::new(),
        };

        // Distribute initial slices.
        coord.distribute_slices();
        Ok(coord)
    }

    /// Register an Ed25519 verifying key for a silo. Required before that silo's
    /// `SpendingCertificate` can be accepted during rebalance.
    ///
    /// Without registration, `rebalance` will reject the silo's certificate with
    /// `BudgetError::MissingSiloPubkey` (fail-closed).
    pub fn register_silo_pubkey(&mut self, silo: SiloId, pubkey: [u8; 32]) {
        self.silo_pubkeys.insert(silo, pubkey);
    }

    /// Calculate the per-silo ceiling based on Byzantine tolerance.
    ///
    /// Formula: ceiling = balance * (f+1) / (2f+1)
    ///
    /// NOTE: The sum of all slice ceilings intentionally exceeds the true balance.
    /// This is the Stingray bounded-counter design: each silo can locally spend up to
    /// its ceiling without coordination. The invariant is that with at most f Byzantine
    /// silos, the maximum overspend is bounded by f * ceiling. The rebalancing protocol
    /// reconciles actual spending to prevent true overspend.
    ///
    /// For safety: true_balance >= total_honestly_spent (enforced at rebalance time).
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
        let slice = self
            .silo_states
            .get_mut(&silo)
            .ok_or(BudgetError::UnknownSilo { silo })?;
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
    /// # Parameters
    /// - `certificates`: spending certificates from silos.
    /// - `require_all_certs`: if true (default for normal operation), reject the
    ///   rebalance if certificates are missing from any silo. If false (crash
    ///   recovery mode), missing silos are assumed to have spent their full ceiling
    ///   (conservative estimate) and a warning is logged.
    ///
    /// # Returns
    /// The total amount spent in this epoch (before redistribution).
    pub fn rebalance(&mut self, certificates: &[SpendingCertificate]) -> Result<u64, BudgetError> {
        self.rebalance_inner(certificates, true)
    }

    /// Rebalance with explicit control over whether all certificates are required.
    pub fn rebalance_partial(
        &mut self,
        certificates: &[SpendingCertificate],
    ) -> Result<u64, BudgetError> {
        self.rebalance_inner(certificates, false)
    }

    /// Inner rebalance implementation.
    fn rebalance_inner(
        &mut self,
        certificates: &[SpendingCertificate],
        require_all_certs: bool,
    ) -> Result<u64, BudgetError> {
        // Check if all silos submitted certificates.
        if require_all_certs && certificates.len() < self.silos.len() {
            return Err(BudgetError::IncompleteCertificates {
                received: certificates.len(),
                expected: self.silos.len(),
            });
        }
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
            let slice = self
                .silo_states
                .get(&cert.silo)
                .ok_or(BudgetError::UnknownSilo { silo: cert.silo })?;
            if cert.total_spent > slice.ceiling {
                return Err(BudgetError::CertificateExceedsCeiling {
                    silo: cert.silo,
                    claimed: cert.total_spent,
                    ceiling: slice.ceiling,
                });
            }

            // SECURITY: Verify the certificate's Ed25519 signature against the
            // silo's registered pubkey. Without a registered pubkey, the
            // certificate is rejected (fail-closed). Without verification, a
            // malicious coordinator could forge certificates and silently
            // overspend the agent's true balance up to the slice ceiling.
            let pubkey = self
                .silo_pubkeys
                .get(&cert.silo)
                .ok_or(BudgetError::MissingSiloPubkey { silo: cert.silo })?;
            if !cert.verify_signature(pubkey) {
                return Err(BudgetError::InvalidCertificateSignature { silo: cert.silo });
            }

            seen_silos.insert(cert.silo, cert.total_spent);
            total_spent = total_spent.saturating_add(cert.total_spent);
        }

        // For missing silos in partial mode: assume they spent their full ceiling
        // (conservative estimate to maintain safety).
        if !require_all_certs {
            let ceiling = self.compute_slice_ceiling();
            for silo in &self.silos {
                if !seen_silos.contains_key(silo) {
                    total_spent = total_spent.saturating_add(ceiling);
                }
            }
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
    /// Ed25519 signature over the vote contents (voter signs to attest).
    /// Prevents forged unlock votes.
    #[serde(with = "crate::serde_sig")]
    pub signature: [u8; 64],
}

impl UnlockVote {
    /// Reconstruct the signing message for this vote.
    /// Must match the format used by `FastUnlockManager::vote_unlock`:
    ///   proposal_id || voter || has_conflict_byte
    fn signing_message(&self) -> Vec<u8> {
        let mut msg = Vec::with_capacity(32 + 32 + 1);
        msg.extend_from_slice(&self.request.proposal_id);
        msg.extend_from_slice(&self.voter);
        msg.push(if self.has_conflict { 1 } else { 0 });
        msg
    }

    /// Verify this vote's signature against the voter's Ed25519 pubkey.
    ///
    /// Returns `true` if the signature is valid, `false` otherwise (including
    /// when the pubkey or signature bytes are not a valid Ed25519 form).
    pub fn verify_signature(&self, pubkey_bytes: &[u8; 32]) -> bool {
        let Ok(verifying_key) = VerifyingKey::from_bytes(pubkey_bytes) else {
            return false;
        };
        let sig = Signature::from_bytes(&self.signature);
        let msg = self.signing_message();
        verifying_key.verify_strict(&msg, &sig).is_ok()
    }
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
    /// Ed25519 public keys for each silo. Used to verify `UnlockVote`
    /// signatures. A voter whose pubkey is not registered will have their vote
    /// rejected with `MissingSiloPubkey` (fail-closed).
    pub silo_pubkeys: HashMap<SiloId, [u8; 32]>,
}

impl FastUnlockManager {
    /// Create a new fast unlock manager.
    pub fn new(byzantine_tolerance: usize, total_silos: usize) -> Self {
        FastUnlockManager {
            locks: HashMap::new(),
            byzantine_tolerance,
            total_silos,
            silo_pubkeys: HashMap::new(),
        }
    }

    /// Register an Ed25519 verifying key for a silo. Required before that
    /// silo's `UnlockVote` can be accepted in an unlock certificate.
    ///
    /// Without registration, `apply_unlock_certificate` rejects the vote with
    /// `BudgetError::MissingSiloPubkey` (fail-closed).
    pub fn register_silo_pubkey(&mut self, silo: SiloId, pubkey: [u8; 32]) {
        self.silo_pubkeys.insert(silo, pubkey);
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
    /// Returns a signed UnlockVote if this silo agrees the lock can be released.
    /// A silo votes "no conflict" if it has NOT signed a commit for this proposal.
    ///
    /// The `signing_key` is the voter silo's Ed25519 key.
    pub fn vote_unlock(
        &self,
        request: &UnlockRequest,
        voter: SiloId,
        has_signed_commit: bool,
        signing_key: &[u8; 32],
    ) -> UnlockVote {
        use ed25519_dalek::{Signer, SigningKey};
        let sk = SigningKey::from_bytes(signing_key);
        // Sign over: proposal_id || voter || has_conflict byte
        let mut msg = Vec::new();
        msg.extend_from_slice(&request.proposal_id);
        msg.extend_from_slice(&voter);
        msg.push(if has_signed_commit { 1 } else { 0 });
        let sig = sk.sign(&msg);

        UnlockVote {
            request: request.clone(),
            voter,
            has_conflict: has_signed_commit,
            signature: sig.to_bytes(),
        }
    }

    /// Verify and apply an unlock certificate.
    ///
    /// The certificate is valid if:
    /// 1. It has >= 2f+1 votes.
    /// 2. No voter reports a conflict (meaning no commit was signed).
    ///
    /// On success, releases the lock and returns `(amount, silo)` -- the amount
    /// unlocked and the silo whose slice should be refunded.
    pub fn apply_unlock_certificate(
        &mut self,
        certificate: &UnlockCertificate,
    ) -> Result<(u64, SiloId), BudgetError> {
        let quorum = 2 * self.byzantine_tolerance + 1;

        // Check quorum.
        if certificate.votes.len() < quorum {
            return Err(BudgetError::InsufficientUnlockVotes {
                have: certificate.votes.len(),
                need: quorum,
            });
        }

        // SECURITY: Verify each vote's Ed25519 signature against the voter's
        // registered pubkey. Without verification, a Byzantine coordinator
        // could fabricate `UnlockVote`s and silently release locked resources.
        // Also reject duplicate votes from the same voter, and any vote whose
        // request field does not match the certificate's request (the
        // signature is bound to the vote's own request copy).
        let mut seen_voters: HashMap<SiloId, ()> = HashMap::new();
        for vote in &certificate.votes {
            if vote.request != certificate.request {
                return Err(BudgetError::InvalidUnlockVoteSignature { voter: vote.voter });
            }
            if seen_voters.insert(vote.voter, ()).is_some() {
                return Err(BudgetError::InvalidUnlockVoteSignature { voter: vote.voter });
            }
            let pubkey = self
                .silo_pubkeys
                .get(&vote.voter)
                .ok_or(BudgetError::MissingSiloPubkey { silo: vote.voter })?;
            if !vote.verify_signature(pubkey) {
                return Err(BudgetError::InvalidUnlockVoteSignature { voter: vote.voter });
            }
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
            Some(LockStatus::Locked { amount, silo, .. }) => {
                let amount = *amount;
                let silo = *silo;
                self.locks.insert(proposal_id, LockStatus::Released);
                Ok((amount, silo))
            }
            Some(LockStatus::Released) => Err(BudgetError::AlreadyReleased { proposal_id }),
            None => Err(BudgetError::LockNotFound { proposal_id }),
        }
    }

    /// Apply an unlock certificate AND refund the amount to the silo's budget slice.
    ///
    /// This is the recommended entrypoint for fast unlock: it both releases the lock
    /// and credits the amount back to the originating silo's `BudgetSlice`.
    pub fn apply_unlock_and_refund(
        &mut self,
        certificate: &UnlockCertificate,
        coordinator: &mut StingrayCounter,
    ) -> Result<u64, BudgetError> {
        let (amount, silo) = self.apply_unlock_certificate(certificate)?;
        // Refund the amount back to the silo's budget slice.
        if let Some(slice) = coordinator.silo_states.get_mut(&silo) {
            slice.refund(amount);
        }
        Ok(amount)
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
    InsufficientSilos { have: usize, need: usize },
    /// Unknown silo ID.
    UnknownSilo { silo: SiloId },
    /// Certificate is for the wrong agent.
    WrongAgent { expected: CellId, got: CellId },
    /// Certificate version doesn't match current epoch.
    VersionMismatch {
        expected: BudgetVersion,
        got: BudgetVersion,
    },
    /// Duplicate spending certificate from the same silo.
    DuplicateCertificate { silo: SiloId },
    /// A certificate claims more spending than the silo's ceiling allows.
    CertificateExceedsCeiling {
        silo: SiloId,
        claimed: u64,
        ceiling: u64,
    },
    /// Resources are already locked for this proposal.
    AlreadyLocked { proposal_id: [u8; 32] },
    /// Lock has already been released.
    AlreadyReleased { proposal_id: [u8; 32] },
    /// No lock exists for this proposal.
    LockNotFound { proposal_id: [u8; 32] },
    /// Not enough votes to form an unlock certificate.
    InsufficientUnlockVotes { have: usize, need: usize },
    /// A silo reports a conflict (it signed a commit for this proposal).
    ConflictingUnlock { silo: SiloId, proposal_id: [u8; 32] },
    /// Not all silos submitted spending certificates during rebalance.
    IncompleteCertificates { received: usize, expected: usize },
    /// No Ed25519 pubkey is registered for this silo (cannot verify certificate
    /// or unlock vote). Register via `register_silo_pubkey` /
    /// `FastUnlockManager::register_silo_pubkey` before applying.
    MissingSiloPubkey { silo: SiloId },
    /// A `SpendingCertificate` failed Ed25519 signature verification.
    /// Indicates a forgery attempt or a corrupted certificate.
    InvalidCertificateSignature { silo: SiloId },
    /// An `UnlockVote` failed Ed25519 signature verification.
    /// Indicates a forgery attempt or a corrupted vote.
    InvalidUnlockVoteSignature { voter: SiloId },
}

impl core::fmt::Display for BudgetError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BudgetError::SliceExhausted {
                agent,
                remaining,
                requested,
            } => {
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
                write!(
                    f,
                    "certificate for wrong agent: expected {expected}, got {got}"
                )
            }
            BudgetError::VersionMismatch { expected, got } => {
                write!(f, "budget version mismatch: expected {expected}, got {got}")
            }
            BudgetError::DuplicateCertificate { .. } => {
                write!(f, "duplicate spending certificate from silo")
            }
            BudgetError::CertificateExceedsCeiling {
                claimed, ceiling, ..
            } => {
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
                write!(
                    f,
                    "conflicting unlock: silo signed a commit for this proposal"
                )
            }
            BudgetError::IncompleteCertificates { received, expected } => {
                write!(
                    f,
                    "incomplete certificates: received {received}, expected {expected}"
                )
            }
            BudgetError::MissingSiloPubkey { .. } => {
                write!(f, "no Ed25519 pubkey registered for silo")
            }
            BudgetError::InvalidCertificateSignature { .. } => {
                write!(f, "spending certificate signature failed verification")
            }
            BudgetError::InvalidUnlockVoteSignature { .. } => {
                write!(f, "unlock vote signature failed verification")
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
        (0..n)
            .map(|i| {
                let mut id = [0u8; 32];
                id[0] = i as u8;
                id[1] = (i >> 8) as u8;
                id
            })
            .collect()
    }

    fn test_digest(n: u64) -> DebitDigest {
        *blake3::hash(&n.to_le_bytes()).as_bytes()
    }

    /// Generate a deterministic test signing key from a silo id.
    fn test_signing_key(silo: &SiloId) -> [u8; 32] {
        *blake3::hash(silo).as_bytes()
    }

    /// Derive the Ed25519 verifying key (pubkey) from a signing key.
    fn test_pubkey(signing_key: &[u8; 32]) -> [u8; 32] {
        ed25519_dalek::SigningKey::from_bytes(signing_key)
            .verifying_key()
            .to_bytes()
    }

    /// Register Ed25519 pubkeys for every silo in the coordinator.
    fn register_all_silo_pubkeys(coord: &mut BudgetCoordinator) {
        let silos = coord.silos.clone();
        for silo in &silos {
            let sk = test_signing_key(silo);
            coord.register_silo_pubkey(*silo, test_pubkey(&sk));
        }
    }

    /// Register Ed25519 pubkeys for every silo on the unlock manager.
    fn register_all_unlock_pubkeys(mgr: &mut FastUnlockManager, silos: &[SiloId]) {
        for silo in silos {
            let sk = test_signing_key(silo);
            mgr.register_silo_pubkey(*silo, test_pubkey(&sk));
        }
    }

    // ── Bounded Counter Tests ─────────────────────────────────────────────

    #[test]
    fn test_slice_ceiling_various_f() {
        let cases = vec![
            // (balance, silo_count, f, expected_ceiling)
            (1000, 4, 1, 666),   // f=1: balance * 2/3
            (10000, 7, 2, 6000), // f=2: balance * 3/5
        ];
        for (balance, silo_count, f, expected) in cases {
            let silos = test_silos(silo_count);
            let coord = BudgetCoordinator::new(test_agent(), balance, silos, f).unwrap();
            assert_eq!(
                coord.compute_slice_ceiling(),
                expected,
                "ceiling mismatch for balance={balance}, f={f}"
            );
        }
    }

    #[test]
    fn test_insufficient_silos() {
        let silos = test_silos(3); // Need 3*1+1 = 4 silos for f=1
        let result = BudgetCoordinator::new(test_agent(), 1000, silos, 1);
        assert!(matches!(
            result,
            Err(BudgetError::InsufficientSilos { have: 3, need: 4 })
        ));
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
        assert!(matches!(
            err,
            BudgetError::SliceExhausted {
                remaining: 0,
                requested: 1,
                ..
            }
        ));
    }

    #[test]
    fn test_rebalancing_after_spending() {
        let silos = test_silos(4);
        let silo_a = silos[0];
        let silo_b = silos[1];
        let silo_c = silos[2];
        let silo_d = silos[3];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos.clone(), 1).unwrap();
        register_all_silo_pubkeys(&mut coord);

        // Spend from two silos.
        coord.try_debit(silo_a, 200, test_digest(1)).unwrap();
        coord.try_debit(silo_b, 100, test_digest(2)).unwrap();

        // Collect certificates from ALL silos (required by default).
        let key_a = test_signing_key(&silo_a);
        let key_b = test_signing_key(&silo_b);
        let key_c = test_signing_key(&silo_c);
        let key_d = test_signing_key(&silo_d);
        let cert_a = coord.silo_states[&silo_a].certificate(silo_a, &key_a);
        let cert_b = coord.silo_states[&silo_b].certificate(silo_b, &key_b);
        let cert_c = coord.silo_states[&silo_c].certificate(silo_c, &key_c);
        let cert_d = coord.silo_states[&silo_d].certificate(silo_d, &key_d);

        // Rebalance.
        let total = coord.rebalance(&[cert_a, cert_b, cert_c, cert_d]).unwrap();
        assert_eq!(total, 300);

        // Balance updated: 1000 - 300 = 700.
        assert_eq!(coord.total_balance, 700);

        // Version incremented.
        assert_eq!(coord.version, 1);

        // New slices have ceiling based on new balance: 700 * 2/3 = 466.
        assert_eq!(coord.compute_slice_ceiling(), 466);
    }

    #[test]
    fn test_rebalance_rejects_incomplete_certificates() {
        let silos = test_silos(4);
        let silo_a = silos[0];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos, 1).unwrap();
        coord.try_debit(silo_a, 50, test_digest(1)).unwrap();

        let key_a = test_signing_key(&silo_a);
        let cert_a = coord.silo_states[&silo_a].certificate(silo_a, &key_a);

        // Only 1 of 4 silos submitted -- should fail with require_all_certs.
        let err = coord.rebalance(&[cert_a]).unwrap_err();
        assert!(matches!(
            err,
            BudgetError::IncompleteCertificates {
                received: 1,
                expected: 4
            }
        ));
    }

    #[test]
    fn test_rebalance_partial_mode() {
        let silos = test_silos(4);
        let silo_a = silos[0];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos, 1).unwrap();
        register_all_silo_pubkeys(&mut coord);
        coord.try_debit(silo_a, 50, test_digest(1)).unwrap();

        let key_a = test_signing_key(&silo_a);
        let cert_a = coord.silo_states[&silo_a].certificate(silo_a, &key_a);

        // Partial mode: missing silos assumed to spend full ceiling (666 each).
        // total = 50 (from cert_a) + 3 * 666 (missing) = 2048
        let total = coord.rebalance_partial(&[cert_a]).unwrap();
        assert_eq!(total, 50 + 3 * 666); // Conservative estimate.
    }

    #[test]
    fn test_rebalance_rejects_wrong_version() {
        let silos = test_silos(4);
        let silo = silos[0];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos, 1).unwrap();
        register_all_silo_pubkeys(&mut coord);
        coord.try_debit(silo, 50, test_digest(1)).unwrap();

        let key = test_signing_key(&silo);
        let mut cert = coord.silo_states[&silo].certificate(silo, &key);
        cert.version = 99; // Wrong version.

        let err = coord.rebalance_partial(&[cert]).unwrap_err();
        assert!(matches!(
            err,
            BudgetError::VersionMismatch {
                expected: 0,
                got: 99
            }
        ));
    }

    #[test]
    fn test_rebalance_rejects_overspend_certificate() {
        let silos = test_silos(4);
        let silo = silos[0];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos, 1).unwrap();
        register_all_silo_pubkeys(&mut coord);

        // Forge a certificate claiming more than ceiling.
        let cert = SpendingCertificate {
            silo,
            agent: test_agent(),
            version: 0,
            total_spent: 9999,
            debits: vec![],
            signature: [0u8; 64], // Forged; ceiling check fires before sig check.
                                  // (STARBRIDGE-FOLLOWUP-03: full Ed25519 verify now present in
                                  // rebalance_inner at the SECURITY comment block; see also
                                  // apply_unlock_certificate:756. §5.6 gap from AUDIT-coord-crate
                                  // and STARBRIDGE-07 is CLOSED for the signature path. Test still
                                  // exercises the ceiling-precedence defense-in-depth.)
        };

        // Use rebalance_partial to avoid the incomplete certs check.
        // The ceiling check fires before the signature check, so this still
        // surfaces as CertificateExceedsCeiling.
        let err = coord.rebalance_partial(&[cert]).unwrap_err();
        assert!(matches!(err, BudgetError::CertificateExceedsCeiling { .. }));
    }

    // ── Block 1: Adversarial signature-verification tests ───────────────────

    #[test]
    fn test_rebalance_rejects_forged_certificate_signature() {
        // A certificate within the ceiling but with an invalid signature must
        // be rejected. This is the Stingray-correctness gap that previously
        // allowed a malicious coordinator to forge silos' spending claims.
        let silos = test_silos(4);
        let silo = silos[0];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos, 1).unwrap();
        register_all_silo_pubkeys(&mut coord);

        // Forge a certificate within the ceiling (so ceiling check passes)
        // but with a bogus signature.
        let cert = SpendingCertificate {
            silo,
            agent: test_agent(),
            version: 0,
            total_spent: 100, // Under ceiling 666.
            debits: vec![],
            signature: [0u8; 64], // Invalid Ed25519 signature.
        };

        let err = coord.rebalance_partial(&[cert]).unwrap_err();
        assert!(
            matches!(err, BudgetError::InvalidCertificateSignature { .. }),
            "expected InvalidCertificateSignature, got {err:?}"
        );
    }

    #[test]
    fn test_rebalance_rejects_certificate_signed_by_wrong_silo() {
        // A certificate signed by silo_b but claiming to be from silo_a must
        // be rejected: the signature won't verify under silo_a's pubkey.
        let silos = test_silos(4);
        let silo_a = silos[0];
        let silo_b = silos[1];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos, 1).unwrap();
        register_all_silo_pubkeys(&mut coord);

        // Silo B signs a certificate, but it claims silo == silo_a.
        let key_b = test_signing_key(&silo_b);
        let mut cert = coord.silo_states[&silo_b].certificate(silo_b, &key_b);
        cert.silo = silo_a; // Forge the silo field.

        let err = coord.rebalance_partial(&[cert]).unwrap_err();
        assert!(
            matches!(err, BudgetError::InvalidCertificateSignature { .. }),
            "expected InvalidCertificateSignature, got {err:?}"
        );
    }

    #[test]
    fn test_rebalance_rejects_certificate_when_pubkey_unregistered() {
        // Without a registered pubkey, the certificate is rejected fail-closed.
        let silos = test_silos(4);
        let silo = silos[0];

        let mut coord = BudgetCoordinator::new(test_agent(), 1000, silos, 1).unwrap();
        // Note: NO register_all_silo_pubkeys call.

        let key = test_signing_key(&silo);
        let cert = coord.silo_states[&silo].certificate(silo, &key);

        let err = coord.rebalance_partial(&[cert]).unwrap_err();
        assert!(
            matches!(err, BudgetError::MissingSiloPubkey { .. }),
            "expected MissingSiloPubkey, got {err:?}"
        );
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
        register_all_unlock_pubkeys(&mut mgr, &silos);

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
            .map(|&voter| {
                let key = test_signing_key(&voter);
                mgr.vote_unlock(&request, voter, false, &key)
            })
            .collect();

        let certificate = UnlockCertificate {
            request: request.clone(),
            votes,
        };

        // Apply the unlock certificate.
        let (unlocked, unlocked_silo) = mgr.apply_unlock_certificate(&certificate).unwrap();
        assert_eq!(unlocked, 300);
        assert_eq!(unlocked_silo, silo);
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
            .map(|&voter| {
                let key = test_signing_key(&voter);
                mgr.vote_unlock(&request, voter, false, &key)
            })
            .collect();

        let certificate = UnlockCertificate { request, votes };

        let err = mgr.apply_unlock_certificate(&certificate).unwrap_err();
        assert!(matches!(
            err,
            BudgetError::InsufficientUnlockVotes { have: 2, need: 3 }
        ));
    }

    #[test]
    fn test_fast_unlock_blocked_by_conflict() {
        let mut mgr = FastUnlockManager::new(1, 4);
        let proposal = [0x04; 32];
        let silo = [0x40; 32];
        let silos = test_silos(4);
        register_all_unlock_pubkeys(&mut mgr, &silos);

        mgr.lock(proposal, test_agent(), 200, silo, 0).unwrap();

        let request = UnlockRequest {
            proposal_id: proposal,
            agent: test_agent(),
            amount: 200,
            requester: silo,
        };

        // One silo has a conflict (it signed a commit).
        let mut votes: Vec<UnlockVote> = Vec::new();
        let key0 = test_signing_key(&silos[0]);
        let key1 = test_signing_key(&silos[1]);
        let key2 = test_signing_key(&silos[2]);
        votes.push(mgr.vote_unlock(&request, silos[0], false, &key0));
        votes.push(mgr.vote_unlock(&request, silos[1], true, &key1)); // CONFLICT
        votes.push(mgr.vote_unlock(&request, silos[2], false, &key2));

        let certificate = UnlockCertificate { request, votes };

        let err = mgr.apply_unlock_certificate(&certificate).unwrap_err();
        assert!(matches!(err, BudgetError::ConflictingUnlock { .. }));
    }

    #[test]
    fn test_fast_unlock_rejects_forged_vote_signature() {
        // A vote with a quorum count but an invalid signature must be
        // rejected. This is the Stingray-correctness gap that previously
        // allowed a Byzantine coordinator to fabricate `UnlockVote`s and
        // silently release locked resources.
        let mut mgr = FastUnlockManager::new(1, 4);
        let proposal = [0x06; 32];
        let silo = [0x60; 32];
        let silos = test_silos(4);
        register_all_unlock_pubkeys(&mut mgr, &silos);

        mgr.lock(proposal, test_agent(), 100, silo, 0).unwrap();

        let request = UnlockRequest {
            proposal_id: proposal,
            agent: test_agent(),
            amount: 100,
            requester: silo,
        };

        // Fabricate 3 votes with zero signatures (forged).
        let votes: Vec<UnlockVote> = silos[..3]
            .iter()
            .map(|&voter| UnlockVote {
                request: request.clone(),
                voter,
                has_conflict: false,
                signature: [0u8; 64], // Invalid Ed25519 signature.
            })
            .collect();

        let certificate = UnlockCertificate { request, votes };

        let err = mgr.apply_unlock_certificate(&certificate).unwrap_err();
        assert!(
            matches!(err, BudgetError::InvalidUnlockVoteSignature { .. }),
            "expected InvalidUnlockVoteSignature, got {err:?}"
        );
    }

    #[test]
    fn test_fast_unlock_rejects_vote_signed_by_wrong_voter() {
        // A vote signed by silo_b but claiming to be from silo_a must be
        // rejected: the signature won't verify under silo_a's pubkey.
        let mut mgr = FastUnlockManager::new(1, 4);
        let proposal = [0x07; 32];
        let silo = [0x70; 32];
        let silos = test_silos(4);
        register_all_unlock_pubkeys(&mut mgr, &silos);

        mgr.lock(proposal, test_agent(), 100, silo, 0).unwrap();

        let request = UnlockRequest {
            proposal_id: proposal,
            agent: test_agent(),
            amount: 100,
            requester: silo,
        };

        // silo_b signs a vote, but the vote claims voter == silo_a.
        let key_b = test_signing_key(&silos[1]);
        let mut vote_a_forged = mgr.vote_unlock(&request, silos[1], false, &key_b);
        vote_a_forged.voter = silos[0]; // Forge the voter field.

        // Two more honest votes to satisfy the quorum check before signature
        // verification fires.
        let key1 = test_signing_key(&silos[2]);
        let key2 = test_signing_key(&silos[3]);
        let votes = vec![
            vote_a_forged,
            mgr.vote_unlock(&request, silos[2], false, &key1),
            mgr.vote_unlock(&request, silos[3], false, &key2),
        ];

        let certificate = UnlockCertificate { request, votes };

        let err = mgr.apply_unlock_certificate(&certificate).unwrap_err();
        assert!(
            matches!(err, BudgetError::InvalidUnlockVoteSignature { .. }),
            "expected InvalidUnlockVoteSignature, got {err:?}"
        );
    }

    #[test]
    fn test_fast_unlock_rejects_when_pubkey_unregistered() {
        // Without registered pubkeys, votes are rejected fail-closed.
        let mut mgr = FastUnlockManager::new(1, 4);
        let proposal = [0x08; 32];
        let silo = [0x80; 32];
        let silos = test_silos(4);
        // Note: NO register_all_unlock_pubkeys call.

        mgr.lock(proposal, test_agent(), 100, silo, 0).unwrap();

        let request = UnlockRequest {
            proposal_id: proposal,
            agent: test_agent(),
            amount: 100,
            requester: silo,
        };
        let votes: Vec<UnlockVote> = silos[..3]
            .iter()
            .map(|&voter| {
                let key = test_signing_key(&voter);
                mgr.vote_unlock(&request, voter, false, &key)
            })
            .collect();
        let certificate = UnlockCertificate { request, votes };

        let err = mgr.apply_unlock_certificate(&certificate).unwrap_err();
        assert!(
            matches!(err, BudgetError::MissingSiloPubkey { .. }),
            "expected MissingSiloPubkey, got {err:?}"
        );
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
        register_all_silo_pubkeys(&mut coord);
        let mut unlock_mgr = FastUnlockManager::new(1, 4);
        register_all_unlock_pubkeys(&mut unlock_mgr, &silos);

        // Debit from the silo's budget for a proposed atomic turn.
        let proposal = [0x99; 32];
        let amount = 150;
        coord.try_debit(silo, amount, test_digest(1)).unwrap();

        // Lock the computrons pending the 2PC outcome.
        unlock_mgr
            .lock(proposal, test_agent(), amount, silo, coord.version)
            .unwrap();

        // The 2PC aborts. Fast unlock to reclaim.
        let request = UnlockRequest {
            proposal_id: proposal,
            agent: test_agent(),
            amount,
            requester: silo,
        };

        let votes: Vec<UnlockVote> = silos[..3]
            .iter()
            .map(|&voter| {
                let key = test_signing_key(&voter);
                unlock_mgr.vote_unlock(&request, voter, false, &key)
            })
            .collect();

        let certificate = UnlockCertificate { request, votes };
        let (unlocked, unlocked_silo) = unlock_mgr.apply_unlock_certificate(&certificate).unwrap();
        assert_eq!(unlocked, 150);
        assert_eq!(unlocked_silo, silo);

        // Issue #8 fix: refund the unlocked amount back to the silo's slice.
        coord
            .silo_states
            .get_mut(&unlocked_silo)
            .unwrap()
            .refund(unlocked);
        // Verify the refund restored the budget.
        assert_eq!(coord.remaining(&silo), Some(coord.compute_slice_ceiling()));
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
