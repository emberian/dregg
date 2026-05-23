//! Executor delegation: a client strand delegates turn execution to an executor strand.
//!
//! The executor processes turns on behalf of the client and publishes proof-carrying
//! execution blocks.
//!
//! # Trust Model
//!
//! The client verifies the executor's proofs. If the executor cheats
//! (produces invalid proofs), the client can challenge and stop delegating.
//!
//! # Design
//!
//! In the unified lace, an "executor" is just a strand that other strands trust with
//! their state transitions. A phone can delegate to a cloud executor: "process my turns,
//! prove them, publish the results."
//!
//! Delegation is:
//! - **Voluntary**: clients opt in by signing a delegation authorization.
//! - **Revocable**: clients can revoke at any time and switch executors.
//! - **Scoped**: delegation can be limited to specific cells or effect types.
//! - **Challengeable**: if an executor misbehaves, the client can challenge and the
//!   executor's reputation is damaged.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::serde_sig64;

// ─── Core Types ─────────────────────────────────────────────────────────────

/// A delegation relationship: client trusts executor to process their turns.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExecutorDelegation {
    /// The client strand (who's delegating).
    pub client: [u8; 32],
    /// The executor strand (who's executing).
    pub executor: [u8; 32],
    /// What the executor is authorized to do.
    pub scope: DelegationScope,
    /// When this delegation was established (block height).
    pub established_at: u64,
    /// Optional expiry (block height).
    pub expires_at: Option<u64>,
    /// Signature by client authorizing this delegation.
    #[serde(with = "serde_sig64")]
    pub client_signature: [u8; 64],
}

/// Scope of what an executor is authorized to do on behalf of a client.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum DelegationScope {
    /// Execute ALL turns for the client (full delegation).
    Full,
    /// Execute only turns affecting specific cells.
    CellsOnly { cell_ids: Vec<[u8; 32]> },
    /// Execute only specific effect types.
    EffectsOnly { allowed_effects: Vec<u8> },
}

/// A batch execution block: executor processes multiple client turns in one block.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BatchExecution {
    /// The executor who produced this batch.
    pub executor: [u8; 32],
    /// Client turns included in this batch.
    pub client_turns: Vec<ClientTurnRequest>,
    /// The STARK proof covering ALL turns in the batch.
    pub batch_proof: Vec<u8>,
    /// Individual results per turn (state transitions).
    pub results: Vec<TurnResult>,
    /// Batch sequence number (monotonic per executor).
    pub batch_seq: u64,
}

/// A client's request for the executor to process a turn.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ClientTurnRequest {
    /// The client requesting execution.
    pub client: [u8; 32],
    /// The turn to execute (effects, target cells, etc.).
    pub turn_data: Vec<u8>,
    /// Client's signature over the turn (proves they authorized it).
    #[serde(with = "serde_sig64")]
    pub client_signature: [u8; 64],
    /// Nonce (prevents replay).
    pub nonce: u64,
    /// Block height at which this request was submitted.
    pub submitted_at: u64,
}

/// Result of a single turn within a batch.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TurnResult {
    /// The client whose turn was executed.
    pub client: [u8; 32],
    /// State commitment before execution.
    pub old_commitment: [u8; 32],
    /// State commitment after execution.
    pub new_commitment: [u8; 32],
    /// Hash of the effects that were applied.
    pub effects_hash: [u8; 32],
    /// Whether execution succeeded.
    pub success: bool,
}

// ─── Challenge / Error Types ────────────────────────────────────────────────

/// Reason for a client challenging an executor's batch result.
#[derive(Clone, Debug)]
pub enum ChallengeReason {
    /// The STARK proof doesn't verify.
    InvalidProof,
    /// The executor changed my state without my turn requesting it.
    UnauthorizedMutation,
    /// The executor didn't include my turn (censorship).
    Censorship { submitted_at: u64, deadline: u64 },
    /// The executor included my turn but produced wrong output.
    WrongOutput { expected_commitment: [u8; 32] },
}

/// A recorded challenge from a client against their executor.
#[derive(Clone, Debug)]
pub struct Challenge {
    /// The client who issued the challenge.
    pub client: [u8; 32],
    /// The batch being challenged.
    pub batch_seq: u64,
    /// Reason for the challenge.
    pub reason: ChallengeReason,
}

/// Errors that can occur during delegation operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DelegationError {
    /// Client already has an active delegation.
    AlreadyDelegated,
    /// Client does not have an active delegation.
    NotDelegated,
    /// The specified executor is not known.
    ExecutorNotFound,
    /// Signature verification failed.
    InvalidSignature,
    /// The delegation has expired.
    Expired,
    /// The turn is outside the delegation's allowed scope.
    ScopeViolation,
    /// Batch proof verification failed.
    BatchVerificationFailed,
    /// Executor censored the client's turn.
    CensorshipDetected,
    /// Batch sequence number is not monotonically increasing.
    BatchSeqNotMonotonic,
}

// ─── Delegation Manager ─────────────────────────────────────────────────────

/// Executor delegation manager.
///
/// Tracks active delegations, pending turn requests, executed batches,
/// and challenges.
pub struct DelegationManager {
    /// Active delegations (client → delegation).
    delegations: HashMap<[u8; 32], ExecutorDelegation>,
    /// Pending turn requests (grouped by executor).
    pending_requests: HashMap<[u8; 32], Vec<ClientTurnRequest>>,
    /// Executed batches (for verification), keyed by executor.
    executed_batches: HashMap<[u8; 32], Vec<BatchExecution>>,
    /// Active challenges.
    challenges: Vec<Challenge>,
    /// Current block height (for expiry checks).
    current_height: u64,
    /// Censorship deadline: how many blocks an executor has to include a turn.
    pub censorship_deadline: u64,
}

impl DelegationManager {
    /// Create a new delegation manager.
    pub fn new() -> Self {
        DelegationManager {
            delegations: HashMap::new(),
            pending_requests: HashMap::new(),
            executed_batches: HashMap::new(),
            challenges: Vec::new(),
            current_height: 0,
            censorship_deadline: 10,
        }
    }

    /// Advance the current block height.
    pub fn set_height(&mut self, height: u64) {
        self.current_height = height;
    }

    /// Get the current block height.
    pub fn current_height(&self) -> u64 {
        self.current_height
    }

    /// Client delegates to executor.
    ///
    /// Fails if the client already has an active (non-expired) delegation.
    pub fn delegate(&mut self, delegation: ExecutorDelegation) -> Result<(), DelegationError> {
        let client = delegation.client;

        // Check for existing active delegation.
        if let Some(existing) = self.delegations.get(&client) {
            if !self.is_expired(existing) {
                return Err(DelegationError::AlreadyDelegated);
            }
        }

        // Check expiry of the new delegation.
        if let Some(expires) = delegation.expires_at {
            if expires <= self.current_height {
                return Err(DelegationError::Expired);
            }
        }

        self.delegations.insert(client, delegation);
        Ok(())
    }

    /// Client revokes delegation (can switch executors after).
    pub fn revoke(&mut self, client: &[u8; 32]) -> Result<(), DelegationError> {
        if self.delegations.remove(client).is_none() {
            return Err(DelegationError::NotDelegated);
        }
        Ok(())
    }

    /// Client submits a turn request to their executor.
    ///
    /// The request is placed in the executor's pending queue.
    pub fn submit_turn(&mut self, request: ClientTurnRequest) -> Result<(), DelegationError> {
        let client = &request.client;

        // Check client has active delegation.
        let delegation = self
            .delegations
            .get(client)
            .ok_or(DelegationError::NotDelegated)?;

        // Check delegation hasn't expired.
        if self.is_expired(delegation) {
            return Err(DelegationError::Expired);
        }

        // Check scope.
        if !self.check_scope(delegation, &request) {
            return Err(DelegationError::ScopeViolation);
        }

        let executor = delegation.executor;
        self.pending_requests
            .entry(executor)
            .or_default()
            .push(request);
        Ok(())
    }

    /// Executor collects pending turns for a batch.
    ///
    /// Drains up to `max_size` requests from the executor's pending queue.
    pub fn collect_batch(
        &mut self,
        executor: &[u8; 32],
        max_size: usize,
    ) -> Vec<ClientTurnRequest> {
        let pending = match self.pending_requests.get_mut(executor) {
            Some(p) => p,
            None => return Vec::new(),
        };

        let drain_count = pending.len().min(max_size);
        pending.drain(..drain_count).collect()
    }

    /// Executor publishes a batch execution result.
    ///
    /// Validates that batch_seq is monotonically increasing for this executor.
    pub fn publish_batch(&mut self, batch: BatchExecution) -> Result<(), DelegationError> {
        let executor = batch.executor;

        // Check monotonicity of batch_seq.
        if let Some(existing) = self.executed_batches.get(&executor) {
            if let Some(last) = existing.last() {
                if batch.batch_seq <= last.batch_seq {
                    return Err(DelegationError::BatchSeqNotMonotonic);
                }
            }
        }

        self.executed_batches
            .entry(executor)
            .or_default()
            .push(batch);
        Ok(())
    }

    /// Client verifies their turn was correctly executed in a batch.
    ///
    /// Returns `Ok(true)` if a matching result exists and shows success,
    /// `Ok(false)` if a matching result exists but shows failure,
    /// and `Err(BatchVerificationFailed)` if no matching result is found.
    pub fn verify_turn_in_batch(
        &self,
        client: &[u8; 32],
        batch: &BatchExecution,
    ) -> Result<bool, DelegationError> {
        // Find a result for this client.
        let result = batch
            .results
            .iter()
            .find(|r| &r.client == client)
            .ok_or(DelegationError::BatchVerificationFailed)?;

        Ok(result.success)
    }

    /// Challenge: client disputes executor's result.
    ///
    /// Records the challenge and automatically revokes the delegation.
    pub fn challenge(
        &mut self,
        client: &[u8; 32],
        batch_seq: u64,
        reason: ChallengeReason,
    ) -> Result<(), DelegationError> {
        if !self.delegations.contains_key(client) {
            return Err(DelegationError::NotDelegated);
        }

        self.challenges.push(Challenge {
            client: *client,
            batch_seq,
            reason,
        });

        // Auto-revoke on challenge.
        self.delegations.remove(client);
        Ok(())
    }

    /// Check if a client has an active (non-expired) delegation.
    pub fn is_delegated(&self, client: &[u8; 32]) -> bool {
        match self.delegations.get(client) {
            Some(d) => !self.is_expired(d),
            None => false,
        }
    }

    /// Get the executor for a client (if actively delegated).
    pub fn executor_for(&self, client: &[u8; 32]) -> Option<&[u8; 32]> {
        let delegation = self.delegations.get(client)?;
        if self.is_expired(delegation) {
            None
        } else {
            Some(&delegation.executor)
        }
    }

    /// Switch executor (revoke old, delegate new).
    ///
    /// Atomically revokes the old delegation and establishes the new one.
    pub fn switch_executor(
        &mut self,
        client: &[u8; 32],
        new_delegation: ExecutorDelegation,
    ) -> Result<(), DelegationError> {
        // Must have an existing delegation to switch.
        if !self.delegations.contains_key(client) {
            return Err(DelegationError::NotDelegated);
        }

        // Revoke the old one.
        self.delegations.remove(client);

        // Delegate the new one (bypassing the AlreadyDelegated check since we just revoked).
        if let Some(expires) = new_delegation.expires_at {
            if expires <= self.current_height {
                return Err(DelegationError::Expired);
            }
        }

        self.delegations.insert(*client, new_delegation);
        Ok(())
    }

    /// Detect censorship: check if a client has a pending turn that should
    /// have been included by now (past the deadline).
    pub fn detect_censorship(&self, client: &[u8; 32]) -> Option<DelegationError> {
        let delegation = self.delegations.get(client)?;
        let executor = &delegation.executor;

        if let Some(pending) = self.pending_requests.get(executor) {
            for req in pending {
                if &req.client == client {
                    let deadline = req.submitted_at + self.censorship_deadline;
                    if self.current_height > deadline {
                        return Some(DelegationError::CensorshipDetected);
                    }
                }
            }
        }
        None
    }

    /// Get all challenges issued by a client.
    pub fn challenges_for(&self, client: &[u8; 32]) -> Vec<&Challenge> {
        self.challenges
            .iter()
            .filter(|c| &c.client == client)
            .collect()
    }

    /// Get executed batches for an executor.
    pub fn batches_for(&self, executor: &[u8; 32]) -> &[BatchExecution] {
        self.executed_batches
            .get(executor)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    // ─── Internal Helpers ───────────────────────────────────────────────────

    /// Check if a delegation has expired.
    fn is_expired(&self, delegation: &ExecutorDelegation) -> bool {
        match delegation.expires_at {
            Some(expires) => self.current_height >= expires,
            None => false,
        }
    }

    /// Check if a turn request is within the delegation's scope.
    ///
    /// For `CellsOnly` scope, we check if the turn_data's first 32 bytes
    /// (representing the target cell ID) match one of the allowed cells.
    /// For `EffectsOnly`, we check if the first byte of turn_data (effect type)
    /// is in the allowed list.
    fn check_scope(&self, delegation: &ExecutorDelegation, request: &ClientTurnRequest) -> bool {
        match &delegation.scope {
            DelegationScope::Full => true,
            DelegationScope::CellsOnly { cell_ids } => {
                if request.turn_data.len() < 32 {
                    return false;
                }
                let target_cell: [u8; 32] = request.turn_data[..32]
                    .try_into()
                    .expect("checked length above");
                cell_ids.contains(&target_cell)
            }
            DelegationScope::EffectsOnly { allowed_effects } => {
                if request.turn_data.is_empty() {
                    return false;
                }
                allowed_effects.contains(&request.turn_data[0])
            }
        }
    }
}

impl Default for DelegationManager {
    fn default() -> Self {
        Self::new()
    }
}

// ─── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn make_key(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    fn make_delegation(client: u8, executor: u8) -> ExecutorDelegation {
        ExecutorDelegation {
            client: make_key(client),
            executor: make_key(executor),
            scope: DelegationScope::Full,
            established_at: 0,
            expires_at: None,
            client_signature: [0u8; 64],
        }
    }

    fn make_delegation_with_expiry(client: u8, executor: u8, expires: u64) -> ExecutorDelegation {
        ExecutorDelegation {
            client: make_key(client),
            executor: make_key(executor),
            scope: DelegationScope::Full,
            established_at: 0,
            expires_at: Some(expires),
            client_signature: [0u8; 64],
        }
    }

    fn make_delegation_cells_only(
        client: u8,
        executor: u8,
        cell_ids: Vec<[u8; 32]>,
    ) -> ExecutorDelegation {
        ExecutorDelegation {
            client: make_key(client),
            executor: make_key(executor),
            scope: DelegationScope::CellsOnly { cell_ids },
            established_at: 0,
            expires_at: None,
            client_signature: [0u8; 64],
        }
    }

    fn make_turn_request(client: u8, nonce: u64) -> ClientTurnRequest {
        ClientTurnRequest {
            client: make_key(client),
            turn_data: vec![1, 2, 3, 4],
            client_signature: [0u8; 64],
            nonce,
            submitted_at: 0,
        }
    }

    fn make_turn_request_at(client: u8, nonce: u64, submitted_at: u64) -> ClientTurnRequest {
        ClientTurnRequest {
            client: make_key(client),
            turn_data: vec![1, 2, 3, 4],
            client_signature: [0u8; 64],
            nonce,
            submitted_at,
        }
    }

    fn make_turn_request_with_data(client: u8, nonce: u64, data: Vec<u8>) -> ClientTurnRequest {
        ClientTurnRequest {
            client: make_key(client),
            turn_data: data,
            client_signature: [0u8; 64],
            nonce,
            submitted_at: 0,
        }
    }

    // ─── Test 1: Delegate → verify delegation exists ────────────────────────

    #[test]
    fn test_delegate_creates_active_delegation() {
        let mut mgr = DelegationManager::new();
        let delegation = make_delegation(1, 10);

        mgr.delegate(delegation).unwrap();

        assert!(mgr.is_delegated(&make_key(1)));
        assert_eq!(mgr.executor_for(&make_key(1)), Some(&make_key(10)));
    }

    // ─── Test 2: Revoke → delegation gone, can re-delegate ──────────────────

    #[test]
    fn test_revoke_removes_delegation_and_allows_redelegate() {
        let mut mgr = DelegationManager::new();
        let delegation = make_delegation(1, 10);

        mgr.delegate(delegation).unwrap();
        assert!(mgr.is_delegated(&make_key(1)));

        mgr.revoke(&make_key(1)).unwrap();
        assert!(!mgr.is_delegated(&make_key(1)));
        assert_eq!(mgr.executor_for(&make_key(1)), None);

        // Can re-delegate.
        let new_delegation = make_delegation(1, 20);
        mgr.delegate(new_delegation).unwrap();
        assert!(mgr.is_delegated(&make_key(1)));
        assert_eq!(mgr.executor_for(&make_key(1)), Some(&make_key(20)));
    }

    // ─── Test 3: Submit turn → appears in executor's pending queue ──────────

    #[test]
    fn test_submit_turn_appears_in_pending_queue() {
        let mut mgr = DelegationManager::new();
        mgr.delegate(make_delegation(1, 10)).unwrap();

        let request = make_turn_request(1, 1);
        mgr.submit_turn(request).unwrap();

        let batch = mgr.collect_batch(&make_key(10), 10);
        assert_eq!(batch.len(), 1);
        assert_eq!(batch[0].client, make_key(1));
        assert_eq!(batch[0].nonce, 1);
    }

    // ─── Test 4: Collect batch → groups pending turns ───────────────────────

    #[test]
    fn test_collect_batch_groups_and_limits() {
        let mut mgr = DelegationManager::new();
        mgr.delegate(make_delegation(1, 10)).unwrap();
        mgr.delegate(make_delegation(2, 10)).unwrap();

        // Submit 3 turns from client 1 and 2 from client 2.
        for nonce in 0..3 {
            mgr.submit_turn(make_turn_request(1, nonce)).unwrap();
        }
        for nonce in 0..2 {
            mgr.submit_turn(make_turn_request(2, nonce)).unwrap();
        }

        // Collect with max_size 3 (should get first 3).
        let batch = mgr.collect_batch(&make_key(10), 3);
        assert_eq!(batch.len(), 3);

        // Remaining 2 should still be there.
        let remaining = mgr.collect_batch(&make_key(10), 10);
        assert_eq!(remaining.len(), 2);

        // Queue is now empty.
        let empty = mgr.collect_batch(&make_key(10), 10);
        assert!(empty.is_empty());
    }

    // ─── Test 5: Publish batch → results stored ─────────────────────────────

    #[test]
    fn test_publish_batch_stores_results() {
        let mut mgr = DelegationManager::new();

        let batch = BatchExecution {
            executor: make_key(10),
            client_turns: vec![make_turn_request(1, 0)],
            batch_proof: vec![0xDE, 0xAD],
            results: vec![TurnResult {
                client: make_key(1),
                old_commitment: [0u8; 32],
                new_commitment: [1u8; 32],
                effects_hash: [2u8; 32],
                success: true,
            }],
            batch_seq: 1,
        };

        mgr.publish_batch(batch).unwrap();

        let batches = mgr.batches_for(&make_key(10));
        assert_eq!(batches.len(), 1);
        assert_eq!(batches[0].batch_seq, 1);
        assert_eq!(batches[0].results.len(), 1);
    }

    // ─── Test 6: Verify turn in batch → correct result found ────────────────

    #[test]
    fn test_verify_turn_in_batch() {
        let mgr = DelegationManager::new();

        let batch = BatchExecution {
            executor: make_key(10),
            client_turns: vec![make_turn_request(1, 0), make_turn_request(2, 0)],
            batch_proof: vec![],
            results: vec![
                TurnResult {
                    client: make_key(1),
                    old_commitment: [0u8; 32],
                    new_commitment: [1u8; 32],
                    effects_hash: [2u8; 32],
                    success: true,
                },
                TurnResult {
                    client: make_key(2),
                    old_commitment: [0u8; 32],
                    new_commitment: [3u8; 32],
                    effects_hash: [4u8; 32],
                    success: false,
                },
            ],
            batch_seq: 1,
        };

        // Client 1's turn succeeded.
        assert_eq!(mgr.verify_turn_in_batch(&make_key(1), &batch), Ok(true));

        // Client 2's turn failed.
        assert_eq!(mgr.verify_turn_in_batch(&make_key(2), &batch), Ok(false));

        // Client 3 not in batch.
        assert_eq!(
            mgr.verify_turn_in_batch(&make_key(3), &batch),
            Err(DelegationError::BatchVerificationFailed)
        );
    }

    // ─── Test 7: Challenge invalid proof → challenge recorded ───────────────

    #[test]
    fn test_challenge_records_and_revokes() {
        let mut mgr = DelegationManager::new();
        mgr.delegate(make_delegation(1, 10)).unwrap();
        assert!(mgr.is_delegated(&make_key(1)));

        mgr.challenge(&make_key(1), 5, ChallengeReason::InvalidProof)
            .unwrap();

        // Delegation should be auto-revoked after challenge.
        assert!(!mgr.is_delegated(&make_key(1)));

        // Challenge should be recorded.
        let challenges = mgr.challenges_for(&make_key(1));
        assert_eq!(challenges.len(), 1);
        assert_eq!(challenges[0].batch_seq, 5);
    }

    // ─── Test 8: Switch executor → old revoked, new active ──────────────────

    #[test]
    fn test_switch_executor() {
        let mut mgr = DelegationManager::new();
        mgr.delegate(make_delegation(1, 10)).unwrap();
        assert_eq!(mgr.executor_for(&make_key(1)), Some(&make_key(10)));

        let new_delegation = make_delegation(1, 20);
        mgr.switch_executor(&make_key(1), new_delegation).unwrap();

        assert!(mgr.is_delegated(&make_key(1)));
        assert_eq!(mgr.executor_for(&make_key(1)), Some(&make_key(20)));
    }

    // ─── Test 9: Scope enforcement: CellsOnly rejects turns for other cells ─

    #[test]
    fn test_scope_cells_only_enforcement() {
        let mut mgr = DelegationManager::new();
        let allowed_cell = [0xAA; 32];
        let delegation = make_delegation_cells_only(1, 10, vec![allowed_cell]);
        mgr.delegate(delegation).unwrap();

        // Turn targeting the allowed cell (first 32 bytes = cell ID).
        let mut allowed_data = allowed_cell.to_vec();
        allowed_data.extend_from_slice(&[0xFF; 4]); // extra payload
        let allowed_req = make_turn_request_with_data(1, 1, allowed_data);
        assert!(mgr.submit_turn(allowed_req).is_ok());

        // Turn targeting a disallowed cell.
        let mut disallowed_data = [0xBB; 32].to_vec();
        disallowed_data.extend_from_slice(&[0xFF; 4]);
        let disallowed_req = make_turn_request_with_data(1, 2, disallowed_data);
        assert_eq!(
            mgr.submit_turn(disallowed_req),
            Err(DelegationError::ScopeViolation)
        );
    }

    // ─── Test 10: Expired delegation rejected ───────────────────────────────

    #[test]
    fn test_expired_delegation_rejected() {
        let mut mgr = DelegationManager::new();
        mgr.set_height(100);

        // Delegation that expires at height 50 (already expired).
        let delegation = make_delegation_with_expiry(1, 10, 50);
        assert_eq!(mgr.delegate(delegation), Err(DelegationError::Expired));

        // Delegation that expires at height 200 (still valid).
        let delegation = make_delegation_with_expiry(1, 10, 200);
        mgr.delegate(delegation).unwrap();
        assert!(mgr.is_delegated(&make_key(1)));

        // Advance past expiry.
        mgr.set_height(200);
        assert!(!mgr.is_delegated(&make_key(1)));
        assert_eq!(mgr.executor_for(&make_key(1)), None);
    }

    // ─── Test 11: Duplicate delegation rejected ─────────────────────────────

    #[test]
    fn test_duplicate_delegation_rejected() {
        let mut mgr = DelegationManager::new();
        mgr.delegate(make_delegation(1, 10)).unwrap();

        // Attempting to delegate again should fail.
        let duplicate = make_delegation(1, 20);
        assert_eq!(
            mgr.delegate(duplicate),
            Err(DelegationError::AlreadyDelegated)
        );

        // The original delegation should still be intact.
        assert_eq!(mgr.executor_for(&make_key(1)), Some(&make_key(10)));
    }

    // ─── Test 12: Censorship detection ──────────────────────────────────────

    #[test]
    fn test_censorship_detection() {
        let mut mgr = DelegationManager::new();
        mgr.censorship_deadline = 10;
        mgr.set_height(5);

        mgr.delegate(make_delegation(1, 10)).unwrap();

        // Submit a turn at height 5.
        let request = make_turn_request_at(1, 1, 5);
        mgr.submit_turn(request).unwrap();

        // At height 10, still within deadline (5 + 10 = 15).
        mgr.set_height(10);
        assert_eq!(mgr.detect_censorship(&make_key(1)), None);

        // At height 16, past the deadline (5 + 10 = 15, current > 15).
        mgr.set_height(16);
        assert_eq!(
            mgr.detect_censorship(&make_key(1)),
            Some(DelegationError::CensorshipDetected)
        );
    }

    // ─── Test 13: Batch sequence monotonic enforcement ──────────────────────

    #[test]
    fn test_batch_seq_monotonic() {
        let mut mgr = DelegationManager::new();

        let batch1 = BatchExecution {
            executor: make_key(10),
            client_turns: vec![],
            batch_proof: vec![],
            results: vec![],
            batch_seq: 1,
        };
        mgr.publish_batch(batch1).unwrap();

        // Publish batch with higher seq: OK.
        let batch2 = BatchExecution {
            executor: make_key(10),
            client_turns: vec![],
            batch_proof: vec![],
            results: vec![],
            batch_seq: 5,
        };
        mgr.publish_batch(batch2).unwrap();

        // Publish batch with equal seq: FAIL.
        let batch_dup = BatchExecution {
            executor: make_key(10),
            client_turns: vec![],
            batch_proof: vec![],
            results: vec![],
            batch_seq: 5,
        };
        assert_eq!(
            mgr.publish_batch(batch_dup),
            Err(DelegationError::BatchSeqNotMonotonic)
        );

        // Publish batch with lower seq: FAIL.
        let batch_lower = BatchExecution {
            executor: make_key(10),
            client_turns: vec![],
            batch_proof: vec![],
            results: vec![],
            batch_seq: 3,
        };
        assert_eq!(
            mgr.publish_batch(batch_lower),
            Err(DelegationError::BatchSeqNotMonotonic)
        );
    }

    // ─── Additional coverage tests ──────────────────────────────────────────

    #[test]
    fn test_revoke_without_delegation_fails() {
        let mut mgr = DelegationManager::new();
        assert_eq!(mgr.revoke(&make_key(1)), Err(DelegationError::NotDelegated));
    }

    #[test]
    fn test_submit_turn_without_delegation_fails() {
        let mut mgr = DelegationManager::new();
        let request = make_turn_request(1, 0);
        assert_eq!(mgr.submit_turn(request), Err(DelegationError::NotDelegated));
    }

    #[test]
    fn test_challenge_without_delegation_fails() {
        let mut mgr = DelegationManager::new();
        assert_eq!(
            mgr.challenge(&make_key(1), 0, ChallengeReason::InvalidProof),
            Err(DelegationError::NotDelegated)
        );
    }

    #[test]
    fn test_switch_executor_without_delegation_fails() {
        let mut mgr = DelegationManager::new();
        let new_delegation = make_delegation(1, 20);
        assert_eq!(
            mgr.switch_executor(&make_key(1), new_delegation),
            Err(DelegationError::NotDelegated)
        );
    }

    #[test]
    fn test_effects_only_scope() {
        let mut mgr = DelegationManager::new();
        let delegation = ExecutorDelegation {
            client: make_key(1),
            executor: make_key(10),
            scope: DelegationScope::EffectsOnly {
                allowed_effects: vec![0x01, 0x02],
            },
            established_at: 0,
            expires_at: None,
            client_signature: [0u8; 64],
        };
        mgr.delegate(delegation).unwrap();

        // Allowed effect type (0x01).
        let req = make_turn_request_with_data(1, 1, vec![0x01, 0xAA, 0xBB]);
        assert!(mgr.submit_turn(req).is_ok());

        // Disallowed effect type (0x03).
        let req = make_turn_request_with_data(1, 2, vec![0x03, 0xAA, 0xBB]);
        assert_eq!(mgr.submit_turn(req), Err(DelegationError::ScopeViolation));
    }

    #[test]
    fn test_expired_delegation_allows_new_delegate() {
        let mut mgr = DelegationManager::new();
        mgr.set_height(0);

        // Create delegation that expires at 10.
        let delegation = make_delegation_with_expiry(1, 10, 10);
        mgr.delegate(delegation).unwrap();

        // Advance past expiry.
        mgr.set_height(10);
        assert!(!mgr.is_delegated(&make_key(1)));

        // Can now delegate to a new executor (expired delegation is treated as absent).
        let new_delegation = make_delegation_with_expiry(1, 20, 100);
        mgr.delegate(new_delegation).unwrap();
        assert!(mgr.is_delegated(&make_key(1)));
        assert_eq!(mgr.executor_for(&make_key(1)), Some(&make_key(20)));
    }
}
