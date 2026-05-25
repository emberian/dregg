//! Relay operator obligation model.
//!
//! # DEPRECATED — migrate to `pyana_storage_templates::relay_operator`
//!
//! Per `STORAGE-AS-CELL-PROGRAMS.md` §3.5 this module's
//! [`RelayOperator`] / [`HostedInbox`] / [`DeliveryDispute`] surface
//! is the legacy operator-side bond / quota / dispute primitive.
//! The canonical replacement is the cell-program template
//! [`pyana_storage_templates::relay_operator`], whose
//! `relay_operator_factory_descriptor()` exports a
//! `FactoryDescriptor` whose `CellProgram::Cases` enforces
//! `RateLimitBySum` quota, `BoundedBy` bond-decrement-on-dispute,
//! `Monotonic` dispute counting, and `WitnessedPredicate::Dfa`
//! dispatch classification on every turn.
//!
//! A relay operator bonds computrons (CreateObligation pattern) to host inboxes.
//! If they fail to deliver messages (provable non-delivery), they get slashed.
//! If they deliver correctly, the bond is returned + they earn fees.
//!
//! # Economic Model
//!
//! - Operator posts a bond proportional to hosted capacity.
//! - Each inbox has a committed capacity (the operator guarantees this much space).
//! - Senders pay deposits when enqueuing (anti-spam + operator revenue).
//! - On GC: operator keeps 10% of expired message deposits as fee.
//! - On delivery: deposits flow to the inbox owner (compensation for reading).
//! - On eviction (owner quota depleted): remaining messages refunded to senders.
//!
//! # Dispute Integration
//!
//! Uses the `app-framework/src/dispute.rs` Disputable pattern:
//! - Sender proves enqueue via old queue root + enqueue receipt (DequeueProof).
//! - Operator proves delivery via dequeue proof (new queue root).
//! - If operator cannot produce dequeue proof within SLA window → slash.

#![allow(deprecated)]

use std::collections::HashMap;

use crate::QuotaId;
use crate::inbox::{CapInbox, InboxError, InboxMessage};
use crate::queue::{DequeueProof, MerkleQueue, QueueEntry};
use crate::relay::RelayError;

/// Bond rate: computrons required per unit of committed capacity.
const BOND_RATE_PER_CAPACITY: u64 = 100;

/// Operator fee: percentage of expired message deposits kept by operator.
const OPERATOR_GC_FEE_PCT: u64 = 10;

/// A relay operator that bonds computrons to host inboxes.
#[deprecated(
    since = "0.1.0",
    note = "Use `pyana_storage_templates::relay_operator::relay_operator_factory_descriptor()` per STORAGE-AS-CELL-PROGRAMS.md §3.5. The cell-program template's `RateLimitBySum` quota, `BoundedBy` slash-only-on-dispute, monotonic dispute counter, and `WitnessedPredicate::Dfa` dispatch are enforced by the executor on every turn."
)]
#[derive(Debug, Clone)]
pub struct RelayOperator {
    /// The operator's identity.
    pub id: [u8; 32],
    /// Bond amount (locked via CreateObligation pattern).
    pub bond: u64,
    /// Inboxes this operator hosts.
    pub hosted_inboxes: HashMap<[u8; 32], HostedInbox>,
    /// Revenue earned (from enqueue deposits on GC).
    pub earned_fees: u64,
    /// SLA: max delivery latency (blocks).
    pub max_delivery_latency: u64,
}

/// A hosted inbox: queue + inbox + ownership metadata.
#[derive(Debug, Clone)]
pub struct HostedInbox {
    /// The underlying MerkleQueue for provable message ordering.
    pub queue: MerkleQueue,
    /// The CapInbox wrapping the queue (deposit/size enforcement).
    pub inbox: CapInbox,
    /// Owner's identity (public key).
    pub owner: [u8; 32],
    /// The agreed capacity (operator committed to hosting this much).
    pub committed_capacity: usize,
    /// Last known drain height (for liveness tracking).
    pub last_drain_height: u64,
    /// Whether this inbox has been evicted.
    pub evicted: bool,
}

/// Result of a GC pass.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GcResult {
    /// Number of messages garbage-collected.
    pub messages_collected: usize,
    /// Total deposits reclaimed by operator as fees.
    pub operator_fees: u64,
    /// Refunds returned to senders (90% of expired deposits).
    pub sender_refunds: Vec<SenderRefund>,
}

/// A refund to a sender whose message expired.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SenderRefund {
    pub sender: [u8; 32],
    pub amount: u64,
}

/// A delivery dispute: sender claims message was sent, operator claims it was delivered.
///
/// Integration with `app-framework/src/dispute.rs` Disputable trait:
/// - Sender submits `enqueue_proof` (proves they enqueued at a given queue state).
/// - Operator responds with dequeue proof (proves they delivered).
/// - If operator cannot produce proof within `max_delivery_latency` blocks → slash.
#[derive(Debug, Clone)]
pub struct DeliveryDispute {
    /// The sender who claims non-delivery.
    pub sender: [u8; 32],
    /// Hash of the message in question.
    pub message_hash: [u8; 32],
    /// Sender's proof they enqueued (the old queue root + position).
    pub enqueue_proof: DequeueProof,
    /// Operator's claimed delivery height (None if they haven't responded).
    pub claimed_delivery_height: Option<u64>,
    /// Operator's delivery proof (if they can produce one).
    pub delivery_proof: Option<DequeueProof>,
    /// Block height when the dispute was filed.
    pub filed_at: u64,
}

/// Outcome of dispute resolution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DisputeOutcome {
    /// Operator proved delivery — dispute dismissed.
    OperatorVindicated,
    /// Operator failed to prove delivery within SLA — slash.
    OperatorSlashed { slash_amount: u64 },
    /// Invalid dispute (e.g., bad enqueue proof).
    InvalidDispute,
}

impl RelayOperator {
    /// Create a new relay operator with the given identity and bond.
    pub fn new(id: [u8; 32], bond: u64, max_delivery_latency: u64) -> Self {
        Self {
            id,
            bond,
            hosted_inboxes: HashMap::new(),
            earned_fees: 0,
            max_delivery_latency,
        }
    }

    /// Accept a new inbox for hosting (increases bond requirement).
    ///
    /// Fails if the operator would become underbonded.
    pub fn host_inbox(
        &mut self,
        owner: [u8; 32],
        capacity: usize,
        min_deposit: u64,
    ) -> Result<(), RelayError> {
        // Check if already hosted.
        if self.hosted_inboxes.contains_key(&owner) {
            return Err(RelayError::AlreadyHosted { owner });
        }

        // Check if accepting this inbox would make us underbonded.
        let new_required = self.required_bond() + (capacity as u64 * BOND_RATE_PER_CAPACITY);
        if self.bond < new_required {
            return Err(RelayError::Underbonded {
                required: new_required,
                actual: self.bond,
            });
        }

        let queue = MerkleQueue::new(capacity);
        let inbox = CapInbox::new(QuotaId(0), capacity, min_deposit);

        self.hosted_inboxes.insert(
            owner,
            HostedInbox {
                queue,
                inbox,
                owner,
                committed_capacity: capacity,
                last_drain_height: 0,
                evicted: false,
            },
        );

        Ok(())
    }

    /// Process an incoming message for a hosted inbox.
    ///
    /// The sender pays a deposit (anti-spam). Returns the new queue root on success.
    pub fn receive_message(
        &mut self,
        dest: &[u8; 32],
        msg: InboxMessage,
        deposit: u64,
        current_height: u64,
    ) -> Result<[u8; 32], RelayError> {
        let hosted = self
            .hosted_inboxes
            .get_mut(dest)
            .ok_or(RelayError::InboxNotFound { destination: *dest })?;

        if hosted.evicted {
            return Err(RelayError::InboxNotFound { destination: *dest });
        }

        // Use the CapInbox to enforce deposit and size limits.
        let root = hosted
            .inbox
            .receive_at(msg.clone(), deposit, current_height)
            .map_err(|e| match e {
                InboxError::InsufficientDeposit { provided, minimum } => {
                    RelayError::InsufficientDeposit { provided, minimum }
                }
                InboxError::Full { capacity } => RelayError::QueueFull { capacity },
                InboxError::MessageTooLarge { size, max } => {
                    RelayError::MessageTooLarge { size, max }
                }
                InboxError::Empty => RelayError::QueueFull { capacity: 0 },
            })?;

        Ok(root)
    }

    /// Drain messages to a reconnected owner (returns dequeue proofs).
    ///
    /// The owner comes online and collects pending messages. Each message
    /// is returned with a DequeueProof that can be used to verify delivery.
    pub fn drain_for_owner(
        &mut self,
        owner: &[u8; 32],
        max: usize,
        current_height: u64,
    ) -> Vec<(QueueEntry, DequeueProof)> {
        let hosted = match self.hosted_inboxes.get_mut(owner) {
            Some(h) => h,
            None => return Vec::new(),
        };

        if hosted.evicted {
            return Vec::new();
        }

        let mut results = Vec::new();
        for _ in 0..max {
            match hosted.inbox.read_next() {
                Ok((entry, proof)) => results.push((entry, proof)),
                Err(_) => break,
            }
        }

        if !results.is_empty() {
            hosted.last_drain_height = current_height;
        }

        results
    }

    /// GC expired messages (operator keeps 10% of deposits as fee).
    ///
    /// Messages that have been in the queue longer than `ttl` blocks are expired.
    /// - Operator earns 10% of expired deposits as fees.
    /// - Senders get 90% of their deposits refunded.
    pub fn gc_expired(&mut self, current_height: u64, ttl: u64) -> GcResult {
        let mut total_operator_fees = 0u64;
        let mut total_messages = 0usize;
        let mut sender_refunds = Vec::new();

        let owners: Vec<[u8; 32]> = self.hosted_inboxes.keys().copied().collect();

        for owner in owners {
            let hosted = match self.hosted_inboxes.get_mut(&owner) {
                Some(h) => h,
                None => continue,
            };

            if hosted.evicted {
                continue;
            }

            // Use CapInbox's gc_expired to handle expiry.
            // But we need finer control for operator fee tracking.
            // Manually check and dequeue expired entries.
            loop {
                match hosted.inbox.peek() {
                    Some(entry) if current_height > entry.enqueued_at + ttl => {
                        let deposit = entry.deposit;
                        let sender = entry.sender;
                        // Dequeue the expired entry.
                        let _ = hosted.inbox.read_next();
                        total_messages += 1;

                        // Operator keeps 10%, sender gets 90%.
                        let operator_fee =
                            (deposit as u128 * OPERATOR_GC_FEE_PCT as u128 / 100) as u64;
                        let sender_refund = deposit.saturating_sub(operator_fee);

                        total_operator_fees += operator_fee;
                        if sender_refund > 0 {
                            sender_refunds.push(SenderRefund {
                                sender,
                                amount: sender_refund,
                            });
                        }
                    }
                    _ => break,
                }
            }
        }

        self.earned_fees += total_operator_fees;

        GcResult {
            messages_collected: total_messages,
            operator_fees: total_operator_fees,
            sender_refunds,
        }
    }

    /// Compute total bond required (sum of committed capacities * rate).
    pub fn required_bond(&self) -> u64 {
        self.hosted_inboxes
            .values()
            .filter(|h| !h.evicted)
            .map(|h| h.committed_capacity as u64 * BOND_RATE_PER_CAPACITY)
            .sum()
    }

    /// Check if operator is underbonded (should be slashed or new inboxes rejected).
    pub fn is_underbonded(&self) -> bool {
        self.bond < self.required_bond()
    }

    /// Evict an inbox (owner's quota depleted or other policy reason).
    ///
    /// Remaining messages are "returned" to senders (deposits refunded in full).
    /// Operator stops earning fees on this inbox.
    pub fn evict_inbox(&mut self, owner: &[u8; 32]) -> Vec<SenderRefund> {
        let hosted = match self.hosted_inboxes.get_mut(owner) {
            Some(h) => h,
            None => return Vec::new(),
        };

        if hosted.evicted {
            return Vec::new();
        }

        hosted.evicted = true;
        let mut refunds = Vec::new();

        // Drain all remaining messages and refund deposits to senders.
        while let Ok((entry, _proof)) = hosted.inbox.read_next() {
            if entry.deposit > 0 {
                refunds.push(SenderRefund {
                    sender: entry.sender,
                    amount: entry.deposit,
                });
            }
        }

        refunds
    }

    /// Get the queue root for a hosted inbox (verifiable state commitment).
    pub fn inbox_root(&self, owner: &[u8; 32]) -> Option<[u8; 32]> {
        self.hosted_inboxes
            .get(owner)
            .filter(|h| !h.evicted)
            .map(|h| h.inbox.root())
    }

    /// Number of active (non-evicted) hosted inboxes.
    pub fn active_inbox_count(&self) -> usize {
        self.hosted_inboxes.values().filter(|h| !h.evicted).count()
    }

    /// Total messages pending across all hosted inboxes.
    pub fn total_pending(&self) -> usize {
        self.hosted_inboxes
            .values()
            .filter(|h| !h.evicted)
            .map(|h| h.inbox.len())
            .sum()
    }

    /// Resolve a delivery dispute.
    ///
    /// If the operator can produce a valid dequeue proof, the dispute is dismissed.
    /// If not, and the SLA window has passed, the operator is slashed.
    pub fn resolve_dispute(
        &self,
        dispute: &DeliveryDispute,
        current_height: u64,
    ) -> DisputeOutcome {
        // Validate the sender's enqueue proof.
        if !crate::queue::verify_dequeue_proof(&dispute.enqueue_proof) {
            return DisputeOutcome::InvalidDispute;
        }

        // If operator has a delivery proof, verify it.
        if let Some(ref delivery_proof) = dispute.delivery_proof
            && crate::queue::verify_dequeue_proof(delivery_proof)
        {
            // Operator proved delivery.
            return DisputeOutcome::OperatorVindicated;
        }

        // Check if SLA window has passed.
        let sla_deadline = dispute.filed_at + self.max_delivery_latency;
        if current_height >= sla_deadline {
            // Operator failed to prove delivery within SLA. Slash.
            // Slash amount: proportional to bond / number of inboxes.
            let active = self.active_inbox_count().max(1) as u64;
            let slash_amount = self.bond / active;
            return DisputeOutcome::OperatorSlashed { slash_amount };
        }

        // SLA window still open — dispute is pending (treated as invalid for now).
        // In a real system this would return a "Pending" state.
        DisputeOutcome::InvalidDispute
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inbox::InboxMessage;
    use crate::queue::verify_dequeue_proof;

    fn test_operator() -> RelayOperator {
        RelayOperator::new([0xAA; 32], 100_000, 50)
    }

    fn test_msg(sender: [u8; 32], data: &[u8]) -> InboxMessage {
        InboxMessage::Encrypted {
            ciphertext: data.to_vec(),
            sender,
        }
    }

    // --- Test 1: Relay hosts an inbox, receives messages into MerkleQueue ---
    #[test]
    fn host_inbox_and_receive_messages() {
        let mut op = test_operator();
        let owner = [0x01; 32];

        op.host_inbox(owner, 10, 100).unwrap();
        assert_eq!(op.active_inbox_count(), 1);

        let msg = test_msg([0xBB; 32], b"hello");
        let root = op.receive_message(&owner, msg, 200, 10).unwrap();

        // Root should be non-empty (not the empty queue root).
        assert_ne!(root, crate::queue::empty_queue_root());

        // Should have 1 pending message.
        assert_eq!(op.total_pending(), 1);
    }

    // --- Test 2: Drain returns messages in FIFO with dequeue proofs ---
    #[test]
    fn drain_returns_fifo_with_proofs() {
        let mut op = test_operator();
        let owner = [0x01; 32];
        op.host_inbox(owner, 10, 50).unwrap();

        // Enqueue 3 messages.
        for i in 0u8..3 {
            let msg = test_msg([i + 1; 32], &[i; 8]);
            op.receive_message(&owner, msg, 100, 10 + i as u64).unwrap();
        }

        assert_eq!(op.total_pending(), 3);

        // Drain all.
        let drained = op.drain_for_owner(&owner, 10, 100);
        assert_eq!(drained.len(), 3);

        // Verify FIFO order: first enqueued has sender [1;32].
        assert_eq!(drained[0].0.sender, [1u8; 32]);
        assert_eq!(drained[1].0.sender, [2u8; 32]);
        assert_eq!(drained[2].0.sender, [3u8; 32]);

        // Each proof should be verifiable.
        for (_, proof) in &drained {
            assert!(verify_dequeue_proof(proof));
        }

        // Queue should be empty now.
        assert_eq!(op.total_pending(), 0);
    }

    // --- Test 3: GC expired messages (operator earns fees) ---
    #[test]
    fn gc_expired_operator_earns_fees() {
        let mut op = test_operator();
        let owner = [0x01; 32];
        op.host_inbox(owner, 10, 50).unwrap();

        // Enqueue at block 10.
        let msg = test_msg([0xBB; 32], b"will expire");
        op.receive_message(&owner, msg, 1000, 10).unwrap();

        // GC with TTL=20, current_height=35 (10 + 20 = 30 < 35, expired).
        let result = op.gc_expired(35, 20);

        assert_eq!(result.messages_collected, 1);
        assert_eq!(result.operator_fees, 100); // 10% of 1000
        assert_eq!(result.sender_refunds.len(), 1);
        assert_eq!(result.sender_refunds[0].amount, 900); // 90% of 1000
        assert_eq!(result.sender_refunds[0].sender, [0xBB; 32]);

        // Operator earned fees.
        assert_eq!(op.earned_fees, 100);
    }

    // --- Test 4: Underbonded operator can't accept new inboxes ---
    #[test]
    fn underbonded_operator_rejects_new_inboxes() {
        // Bond = 500, rate = 100 per capacity. Can host 5 capacity total.
        let mut op = RelayOperator::new([0xAA; 32], 500, 50);

        // Host inbox with capacity 5 (requires 500 bond). Should succeed.
        op.host_inbox([0x01; 32], 5, 50).unwrap();
        assert!(!op.is_underbonded());

        // Try to host another inbox with capacity 1 (would need 600 total).
        let result = op.host_inbox([0x02; 32], 1, 50);
        assert!(matches!(result, Err(RelayError::Underbonded { .. })));
    }

    // --- Test 5: Eviction on owner quota depletion ---
    #[test]
    fn eviction_refunds_senders() {
        let mut op = test_operator();
        let owner = [0x01; 32];
        op.host_inbox(owner, 10, 50).unwrap();

        // Enqueue 3 messages with deposits.
        for i in 0u8..3 {
            let msg = test_msg([i + 10; 32], &[i; 4]);
            op.receive_message(&owner, msg, 500 + i as u64 * 100, 10)
                .unwrap();
        }

        assert_eq!(op.total_pending(), 3);

        // Evict the inbox (simulating owner quota depletion).
        let refunds = op.evict_inbox(&owner);

        // All deposits refunded to senders.
        assert_eq!(refunds.len(), 3);
        assert_eq!(refunds[0].sender, [10u8; 32]);
        assert_eq!(refunds[0].amount, 500);
        assert_eq!(refunds[1].sender, [11u8; 32]);
        assert_eq!(refunds[1].amount, 600);
        assert_eq!(refunds[2].sender, [12u8; 32]);
        assert_eq!(refunds[2].amount, 700);

        // Inbox is now evicted — no more operations.
        assert_eq!(op.active_inbox_count(), 0);
        assert_eq!(op.total_pending(), 0);
    }

    // --- Test 6: Delivery dispute — sender proves enqueue, operator proves delivery ---
    #[test]
    fn dispute_operator_proves_delivery() {
        let mut op = test_operator();
        let owner = [0x01; 32];
        op.host_inbox(owner, 10, 50).unwrap();

        // Enqueue a message.
        let msg = test_msg([0xBB; 32], b"disputed msg");
        op.receive_message(&owner, msg, 200, 10).unwrap();

        // Owner drains (operator delivers).
        let drained = op.drain_for_owner(&owner, 1, 20);
        assert_eq!(drained.len(), 1);
        let (entry, delivery_proof) = &drained[0];

        // Sender files a dispute (they claim non-delivery).
        // They use the delivery_proof as their "enqueue proof" (same structure).
        let dispute = DeliveryDispute {
            sender: [0xBB; 32],
            message_hash: entry.content_hash,
            enqueue_proof: delivery_proof.clone(),
            claimed_delivery_height: Some(20),
            delivery_proof: Some(delivery_proof.clone()),
            filed_at: 25,
        };

        // Operator provides valid delivery proof → vindicated.
        let outcome = op.resolve_dispute(&dispute, 30);
        assert_eq!(outcome, DisputeOutcome::OperatorVindicated);
    }

    // --- Test 7: Delivery dispute — operator can't prove delivery → slash ---
    #[test]
    fn dispute_operator_slashed_no_proof() {
        let mut op = test_operator();
        let owner = [0x01; 32];
        op.host_inbox(owner, 10, 50).unwrap();

        // Enqueue a message.
        let msg = test_msg([0xBB; 32], b"lost msg");
        op.receive_message(&owner, msg, 200, 10).unwrap();

        // Drain to get a valid proof structure for the enqueue_proof.
        let drained = op.drain_for_owner(&owner, 1, 20);
        let (entry, proof) = &drained[0];

        // Sender files dispute. Operator has NO delivery proof.
        let dispute = DeliveryDispute {
            sender: [0xBB; 32],
            message_hash: entry.content_hash,
            enqueue_proof: proof.clone(),
            claimed_delivery_height: None,
            delivery_proof: None, // No proof!
            filed_at: 25,
        };

        // SLA window = 50 blocks. At height 25 + 50 = 75, operator is slashed.
        let outcome = op.resolve_dispute(&dispute, 80);
        assert_eq!(
            outcome,
            DisputeOutcome::OperatorSlashed {
                slash_amount: 100_000 // full bond / 1 active inbox
            }
        );
    }

    // --- Test 8: Multiple inboxes per operator ---
    #[test]
    fn multiple_inboxes_per_operator() {
        let mut op = test_operator(); // bond = 100_000

        let owner_a = [0x01; 32];
        let owner_b = [0x02; 32];
        let owner_c = [0x03; 32];

        op.host_inbox(owner_a, 10, 50).unwrap();
        op.host_inbox(owner_b, 20, 100).unwrap();
        op.host_inbox(owner_c, 5, 25).unwrap();

        assert_eq!(op.active_inbox_count(), 3);

        // Send to each.
        op.receive_message(&owner_a, test_msg([0xAA; 32], b"a"), 100, 10)
            .unwrap();
        op.receive_message(&owner_b, test_msg([0xBB; 32], b"b"), 200, 10)
            .unwrap();
        op.receive_message(&owner_c, test_msg([0xCC; 32], b"c"), 50, 10)
            .unwrap();

        assert_eq!(op.total_pending(), 3);

        // Each inbox has its own root.
        let root_a = op.inbox_root(&owner_a).unwrap();
        let root_b = op.inbox_root(&owner_b).unwrap();
        let root_c = op.inbox_root(&owner_c).unwrap();

        assert_ne!(root_a, root_b);
        assert_ne!(root_b, root_c);
    }

    // --- Test 9: Bond calculation scales with hosted capacity ---
    #[test]
    fn bond_calculation_scales_with_capacity() {
        let mut op = test_operator();

        assert_eq!(op.required_bond(), 0);

        op.host_inbox([0x01; 32], 10, 50).unwrap();
        assert_eq!(op.required_bond(), 10 * BOND_RATE_PER_CAPACITY); // 1000

        op.host_inbox([0x02; 32], 20, 50).unwrap();
        assert_eq!(op.required_bond(), 30 * BOND_RATE_PER_CAPACITY); // 3000

        // After eviction, required bond decreases.
        op.evict_inbox(&[0x01; 32]);
        assert_eq!(op.required_bond(), 20 * BOND_RATE_PER_CAPACITY); // 2000
    }

    // --- Test 10: Queue root is verifiable after operations ---
    #[test]
    fn queue_root_verifiable_after_operations() {
        let mut op = test_operator();
        let owner = [0x01; 32];
        op.host_inbox(owner, 10, 50).unwrap();

        // Empty root.
        let empty_root = op.inbox_root(&owner).unwrap();
        assert_eq!(empty_root, crate::queue::empty_queue_root());

        // Enqueue changes root.
        let msg1 = test_msg([0xAA; 32], b"first");
        let root_after_1 = op.receive_message(&owner, msg1, 100, 10).unwrap();
        assert_ne!(root_after_1, empty_root);
        assert_eq!(op.inbox_root(&owner).unwrap(), root_after_1);

        // Second enqueue changes root again.
        let msg2 = test_msg([0xBB; 32], b"second");
        let root_after_2 = op.receive_message(&owner, msg2, 100, 11).unwrap();
        assert_ne!(root_after_2, root_after_1);
        assert_eq!(op.inbox_root(&owner).unwrap(), root_after_2);

        // Drain changes root.
        let _drained = op.drain_for_owner(&owner, 1, 20);
        let root_after_drain = op.inbox_root(&owner).unwrap();
        assert_ne!(root_after_drain, root_after_2);
        // After draining 1 of 2, root should equal a fresh queue with just the 2nd message.
        assert_ne!(root_after_drain, empty_root);

        // Drain the last one.
        let _drained = op.drain_for_owner(&owner, 1, 21);
        let final_root = op.inbox_root(&owner).unwrap();
        // Back to empty.
        assert_eq!(final_root, empty_root);
    }

    // --- Additional: duplicate host_inbox fails ---
    #[test]
    fn duplicate_host_fails() {
        let mut op = test_operator();
        let owner = [0x01; 32];
        op.host_inbox(owner, 10, 50).unwrap();
        let result = op.host_inbox(owner, 5, 25);
        assert!(matches!(result, Err(RelayError::AlreadyHosted { .. })));
    }

    // --- Additional: receive to non-existent inbox fails ---
    #[test]
    fn receive_to_nonexistent_inbox_fails() {
        let mut op = test_operator();
        let msg = test_msg([0xBB; 32], b"orphan");
        let result = op.receive_message(&[0xFF; 32], msg, 100, 10);
        assert!(matches!(result, Err(RelayError::InboxNotFound { .. })));
    }

    // --- Additional: insufficient deposit rejected ---
    #[test]
    fn insufficient_deposit_rejected() {
        let mut op = test_operator();
        let owner = [0x01; 32];
        op.host_inbox(owner, 10, 500).unwrap(); // min_deposit = 500

        let msg = test_msg([0xBB; 32], b"cheap");
        let result = op.receive_message(&owner, msg, 100, 10); // Only 100 < 500
        assert!(matches!(
            result,
            Err(RelayError::InsufficientDeposit { .. })
        ));
    }
}
