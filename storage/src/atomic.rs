//! Cross-queue atomic operations.
//!
//! `QueueTransaction` provides atomic multi-queue transactions: all operations
//! commit or all abort. Enables patterns like "dequeue from A, enqueue to B"
//! atomically (no message lost, no double-processing).

use std::collections::HashMap;

use crate::queue::{DequeueProof, MerkleQueue, QueueEntry, QueueError};

// ============================================================================
// Core types
// ============================================================================

/// Atomic multi-queue transaction: all operations commit or all abort.
/// Enables patterns like: "dequeue from A, enqueue to B" atomically.
pub struct QueueTransaction {
    /// Operations to perform atomically.
    ops: Vec<QueueOp>,
    /// Transaction state.
    state: TxState,
}

/// A single operation within a transaction.
#[derive(Debug, Clone)]
pub enum QueueOp {
    /// Enqueue an entry to a queue.
    Enqueue { queue_id: [u8; 32], entry: QueueEntry },
    /// Dequeue from a queue.
    Dequeue { queue_id: [u8; 32] },
    /// Conditional: only proceed if queue root matches expected.
    AssertRoot { queue_id: [u8; 32], expected_root: [u8; 32] },
}

/// Transaction state machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TxState {
    Building,
    Committed,
    Aborted,
}

/// Result of executing a transaction.
#[derive(Debug, Clone)]
pub struct TxResult {
    /// Results per operation (in order).
    pub results: Vec<OpResult>,
    /// Combined root changes (queue_id, old_root, new_root) for each queue touched.
    pub root_transitions: Vec<([u8; 32], [u8; 32], [u8; 32])>,
}

/// Result of a single operation within a transaction.
#[derive(Debug, Clone)]
pub enum OpResult {
    /// Enqueue succeeded.
    Enqueued { new_root: [u8; 32] },
    /// Dequeue succeeded.
    Dequeued { entry: QueueEntry, proof: DequeueProof },
    /// Root assertion passed.
    Asserted,
}

/// Errors from transaction execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TxError {
    /// Transaction was already committed or aborted.
    InvalidState { state: &'static str },
    /// A queue referenced by the transaction was not found.
    QueueNotFound { queue_id: [u8; 32] },
    /// Root assertion failed (expected vs actual).
    RootMismatch { queue_id: [u8; 32], expected: [u8; 32], actual: [u8; 32] },
    /// A queue operation failed.
    QueueError { queue_id: [u8; 32], error: QueueError },
    /// Transaction has no operations.
    EmptyTransaction,
}

// ============================================================================
// Implementation
// ============================================================================

impl QueueTransaction {
    /// Create a new empty transaction (in building state).
    pub fn new() -> Self {
        Self {
            ops: Vec::new(),
            state: TxState::Building,
        }
    }

    /// Add an enqueue operation.
    pub fn enqueue(&mut self, queue_id: [u8; 32], entry: QueueEntry) -> &mut Self {
        self.ops.push(QueueOp::Enqueue { queue_id, entry });
        self
    }

    /// Add a dequeue operation.
    pub fn dequeue(&mut self, queue_id: [u8; 32]) -> &mut Self {
        self.ops.push(QueueOp::Dequeue { queue_id });
        self
    }

    /// Add a root assertion (conditional check).
    pub fn assert_root(&mut self, queue_id: [u8; 32], expected: [u8; 32]) -> &mut Self {
        self.ops.push(QueueOp::AssertRoot {
            queue_id,
            expected_root: expected,
        });
        self
    }

    /// Execute atomically: all ops succeed or all are rolled back.
    /// Returns the results of each operation.
    pub fn execute(
        mut self,
        queues: &mut HashMap<[u8; 32], MerkleQueue>,
    ) -> Result<TxResult, TxError> {
        if self.state != TxState::Building {
            let state_str = match self.state {
                TxState::Committed => "committed",
                TxState::Aborted => "aborted",
                TxState::Building => unreachable!(),
            };
            return Err(TxError::InvalidState { state: state_str });
        }

        if self.ops.is_empty() {
            return Err(TxError::EmptyTransaction);
        }

        // Snapshot all queues that will be touched, for rollback.
        let touched_ids: Vec<[u8; 32]> = self.ops.iter().map(|op| match op {
            QueueOp::Enqueue { queue_id, .. } => *queue_id,
            QueueOp::Dequeue { queue_id } => *queue_id,
            QueueOp::AssertRoot { queue_id, .. } => *queue_id,
        }).collect();

        // Verify all queues exist.
        for id in &touched_ids {
            if !queues.contains_key(id) {
                self.state = TxState::Aborted;
                return Err(TxError::QueueNotFound { queue_id: *id });
            }
        }

        // Snapshot old roots for rollback.
        let old_roots: HashMap<[u8; 32], [u8; 32]> = touched_ids
            .iter()
            .map(|id| (*id, queues[id].root()))
            .collect();

        // Snapshot clones for rollback.
        let snapshots: HashMap<[u8; 32], MerkleQueue> = touched_ids
            .iter()
            .map(|id| (*id, queues[id].clone()))
            .collect();

        // Execute operations sequentially.
        let mut results: Vec<OpResult> = Vec::new();

        for op in &self.ops {
            match op {
                QueueOp::Enqueue { queue_id, entry } => {
                    let queue = queues.get_mut(queue_id).unwrap();
                    match queue.enqueue(entry.clone()) {
                        Ok(new_root) => {
                            results.push(OpResult::Enqueued { new_root });
                        }
                        Err(e) => {
                            // Rollback.
                            self.rollback(queues, &snapshots);
                            self.state = TxState::Aborted;
                            return Err(TxError::QueueError { queue_id: *queue_id, error: e });
                        }
                    }
                }
                QueueOp::Dequeue { queue_id } => {
                    let queue = queues.get_mut(queue_id).unwrap();
                    match queue.dequeue() {
                        Ok((entry, proof)) => {
                            results.push(OpResult::Dequeued { entry, proof });
                        }
                        Err(e) => {
                            self.rollback(queues, &snapshots);
                            self.state = TxState::Aborted;
                            return Err(TxError::QueueError { queue_id: *queue_id, error: e });
                        }
                    }
                }
                QueueOp::AssertRoot { queue_id, expected_root } => {
                    let queue = queues.get(queue_id).unwrap();
                    let actual = queue.root();
                    if actual != *expected_root {
                        self.rollback(queues, &snapshots);
                        self.state = TxState::Aborted;
                        return Err(TxError::RootMismatch {
                            queue_id: *queue_id,
                            expected: *expected_root,
                            actual,
                        });
                    }
                    results.push(OpResult::Asserted);
                }
            }
        }

        // Compute root transitions.
        let mut root_transitions = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for id in &touched_ids {
            if seen.insert(*id) {
                let old = old_roots[id];
                let new = queues[id].root();
                if old != new {
                    root_transitions.push((*id, old, new));
                }
            }
        }

        self.state = TxState::Committed;
        Ok(TxResult {
            results,
            root_transitions,
        })
    }

    /// Compute the transaction hash (for Effect VM binding).
    /// This hash can be used as a public input to prove the atomic operation.
    pub fn tx_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"queue_tx_v1");

        for op in &self.ops {
            match op {
                QueueOp::Enqueue { queue_id, entry } => {
                    hasher.update(b"enqueue");
                    hasher.update(queue_id);
                    hasher.update(&entry.content_hash);
                    hasher.update(&entry.sender);
                    hasher.update(&entry.deposit.to_le_bytes());
                }
                QueueOp::Dequeue { queue_id } => {
                    hasher.update(b"dequeue");
                    hasher.update(queue_id);
                }
                QueueOp::AssertRoot { queue_id, expected_root } => {
                    hasher.update(b"assert_root");
                    hasher.update(queue_id);
                    hasher.update(expected_root);
                }
            }
        }

        *hasher.finalize().as_bytes()
    }

    /// Rollback all queues to their snapshots.
    fn rollback(
        &self,
        queues: &mut HashMap<[u8; 32], MerkleQueue>,
        snapshots: &HashMap<[u8; 32], MerkleQueue>,
    ) {
        for (id, snapshot) in snapshots {
            queues.insert(*id, snapshot.clone());
        }
    }
}

impl Default for QueueTransaction {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_entry(content: &[u8], sender: [u8; 32], deposit: u64) -> QueueEntry {
        QueueEntry {
            content_hash: *blake3::hash(content).as_bytes(),
            sender,
            deposit,
            enqueued_at: 100,
            size: content.len(),
        }
    }

    #[test]
    fn atomic_enqueue_dequeue_both_succeed() {
        let queue_a_id = [0x0A; 32];
        let queue_b_id = [0x0B; 32];

        let mut queues = HashMap::new();
        let mut qa = MerkleQueue::new(10);
        qa.enqueue(make_entry(b"transfer_me", [0xAA; 32], 500)).unwrap();
        queues.insert(queue_a_id, qa);
        queues.insert(queue_b_id, MerkleQueue::new(10));

        // Atomically: dequeue from A, enqueue to B.
        let entry_to_move = make_entry(b"transfer_me", [0xAA; 32], 500);
        let mut tx = QueueTransaction::new();
        tx.dequeue(queue_a_id)
          .enqueue(queue_b_id, entry_to_move);

        let result = tx.execute(&mut queues).unwrap();
        assert_eq!(result.results.len(), 2);
        assert!(matches!(&result.results[0], OpResult::Dequeued { .. }));
        assert!(matches!(&result.results[1], OpResult::Enqueued { .. }));

        // A is empty, B has 1.
        assert_eq!(queues.get(&queue_a_id).unwrap().len(), 0);
        assert_eq!(queues.get(&queue_b_id).unwrap().len(), 1);
    }

    #[test]
    fn atomic_assert_root_fails_aborts_all() {
        let queue_a_id = [0x0A; 32];
        let queue_b_id = [0x0B; 32];

        let mut queues = HashMap::new();
        let mut qa = MerkleQueue::new(10);
        qa.enqueue(make_entry(b"msg", [0xAA; 32], 100)).unwrap();
        let qa_root = qa.root();
        queues.insert(queue_a_id, qa);
        queues.insert(queue_b_id, MerkleQueue::new(10));

        // Transaction: assert wrong root on A -> should abort everything.
        let wrong_root = [0xFF; 32];
        let entry = make_entry(b"should_not_land", [0xBB; 32], 200);
        let mut tx = QueueTransaction::new();
        tx.enqueue(queue_b_id, entry)
          .assert_root(queue_a_id, wrong_root);

        let result = tx.execute(&mut queues);
        assert!(matches!(result, Err(TxError::RootMismatch { .. })));

        // B should still be empty (rolled back).
        assert_eq!(queues.get(&queue_b_id).unwrap().len(), 0);
        // A should be unchanged.
        assert_eq!(queues.get(&queue_a_id).unwrap().root(), qa_root);
    }

    #[test]
    fn atomic_dequeue_from_empty_aborts() {
        let queue_a_id = [0x0A; 32];
        let queue_b_id = [0x0B; 32];

        let mut queues = HashMap::new();
        queues.insert(queue_a_id, MerkleQueue::new(10)); // empty
        queues.insert(queue_b_id, MerkleQueue::new(10));

        let entry = make_entry(b"msg", [0xAA; 32], 100);
        let mut tx = QueueTransaction::new();
        tx.enqueue(queue_b_id, entry)
          .dequeue(queue_a_id); // will fail: empty

        let result = tx.execute(&mut queues);
        assert!(matches!(result, Err(TxError::QueueError { error: QueueError::Empty, .. })));

        // B should be rolled back (empty).
        assert_eq!(queues.get(&queue_b_id).unwrap().len(), 0);
    }

    #[test]
    fn tx_hash_is_deterministic() {
        let entry = make_entry(b"hello", [0xAA; 32], 100);

        let mut tx1 = QueueTransaction::new();
        tx1.enqueue([0x01; 32], entry.clone())
           .dequeue([0x02; 32]);

        let mut tx2 = QueueTransaction::new();
        tx2.enqueue([0x01; 32], entry.clone())
           .dequeue([0x02; 32]);

        assert_eq!(tx1.tx_hash(), tx2.tx_hash());

        // Different ops -> different hash.
        let mut tx3 = QueueTransaction::new();
        tx3.enqueue([0x01; 32], entry)
           .dequeue([0x03; 32]); // different queue

        assert_ne!(tx1.tx_hash(), tx3.tx_hash());
    }

    #[test]
    fn atomic_assert_root_succeeds_when_correct() {
        let queue_id = [0x01; 32];

        let mut queues = HashMap::new();
        let mut q = MerkleQueue::new(10);
        q.enqueue(make_entry(b"existing", [0xAA; 32], 100)).unwrap();
        let current_root = q.root();
        queues.insert(queue_id, q);

        // Assert correct root then enqueue.
        let entry = make_entry(b"new_msg", [0xBB; 32], 200);
        let mut tx = QueueTransaction::new();
        tx.assert_root(queue_id, current_root)
          .enqueue(queue_id, entry);

        let result = tx.execute(&mut queues).unwrap();
        assert_eq!(result.results.len(), 2);
        assert!(matches!(&result.results[0], OpResult::Asserted));
        assert!(matches!(&result.results[1], OpResult::Enqueued { .. }));
        assert_eq!(queues.get(&queue_id).unwrap().len(), 2);
    }

    #[test]
    fn empty_transaction_returns_error() {
        let mut queues: HashMap<[u8; 32], MerkleQueue> = HashMap::new();
        let tx = QueueTransaction::new();
        let result = tx.execute(&mut queues);
        assert!(matches!(result, Err(TxError::EmptyTransaction)));
    }
}
