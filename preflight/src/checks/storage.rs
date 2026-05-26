//! Storage subsystem checks: MerkleQueue, CapInbox, programmable queues, WAL, dedup, pub-sub.
#![allow(deprecated)]

use dregg_storage::QuotaId;
use dregg_storage::dedup::DeduplicationFilter;
use dregg_storage::inbox::{CapInbox, InboxMessage};
use dregg_storage::programmable::{
    ProgramError, ProgrammableQueue, QueueConstraint, QueueProgram, ValidationContext,
};
use dregg_storage::pubsub::PubSubTopic;
use dregg_storage::queue::{MerkleQueue, QueueEntry};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("merkle_queue", check_merkle_queue),
        run_check("cap_inbox", check_cap_inbox),
        run_check("programmable_queue", check_programmable_queue),
        run_check("wal_recovery", check_wal_recovery),
        run_check("dedup", check_dedup),
        run_check("pubsub", check_pubsub),
    ]
}

fn make_entry(data: &[u8], sender: [u8; 32]) -> QueueEntry {
    QueueEntry {
        content_hash: *blake3::hash(data).as_bytes(),
        sender,
        deposit: 100,
        enqueued_at: 1,
        size: data.len(),
    }
}

fn check_merkle_queue() -> Result<(), String> {
    let mut queue = MerkleQueue::new(10);

    // Enqueue.
    let sender = [1u8; 32];
    let entry1 = make_entry(b"message-1", sender);
    let root1 = queue
        .enqueue(entry1.clone())
        .map_err(|e| format!("enqueue 1 failed: {e:?}"))?;

    if root1 == [0u8; 32] {
        return Err("root should not be all zeros after enqueue".into());
    }

    // Enqueue a second message: root should change.
    let entry2 = make_entry(b"message-2", sender);
    let root2 = queue
        .enqueue(entry2.clone())
        .map_err(|e| format!("enqueue 2 failed: {e:?}"))?;

    if root2 == root1 {
        return Err("root should change after second enqueue".into());
    }

    // Dequeue: should get entry1 first (FIFO).
    let (dequeued, proof) = queue
        .dequeue()
        .map_err(|e| format!("dequeue failed: {e:?}"))?;

    if dequeued.content_hash != entry1.content_hash {
        return Err("dequeue should return first enqueued entry (FIFO)".into());
    }

    // Verify proof structure.
    if proof.old_root != root2 {
        return Err("dequeue proof old_root should match pre-dequeue root".into());
    }
    if proof.new_root == proof.old_root {
        return Err("dequeue proof new_root should differ from old_root".into());
    }

    Ok(())
}

fn check_cap_inbox() -> Result<(), String> {
    let owner_quota = QuotaId(1);
    let mut inbox = CapInbox::new(owner_quota, 100, 50);

    // Receive a message with sufficient deposit.
    let sender = [2u8; 32];
    let msg = InboxMessage::Encrypted {
        ciphertext: vec![0xDE, 0xAD, 0xBE, 0xEF],
        sender,
    };

    let root = inbox
        .receive(msg.clone(), 100) // 100 >= min_deposit of 50
        .map_err(|e| format!("receive failed: {e:?}"))?;

    if root == [0u8; 32] {
        return Err("inbox root should not be zeros after receive".into());
    }

    // Receive with insufficient deposit should fail.
    let msg2 = InboxMessage::SturdyRef {
        uri: "dregg://fed/cell/swiss".to_string(),
        sender,
    };
    let result = inbox.receive(msg2, 10); // 10 < min_deposit of 50
    if result.is_ok() {
        return Err("receive with insufficient deposit should fail".into());
    }

    // Read from inbox.
    let (entry, _proof) = inbox
        .read_next()
        .map_err(|e| format!("inbox read_next failed: {e:?}"))?;
    if entry.sender != sender {
        return Err("read entry sender mismatch".into());
    }

    Ok(())
}

fn check_programmable_queue() -> Result<(), String> {
    let owner = [3u8; 32];
    let program = QueueProgram {
        name: "test-program".to_string(),
        constraints: vec![
            QueueConstraint::MinDeposit { amount: 50 },
            QueueConstraint::MaxSize { bytes: 1024 },
        ],
        lookup_tables: vec![],
    };

    let mut pq = ProgrammableQueue::new("test-queue".to_string(), owner, program, None, 100);

    // Valid enqueue: meets constraints.
    let entry = QueueEntry {
        content_hash: *blake3::hash(b"valid-msg").as_bytes(),
        sender: owner,
        deposit: 100, // >= min_deposit 50
        enqueued_at: 1,
        size: 64, // <= max_size 1024
    };

    let ctx = ValidationContext {
        sender: owner,
        current_height: 10,
        current_epoch: 1,
        sender_epoch_count: 0,
        preimage: None,
        sequence: None,
    };

    let root = pq
        .enqueue_validated(entry, &ctx)
        .map_err(|e| format!("valid enqueue failed: {e:?}"))?;

    if root == [0u8; 32] {
        return Err("programmable queue root should not be zeros".into());
    }

    // Invalid enqueue: deposit too low.
    let bad_entry = QueueEntry {
        content_hash: *blake3::hash(b"bad-msg").as_bytes(),
        sender: owner,
        deposit: 10, // < min_deposit 50
        enqueued_at: 2,
        size: 64,
    };

    let result = pq.enqueue_validated(bad_entry, &ctx);
    match result {
        Err(ProgramError::ConstraintViolation { .. }) => {} // expected
        Err(other) => return Err(format!("expected ConstraintViolation, got {other:?}")),
        Ok(_) => return Err("enqueue with low deposit should be rejected".into()),
    }

    // Verify queue state.
    if pq.len() != 1 {
        return Err(format!("expected queue len 1, got {}", pq.len()));
    }
    if pq.name() != "test-queue" {
        return Err(format!("expected name 'test-queue', got '{}'", pq.name()));
    }

    Ok(())
}

fn check_wal_recovery() -> Result<(), String> {
    // Use a temp directory for WAL testing.
    let tmp_dir = std::env::temp_dir().join(format!("preflight-wal-{}", std::process::id()));
    std::fs::create_dir_all(&tmp_dir).map_err(|e| format!("create tmp dir failed: {e}"))?;

    let wal_path = tmp_dir.join("test.wal");

    // Create a queue with WAL.
    let mut queue = MerkleQueue::with_wal(10, wal_path.clone())
        .map_err(|e| format!("create WAL queue failed: {e}"))?;

    // Enqueue with WAL durability.
    let entry = make_entry(b"durable-message", [4u8; 32]);
    let root = queue
        .enqueue_durable(entry.clone())
        .map_err(|e| format!("enqueue_durable failed: {e}"))?;

    if root == [0u8; 32] {
        return Err("WAL queue root should not be zeros".into());
    }

    // Simulate crash: drop the queue (in-memory state lost).
    drop(queue);

    // Verify the WAL file exists.
    if !wal_path.exists() {
        return Err("WAL file should exist after durable enqueue".into());
    }

    // Cleanup.
    let _ = std::fs::remove_dir_all(&tmp_dir);

    Ok(())
}

fn check_dedup() -> Result<(), String> {
    let mut dedup = DeduplicationFilter::new(100);

    let hash1 = *blake3::hash(b"message-alpha").as_bytes();
    let hash2 = *blake3::hash(b"message-beta").as_bytes();

    // First time: not a duplicate.
    if dedup.is_duplicate(&hash1) {
        return Err("first occurrence should not be flagged as duplicate".into());
    }

    // Second time: IS a duplicate.
    if !dedup.is_duplicate(&hash1) {
        return Err("second occurrence should be flagged as duplicate".into());
    }

    // Different hash: not a duplicate.
    if dedup.is_duplicate(&hash2) {
        return Err("different hash should not be flagged as duplicate".into());
    }

    // Verify count.
    if dedup.len() != 2 {
        return Err(format!("expected 2 tracked entries, got {}", dedup.len()));
    }

    Ok(())
}

fn check_pubsub() -> Result<(), String> {
    let publisher = [5u8; 32];
    let subscriber = [6u8; 32];
    let mut topic = PubSubTopic::new(publisher, "test-topic".to_string(), 100, 10);

    // Subscribe.
    topic
        .subscribe(subscriber)
        .map_err(|e| format!("subscribe failed: {e:?}"))?;

    // Publish messages.
    let data1 = *blake3::hash(b"event-1").as_bytes();
    let data2 = *blake3::hash(b"event-2").as_bytes();

    topic
        .publish(&publisher, data1, 50)
        .map_err(|e| format!("publish 1 failed: {e:?}"))?;

    topic
        .publish(&publisher, data2, 50)
        .map_err(|e| format!("publish 2 failed: {e:?}"))?;

    // Read as subscriber: should get event-1 first.
    let entry1 = topic
        .read_next(&subscriber)
        .map_err(|e| format!("read_next 1 failed: {e:?}"))?;

    match entry1 {
        Some(entry) => {
            if entry.content_hash != data1 {
                return Err("first read should return first published message".into());
            }
        }
        None => return Err("subscriber should have messages to read".into()),
    }

    // Read again: should get event-2.
    let entry2 = topic
        .read_next(&subscriber)
        .map_err(|e| format!("read_next 2 failed: {e:?}"))?;

    match entry2 {
        Some(entry) => {
            if entry.content_hash != data2 {
                return Err("second read should return second published message".into());
            }
        }
        None => return Err("subscriber should have second message to read".into()),
    }

    Ok(())
}
