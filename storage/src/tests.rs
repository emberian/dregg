//! Tests for pyana-storage.

use crate::content::ContentStore;
use crate::erasure::{self, ErasureEncoder};
use crate::inbox::{CapInbox, InboxError, InboxMessage};
use crate::metering::{self, MeteringPolicy, StorageOp};
use crate::queue::{MerkleQueue, QueueEntry, QueueError};
use crate::quota::SpaceBank;
use crate::relay::MeteredRelay;
use crate::{QuotaId, StorageError};

/// Helper: create a space bank with standard test parameters.
fn test_bank() -> SpaceBank {
    SpaceBank::new(
        10,   // cost_per_byte
        50,   // cost_per_relay_message
        0.8,  // refund_rate
    )
}

/// Helper: create a content store with one quota cell.
fn test_store(initial_computrons: u64) -> (ContentStore, QuotaId) {
    let mut bank = test_bank();
    let owner = [0xAA; 32];
    let id = bank.allocate_quota(owner, initial_computrons, None);
    (ContentStore::new(bank), id)
}

// ============================================================================
// Content store tests
// ============================================================================

#[test]
fn write_read_roundtrip() {
    let (mut store, payer) = test_store(100_000);
    let data = b"hello, content-addressed world!";
    let hash = store.write(data, &payer).unwrap();

    let read_back = store.read(&hash).unwrap();
    assert_eq!(read_back, data);
}

#[test]
fn write_exceeds_quota_error() {
    let (mut store, payer) = test_store(50); // Only 50 computrons
    let data = vec![0u8; 100]; // 100 bytes * 10 cost_per_byte = 1000 computrons needed

    let result = store.write(&data, &payer);
    assert!(result.is_err());
    match result.unwrap_err() {
        StorageError::QuotaExhausted { available, required } => {
            assert_eq!(available, 50);
            assert_eq!(required, 1000);
        }
        other => panic!("Expected QuotaExhausted, got {:?}", other),
    }
}

#[test]
fn write_exceeds_byte_cap() {
    let mut bank = test_bank();
    let owner = [0xBB; 32];
    let id = bank.allocate_quota(owner, 100_000, Some(50)); // 50 byte cap
    let mut store = ContentStore::new(bank);

    let data = vec![0u8; 100]; // 100 bytes exceeds 50 byte cap
    let result = store.write(&data, &id);
    assert!(result.is_err());
    match result.unwrap_err() {
        StorageError::ByteCapExceeded { current, max, attempted } => {
            assert_eq!(current, 0);
            assert_eq!(max, 50);
            assert_eq!(attempted, 100);
        }
        other => panic!("Expected ByteCapExceeded, got {:?}", other),
    }
}

#[test]
fn splice_updates_hash() {
    let (mut store, payer) = test_store(100_000);
    let data = b"hello world";
    let hash1 = store.write(data, &payer).unwrap();

    // Splice "world" -> "rust!" (offset 6, 5 bytes)
    let hash2 = store.splice(&hash1, 6, b"rust!", &payer).unwrap();

    assert_ne!(hash1, hash2);
    let read_back = store.read(&hash2).unwrap();
    assert_eq!(read_back, b"hello rust!");

    // Old hash should be gone.
    assert!(store.read(&hash1).is_none());
}

#[test]
fn delete_refunds_computrons() {
    let (mut store, payer) = test_store(100_000);
    let data = vec![0u8; 100]; // Cost: 100 * 10 = 1000
    let hash = store.write(&data, &payer).unwrap();

    let consumed_before = store.bank.get(&payer).unwrap().total_consumed;
    assert_eq!(consumed_before, 1000);

    let refund = store.delete(&hash, &payer).unwrap();
    // Refund rate is 0.8, so refund = 1000 * 0.8 = 800
    assert_eq!(refund.amount, 800);

    let consumed_after = store.bank.get(&payer).unwrap().total_consumed;
    assert_eq!(consumed_after, 200); // 1000 - 800
}

#[test]
fn quota_tracks_bytes_accurately() {
    let (mut store, payer) = test_store(100_000);

    let data1 = vec![1u8; 50];
    let data2 = vec![2u8; 75];
    let hash1 = store.write(&data1, &payer).unwrap();
    let _hash2 = store.write(&data2, &payer).unwrap();

    let cell = store.bank.get(&payer).unwrap();
    assert_eq!(cell.bytes_stored, 125); // 50 + 75

    store.delete(&hash1, &payer).unwrap();
    let cell = store.bank.get(&payer).unwrap();
    assert_eq!(cell.bytes_stored, 75); // Only data2 remains
}

#[test]
fn content_deduplication() {
    let (mut store, payer) = test_store(100_000);
    let data = b"duplicate me";

    let hash1 = store.write(data, &payer).unwrap();
    let hash2 = store.write(data, &payer).unwrap();

    assert_eq!(hash1, hash2);
    // Both writes charged.
    let cell = store.bank.get(&payer).unwrap();
    assert_eq!(cell.total_consumed, 2 * (data.len() as u64 * 10));
}

// ============================================================================
// Erasure coding tests
// ============================================================================

#[test]
fn erasure_encode_reconstruct_roundtrip() {
    let encoder = ErasureEncoder::new(32, 2);
    let data = b"the quick brown fox jumps over the lazy dog!!!!!";

    let chunks = encoder.encode(data);
    // With expansion_factor=2, we get 2N chunks.
    let n_data = (data.len() + 31) / 32;
    assert_eq!(chunks.len(), n_data * 2);

    // Reconstruct from all chunks.
    let recovered = encoder.reconstruct(&chunks, data.len()).unwrap();
    assert_eq!(recovered, data);
}

#[test]
fn erasure_reconstruct_with_data_chunks_only() {
    let encoder = ErasureEncoder::new(16, 2);
    let data = b"hello erasure coded world!";

    let chunks = encoder.encode(data);
    // Keep only data chunks.
    let data_chunks: Vec<_> = chunks.into_iter().filter(|c| !c.is_parity).collect();

    let recovered = encoder.reconstruct(&data_chunks, data.len()).unwrap();
    assert_eq!(recovered, data);
}

#[test]
fn erasure_fails_with_too_few_chunks() {
    let encoder = ErasureEncoder::new(16, 2);
    let data = b"need more chunks than this to reconstruct longer data yes indeed";

    let chunks = encoder.encode(data);
    let n_data = (data.len() + 15) / 16;

    // Keep only 1 chunk (need n_data).
    let too_few = &chunks[..1];

    let result = encoder.reconstruct(too_few, data.len());
    assert!(result.is_err());
    match result.unwrap_err() {
        erasure::ReconstructError::InsufficientChunks { have, need } => {
            assert!(have < need);
            assert_eq!(need, n_data);
        }
        other => panic!("Expected InsufficientChunks, got {:?}", other),
    }
}

#[test]
fn erasure_chunk_verification() {
    let encoder = ErasureEncoder::new(32, 2);
    let data = b"verify my chunks please";
    let chunks = encoder.encode(data);

    // All chunks should verify.
    for chunk in &chunks {
        assert!(erasure::verify_chunk(chunk));
    }

    // Tampered chunk should fail.
    let mut bad_chunk = chunks[0].clone();
    bad_chunk.data[0] ^= 0xFF;
    assert!(!erasure::verify_chunk(&bad_chunk));
}

#[test]
fn sampling_probability_calculation() {
    // All chunks available => confidence 1.0
    let conf = erasure::sample_availability(10, 10, 5);
    assert_eq!(conf, 1.0);

    // Zero chunks => 0.0
    let conf = erasure::sample_availability(0, 10, 5);
    assert_eq!(conf, 0.0);

    // 80% available, sample 10 => high confidence
    let conf = erasure::sample_availability(8, 10, 10);
    assert!(conf > 0.9);

    // 30% available, sample 5 => very low confidence
    let conf = erasure::sample_availability(3, 10, 5);
    assert!(conf < 0.01);
}

// ============================================================================
// Metering tests
// ============================================================================

#[test]
fn cost_computation_write() {
    let policy = MeteringPolicy::default_policy();
    let cost = metering::compute_cost(&policy, &StorageOp::Write { size: 100 });
    // base_cost(100) + 100 * cost_per_byte(10) = 1100
    assert_eq!(cost, 1100);
}

#[test]
fn cost_computation_relay() {
    let policy = MeteringPolicy::default_policy();
    let cost = metering::compute_cost(
        &policy,
        &StorageOp::Relay {
            size: 200,
            ttl_blocks: 10,
        },
    );
    // relay_base(50) + 200 * relay_cost_per_byte_block(5) * 10 = 50 + 10000 = 10050
    assert_eq!(cost, 10050);
}

#[test]
fn cost_computation_rental() {
    let policy = MeteringPolicy::default_policy();
    let cost = metering::compute_cost(
        &policy,
        &StorageOp::Rental {
            bytes: 1000,
            epochs: 5,
        },
    );
    // 1000 * rental_cost_per_byte_epoch(1) * 5 = 5000
    assert_eq!(cost, 5000);
}

#[test]
fn cost_computation_splice() {
    let policy = MeteringPolicy::default_policy();
    let cost = metering::compute_cost(
        &policy,
        &StorageOp::Splice {
            old_size: 100,
            new_size: 150,
        },
    );
    // Refund from old: (100 + 100*10) * 0.8 = 1100 * 0.8 = 880
    // New write: 100 + 150*10 = 1600
    // Net: 1600 - 880 = 720
    assert_eq!(cost, 720);
}

#[test]
fn refund_computation() {
    let policy = MeteringPolicy::default_policy();
    let refund = metering::compute_refund(&policy, &StorageOp::Write { size: 100 });
    // (100 + 100*10) * 0.8 = 1100 * 0.8 = 880
    assert_eq!(refund, 880);
}

// ============================================================================
// Relay tests
// ============================================================================

#[test]
fn relay_enqueue_and_drain() {
    let mut bank = test_bank();
    let owner = [0xCC; 32];
    let payer = bank.allocate_quota(owner, 1_000_000, None);

    let mut relay = MeteredRelay::new(bank, 1024, 100);
    let dest = [0xDD; 32];

    relay
        .enqueue(dest, b"hello offline node".to_vec(), 10, &payer)
        .unwrap();
    relay
        .enqueue(dest, b"second message".to_vec(), 5, &payer)
        .unwrap();

    assert_eq!(relay.total_buffered(), 2);
    assert_eq!(relay.buffered_for(&dest), 2);

    let messages = relay.drain(&dest);
    assert_eq!(messages.len(), 2);
    assert_eq!(messages[0].payload, b"hello offline node");
    assert_eq!(messages[1].payload, b"second message");
    assert_eq!(relay.total_buffered(), 0);
}

#[test]
fn relay_rejects_on_exhausted_quota() {
    let mut bank = test_bank();
    let owner = [0xEE; 32];
    let payer = bank.allocate_quota(owner, 100, None); // Very small quota

    let mut relay = MeteredRelay::new(bank, 1024, 100);
    let dest = [0xFF; 32];

    // This message costs: 50 (base) + 100 * 10 * 10 = 10050 computrons.
    let result = relay.enqueue(dest, vec![0u8; 100], 10, &payer);
    assert!(result.is_err());
    match result.unwrap_err() {
        crate::relay::RelayError::QuotaExhausted { available, required } => {
            assert_eq!(available, 100);
            assert!(required > 100);
        }
        other => panic!("Expected QuotaExhausted, got {:?}", other),
    }
}

#[test]
fn relay_ttl_expiry_refund() {
    let mut bank = test_bank();
    let owner = [0xAA; 32];
    let payer = bank.allocate_quota(owner, 1_000_000, None);

    let mut relay = MeteredRelay::new(bank, 1024, 100);
    let dest = [0xBB; 32];

    relay.enqueue(dest, b"will expire".to_vec(), 5, &payer).unwrap();
    assert_eq!(relay.total_buffered(), 1);

    // Advance past TTL.
    let refunds = relay.gc_expired(10);
    assert_eq!(refunds.len(), 1);
    assert!(refunds[0].amount > 0); // Got some refund.
    assert_eq!(relay.total_buffered(), 0);
}

#[test]
fn relay_message_too_large() {
    let mut bank = test_bank();
    let owner = [0xAA; 32];
    let payer = bank.allocate_quota(owner, 1_000_000, None);

    let mut relay = MeteredRelay::new(bank, 100, 100); // max 100 bytes
    let dest = [0xBB; 32];

    let result = relay.enqueue(dest, vec![0u8; 200], 5, &payer);
    assert!(result.is_err());
    match result.unwrap_err() {
        crate::relay::RelayError::MessageTooLarge { size, max } => {
            assert_eq!(size, 200);
            assert_eq!(max, 100);
        }
        other => panic!("Expected MessageTooLarge, got {:?}", other),
    }
}

// ============================================================================
// Space bank multi-tenant tests
// ============================================================================

#[test]
fn space_bank_multi_tenant_isolation() {
    let mut bank = test_bank();
    let alice = bank.allocate_quota([0x01; 32], 10_000, None);
    let bob = bank.allocate_quota([0x02; 32], 5_000, None);

    let mut store = ContentStore::new(bank);

    // Alice writes 50 bytes (cost: 500).
    let hash_a = store.write(&vec![0xAA; 50], &alice).unwrap();
    // Bob writes 30 bytes (cost: 300).
    let _hash_b = store.write(&vec![0xBB; 30], &bob).unwrap();

    // Alice's quota consumed: 500, Bob's: 300.
    assert_eq!(store.bank.get(&alice).unwrap().total_consumed, 500);
    assert_eq!(store.bank.get(&bob).unwrap().total_consumed, 300);
    assert_eq!(store.bank.get(&alice).unwrap().bytes_stored, 50);
    assert_eq!(store.bank.get(&bob).unwrap().bytes_stored, 30);

    // Bob cannot delete Alice's blob.
    let result = store.delete(&hash_a, &bob);
    assert!(result.is_err());
    match result.unwrap_err() {
        StorageError::NotOwner { owner, caller, .. } => {
            assert_eq!(owner, alice);
            assert_eq!(caller, bob);
        }
        other => panic!("Expected NotOwner, got {:?}", other),
    }
}

#[test]
fn rental_model_quota_depletes_over_epochs() {
    let mut bank = SpaceBank::new(10, 50, 0.8);
    let owner = [0x01; 32];
    let id = bank.allocate_quota(owner, 500, None);

    // Simulate storing 20 bytes.
    bank.charge_write(&id, 20).unwrap(); // Costs 200 computrons. Remaining: 300.

    // Each epoch costs 20 bytes * 10 cost_per_byte = 200 computrons for rental.
    // After tick_epoch: consumed goes up by 200. Remaining: 100.
    let depleted = bank.tick_epoch();
    assert!(depleted.is_empty());
    assert_eq!(bank.get(&id).unwrap().total_consumed, 400); // 200 write + 200 rental

    // After second tick_epoch: need 200 but only have 100. Depleted!
    let depleted = bank.tick_epoch();
    assert_eq!(depleted.len(), 1);
    assert_eq!(depleted[0], id);
}

#[test]
fn quota_top_up() {
    let mut bank = test_bank();
    let id = bank.allocate_quota([0x01; 32], 100, None);

    // Nearly exhausted.
    bank.charge_write(&id, 9).unwrap(); // 90 computrons.
    assert_eq!(bank.get(&id).unwrap().available(), 10);

    // Top up.
    bank.top_up(&id, 500).unwrap();
    assert_eq!(bank.get(&id).unwrap().available(), 510);

    // Can write more now.
    bank.charge_write(&id, 40).unwrap(); // 400 computrons.
    assert_eq!(bank.get(&id).unwrap().available(), 110);
}

// ============================================================================
// MerkleQueue tests (integration with metering)
// ============================================================================

#[test]
fn queue_enqueue_dequeue_roundtrip() {
    let mut q = MerkleQueue::new(10);
    let entry = QueueEntry {
        content_hash: *blake3::hash(b"test data").as_bytes(),
        sender: [0xAA; 32],
        deposit: 500,
        enqueued_at: 42,
        size: 9,
    };

    let root = q.enqueue(entry.clone()).unwrap();
    assert_ne!(root, [0u8; 32]);
    assert_eq!(q.len(), 1);

    let (dequeued, proof) = q.dequeue().unwrap();
    assert_eq!(dequeued, entry);
    assert_eq!(proof.old_root, root);
    assert_eq!(q.len(), 0);
}

#[test]
fn queue_root_changes_on_mutation() {
    let mut q = MerkleQueue::new(10);
    let empty_root = q.root();

    let e1 = QueueEntry {
        content_hash: *blake3::hash(b"first").as_bytes(),
        sender: [1u8; 32],
        deposit: 100,
        enqueued_at: 1,
        size: 5,
    };
    q.enqueue(e1).unwrap();
    let root_after_one = q.root();
    assert_ne!(empty_root, root_after_one);

    let e2 = QueueEntry {
        content_hash: *blake3::hash(b"second").as_bytes(),
        sender: [2u8; 32],
        deposit: 200,
        enqueued_at: 2,
        size: 6,
    };
    q.enqueue(e2).unwrap();
    let root_after_two = q.root();
    assert_ne!(root_after_one, root_after_two);
}

#[test]
fn queue_full_rejects() {
    let mut q = MerkleQueue::new(1);
    let e = QueueEntry {
        content_hash: [0xAB; 32],
        sender: [1u8; 32],
        deposit: 50,
        enqueued_at: 0,
        size: 10,
    };
    q.enqueue(e.clone()).unwrap();
    let result = q.enqueue(e);
    assert_eq!(result, Err(QueueError::Full { capacity: 1 }));
}

#[test]
fn queue_empty_dequeue_error() {
    let mut q = MerkleQueue::new(10);
    assert_eq!(q.dequeue(), Err(QueueError::Empty));
}

#[test]
fn queue_root_deterministic() {
    let entries: Vec<QueueEntry> = (0..3)
        .map(|i| QueueEntry {
            content_hash: *blake3::hash(&[i as u8; 16]).as_bytes(),
            sender: [i as u8; 32],
            deposit: (i + 1) * 100,
            enqueued_at: i,
            size: 16,
        })
        .collect();

    let mut q1 = MerkleQueue::new(10);
    let mut q2 = MerkleQueue::new(10);

    for e in &entries {
        q1.enqueue(e.clone()).unwrap();
        q2.enqueue(e.clone()).unwrap();
    }

    assert_eq!(q1.root(), q2.root());
}

#[test]
fn queue_dequeue_proof_verifiable() {
    let mut q = MerkleQueue::new(10);
    let e1 = QueueEntry {
        content_hash: *blake3::hash(b"alpha").as_bytes(),
        sender: [0x10; 32],
        deposit: 100,
        enqueued_at: 5,
        size: 5,
    };
    let e2 = QueueEntry {
        content_hash: *blake3::hash(b"beta").as_bytes(),
        sender: [0x20; 32],
        deposit: 200,
        enqueued_at: 6,
        size: 4,
    };

    q.enqueue(e1).unwrap();
    q.enqueue(e2).unwrap();

    let (_, proof) = q.dequeue().unwrap();
    assert!(crate::queue::verify_dequeue_proof(&proof));
    assert_ne!(proof.old_root, proof.new_root);
    assert_eq!(proof.position, 0);

    let (_, proof2) = q.dequeue().unwrap();
    assert!(crate::queue::verify_dequeue_proof(&proof2));
    // After last dequeue, new_root should be the empty root.
    assert_eq!(proof2.new_root, *blake3::hash(b"empty_queue").as_bytes());
}

// ============================================================================
// CapInbox tests (integration)
// ============================================================================

#[test]
fn inbox_receive_valid_deposit() {
    let mut inbox = CapInbox::new(QuotaId(1), 10, 100);
    let msg = InboxMessage::Capability {
        cert_bytes: vec![0xCA, 0xFE, 0xBA, 0xBE],
        sender: [0xAA; 32],
    };
    let result = inbox.receive(msg, 150);
    assert!(result.is_ok());
    assert_eq!(inbox.len(), 1);
}

#[test]
fn inbox_receive_insufficient_deposit() {
    let mut inbox = CapInbox::new(QuotaId(1), 10, 500);
    let msg = InboxMessage::Encrypted {
        ciphertext: vec![1, 2, 3, 4],
        sender: [0xBB; 32],
    };
    let result = inbox.receive(msg, 200);
    assert_eq!(
        result,
        Err(InboxError::InsufficientDeposit {
            provided: 200,
            minimum: 500,
        })
    );
}

#[test]
fn inbox_fifo_order() {
    let mut inbox = CapInbox::new(QuotaId(1), 10, 50);

    for i in 0u8..5 {
        let msg = InboxMessage::Encrypted {
            ciphertext: vec![i; 4],
            sender: [i; 32],
        };
        inbox.receive(msg, 100 + i as u64).unwrap();
    }

    for i in 0u8..5 {
        let (entry, _) = inbox.read_next().unwrap();
        assert_eq!(entry.sender, [i; 32]);
        assert_eq!(entry.deposit, 100 + i as u64);
    }
}

#[test]
fn inbox_full_bounces() {
    let mut inbox = CapInbox::new(QuotaId(1), 3, 10);
    let msg = InboxMessage::SturdyRef {
        uri: "test".to_string(),
        sender: [0x01; 32],
    };

    inbox.receive(msg.clone(), 10).unwrap();
    inbox.receive(msg.clone(), 10).unwrap();
    inbox.receive(msg.clone(), 10).unwrap();
    let result = inbox.receive(msg, 10);
    assert_eq!(result, Err(InboxError::Full { capacity: 3 }));
}

#[test]
fn inbox_gc_expired_keeps_deposits() {
    let mut inbox = CapInbox::new(QuotaId(1), 10, 50);

    let msg1 = InboxMessage::Capability {
        cert_bytes: vec![1],
        sender: [0x01; 32],
    };
    let msg2 = InboxMessage::Capability {
        cert_bytes: vec![2],
        sender: [0x02; 32],
    };

    inbox.receive_at(msg1, 1000, 10).unwrap(); // enqueued at block 10
    inbox.receive_at(msg2, 2000, 50).unwrap(); // enqueued at block 50

    // TTL = 20. At block 35: msg1 (10+20=30 < 35) expired, msg2 (50+20=70 > 35) alive.
    let refunds = inbox.gc_expired(35, 20);
    assert_eq!(inbox.len(), 1);
    assert_eq!(refunds.len(), 1);
    assert_eq!(refunds[0].amount, 900); // 1000 * 0.9
}

#[test]
fn inbox_different_message_types() {
    let mut inbox = CapInbox::new(QuotaId(1), 10, 10);

    let cap = InboxMessage::Capability {
        cert_bytes: vec![0xDE, 0xAD],
        sender: [0x01; 32],
    };
    let sref = InboxMessage::SturdyRef {
        uri: "cap://node/obj".to_string(),
        sender: [0x02; 32],
    };
    let enc = InboxMessage::Encrypted {
        ciphertext: vec![0xFF; 32],
        sender: [0x03; 32],
    };

    inbox.receive(cap, 100).unwrap();
    inbox.receive(sref, 100).unwrap();
    inbox.receive(enc, 100).unwrap();
    assert_eq!(inbox.len(), 3);

    let (e1, _) = inbox.read_next().unwrap();
    let (e2, _) = inbox.read_next().unwrap();
    let (e3, _) = inbox.read_next().unwrap();

    // All have different content hashes (different types/data).
    assert_ne!(e1.content_hash, e2.content_hash);
    assert_ne!(e2.content_hash, e3.content_hash);
}

// ============================================================================
// Metering: queue operation costs
// ============================================================================

#[test]
fn metering_queue_enqueue_cost() {
    let policy = MeteringPolicy::default_policy();
    let cost = metering::compute_cost(
        &policy,
        &StorageOp::Enqueue {
            size: 100,
            deposit: 500,
        },
    );
    // base(100) + size(100) * per_byte(10) + deposit(500) = 100 + 1000 + 500 = 1600
    assert_eq!(cost, 1600);
}

#[test]
fn metering_queue_dequeue_cost() {
    let policy = MeteringPolicy::default_policy();
    let cost = metering::compute_cost(&policy, &StorageOp::Dequeue { size: 100 });
    // Dequeue is free for reader.
    assert_eq!(cost, 0);
}

#[test]
fn metering_create_queue_cost() {
    let policy = MeteringPolicy::default_policy();
    let cost = metering::compute_cost(&policy, &StorageOp::CreateQueue { capacity: 50 });
    // base(100) + capacity(50) * per_byte(10) = 100 + 500 = 600
    assert_eq!(cost, 600);
}

#[test]
fn metering_resize_queue_cost() {
    let policy = MeteringPolicy::default_policy();

    // Growing.
    let cost = metering::compute_cost(
        &policy,
        &StorageOp::ResizeQueue {
            old_capacity: 10,
            new_capacity: 30,
        },
    );
    // delta(20) * per_byte(10) = 200
    assert_eq!(cost, 200);

    // Shrinking is free.
    let cost = metering::compute_cost(
        &policy,
        &StorageOp::ResizeQueue {
            old_capacity: 30,
            new_capacity: 10,
        },
    );
    assert_eq!(cost, 0);
}

// ============================================================================
// Integration: quota depletion prevents enqueue
// ============================================================================

#[test]
fn quota_depletion_prevents_enqueue() {
    // Simulate the scenario: sender's quota is too small to cover the deposit.
    let mut bank = test_bank();
    let sender_id = bank.allocate_quota([0x01; 32], 200, None);

    // The sender wants to enqueue with deposit 500.
    // Metering says the cost is: base(100) + size(10)*per_byte(10) + deposit(500) = 700.
    let policy = MeteringPolicy::default_policy();
    let cost = policy.compute_cost(&StorageOp::Enqueue {
        size: 10,
        deposit: 500,
    });
    assert_eq!(cost, 700);

    // Try to charge sender.
    let cell = bank.get_mut(&sender_id).unwrap();
    let result = cell.charge(cost);
    // Should fail: only 200 available, need 700.
    assert!(result.is_err());
    match result.unwrap_err() {
        StorageError::QuotaExhausted { available, required } => {
            assert_eq!(available, 200);
            assert_eq!(required, 700);
        }
        other => panic!("Expected QuotaExhausted, got {:?}", other),
    }
}
