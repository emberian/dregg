//! Pub-sub in multi-node simulation context.
//!
//! Exercises topic creation, subscriber management, independent cursor tracking,
//! lag monitoring, GC of consumed entries, subscriber caps, and fee model.

use pyana_storage::pubsub::{PubSubError, PubSubTopic};
use pyana_teasting::harness::SimulationHarness;

/// Deterministic identity from a seed byte.
fn identity(n: u8) -> [u8; 32] {
    [n; 32]
}

/// Create a hash from data for publishing.
fn data_hash(data: &[u8]) -> [u8; 32] {
    *blake3::hash(data).as_bytes()
}

// ---------------------------------------------------------------------------
// Test 1: Publisher creates topic, subscribers join
// ---------------------------------------------------------------------------
#[test]
fn publisher_creates_topic_subscribers_join() {
    let _harness = SimulationHarness::new_federation(3);

    let publisher = identity(0xAA);
    let mut topic = PubSubTopic::new(publisher, "market-data".to_string(), 100, 10);

    assert_eq!(topic.name(), "market-data");
    assert_eq!(topic.publisher(), &publisher);
    assert_eq!(topic.subscriber_count(), 0);
    assert_eq!(topic.total_published(), 0);

    // Subscribers join.
    let sub1 = identity(0x01);
    let sub2 = identity(0x02);
    let sub3 = identity(0x03);

    topic.subscribe(sub1).unwrap();
    topic.subscribe(sub2).unwrap();
    topic.subscribe(sub3).unwrap();

    assert_eq!(topic.subscriber_count(), 3);

    // All start with 0 lag (subscribed before any messages).
    assert_eq!(topic.subscriber_lag(&sub1), Some(0));
    assert_eq!(topic.subscriber_lag(&sub2), Some(0));
    assert_eq!(topic.subscriber_lag(&sub3), Some(0));
}

// ---------------------------------------------------------------------------
// Test 2: Publisher publishes -> all subscribers can read (different cursors)
// ---------------------------------------------------------------------------
#[test]
fn publisher_publishes_all_subscribers_read_independently() {
    let mut harness = SimulationHarness::new_federation(3);

    let publisher = identity(0xAA);
    let mut topic = PubSubTopic::new(publisher, "events".to_string(), 100, 10);

    let sub_a = identity(0x01);
    let sub_b = identity(0x02);
    topic.subscribe(sub_a).unwrap();
    topic.subscribe(sub_b).unwrap();

    // Publish 3 messages.
    let messages: Vec<[u8; 32]> = (0u8..3)
        .map(|i| {
            harness.advance_blocks(1);
            let hash = data_hash(&[i; 16]);
            topic
                .publish_at(&publisher, hash, 100, harness.clock.block_height)
                .unwrap();
            hash
        })
        .collect();

    assert_eq!(topic.total_published(), 3);

    // Sub A reads all 3.
    for expected_hash in &messages {
        let entry = topic.read_next(&sub_a).unwrap().unwrap();
        assert_eq!(&entry.content_hash, expected_hash);
    }
    // Sub A is caught up.
    assert!(topic.read_next(&sub_a).unwrap().is_none());
    assert_eq!(topic.subscriber_lag(&sub_a), Some(0));

    // Sub B reads only the first one.
    let entry = topic.read_next(&sub_b).unwrap().unwrap();
    assert_eq!(entry.content_hash, messages[0]);
    assert_eq!(topic.subscriber_lag(&sub_b), Some(2));
}

// ---------------------------------------------------------------------------
// Test 3: Subscriber lag tracking (slow subscriber falls behind)
// ---------------------------------------------------------------------------
#[test]
fn subscriber_lag_tracks_slow_reader() {
    let mut harness = SimulationHarness::new_federation(3);

    let publisher = identity(0xAA);
    let mut topic = PubSubTopic::new(publisher, "firehose".to_string(), 1000, 10);

    let fast_sub = identity(0x01);
    let slow_sub = identity(0x02);
    topic.subscribe(fast_sub).unwrap();
    topic.subscribe(slow_sub).unwrap();

    // Publish 10 messages.
    for i in 0u8..10 {
        harness.advance_blocks(1);
        let hash = data_hash(&[i; 8]);
        topic
            .publish_at(&publisher, hash, 50, harness.clock.block_height)
            .unwrap();
    }

    // Fast sub reads all 10.
    for _ in 0..10 {
        topic.read_next(&fast_sub).unwrap().unwrap();
    }
    assert_eq!(topic.subscriber_lag(&fast_sub), Some(0));

    // Slow sub reads 3.
    for _ in 0..3 {
        topic.read_next(&slow_sub).unwrap().unwrap();
    }
    assert_eq!(topic.subscriber_lag(&slow_sub), Some(7));

    // Publish 5 more.
    for i in 10u8..15 {
        harness.advance_blocks(1);
        let hash = data_hash(&[i; 8]);
        topic
            .publish_at(&publisher, hash, 50, harness.clock.block_height)
            .unwrap();
    }

    // Fast sub now has 5 unread, slow sub has 12.
    assert_eq!(topic.subscriber_lag(&fast_sub), Some(5));
    assert_eq!(topic.subscriber_lag(&slow_sub), Some(12));
}

// ---------------------------------------------------------------------------
// Test 4: GC consumed: entries all subs have read get cleaned up
// ---------------------------------------------------------------------------
#[test]
fn gc_consumed_removes_entries_read_by_all() {
    let _harness = SimulationHarness::new_federation(3);

    let publisher = identity(0xAA);
    let mut topic = PubSubTopic::new(publisher, "gc-test".to_string(), 100, 10);

    let sub_a = identity(0x01);
    let sub_b = identity(0x02);
    topic.subscribe(sub_a).unwrap();
    topic.subscribe(sub_b).unwrap();

    // Publish 5 messages.
    for i in 0u8..5 {
        let hash = data_hash(&[i; 4]);
        topic.publish(&publisher, hash, 20).unwrap();
    }
    assert_eq!(topic.pending_count(), 5);

    // Sub A reads all 5, Sub B reads 3.
    for _ in 0..5 {
        topic.read_next(&sub_a).unwrap();
    }
    for _ in 0..3 {
        topic.read_next(&sub_b).unwrap();
    }

    // GC: min cursor is sub_b at position 3. Can remove first 3 entries.
    let removed = topic.gc_consumed();
    assert_eq!(removed, 3);
    assert_eq!(topic.pending_count(), 2); // Only entries 3 and 4 remain.

    // Sub B can still read the remaining 2.
    let entry = topic.read_next(&sub_b).unwrap().unwrap();
    assert_eq!(entry.content_hash, data_hash(&[3u8; 4]));
    let entry = topic.read_next(&sub_b).unwrap().unwrap();
    assert_eq!(entry.content_hash, data_hash(&[4u8; 4]));

    // Now all caught up.
    assert!(topic.read_next(&sub_b).unwrap().is_none());
}

// ---------------------------------------------------------------------------
// Test 5: Max subscribers enforced
// ---------------------------------------------------------------------------
#[test]
fn max_subscribers_enforced() {
    let _harness = SimulationHarness::new_federation(3);

    let publisher = identity(0xAA);
    let mut topic = PubSubTopic::new(publisher, "exclusive".to_string(), 100, 3); // max 3 subs

    topic.subscribe(identity(0x01)).unwrap();
    topic.subscribe(identity(0x02)).unwrap();
    topic.subscribe(identity(0x03)).unwrap();
    assert_eq!(topic.subscriber_count(), 3);

    // Fourth subscriber rejected.
    let result = topic.subscribe(identity(0x04));
    assert_eq!(result, Err(PubSubError::MaxSubscribers { max: 3 }));

    // Unsubscribe one, then the fourth can join.
    topic.unsubscribe(&identity(0x01));
    assert_eq!(topic.subscriber_count(), 2);

    topic.subscribe(identity(0x04)).unwrap();
    assert_eq!(topic.subscriber_count(), 3);
}

// ---------------------------------------------------------------------------
// Test 6: Publisher pays for all writes; subscribers read free
// ---------------------------------------------------------------------------
#[test]
fn publisher_pays_subscribers_read_free() {
    let mut harness = SimulationHarness::new_federation(3);

    let publisher = identity(0xAA);
    let mut topic = PubSubTopic::new(publisher, "paid-writes".to_string(), 100, 10);

    let sub = identity(0x01);
    topic.subscribe(sub).unwrap();

    // Only the publisher can write (pays deposit per entry).
    let deposit = 500u64;
    harness.advance_blocks(1);
    let hash = data_hash(b"publisher-pays");
    topic
        .publish_at(&publisher, hash, deposit, harness.clock.block_height)
        .unwrap();

    // Imposter cannot write.
    let imposter = identity(0xFF);
    let result = topic.publish(&imposter, data_hash(b"nope"), 500);
    assert_eq!(result, Err(PubSubError::NotPublisher));

    // Subscriber reads without paying anything (free read).
    let entry = topic.read_next(&sub).unwrap().unwrap();
    assert_eq!(entry.content_hash, hash);
    assert_eq!(entry.deposit, deposit); // Records publisher's deposit.
    // Subscriber identity is not the sender (publisher is).
    assert_eq!(entry.sender, publisher);
}

// ---------------------------------------------------------------------------
// Test 7 (bonus): Late subscriber only sees new messages
// ---------------------------------------------------------------------------
#[test]
fn late_subscriber_only_sees_new_messages() {
    let _harness = SimulationHarness::new_federation(3);

    let publisher = identity(0xAA);
    let mut topic = PubSubTopic::new(publisher, "late-join".to_string(), 100, 10);

    let early_sub = identity(0x01);
    topic.subscribe(early_sub).unwrap();

    // Publish 3 messages before late subscriber joins.
    for i in 0u8..3 {
        topic.publish(&publisher, data_hash(&[i]), 10).unwrap();
    }

    // Late subscriber joins.
    let late_sub = identity(0x02);
    topic.subscribe(late_sub).unwrap();

    // Late sub has 0 lag (starts at current tail).
    assert_eq!(topic.subscriber_lag(&late_sub), Some(0));
    assert!(topic.read_next(&late_sub).unwrap().is_none());

    // Publish 2 more.
    let new_hash_1 = data_hash(b"new-1");
    let new_hash_2 = data_hash(b"new-2");
    topic.publish(&publisher, new_hash_1, 10).unwrap();
    topic.publish(&publisher, new_hash_2, 10).unwrap();

    // Late sub sees only the 2 new ones.
    assert_eq!(topic.subscriber_lag(&late_sub), Some(2));
    let entry = topic.read_next(&late_sub).unwrap().unwrap();
    assert_eq!(entry.content_hash, new_hash_1);
    let entry = topic.read_next(&late_sub).unwrap().unwrap();
    assert_eq!(entry.content_hash, new_hash_2);

    // Early sub still has 5 unread (3 old + 2 new).
    assert_eq!(topic.subscriber_lag(&early_sub), Some(5));
}

// ---------------------------------------------------------------------------
// Test 8 (bonus): Duplicate subscription fails
// ---------------------------------------------------------------------------
#[test]
fn duplicate_subscription_fails() {
    let _harness = SimulationHarness::new_federation(3);

    let publisher = identity(0xAA);
    let mut topic = PubSubTopic::new(publisher, "dedup".to_string(), 100, 10);

    let sub = identity(0x01);
    topic.subscribe(sub).unwrap();

    let result = topic.subscribe(sub);
    assert_eq!(result, Err(PubSubError::AlreadySubscribed));
}
