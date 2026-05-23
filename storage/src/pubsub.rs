//! Pub-sub topics: one publisher, multiple subscriber cursors over a shared queue.
//!
//! Publisher pays for writes. Readers read for free (already paid by publisher).
//! Each subscriber has an independent cursor into the shared queue.

use std::collections::HashMap;

use crate::dedup::DeduplicationFilter;
use crate::queue::{MerkleQueue, QueueEntry, QueueError};

/// Errors from pub-sub operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PubSubError {
    /// Queue is full.
    QueueFull { capacity: usize },
    /// Subscriber already exists.
    AlreadySubscribed,
    /// Subscriber not found.
    NotSubscribed,
    /// Maximum subscribers reached.
    MaxSubscribers { max: usize },
    /// Publisher identity mismatch.
    NotPublisher,
}

/// Result of an idempotent publish operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PublishResult {
    /// A new message was published.
    New { root: [u8; 32] },
    /// The message was a duplicate (already published).
    Duplicate { existing_position: usize },
}

impl From<QueueError> for PubSubError {
    fn from(e: QueueError) -> Self {
        match e {
            QueueError::Full { capacity } => PubSubError::QueueFull { capacity },
            QueueError::Empty => unreachable!("empty queue should not produce PubSubError"),
        }
    }
}

/// A pub-sub topic: one writer (publisher), multiple readers (subscribers).
/// Each subscriber has their own cursor (head pointer) into the shared queue.
/// Publisher pays for writes. Readers read for free (already paid by publisher).
/// Subscribers can be added/removed dynamically.
#[derive(Debug, Clone)]
pub struct PubSubTopic {
    /// The underlying queue (shared among all readers).
    queue: MerkleQueue,
    /// Per-subscriber read cursors (maps subscriber ID -> index into entries).
    cursors: HashMap<[u8; 32], usize>,
    /// Publisher (who pays for writes).
    publisher: [u8; 32],
    /// Topic metadata.
    name: String,
    /// Discovery tags.
    tags: Vec<String>,
    /// Max subscribers (bounded by publisher's quota).
    max_subscribers: usize,
    /// Deduplication filter for idempotent publish.
    dedup: DeduplicationFilter,
}

impl PubSubTopic {
    /// Create a new pub-sub topic.
    ///
    /// # Arguments
    /// * `publisher` - The identity of the publisher (who pays for writes).
    /// * `name` - Human-readable topic name.
    /// * `capacity` - Maximum number of entries the underlying queue can hold.
    /// * `max_subscribers` - Maximum number of subscribers allowed.
    pub fn new(publisher: [u8; 32], name: String, capacity: usize, max_subscribers: usize) -> Self {
        Self {
            queue: MerkleQueue::new(capacity),
            cursors: HashMap::new(),
            publisher,
            name,
            tags: Vec::new(),
            max_subscribers,
            dedup: DeduplicationFilter::new(capacity * 2),
        }
    }

    /// Create a new pub-sub topic with tags.
    pub fn with_tags(
        publisher: [u8; 32],
        name: String,
        capacity: usize,
        max_subscribers: usize,
        tags: Vec<String>,
    ) -> Self {
        Self {
            queue: MerkleQueue::new(capacity),
            cursors: HashMap::new(),
            publisher,
            name,
            tags,
            max_subscribers,
            dedup: DeduplicationFilter::new(capacity * 2),
        }
    }

    /// Publish a message to the topic. Only the publisher can write.
    ///
    /// Returns the new queue root on success.
    pub fn publish(
        &mut self,
        publisher: &[u8; 32],
        data_hash: [u8; 32],
        deposit: u64,
    ) -> Result<[u8; 32], PubSubError> {
        if publisher != &self.publisher {
            return Err(PubSubError::NotPublisher);
        }

        let entry = QueueEntry {
            content_hash: data_hash,
            sender: self.publisher,
            deposit,
            enqueued_at: 0, // Caller should set from block height.
            size: 32, // Hash reference; actual data stored externally.
        };

        let root = self.queue.enqueue(entry)?;
        Ok(root)
    }

    /// Publish with a block height timestamp.
    pub fn publish_at(
        &mut self,
        publisher: &[u8; 32],
        data_hash: [u8; 32],
        deposit: u64,
        block_height: u64,
    ) -> Result<[u8; 32], PubSubError> {
        if publisher != &self.publisher {
            return Err(PubSubError::NotPublisher);
        }

        let entry = QueueEntry {
            content_hash: data_hash,
            sender: self.publisher,
            deposit,
            enqueued_at: block_height,
            size: 32,
        };

        let root = self.queue.enqueue(entry)?;
        Ok(root)
    }

    /// Publish with deduplication. If data_hash was already published, returns
    /// the existing entry (idempotent). Callers retrying after timeout get
    /// the same result without creating duplicates.
    pub fn publish_idempotent(
        &mut self,
        publisher: &[u8; 32],
        data_hash: [u8; 32],
        deposit: u64,
    ) -> Result<PublishResult, PubSubError> {
        if publisher != &self.publisher {
            return Err(PubSubError::NotPublisher);
        }

        // Check dedup filter.
        if self.dedup.is_duplicate(&data_hash) {
            // Find the position of the existing entry.
            let head = self.queue.head_position();
            let tail = self.queue.tail();
            for idx in head..tail {
                if let Some(entry) = self.peek_at(idx)
                    && entry.content_hash == data_hash
                {
                    return Ok(PublishResult::Duplicate {
                        existing_position: idx,
                    });
                }
            }
            // If we can't find it (was GC'd), treat it as already-published.
            return Ok(PublishResult::Duplicate {
                existing_position: 0,
            });
        }

        let entry = QueueEntry {
            content_hash: data_hash,
            sender: self.publisher,
            deposit,
            enqueued_at: 0,
            size: 32,
        };

        let root = self.queue.enqueue(entry)?;
        Ok(PublishResult::New { root })
    }

    /// Subscribe to this topic. Returns error if already subscribed or max reached.
    pub fn subscribe(&mut self, subscriber: [u8; 32]) -> Result<(), PubSubError> {
        if self.cursors.contains_key(&subscriber) {
            return Err(PubSubError::AlreadySubscribed);
        }
        if self.cursors.len() >= self.max_subscribers {
            return Err(PubSubError::MaxSubscribers {
                max: self.max_subscribers,
            });
        }

        // New subscriber starts at current tail (only sees new messages).
        let cursor = self.queue.tail();
        self.cursors.insert(subscriber, cursor);
        Ok(())
    }

    /// Unsubscribe from this topic.
    pub fn unsubscribe(&mut self, subscriber: &[u8; 32]) {
        self.cursors.remove(subscriber);
    }

    /// Read the next message for a given subscriber. Advances that subscriber's cursor.
    /// Returns None if the subscriber is caught up (no new messages).
    pub fn read_next(&mut self, subscriber: &[u8; 32]) -> Result<Option<&QueueEntry>, PubSubError> {
        let cursor = self
            .cursors
            .get_mut(subscriber)
            .ok_or(PubSubError::NotSubscribed)?;

        let tail = self.queue.tail();
        if *cursor >= tail {
            // Caught up.
            return Ok(None);
        }

        // The entry at `cursor` is at index (cursor - queue.head_position()) in the
        // pending slice. But since pub-sub doesn't dequeue, head stays at 0 unless
        // gc_consumed is called. The absolute index into `entries` is just `cursor`.
        let head_pos = self.queue.head_position();
        if *cursor < head_pos {
            // This entry was already GC'd. Advance cursor to head.
            *cursor = head_pos;
            if *cursor >= tail {
                return Ok(None);
            }
        }

        let entry_index = *cursor;
        *cursor += 1;

        // Access the entry via the queue's internal buffer.
        // We use peek_at to access by absolute index.
        Ok(self.peek_at(entry_index))
    }

    /// How many messages a subscriber is behind (unread count).
    pub fn subscriber_lag(&self, subscriber: &[u8; 32]) -> Option<usize> {
        let cursor = self.cursors.get(subscriber)?;
        let tail = self.queue.tail();
        Some(tail.saturating_sub(*cursor))
    }

    /// Remove entries that ALL subscribers have already read.
    /// Returns the number of entries removed.
    pub fn gc_consumed(&mut self) -> usize {
        if self.cursors.is_empty() {
            // No subscribers: nothing to GC (publisher might want history).
            return 0;
        }

        // Find the minimum cursor position across all subscribers.
        let min_cursor = self
            .cursors
            .values()
            .copied()
            .min()
            .unwrap_or(self.queue.tail());

        // Dequeue entries from head up to min_cursor.
        let head = self.queue.head_position();
        let to_remove = min_cursor.saturating_sub(head);

        for _ in 0..to_remove {
            if self.queue.dequeue().is_err() {
                break;
            }
        }

        to_remove
    }

    /// Get the topic name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the topic tags.
    pub fn tags(&self) -> &[String] {
        &self.tags
    }

    /// Get the publisher identity.
    pub fn publisher(&self) -> &[u8; 32] {
        &self.publisher
    }

    /// Number of current subscribers.
    pub fn subscriber_count(&self) -> usize {
        self.cursors.len()
    }

    /// Max subscribers allowed.
    pub fn max_subscribers(&self) -> usize {
        self.max_subscribers
    }

    /// Total messages published (queue tail).
    pub fn total_published(&self) -> usize {
        self.queue.tail()
    }

    /// Number of messages still held in the queue (not GC'd).
    pub fn pending_count(&self) -> usize {
        self.queue.len()
    }

    /// Current queue root hash.
    pub fn root(&self) -> [u8; 32] {
        self.queue.root()
    }

    /// Peek at an entry by absolute index. Returns None if the entry has been GC'd
    /// or doesn't exist.
    fn peek_at(&self, absolute_index: usize) -> Option<&QueueEntry> {
        let head = self.queue.head_position();
        if absolute_index < head {
            return None; // GC'd.
        }
        let relative = absolute_index - head;
        self.queue.peek_relative(relative)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_topic() -> PubSubTopic {
        PubSubTopic::new([0xAA; 32], "test-topic".to_string(), 100, 10)
    }

    #[test]
    fn publish_and_subscribe_read() {
        let mut topic = make_topic();
        let publisher = [0xAA; 32];
        let subscriber = [0xBB; 32];

        // Subscribe before any messages.
        topic.subscribe(subscriber).unwrap();

        // Publish a message.
        let data_hash = *blake3::hash(b"hello pub-sub").as_bytes();
        topic.publish(&publisher, data_hash, 100).unwrap();

        // Subscriber reads it.
        let entry = topic.read_next(&subscriber).unwrap().unwrap();
        assert_eq!(entry.content_hash, data_hash);
        assert_eq!(entry.deposit, 100);

        // No more messages.
        let next = topic.read_next(&subscriber).unwrap();
        assert!(next.is_none());
    }

    #[test]
    fn multiple_subscribers_independent_cursors() {
        let mut topic = make_topic();
        let publisher = [0xAA; 32];
        let sub_a = [0x01; 32];
        let sub_b = [0x02; 32];

        topic.subscribe(sub_a).unwrap();
        topic.subscribe(sub_b).unwrap();

        // Publish 3 messages.
        for i in 0u8..3 {
            let hash = *blake3::hash(&[i]).as_bytes();
            topic.publish(&publisher, hash, 50).unwrap();
        }

        // Sub A reads 2, Sub B reads 1.
        topic.read_next(&sub_a).unwrap().unwrap();
        topic.read_next(&sub_a).unwrap().unwrap();

        topic.read_next(&sub_b).unwrap().unwrap();

        // Lags differ.
        assert_eq!(topic.subscriber_lag(&sub_a), Some(1));
        assert_eq!(topic.subscriber_lag(&sub_b), Some(2));
    }

    #[test]
    fn gc_consumed_removes_entries_all_subs_have_read() {
        let mut topic = make_topic();
        let publisher = [0xAA; 32];
        let sub_a = [0x01; 32];
        let sub_b = [0x02; 32];

        topic.subscribe(sub_a).unwrap();
        topic.subscribe(sub_b).unwrap();

        // Publish 3 messages.
        for i in 0u8..3 {
            let hash = *blake3::hash(&[i]).as_bytes();
            topic.publish(&publisher, hash, 50).unwrap();
        }

        // Sub A reads all 3, Sub B reads 2.
        for _ in 0..3 {
            topic.read_next(&sub_a).unwrap();
        }
        for _ in 0..2 {
            topic.read_next(&sub_b).unwrap();
        }

        // GC: min cursor is sub_b's at position 2. Can remove entries 0 and 1.
        let removed = topic.gc_consumed();
        assert_eq!(removed, 2);
        assert_eq!(topic.pending_count(), 1); // Only entry 2 remains.
    }

    #[test]
    fn max_subscribers_enforced() {
        let mut topic = PubSubTopic::new([0xAA; 32], "limited".to_string(), 100, 2);

        topic.subscribe([0x01; 32]).unwrap();
        topic.subscribe([0x02; 32]).unwrap();

        let result = topic.subscribe([0x03; 32]);
        assert_eq!(result, Err(PubSubError::MaxSubscribers { max: 2 }));
    }

    #[test]
    fn subscriber_lag_tracking() {
        let mut topic = make_topic();
        let publisher = [0xAA; 32];
        let subscriber = [0xBB; 32];

        topic.subscribe(subscriber).unwrap();

        // Initially 0 lag.
        assert_eq!(topic.subscriber_lag(&subscriber), Some(0));

        // Publish 5 messages.
        for i in 0u8..5 {
            let hash = *blake3::hash(&[i]).as_bytes();
            topic.publish(&publisher, hash, 10).unwrap();
        }

        // Lag is 5.
        assert_eq!(topic.subscriber_lag(&subscriber), Some(5));

        // Read 3.
        for _ in 0..3 {
            topic.read_next(&subscriber).unwrap();
        }

        // Lag is 2.
        assert_eq!(topic.subscriber_lag(&subscriber), Some(2));
    }

    #[test]
    fn non_publisher_cannot_write() {
        let mut topic = make_topic();
        let imposter = [0xFF; 32];
        let hash = *blake3::hash(b"nope").as_bytes();

        let result = topic.publish(&imposter, hash, 100);
        assert_eq!(result, Err(PubSubError::NotPublisher));
    }

    #[test]
    fn unsubscribe_removes_cursor() {
        let mut topic = make_topic();
        let sub = [0xBB; 32];

        topic.subscribe(sub).unwrap();
        assert_eq!(topic.subscriber_count(), 1);

        topic.unsubscribe(&sub);
        assert_eq!(topic.subscriber_count(), 0);

        // Reading after unsubscribe fails.
        let result = topic.read_next(&sub);
        assert_eq!(result, Err(PubSubError::NotSubscribed));
    }

    #[test]
    fn late_subscriber_sees_only_new_messages() {
        let mut topic = make_topic();
        let publisher = [0xAA; 32];
        let early_sub = [0x01; 32];
        let late_sub = [0x02; 32];

        topic.subscribe(early_sub).unwrap();

        // Publish 3 messages.
        for i in 0u8..3 {
            let hash = *blake3::hash(&[i]).as_bytes();
            topic.publish(&publisher, hash, 10).unwrap();
        }

        // Late subscriber joins now.
        topic.subscribe(late_sub).unwrap();

        // Early sub has 3 unread, late sub has 0.
        assert_eq!(topic.subscriber_lag(&early_sub), Some(3));
        assert_eq!(topic.subscriber_lag(&late_sub), Some(0));

        // Publish 1 more.
        let hash = *blake3::hash(&[99u8]).as_bytes();
        topic.publish(&publisher, hash, 10).unwrap();

        // Early sub has 4, late sub has 1.
        assert_eq!(topic.subscriber_lag(&early_sub), Some(4));
        assert_eq!(topic.subscriber_lag(&late_sub), Some(1));

        // Late sub reads the 1 new message.
        let entry = topic.read_next(&late_sub).unwrap().unwrap();
        assert_eq!(entry.content_hash, hash);
    }
}
