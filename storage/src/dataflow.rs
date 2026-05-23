//! Queue-to-queue dataflow pipelines.
//!
//! A `Pipeline` connects queues together: output of one queue feeds input of another,
//! with optional filtering, transformation, and routing.
//!
//! This is the "unix pipe" model for message queues:
//!   inbox | filter(is_capability) | route(by_asset_type) | [queue_a, queue_b]

use std::collections::HashMap;

use crate::queue::{MerkleQueue, QueueEntry, QueueError};

// ============================================================================
// Core types
// ============================================================================

/// A dataflow pipeline: connects queues together.
/// Output of one queue feeds input of another, with optional transformation.
///
/// Example: "messages from the inbox -> filter by type -> route to specific topic"
pub struct Pipeline {
    /// Stages in the pipeline (source -> transforms -> sinks)
    stages: Vec<PipelineStage>,
    /// Pipeline identity (content-addressed from stage descriptions)
    id: [u8; 32],
}

/// A single stage in the pipeline.
#[derive(Debug, Clone)]
pub enum PipelineStage {
    /// Read from a source queue.
    Source { queue_id: [u8; 32] },
    /// Filter messages (only pass those matching predicate).
    Filter { predicate: FilterPredicate },
    /// Transform message content (map).
    Transform { transform: TransformFn },
    /// Route to different sinks based on content.
    Router { routes: Vec<(FilterPredicate, [u8; 32])> },
    /// Write to a sink queue.
    Sink { queue_id: [u8; 32] },
    /// Fan-out: write to ALL listed queues.
    FanOut { queue_ids: Vec<[u8; 32]> },
}

/// Predicates for filtering and routing.
#[derive(Debug, Clone)]
pub enum FilterPredicate {
    /// Message content hash starts with this prefix.
    ContentPrefix(Vec<u8>),
    /// Sender matches.
    Sender([u8; 32]),
    /// Deposit above threshold.
    MinDeposit(u64),
    /// Custom (blake3 hash of predicate description for extensibility).
    Custom { description: String, hash: [u8; 32] },
}

/// Transformations applied to messages in-flight.
#[derive(Debug, Clone)]
pub enum TransformFn {
    /// Pass through unchanged.
    Identity,
    /// Strip sender info (anonymize).
    Anonymize,
    /// Add metadata (pipeline stage marker).
    Tag { tag: Vec<u8> },
}

/// Result of executing one pipeline step.
#[derive(Debug, Clone, Default)]
pub struct PipelineResult {
    /// Number of messages processed from source.
    pub messages_processed: usize,
    /// Messages routed to each sink (sink_id -> count).
    pub messages_routed: HashMap<[u8; 32], usize>,
    /// Messages dropped by filters.
    pub messages_filtered: usize,
}

/// Errors from pipeline execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PipelineError {
    /// No source stage defined.
    NoSource,
    /// Source queue not found in the queue map.
    SourceNotFound { queue_id: [u8; 32] },
    /// Sink queue not found in the queue map.
    SinkNotFound { queue_id: [u8; 32] },
    /// Queue error during enqueue or dequeue.
    QueueError(QueueError),
    /// Pipeline has no stages.
    EmptyPipeline,
}

impl From<QueueError> for PipelineError {
    fn from(e: QueueError) -> Self {
        PipelineError::QueueError(e)
    }
}

// ============================================================================
// Implementation
// ============================================================================

impl Pipeline {
    /// Create a new pipeline from a list of stages.
    /// The pipeline id is content-addressed from the stage descriptions.
    pub fn new(stages: Vec<PipelineStage>) -> Self {
        let id = compute_pipeline_id(&stages);
        Self { stages, id }
    }

    /// Pipeline identity hash (deterministic from stages).
    pub fn id(&self) -> [u8; 32] {
        self.id
    }

    /// Execute one step: dequeue from source, process through stages, enqueue to sinks.
    /// Returns the messages that reached each sink.
    pub fn step(
        &self,
        queues: &mut HashMap<[u8; 32], MerkleQueue>,
    ) -> Result<PipelineResult, PipelineError> {
        if self.stages.is_empty() {
            return Err(PipelineError::EmptyPipeline);
        }

        // Find source stage.
        let source_id = self.find_source()?;

        // Dequeue one message from source.
        let source_queue = queues
            .get_mut(&source_id)
            .ok_or(PipelineError::SourceNotFound { queue_id: source_id })?;

        let entry = match source_queue.dequeue() {
            Ok((entry, _proof)) => entry,
            Err(QueueError::Empty) => {
                // Source is empty, nothing to do.
                return Ok(PipelineResult::default());
            }
            Err(e) => return Err(PipelineError::QueueError(e)),
        };

        let mut result = PipelineResult {
            messages_processed: 1,
            messages_routed: HashMap::new(),
            messages_filtered: 0,
        };

        // Process through stages (skip Source, process Filter/Transform/Router/Sink/FanOut).
        let mut messages: Vec<QueueEntry> = vec![entry];

        for stage in &self.stages {
            match stage {
                PipelineStage::Source { .. } => {
                    // Already handled above.
                }
                PipelineStage::Filter { predicate } => {
                    let before_count = messages.len();
                    messages.retain(|entry| evaluate_predicate(predicate, entry));
                    result.messages_filtered += before_count - messages.len();
                }
                PipelineStage::Transform { transform } => {
                    messages = messages.into_iter().map(|e| apply_transform(transform, e)).collect();
                }
                PipelineStage::Router { routes } => {
                    // Route each message to the first matching route's sink.
                    let mut routed_messages: Vec<QueueEntry> = Vec::new();
                    for msg in &messages {
                        let mut was_routed = false;
                        for (pred, sink_id) in routes {
                            if evaluate_predicate(pred, msg) {
                                let sink_queue = queues
                                    .get_mut(sink_id)
                                    .ok_or(PipelineError::SinkNotFound { queue_id: *sink_id })?;
                                sink_queue.enqueue(msg.clone())?;
                                *result.messages_routed.entry(*sink_id).or_insert(0) += 1;
                                was_routed = true;
                                break; // First matching route wins.
                            }
                        }
                        if !was_routed {
                            // No route matched; message passes through unrouted.
                            routed_messages.push(msg.clone());
                        }
                    }
                    messages = routed_messages;
                }
                PipelineStage::Sink { queue_id } => {
                    let sink_queue = queues
                        .get_mut(queue_id)
                        .ok_or(PipelineError::SinkNotFound { queue_id: *queue_id })?;
                    for msg in &messages {
                        sink_queue.enqueue(msg.clone())?;
                        *result.messages_routed.entry(*queue_id).or_insert(0) += 1;
                    }
                    messages.clear();
                }
                PipelineStage::FanOut { queue_ids } => {
                    for sink_id in queue_ids {
                        let sink_queue = queues
                            .get_mut(sink_id)
                            .ok_or(PipelineError::SinkNotFound { queue_id: *sink_id })?;
                        for msg in &messages {
                            sink_queue.enqueue(msg.clone())?;
                            *result.messages_routed.entry(*sink_id).or_insert(0) += 1;
                        }
                    }
                    messages.clear();
                }
            }
        }

        Ok(result)
    }

    /// Execute until source is empty (batch processing).
    pub fn drain(
        &self,
        queues: &mut HashMap<[u8; 32], MerkleQueue>,
    ) -> Result<Vec<PipelineResult>, PipelineError> {
        let mut results = Vec::new();
        loop {
            let result = self.step(queues)?;
            if result.messages_processed == 0 {
                break;
            }
            results.push(result);
        }
        Ok(results)
    }

    /// Find the source queue id from the pipeline stages.
    fn find_source(&self) -> Result<[u8; 32], PipelineError> {
        for stage in &self.stages {
            if let PipelineStage::Source { queue_id } = stage {
                return Ok(*queue_id);
            }
        }
        Err(PipelineError::NoSource)
    }
}

// ============================================================================
// Helpers
// ============================================================================

/// Evaluate a filter predicate against a queue entry.
fn evaluate_predicate(predicate: &FilterPredicate, entry: &QueueEntry) -> bool {
    match predicate {
        FilterPredicate::ContentPrefix(prefix) => {
            if prefix.len() > entry.content_hash.len() {
                return false;
            }
            entry.content_hash[..prefix.len()] == prefix[..]
        }
        FilterPredicate::Sender(sender) => entry.sender == *sender,
        FilterPredicate::MinDeposit(min) => entry.deposit >= *min,
        FilterPredicate::Custom { .. } => {
            // Custom predicates always pass in local evaluation.
            // In-circuit, they are verified by the proof system.
            true
        }
    }
}

/// Apply a transformation to a queue entry.
fn apply_transform(transform: &TransformFn, mut entry: QueueEntry) -> QueueEntry {
    match transform {
        TransformFn::Identity => entry,
        TransformFn::Anonymize => {
            entry.sender = [0u8; 32];
            entry
        }
        TransformFn::Tag { tag } => {
            // Re-hash content with tag to mark it as processed.
            let mut hasher = blake3::Hasher::new();
            hasher.update(&entry.content_hash);
            hasher.update(tag);
            entry.content_hash = *hasher.finalize().as_bytes();
            entry
        }
    }
}

/// Compute the pipeline identity hash from its stages.
fn compute_pipeline_id(stages: &[PipelineStage]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pipeline_v1");

    for stage in stages {
        match stage {
            PipelineStage::Source { queue_id } => {
                hasher.update(b"source");
                hasher.update(queue_id);
            }
            PipelineStage::Filter { predicate } => {
                hasher.update(b"filter");
                hash_predicate(&mut hasher, predicate);
            }
            PipelineStage::Transform { transform } => {
                hasher.update(b"transform");
                match transform {
                    TransformFn::Identity => hasher.update(b"identity"),
                    TransformFn::Anonymize => hasher.update(b"anonymize"),
                    TransformFn::Tag { tag } => {
                        hasher.update(b"tag");
                        hasher.update(tag)
                    }
                };
            }
            PipelineStage::Router { routes } => {
                hasher.update(b"router");
                for (pred, sink_id) in routes {
                    hash_predicate(&mut hasher, pred);
                    hasher.update(sink_id);
                }
            }
            PipelineStage::Sink { queue_id } => {
                hasher.update(b"sink");
                hasher.update(queue_id);
            }
            PipelineStage::FanOut { queue_ids } => {
                hasher.update(b"fanout");
                for id in queue_ids {
                    hasher.update(id);
                }
            }
        }
    }

    *hasher.finalize().as_bytes()
}

/// Hash a predicate into a hasher for pipeline identity computation.
fn hash_predicate(hasher: &mut blake3::Hasher, predicate: &FilterPredicate) {
    match predicate {
        FilterPredicate::ContentPrefix(prefix) => {
            hasher.update(b"content_prefix");
            hasher.update(prefix);
        }
        FilterPredicate::Sender(sender) => {
            hasher.update(b"sender");
            hasher.update(sender);
        }
        FilterPredicate::MinDeposit(min) => {
            hasher.update(b"min_deposit");
            hasher.update(&min.to_le_bytes());
        }
        FilterPredicate::Custom { description, hash } => {
            hasher.update(b"custom");
            hasher.update(description.as_bytes());
            hasher.update(hash);
        }
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

    fn make_entry_with_prefix(prefix: &[u8], sender: [u8; 32], deposit: u64) -> QueueEntry {
        let mut content_hash = [0u8; 32];
        content_hash[..prefix.len()].copy_from_slice(prefix);
        QueueEntry {
            content_hash,
            sender,
            deposit,
            enqueued_at: 100,
            size: 32,
        }
    }

    #[test]
    fn pipeline_source_filter_sink() {
        let source_id = [0x01; 32];
        let sink_id = [0x02; 32];

        let pipeline = Pipeline::new(vec![
            PipelineStage::Source { queue_id: source_id },
            PipelineStage::Filter {
                predicate: FilterPredicate::MinDeposit(100),
            },
            PipelineStage::Sink { queue_id: sink_id },
        ]);

        let mut queues = HashMap::new();
        let mut source = MerkleQueue::new(10);
        let sink = MerkleQueue::new(10);

        // Enqueue entries: one above threshold, one below.
        let high_deposit = make_entry(b"high", [0xAA; 32], 200);
        let low_deposit = make_entry(b"low", [0xBB; 32], 50);
        source.enqueue(high_deposit).unwrap();
        source.enqueue(low_deposit).unwrap();

        queues.insert(source_id, source);
        queues.insert(sink_id, sink);

        // Step 1: processes high-deposit message.
        let result = pipeline.step(&mut queues).unwrap();
        assert_eq!(result.messages_processed, 1);
        assert_eq!(result.messages_filtered, 0);
        assert_eq!(*result.messages_routed.get(&sink_id).unwrap_or(&0), 1);

        // Step 2: low-deposit message gets filtered.
        let result = pipeline.step(&mut queues).unwrap();
        assert_eq!(result.messages_processed, 1);
        assert_eq!(result.messages_filtered, 1);
        assert_eq!(*result.messages_routed.get(&sink_id).unwrap_or(&0), 0);

        // Sink should have 1 message.
        assert_eq!(queues.get(&sink_id).unwrap().len(), 1);
    }

    #[test]
    fn pipeline_source_router_multiple_sinks() {
        let source_id = [0x01; 32];
        let sink_a = [0x0A; 32];
        let sink_b = [0x0B; 32];

        let pipeline = Pipeline::new(vec![
            PipelineStage::Source { queue_id: source_id },
            PipelineStage::Router {
                routes: vec![
                    (FilterPredicate::Sender([0xAA; 32]), sink_a),
                    (FilterPredicate::Sender([0xBB; 32]), sink_b),
                ],
            },
        ]);

        let mut queues = HashMap::new();
        let mut source = MerkleQueue::new(10);

        let msg_a = make_entry(b"from_a", [0xAA; 32], 100);
        let msg_b = make_entry(b"from_b", [0xBB; 32], 100);
        source.enqueue(msg_a).unwrap();
        source.enqueue(msg_b).unwrap();

        queues.insert(source_id, source);
        queues.insert(sink_a, MerkleQueue::new(10));
        queues.insert(sink_b, MerkleQueue::new(10));

        // Drain pipeline.
        let results = pipeline.drain(&mut queues).unwrap();
        assert_eq!(results.len(), 2);

        // sink_a got 1 message, sink_b got 1 message.
        assert_eq!(queues.get(&sink_a).unwrap().len(), 1);
        assert_eq!(queues.get(&sink_b).unwrap().len(), 1);
    }

    #[test]
    fn pipeline_fanout_to_multiple_sinks() {
        let source_id = [0x01; 32];
        let sink_a = [0x0A; 32];
        let sink_b = [0x0B; 32];
        let sink_c = [0x0C; 32];

        let pipeline = Pipeline::new(vec![
            PipelineStage::Source { queue_id: source_id },
            PipelineStage::FanOut {
                queue_ids: vec![sink_a, sink_b, sink_c],
            },
        ]);

        let mut queues = HashMap::new();
        let mut source = MerkleQueue::new(10);
        source.enqueue(make_entry(b"broadcast", [0xAA; 32], 100)).unwrap();

        queues.insert(source_id, source);
        queues.insert(sink_a, MerkleQueue::new(10));
        queues.insert(sink_b, MerkleQueue::new(10));
        queues.insert(sink_c, MerkleQueue::new(10));

        let result = pipeline.step(&mut queues).unwrap();
        assert_eq!(result.messages_processed, 1);

        // All three sinks got the message.
        assert_eq!(queues.get(&sink_a).unwrap().len(), 1);
        assert_eq!(queues.get(&sink_b).unwrap().len(), 1);
        assert_eq!(queues.get(&sink_c).unwrap().len(), 1);
    }

    #[test]
    fn pipeline_drain_processes_all_source_messages() {
        let source_id = [0x01; 32];
        let sink_id = [0x02; 32];

        let pipeline = Pipeline::new(vec![
            PipelineStage::Source { queue_id: source_id },
            PipelineStage::Sink { queue_id: sink_id },
        ]);

        let mut queues = HashMap::new();
        let mut source = MerkleQueue::new(20);
        for i in 0..5u8 {
            source.enqueue(make_entry(&[i], [i; 32], 100)).unwrap();
        }

        queues.insert(source_id, source);
        queues.insert(sink_id, MerkleQueue::new(20));

        let results = pipeline.drain(&mut queues).unwrap();
        assert_eq!(results.len(), 5);
        assert_eq!(queues.get(&source_id).unwrap().len(), 0);
        assert_eq!(queues.get(&sink_id).unwrap().len(), 5);
    }

    #[test]
    fn pipeline_empty_source_noop() {
        let source_id = [0x01; 32];
        let sink_id = [0x02; 32];

        let pipeline = Pipeline::new(vec![
            PipelineStage::Source { queue_id: source_id },
            PipelineStage::Sink { queue_id: sink_id },
        ]);

        let mut queues = HashMap::new();
        queues.insert(source_id, MerkleQueue::new(10));
        queues.insert(sink_id, MerkleQueue::new(10));

        let result = pipeline.step(&mut queues).unwrap();
        assert_eq!(result.messages_processed, 0);
        assert_eq!(result.messages_filtered, 0);
        assert!(result.messages_routed.is_empty());
    }

    #[test]
    fn pipeline_id_is_deterministic() {
        let stages = vec![
            PipelineStage::Source { queue_id: [0x01; 32] },
            PipelineStage::Filter {
                predicate: FilterPredicate::MinDeposit(100),
            },
            PipelineStage::Sink { queue_id: [0x02; 32] },
        ];

        let p1 = Pipeline::new(stages.clone());
        let p2 = Pipeline::new(stages);
        assert_eq!(p1.id(), p2.id());

        // Different stages -> different id.
        let p3 = Pipeline::new(vec![
            PipelineStage::Source { queue_id: [0x01; 32] },
            PipelineStage::Sink { queue_id: [0x03; 32] },
        ]);
        assert_ne!(p1.id(), p3.id());
    }

    #[test]
    fn pipeline_transform_anonymize() {
        let source_id = [0x01; 32];
        let sink_id = [0x02; 32];

        let pipeline = Pipeline::new(vec![
            PipelineStage::Source { queue_id: source_id },
            PipelineStage::Transform { transform: TransformFn::Anonymize },
            PipelineStage::Sink { queue_id: sink_id },
        ]);

        let mut queues = HashMap::new();
        let mut source = MerkleQueue::new(10);
        source.enqueue(make_entry(b"secret", [0xFF; 32], 100)).unwrap();

        queues.insert(source_id, source);
        queues.insert(sink_id, MerkleQueue::new(10));

        pipeline.step(&mut queues).unwrap();

        // Dequeue from sink and verify sender is zeroed.
        let (entry, _) = queues.get_mut(&sink_id).unwrap().dequeue().unwrap();
        assert_eq!(entry.sender, [0u8; 32]);
    }

    #[test]
    fn pipeline_content_prefix_filter() {
        let source_id = [0x01; 32];
        let sink_id = [0x02; 32];

        let pipeline = Pipeline::new(vec![
            PipelineStage::Source { queue_id: source_id },
            PipelineStage::Filter {
                predicate: FilterPredicate::ContentPrefix(vec![0xDE, 0xAD]),
            },
            PipelineStage::Sink { queue_id: sink_id },
        ]);

        let mut queues = HashMap::new();
        let mut source = MerkleQueue::new(10);

        // One matching, one not matching.
        let matching = make_entry_with_prefix(&[0xDE, 0xAD], [0xAA; 32], 100);
        let non_matching = make_entry_with_prefix(&[0xCA, 0xFE], [0xBB; 32], 100);
        source.enqueue(matching).unwrap();
        source.enqueue(non_matching).unwrap();

        queues.insert(source_id, source);
        queues.insert(sink_id, MerkleQueue::new(10));

        let results = pipeline.drain(&mut queues).unwrap();
        // 2 messages processed, 1 filtered.
        let total_filtered: usize = results.iter().map(|r| r.messages_filtered).sum();
        assert_eq!(total_filtered, 1);
        assert_eq!(queues.get(&sink_id).unwrap().len(), 1);
    }
}
