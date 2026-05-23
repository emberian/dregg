//! Fault injection primitives for adversarial testing.
//!
//! Provides a `FaultyNetwork` simulator that can drop, reorder, duplicate, and delay
//! messages between federations. Also includes `CrashableNode` for simulating node
//! crashes/recoveries and `Partition` for network splits.
//!
//! All randomness is seeded for reproducibility — the same seed produces the same
//! failure sequence, making flaky tests impossible if the code is deterministic.

use std::collections::VecDeque;

use pyana_wire::message::WireMessage;

// =============================================================================
// Deterministic RNG
// =============================================================================

/// Simple xorshift64 PRNG for deterministic fault injection.
#[derive(Clone, Debug)]
pub struct SimpleRng {
    state: u64,
}

impl SimpleRng {
    /// Create a new RNG from a string seed (hashed with BLAKE3).
    pub fn from_seed(seed: &str) -> Self {
        let hash = blake3::hash(seed.as_bytes());
        let bytes: [u8; 8] = hash.as_bytes()[..8].try_into().unwrap();
        let state = u64::from_le_bytes(bytes) | 1; // ensure non-zero
        Self { state }
    }

    /// Next u64 value.
    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    /// Generate a float in [0.0, 1.0).
    pub fn next_f64(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }

    /// Generate a bool with given probability (0.0 = never, 1.0 = always).
    pub fn gen_bool(&mut self, probability: f64) -> bool {
        self.next_f64() < probability
    }

    /// Generate a u64 in [lo, hi).
    pub fn gen_range(&mut self, lo: u64, hi: u64) -> u64 {
        if hi <= lo {
            return lo;
        }
        lo + self.next_u64() % (hi - lo)
    }

    /// Generate 32 random bytes.
    pub fn gen_bytes(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for chunk in out.chunks_exact_mut(8) {
            chunk.copy_from_slice(&self.next_u64().to_le_bytes());
        }
        out
    }

    /// Shuffle a slice in-place (Fisher-Yates).
    pub fn shuffle<T>(&mut self, slice: &mut [T]) {
        let len = slice.len();
        for i in (1..len).rev() {
            let j = self.gen_range(0, (i + 1) as u64) as usize;
            slice.swap(i, j);
        }
    }
}

// =============================================================================
// Fault Configuration
// =============================================================================

/// Configuration for fault injection behavior.
#[derive(Clone, Debug)]
pub struct FaultConfig {
    /// Probability of dropping a message (0.0 = never, 1.0 = always).
    pub drop_rate: f64,
    /// Probability of reordering messages (0.0 = FIFO, 1.0 = random order).
    pub reorder_rate: f64,
    /// Probability of duplicating a message.
    pub duplicate_rate: f64,
    /// Maximum delay in simulated ticks before delivery.
    pub max_delay: u64,
    /// Whether to simulate partitions.
    pub partition: Option<Partition>,
}

impl FaultConfig {
    /// No faults — perfect network behavior.
    pub fn perfect() -> Self {
        Self {
            drop_rate: 0.0,
            reorder_rate: 0.0,
            duplicate_rate: 0.0,
            max_delay: 0,
            partition: None,
        }
    }

    /// Lossy network: 10% drop, 20% reorder, no duplicates.
    pub fn lossy() -> Self {
        Self {
            drop_rate: 0.10,
            reorder_rate: 0.20,
            duplicate_rate: 0.0,
            max_delay: 3,
            partition: None,
        }
    }

    /// Hostile network: 30% drop, 50% reorder, 10% duplicate.
    pub fn hostile() -> Self {
        Self {
            drop_rate: 0.30,
            reorder_rate: 0.50,
            duplicate_rate: 0.10,
            max_delay: 10,
            partition: None,
        }
    }

    /// Only partitions, no other faults.
    pub fn partition_only(isolated_pairs: Vec<(usize, usize)>, duration: u64) -> Self {
        Self {
            drop_rate: 0.0,
            reorder_rate: 0.0,
            duplicate_rate: 0.0,
            max_delay: 0,
            partition: Some(Partition {
                isolated_pairs,
                duration,
            }),
        }
    }
}

impl Default for FaultConfig {
    fn default() -> Self {
        Self::perfect()
    }
}

// =============================================================================
// Partition
// =============================================================================

/// A network partition configuration.
#[derive(Clone, Debug)]
pub struct Partition {
    /// Which federation pairs are partitioned (cannot communicate).
    pub isolated_pairs: Vec<(usize, usize)>,
    /// Duration of partition in simulated ticks.
    pub duration: u64,
}

impl Partition {
    /// Check if two federations are currently partitioned.
    pub fn is_partitioned(&self, a: usize, b: usize) -> bool {
        let (lo, hi) = if a < b { (a, b) } else { (b, a) };
        self.isolated_pairs.iter().any(|&(x, y)| x == lo && y == hi)
    }
}

// =============================================================================
// In-Flight Message
// =============================================================================

/// A message that is in transit between federations.
#[derive(Clone, Debug)]
pub struct InFlightMessage {
    /// Source federation index.
    pub from: usize,
    /// Destination federation index.
    pub to: usize,
    /// The wire message payload.
    pub message: WireMessage,
    /// Simulated tick at which this message becomes deliverable.
    pub deliver_at: u64,
    /// Whether this message has been delivered.
    pub delivered: bool,
}

/// A message that has been successfully delivered.
#[derive(Clone, Debug)]
pub struct DeliveredMessage {
    /// Source federation index.
    pub from: usize,
    /// Destination federation index.
    pub to: usize,
    /// The wire message payload.
    pub message: WireMessage,
}

// =============================================================================
// Saved State (for crash/recovery)
// =============================================================================

/// Captured state of a node at crash time.
///
/// In a real system this would be a snapshot of persistent storage. Here we
/// capture enough metadata to verify safety properties on recovery.
#[derive(Clone, Debug)]
pub struct SavedState {
    /// The node index that crashed.
    pub node_idx: usize,
    /// The federation index the node belongs to.
    pub federation_idx: usize,
    /// Block height at the time of crash.
    pub height_at_crash: u64,
    /// Messages that were in the outbound queue but never sent.
    pub unsent_messages: Vec<WireMessage>,
    /// Messages received but not yet processed.
    pub unprocessed_messages: Vec<WireMessage>,
}

// =============================================================================
// Crashable Node
// =============================================================================

/// A simulated node that can crash and recover.
#[derive(Clone, Debug)]
pub struct CrashableNode {
    /// Whether this node is currently healthy/online.
    pub healthy: bool,
    /// Saved state from the last crash (if any).
    pub state_at_crash: Option<SavedState>,
    /// Messages lost during the crash (were in-flight to this node).
    pub messages_lost_during_crash: Vec<WireMessage>,
    /// Federation index this node belongs to.
    pub federation_idx: usize,
    /// Node index within the federation.
    pub node_idx: usize,
}

impl CrashableNode {
    /// Create a new healthy node.
    pub fn new(federation_idx: usize, node_idx: usize) -> Self {
        Self {
            healthy: true,
            state_at_crash: None,
            messages_lost_during_crash: Vec::new(),
            federation_idx,
            node_idx,
        }
    }

    /// Crash this node, capturing its current state.
    pub fn crash(&mut self, height: u64, unsent: Vec<WireMessage>) -> SavedState {
        self.healthy = false;
        let state = SavedState {
            node_idx: self.node_idx,
            federation_idx: self.federation_idx,
            height_at_crash: height,
            unsent_messages: unsent,
            unprocessed_messages: Vec::new(),
        };
        self.state_at_crash = Some(state.clone());
        state
    }

    /// Recover this node from a saved state.
    pub fn recover(&mut self, _state: SavedState) {
        self.healthy = true;
        // Messages lost during crash are NOT automatically re-delivered.
        // The recovery protocol must handle this explicitly.
    }

    /// Record a message that was lost because this node was crashed.
    pub fn record_lost_message(&mut self, msg: WireMessage) {
        self.messages_lost_during_crash.push(msg);
    }
}

// =============================================================================
// Faulty Network
// =============================================================================

/// A network simulator that can inject faults.
///
/// Sits between federations and controls message delivery. Can drop, reorder,
/// duplicate, and delay messages. Can also simulate network partitions.
pub struct FaultyNetwork {
    /// Messages in flight between federations.
    pub in_flight: Vec<InFlightMessage>,
    /// Fault injection configuration.
    pub config: FaultConfig,
    /// Random seed for deterministic fault injection.
    pub rng: SimpleRng,
    /// Current simulated tick.
    pub current_tick: u64,
    /// Messages that were dropped (for post-mortem inspection).
    pub dropped_messages: Vec<InFlightMessage>,
    /// Messages that were duplicated (for post-mortem inspection).
    pub duplicated_count: u64,
    /// Total messages sent through this network.
    pub total_sent: u64,
    /// Total messages delivered.
    pub total_delivered: u64,
    /// Crashable nodes, keyed by (federation_idx, node_idx).
    pub nodes: Vec<CrashableNode>,
}

impl FaultyNetwork {
    /// Create a new faulty network with the given configuration and seed.
    pub fn new(config: FaultConfig, seed: &str) -> Self {
        Self {
            in_flight: Vec::new(),
            config,
            rng: SimpleRng::from_seed(seed),
            current_tick: 0,
            dropped_messages: Vec::new(),
            duplicated_count: 0,
            total_sent: 0,
            total_delivered: 0,
            nodes: Vec::new(),
        }
    }

    /// Register nodes for crash simulation.
    pub fn register_nodes(&mut self, federation_idx: usize, num_nodes: usize) {
        for node_idx in 0..num_nodes {
            self.nodes
                .push(CrashableNode::new(federation_idx, node_idx));
        }
    }

    /// Send a message from one federation to another.
    ///
    /// The message may be dropped, delayed, or duplicated based on the fault config.
    /// Returns `true` if the message was accepted into the network (not dropped).
    pub fn send(&mut self, from: usize, to: usize, message: WireMessage) -> bool {
        self.total_sent += 1;

        // Check partition
        if let Some(ref partition) = self.config.partition {
            if partition.is_partitioned(from, to) {
                let msg = InFlightMessage {
                    from,
                    to,
                    message,
                    deliver_at: 0,
                    delivered: true, // mark as "handled" — it was dropped by partition
                };
                self.dropped_messages.push(msg);
                return false;
            }
        }

        // Drop?
        if self.rng.gen_bool(self.config.drop_rate) {
            let msg = InFlightMessage {
                from,
                to,
                message,
                deliver_at: 0,
                delivered: true,
            };
            self.dropped_messages.push(msg);
            return false;
        }

        // Calculate delivery tick
        let delay = if self.config.max_delay > 0 {
            self.rng.gen_range(0, self.config.max_delay + 1)
        } else {
            0
        };
        let deliver_at = self.current_tick + delay;

        // Duplicate?
        if self.rng.gen_bool(self.config.duplicate_rate) {
            self.in_flight.push(InFlightMessage {
                from,
                to,
                message: message.clone(),
                deliver_at: deliver_at + self.rng.gen_range(0, 3),
                delivered: false,
            });
            self.duplicated_count += 1;
        }

        self.in_flight.push(InFlightMessage {
            from,
            to,
            message,
            deliver_at,
            delivered: false,
        });

        true
    }

    /// Advance the network clock by one tick.
    pub fn tick(&mut self) {
        self.current_tick += 1;

        // Check if partition has expired
        if let Some(ref partition) = self.config.partition {
            if self.current_tick >= partition.duration {
                // Auto-heal after duration
                self.config.partition = None;
            }
        }
    }

    /// Advance the network clock by N ticks.
    pub fn advance_ticks(&mut self, n: u64) {
        for _ in 0..n {
            self.tick();
        }
    }

    /// Deliver one message that is ready (deliver_at <= current_tick).
    ///
    /// If reorder_rate > 0, may deliver messages out of order.
    /// Returns `None` if no messages are ready for delivery.
    pub fn deliver_one(&mut self) -> Option<DeliveredMessage> {
        // Find deliverable messages
        let ready_indices: Vec<usize> = self
            .in_flight
            .iter()
            .enumerate()
            .filter(|(_, m)| !m.delivered && m.deliver_at <= self.current_tick)
            .map(|(i, _)| i)
            .collect();

        if ready_indices.is_empty() {
            return None;
        }

        // Pick which one to deliver
        let idx = if self.rng.gen_bool(self.config.reorder_rate) && ready_indices.len() > 1 {
            // Reorder: pick a random one from the ready set
            let pick = self.rng.gen_range(0, ready_indices.len() as u64) as usize;
            ready_indices[pick]
        } else {
            // FIFO: pick the earliest
            *ready_indices
                .iter()
                .min_by_key(|&&i| self.in_flight[i].deliver_at)
                .unwrap()
        };

        self.in_flight[idx].delivered = true;
        let msg = &self.in_flight[idx];
        let delivered = DeliveredMessage {
            from: msg.from,
            to: msg.to,
            message: msg.message.clone(),
        };
        self.total_delivered += 1;
        Some(delivered)
    }

    /// Deliver all ready messages, returning them in delivery order.
    pub fn deliver_all_ready(&mut self) -> Vec<DeliveredMessage> {
        let mut delivered = Vec::new();
        while let Some(msg) = self.deliver_one() {
            delivered.push(msg);
        }
        delivered
    }

    /// Drain all undelivered messages (e.g., after a partition heals).
    pub fn drain_undelivered(&mut self) -> Vec<InFlightMessage> {
        let undelivered: Vec<InFlightMessage> = self
            .in_flight
            .iter()
            .filter(|m| !m.delivered)
            .cloned()
            .collect();
        self.in_flight.retain(|m| m.delivered);
        undelivered
    }

    /// Inject a partition between two federations.
    pub fn inject_partition(&mut self, a: usize, b: usize, duration: u64) {
        let (lo, hi) = if a < b { (a, b) } else { (b, a) };
        let partition = Partition {
            isolated_pairs: vec![(lo, hi)],
            duration: self.current_tick + duration,
        };
        self.config.partition = Some(partition);
    }

    /// Heal a partition between two federations.
    pub fn heal_partition(&mut self, _a: usize, _b: usize) {
        self.config.partition = None;
    }

    /// Crash a node, returning its saved state.
    ///
    /// All in-flight messages destined for this node are lost.
    pub fn crash_node(
        &mut self,
        federation_idx: usize,
        node_idx: usize,
        height: u64,
    ) -> SavedState {
        // Find messages destined for this federation's node and mark them lost
        let lost: Vec<WireMessage> = self
            .in_flight
            .iter()
            .filter(|m| !m.delivered && m.to == federation_idx)
            .map(|m| m.message.clone())
            .collect();

        // Mark those messages as delivered (they won't be delivered to the crashed node)
        for msg in self.in_flight.iter_mut() {
            if !msg.delivered && msg.to == federation_idx {
                msg.delivered = true;
            }
        }

        // Find the crashable node and crash it
        if let Some(node) = self
            .nodes
            .iter_mut()
            .find(|n| n.federation_idx == federation_idx && n.node_idx == node_idx)
        {
            for lost_msg in &lost {
                node.record_lost_message(lost_msg.clone());
            }
            node.crash(height, vec![])
        } else {
            SavedState {
                node_idx,
                federation_idx,
                height_at_crash: height,
                unsent_messages: vec![],
                unprocessed_messages: lost,
            }
        }
    }

    /// Recover a node from its saved state.
    pub fn recover_node(&mut self, federation_idx: usize, node_idx: usize, state: SavedState) {
        if let Some(node) = self
            .nodes
            .iter_mut()
            .find(|n| n.federation_idx == federation_idx && n.node_idx == node_idx)
        {
            node.recover(state);
        }
    }

    /// Check if a node is healthy.
    pub fn is_node_healthy(&self, federation_idx: usize, node_idx: usize) -> bool {
        self.nodes
            .iter()
            .find(|n| n.federation_idx == federation_idx && n.node_idx == node_idx)
            .map(|n| n.healthy)
            .unwrap_or(true)
    }

    /// Get statistics about the network.
    pub fn stats(&self) -> NetworkStats {
        NetworkStats {
            total_sent: self.total_sent,
            total_delivered: self.total_delivered,
            total_dropped: self.dropped_messages.len() as u64,
            total_duplicated: self.duplicated_count,
            in_flight: self.in_flight.iter().filter(|m| !m.delivered).count() as u64,
            current_tick: self.current_tick,
        }
    }

    /// Clean up delivered messages from the in_flight buffer (memory management).
    pub fn gc(&mut self) {
        self.in_flight.retain(|m| !m.delivered);
    }
}

/// Network statistics for debugging and assertions.
#[derive(Clone, Debug)]
pub struct NetworkStats {
    pub total_sent: u64,
    pub total_delivered: u64,
    pub total_dropped: u64,
    pub total_duplicated: u64,
    pub in_flight: u64,
    pub current_tick: u64,
}

// =============================================================================
// Message Buffer (for store-and-forward during crashes)
// =============================================================================

/// A message buffer that accumulates messages while a node is crashed.
///
/// Messages are delivered in order when the node recovers.
#[derive(Clone, Debug, Default)]
pub struct MessageBuffer {
    /// Buffered messages awaiting delivery, keyed by destination (federation_idx, node_idx).
    pub buffers: std::collections::HashMap<(usize, usize), VecDeque<WireMessage>>,
}

impl MessageBuffer {
    pub fn new() -> Self {
        Self {
            buffers: std::collections::HashMap::new(),
        }
    }

    /// Buffer a message for a crashed node.
    pub fn buffer(&mut self, federation_idx: usize, node_idx: usize, msg: WireMessage) {
        self.buffers
            .entry((federation_idx, node_idx))
            .or_default()
            .push_back(msg);
    }

    /// Drain all buffered messages for a recovering node (in order).
    pub fn drain(&mut self, federation_idx: usize, node_idx: usize) -> Vec<WireMessage> {
        self.buffers
            .remove(&(federation_idx, node_idx))
            .map(|q| q.into_iter().collect())
            .unwrap_or_default()
    }

    /// Number of buffered messages for a specific node.
    pub fn pending_count(&self, federation_idx: usize, node_idx: usize) -> usize {
        self.buffers
            .get(&(federation_idx, node_idx))
            .map(|q| q.len())
            .unwrap_or(0)
    }

    /// Total buffered messages across all nodes.
    pub fn total_buffered(&self) -> usize {
        self.buffers.values().map(|q| q.len()).sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn perfect_network_delivers_all() {
        let mut net = FaultyNetwork::new(FaultConfig::perfect(), "test-perfect");
        let msg = WireMessage::Ping {
            seq: 1,
            timestamp: 0,
        };

        assert!(net.send(0, 1, msg.clone()));
        let delivered = net.deliver_all_ready();
        assert_eq!(delivered.len(), 1);
        assert_eq!(delivered[0].message, msg);
    }

    #[test]
    fn partition_blocks_messages() {
        let config = FaultConfig::partition_only(vec![(0, 1)], 100);
        let mut net = FaultyNetwork::new(config, "test-partition");
        let msg = WireMessage::Ping {
            seq: 1,
            timestamp: 0,
        };

        assert!(!net.send(0, 1, msg.clone()));
        assert_eq!(net.dropped_messages.len(), 1);
    }

    #[test]
    fn partition_heals_after_duration() {
        let config = FaultConfig::partition_only(vec![(0, 1)], 10);
        let mut net = FaultyNetwork::new(config, "test-heal");
        let msg = WireMessage::Ping {
            seq: 1,
            timestamp: 0,
        };

        // While partitioned: messages blocked
        assert!(!net.send(0, 1, msg.clone()));

        // Advance past partition duration
        net.advance_ticks(11);

        // After heal: messages go through
        assert!(net.send(0, 1, msg.clone()));
        let delivered = net.deliver_all_ready();
        assert_eq!(delivered.len(), 1);
    }

    #[test]
    fn delay_respects_ticks() {
        let config = FaultConfig {
            drop_rate: 0.0,
            reorder_rate: 0.0,
            duplicate_rate: 0.0,
            max_delay: 5,
            partition: None,
        };
        let mut net = FaultyNetwork::new(config, "test-delay");
        let msg = WireMessage::Ping {
            seq: 42,
            timestamp: 0,
        };

        net.send(0, 1, msg.clone());

        // Immediately: maybe not deliverable (depends on delay)
        // After advancing enough ticks: definitely deliverable
        net.advance_ticks(6);
        let delivered = net.deliver_all_ready();
        assert_eq!(delivered.len(), 1);
        assert_eq!(delivered[0].message, msg);
    }

    #[test]
    fn rng_is_deterministic() {
        let mut rng1 = SimpleRng::from_seed("determinism-check");
        let mut rng2 = SimpleRng::from_seed("determinism-check");
        for _ in 0..100 {
            assert_eq!(rng1.next_u64(), rng2.next_u64());
        }
    }

    #[test]
    fn message_buffer_fifo_order() {
        let mut buf = MessageBuffer::new();
        for i in 0..5 {
            buf.buffer(
                0,
                0,
                WireMessage::Ping {
                    seq: i,
                    timestamp: 0,
                },
            );
        }
        assert_eq!(buf.pending_count(0, 0), 5);

        let msgs = buf.drain(0, 0);
        assert_eq!(msgs.len(), 5);
        for (i, msg) in msgs.iter().enumerate() {
            assert_eq!(
                *msg,
                WireMessage::Ping {
                    seq: i as u64,
                    timestamp: 0
                }
            );
        }
        assert_eq!(buf.pending_count(0, 0), 0);
    }
}
