//! Multi-node simulation harness.
//!
//! Provides an in-process multi-node environment where federation nodes communicate
//! via direct function calls rather than real networking. This lets integration tests
//! exercise consensus, turn execution, and proof verification without any I/O.

use pyana_cell::Ledger;
use pyana_federation::node::Federation;
use pyana_federation::types::AttestedRoot;
use pyana_turn::executor::{ComputronCosts, TurnExecutor};
use pyana_turn::{Turn, TurnResult};

/// Simulated clock for deterministic time progression.
#[derive(Clone, Debug)]
pub struct SimClock {
    /// Current simulated timestamp (seconds since epoch).
    pub now: i64,
    /// Current simulated block height.
    pub block_height: u64,
}

impl SimClock {
    pub fn new() -> Self {
        Self {
            now: 1_700_000_000, // arbitrary start
            block_height: 0,
        }
    }

    /// Advance time by `seconds` and increment block height.
    pub fn advance(&mut self, seconds: i64) {
        self.now += seconds;
        self.block_height += 1;
    }

    /// Advance block height by N without changing wall-clock time.
    pub fn advance_blocks(&mut self, n: u64) {
        self.block_height += n;
    }
}

/// A simulated federation wrapping the existing `Federation` type.
pub struct SimFederation {
    pub inner: Federation,
    pub name: String,
}

impl SimFederation {
    /// Create a new simulated federation with `num_nodes` nodes.
    pub fn new(name: &str, num_nodes: usize) -> Self {
        let node_names: Vec<String> = (0..num_nodes)
            .map(|i| format!("{}-node-{}", name, i))
            .collect();
        let name_refs: Vec<&str> = node_names.iter().map(|s| s.as_str()).collect();
        Self {
            inner: Federation::new(&name_refs),
            name: name.to_string(),
        }
    }

    /// Run one consensus round and return whether a block was finalized.
    pub fn run_consensus_round(&mut self) -> bool {
        self.inner.run_consensus_round().is_some()
    }

    /// Submit a revocation from a specific node.
    pub fn submit_revocation(&mut self, node_idx: usize, token_id: &str) {
        self.inner.submit_revocation(node_idx, token_id);
    }

    /// Check that all online nodes agree on the same Merkle root.
    pub fn all_nodes_agree(&mut self) -> bool {
        self.inner.roots_agree()
    }

    /// Get the attested root from a specific node (if finalized).
    pub fn attested_root(&self, node_idx: usize) -> Option<&AttestedRoot> {
        self.inner.nodes[node_idx].get_attested_root()
    }

    /// Check whether a token is revoked according to a specific node.
    pub fn is_revoked(&self, node_idx: usize, token_id: &str) -> bool {
        self.inner.nodes[node_idx].is_revoked(token_id)
    }

    /// Crash a node (take offline).
    pub fn crash_node(&mut self, node_idx: usize) {
        self.inner.crash_node(node_idx);
    }

    /// Recover a crashed node.
    pub fn recover_node(&mut self, node_idx: usize) {
        self.inner.recover_node(node_idx);
    }

    /// Number of online nodes.
    pub fn online_count(&self) -> usize {
        self.inner.online_count()
    }

    /// Total number of nodes.
    pub fn node_count(&self) -> usize {
        self.inner.nodes.len()
    }
}

/// The top-level simulation harness.
pub struct SimulationHarness {
    /// All federations in this simulation.
    pub federations: Vec<SimFederation>,
    /// Shared simulated clock.
    pub clock: SimClock,
    /// Turn executor for applying turns to ledgers.
    pub executor: TurnExecutor,
    /// Shared ledger for turn execution.
    pub ledger: Ledger,
}

impl SimulationHarness {
    /// Create a harness with a single federation of N nodes.
    pub fn new_federation(num_nodes: usize) -> Self {
        Self {
            federations: vec![SimFederation::new("fed-alpha", num_nodes)],
            clock: SimClock::new(),
            executor: TurnExecutor::new(ComputronCosts::default_costs()),
            ledger: Ledger::new(),
        }
    }

    /// Create a harness with two federations for cross-federation testing.
    pub fn two_federations(nodes_a: usize, nodes_b: usize) -> Self {
        Self {
            federations: vec![
                SimFederation::new("fed-alpha", nodes_a),
                SimFederation::new("fed-beta", nodes_b),
            ],
            clock: SimClock::new(),
            executor: TurnExecutor::new(ComputronCosts::default_costs()),
            ledger: Ledger::new(),
        }
    }

    /// Advance the clock by N blocks (each block = 6 seconds).
    pub fn advance_blocks(&mut self, n: u64) {
        for _ in 0..n {
            self.clock.advance(6);
        }
    }

    /// Submit a turn and execute it against the shared ledger.
    pub fn submit_turn(&mut self, turn: &Turn) -> TurnResult {
        self.executor.set_timestamp(self.clock.now);
        self.executor.set_block_height(self.clock.block_height);
        self.executor.execute(turn, &mut self.ledger)
    }

    /// Run a consensus round on a specific federation.
    pub fn run_consensus_round(&mut self, fed_idx: usize) -> bool {
        self.federations[fed_idx].run_consensus_round()
    }

    /// Assert that all nodes in a federation agree on state.
    pub fn assert_all_nodes_agree(&mut self, fed_idx: usize) {
        assert!(
            self.federations[fed_idx].all_nodes_agree(),
            "Federation '{}' nodes disagree on state root",
            self.federations[fed_idx].name
        );
    }

    /// Get a mutable reference to a specific federation.
    pub fn federation_mut(&mut self, idx: usize) -> &mut SimFederation {
        &mut self.federations[idx]
    }

    /// Get an immutable reference to a specific federation.
    pub fn federation(&self, idx: usize) -> &SimFederation {
        &self.federations[idx]
    }
}
