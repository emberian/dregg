//! Multi-node simulation harness.
//!
//! Provides an in-process multi-node environment where federation nodes communicate
//! via direct function calls rather than real networking. This lets integration tests
//! exercise consensus, turn execution, and proof verification without any I/O.

use std::collections::HashMap;

use pyana_captp::{FederationId, PyanaUri};
use pyana_cell::{AuthRequired, Ledger};
use pyana_federation::node::Federation;
use pyana_federation::types::AttestedRoot;
use pyana_turn::executor::{ComputronCosts, TurnExecutor};
use pyana_turn::{Turn, TurnResult};
use pyana_types::CellId;

use crate::captp_sim::SimCapTpSession;

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
    /// Active CapTP sessions between federations.
    /// Key is (smaller_idx, larger_idx) to avoid duplicate pairs.
    pub captp_sessions: HashMap<(usize, usize), SimCapTpSession>,
    /// Federation IDs for each federation (derived deterministically from name).
    pub federation_ids: Vec<FederationId>,
}

impl SimulationHarness {
    /// Derive a deterministic FederationId from a federation name.
    fn derive_federation_id(name: &str) -> FederationId {
        let hash = blake3::derive_key("pyana-teasting-federation-id-v1", name.as_bytes());
        FederationId(hash)
    }

    /// Create a harness with a single federation of N nodes.
    pub fn new_federation(num_nodes: usize) -> Self {
        let fed = SimFederation::new("fed-alpha", num_nodes);
        let fed_id = Self::derive_federation_id("fed-alpha");
        Self {
            federations: vec![fed],
            clock: SimClock::new(),
            executor: TurnExecutor::new(ComputronCosts::default_costs()),
            ledger: Ledger::new(),
            captp_sessions: HashMap::new(),
            federation_ids: vec![fed_id],
        }
    }

    /// Create a harness with two federations for cross-federation testing.
    pub fn two_federations(nodes_a: usize, nodes_b: usize) -> Self {
        let fed_a = SimFederation::new("fed-alpha", nodes_a);
        let fed_b = SimFederation::new("fed-beta", nodes_b);
        let id_a = Self::derive_federation_id("fed-alpha");
        let id_b = Self::derive_federation_id("fed-beta");
        Self {
            federations: vec![fed_a, fed_b],
            clock: SimClock::new(),
            executor: TurnExecutor::new(ComputronCosts::default_costs()),
            ledger: Ledger::new(),
            captp_sessions: HashMap::new(),
            federation_ids: vec![id_a, id_b],
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

    // =========================================================================
    // Cross-federation CapTP helpers
    // =========================================================================

    /// Connect two federations via a simulated CapTP session.
    ///
    /// Establishes a bilateral session and delivers the initial CapHello messages.
    /// Returns a mutable reference to the new session.
    ///
    /// Panics if a session already exists between these two federations.
    pub fn connect_federations(&mut self, a_idx: usize, b_idx: usize) -> &mut SimCapTpSession {
        assert_ne!(a_idx, b_idx, "cannot connect a federation to itself");
        let key = if a_idx < b_idx {
            (a_idx, b_idx)
        } else {
            (b_idx, a_idx)
        };

        assert!(
            !self.captp_sessions.contains_key(&key),
            "session already exists between federations {} and {}",
            a_idx,
            b_idx,
        );

        let fed_a_id = self.federation_ids[a_idx];
        let fed_b_id = self.federation_ids[b_idx];

        let mut session = SimCapTpSession::establish(fed_a_id, fed_b_id);
        session.current_height = self.clock.block_height;
        session.deliver_pending();

        self.captp_sessions.insert(key, session);
        self.captp_sessions.get_mut(&key).unwrap()
    }

    /// Get a mutable reference to the CapTP session between two federations.
    ///
    /// Returns `None` if no session exists between them.
    pub fn session_mut(&mut self, a_idx: usize, b_idx: usize) -> Option<&mut SimCapTpSession> {
        let key = if a_idx < b_idx {
            (a_idx, b_idx)
        } else {
            (b_idx, a_idx)
        };
        self.captp_sessions.get_mut(&key)
    }

    /// Get an immutable reference to the CapTP session between two federations.
    pub fn session(&self, a_idx: usize, b_idx: usize) -> Option<&SimCapTpSession> {
        let key = if a_idx < b_idx {
            (a_idx, b_idx)
        } else {
            (b_idx, a_idx)
        };
        self.captp_sessions.get(&key)
    }

    /// Export a cell from one federation as a sturdy ref.
    ///
    /// The federation must have a CapTP session with at least one other federation.
    /// The returned URI can be shared with any other federation.
    pub fn export_sturdy(
        &mut self,
        fed_idx: usize,
        cell_id: CellId,
        target_fed_idx: usize,
    ) -> PyanaUri {
        let key = if fed_idx < target_fed_idx {
            (fed_idx, target_fed_idx)
        } else {
            (target_fed_idx, fed_idx)
        };

        let session = self
            .captp_sessions
            .get_mut(&key)
            .expect("no session between these federations");

        // Determine which side is exporting
        let fed_id = self.federation_ids[fed_idx];
        if session.fed_a_id == fed_id {
            session.export_from_a(cell_id, AuthRequired::Signature)
        } else {
            session.export_from_b(cell_id, AuthRequired::Signature)
        }
    }

    /// Enliven a sturdy ref from another federation.
    ///
    /// The caller must have a CapTP session with the federation that exported the URI.
    /// Returns the local CellId handle for the enlivened capability.
    pub fn enliven_sturdy(
        &mut self,
        fed_idx: usize,
        uri: &PyanaUri,
        source_fed_idx: usize,
    ) -> Result<CellId, String> {
        let key = if fed_idx < source_fed_idx {
            (fed_idx, source_fed_idx)
        } else {
            (source_fed_idx, fed_idx)
        };

        let session = self
            .captp_sessions
            .get_mut(&key)
            .expect("no session between these federations");

        // The source federation is the one that exported the URI,
        // so we enliven "at" the source.
        let source_id = self.federation_ids[source_fed_idx];
        if session.fed_a_id == source_id {
            session.enliven_at_a(uri)
        } else {
            session.enliven_at_b(uri)
        }
    }

    /// Disconnect two federations (simulate network partition).
    pub fn disconnect_federations(&mut self, a_idx: usize, b_idx: usize) {
        let key = if a_idx < b_idx {
            (a_idx, b_idx)
        } else {
            (b_idx, a_idx)
        };
        if let Some(session) = self.captp_sessions.get_mut(&key) {
            session.disconnect();
        }
    }

    /// Get the FederationId for a federation by index.
    pub fn federation_id(&self, idx: usize) -> FederationId {
        self.federation_ids[idx]
    }

    /// Add a new federation to the harness (for multi-federation scenarios).
    pub fn add_federation(&mut self, name: &str, num_nodes: usize) -> usize {
        let idx = self.federations.len();
        self.federations.push(SimFederation::new(name, num_nodes));
        self.federation_ids.push(Self::derive_federation_id(name));
        idx
    }
}
