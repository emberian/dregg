//! DFA-based message routing for wire protocol dispatch.
//!
//! This module provides a routing layer that uses deterministic finite automata
//! to classify incoming wire protocol messages and gossip topic filters. The DFA
//! approach gives us:
//!
//! - **O(n) classification** in constant space (one state integer per message)
//! - **Deterministic commitment**: the transition table hashes to a fixed value
//!   that can be bound into governance constitutions
//! - **Atomic route updates**: swap the entire table in one operation
//!
//! # Architecture
//!
//! ```text
//!   receive bytes
//!        │
//!        ▼
//!   ┌──────────┐
//!   │  Router  │  ← runs DFA on message prefix / path
//!   └──────────┘
//!        │
//!   ┌────┴─────────────────────────┐
//!   ▼         ▼          ▼         ▼
//!  Cell    Handler    Federation   Drop
//! ```

use std::collections::HashMap;

use pyana_captp::GroupId;
use pyana_types::CellId;

// ---------------------------------------------------------------------------
// Route Target
// ---------------------------------------------------------------------------

/// Where a classified message should be dispatched.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RouteTarget {
    /// Route to a specific cell by ID.
    Cell(CellId),
    /// Route to a named handler (e.g. "intent_pool", "admin").
    Handler(String),
    /// Forward to another group (formerly "federation").
    Federation(GroupId),
    /// Silently discard (capability revoked or blocked topic).
    Drop,
}

// ---------------------------------------------------------------------------
// Route Table
// ---------------------------------------------------------------------------

/// A compiled route table: DFA transition table plus metadata.
///
/// The transition table is flat: `transitions[state * 256 + byte]` gives the
/// next state (as a `u8` state index). State 0 is the dead/reject state.
/// Accept states map to `RouteTarget`s via `accept_map`.
#[derive(Clone, Debug)]
pub struct RouteTable {
    /// BLAKE3 hash of the serialized transition table (for governance binding).
    pub commitment: [u8; 32],
    /// Flat transition table: states x 256 entries.
    /// Each entry is a state index (u8), supporting up to 255 live states.
    pub transitions: Vec<u8>,
    /// Number of states in the DFA (including dead state 0).
    pub num_states: usize,
    /// Maps accept-state indices to route targets.
    pub accept_map: HashMap<u8, RouteTarget>,
}

impl RouteTable {
    /// Compute the BLAKE3 commitment of the transition table.
    fn compute_commitment(transitions: &[u8]) -> [u8; 32] {
        *blake3::hash(transitions).as_bytes()
    }
}

// ---------------------------------------------------------------------------
// Router (live dispatch engine)
// ---------------------------------------------------------------------------

/// The live router: classifies messages by running the DFA.
#[derive(Clone, Debug)]
pub struct Router {
    table: RouteTable,
}

impl Router {
    /// Create a router from a compiled route table.
    pub fn new(table: RouteTable) -> Self {
        Router { table }
    }

    /// Classify a raw message by running the DFA over its bytes.
    ///
    /// Returns the route target if the DFA reaches an accept state,
    /// or `None` if classification fails (dead state or non-accept terminal).
    pub fn classify(&self, message: &[u8]) -> Option<&RouteTarget> {
        let state = self.run_dfa(message);
        self.table.accept_map.get(&state)
    }

    /// Classify a URL-style path (e.g. `/cells/stablecoin/transfer`).
    ///
    /// Same DFA execution but on path bytes specifically.
    pub fn classify_path(&self, path: &[u8]) -> Option<&RouteTarget> {
        let state = self.run_dfa(path);
        self.table.accept_map.get(&state)
    }

    /// Get the route table commitment hash.
    pub fn commitment(&self) -> &[u8; 32] {
        &self.table.commitment
    }

    /// Get a reference to the underlying route table.
    pub fn table(&self) -> &RouteTable {
        &self.table
    }

    /// Run the DFA on input, return the final state.
    fn run_dfa(&self, input: &[u8]) -> u8 {
        let mut state: u8 = 1; // start state is always 1
        for &byte in input {
            let idx = (state as usize) * 256 + (byte as usize);
            if idx >= self.table.transitions.len() {
                return 0; // out of bounds -> dead
            }
            state = self.table.transitions[idx];
            if state == 0 {
                return 0; // dead state, early exit
            }
        }
        state
    }
}

// ---------------------------------------------------------------------------
// Route Compilation (URL-style patterns -> DFA)
// ---------------------------------------------------------------------------

/// Compile a set of URL-style route patterns into a `RouteTable`.
///
/// Patterns support:
/// - Literal path segments: `/cells/stablecoin`
/// - Wildcard suffix: `/cells/stablecoin/*` (matches any continuation)
/// - Exact match: `/admin` (no trailing wildcard means exact)
///
/// # Example
///
/// ```ignore
/// let table = compile_routes(&[
///     ("/cells/stablecoin/*", RouteTarget::Cell(stablecoin_id)),
///     ("/intents/*", RouteTarget::Handler("intent_pool".into())),
///     ("/admin/*", RouteTarget::Handler("admin".into())),
/// ]);
/// ```
pub fn compile_routes(routes: &[(&str, RouteTarget)]) -> RouteTable {
    // We build a trie of path bytes, then flatten it into a DFA transition table.
    // Each route gets its own accept state.
    let mut builder = DfaBuilder::new();

    for (pattern, target) in routes {
        builder.add_route(pattern.as_bytes(), target.clone());
    }

    builder.build()
}

/// Internal trie node for DFA construction.
#[derive(Debug, Default)]
struct TrieNode {
    /// Transitions on specific bytes.
    children: HashMap<u8, usize>, // byte -> node index
    /// If this node is a wildcard accept (matches anything past here).
    wildcard: bool,
    /// Route target if this is an accept state (exact match).
    target: Option<RouteTarget>,
}

/// DFA builder that constructs from route patterns via trie intermediate.
struct DfaBuilder {
    nodes: Vec<TrieNode>,
}

impl DfaBuilder {
    fn new() -> Self {
        // Node 0 = root (will become DFA state 1, since DFA state 0 = dead)
        DfaBuilder {
            nodes: vec![TrieNode::default()],
        }
    }

    fn add_route(&mut self, pattern: &[u8], target: RouteTarget) {
        let mut current = 0usize; // trie node index

        // Check for trailing wildcard `/*`
        let (path_bytes, is_wildcard) = if pattern.len() >= 2
            && pattern[pattern.len() - 2] == b'/'
            && pattern[pattern.len() - 1] == b'*'
        {
            (&pattern[..pattern.len() - 2], true)
        } else if pattern.len() >= 1 && pattern[pattern.len() - 1] == b'*' {
            (&pattern[..pattern.len() - 1], true)
        } else {
            (pattern, false)
        };

        // Walk/build the trie for the literal prefix
        for &byte in path_bytes {
            let next = if let Some(&child) = self.nodes[current].children.get(&byte) {
                child
            } else {
                let idx = self.nodes.len();
                self.nodes.push(TrieNode::default());
                self.nodes[current].children.insert(byte, idx);
                idx
            };
            current = next;
        }

        if is_wildcard {
            // For wildcard: add a `/` transition to a wildcard-accept node
            let wildcard_via_slash = if let Some(&child) = self.nodes[current].children.get(&b'/') {
                child
            } else {
                let idx = self.nodes.len();
                self.nodes.push(TrieNode::default());
                self.nodes[current].children.insert(b'/', idx);
                idx
            };
            self.nodes[wildcard_via_slash].wildcard = true;
            self.nodes[wildcard_via_slash].target = Some(target.clone());
            // Also accept the prefix itself with trailing slash
            // e.g. "/cells/stablecoin/" should match "/cells/stablecoin/*"
            // And the prefix node itself is also accept for "/cells/stablecoin/*"
            // meaning "/cells/stablecoin" alone won't match, but "/cells/stablecoin/anything" will.
            // Actually for usability, also mark the slash-node as accept.
        } else {
            // Exact match: current node is accept
            self.nodes[current].target = Some(target);
        }
    }

    fn build(self) -> RouteTable {
        // Convert trie to flat DFA transition table.
        // DFA state 0 = dead state (no trie node)
        // DFA state i+1 = trie node i
        // Wildcard nodes: all 256 transitions loop back to themselves.

        let num_states = self.nodes.len() + 1; // +1 for dead state
        assert!(num_states <= 256, "route table exceeds 255 live states");

        let mut transitions = vec![0u8; num_states * 256];
        let mut accept_map = HashMap::new();

        // State 0 (dead): all transitions stay at 0 (already zeroed)

        for (node_idx, node) in self.nodes.iter().enumerate() {
            let dfa_state = (node_idx + 1) as u8; // trie node 0 -> DFA state 1

            if node.wildcard {
                // Wildcard node: all bytes loop back to self
                for byte in 0..=255u8 {
                    transitions[(dfa_state as usize) * 256 + (byte as usize)] = dfa_state;
                }
                // Also set explicit children (they take priority but since we're
                // building from trie they'd go to the same or more specific state)
                for (&byte, &child_idx) in &node.children {
                    let child_state = (child_idx + 1) as u8;
                    transitions[(dfa_state as usize) * 256 + (byte as usize)] = child_state;
                }
            } else {
                // Normal node: only explicit transitions, rest go to dead (0)
                for (&byte, &child_idx) in &node.children {
                    let child_state = (child_idx + 1) as u8;
                    transitions[(dfa_state as usize) * 256 + (byte as usize)] = child_state;
                }
            }

            // Register accept state
            if node.target.is_some() {
                accept_map.insert(dfa_state, node.target.clone().unwrap());
            }
        }

        let commitment = RouteTable::compute_commitment(&transitions);

        RouteTable {
            commitment,
            transitions,
            num_states,
            accept_map,
        }
    }
}

// ---------------------------------------------------------------------------
// Governed Router (governance-bound route updates)
// ---------------------------------------------------------------------------

/// Proof that a route update was authorized by governance.
///
/// In production this would carry a threshold signature or ZK proof
/// referencing the constitution. For now it carries the expected old
/// commitment so updates are atomic compare-and-swap.
#[derive(Clone, Debug)]
pub struct GovernanceProof {
    /// The commitment hash the updater believes is currently active.
    pub expected_old_commitment: [u8; 32],
    /// Signature or proof data (placeholder for threshold sig / ZK proof).
    pub proof_data: Vec<u8>,
}

/// A router that enforces governance authorization on route updates.
///
/// The `commitment` is the BLAKE3 hash of the active transition table,
/// which is expected to match a value committed in the federation constitution.
/// Route updates are atomic: they only succeed if the caller provides the
/// correct current commitment (compare-and-swap semantics).
#[derive(Clone, Debug)]
pub struct GovernedRouter {
    current: Router,
    commitment: [u8; 32],
}

impl GovernedRouter {
    /// Create a governed router from an initial route table.
    pub fn new(table: RouteTable) -> Self {
        let commitment = table.commitment;
        GovernedRouter {
            current: Router::new(table),
            commitment,
        }
    }

    /// Get the current governance commitment.
    pub fn commitment(&self) -> &[u8; 32] {
        &self.commitment
    }

    /// Classify a message using the current route table.
    pub fn classify(&self, message: &[u8]) -> Option<&RouteTarget> {
        self.current.classify(message)
    }

    /// Classify a path using the current route table.
    pub fn classify_path(&self, path: &[u8]) -> Option<&RouteTarget> {
        self.current.classify_path(path)
    }

    /// Atomically update the route table, given a governance proof.
    ///
    /// Returns `Ok(())` if the update succeeds, or `Err` with a description
    /// if the governance proof doesn't match the current commitment.
    pub fn update_routes(
        &mut self,
        new_table: RouteTable,
        proof: &GovernanceProof,
    ) -> Result<(), RouteUpdateError> {
        // Verify the caller knows the current commitment (CAS semantics)
        if proof.expected_old_commitment != self.commitment {
            return Err(RouteUpdateError::CommitmentMismatch {
                expected: proof.expected_old_commitment,
                actual: self.commitment,
            });
        }

        // In production: verify proof.proof_data against threshold sig / ZK proof.
        // For now we just check the CAS.

        self.commitment = new_table.commitment;
        self.current = Router::new(new_table);
        Ok(())
    }

    /// Get a reference to the inner router.
    pub fn router(&self) -> &Router {
        &self.current
    }
}

/// Errors from route update attempts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RouteUpdateError {
    /// The expected old commitment doesn't match the actual current commitment.
    CommitmentMismatch {
        expected: [u8; 32],
        actual: [u8; 32],
    },
}

impl std::fmt::Display for RouteUpdateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RouteUpdateError::CommitmentMismatch { expected, actual } => {
                write!(
                    f,
                    "commitment mismatch: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                    expected[0], expected[1], actual[0], actual[1]
                )
            }
        }
    }
}

impl std::error::Error for RouteUpdateError {}

// ---------------------------------------------------------------------------
// Wire message dispatch integration
// ---------------------------------------------------------------------------

/// Dispatch result from the router, used to bridge between raw byte
/// classification and the typed message processing layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DispatchDecision {
    /// Deliver to a cell's message handler.
    DeliverToCell(CellId),
    /// Deliver to a named service handler.
    DeliverToHandler(String),
    /// Forward to a peer group (formerly "federation").
    ForwardToFederation(GroupId),
    /// Drop the message (revoked capability or blocked topic).
    Discard,
    /// No route matched; use default handling.
    Unrouted,
}

/// Classify an incoming wire message and determine its dispatch target.
///
/// This function sits between "receive bytes" and "process_message" in the
/// server pipeline:
///
/// ```text
///   TcpStream → frame_codec → dispatch_message() → handler
/// ```
///
/// The `path_prefix` is extracted from the message framing (e.g. first N bytes
/// that encode the destination topic/path).
pub fn dispatch_message(router: &Router, raw_message: &[u8]) -> DispatchDecision {
    match router.classify(raw_message) {
        Some(RouteTarget::Cell(cell_id)) => DispatchDecision::DeliverToCell(*cell_id),
        Some(RouteTarget::Handler(name)) => DispatchDecision::DeliverToHandler(name.clone()),
        Some(RouteTarget::Federation(fed_id)) => DispatchDecision::ForwardToFederation(*fed_id),
        Some(RouteTarget::Drop) => DispatchDecision::Discard,
        None => DispatchDecision::Unrouted,
    }
}

/// Classify a path-based request (e.g. from HTTP-like routing or topic names).
pub fn dispatch_path(router: &Router, path: &[u8]) -> DispatchDecision {
    match router.classify_path(path) {
        Some(RouteTarget::Cell(cell_id)) => DispatchDecision::DeliverToCell(*cell_id),
        Some(RouteTarget::Handler(name)) => DispatchDecision::DeliverToHandler(name.clone()),
        Some(RouteTarget::Federation(fed_id)) => DispatchDecision::ForwardToFederation(*fed_id),
        Some(RouteTarget::Drop) => DispatchDecision::Discard,
        None => DispatchDecision::Unrouted,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn test_cell_id(n: u8) -> CellId {
        CellId([n; 32])
    }

    fn test_federation_id(n: u8) -> GroupId {
        GroupId([n; 32])
    }

    #[test]
    fn test_compile_routes_basic() {
        let table = compile_routes(&[
            ("/cells/alpha/*", RouteTarget::Cell(test_cell_id(1))),
            ("/intents/*", RouteTarget::Handler("intent_pool".into())),
        ]);
        assert!(table.num_states > 1);
        assert!(!table.accept_map.is_empty());
    }

    #[test]
    fn test_classify_wildcard_route() {
        let table = compile_routes(&[
            ("/cells/alpha/*", RouteTarget::Cell(test_cell_id(1))),
            ("/intents/*", RouteTarget::Handler("intent_pool".into())),
        ]);
        let router = Router::new(table);

        assert_eq!(
            router.classify_path(b"/cells/alpha/transfer"),
            Some(&RouteTarget::Cell(test_cell_id(1)))
        );
        assert_eq!(
            router.classify_path(b"/cells/alpha/balance"),
            Some(&RouteTarget::Cell(test_cell_id(1)))
        );
        assert_eq!(
            router.classify_path(b"/intents/submit"),
            Some(&RouteTarget::Handler("intent_pool".into()))
        );
    }

    #[test]
    fn test_unknown_path_returns_none() {
        let table = compile_routes(&[("/cells/alpha/*", RouteTarget::Cell(test_cell_id(1)))]);
        let router = Router::new(table);

        assert_eq!(router.classify_path(b"/unknown/path"), None);
        assert_eq!(router.classify_path(b"/cells/beta/x"), None);
        assert_eq!(router.classify_path(b""), None);
    }

    #[test]
    fn test_commitment_is_deterministic() {
        let routes: &[(&str, RouteTarget)] = &[
            ("/cells/alpha/*", RouteTarget::Cell(test_cell_id(1))),
            ("/intents/*", RouteTarget::Handler("intent_pool".into())),
        ];
        let table1 = compile_routes(routes);
        let table2 = compile_routes(routes);

        assert_eq!(table1.commitment, table2.commitment);
        assert_ne!(table1.commitment, [0u8; 32]);
    }

    #[test]
    fn test_route_update_changes_classification() {
        let table1 = compile_routes(&[("/cells/alpha/*", RouteTarget::Cell(test_cell_id(1)))]);
        let commitment1 = table1.commitment;
        let mut governed = GovernedRouter::new(table1);

        // Before update: alpha routes to cell 1
        assert_eq!(
            governed.classify_path(b"/cells/alpha/x"),
            Some(&RouteTarget::Cell(test_cell_id(1)))
        );

        // Update routes: alpha now routes to cell 2
        let table2 = compile_routes(&[("/cells/alpha/*", RouteTarget::Cell(test_cell_id(2)))]);
        let proof = GovernanceProof {
            expected_old_commitment: commitment1,
            proof_data: vec![],
        };
        governed.update_routes(table2, &proof).unwrap();

        // After update: alpha routes to cell 2
        assert_eq!(
            governed.classify_path(b"/cells/alpha/x"),
            Some(&RouteTarget::Cell(test_cell_id(2)))
        );
    }

    #[test]
    fn test_route_update_rejects_wrong_commitment() {
        let table1 = compile_routes(&[("/cells/alpha/*", RouteTarget::Cell(test_cell_id(1)))]);
        let mut governed = GovernedRouter::new(table1);

        let table2 = compile_routes(&[("/cells/alpha/*", RouteTarget::Cell(test_cell_id(2)))]);
        let bad_proof = GovernanceProof {
            expected_old_commitment: [0xffu8; 32], // wrong
            proof_data: vec![],
        };
        let result = governed.update_routes(table2, &bad_proof);
        assert!(result.is_err());
    }

    #[test]
    fn test_shared_prefix_routes() {
        let table = compile_routes(&[
            ("/cells/alpha/*", RouteTarget::Cell(test_cell_id(1))),
            ("/cells/beta/*", RouteTarget::Cell(test_cell_id(2))),
            ("/cells/gamma/*", RouteTarget::Cell(test_cell_id(3))),
        ]);
        let router = Router::new(table);

        assert_eq!(
            router.classify_path(b"/cells/alpha/x"),
            Some(&RouteTarget::Cell(test_cell_id(1)))
        );
        assert_eq!(
            router.classify_path(b"/cells/beta/y"),
            Some(&RouteTarget::Cell(test_cell_id(2)))
        );
        assert_eq!(
            router.classify_path(b"/cells/gamma/z"),
            Some(&RouteTarget::Cell(test_cell_id(3)))
        );
        // Shared prefix alone doesn't match
        assert_eq!(router.classify_path(b"/cells/"), None);
        assert_eq!(router.classify_path(b"/cells"), None);
    }

    #[test]
    fn test_drop_target_discards() {
        let table = compile_routes(&[
            ("/blocked/*", RouteTarget::Drop),
            ("/allowed/*", RouteTarget::Handler("ok".into())),
        ]);
        let router = Router::new(table);

        assert_eq!(
            dispatch_path(&router, b"/blocked/anything"),
            DispatchDecision::Discard
        );
        assert_eq!(
            dispatch_path(&router, b"/allowed/something"),
            DispatchDecision::DeliverToHandler("ok".into())
        );
    }

    #[test]
    fn test_federation_routing() {
        let fed_id = test_federation_id(42);
        let table = compile_routes(&[("/federated/*", RouteTarget::Federation(fed_id))]);
        let router = Router::new(table);

        assert_eq!(
            dispatch_path(&router, b"/federated/sync"),
            DispatchDecision::ForwardToFederation(fed_id)
        );
    }

    #[test]
    fn test_classify_raw_message_bytes() {
        // Simulate a wire message whose first bytes are a path-like prefix
        let table = compile_routes(&[("/cells/stablecoin/*", RouteTarget::Cell(test_cell_id(10)))]);
        let router = Router::new(table);

        let msg = b"/cells/stablecoin/transfer\x00payload_data_here";
        // The DFA keeps going through the wildcard, consuming all bytes
        assert_eq!(
            router.classify(msg),
            Some(&RouteTarget::Cell(test_cell_id(10)))
        );
    }

    #[test]
    fn test_dispatch_message_unrouted() {
        let table = compile_routes(&[("/cells/alpha/*", RouteTarget::Cell(test_cell_id(1)))]);
        let router = Router::new(table);

        assert_eq!(
            dispatch_message(&router, b"/unknown"),
            DispatchDecision::Unrouted
        );
    }

    #[test]
    fn test_many_routes_stress() {
        // Ensure we can handle a realistic number of routes
        let routes: Vec<(String, RouteTarget)> = (0..50)
            .map(|i| {
                (
                    format!("/svc/handler_{i}/*"),
                    RouteTarget::Handler(format!("handler_{i}")),
                )
            })
            .collect();

        let route_refs: Vec<(&str, RouteTarget)> = routes
            .iter()
            .map(|(s, t)| (s.as_str(), t.clone()))
            .collect();

        let table = compile_routes(&route_refs);
        let router = Router::new(table);

        for i in 0..50 {
            let path = format!("/svc/handler_{i}/action");
            assert_eq!(
                router.classify_path(path.as_bytes()),
                Some(&RouteTarget::Handler(format!("handler_{i}"))),
                "failed for handler_{i}"
            );
        }
    }

    #[test]
    fn test_commitment_changes_with_routes() {
        let table1 = compile_routes(&[("/a/*", RouteTarget::Handler("a".into()))]);
        let table2 = compile_routes(&[("/b/*", RouteTarget::Handler("b".into()))]);
        // Different routes produce different commitments
        assert_ne!(table1.commitment, table2.commitment);
    }

    #[test]
    fn test_governed_router_commitment_tracks() {
        let table = compile_routes(&[("/x/*", RouteTarget::Handler("x".into()))]);
        let expected_commitment = table.commitment;
        let governed = GovernedRouter::new(table);
        assert_eq!(governed.commitment(), &expected_commitment);
    }
}
