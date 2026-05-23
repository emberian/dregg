//! Generalized intent solver: heterogeneous exchange across asset, capability,
//! service, storage, and namespace items.
//!
//! Unlike the asset-only ring solver (`solver.rs`) or the pairwise capability
//! matcher (`matcher.rs`), this module finds multi-party settlements involving
//! ANY combination of exchange item types in a single ring trade.
//!
//! # Design
//!
//! - Each participant declares what they OFFER and what they WANT.
//! - Items can be heterogeneous (e.g., "I offer tokens + read access, want compute").
//! - Edge A->B exists if A's offers can satisfy SOME or ALL of B's wants.
//! - Cycle detection finds rings where every participant's wants are satisfied.
//! - Subjective valuation: no global pricing; satisfaction is structural + boolean.
//!
//! # Integration with DFA Routing
//!
//! Intents declare a zone (namespace path). The DFA classifier from `rbg/src/routing.rs`
//! routes intents to solver shards. Cross-zone rings use bridge intents.

use crate::CommitmentId;
use crate::exchange::AssetId;
use crate::matcher::resource_matches;

// ---------------------------------------------------------------------------
// Exchange item types
// ---------------------------------------------------------------------------

/// A single item in a heterogeneous exchange.
///
/// Participants offer and want collections of these items. Different types can
/// coexist in the same intent (e.g., "I offer 100 tokens + read access").
#[derive(Clone, Debug, PartialEq)]
pub enum ExchangeItem {
    /// Fungible asset transfer: specific asset ID and amount.
    Asset { id: AssetId, amount: u64 },
    /// Capability grant/delegation: described by a MatchSpec-like pattern.
    /// The granter must hold a capability satisfying these parameters.
    Capability {
        /// Actions being granted (e.g., ["read", "write"]).
        actions: Vec<String>,
        /// Resource pattern (glob, e.g., "documents/*").
        resource: String,
        /// Duration of the grant in epochs. 0 = permanent.
        duration_epochs: u64,
    },
    /// Service invocation: access to a specific compute endpoint.
    Service {
        /// Service endpoint identifier.
        endpoint: String,
        /// Number of invocations granted.
        invocations: u64,
    },
    /// Storage allocation: queue/inbox space.
    Storage {
        /// Queue or storage pool identifier.
        queue_id: String,
        /// Bytes of storage allocated.
        bytes: u64,
        /// Duration in epochs.
        duration_epochs: u64,
    },
    /// Namespace entry: ownership or delegation of a name.
    Name {
        /// The namespace (e.g., "oracle").
        namespace: String,
        /// The specific entry within the namespace (e.g., "alice").
        entry: String,
    },
}

// ---------------------------------------------------------------------------
// Generalized exchange intent
// ---------------------------------------------------------------------------

/// A generalized exchange: "I offer these items, I want those items."
///
/// This is the heterogeneous generalization of `ExchangeSpec` (which only handles
/// asset-for-asset). A single GeneralizedExchange can mix types freely.
#[derive(Clone, Debug)]
pub struct GeneralizedExchange {
    /// Items being offered by this participant.
    pub offering: Vec<ExchangeItem>,
    /// Items wanted by this participant.
    pub wanting: Vec<ExchangeItem>,
}

/// A node in the generalized intent graph.
#[derive(Clone, Debug)]
pub struct GeneralizedIntentNode {
    /// Content-addressed intent ID.
    pub intent_id: crate::IntentId,
    /// The heterogeneous exchange parameters.
    pub exchange: GeneralizedExchange,
    /// Anonymous creator commitment.
    pub creator: CommitmentId,
    /// Expiry timestamp.
    pub expiry: u64,
    /// Optional zone for DFA routing (e.g., "/defi/swap", "/services/compute").
    pub zone: Option<String>,
}

// ---------------------------------------------------------------------------
// Compatibility checking
// ---------------------------------------------------------------------------

/// Check if a single offered item can satisfy a single wanted item.
///
/// Returns true if the offered item structurally subsumes the wanted item
/// according to type-specific rules.
pub fn item_satisfies(offered: &ExchangeItem, wanted: &ExchangeItem) -> bool {
    match (offered, wanted) {
        // Asset: same ID and sufficient amount.
        (
            ExchangeItem::Asset {
                id: offer_id,
                amount: offer_amount,
            },
            ExchangeItem::Asset {
                id: want_id,
                amount: want_amount,
            },
        ) => offer_id == want_id && offer_amount >= want_amount,

        // Capability: actions must include all wanted actions, resource must match.
        (
            ExchangeItem::Capability {
                actions: offer_actions,
                resource: offer_resource,
                duration_epochs: offer_dur,
            },
            ExchangeItem::Capability {
                actions: want_actions,
                resource: want_resource,
                duration_epochs: want_dur,
            },
        ) => {
            // All wanted actions must be provided by the offer.
            let actions_ok = want_actions
                .iter()
                .all(|wa| offer_actions.iter().any(|oa| oa == wa || oa == "*"));
            // Resource must match (using glob matching from matcher.rs).
            let resource_ok = resource_matches(offer_resource, want_resource);
            // Duration must be at least as long.
            let duration_ok = *offer_dur >= *want_dur || *offer_dur == 0;
            actions_ok && resource_ok && duration_ok
        }

        // Service: endpoint must match, invocations sufficient.
        (
            ExchangeItem::Service {
                endpoint: offer_ep,
                invocations: offer_inv,
            },
            ExchangeItem::Service {
                endpoint: want_ep,
                invocations: want_inv,
            },
        ) => offer_ep == want_ep && offer_inv >= want_inv,

        // Storage: queue match, bytes and duration sufficient.
        (
            ExchangeItem::Storage {
                queue_id: offer_q,
                bytes: offer_b,
                duration_epochs: offer_d,
            },
            ExchangeItem::Storage {
                queue_id: want_q,
                bytes: want_b,
                duration_epochs: want_d,
            },
        ) => offer_q == want_q && offer_b >= want_b && offer_d >= want_d,

        // Name: exact match on namespace + entry.
        (
            ExchangeItem::Name {
                namespace: offer_ns,
                entry: offer_e,
            },
            ExchangeItem::Name {
                namespace: want_ns,
                entry: want_e,
            },
        ) => offer_ns == want_ns && offer_e == want_e,

        // Cross-type: items of different types never structurally satisfy each other.
        // (Subjective cross-type equivalence is expressed by the participant listing
        //  both types in their offer/want sets, not by the solver guessing.)
        _ => false,
    }
}

/// Check if a set of offered items can satisfy a set of wanted items.
///
/// Returns `Some(score)` where score is the fraction of wants satisfied (0.0, 1.0].
/// Returns `None` if no wants are satisfied (no edge).
///
/// Each wanted item must be matched by a DISTINCT offered item (no double-spending
/// a single offer against two wants). Uses greedy matching for simplicity.
pub fn can_satisfy(offering: &[ExchangeItem], wanting: &[ExchangeItem]) -> Option<f64> {
    if wanting.is_empty() || offering.is_empty() {
        return None;
    }

    let mut used_offers: Vec<bool> = vec![false; offering.len()];
    let mut satisfied_count = 0usize;

    for want in wanting {
        // Find the first unused offer that satisfies this want.
        for (idx, offer) in offering.iter().enumerate() {
            if !used_offers[idx] && item_satisfies(offer, want) {
                used_offers[idx] = true;
                satisfied_count += 1;
                break;
            }
        }
    }

    if satisfied_count == 0 {
        None
    } else {
        Some(satisfied_count as f64 / wanting.len() as f64)
    }
}

// ---------------------------------------------------------------------------
// Generalized intent graph
// ---------------------------------------------------------------------------

/// The generalized intent compatibility graph.
pub struct GeneralizedIntentGraph {
    /// Nodes indexed by position.
    pub nodes: Vec<GeneralizedIntentNode>,
    /// Adjacency: edges[i] = [(j, score), ...] meaning node i's offer can satisfy
    /// some fraction of node j's wants.
    pub edges: Vec<Vec<(usize, f64)>>,
}

impl GeneralizedIntentGraph {
    /// Build the graph from a set of intent nodes.
    ///
    /// Edges are created when can_satisfy returns Some(score) with score >= min_score.
    pub fn build(nodes: Vec<GeneralizedIntentNode>, min_score: f64) -> Self {
        let n = nodes.len();
        let mut edges: Vec<Vec<(usize, f64)>> = vec![Vec::new(); n];

        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                if let Some(score) =
                    can_satisfy(&nodes[i].exchange.offering, &nodes[j].exchange.wanting)
                {
                    if score >= min_score {
                        edges[i].push((j, score));
                    }
                }
            }
        }

        Self { nodes, edges }
    }

    /// Find all simple cycles up to max_len using bounded DFS.
    pub fn find_cycles(&self, max_len: usize) -> Vec<Vec<usize>> {
        let n = self.nodes.len();
        let mut all_cycles: Vec<Vec<usize>> = Vec::new();

        for start in 0..n {
            let mut path: Vec<usize> = vec![start];
            let mut visited = vec![false; n];
            visited[start] = true;
            self.dfs_cycles(start, &mut path, &mut visited, max_len, &mut all_cycles);
        }

        Self::deduplicate_cycles(&mut all_cycles);
        all_cycles
    }

    fn dfs_cycles(
        &self,
        start: usize,
        path: &mut Vec<usize>,
        visited: &mut Vec<bool>,
        max_len: usize,
        results: &mut Vec<Vec<usize>>,
    ) {
        let current = *path.last().unwrap();

        if path.len() > max_len {
            return;
        }

        for &(next, _score) in &self.edges[current] {
            if next == start && path.len() >= 2 {
                results.push(path.clone());
            } else if !visited[next] && path.len() < max_len {
                visited[next] = true;
                path.push(next);
                self.dfs_cycles(start, path, visited, max_len, results);
                path.pop();
                visited[next] = false;
            }
        }
    }

    fn deduplicate_cycles(cycles: &mut Vec<Vec<usize>>) {
        for cycle in cycles.iter_mut() {
            if cycle.is_empty() {
                continue;
            }
            let min_pos = cycle
                .iter()
                .enumerate()
                .min_by_key(|(_, val)| *val)
                .map(|(idx, _)| idx)
                .unwrap_or(0);
            cycle.rotate_left(min_pos);
        }
        cycles.sort();
        cycles.dedup();
    }

    /// Get nodes in the graph.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Get total edge count.
    pub fn edge_count(&self) -> usize {
        self.edges.iter().map(|e| e.len()).sum()
    }
}

// ---------------------------------------------------------------------------
// Generalized solver
// ---------------------------------------------------------------------------

/// A settlement action in a generalized ring trade.
#[derive(Clone, Debug)]
pub struct GeneralizedSettlement {
    /// Sender's commitment.
    pub from: CommitmentId,
    /// Receiver's commitment.
    pub to: CommitmentId,
    /// Items being transferred from sender to receiver.
    pub items: Vec<ExchangeItem>,
}

/// A discovered generalized ring trade.
#[derive(Clone, Debug)]
pub struct GeneralizedRingTrade {
    /// Participating intent IDs in cycle order.
    pub participants: Vec<crate::IntentId>,
    /// The settlement actions (one per edge in the cycle).
    pub settlements: Vec<GeneralizedSettlement>,
    /// Combined satisfaction score (sum of edge scores / ring size).
    pub score: f64,
    /// Whether ALL participants have their full want-set satisfied (not just partial).
    pub fully_satisfied: bool,
}

/// The generalized ring trade solver.
pub struct GeneralizedSolver {
    /// Maximum cycle length to search.
    pub max_ring_size: usize,
    /// Minimum edge score to consider (0.0 = any partial satisfaction creates an edge).
    pub min_edge_score: f64,
    /// Maximum results to return.
    pub max_results: usize,
    /// Whether to require full satisfaction (score == 1.0 for every edge in the ring).
    pub require_full_satisfaction: bool,
}

impl GeneralizedSolver {
    /// Create a new solver.
    pub fn new(max_ring_size: usize) -> Self {
        Self {
            max_ring_size: max_ring_size.max(2),
            min_edge_score: 0.0,
            max_results: 100,
            require_full_satisfaction: false,
        }
    }

    /// Create a solver that requires every participant's wants to be fully met.
    pub fn strict(max_ring_size: usize) -> Self {
        Self {
            max_ring_size: max_ring_size.max(2),
            min_edge_score: 1.0,
            max_results: 100,
            require_full_satisfaction: true,
        }
    }

    /// Build the compatibility graph and find ring trades.
    pub fn solve(&self, nodes: &[GeneralizedIntentNode], now: u64) -> Vec<GeneralizedRingTrade> {
        // Filter expired intents.
        let active: Vec<GeneralizedIntentNode> =
            nodes.iter().filter(|n| now < n.expiry).cloned().collect();

        if active.len() < 2 {
            return Vec::new();
        }

        let graph = GeneralizedIntentGraph::build(active, self.min_edge_score);
        let cycles = graph.find_cycles(self.max_ring_size);
        let mut rings: Vec<GeneralizedRingTrade> = Vec::new();

        for cycle in cycles {
            if rings.len() >= self.max_results {
                break;
            }

            // Verify each edge in the cycle is valid and compute scores.
            let mut total_score = 0.0;
            let mut fully_satisfied = true;
            let mut valid = true;

            for k in 0..cycle.len() {
                let next = (k + 1) % cycle.len();
                let edge_score = graph.edges[cycle[k]]
                    .iter()
                    .find(|(target, _)| *target == cycle[next])
                    .map(|(_, s)| *s);

                match edge_score {
                    Some(s) if s > 0.0 => {
                        total_score += s;
                        if s < 1.0 {
                            fully_satisfied = false;
                        }
                    }
                    _ => {
                        valid = false;
                        break;
                    }
                }
            }

            if !valid {
                continue;
            }

            if self.require_full_satisfaction && !fully_satisfied {
                continue;
            }

            // Check for self-loops (same creator).
            let has_self_loop = cycle.iter().enumerate().any(|(i, &ci)| {
                cycle
                    .iter()
                    .enumerate()
                    .any(|(j, &cj)| i != j && graph.nodes[ci].creator == graph.nodes[cj].creator)
            });
            if has_self_loop {
                continue;
            }

            // Build settlements.
            let participants: Vec<crate::IntentId> = cycle
                .iter()
                .map(|&idx| graph.nodes[idx].intent_id)
                .collect();

            let mut settlements = Vec::new();
            for k in 0..cycle.len() {
                let next = (k + 1) % cycle.len();
                let from_node = &graph.nodes[cycle[k]];
                let to_node = &graph.nodes[cycle[next]];

                // Determine which items from the offerer satisfy the receiver's wants.
                let items = compute_settlement_items(
                    &from_node.exchange.offering,
                    &to_node.exchange.wanting,
                );

                settlements.push(GeneralizedSettlement {
                    from: from_node.creator,
                    to: to_node.creator,
                    items,
                });
            }

            let avg_score = total_score / cycle.len() as f64;
            rings.push(GeneralizedRingTrade {
                participants,
                settlements,
                score: avg_score,
                fully_satisfied,
            });
        }

        // Sort by score descending (prefer fully-satisfied, then highest average score).
        rings.sort_by(|a, b| {
            // Fully satisfied rings first.
            let full_cmp = b.fully_satisfied.cmp(&a.fully_satisfied);
            if full_cmp != std::cmp::Ordering::Equal {
                return full_cmp;
            }
            b.score
                .partial_cmp(&a.score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        rings
    }

    /// Find the best single ring trade.
    pub fn solve_best(
        &self,
        nodes: &[GeneralizedIntentNode],
        now: u64,
    ) -> Option<GeneralizedRingTrade> {
        self.solve(nodes, now).into_iter().next()
    }
}

/// Determine which offered items to transfer to satisfy the receiver's wants.
///
/// Returns the subset of offered items that match the receiver's want-set.
fn compute_settlement_items(
    offering: &[ExchangeItem],
    wanting: &[ExchangeItem],
) -> Vec<ExchangeItem> {
    let mut used_offers: Vec<bool> = vec![false; offering.len()];
    let mut items = Vec::new();

    for want in wanting {
        for (idx, offer) in offering.iter().enumerate() {
            if !used_offers[idx] && item_satisfies(offer, want) {
                used_offers[idx] = true;
                // Transfer the WANTED amount (not the full offered amount).
                items.push(want.clone());
                break;
            }
        }
    }

    items
}

// ---------------------------------------------------------------------------
// Zone classification (DFA integration point)
// ---------------------------------------------------------------------------

/// Classify an intent's zone from its exchange items.
///
/// Returns a zone path string that the DFA router can use to shard solving.
/// This is a heuristic classifier; the DFA proper handles byte-level routing.
pub fn classify_zone(exchange: &GeneralizedExchange) -> &'static str {
    let has_asset = exchange
        .offering
        .iter()
        .chain(exchange.wanting.iter())
        .any(|item| matches!(item, ExchangeItem::Asset { .. }));
    let has_cap = exchange
        .offering
        .iter()
        .chain(exchange.wanting.iter())
        .any(|item| matches!(item, ExchangeItem::Capability { .. }));
    let has_service = exchange
        .offering
        .iter()
        .chain(exchange.wanting.iter())
        .any(|item| matches!(item, ExchangeItem::Service { .. }));
    let has_storage = exchange
        .offering
        .iter()
        .chain(exchange.wanting.iter())
        .any(|item| matches!(item, ExchangeItem::Storage { .. }));

    match (has_asset, has_cap, has_service, has_storage) {
        (true, false, false, false) => "/defi/swap",
        (false, true, false, false) => "/services/capability",
        (false, false, true, false) => "/services/compute",
        (false, false, false, true) => "/storage/hosting",
        _ => "/mixed/general",
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create an asset exchange item.
    fn asset_item(id_byte: u8, amount: u64) -> ExchangeItem {
        let mut id = [0u8; 32];
        id[0] = id_byte;
        ExchangeItem::Asset { id, amount }
    }

    /// Helper: create a capability exchange item.
    fn cap_item(actions: &[&str], resource: &str, duration: u64) -> ExchangeItem {
        ExchangeItem::Capability {
            actions: actions.iter().map(|s| s.to_string()).collect(),
            resource: resource.to_string(),
            duration_epochs: duration,
        }
    }

    /// Helper: create a service exchange item.
    fn service_item(endpoint: &str, invocations: u64) -> ExchangeItem {
        ExchangeItem::Service {
            endpoint: endpoint.to_string(),
            invocations,
        }
    }

    /// Helper: create a storage exchange item.
    fn storage_item(queue: &str, bytes: u64, duration: u64) -> ExchangeItem {
        ExchangeItem::Storage {
            queue_id: queue.to_string(),
            bytes,
            duration_epochs: duration,
        }
    }

    /// Helper: create a name exchange item.
    fn name_item(namespace: &str, entry: &str) -> ExchangeItem {
        ExchangeItem::Name {
            namespace: namespace.to_string(),
            entry: entry.to_string(),
        }
    }

    /// Helper: create a generalized intent node.
    fn make_node(
        id_byte: u8,
        offering: Vec<ExchangeItem>,
        wanting: Vec<ExchangeItem>,
        creator_byte: u8,
    ) -> GeneralizedIntentNode {
        let mut intent_id = [0u8; 32];
        intent_id[0] = id_byte;
        GeneralizedIntentNode {
            intent_id,
            exchange: GeneralizedExchange { offering, wanting },
            creator: CommitmentId([creator_byte; 32]),
            expiry: 9999,
            zone: None,
        }
    }

    // =========================================================================
    // Item satisfaction tests
    // =========================================================================

    #[test]
    fn test_asset_satisfies_same_id_sufficient_amount() {
        let offer = asset_item(0xAA, 100);
        let want = asset_item(0xAA, 50);
        assert!(item_satisfies(&offer, &want));
    }

    #[test]
    fn test_asset_does_not_satisfy_different_id() {
        let offer = asset_item(0xAA, 100);
        let want = asset_item(0xBB, 50);
        assert!(!item_satisfies(&offer, &want));
    }

    #[test]
    fn test_asset_does_not_satisfy_insufficient_amount() {
        let offer = asset_item(0xAA, 30);
        let want = asset_item(0xAA, 50);
        assert!(!item_satisfies(&offer, &want));
    }

    #[test]
    fn test_capability_satisfies_matching_spec() {
        let offer = cap_item(&["read", "write"], "documents/*", 10);
        let want = cap_item(&["read"], "documents/*", 5);
        assert!(item_satisfies(&offer, &want));
    }

    #[test]
    fn test_capability_does_not_satisfy_missing_action() {
        let offer = cap_item(&["read"], "documents/*", 10);
        let want = cap_item(&["write"], "documents/*", 5);
        assert!(!item_satisfies(&offer, &want));
    }

    #[test]
    fn test_capability_wildcard_action_satisfies_any() {
        let offer = cap_item(&["*"], "documents/*", 10);
        let want = cap_item(&["delete"], "documents/*", 5);
        assert!(item_satisfies(&offer, &want));
    }

    #[test]
    fn test_capability_resource_mismatch() {
        let offer = cap_item(&["read"], "documents/*", 10);
        let want = cap_item(&["read"], "treasury/*", 5);
        assert!(!item_satisfies(&offer, &want));
    }

    #[test]
    fn test_capability_duration_insufficient() {
        let offer = cap_item(&["read"], "documents/*", 3);
        let want = cap_item(&["read"], "documents/*", 10);
        assert!(!item_satisfies(&offer, &want));
    }

    #[test]
    fn test_capability_permanent_satisfies_any_duration() {
        // duration 0 = permanent, satisfies any requested duration.
        let offer = cap_item(&["read"], "documents/*", 0);
        let want = cap_item(&["read"], "documents/*", 100);
        assert!(item_satisfies(&offer, &want));
    }

    #[test]
    fn test_service_satisfies() {
        let offer = service_item("ml-inference", 100);
        let want = service_item("ml-inference", 50);
        assert!(item_satisfies(&offer, &want));
    }

    #[test]
    fn test_service_different_endpoint() {
        let offer = service_item("ml-inference", 100);
        let want = service_item("data-pipeline", 50);
        assert!(!item_satisfies(&offer, &want));
    }

    #[test]
    fn test_storage_satisfies() {
        let offer = storage_item("inbox-a", 1024, 10);
        let want = storage_item("inbox-a", 512, 5);
        assert!(item_satisfies(&offer, &want));
    }

    #[test]
    fn test_name_satisfies_exact() {
        let offer = name_item("oracle", "alice");
        let want = name_item("oracle", "alice");
        assert!(item_satisfies(&offer, &want));
    }

    #[test]
    fn test_name_does_not_satisfy_different() {
        let offer = name_item("oracle", "alice");
        let want = name_item("oracle", "bob");
        assert!(!item_satisfies(&offer, &want));
    }

    #[test]
    fn test_cross_type_never_satisfies() {
        let offer = asset_item(0xAA, 100);
        let want = cap_item(&["read"], "documents/*", 5);
        assert!(!item_satisfies(&offer, &want));
    }

    // =========================================================================
    // can_satisfy tests
    // =========================================================================

    #[test]
    fn test_can_satisfy_full_coverage() {
        let offering = vec![asset_item(0xAA, 100), cap_item(&["read"], "docs/*", 10)];
        let wanting = vec![asset_item(0xAA, 50), cap_item(&["read"], "docs/*", 5)];
        let score = can_satisfy(&offering, &wanting);
        assert_eq!(score, Some(1.0));
    }

    #[test]
    fn test_can_satisfy_partial_coverage() {
        let offering = vec![asset_item(0xAA, 100)];
        let wanting = vec![asset_item(0xAA, 50), cap_item(&["read"], "docs/*", 5)];
        let score = can_satisfy(&offering, &wanting);
        assert_eq!(score, Some(0.5));
    }

    #[test]
    fn test_can_satisfy_no_coverage() {
        let offering = vec![asset_item(0xAA, 100)];
        let wanting = vec![cap_item(&["read"], "docs/*", 5)];
        let score = can_satisfy(&offering, &wanting);
        assert_eq!(score, None);
    }

    #[test]
    fn test_can_satisfy_empty_wanting() {
        let offering = vec![asset_item(0xAA, 100)];
        let wanting: Vec<ExchangeItem> = vec![];
        assert_eq!(can_satisfy(&offering, &wanting), None);
    }

    #[test]
    fn test_can_satisfy_no_double_spending() {
        // One offer item cannot satisfy two wants.
        let offering = vec![asset_item(0xAA, 100)];
        let wanting = vec![asset_item(0xAA, 50), asset_item(0xAA, 50)];
        // Only one want can be satisfied (greedy: first one wins).
        let score = can_satisfy(&offering, &wanting);
        assert_eq!(score, Some(0.5));
    }

    // =========================================================================
    // 2-party asset-for-capability swap
    // =========================================================================

    #[test]
    fn test_two_party_asset_for_capability() {
        // Alice offers tokens, wants read access.
        // Bob offers read access, wants tokens.
        let nodes = vec![
            make_node(
                1,
                vec![asset_item(0xAA, 100)],
                vec![cap_item(&["read"], "oracle/*", 10)],
                0x01,
            ),
            make_node(
                2,
                vec![cap_item(&["read"], "oracle/*", 10)],
                vec![asset_item(0xAA, 50)],
                0x02,
            ),
        ];

        let solver = GeneralizedSolver::new(5);
        let rings = solver.solve(&nodes, 100);

        assert!(!rings.is_empty(), "should find asset-for-capability swap");
        let ring = &rings[0];
        assert_eq!(ring.participants.len(), 2);
        assert!(ring.fully_satisfied);
        assert_eq!(ring.settlements.len(), 2);

        // Alice sends tokens to Bob.
        assert_eq!(ring.settlements[0].from, CommitmentId([0x01; 32]));
        assert_eq!(ring.settlements[0].to, CommitmentId([0x02; 32]));
        assert!(matches!(
            ring.settlements[0].items[0],
            ExchangeItem::Asset { amount: 50, .. }
        ));

        // Bob sends capability to Alice.
        assert_eq!(ring.settlements[1].from, CommitmentId([0x02; 32]));
        assert_eq!(ring.settlements[1].to, CommitmentId([0x01; 32]));
        assert!(matches!(
            ring.settlements[1].items[0],
            ExchangeItem::Capability { .. }
        ));
    }

    // =========================================================================
    // 3-party mixed ring
    // =========================================================================

    #[test]
    fn test_three_party_mixed_ring() {
        // Alice: offers tokens, wants compute service.
        // Bob: offers compute service, wants read access on oracle.
        // Carol: offers read access on oracle, wants tokens.
        //
        // Ring: Alice -> Carol (tokens), Carol -> Bob (oracle access), Bob -> Alice (compute).
        let nodes = vec![
            make_node(
                1,
                vec![asset_item(0xAA, 100)],
                vec![service_item("ml-inference", 10)],
                0x01,
            ),
            make_node(
                2,
                vec![service_item("ml-inference", 20)],
                vec![cap_item(&["read"], "oracle/*", 5)],
                0x02,
            ),
            make_node(
                3,
                vec![cap_item(&["read"], "oracle/*", 10)],
                vec![asset_item(0xAA, 50)],
                0x03,
            ),
        ];

        let solver = GeneralizedSolver::new(5);
        let rings = solver.solve(&nodes, 100);

        assert!(!rings.is_empty(), "should find 3-party mixed ring");
        let ring = &rings[0];
        assert_eq!(ring.participants.len(), 3);
        assert!(ring.fully_satisfied);
        assert_eq!(ring.settlements.len(), 3);
    }

    // =========================================================================
    // Compound want satisfaction
    // =========================================================================

    #[test]
    fn test_compound_want_requires_all_items() {
        // Alice offers tokens AND storage.
        // Bob wants BOTH tokens and storage (compound want).
        // Bob offers capability.
        // Alice wants capability.
        let nodes = vec![
            make_node(
                1,
                vec![asset_item(0xAA, 100), storage_item("inbox", 1024, 10)],
                vec![cap_item(&["execute"], "compute/*", 5)],
                0x01,
            ),
            make_node(
                2,
                vec![cap_item(&["execute"], "compute/*", 10)],
                vec![asset_item(0xAA, 50), storage_item("inbox", 512, 5)],
                0x02,
            ),
        ];

        let solver = GeneralizedSolver::strict(5);
        let rings = solver.solve(&nodes, 100);

        assert!(!rings.is_empty(), "should find compound-want swap");
        let ring = &rings[0];
        assert!(ring.fully_satisfied);

        // Alice -> Bob should include BOTH tokens and storage.
        let alice_to_bob = &ring.settlements[0];
        assert_eq!(alice_to_bob.items.len(), 2);
    }

    #[test]
    fn test_compound_want_partial_not_found_in_strict_mode() {
        // Alice offers only tokens (not storage).
        // Bob wants tokens AND storage (compound).
        // In strict mode, this ring should NOT be found.
        let nodes = vec![
            make_node(
                1,
                vec![asset_item(0xAA, 100)],
                vec![cap_item(&["execute"], "compute/*", 5)],
                0x01,
            ),
            make_node(
                2,
                vec![cap_item(&["execute"], "compute/*", 10)],
                vec![asset_item(0xAA, 50), storage_item("inbox", 512, 5)],
                0x02,
            ),
        ];

        let solver = GeneralizedSolver::strict(5);
        let rings = solver.solve(&nodes, 100);

        assert!(
            rings.is_empty(),
            "strict solver should not find partial-satisfaction rings"
        );
    }

    // =========================================================================
    // Expired intents filtered out
    // =========================================================================

    #[test]
    fn test_expired_intents_excluded() {
        let mut node1 = make_node(
            1,
            vec![asset_item(0xAA, 100)],
            vec![cap_item(&["read"], "docs/*", 5)],
            0x01,
        );
        node1.expiry = 50; // already expired at now=100

        let node2 = make_node(
            2,
            vec![cap_item(&["read"], "docs/*", 10)],
            vec![asset_item(0xAA, 50)],
            0x02,
        );

        let solver = GeneralizedSolver::new(5);
        let rings = solver.solve(&[node1, node2], 100);

        assert!(rings.is_empty(), "expired intent should not participate");
    }

    // =========================================================================
    // Self-loop (same creator) rejected
    // =========================================================================

    #[test]
    fn test_self_loop_rejected() {
        // Same creator on both nodes.
        let nodes = vec![
            make_node(
                1,
                vec![asset_item(0xAA, 100)],
                vec![cap_item(&["read"], "docs/*", 5)],
                0x01, // same creator
            ),
            make_node(
                2,
                vec![cap_item(&["read"], "docs/*", 10)],
                vec![asset_item(0xAA, 50)],
                0x01, // same creator!
            ),
        ];

        let solver = GeneralizedSolver::new(5);
        let rings = solver.solve(&nodes, 100);

        assert!(rings.is_empty(), "self-loops should be rejected");
    }

    // =========================================================================
    // Zone classification
    // =========================================================================

    #[test]
    fn test_zone_classification_asset_only() {
        let exchange = GeneralizedExchange {
            offering: vec![asset_item(0xAA, 100)],
            wanting: vec![asset_item(0xBB, 50)],
        };
        assert_eq!(classify_zone(&exchange), "/defi/swap");
    }

    #[test]
    fn test_zone_classification_capability_only() {
        let exchange = GeneralizedExchange {
            offering: vec![cap_item(&["read"], "docs/*", 5)],
            wanting: vec![cap_item(&["write"], "docs/*", 5)],
        };
        assert_eq!(classify_zone(&exchange), "/services/capability");
    }

    #[test]
    fn test_zone_classification_mixed() {
        let exchange = GeneralizedExchange {
            offering: vec![asset_item(0xAA, 100)],
            wanting: vec![cap_item(&["read"], "docs/*", 5)],
        };
        assert_eq!(classify_zone(&exchange), "/mixed/general");
    }

    // =========================================================================
    // Real-world scenario: service-for-tokens
    // =========================================================================

    #[test]
    fn test_service_for_tokens_swap() {
        // "I'll run your ML model if you give me 500 tokens"
        let nodes = vec![
            make_node(
                1,
                vec![asset_item(0xAA, 500)],
                vec![service_item("ml-inference", 10)],
                0x01,
            ),
            make_node(
                2,
                vec![service_item("ml-inference", 20)],
                vec![asset_item(0xAA, 400)],
                0x02,
            ),
        ];

        let solver = GeneralizedSolver::new(5);
        let rings = solver.solve(&nodes, 100);

        assert!(!rings.is_empty());
        assert!(rings[0].fully_satisfied);
    }

    // =========================================================================
    // Real-world scenario: capability-for-capability barter
    // =========================================================================

    #[test]
    fn test_capability_barter() {
        // "I'll give you oracle access if you give me storage hosting"
        let nodes = vec![
            make_node(
                1,
                vec![cap_item(&["read"], "oracle/*", 10)],
                vec![storage_item("my-inbox", 2048, 5)],
                0x01,
            ),
            make_node(
                2,
                vec![storage_item("my-inbox", 4096, 10)],
                vec![cap_item(&["read"], "oracle/*", 5)],
                0x02,
            ),
        ];

        let solver = GeneralizedSolver::new(5);
        let rings = solver.solve(&nodes, 100);

        assert!(!rings.is_empty(), "cap-for-storage barter should resolve");
        assert!(rings[0].fully_satisfied);
    }

    // =========================================================================
    // Real-world scenario: 3-DAO governance ring
    // =========================================================================

    #[test]
    fn test_three_dao_governance_ring() {
        // DAO-A: offers naming authority, wants compute capability.
        // DAO-B: offers compute capability, wants treasury read access.
        // DAO-C: offers treasury read access, wants naming authority.
        let nodes = vec![
            make_node(
                1,
                vec![name_item("registry", "oracle.alice")],
                vec![cap_item(&["execute"], "compute/*", 5)],
                0x01,
            ),
            make_node(
                2,
                vec![cap_item(&["execute"], "compute/*", 10)],
                vec![cap_item(&["read"], "treasury/*", 5)],
                0x02,
            ),
            make_node(
                3,
                vec![cap_item(&["read"], "treasury/*", 10)],
                vec![name_item("registry", "oracle.alice")],
                0x03,
            ),
        ];

        let solver = GeneralizedSolver::new(5);
        let rings = solver.solve(&nodes, 100);

        assert!(!rings.is_empty(), "3-DAO governance ring should be found");
        let ring = &rings[0];
        assert_eq!(ring.participants.len(), 3);
        assert!(ring.fully_satisfied);
    }

    // =========================================================================
    // Graph construction test
    // =========================================================================

    #[test]
    fn test_graph_construction() {
        let nodes = vec![
            make_node(
                1,
                vec![asset_item(0xAA, 100)],
                vec![cap_item(&["read"], "docs/*", 5)],
                0x01,
            ),
            make_node(
                2,
                vec![cap_item(&["read"], "docs/*", 10)],
                vec![asset_item(0xAA, 50)],
                0x02,
            ),
        ];

        let graph = GeneralizedIntentGraph::build(nodes, 0.0);
        assert_eq!(graph.node_count(), 2);
        // Node 0 offers tokens -> satisfies Node 1's want (tokens). Edge 0->1.
        // Node 1 offers cap -> satisfies Node 0's want (cap). Edge 1->0.
        assert_eq!(graph.edge_count(), 2);
    }

    // =========================================================================
    // No ring possible
    // =========================================================================

    #[test]
    fn test_no_ring_when_incompatible() {
        // Both want the same thing, neither offers what the other wants.
        let nodes = vec![
            make_node(
                1,
                vec![asset_item(0xAA, 100)],
                vec![cap_item(&["read"], "docs/*", 5)],
                0x01,
            ),
            make_node(
                2,
                vec![asset_item(0xBB, 100)],
                vec![cap_item(&["read"], "docs/*", 5)],
                0x02,
            ),
        ];

        let solver = GeneralizedSolver::new(5);
        let rings = solver.solve(&nodes, 100);
        assert!(rings.is_empty());
    }
}
