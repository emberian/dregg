//! Ring trade solver: multi-party cycle detection for atomic settlement.
//!
//! Instead of pairwise matching (A wants B, B wants A), this solver finds
//! **ring trades** -- cycles in the intent compatibility graph where A->B,
//! B->C, C->A can all settle atomically without a common denominator.
//!
//! # Algorithm
//!
//! Based on Johnson's algorithm for finding all elementary circuits in a
//! directed graph, bounded to a maximum cycle length (3-5) for practical
//! atomic settlement.
//!
//! # References
//!
//! - Johnson (1975): "Finding all the elementary circuits of a directed graph"
//! - Shapley-Scarf (1974): "Top Trading Cycles" for indivisible goods
//! - Roth et al. (2004): Kidney exchange algorithms (Nobel Prize 2012)

use crate::CommitmentId;
use crate::exchange::AssetId;

/// An exchange specification: "I have X, I want Y"
#[derive(Clone, Debug)]
pub struct ExchangeSpec {
    /// What I'm offering (asset type + amount).
    pub offer_asset: AssetId,
    pub offer_amount: u64,
    /// What I want (asset type + min amount).
    pub want_asset: AssetId,
    pub want_min_amount: u64,
    /// Optional: minimum acceptable exchange rate (offer/want).
    pub min_rate: Option<f64>,
    /// Optional: maximum acceptable exchange rate (offer/want).
    pub max_rate: Option<f64>,
}

/// A node in the intent graph.
#[derive(Clone, Debug)]
pub struct IntentNode {
    /// Content-addressed intent ID.
    pub intent_id: crate::IntentId,
    /// The exchange parameters.
    pub exchange: ExchangeSpec,
    /// Anonymous creator commitment.
    pub creator: CommitmentId,
    /// Expiry timestamp.
    pub expiry: u64,
}

/// A discovered ring trade.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RingTrade {
    /// The participating intents in cycle order.
    pub participants: Vec<crate::IntentId>,
    /// The transfers that settle this ring.
    pub settlements: Vec<Settlement>,
    /// Combined compatibility score.
    pub score: f64,
}

/// A single transfer within a ring trade settlement.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Settlement {
    /// Sender's commitment ID.
    pub from: CommitmentId,
    /// Receiver's commitment ID.
    pub to: CommitmentId,
    /// Asset being transferred.
    pub asset: AssetId,
    /// Amount being transferred.
    pub amount: u64,
}

/// Errors from the ring solver.
#[derive(Clone, Debug, PartialEq)]
pub enum SolverError {
    /// A participant's offer amount is insufficient for the next party's want.
    InsufficientAmount {
        offerer_index: usize,
        offered: u64,
        needed: u64,
    },
    /// Time constraints don't overlap (not all intents valid simultaneously).
    TimeConstraintViolation { expired_index: usize, now: u64 },
    /// Ring contains a self-loop (same creator appears twice).
    SelfLoop,
    /// Ring is empty or has fewer than 2 participants.
    TooSmall,
    /// Rate bounds violated.
    RateBoundsViolated { index: usize },
}

impl std::fmt::Display for SolverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InsufficientAmount {
                offerer_index,
                offered,
                needed,
            } => write!(
                f,
                "node {} offers {} but next node needs {}",
                offerer_index, offered, needed
            ),
            Self::TimeConstraintViolation { expired_index, now } => {
                write!(f, "node {} expired at time {}", expired_index, now)
            }
            Self::SelfLoop => write!(f, "ring contains a self-loop"),
            Self::TooSmall => write!(f, "ring must have at least 2 participants"),
            Self::RateBoundsViolated { index } => {
                write!(f, "rate bounds violated at node {}", index)
            }
        }
    }
}

/// The ring trade solver.
pub struct RingSolver {
    /// Maximum cycle length to search for.
    pub max_ring_size: usize,
    /// Minimum compatibility score to consider an edge.
    pub min_edge_score: f64,
    /// Maximum number of rings to find per solve() call.
    pub max_results: usize,
}

impl RingSolver {
    /// Create a new solver with the given maximum ring size.
    pub fn new(max_ring_size: usize) -> Self {
        Self {
            max_ring_size: max_ring_size.max(2),
            min_edge_score: 0.0,
            max_results: 100,
        }
    }

    /// Build the intent compatibility graph from active intents.
    pub fn build_graph(&self, intents: &[IntentNode]) -> IntentGraph {
        let mut edges: Vec<Vec<(usize, f64)>> = vec![Vec::new(); intents.len()];

        for i in 0..intents.len() {
            for j in 0..intents.len() {
                if i == j {
                    continue;
                }
                if let Some(score) = IntentGraph::is_compatible(&intents[i], &intents[j]) {
                    if score >= self.min_edge_score {
                        edges[i].push((j, score));
                    }
                }
            }
        }

        IntentGraph {
            nodes: intents.to_vec(),
            edges,
        }
    }

    /// Find all valid ring trades in the graph.
    /// Uses Johnson's algorithm bounded to max_ring_size.
    pub fn find_rings(&self, graph: &IntentGraph) -> Vec<RingTrade> {
        let cycles = graph.find_cycles(self.max_ring_size);
        let mut rings: Vec<RingTrade> = Vec::new();

        for cycle in cycles {
            if rings.len() >= self.max_results {
                break;
            }
            // Build the ring trade from the cycle
            let mut score = 0.0;
            let mut valid = true;

            for k in 0..cycle.len() {
                let next = (k + 1) % cycle.len();
                let edge_score = graph.edges[cycle[k]]
                    .iter()
                    .find(|(target, _)| *target == cycle[next])
                    .map(|(_, s)| *s)
                    .unwrap_or(0.0);
                if edge_score <= 0.0 {
                    valid = false;
                    break;
                }
                score += edge_score;
            }

            if !valid {
                continue;
            }

            let participants: Vec<crate::IntentId> = cycle
                .iter()
                .map(|&idx| graph.nodes[idx].intent_id)
                .collect();

            let mut settlements = Vec::new();
            for k in 0..cycle.len() {
                let next = (k + 1) % cycle.len();
                let from_node = &graph.nodes[cycle[k]];
                let to_node = &graph.nodes[cycle[next]];
                settlements.push(Settlement {
                    from: from_node.creator,
                    to: to_node.creator,
                    asset: from_node.exchange.offer_asset,
                    amount: to_node
                        .exchange
                        .want_min_amount
                        .min(from_node.exchange.offer_amount),
                });
            }

            // Scoring convention (audit §7): score = number of participants.
            // This matches `validate_ring` so the same ring produces the
            // same score whichever entry point built it. The accumulated
            // edge-weight `score` above is informative (it would tilt
            // toward exact-match rings) but conflicting with
            // `validate_ring`, which is the canonical scorer. We retain
            // the edge-score loop for the early `valid` filter (rings
            // with any non-positive edge score must be discarded).
            let _ = score;
            rings.push(RingTrade {
                participants,
                settlements,
                score: cycle.len() as f64,
            });
        }

        // Sort by score descending
        rings.sort_by(|a, b| {
            b.score
                .partial_cmp(&a.score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        rings
    }

    /// Validate a ring: all quantities compatible, times overlap.
    pub fn validate_ring(&self, ring: &[IntentNode], now: u64) -> Result<RingTrade, SolverError> {
        if ring.len() < 2 {
            return Err(SolverError::TooSmall);
        }

        // Check for self-loops (same creator appears more than once).
        for i in 0..ring.len() {
            for j in (i + 1)..ring.len() {
                if ring[i].creator == ring[j].creator {
                    return Err(SolverError::SelfLoop);
                }
            }
        }

        // Check time constraints: all intents must be valid at `now`.
        for (idx, node) in ring.iter().enumerate() {
            if now >= node.expiry {
                return Err(SolverError::TimeConstraintViolation {
                    expired_index: idx,
                    now,
                });
            }
        }

        // Check quantity compatibility: each node's offer must satisfy the next node's want.
        for k in 0..ring.len() {
            let next = (k + 1) % ring.len();
            let offerer = &ring[k];
            let receiver = &ring[next];

            // The offerer's offered asset must be what the receiver wants.
            if offerer.exchange.offer_asset != receiver.exchange.want_asset {
                return Err(SolverError::InsufficientAmount {
                    offerer_index: k,
                    offered: 0,
                    needed: receiver.exchange.want_min_amount,
                });
            }

            // The offerer must offer enough for the receiver's minimum.
            if offerer.exchange.offer_amount < receiver.exchange.want_min_amount {
                return Err(SolverError::InsufficientAmount {
                    offerer_index: k,
                    offered: offerer.exchange.offer_amount,
                    needed: receiver.exchange.want_min_amount,
                });
            }

            // Check rate bounds if specified.
            if let Some(min_rate) = offerer.exchange.min_rate {
                // Rate = what I get / what I give = receiver's offer to me / my offer to them
                // For the offerer at position k, they give to node (k+1) and receive from node (k-1)
                // Actually, in a ring: node k gives offer_amount of offer_asset to node (k+1)
                // and receives want_min_amount of want_asset from node (k-1) which is ring[(k + ring.len() - 1) % ring.len()]
                let prev = (k + ring.len() - 1) % ring.len();
                let giver_to_me = &ring[prev];
                let i_receive = giver_to_me
                    .exchange
                    .offer_amount
                    .min(offerer.exchange.want_min_amount);
                let i_give = offerer
                    .exchange
                    .offer_amount
                    .min(receiver.exchange.want_min_amount);
                if i_give > 0 {
                    let actual_rate = i_receive as f64 / i_give as f64;
                    if actual_rate < min_rate {
                        return Err(SolverError::RateBoundsViolated { index: k });
                    }
                }
            }

            if let Some(max_rate) = offerer.exchange.max_rate {
                let prev = (k + ring.len() - 1) % ring.len();
                let giver_to_me = &ring[prev];
                let i_receive = giver_to_me
                    .exchange
                    .offer_amount
                    .min(offerer.exchange.want_min_amount);
                let i_give = offerer
                    .exchange
                    .offer_amount
                    .min(receiver.exchange.want_min_amount);
                if i_give > 0 {
                    let actual_rate = i_receive as f64 / i_give as f64;
                    if actual_rate > max_rate {
                        return Err(SolverError::RateBoundsViolated { index: k });
                    }
                }
            }
        }

        // Build settlements.
        let mut settlements = Vec::new();
        for k in 0..ring.len() {
            let next = (k + 1) % ring.len();
            let offerer = &ring[k];
            let receiver = &ring[next];
            let amount = offerer
                .exchange
                .offer_amount
                .min(receiver.exchange.want_min_amount)
                .max(receiver.exchange.want_min_amount);
            settlements.push(Settlement {
                from: offerer.creator,
                to: receiver.creator,
                asset: offerer.exchange.offer_asset,
                amount,
            });
        }

        let participants: Vec<crate::IntentId> = ring.iter().map(|n| n.intent_id).collect();

        // Score is the number of participants (more = better social welfare).
        let score = ring.len() as f64;

        Ok(RingTrade {
            participants,
            settlements,
            score,
        })
    }

    /// Find the BEST ring (highest score / most participants satisfied).
    pub fn solve_best(&self, intents: &[IntentNode], now: u64) -> Option<RingTrade> {
        // Filter expired intents.
        let active: Vec<IntentNode> = intents.iter().filter(|n| now < n.expiry).cloned().collect();

        if active.len() < 2 {
            return None;
        }

        let graph = self.build_graph(&active);
        let rings = self.find_rings(&graph);
        rings.into_iter().next()
    }

    /// Solve greedily: find rings, settle them, remove from pool, repeat.
    pub fn solve_greedy(&self, intents: &mut Vec<IntentNode>, now: u64) -> Vec<RingTrade> {
        let mut results = Vec::new();
        let mut used_ids: std::collections::HashSet<crate::IntentId> =
            std::collections::HashSet::new();

        loop {
            // Remove expired and already-used intents.
            intents.retain(|n| now < n.expiry && !used_ids.contains(&n.intent_id));

            if intents.len() < 2 {
                break;
            }

            let graph = self.build_graph(intents);
            let rings = self.find_rings(&graph);

            if rings.is_empty() {
                break;
            }

            // Take the best ring.
            let best = &rings[0];

            // Check that none of the participants were already used.
            let any_used = best.participants.iter().any(|id| used_ids.contains(id));
            if any_used {
                // Try the next ring, or break if no viable ring exists.
                let mut found = false;
                for ring in &rings {
                    if !ring.participants.iter().any(|id| used_ids.contains(id)) {
                        for id in &ring.participants {
                            used_ids.insert(*id);
                        }
                        results.push(ring.clone());
                        found = true;
                        break;
                    }
                }
                if !found {
                    break;
                }
            } else {
                for id in &best.participants {
                    used_ids.insert(*id);
                }
                results.push(best.clone());
            }

            if results.len() >= self.max_results {
                break;
            }
        }

        results
    }
}

/// The intent compatibility graph (adjacency list).
pub struct IntentGraph {
    /// Nodes indexed by position.
    nodes: Vec<IntentNode>,
    /// Adjacency: edges[i] = [(j, score), ...] meaning node i's offer could satisfy node j's want.
    edges: Vec<Vec<(usize, f64)>>,
}

impl IntentGraph {
    /// Check if intent A's offer is compatible with intent B's want.
    ///
    /// Returns Some(score) if A's offered asset matches B's wanted asset and
    /// A's offered amount >= B's wanted minimum amount.
    /// Score is in (0, 1] based on how well the amounts match.
    pub fn is_compatible(a: &IntentNode, b: &IntentNode) -> Option<f64> {
        // Asset types must match: A offers what B wants.
        if a.exchange.offer_asset != b.exchange.want_asset {
            return None;
        }

        // A must offer enough for B's minimum.
        if a.exchange.offer_amount < b.exchange.want_min_amount {
            return None;
        }

        // Score: closer to exact match = higher score.
        // Perfect match (offer == want) = 1.0
        // Overshoot is slightly penalized (excess is wasted in the ring context).
        let ratio = b.exchange.want_min_amount as f64 / a.exchange.offer_amount as f64;
        let score = ratio.min(1.0); // max 1.0

        Some(score)
    }

    /// Find all simple cycles up to length max_len.
    ///
    /// Uses a bounded DFS approach (simplified Johnson's algorithm).
    pub fn find_cycles(&self, max_len: usize) -> Vec<Vec<usize>> {
        let n = self.nodes.len();
        let mut all_cycles: Vec<Vec<usize>> = Vec::new();

        for start in 0..n {
            let mut path: Vec<usize> = vec![start];
            let mut visited = vec![false; n];
            visited[start] = true;
            self.dfs_cycles(start, &mut path, &mut visited, max_len, &mut all_cycles);
        }

        // Deduplicate cycles (a cycle A->B->C->A is the same as B->C->A->B).
        Self::deduplicate_cycles(&mut all_cycles);

        all_cycles
    }

    /// DFS to find cycles starting and ending at `start`.
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
                // Found a cycle back to start.
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

    /// Deduplicate cycles: normalize each cycle to start with the smallest index.
    fn deduplicate_cycles(cycles: &mut Vec<Vec<usize>>) {
        // Normalize each cycle to its canonical rotation (smallest element first).
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

    /// Get the number of nodes.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Get the number of edges.
    pub fn edge_count(&self) -> usize {
        self.edges.iter().map(|e| e.len()).sum()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CommitmentId;

    /// Helper to create a deterministic asset ID from a byte.
    fn asset(byte: u8) -> AssetId {
        let mut id = [0u8; 32];
        id[0] = byte;
        id
    }

    /// Helper to create an IntentNode.
    fn make_node(
        id_byte: u8,
        offer_asset: u8,
        offer_amount: u64,
        want_asset: u8,
        want_min_amount: u64,
        creator_byte: u8,
        expiry: u64,
    ) -> IntentNode {
        let mut intent_id = [0u8; 32];
        intent_id[0] = id_byte;
        IntentNode {
            intent_id,
            exchange: ExchangeSpec {
                offer_asset: asset(offer_asset),
                offer_amount,
                want_asset: asset(want_asset),
                want_min_amount,
                min_rate: None,
                max_rate: None,
            },
            creator: CommitmentId([creator_byte; 32]),
            expiry,
        }
    }

    // =========================================================================
    // Test 1: Simple 2-party swap
    // =========================================================================
    #[test]
    fn test_simple_two_party_swap() {
        // A has X wants Y, B has Y wants X -> ring of size 2
        let nodes = vec![
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 9999),
            make_node(2, 0xBB, 80, 0xAA, 60, 0x02, 9999),
        ];

        let solver = RingSolver::new(5);
        let graph = solver.build_graph(&nodes);
        let rings = solver.find_rings(&graph);

        assert!(!rings.is_empty(), "should find at least one ring");
        assert_eq!(rings[0].participants.len(), 2);
        assert_eq!(rings[0].settlements.len(), 2);
    }

    // =========================================================================
    // Test 2: 3-party ring
    // =========================================================================
    #[test]
    fn test_three_party_ring() {
        // A has X wants Y, B has Y wants Z, C has Z wants X
        let nodes = vec![
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 9999), // A: has AA, wants BB
            make_node(2, 0xBB, 80, 0xCC, 30, 0x02, 9999),  // B: has BB, wants CC
            make_node(3, 0xCC, 60, 0xAA, 40, 0x03, 9999),  // C: has CC, wants AA
        ];

        let solver = RingSolver::new(5);
        let graph = solver.build_graph(&nodes);
        let rings = solver.find_rings(&graph);

        assert!(!rings.is_empty(), "should find a 3-party ring");
        let ring = &rings[0];
        assert_eq!(ring.participants.len(), 3);
        assert_eq!(ring.settlements.len(), 3);
    }

    // =========================================================================
    // Test 3: 4-party ring works
    // =========================================================================
    #[test]
    fn test_four_party_ring() {
        // A->B->C->D->A
        let nodes = vec![
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 9999),
            make_node(2, 0xBB, 80, 0xCC, 30, 0x02, 9999),
            make_node(3, 0xCC, 60, 0xDD, 20, 0x03, 9999),
            make_node(4, 0xDD, 50, 0xAA, 40, 0x04, 9999),
        ];

        let solver = RingSolver::new(5);
        let graph = solver.build_graph(&nodes);
        let rings = solver.find_rings(&graph);

        assert!(!rings.is_empty(), "should find a 4-party ring");
        // The 4-party ring should be present
        let has_four_party = rings.iter().any(|r| r.participants.len() == 4);
        assert!(has_four_party, "should have a 4-party ring");
    }

    // =========================================================================
    // Test 4: Incompatible amounts - ring found but validation fails
    // =========================================================================
    #[test]
    fn test_incompatible_amounts_validation_fails() {
        // Ring order [A, C, B] means: A->C, C->B, B->A
        // A offers AA to C (C wants AA). A has 10, but C wants 40 -> insufficient.
        // The assets match but the amounts don't.
        let ring_nodes = vec![
            IntentNode {
                intent_id: [1; 32],
                exchange: ExchangeSpec {
                    offer_asset: asset(0xAA),
                    offer_amount: 10, // only 10, but C needs 40
                    want_asset: asset(0xBB),
                    want_min_amount: 50,
                    min_rate: None,
                    max_rate: None,
                },
                creator: CommitmentId([0x01; 32]),
                expiry: 9999,
            },
            // C: offers CC, wants AA. Positioned as ring[1] so A offers to C.
            IntentNode {
                intent_id: [3; 32],
                exchange: ExchangeSpec {
                    offer_asset: asset(0xCC),
                    offer_amount: 60,
                    want_asset: asset(0xAA),
                    want_min_amount: 40, // needs 40, but A only offers 10
                    min_rate: None,
                    max_rate: None,
                },
                creator: CommitmentId([0x03; 32]),
                expiry: 9999,
            },
            // B: offers BB, wants CC. Positioned as ring[2] so C offers to B.
            IntentNode {
                intent_id: [2; 32],
                exchange: ExchangeSpec {
                    offer_asset: asset(0xBB),
                    offer_amount: 80,
                    want_asset: asset(0xCC),
                    want_min_amount: 30,
                    min_rate: None,
                    max_rate: None,
                },
                creator: CommitmentId([0x02; 32]),
                expiry: 9999,
            },
        ];

        let solver = RingSolver::new(5);
        let result = solver.validate_ring(&ring_nodes, 100);

        assert!(result.is_err());
        match result.unwrap_err() {
            SolverError::InsufficientAmount {
                offerer_index: 0,
                offered: 10,
                needed: 40,
            } => {} // expected: A offers 10 but C (next in ring) needs 40
            other => panic!("expected InsufficientAmount at index 0, got: {:?}", other),
        }
    }

    // =========================================================================
    // Test 5: Time constraint - overlapping vs non-overlapping expiries
    // =========================================================================
    #[test]
    fn test_time_constraints_overlapping_valid() {
        let ring_nodes = vec![
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 5000),
            make_node(2, 0xBB, 80, 0xAA, 60, 0x02, 6000),
        ];

        let solver = RingSolver::new(5);
        // now=1000, both expire after 1000 -> valid
        let result = solver.validate_ring(&ring_nodes, 1000);
        assert!(result.is_ok());
    }

    #[test]
    fn test_time_constraints_non_overlapping_invalid() {
        let ring_nodes = vec![
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 500), // already expired
            make_node(2, 0xBB, 80, 0xAA, 60, 0x02, 6000),
        ];

        let solver = RingSolver::new(5);
        // now=1000, first node expired at 500 -> invalid
        let result = solver.validate_ring(&ring_nodes, 1000);
        assert!(result.is_err());
        match result.unwrap_err() {
            SolverError::TimeConstraintViolation {
                expired_index: 0, ..
            } => {}
            other => panic!("expected TimeConstraintViolation, got: {:?}", other),
        }
    }

    // =========================================================================
    // Test 6: No ring exists -> empty result
    // =========================================================================
    #[test]
    fn test_no_ring_exists() {
        // All nodes want the same thing -- no cycle possible
        let nodes = vec![
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 9999),
            make_node(2, 0xCC, 80, 0xBB, 30, 0x02, 9999),
            make_node(3, 0xDD, 60, 0xBB, 20, 0x03, 9999),
        ];

        let solver = RingSolver::new(5);
        let graph = solver.build_graph(&nodes);
        let rings = solver.find_rings(&graph);

        assert!(rings.is_empty(), "no ring should exist");
    }

    // =========================================================================
    // Test 7: Greedy solver finds multiple non-overlapping rings
    // =========================================================================
    #[test]
    fn test_greedy_solver_multiple_rings() {
        // Two independent 2-party swaps
        let mut nodes = vec![
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 9999), // ring 1
            make_node(2, 0xBB, 80, 0xAA, 60, 0x02, 9999),  // ring 1
            make_node(3, 0xCC, 100, 0xDD, 50, 0x03, 9999), // ring 2
            make_node(4, 0xDD, 80, 0xCC, 60, 0x04, 9999),  // ring 2
        ];

        let solver = RingSolver::new(5);
        let rings = solver.solve_greedy(&mut nodes, 100);

        assert_eq!(rings.len(), 2, "should find 2 non-overlapping rings");

        // Verify no intent is used in more than one ring
        let mut all_participants: Vec<crate::IntentId> = Vec::new();
        for ring in &rings {
            for p in &ring.participants {
                assert!(
                    !all_participants.contains(p),
                    "intent used in multiple rings"
                );
                all_participants.push(*p);
            }
        }
    }

    // =========================================================================
    // Test 8: Self-loop rejected
    // =========================================================================
    #[test]
    fn test_self_loop_rejected() {
        // Same creator in two nodes -> self-loop
        let ring_nodes = vec![
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 9999),
            make_node(2, 0xBB, 80, 0xAA, 60, 0x01, 9999), // same creator 0x01!
        ];

        let solver = RingSolver::new(5);
        let result = solver.validate_ring(&ring_nodes, 100);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), SolverError::SelfLoop);
    }

    // =========================================================================
    // Test 9: Duplicate intent not used twice
    // =========================================================================
    #[test]
    fn test_duplicate_intent_not_used_twice() {
        // Insert the same intent twice. The greedy solver should use it only once.
        let mut nodes = vec![
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 9999),
            make_node(2, 0xBB, 80, 0xAA, 60, 0x02, 9999),
            // Duplicate of node 1 (same intent_id)
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 9999),
        ];

        let solver = RingSolver::new(5);
        let rings = solver.solve_greedy(&mut nodes, 100);

        // Should find at most 1 ring (the duplicate can't form a second ring)
        assert_eq!(rings.len(), 1);
    }

    // =========================================================================
    // Test 10: Rate bounds respected
    // =========================================================================
    #[test]
    fn test_rate_bounds_respected() {
        // A offers 100 AA for 50 BB, wants rate >= 2.0 (meaning get at least 2 BB per AA given)
        // But B only offers 80 BB for 60 AA -- actual rate for A = 50/100 = 0.5 which is < 2.0
        let ring_nodes = vec![
            IntentNode {
                intent_id: [1; 32],
                exchange: ExchangeSpec {
                    offer_asset: asset(0xAA),
                    offer_amount: 100,
                    want_asset: asset(0xBB),
                    want_min_amount: 50,
                    min_rate: Some(2.0), // wants at least 2.0 ratio
                    max_rate: None,
                },
                creator: CommitmentId([0x01; 32]),
                expiry: 9999,
            },
            IntentNode {
                intent_id: [2; 32],
                exchange: ExchangeSpec {
                    offer_asset: asset(0xBB),
                    offer_amount: 80,
                    want_asset: asset(0xAA),
                    want_min_amount: 60,
                    min_rate: None,
                    max_rate: None,
                },
                creator: CommitmentId([0x02; 32]),
                expiry: 9999,
            },
        ];

        let solver = RingSolver::new(5);
        let result = solver.validate_ring(&ring_nodes, 100);

        assert!(result.is_err());
        match result.unwrap_err() {
            SolverError::RateBoundsViolated { index: 0 } => {} // A's rate bound violated
            other => panic!("expected RateBoundsViolated at index 0, got: {:?}", other),
        }
    }

    // =========================================================================
    // Test 11: Large pool - solver terminates in reasonable time
    // =========================================================================
    #[test]
    fn test_large_pool_terminates() {
        // 100 intents forming many 2-party swap pairs.
        // Create 50 pairs: node 2i offers asset A wants asset B,
        // node 2i+1 offers asset B wants asset A (with different A,B per pair).
        // This guarantees many short cycles exist.
        let mut nodes = Vec::new();
        for i in 0..50u8 {
            let asset_a = i * 2;
            let asset_b = i * 2 + 1;
            // First node in pair: offers A, wants B
            nodes.push(make_node(i * 2, asset_a, 100, asset_b, 50, i * 2, 9999));
            // Second node in pair: offers B, wants A
            nodes.push(make_node(
                i * 2 + 1,
                asset_b,
                80,
                asset_a,
                60,
                i * 2 + 1,
                9999,
            ));
        }

        let solver = RingSolver {
            max_ring_size: 4, // bound to keep it tractable
            min_edge_score: 0.0,
            max_results: 10, // only find first 10
        };

        let start = std::time::Instant::now();
        let graph = solver.build_graph(&nodes);
        let rings = solver.find_rings(&graph);
        let elapsed = start.elapsed();

        // Should terminate within 5 seconds (typically much faster)
        assert!(elapsed.as_secs() < 5, "solver took too long: {:?}", elapsed);
        // Should find rings (each pair forms a 2-cycle)
        assert!(!rings.is_empty(), "should find rings in large pool");
    }

    // =========================================================================
    // Test 12: Settlement generation with invalid ring order is caught
    // =========================================================================
    #[test]
    fn test_settlement_invalid_ring_order_detected() {
        // This ring ordering has mismatched assets (A offers AA but B wants CC, not AA)
        // validate_ring should detect the incompatibility.
        let ring_nodes = vec![
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 9999), // A: offers AA, wants BB
            make_node(2, 0xBB, 80, 0xCC, 30, 0x02, 9999),  // B: offers BB, wants CC
            make_node(3, 0xCC, 60, 0xAA, 40, 0x03, 9999),  // C: offers CC, wants AA
        ];

        // In this ordering [A, B, C]: A->B requires A.offer == B.want.
        // A.offer_asset = AA, B.want_asset = CC. AA != CC -> fails.
        let solver = RingSolver::new(5);
        let result = solver.validate_ring(&ring_nodes, 100);
        assert!(result.is_err(), "mismatched asset types should fail");
    }

    // =========================================================================
    // Test 12 (corrected): Settlement generation with proper ring
    // =========================================================================
    #[test]
    fn test_settlement_generation_correct_ring() {
        // Proper ring: A has AA wants BB, B has BB wants CC, C has CC wants AA
        // Edges: A->B (A offers AA which is C's want, not B's), wait...
        // Edge direction: edge from A to B means A's offer satisfies B's want.
        // A offers AA. B wants CC. So A->B requires AA == CC? No.
        // Let me think again:
        // A: offers AA, wants BB
        // B: offers BB, wants CC
        // C: offers CC, wants AA
        //
        // Compatibility check: is_compatible(A, B) checks if A's offer_asset == B's want_asset.
        // B's want_asset is CC. A's offer_asset is AA. AA != CC, so NO edge A->B.
        //
        // is_compatible(A, C) checks if A's offer_asset (AA) == C's want_asset (AA). YES!
        // So edge A->C exists.
        //
        // is_compatible(B, A) checks if B's offer_asset (BB) == A's want_asset (BB). YES!
        // So edge B->A exists.
        //
        // is_compatible(C, B) checks if C's offer_asset (CC) == B's want_asset (CC). YES!
        // So edge C->B exists.
        //
        // Cycle: A->C->B->A (edges: A->C, C->B, B->A). That's a 3-cycle!
        //
        // Settlements:
        //   A sends AA to C (C wants AA)
        //   C sends CC to B (B wants CC)
        //   B sends BB to A (A wants BB)

        let ring_nodes = vec![
            IntentNode {
                intent_id: [1; 32],
                exchange: ExchangeSpec {
                    offer_asset: asset(0xAA),
                    offer_amount: 100,
                    want_asset: asset(0xBB),
                    want_min_amount: 50,
                    min_rate: None,
                    max_rate: None,
                },
                creator: CommitmentId([0x01; 32]),
                expiry: 9999,
            },
            IntentNode {
                intent_id: [2; 32],
                exchange: ExchangeSpec {
                    offer_asset: asset(0xBB),
                    offer_amount: 80,
                    want_asset: asset(0xCC),
                    want_min_amount: 30,
                    min_rate: None,
                    max_rate: None,
                },
                creator: CommitmentId([0x02; 32]),
                expiry: 9999,
            },
            IntentNode {
                intent_id: [3; 32],
                exchange: ExchangeSpec {
                    offer_asset: asset(0xCC),
                    offer_amount: 60,
                    want_asset: asset(0xAA),
                    want_min_amount: 40,
                    min_rate: None,
                    max_rate: None,
                },
                creator: CommitmentId([0x03; 32]),
                expiry: 9999,
            },
        ];

        // The ring order for validation is: [A, C, B] because:
        // A offers AA -> C (C wants AA), C offers CC -> B (B wants CC), B offers BB -> A (A wants BB)
        let ordered_ring = vec![
            ring_nodes[0].clone(), // A
            ring_nodes[2].clone(), // C
            ring_nodes[1].clone(), // B
        ];

        let solver = RingSolver::new(5);
        let result = solver.validate_ring(&ordered_ring, 100);
        assert!(result.is_ok(), "ring should validate: {:?}", result.err());

        let ring = result.unwrap();
        assert_eq!(ring.settlements.len(), 3);

        // Settlement 0: A sends AA to C (amount = C's want_min = 40)
        assert_eq!(ring.settlements[0].from, CommitmentId([0x01; 32]));
        assert_eq!(ring.settlements[0].to, CommitmentId([0x03; 32]));
        assert_eq!(ring.settlements[0].asset, asset(0xAA));
        assert_eq!(ring.settlements[0].amount, 40);

        // Settlement 1: C sends CC to B (amount = B's want_min = 30)
        assert_eq!(ring.settlements[1].from, CommitmentId([0x03; 32]));
        assert_eq!(ring.settlements[1].to, CommitmentId([0x02; 32]));
        assert_eq!(ring.settlements[1].asset, asset(0xCC));
        assert_eq!(ring.settlements[1].amount, 30);

        // Settlement 2: B sends BB to A (amount = A's want_min = 50)
        assert_eq!(ring.settlements[2].from, CommitmentId([0x02; 32]));
        assert_eq!(ring.settlements[2].to, CommitmentId([0x01; 32]));
        assert_eq!(ring.settlements[2].asset, asset(0xBB));
        assert_eq!(ring.settlements[2].amount, 50);
    }

    // =========================================================================
    // Test: solve_best returns None with empty pool
    // =========================================================================
    #[test]
    fn test_solve_best_empty_pool() {
        let solver = RingSolver::new(5);
        let result = solver.solve_best(&[], 100);
        assert!(result.is_none());
    }

    // =========================================================================
    // Test: solve_best with valid intents
    // =========================================================================
    #[test]
    fn test_solve_best_finds_ring() {
        let nodes = vec![
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 9999),
            make_node(2, 0xBB, 80, 0xAA, 60, 0x02, 9999),
        ];

        let solver = RingSolver::new(5);
        let result = solver.solve_best(&nodes, 100);
        assert!(result.is_some());
        assert_eq!(result.unwrap().participants.len(), 2);
    }

    // =========================================================================
    // Test: validate_ring rejects too-small ring
    // =========================================================================
    #[test]
    fn test_validate_ring_too_small() {
        let ring_nodes = vec![make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 9999)];

        let solver = RingSolver::new(5);
        let result = solver.validate_ring(&ring_nodes, 100);
        assert_eq!(result.unwrap_err(), SolverError::TooSmall);
    }

    // =========================================================================
    // Test: graph construction produces correct edges
    // =========================================================================
    #[test]
    fn test_graph_construction() {
        let nodes = vec![
            make_node(1, 0xAA, 100, 0xBB, 50, 0x01, 9999),
            make_node(2, 0xBB, 80, 0xAA, 60, 0x02, 9999),
        ];

        let solver = RingSolver::new(5);
        let graph = solver.build_graph(&nodes);

        assert_eq!(graph.node_count(), 2);
        // Node 0 offers AA, Node 1 wants AA -> edge 0->1
        // Node 1 offers BB, Node 0 wants BB -> edge 1->0
        assert_eq!(graph.edge_count(), 2);
    }
}
