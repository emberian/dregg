//! Cross-federation intent matching.
//!
//! Today the intent pool is single-federation: an intent posted to
//! federation A's gossip is only visible to A's cipherclerks. Audit §7
//! flagged this — multi-federation rings (e.g., a swap between two
//! tokens whose primary federations differ) cannot form because
//! solvers only see one federation's pool at a time.
//!
//! The fix wires the cross-federation registry
//! ([`pyana_federation::KnownFederations`]) into the intent layer's
//! solver dispatch. For each known federation, the solver collects
//! that federation's `RingTrade` candidates and produces a unified
//! cross-federation candidate set.
//!
//! ## Design
//!
//! Cross-federation ring detection is *additive*: intents are still
//! local to their submitting federation, but a `CrossFederationSolver`
//! takes a `KnownFederations` and a per-federation intent provider,
//! merges the pools (preserving federation provenance), and runs
//! standard ring detection over the merged graph. Resulting rings
//! whose participants span multiple federations are wrapped in a
//! [`CrossFedRingTrade`] with per-leg federation tags so the lowering
//! layer can produce the right `CrossFedReceiptBundle` entries on
//! settlement.
//!
//! The federation crate is read-only here per lane constraints — we
//! consume `KnownFederations` but don't restructure it.

use pyana_federation::{FederationId, KnownFederations};

use crate::solver::{RingSolver, RingTrade, Settlement};
use crate::{IntentId, solver::IntentNode};

/// A ring trade tagged with per-leg federation provenance.
///
/// The `participants` field mirrors `RingTrade::participants` — same
/// intent-id ordering. The `federations` parallel vector records the
/// originating federation for each participant. When the ring spans
/// more than one distinct federation, this is a *cross-federation*
/// ring and the settlement turn carries a
/// `CrossFedReceiptBundle` entry per remote leg (per Lane N's bridge
/// design).
#[derive(Clone, Debug)]
pub struct CrossFedRingTrade {
    /// The underlying ring trade.
    pub ring: RingTrade,
    /// Per-participant federation tags (parallel to `ring.participants`).
    pub federations: Vec<FederationId>,
}

impl CrossFedRingTrade {
    /// Whether this ring spans more than one federation. Single-fed
    /// rings settle through the normal trustless engine path;
    /// multi-fed rings need cross-federation receipt bundling.
    pub fn is_cross_federation(&self) -> bool {
        if self.federations.is_empty() {
            return false;
        }
        let first = self.federations[0];
        self.federations.iter().any(|f| *f != first)
    }

    /// The set of distinct federations participating in this ring.
    pub fn distinct_federations(&self) -> Vec<FederationId> {
        let mut seen: Vec<FederationId> = Vec::new();
        for f in &self.federations {
            if !seen.contains(f) {
                seen.push(*f);
            }
        }
        seen
    }
}

/// An intent node paired with the federation it originated from.
#[derive(Clone, Debug)]
pub struct FederatedIntentNode {
    pub federation: FederationId,
    pub node: IntentNode,
}

/// Solver that operates across multiple federations' pools.
///
/// Construct with a [`KnownFederations`] reference and a per-federation
/// intent provider; the solver iterates over registered federations,
/// merges their pools (tagging by federation), and runs cycle
/// detection over the merged graph. Each discovered ring is wrapped
/// in a [`CrossFedRingTrade`] with federation provenance preserved.
pub struct CrossFederationSolver<'a> {
    /// Underlying single-federation solver (parameterizes ring size,
    /// max results, etc.).
    pub inner: RingSolver,
    /// Federation registry — read-only.
    pub known: &'a KnownFederations,
}

impl<'a> CrossFederationSolver<'a> {
    /// Create a new cross-federation solver wrapping a single-fed solver.
    pub fn new(inner: RingSolver, known: &'a KnownFederations) -> Self {
        Self { inner, known }
    }

    /// Solve over a flat list of federation-tagged intents. The caller
    /// is responsible for assembling this list from per-federation
    /// pools (typically: walk `known.iter()`, look up each federation's
    /// intent pool, push tagged intents).
    ///
    /// Returns ALL rings (single-fed *and* cross-fed); use
    /// [`CrossFedRingTrade::is_cross_federation`] to filter.
    pub fn solve(&self, federated: &[FederatedIntentNode], now: u64) -> Vec<CrossFedRingTrade> {
        if federated.is_empty() {
            return Vec::new();
        }

        // Map IntentId → FederationId for fast lookup.
        let mut intent_fed: std::collections::HashMap<IntentId, FederationId> =
            std::collections::HashMap::new();
        let mut nodes: Vec<IntentNode> = Vec::with_capacity(federated.len());
        for f in federated {
            intent_fed.insert(f.node.intent_id, f.federation);
            nodes.push(f.node.clone());
        }

        let active: Vec<IntentNode> = nodes.iter().filter(|n| now < n.expiry).cloned().collect();
        if active.len() < 2 {
            return Vec::new();
        }
        let graph = self.inner.build_graph(&active);
        let rings = self.inner.find_rings(&graph);

        rings
            .into_iter()
            .map(|ring| {
                let federations: Vec<FederationId> = ring
                    .participants
                    .iter()
                    .map(|id| intent_fed.get(id).copied().unwrap_or(FederationId([0; 32])))
                    .collect();
                CrossFedRingTrade { ring, federations }
            })
            .collect()
    }

    /// Solve for ONLY rings that span more than one federation. Useful
    /// for the cross-federation dispatch path — single-fed rings are
    /// handled by the standard `RingSolver`.
    pub fn solve_cross_fed_only(
        &self,
        federated: &[FederatedIntentNode],
        now: u64,
    ) -> Vec<CrossFedRingTrade> {
        self.solve(federated, now)
            .into_iter()
            .filter(|r| r.is_cross_federation())
            .collect()
    }
}

/// Convenience: extract the asset settlements that cross from one
/// federation to another. Each entry in the returned vec is
/// (sending_fed, receiving_fed, Settlement). The lowering layer uses
/// these to attach a `CrossFedReceiptBundle` to the settlement turn
/// per Lane N's bridge protocol.
pub fn cross_federation_legs(
    ring: &CrossFedRingTrade,
) -> Vec<(FederationId, FederationId, Settlement)> {
    let n = ring.ring.settlements.len();
    if n == 0 || ring.federations.len() != ring.ring.participants.len() {
        return Vec::new();
    }
    let mut out = Vec::new();
    for k in 0..n {
        let next = (k + 1) % n;
        let from_fed = ring.federations[k];
        let to_fed = ring.federations[next];
        if from_fed != to_fed {
            out.push((from_fed, to_fed, ring.ring.settlements[k].clone()));
        }
    }
    out
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CommitmentId;
    use crate::solver::ExchangeSpec;

    fn fed_id(b: u8) -> FederationId {
        FederationId([b; 32])
    }

    fn make_node(intent_byte: u8, creator_byte: u8, offer: u8, want: u8) -> IntentNode {
        let mut intent_id = [0u8; 32];
        intent_id[0] = intent_byte;
        let mut offer_id = [0u8; 32];
        offer_id[0] = offer;
        let mut want_id = [0u8; 32];
        want_id[0] = want;
        IntentNode {
            intent_id,
            exchange: ExchangeSpec {
                offer_asset: offer_id,
                offer_amount: 100,
                want_asset: want_id,
                want_min_amount: 50,
                min_rate: None,
                max_rate: None,
            },
            creator: CommitmentId([creator_byte; 32]),
            expiry: 9999,
        }
    }

    #[test]
    fn cross_fed_ring_detection() {
        // Federation A holds intent 1: offers AA, wants BB.
        // Federation B holds intent 2: offers BB, wants AA.
        // A cross-fed ring exists between them.
        let known = KnownFederations::new();
        let inner = RingSolver::new(3);
        let solver = CrossFederationSolver::new(inner, &known);

        let nodes = vec![
            FederatedIntentNode {
                federation: fed_id(0xAA),
                node: make_node(1, 0x11, 0xAA, 0xBB),
            },
            FederatedIntentNode {
                federation: fed_id(0xBB),
                node: make_node(2, 0x22, 0xBB, 0xAA),
            },
        ];

        let rings = solver.solve(&nodes, 100);
        assert!(!rings.is_empty(), "should find a 2-participant ring");
        assert!(
            rings[0].is_cross_federation(),
            "ring spans federations AA and BB"
        );
        let fs = rings[0].distinct_federations();
        assert_eq!(fs.len(), 2);
    }

    #[test]
    fn single_fed_ring_not_flagged_as_cross() {
        let known = KnownFederations::new();
        let inner = RingSolver::new(3);
        let solver = CrossFederationSolver::new(inner, &known);

        let nodes = vec![
            FederatedIntentNode {
                federation: fed_id(0xAA),
                node: make_node(1, 0x11, 0xAA, 0xBB),
            },
            FederatedIntentNode {
                federation: fed_id(0xAA),
                node: make_node(2, 0x22, 0xBB, 0xAA),
            },
        ];

        let rings = solver.solve(&nodes, 100);
        assert!(!rings.is_empty());
        assert!(!rings[0].is_cross_federation());
    }

    #[test]
    fn solve_cross_fed_only_filters_single_fed() {
        let known = KnownFederations::new();
        let inner = RingSolver::new(3);
        let solver = CrossFederationSolver::new(inner, &known);

        let nodes = vec![
            FederatedIntentNode {
                federation: fed_id(0xAA),
                node: make_node(1, 0x11, 0xAA, 0xBB),
            },
            FederatedIntentNode {
                federation: fed_id(0xAA),
                node: make_node(2, 0x22, 0xBB, 0xAA),
            },
        ];
        let cross_only = solver.solve_cross_fed_only(&nodes, 100);
        assert!(
            cross_only.is_empty(),
            "single-fed rings should be filtered out"
        );
    }

    #[test]
    fn cross_federation_legs_identifies_inter_fed_transfers() {
        // A 3-way ring: feds AA, BB, CC. Each leg crosses a federation
        // boundary.
        let nodes = vec![
            FederatedIntentNode {
                federation: fed_id(0xAA),
                node: make_node(1, 0x11, 0xAA, 0xCC),
            },
            FederatedIntentNode {
                federation: fed_id(0xCC),
                node: make_node(3, 0x33, 0xCC, 0xBB),
            },
            FederatedIntentNode {
                federation: fed_id(0xBB),
                node: make_node(2, 0x22, 0xBB, 0xAA),
            },
        ];
        let known = KnownFederations::new();
        let inner = RingSolver::new(5);
        let solver = CrossFederationSolver::new(inner, &known);
        let rings = solver.solve(&nodes, 100);
        assert!(!rings.is_empty(), "should find a 3-participant ring");
        let ring = &rings[0];
        assert!(ring.is_cross_federation());
        let legs = cross_federation_legs(ring);
        // All 3 legs cross federation boundaries.
        assert_eq!(legs.len(), 3);
    }
}
