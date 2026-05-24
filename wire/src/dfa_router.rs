//! Wire-side adapter over the canonical [`pyana_dfa`] DFA router.
//!
//! Historically this module hosted its own DFA implementation (255-state cap,
//! trie-only patterns, `proof_data: Vec<u8>` governance stub). That code has
//! been promoted into the dedicated [`pyana_dfa`] crate so it can be a
//! userspace primitive for starbridge-apps rather than a wire-only concern.
//!
//! What lives here now:
//!
//! * Type re-exports from [`pyana_dfa`] so existing `pyana_wire::dfa_router`
//!   importers keep compiling.
//! * Convenience helpers for the wire-specific accept types
//!   (`Cell(CellId)`, `Federation(FederationId)`) that the legacy `RouteTarget`
//!   enum had as first-class variants. They're now expressed via
//!   `RouteTarget::Handler("cell:<hex>")` and
//!   `RouteTarget::Federation { group_id }` — see [`cell_target`] and
//!   [`federation_target`] below.
//! * Light wrappers ([`compile_routes`], [`dispatch_path`],
//!   [`dispatch_message`], [`DispatchDecision`]) that reproduce the old wire
//!   API on top of the new [`pyana_dfa::RouteTableBuilder`].
//!
//! New code should use [`pyana_dfa`] directly.

use pyana_captp::FederationId;
use pyana_types::CellId;

pub use pyana_dfa::air;
pub use pyana_dfa::{
    Classification, Dfa, FilterTree, GovernanceProof, GovernedRouter, KindRegistry, Pattern,
    RouteTable, RouteTableBuilder, RouteTarget, RouteUpdateError, Router, ThresholdVerifier,
    TopicFilter, UserspaceTarget,
};

// ---------------------------------------------------------------------------
// Wire-specific destination helpers
// ---------------------------------------------------------------------------

/// Build a `RouteTarget` that names a local cell. Cells were a first-class
/// variant in the legacy router; now they're handlers with a canonical name.
pub fn cell_target(cell_id: CellId) -> RouteTarget {
    RouteTarget::Handler(format!("cell:{}", hex(&cell_id.0)))
}

/// Build a `RouteTarget` forwarding to a peer federation.
pub fn federation_target(fed_id: FederationId) -> RouteTarget {
    RouteTarget::Federation { group_id: fed_id.0 }
}

/// Extract a cell ID encoded in a `RouteTarget::Handler("cell:<hex>")`.
pub fn target_as_cell(target: &RouteTarget) -> Option<CellId> {
    match target {
        RouteTarget::Handler(s) if s.starts_with("cell:") => {
            let hex_str = &s[5..];
            if hex_str.len() != 64 {
                return None;
            }
            let mut bytes = [0u8; 32];
            for (i, b) in bytes.iter_mut().enumerate() {
                *b = u8::from_str_radix(&hex_str[i * 2..i * 2 + 2], 16).ok()?;
            }
            Some(CellId(bytes))
        }
        _ => None,
    }
}

/// Extract a federation ID from a `RouteTarget::Federation { group_id }`.
pub fn target_as_federation(target: &RouteTarget) -> Option<FederationId> {
    match target {
        RouteTarget::Federation { group_id } => Some(FederationId(*group_id)),
        _ => None,
    }
}

fn hex(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for byte in b {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}

// ---------------------------------------------------------------------------
// Legacy ergonomics: `compile_routes` and `DispatchDecision`
// ---------------------------------------------------------------------------

/// Compile URL-style routes into a [`RouteTable`].
///
/// Equivalent to feeding each `(pattern, target)` pair into
/// [`RouteTableBuilder::route`]. Kept for wire-side ergonomics and for the
/// teasting / preflight harnesses that imported `compile_routes` by name.
pub fn compile_routes(routes: &[(&str, RouteTarget)]) -> RouteTable {
    let mut b = RouteTableBuilder::new();
    for (pat, target) in routes {
        b = b.route(pat, target.clone());
    }
    b.compile()
}

/// Higher-level dispatch decision, retained at the wire layer for callers
/// that don't want to match the [`RouteTarget`] enum directly. The new
/// canonical analog is [`pyana_dfa::DispatchDecision`]; this enum keeps the
/// wire-specific `DeliverToCell` / `ForwardToFederation` shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DispatchDecision {
    DeliverToCell(CellId),
    DeliverToHandler(String),
    ForwardToFederation(FederationId),
    Discard,
    Unrouted,
}

impl DispatchDecision {
    pub fn from_target(target: Option<&RouteTarget>) -> Self {
        match target {
            None => DispatchDecision::Unrouted,
            Some(RouteTarget::Drop) => DispatchDecision::Discard,
            Some(RouteTarget::Handler(name)) => {
                // Recognize the "cell:<hex>" sentinel.
                if let Some(cid) = target_as_cell(&RouteTarget::Handler(name.clone())) {
                    DispatchDecision::DeliverToCell(cid)
                } else {
                    DispatchDecision::DeliverToHandler(name.clone())
                }
            }
            Some(RouteTarget::Federation { group_id }) => {
                DispatchDecision::ForwardToFederation(FederationId(*group_id))
            }
            Some(RouteTarget::Userspace(_)) => DispatchDecision::Unrouted,
        }
    }
}

/// Classify a message via the router and project the result to
/// [`DispatchDecision`].
pub fn dispatch_message(router: &Router, message: &[u8]) -> DispatchDecision {
    DispatchDecision::from_target(router.classify(message).map(|c| c.target))
}

/// Classify a URL-style path and project the result to [`DispatchDecision`].
pub fn dispatch_path(router: &Router, path: &[u8]) -> DispatchDecision {
    DispatchDecision::from_target(router.classify_path(path).map(|c| c.target))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        CellId([b; 32])
    }

    fn fid(b: u8) -> FederationId {
        FederationId([b; 32])
    }

    #[test]
    fn cell_target_roundtrip() {
        let id = cid(0xAB);
        let t = cell_target(id);
        assert_eq!(target_as_cell(&t), Some(id));
    }

    #[test]
    fn federation_target_roundtrip() {
        let id = fid(0x42);
        let t = federation_target(id);
        assert_eq!(target_as_federation(&t), Some(id));
    }

    #[test]
    fn compile_routes_classifies() {
        let table = compile_routes(&[
            ("/cells/alpha/*", cell_target(cid(1))),
            ("/intents/*", RouteTarget::handler("intent_pool")),
            ("/federated/*", federation_target(fid(7))),
            ("/blocked/*", RouteTarget::Drop),
        ]);
        let router = Router::new(table);

        assert_eq!(
            dispatch_path(&router, b"/cells/alpha/transfer"),
            DispatchDecision::DeliverToCell(cid(1))
        );
        assert_eq!(
            dispatch_path(&router, b"/intents/submit"),
            DispatchDecision::DeliverToHandler("intent_pool".into())
        );
        assert_eq!(
            dispatch_path(&router, b"/federated/sync"),
            DispatchDecision::ForwardToFederation(fid(7))
        );
        assert_eq!(
            dispatch_path(&router, b"/blocked/anything"),
            DispatchDecision::Discard
        );
        assert_eq!(
            dispatch_path(&router, b"/unknown/path"),
            DispatchDecision::Unrouted
        );
    }

    #[test]
    fn governed_update_cas_through_wire_shim() {
        let table = compile_routes(&[("/x/*", cell_target(cid(1)))]);
        let commitment = table.commitment;
        let mut governed = GovernedRouter::new(table);

        let new_table = compile_routes(&[("/x/*", cell_target(cid(2)))]);
        let proof = GovernanceProof {
            expected_old_commitment: commitment,
            proof_data: vec![1, 2, 3],
        };
        governed.update_routes(new_table, &proof).unwrap();

        let c = governed.classify_path(b"/x/y").unwrap();
        assert_eq!(target_as_cell(c.target), Some(cid(2)));
    }
}
