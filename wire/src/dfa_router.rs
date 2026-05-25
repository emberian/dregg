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
// Ingress pre-filter
// ---------------------------------------------------------------------------

/// Decision returned by [`IngressFilter::check`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IngressDecision {
    /// Allow the message to proceed to the normal dispatcher.
    Allow,
    /// Drop the message silently (counts toward an "ingress filtered" metric).
    Drop,
    /// No DFA match; defaults to `Allow` for backward compatibility (the
    /// caller can elect to drop if desired).
    NoMatch,
}

impl IngressDecision {
    pub fn permits(&self) -> bool {
        matches!(self, IngressDecision::Allow | IngressDecision::NoMatch)
    }
}

/// Wire-ingress pre-filter wrapping a [`GovernedRouter`].
///
/// This is the keystone-fast-path companion described in
/// `DFA-RATIONALIZATION-DESIGN.md` §7: the swiss-table stays as the primary
/// dispatch, the DFA wraps it as a pre-filter at the wire ingress.
///
/// The filter operates on a `route_key: Vec<u8>` that the caller extracts
/// from each incoming `WireMessage`. The caller chooses what the key looks
/// like — typically a short namespace prefix like `b"captp:cap_hello:"`
/// followed by a discriminator — and configures the route table accordingly.
///
/// `RouteTarget::Drop` → drop the message. Any other accepting target →
/// allow. No match → `NoMatch` (caller decides).
#[derive(Clone, Debug)]
pub struct IngressFilter {
    router: Router,
    commitment: [u8; 32],
}

impl IngressFilter {
    /// Build a filter from a compiled [`RouteTable`].
    pub fn new(table: RouteTable) -> Self {
        let commitment = table.commitment;
        IngressFilter {
            router: Router::new(table),
            commitment,
        }
    }

    /// Build a filter from a [`GovernedRouter`] (lifts a snapshot of its
    /// table; subsequent governance updates require re-instantiation).
    pub fn from_governed(governed: &GovernedRouter) -> Self {
        let table = governed.router().table().clone();
        IngressFilter::new(table)
    }

    /// Apply the filter to a route key extracted from a wire message.
    pub fn check(&self, route_key: &[u8]) -> IngressDecision {
        match self.router.classify(route_key) {
            Some(c) => match c.target {
                RouteTarget::Drop => IngressDecision::Drop,
                _ => IngressDecision::Allow,
            },
            None => IngressDecision::NoMatch,
        }
    }

    /// Underlying route table commitment.
    pub fn commitment(&self) -> &[u8; 32] {
        &self.commitment
    }
}

/// Sentinel namespace prefixes the wire ingress uses when constructing the
/// route key for the [`IngressFilter`]. Apps that compile route tables for
/// the ingress filter should use these to anchor their patterns.
pub mod ingress_keys {
    /// CapTP framing prefix (the first bytes of a `WireMessage::CapHello`,
    /// `CapTpForward`, etc.). The dispatcher prepends `"captp:"` plus the
    /// variant discriminator before classification.
    pub const CAPTP_NAMESPACE: &[u8] = b"captp:";
    /// Token-presentation framing.
    pub const PRESENT_NAMESPACE: &[u8] = b"present:";
    /// Federation handshake (Hello, PeerAuth, etc.).
    pub const HANDSHAKE_NAMESPACE: &[u8] = b"handshake:";
    /// Ping/pong heartbeat.
    pub const HEARTBEAT_NAMESPACE: &[u8] = b"heartbeat:";
}

/// Build the route key the [`IngressFilter`] classifies for a given
/// [`crate::message::WireMessage`]. The key is a short stable byte string of the form
/// `<namespace>:<variant>` so operators can write patterns like
/// `"captp:*"` or `"handshake:hello"` to selectively block.
pub fn wire_message_route_key(msg: &crate::message::WireMessage) -> Vec<u8> {
    let variant: &str = msg.variant_name();
    let ns: &[u8] = match variant {
        "Hello" | "Welcome" | "PeerChallenge" | "PeerAuthResponse" | "PeerAuthenticated" => {
            ingress_keys::HANDSHAKE_NAMESPACE
        }
        "Ping" | "Pong" => ingress_keys::HEARTBEAT_NAMESPACE,
        "PresentToken"
        | "PresentationResult"
        | "RequestAttestedRoot"
        | "AttestedRoot"
        | "AttestedRootPush"
        | "SubmitRevocation"
        | "RevocationAck"
        | "RequestNonMembership"
        | "NonMembershipResponse" => ingress_keys::PRESENT_NAMESPACE,
        "CapHello" | "CapGoodbye" | "EnlivenSturdyRef" | "EnlivenResponse" | "DropRemoteRef"
        | "PipelinedMsg" | "PromiseBroken" | "PresentHandoff" | "HandoffAccepted" => {
            ingress_keys::CAPTP_NAMESPACE
        }
        _ => b"control:",
    };
    let mut out = Vec::with_capacity(ns.len() + variant.len());
    out.extend_from_slice(ns);
    // ns already ends with ":"; append the variant name lowercased
    for b in variant.bytes() {
        // Lowercase ASCII to align with userspace pattern conventions
        // (e.g. `"captp:cap_hello"`). Non-ASCII (cannot happen for these
        // variant names) is passed through unchanged.
        if b.is_ascii_uppercase() {
            out.push(b + 32);
        } else {
            out.push(b);
        }
    }
    out
}

#[cfg(test)]
mod ingress_tests {
    use super::*;

    #[test]
    fn ingress_filter_drops_blocked_namespace() {
        let table = compile_routes(&[
            ("captp:cap_hello:*", RouteTarget::handler("captp")),
            ("present:*", RouteTarget::handler("present")),
            ("blocked:*", RouteTarget::Drop),
        ]);
        let f = IngressFilter::new(table);
        assert_eq!(f.check(b"captp:cap_hello:abc"), IngressDecision::Allow);
        assert_eq!(f.check(b"blocked:malformed"), IngressDecision::Drop);
        assert_eq!(f.check(b"unknown:msg"), IngressDecision::NoMatch);
    }

    #[test]
    fn ingress_filter_commitment_matches_table() {
        let table = compile_routes(&[("captp:*", RouteTarget::handler("captp"))]);
        let commitment = table.commitment;
        let f = IngressFilter::new(table);
        assert_eq!(*f.commitment(), commitment);
    }
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
