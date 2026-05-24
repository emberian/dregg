//! DFA-mediated gossip topic filtering for the intent pool.
//!
//! Background: today's intent gossip in [`crate::gossip`] is flat broadcast —
//! every connected peer sees every intent. The audit in
//! `STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md` §4.4 and the rationalization in
//! `DFA-RATIONALIZATION-DESIGN.md` §6.2 name the gap: topic filtering should
//! be DFA-mediated so subscribers only receive intents on topics they've
//! opted into, the topic-filter table is constitutionally committed (when
//! used in a federated deployment), and the seam composes with the local
//! matcher cleanly.
//!
//! This module is **non-invasive**: it sits alongside the existing
//! [`crate::gossip::IntentPool`] and provides a filter that the caller wires
//! in *before* invoking `broadcast_intent` / `receive_intent`. The intent
//! pool itself stays as-is — Lane Intent-α owns it.
//!
//! # Composition
//!
//! ```text
//! Sender                                Receiver
//!   |                                      |
//!   v                                      v
//! Intent (intent_id || topic_bytes)     GossipTopicFilter::accept(topic_bytes)
//!   |                                      |
//!   v                                      v
//! sender.broadcast()                      if accepted: pool.receive_intent(intent)
//! ```
//!
//! The filter does NOT decide whether the matcher's local Datalog evaluation
//! will accept — that's a structural check on (held caps × MatchSpec) and
//! happens later. The filter answers "should I even look at this intent?"
//!
//! # Topic shape
//!
//! `GossipTopicFilter` doesn't prescribe a layout for the topic bytes;
//! callers pass whatever bytestring is meaningful for their pool. Two
//! conventional shapes:
//!
//! 1. **Intent ID prefix:** the first 8 bytes of `intent.id` (a hash). The
//!    filter's pattern recognizes a prefix range (e.g., "topics starting
//!    with `0x00` through `0x7F`").
//! 2. **Topic namespace string:** a UTF-8 namespace like
//!    `"topic:auth:login"` or `"topic:swap:USDC-ETH"`. The filter is a
//!    URL-style prefix DFA.
//!
//! The DFA accepts a flat byte slice; the filter is agnostic.

use std::sync::Arc;

use pyana_dfa::{
    Classification, GovernedRouter, KindRegistry, Pattern, RouteTableBuilder, RouteTarget,
};

/// Userspace destination kind for accepted topics.
pub const TOPIC_ACCEPT_KIND: &str = "intent_topic_accept";

/// Decision returned by [`GossipTopicFilter::accept`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TopicDecision {
    /// The topic matched a configured route. Carries the userspace payload
    /// the route was registered with (`payload`); intent pools that don't
    /// care can ignore this.
    Accept { payload: Vec<u8> },
    /// The topic was explicitly blocked.
    Drop,
    /// No route matched. Default action is up to the caller (typically: drop).
    NoMatch,
}

impl TopicDecision {
    /// True iff the decision is `Accept`.
    pub fn is_accept(&self) -> bool {
        matches!(self, TopicDecision::Accept { .. })
    }
}

/// A DFA-mediated topic filter for the intent gossip layer.
///
/// Wraps a [`pyana_dfa::GovernedRouter`]; the route table commits to which
/// topics the local peer subscribes to, supports atomic CAS-based swaps when
/// subscriptions change, and (when a `ThresholdVerifier` is wired) supports
/// federation-bound governance over the subscription set.
#[derive(Clone, Debug)]
pub struct GossipTopicFilter {
    router: Arc<GovernedRouter>,
}

impl GossipTopicFilter {
    /// Build a filter from a fully-configured [`GovernedRouter`]. Callers who
    /// want governance / threshold-signed table swaps should construct the
    /// router directly.
    pub fn from_router(router: GovernedRouter) -> Self {
        Self {
            router: Arc::new(router),
        }
    }

    /// Build a filter that accepts every topic. Useful for dev / testing
    /// where the pool wants the legacy "flat broadcast" semantics
    /// transparently.
    pub fn accept_all() -> Self {
        let table = RouteTableBuilder::new()
            .route_pattern(
                Pattern::prefix_of(Pattern::any_byte()),
                RouteTarget::userspace(TOPIC_ACCEPT_KIND, b"".to_vec()),
            )
            .compile();
        let mut router = GovernedRouter::new(table);
        let mut reg = KindRegistry::new();
        reg.register(TOPIC_ACCEPT_KIND);
        router.set_kind_registry(reg);
        Self::from_router(router)
    }

    /// Build a filter from a list of accepted-topic patterns and a list of
    /// blocked-topic patterns. Blocked topics take precedence (longer prefix
    /// wins, but `RouteTarget::Drop` and `TOPIC_ACCEPT_KIND` are disjoint;
    /// when both match the deepest-accept rule selects, so order patterns
    /// from broad-accept to specific-block).
    pub fn from_subscriptions(accepts: &[&str], drops: &[&str]) -> Self {
        let mut b = RouteTableBuilder::new();
        for pat in accepts {
            let with_star = if pat.ends_with('*') {
                pat.to_string()
            } else {
                format!("{pat}*")
            };
            b = b.route(
                &with_star,
                RouteTarget::userspace(TOPIC_ACCEPT_KIND, b"".to_vec()),
            );
        }
        for pat in drops {
            let with_star = if pat.ends_with('*') {
                pat.to_string()
            } else {
                format!("{pat}*")
            };
            b = b.route(&with_star, RouteTarget::Drop);
        }
        let table = b.compile();
        let mut router = GovernedRouter::new(table);
        let mut reg = KindRegistry::new();
        reg.register(TOPIC_ACCEPT_KIND);
        router.set_kind_registry(reg);
        Self::from_router(router)
    }

    /// Classify a topic byte slice. The slice can be any layout the pool
    /// chose (intent-id prefix, topic-namespace string, framing bytes).
    pub fn accept(&self, topic_bytes: &[u8]) -> TopicDecision {
        match self.router.classify_path(topic_bytes) {
            Some(Classification { target, .. }) => match target {
                RouteTarget::Drop => TopicDecision::Drop,
                RouteTarget::Userspace(u) if u.kind == TOPIC_ACCEPT_KIND => TopicDecision::Accept {
                    payload: u.payload.clone(),
                },
                // Unknown handler / federation forward: treat as accept with
                // empty payload (the pool can decide how to interpret it).
                RouteTarget::Handler(_) | RouteTarget::Federation { .. } => TopicDecision::Accept {
                    payload: Vec::new(),
                },
                RouteTarget::Userspace(_) => TopicDecision::NoMatch,
            },
            None => TopicDecision::NoMatch,
        }
    }

    /// Convenience: `accept(b).is_accept()`.
    pub fn permits(&self, topic_bytes: &[u8]) -> bool {
        self.accept(topic_bytes).is_accept()
    }

    /// The route table commitment (constitutional hash).
    pub fn commitment(&self) -> &[u8; 32] {
        self.router.commitment()
    }

    /// The underlying governed router (for callers that want to perform
    /// governance-bound table swaps).
    pub fn router(&self) -> &GovernedRouter {
        &self.router
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accept_all_permits_everything() {
        let f = GossipTopicFilter::accept_all();
        assert!(f.permits(b"anything"));
        assert!(f.permits(b"topic:auth:login"));
        assert!(f.permits(&[0xAB, 0xCD, 0xEF]));
    }

    #[test]
    fn subscription_prefixes_filter_correctly() {
        let f = GossipTopicFilter::from_subscriptions(
            &["topic:auth:", "topic:swap:"],
            &["topic:spam:"],
        );
        assert!(f.permits(b"topic:auth:login"));
        assert!(f.permits(b"topic:swap:USDC-ETH"));
        assert_eq!(f.accept(b"topic:spam:flood"), TopicDecision::Drop);
        assert_eq!(f.accept(b"topic:other:event"), TopicDecision::NoMatch);
    }

    #[test]
    fn raw_byte_topic_routes_work() {
        // Topic shape: 1-byte family + arbitrary tail. Subscribers say
        // "I want family 0x01" via a literal prefix.
        let f = GossipTopicFilter::from_subscriptions(&["\x01"], &[]);
        assert!(f.permits(&[0x01, 0xAA, 0xBB]));
        assert!(!f.permits(&[0x02, 0xAA, 0xBB]));
    }

    #[test]
    fn commitment_is_deterministic_per_subscription() {
        let f1 = GossipTopicFilter::from_subscriptions(&["t:a"], &["t:bad"]);
        let f2 = GossipTopicFilter::from_subscriptions(&["t:a"], &["t:bad"]);
        assert_eq!(f1.commitment(), f2.commitment());

        let f3 = GossipTopicFilter::from_subscriptions(&["t:b"], &["t:bad"]);
        assert_ne!(f1.commitment(), f3.commitment());
    }

    #[test]
    fn accept_carries_userspace_payload() {
        use pyana_dfa::Pattern;
        let table = pyana_dfa::RouteTableBuilder::new()
            .route_pattern(
                Pattern::path_prefix("topic:auth:"),
                RouteTarget::userspace(TOPIC_ACCEPT_KIND, b"auth_subscription".to_vec()),
            )
            .compile();
        let mut router = pyana_dfa::GovernedRouter::new(table);
        let mut reg = pyana_dfa::KindRegistry::new();
        reg.register(TOPIC_ACCEPT_KIND);
        router.set_kind_registry(reg);
        let f = GossipTopicFilter::from_router(router);

        match f.accept(b"topic:auth:login") {
            TopicDecision::Accept { payload } => assert_eq!(payload, b"auth_subscription"),
            other => panic!("expected accept with payload, got {other:?}"),
        }
    }
}
