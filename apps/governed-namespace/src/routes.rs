//! DFA-governed routing for the governed-namespace app.
//!
//! Historically this module was a 287-line `BTreeMap<String, RouteEntry>`
//! pretending to be a DFA. It's now a thin adapter on top of the canonical
//! [`pyana_dfa`] crate's [`GovernedRouter`], preserving the public surface
//! (`RoutingTable`, `RouteEntry`, `RouteClass`, `Classification`) so the rest
//! of the app doesn't notice the swap.
//!
//! Semantic preservation:
//!
//! - `RouteClass` is encoded as a `RouteTarget::Userspace { kind: "namespace_class",
//!   payload: postcard(RouteClass) }` in the underlying DFA. The kind is
//!   registered with the `GovernedRouter`'s `KindRegistry`.
//! - `RouteEntry.prefix` is fed to the DFA as a `"/prefix/*"`-style pattern,
//!   so paths starting with the prefix match (longest-prefix-wins is enforced
//!   by the DFA compiler's longest-match semantics, not by ordering).
//! - `RoutingTable::version` and `replace_all` semantics are preserved
//!   (version increments on every replace).
//! - `RoutingTable::commitment` returns the underlying DFA's BLAKE3 commitment
//!   so the governance hash chain stays meaningful (the new commitment is
//!   the DFA route table commitment, not the old JSON serialization; this is
//!   a one-time migration that all consumers of `commitment()` see uniformly).

use std::collections::BTreeMap;

use pyana_dfa::{
    Classification as DfaClassification, GovernedRouter, KindRegistry, RouteTableBuilder,
    RouteTarget,
};
use serde::{Deserialize, Serialize};

/// Registered userspace-kind identifier for the namespace-class destination.
pub const NAMESPACE_CLASS_KIND: &str = "namespace_class";

/// Access classification for a route.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RouteClass {
    /// Anyone can access (no auth required).
    Public,
    /// Only authenticated members can access.
    MembersOnly,
    /// Only administrators can access.
    AdminOnly,
    /// Requires multi-signature (e.g., treasury).
    Multisig { threshold: u32 },
    /// Custom classification with a named policy.
    Custom(String),
}

impl RouteClass {
    /// Human-readable label for the classification.
    pub fn label(&self) -> &str {
        match self {
            RouteClass::Public => "public",
            RouteClass::MembersOnly => "members_only",
            RouteClass::AdminOnly => "admin_only",
            RouteClass::Multisig { .. } => "multisig",
            RouteClass::Custom(name) => name.as_str(),
        }
    }
}

/// A single route entry: maps a path prefix to an access classification.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RouteEntry {
    /// The path prefix pattern (e.g., "/public/", "/treasury/").
    /// Always starts with "/" and ends with "/".
    pub prefix: String,
    /// The access classification for this route.
    pub class: RouteClass,
    /// Optional description for governance proposals.
    pub description: Option<String>,
}

/// The compiled DFA routing table.
///
/// Backed by [`pyana_dfa::GovernedRouter`]. The `BTreeMap` mirror is retained
/// so `entries()` / `len()` / governance proposal previews stay cheap; the
/// authoritative classifier is the compiled router.
#[derive(Clone)]
pub struct RoutingTable {
    /// Authoritative DFA classifier (compiled from `entries`).
    router: GovernedRouter,
    /// Ordered mirror of the routes for fast iteration / proposal previews.
    entries: BTreeMap<String, RouteEntry>,
    /// The version number of this table (incremented on each governance amendment).
    pub version: u64,
}

impl std::fmt::Debug for RoutingTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RoutingTable")
            .field("entries", &self.entries)
            .field("version", &self.version)
            .finish_non_exhaustive()
    }
}

impl PartialEq for RoutingTable {
    fn eq(&self, other: &Self) -> bool {
        self.entries == other.entries && self.version == other.version
    }
}

impl Eq for RoutingTable {}

impl Serialize for RoutingTable {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        // Serialize as a portable (entries, version) tuple.
        #[derive(Serialize)]
        struct RT<'a> {
            entries: &'a BTreeMap<String, RouteEntry>,
            version: u64,
        }
        RT {
            entries: &self.entries,
            version: self.version,
        }
        .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for RoutingTable {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        struct RT {
            entries: BTreeMap<String, RouteEntry>,
            version: u64,
        }
        let RT { entries, version } = RT::deserialize(deserializer)?;
        let router = build_router(entries.values().cloned().collect::<Vec<_>>());
        Ok(RoutingTable {
            router,
            entries,
            version,
        })
    }
}

/// The result of classifying a path through the DFA.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Classification {
    /// The matching route entry (None = no route matched, deny by default).
    pub route: Option<RouteEntry>,
    /// The matched prefix (longest match).
    pub matched_prefix: Option<String>,
    /// The remaining path after the prefix (the "file path" within the route).
    pub remainder: String,
}

fn build_router(entries: Vec<RouteEntry>) -> GovernedRouter {
    let mut builder = RouteTableBuilder::new();
    for entry in &entries {
        // `/prefix/*` semantics: the prefix matches anything that starts with
        // it. Encode the RouteClass as a postcard payload under the
        // `namespace_class` userspace kind.
        let payload =
            postcard::to_allocvec(&entry.class).expect("RouteClass postcard encoding cannot fail");
        let pattern = format!("{}*", entry.prefix);
        builder = builder.route(
            &pattern,
            RouteTarget::userspace(NAMESPACE_CLASS_KIND, payload),
        );
    }
    let table = builder.compile();
    let mut router = GovernedRouter::new(table);
    let mut registry = KindRegistry::new();
    registry.register(NAMESPACE_CLASS_KIND);
    router.set_kind_registry(registry);
    router
}

fn decode_classification(raw: Option<DfaClassification<'_>>, normalized: &str) -> Classification {
    match raw {
        Some(c) => {
            // Decode the userspace payload back into a RouteClass.
            let (class, route_entry_prefix) = match c.target {
                RouteTarget::Userspace(u) if u.kind == NAMESPACE_CLASS_KIND => {
                    let class: RouteClass = postcard::from_bytes(&u.payload)
                        .expect("RouteClass payload was produced by build_router");
                    // matched_prefix bytes correspond to the literal prefix
                    // we configured (route("/prefix/*", _) -> declared
                    // prefix length is the literal-byte length).
                    let prefix = String::from_utf8_lossy(c.matched_prefix).into_owned();
                    (Some(class), Some(prefix))
                }
                _ => (None, None),
            };
            let matched_prefix = route_entry_prefix.clone();
            let remainder = String::from_utf8_lossy(c.remainder).into_owned();
            let route = class.map(|class| RouteEntry {
                prefix: route_entry_prefix.unwrap_or_default(),
                class,
                description: None,
            });
            Classification {
                route,
                matched_prefix,
                remainder,
            }
        }
        None => Classification {
            route: None,
            matched_prefix: None,
            remainder: normalized.to_string(),
        },
    }
}

impl RoutingTable {
    /// Create a new empty routing table at version 0.
    pub fn new() -> Self {
        let router = build_router(Vec::new());
        Self {
            router,
            entries: BTreeMap::new(),
            version: 0,
        }
    }

    /// Create a routing table with the default DAO routes.
    pub fn default_dao() -> Self {
        let mut table = Self::new();
        for entry in default_dao_entries() {
            table.entries.insert(entry.prefix.clone(), entry);
        }
        table.recompile();
        table
    }

    fn recompile(&mut self) {
        let entries: Vec<RouteEntry> = self.entries.values().cloned().collect();
        self.router = build_router(entries);
    }

    /// Add or update a route entry.
    pub fn add_route(&mut self, entry: RouteEntry) {
        self.entries.insert(entry.prefix.clone(), entry);
        self.recompile();
    }

    /// Remove a route by prefix.
    pub fn remove_route(&mut self, prefix: &str) -> bool {
        let removed = self.entries.remove(prefix).is_some();
        if removed {
            self.recompile();
        }
        removed
    }

    /// Classify a path by finding the longest matching prefix.
    ///
    /// Backed by the canonical [`pyana_dfa`] DFA.
    pub fn classify(&self, path: &str) -> Classification {
        // Ensure path starts with /
        let normalized = if path.starts_with('/') {
            path.to_string()
        } else {
            format!("/{path}")
        };
        let raw = self.router.classify_path(normalized.as_bytes());
        // Re-bind the lifetime: re-derive from the classifier's table.
        // We do this here (eagerly clone strings) because Classification is owned.
        decode_classification(raw, &normalized)
    }

    /// Compute the blake3 commitment hash of this routing table.
    ///
    /// The commitment is the underlying DFA route table commitment, which is
    /// deterministic over (transitions, accept_map, prefix_lens) and changes
    /// whenever any route is added/removed/altered.
    pub fn commitment(&self) -> [u8; 32] {
        *self.router.commitment()
    }

    /// Get all route entries as a list (for API responses).
    pub fn entries(&self) -> Vec<&RouteEntry> {
        self.entries.values().collect()
    }

    /// Get the number of routes.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Check if the table is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Replace the entire route set atomically (used when governance passes an amendment).
    pub fn replace_all(&mut self, new_routes: Vec<RouteEntry>) {
        self.entries.clear();
        for entry in new_routes {
            self.entries.insert(entry.prefix.clone(), entry);
        }
        self.version += 1;
        self.recompile();
    }
}

impl Default for RoutingTable {
    fn default() -> Self {
        Self::new()
    }
}

fn default_dao_entries() -> Vec<RouteEntry> {
    vec![
        RouteEntry {
            prefix: "/public/".to_string(),
            class: RouteClass::Public,
            description: Some("Publicly accessible files".to_string()),
        },
        RouteEntry {
            prefix: "/members/".to_string(),
            class: RouteClass::MembersOnly,
            description: Some("Member-only documents".to_string()),
        },
        RouteEntry {
            prefix: "/admin/".to_string(),
            class: RouteClass::AdminOnly,
            description: Some("Administrative files".to_string()),
        },
        RouteEntry {
            prefix: "/treasury/".to_string(),
            class: RouteClass::Multisig { threshold: 3 },
            description: Some("Treasury documents requiring multisig".to_string()),
        },
        RouteEntry {
            prefix: "/proposals/".to_string(),
            class: RouteClass::MembersOnly,
            description: Some("Governance proposals".to_string()),
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_longest_prefix() {
        let table = RoutingTable::default_dao();

        let c = table.classify("/public/readme.txt");
        assert_eq!(c.route.as_ref().unwrap().class, RouteClass::Public);
        assert_eq!(c.matched_prefix.as_deref(), Some("/public/"));
        assert_eq!(c.remainder, "readme.txt");
    }

    #[test]
    fn classify_no_match_denies() {
        let table = RoutingTable::default_dao();
        let c = table.classify("/unknown/path");
        assert!(c.route.is_none());
    }

    #[test]
    fn classify_multisig() {
        let table = RoutingTable::default_dao();
        let c = table.classify("/treasury/budget.csv");
        assert_eq!(
            c.route.as_ref().unwrap().class,
            RouteClass::Multisig { threshold: 3 }
        );
        assert_eq!(c.remainder, "budget.csv");
    }

    #[test]
    fn commitment_is_deterministic() {
        let t1 = RoutingTable::default_dao();
        let t2 = RoutingTable::default_dao();
        assert_eq!(t1.commitment(), t2.commitment());
    }

    #[test]
    fn commitment_changes_on_mutation() {
        let t1 = RoutingTable::default_dao();
        let mut t2 = RoutingTable::default_dao();
        t2.add_route(RouteEntry {
            prefix: "/grants/".to_string(),
            class: RouteClass::MembersOnly,
            description: None,
        });
        assert_ne!(t1.commitment(), t2.commitment());
    }

    #[test]
    fn replace_all_bumps_version() {
        let mut table = RoutingTable::default_dao();
        assert_eq!(table.version, 0);

        table.replace_all(vec![RouteEntry {
            prefix: "/new/".to_string(),
            class: RouteClass::Public,
            description: None,
        }]);

        assert_eq!(table.version, 1);
        assert_eq!(table.len(), 1);
    }

    #[test]
    fn round_trip_through_dfa_userspace() {
        // Sanity: every default route classifies through the DFA and decodes
        // back to its original RouteClass.
        let table = RoutingTable::default_dao();
        for entry in default_dao_entries() {
            let probe = format!("{}probe.txt", entry.prefix);
            let c = table.classify(&probe);
            let got = c.route.as_ref().expect("default route must classify");
            assert_eq!(got.class, entry.class, "mismatch on {}", entry.prefix);
            assert_eq!(c.matched_prefix.as_deref(), Some(entry.prefix.as_str()));
        }
    }
}
