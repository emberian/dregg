//! Pattern-based filters used by gossip and capability-secure revocation.
//!
//! - [`TopicFilter`] — a wrapper around a compiled DFA that classifies the
//!   leading bytes of a message. Used by `intent::gossip` and by CapTP
//!   pre-/post-filters.
//! - [`FilterTree`] — a tree of DFA filters supporting revocation by
//!   marking a node inactive and recompiling the combined-intersection DFA.
//!   Lifted from `rbg::routing` with light changes.

use std::collections::BTreeSet;
use std::sync::Arc;

use crate::compiler::{DEAD_STATE, Dfa, Pattern, dfa_intersection};

// ---------------------------------------------------------------------------
// TopicFilter
// ---------------------------------------------------------------------------

/// A compiled topic filter for gossip dispatch.
///
/// The filter is generic over what "topic bytes" mean for a given crate —
/// `intent::gossip` uses a 32-byte topic id; CapTP could use a 4-byte
/// framing prefix; an HTTP layer could use a path. The filter doesn't
/// prescribe a layout; it just matches its compiled pattern against the
/// leading `n` bytes of any input.
#[derive(Clone, Debug)]
pub struct TopicFilter {
    pattern: Pattern,
    compiled: Arc<Dfa>,
}

impl TopicFilter {
    /// Compile a topic filter from an arbitrary pattern.
    pub fn from_pattern(pattern: Pattern) -> Self {
        let compiled = Arc::new(pattern.compile());
        TopicFilter { pattern, compiled }
    }

    /// Match against an exact topic id.
    pub fn exact(topic: &[u8]) -> Self {
        Self::from_pattern(Pattern::word(topic))
    }

    /// Match any topic in `[low, high]` for its first byte, with the remaining
    /// `tail_len` bytes free. Mirrors `rbg::routing::TopicFilter::topic_namespace`.
    pub fn first_byte_range(low: u8, high: u8, tail_len: usize) -> Self {
        let mut parts = vec![Pattern::range(low, high)];
        for _ in 0..tail_len {
            parts.push(Pattern::any_byte());
        }
        Self::from_pattern(Pattern::seq(parts))
    }

    /// Match a fixed prefix followed by anything.
    pub fn prefix(prefix: &[u8]) -> Self {
        Self::from_pattern(Pattern::prefix_of(Pattern::word(prefix)))
    }

    /// True iff the filter accepts the message.
    pub fn matches(&self, message: &[u8]) -> bool {
        self.compiled.matches(message)
    }

    /// Match the leading `len` bytes only.
    pub fn matches_prefix_bytes(&self, message: &[u8], len: usize) -> bool {
        if message.len() < len {
            return false;
        }
        self.compiled.matches(&message[..len])
    }

    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    pub fn dfa(&self) -> &Dfa {
        &self.compiled
    }
}

// ---------------------------------------------------------------------------
// FilterTree (capability-secure filter revocation)
// ---------------------------------------------------------------------------

/// A tree of DFA filters that compose by intersection along each root→leaf
/// path. Revoking a node marks it inactive (intersection identity → accept-all)
/// and a subsequent `compile_combined` rebuilds the active intersection.
pub struct FilterTree {
    nodes: Vec<FilterNode>,
    root: usize,
}

struct FilterNode {
    dfa: Arc<Dfa>,
    children: Vec<usize>,
    active: bool,
}

impl FilterTree {
    /// Construct a fresh tree whose root accepts everything.
    pub fn new() -> Self {
        FilterTree {
            nodes: vec![FilterNode {
                dfa: Arc::new(accept_all_dfa()),
                children: Vec::new(),
                active: true,
            }],
            root: 0,
        }
    }

    /// Add a child filter under `parent`. Returns the new node index.
    pub fn add_filter(&mut self, parent: usize, dfa: Dfa) -> usize {
        let idx = self.nodes.len();
        self.nodes.push(FilterNode {
            dfa: Arc::new(dfa),
            children: Vec::new(),
            active: true,
        });
        self.nodes[parent].children.push(idx);
        idx
    }

    /// Mark `node_idx` inactive.
    pub fn revoke(&mut self, node_idx: usize) {
        self.nodes[node_idx].active = false;
    }

    /// Compile the active intersection from the root.
    pub fn compile_combined(&self) -> Dfa {
        self.compile_subtree(self.root)
    }

    fn compile_subtree(&self, node_idx: usize) -> Dfa {
        let node = &self.nodes[node_idx];
        if !node.active {
            return accept_all_dfa();
        }
        let mut combined = (*node.dfa).clone();
        for &child_idx in &node.children {
            let child = self.compile_subtree(child_idx);
            combined = dfa_intersection(&combined, &child);
        }
        combined
    }
}

impl Default for FilterTree {
    fn default() -> Self {
        Self::new()
    }
}

fn accept_all_dfa() -> Dfa {
    // 2 states: dead (0) and accepting (1). State 1 loops on every byte.
    let mut t = vec![DEAD_STATE; 512];
    for i in 0..256 {
        t[256 + i] = 1;
    }
    let mut acc = BTreeSet::new();
    acc.insert(1);
    Dfa {
        num_states: 2,
        transitions: t,
        start: 1,
        accepting: acc,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_topic_filter() {
        let f = TopicFilter::exact(b"hello");
        assert!(f.matches(b"hello"));
        assert!(!f.matches(b"hellp"));
    }

    #[test]
    fn first_byte_range_filter() {
        let f = TopicFilter::first_byte_range(0x10, 0x1F, 3);
        assert!(f.matches(&[0x10, 0xAA, 0xBB, 0xCC]));
        assert!(f.matches(&[0x1F, 0x00, 0x00, 0x00]));
        assert!(!f.matches(&[0x20, 0x00, 0x00, 0x00]));
        assert!(!f.matches(&[0x10, 0xAA])); // too short
    }

    #[test]
    fn prefix_filter() {
        let f = TopicFilter::prefix(b"topic:auth:");
        assert!(f.matches(b"topic:auth:login"));
        assert!(!f.matches(b"topic:data:event"));
    }

    #[test]
    fn filter_tree_revocation_restores_acceptance() {
        let mut tree = FilterTree::new();
        let a = Pattern::seq(vec![
            Pattern::word(b"A"),
            Pattern::any_byte(),
            Pattern::any_byte(),
        ])
        .compile();
        let z = Pattern::seq(vec![
            Pattern::any_byte(),
            Pattern::any_byte(),
            Pattern::word(b"Z"),
        ])
        .compile();
        let _na = tree.add_filter(0, a);
        let nz = tree.add_filter(0, z);

        let combined = tree.compile_combined();
        assert!(combined.matches(b"AxZ"));
        assert!(!combined.matches(b"BxZ"));
        assert!(!combined.matches(b"AxY"));

        tree.revoke(nz);
        let after = tree.compile_combined();
        assert!(after.matches(b"AxZ"));
        assert!(after.matches(b"AxY"));
        assert!(!after.matches(b"BxZ"));
    }
}
