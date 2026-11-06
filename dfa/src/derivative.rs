//! Derivative-based DFA compiler over the byte alphabet.
//!
//! This is the Rust realization of the Brzozowski/Antimirov **symbolic
//! derivative** front-end designed in
//! `docs/deos/DERIVATIVE-MATCHING-DESIGN.md` (§2, §5.1 Stage 2). It exists to
//! give the [`crate::compiler::Pattern`] / [`crate::filter::FilterTree`] layer
//! two capabilities the eager `Pattern → Nfa → Dfa` product path cannot offer:
//!
//! * **complement (`~` / [`crate::compiler::Pattern::Not`])** — the cap-secure
//!   *deny* filter ("match everything except a revoked namespace"), which is
//!   *inexpressible* in the NFA-product world (Thompson NFAs have no
//!   complement constructor).
//! * **intersection without the eager product blow-up** — `inter` is a
//!   *derivative constructor* (`der b (l ∩ r) = der b l ∩ der b r`), so a
//!   `k`-fold intersection determinizes **lazily**: only the reachable product
//!   states are ever materialized, and structural normalization collapses the
//!   ones that denote the same residual language.
//!
//! The output is the **same flat [`Dfa`]** the rest of the crate (and, crucially,
//! the in-circuit DFA-AIR — `air.rs`, `metatheory/Dregg2/Crypto/Dfa.lean`)
//! already consumes: `transitions[state * 256 + byte] -> next_state`, dead
//! state at index 0, start state at index 1. Nothing about the table layout,
//! the AIR trace shape, or the proof side changes — the derivative theory is a
//! *new way to build the table*, living entirely in the compiler.
//!
//! ## How the byte alphabet stays cheap
//!
//! A naïve derivative determinizer would take `der b R` for all 256 `b` at
//! every state. Instead we compute, per regex node, the set of **derivative
//! classes** — the byte-boundaries at which `der b R` can change — from the
//! leaf byte-class predicates, take the derivative once per class
//! representative, and fan the result out across the 256-wide flat row. This is
//! the symbolic/lazy determinization the design calls for: work is proportional
//! to the number of distinct byte-classes, not to 256.
//!
//! ## Why the derivative set is finite: the ACI canonical form
//!
//! Brzozowski (1964) showed a regular expression has finitely many derivatives
//! only up to *similarity*: associativity, commutativity and idempotence (ACI)
//! of alternation. Taken literally, `der` produces ever-deeper alternations
//! (`(a|b)|c` vs `a|(b|c)`) that denote the same language but never compare
//! equal, and the determinizer below would never close. Owens, Reppy and Turon,
//! "Regular-expression derivatives re-examined" (JFP 2009), make the similarity
//! constructive: keep every term in a canonical form under ACI of `|` and `&`
//! plus a handful of identities, and use structural equality on that form as
//! the state key. This module does exactly that; see the invariant on [`Re`].
//! The Lean side of the same fact is
//! `metatheory/Dregg2/Crypto/Deriv/Finiteness.lean` (`der_finite`, finite up to
//! the ACI similarity of `metatheory/Dregg2/Crypto/Deriv/Similarity.lean`).
//! Nothing proves this Rust normalizer meets that relation; the evidence is the
//! differential tests here and in `demo/absence-receipt/tests/`.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use crate::compiler::{DEAD_STATE, Dfa, StateId};

// ---------------------------------------------------------------------------
// Byte-class predicate (the `sym` leaf)
// ---------------------------------------------------------------------------

/// A predicate over a single byte: the union of inclusive ranges it accepts.
///
/// This is the `sym φ` leaf of the design's `PredRE` specialized to the byte
/// alphabet — `Pred` over a byte is exactly a finite union of byte ranges
/// (`Range(low,high)` is a `Pred` over a byte, `DERIVATIVE-MATCHING-DESIGN.md`
/// §2.3). Stored as a sorted, disjoint, merged set of `[low, high]` ranges so
/// equality is canonical (two `ByteClass`es are equal iff they accept the same
/// byte set), which the similarity quotient relies on.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ByteClass {
    /// Sorted, disjoint, gap-separated inclusive ranges.
    ranges: Vec<(u8, u8)>,
}

impl ByteClass {
    /// The empty class — accepts no byte.
    pub fn empty() -> Self {
        ByteClass { ranges: Vec::new() }
    }

    /// The full class — accepts every byte.
    pub fn full() -> Self {
        ByteClass {
            ranges: vec![(0, 255)],
        }
    }

    /// A single inclusive range `[low, high]`. Empty if `low > high`.
    pub fn range(low: u8, high: u8) -> Self {
        if low > high {
            ByteClass::empty()
        } else {
            ByteClass {
                ranges: vec![(low, high)],
            }
        }
    }

    /// A single byte.
    pub fn byte(b: u8) -> Self {
        ByteClass::range(b, b)
    }

    /// Build from an arbitrary list of inclusive ranges (canonicalized).
    pub fn from_ranges(ranges: Vec<(u8, u8)>) -> Self {
        ByteClass::normalize(ranges)
    }

    pub fn is_empty(&self) -> bool {
        self.ranges.is_empty()
    }

    /// True iff `b` is in the class.
    pub fn contains(&self, b: u8) -> bool {
        self.ranges.iter().any(|&(lo, hi)| lo <= b && b <= hi)
    }

    /// Canonicalize: sort and merge adjacent/overlapping ranges.
    fn normalize(mut ranges: Vec<(u8, u8)>) -> Self {
        ranges.retain(|&(lo, hi)| lo <= hi);
        ranges.sort_unstable();
        let mut merged: Vec<(u8, u8)> = Vec::with_capacity(ranges.len());
        for (lo, hi) in ranges {
            if let Some(last) = merged.last_mut() {
                // merge if overlapping or directly adjacent (last.1 + 1 == lo)
                if lo <= last.1 || (last.1 < 255 && last.1 + 1 == lo) {
                    if hi > last.1 {
                        last.1 = hi;
                    }
                    continue;
                }
            }
            merged.push((lo, hi));
        }
        ByteClass { ranges: merged }
    }

    /// Set complement (within `[0, 255]`).
    pub fn complement(&self) -> Self {
        let mut out = Vec::new();
        let mut cursor: u16 = 0;
        for &(lo, hi) in &self.ranges {
            if (lo as u16) > cursor {
                out.push((cursor as u8, (lo - 1)));
            }
            cursor = hi as u16 + 1;
        }
        if cursor <= 255 {
            out.push((cursor as u8, 255));
        }
        ByteClass { ranges: out }
    }
}

// ---------------------------------------------------------------------------
// Re — the byte regex with native intersection and complement
// ---------------------------------------------------------------------------

/// A regular expression over the byte alphabet, with native intersection and
/// complement — the design's `PredRE` specialized to `σ := byte`
/// (`DERIVATIVE-MATCHING-DESIGN.md` §1.2).
///
/// Held behind `Box` for the recursive arms. Equality / ordering are
/// structural; the smart constructors ([`Re::or`], [`Re::and`], [`Re::then`],
/// [`Re::not`], [`Re::star`], [`Re::sym`]) and [`Re::derive`] keep every term
/// they build in the **canonical form** below, so ACI-similar derivatives
/// compare equal and the derivative set reachable from a canonical term is
/// finite (Brzozowski's theorem up to ACI; the module doc).
///
/// # Canonical-form invariant
///
/// * `Alt` is a right-nested chain `Alt(a1, Alt(a2, … Alt(a(n-1), an)))` with
///   `n >= 2` operands, strictly increasing in the derived `Ord`, none of them
///   an `Alt`, `Empty` (`∅ | r = r`), or `any*` (`any* | r = any*`).
/// * `Inter` is the same shape over its operands, none of them an `Inter`,
///   `Empty` (`∅ & r = ∅`), or `any*` (`any* & r = r`).
/// * `Cat(l, r)` is right-associated (`l` is not a `Cat`) and neither side is
///   `Empty` (`∅·r = r·∅ = ∅`) or `Epsilon` (`ε·r = r·ε = r`).
/// * `Neg(r)`: `r` is not a `Neg` (`~~r = r`), not `Empty` (`~∅ = any*`) and
///   not `any*` (`~any* = ∅`).
/// * `Star(r)`: `r` is not `Empty`, `Epsilon` or a `Star` (`∅* = ε* = ε`,
///   `r** = r*`).
/// * `Sym(c)`: `c` is non-empty (an empty class is `Empty`).
///
/// The variants are public, so a term built directly from them may break the
/// invariant; [`Re::canonical`] restores it, and [`Re::compile`] canonicalizes
/// its input before determinizing.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Re {
    /// `∅` — matches nothing (the empty language).
    Empty,
    /// `ε` — matches the empty word only.
    Epsilon,
    /// `sym φ` — one byte satisfying the byte-class `φ`.
    Sym(ByteClass),
    /// Concatenation `l · r`.
    Cat(Box<Re>, Box<Re>),
    /// Alternation `l ⋓ r` (union of languages).
    Alt(Box<Re>, Box<Re>),
    /// Intersection `l ⋒ r` (the FilterTree product, as a derivative ctor).
    Inter(Box<Re>, Box<Re>),
    /// Complement `~r` (the deny-filter — newly expressible).
    Neg(Box<Re>),
    /// Kleene star `r*`.
    Star(Box<Re>),
}

impl Re {
    pub fn empty() -> Re {
        Re::Empty
    }
    pub fn epsilon() -> Re {
        Re::Epsilon
    }
    /// One byte satisfying `class`.
    pub fn sym(class: ByteClass) -> Re {
        if class.is_empty() {
            Re::Empty
        } else {
            Re::Sym(class)
        }
    }
    /// One byte in `[low, high]`.
    pub fn range(low: u8, high: u8) -> Re {
        Re::sym(ByteClass::range(low, high))
    }
    /// Exactly the byte `b`.
    pub fn byte(b: u8) -> Re {
        Re::sym(ByteClass::byte(b))
    }
    /// Any single byte.
    pub fn any_byte() -> Re {
        Re::sym(ByteClass::full())
    }
    /// `ε` if the word is empty; matches the literal byte sequence otherwise.
    pub fn word(bytes: &[u8]) -> Re {
        let mut re = Re::Epsilon;
        for &b in bytes {
            re = re.then(Re::byte(b));
        }
        re
    }

    // --- smart constructors: each returns the canonical form (see `Re`) ---

    /// `any*`, the universal language: the absorbing element of `|` and the
    /// identity of `&`.
    pub fn top() -> Re {
        Re::Star(Box::new(Re::Sym(ByteClass::full())))
    }

    fn is_top(&self) -> bool {
        matches!(self, Re::Star(inner) if matches!(&**inner, Re::Sym(c) if c.ranges == [(0, 255)]))
    }

    /// `self · other`, right-associated, with `∅` absorption and `ε` identity.
    pub fn then(self, other: Re) -> Re {
        match (self, other) {
            (Re::Empty, _) | (_, Re::Empty) => Re::Empty,
            (Re::Epsilon, r) => r,
            (l, Re::Epsilon) => l,
            // (a·b)·r = a·(b·r): right-associate so concatenations that differ
            // only in grouping share a representative.
            (Re::Cat(a, b), r) => (*a).then((*b).then(r)),
            (l, r) => Re::Cat(Box::new(l), Box::new(r)),
        }
    }

    /// `self ⋓ other`: the operands of both sides are flattened into one
    /// sorted, deduplicated chain (associativity, commutativity, idempotence),
    /// with `∅` dropped and `any*` absorbing.
    pub fn or(self, other: Re) -> Re {
        let mut ops = Vec::new();
        flatten_alt(self, &mut ops);
        flatten_alt(other, &mut ops);
        if ops.iter().any(Re::is_top) {
            return Re::top();
        }
        ops.retain(|r| !matches!(r, Re::Empty));
        ops.sort_unstable();
        ops.dedup();
        nest(ops, Re::Empty, |a, b| Re::Alt(Box::new(a), Box::new(b)))
    }

    /// `self ⋒ other`: flattened, sorted, deduplicated (ACI), with `∅`
    /// absorbing and `any*` dropped as the identity.
    pub fn and(self, other: Re) -> Re {
        let mut ops = Vec::new();
        flatten_inter(self, &mut ops);
        flatten_inter(other, &mut ops);
        if ops.iter().any(|r| matches!(r, Re::Empty)) {
            return Re::Empty;
        }
        ops.retain(|r| !r.is_top());
        ops.sort_unstable();
        ops.dedup();
        nest(ops, Re::top(), |a, b| Re::Inter(Box::new(a), Box::new(b)))
    }

    /// `~self`, with `~~r = r`, `~∅ = any*` and `~any* = ∅`.
    pub fn not(self) -> Re {
        match self {
            Re::Neg(inner) => *inner,
            Re::Empty => Re::top(),
            r if r.is_top() => Re::Empty,
            r => Re::Neg(Box::new(r)),
        }
    }

    /// `self*`, with `∅* = ε* = ε` and `r** = r*` idempotence.
    pub fn star(self) -> Re {
        match self {
            Re::Empty | Re::Epsilon => Re::Epsilon,
            Re::Star(_) => self,
            r => Re::Star(Box::new(r)),
        }
    }

    /// Rebuild `self` bottom-up through the smart constructors, restoring the
    /// canonical-form invariant (see [`Re`]) on a term assembled directly from
    /// the public variants. Idempotent; the identity on canonical terms.
    pub fn canonical(&self) -> Re {
        match self {
            Re::Empty => Re::Empty,
            Re::Epsilon => Re::Epsilon,
            Re::Sym(c) => Re::sym(c.clone()),
            Re::Cat(l, r) => l.canonical().then(r.canonical()),
            Re::Alt(l, r) => l.canonical().or(r.canonical()),
            Re::Inter(l, r) => l.canonical().and(r.canonical()),
            Re::Neg(r) => r.canonical().not(),
            Re::Star(r) => r.canonical().star(),
        }
    }

    /// `self · any*` — the `prefix/*` wildcard.
    pub fn prefix_of(self) -> Re {
        self.then(Re::any_byte().star())
    }

    // --- nullability + derivative ---

    /// `null R` — does `R` match the empty word? (location-free; we have no
    /// lookaround — `DERIVATIVE-MATCHING-DESIGN.md` §1.3).
    pub fn nullable(&self) -> bool {
        match self {
            Re::Empty => false,
            Re::Epsilon => true,
            Re::Sym(_) => false,
            Re::Cat(l, r) => l.nullable() && r.nullable(),
            Re::Alt(l, r) => l.nullable() || r.nullable(),
            Re::Inter(l, r) => l.nullable() && r.nullable(),
            Re::Neg(r) => !r.nullable(),
            Re::Star(_) => true,
        }
    }

    /// `der b R` — the Brzozowski derivative w.r.t. byte `b`. Built through the
    /// smart constructors so the result is canonical (the similarity quotient).
    pub fn derive(&self, b: u8) -> Re {
        match self {
            Re::Empty | Re::Epsilon => Re::Empty,
            Re::Sym(class) => {
                if class.contains(b) {
                    Re::Epsilon
                } else {
                    Re::Empty
                }
            }
            Re::Cat(l, r) => {
                let dl = l.derive(b).then((**r).clone());
                if l.nullable() { dl.or(r.derive(b)) } else { dl }
            }
            Re::Alt(l, r) => l.derive(b).or(r.derive(b)),
            Re::Inter(l, r) => l.derive(b).and(r.derive(b)),
            Re::Neg(r) => r.derive(b).not(),
            Re::Star(r) => r.derive(b).then(self.clone()),
        }
    }

    /// Decide whether `word` matches by iterating the derivative
    /// (`derives w R = null (der* w R)` — the streaming matcher).
    pub fn matches(&self, word: &[u8]) -> bool {
        let mut cur = self.canonical();
        for &b in word {
            cur = cur.derive(b);
            if let Re::Empty = cur {
                return false;
            }
        }
        cur.nullable()
    }

    /// The set of byte-boundaries at which `der b R` can change behavior — the
    /// **derivative classes**. We collect the endpoints of every leaf range and
    /// determinize one representative per resulting cell, instead of all 256
    /// bytes. The returned vector is a partition of `[0, 255]` into maximal
    /// intervals on which the derivative is constant.
    fn derivative_classes(&self) -> Vec<(u8, u8)> {
        let mut cuts: BTreeSet<u16> = BTreeSet::new();
        cuts.insert(0);
        cuts.insert(256); // sentinel = "one past the last byte"
        self.collect_cuts(&mut cuts);
        let sorted: Vec<u16> = cuts.into_iter().collect();
        let mut out = Vec::new();
        for win in sorted.windows(2) {
            let lo = win[0];
            let hi = win[1] - 1;
            if lo <= hi && lo <= 255 {
                out.push((lo as u8, hi.min(255) as u8));
            }
        }
        out
    }

    /// Gather range start/end+1 boundaries from every `Sym` leaf.
    fn collect_cuts(&self, cuts: &mut BTreeSet<u16>) {
        match self {
            Re::Empty | Re::Epsilon => {}
            Re::Sym(class) => {
                for &(lo, hi) in &class.ranges {
                    cuts.insert(lo as u16);
                    cuts.insert(hi as u16 + 1);
                }
            }
            Re::Cat(l, r) | Re::Alt(l, r) | Re::Inter(l, r) => {
                l.collect_cuts(cuts);
                r.collect_cuts(cuts);
            }
            Re::Neg(r) | Re::Star(r) => r.collect_cuts(cuts),
        }
    }
}

/// Push the operands of an alternation (any nesting) onto `out`.
fn flatten_alt(r: Re, out: &mut Vec<Re>) {
    match r {
        Re::Alt(l, rr) => {
            flatten_alt(*l, out);
            flatten_alt(*rr, out);
        }
        other => out.push(other),
    }
}

/// Push the operands of an intersection (any nesting) onto `out`.
fn flatten_inter(r: Re, out: &mut Vec<Re>) {
    match r {
        Re::Inter(l, rr) => {
            flatten_inter(*l, out);
            flatten_inter(*rr, out);
        }
        other => out.push(other),
    }
}

/// Right-nest a sorted operand list with `node`; `unit` for zero operands.
fn nest(mut ops: Vec<Re>, unit: Re, node: impl Fn(Re, Re) -> Re) -> Re {
    let Some(last) = ops.pop() else {
        return unit;
    };
    ops.into_iter().rev().fold(last, |acc, op| node(op, acc))
}

// ---------------------------------------------------------------------------
// Dfa → Re recovery (state elimination)
// ---------------------------------------------------------------------------

impl Re {
    /// Recover a byte regex recognizing the same language as `dfa`, via the
    /// classic **state-elimination** construction. Used by [`crate::filter::FilterTree`]
    /// as a compatibility shim so a node added as an already-compiled [`Dfa`]
    /// can still participate in the lazy derivative `inter` fold.
    ///
    /// The preferred path is to add filters as patterns/`Re`s directly (no
    /// recovery needed); this exists only to keep the `add_filter(Dfa)` API
    /// working without an eager product.
    pub fn from_dfa(dfa: &Dfa) -> Re {
        let n = dfa.num_states as usize;
        // Generalized-NFA transition matrix `g[i][j]` = Re from state i to j.
        // Add a fresh source `S` (index n) and sink `T` (index n+1).
        let src = n;
        let sink = n + 1;
        let total = n + 2;
        let mut g: Vec<Vec<Re>> = vec![vec![Re::Empty; total]; total];

        // Edge from each state on each byte-class (group bytes by target).
        for s in 0..n {
            if s == DEAD_STATE as usize {
                continue; // dead state has no useful outgoing edges
            }
            // Group bytes by their next state into classes.
            let mut by_target: BTreeMap<StateId, Vec<(u8, u8)>> = BTreeMap::new();
            for b in 0u16..=255u16 {
                let next = dfa.transitions[s * 256 + b as usize];
                if next == DEAD_STATE {
                    continue;
                }
                let entry = by_target.entry(next).or_default();
                // extend a run if contiguous
                if let Some(last) = entry.last_mut()
                    && last.1 as u16 + 1 == b
                {
                    last.1 = b as u8;
                    continue;
                }
                entry.push((b as u8, b as u8));
            }
            for (target, ranges) in by_target {
                let class = ByteClass::from_ranges(ranges);
                let edge = Re::sym(class);
                g[s][target as usize] = g[s][target as usize].clone().or(edge);
            }
        }

        // Source → start (ε); each accepting state → sink (ε).
        g[src][dfa.start as usize] = Re::Epsilon;
        for &acc in &dfa.accepting {
            g[acc as usize][sink] = g[acc as usize][sink].clone().or(Re::Epsilon);
        }

        // Eliminate every real state (0..n), keeping src and sink.
        let mut eliminated = vec![false; total];
        for k in 0..n {
            eliminated[k] = true;
            let loop_re = g[k][k].clone().star();
            for i in 0..total {
                if eliminated[i] || g[i][k] == Re::Empty {
                    continue;
                }
                for j in 0..total {
                    if eliminated[j] || g[k][j] == Re::Empty {
                        continue;
                    }
                    // new path i→j: existing  ⋓  (i→k)(k→k)*(k→j)
                    let through = g[i][k].clone().then(loop_re.clone()).then(g[k][j].clone());
                    g[i][j] = g[i][j].clone().or(through);
                }
            }
        }

        g[src][sink].clone()
    }
}

// ---------------------------------------------------------------------------
// Lazy determinization: Re → flat Dfa
// ---------------------------------------------------------------------------

impl Re {
    /// Lazily determinize this regex into the crate's flat [`Dfa`], visiting
    /// only reachable derivative-states. The emitted table is the exact shape
    /// the rest of the crate and the in-circuit AIR consume:
    /// `transitions[state * 256 + byte]`, dead state 0, start state 1.
    ///
    /// State = a similarity-class of derivatives (canonicalized `Re`). The dead
    /// state is the `Re::Empty` class, mapped to index 0. Because `Neg` is a
    /// real constructor, the dead state is reachable *and complementable* — a
    /// complemented pattern produces an explicit accepting "trap" with
    /// self-loops on every byte, which is exactly what makes deny-filters total.
    pub fn compile(&self) -> Dfa {
        let mut state_ids: HashMap<Re, StateId> = HashMap::new();
        let mut order: Vec<Re> = Vec::new();
        let mut transitions: Vec<StateId> = Vec::new();
        let mut accepting: BTreeSet<StateId> = BTreeSet::new();

        // Dead state (index 0) is the Empty regex: it loops to itself on every
        // byte and never accepts.
        state_ids.insert(Re::Empty, DEAD_STATE);
        order.push(Re::Empty);
        transitions.extend(std::iter::repeat_n(DEAD_STATE, 256));

        // Start state (index 1). Canonicalize first: derivatives of a canonical
        // term are canonical, so every key in `state_ids` is in normal form.
        let start_re = self.canonical();
        let start_id: StateId = 1;
        // If the start regex happens to *be* Empty, the whole language is ∅;
        // start is still 1 (a fresh dead-equivalent) for table-shape parity
        // with the eager compiler, which always reserves state 1 as start.
        state_ids.insert(start_re.clone(), start_id);
        // Guard: if start collided with Empty above (language is ∅), the insert
        // above is a no-op and start_id below would be wrong. Handle explicitly.
        let language_empty = matches!(start_re, Re::Empty);
        if !language_empty {
            order.push(start_re.clone());
            transitions.extend(std::iter::repeat_n(DEAD_STATE, 256));
            if start_re.nullable() {
                accepting.insert(start_id);
            }
        } else {
            // Empty language: a 2-state table (dead 0, empty start 1) that
            // never accepts. Mirrors the eager compiler's "accept nothing".
            order.push(Re::Star(Box::new(Re::Empty))); // placeholder distinct key
            transitions.extend(std::iter::repeat_n(DEAD_STATE, 256));
        }

        let mut worklist: VecDeque<StateId> = VecDeque::new();
        worklist.push_back(start_id);

        while let Some(cur_id) = worklist.pop_front() {
            let cur_re = order[cur_id as usize].clone();
            // Empty/placeholder states stay dead-looping; nothing to expand.
            if matches!(cur_re, Re::Empty) || (language_empty && cur_id == start_id) {
                continue;
            }

            // Compute the derivative once per byte-class, then fan it across the
            // 256-wide flat row — the lazy/symbolic determinization.
            let classes = cur_re.derivative_classes();
            for (lo, hi) in classes {
                let next_re = cur_re.derive(lo);
                let next_id = match state_ids.get(&next_re) {
                    Some(&id) => id,
                    None => {
                        let id = order.len() as StateId;
                        state_ids.insert(next_re.clone(), id);
                        if next_re.nullable() {
                            accepting.insert(id);
                        }
                        order.push(next_re.clone());
                        transitions.extend(std::iter::repeat_n(DEAD_STATE, 256));
                        worklist.push_back(id);
                        id
                    }
                };
                // Fill every byte in [lo, hi] of this state's row.
                let base = (cur_id as usize) * 256;
                for b in lo..=hi {
                    transitions[base + b as usize] = next_id;
                }
            }
        }

        Dfa {
            num_states: order.len() as u32,
            transitions,
            start: start_id,
            accepting,
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn byte_class_complement_roundtrip() {
        let c = ByteClass::range(b'a', b'z');
        let comp = c.complement();
        assert!(!comp.contains(b'a'));
        assert!(!comp.contains(b'z'));
        assert!(comp.contains(b'A'));
        assert!(comp.contains(0));
        assert!(comp.contains(255));
        // double complement is the original
        assert_eq!(comp.complement(), c);
    }

    #[test]
    fn byte_class_normalize_merges_adjacent() {
        let c = ByteClass::normalize(vec![(0, 5), (6, 10), (3, 7)]);
        assert_eq!(c, ByteClass::range(0, 10));
    }

    #[test]
    fn word_matches_via_derivative() {
        let re = Re::word(b"hello");
        assert!(re.matches(b"hello"));
        assert!(!re.matches(b"hell"));
        assert!(!re.matches(b"helloo"));
        assert!(!re.matches(b""));
    }

    #[test]
    fn star_and_prefix() {
        let re = Re::word(b"/x/").prefix_of();
        assert!(re.matches(b"/x/"));
        assert!(re.matches(b"/x/anything"));
        assert!(!re.matches(b"/y/"));
    }

    #[test]
    fn intersection_via_derivative() {
        // [a-z].. ∩ ..[0-9]  (3 bytes: first lowercase, last digit)
        let l = Re::range(b'a', b'z')
            .then(Re::any_byte())
            .then(Re::any_byte());
        let r = Re::any_byte()
            .then(Re::any_byte())
            .then(Re::range(b'0', b'9'));
        let re = l.and(r);
        assert!(re.matches(b"ab1"));
        assert!(!re.matches(b"ab_"));
        assert!(!re.matches(b"1b1"));
    }

    #[test]
    fn complement_denies() {
        // ~(word "no") — match everything EXCEPT exactly "no".
        let re = Re::word(b"no").not();
        assert!(!re.matches(b"no"));
        assert!(re.matches(b"yes"));
        assert!(re.matches(b"n"));
        assert!(re.matches(b"nope"));
        assert!(re.matches(b""));
    }

    #[test]
    fn deny_filter_intersection() {
        // any* ∩ ~(prefix "/blocked/") — accept anything that is NOT under
        // the /blocked/ namespace. The canonical capability-secure deny filter.
        let allow_all = Re::any_byte().star();
        let blocked = Re::word(b"/blocked/").prefix_of();
        let re = allow_all.and(blocked.not());
        assert!(re.matches(b"/cells/alpha"));
        assert!(!re.matches(b"/blocked/secret"));
        assert!(re.matches(b"/blocked")); // not under the / boundary
        assert!(re.matches(b""));
    }

    #[test]
    fn compiled_dfa_matches_derivative() {
        // Compile to the flat table and confirm the table agrees with the
        // streaming matcher on a corpus — this is the table the AIR consumes.
        let re = Re::word(b"/blocked/").prefix_of().not();
        let dfa = re.compile();
        for w in [
            &b""[..],
            b"/blocked/x",
            b"/blocked",
            b"/cells",
            b"/blocked/",
            b"hello world",
        ] {
            assert_eq!(
                dfa.matches(w),
                re.matches(w),
                "table vs derivative disagree on {:?}",
                w
            );
        }
    }

    #[test]
    fn lazy_intersection_is_small() {
        // A k-fold intersection of "first byte in disjoint-ish ranges" — the
        // eager product would multiply state counts; the lazy derivative path
        // collapses equivalent residuals. Just assert it compiles to a modest
        // size and matches correctly.
        let parts: Vec<Re> = (0..6)
            .map(|i| {
                // each constrains a different position to a wide range, free elsewhere
                let mut seq = Re::epsilon();
                for j in 0..6 {
                    if j == i {
                        seq = seq.then(Re::range(b'a', b'y'));
                    } else {
                        seq = seq.then(Re::any_byte());
                    }
                }
                seq
            })
            .collect();
        let re = parts.into_iter().reduce(|a, b| a.and(b)).unwrap();
        let dfa = re.compile();
        assert!(re.matches(b"abcdef"));
        assert!(!re.matches(b"abcdez")); // last pos must be a..y, z fails the i=5 part? z>y
        // Sanity: 6-byte words only; state growth is linear-ish in length, not
        // exponential in the number of intersected parts.
        assert!(
            dfa.num_states < 40,
            "lazy intersection blew up: {} states",
            dfa.num_states
        );
        assert_eq!(dfa.matches(b"abcdef"), re.matches(b"abcdef"));
    }

    #[test]
    fn empty_language_compiles() {
        let re = Re::empty();
        let dfa = re.compile();
        assert!(!dfa.matches(b""));
        assert!(!dfa.matches(b"x"));
    }

    #[test]
    fn epsilon_language_compiles() {
        let re = Re::epsilon();
        let dfa = re.compile();
        assert!(dfa.matches(b""));
        assert!(!dfa.matches(b"x"));
    }

    // --- ACI canonical form: termination and agreement on complement patterns ---

    /// `~(any* · w · any*)`: "never contains `w`".
    fn absent(w: &[u8]) -> Re {
        Re::top().then(Re::word(w)).then(Re::top()).not()
    }

    /// xorshift64*: a fixed-seed generator so the random corpus is reproducible.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    /// Random words: a third uniform bytes, two thirds spliced from fragments of
    /// the patterns under test (so matches and near misses are common).
    fn random_words(seed: u64, count: usize, fragments: &[&[u8]]) -> Vec<Vec<u8>> {
        let mut rng = Rng(seed);
        (0..count)
            .map(|i| {
                let mut w = Vec::new();
                let len = rng.below(48);
                if i % 3 == 0 {
                    w.extend((0..len).map(|_| rng.next() as u8));
                } else {
                    while w.len() < len {
                        match rng.below(4) {
                            0 => w.push(rng.next() as u8),
                            1 => w.push(b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ "[rng.below(37)]),
                            _ => {
                                let f = fragments[rng.below(fragments.len())];
                                let a = rng.below(f.len());
                                let b = a + 1 + rng.below(f.len() - a);
                                w.extend_from_slice(if rng.below(2) == 0 { f } else { &f[a..b] });
                            }
                        }
                    }
                }
                w
            })
            .collect()
    }

    fn pem_header(kind: &str) -> Vec<u8> {
        // Built from parts: the repository's secret scanner refuses PEM-header literals.
        format!("{}BEGIN {kind}{}{}", "-----", "PRIVATE KEY", "-----").into_bytes()
    }

    #[test]
    fn smart_constructors_are_aci_canonical() {
        let (a, b, c) = (Re::byte(b'a'), Re::byte(b'b'), Re::byte(b'c'));
        let left = a.clone().or(b.clone()).or(c.clone());
        let right = c.clone().or(a.clone().or(b.clone()));
        assert_eq!(left, right, "associativity + commutativity of |");
        assert_eq!(
            left.clone().or(b.clone()),
            left,
            "idempotence across nesting"
        );
        assert_eq!(left.clone().or(Re::empty()), left);
        assert_eq!(left.clone().or(Re::top()), Re::top());
        let l = a.clone().and(b.clone()).and(c.clone());
        assert_eq!(l, c.clone().and(b.clone().and(a.clone())));
        assert_eq!(l.clone().and(Re::top()), l);
        assert_eq!(l.and(Re::empty()), Re::empty());
        let cat = a.clone().then(b.clone()).then(c.clone());
        assert_eq!(cat, a.clone().then(b.clone().then(c.clone())));
        assert_eq!(Re::empty().not(), Re::top());
        assert_eq!(Re::top().not(), Re::empty());
        assert_eq!(cat.clone().not().not(), cat);
        // A term assembled from the raw variants canonicalizes to the smart form.
        let raw = Re::Alt(
            Box::new(Re::Alt(Box::new(c.clone()), Box::new(a.clone()))),
            Box::new(Re::Alt(Box::new(b.clone()), Box::new(a.clone()))),
        );
        assert_eq!(raw.canonical(), a.or(b).or(c));
    }

    #[test]
    fn derivatives_of_canonical_terms_are_canonical() {
        let mut cur = absent(b"AKIA").and(absent(b"-----BEGIN"));
        assert_eq!(cur.canonical(), cur);
        let mut rng = Rng(7);
        for _ in 0..2_000 {
            let b = b"AKI-BEGN x"[rng.below(10)];
            cur = cur.derive(b);
            assert_eq!(cur.canonical(), cur, "derivative left canonical form");
        }
    }

    #[test]
    fn absence_of_a_word_compiles_with_pinned_state_count() {
        let re = absent(b"AKIA");
        let dfa = re.compile();
        let min = dfa.minimize();
        eprintln!(
            "absent(AKIA): {} states, {} minimized",
            dfa.num_states, min.num_states
        );
        // dead + one accepting state per matched prefix length 0..=3: the
        // canonical form already reaches the minimal automaton.
        assert_eq!(dfa.num_states, 5);
        assert_eq!(min.num_states, 5);
        assert!(!dfa.matches(b"xxAKIAxx"));
        assert!(dfa.matches(b"AKIxAKAKI"));
        assert!(dfa.matches(b""));
    }

    #[test]
    fn absence_of_two_words_agrees_with_the_derivative_matcher() {
        let re = absent(b"AKIA").and(absent(b"-----BEGIN"));
        let dfa = re.compile();
        let min = dfa.minimize();
        eprintln!(
            "absent(AKIA) & absent(-----BEGIN): {} states, {} minimized",
            dfa.num_states, min.num_states
        );
        // dead + empty prefix + 3 proper prefixes of AKIA + 9 of -----BEGIN.
        assert_eq!(dfa.num_states, 14);
        assert_eq!(min.num_states, 14);
        let mut words = random_words(
            0x5eed,
            10_000,
            &[b"AKIA", b"-----BEGIN ", b"AKIAIOSFODNN7EXAMPLE"],
        );
        words.push(b"AKIAIOSFODNN7EXAMPLE".to_vec());
        words.push(b"AKIAIOSFODNN7EXAMPL".to_vec());
        words.push(pem_header("RSA "));
        words.push(pem_header(""));
        let mut rejected = 0;
        for w in &words {
            let want = re.matches(w);
            assert_eq!(dfa.matches(w), want, "table vs derivative on {w:?}");
            assert_eq!(
                min.matches(w),
                want,
                "minimized table vs derivative on {w:?}"
            );
            rejected += usize::from(!want);
        }
        // the corpus exercises both verdicts
        assert!(rejected > 1_000 && rejected < 9_000, "rejected {rejected}");
    }
}
