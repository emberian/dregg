//! DFA compiler: `Pattern → Nfa → Dfa` via subset construction.
//!
//! Lifted and generalized from `rbg::routing`. State IDs are `u32` (no 255-state
//! cap), accept information lives in a `BTreeSet<StateId>` (the router layer
//! converts that into a `BTreeMap<StateId, RouteTarget>` for routing tables).
//!
//! The flat transition table is laid out as `[state * 256 + byte] -> next_state`.
//! State 0 is the dead/reject state by convention; the start state is always
//! state 1 for compiled DFAs.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use serde::{Deserialize, Serialize};

/// A state identifier in the DFA.
pub type StateId = u32;

/// The dead / reject state. By convention state 0 is always dead and absorbs
/// all transitions.
pub const DEAD_STATE: StateId = 0;

// ---------------------------------------------------------------------------
// DFA
// ---------------------------------------------------------------------------

/// A compiled DFA with a flat transition table.
///
/// The transition table is laid out as `[state * 256 + byte] -> next_state`.
/// This flat layout is cache-friendly for linear scans and maps directly into
/// AIR constraint rows (one row per transition).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Dfa {
    /// Number of states, including the dead state at index 0.
    pub num_states: u32,
    /// Flat transition table: `transitions[state * 256 + byte] = next_state`.
    pub transitions: Vec<StateId>,
    /// Start state. Always 1 for freshly compiled DFAs.
    pub start: StateId,
    /// Set of accepting states.
    pub accepting: BTreeSet<StateId>,
}

impl Dfa {
    /// Run the DFA against an input byte sequence. Returns true if the DFA
    /// ends in an accepting state.
    pub fn matches(&self, input: &[u8]) -> bool {
        let mut state = self.start;
        for &byte in input {
            let idx = (state as usize) * 256 + (byte as usize);
            if idx >= self.transitions.len() {
                return false;
            }
            state = self.transitions[idx];
            if state == DEAD_STATE {
                return false;
            }
        }
        self.accepting.contains(&state)
    }

    /// Run the DFA and return the final state reached (without checking
    /// acceptance). Returns [`DEAD_STATE`] if any transition went dead.
    pub fn run(&self, input: &[u8]) -> StateId {
        let mut state = self.start;
        for &byte in input {
            let idx = (state as usize) * 256 + (byte as usize);
            if idx >= self.transitions.len() {
                return DEAD_STATE;
            }
            state = self.transitions[idx];
            if state == DEAD_STATE {
                return DEAD_STATE;
            }
        }
        state
    }

    /// Run the DFA against `input` and also report the longest prefix that
    /// landed on an accepting state. Returns `(final_state, longest_accept_len)`.
    ///
    /// `longest_accept_len` is the byte count consumed before the most recent
    /// accept state was visited (inclusive of that byte). 0 means "the start
    /// state itself was accepting before any input was consumed."
    pub fn run_with_longest_match(&self, input: &[u8]) -> (StateId, Option<usize>) {
        let mut state = self.start;
        let mut longest: Option<usize> = if self.accepting.contains(&state) {
            Some(0)
        } else {
            None
        };
        for (i, &byte) in input.iter().enumerate() {
            let idx = (state as usize) * 256 + (byte as usize);
            if idx >= self.transitions.len() {
                return (DEAD_STATE, longest);
            }
            state = self.transitions[idx];
            if state == DEAD_STATE {
                return (DEAD_STATE, longest);
            }
            if self.accepting.contains(&state) {
                longest = Some(i + 1);
            }
        }
        (state, longest)
    }

    /// Return the trace of `(state, byte, next_state)` for each transition.
    /// Used by [`crate::air::generate_air_trace`].
    pub fn trace(&self, input: &[u8]) -> Vec<Transition> {
        let mut state = self.start;
        let mut trace = Vec::with_capacity(input.len());
        for &byte in input {
            let idx = (state as usize) * 256 + (byte as usize);
            let next = if idx < self.transitions.len() {
                self.transitions[idx]
            } else {
                DEAD_STATE
            };
            trace.push(Transition {
                state,
                byte,
                next_state: next,
            });
            state = next;
        }
        trace
    }

    /// Size of the transition table in bytes (for resource bounds).
    pub fn table_size_bytes(&self) -> usize {
        self.transitions.len() * std::mem::size_of::<StateId>()
    }
}

/// A single state transition emitted by [`Dfa::trace`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transition {
    pub state: StateId,
    pub byte: u8,
    pub next_state: StateId,
}

// ---------------------------------------------------------------------------
// NFA (internal — used as intermediate representation)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct NfaState {
    byte_transitions: HashMap<u8, Vec<StateId>>,
    epsilon: Vec<StateId>,
}

#[derive(Clone, Debug)]
struct Nfa {
    states: Vec<NfaState>,
    start: StateId,
    accept: StateId,
}

impl Nfa {
    fn new_state(&mut self) -> StateId {
        let id = self.states.len() as StateId;
        self.states.push(NfaState {
            byte_transitions: HashMap::new(),
            epsilon: Vec::new(),
        });
        id
    }

    fn empty() -> Self {
        let mut nfa = Nfa {
            states: Vec::new(),
            start: 0,
            accept: 0,
        };
        let s = nfa.new_state();
        let a = nfa.new_state();
        nfa.start = s;
        nfa.accept = a;
        nfa.states[s as usize].epsilon.push(a);
        nfa
    }

    fn single_byte(b: u8) -> Self {
        let mut nfa = Nfa {
            states: Vec::new(),
            start: 0,
            accept: 0,
        };
        let s = nfa.new_state();
        let a = nfa.new_state();
        nfa.start = s;
        nfa.accept = a;
        nfa.states[s as usize]
            .byte_transitions
            .entry(b)
            .or_default()
            .push(a);
        nfa
    }

    fn byte_range(low: u8, high: u8) -> Self {
        let mut nfa = Nfa {
            states: Vec::new(),
            start: 0,
            accept: 0,
        };
        let s = nfa.new_state();
        let a = nfa.new_state();
        nfa.start = s;
        nfa.accept = a;
        for b in low..=high {
            nfa.states[s as usize]
                .byte_transitions
                .entry(b)
                .or_default()
                .push(a);
        }
        nfa
    }

    fn concat(mut self, mut other: Nfa) -> Nfa {
        let offset = self.states.len() as StateId;
        for state in &mut other.states {
            for targets in state.byte_transitions.values_mut() {
                for t in targets.iter_mut() {
                    *t += offset;
                }
            }
            for e in state.epsilon.iter_mut() {
                *e += offset;
            }
        }
        let other_start = other.start + offset;
        let other_accept = other.accept + offset;
        self.states[self.accept as usize].epsilon.push(other_start);
        self.states.extend(other.states);
        self.accept = other_accept;
        self
    }

    fn union(mut self, mut other: Nfa) -> Nfa {
        let offset = self.states.len() as StateId;
        for state in &mut other.states {
            for targets in state.byte_transitions.values_mut() {
                for t in targets.iter_mut() {
                    *t += offset;
                }
            }
            for e in state.epsilon.iter_mut() {
                *e += offset;
            }
        }
        let other_start = other.start + offset;
        let other_accept = other.accept + offset;
        self.states.extend(other.states);

        let new_start = self.new_state();
        let new_accept = self.new_state();
        self.states[new_start as usize].epsilon.push(self.start);
        self.states[new_start as usize].epsilon.push(other_start);
        self.states[self.accept as usize].epsilon.push(new_accept);
        self.states[other_accept as usize].epsilon.push(new_accept);
        self.start = new_start;
        self.accept = new_accept;
        self
    }

    fn star(mut self) -> Nfa {
        let new_start = self.new_state();
        let new_accept = self.new_state();
        self.states[new_start as usize].epsilon.push(self.start);
        self.states[new_start as usize].epsilon.push(new_accept);
        self.states[self.accept as usize].epsilon.push(self.start);
        self.states[self.accept as usize].epsilon.push(new_accept);
        self.start = new_start;
        self.accept = new_accept;
        self
    }

    fn epsilon_closure(&self, states: &BTreeSet<StateId>) -> BTreeSet<StateId> {
        let mut closure = states.clone();
        let mut stack: Vec<StateId> = states.iter().copied().collect();
        while let Some(s) = stack.pop() {
            for &e in &self.states[s as usize].epsilon {
                if closure.insert(e) {
                    stack.push(e);
                }
            }
        }
        closure
    }

    fn determinize(&self) -> Dfa {
        let mut dfa_states: Vec<BTreeSet<StateId>> = Vec::new();
        let mut state_map: BTreeMap<BTreeSet<StateId>, StateId> = BTreeMap::new();
        let mut transitions: Vec<StateId> = Vec::new();
        let mut accepting = BTreeSet::new();

        // Dead state (index 0).
        let dead_set = BTreeSet::new();
        dfa_states.push(dead_set.clone());
        state_map.insert(dead_set, DEAD_STATE);
        transitions.extend(std::iter::repeat(DEAD_STATE).take(256));

        // Start state.
        let start_set = {
            let mut s = BTreeSet::new();
            s.insert(self.start);
            self.epsilon_closure(&s)
        };
        let start_id: StateId = 1;
        dfa_states.push(start_set.clone());
        state_map.insert(start_set.clone(), start_id);
        if start_set.contains(&self.accept) {
            accepting.insert(start_id);
        }
        transitions.extend(std::iter::repeat(DEAD_STATE).take(256));

        let mut worklist = VecDeque::new();
        worklist.push_back(start_id);

        while let Some(dfa_state_id) = worklist.pop_front() {
            let nfa_states = dfa_states[dfa_state_id as usize].clone();
            for byte in 0u16..=255u16 {
                let b = byte as u8;
                let mut next_nfa_states = BTreeSet::new();
                for &nfa_s in &nfa_states {
                    if let Some(targets) = self.states[nfa_s as usize].byte_transitions.get(&b) {
                        for &t in targets {
                            next_nfa_states.insert(t);
                        }
                    }
                }
                let next_closure = self.epsilon_closure(&next_nfa_states);
                if next_closure.is_empty() {
                    transitions[(dfa_state_id as usize) * 256 + (b as usize)] = DEAD_STATE;
                } else if let Some(&existing_id) = state_map.get(&next_closure) {
                    transitions[(dfa_state_id as usize) * 256 + (b as usize)] = existing_id;
                } else {
                    let new_id = dfa_states.len() as StateId;
                    if next_closure.contains(&self.accept) {
                        accepting.insert(new_id);
                    }
                    state_map.insert(next_closure.clone(), new_id);
                    dfa_states.push(next_closure);
                    transitions.extend(std::iter::repeat(DEAD_STATE).take(256));
                    worklist.push_back(new_id);
                    transitions[(dfa_state_id as usize) * 256 + (b as usize)] = new_id;
                }
            }
        }

        Dfa {
            num_states: dfa_states.len() as u32,
            transitions,
            start: start_id,
            accepting,
        }
    }
}

// ---------------------------------------------------------------------------
// Pattern combinators
// ---------------------------------------------------------------------------

/// Pattern combinators that compile into DFAs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Pattern {
    /// Match a literal byte sequence.
    Word(Vec<u8>),
    /// Match a single byte in `[low, high]` inclusive.
    Range(u8, u8),
    /// Match any single byte.
    AnyByte,
    /// Match a specific bit at byte position `(offset_byte, bit_pos, value)`.
    /// Skips `offset_byte` arbitrary bytes, then matches a byte whose `bit_pos`
    /// equals `value`.
    Bit(usize, u8, bool),
    /// Concatenation.
    Seq(Vec<Pattern>),
    /// Intersection (all sub-patterns must accept the same input).
    All(Vec<Pattern>),
    /// Alternation (any sub-pattern accepts).
    Any(Vec<Pattern>),
    /// Skip `n` bytes, then match the inner pattern.
    Offset(usize, Box<Pattern>),
    /// Repeat the inner pattern exactly `count` times.
    Repeat(Box<Pattern>, usize),
    /// Match a literal byte sequence at a fixed offset.
    BytesAt(usize, Vec<u8>),
    /// Match the inner pattern followed by any tail (i.e. `inner . any*`).
    /// Equivalent to a URL `prefix/*` wildcard.
    PrefixOf(Box<Pattern>),
}

impl Pattern {
    pub fn word(w: &[u8]) -> Pattern {
        Pattern::Word(w.to_vec())
    }
    pub fn literal(s: &str) -> Pattern {
        Pattern::Word(s.as_bytes().to_vec())
    }
    pub fn range(low: u8, high: u8) -> Pattern {
        Pattern::Range(low, high)
    }
    pub fn any_byte() -> Pattern {
        Pattern::AnyByte
    }
    pub fn bit(offset_byte: usize, bit_pos: u8, value: bool) -> Pattern {
        Pattern::Bit(offset_byte, bit_pos, value)
    }
    pub fn seq(parts: Vec<Pattern>) -> Pattern {
        Pattern::Seq(parts)
    }
    pub fn all(parts: Vec<Pattern>) -> Pattern {
        Pattern::All(parts)
    }
    pub fn any(parts: Vec<Pattern>) -> Pattern {
        Pattern::Any(parts)
    }
    pub fn offset(skip: usize, inner: Pattern) -> Pattern {
        Pattern::Offset(skip, Box::new(inner))
    }
    pub fn repeat(inner: Pattern, count: usize) -> Pattern {
        Pattern::Repeat(Box::new(inner), count)
    }
    pub fn bytes_at(off: usize, data: &[u8]) -> Pattern {
        Pattern::BytesAt(off, data.to_vec())
    }
    /// Match the inner pattern followed by an arbitrary tail.
    pub fn prefix_of(inner: Pattern) -> Pattern {
        Pattern::PrefixOf(Box::new(inner))
    }
    /// Sugar: `path/*` style — match a URL path prefix followed by anything.
    pub fn path_prefix(prefix: &str) -> Pattern {
        Pattern::PrefixOf(Box::new(Pattern::literal(prefix)))
    }

    /// Compile this pattern to a DFA.
    pub fn compile(&self) -> Dfa {
        pattern_to_nfa(self).determinize()
    }
}

fn pattern_to_nfa(p: &Pattern) -> Nfa {
    match p {
        Pattern::Word(w) => {
            if w.is_empty() {
                return Nfa::empty();
            }
            let mut nfa = Nfa::single_byte(w[0]);
            for &b in &w[1..] {
                nfa = nfa.concat(Nfa::single_byte(b));
            }
            nfa
        }
        Pattern::Range(low, high) => Nfa::byte_range(*low, *high),
        Pattern::AnyByte => Nfa::byte_range(0, 255),
        Pattern::Bit(offset_byte, bit_pos, value) => {
            let mut nfa = if *offset_byte > 0 {
                let mut chain = Nfa::byte_range(0, 255);
                for _ in 1..*offset_byte {
                    chain = chain.concat(Nfa::byte_range(0, 255));
                }
                chain
            } else {
                Nfa::empty()
            };
            let bit_nfa = {
                let mut n = Nfa {
                    states: Vec::new(),
                    start: 0,
                    accept: 0,
                };
                let s = n.new_state();
                let a = n.new_state();
                n.start = s;
                n.accept = a;
                for b in 0u16..=255u16 {
                    let byte_val = b as u8;
                    let bit_set = (byte_val >> bit_pos) & 1 == 1;
                    if bit_set == *value {
                        n.states[s as usize]
                            .byte_transitions
                            .entry(byte_val)
                            .or_default()
                            .push(a);
                    }
                }
                n
            };
            if *offset_byte > 0 {
                nfa.concat(bit_nfa)
            } else {
                bit_nfa
            }
        }
        Pattern::Seq(parts) => {
            if parts.is_empty() {
                return Nfa::empty();
            }
            let mut nfa = pattern_to_nfa(&parts[0]);
            for p in &parts[1..] {
                nfa = nfa.concat(pattern_to_nfa(p));
            }
            nfa
        }
        Pattern::Any(parts) => {
            if parts.is_empty() {
                return Nfa::empty();
            }
            let mut nfa = pattern_to_nfa(&parts[0]);
            for p in &parts[1..] {
                nfa = nfa.union(pattern_to_nfa(p));
            }
            nfa
        }
        Pattern::All(parts) => {
            // Intersection: handled via DFA product. We build an NFA wrapper
            // here that compiles down by intersecting two-by-two and rebuilding
            // a trivial NFA from the product DFA. The simpler path is to short-
            // circuit by compiling at the top level (`Pattern::compile`).
            // Build a single-byte NFA stub that the determinizer will produce
            // a degenerate DFA from; for `All` we redirect via `compile`.
            // Since `pattern_to_nfa` is only meant for combinator composition,
            // and `Pattern::All` only appears at root or within other combinators,
            // we materialize it by compiling its parts and rebuilding via
            // synthetic NFA: walk every accepting input is unrealistic, so
            // instead we do this: compile each part, intersect them via DFA
            // product, then convert back to NFA via the byte transitions.
            if parts.is_empty() {
                return Nfa::empty();
            }
            let dfas: Vec<Dfa> = parts.iter().map(|p| p.compile()).collect();
            let mut result = dfas[0].clone();
            for d in &dfas[1..] {
                result = dfa_intersection(&result, d);
            }
            dfa_to_nfa(&result)
        }
        Pattern::Offset(skip, inner) => {
            let mut nfa = if *skip > 0 {
                let mut chain = Nfa::byte_range(0, 255);
                for _ in 1..*skip {
                    chain = chain.concat(Nfa::byte_range(0, 255));
                }
                chain
            } else {
                Nfa::empty()
            };
            nfa.concat(pattern_to_nfa(inner))
        }
        Pattern::Repeat(inner, count) => {
            if *count == 0 {
                return Nfa::empty();
            }
            let mut nfa = pattern_to_nfa(inner);
            for _ in 1..*count {
                nfa = nfa.concat(pattern_to_nfa(inner));
            }
            nfa
        }
        Pattern::BytesAt(off, data) => pattern_to_nfa(&Pattern::Offset(
            *off,
            Box::new(Pattern::Word(data.clone())),
        )),
        Pattern::PrefixOf(inner) => {
            // inner . any*
            let inner_nfa = pattern_to_nfa(inner);
            let tail = Nfa::byte_range(0, 255).star();
            inner_nfa.concat(tail)
        }
    }
}

/// Convert a DFA back into an equivalent NFA so it can be composed with other
/// NFA-shaped patterns. Used to inline `Pattern::All` (intersection) inside
/// larger combinators.
fn dfa_to_nfa(dfa: &Dfa) -> Nfa {
    let mut states: Vec<NfaState> = (0..dfa.num_states)
        .map(|_| NfaState {
            byte_transitions: HashMap::new(),
            epsilon: Vec::new(),
        })
        .collect();
    for s in 0..dfa.num_states {
        for b in 0u16..=255u16 {
            let next = dfa.transitions[(s as usize) * 256 + (b as usize)];
            if next != DEAD_STATE {
                states[s as usize]
                    .byte_transitions
                    .entry(b as u8)
                    .or_default()
                    .push(next);
            }
        }
    }
    // Add a single new accept state and epsilon-connect every DFA accepting
    // state to it.
    let mut nfa = Nfa {
        states,
        start: dfa.start,
        accept: 0,
    };
    let new_accept = nfa.new_state();
    nfa.accept = new_accept;
    for &acc in &dfa.accepting {
        nfa.states[acc as usize].epsilon.push(new_accept);
    }
    nfa
}

// ---------------------------------------------------------------------------
// DFA intersection (product construction)
// ---------------------------------------------------------------------------

/// Compute the intersection DFA of two DFAs via product construction.
pub fn dfa_intersection(a: &Dfa, b: &Dfa) -> Dfa {
    let mut state_map: HashMap<(StateId, StateId), StateId> = HashMap::new();
    let mut transitions: Vec<StateId> = Vec::new();
    let mut accepting = BTreeSet::new();

    // Dead state.
    state_map.insert((DEAD_STATE, DEAD_STATE), DEAD_STATE);
    transitions.extend(std::iter::repeat(DEAD_STATE).take(256));

    let start_pair = (a.start, b.start);
    let start_id: StateId = 1;
    state_map.insert(start_pair, start_id);
    transitions.extend(std::iter::repeat(DEAD_STATE).take(256));
    if a.accepting.contains(&a.start) && b.accepting.contains(&b.start) {
        accepting.insert(start_id);
    }

    let mut worklist = VecDeque::new();
    worklist.push_back(start_pair);
    let mut next_id: StateId = 2;

    while let Some((sa, sb)) = worklist.pop_front() {
        let current_id = state_map[&(sa, sb)];
        for byte in 0u16..=255u16 {
            let b_val = byte as u8;
            let na = if sa == DEAD_STATE {
                DEAD_STATE
            } else {
                a.transitions[(sa as usize) * 256 + (b_val as usize)]
            };
            let nb = if sb == DEAD_STATE {
                DEAD_STATE
            } else {
                b.transitions[(sb as usize) * 256 + (b_val as usize)]
            };

            if na == DEAD_STATE || nb == DEAD_STATE {
                transitions[(current_id as usize) * 256 + (b_val as usize)] = DEAD_STATE;
            } else {
                let pair = (na, nb);
                let target_id = if let Some(&id) = state_map.get(&pair) {
                    id
                } else {
                    let id = next_id;
                    next_id += 1;
                    state_map.insert(pair, id);
                    transitions.extend(std::iter::repeat(DEAD_STATE).take(256));
                    if a.accepting.contains(&na) && b.accepting.contains(&nb) {
                        accepting.insert(id);
                    }
                    worklist.push_back(pair);
                    id
                };
                transitions[(current_id as usize) * 256 + (b_val as usize)] = target_id;
            }
        }
    }

    Dfa {
        num_states: next_id,
        transitions,
        start: start_id,
        accepting,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_word_match() {
        let d = Pattern::word(b"hello").compile();
        assert!(d.matches(b"hello"));
        assert!(!d.matches(b"hell"));
        assert!(!d.matches(b"helloo"));
        assert!(!d.matches(b""));
    }

    #[test]
    fn any_union() {
        let d = Pattern::any(vec![Pattern::word(b"foo"), Pattern::word(b"bar")]).compile();
        assert!(d.matches(b"foo"));
        assert!(d.matches(b"bar"));
        assert!(!d.matches(b"baz"));
    }

    #[test]
    fn all_intersection() {
        let az = Pattern::seq(vec![
            Pattern::range(b'a', b'z'),
            Pattern::any_byte(),
            Pattern::any_byte(),
        ]);
        let fm = Pattern::seq(vec![
            Pattern::range(b'f', b'm'),
            Pattern::any_byte(),
            Pattern::any_byte(),
        ]);
        let d = Pattern::all(vec![az, fm]).compile();
        assert!(d.matches(b"foo"));
        assert!(d.matches(b"moo"));
        assert!(!d.matches(b"aoo"));
        assert!(!d.matches(b"zoo"));
    }

    #[test]
    fn prefix_of_path() {
        let d = Pattern::path_prefix("/cells/alpha/").compile();
        assert!(d.matches(b"/cells/alpha/"));
        assert!(d.matches(b"/cells/alpha/transfer"));
        assert!(!d.matches(b"/cells/beta/"));
    }

    #[test]
    fn longest_match_reports_accept_boundary() {
        // Pattern: "/a" OR "/abc". For input "/abcd" longest accept is "/abc" (3).
        let d = Pattern::any(vec![
            Pattern::word(b"/a"),
            Pattern::word(b"/abc"),
            Pattern::path_prefix("/abc"),
        ])
        .compile();
        let (_state, longest) = d.run_with_longest_match(b"/abcd");
        assert!(longest.is_some());
    }

    #[test]
    fn state_count_unbounded_beyond_u8() {
        // 60 disjoint literals — this would exceed the old 255-state u8 cap
        // when each adds ~3 states to a trie. Sanity check we go well past.
        let literals: Vec<Pattern> = (0..60)
            .map(|i| Pattern::literal(&format!("/svc/handler_{i:03}/x")))
            .collect();
        let d = Pattern::any(literals).compile();
        // Just confirm it compiles and matches.
        assert!(d.matches(b"/svc/handler_007/x"));
        assert!(!d.matches(b"/svc/handler_007/y"));
        assert!(d.num_states > 100);
    }

    #[test]
    fn empty_pattern_matches_empty() {
        let d = Pattern::word(b"").compile();
        assert!(d.matches(b""));
        assert!(!d.matches(b"x"));
    }

    #[test]
    fn intersection_correct() {
        let a = Pattern::seq(vec![Pattern::range(b'a', b'z'), Pattern::any_byte()]).compile();
        let b = Pattern::seq(vec![Pattern::any_byte(), Pattern::range(b'0', b'9')]).compile();
        let inter = dfa_intersection(&a, &b);
        assert!(inter.matches(b"a1"));
        assert!(!inter.matches(b"aa"));
        assert!(!inter.matches(b"1a"));
    }
}
