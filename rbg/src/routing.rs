//! DFA-based message routing with provable resource bounds.
//!
//! Adapted from the Robigalia capability-secure OS routing design for pyana's
//! distributed ZK credential federation.
//!
//! # Design
//!
//! Messages are classified by DFA (deterministic finite automaton) operating on
//! raw message bytes. This gives us:
//! - **Constant space**: DFA state is a single integer
//! - **Linear time**: one transition per input byte
//! - **Composability**: DFAs close under intersection, union, complement
//! - **Provability**: bounded state transitions encode directly as AIR constraints
//!
//! # Capability-secure routing
//!
//! A `PacketSource` can be split by a `Classifier` (compiled DFA) into two
//! sub-sources. Each sub-source is a new capability reference. Revocation =
//! remove a filter from the tree, recompile, atomically swap the transition table.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::sync::Arc;

// ---------------------------------------------------------------------------
// DFA core types
// ---------------------------------------------------------------------------

/// A state in the DFA. States are numbered 0..N-1.
pub type StateId = u32;

/// The dead/reject state. By convention state 0 is always the dead state.
pub const DEAD_STATE: StateId = 0;

/// A compiled DFA with a flat transition table.
///
/// The transition table is laid out as `[state * 256 + byte] -> next_state`.
/// This flat layout is ideal for:
/// - Cache-friendly linear scans (wire protocol dispatch)
/// - Circuit encoding (each row = one state transition)
#[derive(Clone, Debug)]
pub struct Dfa {
    /// Number of states (including the dead state at index 0).
    pub num_states: u32,
    /// Flat transition table: `transitions[state * 256 + byte] = next_state`
    pub transitions: Vec<StateId>,
    /// Start state (always 1 for compiled DFAs).
    pub start: StateId,
    /// Set of accepting states.
    pub accepting: BTreeSet<StateId>,
}

impl Dfa {
    /// Run the DFA against an input byte sequence. Returns true if the DFA
    /// accepts (ends in an accepting state).
    pub fn matches(&self, input: &[u8]) -> bool {
        let mut state = self.start;
        for &byte in input {
            state = self.transitions[(state as usize) * 256 + (byte as usize)];
            if state == DEAD_STATE {
                return false;
            }
        }
        self.accepting.contains(&state)
    }

    /// Run the DFA and return a trace of (state, byte, next_state) for each step.
    /// This trace is what gets encoded into AIR constraint rows.
    pub fn trace(&self, input: &[u8]) -> Vec<Transition> {
        let mut state = self.start;
        let mut trace = Vec::with_capacity(input.len());
        for &byte in input {
            let next = self.transitions[(state as usize) * 256 + (byte as usize)];
            trace.push(Transition {
                state,
                byte,
                next_state: next,
            });
            state = next;
        }
        trace
    }

    /// Number of bytes in the transition table (for resource bound proofs).
    pub fn table_size_bytes(&self) -> usize {
        self.transitions.len() * std::mem::size_of::<StateId>()
    }
}

/// A single state transition, used in execution traces for circuit proofs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transition {
    pub state: StateId,
    pub byte: u8,
    pub next_state: StateId,
}

// ---------------------------------------------------------------------------
// NFA (used as intermediate representation for combinator compilation)
// ---------------------------------------------------------------------------

/// NFA state with epsilon transitions, used during construction.
#[derive(Clone, Debug)]
struct NfaState {
    /// Transitions on specific bytes.
    byte_transitions: HashMap<u8, Vec<StateId>>,
    /// Epsilon (free) transitions.
    epsilon: Vec<StateId>,
}

/// An NFA built from combinators, later determinized into a DFA.
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

    /// Concatenate two NFAs: self followed by other.
    fn concat(mut self, mut other: Nfa) -> Nfa {
        let offset = self.states.len() as StateId;
        // Remap other's state IDs
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

        // Epsilon from self.accept to other.start
        self.states[self.accept as usize]
            .epsilon
            .push(other_start);
        self.states.extend(other.states);
        self.accept = other_accept;
        self
    }

    /// Union of two NFAs (alternation).
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

        // New start and accept
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

    /// Kleene star (zero or more repetitions).
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

    /// Compute epsilon closure of a set of states.
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

    /// Subset construction: convert NFA to DFA.
    fn determinize(&self) -> Dfa {
        let mut dfa_states: Vec<BTreeSet<StateId>> = Vec::new();
        let mut state_map: BTreeMap<BTreeSet<StateId>, StateId> = BTreeMap::new();
        let mut transitions: Vec<StateId> = Vec::new();
        let mut accepting = BTreeSet::new();

        // Dead state (index 0)
        let dead_set = BTreeSet::new();
        dfa_states.push(dead_set.clone());
        state_map.insert(dead_set, DEAD_STATE);
        // Dead state transitions: all go to dead
        transitions.extend(std::iter::repeat(DEAD_STATE).take(256));

        // Start state
        let start_set = {
            let mut s = BTreeSet::new();
            s.insert(self.start);
            self.epsilon_closure(&s)
        };
        let start_id = 1u32;
        dfa_states.push(start_set.clone());
        state_map.insert(start_set.clone(), start_id);
        if start_set.contains(&self.accept) {
            accepting.insert(start_id);
        }
        // Placeholder transitions for start state
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
                    // Goes to dead state
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
// Combinator API (Robigalia-style)
// ---------------------------------------------------------------------------

/// A DFA pattern builder. Patterns are constructed via combinators
/// and compiled to flat transition tables.
#[derive(Clone, Debug)]
pub enum Pattern {
    /// Match a literal byte sequence.
    Word(Vec<u8>),
    /// Match a single byte in the range [low, high] inclusive.
    Range(u8, u8),
    /// Match a single specific bit at a byte offset. `bit(offset_byte, bit_pos, value)`
    Bit(usize, u8, bool),
    /// Match any single byte.
    AnyByte,
    /// Sequence of patterns (concatenation).
    Seq(Vec<Pattern>),
    /// All patterns must match (intersection of DFAs).
    All(Vec<Pattern>),
    /// Any pattern may match (union of DFAs).
    Any(Vec<Pattern>),
    /// Skip N bytes from the start (match N arbitrary bytes then the inner pattern).
    Offset(usize, Box<Pattern>),
    /// Repeat inner pattern count times.
    Repeat(Box<Pattern>, usize),
    /// Match the exact byte sequence at a specific offset in the message.
    BytesAt(usize, Vec<u8>),
}

/// Convenience constructors matching the Robigalia combinator names.
pub fn word(w: &[u8]) -> Pattern {
    Pattern::Word(w.to_vec())
}

pub fn bytes(b: &[u8]) -> Pattern {
    Pattern::Word(b.to_vec())
}

pub fn offset(skip: usize, inner: Pattern) -> Pattern {
    Pattern::Offset(skip, Box::new(inner))
}

pub fn all(patterns: Vec<Pattern>) -> Pattern {
    Pattern::All(patterns)
}

pub fn any(patterns: Vec<Pattern>) -> Pattern {
    Pattern::Any(patterns)
}

pub fn range(low: u8, high: u8) -> Pattern {
    Pattern::Range(low, high)
}

pub fn bit(offset_byte: usize, bit_pos: u8, value: bool) -> Pattern {
    Pattern::Bit(offset_byte, bit_pos, value)
}

pub fn repeat(inner: Pattern, count: usize) -> Pattern {
    Pattern::Repeat(Box::new(inner), count)
}

pub fn any_byte() -> Pattern {
    Pattern::AnyByte
}

impl Pattern {
    /// Compile this pattern to a DFA.
    pub fn compile(&self) -> Dfa {
        match self {
            Pattern::Word(w) => {
                let mut nfa = Nfa::empty();
                // Rebuild: chain of single-byte NFAs
                if w.is_empty() {
                    return nfa.determinize();
                }
                nfa = Nfa::single_byte(w[0]);
                for &b in &w[1..] {
                    nfa = nfa.concat(Nfa::single_byte(b));
                }
                nfa.determinize()
            }
            Pattern::Range(low, high) => {
                let nfa = Nfa::byte_range(*low, *high);
                nfa.determinize()
            }
            Pattern::AnyByte => {
                let nfa = Nfa::byte_range(0, 255);
                nfa.determinize()
            }
            Pattern::Bit(offset_byte, bit_pos, value) => {
                // Build pattern: `offset_byte` any-bytes, then a byte with the
                // specified bit set/unset.
                let mut nfa = if *offset_byte > 0 {
                    let mut chain = Nfa::byte_range(0, 255);
                    for _ in 1..*offset_byte {
                        chain = chain.concat(Nfa::byte_range(0, 255));
                    }
                    chain
                } else {
                    Nfa::empty()
                };

                // Build the byte matcher for the specific bit
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
                    nfa = nfa.concat(bit_nfa);
                } else {
                    nfa = bit_nfa;
                }
                nfa.determinize()
            }
            Pattern::Seq(patterns) => {
                if patterns.is_empty() {
                    return Nfa::empty().determinize();
                }
                let mut nfa = pattern_to_nfa(&patterns[0]);
                for p in &patterns[1..] {
                    nfa = nfa.concat(pattern_to_nfa(p));
                }
                nfa.determinize()
            }
            Pattern::All(patterns) => {
                // Intersection: compile each to DFA, then product construction
                if patterns.is_empty() {
                    return Nfa::empty().determinize();
                }
                let dfas: Vec<Dfa> = patterns.iter().map(|p| p.compile()).collect();
                let mut result = dfas[0].clone();
                for dfa in &dfas[1..] {
                    result = dfa_intersection(&result, dfa);
                }
                result
            }
            Pattern::Any(patterns) => {
                if patterns.is_empty() {
                    return Nfa::empty().determinize();
                }
                let mut nfa = pattern_to_nfa(&patterns[0]);
                for p in &patterns[1..] {
                    nfa = nfa.union(pattern_to_nfa(p));
                }
                nfa.determinize()
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
                nfa = nfa.concat(pattern_to_nfa(inner));
                nfa.determinize()
            }
            Pattern::Repeat(inner, count) => {
                if *count == 0 {
                    return Nfa::empty().determinize();
                }
                let mut nfa = pattern_to_nfa(inner);
                for _ in 1..*count {
                    nfa = nfa.concat(pattern_to_nfa(inner));
                }
                nfa.determinize()
            }
            Pattern::BytesAt(off, data) => {
                offset(*off, Pattern::Word(data.clone())).compile()
            }
        }
    }
}

/// Convert a Pattern to an NFA without determinizing (for composition).
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
        Pattern::Seq(patterns) => {
            if patterns.is_empty() {
                return Nfa::empty();
            }
            let mut nfa = pattern_to_nfa(&patterns[0]);
            for pat in &patterns[1..] {
                nfa = nfa.concat(pattern_to_nfa(pat));
            }
            nfa
        }
        Pattern::Any(patterns) => {
            if patterns.is_empty() {
                return Nfa::empty();
            }
            let mut nfa = pattern_to_nfa(&patterns[0]);
            for pat in &patterns[1..] {
                nfa = nfa.union(pattern_to_nfa(pat));
            }
            nfa
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
        // For complex patterns, build via compile then wrap as a pseudo-NFA.
        // This is fine because these are only used during composition.
        _ => {
            // Fall back: compile to DFA, use that. We could convert back to NFA
            // but it's simpler to just compile the sub-pattern.
            // For correctness, handle Offset/Bit/All/BytesAt here:
            match p {
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
                    nfa = nfa.concat(pattern_to_nfa(inner));
                    nfa
                }
                Pattern::Bit(offset_byte, bit_pos, value) => {
                    let nfa = if *offset_byte > 0 {
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
                Pattern::BytesAt(off, data) => {
                    pattern_to_nfa(&Pattern::Offset(*off, Box::new(Pattern::Word(data.clone()))))
                }
                _ => unreachable!("All handled"),
            }
        }
    }
}

/// DFA product construction for intersection.
fn dfa_intersection(a: &Dfa, b: &Dfa) -> Dfa {
    // Product states: (state_a, state_b) → new_state_id
    let mut state_map: HashMap<(StateId, StateId), StateId> = HashMap::new();
    let mut transitions: Vec<StateId> = Vec::new();
    let mut accepting = BTreeSet::new();

    // Dead state
    state_map.insert((DEAD_STATE, DEAD_STATE), DEAD_STATE);
    transitions.extend(std::iter::repeat(DEAD_STATE).take(256));

    // Start state
    let start_pair = (a.start, b.start);
    let start_id = 1u32;
    state_map.insert(start_pair, start_id);
    transitions.extend(std::iter::repeat(DEAD_STATE).take(256));
    if a.accepting.contains(&a.start) && b.accepting.contains(&b.start) {
        accepting.insert(start_id);
    }

    let mut worklist = VecDeque::new();
    worklist.push_back(start_pair);
    let mut next_id = 2u32;

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
// Capability-secure packet source / classifier
// ---------------------------------------------------------------------------

/// A message that can be routed.
pub trait Message {
    fn payload(&self) -> &[u8];
}

/// Simple byte-buffer message for testing.
#[derive(Clone, Debug)]
pub struct RawMessage {
    pub data: Vec<u8>,
}

impl Message for RawMessage {
    fn payload(&self) -> &[u8] {
        &self.data
    }
}

/// A Classifier wraps a compiled DFA and classifies messages into accept/reject.
#[derive(Clone, Debug)]
pub struct Classifier {
    pub dfa: Arc<Dfa>,
    pub label: String,
}

impl Classifier {
    pub fn new(label: &str, pattern: Pattern) -> Self {
        Classifier {
            dfa: Arc::new(pattern.compile()),
            label: label.to_string(),
        }
    }

    pub fn classify<M: Message>(&self, msg: &M) -> bool {
        self.dfa.matches(msg.payload())
    }
}

/// Outcome of a split classification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RouteDecision {
    Left,
    Right,
}

/// A PacketSource that can be split by a classifier into two sub-sources.
/// Each sub-source is a capability reference — holding a `SourceHandle` gives
/// you the right to receive messages matching that filter.
///
/// This models the Robigalia pattern where `classify(dfa)` on a source produces
/// two new source capabilities.
pub struct PacketSource {
    /// Identifier for this source (capability token).
    pub id: u64,
    /// The filter tree: a series of classifiers applied in order.
    /// A message must pass ALL filters to reach this source.
    filters: Vec<Arc<Dfa>>,
}

/// A handle to one side of a split. This is the capability reference.
#[derive(Debug)]
pub struct SourceHandle {
    pub source_id: u64,
    pub side: RouteDecision,
}

impl PacketSource {
    /// Create a root source (accepts everything).
    pub fn root(id: u64) -> Self {
        PacketSource {
            id,
            filters: Vec::new(),
        }
    }

    /// Test if a message would be accepted by this source's filters.
    pub fn accepts(&self, payload: &[u8]) -> bool {
        for dfa in &self.filters {
            if !dfa.matches(payload) {
                return false;
            }
        }
        true
    }

    /// Split this source by a classifier. Returns two child sources:
    /// - left: messages that match the classifier AND all existing filters
    /// - right: messages that do NOT match the classifier but DO match existing filters
    ///
    /// This is the capability-secure split: each child is a new capability.
    pub fn split(&self, classifier: &Classifier, left_id: u64, right_id: u64) -> (PacketSource, PacketSource) {
        let mut left_filters = self.filters.clone();
        left_filters.push(classifier.dfa.clone());

        // Right side gets the complement — but since we don't have a complement DFA
        // built in, the right source just uses the existing filters and checks
        // non-membership at route time. In a production system, you would compile
        // the complement DFA here.
        let right_filters = self.filters.clone();

        (
            PacketSource {
                id: left_id,
                filters: left_filters,
            },
            PacketSource {
                id: right_id,
                filters: right_filters,
            },
        )
    }

    /// Route a message: returns Left if the message matches all filters plus
    /// an additional classifier, Right otherwise.
    pub fn route(&self, classifier: &Classifier, payload: &[u8]) -> RouteDecision {
        if !self.accepts(payload) {
            // Message doesn't even pass base filters — goes right by default
            return RouteDecision::Right;
        }
        if classifier.dfa.matches(payload) {
            RouteDecision::Left
        } else {
            RouteDecision::Right
        }
    }
}

// ---------------------------------------------------------------------------
// Revocation model
// ---------------------------------------------------------------------------

/// A tree of DFA filters. Revocation = remove a node, recompile the combined
/// DFA for that subtree, and atomically swap.
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
    /// Create a new filter tree with a root that accepts everything (single
    /// accepting state, all transitions loop).
    pub fn new() -> Self {
        let accept_all = {
            // We need state 1 to loop on all bytes and be accepting
            let mut t = vec![DEAD_STATE; 512]; // 2 states * 256
            for i in 0..256 {
                t[256 + i] = 1; // state 1 loops to state 1 on all bytes
            }
            Dfa {
                num_states: 2,
                transitions: t,
                start: 1,
                accepting: {
                    let mut s = BTreeSet::new();
                    s.insert(1);
                    s
                },
            }
        };

        FilterTree {
            nodes: vec![FilterNode {
                dfa: Arc::new(accept_all),
                children: Vec::new(),
                active: true,
            }],
            root: 0,
        }
    }

    /// Add a filter as a child of the given parent node. Returns the node index.
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

    /// Revoke a filter node (marks it inactive).
    pub fn revoke(&mut self, node_idx: usize) {
        self.nodes[node_idx].active = false;
    }

    /// Compile all active filters in the tree into a single combined DFA
    /// (intersection of all active nodes along any path from root).
    /// Returns the combined DFA for the root path.
    pub fn compile_combined(&self) -> Dfa {
        self.compile_subtree(self.root)
    }

    fn compile_subtree(&self, node_idx: usize) -> Dfa {
        let node = &self.nodes[node_idx];
        if !node.active {
            // Inactive node: return accept-all (identity for intersection)
            let mut t = vec![DEAD_STATE; 512];
            for i in 0..256 {
                t[256 + i] = 1;
            }
            return Dfa {
                num_states: 2,
                transitions: t,
                start: 1,
                accepting: {
                    let mut s = BTreeSet::new();
                    s.insert(1);
                    s
                },
            };
        }

        let mut combined = (*node.dfa).clone();
        for &child_idx in &node.children {
            let child_dfa = self.compile_subtree(child_idx);
            combined = dfa_intersection(&combined, &child_dfa);
        }
        combined
    }
}

// ---------------------------------------------------------------------------
// AIR constraint sketch for DFA transition verification
// ---------------------------------------------------------------------------

/// Sketch of how DFA transitions map to AIR (Algebraic Intermediate Representation)
/// constraints.
///
/// Each execution trace row contains:
///   (step_index, current_state, input_byte, next_state)
///
/// Constraints:
/// 1. Transition validity: next_state == transition_table[current_state * 256 + input_byte]
///    - Encoded as a lookup argument into the transition table
/// 2. Continuity: row[i].next_state == row[i+1].current_state
/// 3. Boundary: row[0].current_state == start_state
/// 4. Acceptance: row[last].next_state in accepting_states
///
/// The transition table is committed as a public input (or verified via
/// Merkle path if too large). This lets us prove "message M was correctly
/// classified by DFA D" in zero knowledge.
pub struct AirTraceRow {
    pub step: u32,
    pub state: StateId,
    pub byte: u8,
    pub next_state: StateId,
}

/// Generate the AIR trace for verifying correct DFA execution on an input.
pub fn generate_air_trace(dfa: &Dfa, input: &[u8]) -> Vec<AirTraceRow> {
    let transitions = dfa.trace(input);
    transitions
        .into_iter()
        .enumerate()
        .map(|(i, t)| AirTraceRow {
            step: i as u32,
            state: t.state,
            byte: t.byte,
            next_state: t.next_state,
        })
        .collect()
}

/// Verify the AIR trace constraints (simulates what a STARK verifier checks).
/// Returns true if all constraints hold.
pub fn verify_air_trace(dfa: &Dfa, input: &[u8], trace: &[AirTraceRow]) -> bool {
    if trace.len() != input.len() {
        return false;
    }
    if trace.is_empty() {
        return true;
    }

    // Constraint 1: first row starts at DFA start state
    if trace[0].state != dfa.start {
        return false;
    }

    for (i, row) in trace.iter().enumerate() {
        // Constraint 2: input bytes match
        if row.byte != input[i] {
            return false;
        }

        // Constraint 3: transition validity
        let expected_next = dfa.transitions[(row.state as usize) * 256 + (row.byte as usize)];
        if row.next_state != expected_next {
            return false;
        }

        // Constraint 4: continuity (next row's state == this row's next_state)
        if i + 1 < trace.len() && trace[i + 1].state != row.next_state {
            return false;
        }
    }

    // Constraint 5: acceptance
    let final_state = trace.last().unwrap().next_state;
    dfa.accepting.contains(&final_state)
}

// ---------------------------------------------------------------------------
// Pyana-specific: gossip topic routing
// ---------------------------------------------------------------------------

/// A topic filter for gossip network messages.
/// Messages have a 4-byte topic prefix followed by payload.
/// Topic filters compile to DFAs that match on the prefix bytes.
pub struct TopicFilter {
    pub topic_pattern: Pattern,
    compiled: Dfa,
}

impl TopicFilter {
    /// Create a filter that matches messages with a specific 4-byte topic ID.
    pub fn exact_topic(topic_bytes: [u8; 4]) -> Self {
        let pattern = word(&topic_bytes);
        let compiled = pattern.compile();
        TopicFilter {
            topic_pattern: pattern,
            compiled,
        }
    }

    /// Create a filter that matches any topic in a range (e.g., topic IDs 0x00..0xFF
    /// in the first byte, useful for namespace-based routing).
    pub fn topic_namespace(first_byte_low: u8, first_byte_high: u8) -> Self {
        let pattern = Pattern::Seq(vec![
            range(first_byte_low, first_byte_high),
            any_byte(),
            any_byte(),
            any_byte(),
        ]);
        let compiled = pattern.compile();
        TopicFilter {
            topic_pattern: pattern,
            compiled,
        }
    }

    /// Test if a message matches this topic filter.
    /// Only looks at the first 4 bytes (topic prefix).
    pub fn matches(&self, msg: &[u8]) -> bool {
        if msg.len() < 4 {
            return false;
        }
        self.compiled.matches(&msg[..4])
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal_word_match() {
        let dfa = word(b"hello").compile();
        assert!(dfa.matches(b"hello"));
        assert!(!dfa.matches(b"hell"));
        assert!(!dfa.matches(b"helloo"));
        assert!(!dfa.matches(b"world"));
        assert!(!dfa.matches(b""));
    }

    #[test]
    fn test_single_byte_range() {
        let dfa = range(b'a', b'z').compile();
        assert!(dfa.matches(b"a"));
        assert!(dfa.matches(b"m"));
        assert!(dfa.matches(b"z"));
        assert!(!dfa.matches(b"A"));
        assert!(!dfa.matches(b"0"));
        assert!(!dfa.matches(b"ab")); // too long
        assert!(!dfa.matches(b""));   // too short
    }

    #[test]
    fn test_any_union() {
        // Match either "foo" or "bar"
        let dfa = any(vec![word(b"foo"), word(b"bar")]).compile();
        assert!(dfa.matches(b"foo"));
        assert!(dfa.matches(b"bar"));
        assert!(!dfa.matches(b"baz"));
        assert!(!dfa.matches(b"fo"));
        assert!(!dfa.matches(b"foobar"));
    }

    #[test]
    fn test_all_intersection() {
        // 3-byte string where first byte is in 'a'..'z' AND first byte is in 'f'..'m'
        // Combined: first byte in 'f'..'m', then any 2 bytes
        let pattern_az = Pattern::Seq(vec![range(b'a', b'z'), any_byte(), any_byte()]);
        let pattern_fm = Pattern::Seq(vec![range(b'f', b'm'), any_byte(), any_byte()]);
        let dfa = all(vec![pattern_az, pattern_fm]).compile();

        assert!(dfa.matches(b"foo"));  // 'f' is in both ranges
        assert!(dfa.matches(b"moo"));  // 'm' is in both ranges
        assert!(!dfa.matches(b"aoo")); // 'a' is in a-z but not f-m
        assert!(!dfa.matches(b"zoo")); // 'z' is in a-z but not f-m
        assert!(!dfa.matches(b"Foo")); // 'F' is in neither
    }

    #[test]
    fn test_offset_pattern() {
        // Skip 2 bytes then match "OK"
        let dfa = offset(2, word(b"OK")).compile();
        assert!(dfa.matches(b"xxOK"));
        assert!(dfa.matches(b"\x00\x00OK"));
        assert!(!dfa.matches(b"OK"));     // no offset
        assert!(!dfa.matches(b"xOK"));    // only 1 byte offset
        assert!(!dfa.matches(b"xxOKx"));  // too long
    }

    #[test]
    fn test_repeat_pattern() {
        // Three lowercase letters
        let dfa = repeat(range(b'a', b'z'), 3).compile();
        assert!(dfa.matches(b"abc"));
        assert!(dfa.matches(b"zzz"));
        assert!(!dfa.matches(b"ab"));
        assert!(!dfa.matches(b"abcd"));
        assert!(!dfa.matches(b"AB1"));
    }

    #[test]
    fn test_bit_pattern() {
        // Match single byte with bit 7 set (high bit = value >= 128)
        let dfa = bit(0, 7, true).compile();
        assert!(dfa.matches(&[0x80]));
        assert!(dfa.matches(&[0xFF]));
        assert!(!dfa.matches(&[0x7F]));
        assert!(!dfa.matches(&[0x00]));
    }

    #[test]
    fn test_capability_secure_split() {
        let root = PacketSource::root(1);
        let http_classifier = Classifier::new("http", word(b"HTTP"));
        // Split root by HTTP
        let (http_source, _non_http_source) = root.split(&http_classifier, 2, 3);

        assert!(http_source.accepts(b"HTTP"));
        assert!(!http_source.accepts(b"SMTP"));

        // Route decisions
        assert_eq!(root.route(&http_classifier, b"HTTP"), RouteDecision::Left);
        assert_eq!(root.route(&http_classifier, b"SMTP"), RouteDecision::Right);
    }

    #[test]
    fn test_filter_tree_revocation() {
        let mut tree = FilterTree::new();

        // Add a filter that only accepts messages starting with 'A'
        let filter_a = Pattern::Seq(vec![word(b"A"), any_byte(), any_byte()]).compile();
        let _node_a = tree.add_filter(0, filter_a);

        // Add a filter that only accepts 3-byte messages ending with 'Z'
        let filter_z = Pattern::Seq(vec![any_byte(), any_byte(), word(b"Z")]).compile();
        let node_z = tree.add_filter(0, filter_z);

        // Combined: must start with 'A' AND end with 'Z' (3 bytes total)
        let combined = tree.compile_combined();
        assert!(combined.matches(b"AxZ"));
        assert!(!combined.matches(b"BxZ")); // doesn't start with A
        assert!(!combined.matches(b"AxY")); // doesn't end with Z

        // Revoke the 'Z' filter
        tree.revoke(node_z);
        let combined_after = tree.compile_combined();
        assert!(combined_after.matches(b"AxZ")); // still starts with A
        assert!(combined_after.matches(b"AxY")); // no longer requires Z
        assert!(!combined_after.matches(b"BxZ")); // still requires A
    }

    #[test]
    fn test_air_trace_generation() {
        let dfa = word(b"hi").compile();
        let trace = generate_air_trace(&dfa, b"hi");

        assert_eq!(trace.len(), 2);
        assert_eq!(trace[0].step, 0);
        assert_eq!(trace[0].byte, b'h');
        assert_eq!(trace[1].step, 1);
        assert_eq!(trace[1].byte, b'i');

        // Verify trace is valid
        assert!(verify_air_trace(&dfa, b"hi", &trace));
    }

    #[test]
    fn test_air_trace_verification_detects_tampering() {
        let dfa = word(b"hi").compile();
        let mut trace = generate_air_trace(&dfa, b"hi");

        // Tamper with the trace
        trace[0].next_state = 99; // invalid state
        assert!(!verify_air_trace(&dfa, b"hi", &trace));
    }

    #[test]
    fn test_gossip_topic_filter() {
        let filter = TopicFilter::exact_topic([0x01, 0x02, 0x03, 0x04]);
        assert!(filter.matches(&[0x01, 0x02, 0x03, 0x04, 0xFF, 0xAA]));
        assert!(!filter.matches(&[0x01, 0x02, 0x03, 0x05, 0xFF, 0xAA]));
        assert!(!filter.matches(&[0x01, 0x02, 0x03])); // too short
    }

    #[test]
    fn test_gossip_namespace_filter() {
        // Accept topics where first byte is in range 0x10..0x1F
        let filter = TopicFilter::topic_namespace(0x10, 0x1F);
        assert!(filter.matches(&[0x10, 0x00, 0x00, 0x00, 0xDE, 0xAD]));
        assert!(filter.matches(&[0x1F, 0xFF, 0xFF, 0xFF]));
        assert!(!filter.matches(&[0x20, 0x00, 0x00, 0x00, 0x00]));
        assert!(!filter.matches(&[0x0F, 0x00, 0x00, 0x00, 0x00]));
    }

    #[test]
    fn test_dfa_resource_bounds() {
        // Verify that DFA has bounded, predictable resource usage
        let dfa = word(b"test").compile();
        // 5 states (dead + start + one per byte after first) — exact count depends
        // on implementation but must be bounded
        assert!(dfa.num_states <= 10);
        // Table size is exactly num_states * 256 * size_of(StateId)
        assert_eq!(
            dfa.table_size_bytes(),
            (dfa.num_states as usize) * 256 * 4
        );
    }

    #[test]
    fn test_empty_pattern() {
        let dfa = word(b"").compile();
        assert!(dfa.matches(b"")); // empty matches empty
        assert!(!dfa.matches(b"x")); // empty doesn't match non-empty
    }

    #[test]
    fn test_complex_composed_pattern() {
        // Wire protocol dispatch: 1-byte type tag, then type-specific matching
        // Type 0x01 = "auth" messages (must have 0x01 followed by 4+ bytes)
        // Type 0x02 = "data" messages
        let auth_pattern = Pattern::Seq(vec![
            word(&[0x01]),
            any_byte(),
            any_byte(),
            any_byte(),
            any_byte(),
        ]);
        let data_pattern = Pattern::Seq(vec![
            word(&[0x02]),
            any_byte(),
            any_byte(),
        ]);
        let dispatch = any(vec![auth_pattern, data_pattern]);
        let dfa = dispatch.compile();

        // Auth message (5 bytes: type + 4 payload)
        assert!(dfa.matches(&[0x01, 0xAA, 0xBB, 0xCC, 0xDD]));
        // Data message (3 bytes: type + 2 payload)
        assert!(dfa.matches(&[0x02, 0x00, 0x01]));
        // Unknown type
        assert!(!dfa.matches(&[0x03, 0x00, 0x00]));
        // Auth message wrong length
        assert!(!dfa.matches(&[0x01, 0xAA, 0xBB]));
    }

    #[test]
    fn test_classifier_routing_pipeline() {
        // Simulate a 3-level routing tree:
        // root -> [tcp/udp] -> [port range] -> [payload pattern]
        //
        // DFAs match fixed-length sequences, so patterns must account for
        // the full message length. Here messages are 5 bytes:
        //   [protocol, port_hi, port_lo, payload0, payload1]
        let root = PacketSource::root(0);

        // Level 1: TCP (0x06) followed by 4 arbitrary bytes
        let tcp_filter = Classifier::new("tcp", Pattern::Seq(vec![
            word(&[0x06]), any_byte(), any_byte(), any_byte(), any_byte(),
        ]));
        let (tcp_source, _udp_source) = root.split(&tcp_filter, 1, 2);

        // Level 2: any protocol byte, then port 80 (0x00 0x50), then 2 payload bytes
        let port80_filter = Classifier::new("port80", Pattern::Seq(vec![
            any_byte(), word(&[0x00, 0x50]), any_byte(), any_byte(),
        ]));

        // TCP + port 80
        let msg_tcp_80 = [0x06u8, 0x00, 0x50, 0xDE, 0xAD];
        let msg_tcp_443 = [0x06u8, 0x01, 0xBB, 0xDE, 0xAD];
        let msg_udp_53 = [0x11u8, 0x00, 0x35, 0xDE, 0xAD];

        // TCP source accepts TCP messages (5 bytes starting with 0x06)
        assert!(tcp_source.accepts(&msg_tcp_80));
        assert!(tcp_source.accepts(&msg_tcp_443));
        assert!(!tcp_source.accepts(&msg_udp_53));

        // Route within TCP source by port
        assert_eq!(
            tcp_source.route(&port80_filter, &msg_tcp_80),
            RouteDecision::Left
        );
        assert_eq!(
            tcp_source.route(&port80_filter, &msg_tcp_443),
            RouteDecision::Right
        );
    }
}
