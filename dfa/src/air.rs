//! AIR trace generation/verification for proving correct DFA execution.
//!
//! The trace shape `(step, state, byte, next_state)` matches the
//! `dregg-dfa-routing-v1` AIR in `tests/src/dfa_circuit.rs` and the in-DSL
//! variant at `circuit::dsl::circuit:1711-1941`. Hooking up a route-table
//! commitment to a STARK proof of "this input was correctly classified by
//! the governance-bound DFA D" is therefore mechanical: serialize each
//! transition as a row in this shape, hand the trace to the AIR.

use crate::compiler::{DEAD_STATE, Dfa, StateId};
use crate::router::{RouteTable, RouteTarget, Router, compute_commitment};
use std::collections::{BTreeMap, BTreeSet};

/// One row of the DFA execution trace.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct AirTraceRow {
    pub step: u32,
    pub state: StateId,
    pub byte: u8,
    pub next_state: StateId,
}

/// Generate the AIR trace for running `dfa` on `input`.
pub fn generate_air_trace(dfa: &Dfa, input: &[u8]) -> Vec<AirTraceRow> {
    dfa.trace(input)
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

/// Sanity-check the trace constraints out of circuit (the same checks the AIR
/// performs in zero knowledge):
///
/// 1. Trace length == input length.
/// 2. Row 0's state == dfa.start.
/// 3. Per-row: `byte == input[i]` and `next_state == dfa.transitions[state*256 + byte]`.
/// 4. Continuity: `trace[i+1].state == trace[i].next_state`.
/// 5. Acceptance: the final `next_state` is in `dfa.accepting`.
pub fn verify_air_trace(dfa: &Dfa, input: &[u8], trace: &[AirTraceRow]) -> bool {
    if trace.len() != input.len() {
        return false;
    }
    if trace.is_empty() {
        return dfa.accepting.contains(&dfa.start);
    }
    if trace[0].state != dfa.start {
        return false;
    }
    for (i, row) in trace.iter().enumerate() {
        if row.byte != input[i] {
            return false;
        }
        let idx = (row.state as usize) * 256 + (row.byte as usize);
        let expected_next = if idx < dfa.transitions.len() {
            dfa.transitions[idx]
        } else {
            return false;
        };
        if row.next_state != expected_next {
            return false;
        }
        if i + 1 < trace.len() && trace[i + 1].state != row.next_state {
            return false;
        }
    }
    let final_state = trace.last().unwrap().next_state;
    dfa.accepting.contains(&final_state)
}

// ---------------------------------------------------------------------------
// External AIR API: compile_to_air / verify_acceptance
// ---------------------------------------------------------------------------

use serde::{Deserialize, Serialize};

/// The full AIR-ready witness for a routed input: the route table commitment
/// the trace was generated against, the trace itself, and the table's
/// transition vector (needed in-circuit as the lookup table).
///
/// The slot-caveat predicate kind `WitnessedPredicateKind::Dfa` (in `cell/`)
/// proves "input `I` was classified by route-table-commitment `C` and landed
/// on an accepting state." A prover produces one of these via
/// [`compile_to_air`] / [`compile_to_air_from_table`]; the cell-side
/// `DfaAcceptanceVerifier` (registered by
/// `WitnessedPredicateRegistry::default_builtins`) re-checks it via
/// [`verify_acceptance`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AirTrace {
    /// BLAKE3 commitment of the route table the trace was produced against.
    /// In-circuit, this is bound as a public input so the verifier can match
    /// it against the constitution-bound table.
    pub router_root: [u8; 32],
    /// The flat transition table layered as `[state * 256 + byte] -> next_state`.
    /// Used as the lookup table for the AIR's `Lookup` constraint over the
    /// `(state, byte, next_state)` row shape.
    pub transitions: Vec<StateId>,
    /// Number of states in the DFA (including the dead state at index 0).
    pub num_states: u32,
    /// Start state (always 1 for compiled DFAs).
    pub start: StateId,
    /// The route table's accept-map: accepting state -> route target. This is
    /// what the commitment covers, so the verifier derives the accepting set
    /// from it instead of trusting a free list (the AIR boundary constraint
    /// is `final_state IN keys(accept_map)`).
    pub accept_map: BTreeMap<StateId, RouteTarget>,
    /// The route table's declared-prefix lengths (part of the commitment).
    pub prefix_lens: BTreeMap<StateId, usize>,
    /// The input bytes the trace was generated against.
    pub input: Vec<u8>,
    /// The execution trace rows.
    pub trace: Vec<AirTraceRow>,
}

impl AirTrace {
    /// The final state the DFA reached on this input.
    pub fn final_state(&self) -> StateId {
        self.trace
            .last()
            .map(|r| r.next_state)
            .unwrap_or(self.start)
    }

    /// True iff the trace ends in an accepting state.
    pub fn accepts(&self) -> bool {
        let final_state = self.final_state();
        self.accept_map.contains_key(&final_state)
    }

    /// The commitment this trace's OWN table hashes to. Equal to `router_root`
    /// for an honest trace; [`verify_acceptance`] refuses any trace where the
    /// two differ, which is what binds the table to the constitution-bound root.
    pub fn recomputed_root(&self) -> [u8; 32] {
        compute_commitment(&self.transitions, &self.accept_map, &self.prefix_lens)
    }

    /// The authenticated DFA (only meaningful after the shape checks of
    /// [`verify_acceptance`] have passed).
    fn as_dfa(&self) -> Dfa {
        Dfa {
            num_states: self.num_states,
            transitions: self.transitions.clone(),
            start: self.start,
            accepting: self.accept_map.keys().copied().collect::<BTreeSet<_>>(),
        }
    }

    /// Serialize this trace to a wire-friendly byte blob (postcard).
    /// This is the `proof_bytes` payload that
    /// [`verify_acceptance`] consumes.
    pub fn to_proof_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("AirTrace postcard encoding cannot fail")
    }

    /// Deserialize a trace from `proof_bytes`.
    pub fn from_proof_bytes(bytes: &[u8]) -> Result<Self, DfaError> {
        postcard::from_bytes(bytes).map_err(|e| DfaError::Decode(e.to_string()))
    }
}

/// Errors returned by the AIR-facing DFA API.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DfaError {
    /// The supplied `proof_bytes` could not be decoded as an [`AirTrace`].
    Decode(String),
    /// The trace's `router_root` did not match the expected commitment.
    CommitmentMismatch,
    /// The trace is internally inconsistent (trace length != input length, or
    /// a transition row doesn't match the embedded table).
    TraceInvalid(&'static str),
    /// The trace verified structurally but the final state is not accepting.
    NotAccepting,
    /// The supplied input bytes did not match the trace's input.
    InputMismatch,
    /// The embedded table is malformed (wrong length, out-of-range state ids).
    TableInvalid(&'static str),
}

impl std::fmt::Display for DfaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DfaError::Decode(msg) => write!(f, "decode error: {msg}"),
            DfaError::CommitmentMismatch => write!(f, "router root commitment mismatch"),
            DfaError::TraceInvalid(why) => write!(f, "trace invalid: {why}"),
            DfaError::NotAccepting => write!(f, "trace did not end in an accepting state"),
            DfaError::InputMismatch => write!(f, "input bytes did not match trace input"),
            DfaError::TableInvalid(why) => write!(f, "table invalid: {why}"),
        }
    }
}

impl std::error::Error for DfaError {}

// (StateId is already imported at the top of the file.)

/// Compile a [`Router`]'s DFA and an input bytestring into an [`AirTrace`]
/// ready to feed the in-circuit DFA AIR. The router's table commitment is
/// embedded as `router_root`.
///
/// This is the API that the slot-caveat verifier
/// (`WitnessedPredicateKind::Dfa`) calls when constructing the AIR-bound
/// proof. Consumers can either:
///
/// 1. Hand the trace to the STARK prover directly (typical path), or
/// 2. Serialize via [`AirTrace::to_proof_bytes`] and ship it across the wire
///    where [`verify_acceptance`] reconstructs and checks it.
pub fn compile_to_air(router: &Router, input: &[u8]) -> AirTrace {
    let dfa = router.as_dfa();
    // For prefix-style routes ("/cells/alpha/*"), the accepting state is the
    // declared-boundary state, and consuming bytes past it leaves the DFA in
    // a non-accepting state. The AIR proves "input I was accepted by DFA D" —
    // so we truncate the trace at the longest accept boundary (the same
    // longest-match boundary `Router::classify` uses).
    let (_final, longest) = dfa.run_with_longest_match(input);
    let trace_len = longest.unwrap_or(input.len()).min(input.len());
    let truncated = &input[..trace_len];
    let trace = generate_air_trace(&dfa, truncated);
    AirTrace {
        router_root: router.table().commitment,
        transitions: dfa.transitions.clone(),
        num_states: dfa.num_states,
        start: dfa.start,
        accept_map: router.table().accept_map.clone(),
        prefix_lens: router.table().prefix_lens.clone(),
        input: truncated.to_vec(),
        trace,
    }
}

/// Variant of [`compile_to_air`] that takes the [`RouteTable`] directly.
pub fn compile_to_air_from_table(table: &RouteTable, input: &[u8]) -> AirTrace {
    let r = Router::new(table.clone());
    compile_to_air(&r, input)
}

/// In-executor verification of a serialized [`AirTrace`].
///
/// Stable signature (do not change — the cell-side `DfaAcceptanceVerifier` for
/// `WitnessedPredicateKind::Dfa` in `dregg-cell/src/predicate.rs` calls this
/// directly, mapping `Ok(true)` → accept and `Ok(false)`/`Err(_)` → reject):
///
/// ```text
/// verify_acceptance(router_root: [u8;32], input: &[u8], proof_bytes: &[u8])
///     -> Result<bool, DfaError>
/// ```
///
/// ⚑ 2026-11-06 (codex round 3 of the automata program, finding 3): until this
/// date the table, start state and accepting set were read off the proof and
/// never authenticated against `router_root`; the root was compared to the
/// proof's OWN copy of itself. A proof carrying the expected root, an empty
/// input, an empty trace, `start = 0` and `accepting = [0]` verified for ANY
/// supplied input (every string starts with the empty prefix; `accepts()` of an
/// empty trace is `accepting ∋ start`). A second forgery: a trace over a SHORTER
/// accepting prefix of the input re-classified it to the shorter route's
/// target, because only `input.starts_with(trace.input)` was checked. Both are
/// pinned red below (`forged_empty_trace_with_copied_root_is_rejected`,
/// `shorter_accepting_prefix_is_not_the_classification`).
///
/// Returns `Ok(true)` iff:
///
/// 1. `proof_bytes` decodes to an [`AirTrace`] whose table is well-shaped
///    (`transitions.len() == num_states · 256`, every state id `< num_states`).
/// 2. The commitment RECOMPUTED from the proof's table (`transitions ‖
///    accept-map ‖ prefix-lens`, the same function `RouteTable` uses) equals
///    the supplied `router_root`, and so does the proof's embedded copy. The
///    table is thereby the constitution-bound one; nothing below trusts a
///    field the root does not cover.
/// 3. The trace's `input` is exactly the longest-match truncation of the
///    supplied `input` under that table (the span `Router::classify` uses), so
///    the classification is the table's, not the prover's.
/// 4. Every row's `next_state` matches the table and rows chain.
/// 5. The final state is a key of the accept-map.
pub fn verify_acceptance(
    router_root: [u8; 32],
    input: &[u8],
    proof_bytes: &[u8],
) -> Result<bool, DfaError> {
    let air = AirTrace::from_proof_bytes(proof_bytes)?;
    // 1. shape
    let n = air.num_states as usize;
    if n == 0 || air.transitions.len() != n * 256 {
        return Err(DfaError::TableInvalid(
            "transitions length must equal num_states * 256",
        ));
    }
    if air.transitions.iter().any(|&t| (t as usize) >= n) {
        return Err(DfaError::TableInvalid("transition target out of range"));
    }
    if (air.start as usize) >= n || air.start == DEAD_STATE {
        return Err(DfaError::TableInvalid("start state out of range or dead"));
    }
    if air
        .accept_map
        .keys()
        .any(|&q| (q as usize) >= n || q == DEAD_STATE)
    {
        return Err(DfaError::TableInvalid(
            "accepting state out of range or dead",
        ));
    }
    // 2. the root is EARNED by the table, not copied
    let recomputed = air.recomputed_root();
    if recomputed != router_root || air.router_root != router_root {
        return Err(DfaError::CommitmentMismatch);
    }
    let dfa = air.as_dfa();
    // 3. the trace covers exactly the longest-match span of the supplied input
    let (_final, longest) = dfa.run_with_longest_match(input);
    let span = longest.unwrap_or(input.len()).min(input.len());
    if air.input.as_slice() != &input[..span] {
        return Err(DfaError::InputMismatch);
    }
    if air.trace.len() != air.input.len() {
        return Err(DfaError::TraceInvalid(
            "trace length must equal input length",
        ));
    }
    // 4. rows
    if !air.trace.is_empty() && air.trace[0].state != air.start {
        return Err(DfaError::TraceInvalid("first row state must be DFA start"));
    }
    for (i, row) in air.trace.iter().enumerate() {
        if row.byte != air.input[i] {
            return Err(DfaError::TraceInvalid("row byte does not match input"));
        }
        let idx = (row.state as usize) * 256 + (row.byte as usize);
        let expected_next = air
            .transitions
            .get(idx)
            .copied()
            .ok_or(DfaError::TraceInvalid("row index out of transition table"))?;
        if row.next_state != expected_next {
            return Err(DfaError::TraceInvalid(
                "row next_state does not match transitions table",
            ));
        }
        if i + 1 < air.trace.len() && air.trace[i + 1].state != row.next_state {
            return Err(DfaError::TraceInvalid("trace continuity broken"));
        }
    }
    // 5. acceptance, against the authenticated accept-map
    Ok(air.accepts())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::Pattern;

    #[test]
    fn trace_for_literal_match_verifies() {
        let dfa = Pattern::word(b"hi").compile();
        let trace = generate_air_trace(&dfa, b"hi");
        assert_eq!(trace.len(), 2);
        assert_eq!(trace[0].step, 0);
        assert_eq!(trace[0].byte, b'h');
        assert_eq!(trace[1].byte, b'i');
        assert!(verify_air_trace(&dfa, b"hi", &trace));
    }

    #[test]
    fn tampered_trace_rejected() {
        let dfa = Pattern::word(b"hi").compile();
        let mut trace = generate_air_trace(&dfa, b"hi");
        trace[0].next_state = 99;
        assert!(!verify_air_trace(&dfa, b"hi", &trace));
    }

    #[test]
    fn non_matching_input_trace_rejected_on_acceptance() {
        let dfa = Pattern::word(b"hi").compile();
        // Feed "hx" — DFA goes to dead state after 'x'.
        let trace = generate_air_trace(&dfa, b"hx");
        // The trace itself is internally consistent (transitions match the
        // table), but the final state isn't accepting.
        assert!(!verify_air_trace(&dfa, b"hx", &trace));
    }

    // ------------------------- compile_to_air / verify_acceptance ----------

    use crate::router::RouteTableBuilder;

    #[test]
    fn air_trace_roundtrip_through_proof_bytes() {
        let table = RouteTableBuilder::new()
            .route("/health", RouteTarget::handler("health"))
            .route("/cells/alpha/*", RouteTarget::handler("alpha"))
            .compile();
        let router = Router::new(table.clone());
        let trace = compile_to_air(&router, b"/cells/alpha/transfer");
        assert!(trace.accepts(), "trace should accept on a matching input");
        let bytes = trace.to_proof_bytes();
        let ok = verify_acceptance(table.commitment, b"/cells/alpha/transfer", &bytes).unwrap();
        assert!(ok);
    }

    #[test]
    fn air_verify_rejects_commitment_mismatch() {
        let table = RouteTableBuilder::new()
            .route("/health", RouteTarget::handler("health"))
            .compile();
        let router = Router::new(table);
        let trace = compile_to_air(&router, b"/health");
        let bytes = trace.to_proof_bytes();
        let err = verify_acceptance([0u8; 32], b"/health", &bytes).unwrap_err();
        assert_eq!(err, DfaError::CommitmentMismatch);
    }

    #[test]
    fn air_verify_rejects_input_mismatch() {
        let table = RouteTableBuilder::new()
            .route("/health", RouteTarget::handler("health"))
            .compile();
        let commitment = table.commitment;
        let router = Router::new(table);
        let trace = compile_to_air(&router, b"/health");
        let bytes = trace.to_proof_bytes();
        let err = verify_acceptance(commitment, b"/other", &bytes).unwrap_err();
        assert_eq!(err, DfaError::InputMismatch);
    }

    #[test]
    fn air_verify_rejects_tampered_transition() {
        let table = RouteTableBuilder::new()
            .route("/health", RouteTarget::handler("health"))
            .compile();
        let commitment = table.commitment;
        let router = Router::new(table);
        let mut trace = compile_to_air(&router, b"/health");
        if !trace.trace.is_empty() {
            // Flip a transition to something the table doesn't agree with.
            trace.trace[0].next_state = trace.trace[0].next_state.wrapping_add(1).max(2);
        }
        let bytes = trace.to_proof_bytes();
        let err = verify_acceptance(commitment, b"/health", &bytes).unwrap_err();
        assert!(matches!(err, DfaError::TraceInvalid(_)));
    }

    #[test]
    fn air_verify_returns_false_for_non_accepting_input() {
        // Input that runs the DFA off into a non-accepting (or dead) state.
        let table = RouteTableBuilder::new()
            .route("/health", RouteTarget::handler("health"))
            .compile();
        let commitment = table.commitment;
        let router = Router::new(table);
        // "/healx" — diverges at the last byte.
        let trace = compile_to_air(&router, b"/healx");
        let bytes = trace.to_proof_bytes();
        let ok = verify_acceptance(commitment, b"/healx", &bytes).unwrap();
        assert!(!ok);
    }

    // ------------------------- the two forgeries of 2026-11-06 ---------------

    #[test]
    fn forged_empty_trace_with_copied_root_is_rejected() {
        // The constitution-bound table.
        let table = RouteTableBuilder::new()
            .route("/health", RouteTarget::handler("health"))
            .compile();
        let commitment = table.commitment;
        // A prover who knows the public root crafts a two-state table whose
        // start state accepts, copies the root, and supplies an EMPTY trace:
        // every input starts with the empty prefix.
        let mut accept_map = BTreeMap::new();
        accept_map.insert(1u32, RouteTarget::handler("anything"));
        let forged = AirTrace {
            router_root: commitment,
            transitions: vec![0; 2 * 256],
            num_states: 2,
            start: 1,
            accept_map,
            prefix_lens: BTreeMap::new(),
            input: Vec::new(),
            trace: Vec::new(),
        };
        assert!(forged.accepts(), "the forgery is internally consistent");
        let err =
            verify_acceptance(commitment, b"/not-a-route", &forged.to_proof_bytes()).unwrap_err();
        assert_eq!(err, DfaError::CommitmentMismatch);
    }

    #[test]
    fn foreign_table_with_copied_root_is_rejected() {
        let bound = RouteTableBuilder::new()
            .route("/health", RouteTarget::handler("health"))
            .compile();
        let other = RouteTableBuilder::new()
            .route("/admin", RouteTarget::handler("admin"))
            .compile();
        // An honest trace over the OTHER table, re-labelled with the bound root.
        let mut trace = compile_to_air(&Router::new(other), b"/admin");
        assert!(trace.accepts());
        trace.router_root = bound.commitment;
        let err =
            verify_acceptance(bound.commitment, b"/admin", &trace.to_proof_bytes()).unwrap_err();
        assert_eq!(err, DfaError::CommitmentMismatch);
    }

    #[test]
    fn widened_accept_map_is_rejected() {
        let table = RouteTableBuilder::new()
            .route("/health", RouteTarget::handler("health"))
            .compile();
        let commitment = table.commitment;
        let router = Router::new(table);
        // "/heal" stops in a live, non-accepting state; the prover "accepts"
        // it by adding that state to the accept-map. The map is committed: refused.
        let mut trace = compile_to_air(&router, b"/heal");
        assert!(!trace.accepts());
        assert_ne!(trace.final_state(), DEAD_STATE);
        trace
            .accept_map
            .insert(trace.final_state(), RouteTarget::handler("health"));
        let err = verify_acceptance(commitment, b"/heal", &trace.to_proof_bytes()).unwrap_err();
        assert_eq!(err, DfaError::CommitmentMismatch);
    }

    #[test]
    fn shorter_accepting_prefix_is_not_the_classification() {
        // Two routes where one is a proper prefix of the other.
        let table = RouteTableBuilder::new()
            .route("/a", RouteTarget::handler("short"))
            .route("/ab", RouteTarget::handler("long"))
            .compile();
        let commitment = table.commitment;
        let router = Router::new(table);
        // Honest: the longest match of "/ab" is "/ab".
        let honest = compile_to_air(&router, b"/ab");
        assert_eq!(honest.input, b"/ab");
        assert!(verify_acceptance(commitment, b"/ab", &honest.to_proof_bytes()).unwrap());
        // Forged: a genuine accepting trace over the shorter prefix "/a",
        // presented as the classification of "/ab" (it used to pass: "/ab"
        // starts with "/a"). The classification is the table's longest match.
        let forged = compile_to_air(&router, b"/a");
        assert!(forged.accepts());
        let err = verify_acceptance(commitment, b"/ab", &forged.to_proof_bytes()).unwrap_err();
        assert_eq!(err, DfaError::InputMismatch);
    }

    #[test]
    fn malformed_table_is_rejected_before_the_root_is_compared() {
        let table = RouteTableBuilder::new()
            .route("/health", RouteTarget::handler("health"))
            .compile();
        let commitment = table.commitment;
        let mut trace = compile_to_air(&Router::new(table), b"/health");
        trace.transitions.push(0);
        let err = verify_acceptance(commitment, b"/health", &trace.to_proof_bytes()).unwrap_err();
        assert!(matches!(err, DfaError::TableInvalid(_)));
    }
}
