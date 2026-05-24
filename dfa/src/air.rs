//! AIR trace generation/verification for proving correct DFA execution.
//!
//! The trace shape `(step, state, byte, next_state)` matches the
//! `pyana-dfa-routing-v1` AIR in `tests/src/dfa_circuit.rs` and the in-DSL
//! variant at `circuit::dsl::circuit:1711-1941`. Hooking up a route-table
//! commitment to a STARK proof of "this input was correctly classified by
//! the governance-bound DFA D" is therefore mechanical: serialize each
//! transition as a row in this shape, hand the trace to the AIR.

use crate::compiler::{Dfa, StateId};

/// One row of the DFA execution trace.
#[derive(Clone, Debug, PartialEq, Eq)]
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
}
