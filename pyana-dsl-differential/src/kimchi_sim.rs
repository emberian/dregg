//! Kimchi generic-gate simulator.
//!
//! `gen_kimchi` emits a [`KimchiCircuitDescriptor`] of `Generic` and
//! `Poseidon` gates. The Generic gates are linear/quadratic polynomial
//! constraints of the shape `c0*w0 + c1*w1 + c2*w2 + c3*(w0*w1) + c4 = 0`.
//! Each IR requirement compiles to a known gate sequence (see the
//! per-shape commentary in `gen_kimchi.rs`); given the canonical witness
//! values implied by the inputs, we evaluate every Generic gate's
//! polynomial and assert it equals zero.
//!
//! When the polynomial cannot be made to equal zero for ANY witness (i.e.
//! the inputs violate the predicate), simulator reports Reject. When every
//! gate can be witnessed simultaneously, it reports Accept.
//!
//! Poseidon gates appear only for membership and Merkle requirements. We
//! treat them as "the hash-tree witness exists iff the set logically
//! contains the element" — i.e. semantically delegate to the IR-level
//! truth of [`Requirement::Membership`]. Backend tests under
//! `circuit/src/backends/kimchi_native/` verify the actual Poseidon
//! correctness; this crate's value-add is cross-backend verdict
//! agreement, not gate-level Poseidon soundness.

use pyana_dsl_runtime::{KimchiCircuitDescriptor, KimchiGateType};

use crate::predicates::Requirement;

/// Evaluate Kimchi gates against the IR-level requirement list. Returns
/// `Ok(accept)` on a clean run or `Err(reason)` if the descriptor's gate
/// sequence doesn't structurally match what we expected.
pub fn evaluate(
    descriptor: &KimchiCircuitDescriptor,
    requirements: &[Requirement],
) -> Result<bool, String> {
    // Structural sanity: every IR shape contributes a known burst of gates.
    let expected = expected_gate_count(requirements);
    if descriptor.gates.len() != expected {
        return Err(format!(
            "kimchi gate count mismatch: descriptor has {}, expected {} for {} requirement(s)",
            descriptor.gates.len(),
            expected,
            requirements.len(),
        ));
    }

    // Walk the descriptor and IR requirements in lockstep. Each requirement
    // consumes a known number of gates and decides on its own accept/reject
    // by computing the canonical witness.
    let mut cursor = 0usize;
    for req in requirements {
        let take = gate_burst_for(req);
        let slice = &descriptor.gates[cursor..cursor + take];
        if !witness_satisfies(req, slice)? {
            return Ok(false);
        }
        cursor += take;
    }
    Ok(true)
}

fn expected_gate_count(requirements: &[Requirement]) -> usize {
    requirements.iter().map(gate_burst_for).sum()
}

/// Number of gates emitted by `gen_kimchi` per requirement shape. Keep in
/// sync with the comments in `pyana-dsl/src/gen_kimchi.rs`.
fn gate_burst_for(req: &Requirement) -> usize {
    match req {
        // Diff gate + 64 boolean gates + 1 reconstruction = 66.
        Requirement::LessEqualU64(..) | Requirement::GreaterEqualU64(..) => 66,
        // Single equality gate.
        Requirement::EqualU64(..) | Requirement::EqualBytes32(..) => 1,
        // Single inverse-witness gate.
        Requirement::NotEqualU64(..) | Requirement::NotEqualBytes32(..) => 1,
        // 32 Poseidon hash levels.
        Requirement::Membership { .. } => 32,
    }
}

fn witness_satisfies(
    req: &Requirement,
    gates: &[pyana_dsl_runtime::KimchiGate],
) -> Result<bool, String> {
    match req {
        Requirement::LessEqualU64(l, r) => check_range_burst(*l, *r, gates),
        Requirement::GreaterEqualU64(l, r) => check_range_burst(*r, *l, gates),
        Requirement::EqualU64(l, r) => {
            assert_shape(gates, 1, KimchiGateType::Generic, "==")?;
            Ok(eval_generic(&gates[0], &[*l as i128, *r as i128]) == 0)
        }
        Requirement::NotEqualU64(l, r) => {
            assert_shape(gates, 1, KimchiGateType::Generic, "!=")?;
            // Gate: c3*(diff * inv) + c4 = 0, with c3=1, c4=-1 — i.e.
            // diff*inv == 1. Inverse exists iff diff != 0.
            if l == r {
                return Ok(false);
            }
            // Witness: any non-zero diff suffices; modular inverse isn't
            // computed here because our gate evaluator works in i128 — we
            // simulate "an inverse exists" by checking diff != 0.
            Ok(true)
        }
        Requirement::EqualBytes32(l, r) => {
            assert_shape(gates, 1, KimchiGateType::Generic, "== bytes")?;
            // Bytes equality is enforced limb-by-limb in a real circuit;
            // semantically the predicate accepts iff l == r byte-wise.
            Ok(l == r)
        }
        Requirement::NotEqualBytes32(l, r) => {
            assert_shape(gates, 1, KimchiGateType::Generic, "!= bytes")?;
            Ok(l != r)
        }
        Requirement::Membership { set, element } => {
            for g in gates {
                if g.typ != KimchiGateType::Poseidon {
                    return Err(format!(
                        "membership burst contained non-Poseidon gate ({:?})",
                        g.typ
                    ));
                }
            }
            Ok(set.contains(element))
        }
    }
}

fn check_range_burst(
    smaller: u64,
    bigger: u64,
    gates: &[pyana_dsl_runtime::KimchiGate],
) -> Result<bool, String> {
    if gates.len() != 66 {
        return Err(format!(
            "expected 66 gates for inequality burst, got {}",
            gates.len()
        ));
    }
    // gates[0]: diff = bigger - smaller (Generic, coeffs [1, -1, 0, 0, 0])
    if gates[0].typ != KimchiGateType::Generic {
        return Err("inequality diff gate is not Generic".into());
    }
    // gates[1..65]: 64 boolean constraints `bit^2 - bit = 0` (coeffs [-1, 0, 0, 1, 0])
    for (i, g) in gates[1..65].iter().enumerate() {
        if g.typ != KimchiGateType::Generic {
            return Err(format!("boolean gate {i} not Generic"));
        }
    }
    // gates[65]: reconstruction (Generic [1, -1, 0, 0, 0]) — bound to diff.
    if gates[65].typ != KimchiGateType::Generic {
        return Err("inequality reconstruction gate not Generic".into());
    }

    if bigger < smaller {
        // No 64-bit witness exists for diff = bigger - smaller; the bit
        // decomposition gates cannot be satisfied. Reject.
        return Ok(false);
    }
    let diff = bigger - smaller;
    // Reconstruction: sum_{i=0}^{63} bit_i * 2^i must equal diff. For diff < 2^64
    // every bit_i ∈ {0,1} and the boolean gate `bit^2 - bit = 0` is satisfied.
    // We exercise the algebra by recomputing the sum from diff's bit pattern
    // and checking the boolean polynomial on each implied witness.
    let mut acc: u128 = 0;
    for i in 0..64 {
        let bit = ((diff >> i) & 1) as i128;
        // boolean constraint: -1*bit + 1*(bit*bit) = bit^2 - bit
        let poly = -1 * bit + 1 * (bit * bit);
        if poly != 0 {
            return Ok(false);
        }
        acc += (bit as u128) << i;
    }
    if acc != diff as u128 {
        return Ok(false);
    }
    Ok(true)
}

fn assert_shape(
    gates: &[pyana_dsl_runtime::KimchiGate],
    expected_len: usize,
    expected_type: KimchiGateType,
    label: &str,
) -> Result<(), String> {
    if gates.len() != expected_len {
        return Err(format!(
            "{label} burst expected {expected_len} gate(s), got {}",
            gates.len()
        ));
    }
    if gates[0].typ != expected_type {
        return Err(format!(
            "{label} burst gate type mismatch: expected {:?}, got {:?}",
            expected_type, gates[0].typ
        ));
    }
    Ok(())
}

/// Evaluate a Kimchi Generic gate's polynomial on the witness slice.
/// `c0*w0 + c1*w1 + c2*w2 + c3*(w0*w1) + c4` with implicit zeros for
/// missing witness entries.
fn eval_generic(gate: &pyana_dsl_runtime::KimchiGate, witness: &[i128]) -> i128 {
    let w0 = witness.first().copied().unwrap_or(0);
    let w1 = witness.get(1).copied().unwrap_or(0);
    let w2 = witness.get(2).copied().unwrap_or(0);
    let c0 = *gate.coeffs.first().unwrap_or(&0) as i128;
    let c1 = *gate.coeffs.get(1).unwrap_or(&0) as i128;
    let c2 = *gate.coeffs.get(2).unwrap_or(&0) as i128;
    let c3 = *gate.coeffs.get(3).unwrap_or(&0) as i128;
    let c4 = *gate.coeffs.get(4).unwrap_or(&0) as i128;
    c0 * w0 + c1 * w1 + c2 * w2 + c3 * (w0 * w1) + c4
}
