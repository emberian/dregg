//! circuit_differential.rs — the CIRCUIT-EXTRACTION differential harness.
//!
//! The Lean-`emit`ted kernel-circuit wire string (the golden, produced by
//! `#eval Dregg2.Exec.CircuitEmit.kernelWire`) is decoded into a
//! `DecodedDescriptor` and shown to AGREE — by AIR-shape fingerprint — with the
//! Rust-native reference AIR. Equal fingerprints are the binding certificate:
//! "the AIR the backend runs IS the AIR Lean proved `Circuit.bridge` for."
//!
//! This is the third leg of the Lean→backend extraction bridge:
//!   1. Lean `emit` + `emit_faithful` (the wire form denotes the proved system);
//!   2. Rust `decode` (the wire form parses into the backend descriptor shape);
//!   3. fingerprint binding (decoded shape ≡ native shape) — HERE.
//!
//! Run with `cargo run --bin circuit_differential` in this crate. No Lean link.

#[path = "circuit_decode.rs"]
mod circuit_decode;

use circuit_decode::*;
use std::process::ExitCode;

/// The GOLDEN wire string, copied verbatim from
/// `#eval Dregg2.Exec.CircuitEmit.kernelWire`. If the Lean emitter changes, this
/// must be re-pasted; the differential then re-verifies the fingerprint binding.
const KERNEL_WIRE: &str = r#"{"name":"dregg-kernel-step-v1","trace_width":6,"constraints":[{"lhs":{"t":"var","v":1},"rhs":{"t":"var","v":0}},{"lhs":{"t":"var","v":2},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":4},"rhs":{"t":"add","l":{"t":"var","v":3},"r":{"t":"const","v":1}}}]}"#;

/// The GOLDEN Merkle wire string, copied verbatim from
/// `#eval Dregg2.Exec.CircuitEmit.merkleWire`. The `merkle_hash` + `transition`
/// constraints and the two `pi_binding_*` boundaries of the Merkle Poseidon2 AIR.
const MERKLE_WIRE: &str = r#"{"name":"dregg-merkle-poseidon2-v1","trace_width":6,"public_input_count":2,"constraints":[{"t":"merkle_hash","output_col":5,"current_col":0,"sib_cols":[1,2,3],"position_col":4},{"t":"transition","next_col":0,"local_col":5},{"t":"pi_binding_first","col":0,"pi_index":0},{"t":"pi_binding_last","col":5,"pi_index":1}]}"#;

/// The GOLDEN C1 position-validity polynomial wire, copied verbatim from
/// `#eval Dregg2.Exec.CircuitEmit.merkleC1Poly.toJson`. Expanded form of
/// `pos*(pos-1)*(pos-2)*(pos-3)` over the position column (col 4); signed
/// coefficients reduce into BabyBear (`-6 -> p-6`, etc.).
const MERKLE_C1_WIRE: &str = r#"{"t":"polynomial","terms":[{"coeff":1,"cols":[4,4,4,4]},{"coeff":-6,"cols":[4,4,4]},{"coeff":11,"cols":[4,4]},{"coeff":-6,"cols":[4]}]}"#;

fn hex(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

fn main() -> ExitCode {
    // 1. Decode the Lean-emitted wire form.
    let decoded = match decode(KERNEL_WIRE) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("DECODE FAILED: {e}");
            return ExitCode::FAILURE;
        }
    };
    println!(
        "decoded: name={:?} trace_width={} constraints={}",
        decoded.name,
        decoded.trace_width,
        decoded.constraints.len()
    );

    // Structural sanity: the four fullStepInv gates, six wires.
    let mut ok = true;
    if decoded.name != "dregg-kernel-step-v1" {
        eprintln!("  FAIL: unexpected AIR name {:?}", decoded.name);
        ok = false;
    }
    if decoded.trace_width != 6 {
        eprintln!("  FAIL: expected trace_width 6, got {}", decoded.trace_width);
        ok = false;
    }
    if decoded.constraints.len() != 4 {
        eprintln!(
            "  FAIL: expected 4 gates, got {}",
            decoded.constraints.len()
        );
        ok = false;
    }

    // Gate-by-gate structural check against the known kernelCircuit gates.
    let expected = vec![
        // conservation: var1 = var0
        DecodedConstraint {
            lhs: DecodedExpr::Var(1),
            rhs: DecodedExpr::Var(0),
        },
        // authority: var2 = 1
        DecodedConstraint {
            lhs: DecodedExpr::Var(2),
            rhs: DecodedExpr::Const(1),
        },
        // chain-link: var5 = 1
        DecodedConstraint {
            lhs: DecodedExpr::Var(5),
            rhs: DecodedExpr::Const(1),
        },
        // obs-advance: var4 = var3 + 1
        DecodedConstraint {
            lhs: DecodedExpr::Var(4),
            rhs: DecodedExpr::Add(
                Box::new(DecodedExpr::Var(3)),
                Box::new(DecodedExpr::Const(1)),
            ),
        },
    ];
    if decoded.constraints != expected {
        eprintln!("  FAIL: decoded gates differ from the expected kernelCircuit gates");
        eprintln!("    decoded:  {:?}", decoded.constraints);
        eprintln!("    expected: {expected:?}");
        ok = false;
    } else {
        println!("  gates match kernelCircuit (conservation, authority, chain-link, obs-advance)");
    }

    // 2. THE BINDING: AIR-shape fingerprint of the Lean-decoded circuit vs the
    //    Rust-native reference AIR shape.
    let lean_shape = kernel_air_shape_from_decoded(&decoded);
    let native_shape = kernel_air_shape_native();
    let fp_lean = fingerprint(&lean_shape);
    let fp_native = fingerprint(&native_shape);

    println!("  fingerprint(lean-decoded) = {}", hex(&fp_lean));
    println!("  fingerprint(rust-native)  = {}", hex(&fp_native));

    if fp_lean == fp_native {
        println!("  BINDING OK: decoded-Lean AIR fingerprint == Rust-native AIR fingerprint");
    } else {
        eprintln!("  FAIL: fingerprint MISMATCH — decoded AIR is NOT the native AIR");
        ok = false;
    }

    // 3. Tamper check: a perturbed descriptor MUST produce a different fingerprint
    //    (the binding is discriminating, not vacuous).
    let mut tampered = native_shape.clone();
    tampered.constraint_polynomial_count += 1;
    if fingerprint(&tampered) == fp_native {
        eprintln!("  FAIL: fingerprint did NOT change under tampering (vacuous binding)");
        ok = false;
    } else {
        println!("  tamper check OK: a perturbed AIR shape yields a different fingerprint");
    }

    // ========================================================================
    // 4. THE MERKLE BINDING — the FULL ConstraintExpr wire (PART II/III).
    //    Decode the Lean-emitted Merkle wire (merkle_hash + transition + two
    //    pi_binding_* boundaries) plus the separately-emitted C1 polynomial,
    //    rebuild the Merkle AIR shape, and fingerprint-bind it to the native
    //    merkle_poseidon2_descriptor() shape.
    // ========================================================================
    println!();
    println!("== Merkle (full ConstraintExpr) binding ==");

    let merkle = match decode_full(MERKLE_WIRE) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("  MERKLE DECODE FAILED: {e}");
            return ExitCode::FAILURE;
        }
    };
    let c1 = match decode_constraint_expr(MERKLE_C1_WIRE) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("  MERKLE C1 DECODE FAILED: {e}");
            return ExitCode::FAILURE;
        }
    };
    println!(
        "  decoded: name={:?} trace_width={} pi_count={} constraints={} boundaries={}",
        merkle.name,
        merkle.trace_width,
        merkle.public_input_count,
        merkle.constraints.len(),
        merkle.boundaries.len()
    );

    // Structural checks against the known merkle_poseidon2_descriptor wire.
    if merkle.name != "dregg-merkle-poseidon2-v1" {
        eprintln!("  FAIL: unexpected Merkle AIR name {:?}", merkle.name);
        ok = false;
    }
    if merkle.trace_width != 6 {
        eprintln!("  FAIL: expected Merkle trace_width 6, got {}", merkle.trace_width);
        ok = false;
    }
    // The wire carries C2 (MerkleHash) + C3 (Transition) as constraints; C1 is
    // the separately-emitted polynomial.
    let expected_merkle_constraints = vec![
        DecodedConstraintExpr::MerkleHash {
            output_col: 5,
            current_col: 0,
            sib_cols: [1, 2, 3],
            position_col: 4,
        },
        DecodedConstraintExpr::Transition {
            next_col: 0,
            local_col: 5,
        },
    ];
    if merkle.constraints != expected_merkle_constraints {
        eprintln!("  FAIL: decoded Merkle constraints differ from native (C2 MerkleHash, C3 Transition)");
        eprintln!("    decoded:  {:?}", merkle.constraints);
        ok = false;
    } else {
        println!("  constraints match native (C2 MerkleHash, C3 Transition)");
    }
    let expected_merkle_boundaries = vec![
        DecodedBoundary { row: DecodedBoundaryRow::First, col: 0, pi_index: 0 },
        DecodedBoundary { row: DecodedBoundaryRow::Last, col: 5, pi_index: 1 },
    ];
    if merkle.boundaries != expected_merkle_boundaries {
        eprintln!("  FAIL: decoded Merkle boundaries differ from native (PiBinding First/Last)");
        eprintln!("    decoded:  {:?}", merkle.boundaries);
        ok = false;
    } else {
        println!("  boundaries match native (PiBinding First[leaf], Last[root])");
    }

    // Verify the C1 polynomial decoded with the signed->BabyBear coeff reduction
    // (`-6 -> p-6`) exactly as descriptors.rs encodes it.
    let expected_c1 = DecodedConstraintExpr::Polynomial {
        terms: vec![
            DecodedPolyTerm { coeff: 1, col_indices: vec![4, 4, 4, 4] },
            DecodedPolyTerm { coeff: BABYBEAR_P - 6, col_indices: vec![4, 4, 4] },
            DecodedPolyTerm { coeff: 11, col_indices: vec![4, 4] },
            DecodedPolyTerm { coeff: BABYBEAR_P - 6, col_indices: vec![4] },
        ],
    };
    if c1 != expected_c1 {
        eprintln!("  FAIL: decoded C1 polynomial differs from native (signed->BabyBear reduction)");
        eprintln!("    decoded:  {c1:?}");
        ok = false;
    } else {
        println!("  C1 polynomial matches native (pos*(pos-1)*(pos-2)*(pos-3), -6 -> p-6)");
    }

    // THE MERKLE BINDING: fingerprint of the decoded-Lean Merkle AIR vs native.
    let merkle_lean_shape = merkle_air_shape_from_decoded(&merkle, &c1);
    let merkle_native_shape = merkle_air_shape_native();
    let fp_m_lean = fingerprint(&merkle_lean_shape);
    let fp_m_native = fingerprint(&merkle_native_shape);
    println!("  fingerprint(lean-decoded merkle) = {}", hex(&fp_m_lean));
    println!("  fingerprint(rust-native merkle)  = {}", hex(&fp_m_native));
    if fp_m_lean == fp_m_native {
        println!("  MERKLE BINDING OK: decoded-Lean Merkle AIR fingerprint == native merkle_poseidon2 fingerprint");
    } else {
        eprintln!("  FAIL: Merkle fingerprint MISMATCH — decoded AIR is NOT merkle_poseidon2_descriptor()");
        ok = false;
    }

    // Merkle tamper check (discriminating binding).
    let mut m_tampered = merkle_native_shape.clone();
    m_tampered.boundary_constraint_count += 1;
    if fingerprint(&m_tampered) == fp_m_native {
        eprintln!("  FAIL: Merkle fingerprint did NOT change under tampering (vacuous binding)");
        ok = false;
    } else {
        println!("  Merkle tamper check OK: a perturbed AIR shape yields a different fingerprint");
    }

    if ok {
        println!();
        println!("circuit extraction differential PASSED — Lean emit \u{2261} Rust decode \u{2261} native AIR (kernel + Merkle)");
        ExitCode::SUCCESS
    } else {
        eprintln!("circuit extraction differential FAILED");
        ExitCode::FAILURE
    }
}

// ============================================================================
// Self-checks: decoder round-trip + fingerprint determinism, and a faithfulness
// witness that the fingerprint reproduction matches air_descriptor.rs's recipe
// on a known vector.
// ============================================================================

#[cfg(test)]
mod tests {
    use super::circuit_decode::*;

    const WIRE: &str = super::KERNEL_WIRE;

    #[test]
    fn decodes_kernel_wire() {
        let d = decode(WIRE).expect("decode");
        assert_eq!(d.name, "dregg-kernel-step-v1");
        assert_eq!(d.trace_width, 6);
        assert_eq!(d.constraints.len(), 4);
    }

    #[test]
    fn fingerprint_binding_holds() {
        let d = decode(WIRE).unwrap();
        let lean = fingerprint(&kernel_air_shape_from_decoded(&d));
        let native = fingerprint(&kernel_air_shape_native());
        assert_eq!(lean, native, "decoded-Lean AIR must bind to native AIR");
    }

    #[test]
    fn fingerprint_is_discriminating() {
        let mut a = kernel_air_shape_native();
        let base = fingerprint(&a);
        a.max_degree += 1;
        assert_ne!(fingerprint(&a), base);
    }

    #[test]
    fn decode_rejects_garbage() {
        assert!(decode("{\"name\":\"x\"}").is_err());
        assert!(decode("not json").is_err());
    }

    // ---- Merkle (full ConstraintExpr) wire ----

    const MERKLE: &str = super::MERKLE_WIRE;
    const C1: &str = super::MERKLE_C1_WIRE;

    #[test]
    fn decodes_merkle_wire() {
        let m = decode_full(MERKLE).expect("merkle decode");
        assert_eq!(m.name, "dregg-merkle-poseidon2-v1");
        assert_eq!(m.trace_width, 6);
        assert_eq!(m.public_input_count, 2);
        assert_eq!(m.constraints.len(), 2); // MerkleHash + Transition
        assert_eq!(m.boundaries.len(), 2); // PiBinding First + Last
        assert_eq!(
            m.constraints[0],
            DecodedConstraintExpr::MerkleHash {
                output_col: 5,
                current_col: 0,
                sib_cols: [1, 2, 3],
                position_col: 4,
            }
        );
        assert_eq!(
            m.constraints[1],
            DecodedConstraintExpr::Transition { next_col: 0, local_col: 5 }
        );
        assert_eq!(m.boundaries[0].row, DecodedBoundaryRow::First);
        assert_eq!(m.boundaries[1].row, DecodedBoundaryRow::Last);
    }

    #[test]
    fn decodes_c1_polynomial_with_babybear_reduction() {
        let c1 = decode_constraint_expr(C1).expect("c1 decode");
        // -6 must reduce to p-6, 11 stays 11, 1 stays 1.
        let expected = DecodedConstraintExpr::Polynomial {
            terms: vec![
                DecodedPolyTerm { coeff: 1, col_indices: vec![4, 4, 4, 4] },
                DecodedPolyTerm { coeff: BABYBEAR_P - 6, col_indices: vec![4, 4, 4] },
                DecodedPolyTerm { coeff: 11, col_indices: vec![4, 4] },
                DecodedPolyTerm { coeff: BABYBEAR_P - 6, col_indices: vec![4] },
            ],
        };
        assert_eq!(c1, expected);
        assert_eq!(c1.degree(), 4); // deepest term has 4 column factors
    }

    #[test]
    fn merkle_fingerprint_binding_holds() {
        let m = decode_full(MERKLE).unwrap();
        let c1 = decode_constraint_expr(C1).unwrap();
        let lean = fingerprint(&merkle_air_shape_from_decoded(&m, &c1));
        let native = fingerprint(&merkle_air_shape_native());
        assert_eq!(lean, native, "decoded-Lean Merkle AIR must bind to native");
    }

    #[test]
    fn merkle_fingerprint_is_discriminating() {
        let mut a = merkle_air_shape_native();
        let base = fingerprint(&a);
        a.boundary_constraint_count += 1;
        assert_ne!(fingerprint(&a), base);
    }

    #[test]
    fn decode_full_round_trips_each_algebraic_form() {
        // Each algebraic tag decodes to its column-indexed ConstraintExpr.
        let cases: &[(&str, DecodedConstraintExpr)] = &[
            (
                r#"{"t":"equality","col_a":3,"col_b":7}"#,
                DecodedConstraintExpr::Equality { col_a: 3, col_b: 7 },
            ),
            (
                r#"{"t":"multiplication","a":1,"b":2,"output":4}"#,
                DecodedConstraintExpr::Multiplication { a: 1, b: 2, output: 4 },
            ),
            (
                r#"{"t":"binary","col":5}"#,
                DecodedConstraintExpr::Binary { col: 5 },
            ),
            (
                r#"{"t":"pi_binding","col":2,"pi_index":1}"#,
                DecodedConstraintExpr::PiBinding { col: 2, pi_index: 1 },
            ),
            (
                r#"{"t":"conditional_nonzero","selector_col":1,"value_col":2,"inverse_col":3}"#,
                DecodedConstraintExpr::ConditionalNonzero {
                    selector_col: 1,
                    value_col: 2,
                    inverse_col: 3,
                },
            ),
            (
                r#"{"t":"at_least_one","flag_cols":[0,1,2]}"#,
                DecodedConstraintExpr::AtLeastOne { flag_cols: vec![0, 1, 2] },
            ),
        ];
        for (wire, expected) in cases {
            let got = decode_constraint_expr(wire).expect("decode algebraic");
            assert_eq!(&got, expected, "wire {wire}");
        }
    }

    #[test]
    fn decode_full_handles_recursive_gated_forms() {
        // gated / inverted_gated / squared recurse into `inner`.
        let gated = decode_constraint_expr(
            r#"{"t":"gated","selector_col":2,"inner":{"t":"binary","col":3}}"#,
        )
        .unwrap();
        assert_eq!(
            gated,
            DecodedConstraintExpr::Gated {
                selector_col: 2,
                inner: Box::new(DecodedConstraintExpr::Binary { col: 3 }),
            }
        );
        assert_eq!(gated.degree(), 1 + 2); // gating adds 1 to Binary's degree 2

        let inv = decode_constraint_expr(
            r#"{"t":"inverted_gated","selector_col":0,"inner":{"t":"equality","col_a":1,"col_b":2}}"#,
        )
        .unwrap();
        assert_eq!(
            inv,
            DecodedConstraintExpr::InvertedGated {
                selector_col: 0,
                inner: Box::new(DecodedConstraintExpr::Equality { col_a: 1, col_b: 2 }),
            }
        );

        let sq = decode_constraint_expr(
            r#"{"t":"squared","inner":{"t":"equality","col_a":1,"col_b":2}}"#,
        )
        .unwrap();
        assert_eq!(
            sq,
            DecodedConstraintExpr::Squared {
                inner: Box::new(DecodedConstraintExpr::Equality { col_a: 1, col_b: 2 }),
            }
        );
        assert_eq!(sq.degree(), 2); // 2 * Equality(1)
    }

    #[test]
    fn decode_full_rejects_garbage_and_nested_boundary() {
        assert!(decode_full("not json").is_err());
        assert!(decode_constraint_expr(r#"{"t":"unknown_tag","x":1}"#).is_err());
        // A boundary tag may not nest inside a gated inner.
        assert!(decode_constraint_expr(
            r#"{"t":"gated","selector_col":0,"inner":{"t":"pi_binding_first","col":0,"pi_index":0}}"#
        )
        .is_err());
    }
}
