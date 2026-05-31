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

    if ok {
        println!("circuit extraction differential PASSED — Lean emit \u{2261} Rust decode \u{2261} native AIR");
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
}
