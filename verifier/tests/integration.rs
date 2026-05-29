//! Integration tests for `dregg-verifier`.
//!
//! These tests exercise the full verification path:
//! 1. Generate a real Effect VM STARK proof using `dregg-circuit`.
//! 2. Serialise it to bytes (as the prover would write to disk).
//! 3. Call `dregg_verifier::verify_effect_vm_proof` with the bytes — simulating
//!    the independent verifier reading from disk.
//! 4. Assert accept / reject as appropriate.
//!
//! The verifier function is called directly here (faster than spawning a subprocess),
//! but the binary integration test at the bottom exercises the actual subprocess too.

use dregg_circuit::{
    BabyBear, CellState, Effect, EffectVmAir,
    effect_vm::generate_effect_vm_trace,
    stark::{self, proof_to_bytes},
};
use dregg_verifier::{
    AUTO_DETECT_VK_HASH, EFFECT_VM_VK_HASH_HEX, exit_code, verify_effect_vm_proof,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn make_proof_and_pi(balance: u64, effects: &[Effect]) -> (Vec<u8>, Vec<u32>) {
    let state = CellState::new(balance, 0);
    let (trace, public_inputs) = generate_effect_vm_trace(&state, effects);
    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &public_inputs);
    let proof_bytes = proof_to_bytes(&proof);
    let pi_u32: Vec<u32> = public_inputs.iter().map(|bb| bb.as_u32()).collect();
    (proof_bytes, pi_u32)
}

// ---------------------------------------------------------------------------
// Test: known-good proof — accept
// ---------------------------------------------------------------------------

#[test]
fn test_verify_known_good_proof_accepted() {
    let (proof_bytes, pi_u32) = make_proof_and_pi(
        1000,
        &[Effect::Transfer {
            amount: 100,
            direction: 1,
        }],
    );

    let (output, code) = verify_effect_vm_proof(&proof_bytes, &pi_u32, AUTO_DETECT_VK_HASH);
    assert_eq!(
        code,
        exit_code::VERIFIED,
        "expected accepted, got: {:?}",
        output
    );
    assert!(output.verified, "output.verified must be true");
}

// ---------------------------------------------------------------------------
// Test: tampered proof bytes — reject
// ---------------------------------------------------------------------------

#[test]
fn test_verify_tampered_proof_rejected() {
    let (mut proof_bytes, pi_u32) = make_proof_and_pi(
        500,
        &[Effect::Transfer {
            amount: 50,
            direction: 0,
        }],
    );

    // Flip a byte deep in the proof body (past the 5-byte header and commitments).
    // Byte 100 is safely inside the FRI commitment / query region for any
    // non-trivial proof.
    let tamper_offset = 100.min(proof_bytes.len() - 1);
    proof_bytes[tamper_offset] ^= 0xFF;

    let (output, code) = verify_effect_vm_proof(&proof_bytes, &pi_u32, AUTO_DETECT_VK_HASH);
    // A tampered proof must either be rejected (exit 1) or cause an error (exit 2).
    // Both are acceptable; what must NOT happen is exit 0 (verified).
    assert_ne!(
        code,
        exit_code::VERIFIED,
        "tampered proof must not verify; got: {:?}",
        output
    );
    assert!(
        !output.verified,
        "output.verified must be false for tampered proof"
    );
}

// ---------------------------------------------------------------------------
// Test: wrong public inputs — reject
// ---------------------------------------------------------------------------

#[test]
fn test_verify_wrong_pi_rejected() {
    let (proof_bytes, mut pi_u32) = make_proof_and_pi(
        2000,
        &[Effect::Transfer {
            amount: 200,
            direction: 1,
        }],
    );

    // Corrupt the first public input (old_commit[0]).
    if !pi_u32.is_empty() {
        pi_u32[0] ^= 0xDEAD_BEEF;
    }

    let (output, code) = verify_effect_vm_proof(&proof_bytes, &pi_u32, AUTO_DETECT_VK_HASH);
    assert_ne!(
        code,
        exit_code::VERIFIED,
        "wrong PI must not verify; got: {:?}",
        output
    );
    assert!(!output.verified);
}

// ---------------------------------------------------------------------------
// Test: unknown VK hash — error (not rejected, not verified)
// ---------------------------------------------------------------------------

#[test]
fn test_unknown_vk_hash_returns_error() {
    let (proof_bytes, pi_u32) = make_proof_and_pi(100, &[Effect::NoOp]);

    let unknown_hash = "0000000000000000000000000000000000000000000000000000000000000000";
    let (output, code) = verify_effect_vm_proof(&proof_bytes, &pi_u32, unknown_hash);
    assert_eq!(
        code,
        exit_code::ERROR,
        "unknown VK should be exit 2; got: {:?}",
        output
    );
    assert!(!output.verified);
}

// ---------------------------------------------------------------------------
// Test: invalid proof bytes — error
// ---------------------------------------------------------------------------

#[test]
fn test_garbage_proof_bytes_returns_error() {
    let garbage = b"not a real proof at all";
    let pi_u32: Vec<u32> = vec![0u32; 25];
    let (output, code) = verify_effect_vm_proof(garbage, &pi_u32, AUTO_DETECT_VK_HASH);
    assert_eq!(
        code,
        exit_code::ERROR,
        "garbage bytes should be exit 2; got: {:?}",
        output
    );
    assert!(!output.verified);
}

// ---------------------------------------------------------------------------
// Test: VK hash resolution — known canonical hash matches
// ---------------------------------------------------------------------------

#[test]
fn test_canonical_vk_hash_accepted() {
    let (proof_bytes, pi_u32) = make_proof_and_pi(
        750,
        &[Effect::Transfer {
            amount: 75,
            direction: 1,
        }],
    );

    // Using the canonical VK hash instead of "auto".
    let (output, code) = verify_effect_vm_proof(&proof_bytes, &pi_u32, EFFECT_VM_VK_HASH_HEX);
    assert_eq!(
        code,
        exit_code::VERIFIED,
        "canonical VK hash should work; got: {:?}",
        output
    );
    assert!(output.verified);
}

// ---------------------------------------------------------------------------
// Test: multi-effect turn — accept
// ---------------------------------------------------------------------------

#[test]
fn test_verify_multi_effect_turn_accepted() {
    let (proof_bytes, pi_u32) = make_proof_and_pi(
        5000,
        &[
            Effect::Transfer {
                amount: 100,
                direction: 1,
            },
            Effect::SetField {
                field_idx: 0,
                value: BabyBear::new(42),
            },
            Effect::GrantCapability {
                cap_entry: [BabyBear::new(0xCAFE); 8],
            },
        ],
    );

    let (output, code) = verify_effect_vm_proof(&proof_bytes, &pi_u32, AUTO_DETECT_VK_HASH);
    assert_eq!(
        code,
        exit_code::VERIFIED,
        "multi-effect turn should verify; got: {:?}",
        output
    );
    assert!(output.verified);
}

// ---------------------------------------------------------------------------
// Binary subprocess tests (file-args + stdin modes, plus negative cases)
// ---------------------------------------------------------------------------

#[test]
fn test_binary_cli() {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let binary = env!("CARGO_BIN_EXE_dregg-verifier");

    // ---- 1. File-arg mode (happy path) ----
    let (proof_bytes, pi_u32) = make_proof_and_pi(
        300,
        &[Effect::Transfer {
            amount: 30,
            direction: 0,
        }],
    );
    let pi_json = serde_json::to_string(&pi_u32).expect("pi serialisation");

    let mut proof_file = tempfile::NamedTempFile::new().expect("tempfile");
    proof_file.write_all(&proof_bytes).expect("write proof");
    proof_file.flush().expect("flush proof");

    let mut pi_file = tempfile::NamedTempFile::new().expect("tempfile");
    pi_file.write_all(pi_json.as_bytes()).expect("write pi");
    pi_file.flush().expect("flush pi");

    let output = Command::new(binary)
        .arg("--proof")
        .arg(proof_file.path())
        .arg("--pi")
        .arg(pi_file.path())
        .arg("--vk-hash")
        .arg(AUTO_DETECT_VK_HASH)
        .output()
        .expect("failed to run binary");

    assert_eq!(
        output.status.code(),
        Some(0),
        "binary should exit 0 for good proof; stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let result: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("valid JSON output");
    assert_eq!(result["verified"], true, "expected verified=true");

    // ---- 2. Stdin JSON mode (happy path) ----
    let (proof_bytes2, pi_u32_2) = make_proof_and_pi(
        150,
        &[Effect::Transfer {
            amount: 15,
            direction: 1,
        }],
    );
    let request = serde_json::json!({
        "proof_hex": hex::encode(&proof_bytes2),
        "public_inputs": pi_u32_2,
        "vk_hash": AUTO_DETECT_VK_HASH,
    });
    let request_json = serde_json::to_string(&request).expect("serialise request");

    let mut child = Command::new(binary)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn binary");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(request_json.as_bytes())
        .expect("write stdin");
    let out = child.wait_with_output().expect("wait");

    assert_eq!(
        out.status.code(),
        Some(0),
        "stdin JSON mode should exit 0; stdout={}, stderr={}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let result2: serde_json::Value =
        serde_json::from_slice(&out.stdout).expect("valid JSON output");
    assert_eq!(result2["verified"], true);

    // ---- 3. Negative: missing required args ----
    let bad_output = Command::new(binary)
        .output()
        .expect("run binary with no args");
    assert_ne!(
        bad_output.status.code(),
        Some(0),
        "binary must fail when invoked without arguments"
    );

    // ---- 4. Negative: invalid stdin JSON ----
    let mut bad_child = Command::new(binary)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn binary");
    bad_child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(b"not-valid-json")
        .expect("write stdin");
    let bad_out = bad_child.wait_with_output().expect("wait");
    assert_ne!(
        bad_out.status.code(),
        Some(0),
        "binary must reject malformed stdin JSON"
    );
}
