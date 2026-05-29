//! Adversarial conservation-proof verification (mirrors the WASM binding).
//!
//! `wasm/src/privacy.rs::verify_conservation_proof` was previously a stub that
//! always returned `{ valid: false, not_implemented: true }`. The
//! effect-vm-hash-truncation lane (2026-05-28) replaced it with a REAL check
//! that decodes the hex commitments + Schnorr excess proof and calls the
//! canonical `dregg_cell::value_commitment::verify_conservation`.
//!
//! The WASM fn returns a `JsValue` (needs a JS runtime), so these host tests
//! exercise the EXACT decode→verify flow the binding wraps: hex-encode the
//! `ValueCommitment::to_bytes` outputs and the `ConservationProof` fields,
//! decode them back the way the binding does, and assert
//!   (a) a CONSERVING set (Σ inputs == Σ outputs in value) is ACCEPTED, and
//!   (b) a NON-CONSERVING set (Σ in ≠ Σ out) is REJECTED.
//!
//! These mirror `wasm/src/privacy.rs::audit_tests` (which are
//! `#[cfg(target_arch = "wasm32")]`-gated and so don't run on the host CI).

use crate::Invariant;

/// Marker for documentation / tooling parity with the other invariants.
pub struct ConservationProofWasm;

impl Invariant for ConservationProofWasm {
    const NAME: &'static str = "conservation_proof_wasm";
    const DESCRIPTION: &'static str = "the WASM verify_conservation_proof binding accepts a balanced Pedersen \
         transaction and rejects an unbalanced one (real Schnorr excess check)";
}

#[cfg(test)]
mod tests {
    use curve25519_dalek::scalar::Scalar;
    use dregg_cell::value_commitment::{
        ConservationProof, ValueCommitment, ValueCommitmentBytes, prove_conservation,
        verify_conservation,
    };

    fn test_scalar(seed: u8) -> Scalar {
        let mut bytes = [0u8; 64];
        bytes[0] = seed;
        bytes[1] = seed.wrapping_mul(37);
        bytes[2] = seed.wrapping_add(101);
        Scalar::from_bytes_mod_order_wide(&bytes)
    }

    fn hex_encode(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    // Re-implements the binding's hex→[u8;32] decode so the test walks the
    // same path WASM does.
    fn decode_hex_32(hex: &str) -> [u8; 32] {
        assert_eq!(hex.len(), 64, "commitment must be 64 hex chars");
        let mut out = [0u8; 32];
        for i in 0..32 {
            out[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).expect("valid hex");
        }
        out
    }

    /// Round-trip a slice of commitments through hex (as the WASM caller would)
    /// and decode them back into real Ristretto `ValueCommitment`s.
    fn roundtrip(commitments: &[ValueCommitment]) -> Vec<ValueCommitment> {
        commitments
            .iter()
            .map(|c| {
                let hex = hex_encode(&c.to_bytes().0);
                let bytes = decode_hex_32(&hex);
                ValueCommitment::from_bytes(&ValueCommitmentBytes(bytes))
                    .expect("valid commitment round-trips")
            })
            .collect()
    }

    /// Round-trip a proof through hex and back (as the binding does).
    fn roundtrip_proof(p: &ConservationProof) -> ConservationProof {
        ConservationProof {
            excess_commitment: decode_hex_32(&hex_encode(&p.excess_commitment)),
            nonce_commitment: decode_hex_32(&hex_encode(&p.nonce_commitment)),
            response: decode_hex_32(&hex_encode(&p.response)),
        }
    }

    #[test]
    fn adversarial_conserving_set_is_accepted() {
        // 2 inputs (300, 500) -> 2 outputs (450, 350). Σ in == Σ out == 800.
        let r_in1 = test_scalar(10);
        let r_in2 = test_scalar(11);
        let r_out1 = test_scalar(12);
        let r_out2 = test_scalar(13);

        let inputs = vec![
            ValueCommitment::commit(300, &r_in1),
            ValueCommitment::commit(500, &r_in2),
        ];
        let outputs = vec![
            ValueCommitment::commit(450, &r_out1),
            ValueCommitment::commit(350, &r_out2),
        ];
        let excess = (r_in1 + r_in2) - (r_out1 + r_out2);
        let message = b"conserve-tx";

        let proof = prove_conservation(&inputs, &outputs, &excess, message);

        // Walk the binding's decode path.
        let inputs_rt = roundtrip(&inputs);
        let outputs_rt = roundtrip(&outputs);
        let proof_rt = roundtrip_proof(&proof);

        assert!(
            verify_conservation(&inputs_rt, &outputs_rt, &proof_rt, message).is_ok(),
            "a balanced transaction must verify as conserving",
        );
    }

    #[test]
    fn adversarial_nonconserving_set_is_rejected() {
        // Inputs sum to 100, outputs sum to 200 — value is NOT conserved.
        // Even with the honest blinding excess, the excess point carries a
        // non-zero V-component, so the Schnorr check fails closed.
        let r_in = test_scalar(20);
        let r_out = test_scalar(21);

        let inputs = vec![ValueCommitment::commit(100, &r_in)];
        let outputs = vec![ValueCommitment::commit(200, &r_out)];
        let excess = r_in - r_out; // honest blinding diff; values still imbalanced
        let message = b"inflate-tx";

        let proof = prove_conservation(&inputs, &outputs, &excess, message);

        let inputs_rt = roundtrip(&inputs);
        let outputs_rt = roundtrip(&outputs);
        let proof_rt = roundtrip_proof(&proof);

        assert!(
            verify_conservation(&inputs_rt, &outputs_rt, &proof_rt, message).is_err(),
            "an unbalanced (inflating) transaction MUST be rejected",
        );
    }

    #[test]
    fn adversarial_wrong_message_binding_is_rejected() {
        // A valid conserving proof bound to message A must NOT verify under a
        // different message B (replay / context-confusion protection).
        let r_in = test_scalar(30);
        let r_out = test_scalar(31);
        let inputs = vec![ValueCommitment::commit(777, &r_in)];
        let outputs = vec![ValueCommitment::commit(777, &r_out)];
        let excess = r_in - r_out;

        let proof = prove_conservation(&inputs, &outputs, &excess, b"context-A");

        let inputs_rt = roundtrip(&inputs);
        let outputs_rt = roundtrip(&outputs);
        let proof_rt = roundtrip_proof(&proof);

        assert!(
            verify_conservation(&inputs_rt, &outputs_rt, &proof_rt, b"context-A").is_ok(),
            "the proof must verify under its own binding message",
        );
        assert!(
            verify_conservation(&inputs_rt, &outputs_rt, &proof_rt, b"context-B").is_err(),
            "the proof must NOT verify under a different binding message",
        );
    }

    #[test]
    fn adversarial_malformed_commitment_fails_closed() {
        // 0xFF..FF is not a valid compressed Ristretto point — the binding's
        // decode step must fail closed rather than accept.
        let bad = ValueCommitmentBytes([0xFFu8; 32]);
        assert!(
            ValueCommitment::from_bytes(&bad).is_none(),
            "a malformed commitment must fail decoding (fail-closed)",
        );
    }
}
