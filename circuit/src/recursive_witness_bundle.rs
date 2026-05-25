//! Recursive witness-bundle compression — Golden Vision substrate v1.
//!
//! This module is the bridge between
//! [`turn::WitnessedReceipt`]'s Silver Vision form (carry full trace data;
//! verifier re-runs the AIR) and the Golden Vision form (carry one small
//! recursive STARK proof attesting that the AIR accepted).
//!
//! ## Architecture
//!
//! ```text
//! Silver Vision (scope-2 today):
//!   WitnessBundle { trace_rows: Vec<Vec<u32>> }  (hundreds of KB)
//!     ↓ verifier re-runs EffectVmAir::eval_constraints  (O(trace_len))
//!
//! Golden Vision (this module):
//!   WitnessBundle { recursive_proof: Some(RecursiveProofVariant {
//!       proof_bytes,             // ~few KB
//!       public_inputs,
//!       recursive_vk_hash,
//!   }) }
//!     ↓ verifier verifies one recursive STARK proof  (O(1) in trace_len)
//! ```
//!
//! Both modes attest the same fact: "the trace satisfied the AIR's
//! constraints against this public-input vector." The Golden form trades
//! one-time prover cost (~seconds, building the recursive proof) for
//! asymptotic verifier-cost savings that compound across long chains.
//!
//! ## Producer / verifier surfaces
//!
//! - [`RecursiveProofProducer::produce`] — bridge from
//!   Silver-form (trace + PI) to Golden-form (recursive proof bytes +
//!   PI + VK hash). Run by the prover side at WR construction time when
//!   `recursive_compress` is requested.
//! - [`verify_recursive_proof_variant`] — verifier-side dispatch: looks
//!   up the `recursive_vk_hash` in a registry, then runs
//!   [`crate::plonky3_recursion_impl::recursive::verify_recursive_layer_bytes`]
//!   on the proof bytes.
//!
//! ## Inner AIR choice (substrate honesty)
//!
//! The recursive proof's inner AIR is
//! [`crate::effect_vm_p3_air::EffectVmShapeAir`] — the p3-air-compatible
//! "Effect VM shape" AIR introduced in Block 2 of the Golden Vision
//! recursion lane. It mirrors the real `EffectVmAir`'s column count
//! (`EFFECT_VM_WIDTH = 105`), public-input count (`pi::BASE_COUNT`), and
//! a structural subset of the constraints (selector booleanity, sum-to-one,
//! NoOp passthrough, Transfer balance delta, chain continuity, boundary
//! PI binding).
//!
//! It is **not** a soundness equivalent of the full `EffectVmAir`. A
//! trace accepted by `EffectVmShapeAir` would not necessarily satisfy
//! the full Effect VM constraint set. The honest framing: a verifier
//! that accepts a Golden Vision proof has learned that the trace
//! satisfies the structural subset; the Silver Vision (inline trace
//! replay) path still exists in the same `WitnessBundle` and is the
//! authoritative scope-2 check until `EffectVmShapeAir`'s `eval` grows to
//! cover every selector branch of `EffectVmAir::eval_constraints`.
//!
//! Growing that coverage is a mechanical translation task —
//! `effect_vm_p3_air.rs::eval` already documents the pattern. When that
//! coverage closes, the Golden Vision path stands on its own; the inline
//! trace becomes a redundant scope-2 backup.
//!
//! ## VK hash — VK v2 layered encoding
//!
//! The `recursive_vk_hash` field of a [`RecursiveProofVariant`] follows
//! the VK v2 layered encoding from `pyana_cell::vk_v2`:
//!
//! ```text
//! recursive_vk_hash = canonical_vk_v2({
//!     program_bytes:       b"pyana-effect-vm-recursive-v1",
//!     air_fingerprint:     fingerprint(EFFECT_VM_AIR_DESCRIPTOR),
//!     verifier_fingerprint: SourceHash(verifier_source_hash),
//!     proving_system_id:   Plonky3BabyBearFri { p3_rev },
//! })
//! ```
//!
//! Where:
//! - `program_bytes` is the stable domain string for "the recursive Effect
//!   VM verifier" — disjoint from cell-program VK hashes.
//! - `air_fingerprint` pins the Effect VM AIR's shape; mutating the AIR
//!   changes the hash and invalidates old recursive proofs.
//! - `verifier_fingerprint` is the source hash of this module file (set
//!   at registry-registration time); pins the verifier's code.
//! - `proving_system_id` carries the Plonky3 git rev so a rev bump
//!   invalidates old recursive proofs (which were produced against the
//!   old FRI configuration).
//!
//! See `cell/src/vk_v2.rs` for the canonical encoder.

#![cfg(feature = "recursion")]

use crate::field::BabyBear;

// ---------------------------------------------------------------------------
// VK v2 layered hash
// ---------------------------------------------------------------------------

/// Stable program-bytes identifier for the recursive Effect VM verifier.
///
/// Used as the `program_bytes` component of the VK v2 layered hash for
/// recursive proofs. Disjoint from cell-program VK hashes (which use
/// `postcard(CellProgram)` bytes) and from custom-predicate VK hashes.
pub const RECURSIVE_VK_PROGRAM_BYTES: &[u8] = b"pyana-effect-vm-recursive-v1";

/// Plonky3 git revision the recursion config was built against.
///
/// Pinned to the workspace `p3-recursion` rev from `Cargo.toml`. A bump
/// must be mirrored here, since the proving-system identifier is part of
/// the recursive VK hash — bumping the rev without bumping this string
/// would silently let old recursive proofs verify against new code.
pub const RECURSION_P3_REV: &str = "c14b5fc079af18d7f3ba3f3586f173bd166c7cd4";

/// Returns the verifier-source fingerprint used in the recursive VK
/// hash. Deterministic: BLAKE3 of a stable string identifying this
/// module's verifier surface.
///
/// In a fuller VK v2 rollout this would be the git-blob-hash of this
/// source file pinned at registration time; we use a stable canonical-
/// bytes derivation under "pyana-recursive-witness-bundle-verifier-v1"
/// so the hash is deterministic without a build-time hook. When this
/// module's verifier surface changes meaningfully, bump the suffix to
/// invalidate old VK hashes.
pub fn recursive_verifier_source_hash() -> [u8; 32] {
    *blake3::hash(b"pyana-recursive-witness-bundle-verifier-v1").as_bytes()
}

/// Compute the canonical VK v2 layered hash for the recursive Effect VM
/// verifier.
///
/// Mirrors `pyana_cell::vk_v2::canonical_vk_v2`'s encoding inline so this
/// crate does not depend on `pyana-cell` (which would create a cycle:
/// `pyana-cell` depends on `pyana-circuit`). The encoding is byte-identical
/// to a call through `pyana_cell::vk_v2::canonical_vk_v2` with the
/// equivalent `VkComponents`.
pub fn compute_recursive_vk_hash() -> [u8; 32] {
    let air_fp = crate::air_descriptor::fingerprint(&crate::effect_vm::AIR_DESCRIPTOR);
    let verifier_fp = recursive_verifier_source_hash();

    // BLAKE3 keyed under "pyana-vk-v2" — same domain as
    // `pyana_cell::vk_v2::canonical_vk_v2`.
    let mut hasher = blake3::Hasher::new_derive_key("pyana-vk-v2");

    // program_bytes (length-prefixed)
    hasher.update(&(RECURSIVE_VK_PROGRAM_BYTES.len() as u64).to_le_bytes());
    hasher.update(RECURSIVE_VK_PROGRAM_BYTES);

    // air_fingerprint (fixed 32-byte)
    hasher.update(&air_fp);

    // verifier_fingerprint: hash of (variant_tag=0 [SourceHash] || verifier_fp)
    // under the "pyana-verifier-fingerprint-v1" domain, mirroring
    // VerifierFingerprint::SourceHash.canonical_bytes().
    let vf_canonical = {
        let mut hh = blake3::Hasher::new_derive_key("pyana-verifier-fingerprint-v1");
        hh.update(&[0u8]); // tag = SourceHash
        hh.update(&verifier_fp);
        *hh.finalize().as_bytes()
    };
    hasher.update(&vf_canonical);

    // proving_system_id canonical bytes: tag=0 (Plonky3BabyBearFri)
    // followed by length-prefixed rev string.
    let mut ps = Vec::new();
    ps.push(0u8);
    ps.extend_from_slice(&(RECURSION_P3_REV.as_bytes().len() as u64).to_le_bytes());
    ps.extend_from_slice(RECURSION_P3_REV.as_bytes());
    hasher.update(&(ps.len() as u64).to_le_bytes());
    hasher.update(&ps);

    *hasher.finalize().as_bytes()
}

/// VK hash registry: lookup by 32-byte hash → `()` (acceptance signal).
///
/// v1 has exactly one entry — the canonical `compute_recursive_vk_hash()`.
/// Future extensions register additional shapes. An unknown hash is
/// rejected here, before any cryptographic verification runs (cheap
/// rejection of forged or stale-rev proofs).
pub fn lookup_recursive_vk(hash: &[u8; 32]) -> Option<()> {
    if hash == &compute_recursive_vk_hash() {
        Some(())
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Producer
// ---------------------------------------------------------------------------

/// The output of [`RecursiveProofProducer::produce`].
///
/// Three pieces, mirroring the wire-shape on `pyana_turn::RecursiveProofVariant`:
/// the recursive proof bytes, the public-input vector the proof commits
/// to (as canonical `u32` cells — same encoding as `WitnessedReceipt.public_inputs`),
/// and the VK v2 layered hash identifying which recursive verifier
/// adjudicates this proof.
#[derive(Clone, Debug)]
pub struct RecursiveProofOutput {
    /// Postcard-encoded `BatchStarkProof<PyanaRecursionConfig>` bytes.
    pub proof_bytes: Vec<u8>,
    /// Public inputs as canonical-BabyBear `u32` cells.
    pub public_inputs_u32: Vec<u32>,
    /// VK v2 layered hash; equal to [`compute_recursive_vk_hash`] today.
    pub recursive_vk_hash: [u8; 32],
}

/// Producer for the recursive (Golden Vision) compression of an inline
/// scope-2 witness bundle.
///
/// Given the prover's trace + the public inputs the original Effect VM
/// proof committed to, [`Self::produce`] runs:
///
/// 1. Build the inner AIR ([`crate::effect_vm_p3_air::EffectVmShapeAir`]).
/// 2. Convert the trace to a `RowMajorMatrix` and convert PI to p3-BabyBear.
/// 3. Generate a recursion-compatible inner STARK proof via
///    [`crate::plonky3_recursion_impl::recursive::prove_inner_for_air`].
/// 4. Self-verify that inner proof (defense-in-depth; the prover should
///    never ship a proof that fails its own verifier).
/// 5. Wrap it in the recursive layer via
///    [`crate::plonky3_recursion_impl::recursive::prove_recursive_layer_for_air`].
/// 6. Postcard-encode the outer recursive proof bytes.
/// 7. Compute the VK v2 layered hash.
///
/// On success, returns [`RecursiveProofOutput`]; on failure, returns a
/// human-readable error string from the recursion library.
pub struct RecursiveProofProducer;

impl RecursiveProofProducer {
    /// Bridge: Silver-form trace → Golden-form recursive proof.
    pub fn produce(
        trace: &[Vec<BabyBear>],
        public_inputs: &[BabyBear],
    ) -> Result<RecursiveProofOutput, String> {
        use crate::effect_vm_p3_air::EffectVmShapeAir;
        use crate::plonky3_prover::to_p3;
        use crate::plonky3_recursion_impl::recursive::{
            prove_inner_for_air, prove_recursive_layer_for_air, verify_inner_for_air,
        };
        use p3_baby_bear::BabyBear as P3BabyBear;
        use p3_matrix::dense::RowMajorMatrix;

        if trace.is_empty() {
            return Err("recursive compression requires a non-empty trace".to_string());
        }
        let width = trace[0].len();
        if width != EffectVmShapeAir::WIDTH {
            return Err(format!(
                "trace width {} does not match EffectVmShapeAir::WIDTH ({})",
                width,
                EffectVmShapeAir::WIDTH
            ));
        }
        let trace_len = trace.len();
        if trace_len < 2 || !trace_len.is_power_of_two() {
            return Err(format!(
                "trace_len {trace_len} must be a power of two ≥ 2 for the inner STARK"
            ));
        }
        if !trace.iter().all(|r| r.len() == width) {
            return Err("ragged trace rows".to_string());
        }
        if public_inputs.len() < EffectVmShapeAir::PUBLIC_INPUTS {
            return Err(format!(
                "public_inputs len {} is below EffectVmShapeAir::PUBLIC_INPUTS ({})",
                public_inputs.len(),
                EffectVmShapeAir::PUBLIC_INPUTS
            ));
        }

        // Flatten the trace into a RowMajorMatrix over P3BabyBear.
        let flat: Vec<P3BabyBear> = trace
            .iter()
            .flat_map(|row| row.iter().map(|&v| to_p3(v)))
            .collect();
        let matrix = RowMajorMatrix::new(flat, width);

        // The shape AIR consumes exactly the first BASE_COUNT slots of
        // the receipt's PI. The full receipt PI is wider (custom-effect
        // commitments); we truncate to the shape-AIR's declared width.
        let pi_for_air: Vec<BabyBear> = public_inputs[..EffectVmShapeAir::PUBLIC_INPUTS].to_vec();

        let air = EffectVmShapeAir;

        let inner = prove_inner_for_air(&air, matrix, &pi_for_air);

        verify_inner_for_air(&air, &inner, &pi_for_air)
            .map_err(|e| format!("inner shape-AIR proof self-verify failed: {e}"))?;

        let output = prove_recursive_layer_for_air(&air, &inner, &pi_for_air)
            .map_err(|e| format!("recursive layer prove failed: {e}"))?;

        let proof_bytes = postcard::to_allocvec(&output.0)
            .map_err(|e| format!("recursive proof postcard encode failed: {e}"))?;

        let public_inputs_u32: Vec<u32> = pi_for_air.iter().map(|x| x.as_u32()).collect();

        Ok(RecursiveProofOutput {
            proof_bytes,
            public_inputs_u32,
            recursive_vk_hash: compute_recursive_vk_hash(),
        })
    }
}

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

/// Outcome of [`verify_recursive_proof_variant`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecursiveVariantVerdict {
    /// Recursive proof verified against the registered VK.
    Verified,
    /// `recursive_vk_hash` did not match any entry in the v1 registry.
    UnknownVkHash { hash: [u8; 32] },
    /// `public_inputs` length is below the AIR's declared PI width.
    PublicInputsTooShort { have: usize, need: usize },
    /// `public_inputs` did not match the bound public inputs declared by
    /// the receipt. (Bound checked at higher layers; this variant fires
    /// only when an explicit `expected_pi` is passed.)
    PublicInputsMismatch { reason: String },
    /// The recursive proof bytes failed to deserialise or verify.
    ProofRejected { reason: String },
}

impl RecursiveVariantVerdict {
    /// True iff the verdict is [`Self::Verified`].
    pub fn is_verified(&self) -> bool {
        matches!(self, Self::Verified)
    }
}

/// Verify a [`pyana_turn::RecursiveProofVariant`]-shaped payload.
///
/// Steps:
/// 1. **Registry lookup.** `recursive_vk_hash` must be a known entry; an
///    unknown hash means either a tampered hash or a stale/future
///    recursive verifier. Reject before any cryptographic work.
/// 2. **PI width.** Public inputs must carry at least
///    `EffectVmShapeAir::PUBLIC_INPUTS` slots.
/// 3. **Optional PI cross-binding.** If `expected_pi_u32` is `Some`,
///    confirm `public_inputs_u32[..EffectVmShapeAir::PUBLIC_INPUTS]`
///    matches `expected_pi_u32[..EffectVmShapeAir::PUBLIC_INPUTS]`. The
///    caller passes `Some` when verifying as part of a `WitnessedReceipt`
///    replay (where the receipt's `public_inputs` are authoritative); a
///    bare-recursive-proof verifier may pass `None`.
/// 4. **Recursive STARK verify** via
///    [`crate::plonky3_recursion_impl::recursive::verify_recursive_layer_bytes`].
///
/// Returns `Verified` only when all four checks pass.
pub fn verify_recursive_proof_variant(
    proof_bytes: &[u8],
    public_inputs_u32: &[u32],
    recursive_vk_hash: &[u8; 32],
    expected_pi_u32: Option<&[u32]>,
) -> RecursiveVariantVerdict {
    use crate::effect_vm_p3_air::EffectVmShapeAir;
    use crate::plonky3_recursion_impl::recursive::verify_recursive_layer_bytes;

    // 1. Registry lookup.
    if lookup_recursive_vk(recursive_vk_hash).is_none() {
        return RecursiveVariantVerdict::UnknownVkHash {
            hash: *recursive_vk_hash,
        };
    }

    // 2. PI width.
    if public_inputs_u32.len() < EffectVmShapeAir::PUBLIC_INPUTS {
        return RecursiveVariantVerdict::PublicInputsTooShort {
            have: public_inputs_u32.len(),
            need: EffectVmShapeAir::PUBLIC_INPUTS,
        };
    }

    // 3. Cross-binding (optional).
    if let Some(expected) = expected_pi_u32 {
        if expected.len() < EffectVmShapeAir::PUBLIC_INPUTS {
            return RecursiveVariantVerdict::PublicInputsTooShort {
                have: expected.len(),
                need: EffectVmShapeAir::PUBLIC_INPUTS,
            };
        }
        for i in 0..EffectVmShapeAir::PUBLIC_INPUTS {
            if public_inputs_u32[i] != expected[i] {
                return RecursiveVariantVerdict::PublicInputsMismatch {
                    reason: format!(
                        "PI[{i}] = {} (recursive variant) != {} (receipt-bound)",
                        public_inputs_u32[i], expected[i]
                    ),
                };
            }
        }
    }

    // 4. Recursive STARK verify.
    match verify_recursive_layer_bytes(proof_bytes) {
        Ok(()) => RecursiveVariantVerdict::Verified,
        Err(e) => RecursiveVariantVerdict::ProofRejected { reason: e },
    }
}

// ---------------------------------------------------------------------------
// Tests (adversarial)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effect_vm_p3_air::EffectVmShapeAir;
    use crate::field::BabyBear;

    /// Borrow the existing minimal-shape-trace witness factory from
    /// `effect_vm_p3_air`. 4 rows; satisfies booleanity, sum-to-one,
    /// NoOp passthrough, Transfer (amount=0), chain continuity, and
    /// the boundary PI binding.
    fn build_minimal_shape_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        crate::effect_vm_p3_air::build_minimal_shape_trace(4)
    }

    /// Adversarial test 1: a valid scope-2 trace → recursive proof verifies.
    #[test]
    fn recursive_proof_verifies_for_valid_trace() {
        let (trace, public_inputs) = build_minimal_shape_trace();
        let out = RecursiveProofProducer::produce(&trace, &public_inputs)
            .expect("recursive producer must succeed on a valid trace");

        let pi_u32: Vec<u32> = public_inputs.iter().map(|x| x.as_u32()).collect();
        assert_eq!(out.public_inputs_u32.len(), EffectVmShapeAir::PUBLIC_INPUTS);
        // The recursive VK hash is stable.
        assert_eq!(out.recursive_vk_hash, compute_recursive_vk_hash());

        let verdict = verify_recursive_proof_variant(
            &out.proof_bytes,
            &out.public_inputs_u32,
            &out.recursive_vk_hash,
            Some(&pi_u32),
        );
        assert_eq!(
            verdict,
            RecursiveVariantVerdict::Verified,
            "valid recursive proof must verify; got {:?}",
            verdict
        );
    }

    /// Adversarial test 2: tampered inline trace + valid old recursive
    /// proof → rejected.
    ///
    /// The recursive proof's public inputs commit to the *original* trace
    /// boundary. If a verifier holds a tampered inline trace whose
    /// boundary values differ from the recursive proof's PI, the
    /// `expected_pi_u32` cross-binding step rejects.
    ///
    /// (The recursion library does not re-read the trace; it only verifies
    /// the proof. So the binding to the inline trace must be enforced at
    /// the wire-bundle layer — which is exactly what
    /// `verify_recursive_proof_variant` does via `expected_pi_u32`.)
    #[test]
    fn tampered_inline_trace_rejected_via_pi_binding() {
        let (trace, public_inputs) = build_minimal_shape_trace();
        let out = RecursiveProofProducer::produce(&trace, &public_inputs)
            .expect("recursive producer must succeed on a valid trace");

        // Simulate the WR carrying a tampered inline trace by flipping the
        // boundary PI the verifier reads from the receipt. (In a real
        // attack, the executor would have re-derived the PI from the
        // tampered trace and shipped that to the verifier; here we
        // shortcut to the resulting cross-binding violation.)
        let mut tampered_pi_u32: Vec<u32> = public_inputs.iter().map(|x| x.as_u32()).collect();
        use crate::effect_vm::pi;
        tampered_pi_u32[pi::OLD_COMMIT] ^= 0xDEAD_BEEF;

        let verdict = verify_recursive_proof_variant(
            &out.proof_bytes,
            &out.public_inputs_u32,
            &out.recursive_vk_hash,
            Some(&tampered_pi_u32),
        );
        match verdict {
            RecursiveVariantVerdict::PublicInputsMismatch { .. } => {}
            other => panic!(
                "tampered receipt-side PI must surface a PublicInputsMismatch; got {:?}",
                other
            ),
        }
    }

    /// Adversarial test 3: tampered recursive proof bytes → rejected.
    #[test]
    fn tampered_recursive_proof_bytes_rejected() {
        let (trace, public_inputs) = build_minimal_shape_trace();
        let out = RecursiveProofProducer::produce(&trace, &public_inputs)
            .expect("recursive producer must succeed on a valid trace");

        let mut tampered = out.proof_bytes.clone();
        // Flip some bytes deep inside the proof; this should cause either
        // a postcard decode failure or a recursion verify failure. Either
        // way, the verdict is `ProofRejected`.
        let mid = tampered.len() / 2;
        for i in 0..16usize {
            let idx = mid + i;
            if idx < tampered.len() {
                tampered[idx] ^= 0xFF;
            }
        }

        let verdict = verify_recursive_proof_variant(
            &tampered,
            &out.public_inputs_u32,
            &out.recursive_vk_hash,
            None,
        );
        match verdict {
            RecursiveVariantVerdict::ProofRejected { .. } => {}
            other => panic!(
                "tampered recursive proof bytes must surface a ProofRejected verdict; got {:?}",
                other
            ),
        }
    }

    /// Adversarial test 4: unknown `recursive_vk_hash` → rejected at
    /// registry lookup (cheap; before any cryptographic work).
    #[test]
    fn unknown_recursive_vk_hash_rejected() {
        let (trace, public_inputs) = build_minimal_shape_trace();
        let out = RecursiveProofProducer::produce(&trace, &public_inputs)
            .expect("recursive producer must succeed on a valid trace");

        let mut bogus_hash = [0u8; 32];
        bogus_hash[0] = 0xAA;
        bogus_hash[31] = 0xBB;
        // Sanity: not the canonical hash.
        assert_ne!(bogus_hash, compute_recursive_vk_hash());

        let verdict = verify_recursive_proof_variant(
            &out.proof_bytes,
            &out.public_inputs_u32,
            &bogus_hash,
            None,
        );
        match verdict {
            RecursiveVariantVerdict::UnknownVkHash { hash } => {
                assert_eq!(hash, bogus_hash);
            }
            other => panic!("bogus recursive_vk_hash must be rejected; got {:?}", other),
        }
    }

    /// The VK hash is deterministic (same inputs → same hash) and
    /// non-trivial (not all-zeros).
    #[test]
    fn recursive_vk_hash_is_deterministic_and_nontrivial() {
        let a = compute_recursive_vk_hash();
        let b = compute_recursive_vk_hash();
        assert_eq!(a, b, "recursive VK hash must be deterministic");
        assert_ne!(a, [0u8; 32], "recursive VK hash must not be all-zeros");
    }

    /// Size comparison sanity: the recursive proof bytes are *not*
    /// dramatically larger than the inline trace at typical sizes. We do
    /// not assert a strict inequality (recursion library proof size is a
    /// fixed-ish overhead independent of trace_len, so for small traces
    /// it can exceed the inline shape), but for trace_len=4 we still
    /// expect a few KB of proof — the comparison becomes favorable as
    /// trace_len grows.
    #[test]
    fn recursive_proof_size_is_bounded() {
        let (trace, public_inputs) = build_minimal_shape_trace();
        let out = RecursiveProofProducer::produce(&trace, &public_inputs)
            .expect("recursive producer must succeed");

        let inline_bytes: usize = trace.iter().map(|r| r.len() * 4).sum();
        let recursive_bytes = out.proof_bytes.len();

        // Loose upper bound: recursive proof should be on the order of
        // tens of KB at worst. (We don't compare against inline_bytes
        // here because for a 4-row trace inline ~1.6 KiB but the
        // recursive proof carries fixed FRI overhead.)
        assert!(
            recursive_bytes < 1024 * 1024,
            "recursive proof unexpectedly large: {recursive_bytes} bytes",
        );
        // Smoke: both are present and non-zero.
        assert!(inline_bytes > 0);
        assert!(recursive_bytes > 0);
    }
}
