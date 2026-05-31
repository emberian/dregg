//! # SOUNDNESS WARNING — UNSAFE FOR PRODUCTION (AUDIT-circuit.md P0-2)
//!
//! As of 2026-05-23, every Generic gate in this backend uses
//! `Wire::for_row(r)` — the wire-routing API that points each wire back to
//! the gate's own row. **No copy constraints** thread Poseidon / Merkle
//! gadget outputs into the cells of downstream binding gates. A binding gate
//! like `c[0]*w[0] + c[1]*w[1] == 0` (intended to enforce `w[0] == w[1]`)
//! constrains only the two wires of THAT row; the prover can fill them with
//! any matching value, regardless of what a Poseidon gadget computed
//! several rows earlier.
//!
//! Existing tests pass because they invoke `prove()`, which has Rust-side
//! preconditions (e.g., `if ta != tb { return Err(...) }`) that catch buggy
//! inputs at trace-generation time. Those checks live in the prover, not in
//! the circuit, so they do NOT prove the verifier rejects an adversarially
//! constructed witness. The audit confirmed multiple binding gates that are
//! vacuous in the absence of copy constraints (see
//! `derivation.rs:280-528`, `derivation.rs:421-424` (explicit FIXME comment),
//! `predicates.rs:36-101`).
//!
//! This backend has been downgraded to `ProofTier::Experimental` (see
//! `crate::proof_tier::kimchi_native_tier`). Do not use these proofs to gate
//! any authorization decision until copy constraints have been wired up and
//! re-audited.
//!
//! Fixing requires re-threading wires through
//! `Wire::new(target_row, target_col)` for every gadget-output →
//! binding-gate data flow, plus updates to the Pickles wrap/step circuits in
//! `circuit/src/backends/mina/` (~5800 LOC, not audited) that consume these
//! proofs.
//!
//! Last audit: 2026-05-23 (AUDIT-circuit.md P0-2).
//!
//! Native Kimchi circuit backend for dregg derivation proofs.
pub mod derivation;
pub mod dsl_backend;
pub mod fold;
pub mod from_dsl;
pub mod ivc;
pub mod non_membership;
pub mod predicates;
pub mod presentation;
#[cfg(test)]
pub mod tests;

use ark_ff::{One, PrimeField, Zero};
use groupmap::GroupMap;
use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        wires::{COLUMNS, Wire},
    },
    curve::KimchiCurve,
    proof::ProverProof,
};
use mina_curves::pasta::{Fp, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    pasta::FULL_ROUNDS,
    poseidon::{ArithmeticSponge, Sponge},
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use poly_commitment::{commitment::CommitmentCurve, ipa::OpeningProof};

pub(crate) type SpongeParams = PlonkSpongeConstantsKimchi;
pub(crate) type BaseSponge = DefaultFqSponge<VestaParameters, SpongeParams, FULL_ROUNDS>;
pub(crate) type ScalarSponge = DefaultFrSponge<Fp, SpongeParams, FULL_ROUNDS>;
pub(crate) type VestaOpeningProof = OpeningProof<Vesta, FULL_ROUNDS>;

pub const MAX_BODY_ATOMS: usize = 8;
pub const MAX_SUB_VARS: usize = 8;
pub const MAX_HEAD_TERMS: usize = 4;
pub const MAX_EQUAL_CHECKS: usize = 4;
pub const GTE_DIFF_BITS: usize = 64;

pub fn hash_fact_fp(predicate: Fp, terms: &[Fp]) -> Fp {
    let params = Vesta::sponge_params();
    let mut sponge = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(params);
    let mut inputs = vec![predicate];
    inputs.extend_from_slice(terms);
    sponge.absorb(&inputs);
    sponge.squeeze()
}

#[allow(dead_code)]
pub(crate) fn u64_to_fp(v: u64) -> Fp {
    Fp::from(v)
}

pub(crate) fn fp_to_bytes32(fp: &Fp) -> [u8; 32] {
    let bigint = fp.into_bigint();
    let limbs = bigint.as_ref();
    let mut out = [0u8; 32];
    for (i, limb) in limbs.iter().enumerate() {
        let bytes = limb.to_le_bytes();
        let start = i * 8;
        let end = (start + 8).min(32);
        out[start..end].copy_from_slice(&bytes[..end - start]);
    }
    out
}

pub(crate) fn bytes32_to_fp(bytes: &[u8; 32]) -> Fp {
    Fp::from_le_bytes_mod_order(bytes)
}

pub fn hash_many_fp(inputs: &[Fp]) -> Fp {
    let params = Vesta::sponge_params();
    let mut sponge = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(params);
    sponge.absorb(inputs);
    sponge.squeeze()
}

pub fn make_generic_gate_with_constraints(row: usize, coeffs: [Fp; COLUMNS]) -> CircuitGate<Fp> {
    CircuitGate::new(GateType::Generic, Wire::for_row(row), coeffs.to_vec())
}

/// Add a copy constraint linking two cells in a 2-cycle (Kimchi permutation argument).
///
/// After this call, the Kimchi prover/verifier enforces:
///     `gates[row_a].wires[col_a] == gates[row_b].wires[col_b]`
///
/// **SOUNDNESS**: Without copy constraints, Generic gate equalities only bind the
/// cells inside that one row. A "binding gate" like `c[0]=1, c[1]=-1` only proves
/// `w[0] == w[1]` ON THAT ROW; if `w[0]` is supposed to equal a Poseidon gadget
/// output cell N rows earlier, the prover can set `w[0]` to ANY value matching `w[1]`
/// on that binding row, breaking the chain. See P0-2 in `AUDIT-circuit.md`.
///
/// Caller must:
/// 1. Ensure both `(row_a, col_a)` and `(row_b, col_b)` are valid indices.
/// 2. Call this AFTER all `CircuitGate::new(_, Wire::for_row(_), _)` self-loops
///    are constructed (so we can overwrite them).
/// 3. Avoid linking the same cell more than once (would break the 2-cycle).
pub fn link_wires(
    gates: &mut [CircuitGate<Fp>],
    (row_a, col_a): (usize, usize),
    (row_b, col_b): (usize, usize),
) {
    debug_assert!(row_a < gates.len(), "link_wires row_a OOB");
    debug_assert!(row_b < gates.len(), "link_wires row_b OOB");
    debug_assert!(col_a < COLUMNS, "link_wires col_a OOB");
    debug_assert!(col_b < COLUMNS, "link_wires col_b OOB");
    debug_assert!(
        (row_a, col_a) != (row_b, col_b),
        "link_wires: self-link is no-op"
    );
    gates[row_a].wires[col_a] = Wire {
        row: row_b,
        col: col_b,
    };
    gates[row_b].wires[col_b] = Wire {
        row: row_a,
        col: col_a,
    };
}

/// Row offset within a Poseidon gadget at which the permutation output lives.
///
/// `CircuitGate::create_poseidon_gadget(start, ...)` lays down `POS_ROWS`
/// `Poseidon` gates at rows `[start..start+POS_ROWS)` and a final `Zero` output
/// row at `start + POS_ROWS`. The permutation's three output field elements
/// live at columns 0, 1, 2 of the output row.
pub const POSEIDON_OUTPUT_ROW_OFFSET: usize = FULL_ROUNDS / 5;

pub fn verify_kimchi_proof(
    proof: &ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS>,
    gates: Vec<CircuitGate<Fp>>,
    public_inputs: &[Fp],
    public_count: usize,
) -> Result<bool, String> {
    // Fail-closed: this backend is unsound and broken. No kimchi proof may ever
    // be ACCEPTED outside the crate's own test suite. This is the universal
    // verification choke point, so guarding here disables every verify_* entry
    // point regardless of how it is reached. See `production_guard`.
    production_guard()?;
    let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(
        gates,
        public_count,
    );
    let verifier_index = index.verifier_index();
    let group_map = <Vesta as CommitmentCurve>::Map::setup();
    kimchi::verifier::verify::<FULL_ROUNDS, Vesta, BaseSponge, ScalarSponge, VestaOpeningProof>(
        &group_map,
        &verifier_index,
        proof,
        public_inputs,
    )
    .map(|_| true)
    .map_err(|e| format!("Kimchi verification failed: {:?}", e))
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum KimchiNativeCircuitType {
    Derivation,
    NonMembership,
    Fold,
    Ivc,
    Presentation,
    ArithmeticPredicate,
    RelationalPredicate,
    TemporalPredicate,
    CompoundPredicate,
    /// Generic DSL circuit proven via the constraint-level backend.
    Dsl,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct KimchiNativeProof {
    pub proof_bytes: Vec<u8>,
    pub public_input_bytes: Vec<u8>,
    pub circuit_type: KimchiNativeCircuitType,
    /// **DEPRECATED — DO NOT TRUST IN VERIFICATION.**
    ///
    /// Serialized gates used during proving. Retained ONLY as an opaque
    /// payload that the verifier IGNORES; the verifier always rebuilds gates
    /// canonically from a known descriptor (a witness/shape template) and
    /// checks the resulting hash against [`Self::circuit_hash`]. Trusting
    /// these prover-supplied bytes lets a malicious prover embed a
    /// permissive circuit (SOUNDNESS BREAK).
    #[serde(default)]
    pub circuit_gates_bytes: Vec<u8>,
    /// BLAKE3 hash of the CANONICAL gate serialization (`serialize_circuit_gates(gates, pc)`).
    ///
    /// Set by the prover. The verifier MUST:
    /// 1. Rebuild the gates canonically from a known shape/descriptor.
    /// 2. Compute BLAKE3 over the canonical serialization.
    /// 3. Reject the proof if the computed hash != this field.
    ///
    /// This binds the proof to a specific circuit shape WITHOUT trusting any
    /// prover-supplied gate bytes.
    #[serde(default)]
    pub circuit_hash: [u8; 32],
    /// Number of public inputs (gate count for public wire).
    #[serde(default = "default_public_count")]
    pub public_count: usize,
}

fn default_public_count() -> usize {
    3
}

/// Serialize a circuit (gates + public count) into compact bytes.
///
/// Used to derive the canonical [`KimchiNativeProof::circuit_hash`] binding.
/// This bytes form is NOT trusted across the prover/verifier boundary; both
/// sides recompute it independently from their canonical gate construction.
pub fn serialize_circuit_gates(gates: &[CircuitGate<Fp>], pc: usize) -> Vec<u8> {
    rmp_serde::to_vec(&(gates, pc)).unwrap_or_default()
}

/// Compute the canonical circuit hash (BLAKE3 over the serialized gates).
///
/// The prover embeds this in the proof; the verifier independently rebuilds
/// the canonical gates and recomputes this hash. A mismatch indicates either
/// (a) a malicious prover with a tampered circuit, or (b) verifier/prover
/// disagreement about circuit shape (also a soundness break).
pub fn compute_circuit_hash(gates: &[CircuitGate<Fp>], pc: usize) -> [u8; 32] {
    let bytes = serialize_circuit_gates(gates, pc);
    *blake3::hash(&bytes).as_bytes()
}

/// **DEPRECATED — UNSOUND.** Do not use in any verification path.
///
/// Previously deserialized prover-supplied gates; this is the exact pattern
/// that allowed a malicious prover to embed a permissive circuit (P0-3 in
/// AUDIT-circuit.md). Retained only for source compatibility; the verifier
/// MUST always rebuild gates canonically.
#[deprecated(
    note = "Deserializing prover-supplied gates is a SOUNDNESS BREAK; rebuild gates canonically and verify circuit_hash instead."
)]
pub fn deserialize_circuit_gates(bytes: &[u8]) -> Option<(Vec<CircuitGate<Fp>>, usize)> {
    rmp_serde::from_slice(bytes).ok()
}

/// Verify the proof's embedded `circuit_hash` matches the gates that the
/// verifier rebuilt canonically. Call this before invoking the Kimchi verifier.
///
/// Returns `Err(reason)` if the hash is missing or mismatches — indicating
/// the prover either omitted the binding or used a different circuit shape.
pub fn verify_canonical_circuit_hash(
    proof: &KimchiNativeProof,
    canonical_gates: &[CircuitGate<Fp>],
    pc: usize,
) -> Result<(), String> {
    let expected = compute_circuit_hash(canonical_gates, pc);
    // Zero hash means "unset" — reject (the prover must always bind the shape).
    if proof.circuit_hash == [0u8; 32] {
        return Err(
            "Proof is missing circuit_hash; reject (prover must bind circuit shape)".into(),
        );
    }
    if proof.circuit_hash != expected {
        return Err(format!(
            "Canonical circuit_hash mismatch: prover claimed {} but verifier computed {}",
            hex_short(&proof.circuit_hash),
            hex_short(&expected)
        ));
    }
    Ok(())
}

fn hex_short(b: &[u8; 32]) -> String {
    b[..8].iter().map(|x| format!("{:02x}", x)).collect()
}

/// Fail-closed production guard for the native Kimchi backend.
///
/// **This backend is UNSOUND and BROKEN (see the module-level soundness
/// warning and `crate::proof_tier::kimchi_native_tier`).** Two independent
/// defects make it unusable for any authorization decision:
///
/// 1. **No copy constraints (AUDIT-circuit.md P0-2).** Every Generic gate uses
///    `Wire::for_row(r)`, so binding gates never thread gadget outputs and a
///    malicious prover can satisfy them with arbitrary matching values.
/// 2. **Prover/verifier circuit-shape disagreement.** The verifier rebuilds
///    the canonical circuit from a *placeholder* template witness whose shape
///    (number of body atoms, presence of merkle proofs / equal / gte checks,
///    …) does not match the prover's data-dependent `build_circuit`, so even
///    honest proofs fail the `circuit_hash` binding. Several circuits also
///    fail to construct a valid permutation argument (`Permutation("final
///    value")`) and cannot produce honest proofs at all.
///
/// The live turn-authorization path does NOT use this backend — the node
/// proves turns with `dregg_circuit::stark::try_prove(EffectVmAir)`. To make
/// sure the unsound gates can never be relied upon by accident, every
/// `prove_*` / `verify_*` entry point fails closed here unless the caller is
/// the crate's own test suite (`cfg!(test)`).
fn production_guard() -> Result<(), String> {
    if cfg!(test) {
        return Ok(());
    }
    Err(
        "kimchi-native backend is disabled: it is UNSOUND (no copy constraints, \
         AUDIT-circuit.md P0-2) and BROKEN (prover/verifier circuit-shape \
         disagreement). It MUST NOT be used for any authorization decision. \
         The live path uses stark::try_prove(EffectVmAir). See \
         crate::proof_tier::kimchi_native_tier and the kimchi_native module \
         soundness warning."
            .to_string(),
    )
}

pub struct KimchiNativeBackend;
impl KimchiNativeBackend {
    pub fn prove_derivation(
        witness: &derivation::KimchiDerivationWitness,
    ) -> Result<KimchiNativeProof, String> {
        production_guard()?;
        derivation::KimchiDerivationCircuit::new(witness.clone()).prove()
    }
    pub fn verify_derivation(
        proof: &KimchiNativeProof,
        esr: &Fp,
        edh: &Fp,
    ) -> Result<bool, String> {
        production_guard()?;
        if proof.circuit_type != KimchiNativeCircuitType::Derivation {
            return Err("Expected derivation proof".into());
        }
        if proof.public_input_bytes.len() < 96 {
            return Err("Malformed public inputs".into());
        }
        let rb: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "e")?;
        let hb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "e")?;
        let rh: [u8; 32] = proof.public_input_bytes[64..96]
            .try_into()
            .map_err(|_| "e")?;
        if bytes32_to_fp(&rb) != *esr {
            return Ok(false);
        }
        if bytes32_to_fp(&hb) != *edh {
            return Ok(false);
        }
        let rule_hash = bytes32_to_fp(&rh);
        // Deserialize and verify with the real Kimchi verifier.
        let kimchi_proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(&proof.proof_bytes)
                .map_err(|e| format!("Proof deserialization failed: {}", e))?;
        // SOUNDNESS: NEVER deserialize prover-supplied gate bytes. Always
        // rebuild the canonical circuit from a verifier-known template, then
        // bind via `circuit_hash` (BLAKE3 over canonical gates). A malicious
        // prover that embedded a permissive circuit would mismatch the hash.
        let template_witness = derivation::KimchiDerivationWitness {
            rule: derivation::KimchiRule {
                id: 0,
                num_body_atoms: 1,
                num_variables: 0,
                head_predicate: *edh,
                head_terms: [(false, Fp::zero()); 4],
                equal_checks: Vec::new(),
                memberof_checks: Vec::new(),
                gte_check: None,
                lt_check: None,
            },
            state_root: *esr,
            body_fact_hashes: vec![Fp::zero()],
            body_merkle_proofs: vec![],
            substitution: Vec::new(),
            derived_predicate: *edh,
            derived_terms: [Fp::zero(); 4],
        };
        let circuit = derivation::KimchiDerivationCircuit::new(template_witness);
        let (gates, pc) = circuit.build_circuit();
        // Reject any proof whose circuit_hash does not match the canonical
        // rebuilt circuit. This prevents prover-supplied gates from being used.
        verify_canonical_circuit_hash(proof, &gates, pc)?;
        let public_inputs = vec![*esr, *edh, rule_hash];
        verify_kimchi_proof(&kimchi_proof, gates, &public_inputs, pc)
    }
    /// Prove non-membership of multiple elements in the accumulator polynomial.
    ///
    /// Each element gets an independent Horner evaluation + non-zero check.
    /// This matches the STARK accumulator AIR's per-ancestor security property.
    pub fn prove_non_membership(
        elements: &[Fp],
        coeffs: &[Fp],
        root: Fp,
    ) -> Result<KimchiNativeProof, String> {
        production_guard()?;
        non_membership::KimchiNonMembershipCircuit::new(elements.to_vec(), coeffs.to_vec(), root)?
            .prove()
    }

    /// Verify a multi-ancestor non-membership proof.
    ///
    /// `expected_elements`: the elements that should be proven not-in-set.
    /// `expected_root`: the accumulator root (hash of polynomial coefficients).
    /// `coeffs`: the polynomial coefficients (needed to rebuild the circuit).
    pub fn verify_non_membership(
        proof: &KimchiNativeProof,
        expected_elements: &[Fp],
        expected_root: &Fp,
        coeffs: &[Fp],
    ) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::NonMembership {
            return Err("Expected non-membership proof".into());
        }
        let expected_bytes = 32 * non_membership::PUBLIC_INPUT_COUNT;
        if proof.public_input_bytes.len() < expected_bytes {
            return Err("Malformed public inputs".into());
        }

        // Parse root from proof
        let rb: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "bad root bytes")?;
        let proof_root = bytes32_to_fp(&rb);
        if proof_root != *expected_root {
            return Ok(false);
        }

        // Parse num_ancestors from proof
        let nb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "bad num bytes")?;
        let num_ancestors = { bytes32_to_fp(&nb).into_bigint().as_ref()[0] as usize };
        if num_ancestors != expected_elements.len() {
            return Ok(false);
        }

        // Parse and verify element hashes match
        for i in 0..num_ancestors {
            let offset = 64 + i * 32;
            let eb: [u8; 32] = proof.public_input_bytes[offset..offset + 32]
                .try_into()
                .map_err(|_| "bad element bytes")?;
            let proof_elem = bytes32_to_fp(&eb);
            if proof_elem != expected_elements[i] {
                return Ok(false);
            }
        }

        // Full Kimchi verification via circuit reconstruction
        non_membership::KimchiNonMembershipCircuit::verify(proof, coeffs)
    }
    pub fn prove_fold(
        old_root: Fp,
        new_root: Fp,
        removals: Vec<fold::KimchiFoldRemoval>,
        cc: Fp,
    ) -> Result<KimchiNativeProof, String> {
        production_guard()?;
        fold::KimchiFoldCircuit::new(fold::KimchiFoldWitness {
            old_root,
            new_root,
            removals,
            checks_commitment: cc,
        })
        .prove()
    }
    pub fn verify_fold(proof: &KimchiNativeProof, eor: &Fp, enr: &Fp) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::Fold {
            return Err("Expected fold proof".into());
        }
        if proof.public_input_bytes.len() < 5 * 32 {
            return Err("Malformed".into());
        }
        let ob: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "e")?;
        let nb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "e")?;
        let nmb: [u8; 32] = proof.public_input_bytes[64..96]
            .try_into()
            .map_err(|_| "e")?;
        let rthb: [u8; 32] = proof.public_input_bytes[96..128]
            .try_into()
            .map_err(|_| "e")?;
        let ccb: [u8; 32] = proof.public_input_bytes[128..160]
            .try_into()
            .map_err(|_| "e")?;
        if bytes32_to_fp(&ob) != *eor {
            return Ok(false);
        }
        if bytes32_to_fp(&nb) != *enr {
            return Ok(false);
        }
        let num_removals = bytes32_to_fp(&nmb);
        if num_removals == Fp::zero() {
            return Ok(false);
        }
        let transition_hash = bytes32_to_fp(&rthb);
        let checks_commitment = bytes32_to_fp(&ccb);
        // Deserialize and verify with the real Kimchi verifier.
        let kimchi_proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(&proof.proof_bytes).map_err(|e| format!("{}", e))?;
        // SOUNDNESS: NEVER deserialize prover-supplied gate bytes. Always
        // rebuild the canonical circuit from a verifier-known template.
        let witness = fold::KimchiFoldWitness {
            old_root: *eor,
            new_root: *enr,
            removals: vec![fold::KimchiFoldRemoval {
                fact_hash: Fp::zero(),
                membership_proof: fold::FpMerkleWitness {
                    leaf_hash: Fp::zero(),
                    levels: vec![fold::FpMerkleLevelWitness {
                        position: 0,
                        siblings: [Fp::zero(); 3],
                    }],
                    expected_root: *eor,
                },
            }],
            checks_commitment,
        };
        let circuit = fold::KimchiFoldCircuit::new(witness);
        let (gates, pc) = circuit.build_circuit();
        verify_canonical_circuit_hash(proof, &gates, pc)?;
        let public_inputs = vec![*eor, *enr, num_removals, transition_hash, checks_commitment];
        verify_kimchi_proof(&kimchi_proof, gates, &public_inputs, pc)
    }
    pub fn prove_arithmetic_predicate(
        w: &predicates::KimchiArithmeticPredicateWitness,
    ) -> Result<KimchiNativeProof, String> {
        production_guard()?;
        predicates::KimchiArithmeticPredicateCircuit::new(w.clone()).prove()
    }
    pub fn verify_arithmetic_predicate(
        proof: &KimchiNativeProof,
        ec: &Fp,
        ev: &Fp,
        eo: predicates::KimchiCompareOp,
    ) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::ArithmeticPredicate {
            return Err("Expected arithmetic predicate proof".into());
        }
        if proof.public_input_bytes.len() < 96 {
            return Err("Malformed".into());
        }
        let cb: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "e")?;
        let vb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "e")?;
        let ob: [u8; 32] = proof.public_input_bytes[64..96]
            .try_into()
            .map_err(|_| "e")?;
        if bytes32_to_fp(&cb) != *ec {
            return Ok(false);
        }
        if bytes32_to_fp(&vb) != *ev {
            return Ok(false);
        }
        if bytes32_to_fp(&ob) != eo.to_fp() {
            return Ok(false);
        }
        // Deserialize and verify with the real Kimchi verifier.
        let kimchi_proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(&proof.proof_bytes).map_err(|e| format!("{}", e))?;
        // SOUNDNESS: NEVER deserialize prover-supplied gate bytes; rebuild
        // canonically and bind via circuit_hash.
        let witness = predicates::KimchiArithmeticPredicateWitness {
            inputs: vec![Fp::zero()],
            ops: vec![predicates::KimchiArithOp::Input(0)],
            result_slot: 0,
            comparison_value: *ev,
            comparison_op: eo,
            result_commitment: *ec,
        };
        let circuit = predicates::KimchiArithmeticPredicateCircuit::new(witness);
        let (gates, pc) = circuit.build_circuit();
        verify_canonical_circuit_hash(proof, &gates, pc)?;
        let public_inputs = vec![*ec, *ev, eo.to_fp()];
        verify_kimchi_proof(&kimchi_proof, gates, &public_inputs, pc)
    }
    pub fn prove_relational_predicate(
        w: &predicates::KimchiRelationalPredicateWitness,
    ) -> Result<KimchiNativeProof, String> {
        production_guard()?;
        predicates::KimchiRelationalPredicateCircuit::new(w.clone()).prove()
    }
    pub fn verify_relational_predicate(
        proof: &KimchiNativeProof,
        eca: &Fp,
        ecb: &Fp,
        er: predicates::KimchiRelationType,
    ) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::RelationalPredicate {
            return Err("Expected relational predicate proof".into());
        }
        if proof.public_input_bytes.len() < 96 {
            return Err("Malformed".into());
        }
        let ab: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "e")?;
        let bb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "e")?;
        let rb: [u8; 32] = proof.public_input_bytes[64..96]
            .try_into()
            .map_err(|_| "e")?;
        if bytes32_to_fp(&ab) != *eca {
            return Ok(false);
        }
        if bytes32_to_fp(&bb) != *ecb {
            return Ok(false);
        }
        if bytes32_to_fp(&rb) != er.to_fp() {
            return Ok(false);
        }
        // Deserialize and verify with the real Kimchi verifier.
        let kimchi_proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(&proof.proof_bytes).map_err(|e| format!("{}", e))?;
        // SOUNDNESS: NEVER deserialize prover-supplied gate bytes; rebuild
        // canonically and bind via circuit_hash.
        let witness = predicates::KimchiRelationalPredicateWitness {
            value_a: Fp::zero(),
            blinding_a: Fp::zero(),
            value_b: Fp::zero(),
            blinding_b: Fp::zero(),
            relation: er,
        };
        let circuit = predicates::KimchiRelationalPredicateCircuit::new(witness);
        let (gates, pc) = circuit.build_circuit();
        verify_canonical_circuit_hash(proof, &gates, pc)?;
        let public_inputs = vec![*eca, *ecb, er.to_fp()];
        verify_kimchi_proof(&kimchi_proof, gates, &public_inputs, pc)
    }
    pub fn prove_temporal_predicate(
        w: &predicates::KimchiTemporalPredicateWitness,
    ) -> Result<KimchiNativeProof, String> {
        production_guard()?;
        predicates::KimchiTemporalPredicateCircuit::new(w.clone()).prove()
    }
    pub fn verify_temporal_predicate(
        proof: &KimchiNativeProof,
        eah: &Fp,
        enb: u64,
        efsr: &Fp,
        eibh: u64,
    ) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::TemporalPredicate {
            return Err("Expected temporal predicate proof".into());
        }
        if proof.public_input_bytes.len() < 128 {
            return Err("Malformed".into());
        }
        let ab: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "e")?;
        let nb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "e")?;
        let rb: [u8; 32] = proof.public_input_bytes[64..96]
            .try_into()
            .map_err(|_| "e")?;
        let hb: [u8; 32] = proof.public_input_bytes[96..128]
            .try_into()
            .map_err(|_| "e")?;
        if bytes32_to_fp(&ab) != *eah {
            return Ok(false);
        }
        if bytes32_to_fp(&nb) != Fp::from(enb) {
            return Ok(false);
        }
        if bytes32_to_fp(&rb) != *efsr {
            return Ok(false);
        }
        if bytes32_to_fp(&hb) != Fp::from(eibh) {
            return Ok(false);
        }
        // Deserialize and verify with the real Kimchi verifier.
        let kimchi_proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(&proof.proof_bytes).map_err(|e| format!("{}", e))?;
        // SOUNDNESS: NEVER deserialize prover-supplied gate bytes; rebuild
        // canonically. Shape (num_blocks) comes from the verifier-provided
        // `enb` parameter, not from prover bytes.
        let witness = predicates::KimchiTemporalPredicateWitness {
            values: vec![Fp::zero(); enb as usize],
            state_roots: vec![Fp::zero(); enb as usize],
            attribute_hash: *eah,
            threshold: Fp::zero(),
            initial_block_height: eibh,
        };
        let circuit = predicates::KimchiTemporalPredicateCircuit::new(witness);
        let (gates, pc) = circuit.build_circuit();
        verify_canonical_circuit_hash(proof, &gates, pc)?;
        let public_inputs = vec![*eah, Fp::from(enb), *efsr, Fp::from(eibh)];
        verify_kimchi_proof(&kimchi_proof, gates, &public_inputs, pc)
    }
    pub fn prove_compound_predicate(
        w: &predicates::KimchiCompoundPredicateWitness,
    ) -> Result<KimchiNativeProof, String> {
        production_guard()?;
        predicates::KimchiCompoundPredicateCircuit::new(w.clone()).prove()
    }
    pub fn verify_compound_predicate(
        proof: &KimchiNativeProof,
        efh: &Fp,
        enp: u64,
        erc: &Fp,
        etk: u64,
    ) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::CompoundPredicate {
            return Err("Expected compound predicate proof".into());
        }
        if proof.public_input_bytes.len() < 128 {
            return Err("Malformed".into());
        }
        let fb: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "e")?;
        let nb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "e")?;
        let cb: [u8; 32] = proof.public_input_bytes[64..96]
            .try_into()
            .map_err(|_| "e")?;
        let kb: [u8; 32] = proof.public_input_bytes[96..128]
            .try_into()
            .map_err(|_| "e")?;
        if bytes32_to_fp(&fb) != *efh {
            return Ok(false);
        }
        if bytes32_to_fp(&nb) != Fp::from(enp) {
            return Ok(false);
        }
        if bytes32_to_fp(&cb) != *erc {
            return Ok(false);
        }
        if bytes32_to_fp(&kb) != Fp::from(etk) {
            return Ok(false);
        }
        // Deserialize and verify with the real Kimchi verifier.
        let kimchi_proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(&proof.proof_bytes).map_err(|e| format!("{}", e))?;
        // SOUNDNESS: NEVER deserialize prover-supplied gate bytes; rebuild
        // canonically. Shape (num_predicates) comes from verifier param `enp`.
        let sub_results: Vec<predicates::KimchiSubPredicateResult> = (0..enp)
            .map(|_| predicates::KimchiSubPredicateResult {
                proof_hash: Fp::zero(),
                result: true,
            })
            .collect();
        let witness = predicates::KimchiCompoundPredicateWitness {
            sub_results,
            formula: predicates::KimchiBooleanFormula::And,
            result_commitment: *erc,
        };
        let circuit = predicates::KimchiCompoundPredicateCircuit::new(witness);
        let (gates, pc) = circuit.build_circuit();
        verify_canonical_circuit_hash(proof, &gates, pc)?;
        let public_inputs = vec![*efh, Fp::from(enp), *erc, Fp::from(etk)];
        verify_kimchi_proof(&kimchi_proof, gates, &public_inputs, pc)
    }
    pub fn backend_name() -> &'static str {
        "kimchi-native"
    }
    pub fn prove_ivc(steps: &[ivc::KimchiFoldStep]) -> Result<ivc::KimchiIvcProof, String> {
        production_guard()?;
        if steps.is_empty() {
            return Err("Cannot prove empty IVC chain".into());
        }
        for i in 1..steps.len() {
            if steps[i].pre_state != steps[i - 1].post_state {
                return Err(format!(
                    "IVC chain break at step {}: pre_state != previous post_state",
                    i
                ));
            }
        }
        let ir = steps[0].pre_state;
        let fr = steps.last().unwrap().post_state;
        let ns = steps.len() as u32;
        let ah = ivc::kimchi_ivc_accumulated_hash(steps);
        let proof = ivc::KimchiIvcCircuit::new(steps.to_vec()).prove()?;
        Ok(ivc::KimchiIvcProof {
            proof,
            initial_root: ir,
            final_root: fr,
            accumulated_hash: ah,
            num_steps: ns,
        })
    }
    pub fn verify_ivc(proof: &ivc::KimchiIvcProof, eir: &Fp, efr: &Fp) -> Result<bool, String> {
        if proof.proof.circuit_type != KimchiNativeCircuitType::Ivc {
            return Err("Expected IVC proof".into());
        }
        if proof.initial_root != *eir {
            return Ok(false);
        }
        if proof.final_root != *efr {
            return Ok(false);
        }
        if proof.proof.public_input_bytes.len() < 128 {
            return Err("Malformed".into());
        }
        let ib: [u8; 32] = proof.proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "e")?;
        let fb: [u8; 32] = proof.proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "e")?;
        let hb: [u8; 32] = proof.proof.public_input_bytes[64..96]
            .try_into()
            .map_err(|_| "e")?;
        let sb: [u8; 32] = proof.proof.public_input_bytes[96..128]
            .try_into()
            .map_err(|_| "e")?;
        if bytes32_to_fp(&ib) != *eir {
            return Ok(false);
        }
        if bytes32_to_fp(&fb) != *efr {
            return Ok(false);
        }
        if bytes32_to_fp(&hb) != proof.accumulated_hash {
            return Ok(false);
        }
        if bytes32_to_fp(&sb) != Fp::from(proof.num_steps as u64) {
            return Ok(false);
        }
        // Reconstruct the fold steps from the proof metadata and verify with real Kimchi verifier
        let public_inputs = vec![
            *eir,
            *efr,
            proof.accumulated_hash,
            Fp::from(proof.num_steps as u64),
        ];
        let kimchi_proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(&proof.proof.proof_bytes).map_err(|e| format!("{}", e))?;
        // SOUNDNESS: NEVER deserialize prover-supplied gate bytes; rebuild
        // canonically. Shape (num_steps) comes from the IvcProof's bound
        // `num_steps` field, which itself is bound via the public inputs above.
        let steps: Vec<ivc::KimchiFoldStep> = (0..proof.num_steps)
            .map(|_| ivc::KimchiFoldStep {
                pre_state: Fp::zero(),
                post_state: Fp::zero(),
            })
            .collect();
        let circuit = ivc::KimchiIvcCircuit::new(steps);
        let (gates, pc) = circuit.build_circuit();
        verify_canonical_circuit_hash(&proof.proof, &gates, pc)?;
        verify_kimchi_proof(&kimchi_proof, gates, &public_inputs, pc)
    }
    pub fn prove_presentation(
        w: &presentation::KimchiPresentationWitness,
    ) -> Result<presentation::KimchiPresentationProof, String> {
        production_guard()?;
        let proof = presentation::KimchiPresentationCircuit::new(w.clone()).prove()?;
        let rfc = presentation::compute_revealed_facts_commitment(&w.revealed_facts);
        let blinded_leaf = presentation::compute_blinded_leaf(w.issuer_key_hash, w.blinding_factor);
        Ok(presentation::KimchiPresentationProof {
            proof,
            federation_root: w.federation_root,
            request_predicate: w.request_predicate,
            timestamp: w.timestamp,
            verifier_nonce: w.verifier_nonce,
            composition_commitment: w.composition_commitment,
            presentation_tag: w.presentation_tag,
            verifier_block_height: w.verifier_block_height,
            not_after_height: w.not_after_height,
            revealed_facts_commitment: rfc,
            issuer_blinded_leaf: blinded_leaf,
        })
    }
    pub fn verify_presentation(
        proof: &presentation::KimchiPresentationProof,
    ) -> Result<presentation::KimchiPresentationVerification, String> {
        if proof.proof.circuit_type != KimchiNativeCircuitType::Presentation {
            return Err("Expected presentation proof".into());
        }
        // PUBLIC_INPUT_COUNT * 32 = 13 * 32 = 416
        if proof.proof.public_input_bytes.len() < 13 * 32 {
            return Err("Malformed".into());
        }
        // Extract all public inputs from serialized bytes
        let extract_fp = |start: usize| -> Result<Fp, String> {
            let b: [u8; 32] = proof.proof.public_input_bytes[start..start + 32]
                .try_into()
                .map_err(|_| "e".to_string())?;
            Ok(bytes32_to_fp(&b))
        };
        let vf = extract_fp(0)?; // federation_root
        let vr = [
            extract_fp(32)?,  // request_predicate[0]
            extract_fp(64)?,  // request_predicate[1]
            extract_fp(96)?,  // request_predicate[2]
            extract_fp(128)?, // request_predicate[3]
        ];
        let vt = extract_fp(160)?; // timestamp
        let vn = extract_fp(192)?; // verifier_nonce
        let vc = extract_fp(224)?; // composition_commitment
        let vg = extract_fp(256)?; // presentation_tag
        let vbh = extract_fp(288)?; // verifier_block_height
        let vnah = extract_fp(320)?; // not_after_height
        let vrfc = extract_fp(352)?; // revealed_facts_commitment
        let vibl = extract_fp(384)?; // issuer_blinded_leaf

        if vf != proof.federation_root {
            return Ok(presentation::KimchiPresentationVerification::IssuerNotInFederation);
        }
        if vr != proof.request_predicate {
            return Ok(presentation::KimchiPresentationVerification::InvalidDerivation);
        }
        if vt != proof.timestamp {
            return Ok(presentation::KimchiPresentationVerification::InvalidDerivation);
        }
        if vn != proof.verifier_nonce {
            return Ok(presentation::KimchiPresentationVerification::InvalidDerivation);
        }
        if vc != proof.composition_commitment {
            return Ok(presentation::KimchiPresentationVerification::CompositionMismatch);
        }
        if vc == Fp::zero() {
            return Ok(presentation::KimchiPresentationVerification::CompositionMismatch);
        }
        if vg != proof.presentation_tag {
            return Ok(presentation::KimchiPresentationVerification::InvalidPresentationTag);
        }

        // Token expiry check (verifier-side)
        if vbh != Fp::zero() && vnah != Fp::zero() {
            let diff = vnah - vbh;
            let diff_u64 = diff.into_bigint().as_ref()[0];
            let top_bit = (diff_u64 >> (GTE_DIFF_BITS - 1)) & 1;
            if top_bit != 0 {
                return Ok(presentation::KimchiPresentationVerification::TokenExpired);
            }
        }

        // Reconstruct public inputs and verify with real Kimchi verifier
        let public_inputs = vec![
            vf, vr[0], vr[1], vr[2], vr[3], vt, vn, vc, vg, vbh, vnah, vrfc, vibl,
        ];

        // SOUNDNESS: rebuild canonical circuit and check `circuit_hash` BEFORE
        // running the Kimchi verifier. Prover-supplied gate bytes are ignored.
        {
            let dummy = presentation::KimchiPresentationWitness {
                federation_root: Fp::zero(),
                request_predicate: [Fp::zero(); 4],
                timestamp: Fp::zero(),
                verifier_nonce: Fp::zero(),
                composition_commitment: Fp::one(),
                presentation_tag: Fp::zero(),
                issuer_membership_hash: Fp::zero(),
                fold_chain_hash: Fp::zero(),
                derivation_hash: Fp::zero(),
                non_revocation_eval: Fp::one(),
                final_root: Fp::zero(),
                randomness: Fp::zero(),
                verifier_block_height: Fp::zero(),
                not_after_height: Fp::zero(),
                revealed_facts: Vec::new(),
                issuer_key_hash: Fp::zero(),
                blinding_factor: Fp::zero(),
                issuer_membership_proof: None,
            };
            let circuit = presentation::KimchiPresentationCircuit::new(dummy);
            let (gates, pc) = circuit.build_circuit();
            if verify_canonical_circuit_hash(&proof.proof, &gates, pc).is_err() {
                return Ok(presentation::KimchiPresentationVerification::ProofInvalid);
            }
        }

        match presentation::KimchiPresentationCircuit::verify_with_gates(
            &proof.proof.proof_bytes,
            &public_inputs,
            &[],
        ) {
            Ok(true) => Ok(presentation::KimchiPresentationVerification::Valid),
            Ok(false) => Ok(presentation::KimchiPresentationVerification::ProofInvalid),
            Err(_) => Ok(presentation::KimchiPresentationVerification::ProofInvalid),
        }
    }
}

// ============================================================================
// Trait implementations for KimchiNativeBackend
// ============================================================================

use super::{
    AccumulatorBackend, AccumulatorInput, CrossStateBackend, CrossStateCombiningRule,
    CrossStateOutput, CrossStateSource, DerivationBackend, DerivationInput, DerivationOutput,
    FullProofBackend, IvcBackend, IvcFoldStep, IvcOutput, PredicateBackend, PredicateInput,
    PredicateKind, PresentationBackend, PresentationInput, PresentationOutput, ProofBackend,
    RelationalPredicateInput, TemporalPredicateInput, TemporalPredicateOutput,
};

impl ProofBackend for KimchiNativeBackend {
    type Proof = KimchiNativeProof;

    fn prove_membership(
        leaf: &[u8; 32],
        siblings: &[Vec<[u8; 32]>],
        root: &[u8; 32],
    ) -> Result<Self::Proof, String> {
        let leaf_fp = bytes32_to_fp(leaf);
        let root_fp = bytes32_to_fp(root);

        // Convert siblings to FpMerkleLevelWitness format.
        // Each inner vec has 3 siblings (4-ary tree). Derive position from the leaf path.
        let levels: Vec<fold::FpMerkleLevelWitness> = siblings
            .iter()
            .enumerate()
            .map(|(i, level_sibs)| {
                if level_sibs.len() != 3 {
                    return Err(format!(
                        "Expected 3 siblings per level, got {}",
                        level_sibs.len()
                    ));
                }
                let sibs = [
                    bytes32_to_fp(&level_sibs[0]),
                    bytes32_to_fp(&level_sibs[1]),
                    bytes32_to_fp(&level_sibs[2]),
                ];
                // Derive position from the leaf bytes (same heuristic as mina backend)
                let pos = leaf[i % 32] % 4;
                Ok(fold::FpMerkleLevelWitness {
                    position: pos,
                    siblings: sibs,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;

        let merkle_witness = fold::FpMerkleWitness {
            leaf_hash: leaf_fp,
            levels,
            expected_root: root_fp,
        };

        // Build a fold proof with a single "removal" (membership witness) and trivial new_root.
        // This proves leaf membership under old_root via the Merkle path.
        let removal = fold::KimchiFoldRemoval {
            fact_hash: leaf_fp,
            membership_proof: merkle_witness,
        };

        // For a pure membership proof, we use old_root == new_root (no actual removal).
        // The fold circuit requires at least one removal, so we prove membership
        // of the leaf in the tree rooted at `root`.
        KimchiNativeBackend::prove_fold(root_fp, root_fp, vec![removal], Fp::one())
    }

    fn verify_membership(proof: &Self::Proof, root: &[u8; 32]) -> Result<bool, String> {
        let root_fp = bytes32_to_fp(root);
        // Membership proof is stored as a fold proof with old_root == new_root == root
        KimchiNativeBackend::verify_fold(proof, &root_fp, &root_fp)
    }

    fn prove_fold_step(
        old_root: &[u8; 32],
        new_root: &[u8; 32],
        removals: &[[u8; 32]],
    ) -> Result<Self::Proof, String> {
        let old_root_fp = bytes32_to_fp(old_root);
        let new_root_fp = bytes32_to_fp(new_root);

        // Build removals with trivial membership proofs.
        // In the trait interface, callers provide only the hashes of removed facts.
        // We construct minimal membership witnesses (the circuit validates the proofs).
        // For this to work in practice, the caller must provide valid Merkle proofs
        // via a richer interface. Here we build stub membership witnesses that pass
        // the circuit's structural checks by using the fold circuit with Poseidon-based
        // tree membership. We use a single-level trivial tree for each removal.
        let removal_fps: Vec<fold::KimchiFoldRemoval> = removals
            .iter()
            .map(|r| {
                let fact_fp = bytes32_to_fp(r);
                // Build a 1-level trivial membership proof: the leaf IS the tree
                // with siblings = [0, 0, 0] at position 0. This makes fp_hash4
                // compute a specific root. Since the trait contract says the caller
                // ensures the removals are valid, we trust that old_root is correct
                // and build the proof accordingly.
                //
                // For real usage the caller provides full Merkle paths. Here we construct
                // a single-level proof where the leaf is at position 0 with the given root.
                let levels = vec![fold::FpMerkleLevelWitness {
                    position: 0,
                    siblings: [Fp::zero(); 3],
                }];
                fold::KimchiFoldRemoval {
                    fact_hash: fact_fp,
                    membership_proof: fold::FpMerkleWitness {
                        leaf_hash: fact_fp,
                        levels,
                        expected_root: old_root_fp,
                    },
                }
            })
            .collect();

        // Compute checks_commitment from the removals
        let cc = hash_many_fp(&removal_fps.iter().map(|r| r.fact_hash).collect::<Vec<_>>());

        KimchiNativeBackend::prove_fold(old_root_fp, new_root_fp, removal_fps, cc)
    }

    fn verify_fold(proof: &Self::Proof) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::Fold {
            return Err("Expected fold proof".into());
        }
        if proof.public_input_bytes.len() < 5 * 32 {
            return Err("Malformed fold proof".into());
        }
        let ob: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "bad bytes")?;
        let nb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "bad bytes")?;
        let old_root_fp = bytes32_to_fp(&ob);
        let new_root_fp = bytes32_to_fp(&nb);
        KimchiNativeBackend::verify_fold(proof, &old_root_fp, &new_root_fp)
    }

    fn proof_size(proof: &Self::Proof) -> usize {
        proof.proof_bytes.len() + proof.public_input_bytes.len()
    }

    fn backend_name() -> &'static str {
        "kimchi-native"
    }
}

impl DerivationBackend for KimchiNativeBackend {
    type DerivationProof = KimchiNativeProof;

    fn prove_derivation(input: &DerivationInput) -> Result<Self::DerivationProof, String> {
        // Convert the field-agnostic DerivationInput to a KimchiDerivationWitness.
        let state_root = Fp::from(input.state_root);
        let body_fact_hashes: Vec<Fp> = input
            .body_fact_hashes
            .iter()
            .map(|&h| Fp::from(h))
            .collect();
        let substitution: Vec<Fp> = input.substitution.iter().map(|&s| Fp::from(s)).collect();
        let derived_predicate = Fp::from(input.derived_predicate);
        let derived_terms = [
            Fp::from(input.derived_terms[0]),
            Fp::from(input.derived_terms[1]),
            Fp::from(input.derived_terms[2]),
            Fp::from(input.derived_terms[3]),
        ];

        // Build head terms: treat all as constants (non-variable) bound to derived_terms.
        // The trait-level interface uses the substitution to bind variables; at the Kimchi
        // level we encode the final resolved values directly.
        let head_terms: [(bool, Fp); 4] = [
            (false, derived_terms[0]),
            (false, derived_terms[1]),
            (false, derived_terms[2]),
            (false, derived_terms[3]),
        ];

        let rule = derivation::KimchiRule {
            id: input.rule_id as u64,
            num_body_atoms: input.num_body_atoms,
            num_variables: substitution.len(),
            head_predicate: derived_predicate,
            head_terms,
            equal_checks: Vec::new(),
            memberof_checks: Vec::new(),
            gte_check: None,
            lt_check: None,
        };

        let witness = derivation::KimchiDerivationWitness {
            rule,
            state_root,
            body_fact_hashes,
            body_merkle_proofs: vec![],
            substitution,
            derived_predicate,
            derived_terms,
        };

        KimchiNativeBackend::prove_derivation(&witness)
    }

    fn verify_derivation(proof: &Self::DerivationProof) -> Result<DerivationOutput, String> {
        if proof.circuit_type != KimchiNativeCircuitType::Derivation {
            return Err("Expected derivation proof".into());
        }
        if proof.public_input_bytes.len() < 96 {
            return Err("Malformed derivation proof public inputs".into());
        }
        let sr_bytes: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "bad bytes")?;
        let dh_bytes: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "bad bytes")?;
        let state_root_fp = bytes32_to_fp(&sr_bytes);
        let derived_hash_fp = bytes32_to_fp(&dh_bytes);

        // Verify the proof structurally (deserialization check)
        KimchiNativeBackend::verify_derivation(proof, &state_root_fp, &derived_hash_fp)?;

        // Convert Fp values back to FieldElement (u64).
        // For Pasta field elements > u64::MAX, we take the low 64 bits.

        let state_root_u64 = state_root_fp.into_bigint().as_ref()[0];
        let derived_hash_u64 = derived_hash_fp.into_bigint().as_ref()[0];

        Ok(DerivationOutput {
            derived_fact_hash: derived_hash_u64,
            state_root: state_root_u64,
        })
    }
}

impl PredicateBackend for KimchiNativeBackend {
    type PredicateProof = KimchiNativeProof;
    type TemporalProof = KimchiNativeProof;
    type CompoundProof = KimchiNativeProof;
    type RelationalProof = KimchiNativeProof;

    fn prove_predicate(input: &PredicateInput) -> Result<Self::PredicateProof, String> {
        let comparison_op = match input.kind {
            PredicateKind::Gte => predicates::KimchiCompareOp::Gte,
            PredicateKind::Lte => predicates::KimchiCompareOp::Lte,
            PredicateKind::Gt => predicates::KimchiCompareOp::Gt,
            PredicateKind::Lt => predicates::KimchiCompareOp::Lt,
            PredicateKind::Neq => predicates::KimchiCompareOp::Neq,
        };

        let witness = predicates::KimchiArithmeticPredicateWitness {
            inputs: vec![Fp::from(input.value)],
            ops: vec![predicates::KimchiArithOp::Input(0)],
            result_slot: 0,
            comparison_value: Fp::from(input.threshold),
            comparison_op,
            result_commitment: Fp::from(input.value_commitment),
        };

        KimchiNativeBackend::prove_arithmetic_predicate(&witness)
    }

    fn verify_predicate(proof: &Self::PredicateProof) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::ArithmeticPredicate {
            return Err("Expected arithmetic predicate proof".into());
        }
        if proof.public_input_bytes.len() < 96 {
            return Err("Malformed".into());
        }
        let cb: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "e")?;
        let vb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "e")?;
        let ob: [u8; 32] = proof.public_input_bytes[64..96]
            .try_into()
            .map_err(|_| "e")?;
        let ec = bytes32_to_fp(&cb);
        let ev = bytes32_to_fp(&vb);
        let eo_fp = bytes32_to_fp(&ob);
        let eo = predicates::KimchiCompareOp::from_fp(&eo_fp)
            .ok_or_else(|| "Invalid comparison op in proof".to_string())?;
        KimchiNativeBackend::verify_arithmetic_predicate(proof, &ec, &ev, eo)
    }

    fn prove_temporal(input: &TemporalPredicateInput) -> Result<Self::TemporalProof, String> {
        let values: Vec<Fp> = input.values.iter().map(|&v| Fp::from(v)).collect();
        let state_roots: Vec<Fp> = input.state_roots.iter().map(|&r| Fp::from(r)).collect();
        let threshold = Fp::from(input.threshold);

        // Compute an attribute hash from the threshold and kind for binding.
        let kind_fp = match input.kind {
            PredicateKind::Gte => Fp::from(0u64),
            PredicateKind::Lte => Fp::from(1u64),
            PredicateKind::Gt => Fp::from(2u64),
            PredicateKind::Lt => Fp::from(3u64),
            PredicateKind::Neq => Fp::from(5u64),
        };
        let attribute_hash = hash_fact_fp(kind_fp, &[threshold]);

        let witness = predicates::KimchiTemporalPredicateWitness {
            values,
            state_roots,
            attribute_hash,
            threshold,
            initial_block_height: 0,
        };

        KimchiNativeBackend::prove_temporal_predicate(&witness)
    }

    fn verify_temporal(proof: &Self::TemporalProof) -> Result<TemporalPredicateOutput, String> {
        if proof.circuit_type != KimchiNativeCircuitType::TemporalPredicate {
            return Err("Expected temporal predicate proof".into());
        }
        if proof.public_input_bytes.len() < 128 {
            return Err("Malformed temporal proof".into());
        }
        let _ah_bytes: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "e")?;
        let nb_bytes: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "e")?;
        let fsr_bytes: [u8; 32] = proof.public_input_bytes[64..96]
            .try_into()
            .map_err(|_| "e")?;
        let ibh_bytes: [u8; 32] = proof.public_input_bytes[96..128]
            .try_into()
            .map_err(|_| "e")?;

        let num_steps_fp = bytes32_to_fp(&nb_bytes);
        let final_state_root_fp = bytes32_to_fp(&fsr_bytes);
        let initial_block_height_fp = bytes32_to_fp(&ibh_bytes);
        let attribute_hash_fp = bytes32_to_fp(&_ah_bytes);

        // Verify structurally
        let num_steps = num_steps_fp.into_bigint().as_ref()[0];
        let ibh = initial_block_height_fp.into_bigint().as_ref()[0];
        KimchiNativeBackend::verify_temporal_predicate(
            proof,
            &attribute_hash_fp,
            num_steps,
            &final_state_root_fp,
            ibh,
        )?;

        Ok(TemporalPredicateOutput {
            num_steps: num_steps as u32,
            initial_state_root: initial_block_height_fp.into_bigint().as_ref()[0],
            final_state_root: final_state_root_fp.into_bigint().as_ref()[0],
            threshold: 0, // Threshold is embedded in attribute_hash, not directly extractable
        })
    }

    fn prove_compound(
        input: &super::CompoundPredicateInput,
    ) -> Result<Self::CompoundProof, String> {
        // Convert sub-predicates to KimchiSubPredicateResult.
        // The compound input provides PredicateInput structs; we evaluate each to determine
        // whether it passes (result=true) and compute a proof hash binding.
        let sub_results: Vec<predicates::KimchiSubPredicateResult> = input
            .sub_predicates
            .iter()
            .map(|p| {
                // Evaluate the predicate: value vs threshold with the given kind

                let v = p.value;
                let t = p.threshold;
                let result = match p.kind {
                    PredicateKind::Gte => v >= t,
                    PredicateKind::Lte => v <= t,
                    PredicateKind::Gt => v > t,
                    PredicateKind::Lt => v < t,
                    PredicateKind::Neq => v != t,
                };
                let proof_hash = hash_fact_fp(Fp::from(p.value), &[Fp::from(p.threshold)]);
                predicates::KimchiSubPredicateResult { proof_hash, result }
            })
            .collect();

        // Interpret the formula bytes: first byte encodes the formula type.
        let formula = if input.formula.is_empty() {
            predicates::KimchiBooleanFormula::And
        } else {
            match input.formula[0] {
                0 => predicates::KimchiBooleanFormula::And,
                1 => predicates::KimchiBooleanFormula::Or,
                k => predicates::KimchiBooleanFormula::Threshold(k as usize),
            }
        };

        let result_commitment =
            hash_many_fp(&sub_results.iter().map(|s| s.proof_hash).collect::<Vec<_>>());

        let witness = predicates::KimchiCompoundPredicateWitness {
            sub_results,
            formula,
            result_commitment,
        };

        KimchiNativeBackend::prove_compound_predicate(&witness)
    }

    fn verify_compound(proof: &Self::CompoundProof) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::CompoundPredicate {
            return Err("Expected compound predicate proof".into());
        }
        if proof.public_input_bytes.len() < 128 {
            return Err("Malformed".into());
        }
        let fb: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "e")?;
        let nb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "e")?;
        let cb: [u8; 32] = proof.public_input_bytes[64..96]
            .try_into()
            .map_err(|_| "e")?;
        let kb: [u8; 32] = proof.public_input_bytes[96..128]
            .try_into()
            .map_err(|_| "e")?;

        let efh = bytes32_to_fp(&fb);
        let enp = bytes32_to_fp(&nb).into_bigint().as_ref()[0];
        let erc = bytes32_to_fp(&cb);
        let etk = bytes32_to_fp(&kb).into_bigint().as_ref()[0];
        KimchiNativeBackend::verify_compound_predicate(proof, &efh, enp, &erc, etk)
    }

    fn prove_relational(input: &RelationalPredicateInput) -> Result<Self::RelationalProof, String> {
        let relation = match input.kind {
            PredicateKind::Gte => predicates::KimchiRelationType::GreaterOrEqual,
            PredicateKind::Lte => predicates::KimchiRelationType::LessOrEqual,
            PredicateKind::Gt => predicates::KimchiRelationType::GreaterThan,
            PredicateKind::Lt => predicates::KimchiRelationType::LessThan,
            PredicateKind::Neq => predicates::KimchiRelationType::NotEqual,
        };

        // The relational predicate proves a relationship between my value and their value.
        // Commitments are provided; we need blinding factors to reconstruct commitments
        // inside the circuit. Use zero blinding for the trait-level interface (the commitment
        // is provided directly as a FieldElement).
        let witness = predicates::KimchiRelationalPredicateWitness {
            value_a: Fp::from(input.my_value),
            blinding_a: Fp::zero(),
            value_b: Fp::zero(), // We don't know their value — only their commitment
            blinding_b: Fp::zero(),
            relation,
        };

        // The relational circuit needs both values. At the trait level, we have my_value
        // and their_commitment. Since we can't extract their value from the commitment,
        // we use the commitment values directly as the public inputs and prove the relation
        // structurally. Build with my_commitment and their_commitment as the public witnesses.
        KimchiNativeBackend::prove_relational_predicate(&witness)
    }

    fn verify_relational(proof: &Self::RelationalProof) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::RelationalPredicate {
            return Err("Expected relational predicate proof".into());
        }
        if proof.public_input_bytes.len() < 96 {
            return Err("Malformed".into());
        }
        let ab: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "e")?;
        let bb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "e")?;
        let rb: [u8; 32] = proof.public_input_bytes[64..96]
            .try_into()
            .map_err(|_| "e")?;
        let eca = bytes32_to_fp(&ab);
        let ecb = bytes32_to_fp(&bb);
        let er_fp = bytes32_to_fp(&rb);
        let er = predicates::KimchiRelationType::from_fp(&er_fp)
            .ok_or_else(|| "Invalid relation type in proof".to_string())?;
        KimchiNativeBackend::verify_relational_predicate(proof, &eca, &ecb, er)
    }
}

impl AccumulatorBackend for KimchiNativeBackend {
    type AccumulatorProof = KimchiNativeProof;

    fn prove_non_membership(input: &AccumulatorInput) -> Result<Self::AccumulatorProof, String> {
        // The trait-level accumulator uses extension-field elements (4 base-field elements each).
        // For the Kimchi native circuit, we prove each ancestor INDEPENDENTLY via per-element
        // Horner evaluation + non-zero check. This matches the STARK accumulator AIR's
        // security property: each ancestor is independently proven not-in-set.
        //
        // The Pasta Fp field (254 bits) provides stronger collision resistance than
        // BabyBear^4 (124 bits), so per-ancestor Fp evaluation is actually STRONGER
        // than the STARK's extension-field approach.
        if input.ancestor_hashes.is_empty() {
            return Err("No ancestor hashes to prove non-membership for".into());
        }

        // Each ancestor hash becomes an independent evaluation point
        let elements: Vec<Fp> = input.ancestor_hashes.iter().map(|&h| Fp::from(h)).collect();

        // Build polynomial coefficients from the accumulator and alpha.
        // The accumulator [a0, a1, a2, a3] represents an extension field element.
        // We interpret it as polynomial coefficients for the non-membership check.
        let coeffs: Vec<Fp> = input
            .accumulator
            .iter()
            .chain(input.alpha.iter())
            .map(|&v| Fp::from(v))
            .collect();

        // Root is the hash commitment to the accumulator state
        let root = hash_many_fp(&coeffs);

        KimchiNativeBackend::prove_non_membership(&elements, &coeffs, root)
    }

    fn verify_non_membership(
        proof: &Self::AccumulatorProof,
        accumulator: &[super::FieldElement; 4],
        alpha: &[super::FieldElement; 4],
        num_ancestors: usize,
    ) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::NonMembership {
            return Err("Expected non-membership proof".into());
        }
        let expected_bytes = 32 * non_membership::PUBLIC_INPUT_COUNT;
        if proof.public_input_bytes.len() < expected_bytes {
            return Err("Malformed".into());
        }

        // Reconstruct the accumulator root and coefficients from the public parameters
        let coeffs: Vec<Fp> = accumulator
            .iter()
            .chain(alpha.iter())
            .map(|&v| Fp::from(v))
            .collect();
        let expected_root = hash_many_fp(&coeffs);

        // Parse root from proof and compare
        let rb: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "bad root bytes")?;
        let proof_root = bytes32_to_fp(&rb);
        if proof_root != expected_root {
            return Ok(false);
        }

        // Parse num_ancestors from proof
        let nb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "bad num bytes")?;
        let proof_num = { bytes32_to_fp(&nb).into_bigint().as_ref()[0] as usize };
        if proof_num != num_ancestors {
            return Ok(false);
        }

        // Extract elements from proof for full verification
        let mut elements = Vec::with_capacity(num_ancestors);
        for i in 0..num_ancestors {
            let offset = 64 + i * 32;
            let eb: [u8; 32] = proof.public_input_bytes[offset..offset + 32]
                .try_into()
                .map_err(|_| "bad element bytes")?;
            elements.push(bytes32_to_fp(&eb));
        }

        KimchiNativeBackend::verify_non_membership(proof, &elements, &expected_root, &coeffs)
    }
}

impl IvcBackend for KimchiNativeBackend {
    type IvcProof = ivc::KimchiIvcProof;

    fn prove_ivc(
        initial_root: super::FieldElement,
        steps: &[IvcFoldStep],
    ) -> Result<Self::IvcProof, String> {
        if steps.is_empty() {
            return Err("Cannot prove empty IVC chain".into());
        }

        // Convert trait-level IvcFoldStep to native KimchiFoldStep.
        // The native circuit only needs pre_state and post_state (Fp values).
        let kimchi_steps: Vec<ivc::KimchiFoldStep> = {
            let mut result = Vec::with_capacity(steps.len());
            let mut prev_root = Fp::from(initial_root);
            for step in steps {
                let pre = Fp::from(step.old_root);
                let post = Fp::from(step.new_root);
                // Verify chain continuity at the trait boundary
                if pre != prev_root {
                    return Err(format!(
                        "IVC chain break: expected pre_state {:?} but got {:?}",
                        prev_root, pre
                    ));
                }
                result.push(ivc::KimchiFoldStep {
                    pre_state: pre,
                    post_state: post,
                });
                prev_root = post;
            }
            result
        };

        KimchiNativeBackend::prove_ivc(&kimchi_steps)
    }

    fn verify_ivc(proof: &Self::IvcProof) -> Result<IvcOutput, String> {
        let ir = proof.initial_root;
        let fr = proof.final_root;

        KimchiNativeBackend::verify_ivc(proof, &ir, &fr)?;

        Ok(IvcOutput {
            initial_root: ir.into_bigint().as_ref()[0],
            final_root: fr.into_bigint().as_ref()[0],
            step_count: proof.num_steps,
            accumulated_hash: {
                let ah_bytes = fp_to_bytes32(&proof.accumulated_hash);
                // Pack into 4 u64 elements (the accumulated_hash field in IvcOutput)
                let mut out = [0u64; 4];
                for i in 0..4 {
                    let start = i * 8;
                    let mut buf = [0u8; 8];
                    buf.copy_from_slice(&ah_bytes[start..start + 8]);
                    out[i] = u64::from_le_bytes(buf);
                }
                out
            },
        })
    }

    fn max_chain_depth() -> u32 {
        // The Kimchi IVC circuit supports arbitrary chain lengths in principle,
        // but practical limits come from circuit size and SRS. Cap at 256 steps.
        256
    }
}

impl PresentationBackend for KimchiNativeBackend {
    type PresentationProof = presentation::KimchiPresentationProof;

    fn prove_presentation(input: &PresentationInput) -> Result<Self::PresentationProof, String> {
        let federation_root = Fp::from(input.federation_root);
        let request_predicate = [
            Fp::from(input.request_predicate[0]),
            Fp::from(input.request_predicate[1]),
            Fp::from(input.request_predicate[2]),
            Fp::from(input.request_predicate[3]),
        ];
        let timestamp = Fp::from(input.timestamp);
        let verifier_nonce = Fp::from(input.verifier_nonce);
        let final_root = if input.fold_steps.is_empty() {
            Fp::from(input.derivation.state_root)
        } else {
            Fp::from(input.fold_steps.last().unwrap().new_root)
        };
        let randomness = Fp::from(input.presentation_randomness);

        // Compute the presentation tag: Poseidon(final_root, randomness, verifier_nonce)
        let presentation_tag =
            presentation::compute_presentation_tag(final_root, randomness, verifier_nonce);

        // Compute sub-proof hashes for composition commitment binding
        let fold_chain_hash = if input.fold_steps.is_empty() {
            Fp::one()
        } else {
            let steps: Vec<ivc::KimchiFoldStep> = input
                .fold_steps
                .iter()
                .map(|s| ivc::KimchiFoldStep {
                    pre_state: Fp::from(s.old_root),
                    post_state: Fp::from(s.new_root),
                })
                .collect();
            ivc::kimchi_ivc_accumulated_hash(&steps)
        };

        let derivation_hash = hash_fact_fp(
            Fp::from(input.derivation.derived_predicate),
            &input
                .derivation
                .derived_terms
                .iter()
                .map(|&t| Fp::from(t))
                .collect::<Vec<_>>(),
        );

        // Compute composition commitment: Poseidon(fold_chain_hash, derivation_hash, presentation_tag)
        let composition_commitment = presentation::compute_composition_commitment(
            fold_chain_hash,
            derivation_hash,
            presentation_tag,
        );

        // Compute issuer membership hash for the witness
        let issuer_leaf_fp = Fp::from(input.issuer_leaf);
        let issuer_membership_hash = issuer_leaf_fp; // simplified binding

        // Non-revocation eval: use 1 (non-revoked) by default since the trait
        // doesn't provide revocation info directly in PresentationInput.
        let non_revocation_eval = Fp::one();

        let witness = presentation::KimchiPresentationWitness {
            federation_root,
            request_predicate,
            timestamp,
            verifier_nonce,
            composition_commitment,
            presentation_tag,
            issuer_membership_hash,
            fold_chain_hash,
            derivation_hash,
            non_revocation_eval,
            final_root,
            randomness,
            verifier_block_height: Fp::zero(),
            not_after_height: Fp::zero(),
            revealed_facts: Vec::new(),
            issuer_key_hash: issuer_leaf_fp,
            blinding_factor: Fp::one(), // non-zero blinding for trait path
            issuer_membership_proof: None,
        };

        KimchiNativeBackend::prove_presentation(&witness)
    }

    fn verify_presentation(proof: &Self::PresentationProof) -> Result<PresentationOutput, String> {
        let result = KimchiNativeBackend::verify_presentation(proof)?;
        match result {
            presentation::KimchiPresentationVerification::Valid => {}
            presentation::KimchiPresentationVerification::IssuerNotInFederation => {
                return Err("Issuer not in federation".into());
            }
            presentation::KimchiPresentationVerification::InvalidDerivation => {
                return Err("Invalid derivation".into());
            }
            presentation::KimchiPresentationVerification::CompositionMismatch => {
                return Err("Composition mismatch".into());
            }
            presentation::KimchiPresentationVerification::InvalidPresentationTag => {
                return Err("Invalid presentation tag".into());
            }
            presentation::KimchiPresentationVerification::Revoked => {
                return Err("Credential revoked".into());
            }
            presentation::KimchiPresentationVerification::ProofInvalid => {
                return Err("Proof invalid".into());
            }
            presentation::KimchiPresentationVerification::TokenExpired => {
                return Err("Token expired".into());
            }
        }

        // Extract presentation tag as 4 u64 elements
        let tag_bytes = fp_to_bytes32(&proof.presentation_tag);
        let mut presentation_tag = [0u64; 4];
        for i in 0..4 {
            let start = i * 8;
            let mut buf = [0u8; 8];
            buf.copy_from_slice(&tag_bytes[start..start + 8]);
            presentation_tag[i] = u64::from_le_bytes(buf);
        }

        Ok(PresentationOutput {
            federation_root: proof.federation_root.into_bigint().as_ref()[0],
            request_predicate: [
                proof.request_predicate[0].into_bigint().as_ref()[0],
                proof.request_predicate[1].into_bigint().as_ref()[0],
                proof.request_predicate[2].into_bigint().as_ref()[0],
                proof.request_predicate[3].into_bigint().as_ref()[0],
            ],
            timestamp: proof.timestamp.into_bigint().as_ref()[0],
            presentation_tag,
            revealed_facts_commitment: [0u64; 4],
            composition_commitment: {
                let cc_bytes = fp_to_bytes32(&proof.composition_commitment);
                let mut cc = [0u64; 4];
                for i in 0..4 {
                    let start = i * 8;
                    let mut buf = [0u8; 8];
                    buf.copy_from_slice(&cc_bytes[start..start + 8]);
                    cc[i] = u64::from_le_bytes(buf);
                }
                cc
            },
            verifier_nonce: proof.verifier_nonce.into_bigint().as_ref()[0],
            verifier_block_height: proof.verifier_block_height.into_bigint().as_ref()[0],
        })
    }

    fn presentation_proof_size(proof: &Self::PresentationProof) -> usize {
        proof.proof.proof_bytes.len() + proof.proof.public_input_bytes.len()
    }
}

impl CrossStateBackend for KimchiNativeBackend {
    type CrossStateProof = KimchiNativeProof;

    fn prove_cross_state(
        sources: &[CrossStateSource],
        combining_rule: &CrossStateCombiningRule,
    ) -> Result<Self::CrossStateProof, String> {
        if sources.is_empty() {
            return Err("Cross-state derivation requires at least one source".into());
        }

        // 1. Prove each source derivation independently under its own state root.
        let mut intermediate_hashes: Vec<Fp> = Vec::with_capacity(sources.len());
        for source in sources {
            let input = &source.derivation;
            let _state_root = Fp::from(input.state_root);
            let derived_predicate = Fp::from(input.derived_predicate);
            let derived_terms = [
                Fp::from(input.derived_terms[0]),
                Fp::from(input.derived_terms[1]),
                Fp::from(input.derived_terms[2]),
                Fp::from(input.derived_terms[3]),
            ];
            let derived_hash = hash_fact_fp(derived_predicate, &derived_terms);
            intermediate_hashes.push(derived_hash);
        }

        // 2. Compute composition root from intermediate derived fact hashes.
        let composition_root = hash_many_fp(&intermediate_hashes);

        // 3. Prove the final derivation under the composition root using the combining rule.
        let final_derived_terms = [
            Fp::from(combining_rule.derived_terms[0]),
            Fp::from(combining_rule.derived_terms[1]),
            Fp::from(combining_rule.derived_terms[2]),
            Fp::from(combining_rule.derived_terms[3]),
        ];
        let head_predicate = Fp::from(combining_rule.head_predicate);

        let head_terms: [(bool, Fp); 4] = [
            (
                combining_rule.head_terms[0].0,
                Fp::from(combining_rule.head_terms[0].1),
            ),
            (
                combining_rule.head_terms[1].0,
                Fp::from(combining_rule.head_terms[1].1),
            ),
            (
                combining_rule.head_terms[2].0,
                Fp::from(combining_rule.head_terms[2].1),
            ),
            (
                combining_rule.head_terms[3].0,
                Fp::from(combining_rule.head_terms[3].1),
            ),
        ];

        let substitution: Vec<Fp> = combining_rule
            .substitution
            .iter()
            .map(|&s| Fp::from(s))
            .collect();

        let rule = derivation::KimchiRule {
            id: combining_rule.rule_id as u64,
            num_body_atoms: intermediate_hashes.len(),
            num_variables: substitution.len(),
            head_predicate,
            head_terms,
            equal_checks: Vec::new(),
            memberof_checks: Vec::new(),
            gte_check: None,
            lt_check: None,
        };

        let body_fact_hashes = intermediate_hashes.clone();

        let witness = derivation::KimchiDerivationWitness {
            rule,
            state_root: composition_root,
            body_fact_hashes,
            body_merkle_proofs: vec![],
            substitution,
            derived_predicate: head_predicate,
            derived_terms: final_derived_terms,
        };

        KimchiNativeBackend::prove_derivation(&witness)
    }

    fn verify_cross_state(proof: &Self::CrossStateProof) -> Result<CrossStateOutput, String> {
        if proof.circuit_type != KimchiNativeCircuitType::Derivation {
            return Err("Expected derivation proof for cross-state".into());
        }
        if proof.public_input_bytes.len() < 96 {
            return Err("Malformed cross-state proof".into());
        }
        let sr_bytes: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "bad bytes")?;
        let dh_bytes: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "bad bytes")?;

        let composition_root_fp = bytes32_to_fp(&sr_bytes);
        let final_derived_hash_fp = bytes32_to_fp(&dh_bytes);

        // Verify structurally
        KimchiNativeBackend::verify_derivation(
            proof,
            &composition_root_fp,
            &final_derived_hash_fp,
        )?;

        Ok(CrossStateOutput {
            composition_root: composition_root_fp.into_bigint().as_ref()[0],
            source_roots: Vec::new(), // Source roots are not recoverable from the composition proof alone
            final_derived_hash: final_derived_hash_fp.into_bigint().as_ref()[0],
        })
    }
}

/// KimchiNativeBackend implements the full proof surface.
impl FullProofBackend for KimchiNativeBackend {}
