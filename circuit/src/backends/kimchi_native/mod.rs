// ============================================================================
// WARNING: AUDIT FINDINGS
// Most circuits currently use all-zero gate coefficients and do NOT enforce
// constraints. Each circuit must be individually hardened. The Kimchi prover
// will accept any witness that satisfies the (currently vacuous) gate
// equations, meaning an adversarial prover can forge proofs for false statements.
// The `verify_kimchi_proof` helper below calls the real Kimchi verifier and
// should be integrated into each circuit's verification path as they are hardened.
// ============================================================================
//! Native Kimchi circuit backend for pyana derivation proofs.
pub mod derivation;
pub mod fold;
pub mod ivc;
pub mod non_membership;
pub mod predicates;
pub mod presentation;
#[cfg(test)]
pub mod tests;

use ark_ff::{Field, One, PrimeField, Zero};
use groupmap::GroupMap;
use kimchi::{circuits::{gate::{CircuitGate, GateType}, wires::{COLUMNS, Wire}}, curve::KimchiCurve, proof::ProverProof};
use mina_curves::pasta::{Fp, Vesta, VestaParameters};
use mina_poseidon::{constants::PlonkSpongeConstantsKimchi, pasta::FULL_ROUNDS, poseidon::{ArithmeticSponge, Sponge}, sponge::{DefaultFqSponge, DefaultFrSponge}};
use poly_commitment::{commitment::CommitmentCurve, ipa::{OpeningProof, SRS}};

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
    let mut inputs = vec![predicate]; inputs.extend_from_slice(terms);
    sponge.absorb(&inputs); sponge.squeeze()
}

#[allow(dead_code)]
pub(crate) fn u64_to_fp(v: u64) -> Fp { Fp::from(v) }

pub(crate) fn fp_to_bytes32(fp: &Fp) -> [u8; 32] {
    use ark_ff::BigInteger;
    let bigint = fp.into_bigint(); let limbs = bigint.as_ref();
    let mut out = [0u8; 32];
    for (i, limb) in limbs.iter().enumerate() { let bytes = limb.to_le_bytes(); let start = i*8; let end = (start+8).min(32); out[start..end].copy_from_slice(&bytes[..end-start]); }
    out
}

pub(crate) fn bytes32_to_fp(bytes: &[u8; 32]) -> Fp { Fp::from_le_bytes_mod_order(bytes) }

pub fn hash_many_fp(inputs: &[Fp]) -> Fp {
    let params = Vesta::sponge_params();
    let mut sponge = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(params);
    sponge.absorb(inputs); sponge.squeeze()
}

pub fn make_generic_gate_with_constraints(row: usize, coeffs: [Fp; COLUMNS]) -> CircuitGate<Fp> {
    CircuitGate::new(GateType::Generic, Wire::for_row(row), coeffs.to_vec())
}

pub fn verify_kimchi_proof(proof: &ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS>, gates: Vec<CircuitGate<Fp>>, public_inputs: &[Fp], public_count: usize) -> Result<bool, String> {
    let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(gates, public_count);
    let verifier_index = index.verifier_index();
    let group_map = <Vesta as CommitmentCurve>::Map::setup();
    kimchi::verifier::verify::<FULL_ROUNDS, Vesta, BaseSponge, ScalarSponge, VestaOpeningProof>(&group_map, &verifier_index, proof, public_inputs)
        .map(|_| true).map_err(|e| format!("Kimchi verification failed: {:?}", e))
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum KimchiNativeCircuitType { Derivation, NonMembership, Fold, Ivc, Presentation, ArithmeticPredicate, RelationalPredicate, TemporalPredicate, CompoundPredicate }

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct KimchiNativeProof { pub proof_bytes: Vec<u8>, pub public_input_bytes: Vec<u8>, pub circuit_type: KimchiNativeCircuitType }

pub struct KimchiNativeBackend;
impl KimchiNativeBackend {
    pub fn prove_derivation(witness: &derivation::KimchiDerivationWitness) -> Result<KimchiNativeProof, String> { derivation::KimchiDerivationCircuit::new(witness.clone()).prove() }
    pub fn verify_derivation(proof: &KimchiNativeProof, esr: &Fp, edh: &Fp) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::Derivation { return Err("Expected derivation proof".into()); }
        if proof.public_input_bytes.len() < 64 { return Err("Malformed public inputs".into()); }
        let rb: [u8;32] = proof.public_input_bytes[0..32].try_into().map_err(|_|"e")?;
        let hb: [u8;32] = proof.public_input_bytes[32..64].try_into().map_err(|_|"e")?;
        if bytes32_to_fp(&rb) != *esr { return Ok(false); } if bytes32_to_fp(&hb) != *edh { return Ok(false); }
        let _: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> = rmp_serde::from_slice(&proof.proof_bytes).map_err(|e| format!("Proof deserialization failed: {}", e))?; Ok(true)
    }
    pub fn prove_non_membership(element: Fp, coeffs: &[Fp], root: Fp) -> Result<KimchiNativeProof, String> {
        let n = coeffs.len(); let mut eval = Fp::zero(); for i in 0..n { eval = eval*element+coeffs[n-1-i]; }
        if eval == Fp::zero() { return Err("Element IS in the set (accumulator evaluates to zero)".into()); }
        non_membership::KimchiNonMembershipCircuit { element, accumulator_eval: eval, accumulator_root: root, accumulator_coeffs: coeffs.to_vec() }.prove()
    }
    pub fn verify_non_membership(proof: &KimchiNativeProof, ee: &Fp, ear: &Fp) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::NonMembership { return Err("Expected non-membership proof".into()); }
        if proof.public_input_bytes.len() < 96 { return Err("Malformed public inputs".into()); }
        let eb: [u8;32] = proof.public_input_bytes[0..32].try_into().map_err(|_|"e")?;
        let evb: [u8;32] = proof.public_input_bytes[32..64].try_into().map_err(|_|"e")?;
        let rb: [u8;32] = proof.public_input_bytes[64..96].try_into().map_err(|_|"e")?;
        if bytes32_to_fp(&eb) != *ee { return Ok(false); } if bytes32_to_fp(&rb) != *ear { return Ok(false); }
        if bytes32_to_fp(&evb) == Fp::zero() { return Ok(false); }
        let _: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> = rmp_serde::from_slice(&proof.proof_bytes).map_err(|e| format!("{}", e))?; Ok(true)
    }
    pub fn prove_fold(old_root: Fp, new_root: Fp, removals: Vec<fold::KimchiFoldRemoval>, cc: Fp) -> Result<KimchiNativeProof, String> { fold::KimchiFoldCircuit::new(fold::KimchiFoldWitness { old_root, new_root, removals, checks_commitment: cc }).prove() }
    pub fn verify_fold(proof: &KimchiNativeProof, eor: &Fp, enr: &Fp) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::Fold { return Err("Expected fold proof".into()); }
        if proof.public_input_bytes.len() < 5*32 { return Err("Malformed".into()); }
        let ob: [u8;32] = proof.public_input_bytes[0..32].try_into().map_err(|_|"e")?;
        let nb: [u8;32] = proof.public_input_bytes[32..64].try_into().map_err(|_|"e")?;
        let nmb: [u8;32] = proof.public_input_bytes[64..96].try_into().map_err(|_|"e")?;
        if bytes32_to_fp(&ob) != *eor { return Ok(false); } if bytes32_to_fp(&nb) != *enr { return Ok(false); }
        if bytes32_to_fp(&nmb) == Fp::zero() { return Ok(false); }
        let _: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> = rmp_serde::from_slice(&proof.proof_bytes).map_err(|e| format!("{}", e))?; Ok(true)
    }
    pub fn prove_arithmetic_predicate(w: &predicates::KimchiArithmeticPredicateWitness) -> Result<KimchiNativeProof, String> { predicates::KimchiArithmeticPredicateCircuit::new(w.clone()).prove() }
    pub fn verify_arithmetic_predicate(proof: &KimchiNativeProof, ec: &Fp, ev: &Fp, eo: predicates::KimchiCompareOp) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::ArithmeticPredicate { return Err("Expected arithmetic predicate proof".into()); }
        if proof.public_input_bytes.len() < 96 { return Err("Malformed".into()); }
        let cb: [u8;32] = proof.public_input_bytes[0..32].try_into().map_err(|_|"e")?;
        let vb: [u8;32] = proof.public_input_bytes[32..64].try_into().map_err(|_|"e")?;
        let ob: [u8;32] = proof.public_input_bytes[64..96].try_into().map_err(|_|"e")?;
        if bytes32_to_fp(&cb) != *ec { return Ok(false); } if bytes32_to_fp(&vb) != *ev { return Ok(false); } if bytes32_to_fp(&ob) != eo.to_fp() { return Ok(false); }
        let _: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> = rmp_serde::from_slice(&proof.proof_bytes).map_err(|e| format!("{}", e))?; Ok(true)
    }
    pub fn prove_relational_predicate(w: &predicates::KimchiRelationalPredicateWitness) -> Result<KimchiNativeProof, String> { predicates::KimchiRelationalPredicateCircuit::new(w.clone()).prove() }
    pub fn verify_relational_predicate(proof: &KimchiNativeProof, eca: &Fp, ecb: &Fp, er: predicates::KimchiRelationType) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::RelationalPredicate { return Err("Expected relational predicate proof".into()); }
        if proof.public_input_bytes.len() < 96 { return Err("Malformed".into()); }
        let ab: [u8;32] = proof.public_input_bytes[0..32].try_into().map_err(|_|"e")?;
        let bb: [u8;32] = proof.public_input_bytes[32..64].try_into().map_err(|_|"e")?;
        let rb: [u8;32] = proof.public_input_bytes[64..96].try_into().map_err(|_|"e")?;
        if bytes32_to_fp(&ab) != *eca { return Ok(false); } if bytes32_to_fp(&bb) != *ecb { return Ok(false); } if bytes32_to_fp(&rb) != er.to_fp() { return Ok(false); }
        let _: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> = rmp_serde::from_slice(&proof.proof_bytes).map_err(|e| format!("{}", e))?; Ok(true)
    }
    pub fn prove_temporal_predicate(w: &predicates::KimchiTemporalPredicateWitness) -> Result<KimchiNativeProof, String> { predicates::KimchiTemporalPredicateCircuit::new(w.clone()).prove() }
    pub fn verify_temporal_predicate(proof: &KimchiNativeProof, eah: &Fp, enb: u64, efsr: &Fp, eibh: u64) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::TemporalPredicate { return Err("Expected temporal predicate proof".into()); }
        if proof.public_input_bytes.len() < 128 { return Err("Malformed".into()); }
        let ab: [u8;32] = proof.public_input_bytes[0..32].try_into().map_err(|_|"e")?;
        let nb: [u8;32] = proof.public_input_bytes[32..64].try_into().map_err(|_|"e")?;
        let rb: [u8;32] = proof.public_input_bytes[64..96].try_into().map_err(|_|"e")?;
        let hb: [u8;32] = proof.public_input_bytes[96..128].try_into().map_err(|_|"e")?;
        if bytes32_to_fp(&ab) != *eah { return Ok(false); } if bytes32_to_fp(&nb) != Fp::from(enb) { return Ok(false); }
        if bytes32_to_fp(&rb) != *efsr { return Ok(false); } if bytes32_to_fp(&hb) != Fp::from(eibh) { return Ok(false); }
        let _: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> = rmp_serde::from_slice(&proof.proof_bytes).map_err(|e| format!("{}", e))?; Ok(true)
    }
    pub fn prove_compound_predicate(w: &predicates::KimchiCompoundPredicateWitness) -> Result<KimchiNativeProof, String> { predicates::KimchiCompoundPredicateCircuit::new(w.clone()).prove() }
    pub fn verify_compound_predicate(proof: &KimchiNativeProof, efh: &Fp, enp: u64, erc: &Fp, etk: u64) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::CompoundPredicate { return Err("Expected compound predicate proof".into()); }
        if proof.public_input_bytes.len() < 128 { return Err("Malformed".into()); }
        let fb: [u8;32] = proof.public_input_bytes[0..32].try_into().map_err(|_|"e")?;
        let nb: [u8;32] = proof.public_input_bytes[32..64].try_into().map_err(|_|"e")?;
        let cb: [u8;32] = proof.public_input_bytes[64..96].try_into().map_err(|_|"e")?;
        let kb: [u8;32] = proof.public_input_bytes[96..128].try_into().map_err(|_|"e")?;
        if bytes32_to_fp(&fb) != *efh { return Ok(false); } if bytes32_to_fp(&nb) != Fp::from(enp) { return Ok(false); }
        if bytes32_to_fp(&cb) != *erc { return Ok(false); } if bytes32_to_fp(&kb) != Fp::from(etk) { return Ok(false); }
        let _: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> = rmp_serde::from_slice(&proof.proof_bytes).map_err(|e| format!("{}", e))?; Ok(true)
    }
    pub fn backend_name() -> &'static str { "kimchi-native" }
    pub fn prove_ivc(steps: &[ivc::KimchiFoldStep]) -> Result<ivc::KimchiIvcProof, String> {
        if steps.is_empty() { return Err("Cannot prove empty IVC chain".into()); }
        for i in 1..steps.len() { if steps[i].pre_state != steps[i-1].post_state { return Err(format!("IVC chain break at step {}: pre_state != previous post_state", i)); } }
        let ir = steps[0].pre_state; let fr = steps.last().unwrap().post_state;
        let ns = steps.len() as u32; let ah = ivc::kimchi_ivc_accumulated_hash(steps);
        let proof = ivc::KimchiIvcCircuit::new(steps.to_vec()).prove()?;
        Ok(ivc::KimchiIvcProof { proof, initial_root: ir, final_root: fr, accumulated_hash: ah, num_steps: ns })
    }
    pub fn verify_ivc(proof: &ivc::KimchiIvcProof, eir: &Fp, efr: &Fp) -> Result<bool, String> {
        if proof.proof.circuit_type != KimchiNativeCircuitType::Ivc { return Err("Expected IVC proof".into()); }
        if proof.initial_root != *eir { return Ok(false); }
        if proof.final_root != *efr { return Ok(false); }
        if proof.proof.public_input_bytes.len() < 128 { return Err("Malformed".into()); }
        let ib: [u8;32] = proof.proof.public_input_bytes[0..32].try_into().map_err(|_|"e")?;
        let fb: [u8;32] = proof.proof.public_input_bytes[32..64].try_into().map_err(|_|"e")?;
        let hb: [u8;32] = proof.proof.public_input_bytes[64..96].try_into().map_err(|_|"e")?;
        let sb: [u8;32] = proof.proof.public_input_bytes[96..128].try_into().map_err(|_|"e")?;
        if bytes32_to_fp(&ib) != *eir { return Ok(false); }
        if bytes32_to_fp(&fb) != *efr { return Ok(false); }
        if bytes32_to_fp(&hb) != proof.accumulated_hash { return Ok(false); }
        if bytes32_to_fp(&sb) != Fp::from(proof.num_steps as u64) { return Ok(false); }
        // Reconstruct the fold steps from the proof metadata and verify with real Kimchi verifier
        let public_inputs = vec![*eir, *efr, proof.accumulated_hash, Fp::from(proof.num_steps as u64)];
        let kimchi_proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(&proof.proof.proof_bytes).map_err(|e| format!("{}", e))?;
        // Build circuit with the correct number of steps to get matching gates
        let steps: Vec<ivc::KimchiFoldStep> = (0..proof.num_steps).map(|_| ivc::KimchiFoldStep { pre_state: Fp::zero(), post_state: Fp::zero() }).collect();
        let circuit = ivc::KimchiIvcCircuit::new(steps);
        let (gates, pc) = circuit.build_circuit();
        verify_kimchi_proof(&kimchi_proof, gates, &public_inputs, pc)
    }
    pub fn prove_presentation(w: &presentation::KimchiPresentationWitness) -> Result<presentation::KimchiPresentationProof, String> {
        let proof = presentation::KimchiPresentationCircuit::new(w.clone()).prove()?;
        Ok(presentation::KimchiPresentationProof { proof, federation_root: w.federation_root, request_predicate: w.request_predicate, timestamp: w.timestamp, verifier_nonce: w.verifier_nonce, composition_commitment: w.composition_commitment, presentation_tag: w.presentation_tag })
    }
    pub fn verify_presentation(proof: &presentation::KimchiPresentationProof) -> Result<presentation::KimchiPresentationVerification, String> {
        if proof.proof.circuit_type != KimchiNativeCircuitType::Presentation { return Err("Expected presentation proof".into()); }
        if proof.proof.public_input_bytes.len() < 320 { return Err("Malformed".into()); }
        let pf: [u8;32] = proof.proof.public_input_bytes[0..32].try_into().map_err(|_|"e")?;
        let p0: [u8;32] = proof.proof.public_input_bytes[32..64].try_into().map_err(|_|"e")?;
        let p1: [u8;32] = proof.proof.public_input_bytes[64..96].try_into().map_err(|_|"e")?;
        let p2: [u8;32] = proof.proof.public_input_bytes[96..128].try_into().map_err(|_|"e")?;
        let p3: [u8;32] = proof.proof.public_input_bytes[128..160].try_into().map_err(|_|"e")?;
        let pt: [u8;32] = proof.proof.public_input_bytes[160..192].try_into().map_err(|_|"e")?;
        let pn: [u8;32] = proof.proof.public_input_bytes[192..224].try_into().map_err(|_|"e")?;
        let pc: [u8;32] = proof.proof.public_input_bytes[224..256].try_into().map_err(|_|"e")?;
        let pg: [u8;32] = proof.proof.public_input_bytes[256..288].try_into().map_err(|_|"e")?;
        let vf = bytes32_to_fp(&pf); let vr = [bytes32_to_fp(&p0),bytes32_to_fp(&p1),bytes32_to_fp(&p2),bytes32_to_fp(&p3)];
        let vt = bytes32_to_fp(&pt); let vn = bytes32_to_fp(&pn); let vc = bytes32_to_fp(&pc); let vg = bytes32_to_fp(&pg);
        if vf != proof.federation_root { return Ok(presentation::KimchiPresentationVerification::IssuerNotInFederation); }
        if vr != proof.request_predicate { return Ok(presentation::KimchiPresentationVerification::InvalidDerivation); }
        if vt != proof.timestamp { return Ok(presentation::KimchiPresentationVerification::InvalidDerivation); }
        if vn != proof.verifier_nonce { return Ok(presentation::KimchiPresentationVerification::InvalidDerivation); }
        if vc != proof.composition_commitment { return Ok(presentation::KimchiPresentationVerification::CompositionMismatch); }
        if vc == Fp::zero() { return Ok(presentation::KimchiPresentationVerification::CompositionMismatch); }
        if vg != proof.presentation_tag { return Ok(presentation::KimchiPresentationVerification::InvalidPresentationTag); }
        // Reconstruct public inputs and verify with real Kimchi verifier
        let public_inputs = vec![vf, vr[0], vr[1], vr[2], vr[3], vt, vn, vc, vg, Fp::zero()];
        match presentation::KimchiPresentationCircuit::verify(&proof.proof.proof_bytes, &public_inputs) {
            Ok(true) => Ok(presentation::KimchiPresentationVerification::Valid),
            Ok(false) => Ok(presentation::KimchiPresentationVerification::ProofInvalid),
            Err(_) => Ok(presentation::KimchiPresentationVerification::ProofInvalid),
        }
    }
}
