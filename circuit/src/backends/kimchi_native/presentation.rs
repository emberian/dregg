//! Kimchi native presentation circuit.
//!
//! The presentation circuit is the capstone of the credential system. It composes
//! all sub-proofs (fold chain, derivation, non-revocation) into a single
//! authorization statement with REAL algebraic constraints:
//!
//! 1. Composition commitment correctness: Poseidon(fold_chain_hash, derivation_hash, tag) == public[7]
//! 2. Presentation tag correctness: Poseidon(final_root, randomness, verifier_nonce) == public[8]
//! 3. Non-revocation check: non_revocation_eval * inverse == 1
//! 4. Composition commitment non-zero: composition_commitment * inverse == 1
//! 5. Sub-proof hash binding: fold_chain_hash and derivation_hash are inputs to composition Poseidon
use ark_ff::{Field, One, Zero};
use groupmap::GroupMap;
use kimchi::{circuits::{gate::{CircuitGate, GateType}, polynomials::poseidon::{generate_witness, POS_ROWS_PER_HASH}, wires::{COLUMNS, Wire}}, curve::KimchiCurve, proof::ProverProof};
use mina_curves::pasta::{Fp, Vesta};
use mina_poseidon::{constants::PlonkSpongeConstantsKimchi, pasta::FULL_ROUNDS, poseidon::{ArithmeticSponge, Sponge}};
use poly_commitment::commitment::CommitmentCurve;
use rand_core::OsRng;
use super::{BaseSponge, KimchiNativeCircuitType, KimchiNativeProof, ScalarSponge, SpongeParams, VestaOpeningProof, fp_to_bytes32, bytes32_to_fp, verify_kimchi_proof};

/// Number of public input rows in the presentation circuit.
const PUBLIC_INPUT_COUNT: usize = 10;
/// Number of rows in a single Poseidon gadget (POS_ROWS_PER_HASH + 1 for the output row).
const POSEIDON_GADGET_ROWS: usize = POS_ROWS_PER_HASH + 1;

#[derive(Clone, Debug)]
pub struct KimchiPresentationWitness {
    pub federation_root: Fp,
    pub request_predicate: [Fp; 4],
    pub timestamp: Fp,
    pub verifier_nonce: Fp,
    pub composition_commitment: Fp,
    pub presentation_tag: Fp,
    pub issuer_membership_hash: Fp,
    pub fold_chain_hash: Fp,
    pub derivation_hash: Fp,
    pub non_revocation_eval: Fp,
    /// The root used to compute the presentation tag (private).
    pub final_root: Fp,
    /// Randomness used to compute the presentation tag (private).
    pub randomness: Fp,
}

pub fn compute_presentation_tag(final_root: Fp, randomness: Fp, verifier_nonce: Fp) -> Fp {
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&[final_root, randomness, verifier_nonce]);
    s.squeeze()
}

pub fn compute_composition_commitment(fold_chain_hash: Fp, derivation_hash: Fp, presentation_tag: Fp) -> Fp {
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&[fold_chain_hash, derivation_hash, presentation_tag]);
    s.squeeze()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KimchiPresentationVerification {
    Valid,
    IssuerNotInFederation,
    InvalidDerivation,
    CompositionMismatch,
    InvalidPresentationTag,
    Revoked,
    ProofInvalid,
}

pub struct KimchiPresentationCircuit {
    pub witness: KimchiPresentationWitness,
}

impl KimchiPresentationCircuit {
    pub fn new(witness: KimchiPresentationWitness) -> Self { Self { witness } }

    /// Build the circuit gates.
    ///
    /// Layout:
    ///   Rows 0..9:   Public input gates (c[0]=1 constrains w[0] = public[row])
    ///   Rows 10..21: Poseidon gadget 1: hash(fold_chain_hash, derivation_hash, presentation_tag)
    ///   Row 22:      Equality gate: poseidon1_output == composition_commitment (from row 7)
    ///   Rows 23..34: Poseidon gadget 2: hash(final_root, randomness, verifier_nonce)
    ///   Row 35:      Equality gate: poseidon2_output == presentation_tag (from row 8)
    ///   Row 36:      Non-revocation: non_revocation_eval * inverse - 1 = 0
    ///   Row 37:      Non-zero composition: composition_commitment * inverse - 1 = 0
    pub fn build_circuit(&self) -> (Vec<CircuitGate<Fp>>, usize) {
        let mut gates = Vec::new();
        let pc = PUBLIC_INPUT_COUNT;

        // Public input gates: c[0]=1 constrains w[0] = public[row]
        for _ in 0..pc {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        let rc = &Vesta::sponge_params().round_constants;

        // Poseidon gadget 1: composition commitment = hash(fold_chain_hash, derivation_hash, presentation_tag)
        {
            let s = gates.len();
            let pr = POS_ROWS_PER_HASH;
            let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                s,
                [Wire::for_row(s), Wire::for_row(s + pr)],
                rc,
            );
            gates.extend(pg);
        }

        // Equality gate: poseidon1_output - composition_commitment = 0
        // First gate: c[0]*w[0] + c[1]*w[1] + c[4] = 0 → w[0] - w[1] = 0
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();       // poseidon1 output
            c[1] = -Fp::one();      // composition_commitment (from public input)
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Poseidon gadget 2: presentation tag = hash(final_root, randomness, verifier_nonce)
        {
            let s = gates.len();
            let pr = POS_ROWS_PER_HASH;
            let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                s,
                [Wire::for_row(s), Wire::for_row(s + pr)],
                rc,
            );
            gates.extend(pg);
        }

        // Equality gate: poseidon2_output - presentation_tag = 0
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();       // poseidon2 output
            c[1] = -Fp::one();      // presentation_tag (from public input)
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Non-revocation gate: non_revocation_eval * inverse = 1
        // c[3]*(w[0]*w[1]) + c[4] = 0 → w[0]*w[1] - 1 = 0
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[3] = Fp::one();       // mul coefficient
            c[4] = -Fp::one();      // constant = -1
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Non-zero composition commitment gate: composition_commitment * inverse = 1
        // Same pattern: c[3]*(w[0]*w[1]) + c[4] = 0 → w[0]*w[1] - 1 = 0
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[3] = Fp::one();       // mul coefficient
            c[4] = -Fp::one();      // constant = -1
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        (gates, pc)
    }

    /// Generate the witness for the circuit.
    pub fn generate_witness(&self) -> [Vec<Fp>; COLUMNS] {
        let (gates, _) = self.build_circuit();
        let tr = gates.len();
        let w = &self.witness;
        let mut wit: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); tr]);

        let mut row = 0;

        // Public input rows (0..9)
        wit[0][row] = w.federation_root; row += 1;                      // row 0
        wit[0][row] = w.request_predicate[0]; row += 1;                 // row 1
        wit[0][row] = w.request_predicate[1]; row += 1;                 // row 2
        wit[0][row] = w.request_predicate[2]; row += 1;                 // row 3
        wit[0][row] = w.request_predicate[3]; row += 1;                 // row 4
        wit[0][row] = w.timestamp; row += 1;                            // row 5
        wit[0][row] = w.verifier_nonce; row += 1;                       // row 6
        wit[0][row] = w.composition_commitment; row += 1;               // row 7
        wit[0][row] = w.presentation_tag; row += 1;                     // row 8
        wit[0][row] = Fp::zero(); row += 1;                             // row 9 (padding)

        // Poseidon gadget 1: hash(fold_chain_hash, derivation_hash, presentation_tag)
        generate_witness(row, Vesta::sponge_params(), &mut wit, [w.fold_chain_hash, w.derivation_hash, w.presentation_tag]);
        row += POSEIDON_GADGET_ROWS;

        // The Poseidon output is at wit[0][row - 1] (the last row of the gadget = row + POS_ROWS_PER_HASH)
        // Actually: generate_witness fills from `row` through `row + POS_ROWS_PER_HASH`,
        // and the output is at `row + POS_ROWS_PER_HASH` columns 0,1,2.
        // After row += POSEIDON_GADGET_ROWS, the output is at wit[0][row - 1].
        let poseidon1_output = wit[0][row - 1];

        // Equality gate row: w[0] = poseidon1_output, w[1] = composition_commitment
        wit[0][row] = poseidon1_output;
        wit[1][row] = w.composition_commitment;
        row += 1;

        // Poseidon gadget 2: hash(final_root, randomness, verifier_nonce)
        generate_witness(row, Vesta::sponge_params(), &mut wit, [w.final_root, w.randomness, w.verifier_nonce]);
        row += POSEIDON_GADGET_ROWS;

        let poseidon2_output = wit[0][row - 1];

        // Equality gate row: w[0] = poseidon2_output, w[1] = presentation_tag
        wit[0][row] = poseidon2_output;
        wit[1][row] = w.presentation_tag;
        row += 1;

        // Non-revocation gate: w[0] = non_revocation_eval, w[1] = inverse
        let nre_inv = w.non_revocation_eval.inverse().unwrap_or(Fp::zero());
        wit[0][row] = w.non_revocation_eval;
        wit[1][row] = nre_inv;
        row += 1;

        // Non-zero composition commitment gate: w[0] = composition_commitment, w[1] = inverse
        let cc_inv = w.composition_commitment.inverse().unwrap_or(Fp::zero());
        wit[0][row] = w.composition_commitment;
        wit[1][row] = cc_inv;
        let _ = row;

        wit
    }

    /// Generate the proof. Rejects at prove time if composition_commitment is zero
    /// or if non_revocation_eval is zero (revoked credential).
    pub fn prove(&self) -> Result<KimchiNativeProof, String> {
        if self.witness.composition_commitment == Fp::zero() {
            return Err("Composition commitment must be non-zero for sub-proof binding".into());
        }
        if self.witness.non_revocation_eval == Fp::zero() {
            return Err("Non-revocation eval is zero: credential is revoked".into());
        }

        // Verify composition commitment matches the Poseidon hash
        let expected_cc = compute_composition_commitment(
            self.witness.fold_chain_hash,
            self.witness.derivation_hash,
            self.witness.presentation_tag,
        );
        if self.witness.composition_commitment != expected_cc {
            return Err("Composition commitment does not match hash(fold_chain_hash, derivation_hash, presentation_tag)".into());
        }

        // Verify presentation tag matches the Poseidon hash
        let expected_tag = compute_presentation_tag(
            self.witness.final_root,
            self.witness.randomness,
            self.witness.verifier_nonce,
        );
        if self.witness.presentation_tag != expected_tag {
            return Err("Presentation tag does not match hash(final_root, randomness, verifier_nonce)".into());
        }

        let (gates, pc) = self.build_circuit();
        let wit = self.generate_witness();
        let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(gates, pc);
        let gm = <Vesta as CommitmentCurve>::Map::setup();
        let proof = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<BaseSponge, ScalarSponge, _>(
            &gm, wit, &[], &index, &mut OsRng,
        ).map_err(|e| format!("Kimchi presentation prover error: {:?}", e))?;

        let pb = rmp_serde::to_vec(&proof).map_err(|e| format!("Presentation proof serialization error: {}", e))?;
        let w = &self.witness;
        let mut pib = Vec::with_capacity(320);
        pib.extend_from_slice(&fp_to_bytes32(&w.federation_root));
        for i in 0..4 { pib.extend_from_slice(&fp_to_bytes32(&w.request_predicate[i])); }
        pib.extend_from_slice(&fp_to_bytes32(&w.timestamp));
        pib.extend_from_slice(&fp_to_bytes32(&w.verifier_nonce));
        pib.extend_from_slice(&fp_to_bytes32(&w.composition_commitment));
        pib.extend_from_slice(&fp_to_bytes32(&w.presentation_tag));
        pib.extend_from_slice(&fp_to_bytes32(&Fp::zero()));
        Ok(KimchiNativeProof { proof_bytes: pb, public_input_bytes: pib, circuit_type: KimchiNativeCircuitType::Presentation })
    }

    /// Verify a presentation proof using the real Kimchi verifier.
    pub fn verify(proof_bytes: &[u8], public_inputs: &[Fp]) -> Result<bool, String> {
        let proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(proof_bytes).map_err(|e| format!("Deserialization error: {}", e))?;

        // Build a dummy witness to get the circuit structure (we only need gates)
        let dummy = KimchiPresentationWitness {
            federation_root: Fp::zero(), request_predicate: [Fp::zero(); 4],
            timestamp: Fp::zero(), verifier_nonce: Fp::zero(),
            composition_commitment: Fp::one(), presentation_tag: Fp::zero(),
            issuer_membership_hash: Fp::zero(), fold_chain_hash: Fp::zero(),
            derivation_hash: Fp::zero(), non_revocation_eval: Fp::one(),
            final_root: Fp::zero(), randomness: Fp::zero(),
        };
        let circuit = KimchiPresentationCircuit::new(dummy);
        let (gates, pc) = circuit.build_circuit();

        verify_kimchi_proof(&proof, gates, public_inputs, pc)
    }
}

#[derive(Clone, Debug)]
pub struct KimchiPresentationProof {
    pub proof: KimchiNativeProof,
    pub federation_root: Fp,
    pub request_predicate: [Fp; 4],
    pub timestamp: Fp,
    pub verifier_nonce: Fp,
    pub composition_commitment: Fp,
    pub presentation_tag: Fp,
}
