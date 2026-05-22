//! Kimchi native non-membership / accumulator circuit.
//!
//! Proves that an element `x` is NOT in a set represented by an accumulator polynomial.
//! The accumulator polynomial P(X) = c_0 + c_1*X + c_2*X^2 + ... + c_{n-1}*X^{n-1}
//! evaluates to a non-zero value at x (i.e., P(x) != 0).
//!
//! Circuit structure:
//! - Public inputs: element, accumulator_eval, accumulator_root
//! - Horner evaluation gates: enforce correct polynomial evaluation via
//!   acc_new = acc_old * x + coeff  (one gate per coefficient)
//! - Non-zero check gate: remainder * remainder_inv - 1 = 0
//! - Poseidon hash gate: hash(coeffs) = accumulator_root
//! - Final binding gate: computed_eval = public accumulator_eval
use ark_ff::{Field, One, Zero};
use groupmap::GroupMap;
use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        polynomials::poseidon::generate_witness,
        wires::{COLUMNS, Wire},
    },
    curve::KimchiCurve,
    proof::ProverProof,
};
use mina_curves::pasta::{Fp, Vesta};
use mina_poseidon::pasta::FULL_ROUNDS;
use poly_commitment::commitment::CommitmentCurve;
use rand_core::OsRng;

use super::{
    verify_kimchi_proof, BaseSponge, KimchiNativeCircuitType, KimchiNativeProof, ScalarSponge,
    VestaOpeningProof, fp_to_bytes32,
};

/// Kimchi circuit for proving non-membership in an accumulator.
///
/// Given:
/// - `element` (x): the element to prove is NOT in the set
/// - `accumulator_coeffs`: polynomial coefficients [c_0, c_1, ..., c_{n-1}]
/// - `accumulator_eval`: P(x) = c_0 + c_1*x + ... + c_{n-1}*x^{n-1}
/// - `accumulator_root`: Poseidon hash of the coefficients (binds to a specific set)
///
/// The circuit enforces:
/// 1. Horner evaluation: Each step acc_{i+1} = acc_i * x + c_{n-1-i}, starting from acc_0 = 0
/// 2. Non-zero: accumulator_eval * inv = 1 (proves eval is non-zero)
/// 3. Binding: final Horner accumulator = accumulator_eval (public input)
/// 4. Root binding: Poseidon(coeffs) = accumulator_root (public input)
pub struct KimchiNonMembershipCircuit {
    pub element: Fp,
    pub accumulator_eval: Fp,
    pub accumulator_root: Fp,
    pub accumulator_coeffs: Vec<Fp>,
}

impl KimchiNonMembershipCircuit {
    /// Build the constraint circuit.
    ///
    /// Layout:
    /// - Rows 0..3: Public input rows (element, accumulator_eval, accumulator_root)
    /// - Rows 3..3+n: Horner evaluation steps (n = number of coefficients)
    ///   Gate equation: w0*w1 + w2 - w3 = 0
    ///   i.e., acc_old * x + coeff - acc_new = 0
    ///   coeffs: c3=1 (w0*w1 term), c2=1 (w2 = coeff), c[COLUMNS-1]=0, but we use
    ///   the form: c3=1 for w0*w1, c1=1 for +w1 (coeff), c2=-1 for -w2 (acc_new)
    ///   Actually: c0*w0 + c1*w1 + c2*w2 + c3*(w0*w1) + c4*(w0*w2) + c5 = 0
    ///   We want: acc_old*x + coeff - acc_new = 0
    ///   Put acc_old in w0, x in w1, so w0*w1 = acc_old*x -> c3=1
    ///   Put coeff in w2, want +coeff -> c2=1
    ///   Need -acc_new somewhere. We can't subtract w3 directly in a generic gate.
    ///   Instead: put acc_new in w2 position, coeff as constant?
    ///   No - let's use: w0=acc_old, w1=x, w2=acc_new
    ///   Constraint: acc_old * x + coeff - acc_new = 0
    ///   = c3*(w0*w1) + c2*w2 + c5 = 0
    ///   where c3=1, c2=-1, c5=coeff (constant term)
    ///   BUT c5 is baked into the gate at circuit build time, so coeff must be known then.
    ///   That's fine since we know the coefficients at circuit build time.
    ///
    /// - Row 3+n: Non-zero check: remainder * inv - 1 = 0
    ///   w0=remainder, w1=inv, c3=1, c[COLUMNS-1]=-1
    ///
    /// - Row 3+n+1: Binding gate: computed_eval - public_eval = 0
    ///   w0=computed_eval, w1=public_eval, c0=1, c1=-1
    ///
    /// - Poseidon rows: hash(coefficients) for root binding
    ///
    /// - Final row: root binding: hash_output - public_root = 0
    ///   w0=hash_output, w1=public_root, c0=1, c1=-1
    pub fn build_circuit(&self) -> (Vec<CircuitGate<Fp>>, usize) {
        let mut gates = Vec::new();
        let pc = 3; // 3 public inputs: element, accumulator_eval, accumulator_root

        // Public input rows: each requires c0=1 to constrain w0 as public input
        for _ in 0..pc {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Horner evaluation gates: acc_new = acc_old * x + coeff
        // Generic gate first sub-gate: c[0]*w[0] + c[1]*w[1] + c[2]*w[2] + c[3]*(w[0]*w[1]) + c[4] = 0
        // We encode: w[0]=acc_old, w[1]=element, w[2]=acc_new
        // Constraint: acc_old * element + coeff_i - acc_new = 0
        //  => c[3]=1 (mul term), c[2]=-1 (output), c[4]=coeff_i (constant)
        let n = self.accumulator_coeffs.len();
        for i in 0..n {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            // Horner processes coefficients from highest degree to lowest:
            // step i uses coeff[n-1-i]
            let coeff = self.accumulator_coeffs[n - 1 - i];
            c[3] = Fp::one();    // w[0]*w[1] = acc_old * element
            c[2] = -Fp::one();   // -w[2] = -acc_new
            c[4] = coeff;        // constant = coeff_i
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Non-zero check: remainder * remainder_inv - 1 = 0
        // w[0]=remainder, w[1]=remainder_inv
        // c[3]*(w[0]*w[1]) + c[4] = 0 => c[3]=1, c[4]=-1
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[3] = Fp::one();    // w[0]*w[1] term
            c[4] = -Fp::one();   // constant -1
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Binding gate: computed_eval == public_accumulator_eval
        // w0=computed_eval, w1=accumulator_eval (from public input row)
        // c0*w0 + c1*w1 = 0 => c0=1, c1=-1
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            c[1] = -Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Poseidon gadget: hash the coefficients to verify accumulator_root
        let rc = &Vesta::sponge_params().round_constants;
        let pr = FULL_ROUNDS / 5;
        // We need ceil(n/3) Poseidon invocations (each absorbs 3 field elements)
        let num_poseidon_calls = (n + 2) / 3;
        for _ in 0..num_poseidon_calls {
            let s = gates.len();
            let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                s,
                [Wire::for_row(s), Wire::for_row(s + pr)],
                rc,
            );
            gates.extend(pg);
        }

        // Root binding gate: hash_result == public_accumulator_root
        // w0=hash_result, w1=accumulator_root
        // c0=1, c1=-1
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            c[1] = -Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        (gates, pc)
    }

    /// Generate the witness for the circuit.
    pub fn generate_witness(&self) -> [Vec<Fp>; COLUMNS] {
        let (gates, _) = self.build_circuit();
        let tr = gates.len();
        let mut wit: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); tr]);
        let mut row = 0;
        let n = self.accumulator_coeffs.len();

        // Public inputs (rows 0, 1, 2)
        wit[0][row] = self.element;
        row += 1;
        wit[0][row] = self.accumulator_eval;
        row += 1;
        wit[0][row] = self.accumulator_root;
        row += 1;

        // Horner evaluation: acc_new = acc_old * element + coeff
        // Each row: w0=acc_old, w1=element, w2=acc_new
        let mut acc = Fp::zero();
        for i in 0..n {
            let coeff = self.accumulator_coeffs[n - 1 - i];
            let acc_new = acc * self.element + coeff;
            wit[0][row] = acc;           // acc_old
            wit[1][row] = self.element;  // x
            wit[2][row] = acc_new;       // acc_new
            acc = acc_new;
            row += 1;
        }
        // After Horner: acc == accumulator_eval

        // Non-zero check: remainder * remainder_inv = 1
        // w0=remainder (= accumulator_eval), w1=inv
        let inv = self.accumulator_eval.inverse().unwrap_or(Fp::zero());
        wit[0][row] = self.accumulator_eval;
        wit[1][row] = inv;
        row += 1;

        // Binding gate: computed_eval == accumulator_eval
        // w0=acc (computed), w1=accumulator_eval (public)
        wit[0][row] = acc;
        wit[1][row] = self.accumulator_eval;
        row += 1;

        // Poseidon: hash the coefficients
        let pgr = FULL_ROUNDS / 5 + 1;
        let num_poseidon_calls = (n + 2) / 3;
        for call_idx in 0..num_poseidon_calls {
            let base = call_idx * 3;
            let inp = [
                if base < n { self.accumulator_coeffs[base] } else { Fp::zero() },
                if base + 1 < n { self.accumulator_coeffs[base + 1] } else { Fp::zero() },
                if base + 2 < n { self.accumulator_coeffs[base + 2] } else { Fp::zero() },
            ];
            generate_witness(row, Vesta::sponge_params(), &mut wit, inp);
            row += pgr;
        }

        // Root binding gate: hash_result == accumulator_root
        // We need the actual Poseidon hash output. Compute it.
        use mina_poseidon::{
            constants::PlonkSpongeConstantsKimchi,
            poseidon::{ArithmeticSponge, Sponge},
        };
        let params = Vesta::sponge_params();
        let mut sponge =
            ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(params);
        sponge.absorb(&self.accumulator_coeffs);
        let hash_result = sponge.squeeze();

        wit[0][row] = hash_result;
        wit[1][row] = self.accumulator_root;

        wit
    }

    /// Create a proof of non-membership.
    pub fn prove(&self) -> Result<KimchiNativeProof, String> {
        if self.accumulator_eval == Fp::zero() {
            return Err(
                "Cannot prove non-membership: accumulator evaluates to zero (element IS in the set)"
                    .into(),
            );
        }

        // Verify the Horner evaluation matches claimed eval
        let n = self.accumulator_coeffs.len();
        let mut check_eval = Fp::zero();
        for i in 0..n {
            check_eval = check_eval * self.element + self.accumulator_coeffs[n - 1 - i];
        }
        if check_eval != self.accumulator_eval {
            return Err("Accumulator eval does not match polynomial evaluation at element".into());
        }

        // Verify root matches
        use mina_poseidon::{
            constants::PlonkSpongeConstantsKimchi,
            poseidon::{ArithmeticSponge, Sponge},
        };
        let params = Vesta::sponge_params();
        let mut sponge =
            ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(params);
        sponge.absorb(&self.accumulator_coeffs);
        let computed_root = sponge.squeeze();
        if computed_root != self.accumulator_root {
            return Err("Accumulator root does not match hash of coefficients".into());
        }

        let (gates, pc) = self.build_circuit();
        let wit = self.generate_witness();

        let index =
            kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(gates, pc);
        let gm = <Vesta as CommitmentCurve>::Map::setup();
        let proof = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
            BaseSponge,
            ScalarSponge,
            _,
        >(&gm, wit, &[], &index, &mut OsRng)
        .map_err(|e| format!("Kimchi non-membership prover error: {:?}", e))?;

        // Serialize proof
        let pb = rmp_serde::to_vec(&proof)
            .map_err(|e| format!("Proof serialization error: {}", e))?;

        // Public input bytes: element || accumulator_eval || accumulator_root
        let mut pib = Vec::with_capacity(96);
        pib.extend_from_slice(&fp_to_bytes32(&self.element));
        pib.extend_from_slice(&fp_to_bytes32(&self.accumulator_eval));
        pib.extend_from_slice(&fp_to_bytes32(&self.accumulator_root));

        Ok(KimchiNativeProof {
            proof_bytes: pb,
            public_input_bytes: pib,
            circuit_type: KimchiNativeCircuitType::NonMembership,
        })
    }

    /// Verify a non-membership proof using the Kimchi verifier.
    pub fn verify(proof: &KimchiNativeProof, coeffs: &[Fp]) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::NonMembership {
            return Err("Expected non-membership proof".into());
        }
        if proof.public_input_bytes.len() < 96 {
            return Err("Malformed public inputs".into());
        }

        let eb: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "e")?;
        let evb: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "e")?;
        let rb: [u8; 32] = proof.public_input_bytes[64..96]
            .try_into()
            .map_err(|_| "e")?;

        let element = super::bytes32_to_fp(&eb);
        let eval = super::bytes32_to_fp(&evb);
        let root = super::bytes32_to_fp(&rb);

        // eval must be non-zero for valid non-membership
        if eval == Fp::zero() {
            return Ok(false);
        }

        // Reconstruct the circuit with the same coefficients
        let circuit = KimchiNonMembershipCircuit {
            element,
            accumulator_eval: eval,
            accumulator_root: root,
            accumulator_coeffs: coeffs.to_vec(),
        };
        let (gates, pc) = circuit.build_circuit();

        // Public inputs for the verifier
        let public_inputs = vec![element, eval, root];

        // Deserialize and verify the proof
        let kimchi_proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(&proof.proof_bytes)
                .map_err(|e| format!("Proof deserialization error: {}", e))?;

        verify_kimchi_proof(&kimchi_proof, gates, &public_inputs, pc)
    }
}
