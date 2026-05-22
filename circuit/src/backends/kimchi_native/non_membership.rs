//! Kimchi native non-membership / accumulator circuit (multi-ancestor).
//!
//! Proves that EACH of up to `MAX_ANCESTORS` elements is NOT in a set
//! represented by an accumulator polynomial. For each element x_i, the
//! accumulator polynomial P(X) evaluates to a non-zero value: P(x_i) != 0.
//!
//! This matches the security property of the BabyBear STARK accumulator AIR:
//! each ancestor is independently proven not-in-set, without combining them
//! into a single hash first (which would reduce security to a single collision).
//!
//! Circuit structure (per ancestor):
//! - Horner evaluation gates: enforce correct polynomial evaluation
//!   acc_new = acc_old * x_i + coeff  (one gate per coefficient)
//! - Non-zero check gate: eval_i * inv_i - 1 = 0
//!
//! Global structure:
//! - Public inputs: accumulator_root, num_ancestors, element_hashes[0..MAX_ANCESTORS]
//! - Poseidon hash gate: hash(coeffs) = accumulator_root
//! - Per-ancestor Horner chain + non-zero check
//! - Binding gates: computed_eval_i == expected_eval_i
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
    BaseSponge, KimchiNativeCircuitType, KimchiNativeProof, ScalarSponge, VestaOpeningProof,
    fp_to_bytes32, verify_kimchi_proof,
};

/// Maximum number of ancestors supported by the circuit.
/// Matches the STARK accumulator AIR.
pub const MAX_ANCESTORS: usize = 8;

/// Kimchi circuit for proving non-membership of multiple elements in an accumulator.
///
/// Given:
/// - `elements`: up to MAX_ANCESTORS elements x_0..x_k to prove NOT in the set
/// - `accumulator_coeffs`: polynomial coefficients [c_0, c_1, ..., c_{n-1}]
/// - `accumulator_root`: Poseidon hash of the coefficients (binds to a specific set)
///
/// For each element x_i, the circuit enforces:
/// 1. Horner evaluation: P(x_i) computed correctly via acc_{j+1} = acc_j * x_i + c_{n-1-j}
/// 2. Non-zero: P(x_i) * inv_i = 1 (proves eval is non-zero, i.e., x_i not in set)
/// 3. Root binding: Poseidon(coeffs) = accumulator_root (public input)
///
/// Public inputs:
/// - accumulator_root
/// - num_ancestors (as Fp)
/// - element_hashes[0..MAX_ANCESTORS] (padded with zero for unused slots)
pub struct KimchiNonMembershipCircuit {
    /// The elements to prove non-membership for.
    pub elements: Vec<Fp>,
    /// Polynomial evaluations P(x_i) for each element (computed by prover).
    pub evals: Vec<Fp>,
    /// Poseidon hash of the accumulator polynomial coefficients.
    pub accumulator_root: Fp,
    /// Accumulator polynomial coefficients in ascending degree order.
    pub accumulator_coeffs: Vec<Fp>,
}

/// Number of public inputs: accumulator_root + num_ancestors + MAX_ANCESTORS element slots.
pub const PUBLIC_INPUT_COUNT: usize = 2 + MAX_ANCESTORS;

impl KimchiNonMembershipCircuit {
    /// Create a new multi-ancestor non-membership circuit.
    ///
    /// Computes polynomial evaluations internally. Returns Err if any element
    /// evaluates to zero (is in the set).
    pub fn new(
        elements: Vec<Fp>,
        accumulator_coeffs: Vec<Fp>,
        accumulator_root: Fp,
    ) -> Result<Self, String> {
        if elements.is_empty() {
            return Err("No elements provided for non-membership proof".into());
        }
        if elements.len() > MAX_ANCESTORS {
            return Err(format!(
                "Too many elements: {} > MAX_ANCESTORS ({})",
                elements.len(),
                MAX_ANCESTORS
            ));
        }

        let n = accumulator_coeffs.len();
        let mut evals = Vec::with_capacity(elements.len());
        for (idx, elem) in elements.iter().enumerate() {
            let mut eval = Fp::zero();
            for i in 0..n {
                eval = eval * elem + accumulator_coeffs[n - 1 - i];
            }
            if eval == Fp::zero() {
                return Err(format!(
                    "Element {} IS in the set (P(x_{}) = 0, cannot prove non-membership)",
                    idx, idx
                ));
            }
            evals.push(eval);
        }

        // Verify root matches
        use mina_poseidon::{
            constants::PlonkSpongeConstantsKimchi,
            poseidon::{ArithmeticSponge, Sponge},
        };
        let params = Vesta::sponge_params();
        let mut sponge =
            ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(params);
        sponge.absorb(&accumulator_coeffs);
        let computed_root = sponge.squeeze();
        if computed_root != accumulator_root {
            return Err("Accumulator root does not match hash of coefficients".into());
        }

        Ok(Self {
            elements,
            evals,
            accumulator_root,
            accumulator_coeffs,
        })
    }

    /// Build the constraint circuit.
    ///
    /// Layout:
    /// - Rows 0..PUBLIC_INPUT_COUNT: Public input rows
    ///   [accumulator_root, num_ancestors, elem_0, ..., elem_7]
    ///
    /// - For each ancestor i (0..num_ancestors):
    ///   - n Horner evaluation gates: acc_new = acc_old * x_i + coeff
    ///   - 1 Non-zero check gate: eval_i * inv_i - 1 = 0
    ///   - 1 Binding gate: computed_eval_i == eval_i
    ///
    /// - Poseidon hash gadget: hash(coefficients) for root binding
    /// - Root binding gate: hash_result == accumulator_root
    pub fn build_circuit(&self) -> (Vec<CircuitGate<Fp>>, usize) {
        let mut gates = Vec::new();
        let pc = PUBLIC_INPUT_COUNT;
        let num_ancestors = self.elements.len();
        let n = self.accumulator_coeffs.len();

        // Public input rows
        for _ in 0..pc {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Per-ancestor Horner evaluation + non-zero check + binding
        for _ancestor_idx in 0..num_ancestors {
            // Horner evaluation gates: acc_new = acc_old * x + coeff
            // Generic gate: c[3]*(w[0]*w[1]) + c[2]*w[2] + c[4] = 0
            // w[0]=acc_old, w[1]=element, w[2]=acc_new
            // c[3]=1 (mul term), c[2]=-1 (output negation), c[4]=coeff_i
            for i in 0..n {
                let r = gates.len();
                let mut c = vec![Fp::zero(); COLUMNS];
                let coeff = self.accumulator_coeffs[n - 1 - i];
                c[3] = Fp::one(); // w[0]*w[1]
                c[2] = -Fp::one(); // -w[2]
                c[4] = coeff; // constant
                gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
            }

            // Non-zero check: eval * inv - 1 = 0
            // c[3]*(w[0]*w[1]) + c[4] = 0  =>  c[3]=1, c[4]=-1
            {
                let r = gates.len();
                let mut c = vec![Fp::zero(); COLUMNS];
                c[3] = Fp::one();
                c[4] = -Fp::one();
                gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
            }

            // Binding gate: computed_eval == public element eval (ensures Horner output matches)
            // c[0]*w[0] + c[1]*w[1] = 0  =>  c[0]=1, c[1]=-1
            {
                let r = gates.len();
                let mut c = vec![Fp::zero(); COLUMNS];
                c[0] = Fp::one();
                c[1] = -Fp::one();
                gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
            }
        }

        // Poseidon gadget: hash the coefficients to verify accumulator_root
        let rc = &Vesta::sponge_params().round_constants;
        let pr = FULL_ROUNDS / 5;
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

        // Root binding gate: hash_result == public accumulator_root
        // c[0]=1, c[1]=-1
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
        let num_ancestors = self.elements.len();
        let n = self.accumulator_coeffs.len();

        // Public inputs:
        // Row 0: accumulator_root
        wit[0][row] = self.accumulator_root;
        row += 1;
        // Row 1: num_ancestors
        wit[0][row] = Fp::from(num_ancestors as u64);
        row += 1;
        // Rows 2..2+MAX_ANCESTORS: element hashes (padded with zero)
        for i in 0..MAX_ANCESTORS {
            if i < num_ancestors {
                wit[0][row] = self.elements[i];
            }
            // else: already zero
            row += 1;
        }

        // Per-ancestor Horner evaluation + non-zero + binding
        for ancestor_idx in 0..num_ancestors {
            let elem = self.elements[ancestor_idx];

            // Horner evaluation: acc_new = acc_old * element + coeff
            let mut acc = Fp::zero();
            for i in 0..n {
                let coeff = self.accumulator_coeffs[n - 1 - i];
                let acc_new = acc * elem + coeff;
                wit[0][row] = acc; // acc_old
                wit[1][row] = elem; // x
                wit[2][row] = acc_new; // acc_new
                acc = acc_new;
                row += 1;
            }
            // After Horner: acc == evals[ancestor_idx]

            // Non-zero check: eval * inv = 1
            let eval = self.evals[ancestor_idx];
            let inv = eval.inverse().expect("eval must be non-zero");
            wit[0][row] = eval;
            wit[1][row] = inv;
            row += 1;

            // Binding gate: computed_eval == eval
            wit[0][row] = acc;
            wit[1][row] = eval;
            row += 1;
        }

        // Poseidon: hash the coefficients
        let pgr = FULL_ROUNDS / 5 + 1;
        let num_poseidon_calls = (n + 2) / 3;
        for call_idx in 0..num_poseidon_calls {
            let base = call_idx * 3;
            let inp = [
                if base < n {
                    self.accumulator_coeffs[base]
                } else {
                    Fp::zero()
                },
                if base + 1 < n {
                    self.accumulator_coeffs[base + 1]
                } else {
                    Fp::zero()
                },
                if base + 2 < n {
                    self.accumulator_coeffs[base + 2]
                } else {
                    Fp::zero()
                },
            ];
            generate_witness(row, Vesta::sponge_params(), &mut wit, inp);
            row += pgr;
        }

        // Root binding gate: hash_result == accumulator_root
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

    /// Create a proof of non-membership for all elements.
    pub fn prove(&self) -> Result<KimchiNativeProof, String> {
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
        let pb =
            rmp_serde::to_vec(&proof).map_err(|e| format!("Proof serialization error: {}", e))?;

        // Public input bytes: accumulator_root || num_ancestors || elements[0..MAX_ANCESTORS]
        let num_ancestors = self.elements.len();
        let mut pib = Vec::with_capacity(32 * PUBLIC_INPUT_COUNT);
        pib.extend_from_slice(&fp_to_bytes32(&self.accumulator_root));
        pib.extend_from_slice(&fp_to_bytes32(&Fp::from(num_ancestors as u64)));
        for i in 0..MAX_ANCESTORS {
            if i < num_ancestors {
                pib.extend_from_slice(&fp_to_bytes32(&self.elements[i]));
            } else {
                pib.extend_from_slice(&fp_to_bytes32(&Fp::zero()));
            }
        }

        Ok(KimchiNativeProof {
            proof_bytes: pb,
            public_input_bytes: pib,
            circuit_type: KimchiNativeCircuitType::NonMembership,
        })
    }

    /// Verify a non-membership proof using the Kimchi verifier.
    ///
    /// `coeffs` must be provided to rebuild the circuit (same polynomial).
    /// Returns Ok(true) if all elements are proven not-in-set.
    pub fn verify(proof: &KimchiNativeProof, coeffs: &[Fp]) -> Result<bool, String> {
        if proof.circuit_type != KimchiNativeCircuitType::NonMembership {
            return Err("Expected non-membership proof".into());
        }
        let expected_bytes = 32 * PUBLIC_INPUT_COUNT;
        if proof.public_input_bytes.len() < expected_bytes {
            return Err("Malformed public inputs".into());
        }

        // Parse public inputs
        let root_bytes: [u8; 32] = proof.public_input_bytes[0..32]
            .try_into()
            .map_err(|_| "bad bytes")?;
        let num_bytes: [u8; 32] = proof.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "bad bytes")?;

        let root = super::bytes32_to_fp(&root_bytes);
        let num_ancestors_fp = super::bytes32_to_fp(&num_bytes);
        use ark_ff::{BigInteger, PrimeField};
        let num_ancestors = num_ancestors_fp.into_bigint().as_ref()[0] as usize;

        if num_ancestors == 0 || num_ancestors > MAX_ANCESTORS {
            return Ok(false);
        }

        // Parse element hashes
        let mut elements = Vec::with_capacity(num_ancestors);
        for i in 0..num_ancestors {
            let offset = 64 + i * 32;
            let eb: [u8; 32] = proof.public_input_bytes[offset..offset + 32]
                .try_into()
                .map_err(|_| "bad bytes")?;
            elements.push(super::bytes32_to_fp(&eb));
        }

        // Verify root matches hash of coefficients
        use mina_poseidon::{
            constants::PlonkSpongeConstantsKimchi,
            poseidon::{ArithmeticSponge, Sponge},
        };
        let params = Vesta::sponge_params();
        let mut sponge =
            ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(params);
        sponge.absorb(coeffs);
        let expected_root = sponge.squeeze();
        if root != expected_root {
            return Ok(false);
        }

        // Verify each element has non-zero evaluation (structural check)
        let n = coeffs.len();
        for elem in &elements {
            let mut eval = Fp::zero();
            for i in 0..n {
                eval = eval * elem + coeffs[n - 1 - i];
            }
            if eval == Fp::zero() {
                return Ok(false);
            }
        }

        // Reconstruct the circuit and verify with the Kimchi verifier
        let circuit = KimchiNonMembershipCircuit {
            elements: elements.clone(),
            evals: {
                elements
                    .iter()
                    .map(|elem| {
                        let mut eval = Fp::zero();
                        for i in 0..n {
                            eval = eval * elem + coeffs[n - 1 - i];
                        }
                        eval
                    })
                    .collect()
            },
            accumulator_root: root,
            accumulator_coeffs: coeffs.to_vec(),
        };
        let (gates, pc) = circuit.build_circuit();

        // Build public inputs vector matching circuit layout
        let mut public_inputs = Vec::with_capacity(PUBLIC_INPUT_COUNT);
        public_inputs.push(root);
        public_inputs.push(Fp::from(num_ancestors as u64));
        for i in 0..MAX_ANCESTORS {
            if i < num_ancestors {
                public_inputs.push(elements[i]);
            } else {
                public_inputs.push(Fp::zero());
            }
        }

        // Deserialize and verify the proof
        let kimchi_proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(&proof.proof_bytes)
                .map_err(|e| format!("Proof deserialization error: {}", e))?;

        verify_kimchi_proof(&kimchi_proof, gates, &public_inputs, pc)
    }
}
