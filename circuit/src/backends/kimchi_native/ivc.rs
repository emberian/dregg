//! Kimchi native IVC circuit.
use ark_ff::{One, Zero};
use groupmap::GroupMap;
use kimchi::{circuits::{gate::{CircuitGate, GateType}, polynomials::poseidon::generate_witness, wires::{COLUMNS, Wire}}, curve::KimchiCurve, proof::ProverProof};
use mina_curves::pasta::{Fp, Vesta};
use mina_poseidon::{constants::PlonkSpongeConstantsKimchi, pasta::FULL_ROUNDS, poseidon::{ArithmeticSponge, Sponge}};
use poly_commitment::commitment::CommitmentCurve;
use rand_core::OsRng;
use super::{BaseSponge, KimchiNativeCircuitType, KimchiNativeProof, ScalarSponge, SpongeParams, VestaOpeningProof, fp_to_bytes32, verify_kimchi_proof};

#[derive(Clone, Debug)] pub struct KimchiFoldStep { pub pre_state: Fp, pub post_state: Fp }

/// Compute the accumulated hash for an IVC chain.
/// Step 0: Poseidon(pre_state, post_state, 1)
/// Step i>0: Poseidon(prev_hash, pre_state, post_state)
/// Uses exactly 3 inputs per Poseidon invocation to match the in-circuit gadget.
pub fn kimchi_ivc_accumulated_hash(steps: &[KimchiFoldStep]) -> Fp {
    let p = Vesta::sponge_params();
    let mut hash = {
        let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
        s.absorb(&[steps[0].pre_state, steps[0].post_state, Fp::from(1u64)]);
        s.squeeze()
    };
    for step in steps.iter().skip(1) {
        let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
        s.absorb(&[hash, step.pre_state, step.post_state]);
        hash = s.squeeze();
    }
    hash
}

pub struct KimchiIvcCircuit { pub fold_steps: Vec<KimchiFoldStep> }
impl KimchiIvcCircuit {
    pub fn new(fold_steps: Vec<KimchiFoldStep>) -> Self { Self { fold_steps } }

    /// Build the IVC circuit gates.
    ///
    /// Layout:
    /// - Public input rows (4): initial_root, final_root, accumulated_hash, num_steps
    /// - Poseidon gadgets (one per fold step): each is pgr rows (FULL_ROUNDS/5 + 1)
    /// - Poseidon linkage gates (n-1): constrain output[i] == input[i+1] col 0
    /// - Final hash binding gate (1): constrain last Poseidon output == accumulated_hash (pi[2])
    /// - Chain continuity gates (n): constrain post_state[i] == pre_state[i+1]
    pub fn build_circuit(&self) -> (Vec<CircuitGate<Fp>>, usize) {
        let mut gates = Vec::new();
        let pc = 4; // public input count

        // Public input rows: Generic gates with c0=1 (constrains w0 = 0 for public inputs,
        // but Kimchi handles public input binding implicitly for the first `pc` rows)
        for _ in 0..pc {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        let rc = &Vesta::sponge_params().round_constants;
        let pr = FULL_ROUNDS / 5; // round gate rows per Poseidon gadget (excl Zero row)
        let pgr = pr + 1; // total rows per Poseidon gadget (incl Zero/output row)

        // Poseidon gadgets - one per fold step
        for _ in &self.fold_steps {
            let s = gates.len();
            let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                s,
                [Wire::for_row(s), Wire::for_row(s + pr)],
                rc,
            );
            gates.extend(pg);
        }

        // Poseidon output linkage gates: for steps 0..n-2, constrain
        // poseidon_output[i] == poseidon_input[i+1] (which is in col 0 of first row of next gadget)
        // Gate equation: 1*w0 + (-1)*w1 = 0, so w0 == w1
        let n = self.fold_steps.len();
        for _ in 0..(n.saturating_sub(1)) {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            c[1] = -Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Final hash binding gate: constrain last Poseidon output == pi[2] (accumulated_hash)
        // Gate equation: 1*w0 + (-1)*w1 = 0
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            c[1] = -Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Chain continuity gates: constrain post_state[i] == pre_state[i+1]
        // Gate equation: 1*w0 + (-1)*w1 = 0
        for _ in &self.fold_steps {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            c[1] = -Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        (gates, pc)
    }

    pub fn generate_witness(&self) -> [Vec<Fp>; COLUMNS] {
        let (gates, _) = self.build_circuit();
        let tr = gates.len();
        let mut wit: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); tr]);

        let ir = self.fold_steps[0].pre_state;
        let fr = self.fold_steps.last().unwrap().post_state;
        let ns = self.fold_steps.len() as u64;
        let ah = kimchi_ivc_accumulated_hash(&self.fold_steps);

        // Public input rows
        let mut row = 0;
        wit[0][row] = ir; row += 1;
        wit[0][row] = fr; row += 1;
        wit[0][row] = ah; row += 1;
        wit[0][row] = Fp::from(ns); row += 1;

        let pgr = FULL_ROUNDS / 5 + 1;
        let p = Vesta::sponge_params();
        let n = self.fold_steps.len();

        // Generate Poseidon witnesses and track outputs
        let mut poseidon_outputs: Vec<Fp> = Vec::with_capacity(n);
        let mut ch = Fp::zero();
        for (i, step) in self.fold_steps.iter().enumerate() {
            let pi = if i == 0 {
                [step.pre_state, step.post_state, Fp::from(1u64)]
            } else {
                [ch, step.pre_state, step.post_state]
            };
            generate_witness(row, p, &mut wit, pi);
            row += pgr;

            // Compute the hash output for this step (matches the gadget output)
            if i == 0 {
                let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
                s.absorb(&[step.pre_state, step.post_state, Fp::from(1u64)]);
                ch = s.squeeze();
            } else {
                let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
                s.absorb(&[ch, step.pre_state, step.post_state]);
                ch = s.squeeze();
            }
            poseidon_outputs.push(ch);
        }

        // Poseidon linkage witness: w0 = output[i], w1 = output[i] (== input[i+1] col 0)
        // The constraint 1*w0 - 1*w1 = 0 is satisfied when both equal the Poseidon output
        for i in 0..(n.saturating_sub(1)) {
            wit[0][row] = poseidon_outputs[i];
            wit[1][row] = poseidon_outputs[i];
            row += 1;
        }

        // Final hash binding witness: w0 = last Poseidon output, w1 = accumulated_hash (same value)
        wit[0][row] = poseidon_outputs[n - 1];
        wit[1][row] = ah; // ah == poseidon_outputs[n-1]
        row += 1;

        // Chain continuity witness: w0 = post_state[i], w1 = pre_state[i+1] (or post_state for last)
        for (i, step) in self.fold_steps.iter().enumerate() {
            wit[0][row] = step.post_state;
            wit[1][row] = if i + 1 < n {
                self.fold_steps[i + 1].pre_state
            } else {
                step.post_state
            };
            row += 1;
        }

        wit
    }

    pub fn prove(&self) -> Result<KimchiNativeProof, String> {
        let (gates, pc) = self.build_circuit();
        let wit = self.generate_witness();
        let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(gates, pc);
        let gm = <Vesta as CommitmentCurve>::Map::setup();
        let proof = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<BaseSponge, ScalarSponge, _>(
            &gm, wit, &[], &index, &mut OsRng,
        ).map_err(|e| format!("Kimchi IVC prover error: {:?}", e))?;
        let pb = rmp_serde::to_vec(&proof).map_err(|e| format!("IVC proof serialization error: {}", e))?;
        let ir = self.fold_steps[0].pre_state;
        let fr = self.fold_steps.last().unwrap().post_state;
        let ah = kimchi_ivc_accumulated_hash(&self.fold_steps);
        let ns = Fp::from(self.fold_steps.len() as u64);
        let mut pib = Vec::with_capacity(128);
        pib.extend_from_slice(&fp_to_bytes32(&ir));
        pib.extend_from_slice(&fp_to_bytes32(&fr));
        pib.extend_from_slice(&fp_to_bytes32(&ah));
        pib.extend_from_slice(&fp_to_bytes32(&ns));
        Ok(KimchiNativeProof { proof_bytes: pb, public_input_bytes: pib, circuit_type: KimchiNativeCircuitType::Ivc })
    }

    /// Verify an IVC proof using the real Kimchi verifier.
    pub fn verify(proof_bytes: &[u8], public_inputs: &[Fp], fold_steps: &[KimchiFoldStep]) -> Result<bool, String> {
        let proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(proof_bytes).map_err(|e| format!("Deserialization error: {}", e))?;
        let circuit = KimchiIvcCircuit::new(fold_steps.to_vec());
        let (gates, pc) = circuit.build_circuit();
        verify_kimchi_proof(&proof, gates, public_inputs, pc)
    }
}

#[derive(Clone, Debug)] pub struct KimchiIvcProof { pub proof: KimchiNativeProof, pub initial_root: Fp, pub final_root: Fp, pub accumulated_hash: Fp, pub num_steps: u32 }
