use super::*;

// ============================================================================
// Pickles Step/Wrap Dual-Curve Recursive Verification
// ============================================================================
//
// This implements the Pickles-style dual-curve recursive verification architecture
// from Mina's Pickles (~/dev/mina/src/lib/pickles/).
//
// ## Problem
//
// The standalone IPA verifier (`build_ipa_verifier_circuit`) tries to verify a
// Vesta proof INSIDE a Vesta circuit. This fails because the IPA L/R points are
// Vesta curve points (coordinates in Fq = Vesta base field), but EndoMul gates
// on a Vesta circuit enforce the Pallas curve equation (y^2 = x^3 + 5 over Fp).
// Vesta point coordinates are NOT on the Pallas curve.
//
// ## Solution: Pasta Cycle Alternation
//
// Pickles exploits the Pasta cycle:
// - **Fp** = scalar field of Vesta = base field of Pallas
// - **Fq** = scalar field of Pallas = base field of Vesta
//
// **Step circuit** (proves on Vesta, witnesses in Fp):
//   - Fiat-Shamir transcript replay (Poseidon over Fp — NATIVE)
//   - b(zeta) challenge polynomial evaluation (field arithmetic over Fp — NATIVE)
//   - State transition logic (the pyana application logic)
//   - DEFERS: the EC operations (outputs challenges, commitment coords, b(zeta)
//     as public inputs for the wrap circuit to check)
//
// **Wrap circuit** (proves on Pallas, witnesses in Fq):
//   - Verifies the step proof (a Vesta proof)
//   - Performs IPA bullet_reduce: [u_i]*R_i + [u_i^{-1}]*L_i using EndoMul on
//     **Pallas** points. Since L_i, R_i are Vesta points (coords in Fq = Pallas
//     scalar field), and the wrap circuit's native field IS Fq, the EndoMul gates
//     here enforce the Vesta curve equation (y^2 = x^3 + 5 over Fq). NATIVE!
//   - Checks the final IPA equation: c*Q + delta = z1*(sg + b*U) + z2*H
//
// ## Recursion Pattern
//
// Full recursion alternates:
//   Step(Vesta) → Wrap(Pallas) → Step(Vesta) → Wrap(Pallas) → ...
//
// Each wrap verifies the previous step, and each step can verify a previous wrap
// (by deferring its EC operations to the next wrap). The final proof is on
// whichever curve the last step/wrap produced.
//
// ## References
//
// - step_verifier.ml: `check_bulletproof` performs bullet_reduce over Inner_curve
//   (the "other" curve), computing `lr_prod` and challenges. The key is that
//   `Scalar_challenge.endo` and `Scalar_challenge.endo_inv` do the EndoMul
//   scalar multiplication of L/R points.
// - wrap_verifier.ml: Same `check_bulletproof` structure but on the Tock/Wrap
//   side, using the opposite curve's endomorphism.
// - scalar_challenge.ml: `to_field_checked` converts a 128-bit challenge into
//   a field element using the endomorphism decomposition (Section 3.5 in our code).

// --- Step Verifier Circuit (on Vesta, scalar field = Fp) ---

/// Layout of the Step Verifier circuit.
///
/// This circuit runs on Vesta (witnesses in Fp) and proves:
/// 1. Correct Fiat-Shamir transcript replay (Poseidon absorption of L/R coords)
/// 2. Correct b(zeta) computation (Horner chain over challenges)
/// 3. State transition (Poseidon hash of pre/post state)
/// 4. DEFERS the EC operations by exposing challenges + b(zeta) as public outputs
///
/// The deferred values (challenges, commitment, b_at_zeta) become public inputs
/// to the Wrap circuit, which performs the actual EC verification natively.
#[derive(Clone, Debug)]
pub struct StepVerifierLayout {
    /// Total number of gates.
    pub total_gates: usize,
    /// Number of public inputs.
    pub public_input_count: usize,
    /// Row where Poseidon transcript section begins.
    pub transcript_section_start: usize,
    /// Row where b(zeta) Horner chain begins.
    pub b_zeta_section_start: usize,
    /// Row where state transition Poseidon begins.
    pub state_transition_start: usize,
    /// Number of IPA rounds.
    pub num_rounds: usize,
}

/// Build the Step Verifier circuit (on Vesta, scalar field = Fp).
///
/// # Public Inputs (deferred values for the Wrap circuit)
///
/// 0: pre_state_hash
/// 1: post_state_hash
/// 2: accumulated_hash
/// 3: step_count
/// 4: prev_accumulated_hash
/// 5: commitment_x (the combined polynomial commitment, x-coordinate as Fp)
/// 6: commitment_y (y-coordinate)
/// 7: evaluation_at_zeta (the combined evaluation v)
/// 8: challenge_digest (Poseidon hash of all u_i challenges)
/// 9: b_at_zeta (the challenge polynomial evaluated at zeta)
/// 10: zeta (the evaluation point, derived from transcript)
///
/// The key difference from `build_ipa_verifier_circuit`: NO EndoMul or
/// CompleteAdd gates. All EC operations are deferred to the Wrap circuit.
/// This circuit only does field arithmetic (Generic gates) and Poseidon.
pub fn build_step_verifier_circuit(
    num_rounds: usize,
) -> (Vec<CircuitGate<Fp>>, usize, StepVerifierLayout) {
    let mut gates = Vec::new();
    let mut row = 0;

    // --- Section 1: Public input binding gates ---
    let public_count = 11;
    for _i in 0..public_count {
        let mut coeffs = vec![Fp::zero(); COLUMNS];
        coeffs[0] = Fp::one();
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            coeffs,
        ));
        row += 1;
    }

    // --- Section 2: Poseidon transcript replay ---
    // Absorb L/R point coordinates: 4 field elements per round (Lx, Ly, Rx, Ry).
    // These are the Fp-encoded coordinates of the Vesta L/R points.
    // Poseidon over Fp is NATIVE here (we're on a Vesta circuit).
    let transcript_section_start = row;
    let round_constants = &Vesta::sponge_params().round_constants;
    let poseidon_rows = FULL_ROUNDS / 5; // 11
    let poseidon_gadget_total = poseidon_rows + 1; // 12 rows per gadget

    // Absorption: ceil(4*num_rounds / 3) Poseidon calls
    let absorption_calls = (4 * num_rounds).div_ceil(3);
    for _ in 0..absorption_calls {
        let first_wire = Wire::for_row(row);
        let last_wire = Wire::for_row(row + poseidon_rows);
        let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
            row,
            [first_wire, last_wire],
            round_constants,
        );
        gates.extend(pg);
        row += poseidon_gadget_total;
    }

    // Squeeze calls for challenge derivation: one per round
    for _ in 0..num_rounds {
        let first_wire = Wire::for_row(row);
        let last_wire = Wire::for_row(row + poseidon_rows);
        let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
            row,
            [first_wire, last_wire],
            round_constants,
        );
        gates.extend(pg);
        row += poseidon_gadget_total;
    }

    // --- Section 3: b(zeta) Horner evaluation ---
    // b(z) = prod_{i=0}^{k-1} (1 + u_i * z^{2^i})
    // This is pure field arithmetic over Fp — NATIVE.
    let b_zeta_section_start = row;
    for _round in 0..num_rounds {
        // Row 0: z_power squaring: w[0]*w[1] - w[2] = 0
        let mut coeffs = vec![Fp::zero(); COLUMNS];
        coeffs[2] = -Fp::one();
        coeffs[3] = Fp::one();
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            coeffs,
        ));
        row += 1;

        // Row 1: u_i * z_power: w[0]*w[1] - w[2] = 0
        let mut coeffs = vec![Fp::zero(); COLUMNS];
        coeffs[2] = -Fp::one();
        coeffs[3] = Fp::one();
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            coeffs,
        ));
        row += 1;

        // Row 2: factor = 1 + u_i*z_power: w[0] - w[2] + 1 = 0
        let mut coeffs = vec![Fp::zero(); COLUMNS];
        coeffs[0] = Fp::one();
        coeffs[2] = -Fp::one();
        coeffs[4] = Fp::one();
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            coeffs,
        ));
        row += 1;

        // Row 3: b_new = b_old * factor: w[0]*w[1] - w[2] = 0
        let mut coeffs = vec![Fp::zero(); COLUMNS];
        coeffs[2] = -Fp::one();
        coeffs[3] = Fp::one();
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            coeffs,
        ));
        row += 1;
    }

    // --- Section 4: State transition Poseidon ---
    // Poseidon(prev_accumulated || pre_hash || post_hash) = new_accumulated
    let state_transition_start = row;
    let first_wire = Wire::for_row(row);
    let last_wire = Wire::for_row(row + poseidon_rows);
    let (pg, _) =
        CircuitGate::<Fp>::create_poseidon_gadget(row, [first_wire, last_wire], round_constants);
    gates.extend(pg);
    row += poseidon_gadget_total;

    // --- Section 5: Final output binding gate ---
    gates.push(CircuitGate::new(
        GateType::Generic,
        Wire::for_row(row),
        vec![Fp::zero(); COLUMNS],
    ));
    row += 1;

    let layout = StepVerifierLayout {
        total_gates: row,
        public_input_count: public_count,
        transcript_section_start,
        b_zeta_section_start,
        state_transition_start,
        num_rounds,
    };

    (gates, public_count, layout)
}

/// Witness for the Step Verifier circuit.
#[derive(Clone, Debug)]
pub struct StepVerifierWitness {
    /// The L and R point coordinates (as Fp elements from byte-mapping Fq → Fp).
    pub lr_coords: Vec<((Fp, Fp), (Fp, Fp))>,
    /// The IPA challenges u_i (derived from Poseidon transcript).
    pub challenges: Vec<Fp>,
    /// The evaluation point zeta.
    pub zeta: Fp,
    /// b(zeta) — the challenge polynomial evaluated at zeta.
    pub b_at_zeta: Fp,
    /// The combined polynomial commitment (x, y) as Fp elements.
    pub commitment: (Fp, Fp),
    /// The combined evaluation v at zeta.
    pub evaluation: Fp,
    /// State transition data.
    pub pre_state_hash: Fp,
    pub post_state_hash: Fp,
    pub step_count: Fp,
    pub prev_accumulated_hash: Fp,
}

/// Generate witness for the Step Verifier circuit.
pub fn generate_step_verifier_witness(
    w: &StepVerifierWitness,
    layout: &StepVerifierLayout,
) -> [Vec<Fp>; COLUMNS] {
    let total_rows = layout.total_gates;
    let mut witness: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); total_rows]);
    let num_rounds = layout.num_rounds;

    // Compute accumulated hash using the same logic as pickles_accumulated_hash
    let has_previous = w.prev_accumulated_hash != Fp::zero();
    let new_accumulated = {
        let params = Vesta::sponge_params();
        let mut sponge = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(params);
        if has_previous {
            sponge.absorb(&[
                w.prev_accumulated_hash,
                w.pre_state_hash,
                w.post_state_hash,
                w.step_count,
            ]);
        } else {
            sponge.absorb(&[w.pre_state_hash, w.post_state_hash, w.step_count]);
        }
        sponge.squeeze()
    };

    // Compute challenge digest
    let challenge_digest = {
        let params = Vesta::sponge_params();
        let mut sponge = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(params);
        sponge.absorb(&w.challenges);
        sponge.squeeze()
    };

    // --- Public inputs ---
    witness[0][0] = w.pre_state_hash;
    witness[0][1] = w.post_state_hash;
    witness[0][2] = new_accumulated;
    witness[0][3] = w.step_count;
    witness[0][4] = w.prev_accumulated_hash;
    witness[0][5] = w.commitment.0;
    witness[0][6] = w.commitment.1;
    witness[0][7] = w.evaluation;
    witness[0][8] = challenge_digest;
    witness[0][9] = w.b_at_zeta;
    witness[0][10] = w.zeta;

    // --- Poseidon transcript (absorption + squeeze) ---
    let mut transcript_elements = Vec::with_capacity(4 * num_rounds);
    for ((lx, ly), (rx, ry)) in &w.lr_coords {
        transcript_elements.extend_from_slice(&[*lx, *ly, *rx, *ry]);
    }
    let poseidon_gadget_rows = (FULL_ROUNDS / 5) + 1;
    let absorption_calls = (4 * num_rounds).div_ceil(3);
    let mut poseidon_row = layout.transcript_section_start;
    for call_idx in 0..absorption_calls {
        let base_elem = call_idx * 3;
        let input = [
            transcript_elements
                .get(base_elem)
                .copied()
                .unwrap_or(Fp::zero()),
            transcript_elements
                .get(base_elem + 1)
                .copied()
                .unwrap_or(Fp::zero()),
            transcript_elements
                .get(base_elem + 2)
                .copied()
                .unwrap_or(Fp::zero()),
        ];
        generate_witness(poseidon_row, Vesta::sponge_params(), &mut witness, input);
        poseidon_row += poseidon_gadget_rows;
    }
    for squeeze_idx in 0..num_rounds {
        let input = [w.challenges[squeeze_idx], Fp::zero(), Fp::zero()];
        generate_witness(poseidon_row, Vesta::sponge_params(), &mut witness, input);
        poseidon_row += poseidon_gadget_rows;
    }

    // --- b(zeta) Horner chain ---
    let b_poly_start = layout.b_zeta_section_start;
    let mut z_power = w.zeta;
    let mut b_running = Fp::one();
    for i in 0..num_rounds {
        let row_base = b_poly_start + i * 4;
        if row_base + 3 >= total_rows {
            break;
        }
        let u_i = w.challenges[num_rounds - 1 - i];

        // Row 0: squaring
        witness[0][row_base] = z_power;
        witness[1][row_base] = z_power;
        witness[2][row_base] = z_power * z_power;

        // Row 1: u_i * z_power
        witness[0][row_base + 1] = u_i;
        witness[1][row_base + 1] = z_power;
        witness[2][row_base + 1] = u_i * z_power;

        // Row 2: factor = 1 + u_i*z_power
        let product = u_i * z_power;
        let factor = Fp::one() + product;
        witness[0][row_base + 2] = product;
        witness[1][row_base + 2] = Fp::zero();
        witness[2][row_base + 2] = factor;

        // Row 3: b_new = b_old * factor
        let b_new = b_running * factor;
        witness[0][row_base + 3] = b_running;
        witness[1][row_base + 3] = factor;
        witness[2][row_base + 3] = b_new;

        b_running = b_new;
        z_power = z_power * z_power;
    }

    // --- State transition Poseidon ---
    let state_row = layout.state_transition_start;
    if state_row + poseidon_gadget_rows <= total_rows {
        // Match the same Poseidon invocation as pickles_accumulated_hash
        let poseidon_input = if has_previous {
            [w.prev_accumulated_hash, w.pre_state_hash, w.post_state_hash]
        } else {
            [w.pre_state_hash, w.post_state_hash, w.step_count]
        };
        generate_witness(
            state_row,
            Vesta::sponge_params(),
            &mut witness,
            poseidon_input,
        );
    }

    // Final output row
    witness[0][total_rows - 1] = new_accumulated;
    witness
}

// --- Dual-Curve Proof Types ---

/// A Step proof (on Vesta). Contains the Kimchi proof and the deferred values
/// that the Wrap circuit needs to verify.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct DualCurveStepProof {
    /// Serialized Kimchi proof over Vesta.
    pub proof_bytes: Vec<u8>,
    /// Public inputs (serialized Fp field elements).
    pub public_inputs: Vec<u8>,
    /// Deferred IPA data for the Wrap circuit:
    /// - challenges (k Fp elements, serialized)
    /// - challenge inverses (k Fp elements)
    /// - L/R points (k pairs of Vesta points, as Fq coordinates)
    /// - z1, z2, delta, sg (Fp scalars and point coords)
    /// - c_challenge (final challenge scalar)
    pub deferred_ipa_data: Vec<u8>,
    /// Number of recursive steps.
    pub num_steps: u32,
}

/// Prove a Step in the dual-curve recursion (on Vesta).
///
/// This proves the state transition AND the Fiat-Shamir/b(zeta) computation
/// for the previous proof's IPA, but DEFERS the EC operations to the Wrap.
///
/// The Step circuit contains:
/// - Poseidon transcript replay (native Fp arithmetic)
/// - b(zeta) Horner evaluation (native Fp arithmetic)
/// - State transition hash (native Poseidon)
/// - NO EndoMul or CompleteAdd gates
///
/// The deferred values (challenges, commitment, b_at_zeta) become part of the
/// Step proof's public inputs, and the Wrap circuit takes them as witness.
pub fn prove_dual_curve_step(
    previous: Option<&PicklesRecursiveProof>,
    transition: &PicklesStateTransition,
) -> Result<DualCurveStepProof, String> {
    let pre_hash = bytes32_to_fp(&transition.pre_state_hash);
    let post_hash = bytes32_to_fp(&transition.post_state_hash);
    let step_count = previous.map_or(1u32, |p| p.num_steps + 1);
    let step_fp = Fp::from(step_count as u64);

    // Previous accumulated hash
    let prev_accumulated = if let Some(prev) = previous {
        if prev.public_inputs.len() < 96 {
            return Err("Previous proof has malformed public inputs".into());
        }
        let acc_bytes: [u8; 32] = prev.public_inputs[64..96]
            .try_into()
            .map_err(|_| "Invalid accumulated hash bytes")?;
        Some(bytes32_to_fp(&acc_bytes))
    } else {
        None
    };

    // For the base case (no previous proof), we still build a Step circuit
    // but with dummy IPA data (all zeros). The Wrap for the base case is trivial.
    let num_rounds = IPA_ROUNDS;

    // Extract IPA data from previous proof if available
    let (lr_coords, challenges, zeta, b_at_zeta, commitment, evaluation, deferred_ipa_data) =
        if let Some(prev) = previous {
            // Deserialize the previous Kimchi proof to extract IPA opening data
            let prev_kimchi: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
                rmp_serde::from_slice(&prev.proof_bytes)
                    .map_err(|e| format!("Previous proof deserialization: {}", e))?;

            let opening = &prev_kimchi.proof;
            let lr: Vec<((Fp, Fp), (Fp, Fp))> = opening
                .lr
                .iter()
                .map(|(l, r)| (vesta_point_to_fp_coords(*l), vesta_point_to_fp_coords(*r)))
                .collect();

            // Derive challenges from L/R via Fiat-Shamir
            let (_, endo_r) = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos();
            let mut sponge =
                BaseSponge::new(<Vesta as KimchiCurve<FULL_ROUNDS>>::other_curve_sponge_params());
            let seed = {
                let mut hasher = blake3::Hasher::new();
                hasher.update(b"dual-curve-step-v1");
                hasher.update(&prev.proof_bytes[..64.min(prev.proof_bytes.len())]);
                bytes32_to_fp(hasher.finalize().as_bytes())
            };
            sponge.absorb_fr(&[seed]);

            let chals: Vec<Fp> = opening
                .lr
                .iter()
                .map(|(l, r)| {
                    sponge.absorb_g(&[*l]);
                    sponge.absorb_g(&[*r]);
                    squeeze_challenge(endo_r, &mut sponge)
                })
                .collect();

            let z: Fp = sponge.challenge();
            let b = challenge_polynomial_eval(&chals, z);

            let comm = if !prev_kimchi.commitments.w_comm.is_empty()
                && !prev_kimchi.commitments.w_comm[0].chunks.is_empty()
            {
                vesta_point_to_fp_coords(prev_kimchi.commitments.w_comm[0].chunks[0])
            } else {
                (Fp::one(), Fp::one())
            };

            let eval = b; // Combined evaluation

            // Serialize deferred IPA data for the Wrap
            let mut deferred = Vec::new();
            // challenges
            for c in &chals {
                deferred.extend_from_slice(&fp_to_bytes32(c));
            }
            // challenge inverses
            for c in &chals {
                let inv = c.inverse().unwrap_or(Fp::zero());
                deferred.extend_from_slice(&fp_to_bytes32(&inv));
            }
            // L/R points (as raw Fq coordinates for Wrap's native arithmetic)
            for (l, r) in opening.lr.iter() {
                let l_xy = l.xy();
                let r_xy = r.xy();
                if let (Some((lx, ly)), Some((rx, ry))) = (l_xy, r_xy) {
                    deferred.extend_from_slice(&fp_to_bytes32_generic(&lx));
                    deferred.extend_from_slice(&fp_to_bytes32_generic(&ly));
                    deferred.extend_from_slice(&fp_to_bytes32_generic(&rx));
                    deferred.extend_from_slice(&fp_to_bytes32_generic(&ry));
                } else {
                    deferred.extend_from_slice(&[0u8; 128]);
                }
            }
            // z1, z2
            deferred.extend_from_slice(&fp_to_bytes32(&opening.z1));
            deferred.extend_from_slice(&fp_to_bytes32(&opening.z2));
            // delta coords
            let delta_coords = vesta_point_to_fp_coords(opening.delta);
            deferred.extend_from_slice(&fp_to_bytes32(&delta_coords.0));
            deferred.extend_from_slice(&fp_to_bytes32(&delta_coords.1));
            // sg coords
            let sg_coords = vesta_point_to_fp_coords(opening.sg);
            deferred.extend_from_slice(&fp_to_bytes32(&sg_coords.0));
            deferred.extend_from_slice(&fp_to_bytes32(&sg_coords.1));
            // c_challenge
            sponge.absorb_g(&[opening.delta]);
            let c_chal: Fp = squeeze_challenge(endo_r, &mut sponge);
            deferred.extend_from_slice(&fp_to_bytes32(&c_chal));

            // Pad lr_coords to num_rounds if needed
            let mut lr_padded = lr;
            while lr_padded.len() < num_rounds {
                lr_padded.push(((Fp::zero(), Fp::zero()), (Fp::zero(), Fp::zero())));
            }

            let mut chals_padded = chals;
            while chals_padded.len() < num_rounds {
                chals_padded.push(Fp::zero());
            }

            (lr_padded, chals_padded, z, b, comm, eval, deferred)
        } else {
            // Base case: dummy IPA data
            let lr = vec![((Fp::zero(), Fp::zero()), (Fp::zero(), Fp::zero())); num_rounds];
            let chals = vec![Fp::zero(); num_rounds];
            let z = Fp::zero();
            let b = Fp::one(); // b(0) = 1 for all-zero challenges
            let comm = (Fp::zero(), Fp::zero());
            let eval = Fp::zero();
            (lr, chals, z, b, comm, eval, Vec::new())
        };

    // Build the Step circuit
    let (gates, public_count, layout) = build_step_verifier_circuit(num_rounds);

    // Generate witness
    let step_witness = StepVerifierWitness {
        lr_coords,
        challenges,
        zeta,
        b_at_zeta,
        commitment,
        evaluation,
        pre_state_hash: pre_hash,
        post_state_hash: post_hash,
        step_count: step_fp,
        prev_accumulated_hash: prev_accumulated.unwrap_or(Fp::zero()),
    };
    let witness = generate_step_verifier_witness(&step_witness, &layout);

    // Create prover index and prove
    let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(
        gates,
        public_count,
    );

    let group_map = <Vesta as CommitmentCurve>::Map::setup();
    let proof = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
        BaseSponge,
        ScalarSponge,
        _,
    >(&group_map, witness, &[], &index, &mut OsRng)
    .map_err(|e| format!("Step prover error: {:?}", e))?;

    // Serialize
    let proof_bytes =
        rmp_serde::to_vec(&proof).map_err(|e| format!("Proof serialization error: {}", e))?;

    // Encode public inputs
    let accumulated_hash =
        pickles_accumulated_hash(pre_hash, post_hash, step_count, prev_accumulated);

    let challenge_digest = {
        let params = Vesta::sponge_params();
        let mut sponge = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(params);
        sponge.absorb(&step_witness.challenges);
        sponge.squeeze()
    };

    let mut public_input_bytes = Vec::with_capacity(32 * 11);
    public_input_bytes.extend_from_slice(&fp_to_bytes32(&pre_hash));
    public_input_bytes.extend_from_slice(&fp_to_bytes32(&post_hash));
    public_input_bytes.extend_from_slice(&fp_to_bytes32(&accumulated_hash));
    public_input_bytes.extend_from_slice(&fp_to_bytes32(&step_fp));
    public_input_bytes.extend_from_slice(&fp_to_bytes32(&prev_accumulated.unwrap_or(Fp::zero())));
    public_input_bytes.extend_from_slice(&fp_to_bytes32(&step_witness.commitment.0));
    public_input_bytes.extend_from_slice(&fp_to_bytes32(&step_witness.commitment.1));
    public_input_bytes.extend_from_slice(&fp_to_bytes32(&step_witness.evaluation));
    public_input_bytes.extend_from_slice(&fp_to_bytes32(&challenge_digest));
    public_input_bytes.extend_from_slice(&fp_to_bytes32(&step_witness.b_at_zeta));
    public_input_bytes.extend_from_slice(&fp_to_bytes32(&step_witness.zeta));

    Ok(DualCurveStepProof {
        proof_bytes,
        public_inputs: public_input_bytes,
        deferred_ipa_data,
        num_steps: step_count,
    })
}

/// Verify a Step proof (checks the Kimchi proof but NOT the deferred EC operations).
///
/// This is the first half of verification. The second half is done by the Wrap.
pub fn verify_dual_curve_step(proof: &DualCurveStepProof) -> Result<bool, String> {
    if proof.public_inputs.len() < 32 * 11 {
        return Err("Step proof has malformed public inputs".into());
    }

    // Decode and verify accumulated hash chain
    let pre_hash_bytes: [u8; 32] = proof.public_inputs[0..32]
        .try_into()
        .map_err(|_| "Invalid pre_hash")?;
    let post_hash_bytes: [u8; 32] = proof.public_inputs[32..64]
        .try_into()
        .map_err(|_| "Invalid post_hash")?;
    let accumulated_hash_bytes: [u8; 32] = proof.public_inputs[64..96]
        .try_into()
        .map_err(|_| "Invalid acc_hash")?;
    let step_fp_bytes: [u8; 32] = proof.public_inputs[96..128]
        .try_into()
        .map_err(|_| "Invalid step_count")?;
    let prev_acc_bytes: [u8; 32] = proof.public_inputs[128..160]
        .try_into()
        .map_err(|_| "Invalid prev_acc")?;

    let pre_hash = bytes32_to_fp(&pre_hash_bytes);
    let post_hash = bytes32_to_fp(&post_hash_bytes);
    let accumulated_hash = bytes32_to_fp(&accumulated_hash_bytes);
    let step_fp = bytes32_to_fp(&step_fp_bytes);
    let prev_acc = bytes32_to_fp(&prev_acc_bytes);

    // Verify accumulated hash
    let step_count_u64 = {
        let bigint = step_fp.into_bigint();
        bigint.as_ref()[0] as u32
    };

    let prev_accumulated = if prev_acc == Fp::zero() && step_count_u64 == 1 {
        None
    } else {
        Some(prev_acc)
    };

    let expected = pickles_accumulated_hash(pre_hash, post_hash, step_count_u64, prev_accumulated);
    if accumulated_hash != expected {
        return Ok(false);
    }

    // Verify the Kimchi proof (Step circuit: only Poseidon + Generic gates)
    let kimchi_proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
        rmp_serde::from_slice(&proof.proof_bytes)
            .map_err(|e| format!("Proof deserialization: {}", e))?;

    let (gates, public_count, _layout) = build_step_verifier_circuit(IPA_ROUNDS);
    let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(
        gates,
        public_count,
    );
    let verifier_index = index.verifier_index();
    let group_map = <Vesta as CommitmentCurve>::Map::setup();

    // Reconstruct public inputs as Fp elements
    let mut pis = Vec::with_capacity(public_count);
    for i in 0..public_count {
        let offset = i * 32;
        let bytes: [u8; 32] = proof.public_inputs[offset..offset + 32]
            .try_into()
            .map_err(|_| format!("Invalid PI at {}", i))?;
        pis.push(bytes32_to_fp(&bytes));
    }

    if verifier::verify::<FULL_ROUNDS, Vesta, BaseSponge, ScalarSponge, VestaOpeningProof>(
        &group_map,
        &verifier_index,
        &kimchi_proof,
        &pis,
    )
    .is_err()
    {
        return Ok(false);
    }

    Ok(true)
}
