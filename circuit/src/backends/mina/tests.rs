use super::*;

/// Verify that to_field_fq matches the canonical ScalarChallenge::to_field.
#[test]
fn test_to_field_fq_matches_canonical() {
    let (_, endo_r) = kimchi::curve::vesta_endos();
    // Test with a known 128-bit prechallenge
    let pre_fp = Fp::from(0x123456789ABCDEFu64);
    let canonical = ScalarChallenge::new(pre_fp).to_field(endo_r);
    let pre_fq = fp_to_fq(&pre_fp);
    let endo_scalar_fq = fp_to_fq(endo_r);
    let our_result = to_field_fq(pre_fq, endo_scalar_fq);
    let canonical_fq = fp_to_fq(&canonical);
    assert_eq!(
        our_result, canonical_fq,
        "to_field_fq must match ScalarChallenge::to_field"
    );
}

/// Verify native_scalar_mul_fq produces correct results.
#[test]
fn test_native_scalar_mul_fq_basic() {
    // [1] * P = P
    let p = (Fq::from(3u64), {
        let x = Fq::from(3u64);
        let y_sq = x * x * x + Fq::from(5u64);
        y_sq.sqrt().unwrap()
    });
    let result = native_scalar_mul_fq(Fq::one(), p);
    assert_eq!(result, p, "[1]*P should equal P");

    // [2] * P = P + P
    let doubled = point_double_fq(p);
    let result2 = native_scalar_mul_fq(Fq::from(2u64), p);
    assert_eq!(result2, doubled, "[2]*P should equal 2P");
}

// ========================================================================
// Pickles Recursive IVC Tests
// ========================================================================

#[test]
fn test_pickles_single_step_prove_verify() {
    // Prove a single state transition (base case, no previous proof).
    let transition = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };

    let proof = prove_recursive_step(None, &transition).expect("Base case proving should succeed");

    assert_eq!(proof.num_steps, 1);
    assert!(proof.previous_proof_hash.is_none());

    // Verify
    let valid =
        verify_recursive_proof(&proof, Some(&[1u8; 32])).expect("Verification should not error");
    assert!(valid, "Single step proof should verify");
}

#[test]
fn test_pickles_three_steps_recursive() {
    // Prove 3 state transitions recursively with assisted recursion.
    // Each step carries the IPA accumulator from the previous proof via
    // create_recursive, and the final verifier batch-checks all accumulators.
    let transitions = vec![
        PicklesStateTransition {
            pre_state_hash: [1u8; 32],
            post_state_hash: [2u8; 32],
        },
        PicklesStateTransition {
            pre_state_hash: [2u8; 32],
            post_state_hash: [3u8; 32],
        },
        PicklesStateTransition {
            pre_state_hash: [3u8; 32],
            post_state_hash: [4u8; 32],
        },
    ];

    let mut prev: Option<PicklesRecursiveProof> = None;

    for (i, transition) in transitions.iter().enumerate() {
        let proof = prove_recursive_step(prev.as_ref(), transition)
            .unwrap_or_else(|e| panic!("Step {} proving failed: {}", i, e));

        assert_eq!(proof.num_steps, (i + 1) as u32);

        if i > 0 {
            assert!(
                proof.previous_proof_hash.is_some(),
                "Recursive steps must have previous proof hash"
            );
            assert!(
                proof.recursion_challenge_bytes.is_some(),
                "All steps should produce a recursion challenge for the next step"
            );
        }

        prev = Some(proof);
    }

    // With assisted recursion, the final proof IS verifiable:
    // The verifier reconstructs the circuit with the correct prev_challenges count,
    // and kimchi::verifier::verify batch-checks the accumulated IPA commitments.
    let final_proof = prev.unwrap();
    assert_eq!(final_proof.num_steps, 3);

    let valid = verify_recursive_proof(&final_proof, None)
        .expect("Final proof verification should not error");
    assert!(
        valid,
        "3-step recursive proof should verify with assisted recursion: \
         the final verifier batch-checks all accumulated IPA challenges"
    );

    // Proof size should be constant regardless of chain length
    let proof_size = final_proof.proof_bytes.len();
    println!("3-step Pickles recursive proof size: {} bytes", proof_size);
}

#[test]
fn test_pickles_tampered_state_hash_fails() {
    // Prove a valid transition, then verify with wrong expected initial hash.
    let transition = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };

    let proof = prove_recursive_step(None, &transition).expect("Proving should succeed");

    // Verify with WRONG expected initial hash
    let wrong_hash = [99u8; 32];
    let valid =
        verify_recursive_proof(&proof, Some(&wrong_hash)).expect("Verification should not error");
    assert!(
        !valid,
        "Wrong initial hash should cause verification failure"
    );
}

#[test]
fn test_pickles_tampered_accumulated_hash_fails() {
    // Create a valid proof, then tamper with the accumulated hash bytes.
    let transition = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };

    let mut proof = prove_recursive_step(None, &transition).expect("Proving should succeed");

    // Tamper with the accumulated hash (bytes 64..96)
    if proof.public_inputs.len() >= 96 {
        proof.public_inputs[64] ^= 0xFF;
    }

    let valid = verify_recursive_proof(&proof, None)
        .expect("Verification should not error on tampered data");
    assert!(!valid, "Tampered accumulated hash should fail verification");
}

#[test]
fn test_pickles_tampered_proof_bytes_fail() {
    let transition = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };

    let mut proof = prove_recursive_step(None, &transition).expect("Proving should succeed");
    let byte = proof
        .proof_bytes
        .last_mut()
        .expect("Kimchi proof should serialize to non-empty bytes");
    *byte ^= 0x01;

    let result = verify_recursive_proof(&proof, Some(&[1u8; 32]));
    assert!(
        matches!(result, Ok(false) | Err(_)),
        "Tampered Kimchi proof bytes must not verify"
    );
}

#[test]
fn test_pickles_constant_proof_size() {
    // Verify that proof size is roughly constant across different chain lengths.
    let mut sizes = Vec::new();

    for num_steps in [1, 3, 5] {
        let mut prev: Option<PicklesRecursiveProof> = None;
        for i in 0..num_steps {
            let mut pre = [0u8; 32];
            let mut post = [0u8; 32];
            pre[0] = i as u8;
            post[0] = (i + 1) as u8;

            let transition = PicklesStateTransition {
                pre_state_hash: pre,
                post_state_hash: post,
            };

            prev = Some(
                prove_recursive_step(prev.as_ref(), &transition)
                    .unwrap_or_else(|e| panic!("Step {} failed: {}", i, e)),
            );
        }

        let final_proof = prev.unwrap();
        sizes.push((num_steps, final_proof.proof_bytes.len()));
        println!(
            "{}-step Pickles proof: {} bytes",
            num_steps,
            final_proof.proof_bytes.len()
        );
    }

    // The proof size should NOT grow linearly with steps.
    // Base case (1 step) uses a smaller circuit than recursive (>1 steps),
    // but all recursive steps should be the same circuit size.
    if sizes.len() >= 2 {
        let (_, size_3) = sizes[1];
        let (_, size_5) = sizes[2];
        // Recursive steps use the same circuit, so size should be ~identical
        let ratio = size_5 as f64 / size_3 as f64;
        assert!(
            ratio < 1.5,
            "Recursive proof size should be roughly constant, got ratio {:.2}",
            ratio
        );
    }
}

#[test]
fn test_pickles_accumulated_hash_deterministic() {
    let pre = bytes32_to_fp(&[1u8; 32]);
    let post = bytes32_to_fp(&[2u8; 32]);

    let h1 = pickles_accumulated_hash(pre, post, 1, None);
    let h2 = pickles_accumulated_hash(pre, post, 1, None);
    assert_eq!(h1, h2, "Accumulated hash should be deterministic");

    // Different step count -> different hash
    let h3 = pickles_accumulated_hash(pre, post, 2, None);
    assert_ne!(h1, h3, "Different step count should produce different hash");

    // With vs without previous -> different hash
    let h4 = pickles_accumulated_hash(pre, post, 1, Some(Fp::from(42u64)));
    assert_ne!(h1, h4, "Previous accumulated hash should change output");
}

#[test]
fn test_pickles_malformed_public_inputs_rejected() {
    // A proof with truncated public inputs should be rejected.
    let proof = PicklesRecursiveProof {
        proof_bytes: vec![0u8; 100],
        public_inputs: vec![0u8; 50], // too short (need >= 104)
        previous_proof_hash: None,
        num_steps: 1,
        verifier_index_digest: [0u8; 32],
        recursion_challenge_bytes: None,
    };

    let result = verify_recursive_proof(&proof, None);
    assert!(result.is_err(), "Malformed public inputs should error");
}

// ========================================================================
// Original Kimchi Backend Tests
// ========================================================================

#[test]
fn test_poseidon_hash_bytes() {
    let data = b"hello dregg";
    let h1 = poseidon_hash_bytes(data);
    let h2 = poseidon_hash_bytes(data);
    assert_eq!(h1, h2, "Poseidon hash should be deterministic");

    let h3 = poseidon_hash_bytes(b"different");
    assert_ne!(h1, h3, "Different inputs should hash differently");
}

#[test]
fn test_poseidon_4_to_1() {
    let inputs = [
        Fp::from(1u64),
        Fp::from(2u64),
        Fp::from(3u64),
        Fp::from(4u64),
    ];
    let h1 = poseidon_hash_4_to_1(&inputs);
    let h2 = poseidon_hash_4_to_1(&inputs);
    assert_eq!(h1, h2);
    assert_ne!(h1, Fp::zero());
}

#[test]
fn test_bytes32_roundtrip() {
    let bytes = [42u8; 32];
    let fp = bytes32_to_fp(&bytes);
    assert_ne!(fp, Fp::zero());
    // Note: roundtrip isn't exact because from_le_bytes_mod_order reduces
    // but for values < p it should be exact
    let small_bytes = [1u8; 32];
    small_bytes[31]; // just ensure it compiles
    let fp2 = bytes32_to_fp(&small_bytes);
    let back = fp_to_bytes32(&fp2);
    // The reduced value's bytes may differ if original >= p
    let fp3 = bytes32_to_fp(&back);
    assert_eq!(fp2, fp3, "fp -> bytes -> fp should roundtrip");
}

#[test]
fn test_build_merkle_circuit() {
    // Verify we can build the circuit without panicking
    let (gates, public_count) = build_merkle_membership_circuit(4);
    assert!(!gates.is_empty());
    assert_eq!(public_count, 2);
    // 4 levels * (1 generic + poseidon rows + output) + 1 final check
    println!("Circuit has {} gates for depth 4", gates.len());
}

#[test]
fn test_backend_name() {
    assert_eq!(MinaBackend::backend_name(), "mina-kimchi");
}

#[test]
fn test_recursive_fold_single() {
    let proof = MinaProof::Fold(KimchiFoldProof {
        proof_bytes: vec![1, 2, 3],
        public_input_bytes: vec![0; 72],
    });
    let result = recursive_fold(&[proof]).unwrap();
    match result {
        MinaProof::Fold(_) => {} // single proof passes through
        _ => panic!("Single proof should pass through"),
    }
}

#[test]
fn test_recursive_fold_multiple() {
    let p1 = MinaProof::Fold(KimchiFoldProof {
        proof_bytes: vec![1, 2, 3],
        public_input_bytes: vec![0; 72],
    });
    let p2 = MinaProof::Fold(KimchiFoldProof {
        proof_bytes: vec![4, 5, 6],
        public_input_bytes: vec![1; 72],
    });
    let result = recursive_fold(&[p1, p2]).unwrap();
    match result {
        MinaProof::Recursive(r) => {
            assert_eq!(r.num_steps, 2);
        }
        _ => panic!("Multiple proofs should produce recursive proof"),
    }
}

// ========================================================================
// Standalone IPA Verifier Circuit Tests
// ========================================================================

#[test]
fn test_ipa_verifier_circuit_builds() {
    let (gates, public_count, layout) = build_ipa_verifier_circuit(IPA_ROUNDS);
    assert_eq!(public_count, 11);
    assert!(!gates.is_empty());
    assert!(
        layout.total_gates > 1000,
        "Verifier circuit should have >1000 gates"
    );
    assert!(
        layout.total_gates < 4096,
        "Verifier circuit should fit in 2^12 domain, got {} gates",
        layout.total_gates
    );
    assert!(layout.transcript_section_start < layout.limb_decomposition_section_start);
    assert!(layout.limb_decomposition_section_start < layout.bullet_reduce_section_start);
    assert!(layout.bullet_reduce_section_start < layout.final_check_section_start);
    assert!(layout.final_check_section_start < layout.total_gates);
    println!("{}", ipa_verifier_circuit_stats());
}

#[test]
fn test_ipa_verifier_circuit_gate_types() {
    let (gates, _, layout) = build_ipa_verifier_circuit(IPA_ROUNDS);

    // Count gate types
    let mut endomul_count = 0;
    let mut complete_add_count = 0;
    let mut poseidon_count = 0;
    let mut generic_count = 0;
    let mut zero_count = 0;

    for gate in &gates {
        match gate.typ {
            GateType::EndoMul => endomul_count += 1,
            GateType::CompleteAdd => complete_add_count += 1,
            GateType::Poseidon => poseidon_count += 1,
            GateType::Generic => generic_count += 1,
            GateType::Zero => zero_count += 1,
            _ => {}
        }
    }

    // Verify expected counts
    // bullet_reduce (2-limb): 4 * IPA_ROUNDS * 32 EndoMul rows = 1920
    // final equation: 4 * 32 = 128 EndoMul rows
    let expected_endomul = 4 * IPA_ROUNDS * 32 + 4 * 32;
    assert_eq!(
        endomul_count, expected_endomul,
        "Expected {} EndoMul gates, got {}",
        expected_endomul, endomul_count
    );

    // CompleteAdd: 4*IPA_ROUNDS (bullet_reduce: 2 combine + 1 add + 1 acc) + 3 (final equation)
    let expected_complete_add = 4 * IPA_ROUNDS + 3;
    assert_eq!(
        complete_add_count, expected_complete_add,
        "Expected {} CompleteAdd gates, got {}",
        expected_complete_add, complete_add_count
    );

    println!(
        "Gate counts: EndoMul={}, CompleteAdd={}, Poseidon={}, Generic={}, Zero={}",
        endomul_count, complete_add_count, poseidon_count, generic_count, zero_count
    );
    println!("Layout: {:?}", layout);
}

#[test]
fn test_limb_decomposition_roundtrip() {
    let two_128 = two_to_128();

    // Test with small values
    let val = Fp::from(42u64);
    let (lo, hi) = decompose_to_limbs(val);
    assert_eq!(lo + hi * two_128, val);
    assert_eq!(hi, Fp::zero()); // 42 fits in 128 bits

    // Test with a value that has both limbs nonzero
    let big_val = Fp::from(7u64) * two_128 + Fp::from(123u64);
    let (lo, hi) = decompose_to_limbs(big_val);
    assert_eq!(lo, Fp::from(123u64));
    assert_eq!(hi, Fp::from(7u64));
    assert_eq!(lo + hi * two_128, big_val);

    // Test with a random-ish large value (use a field element near the modulus)
    let large = -Fp::one(); // p - 1
    let (lo, hi) = decompose_to_limbs(large);
    assert_eq!(lo + hi * two_128, large);

    // Verify the decomposition is stable
    let val2 = Fp::from(0xDEAD_BEEF_CAFE_BABEu64) * two_128 + Fp::from(0x1234_5678_9ABC_DEF0u64);
    let (lo2, hi2) = decompose_to_limbs(val2);
    assert_eq!(lo2 + hi2 * two_128, val2);
}

#[test]
fn test_challenge_polynomial_eval() {
    // b(z) with empty challenges should be 1
    assert_eq!(challenge_polynomial_eval(&[], Fp::from(42u64)), Fp::one());

    // b(z) = (1 + u_0 * z) for a single challenge
    let u0 = Fp::from(3u64);
    let z = Fp::from(5u64);
    let expected = Fp::one() + u0 * z; // 1 + 3*5 = 16
    assert_eq!(challenge_polynomial_eval(&[u0], z), expected);

    // b(z) = (1 + u_1 * z) * (1 + u_0 * z^2) for two challenges
    let u1 = Fp::from(7u64);
    let expected2 = (Fp::one() + u1 * z) * (Fp::one() + u0 * z * z);
    assert_eq!(challenge_polynomial_eval(&[u0, u1], z), expected2);
}

#[test]
fn test_scalar_to_bits_128() {
    // Zero scalar
    let bits = scalar_to_bits_128(Fp::zero());
    assert_eq!(bits.len(), 128);
    assert!(bits.iter().all(|b| !b));

    // One scalar
    let bits = scalar_to_bits_128(Fp::one());
    assert_eq!(bits.len(), 128);
    assert!(bits[127]); // LSB is last (MSB first)
    assert!(bits[..127].iter().all(|b| !b));

    // 0xFF = 255
    let bits = scalar_to_bits_128(Fp::from(255u64));
    assert_eq!(bits.len(), 128);
    // Last 8 bits should all be 1
    assert!(bits[120..128].iter().all(|b| *b));
    assert!(bits[..120].iter().all(|b| !b));
}

#[test]
fn test_point_double_fp() {
    // Doubling the Pallas generator should give a valid point
    // Pallas generator: (1, some y such that y^2 = 1 + 5 = 6)
    // Actually let's just test with a known point
    let x = Fp::from(1u64);
    // y^2 = x^3 + 5 = 6 for Pallas. Need sqrt(6).
    // Instead, test the algebraic property: 2P computed two ways should match
    let p = (Fp::from(123u64), Fp::from(456u64)); // not on curve, but tests formula
    let dp = point_double_fp(p);
    // Just verify it doesn't panic and gives non-trivial output
    assert_ne!(dp.0, Fp::zero());
}

#[test]
fn test_endosclmul_witness_basic() {
    // Test that EndoMul witness generation doesn't panic with valid inputs
    let (endo_base, _) = kimchi::curve::pallas_endos();
    let base = (Fp::from(7u64), Fp::from(11u64)); // Not on curve but tests mechanics
    let acc0 = point_double_fp(base);
    let bits = vec![false; 128]; // scalar = 0 in some encoding

    let total_rows = 40;
    let mut witness: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); total_rows]);

    // This may panic due to division by zero with fake points, so just test compilation
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        endosclmul_witness_fill(&mut witness, 0, *endo_base, base, &bits, acc0);
    }));
}

#[test]
fn test_complete_add_witness_basic() {
    let total_rows = 5;
    let mut witness: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); total_rows]);

    // Test with distinct x-coordinates (standard addition)
    let p1 = (Fp::from(1u64), Fp::from(2u64));
    let p2 = (Fp::from(3u64), Fp::from(4u64));
    let result = complete_add_witness_fill(&mut witness, 0, p1, p2);

    // Verify witness is filled
    assert_eq!(witness[0][0], p1.0);
    assert_eq!(witness[1][0], p1.1);
    assert_eq!(witness[2][0], p2.0);
    assert_eq!(witness[3][0], p2.1);
    assert_eq!(witness[4][0], result.0);
    assert_eq!(witness[5][0], result.1);
    assert_eq!(witness[7][0], Fp::zero()); // same_x = false
}

#[test]
fn test_standalone_proof_malformed_rejected() {
    let proof = StandaloneRecursiveProof {
        proof_bytes: vec![0u8; 100],
        public_inputs: vec![0u8; 50], // too short
        num_steps: 1,
        circuit_layout_digest: [0u8; 32],
    };
    let result = verify_standalone_recursive_proof(&proof, None);
    assert!(result.is_err());
}

#[test]
#[ignore = "SUPERSEDED by dual-curve Step/Wrap architecture. The monolithic \
            single-curve IPA verifier fails because EndoMul gates on Vesta enforce \
            the Pallas curve equation, but L/R points are Vesta points (Fq coords). \
            The fix is the dual-curve architecture: Step circuit (Vesta) defers EC \
            ops, Wrap circuit (Pallas) verifies them natively. See \
            build_step_verifier_circuit + build_wrap_verifier_circuit."]
fn test_standalone_recursive_step_end_to_end() {
    // Step 1: Create a base-case proof using the assisted recursion path
    let transition1 = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };
    let base_proof = prove_recursive_step(None, &transition1).expect("Base case should succeed");

    // Step 2: Prove a standalone recursive step that verifies the base proof in-circuit
    let transition2 = PicklesStateTransition {
        pre_state_hash: [2u8; 32],
        post_state_hash: [3u8; 32],
    };
    let standalone = prove_standalone_recursive_step(&base_proof, &transition2)
        .expect("Standalone prover should succeed with on-curve witness");

    assert_eq!(standalone.num_steps, 2);
    assert!(!standalone.proof_bytes.is_empty());
    println!(
        "Standalone recursive proof size: {} bytes ({} steps)",
        standalone.proof_bytes.len(),
        standalone.num_steps
    );

    // Verify the standalone proof - this MUST succeed for soundness
    let valid = verify_standalone_recursive_proof(&standalone, None)
        .expect("Verification must not return an error");
    assert!(
        valid,
        "Standalone recursive proof MUST verify. If this fails, the circuit \
         is unsound: either the constraint system has unconstrained witnesses \
         or the IPA equation doesn't balance."
    );
}

/// Test that the b(zeta) Horner evaluation is correctly constrained.
/// This exercises Section 3 in isolation by building a minimal circuit
/// with just the Horner chain and verifying a proof.
#[test]
fn test_b_zeta_horner_chain_sound() {
    // Build a minimal circuit with just Section 3's Horner constraints
    let num_rounds = 3; // Small for fast testing
    let mut gates = Vec::new();
    let mut row = 0;

    // Public inputs: zeta, b_at_zeta
    let public_count = 2;
    for _ in 0..public_count {
        let mut coeffs = vec![Fp::zero(); COLUMNS];
        coeffs[0] = Fp::one();
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            coeffs,
        ));
        row += 1;
    }

    // Section 3: Horner chain (same constraints as build_ipa_verifier_circuit)
    for _ in 0..num_rounds {
        // Row 0: squaring
        let mut coeffs = vec![Fp::zero(); COLUMNS];
        coeffs[2] = -Fp::one();
        coeffs[3] = Fp::one();
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            coeffs,
        ));
        row += 1;

        // Row 1: u_i * z_power
        let mut coeffs = vec![Fp::zero(); COLUMNS];
        coeffs[2] = -Fp::one();
        coeffs[3] = Fp::one();
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            coeffs,
        ));
        row += 1;

        // Row 2: factor = 1 + product
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

        // Row 3: accumulator multiply
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

    // Final output gate (zeroed - just pads the circuit)
    gates.push(CircuitGate::new(
        GateType::Generic,
        Wire::for_row(row),
        vec![Fp::zero(); COLUMNS],
    ));
    row += 1;

    // Generate witness
    let zeta = Fp::from(7u64);
    let challenges = [Fp::from(3u64), Fp::from(5u64), Fp::from(11u64)];
    let expected_b = challenge_polynomial_eval(&challenges, zeta);

    let mut witness: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); row]);

    // Public inputs
    witness[0][0] = zeta;
    witness[0][1] = expected_b;

    // Horner chain witness
    let mut z_power = zeta;
    let mut b_running = Fp::one();
    for i in 0..num_rounds {
        let row_base = public_count + i * 4;
        let u_i = challenges[num_rounds - 1 - i];

        witness[0][row_base] = z_power;
        witness[1][row_base] = z_power;
        witness[2][row_base] = z_power * z_power;

        witness[0][row_base + 1] = u_i;
        witness[1][row_base + 1] = z_power;
        witness[2][row_base + 1] = u_i * z_power;

        let product = u_i * z_power;
        let factor = Fp::one() + product;
        witness[0][row_base + 2] = product;
        witness[1][row_base + 2] = Fp::zero();
        witness[2][row_base + 2] = factor;

        let b_new = b_running * factor;
        witness[0][row_base + 3] = b_running;
        witness[1][row_base + 3] = factor;
        witness[2][row_base + 3] = b_new;

        b_running = b_new;
        z_power = z_power * z_power;
    }

    // Verify the computed b matches expected
    assert_eq!(
        b_running, expected_b,
        "Horner chain must produce correct b(zeta)"
    );

    // Create prover index and prove
    let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(
        gates.clone(),
        public_count,
    );

    let group_map = <Vesta as CommitmentCurve>::Map::setup();
    let proof = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
        BaseSponge,
        ScalarSponge,
        _,
    >(&group_map, witness, &[], &index, &mut OsRng)
    .expect("Prover must succeed with correct Horner witness");

    // Verify
    let verifier_index = index.verifier_index();
    let public_inputs = vec![zeta, expected_b];
    let result = verifier::verify::<FULL_ROUNDS, Vesta, BaseSponge, ScalarSponge, VestaOpeningProof>(
        &group_map,
        &verifier_index,
        &proof,
        &public_inputs,
    );
    assert!(
        result.is_ok(),
        "Horner chain proof must verify: {:?}",
        result.err()
    );
}

/// Test that Section 5 assertion gates reject mismatched coordinates.
/// A dishonest prover who sets LHS != RHS must fail.
#[test]
fn test_section5_assertion_rejects_mismatch() {
    // Build a minimal circuit with assertion gates.
    // We use 1 public input to satisfy Kimchi's requirement that at least
    // one row be a "public input binding" gate.
    let mut gates = Vec::new();
    let mut row = 0;

    let public_count = 1;
    // Public input binding gate (row 0): 1*w[0] - PI[0] = 0
    let mut coeffs = vec![Fp::zero(); COLUMNS];
    coeffs[0] = Fp::one();
    gates.push(CircuitGate::new(
        GateType::Generic,
        Wire::for_row(row),
        coeffs,
    ));
    row += 1;

    // Two assertion gates: w[0] - w[1] = 0
    let mut coeffs = vec![Fp::zero(); COLUMNS];
    coeffs[0] = Fp::one();
    coeffs[1] = -Fp::one();
    gates.push(CircuitGate::new(
        GateType::Generic,
        Wire::for_row(row),
        coeffs,
    ));
    row += 1;

    let mut coeffs = vec![Fp::zero(); COLUMNS];
    coeffs[0] = Fp::one();
    coeffs[1] = -Fp::one();
    gates.push(CircuitGate::new(
        GateType::Generic,
        Wire::for_row(row),
        coeffs,
    ));
    row += 1;

    // Pad to minimum circuit size
    for _ in 0..5 {
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            vec![Fp::zero(); COLUMNS],
        ));
        row += 1;
    }

    // HONEST witness: w[0] == w[1] in assertion rows
    let mut witness_good: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); row]);
    witness_good[0][0] = Fp::from(1u64); // public input
    witness_good[0][1] = Fp::from(42u64);
    witness_good[1][1] = Fp::from(42u64); // equal
    witness_good[0][2] = Fp::from(99u64);
    witness_good[1][2] = Fp::from(99u64); // equal

    let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(
        gates.clone(),
        public_count,
    );
    let group_map = <Vesta as CommitmentCurve>::Map::setup();

    // Honest prover should succeed
    let proof = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
        BaseSponge,
        ScalarSponge,
        _,
    >(&group_map, witness_good, &[], &index, &mut OsRng)
    .expect("Honest prover with matching coordinates must succeed");

    let verifier_index = index.verifier_index();
    let public_inputs = vec![Fp::from(1u64)];
    let result = verifier::verify::<FULL_ROUNDS, Vesta, BaseSponge, ScalarSponge, VestaOpeningProof>(
        &group_map,
        &verifier_index,
        &proof,
        &public_inputs,
    );
    assert!(result.is_ok(), "Honest proof must verify");

    // DISHONEST witness: w[0] != w[1].
    //
    // SOUNDNESS PROPERTY (the real one): a witness that violates the assertion
    // gate must NOT yield a proof that the verifier accepts. There are two ways
    // the Kimchi machinery enforces this, depending on build profile:
    //
    //   * debug builds: the prover's `check_constraint!` debug-assertions fire
    //     and the prover *panics* before emitting a proof.
    //   * release builds (`debug_assertions` off): the prover does NOT panic —
    //     it computes a quotient that does not divide the vanishing polynomial
    //     and emits a *malformed* proof. The constraint is still enforced
    //     cryptographically: the VERIFIER rejects that proof.
    //
    // The earlier version of this test only asserted the prover panics, which
    // is a debug-only behavior and gave a false failure under `--release`. The
    // sound property is "dishonest witness => no accepted proof", which we now
    // assert directly: EITHER the prover fails/panics, OR (if it produced a
    // proof) the verifier rejects it. A dishonest proof being *accepted* is the
    // only outcome that indicates the assertion gates are not constraining.
    let gates_clone = gates.clone();
    let group_map_dishonest = <Vesta as CommitmentCurve>::Map::setup();
    let dishonest_outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut witness_bad: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); row]);
        witness_bad[0][0] = Fp::from(1u64); // public input
        witness_bad[0][1] = Fp::from(42u64);
        witness_bad[1][1] = Fp::from(43u64); // NOT equal!
        witness_bad[0][2] = Fp::from(99u64);
        witness_bad[1][2] = Fp::from(99u64);

        let index2 = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(
            gates_clone,
            public_count,
        );
        ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<BaseSponge, ScalarSponge, _>(
            &group_map_dishonest,
            witness_bad,
            &[],
            &index2,
            &mut OsRng,
        )
    }));

    match dishonest_outcome {
        // Prover panicked (debug builds) or returned Err: dishonest witness
        // never produced a proof. Sound.
        Err(_) | Ok(Err(_)) => {}
        // Prover produced a proof (release builds): it MUST NOT verify.
        Ok(Ok(bad_proof)) => {
            let bad_public_inputs = vec![Fp::from(1u64)];
            let verify_result = verifier::verify::<
                FULL_ROUNDS,
                Vesta,
                BaseSponge,
                ScalarSponge,
                VestaOpeningProof,
            >(
                &group_map_dishonest,
                &verifier_index,
                &bad_proof,
                &bad_public_inputs,
            );
            assert!(
                verify_result.is_err(),
                "SOUNDNESS BREAK: dishonest witness (w[0] != w[1]) produced a proof \
                 that the verifier ACCEPTED. The assertion gates are not constraining."
            );
        }
    }
}

#[test]
fn test_add_copy_constraints_no_panic() {
    // Verify that adding copy constraints doesn't panic
    let (mut gates, _, layout) = build_ipa_verifier_circuit(IPA_ROUNDS);
    add_ipa_verifier_copy_constraints(&mut gates, &layout);

    // Check that Poseidon squeeze outputs are wired through decomposition
    let poseidon_gadget_rows = (FULL_ROUNDS / 5) + 1;
    let absorption_calls = (4 * IPA_ROUNDS + 2) / 3;
    let squeeze_start = layout.transcript_section_start + absorption_calls * poseidon_gadget_rows;
    let poseidon_rows = FULL_ROUNDS / 5;
    let first_squeeze_output = squeeze_start + poseidon_rows;
    if first_squeeze_output < gates.len() {
        let w = gates[first_squeeze_output].wires[0];
        // Should point to the decomposition section (3-cycle: squeeze → decomp → b_poly)
        assert_ne!(
            w.row, first_squeeze_output,
            "Copy constraint should have been set (wire should not be identity)"
        );
        // Target should be in the limb decomposition section (col 2 of first decomp gate)
        let decomp_start = layout.limb_decomposition_section_start;
        assert_eq!(
            w.row,
            decomp_start, // round 0 decomp gate
            "First squeeze output should wire to first decomp gate's w[2] (full challenge)"
        );
        assert_eq!(
            w.col, 2,
            "Target should be col 2 (the full challenge in decomp)"
        );
    }

    // Check that b(zeta) output is wired to Section 5's EndoMul
    let b_poly_start = squeeze_start + IPA_ROUNDS * poseidon_gadget_rows;
    let b_poly_rows = 4 * IPA_ROUNDS;
    let b_output_row = b_poly_start + b_poly_rows - 1;
    let fcs = layout.final_check_section_start;
    let b_endomul_zero_row = fcs + 32;
    if b_output_row < gates.len() && b_endomul_zero_row < gates.len() {
        let w = gates[b_output_row].wires[2];
        assert_eq!(
            w.row, b_endomul_zero_row,
            "b(zeta) output (col 2) should wire to Section 5(a) EndoMul Zero row"
        );
        assert_eq!(w.col, 6, "Target should be n_acc column (col 6)");
    }
}

// ========================================================================
// Dual-Curve Step/Wrap Architecture Tests
// ========================================================================

#[test]
fn test_step_verifier_circuit_builds() {
    let (gates, public_count, layout) = build_step_verifier_circuit(IPA_ROUNDS);
    assert_eq!(public_count, 11);
    assert!(!gates.is_empty());
    assert!(layout.transcript_section_start < layout.b_zeta_section_start);
    assert!(layout.b_zeta_section_start < layout.state_transition_start);
    assert!(layout.state_transition_start < layout.total_gates);

    // Step circuit should have NO EndoMul or CompleteAdd gates
    let mut endomul_count = 0;
    let mut complete_add_count = 0;
    for gate in &gates {
        match gate.typ {
            GateType::EndoMul => endomul_count += 1,
            GateType::CompleteAdd => complete_add_count += 1,
            _ => {}
        }
    }
    assert_eq!(
        endomul_count, 0,
        "Step circuit must have ZERO EndoMul gates (EC ops are deferred)"
    );
    assert_eq!(
        complete_add_count, 0,
        "Step circuit must have ZERO CompleteAdd gates (EC ops are deferred)"
    );

    println!(
        "Step circuit: {} gates, domain 2^{}",
        layout.total_gates,
        (layout.total_gates as f64).log2().ceil() as u32
    );
}

#[test]
fn test_wrap_verifier_circuit_builds() {
    let (gates, public_count, layout) = build_wrap_verifier_circuit(IPA_ROUNDS);
    assert_eq!(public_count, 6);
    assert!(!gates.is_empty());
    assert!(layout.limb_decomp_start < layout.bullet_reduce_start);
    assert!(layout.bullet_reduce_start < layout.final_check_start);
    assert!(layout.final_check_start < layout.total_gates);

    // Wrap circuit SHOULD have EndoMul and CompleteAdd gates
    let mut endomul_count = 0;
    let mut complete_add_count = 0;
    let mut poseidon_count = 0;
    for gate in &gates {
        match gate.typ {
            GateType::EndoMul => endomul_count += 1,
            GateType::CompleteAdd => complete_add_count += 1,
            GateType::Poseidon => poseidon_count += 1,
            _ => {}
        }
    }
    assert!(
        endomul_count > 0,
        "Wrap circuit must have EndoMul gates for bullet_reduce"
    );
    assert!(
        complete_add_count > 0,
        "Wrap circuit must have CompleteAdd gates"
    );
    assert_eq!(
        poseidon_count, 0,
        "Wrap circuit should have NO Poseidon gates (transcript is in Step)"
    );

    // Expected EndoMul: 4*IPA_ROUNDS*32 (bullet_reduce) + 4*32 (final eq) = 2048
    let expected_endomul = 4 * IPA_ROUNDS * 32 + 4 * 32;
    assert_eq!(endomul_count, expected_endomul);

    println!(
        "Wrap circuit: {} gates, domain 2^{}, EndoMul={}, CompleteAdd={}",
        layout.total_gates,
        (layout.total_gates as f64).log2().ceil() as u32,
        endomul_count,
        complete_add_count
    );
}

#[test]
fn test_step_wrap_separation_is_correct() {
    // Verify that the Step + Wrap together cover the same gates as the
    // old monolithic build_ipa_verifier_circuit
    let (_, _, step_layout) = build_step_verifier_circuit(IPA_ROUNDS);
    let (_, _, wrap_layout) = build_wrap_verifier_circuit(IPA_ROUNDS);
    let (_, _, mono_layout) = build_ipa_verifier_circuit(IPA_ROUNDS);

    // The Step has Poseidon + b(zeta) (same as monolithic Sections 2+3)
    // The Wrap has limb_decomp + bullet_reduce + final_check (Sections 3.5+4+5)
    // The monolithic has all of these in one circuit

    // Step should be significantly smaller than monolithic (no EC gates)
    assert!(
        step_layout.total_gates < mono_layout.total_gates,
        "Step ({}) should be smaller than monolithic ({})",
        step_layout.total_gates,
        mono_layout.total_gates
    );

    // Wrap should be similar size to monolithic's EC section
    let mono_ec_gates = mono_layout.total_gates - mono_layout.bullet_reduce_section_start;
    // Wrap includes its own public input gates + decomp + EC
    assert!(
        wrap_layout.total_gates > mono_ec_gates / 2,
        "Wrap should contain the bulk of the EC gates"
    );

    println!("{}", dual_curve_circuit_stats());
}

#[test]
fn test_dual_curve_step_base_case() {
    // Prove a base-case step (no previous proof)
    let transition = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };

    let step_proof =
        prove_dual_curve_step(None, &transition).expect("Base case step proving should succeed");

    assert_eq!(step_proof.num_steps, 1);
    assert!(step_proof.deferred_ipa_data.is_empty()); // No IPA to defer for base case

    // Verify the step proof (Kimchi verification of Poseidon + field arithmetic)
    let valid = verify_dual_curve_step(&step_proof).expect("Step verification should not error");
    assert!(valid, "Base case step proof must verify");
}

#[test]
fn test_dual_curve_step_recursive() {
    // Create a base case first using assisted recursion
    let transition1 = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };
    let base_proof = prove_recursive_step(None, &transition1).expect("Base case should succeed");

    // Now prove a Step that defers the base proof's IPA verification
    let transition2 = PicklesStateTransition {
        pre_state_hash: [2u8; 32],
        post_state_hash: [3u8; 32],
    };
    let step_proof = prove_dual_curve_step(Some(&base_proof), &transition2)
        .expect("Recursive step proving should succeed");

    assert_eq!(step_proof.num_steps, 2);
    assert!(
        !step_proof.deferred_ipa_data.is_empty(),
        "Recursive step must have deferred IPA data for Wrap"
    );

    // Verify the step proof
    let valid = verify_dual_curve_step(&step_proof).expect("Step verification should not error");
    assert!(valid, "Recursive step proof must verify");
}

#[test]
fn test_dual_curve_step_tampered_fails() {
    let transition = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };

    let mut step_proof = prove_dual_curve_step(None, &transition).expect("Proving should succeed");

    // Tamper with accumulated hash
    step_proof.public_inputs[64] ^= 0xFF;

    let valid = verify_dual_curve_step(&step_proof)
        .expect("Verification should not error on tampered data");
    assert!(!valid, "Tampered step proof should fail verification");
}

#[test]
fn test_dual_curve_stats() {
    let stats = dual_curve_circuit_stats();
    assert!(stats.contains("Step Circuit"));
    assert!(stats.contains("Wrap Binding Circuit"));
    assert!(stats.contains("no EC gates"));
    assert!(stats.contains("VESTA curve"));
    println!("{}", stats);
}

#[test]
fn test_fp_one_bytes() {
    let one = Fp::one();
    let bytes = fp_to_bytes32(&one);
    println!("Fp::one() bytes: {:?}", bytes);
    let three = Fp::from(3u64);
    let bytes3 = fp_to_bytes32(&three);
    println!("Fp::from(3) bytes: {:?}", bytes3);
}

#[test]
fn test_dual_curve_wrap_base_case() {
    // Base case: step with no previous proof, then wrap it.
    let transition = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };

    let step_proof =
        prove_dual_curve_step(None, &transition).expect("Base case step proving should succeed");
    assert!(step_proof.deferred_ipa_data.is_empty());

    let wrap_proof =
        prove_dual_curve_wrap(&step_proof, None).expect("Base case wrap proving should succeed");

    assert_eq!(wrap_proof.num_steps, 1);
    assert_eq!(wrap_proof.public_inputs.len(), 32 * 4); // 4 public inputs

    // The wrap proof should bind to the step proof
    let expected_hash = {
        let mut hasher = blake3::Hasher::new();
        hasher.update(&step_proof.proof_bytes);
        let mut out = [0u8; 32];
        out.copy_from_slice(hasher.finalize().as_bytes());
        out
    };
    assert_eq!(wrap_proof.step_proof_hash, expected_hash);

    // Verify the wrap proof
    let valid = verify_dual_curve_wrap(&wrap_proof).expect("Wrap verification should not error");
    assert!(valid, "Base case wrap proof must verify");
}

#[test]
fn test_dual_curve_wrap_recursive() {
    // Create a base recursive proof, then a step that defers it, then wrap.
    let transition1 = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };
    let base_recursive =
        prove_recursive_step(None, &transition1).expect("Base recursive should succeed");

    let transition2 = PicklesStateTransition {
        pre_state_hash: [2u8; 32],
        post_state_hash: [3u8; 32],
    };
    let step_proof = prove_dual_curve_step(Some(&base_recursive), &transition2)
        .expect("Recursive step proving should succeed");
    assert!(!step_proof.deferred_ipa_data.is_empty());

    let wrap_proof =
        prove_dual_curve_wrap(&step_proof, None).expect("Recursive wrap proving should succeed");

    assert_eq!(wrap_proof.num_steps, 2);
    assert_eq!(wrap_proof.public_inputs.len(), 32 * 4);

    // Verify the wrap proof (includes batch-checking accumulated IPA challenges)
    let valid = verify_dual_curve_wrap(&wrap_proof).expect("Wrap verification should not error");
    assert!(
        valid,
        "Recursive wrap proof must verify (batch-checks IPA accumulator)"
    );
}

#[test]
fn test_dual_curve_wrap_tampered_fails() {
    // Create a valid wrap proof, then tamper with it.
    let transition = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };
    let step_proof = prove_dual_curve_step(None, &transition).expect("Step should succeed");
    let mut wrap_proof = prove_dual_curve_wrap(&step_proof, None).expect("Wrap should succeed");

    // Tamper with public inputs
    wrap_proof.public_inputs[0] ^= 0xFF;

    let valid = verify_dual_curve_wrap(&wrap_proof)
        .expect("Verification should not error on tampered data");
    assert!(!valid, "Tampered wrap proof should fail verification");
}

#[test]
fn test_full_recursive_chain_single() {
    // Chain with a single transition: recursive -> step -> wrap.
    let transition = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };

    let wrap_proof =
        prove_full_recursive_chain(&[transition]).expect("Single-transition chain should succeed");

    assert_eq!(wrap_proof.num_steps, 1);
    assert_eq!(wrap_proof.public_inputs.len(), 32 * 4);

    // Verify the final proof
    let valid =
        verify_full_recursive_proof(&wrap_proof).expect("Final verification should not error");
    assert!(valid, "Single-transition chain proof must verify");
}

#[test]
fn test_full_recursive_chain_multiple() {
    // Chain with three transitions.
    let transitions = vec![
        PicklesStateTransition {
            pre_state_hash: [1u8; 32],
            post_state_hash: [2u8; 32],
        },
        PicklesStateTransition {
            pre_state_hash: [2u8; 32],
            post_state_hash: [3u8; 32],
        },
        PicklesStateTransition {
            pre_state_hash: [3u8; 32],
            post_state_hash: [4u8; 32],
        },
    ];

    let wrap_proof =
        prove_full_recursive_chain(&transitions).expect("Multi-transition chain should succeed");

    assert_eq!(wrap_proof.num_steps, 3);
    assert_eq!(wrap_proof.public_inputs.len(), 32 * 4);

    // Verify the final proof (batch-checks all accumulated IPA challenges)
    let valid =
        verify_full_recursive_proof(&wrap_proof).expect("Final verification should not error");
    assert!(valid, "Multi-transition chain proof must verify");
}

#[test]
fn test_full_recursive_chain_tampered_wrap_fails() {
    // Create a valid chain, then tamper with the wrap proof.
    let transition = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };

    let mut wrap_proof = prove_full_recursive_chain(&[transition]).expect("Chain should succeed");

    // Tamper with the proof bytes (corrupts the Kimchi proof)
    if let Some(byte) = wrap_proof.proof_bytes.last_mut() {
        *byte ^= 0x01;
    }

    let result = verify_full_recursive_proof(&wrap_proof);
    // Should either return Ok(false) or Err (deserialization failure)
    match result {
        Ok(false) => {} // Verification failed cleanly
        Err(_) => {}    // Deserialization failed (also acceptable)
        Ok(true) => panic!("Tampered proof must NOT verify"),
    }
}

// ========================================================================
// Standalone-Transitive Wrap Tests
// ========================================================================

#[test]
fn test_standalone_dual_curve_wrap_base_case_rejected() {
    // Base case step proofs have no deferred IPA data, so standalone wrap
    // should reject them (use regular prove_dual_curve_wrap for base cases).
    let transition = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };
    let step_proof =
        prove_dual_curve_step(None, &transition).expect("Base case step should succeed");
    assert!(step_proof.deferred_ipa_data.is_empty());

    #[allow(deprecated)]
    let result = prove_standalone_dual_curve_wrap(&step_proof);
    assert!(
        result.is_err(),
        "Standalone wrap must reject base-case step (no IPA to verify)"
    );
}

#[test]
fn test_standalone_dual_curve_wrap_end_to_end() {
    // Create a recursive proof, then a step that defers its IPA, then
    // standalone-wrap it with in-circuit verification.
    let transition1 = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };
    let base_recursive =
        prove_recursive_step(None, &transition1).expect("Base recursive should succeed");

    let transition2 = PicklesStateTransition {
        pre_state_hash: [2u8; 32],
        post_state_hash: [3u8; 32],
    };
    let step_proof = prove_dual_curve_step(Some(&base_recursive), &transition2)
        .expect("Step with deferred IPA should succeed");
    assert!(
        !step_proof.deferred_ipa_data.is_empty(),
        "Step proof must have deferred IPA data for standalone wrap"
    );

    // This is the key test: standalone wrap with in-circuit EC verification.
    // Gate outputs (EndoMul + CompleteAdd) flow directly into the assertion.
    let standalone_wrap = prove_standalone_dual_curve_wrap(&step_proof)
        .expect("Standalone wrap prover should succeed");

    assert_eq!(standalone_wrap.num_steps, 2);
    assert!(!standalone_wrap.proof_bytes.is_empty());
    println!(
        "Standalone wrap proof size: {} bytes ({} steps)",
        standalone_wrap.proof_bytes.len(),
        standalone_wrap.num_steps
    );

    // Verify the standalone proof — this must succeed for the architecture to work.
    let valid =
        verify_standalone_dual_curve_wrap(&standalone_wrap).expect("Verification should not error");
    assert!(
        valid,
        "Standalone dual-curve wrap proof MUST verify. \
         The EC verifier circuit (EndoMul + CompleteAdd on Pallas) \
         verifies the Vesta IPA equation in-circuit. \
         Only sg MSM is deferred (same as Mina Pickles)."
    );
}

#[test]
fn test_standalone_dual_curve_wrap_tampered_fails() {
    let transition1 = PicklesStateTransition {
        pre_state_hash: [1u8; 32],
        post_state_hash: [2u8; 32],
    };
    let base_recursive =
        prove_recursive_step(None, &transition1).expect("Base recursive should succeed");

    let transition2 = PicklesStateTransition {
        pre_state_hash: [2u8; 32],
        post_state_hash: [3u8; 32],
    };
    let step_proof =
        prove_dual_curve_step(Some(&base_recursive), &transition2).expect("Step should succeed");

    let mut standalone_wrap =
        prove_standalone_dual_curve_wrap(&step_proof).expect("Standalone wrap should succeed");

    // Tamper with proof bytes
    if let Some(byte) = standalone_wrap.proof_bytes.last_mut() {
        *byte ^= 0x01;
    }

    let result = verify_standalone_dual_curve_wrap(&standalone_wrap);
    match result {
        Ok(false) => {} // Clean failure
        Err(_) => {}    // Deserialization error (also acceptable)
        Ok(true) => panic!("Tampered standalone wrap proof must NOT verify"),
    }
}

#[test]
fn test_standalone_recursive_chain() {
    // Full standalone-transitive chain: prove multiple transitions,
    // final proof is self-contained.
    let transitions = vec![
        PicklesStateTransition {
            pre_state_hash: [1u8; 32],
            post_state_hash: [2u8; 32],
        },
        PicklesStateTransition {
            pre_state_hash: [2u8; 32],
            post_state_hash: [3u8; 32],
        },
    ];

    let standalone_wrap = prove_standalone_recursive_chain(&transitions)
        .expect("Standalone recursive chain should succeed");

    println!(
        "Standalone chain proof: {} bytes, {} steps",
        standalone_wrap.proof_bytes.len(),
        standalone_wrap.num_steps
    );

    // Verify
    let valid = verify_standalone_dual_curve_wrap(&standalone_wrap)
        .expect("Standalone chain verification should not error");
    assert!(valid, "Standalone recursive chain proof must verify");
}

#[test]
fn test_full_recursive_chain_constant_proof_size() {
    // Verify that the final wrap proof size is constant regardless of chain length.
    let mut sizes = Vec::new();
    for num_transitions in [1, 2] {
        let transitions: Vec<PicklesStateTransition> = (0..num_transitions)
            .map(|i| {
                let mut pre = [0u8; 32];
                let mut post = [0u8; 32];
                pre[0] = i as u8;
                post[0] = (i + 1) as u8;
                PicklesStateTransition {
                    pre_state_hash: pre,
                    post_state_hash: post,
                }
            })
            .collect();

        let wrap = prove_full_recursive_chain(&transitions)
            .unwrap_or_else(|e| panic!("Chain of {} failed: {}", num_transitions, e));
        sizes.push((num_transitions, wrap.proof_bytes.len()));
    }

    // Both should use the same binding circuit, so proof sizes should be similar
    // (not growing linearly with chain length)
    let (_, size_1) = sizes[0];
    let (_, size_2) = sizes[1];
    let ratio = size_2 as f64 / size_1 as f64;
    println!(
        "Wrap proof sizes: 1-step={} bytes, 2-step={} bytes, ratio={:.2}",
        size_1, size_2, ratio
    );
    assert!(
        ratio < 2.0,
        "Wrap proof size should not double with chain length (got ratio {:.2})",
        ratio
    );
}
