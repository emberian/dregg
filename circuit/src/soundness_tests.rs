//! Soundness tests: prove that the Poseidon2 AIR constraints reject invalid witnesses.
//!
//! These tests verify the key security property: if a prover inserts wrong values
//! into the trace, the constraints evaluate non-zero and the STARK verifier rejects
//! the proof. If any test PASSES when it should FAIL, that constitutes a soundness bug.

#[cfg(test)]
mod poseidon2_soundness {
    use crate::field::BabyBear;
    use crate::poseidon2::{hash_4_to_1, poseidon2_trace, TOTAL_ROUNDS};
    use crate::poseidon2_air::{
        generate_merkle_poseidon2_trace, create_poseidon2_test_witness,
        MerklePoseidon2StarkAir, Poseidon2Air,
    };
    use crate::stark::{self, StarkAir};

    // ========================================================================
    // Test 1: Poseidon2Air -- wrong output (off by one bit)
    // ========================================================================

    #[test]
    fn poseidon2_air_wrong_output_bit_flip_rejected() {
        // Generate a valid trace
        let input = [
            BabyBear::new(10), BabyBear::new(20), BabyBear::new(30), BabyBear::new(40),
            BabyBear::new(4), BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO,
        ];
        let (trace, public_inputs) = Poseidon2Air::generate_trace(&input);
        let air = Poseidon2Air;

        // Verify that the valid trace produces a valid proof
        let valid_proof = stark::prove(&air, &trace, &public_inputs);
        assert!(
            stark::verify(&air, &valid_proof, &public_inputs).is_ok(),
            "Baseline: valid proof must verify"
        );

        // Tamper: flip a single bit in the output (column 8)
        let mut bad_trace = trace.clone();
        let original_output = bad_trace[0][8].0;
        let flipped = original_output ^ 1; // flip LSB
        bad_trace[0][8] = BabyBear::new(flipped);
        bad_trace[1][8] = BabyBear::new(flipped); // both rows must match (padding)

        // Create public inputs matching tampered trace
        let bad_pi = bad_trace[0].clone();

        // Prove with the tampered trace
        let bad_proof = stark::prove(&air, &bad_trace, &bad_pi);
        let result = stark::verify(&air, &bad_proof, &bad_pi);
        assert!(
            result.is_err(),
            "SOUNDNESS BUG: Proof with wrong output (bit-flipped) MUST be rejected. \
             Original output[0] = {}, tampered = {}",
            original_output, flipped
        );
    }

    // ========================================================================
    // Test 2: Poseidon2Air -- wrong intermediate round state
    // ========================================================================

    #[test]
    fn poseidon2_air_wrong_intermediate_round_constraint_nonzero() {
        // The Poseidon2Air's constraint evaluator recomputes the FULL permutation
        // inside eval_constraints, comparing against claimed_output. There is no
        // per-round intermediate in the Poseidon2Air (it's a single-row constraint).
        //
        // So instead, we corrupt the output to a value that would result from
        // skipping one internal round. This tests that the constraint detects
        // a partial computation.
        let input = [
            BabyBear::new(100), BabyBear::new(200), BabyBear::new(300), BabyBear::new(400),
            BabyBear::new(4), BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO,
        ];

        // Compute a "wrong" output by only running TOTAL_ROUNDS - 1 rounds
        let states = poseidon2_trace(&input);
        let partial_output = &states[TOTAL_ROUNDS - 1]; // one round short
        let correct_output = &states[TOTAL_ROUNDS]; // correct

        assert_ne!(
            partial_output, correct_output,
            "Partial and full outputs must differ"
        );

        // Build trace with partial (wrong) output
        let mut bad_row = Vec::with_capacity(16);
        bad_row.extend_from_slice(&input);
        bad_row.extend_from_slice(partial_output);
        let bad_trace = vec![bad_row.clone(), bad_row.clone()];
        let bad_pi = bad_row.clone();

        let air = Poseidon2Air;

        // Direct constraint check: should be non-zero
        let alpha = BabyBear::new(13);
        let c = air.eval_constraints(&bad_row, &bad_row, &bad_pi, alpha);
        assert_ne!(
            c, BabyBear::ZERO,
            "SOUNDNESS BUG: Constraint must be non-zero when output is from an incomplete permutation"
        );

        // STARK-level: prove + verify should fail
        let bad_proof = stark::prove(&air, &bad_trace, &bad_pi);
        let result = stark::verify(&air, &bad_proof, &bad_pi);
        assert!(
            result.is_err(),
            "SOUNDNESS BUG: Proof with intermediate-round output MUST be rejected"
        );
    }

    // ========================================================================
    // Test 3: MerklePoseidon2StarkAir -- forged parent hash
    // ========================================================================

    #[test]
    fn merkle_poseidon2_forged_parent_rejected() {
        let leaf = BabyBear::new(42424242);
        let witness = create_poseidon2_test_witness(leaf, 4);
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, &siblings, &positions);

        let air = MerklePoseidon2StarkAir;

        // Verify valid trace works
        let valid_proof = stark::prove(&air, &trace, &public_inputs);
        assert!(
            stark::verify(&air, &valid_proof, &public_inputs).is_ok(),
            "Baseline: valid Merkle proof must verify"
        );

        // Forge: replace parent hash at level 0 with a made-up value
        let mut bad_trace = trace.clone();
        bad_trace[0][5] = BabyBear::new(0xDEADBEE); // forged parent

        // Fix the chain so level 1 uses the forged parent as its current
        bad_trace[1][0] = BabyBear::new(0xDEADBEE);
        // Recompute parent at level 1 with the forged current
        let mut children_1 = [BabyBear::ZERO; 4];
        let pos1 = positions[1];
        let mut si = 0;
        for j in 0..4u8 {
            if j == pos1 {
                children_1[j as usize] = BabyBear::new(0xDEADBEE);
            } else {
                children_1[j as usize] = siblings[1][si];
                si += 1;
            }
        }
        bad_trace[1][5] = hash_4_to_1(&children_1);

        // Fix level 2
        bad_trace[2][0] = bad_trace[1][5];
        let mut children_2 = [BabyBear::ZERO; 4];
        let pos2 = positions[2];
        let mut si2 = 0;
        for j in 0..4u8 {
            if j == pos2 {
                children_2[j as usize] = bad_trace[2][0];
            } else {
                children_2[j as usize] = siblings[2][si2];
                si2 += 1;
            }
        }
        bad_trace[2][5] = hash_4_to_1(&children_2);

        // Fix level 3
        bad_trace[3][0] = bad_trace[2][5];
        let mut children_3 = [BabyBear::ZERO; 4];
        let pos3 = positions[3];
        let mut si3 = 0;
        for j in 0..4u8 {
            if j == pos3 {
                children_3[j as usize] = bad_trace[3][0];
            } else {
                children_3[j as usize] = siblings[3][si3];
                si3 += 1;
            }
        }
        bad_trace[3][5] = hash_4_to_1(&children_3);

        // The forged root is different from the real root
        let forged_root = bad_trace[3][5];
        assert_ne!(forged_root, public_inputs[1], "Forged root must differ from real root");

        // Now try to prove with the real public inputs (real leaf, real root)
        // but using the forged trace. The constraint at row 0 should be non-zero
        // because the parent stored in the trace doesn't match hash_4_to_1 of the
        // actual children.
        let alpha = BabyBear::new(7);
        let c = air.eval_constraints(&bad_trace[0], &bad_trace[1], &public_inputs, alpha);
        assert_ne!(
            c, BabyBear::ZERO,
            "SOUNDNESS BUG: Constraint MUST be non-zero when parent is forged"
        );

        // Also verify STARK-level rejection: prove with forged trace but REAL public inputs
        // This should fail because the trace doesn't satisfy constraints
        let bad_proof = stark::prove(&air, &bad_trace, &public_inputs);
        let result = stark::verify(&air, &bad_proof, &public_inputs);
        assert!(
            result.is_err(),
            "SOUNDNESS BUG: Proof with forged parent hash MUST be rejected by STARK verifier"
        );
    }

    // ========================================================================
    // Test 4: MerklePoseidon2StarkAir -- wrong position (forged position in trace)
    // ========================================================================

    #[test]
    fn merkle_poseidon2_wrong_position_rejected() {
        // The MerklePoseidon2StarkAir enforces: parent == hash_4_to_1(children)
        // where children are arranged by position. Changing position without
        // recomputing the hash breaks this constraint.

        let leaf = BabyBear::new(12345678);
        let siblings = [
            [BabyBear::new(100), BabyBear::new(200), BabyBear::new(300)],
            [BabyBear::new(400), BabyBear::new(500), BabyBear::new(600)],
        ];
        let positions_correct = [0u8, 1]; // leaf at position 0, then 1

        let (trace_correct, pi_correct) =
            generate_merkle_poseidon2_trace(leaf, &siblings, &positions_correct);

        let air = MerklePoseidon2StarkAir;

        // Verify the correct trace works
        let valid_proof = stark::prove(&air, &trace_correct, &pi_correct);
        assert!(
            stark::verify(&air, &valid_proof, &pi_correct).is_ok(),
            "Baseline: correct position must verify"
        );

        // Constraint-level test: change position in a row without fixing the parent hash.
        // This is the key soundness property: a prover cannot lie about position.
        let mut forged_row = trace_correct[0].clone();
        // Position was 0, change to 2 -- but leave parent hash unchanged
        forged_row[4] = BabyBear::new(2);

        let alpha = BabyBear::new(11);
        let next_row = &trace_correct[1];
        let c = air.eval_constraints(&forged_row, next_row, &pi_correct, alpha);
        assert_ne!(
            c, BabyBear::ZERO,
            "SOUNDNESS BUG: Changing position without fixing hash must yield non-zero constraint"
        );

        // STARK-level: build a trace with forged position, attempt prove/verify
        let mut bad_trace = trace_correct.clone();
        bad_trace[0][4] = BabyBear::new(2); // forge position in row 0
        // Don't update parent hash -- should break constraint

        let bad_proof = stark::prove(&air, &bad_trace, &pi_correct);
        let result = stark::verify(&air, &bad_proof, &pi_correct);
        assert!(
            result.is_err(),
            "SOUNDNESS BUG: Proof with forged position (hash not updated) MUST be rejected"
        );

        // Also verify: different positions produce different roots (collision resistance)
        let positions_alt = [2u8, 1];
        let (_, pi_alt) =
            generate_merkle_poseidon2_trace(leaf, &siblings, &positions_alt);
        assert_ne!(
            pi_correct[1], pi_alt[1],
            "Different positions must produce different Merkle roots"
        );
    }
}

#[cfg(test)]
mod note_spending_soundness {
    use crate::field::BabyBear;
    use crate::note_spending_air::{
        col, create_test_witness, merkle_col, prove_note_spend, verify_note_spend,
        NoteSpendingAir,
    };
    use crate::poseidon2_air::MerklePoseidon2StarkAir;
    use crate::stark::{self, StarkAir};

    // ========================================================================
    // Test 5: NoteSpendingAir -- wrong spending key
    // ========================================================================

    #[test]
    fn note_spending_wrong_key_rejected() {
        // Create a valid witness
        let witness_correct = create_test_witness(
            BabyBear::new(1000),  // owner
            BabyBear::new(500),   // value
            BabyBear::new(1),     // asset_type
            BabyBear::new(0xDEAD_BEEF), // correct spending key
            4,                    // depth
        );

        let correct_nullifier = witness_correct.nullifier();
        let correct_root = witness_correct.merkle_root();

        // Verify valid proof works
        let valid_proof = prove_note_spend(&witness_correct);
        assert!(
            verify_note_spend(correct_nullifier, correct_root, &valid_proof).is_ok(),
            "Baseline: valid spending proof must verify"
        );

        // Create a witness with a WRONG spending key
        let mut witness_wrong = witness_correct.clone();
        witness_wrong.spending_key = BabyBear::new(0xBAD_CAFE); // wrong key!

        // The wrong key produces a different nullifier
        let wrong_nullifier = witness_wrong.nullifier();
        assert_ne!(
            correct_nullifier, wrong_nullifier,
            "Different keys must produce different nullifiers"
        );

        // A proof generated with the wrong key CANNOT verify against the correct nullifier
        let wrong_proof = prove_note_spend(&witness_wrong);
        let result = verify_note_spend(correct_nullifier, correct_root, &wrong_proof);
        assert!(
            result.is_err(),
            "SOUNDNESS BUG: Proof with wrong spending key MUST fail against correct nullifier"
        );

        // Also verify at the constraint level: if someone puts the wrong key in the trace
        // but tries to keep the correct nullifier, the constraint catches it
        let (mut trace, _) = NoteSpendingAir::generate_trace(&witness_correct);
        let air = NoteSpendingAir::new(4);

        // Tamper: change the spending key in row 0 but keep the nullifier
        trace[0][col::SPENDING_KEY] = BabyBear::new(0xBAD_CAFE);
        // The nullifier in the trace is still the one derived from the correct key

        let alpha = BabyBear::new(7);
        let pi = vec![correct_nullifier, correct_root];
        let c = air.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            c, BabyBear::ZERO,
            "SOUNDNESS BUG: Constraint must detect spending key / nullifier mismatch"
        );
    }

    // ========================================================================
    // Test 6: NoteSpendingAir -- wrong commitment preimage
    // ========================================================================

    #[test]
    fn note_spending_wrong_commitment_preimage_rejected() {
        // Create a valid witness
        let witness_correct = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            BabyBear::new(0xDEAD_BEEF),
            4,
        );

        let correct_nullifier = witness_correct.nullifier();
        let correct_root = witness_correct.merkle_root();

        // Verify the valid proof first
        let valid_proof = prove_note_spend(&witness_correct);
        assert!(
            verify_note_spend(correct_nullifier, correct_root, &valid_proof).is_ok(),
            "Baseline: valid proof must verify"
        );

        // Tamper: use the correct spending key but claim a different value/asset_type.
        // This changes the commitment, which breaks the Merkle path.
        let mut witness_wrong = witness_correct.clone();
        witness_wrong.value = BabyBear::new(999999); // claim more value!
        witness_wrong.asset_type = BabyBear::new(42); // different asset

        // The commitment changes
        assert_ne!(
            witness_correct.commitment(), witness_wrong.commitment(),
            "Different preimage must produce different commitment"
        );

        // The Merkle root changes because the commitment is different
        assert_ne!(
            witness_correct.merkle_root(), witness_wrong.merkle_root(),
            "Different commitment must produce different Merkle root"
        );

        // Proof with wrong preimage cannot verify against correct root
        let wrong_proof = prove_note_spend(&witness_wrong);
        let result = verify_note_spend(correct_nullifier, correct_root, &wrong_proof);
        assert!(
            result.is_err(),
            "SOUNDNESS BUG: Proof with wrong value/asset_type MUST be rejected"
        );

        // Constraint-level: tamper value in the trace but keep the original commitment
        let (mut trace, _) = NoteSpendingAir::generate_trace(&witness_correct);
        let air = NoteSpendingAir::new(4);

        // Change value in row 0 but don't update commitment
        trace[0][col::VALUE] = BabyBear::new(999999);

        let alpha = BabyBear::new(7);
        let pi = vec![correct_nullifier, correct_root];
        let c = air.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            c, BabyBear::ZERO,
            "SOUNDNESS BUG: Constraint must detect value / commitment mismatch"
        );
    }

    // ========================================================================
    // Test 7: NoteSpendingAir -- wrong nullifier
    // ========================================================================

    #[test]
    fn note_spending_wrong_nullifier_in_trace_rejected() {
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            BabyBear::new(0xDEAD_BEEF),
            4,
        );

        let correct_nullifier = witness.nullifier();
        let correct_root = witness.merkle_root();

        // Verify the valid proof first
        let valid_proof = prove_note_spend(&witness);
        assert!(
            verify_note_spend(correct_nullifier, correct_root, &valid_proof).is_ok(),
            "Baseline: valid proof must verify"
        );

        // Tamper the nullifier in the trace: put a wrong nullifier while keeping
        // everything else correct. This simulates a prover trying to claim a
        // different nullifier was derived from their key.
        let (mut trace, _) = NoteSpendingAir::generate_trace(&witness);
        let air = NoteSpendingAir::new(4);

        let tampered_nullifier = BabyBear::new(0xFACEFACE);
        trace[0][col::NULLIFIER] = tampered_nullifier;

        // Constraint-level: the nullifier derivation constraint should catch this
        let alpha = BabyBear::new(7);
        let pi = vec![tampered_nullifier, correct_root]; // PI matches tampered nullifier
        let c = air.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(
            c, BabyBear::ZERO,
            "SOUNDNESS BUG: Constraint must detect nullifier tampering"
        );

        // STARK-level: build trace with tampered nullifier, attempt full prove/verify
        // trace already has row 0 tampered above

        let bad_pi = vec![tampered_nullifier, correct_root];
        let bad_proof = stark::prove(&air, &trace, &bad_pi);
        let result = stark::verify(&air, &bad_proof, &bad_pi);
        assert!(
            result.is_err(),
            "SOUNDNESS BUG: Proof with tampered nullifier MUST be rejected by STARK verifier"
        );
    }

    // ========================================================================
    // Test 8: NoteSpendingAir -- wrong Merkle path (sibling from different position)
    // ========================================================================

    #[test]
    fn note_spending_wrong_merkle_path_rejected() {
        // Create a valid witness
        let witness_correct = create_test_witness(
            BabyBear::new(7777),
            BabyBear::new(1000),
            BabyBear::new(2),
            BabyBear::new(0xCAFE),
            4,
        );

        let correct_nullifier = witness_correct.nullifier();
        let correct_root = witness_correct.merkle_root();

        // Verify the valid proof first
        let valid_proof = prove_note_spend(&witness_correct);
        assert!(
            verify_note_spend(correct_nullifier, correct_root, &valid_proof).is_ok(),
            "Baseline: valid proof must verify"
        );

        // Tamper: replace a sibling at level 1 with one from a different position
        let mut witness_wrong = witness_correct.clone();
        witness_wrong.merkle_siblings[1] = [
            BabyBear::new(0xBAD1),
            BabyBear::new(0xBAD2),
            BabyBear::new(0xBAD3),
        ];

        // The Merkle root changes
        let wrong_root = witness_wrong.merkle_root();
        assert_ne!(
            correct_root, wrong_root,
            "Wrong siblings must produce a different root"
        );

        // Proof with wrong Merkle path cannot verify against correct root
        let wrong_proof = prove_note_spend(&witness_wrong);
        let result = verify_note_spend(correct_nullifier, correct_root, &wrong_proof);
        assert!(
            result.is_err(),
            "SOUNDNESS BUG: Proof with wrong Merkle siblings MUST be rejected"
        );

        // Constraint-level: tamper a sibling in the Merkle rows of a valid trace
        // but don't update the parent hash
        let (mut trace, _) = NoteSpendingAir::generate_trace(&witness_correct);
        let air = NoteSpendingAir::new(4);

        // Row 2 (second Merkle level): change sibling[0]
        trace[2][merkle_col::SIB0] = BabyBear::new(0xBAD1);
        // Don't update the parent -- constraint should fire

        let alpha = BabyBear::new(7);
        let pi = vec![correct_nullifier, correct_root];
        let c = air.eval_constraints(&trace[2], &trace[3], &pi, alpha);
        assert_ne!(
            c, BabyBear::ZERO,
            "SOUNDNESS BUG: Constraint must detect sibling/parent inconsistency"
        );

        // Full STARK rejection with tampered trace
        let bad_proof = stark::prove(&air, &trace, &pi);
        let result = stark::verify(&air, &bad_proof, &pi);
        assert!(
            result.is_err(),
            "SOUNDNESS BUG: Proof with wrong Merkle path MUST be rejected by STARK verifier"
        );
    }

    // ========================================================================
    // Additional: verify the constraint evaluator is non-trivial
    // ========================================================================

    #[test]
    fn note_spending_constraints_are_nontrivial() {
        // Verify that constraints are NOT vacuously zero for ALL inputs.
        // Generate random-ish trace rows and check that constraints are non-zero.
        let air = NoteSpendingAir::new(4);
        let alpha = BabyBear::new(13);

        // A completely random row (not satisfying any constraint)
        let random_row: Vec<BabyBear> = (0..12)
            .map(|i| BabyBear::new((i * 7 + 3) as u32))
            .collect();
        let random_next: Vec<BabyBear> = (0..12)
            .map(|i| BabyBear::new((i * 11 + 5) as u32))
            .collect();
        let random_pi = vec![BabyBear::new(999), BabyBear::new(888)];

        let c = air.eval_constraints(&random_row, &random_next, &random_pi, alpha);
        assert_ne!(
            c, BabyBear::ZERO,
            "SOUNDNESS BUG: Random trace row should NOT satisfy constraints (constraints are vacuous)"
        );
    }

    #[test]
    fn poseidon2_air_constraints_are_nontrivial() {
        // Verify Poseidon2Air constraints reject random data
        let air = crate::poseidon2_air::Poseidon2Air;
        let alpha = BabyBear::new(13);

        let random_row: Vec<BabyBear> = (0..16)
            .map(|i| BabyBear::new((i * 13 + 7) as u32))
            .collect();
        let random_pi = random_row.clone();

        let c = air.eval_constraints(&random_row, &random_row, &random_pi, alpha);
        assert_ne!(
            c, BabyBear::ZERO,
            "SOUNDNESS BUG: Random data should NOT satisfy Poseidon2 constraints (constraints are vacuous)"
        );
    }

    #[test]
    fn merkle_poseidon2_constraints_are_nontrivial() {
        // Verify MerklePoseidon2StarkAir constraints reject random data
        let air = MerklePoseidon2StarkAir;
        let alpha = BabyBear::new(13);

        let random_row: Vec<BabyBear> = (0..6)
            .map(|i| BabyBear::new((i * 17 + 11) as u32))
            .collect();
        let random_next: Vec<BabyBear> = (0..6)
            .map(|i| BabyBear::new((i * 19 + 3) as u32))
            .collect();
        let random_pi = vec![BabyBear::new(111), BabyBear::new(222)];

        let c = air.eval_constraints(&random_row, &random_next, &random_pi, alpha);
        assert_ne!(
            c, BabyBear::ZERO,
            "SOUNDNESS BUG: Random data should NOT satisfy Merkle Poseidon2 constraints"
        );
    }
}
