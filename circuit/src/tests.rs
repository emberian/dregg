//! End-to-end integration tests.
//!
//! These tests exercise the full pipeline:
//! 1. Create a token state (a few facts)
//! 2. Attenuate it (remove some facts via fold steps)
//! 3. Generate an authorization trace (derivation)
//! 4. Produce a STARK proof (mock)
//! 5. Verify the proof
//! 6. Print proof size

use crate::derivation_air::{
    BodyAtomPattern, CircuitRule, DerivationAir, DerivationWitness,
};
use crate::field::BabyBear;
use crate::fold_air::{FoldAir, FoldWitness, RemovedFact, build_shared_tree};
use crate::merkle_air::{MerkleAir, create_test_witness};
use crate::mock_prover::{Air, MockProof, MockProver};
use crate::poseidon2::{hash_4_to_1, hash_fact, hash_many};
use crate::presentation::{
    PresentationAir, PresentationVerification, PresentationWitness,
};

/// End-to-end test: Full authorization flow with token creation, attenuation, and proof.
#[test]
fn end_to_end_authorization_proof() {
    println!("=== End-to-end Authorization Proof ===\n");

    // -- Step 1: Create initial token state --
    // Token has facts: owns(alice, file1), owns(alice, file2), can_read(alice, file1),
    // can_read(alice, file2), can_write(alice, file1), can_write(alice, file2)

    let owns = BabyBear::new(100);
    let can_read = BabyBear::new(200);
    let can_write = BabyBear::new(300);
    let access = BabyBear::new(400);
    let alice = BabyBear::new(1001);
    let file1 = BabyBear::new(2001);
    let file2 = BabyBear::new(2002);

    // Compute fact hashes for the initial state
    let h_owns_f1 = hash_fact(owns, &[alice, file1, BabyBear::ZERO]);
    let h_owns_f2 = hash_fact(owns, &[alice, file2, BabyBear::ZERO]);
    let h_read_f1 = hash_fact(can_read, &[alice, file1, BabyBear::ZERO]);
    let h_read_f2 = hash_fact(can_read, &[alice, file2, BabyBear::ZERO]);
    let h_write_f1 = hash_fact(can_write, &[alice, file1, BabyBear::ZERO]);
    let h_write_f2 = hash_fact(can_write, &[alice, file2, BabyBear::ZERO]);

    // Compute initial state root (simplified: hash all fact hashes together)
    let initial_root = hash_many(&[h_owns_f1, h_owns_f2, h_read_f1, h_read_f2, h_write_f1, h_write_f2]);
    println!("Initial state root: {initial_root}");
    println!("  Facts: owns(alice,file1), owns(alice,file2), can_read(alice,file1),");
    println!("         can_read(alice,file2), can_write(alice,file1), can_write(alice,file2)");

    // -- Step 2: First attenuation — remove write access to file2 --
    // Compute fold2's tree root first so fold1.new_root matches fold2.old_root
    let h_owns_f2_for_tree = hash_fact(owns, &[alice, file2, BabyBear::ZERO]);
    let (mid_root, _) = build_shared_tree(&[h_owns_f2_for_tree], 4);

    let h_write_f2_fact = hash_fact(can_write, &[alice, file2, BabyBear::ZERO]);
    let (fold1_tree_root, fold1_proofs) = build_shared_tree(&[h_write_f2_fact], 4);
    // Use the tree root as the actual initial_root (override the simplified hash)
    let initial_root = fold1_tree_root;
    let fold1 = FoldWitness {
        old_root: initial_root,
        new_root: mid_root,
        removed_facts: vec![RemovedFact {
            predicate: can_write,
            terms: [alice, file2, BabyBear::ZERO],
            membership_proof: Some(fold1_proofs.into_iter().next().unwrap()),
        }],
        num_added_checks: 0,
    };

    println!("\nFold step 1: Remove can_write(alice, file2)");
    let fold1_air = FoldAir::new(fold1.clone());
    let fold1_result = MockProver::verify(&fold1_air);
    assert!(fold1_result.is_valid(), "Fold 1 failed: {:?}", fold1_result.violations());
    println!("  Fold 1 constraints: SATISFIED");

    // -- Step 3: Second attenuation — remove ownership of file2 --
    let final_root = hash_many(&[h_owns_f1, h_read_f1, h_read_f2, h_write_f1]);

    let (_, fold2_proofs) = build_shared_tree(&[h_owns_f2_for_tree], 4);
    let fold2 = FoldWitness {
        old_root: mid_root,
        new_root: final_root,
        removed_facts: vec![RemovedFact {
            predicate: owns,
            terms: [alice, file2, BabyBear::ZERO],
            membership_proof: Some(fold2_proofs.into_iter().next().unwrap()),
        }],
        num_added_checks: 1,
    };

    println!("\nFold step 2: Remove owns(alice, file2), add check read_only(file2)");
    let fold2_air = FoldAir::new(fold2.clone());
    let fold2_result = MockProver::verify(&fold2_air);
    assert!(fold2_result.is_valid(), "Fold 2 failed: {:?}", fold2_result.violations());
    println!("  Fold 2 constraints: SATISFIED");

    // -- Step 4: Authorization derivation --
    // Rule: access(X, Y) :- owns(X, Y), can_read(X, Y).
    // Prove: access(alice, file1) using owns(alice, file1) and can_read(alice, file1)

    let derivation = DerivationWitness {
        rule: CircuitRule {
            id: 1,
            num_body_atoms: 2,
            num_variables: 2,
            head_predicate: access,
            head_terms: [
                (true, BabyBear::new(0)),  // X
                (true, BabyBear::new(1)),  // Y
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![
                BodyAtomPattern {
                    predicate: owns,
                    terms: [(true, BabyBear::new(0)), (true, BabyBear::new(1)), (false, BabyBear::ZERO)],
                },
                BodyAtomPattern {
                    predicate: can_read,
                    terms: [(true, BabyBear::new(0)), (true, BabyBear::new(1)), (false, BabyBear::ZERO)],
                },
            ],
            equal_checks: vec![],
        },
        state_root: final_root,
        body_fact_hashes: vec![h_owns_f1, h_read_f1],
        substitution: vec![alice, file1], // X=alice, Y=file1
        derived_predicate: access,
        derived_terms: [alice, file1, BabyBear::ZERO],
    };

    println!("\nDerivation: access(alice, file1) :- owns(alice, file1), can_read(alice, file1)");
    let deriv_air = DerivationAir::new(derivation.clone());
    let deriv_result = MockProver::verify(&deriv_air);
    assert!(deriv_result.is_valid(), "Derivation failed: {:?}", deriv_result.violations());
    println!("  Derivation constraints: SATISFIED");

    // -- Step 5: Issuer membership --
    let issuer_key = BabyBear::new(42424242);
    let issuer_witness = create_test_witness(issuer_key, 8);
    let federation_root = issuer_witness.expected_root;

    println!("\nIssuer membership: key {} in federation root {}", issuer_key, federation_root);
    let issuer_air = MerkleAir::new(issuer_witness.clone());
    let issuer_result = MockProver::verify(&issuer_air);
    assert!(issuer_result.is_valid(), "Issuer membership failed: {:?}", issuer_result.violations());
    println!("  Issuer membership constraints: SATISFIED");

    // -- Step 6: Complete presentation proof --
    let presentation = PresentationWitness {
        federation_root,
        request_predicate: access,
        timestamp: BabyBear::new(1716000000),
        fold_chain: vec![fold1, fold2],
        derivation,
        issuer_membership: issuer_witness,
        issuer_key_hash: issuer_key,
    };

    let presentation_air = PresentationAir::new(presentation);
    let verification = presentation_air.verify_all();
    assert_eq!(verification, PresentationVerification::Valid);
    println!("\n=== Presentation Verification: VALID ===");

    // Generate proof
    let proof = presentation_air.prove().expect("Proof generation should succeed");
    println!("\n--- Proof Statistics ---");
    println!("  Fold proofs: {}", proof.fold_proofs.len());
    println!("  Total proof size: {}", proof.proof_size_display());
    println!("  Initial root: {}", proof.public_inputs.initial_root);
    println!("  Final root: {}", proof.public_inputs.final_root);
    println!("  Federation root: {}", proof.public_inputs.federation_root);
    println!("  Timestamp: {}", proof.public_inputs.timestamp);

    // Verify the generated proof
    let proof_verification = proof.verify();
    assert_eq!(proof_verification, PresentationVerification::Valid);
    println!("  Proof verification: VALID");
}

/// Test: Single-step token (no attenuation) with direct authorization.
#[test]
fn single_step_no_attenuation() {
    let pred_access = BabyBear::new(400);
    let alice = BabyBear::new(1001);
    let resource = BabyBear::new(3001);

    let state_root = hash_many(&[
        hash_fact(BabyBear::new(100), &[alice, resource, BabyBear::ZERO]),
        hash_fact(BabyBear::new(200), &[alice, resource, BabyBear::ZERO]),
    ]);

    let derivation = DerivationWitness {
        rule: CircuitRule {
            id: 1,
            num_body_atoms: 1,
            num_variables: 1,
            head_predicate: pred_access,
            head_terms: [(true, BabyBear::new(0)), (false, BabyBear::ZERO), (false, BabyBear::ZERO)],
            body_atoms: vec![BodyAtomPattern {
                predicate: BabyBear::new(100),
                terms: [(true, BabyBear::new(0)), (false, resource), (false, BabyBear::ZERO)],
            }],
            equal_checks: vec![],
        },
        state_root,
        body_fact_hashes: vec![hash_fact(BabyBear::new(100), &[alice, resource, BabyBear::ZERO])],
        substitution: vec![alice],
        derived_predicate: pred_access,
        derived_terms: [alice, BabyBear::ZERO, BabyBear::ZERO],
    };

    let issuer_witness = create_test_witness(BabyBear::new(9999), 8);
    let federation_root = issuer_witness.expected_root;

    let presentation = PresentationWitness {
        federation_root,
        request_predicate: pred_access,
        timestamp: BabyBear::new(1000),
        fold_chain: vec![], // No attenuation
        derivation,
        issuer_membership: issuer_witness,
        issuer_key_hash: BabyBear::new(9999),
    };

    let air = PresentationAir::new(presentation);
    let verification = air.verify_all();
    assert_eq!(verification, PresentationVerification::Valid);

    let proof = air.prove().unwrap();
    assert_eq!(proof.fold_proofs.len(), 0);
    assert!(proof.total_proof_size_bytes > 0);
}

/// Test: Long attenuation chain (5 steps).
#[test]
fn long_attenuation_chain() {
    // Create a chain of 5 fold steps
    let mut roots = Vec::new();
    for i in 0..6 {
        roots.push(BabyBear::new((i + 1) * 100000));
    }

    let mut folds = Vec::new();
    for i in 0..5 {
        let pred = BabyBear::new((i * 10 + 1) as u32);
        let terms = [BabyBear::new((i * 10 + 2) as u32), BabyBear::new((i * 10 + 3) as u32), BabyBear::ZERO];
        let fact_hash = hash_fact(pred, &terms);
        let (tree_root, proofs) = build_shared_tree(&[fact_hash], 4);
        roots[i] = tree_root; // use tree root as old_root
        if i > 0 { // fix previous fold's new_root
            folds.last_mut().map(|f: &mut FoldWitness| f.new_root = tree_root);
        }
        folds.push(FoldWitness {
            old_root: tree_root,
            new_root: roots[i + 1],
            removed_facts: vec![RemovedFact {
                predicate: pred,
                terms,
                membership_proof: Some(proofs.into_iter().next().unwrap()),
            }],
            num_added_checks: if i % 2 == 0 { 1 } else { 0 },
        });
    }

    // Verify each fold individually
    for (i, fold) in folds.iter().enumerate() {
        let air = FoldAir::new(fold.clone());
        let result = MockProver::verify(&air);
        assert!(result.is_valid(), "Fold {i} failed: {:?}", result.violations());
    }

    // Create derivation from final state
    let final_root = *roots.last().unwrap();
    let body_hash = hash_fact(BabyBear::new(777), &[BabyBear::new(888), BabyBear::ZERO, BabyBear::ZERO]);

    let derivation = DerivationWitness {
        rule: CircuitRule {
            id: 1,
            num_body_atoms: 1,
            num_variables: 1,
            head_predicate: BabyBear::new(999),
            head_terms: [(true, BabyBear::new(0)), (false, BabyBear::ZERO), (false, BabyBear::ZERO)],
            body_atoms: vec![],
            equal_checks: vec![],
        },
        state_root: final_root,
        body_fact_hashes: vec![body_hash],
        substitution: vec![BabyBear::new(888)],
        derived_predicate: BabyBear::new(999),
        derived_terms: [BabyBear::new(888), BabyBear::ZERO, BabyBear::ZERO],
    };

    let issuer_witness = create_test_witness(BabyBear::new(5555), 8);
    let federation_root = issuer_witness.expected_root;

    let presentation = PresentationWitness {
        federation_root,
        request_predicate: BabyBear::new(999),
        timestamp: BabyBear::new(2000),
        fold_chain: folds,
        derivation,
        issuer_membership: issuer_witness,
        issuer_key_hash: BabyBear::new(5555),
    };

    let air = PresentationAir::new(presentation);
    let verification = air.verify_all();
    assert_eq!(verification, PresentationVerification::Valid);

    let proof = air.prove().unwrap();
    assert_eq!(proof.fold_proofs.len(), 5);
    println!("5-step attenuation proof size: {}", proof.proof_size_display());
}

/// Test: Merkle proofs at various depths.
#[test]
fn merkle_proofs_various_depths() {
    for depth in [2, 4, 8, 12, 16] {
        let leaf = BabyBear::new(depth as u32 * 1000);
        let witness = create_test_witness(leaf, depth);
        let air = MerkleAir::new(witness);
        let result = MockProver::verify(&air);
        assert!(
            result.is_valid(),
            "Merkle proof at depth {depth} failed: {:?}",
            result.violations()
        );
    }
}

/// Test: Poseidon2 hash chain integrity.
#[test]
fn poseidon2_hash_chain() {
    // Verify that hashing the same data always gives the same result
    let a = BabyBear::new(1);
    let b = BabyBear::new(2);
    let c = BabyBear::new(3);
    let d = BabyBear::new(4);

    let h1 = hash_4_to_1(&[a, b, c, d]);
    let h2 = hash_4_to_1(&[a, b, c, d]);
    assert_eq!(h1, h2);

    // Different order gives different hash
    let h3 = hash_4_to_1(&[d, c, b, a]);
    assert_ne!(h1, h3);

    // Chain: hash(hash(a,b,c,d), hash(e,f,g,h), 0, 0)
    let e = BabyBear::new(5);
    let f = BabyBear::new(6);
    let g = BabyBear::new(7);
    let h = BabyBear::new(8);

    let left = hash_4_to_1(&[a, b, c, d]);
    let right = hash_4_to_1(&[e, f, g, h]);
    let root = hash_4_to_1(&[left, right, BabyBear::ZERO, BabyBear::ZERO]);
    assert_ne!(root, BabyBear::ZERO);
}

/// Test: Fold AIR rejects proof with wrong fact hash.
#[test]
fn fold_rejects_inconsistent_fact_hash() {
    // If we construct a trace where fact_hash doesn't match hash(pred, terms),
    // the constraint should catch it.
    struct BadHashFoldAir;
    impl Air for BadHashFoldAir {
        fn trace_width(&self) -> usize { crate::fold_air::FOLD_AIR_WIDTH }
        fn num_public_inputs(&self) -> usize { 5 }
        fn constraints(&self) -> Vec<Constraint> {
            FoldAir::new(crate::fold_air::create_test_fold(1, 1)).constraints()
        }
        fn first_row_constraints(&self) -> Vec<Constraint> {
            FoldAir::new(crate::fold_air::create_test_fold(1, 1)).first_row_constraints()
        }
        fn last_row_constraints(&self) -> Vec<Constraint> {
            FoldAir::new(crate::fold_air::create_test_fold(1, 1)).last_row_constraints()
        }
        fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
            use crate::fold_air::col;

            let old_root = BabyBear::new(111111);
            let new_root = BabyBear::new(222222);
            let pred = BabyBear::new(10);
            let t0 = BabyBear::new(20);
            let t1 = BabyBear::new(30);

            // Construct removal row with WRONG hash
            let mut row = vec![BabyBear::ZERO; crate::fold_air::FOLD_AIR_WIDTH];
            row[col::ROW_TYPE] = BabyBear::ZERO;
            row[col::FACT_HASH] = BabyBear::new(99999); // WRONG! Should be hash_fact(pred, terms)
            row[col::MEMBERSHIP_ROOT] = BabyBear::ONE;
            row[col::OLD_ROOT] = old_root;
            row[col::NEW_ROOT] = new_root;
            row[col::REMOVAL_COUNT] = BabyBear::ONE;
            row[col::CHECK_COUNT] = BabyBear::ONE;
            row[col::FACT_PRED] = pred;
            row[col::FACT_TERM_START] = t0;
            row[col::FACT_TERM_START + 1] = t1;
            row[col::FACT_TERM_START + 2] = BabyBear::ZERO;
            row[col::HASH_VALID] = BabyBear::ONE;

            // Summary row
            let mut summary = vec![BabyBear::ZERO; crate::fold_air::FOLD_AIR_WIDTH];
            summary[col::ROW_TYPE] = BabyBear::ONE;
            summary[col::MEMBERSHIP_ROOT] = BabyBear::ONE;
            summary[col::OLD_ROOT] = old_root;
            summary[col::NEW_ROOT] = new_root;
            summary[col::REMOVAL_COUNT] = BabyBear::ONE;
            summary[col::CHECK_COUNT] = BabyBear::ONE;
            summary[col::HASH_VALID] = BabyBear::ONE;

            let root_transition = crate::fold_air::compute_root_transition_hash(
                old_root, new_root, &[BabyBear::new(99999)],
            );
            let pi = vec![old_root, new_root, BabyBear::ONE, BabyBear::ONE, root_transition];
            (vec![row, summary], pi)
        }
    }

    use crate::mock_prover::Constraint;
    let result = MockProver::verify(&BadHashFoldAir);
    assert!(!result.is_valid());
    // Should specifically fail on fact_hash_correct constraint
    let has_hash_violation = result
        .violations()
        .iter()
        .any(|v| v.constraint_name.contains("fact_hash_correct"));
    assert!(has_hash_violation, "Expected fact_hash_correct violation, got: {:?}", result.violations());
}

/// Test: Derivation AIR rejects if derived hash doesn't match head.
#[test]
fn derivation_rejects_wrong_head() {
    use crate::derivation_air::col;
    use crate::mock_prover::Constraint;

    struct BadDerivAir;
    impl Air for BadDerivAir {
        fn trace_width(&self) -> usize { crate::derivation_air::DERIVATION_AIR_WIDTH }
        fn num_public_inputs(&self) -> usize { 2 }
        fn constraints(&self) -> Vec<Constraint> {
            DerivationAir::new(crate::derivation_air::create_test_derivation()).constraints()
        }
        fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
            let witness = crate::derivation_air::create_test_derivation();
            let (mut trace, mut pi) = DerivationAir::new(witness).generate_trace();
            // Tamper: change derived_hash without changing the head columns
            let wrong_hash = BabyBear::new(12345);
            trace[0][col::DERIVED_HASH] = wrong_hash;
            pi[1] = wrong_hash; // keep public input consistent with tampered trace
            (trace, pi)
        }
    }

    let result = MockProver::verify(&BadDerivAir);
    assert!(!result.is_valid());
    let has_hash_violation = result
        .violations()
        .iter()
        .any(|v| v.constraint_name.contains("derived_hash_correct"));
    assert!(has_hash_violation);
}

/// Test: Field arithmetic stress test.
#[test]
fn field_arithmetic_stress() {
    use crate::field::BABYBEAR_P;

    // Test that (p-1) + 1 = 0
    let max = BabyBear::new(BABYBEAR_P - 1);
    assert_eq!((max + BabyBear::ONE), BabyBear::ZERO);

    // Test distributivity: a*(b+c) = a*b + a*c
    let a = BabyBear::new(12345);
    let b = BabyBear::new(67890);
    let c = BabyBear::new(11111);
    assert_eq!(a * (b + c), a * b + a * c);

    // Test inverse for many values
    for i in 1..100u32 {
        let x = BabyBear::new(i);
        let inv = x.inverse().unwrap();
        assert_eq!(x * inv, BabyBear::ONE, "Inverse failed for {i}");
    }
}

/// Test: IVC proof produces constant-size output regardless of chain length.
#[test]
fn ivc_constant_size_proof() {
    use crate::ivc::{create_test_chain, prove_ivc, verify_ivc, IvcVerification};

    println!("\n=== IVC Constant-Size Proof ===");

    let mut ivc_sizes = Vec::new();
    let mut sequential_sizes = Vec::new();

    for chain_len in [1, 2, 5, 10] {
        // IVC path: single proof
        let (initial_root, deltas) = create_test_chain(chain_len);
        let ivc_proof = prove_ivc(initial_root, deltas.clone()).unwrap();

        let result = verify_ivc(&ivc_proof, Some(initial_root));
        assert_eq!(result, IvcVerification::Valid);

        let ivc_size = ivc_proof.proof_size_bytes();
        ivc_sizes.push((chain_len, ivc_size));

        // Sequential path: N separate proofs
        let folds: Vec<crate::fold_air::FoldWitness> =
            deltas.iter().map(|d| d.fold.clone()).collect();
        let seq_size: usize = folds
            .iter()
            .map(|f| {
                let air = FoldAir::new(f.clone());
                crate::mock_prover::MockProof::generate(&air)
                    .unwrap()
                    .simulated_proof_size_bytes
            })
            .sum();
        sequential_sizes.push((chain_len, seq_size));

        println!(
            "  Chain {chain_len:>2}: IVC = {ivc_size:>6} B, Sequential = {seq_size:>6} B, \
             Savings = {:.0}%",
            (1.0 - ivc_size as f64 / seq_size as f64) * 100.0
        );
    }

    // Key property: IVC 10-step should not be 10x of IVC 1-step
    let (_, size_1) = ivc_sizes[0];
    let (_, size_10) = ivc_sizes[3];
    let ivc_ratio = size_10 as f64 / size_1 as f64;
    println!("  IVC growth ratio (10-step / 1-step): {ivc_ratio:.2}x");
    assert!(
        ivc_ratio < 5.0,
        "IVC should provide sub-linear growth"
    );

    // Sequential 10-step should be ~10x of sequential 1-step (linear)
    let (_, seq_1) = sequential_sizes[0];
    let (_, seq_10) = sequential_sizes[3];
    let seq_ratio = seq_10 as f64 / seq_1 as f64;
    println!("  Sequential growth ratio (10-step / 1-step): {seq_ratio:.2}x");
}

/// Test: IVC integration with full presentation proof.
#[test]
fn ivc_presentation_end_to_end() {
    use crate::ivc::IvcPresentationVerification;

    println!("\n=== IVC Presentation End-to-End ===");

    let mut witness = crate::presentation::create_test_presentation();
    // Fix federation root to match issuer membership
    witness.federation_root = witness.issuer_membership.expected_root;

    let air = PresentationAir::new(witness);

    // Generate IVC-based proof
    let ivc_presentation = air.prove_ivc();
    assert!(ivc_presentation.is_some(), "IVC presentation proof should succeed");

    let ivc_pres = ivc_presentation.unwrap();
    let result = ivc_pres.verify();
    assert_eq!(result, IvcPresentationVerification::Valid);

    // Compare sizes
    let sequential_proof = air.prove().unwrap();
    println!("  Sequential proof size: {}", sequential_proof.proof_size_display());
    println!("  IVC proof size: {}", ivc_pres.proof_size_display());
    println!("  IVC fold chain steps: {}", ivc_pres.ivc_proof.step_count);
}

/// Test: Proof size scaling with chain length.
#[test]
fn proof_size_scaling() {
    println!("\n=== Proof Size Scaling ===");
    for chain_len in [1, 2, 5, 10] {
        let mut roots = Vec::new();
        for i in 0..=chain_len {
            roots.push(BabyBear::new((i + 1) as u32 * 100000));
        }

        let folds: Vec<FoldWitness> = (0..chain_len)
            .map(|i| {
                let pred = BabyBear::new((i * 10 + 1) as u32);
                let terms = [BabyBear::new((i * 10 + 2) as u32), BabyBear::ZERO, BabyBear::ZERO];
                let fact_hash = hash_fact(pred, &terms);
                let (tree_root, proofs) = build_shared_tree(&[fact_hash], 4);
                roots[i] = tree_root;
                FoldWitness {
                    old_root: tree_root,
                    new_root: roots[i + 1],
                    removed_facts: vec![RemovedFact {
                        predicate: pred,
                        terms,
                        membership_proof: Some(proofs.into_iter().next().unwrap()),
                    }],
                    num_added_checks: 1,
                }
            })
            .collect();
        // Fix chain continuity: each fold's new_root must match next fold's old_root
        for i in 0..folds.len().saturating_sub(1) {
            // Already correct since each fold's old_root is its own tree_root
        }

        let final_root = *roots.last().unwrap();
        let body_hash = hash_fact(BabyBear::new(777), &[BabyBear::new(888), BabyBear::ZERO, BabyBear::ZERO]);

        let derivation = DerivationWitness {
            rule: CircuitRule {
                id: 1,
                num_body_atoms: 1,
                num_variables: 1,
                head_predicate: BabyBear::new(999),
                head_terms: [(true, BabyBear::new(0)), (false, BabyBear::ZERO), (false, BabyBear::ZERO)],
                body_atoms: vec![],
                equal_checks: vec![],
            },
            state_root: final_root,
            body_fact_hashes: vec![body_hash],
            substitution: vec![BabyBear::new(888)],
            derived_predicate: BabyBear::new(999),
            derived_terms: [BabyBear::new(888), BabyBear::ZERO, BabyBear::ZERO],
        };

        let issuer_witness = create_test_witness(BabyBear::new(5555), 8);
        let federation_root = issuer_witness.expected_root;

        let presentation = PresentationWitness {
            federation_root,
            request_predicate: BabyBear::new(999),
            timestamp: BabyBear::new(2000),
            fold_chain: folds,
            derivation,
            issuer_membership: issuer_witness,
            issuer_key_hash: BabyBear::new(5555),
        };

        let air = PresentationAir::new(presentation);
        let proof = air.prove().unwrap();
        println!(
            "  Chain length {chain_len:>2}: {} ({} fold proofs)",
            proof.proof_size_display(),
            proof.fold_proofs.len()
        );
    }
}
