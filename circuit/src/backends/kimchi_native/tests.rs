//! Tests for the Kimchi native backend circuits.
use ark_ff::{One, Zero};
use mina_curves::pasta::Fp;
use mina_poseidon::{constants::PlonkSpongeConstantsKimchi, pasta::FULL_ROUNDS, poseidon::{ArithmeticSponge, Sponge}};
use kimchi::{curve::KimchiCurve, proof::ProverProof};
use mina_curves::pasta::Vesta;
use poly_commitment::commitment::CommitmentCurve;
use groupmap::GroupMap;
use rand_core::OsRng;
use super::*;
use super::derivation::*;
use super::fold::*;
use super::ivc::*;
use super::non_membership::*;
use super::predicates::*;
use super::presentation::*;

fn create_test_derivation_fp() -> KimchiDerivationWitness {
    let rule = KimchiRule { id: 1, num_body_atoms: 2, num_variables: 2, head_predicate: Fp::from(300u64),
        head_terms: [(true, Fp::from(0u64)), (true, Fp::from(1u64)), (false, Fp::zero()), (false, Fp::zero())], equal_checks: vec![], gte_check: None };
    let alice = Fp::from(1000u64); let file = Fp::from(2000u64);
    let bf1 = hash_fact_fp(Fp::from(100u64), &[alice, file, Fp::zero()]); let bf2 = hash_fact_fp(Fp::from(200u64), &[alice, file, Fp::zero()]);
    KimchiDerivationWitness { rule, state_root: Fp::from(99999u64), body_fact_hashes: vec![bf1, bf2], substitution: vec![alice, file], derived_predicate: Fp::from(300u64), derived_terms: [alice, file, Fp::zero(), Fp::zero()] }
}

#[test] fn test_kimchi_native_hash_fact_deterministic() { let p = Fp::from(100u64); let t = [Fp::from(1u64), Fp::from(2u64), Fp::from(3u64)]; assert_eq!(hash_fact_fp(p, &t), hash_fact_fp(p, &t)); assert_ne!(hash_fact_fp(p, &t), Fp::zero()); }
#[test] fn test_kimchi_native_witness_head_match() { assert!(create_test_derivation_fp().check_head_match()); }
#[test] fn test_kimchi_native_witness_head_mismatch() { let mut w = create_test_derivation_fp(); w.derived_terms[0] = Fp::from(9999u64); assert!(!w.check_head_match()); }
#[test] fn test_kimchi_native_derivation_circuit_build() { let c = KimchiDerivationCircuit::new(create_test_derivation_fp()); let (g, pc) = c.build_circuit(); assert_eq!(pc, 2); assert!(!g.is_empty()); }
#[test] fn test_kimchi_native_derivation_prove_verify() {
    let w = create_test_derivation_fp(); let dh = w.derived_hash(); let sr = w.state_root;
    let proof = KimchiNativeBackend::prove_derivation(&w).expect("ok");
    assert_eq!(proof.circuit_type, KimchiNativeCircuitType::Derivation);
    assert!(KimchiNativeBackend::verify_derivation(&proof, &sr, &dh).expect("ok"));
}
#[test] fn test_kimchi_native_derivation_wrong_root_fails() { let w = create_test_derivation_fp(); let dh = w.derived_hash(); let proof = KimchiNativeBackend::prove_derivation(&w).expect("ok"); assert!(!KimchiNativeBackend::verify_derivation(&proof, &Fp::from(11111u64), &dh).expect("ok")); }
#[test] fn test_kimchi_native_derivation_wrong_hash_fails() { let w = create_test_derivation_fp(); let sr = w.state_root; let proof = KimchiNativeBackend::prove_derivation(&w).expect("ok"); assert!(!KimchiNativeBackend::verify_derivation(&proof, &sr, &Fp::from(77777u64)).expect("ok")); }
#[test] fn test_kimchi_native_derivation_with_equal_check() {
    let rule = KimchiRule { id: 2, num_body_atoms: 1, num_variables: 1, head_predicate: Fp::from(400u64),
        head_terms: [(true, Fp::from(0u64)), (false, Fp::zero()), (false, Fp::zero()), (false, Fp::zero())],
        equal_checks: vec![KimchiEqualCheck { lhs_is_var: true, lhs_value: Fp::from(0u64), rhs_is_var: true, rhs_value: Fp::from(0u64) }], gte_check: None };
    let alice = Fp::from(1000u64); let bf = hash_fact_fp(Fp::from(100u64), &[alice, alice, Fp::zero()]);
    let w = KimchiDerivationWitness { rule, state_root: Fp::from(99999u64), body_fact_hashes: vec![bf], substitution: vec![alice], derived_predicate: Fp::from(400u64), derived_terms: [alice, Fp::zero(), Fp::zero(), Fp::zero()] };
    let proof = KimchiNativeBackend::prove_derivation(&w).expect("ok");
    assert!(KimchiNativeBackend::verify_derivation(&proof, &w.state_root, &w.derived_hash()).expect("ok"));
}
#[test] fn test_kimchi_native_derivation_with_gte_check() {
    let rule = KimchiRule { id: 3, num_body_atoms: 1, num_variables: 3, head_predicate: Fp::from(600u64),
        head_terms: [(true, Fp::from(0u64)), (true, Fp::from(2u64)), (false, Fp::zero()), (false, Fp::zero())],
        equal_checks: vec![], gte_check: Some(KimchiGteCheck { lhs_is_var: true, lhs_value: Fp::from(1u64), rhs_is_var: true, rhs_value: Fp::from(2u64) }) };
    let alice = Fp::from(1000u64); let budget = Fp::from(100u64); let amount = Fp::from(50u64);
    let bf = hash_fact_fp(Fp::from(500u64), &[alice, budget, Fp::zero()]);
    let w = KimchiDerivationWitness { rule, state_root: Fp::from(99999u64), body_fact_hashes: vec![bf], substitution: vec![alice, budget, amount], derived_predicate: Fp::from(600u64), derived_terms: [alice, amount, Fp::zero(), Fp::zero()] };
    let proof = KimchiNativeBackend::prove_derivation(&w).expect("ok");
    assert!(KimchiNativeBackend::verify_derivation(&proof, &w.state_root, &w.derived_hash()).expect("ok"));
}
#[test] fn test_kimchi_native_non_membership() {
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params(); let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p); s.absorb(&coeffs); let ar = s.squeeze();
    let proof = KimchiNativeBackend::prove_non_membership(Fp::from(5u64), &coeffs, ar).expect("ok");
    assert!(KimchiNativeBackend::verify_non_membership(&proof, &Fp::from(5u64), &ar).expect("ok"));
}
#[test] fn test_kimchi_native_membership_element_in_set_fails() {
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params(); let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p); s.absorb(&coeffs); let ar = s.squeeze();
    assert!(KimchiNativeBackend::prove_non_membership(Fp::from(2u64), &coeffs, ar).is_err());
}
#[test] fn test_kimchi_native_backend_name() { assert_eq!(KimchiNativeBackend::backend_name(), "kimchi-native"); }

fn create_test_fold_fp(nr: usize) -> KimchiFoldWitness {
    let fh: Vec<Fp> = (0..nr).map(|i| hash_fact_fp(Fp::from((i*100+10) as u64), &[Fp::from((i*100+20) as u64), Fp::from((i*100+30) as u64), Fp::zero()])).collect();
    let (old_root, proofs) = build_fp_merkle_tree(&fh, FOLD_TREE_DEPTH);
    let removals = fh.into_iter().zip(proofs).map(|(f, p)| KimchiFoldRemoval { fact_hash: f, membership_proof: p }).collect();
    KimchiFoldWitness { old_root, new_root: Fp::from(222222u64), removals, checks_commitment: Fp::zero() }
}

#[test] fn test_kimchi_native_fold_single_removal_prove_verify() { let w = create_test_fold_fp(1); let or = w.old_root; let nr = w.new_root; let proof = KimchiNativeBackend::prove_fold(w.old_root, w.new_root, w.removals, w.checks_commitment).expect("ok"); assert!(KimchiNativeBackend::verify_fold(&proof, &or, &nr).expect("ok")); }
#[test] fn test_kimchi_native_fold_multiple_removals_prove_verify() { let w = create_test_fold_fp(3); let or = w.old_root; let nr = w.new_root; let proof = KimchiNativeBackend::prove_fold(w.old_root, w.new_root, w.removals, w.checks_commitment).expect("ok"); assert!(KimchiNativeBackend::verify_fold(&proof, &or, &nr).expect("ok")); }
#[test] fn test_kimchi_native_fold_wrong_old_root_rejected() { let w = create_test_fold_fp(2); let nr = w.new_root; let proof = KimchiNativeBackend::prove_fold(w.old_root, w.new_root, w.removals, w.checks_commitment).expect("ok"); assert!(!KimchiNativeBackend::verify_fold(&proof, &Fp::from(99999u64), &nr).expect("ok")); }
#[test] fn test_kimchi_native_fold_tampered_removal_rejected() { let mut w = create_test_fold_fp(2); w.removals[0].fact_hash = Fp::from(77777u64); assert!(KimchiNativeBackend::prove_fold(w.old_root, w.new_root, w.removals, w.checks_commitment).is_err()); }

#[test] fn test_kimchi_ivc_3_step_chain_prove_verify() {
    let steps = vec![KimchiFoldStep { pre_state: Fp::from(1000u64), post_state: Fp::from(2000u64) }, KimchiFoldStep { pre_state: Fp::from(2000u64), post_state: Fp::from(3000u64) }, KimchiFoldStep { pre_state: Fp::from(3000u64), post_state: Fp::from(4000u64) }];
    let proof = KimchiNativeBackend::prove_ivc(&steps).expect("ok");
    assert!(KimchiNativeBackend::verify_ivc(&proof, &Fp::from(1000u64), &Fp::from(4000u64)).expect("ok"));
}
#[test] fn test_kimchi_ivc_chain_break_rejected() { let steps = vec![KimchiFoldStep { pre_state: Fp::from(100u64), post_state: Fp::from(200u64) }, KimchiFoldStep { pre_state: Fp::from(999u64), post_state: Fp::from(300u64) }]; assert!(KimchiNativeBackend::prove_ivc(&steps).is_err()); }

#[test] fn test_kimchi_ivc_wrong_accumulated_hash_rejected() {
    let steps = vec![
        KimchiFoldStep { pre_state: Fp::from(1000u64), post_state: Fp::from(2000u64) },
        KimchiFoldStep { pre_state: Fp::from(2000u64), post_state: Fp::from(3000u64) },
        KimchiFoldStep { pre_state: Fp::from(3000u64), post_state: Fp::from(4000u64) },
    ];
    let mut proof = KimchiNativeBackend::prove_ivc(&steps).expect("ok");
    // Tamper with accumulated hash
    proof.accumulated_hash = Fp::from(99999u64);
    assert!(!KimchiNativeBackend::verify_ivc(&proof, &Fp::from(1000u64), &Fp::from(4000u64)).expect("ok"));
}

#[test] fn test_kimchi_ivc_wrong_initial_root_rejected() {
    let steps = vec![
        KimchiFoldStep { pre_state: Fp::from(1000u64), post_state: Fp::from(2000u64) },
        KimchiFoldStep { pre_state: Fp::from(2000u64), post_state: Fp::from(3000u64) },
    ];
    let proof = KimchiNativeBackend::prove_ivc(&steps).expect("ok");
    assert!(!KimchiNativeBackend::verify_ivc(&proof, &Fp::from(9999u64), &Fp::from(3000u64)).expect("ok"));
}

#[test] fn test_kimchi_ivc_wrong_final_root_rejected() {
    let steps = vec![
        KimchiFoldStep { pre_state: Fp::from(1000u64), post_state: Fp::from(2000u64) },
        KimchiFoldStep { pre_state: Fp::from(2000u64), post_state: Fp::from(3000u64) },
    ];
    let proof = KimchiNativeBackend::prove_ivc(&steps).expect("ok");
    assert!(!KimchiNativeBackend::verify_ivc(&proof, &Fp::from(1000u64), &Fp::from(9999u64)).expect("ok"));
}

#[test] fn test_kimchi_ivc_single_step_prove_verify() {
    let steps = vec![KimchiFoldStep { pre_state: Fp::from(100u64), post_state: Fp::from(200u64) }];
    let proof = KimchiNativeBackend::prove_ivc(&steps).expect("ok");
    assert!(KimchiNativeBackend::verify_ivc(&proof, &Fp::from(100u64), &Fp::from(200u64)).expect("ok"));
}

#[test] fn test_kimchi_presentation_prove_verify() {
    let fr = Fp::from(1000000u64); let rp = [Fp::from(111u64),Fp::from(222u64),Fp::from(333u64),Fp::from(444u64)];
    let ts = Fp::from(1716000000u64); let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64); let dh = Fp::from(66666u64); let nre = Fp::from(77777u64);
    let pt = compute_presentation_tag(Fp::from(88888u64), Fp::from(12345u64), vn);
    let cc = compute_composition_commitment(fch, dh, pt);
    let w = KimchiPresentationWitness { federation_root: fr, request_predicate: rp, timestamp: ts, verifier_nonce: vn, composition_commitment: cc, presentation_tag: pt, issuer_membership_hash: Fp::from(42424242u64), fold_chain_hash: fch, derivation_hash: dh, non_revocation_eval: nre, final_root: Fp::from(88888u64), randomness: Fp::from(12345u64) };
    let proof = KimchiNativeBackend::prove_presentation(&w).expect("ok");
    assert_eq!(KimchiNativeBackend::verify_presentation(&proof).expect("ok"), KimchiPresentationVerification::Valid);
}

#[test] fn test_kimchi_presentation_wrong_composition_commitment_fails() {
    let fr = Fp::from(1000000u64); let rp = [Fp::from(111u64),Fp::from(222u64),Fp::from(333u64),Fp::from(444u64)];
    let ts = Fp::from(1716000000u64); let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64); let dh = Fp::from(66666u64); let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64); let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    // Wrong composition commitment (does not match Poseidon hash of inputs)
    let wrong_cc = Fp::from(99999u64);
    let w = KimchiPresentationWitness { federation_root: fr, request_predicate: rp, timestamp: ts, verifier_nonce: vn, composition_commitment: wrong_cc, presentation_tag: pt, issuer_membership_hash: Fp::from(42424242u64), fold_chain_hash: fch, derivation_hash: dh, non_revocation_eval: nre, final_root, randomness };
    assert!(KimchiNativeBackend::prove_presentation(&w).is_err());
}

#[test] fn test_kimchi_presentation_wrong_tag_different_nonce_fails() {
    let fr = Fp::from(1000000u64); let rp = [Fp::from(111u64),Fp::from(222u64),Fp::from(333u64),Fp::from(444u64)];
    let ts = Fp::from(1716000000u64); let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64); let dh = Fp::from(66666u64); let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64); let randomness = Fp::from(12345u64);
    // Compute tag with DIFFERENT nonce than the one in the witness
    let wrong_nonce = Fp::from(111111111u64);
    let pt = compute_presentation_tag(final_root, randomness, wrong_nonce);
    let cc = compute_composition_commitment(fch, dh, pt);
    // Witness claims verifier_nonce=vn but tag was computed with wrong_nonce
    let w = KimchiPresentationWitness { federation_root: fr, request_predicate: rp, timestamp: ts, verifier_nonce: vn, composition_commitment: cc, presentation_tag: pt, issuer_membership_hash: Fp::from(42424242u64), fold_chain_hash: fch, derivation_hash: dh, non_revocation_eval: nre, final_root, randomness };
    assert!(KimchiNativeBackend::prove_presentation(&w).is_err());
}

#[test] fn test_kimchi_presentation_zero_composition_commitment_fails() {
    let fr = Fp::from(1000000u64); let rp = [Fp::from(111u64),Fp::from(222u64),Fp::from(333u64),Fp::from(444u64)];
    let ts = Fp::from(1716000000u64); let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64); let dh = Fp::from(66666u64); let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64); let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    // Zero composition commitment must be rejected
    let w = KimchiPresentationWitness { federation_root: fr, request_predicate: rp, timestamp: ts, verifier_nonce: vn, composition_commitment: Fp::zero(), presentation_tag: pt, issuer_membership_hash: Fp::from(42424242u64), fold_chain_hash: fch, derivation_hash: dh, non_revocation_eval: nre, final_root, randomness };
    assert!(KimchiNativeBackend::prove_presentation(&w).is_err());
}

#[test] fn test_kimchi_presentation_revoked_credential_fails() {
    let fr = Fp::from(1000000u64); let rp = [Fp::from(111u64),Fp::from(222u64),Fp::from(333u64),Fp::from(444u64)];
    let ts = Fp::from(1716000000u64); let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64); let dh = Fp::from(66666u64);
    let final_root = Fp::from(88888u64); let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    let cc = compute_composition_commitment(fch, dh, pt);
    // Zero non_revocation_eval = revoked credential
    let w = KimchiPresentationWitness { federation_root: fr, request_predicate: rp, timestamp: ts, verifier_nonce: vn, composition_commitment: cc, presentation_tag: pt, issuer_membership_hash: Fp::from(42424242u64), fold_chain_hash: fch, derivation_hash: dh, non_revocation_eval: Fp::zero(), final_root, randomness };
    assert!(KimchiNativeBackend::prove_presentation(&w).is_err());
}

#[test] fn test_kimchi_arithmetic_predicate_gte_passes() {
    let inputs = vec![Fp::from(60u64), Fp::from(50u64)]; let ops = vec![KimchiArithOp::Input(0), KimchiArithOp::Input(1), KimchiArithOp::Add(0,1)];
    let rc = hash_fact_fp(Fp::from(999u64), &inputs);
    let w = KimchiArithmeticPredicateWitness { inputs, ops, result_slot: 2, comparison_value: Fp::from(100u64), comparison_op: KimchiCompareOp::Gte, result_commitment: rc };
    let proof = KimchiNativeBackend::prove_arithmetic_predicate(&w).expect("ok");
    assert!(KimchiNativeBackend::verify_arithmetic_predicate(&proof, &rc, &Fp::from(100u64), KimchiCompareOp::Gte).expect("ok"));
}

#[test] fn test_kimchi_relational_predicate_gt_passes() {
    let w = KimchiRelationalPredicateWitness { value_a: Fp::from(100u64), blinding_a: Fp::from(111u64), value_b: Fp::from(50u64), blinding_b: Fp::from(222u64), relation: KimchiRelationType::GreaterThan };
    let ca = w.commitment_a(); let cb = w.commitment_b();
    let proof = KimchiNativeBackend::prove_relational_predicate(&w).expect("ok");
    assert!(KimchiNativeBackend::verify_relational_predicate(&proof, &ca, &cb, KimchiRelationType::GreaterThan).expect("ok"));
}

#[test] fn test_kimchi_temporal_predicate_all_pass() {
    let ah = hash_fact_fp(Fp::from(42u64), &[Fp::from(1u64)]);
    let srs: Vec<Fp> = (0..4).map(|i| Fp::from(1000u64+i)).collect();
    let w = KimchiTemporalPredicateWitness { values: vec![Fp::from(150u64), Fp::from(200u64), Fp::from(100u64), Fp::from(300u64)], state_roots: srs.clone(), attribute_hash: ah, threshold: Fp::from(100u64), initial_block_height: 500 };
    let proof = KimchiNativeBackend::prove_temporal_predicate(&w).expect("ok");
    assert!(KimchiNativeBackend::verify_temporal_predicate(&proof, &ah, 4, &srs[3], 500).expect("ok"));
}

#[test] fn test_kimchi_compound_predicate_and_passes() {
    let subs = vec![KimchiSubPredicateResult { proof_hash: Fp::from(1u64), result: true }, KimchiSubPredicateResult { proof_hash: Fp::from(2u64), result: true }, KimchiSubPredicateResult { proof_hash: Fp::from(3u64), result: true }];
    let rc = hash_fact_fp(Fp::from(555u64), &[Fp::from(1u64)]);
    let w = KimchiCompoundPredicateWitness { sub_results: subs, formula: KimchiBooleanFormula::And, result_commitment: rc };
    let proof = KimchiNativeBackend::prove_compound_predicate(&w).expect("ok");
    assert!(KimchiNativeBackend::verify_compound_predicate(&proof, &w.formula_hash(), 3, &rc, 3).expect("ok"));
}

// ==================================================================================
// Adversarial tests for derivation circuit constraints
// These verify that the Kimchi prover REJECTS tampered witnesses.
// ==================================================================================

/// Adversarial test: tamper with equal check terms so term_a != term_b.
/// The prover must reject because the equal check gate enforces w[0] - w[1] = 0.
#[test]
fn test_kimchi_native_derivation_adversarial_equal_check_tampered() {
    // Build a rule with an equal check: var[0] == var[0] (should always pass)
    let rule = KimchiRule {
        id: 10,
        num_body_atoms: 1,
        num_variables: 2,
        head_predicate: Fp::from(400u64),
        head_terms: [
            (true, Fp::from(0u64)),
            (false, Fp::zero()),
            (false, Fp::zero()),
            (false, Fp::zero()),
        ],
        // Equal check: var[0] == var[1] -- will FAIL if substitution has different values
        equal_checks: vec![KimchiEqualCheck {
            lhs_is_var: true,
            lhs_value: Fp::from(0u64),
            rhs_is_var: true,
            rhs_value: Fp::from(1u64),
        }],
        gte_check: None,
    };
    let alice = Fp::from(1000u64);
    let bob = Fp::from(2000u64); // different from alice!
    let bf = hash_fact_fp(Fp::from(100u64), &[alice, bob, Fp::zero()]);
    let w = KimchiDerivationWitness {
        rule,
        state_root: Fp::from(99999u64),
        body_fact_hashes: vec![bf],
        substitution: vec![alice, bob], // alice != bob
        derived_predicate: Fp::from(400u64),
        derived_terms: [alice, Fp::zero(), Fp::zero(), Fp::zero()],
    };
    // The prover should FAIL because the equal check gate enforces term_a == term_b
    // but alice (1000) != bob (2000)
    let result = KimchiNativeBackend::prove_derivation(&w);
    assert!(result.is_err(), "Prover must reject tampered equal check witness: {:?}", result);
}

/// Adversarial test: GTE check with term_a < term_b (negative diff).
/// The prover must reject because diff would wrap around the field,
/// making the bit decomposition invalid.
#[test]
fn test_kimchi_native_derivation_adversarial_gte_negative_diff() {
    let rule = KimchiRule {
        id: 11,
        num_body_atoms: 1,
        num_variables: 3,
        head_predicate: Fp::from(600u64),
        head_terms: [
            (true, Fp::from(0u64)),
            (true, Fp::from(2u64)),
            (false, Fp::zero()),
            (false, Fp::zero()),
        ],
        equal_checks: vec![],
        // GTE: var[1] >= var[2], but we'll set var[1] < var[2]
        gte_check: Some(KimchiGteCheck {
            lhs_is_var: true,
            lhs_value: Fp::from(1u64),
            rhs_is_var: true,
            rhs_value: Fp::from(2u64),
        }),
    };
    let alice = Fp::from(1000u64);
    let budget = Fp::from(30u64);   // budget = 30
    let amount = Fp::from(100u64);  // amount = 100 > budget!
    let bf = hash_fact_fp(Fp::from(500u64), &[alice, budget, Fp::zero()]);
    let w = KimchiDerivationWitness {
        rule,
        state_root: Fp::from(99999u64),
        body_fact_hashes: vec![bf],
        substitution: vec![alice, budget, amount], // budget < amount
        derived_predicate: Fp::from(600u64),
        derived_terms: [alice, amount, Fp::zero(), Fp::zero()],
    };
    // The prover should FAIL because budget(30) < amount(100), so diff wraps
    // and the high bit won't be 0 (or the bit decomposition won't sum correctly)
    let result = KimchiNativeBackend::prove_derivation(&w);
    assert!(result.is_err(), "Prover must reject GTE check with negative diff: {:?}", result);
}

/// Adversarial test: tamper with state root in body atom row.
/// The prover must reject because the body atom gate enforces w[0] == w[1]
/// (both should be state_root).
#[test]
fn test_kimchi_native_derivation_adversarial_state_root_tampered() {
    // Build a valid witness, then manually tamper with it
    let w = create_test_derivation_fp();
    let circuit = KimchiDerivationCircuit::new(w.clone());
    let mut wit = circuit.generate_witness();

    // Tamper: change w[1] in the first body atom row (row 2) to a different value
    // Row 0,1 are public inputs, row 2 is first body atom
    // The gate enforces w[0] - w[1] = 0, so changing w[1] breaks it
    wit[1][2] = Fp::from(77777u64); // tamper state_root copy

    // Try to prove with tampered witness
    let (gates, pc) = circuit.build_circuit();
    let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(gates, pc);
    let gm = <Vesta as CommitmentCurve>::Map::setup();
    let result = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
        BaseSponge,
        ScalarSponge,
        _,
    >(&gm, wit, &[], &index, &mut OsRng);
    assert!(result.is_err(), "Prover must reject tampered state root in body atom row: {:?}", result);
}

/// Adversarial test: tamper with head term equality.
/// The head term gate enforces w[0] - w[1] = 0 (derived_term == resolved_value).
#[test]
fn test_kimchi_native_derivation_adversarial_head_term_tampered() {
    let w = create_test_derivation_fp();
    let circuit = KimchiDerivationCircuit::new(w.clone());
    let mut wit = circuit.generate_witness();

    // Find the first head term row.
    // Layout: 2 (public) + 2 (body atoms) + poseidon rows + head terms
    // Poseidon: FULL_ROUNDS/5 + 1 per gadget, 2 gadgets
    let pgr = FULL_ROUNDS / 5 + 1;
    let head_term_start = 2 + 2 + 2 * pgr; // 2 PI + 2 body + 2 poseidon gadgets

    // Tamper: change w[1] in first head term row (should equal derived_terms[0])
    wit[1][head_term_start] = Fp::from(88888u64); // wrong resolved value

    let (gates, pc) = circuit.build_circuit();
    let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(gates, pc);
    let gm = <Vesta as CommitmentCurve>::Map::setup();
    let result = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
        BaseSponge,
        ScalarSponge,
        _,
    >(&gm, wit, &[], &index, &mut OsRng);
    assert!(result.is_err(), "Prover must reject tampered head term: {:?}", result);
}
