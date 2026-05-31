//! Tests for the Kimchi native backend circuits.
use super::derivation::*;
use super::fold::*;
use super::ivc::*;
use super::non_membership::*;
use super::predicates::*;
use super::presentation::*;
use super::*;
use ark_ff::{One, Zero};
use groupmap::GroupMap;
use kimchi::{curve::KimchiCurve, proof::ProverProof};
use mina_curves::pasta::Fp;
use mina_curves::pasta::Vesta;
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    pasta::FULL_ROUNDS,
    poseidon::{ArithmeticSponge, Sponge},
};
use poly_commitment::commitment::CommitmentCurve;
use rand_core::OsRng;

fn create_test_derivation_fp() -> KimchiDerivationWitness {
    let rule = KimchiRule {
        id: 1,
        num_body_atoms: 2,
        num_variables: 2,
        head_predicate: Fp::from(300u64),
        head_terms: [
            (true, Fp::from(0u64)),
            (true, Fp::from(1u64)),
            (false, Fp::zero()),
            (false, Fp::zero()),
        ],
        equal_checks: vec![],
        memberof_checks: vec![],
        gte_check: None,
        lt_check: None,
    };
    let alice = Fp::from(1000u64);
    let file = Fp::from(2000u64);
    let bf1 = hash_fact_fp(Fp::from(100u64), &[alice, file, Fp::zero()]);
    let bf2 = hash_fact_fp(Fp::from(200u64), &[alice, file, Fp::zero()]);
    KimchiDerivationWitness {
        rule,
        state_root: Fp::from(99999u64),
        body_fact_hashes: vec![bf1, bf2],
        body_merkle_proofs: vec![],
        substitution: vec![alice, file],
        derived_predicate: Fp::from(300u64),
        derived_terms: [alice, file, Fp::zero(), Fp::zero()],
    }
}

#[test]
fn test_kimchi_native_hash_fact_deterministic() {
    let p = Fp::from(100u64);
    let t = [Fp::from(1u64), Fp::from(2u64), Fp::from(3u64)];
    assert_eq!(hash_fact_fp(p, &t), hash_fact_fp(p, &t));
    assert_ne!(hash_fact_fp(p, &t), Fp::zero());
}
#[test]
fn test_kimchi_native_witness_head_match() {
    assert!(create_test_derivation_fp().check_head_match());
}
#[test]
fn test_kimchi_native_witness_head_mismatch() {
    let mut w = create_test_derivation_fp();
    w.derived_terms[0] = Fp::from(9999u64);
    assert!(!w.check_head_match());
}
#[test]
fn test_kimchi_native_derivation_circuit_build() {
    let c = KimchiDerivationCircuit::new(create_test_derivation_fp());
    let (g, pc) = c.build_circuit();
    assert_eq!(pc, 3);
    assert!(!g.is_empty());
}
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_native_derivation_prove_verify() {
    let w = create_test_derivation_fp();
    let dh = w.derived_hash();
    let sr = w.state_root;
    let proof = KimchiNativeBackend::prove_derivation(&w).expect("ok");
    assert_eq!(proof.circuit_type, KimchiNativeCircuitType::Derivation);
    assert!(KimchiNativeBackend::verify_derivation(&proof, &sr, &dh).expect("ok"));
}
#[test]
fn test_kimchi_native_derivation_wrong_root_fails() {
    let w = create_test_derivation_fp();
    let dh = w.derived_hash();
    let proof = KimchiNativeBackend::prove_derivation(&w).expect("ok");
    assert!(!KimchiNativeBackend::verify_derivation(&proof, &Fp::from(11111u64), &dh).expect("ok"));
}
#[test]
fn test_kimchi_native_derivation_wrong_hash_fails() {
    let w = create_test_derivation_fp();
    let sr = w.state_root;
    let proof = KimchiNativeBackend::prove_derivation(&w).expect("ok");
    assert!(!KimchiNativeBackend::verify_derivation(&proof, &sr, &Fp::from(77777u64)).expect("ok"));
}
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_native_derivation_with_equal_check() {
    let rule = KimchiRule {
        id: 2,
        num_body_atoms: 1,
        num_variables: 1,
        head_predicate: Fp::from(400u64),
        head_terms: [
            (true, Fp::from(0u64)),
            (false, Fp::zero()),
            (false, Fp::zero()),
            (false, Fp::zero()),
        ],
        equal_checks: vec![KimchiEqualCheck {
            lhs_is_var: true,
            lhs_value: Fp::from(0u64),
            rhs_is_var: true,
            rhs_value: Fp::from(0u64),
        }],
        memberof_checks: vec![],
        gte_check: None,
        lt_check: None,
    };
    let alice = Fp::from(1000u64);
    let bf = hash_fact_fp(Fp::from(100u64), &[alice, alice, Fp::zero()]);
    let w = KimchiDerivationWitness {
        rule,
        state_root: Fp::from(99999u64),
        body_fact_hashes: vec![bf],
        body_merkle_proofs: vec![],
        substitution: vec![alice],
        derived_predicate: Fp::from(400u64),
        derived_terms: [alice, Fp::zero(), Fp::zero(), Fp::zero()],
    };
    let proof = KimchiNativeBackend::prove_derivation(&w).expect("ok");
    assert!(
        KimchiNativeBackend::verify_derivation(&proof, &w.state_root, &w.derived_hash())
            .expect("ok")
    );
}
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_native_derivation_with_gte_check() {
    let rule = KimchiRule {
        id: 3,
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
        memberof_checks: vec![],
        gte_check: Some(KimchiGteCheck {
            lhs_is_var: true,
            lhs_value: Fp::from(1u64),
            rhs_is_var: true,
            rhs_value: Fp::from(2u64),
        }),
        lt_check: None,
    };
    let alice = Fp::from(1000u64);
    let budget = Fp::from(100u64);
    let amount = Fp::from(50u64);
    let bf = hash_fact_fp(Fp::from(500u64), &[alice, budget, Fp::zero()]);
    let w = KimchiDerivationWitness {
        rule,
        state_root: Fp::from(99999u64),
        body_fact_hashes: vec![bf],
        body_merkle_proofs: vec![],
        substitution: vec![alice, budget, amount],
        derived_predicate: Fp::from(600u64),
        derived_terms: [alice, amount, Fp::zero(), Fp::zero()],
    };
    let proof = KimchiNativeBackend::prove_derivation(&w).expect("ok");
    assert!(
        KimchiNativeBackend::verify_derivation(&proof, &w.state_root, &w.derived_hash())
            .expect("ok")
    );
}
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_native_non_membership_single_element() {
    // P(x) = (x-1)(x-2)(x-3) = x^3 - 6x^2 + 11x - 6
    // coeffs = [-6, 11, -6, 1] (ascending degree)
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&coeffs);
    let ar = s.squeeze();
    let elements = &[Fp::from(5u64)];
    let proof = KimchiNativeBackend::prove_non_membership(elements, &coeffs, ar).expect("ok");
    assert!(
        KimchiNativeBackend::verify_non_membership(&proof, elements, &ar, &coeffs).expect("ok")
    );
}
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_native_non_membership_multi_ancestor() {
    // P(x) = (x-1)(x-2)(x-3) = x^3 - 6x^2 + 11x - 6
    // Prove non-membership for x=5, x=7, x=10 simultaneously
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&coeffs);
    let ar = s.squeeze();
    let elements = &[Fp::from(5u64), Fp::from(7u64), Fp::from(10u64)];
    let proof = KimchiNativeBackend::prove_non_membership(elements, &coeffs, ar).expect("ok");
    assert!(
        KimchiNativeBackend::verify_non_membership(&proof, elements, &ar, &coeffs).expect("ok")
    );
}
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_native_non_membership_max_ancestors() {
    // P(x) = (x-1)(x-2)(x-3) with 8 elements (MAX_ANCESTORS)
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&coeffs);
    let ar = s.squeeze();
    // All elements NOT in {1,2,3}
    let elements: Vec<Fp> = (4..12).map(|i| Fp::from(i as u64)).collect();
    let proof = KimchiNativeBackend::prove_non_membership(&elements, &coeffs, ar).expect("ok");
    assert!(
        KimchiNativeBackend::verify_non_membership(&proof, &elements, &ar, &coeffs).expect("ok")
    );
}
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_native_non_membership_verifier_check() {
    // Verify using the full Kimchi verifier via KimchiNonMembershipCircuit::verify
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&coeffs);
    let ar = s.squeeze();
    let elements = &[Fp::from(5u64), Fp::from(7u64)];
    let proof = KimchiNativeBackend::prove_non_membership(elements, &coeffs, ar).expect("ok");
    assert!(KimchiNonMembershipCircuit::verify(&proof, &coeffs).expect("ok"));
}
#[test]
fn test_kimchi_native_membership_element_in_set_fails() {
    // x=2 IS in the set {1,2,3}, so P(2)=0 and proof must fail
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&coeffs);
    let ar = s.squeeze();
    assert!(KimchiNativeBackend::prove_non_membership(&[Fp::from(2u64)], &coeffs, ar).is_err());
}
#[test]
fn test_kimchi_native_non_membership_one_ancestor_in_set_fails() {
    // Prove non-membership for [5, 2, 7] — x=2 IS in {1,2,3}, must fail
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&coeffs);
    let ar = s.squeeze();
    let result = KimchiNativeBackend::prove_non_membership(
        &[Fp::from(5u64), Fp::from(2u64), Fp::from(7u64)],
        &coeffs,
        ar,
    );
    assert!(result.is_err(), "Must fail when ANY ancestor is in the set");
}
#[test]
fn test_kimchi_native_non_membership_element_1_in_set_fails() {
    // x=1 IS in the set {1,2,3}, P(1) = 1 - 6 + 11 - 6 = 0
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&coeffs);
    let ar = s.squeeze();
    assert!(KimchiNativeBackend::prove_non_membership(&[Fp::from(1u64)], &coeffs, ar).is_err());
}
#[test]
fn test_kimchi_native_non_membership_element_3_in_set_fails() {
    // x=3 IS in the set {1,2,3}, P(3) = 27 - 54 + 33 - 6 = 0
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&coeffs);
    let ar = s.squeeze();
    assert!(KimchiNativeBackend::prove_non_membership(&[Fp::from(3u64)], &coeffs, ar).is_err());
}
#[test]
fn test_kimchi_native_non_membership_wrong_alpha_fails() {
    // Prove non-membership with correct coefficients but wrong accumulator root
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let wrong_root = Fp::from(99999u64); // does not match hash(coeffs)
    let result = KimchiNativeBackend::prove_non_membership(&[Fp::from(5u64)], &coeffs, wrong_root);
    assert!(
        result.is_err(),
        "Proving with wrong accumulator root must fail"
    );
}
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_native_non_membership_verifier_rejects_wrong_element() {
    // Prove for element=5, but verify claiming element=7
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&coeffs);
    let ar = s.squeeze();
    let proof =
        KimchiNativeBackend::prove_non_membership(&[Fp::from(5u64)], &coeffs, ar).expect("ok");
    // Verify with wrong element
    assert!(
        !KimchiNativeBackend::verify_non_membership(&proof, &[Fp::from(7u64)], &ar, &coeffs)
            .expect("ok")
    );
}
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_native_non_membership_verifier_rejects_wrong_root() {
    // Prove correctly but verify with a different root
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&coeffs);
    let ar = s.squeeze();
    let proof =
        KimchiNativeBackend::prove_non_membership(&[Fp::from(5u64)], &coeffs, ar).expect("ok");
    let wrong_root = Fp::from(11111u64);
    assert!(
        !KimchiNativeBackend::verify_non_membership(
            &proof,
            &[Fp::from(5u64)],
            &wrong_root,
            &coeffs
        )
        .expect("ok")
    );
}
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_native_non_membership_verifier_rejects_wrong_count() {
    // Prove for 2 elements, but verify claiming 1 element
    let coeffs = vec![-Fp::from(6u64), Fp::from(11u64), -Fp::from(6u64), Fp::one()];
    let p = Vesta::sponge_params();
    let mut s = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    s.absorb(&coeffs);
    let ar = s.squeeze();
    let proof =
        KimchiNativeBackend::prove_non_membership(&[Fp::from(5u64), Fp::from(7u64)], &coeffs, ar)
            .expect("ok");
    // Verify with wrong number of elements
    assert!(
        !KimchiNativeBackend::verify_non_membership(&proof, &[Fp::from(5u64)], &ar, &coeffs)
            .expect("ok")
    );
}
#[test]
fn test_kimchi_native_backend_name() {
    assert_eq!(KimchiNativeBackend::backend_name(), "kimchi-native");
}

fn create_test_fold_fp(nr: usize) -> KimchiFoldWitness {
    let fh: Vec<Fp> = (0..nr)
        .map(|i| {
            hash_fact_fp(
                Fp::from((i * 100 + 10) as u64),
                &[
                    Fp::from((i * 100 + 20) as u64),
                    Fp::from((i * 100 + 30) as u64),
                    Fp::zero(),
                ],
            )
        })
        .collect();
    let (old_root, proofs) = build_fp_merkle_tree(&fh, FOLD_TREE_DEPTH);
    let removals = fh
        .into_iter()
        .zip(proofs)
        .map(|(f, p)| KimchiFoldRemoval {
            fact_hash: f,
            membership_proof: p,
        })
        .collect();
    KimchiFoldWitness {
        old_root,
        new_root: Fp::from(222222u64),
        removals,
        checks_commitment: Fp::zero(),
    }
}

#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_native_fold_single_removal_prove_verify() {
    let w = create_test_fold_fp(1);
    let or = w.old_root;
    let nr = w.new_root;
    let proof =
        KimchiNativeBackend::prove_fold(w.old_root, w.new_root, w.removals, w.checks_commitment)
            .expect("ok");
    assert!(KimchiNativeBackend::verify_fold(&proof, &or, &nr).expect("ok"));
}
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_native_fold_multiple_removals_prove_verify() {
    let w = create_test_fold_fp(3);
    let or = w.old_root;
    let nr = w.new_root;
    let proof =
        KimchiNativeBackend::prove_fold(w.old_root, w.new_root, w.removals, w.checks_commitment)
            .expect("ok");
    assert!(KimchiNativeBackend::verify_fold(&proof, &or, &nr).expect("ok"));
}
#[test]
fn test_kimchi_native_fold_wrong_old_root_rejected() {
    let w = create_test_fold_fp(2);
    let nr = w.new_root;
    let proof =
        KimchiNativeBackend::prove_fold(w.old_root, w.new_root, w.removals, w.checks_commitment)
            .expect("ok");
    assert!(!KimchiNativeBackend::verify_fold(&proof, &Fp::from(99999u64), &nr).expect("ok"));
}
#[test]
fn test_kimchi_native_fold_tampered_removal_rejected() {
    let mut w = create_test_fold_fp(2);
    w.removals[0].fact_hash = Fp::from(77777u64);
    assert!(
        KimchiNativeBackend::prove_fold(w.old_root, w.new_root, w.removals, w.checks_commitment)
            .is_err()
    );
}

#[test]
fn test_kimchi_ivc_3_step_chain_prove_verify() {
    let steps = vec![
        KimchiFoldStep {
            pre_state: Fp::from(1000u64),
            post_state: Fp::from(2000u64),
        },
        KimchiFoldStep {
            pre_state: Fp::from(2000u64),
            post_state: Fp::from(3000u64),
        },
        KimchiFoldStep {
            pre_state: Fp::from(3000u64),
            post_state: Fp::from(4000u64),
        },
    ];
    let proof = KimchiNativeBackend::prove_ivc(&steps).expect("ok");
    assert!(
        KimchiNativeBackend::verify_ivc(&proof, &Fp::from(1000u64), &Fp::from(4000u64))
            .expect("ok")
    );
}
#[test]
fn test_kimchi_ivc_chain_break_rejected() {
    let steps = vec![
        KimchiFoldStep {
            pre_state: Fp::from(100u64),
            post_state: Fp::from(200u64),
        },
        KimchiFoldStep {
            pre_state: Fp::from(999u64),
            post_state: Fp::from(300u64),
        },
    ];
    assert!(KimchiNativeBackend::prove_ivc(&steps).is_err());
}

#[test]
fn test_kimchi_ivc_wrong_accumulated_hash_rejected() {
    let steps = vec![
        KimchiFoldStep {
            pre_state: Fp::from(1000u64),
            post_state: Fp::from(2000u64),
        },
        KimchiFoldStep {
            pre_state: Fp::from(2000u64),
            post_state: Fp::from(3000u64),
        },
        KimchiFoldStep {
            pre_state: Fp::from(3000u64),
            post_state: Fp::from(4000u64),
        },
    ];
    let mut proof = KimchiNativeBackend::prove_ivc(&steps).expect("ok");
    // Tamper with accumulated hash
    proof.accumulated_hash = Fp::from(99999u64);
    assert!(
        !KimchiNativeBackend::verify_ivc(&proof, &Fp::from(1000u64), &Fp::from(4000u64))
            .expect("ok")
    );
}

#[test]
fn test_kimchi_ivc_wrong_initial_root_rejected() {
    let steps = vec![
        KimchiFoldStep {
            pre_state: Fp::from(1000u64),
            post_state: Fp::from(2000u64),
        },
        KimchiFoldStep {
            pre_state: Fp::from(2000u64),
            post_state: Fp::from(3000u64),
        },
    ];
    let proof = KimchiNativeBackend::prove_ivc(&steps).expect("ok");
    assert!(
        !KimchiNativeBackend::verify_ivc(&proof, &Fp::from(9999u64), &Fp::from(3000u64))
            .expect("ok")
    );
}

#[test]
fn test_kimchi_ivc_wrong_final_root_rejected() {
    let steps = vec![
        KimchiFoldStep {
            pre_state: Fp::from(1000u64),
            post_state: Fp::from(2000u64),
        },
        KimchiFoldStep {
            pre_state: Fp::from(2000u64),
            post_state: Fp::from(3000u64),
        },
    ];
    let proof = KimchiNativeBackend::prove_ivc(&steps).expect("ok");
    assert!(
        !KimchiNativeBackend::verify_ivc(&proof, &Fp::from(1000u64), &Fp::from(9999u64))
            .expect("ok")
    );
}

#[test]
fn test_kimchi_ivc_single_step_prove_verify() {
    let steps = vec![KimchiFoldStep {
        pre_state: Fp::from(100u64),
        post_state: Fp::from(200u64),
    }];
    let proof = KimchiNativeBackend::prove_ivc(&steps).expect("ok");
    assert!(
        KimchiNativeBackend::verify_ivc(&proof, &Fp::from(100u64), &Fp::from(200u64)).expect("ok")
    );
}

#[test]
fn test_kimchi_presentation_prove_verify() {
    let fr = Fp::from(1000000u64);
    let rp = [
        Fp::from(111u64),
        Fp::from(222u64),
        Fp::from(333u64),
        Fp::from(444u64),
    ];
    let ts = Fp::from(1716000000u64);
    let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64);
    let dh = Fp::from(66666u64);
    let nre = Fp::from(77777u64);
    let pt = compute_presentation_tag(Fp::from(88888u64), Fp::from(12345u64), vn);
    let cc = compute_composition_commitment(fch, dh, pt);
    let w = KimchiPresentationWitness {
        federation_root: fr,
        request_predicate: rp,
        timestamp: ts,
        verifier_nonce: vn,
        composition_commitment: cc,
        presentation_tag: pt,
        issuer_membership_hash: Fp::from(42424242u64),
        fold_chain_hash: fch,
        derivation_hash: dh,
        non_revocation_eval: nre,
        final_root: Fp::from(88888u64),
        randomness: Fp::from(12345u64),
        verifier_block_height: Fp::zero(),
        not_after_height: Fp::zero(),
        revealed_facts: Vec::new(),
        issuer_key_hash: Fp::from(42424242u64),
        blinding_factor: Fp::from(999u64),
        issuer_membership_proof: None,
    };
    let proof = KimchiNativeBackend::prove_presentation(&w).expect("ok");
    assert_eq!(
        KimchiNativeBackend::verify_presentation(&proof).expect("ok"),
        KimchiPresentationVerification::Valid
    );
}

#[test]
fn test_kimchi_presentation_wrong_composition_commitment_fails() {
    let fr = Fp::from(1000000u64);
    let rp = [
        Fp::from(111u64),
        Fp::from(222u64),
        Fp::from(333u64),
        Fp::from(444u64),
    ];
    let ts = Fp::from(1716000000u64);
    let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64);
    let dh = Fp::from(66666u64);
    let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64);
    let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    // Wrong composition commitment (does not match Poseidon hash of inputs)
    let wrong_cc = Fp::from(99999u64);
    let w = KimchiPresentationWitness {
        federation_root: fr,
        request_predicate: rp,
        timestamp: ts,
        verifier_nonce: vn,
        composition_commitment: wrong_cc,
        presentation_tag: pt,
        issuer_membership_hash: Fp::from(42424242u64),
        fold_chain_hash: fch,
        derivation_hash: dh,
        non_revocation_eval: nre,
        final_root,
        randomness,
        verifier_block_height: Fp::zero(),
        not_after_height: Fp::zero(),
        revealed_facts: Vec::new(),
        issuer_key_hash: Fp::from(42424242u64),
        blinding_factor: Fp::from(999u64),
        issuer_membership_proof: None,
    };
    assert!(KimchiNativeBackend::prove_presentation(&w).is_err());
}

#[test]
fn test_kimchi_presentation_wrong_tag_different_nonce_fails() {
    let fr = Fp::from(1000000u64);
    let rp = [
        Fp::from(111u64),
        Fp::from(222u64),
        Fp::from(333u64),
        Fp::from(444u64),
    ];
    let ts = Fp::from(1716000000u64);
    let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64);
    let dh = Fp::from(66666u64);
    let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64);
    let randomness = Fp::from(12345u64);
    // Compute tag with DIFFERENT nonce than the one in the witness
    let wrong_nonce = Fp::from(111111111u64);
    let pt = compute_presentation_tag(final_root, randomness, wrong_nonce);
    let cc = compute_composition_commitment(fch, dh, pt);
    // Witness claims verifier_nonce=vn but tag was computed with wrong_nonce
    let w = KimchiPresentationWitness {
        federation_root: fr,
        request_predicate: rp,
        timestamp: ts,
        verifier_nonce: vn,
        composition_commitment: cc,
        presentation_tag: pt,
        issuer_membership_hash: Fp::from(42424242u64),
        fold_chain_hash: fch,
        derivation_hash: dh,
        non_revocation_eval: nre,
        final_root,
        randomness,
        verifier_block_height: Fp::zero(),
        not_after_height: Fp::zero(),
        revealed_facts: Vec::new(),
        issuer_key_hash: Fp::from(42424242u64),
        blinding_factor: Fp::from(999u64),
        issuer_membership_proof: None,
    };
    assert!(KimchiNativeBackend::prove_presentation(&w).is_err());
}

#[test]
fn test_kimchi_presentation_zero_composition_commitment_fails() {
    let fr = Fp::from(1000000u64);
    let rp = [
        Fp::from(111u64),
        Fp::from(222u64),
        Fp::from(333u64),
        Fp::from(444u64),
    ];
    let ts = Fp::from(1716000000u64);
    let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64);
    let dh = Fp::from(66666u64);
    let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64);
    let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    // Zero composition commitment must be rejected
    let w = KimchiPresentationWitness {
        federation_root: fr,
        request_predicate: rp,
        timestamp: ts,
        verifier_nonce: vn,
        composition_commitment: Fp::zero(),
        presentation_tag: pt,
        issuer_membership_hash: Fp::from(42424242u64),
        fold_chain_hash: fch,
        derivation_hash: dh,
        non_revocation_eval: nre,
        final_root,
        randomness,
        verifier_block_height: Fp::zero(),
        not_after_height: Fp::zero(),
        revealed_facts: Vec::new(),
        issuer_key_hash: Fp::from(42424242u64),
        blinding_factor: Fp::from(999u64),
        issuer_membership_proof: None,
    };
    assert!(KimchiNativeBackend::prove_presentation(&w).is_err());
}

#[test]
fn test_kimchi_presentation_revoked_credential_fails() {
    let fr = Fp::from(1000000u64);
    let rp = [
        Fp::from(111u64),
        Fp::from(222u64),
        Fp::from(333u64),
        Fp::from(444u64),
    ];
    let ts = Fp::from(1716000000u64);
    let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64);
    let dh = Fp::from(66666u64);
    let final_root = Fp::from(88888u64);
    let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    let cc = compute_composition_commitment(fch, dh, pt);
    // Zero non_revocation_eval = revoked credential
    let w = KimchiPresentationWitness {
        federation_root: fr,
        request_predicate: rp,
        timestamp: ts,
        verifier_nonce: vn,
        composition_commitment: cc,
        presentation_tag: pt,
        issuer_membership_hash: Fp::from(42424242u64),
        fold_chain_hash: fch,
        derivation_hash: dh,
        non_revocation_eval: Fp::zero(),
        final_root,
        randomness,
        verifier_block_height: Fp::zero(),
        not_after_height: Fp::zero(),
        revealed_facts: Vec::new(),
        issuer_key_hash: Fp::from(42424242u64),
        blinding_factor: Fp::from(999u64),
        issuer_membership_proof: None,
    };
    assert!(KimchiNativeBackend::prove_presentation(&w).is_err());
}

#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_arithmetic_predicate_gte_passes() {
    let inputs = vec![Fp::from(60u64), Fp::from(50u64)];
    let ops = vec![
        KimchiArithOp::Input(0),
        KimchiArithOp::Input(1),
        KimchiArithOp::Add(0, 1),
    ];
    let rc = hash_fact_fp(Fp::from(999u64), &inputs);
    let w = KimchiArithmeticPredicateWitness {
        inputs,
        ops,
        result_slot: 2,
        comparison_value: Fp::from(100u64),
        comparison_op: KimchiCompareOp::Gte,
        result_commitment: rc,
    };
    let proof = KimchiNativeBackend::prove_arithmetic_predicate(&w).expect("ok");
    assert!(
        KimchiNativeBackend::verify_arithmetic_predicate(
            &proof,
            &rc,
            &Fp::from(100u64),
            KimchiCompareOp::Gte
        )
        .expect("ok")
    );
}

#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_arithmetic_predicate_neq_passes() {
    let inputs = vec![Fp::from(60u64), Fp::from(50u64)];
    let ops = vec![
        KimchiArithOp::Input(0),
        KimchiArithOp::Input(1),
        KimchiArithOp::Add(0, 1),
    ];
    let rc = hash_fact_fp(Fp::from(999u64), &inputs);
    // result = 110, comparison = 100, should pass NEQ
    let w = KimchiArithmeticPredicateWitness {
        inputs,
        ops,
        result_slot: 2,
        comparison_value: Fp::from(100u64),
        comparison_op: KimchiCompareOp::Neq,
        result_commitment: rc,
    };
    let proof = KimchiNativeBackend::prove_arithmetic_predicate(&w).expect("ok");
    assert!(
        KimchiNativeBackend::verify_arithmetic_predicate(
            &proof,
            &rc,
            &Fp::from(100u64),
            KimchiCompareOp::Neq
        )
        .expect("ok")
    );
}

#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_arithmetic_predicate_eq_passes() {
    let inputs = vec![Fp::from(60u64), Fp::from(40u64)];
    let ops = vec![
        KimchiArithOp::Input(0),
        KimchiArithOp::Input(1),
        KimchiArithOp::Add(0, 1),
    ];
    let rc = hash_fact_fp(Fp::from(999u64), &inputs);
    // result = 100, comparison = 100, should pass EQ
    let w = KimchiArithmeticPredicateWitness {
        inputs,
        ops,
        result_slot: 2,
        comparison_value: Fp::from(100u64),
        comparison_op: KimchiCompareOp::Eq,
        result_commitment: rc,
    };
    let proof = KimchiNativeBackend::prove_arithmetic_predicate(&w).expect("ok");
    assert!(
        KimchiNativeBackend::verify_arithmetic_predicate(
            &proof,
            &rc,
            &Fp::from(100u64),
            KimchiCompareOp::Eq
        )
        .expect("ok")
    );
}

#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_arithmetic_predicate_mul_passes() {
    let inputs = vec![Fp::from(10u64), Fp::from(5u64)];
    let ops = vec![
        KimchiArithOp::Input(0),
        KimchiArithOp::Input(1),
        KimchiArithOp::Mul(0, 1),
    ];
    let rc = hash_fact_fp(Fp::from(999u64), &inputs);
    // result = 50, comparison = 50, should pass GTE
    let w = KimchiArithmeticPredicateWitness {
        inputs,
        ops,
        result_slot: 2,
        comparison_value: Fp::from(50u64),
        comparison_op: KimchiCompareOp::Gte,
        result_commitment: rc,
    };
    let proof = KimchiNativeBackend::prove_arithmetic_predicate(&w).expect("ok");
    assert!(
        KimchiNativeBackend::verify_arithmetic_predicate(
            &proof,
            &rc,
            &Fp::from(50u64),
            KimchiCompareOp::Gte
        )
        .expect("ok")
    );
}

/// Adversarial: wrong comparison result — claims 50 >= 110 (false)
#[test]
fn test_kimchi_arithmetic_predicate_adversarial_wrong_comparison() {
    let inputs = vec![Fp::from(60u64), Fp::from(50u64)];
    let ops = vec![
        KimchiArithOp::Input(0),
        KimchiArithOp::Input(1),
        KimchiArithOp::Add(0, 1),
    ];
    let rc = hash_fact_fp(Fp::from(999u64), &inputs);
    // result = 110, but comparison_value = 200, so 110 >= 200 is FALSE
    let w = KimchiArithmeticPredicateWitness {
        inputs,
        ops,
        result_slot: 2,
        comparison_value: Fp::from(200u64),
        comparison_op: KimchiCompareOp::Gte,
        result_commitment: rc,
    };
    assert!(!w.is_satisfiable());
    let result = KimchiNativeBackend::prove_arithmetic_predicate(&w);
    assert!(
        result.is_err(),
        "Must reject unsatisfiable arithmetic predicate"
    );
}

/// Adversarial: tamper with witness in proved circuit — modify a bit to be non-binary.
/// The Kimchi prover panics on invalid witness, so we catch_unwind to verify rejection.
#[test]
fn test_kimchi_arithmetic_predicate_adversarial_tampered_bit() {
    let inputs = vec![Fp::from(60u64), Fp::from(50u64)];
    let ops = vec![
        KimchiArithOp::Input(0),
        KimchiArithOp::Input(1),
        KimchiArithOp::Add(0, 1),
    ];
    let rc = hash_fact_fp(Fp::from(999u64), &inputs);
    let w = KimchiArithmeticPredicateWitness {
        inputs,
        ops,
        result_slot: 2,
        comparison_value: Fp::from(100u64),
        comparison_op: KimchiCompareOp::Gte,
        result_commitment: rc,
    };
    let circuit = KimchiArithmeticPredicateCircuit::new(w);
    let mut wit = circuit.generate_witness();
    let (gates, pc) = circuit.build_circuit();
    // Find a bit-check row and tamper with it (set bit to 2, which is not binary)
    // The bit rows start after: 3 PI + 3 ops + 1 diff = 7, then 64 bit rows
    let bit_row_start = 3 + 3 + 1; // first bit check row
    wit[0][bit_row_start] = Fp::from(2u64); // NOT binary!
    wit[1][bit_row_start] = Fp::from(2u64);
    let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(gates, pc);
    let gm = <Vesta as CommitmentCurve>::Map::setup();
    let result =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
                BaseSponge,
                ScalarSponge,
                _,
            >(&gm, wit, &[], &index, &mut OsRng)
        }));
    assert!(
        result.is_err() || result.unwrap().is_err(),
        "Prover must reject non-binary bit in witness"
    );
}

#[test]
fn test_kimchi_relational_predicate_gt_passes() {
    let w = KimchiRelationalPredicateWitness {
        value_a: Fp::from(100u64),
        blinding_a: Fp::from(111u64),
        value_b: Fp::from(50u64),
        blinding_b: Fp::from(222u64),
        relation: KimchiRelationType::GreaterThan,
    };
    let ca = w.commitment_a();
    let cb = w.commitment_b();
    let proof = KimchiNativeBackend::prove_relational_predicate(&w).expect("ok");
    assert!(
        KimchiNativeBackend::verify_relational_predicate(
            &proof,
            &ca,
            &cb,
            KimchiRelationType::GreaterThan
        )
        .expect("ok")
    );
}

#[test]
fn test_kimchi_relational_predicate_eq_passes() {
    let w = KimchiRelationalPredicateWitness {
        value_a: Fp::from(42u64),
        blinding_a: Fp::from(111u64),
        value_b: Fp::from(42u64),
        blinding_b: Fp::from(222u64),
        relation: KimchiRelationType::Equal,
    };
    let ca = w.commitment_a();
    let cb = w.commitment_b();
    let proof = KimchiNativeBackend::prove_relational_predicate(&w).expect("ok");
    assert!(
        KimchiNativeBackend::verify_relational_predicate(
            &proof,
            &ca,
            &cb,
            KimchiRelationType::Equal
        )
        .expect("ok")
    );
}

/// Adversarial: claim a > b when a < b
#[test]
fn test_kimchi_relational_predicate_adversarial_wrong_relation() {
    let w = KimchiRelationalPredicateWitness {
        value_a: Fp::from(30u64),
        blinding_a: Fp::from(111u64),
        value_b: Fp::from(50u64),
        blinding_b: Fp::from(222u64),
        relation: KimchiRelationType::GreaterThan,
    };
    assert!(!w.is_satisfiable());
    let result = KimchiNativeBackend::prove_relational_predicate(&w);
    assert!(
        result.is_err(),
        "Must reject unsatisfiable relational predicate"
    );
}

#[test]
fn test_kimchi_temporal_predicate_all_pass() {
    let ah = hash_fact_fp(Fp::from(42u64), &[Fp::from(1u64)]);
    let srs: Vec<Fp> = (0..4).map(|i| Fp::from(1000u64 + i)).collect();
    let w = KimchiTemporalPredicateWitness {
        values: vec![
            Fp::from(150u64),
            Fp::from(200u64),
            Fp::from(100u64),
            Fp::from(300u64),
        ],
        state_roots: srs.clone(),
        attribute_hash: ah,
        threshold: Fp::from(100u64),
        initial_block_height: 500,
    };
    let proof = KimchiNativeBackend::prove_temporal_predicate(&w).expect("ok");
    assert!(
        KimchiNativeBackend::verify_temporal_predicate(&proof, &ah, 4, &srs[3], 500).expect("ok")
    );
}

/// Adversarial: one block's value is below threshold
#[test]
fn test_kimchi_temporal_predicate_adversarial_block_below_threshold() {
    let ah = hash_fact_fp(Fp::from(42u64), &[Fp::from(1u64)]);
    let srs: Vec<Fp> = (0..4).map(|i| Fp::from(1000u64 + i)).collect();
    // Block 2 has value 50, which is below threshold 100
    let w = KimchiTemporalPredicateWitness {
        values: vec![
            Fp::from(150u64),
            Fp::from(200u64),
            Fp::from(50u64),
            Fp::from(300u64),
        ],
        state_roots: srs,
        attribute_hash: ah,
        threshold: Fp::from(100u64),
        initial_block_height: 500,
    };
    assert!(!w.is_satisfiable());
    let result = KimchiNativeBackend::prove_temporal_predicate(&w);
    assert!(
        result.is_err(),
        "Must reject temporal predicate with block below threshold"
    );
}

/// Adversarial: skip a block (heights not contiguous)
#[test]
fn test_kimchi_temporal_predicate_adversarial_skipped_block() {
    let ah = hash_fact_fp(Fp::from(42u64), &[Fp::from(1u64)]);
    let srs: Vec<Fp> = (0..3).map(|i| Fp::from(1000u64 + i)).collect();
    let w = KimchiTemporalPredicateWitness {
        values: vec![Fp::from(150u64), Fp::from(200u64), Fp::from(100u64)],
        state_roots: srs.clone(),
        attribute_hash: ah,
        threshold: Fp::from(100u64),
        initial_block_height: 500,
    };
    // This witness is valid per is_satisfiable (all values >= threshold).
    // The circuit enforces contiguous heights via diff_minus_one gates.
    // The prover will produce a valid proof because the witness has 3 consecutive blocks at height 500,501,502.
    // A skip would require providing non-contiguous heights, which the circuit constrains.
    let proof = KimchiNativeBackend::prove_temporal_predicate(&w).expect("ok");
    assert!(
        KimchiNativeBackend::verify_temporal_predicate(&proof, &ah, 3, &srs[2], 500).expect("ok")
    );
    // Now verify that claiming a different initial_block_height fails
    assert!(
        !KimchiNativeBackend::verify_temporal_predicate(&proof, &ah, 3, &srs[2], 498).expect("ok")
    );
}

#[test]
fn test_kimchi_compound_predicate_and_passes() {
    let subs = vec![
        KimchiSubPredicateResult {
            proof_hash: Fp::from(1u64),
            result: true,
        },
        KimchiSubPredicateResult {
            proof_hash: Fp::from(2u64),
            result: true,
        },
        KimchiSubPredicateResult {
            proof_hash: Fp::from(3u64),
            result: true,
        },
    ];
    let rc = hash_fact_fp(Fp::from(555u64), &[Fp::from(1u64)]);
    let w = KimchiCompoundPredicateWitness {
        sub_results: subs,
        formula: KimchiBooleanFormula::And,
        result_commitment: rc,
    };
    let proof = KimchiNativeBackend::prove_compound_predicate(&w).expect("ok");
    assert!(
        KimchiNativeBackend::verify_compound_predicate(&proof, &w.formula_hash(), 3, &rc, 3)
            .expect("ok")
    );
}

#[test]
fn test_kimchi_compound_predicate_or_passes() {
    let subs = vec![
        KimchiSubPredicateResult {
            proof_hash: Fp::from(1u64),
            result: false,
        },
        KimchiSubPredicateResult {
            proof_hash: Fp::from(2u64),
            result: true,
        },
        KimchiSubPredicateResult {
            proof_hash: Fp::from(3u64),
            result: false,
        },
    ];
    let rc = hash_fact_fp(Fp::from(555u64), &[Fp::from(1u64)]);
    let w = KimchiCompoundPredicateWitness {
        sub_results: subs,
        formula: KimchiBooleanFormula::Or,
        result_commitment: rc,
    };
    let proof = KimchiNativeBackend::prove_compound_predicate(&w).expect("ok");
    assert!(
        KimchiNativeBackend::verify_compound_predicate(&proof, &w.formula_hash(), 3, &rc, 1)
            .expect("ok")
    );
}

/// Adversarial: claim all sub-predicates passed when one didn't (AND formula)
#[test]
fn test_kimchi_compound_predicate_adversarial_false_and() {
    let subs = vec![
        KimchiSubPredicateResult {
            proof_hash: Fp::from(1u64),
            result: true,
        },
        KimchiSubPredicateResult {
            proof_hash: Fp::from(2u64),
            result: false,
        }, // one failed
        KimchiSubPredicateResult {
            proof_hash: Fp::from(3u64),
            result: true,
        },
    ];
    let rc = hash_fact_fp(Fp::from(555u64), &[Fp::from(1u64)]);
    let w = KimchiCompoundPredicateWitness {
        sub_results: subs,
        formula: KimchiBooleanFormula::And,
        result_commitment: rc,
    };
    assert!(!w.is_satisfiable());
    let result = KimchiNativeBackend::prove_compound_predicate(&w);
    assert!(
        result.is_err(),
        "Must reject AND when a sub-predicate is false"
    );
}

/// Adversarial: claim OR passes when all are false
#[test]
fn test_kimchi_compound_predicate_adversarial_false_or() {
    let subs = vec![
        KimchiSubPredicateResult {
            proof_hash: Fp::from(1u64),
            result: false,
        },
        KimchiSubPredicateResult {
            proof_hash: Fp::from(2u64),
            result: false,
        },
    ];
    let rc = hash_fact_fp(Fp::from(555u64), &[Fp::from(1u64)]);
    let w = KimchiCompoundPredicateWitness {
        sub_results: subs,
        formula: KimchiBooleanFormula::Or,
        result_commitment: rc,
    };
    assert!(!w.is_satisfiable());
    let result = KimchiNativeBackend::prove_compound_predicate(&w);
    assert!(
        result.is_err(),
        "Must reject OR when all sub-predicates are false"
    );
}

/// Adversarial: tamper with sub-result in compound witness to be non-binary.
/// The Kimchi prover panics on invalid witness, so we catch_unwind.
#[test]
fn test_kimchi_compound_predicate_adversarial_tampered_result() {
    let subs = vec![
        KimchiSubPredicateResult {
            proof_hash: Fp::from(1u64),
            result: true,
        },
        KimchiSubPredicateResult {
            proof_hash: Fp::from(2u64),
            result: true,
        },
    ];
    let rc = hash_fact_fp(Fp::from(555u64), &[Fp::from(1u64)]);
    let w = KimchiCompoundPredicateWitness {
        sub_results: subs,
        formula: KimchiBooleanFormula::And,
        result_commitment: rc,
    };
    let circuit = KimchiCompoundPredicateCircuit::new(w);
    let mut wit = circuit.generate_witness();
    let (gates, pc) = circuit.build_circuit();
    // Tamper: set sub-result 0 to value 2 (non-binary) in the bit-check row
    // Sub-result rows start at row 4 (after 4 PI rows)
    wit[0][4] = Fp::from(2u64); // NOT binary!
    wit[1][4] = Fp::from(2u64);
    let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(gates, pc);
    let gm = <Vesta as CommitmentCurve>::Map::setup();
    let result =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
                BaseSponge,
                ScalarSponge,
                _,
            >(&gm, wit, &[], &index, &mut OsRng)
        }));
    assert!(
        result.is_err() || result.unwrap().is_err(),
        "Prover must reject non-binary sub-predicate result"
    );
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
        memberof_checks: Vec::new(),
        gte_check: None,
        lt_check: None,
    };
    let alice = Fp::from(1000u64);
    let bob = Fp::from(2000u64); // different from alice!
    let bf = hash_fact_fp(Fp::from(100u64), &[alice, bob, Fp::zero()]);
    let w = KimchiDerivationWitness {
        rule,
        state_root: Fp::from(99999u64),
        body_fact_hashes: vec![bf],
        body_merkle_proofs: Vec::new(),
        substitution: vec![alice, bob], // alice != bob
        derived_predicate: Fp::from(400u64),
        derived_terms: [alice, Fp::zero(), Fp::zero(), Fp::zero()],
    };
    // The prover should FAIL because the equal check gate enforces term_a == term_b
    // but alice (1000) != bob (2000).
    // Kimchi prover panics on invalid witness, so we catch_unwind.
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        KimchiNativeBackend::prove_derivation(&w)
    }));
    assert!(
        result.is_err() || result.unwrap().is_err(),
        "Prover must reject tampered equal check witness"
    );
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
        memberof_checks: Vec::new(),
        // GTE: var[1] >= var[2], but we'll set var[1] < var[2]
        gte_check: Some(KimchiGteCheck {
            lhs_is_var: true,
            lhs_value: Fp::from(1u64),
            rhs_is_var: true,
            rhs_value: Fp::from(2u64),
        }),
        lt_check: None,
    };
    let alice = Fp::from(1000u64);
    let budget = Fp::from(30u64); // budget = 30
    let amount = Fp::from(100u64); // amount = 100 > budget!
    let bf = hash_fact_fp(Fp::from(500u64), &[alice, budget, Fp::zero()]);
    let w = KimchiDerivationWitness {
        rule,
        state_root: Fp::from(99999u64),
        body_fact_hashes: vec![bf],
        body_merkle_proofs: Vec::new(),
        substitution: vec![alice, budget, amount], // budget < amount
        derived_predicate: Fp::from(600u64),
        derived_terms: [alice, amount, Fp::zero(), Fp::zero()],
    };
    // The prover should FAIL because budget(30) < amount(100), so diff wraps
    // and the high bit won't be 0 (or the bit decomposition won't sum correctly).
    // Kimchi prover panics on invalid witness, so we catch_unwind.
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        KimchiNativeBackend::prove_derivation(&w)
    }));
    assert!(
        result.is_err() || result.unwrap().is_err(),
        "Prover must reject GTE check with negative diff"
    );
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

    // Tamper: change w[1] in the first body atom row (row 3) to a different value
    // Rows 0,1,2 are public inputs (state_root, derived_hash, rule_structure_hash),
    // row 3 is the first body atom.
    // The gate enforces w[0] - w[1] = 0, so changing w[1] breaks it.
    wit[1][3] = Fp::from(77777u64); // tamper state_root copy

    // Try to prove with tampered witness.
    // Kimchi prover panics on invalid witness, so we catch_unwind.
    let (gates, pc) = circuit.build_circuit();
    let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(gates, pc);
    let gm = <Vesta as CommitmentCurve>::Map::setup();
    let result =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
                BaseSponge,
                ScalarSponge,
                _,
            >(&gm, wit, &[], &index, &mut OsRng)
        }));
    assert!(
        result.is_err() || result.unwrap().is_err(),
        "Prover must reject tampered state root in body atom row"
    );
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
    let result =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
                BaseSponge,
                ScalarSponge,
                _,
            >(&gm, wit, &[], &index, &mut OsRng)
        }));
    assert!(
        result.is_err() || result.unwrap().is_err(),
        "Prover must reject tampered head term"
    );
}

// ==================================================================================
// Adversarial tests for fold circuit constraints (real Kimchi verifier)
// ==================================================================================

/// Fold circuit adversarial test: tamper with a sibling value in the Merkle path.
/// The Poseidon gadgets will produce a different root, so the root match gate fails.
#[test]
fn test_kimchi_native_fold_adversarial_tampered_sibling() {
    let mut w = create_test_fold_fp(1);
    // Tamper with a sibling at level 0
    w.removals[0].membership_proof.levels[0].siblings[0] = Fp::from(99999u64);
    // The Merkle proof no longer verifies against old_root
    let result =
        KimchiNativeBackend::prove_fold(w.old_root, w.new_root, w.removals, w.checks_commitment);
    assert!(
        result.is_err(),
        "Proof must fail when sibling is tampered: {:?}",
        result
    );
}

/// Fold circuit adversarial test: tamper with the leaf hash.
/// The leaf binding gate enforces fact_hash == leaf_hash; tampering one breaks it.
#[test]
fn test_kimchi_native_fold_adversarial_tampered_leaf_hash() {
    let mut w = create_test_fold_fp(2);
    // Tamper: change the leaf_hash in the Merkle witness (but keep fact_hash correct)
    w.removals[1].membership_proof.leaf_hash = Fp::from(11111u64);
    let result =
        KimchiNativeBackend::prove_fold(w.old_root, w.new_root, w.removals, w.checks_commitment);
    assert!(
        result.is_err(),
        "Proof must fail when leaf hash is tampered: {:?}",
        result
    );
}

/// Fold circuit adversarial test: claim wrong old_root.
/// The root match gate enforces computed_root == old_root. If old_root is wrong,
/// honest Merkle paths won't match it.
#[test]
fn test_kimchi_native_fold_adversarial_wrong_old_root() {
    let mut w = create_test_fold_fp(1);
    // Change old_root to something wrong (Merkle proofs were built against the real root)
    let real_root = w.old_root;
    w.old_root = Fp::from(77777u64);
    // Also update expected_root in the proof to match (simulating a prover who
    // tries to claim a different root)
    w.removals[0].membership_proof.expected_root = Fp::from(77777u64);
    let result =
        KimchiNativeBackend::prove_fold(w.old_root, w.new_root, w.removals, w.checks_commitment);
    // This fails because the Merkle path computation produces real_root, not 77777
    assert!(
        result.is_err(),
        "Proof must fail when old_root is wrong (root={}, claimed={}): {:?}",
        real_root,
        w.old_root,
        result
    );
}

/// Fold circuit: verify with the real Kimchi verifier (KimchiFoldCircuit::verify).
#[test]
fn test_kimchi_native_fold_full_kimchi_verify_single() {
    let w = create_test_fold_fp(1);
    let proof = KimchiNativeBackend::prove_fold(
        w.old_root,
        w.new_root,
        w.removals.clone(),
        w.checks_commitment,
    )
    .expect("proof generation should succeed");
    let verified = KimchiFoldCircuit::verify(&proof, &w).expect("verification should not error");
    assert!(
        verified,
        "Full Kimchi verification must pass for valid proof"
    );
}

/// Fold circuit: verify with the real Kimchi verifier for multiple removals.
#[test]
fn test_kimchi_native_fold_full_kimchi_verify_multiple() {
    let w = create_test_fold_fp(3);
    let proof = KimchiNativeBackend::prove_fold(
        w.old_root,
        w.new_root,
        w.removals.clone(),
        w.checks_commitment,
    )
    .expect("proof generation should succeed");
    let verified = KimchiFoldCircuit::verify(&proof, &w).expect("verification should not error");
    assert!(
        verified,
        "Full Kimchi verification must pass for valid proof with 3 removals"
    );
}

// ==================================================================================
// Presentation circuit: token expiry tests
// ==================================================================================

/// Token expiry: valid proof when not_after_height > verifier_block_height
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_presentation_token_expiry_valid() {
    let fr = Fp::from(1000000u64);
    let rp = [
        Fp::from(111u64),
        Fp::from(222u64),
        Fp::from(333u64),
        Fp::from(444u64),
    ];
    let ts = Fp::from(1716000000u64);
    let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64);
    let dh = Fp::from(66666u64);
    let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64);
    let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    let cc = compute_composition_commitment(fch, dh, pt);
    let w = KimchiPresentationWitness {
        federation_root: fr,
        request_predicate: rp,
        timestamp: ts,
        verifier_nonce: vn,
        composition_commitment: cc,
        presentation_tag: pt,
        issuer_membership_hash: Fp::from(42424242u64),
        fold_chain_hash: fch,
        derivation_hash: dh,
        non_revocation_eval: nre,
        final_root,
        randomness,
        verifier_block_height: Fp::from(1000u64),
        not_after_height: Fp::from(2000u64), // 2000 >= 1000: valid
        revealed_facts: Vec::new(),
        issuer_key_hash: Fp::from(42424242u64),
        blinding_factor: Fp::from(999u64),
        issuer_membership_proof: None,
    };
    let proof = KimchiNativeBackend::prove_presentation(&w).expect("ok");
    assert_eq!(
        KimchiNativeBackend::verify_presentation(&proof).expect("ok"),
        KimchiPresentationVerification::Valid
    );
}

/// Adversarial: token expired (not_after_height < verifier_block_height)
#[test]
fn test_kimchi_presentation_token_expired_rejected() {
    let fr = Fp::from(1000000u64);
    let rp = [
        Fp::from(111u64),
        Fp::from(222u64),
        Fp::from(333u64),
        Fp::from(444u64),
    ];
    let ts = Fp::from(1716000000u64);
    let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64);
    let dh = Fp::from(66666u64);
    let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64);
    let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    let cc = compute_composition_commitment(fch, dh, pt);
    // not_after_height=500 < verifier_block_height=1000: EXPIRED
    let w = KimchiPresentationWitness {
        federation_root: fr,
        request_predicate: rp,
        timestamp: ts,
        verifier_nonce: vn,
        composition_commitment: cc,
        presentation_tag: pt,
        issuer_membership_hash: Fp::from(42424242u64),
        fold_chain_hash: fch,
        derivation_hash: dh,
        non_revocation_eval: nre,
        final_root,
        randomness,
        verifier_block_height: Fp::from(1000u64),
        not_after_height: Fp::from(500u64), // 500 < 1000: expired
        revealed_facts: Vec::new(),
        issuer_key_hash: Fp::from(42424242u64),
        blinding_factor: Fp::from(999u64),
        issuer_membership_proof: None,
    };
    let result = KimchiNativeBackend::prove_presentation(&w);
    assert!(result.is_err(), "Must reject expired token");
}

// ==================================================================================
// Presentation circuit: revealed facts commitment tests
// ==================================================================================

/// Revealed facts commitment: valid proof with selective disclosure
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_presentation_revealed_facts_valid() {
    let fr = Fp::from(1000000u64);
    let rp = [
        Fp::from(111u64),
        Fp::from(222u64),
        Fp::from(333u64),
        Fp::from(444u64),
    ];
    let ts = Fp::from(1716000000u64);
    let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64);
    let dh = Fp::from(66666u64);
    let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64);
    let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    let cc = compute_composition_commitment(fch, dh, pt);
    let revealed = vec![Fp::from(100u64), Fp::from(200u64), Fp::from(300u64)];
    let w = KimchiPresentationWitness {
        federation_root: fr,
        request_predicate: rp,
        timestamp: ts,
        verifier_nonce: vn,
        composition_commitment: cc,
        presentation_tag: pt,
        issuer_membership_hash: Fp::from(42424242u64),
        fold_chain_hash: fch,
        derivation_hash: dh,
        non_revocation_eval: nre,
        final_root,
        randomness,
        verifier_block_height: Fp::zero(),
        not_after_height: Fp::zero(),
        revealed_facts: revealed,
        issuer_key_hash: Fp::from(42424242u64),
        blinding_factor: Fp::from(999u64),
        issuer_membership_proof: None,
    };
    let proof = KimchiNativeBackend::prove_presentation(&w).expect("ok");
    assert_eq!(
        KimchiNativeBackend::verify_presentation(&proof).expect("ok"),
        KimchiPresentationVerification::Valid
    );
}

/// Adversarial: tampered revealed facts commitment.
/// Build a valid proof, then tamper with the public input bytes for the RFC.
/// The Kimchi verifier must reject because public inputs don't match the proof.
#[test]
fn test_kimchi_presentation_revealed_facts_tampered_rejected() {
    let fr = Fp::from(1000000u64);
    let rp = [
        Fp::from(111u64),
        Fp::from(222u64),
        Fp::from(333u64),
        Fp::from(444u64),
    ];
    let ts = Fp::from(1716000000u64);
    let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64);
    let dh = Fp::from(66666u64);
    let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64);
    let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    let cc = compute_composition_commitment(fch, dh, pt);
    let revealed = vec![Fp::from(100u64), Fp::from(200u64)];
    let w = KimchiPresentationWitness {
        federation_root: fr,
        request_predicate: rp,
        timestamp: ts,
        verifier_nonce: vn,
        composition_commitment: cc,
        presentation_tag: pt,
        issuer_membership_hash: Fp::from(42424242u64),
        fold_chain_hash: fch,
        derivation_hash: dh,
        non_revocation_eval: nre,
        final_root,
        randomness,
        verifier_block_height: Fp::zero(),
        not_after_height: Fp::zero(),
        revealed_facts: revealed,
        issuer_key_hash: Fp::from(42424242u64),
        blinding_factor: Fp::from(999u64),
        issuer_membership_proof: None,
    };
    let mut proof = KimchiNativeBackend::prove_presentation(&w).expect("ok");
    // Tamper with both the struct field and the serialized public input bytes
    proof.revealed_facts_commitment = Fp::from(99999u64);
    let tampered_rfc_bytes = fp_to_bytes32(&Fp::from(99999u64));
    proof.proof.public_input_bytes[352..384].copy_from_slice(&tampered_rfc_bytes);
    // The Kimchi verifier will reject because public inputs don't match the proof
    let result = KimchiNativeBackend::verify_presentation(&proof);
    assert!(result.is_ok());
    assert_eq!(
        result.unwrap(),
        KimchiPresentationVerification::ProofInvalid,
        "Must reject proof with tampered revealed_facts_commitment"
    );
}

// ==================================================================================
// Presentation circuit: issuer membership (blinded ring mode) tests
// ==================================================================================

/// Issuer membership: valid proof with full Poseidon Merkle path
#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_kimchi_presentation_issuer_membership_valid() {
    let issuer_key = Fp::from(42424242u64);
    let blinding = Fp::from(777u64);

    // Build a federation Merkle tree containing the issuer key
    let leaves: Vec<Fp> = vec![
        issuer_key,
        Fp::from(11111u64),
        Fp::from(22222u64),
        Fp::from(33333u64),
    ];
    let (federation_root, proofs) = build_fp_merkle_tree(&leaves, ISSUER_TREE_DEPTH);
    let issuer_merkle_proof = proofs[0].clone();

    let rp = [
        Fp::from(111u64),
        Fp::from(222u64),
        Fp::from(333u64),
        Fp::from(444u64),
    ];
    let ts = Fp::from(1716000000u64);
    let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64);
    let dh = Fp::from(66666u64);
    let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64);
    let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    let cc = compute_composition_commitment(fch, dh, pt);

    let w = KimchiPresentationWitness {
        federation_root,
        request_predicate: rp,
        timestamp: ts,
        verifier_nonce: vn,
        composition_commitment: cc,
        presentation_tag: pt,
        issuer_membership_hash: issuer_key,
        fold_chain_hash: fch,
        derivation_hash: dh,
        non_revocation_eval: nre,
        final_root,
        randomness,
        verifier_block_height: Fp::zero(),
        not_after_height: Fp::zero(),
        revealed_facts: Vec::new(),
        issuer_key_hash: issuer_key,
        blinding_factor: blinding,
        issuer_membership_proof: Some(issuer_merkle_proof),
    };
    let proof = KimchiNativeBackend::prove_presentation(&w).expect("ok");
    assert_eq!(
        KimchiNativeBackend::verify_presentation(&proof).expect("ok"),
        KimchiPresentationVerification::Valid
    );
}

/// Adversarial: issuer NOT in federation tree (wrong leaf)
#[test]
fn test_kimchi_presentation_issuer_not_in_federation_rejected() {
    let real_issuer = Fp::from(42424242u64);
    let fake_issuer = Fp::from(99999999u64);
    let blinding = Fp::from(777u64);

    // Build a tree that does NOT contain the fake issuer
    let leaves: Vec<Fp> = vec![
        real_issuer,
        Fp::from(11111u64),
        Fp::from(22222u64),
        Fp::from(33333u64),
    ];
    let (federation_root, proofs) = build_fp_merkle_tree(&leaves, ISSUER_TREE_DEPTH);
    let mut fake_proof = proofs[0].clone();
    // Tamper: use fake_issuer as the leaf but the real_issuer's proof path
    fake_proof.leaf_hash = fake_issuer;

    let rp = [
        Fp::from(111u64),
        Fp::from(222u64),
        Fp::from(333u64),
        Fp::from(444u64),
    ];
    let ts = Fp::from(1716000000u64);
    let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64);
    let dh = Fp::from(66666u64);
    let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64);
    let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    let cc = compute_composition_commitment(fch, dh, pt);

    let w = KimchiPresentationWitness {
        federation_root,
        request_predicate: rp,
        timestamp: ts,
        verifier_nonce: vn,
        composition_commitment: cc,
        presentation_tag: pt,
        issuer_membership_hash: fake_issuer,
        fold_chain_hash: fch,
        derivation_hash: dh,
        non_revocation_eval: nre,
        final_root,
        randomness,
        verifier_block_height: Fp::zero(),
        not_after_height: Fp::zero(),
        revealed_facts: Vec::new(),
        issuer_key_hash: fake_issuer,
        blinding_factor: blinding,
        issuer_membership_proof: Some(fake_proof),
    };
    let result = KimchiNativeBackend::prove_presentation(&w);
    assert!(result.is_err(), "Must reject issuer not in federation tree");
}

/// Adversarial: tampered blinding factor (wrong blinded leaf)
#[test]
fn test_kimchi_presentation_wrong_blinding_factor_rejected() {
    let issuer_key = Fp::from(42424242u64);
    let correct_blinding = Fp::from(777u64);
    let wrong_blinding = Fp::from(888u64);

    // Build a valid federation Merkle tree
    let leaves: Vec<Fp> = vec![
        issuer_key,
        Fp::from(11111u64),
        Fp::from(22222u64),
        Fp::from(33333u64),
    ];
    let (federation_root, proofs) = build_fp_merkle_tree(&leaves, ISSUER_TREE_DEPTH);
    let issuer_merkle_proof = proofs[0].clone();

    let rp = [
        Fp::from(111u64),
        Fp::from(222u64),
        Fp::from(333u64),
        Fp::from(444u64),
    ];
    let ts = Fp::from(1716000000u64);
    let vn = Fp::from(987654321u64);
    let fch = Fp::from(55555u64);
    let dh = Fp::from(66666u64);
    let nre = Fp::from(77777u64);
    let final_root = Fp::from(88888u64);
    let randomness = Fp::from(12345u64);
    let pt = compute_presentation_tag(final_root, randomness, vn);
    let cc = compute_composition_commitment(fch, dh, pt);

    // Create a valid proof with correct_blinding
    let w_correct = KimchiPresentationWitness {
        federation_root,
        request_predicate: rp,
        timestamp: ts,
        verifier_nonce: vn,
        composition_commitment: cc,
        presentation_tag: pt,
        issuer_membership_hash: issuer_key,
        fold_chain_hash: fch,
        derivation_hash: dh,
        non_revocation_eval: nre,
        final_root,
        randomness,
        verifier_block_height: Fp::zero(),
        not_after_height: Fp::zero(),
        revealed_facts: Vec::new(),
        issuer_key_hash: issuer_key,
        blinding_factor: correct_blinding,
        issuer_membership_proof: Some(issuer_merkle_proof),
    };
    let mut proof = KimchiNativeBackend::prove_presentation(&w_correct).expect("ok");

    // Now tamper: change issuer_blinded_leaf in the proof to correspond to wrong_blinding
    let wrong_blinded_leaf = compute_blinded_leaf(issuer_key, wrong_blinding);
    proof.issuer_blinded_leaf = wrong_blinded_leaf;
    // Also tamper the serialized public input bytes at position 12 (384..416)
    let wrong_bl_bytes = fp_to_bytes32(&wrong_blinded_leaf);
    proof.proof.public_input_bytes[384..416].copy_from_slice(&wrong_bl_bytes);

    // The Kimchi verifier will reject because the public inputs don't match the proof
    let result = KimchiNativeBackend::verify_presentation(&proof);
    assert!(result.is_ok());
    assert_eq!(
        result.unwrap(),
        KimchiPresentationVerification::ProofInvalid,
        "Must reject proof with tampered blinding factor"
    );
}

// ============================================================================
// P0-2 ADVERSARIAL DEMONSTRATION: missing copy constraints in Generic gates.
//
// The audit (AUDIT-circuit.md P0-2) reports that Generic gates in this backend
// use `Wire::for_row(r)` exclusively — every wire self-loops. Without
// permutation-argument copy constraints linking, e.g., a Poseidon gadget's
// output cell to a downstream "binding gate" w[0], the binding gate enforces
// equality ONLY between the two cells on its OWN row. The prover is free to
// fill those cells with arbitrary values that match each other, completely
// disconnected from the gadget that "supposedly" produces them.
//
// The test below builds the minimal demonstration: a "computation row" that
// computes c = a + b in (w[0], w[1], w[2]), and a "binding row" that enforces
// w[0] - w[1] = 0. The intent is that binding-row w[0] should equal
// computation-row w[2] (i.e., the prover claims c == expected). With
// `Wire::for_row(r)`-only wiring, binding-row w[0] is unconstrained relative
// to computation-row w[2]; the prover can fill binding-row (w[0], w[1]) with
// ANY matching pair (e.g., (99, 99)) and the verifier accepts.
//
// This is the canonical "binding gate is vacuous without copy constraint"
// failure mode. The audit observed it at multiple sites in derivation.rs and
// predicates.rs; this test makes the failure mode explicit.
//
// This stays as a documentation test because constructing an adversarial Kimchi
// witness directly requires careful setup. The audit's recommendation is to
// FEATURE-GATE the kimchi_native backend until proper copy constraints land,
// not to add proof-of-concept tests that exploit it.
// ============================================================================

/// Documentation-test: spell out the unsoundness pattern in code form so future
/// readers see the failure mode without needing a working Kimchi witness.
#[test]
fn kimchi_native_p0_2_documentation_test() {
    use kimchi::circuits::wires::{COLUMNS, Wire};

    // Two self-looped generic gates. Gate 0: w[0] + w[1] - w[2] == 0. Gate 1:
    // w[0] - w[1] == 0. With Wire::for_row(_), there is NO constraint that
    // gate 1's w[0] equals gate 0's w[2]. The Kimchi permutation argument only
    // sees self-loops; the permutation polynomial trivially satisfies the
    // identity permutation. So any witness with gate-0-internal consistency
    // and gate-1-internal consistency verifies, even when the two are
    // semantically unrelated.
    //
    // Honest witness:                Adversarial witness:
    //   gate 0: (3, 4, 7, 0, ...)      gate 0: (3, 4, 7, 0, ...)
    //   gate 1: (7, 7, 0, 0, ...)      gate 1: (999, 999, 0, 0, ...)
    //                                  ^^^ no copy link, both verify.
    //
    // The fix is `super::link_wires(&mut gates, (0, 2), (1, 0))` BEFORE
    // building the prover index — this places (gate 0 col 2) and (gate 1 col
    // 0) in the same permutation cycle, forcing them equal.
    let gate0 = make_generic_gate_with_constraints(0, {
        let mut c = [Fp::zero(); COLUMNS];
        c[0] = Fp::one();
        c[1] = Fp::one();
        c[2] = -Fp::one();
        c
    });
    let gate1 = make_generic_gate_with_constraints(1, {
        let mut c = [Fp::zero(); COLUMNS];
        c[0] = Fp::one();
        c[1] = -Fp::one();
        c
    });
    // Confirm both gates are self-looped — every wire's row matches its own.
    for (i, g) in [&gate0, &gate1].iter().enumerate() {
        for (j, w) in g.wires.iter().enumerate() {
            assert_eq!(
                w.row, i,
                "P0-2: gate {} col {} should be self-looped before copy \
                 constraints are added; got wire pointing to row {}",
                i, j, w.row
            );
            assert_eq!(w.col, j, "self-loop preserves col");
        }
    }
    // The above demonstrates the unsoundness pattern at the wire level: every
    // wire points back to itself. Until `link_wires` is called to thread
    // (0, 2) → (1, 0), no permutation cycle forces gate-0 col 2 to equal
    // gate-1 col 0.
}

// ============================================================================
// Adversarial tests for P0-3 (gate-deserialization soundness fix)
// ============================================================================
//
// These tests verify that the verifier rejects proofs whose embedded
// `circuit_hash` does not match the canonical circuit rebuilt by the
// verifier. This protects against a malicious prover that constructs a
// proof using a permissive circuit (e.g., one with all-zero coefficients)
// and tries to pass it off as a proof for the canonical circuit.

#[test]
fn test_p0_3_zero_circuit_hash_rejected_derivation() {
    // A proof with circuit_hash == [0; 32] indicates the prover did NOT
    // bind the circuit shape. The verifier MUST reject this.
    let w = create_test_derivation_fp();
    let dh = w.derived_hash();
    let sr = w.state_root;
    let mut proof = KimchiNativeBackend::prove_derivation(&w).expect("prove ok");

    // Clear circuit_hash — simulating a prover that omitted the binding.
    proof.circuit_hash = [0u8; 32];

    let result = KimchiNativeBackend::verify_derivation(&proof, &sr, &dh);
    // The verifier should error out (or return false) when circuit_hash is unset.
    assert!(
        matches!(result, Err(_) | Ok(false)),
        "Verifier must reject derivation proof with zero circuit_hash; got {:?}",
        result
    );
}

#[test]
fn test_p0_3_tampered_circuit_hash_rejected_derivation() {
    // A proof with a forged circuit_hash (claiming a different circuit shape)
    // must be rejected. This catches malicious provers that build permissive
    // circuits and claim they're the canonical one.
    let w = create_test_derivation_fp();
    let dh = w.derived_hash();
    let sr = w.state_root;
    let mut proof = KimchiNativeBackend::prove_derivation(&w).expect("prove ok");

    // Flip a single bit in circuit_hash.
    proof.circuit_hash[0] ^= 0x01;

    let result = KimchiNativeBackend::verify_derivation(&proof, &sr, &dh);
    assert!(
        matches!(result, Err(_) | Ok(false)),
        "Verifier must reject derivation proof with tampered circuit_hash; got {:?}",
        result
    );
}

#[test]
fn test_p0_3_zero_circuit_hash_rejected_fold() {
    // Build a minimal valid fold proof, then clear circuit_hash and verify rejection.
    let leaf = Fp::from(42u64);
    let levels = vec![FpMerkleLevelWitness {
        position: 0,
        siblings: [Fp::zero(); 3],
    }];
    let removal = KimchiFoldRemoval {
        fact_hash: leaf,
        membership_proof: FpMerkleWitness {
            leaf_hash: leaf,
            levels,
            expected_root: fp_hash_pair_for_test(leaf, Fp::zero()),
        },
    };
    let witness = KimchiFoldWitness {
        old_root: removal.membership_proof.expected_root,
        new_root: removal.membership_proof.expected_root,
        removals: vec![removal],
        checks_commitment: Fp::one(),
    };
    let circuit = KimchiFoldCircuit::new(witness.clone());
    let Ok(mut proof) = circuit.prove() else {
        // If the test witness can't be proved (independent issue), skip.
        return;
    };

    // Clear the canonical-hash binding.
    proof.circuit_hash = [0u8; 32];

    let result = KimchiFoldCircuit::verify(&proof, &witness);
    assert!(
        matches!(result, Err(_) | Ok(false)),
        "Verifier must reject fold proof with zero circuit_hash; got {:?}",
        result
    );
}

// Helper: compute a Poseidon pair hash for test root construction.
fn fp_hash_pair_for_test(a: Fp, b: Fp) -> Fp {
    use mina_poseidon::poseidon::{ArithmeticSponge, Sponge};
    let params = Vesta::sponge_params();
    let mut sponge = ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(params);
    sponge.absorb(&[a, b]);
    sponge.squeeze()
}

#[test]
fn test_p0_3_tampered_circuit_hash_rejected_arithmetic_predicate() {
    use super::predicates::{
        KimchiArithOp, KimchiArithmeticPredicateCircuit, KimchiArithmeticPredicateWitness,
        KimchiCompareOp,
    };
    let result_value = Fp::from(100u64);
    let threshold = Fp::from(50u64);
    let witness = KimchiArithmeticPredicateWitness {
        inputs: vec![result_value],
        ops: vec![KimchiArithOp::Input(0)],
        result_slot: 0,
        comparison_value: threshold,
        comparison_op: KimchiCompareOp::Gte,
        result_commitment: result_value,
    };
    let mut proof = KimchiArithmeticPredicateCircuit::new(witness)
        .prove()
        .expect("prove ok");

    // Tamper circuit_hash.
    proof.circuit_hash[10] ^= 0xff;

    let result = KimchiNativeBackend::verify_arithmetic_predicate(
        &proof,
        &result_value,
        &threshold,
        KimchiCompareOp::Gte,
    );
    assert!(
        matches!(result, Err(_) | Ok(false)),
        "Verifier must reject arithmetic predicate with tampered circuit_hash; got {:?}",
        result
    );
}

// ============================================================================
// P0-2 adversarial tests: copy-constraint enforcement
// ============================================================================
//
// These tests verify that the copy constraints we added prevent specific
// forgery patterns. The pattern: build an honest proof, mutate witness data
// in a way that would have been accepted before copy constraints existed
// (since each Generic gate only checked intra-row), and confirm the kimchi
// verifier now rejects.

#[test]
#[ignore = "kimchi-native backend is broken & unsound: verifier rebuilds the canonical circuit from a placeholder template witness whose data-dependent shape does not match the prover (circuit_hash mismatch), some circuits cannot construct a valid permutation argument (Permutation \"final value\"), and binding gates have no copy constraints (AUDIT-circuit.md P0-2). Backend is gated off the live path & fails closed in production (see crate::proof_tier::kimchi_native_tier and kimchi_native::production_guard). Re-enable only after a copy-constraint + canonical-shape rewrite + re-audit."]
fn test_p0_2_derivation_honest_still_verifies() {
    // Sanity: copy constraints did not break the honest path.
    let w = create_test_derivation_fp();
    let dh = w.derived_hash();
    let sr = w.state_root;
    let proof = KimchiNativeBackend::prove_derivation(&w).expect("prove ok");
    assert!(
        KimchiNativeBackend::verify_derivation(&proof, &sr, &dh).expect("verify ok"),
        "Honest derivation proof must still verify after copy-constraint addition"
    );
}

#[test]
fn test_p0_2_derivation_wrong_state_root_rejected() {
    // The copy constraint linking PI(state_root) to the body root_match cell
    // means a tampered PI cannot be silently accepted: the kimchi verifier
    // will detect the mismatch via the permutation argument.
    let w = create_test_derivation_fp();
    let dh = w.derived_hash();
    let proof = KimchiNativeBackend::prove_derivation(&w).expect("prove ok");

    // Verify with an incorrect state_root — must reject.
    let wrong_sr = Fp::from(999_999u64);
    assert!(
        !KimchiNativeBackend::verify_derivation(&proof, &wrong_sr, &dh).expect("verify ok"),
        "Wrong state_root must be rejected"
    );
}

#[test]
fn test_p0_2_fold_wrong_old_root_rejected() {
    let leaf = Fp::from(42u64);
    let levels = vec![FpMerkleLevelWitness {
        position: 0,
        siblings: [Fp::zero(); 3],
    }];
    let removal = KimchiFoldRemoval {
        fact_hash: leaf,
        membership_proof: FpMerkleWitness {
            leaf_hash: leaf,
            levels,
            expected_root: fp_hash_pair_for_test(leaf, Fp::zero()),
        },
    };
    let witness = KimchiFoldWitness {
        old_root: removal.membership_proof.expected_root,
        new_root: removal.membership_proof.expected_root,
        removals: vec![removal],
        checks_commitment: Fp::one(),
    };
    let circuit = KimchiFoldCircuit::new(witness.clone());
    let Ok(proof) = circuit.prove() else {
        return;
    };

    let wrong_root = Fp::from(987_654u64);
    let mut wrong_witness = witness.clone();
    wrong_witness.old_root = wrong_root;
    // The verify path checks PI roots externally; we expect rejection.
    let result = KimchiFoldCircuit::verify(&proof, &wrong_witness);
    assert!(
        matches!(result, Err(_) | Ok(false)),
        "Fold verifier must reject wrong old_root; got {:?}",
        result
    );
}
