//! # THE DEPLOYED CUSTOM-BINDING LIGHT-CLIENT TOOTH.
//!
//! This is the integration tooth for the deployed custom-effect fold-wire (the close of the one
//! REAL deployed light-client vacuity). It builds a REAL 2-turn chain whose FIRST turn is an
//! `Effect::Custom` turn carrying a `customVmDescriptor2R24` wide leg (publishing its claimed
//! `custom_proof_commitment` at IR2 PI 46..49) PLUS the prover-side `CustomWitnessBundle` (the
//! re-provable `CellProgram` + trace witness + PIs), folds it through the DEPLOYED chain prover
//! (`prove_turn_chain_recursive` → `prove_chain_core_rotated`), and verifies the whole-chain
//! artifact through the light-client verifier (`verify_turn_chain_recursive`).
//!
//! The deployed wire mints, for the custom turn, a DUAL-EXPOSE leaf (segment ++ the claimed
//! commitment, `ivc_turn_chain::prove_descriptor_leaf_dual_expose`) and folds it against the
//! RE-PROVEN custom sub-proof leaf (`custom_leaf_adapter::prove_custom_leaf_with_commitment`) under
//! the segment-preserving binding node (`joint_turn_recursive::prove_custom_binding_node_segmented`)
//! — the binding `connect`s the leg's claimed commitment to the sub-proof's GENUINE in-circuit
//! commitment INSIDE the recursion tree a pure light client folds.
//!
//! THE TWO POLES:
//!   * HONEST — the leg's claimed commitment EQUALS `custom_proof_pi_commitment(bundle.pis)`: the
//!     chain folds and the light client ACCEPTS.
//!   * FORGED — the leg claims a commitment NO verifying sub-proof of the bundle's PIs backs: the
//!     in-circuit `connect` is a conflict ⇒ the aggregate is UNSAT ⇒ no root ⇒ the light client
//!     never receives a verifying artifact (REJECTED).
//!
//! This makes the premise of Lean `CustomBindingFromFold.custom_binding_from_fold` TRUE on the
//! DEPLOYED path. The fold is a real recursion (minutes), so both poles are `#[ignore]`. Run with:
//!   cargo test -p dregg-circuit-prove --test custom_binding_deployed_tooth -- --ignored --nocapture

use std::collections::HashMap;

use dregg_cell::Ledger;
use dregg_circuit::descriptor_ir2::UMemBoundaryWitness;
use dregg_circuit::descriptor_ir2::prove_vm_descriptor2_for_config;
use dregg_circuit::dsl::circuit::{
    CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest,
    generate_rotated_effect_vm_descriptor_and_trace_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive, verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    CustomWitnessBundle, DescriptorParticipant, RotatedParticipantLeg,
};
use dregg_turn::rotation_witness as rw;

// ============================================================================
// Fixtures
// ============================================================================

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// The actor cell at `(balance, nonce)` with open permissions.
fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// The minimal-but-REAL custom program the custom-leaf adapter tests use: one boolean column
/// (`dir`) + one conservation polynomial (`new − old − amt + 2·dir·amt == 0`).
fn demo_program() -> CellProgram {
    let p_minus_1 = BabyBear::new(BABYBEAR_P - 1);
    let descriptor = CircuitDescriptor {
        name: "dregg-custom-demo-v1".to_string(),
        trace_width: 4,
        max_degree: 2,
        columns: vec![
            ColumnDef {
                name: "old".into(),
                index: 0,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "amt".into(),
                index: 1,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "new".into(),
                index: 2,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "dir".into(),
                index: 3,
                kind: ColumnKind::Binary,
            },
        ],
        constraints: vec![
            ConstraintExpr::Binary { col: 3 },
            ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![2],
                    },
                    PolyTerm {
                        coeff: p_minus_1,
                        col_indices: vec![0],
                    },
                    PolyTerm {
                        coeff: p_minus_1,
                        col_indices: vec![1],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(2),
                        col_indices: vec![3, 1],
                    },
                ],
            },
        ],
        boundaries: vec![],
        public_input_count: 2,
        lookup_tables: vec![],
    };
    CellProgram::new(descriptor, 1)
}

/// Honest witness for a credit (dir=0): new = old + amt, constant across rows.
fn honest_witness() -> (HashMap<String, Vec<BabyBear>>, usize) {
    let rows = 4;
    let mut w = HashMap::new();
    w.insert("old".into(), vec![BabyBear::new(10); rows]);
    w.insert("amt".into(), vec![BabyBear::new(5); rows]);
    w.insert("new".into(), vec![BabyBear::new(15); rows]);
    w.insert("dir".into(), vec![BabyBear::ZERO; rows]);
    (w, rows)
}

/// The custom program's public inputs (the commitment preimage).
fn custom_pis() -> Vec<BabyBear> {
    vec![BabyBear::new(10), BabyBear::new(15)]
}

/// Mint a REAL `customVmDescriptor2R24` wide leg whose claimed `custom_proof_commitment` (IR2 PI
/// 46..49) is `commit`. Custom bumps nonce by 1, balance unchanged: `before=(b,nonce)`,
/// `after=(b,nonce+1)`. Optionally attach the prover-side `bundle` (the deployed custom-binding
/// thread the chain prover reads).
fn mint_custom_leg(
    balance: i64,
    nonce: u64,
    commit: [BabyBear; 4],
    bundle: Option<CustomWitnessBundle>,
) -> RotatedParticipantLeg {
    let st = CellState::new(balance as u64, nonce as u32);
    let effects = vec![Effect::Custom {
        program_vk_hash: [BabyBear::new(9); 8],
        proof_commitment: commit,
    }];
    let before_cell = producer_cell(balance, nonce);
    let after_cell = producer_cell(balance, nonce + 1);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = bridge(&rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
    ));
    let after_w = bridge(&rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
    ));

    let (desc, trace, dpis, map_heaps, mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &before_w,
        &after_w,
        &empty_caveat_manifest(),
        None,
        None,
        None,
    )
    .expect("custom wide dispatch");
    assert!(
        dpis.len() >= 50,
        "custom leg PI vector must carry the commitment slice at 46..49 (got {})",
        dpis.len()
    );
    // The leg PUBLISHES the claimed commitment at PI 46..49 (== the effect's proof_commitment).
    assert_eq!(
        &dpis[46..50],
        &commit[..],
        "custom leg must publish the claimed commitment at PI 46..49"
    );

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &mb,
        &map_heaps,
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("custom wide leg proves under the leaf-wrap config");

    let leg = RotatedParticipantLeg {
        proof,
        descriptor: desc,
        public_inputs: dpis,
        custom_witness: None,
        bridge_witness: None,
    };
    match bundle {
        Some(b) => leg.with_custom_witness(b),
        None => leg,
    }
}

/// A trailing custom turn (no witness bundle — a plain custom leg) starting at `(b, nonce)`, so the
/// chain has >= 2 turns and the first custom turn's `new_root` links to this one's `old_root`.
fn plain_custom_turn(balance: i64, nonce: u64) -> FinalizedTurn {
    // A plain (non-bundled) custom leg still publishes a commitment; it does NOT exercise the
    // binding wire (no witness), so the chain prover takes the ordinary segment-leaf path for it.
    let commit = [
        BabyBear::new(1),
        BabyBear::new(2),
        BabyBear::new(3),
        BabyBear::new(4),
    ];
    let leg = mint_custom_leg(balance, nonce, commit, None);
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

fn honest_bundle() -> CustomWitnessBundle {
    let (w, rows) = honest_witness();
    CustomWitnessBundle {
        program: demo_program(),
        witness_values: w,
        num_rows: rows,
        public_inputs: custom_pis(),
    }
}

/// Build the 2-turn chain. Turn 0 is the bundled custom turn whose claimed commitment is `commit`;
/// turn 1 is a plain custom turn linking off turn 0's post-state `(b, nonce+1)`.
fn build_chain(commit: [BabyBear; 4]) -> Vec<FinalizedTurn> {
    let balance = 1000i64;
    let t0_leg = mint_custom_leg(balance, 0, commit, Some(honest_bundle()));
    let t0 = FinalizedTurn::new(DescriptorParticipant::rotated(t0_leg));
    let t1 = plain_custom_turn(balance, 1);
    // Continuity sanity (host check also enforces this; assert early for a clear failure).
    assert_eq!(
        t0.new_root(),
        t1.old_root(),
        "custom turn 0's post-state must link to turn 1's pre-state"
    );
    vec![t0, t1]
}

// ============================================================================
// THE TEETH
// ============================================================================

/// POSITIVE POLE — an honest custom turn (claimed commitment == the genuine sub-proof commitment)
/// folds through the DEPLOYED chain prover and the LIGHT CLIENT ACCEPTS. The custom binding is now
/// witnessed by a pure light client folding the recursion tree.
#[test]
#[ignore = "SLOW: real deployed custom-binding recursion fold (~minutes); run with --ignored"]
fn deployed_custom_turn_honest_accepts() {
    let real = custom_proof_pi_commitment(&custom_pis());
    let turns = build_chain(real);

    let whole = prove_turn_chain_recursive(&turns)
        .expect("the honest custom-bearing chain must fold through the deployed prover");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the light client must ACCEPT the honest custom-bound whole-chain artifact");
    eprintln!(
        "DEPLOYED custom binding: honest custom turn FOLDED + light-client VERIFIED (commitment \
         bound in the recursion tree)."
    );
}

/// THE TOOTH — a FORGED custom turn: the leg claims a `custom_proof_commitment` no verifying
/// sub-proof of the bundle's PIs backs. The segmented binding node's in-circuit `connect` to the
/// genuine commitment is a conflict ⇒ the aggregate is UNSAT ⇒ no root. The light client never
/// receives a verifying artifact (REJECTED). This is the deployed bite that makes the binding REAL.
#[test]
#[ignore = "SLOW: real deployed custom-binding recursion fold (~minutes); run with --ignored"]
fn deployed_custom_turn_forged_rejected() {
    let real = custom_proof_pi_commitment(&custom_pis());
    // A claim NO verifying sub-proof of `custom_pis()` backs (lane 0 perturbed by +1 mod p). The
    // bundle attached in `build_chain` still proves the HONEST PIs, so the genuine in-circuit
    // commitment is `real` ≠ `forged` — the binding `connect` conflicts.
    let mut forged = real;
    forged[0] = BabyBear::new((real[0].0 + 1) % BABYBEAR_P);
    assert_ne!(forged, real);

    let turns = build_chain(forged);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_turn_chain_recursive(&turns)
    }));
    match result {
        // The in-circuit `connect` conflict panicked the constraint/witness builder — rejected.
        Err(_) => {}
        // Or the chain prover returned an error — rejected.
        Ok(Err(_)) => {}
        Ok(Ok(_)) => panic!(
            "a FORGED custom_proof_commitment folded into a verifying deployed whole-chain artifact \
             — the deployed binding is OPEN"
        ),
    }
    eprintln!(
        "DEPLOYED custom binding: forged custom commitment REJECTED by the deployed fold (no root)."
    );
}
