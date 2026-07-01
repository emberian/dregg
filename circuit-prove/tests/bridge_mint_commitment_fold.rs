//! # THE COMPACT BRIDGE-MINT PAYMENT-BINDING FOLD MECHANISM (Design M — mint_hash commitment).
//!
//! The bridge-mint twin of the custom fold-wire teeth (`custom_fold_wire_tests`), for the COMPACT
//! payment claim the gated `decoBridgeMintVmDescriptor` publishes: `[mint_hash, value]` at PI[42..44]
//! (Lean `EffectVmEmitBridgeMintDeco`, `PI_PAYMENT_COMMIT`/`PI_PAYMENT_VALUE`). This is the fold that
//! matches what the substrate `BridgeMint` row actually carries — `mint_hash` binds
//! `(nullifier, root, dest_federation, asset_type)`, `value_lo` the amount — NOT the 26-felt
//! full-fidelity tuple (that path needs a widened trace).
//!
//! Two stand-in claim leaves — each a real IR-v2 leaf publishing `[mint_hash, value]` at its PI slots
//! and re-exposing them as an `expose_claim` — are folded through `prove_bridge_mint_commitment_node`,
//! which `connect`s the two claims lane-by-lane. The LEG leaf publishes at the gated descriptor's real
//! slots PI[42..44]; the SUB-PROOF leaf carries the genuine payment claim.
//!
//! * HONEST — both leaves attest the SAME `[mint_hash, value]`: the per-lane `connect` is consistent,
//!   the node folds, the bound claim is re-exposed. A light client folding the tree witnesses that the
//!   mint's published payment commitment is backed.
//! * FORGED — the LEG claims a DIFFERENT `mint_hash` than the sub-proof backs: the per-lane `connect`
//!   is a conflict ⇒ the aggregation is UNSAT ⇒ no node proof. A mint cannot publish a payment
//!   commitment no verifying sub-proof backs.
//!
//! This is the direct analog of `custom_fold_wire_tests` / `bridge_binding_mechanism.rs` (both use
//! stand-in leaves for the MECHANISM tooth). The gated descriptor (`bridgemint-deco-v1`) is the real
//! leg-side emit this fold consumes; the deployed production wiring (the leg re-exposing PI[42..44] +
//! the minter attaching the payment sub-proof) is the deployment cutover.
//!
//! Real recursion (minutes), so both poles are `#[ignore]`. Run with:
//!   cargo test -p dregg-circuit-prove --test bridge_mint_commitment_fold -- --ignored --nocapture

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, VmConstraint2,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit_prove::ivc_turn_chain::{
    ir2_leaf_wrap_config, prove_descriptor_leaf_with_pi_slice_expose,
};
use dregg_circuit_prove::joint_turn_recursive::{
    BRIDGE_MINT_CLAIM_LEN, BRIDGE_MINT_CLAIM_PI_LO, prove_bridge_mint_commitment_node,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::DreggRecursionConfig;
use p3_recursion::RecursionOutput;

/// A stand-in claim leaf: a real IR-v2 leaf that PUBLISHES `claim = [mint_hash, value]` at PI slots
/// `[pi_lo .. pi_lo + BRIDGE_MINT_CLAIM_LEN)` (via `PiBinding{First}` pins over a trivial trace) and
/// re-exposes them as an `expose_claim`. A minimal stand-in for the gated bridge-mint leg / the payment
/// sub-proof at the SAME exposure surface — exactly the shape `custom_fold_wire_tests::effectvm_leg_leaf`
/// uses for the custom commitment.
fn claim_leaf(
    claim: [BabyBear; BRIDGE_MINT_CLAIM_LEN],
    pi_lo: usize,
    config: &DreggRecursionConfig,
) -> RecursionOutput<DreggRecursionConfig> {
    let pi_count = pi_lo + BRIDGE_MINT_CLAIM_LEN;
    let constraints: Vec<VmConstraint2> = (0..BRIDGE_MINT_CLAIM_LEN)
        .map(|k| {
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: k,
                pi_index: pi_lo + k,
            })
        })
        .collect();
    let desc = EffectVmDescriptor2 {
        name: "bridgemint-deco-claim-standin".to_string(),
        trace_width: BRIDGE_MINT_CLAIM_LEN,
        public_input_count: pi_count,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    };
    let rows = 4;
    let trace: Vec<Vec<BabyBear>> = (0..rows).map(|_| claim.to_vec()).collect();
    let mut pis = vec![BabyBear::ZERO; pi_count];
    for k in 0..BRIDGE_MINT_CLAIM_LEN {
        pis[pi_lo + k] = claim[k];
    }
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &trace,
        &pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .expect("claim leaf stand-in proves (the claim is internally consistent)");
    prove_descriptor_leaf_with_pi_slice_expose(
        &desc,
        &inner,
        &pis,
        config,
        pi_lo,
        BRIDGE_MINT_CLAIM_LEN,
    )
    .expect("claim leaf re-exposes the payment claim [mint_hash, value]")
}

/// POSITIVE POLE — the leg leaf and the payment sub-proof leaf attest the SAME `[mint_hash, value]`:
/// the binding node folds and re-exposes the bound claim.
#[test]
#[ignore = "SLOW: real bridge-mint commitment recursion fold (~minutes); run with --ignored"]
fn bridge_mint_commitment_honest_folds() {
    let config = ir2_leaf_wrap_config();
    let claim = [BabyBear::new(0x31D6), BabyBear::new(900)]; // [mint_hash, value]
    let leg = claim_leaf(claim, BRIDGE_MINT_CLAIM_PI_LO, &config); // the gated descriptor's PI[42..44]
    let sub = claim_leaf(claim, 0, &config); // the genuine payment claim

    prove_bridge_mint_commitment_node(&leg, &sub, &config)
        .expect("the honest bridge-mint payment claim binds in the fold (claims agree)");
    eprintln!("BRIDGE-MINT commitment: honest [mint_hash, value] FOLDED + bound in the recursion tree.");
}

/// THE TOOTH — the leg leaf claims a DIFFERENT `mint_hash` (a forged payment commitment) than the
/// sub-proof backs: the in-circuit `connect` is a conflict ⇒ UNSAT ⇒ no node proof.
#[test]
#[ignore = "SLOW: real bridge-mint commitment recursion fold (~minutes); run with --ignored"]
fn bridge_mint_commitment_forged_rejected() {
    let config = ir2_leaf_wrap_config();
    let leg_claim = [BabyBear::new(0x9999), BabyBear::new(900)]; // FORGED mint_hash
    let sub_claim = [BabyBear::new(0x31D6), BabyBear::new(900)]; // the genuine one
    assert_ne!(leg_claim, sub_claim);
    let leg = claim_leaf(leg_claim, BRIDGE_MINT_CLAIM_PI_LO, &config);
    let sub = claim_leaf(sub_claim, 0, &config);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_bridge_mint_commitment_node(&leg, &sub, &config)
    }));
    match result {
        Err(_) => {}
        Ok(Err(_)) => {}
        Ok(Ok(_)) => panic!(
            "a leg claiming a [mint_hash, value] NO verifying sub-proof backs folded into a verifying \
             node — the bridge-mint payment binding is OPEN"
        ),
    }
    eprintln!("BRIDGE-MINT commitment: forged mint_hash REJECTED by the fold (connect conflict ⇒ no root).");
}
