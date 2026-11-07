//! R3 over a MULTI-turn grain session through the single-tick grain member: ONE leg per executor
//! turn, minted over the REAL ledger pre/post cells, folded into one aggregate the Lean
//! `r3VerifyCore` decides at the LEDGER head. Plus the tamper rungs: a wrong fee is refused by the
//! leg (its constraint / its published fee PI), a wrong nonce tick by the head opening.
//!
//! SLOW (leg proves + a recursive fold), `#[ignore]`d; run with
//! `cargo test -p grain-turn --features prover --test r3_threaded_session -- --ignored --nocapture`.
#![cfg(feature = "prover")]

use dregg_agent::agent::GrainTurnMinter;
use dregg_circuit::effect_vm::Effect as VmEffect;
use dregg_circuit::effect_vm::trace_rotated::ROT_PI_COUNT;
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, prove_turn_chain_recursive_without_host_gate, verify_whole_chain_proof_bytes,
};
use dregg_circuit_prove::joint_turn_aggregation::verify_descriptor_participant;
use grain_turn::{
    ToolGatewayMinter, finalize_session_threaded, grain_turn_vm_effect, session_head_openings,
};

/// The fee `ToolGateway::invoke` stamps on every grain turn (`sdk/src/runtime.rs`).
const GATEWAY_TURN_FEE: u32 = 5_000;

fn seam_breaks(legs: &[FinalizedTurn]) -> usize {
    legs.windows(2)
        .filter(|w| {
            w[0].participant.rotated.wide_new_root8() != w[1].participant.rotated.wide_old_root8()
        })
        .count()
}

fn session(label: &str, turns: usize, salt: u8) -> ToolGatewayMinter {
    let mut minter = ToolGatewayMinter::open(label, 64).expect("open");
    for t in 0..turns {
        minter
            .mint_turn(
                &format!("{label}-{t}"),
                1,
                (t + 1) as i64,
                [salt ^ t as u8; 32],
            )
            .expect("turn commits");
    }
    minter
}

#[test]
#[ignore = "SLOW: leg proves + a recursive fold; run with --ignored"]
fn a_multi_turn_session_folds_at_the_ledger_head_one_leg_per_turn() {
    let turns: usize = std::env::var("R3_TURNS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(3);
    let minter = session("grain-r3-threaded", turns, 0);
    let records = minter.records();

    let t0 = std::time::Instant::now();
    let legs = finalize_session_threaded(records).expect("threaded finalize");
    let fin = t0.elapsed();
    eprintln!(
        "turns={turns} legs={} seam breaks={} finalize={fin:?} ({:?}/leg)",
        legs.len(),
        seam_breaks(&legs),
        fin / legs.len() as u32
    );
    assert_eq!(legs.len(), turns, "ONE leg per executor turn");
    assert_eq!(
        seam_breaks(&legs),
        0,
        "consecutive legs meet at the ledger cells"
    );

    // Every leg attests the per-turn fee: the published fee PI is the executor's `turn.fee`.
    for (i, leg) in legs.iter().enumerate() {
        assert_eq!(
            leg.participant.rotated.public_inputs[ROT_PI_COUNT],
            BabyBear::new(GATEWAY_TURN_FEE),
            "leg {i} publishes the fee its row debited"
        );
    }

    // OPEN THE HEAD before folding: the last leg's committed AFTER anchor is the LAST LEDGER CELL
    // under the session context — no model nonce, no carried balance.
    let turn_hashes: Vec<[u8; 32]> = records.iter().map(|r| r.turn_hash).collect();
    let last = &records.last().unwrap().after_cell;
    let head = session_head_openings(last, &turn_hashes).unwrap();
    let leg_head: [u32; 8] = {
        let w = legs
            .last()
            .unwrap()
            .participant
            .rotated
            .wide_new_root8()
            .unwrap();
        core::array::from_fn(|i| w[i].as_u32())
    };
    assert_eq!(
        head, leg_head,
        "the folded head opens to the last LEDGER cell"
    );
    let genesis = session_head_openings(&records[0].before_cell, &turn_hashes).unwrap();
    let leg_genesis: [u32; 8] = {
        let w = legs[0].participant.rotated.wide_old_root8().unwrap();
        core::array::from_fn(|i| w[i].as_u32())
    };
    assert_eq!(
        genesis, leg_genesis,
        "the chain genesis is the first LEDGER pre-cell"
    );

    let selectors: Vec<usize> = legs
        .iter()
        .map(|t| verify_descriptor_participant(&t.participant).expect("leg admitted"))
        .collect();
    let t1 = std::time::Instant::now();
    let proof = prove_turn_chain_recursive_without_host_gate(&legs, &selectors).expect("folds");
    let fold = t1.elapsed();
    // The anchor is NOT taken from the proof under test: an independent session of the same shape
    // is finalized and folded by the setup party.
    let setup = session("grain-r3-threaded-setup", turns, 0xA0);
    let setup_legs = finalize_session_threaded(setup.records()).expect("setup finalize");
    let setup_selectors: Vec<usize> = setup_legs
        .iter()
        .map(|t| verify_descriptor_participant(&t.participant).expect("setup leg admitted"))
        .collect();
    let vk = prove_turn_chain_recursive_without_host_gate(&setup_legs, &setup_selectors)
        .expect("setup folds")
        .root_vk_fingerprint();
    assert_eq!(
        vk,
        proof.root_vk_fingerprint(),
        "the VK is a function of the session's shape, not its content"
    );
    let bytes = proof.to_bytes();
    let t2 = std::time::Instant::now();
    verify_whole_chain_proof_bytes(&bytes, &vk)
        .expect("aggregate verifies against the independent setup anchor");
    let verify = t2.elapsed();
    let env =
        dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes::from_postcard(&bytes).unwrap();
    assert_eq!(
        env.final_root, head,
        "the aggregate's committed head is the LEDGER head"
    );

    // THE R3 DECISION, through the Lean-proven core (no Rust fallback).
    let v = grain_verify::r3_verify_aggregate(&bytes, &head, &vk)
        .expect("the Lean r3VerifyCore accepts the session at the ledger head");
    assert_eq!(v.num_turns, turns);

    // TAMPER (nonce, the head-opening rung): the last cell with ONE extra tick — the per-effect
    // model's shape — opens to a different head, and the Lean core refuses the aggregate there.
    let mut two_ticks = last.clone();
    two_ticks.state.set_nonce(last.state.nonce() + 1);
    let forged = session_head_openings(&two_ticks, &turn_hashes).unwrap();
    assert_ne!(forged, head);
    let err = grain_verify::r3_verify_aggregate(&bytes, &forged, &vk)
        .expect_err("a head with an extra nonce tick is refused");
    assert!(
        matches!(
            err,
            grain_verify::R3Error::Rejected {
                aggregate_verified: true,
                ..
            }
        ),
        "refused by the head comparison, not the fold: {err}"
    );
    eprintln!("nonce-tamper refusal: {err}");
    // TAMPER (fee, the head-opening rung's twin): the last cell WITHOUT its fee debited.
    let mut no_fee = last.clone();
    no_fee
        .state
        .set_balance(last.state.balance() + GATEWAY_TURN_FEE as i64);
    let unfee = session_head_openings(&no_fee, &turn_hashes).unwrap();
    assert!(matches!(
        grain_verify::r3_verify_aggregate(&bytes, &unfee, &vk),
        Err(grain_verify::R3Error::Rejected {
            aggregate_verified: true,
            ..
        })
    ));
    let mut foreign = vk;
    foreign.0[0] ^= 1;
    assert!(matches!(
        grain_verify::r3_verify_aggregate(&bytes, &head, &foreign),
        Err(grain_verify::R3Error::Rejected { .. })
    ));
    eprintln!(
        "fold={fold:?} verify={verify:?} bytes={} num_turns={}",
        bytes.len(),
        proof.num_turns
    );
}

/// TAMPER (fee, the LEG rung). (1) A leg whose published fee PI is moved off the fee the proof
/// debited does not verify. (2) A witness that debits the true fee while CLAIMING a different
/// one has no proof: the mint's own prove/self-verify refuses it.
#[test]
#[ignore = "SLOW: leg proves; run with --ignored"]
fn a_wrong_fee_is_refused_by_the_leg() {
    let minter = session("grain-r3-fee-tamper", 1, 0x55);
    let rec = &minter.records()[0];
    let mut leg = grain_turn::finalize_grain_turn(rec)
        .expect("honest leg")
        .remove(0);
    verify_descriptor_participant(&leg.participant).expect("the honest leg verifies");

    leg.participant.rotated.public_inputs[ROT_PI_COUNT] = BabyBear::new(GATEWAY_TURN_FEE - 1);
    let err =
        verify_descriptor_participant(&leg.participant).expect_err("a moved fee PI is refused");
    eprintln!("fee-PI tamper refusal: {err}");
    assert!(
        err.contains("rotated descriptor participant proof failed standalone verification"),
        "{err}"
    );

    // The honest row with the fee param one short: the balance moved by 5000, the row claims 4999.
    let VmEffect::GrainTurn { values, fee } = grain_turn_vm_effect(rec).unwrap() else {
        panic!("a grain turn coalesces to GrainTurn")
    };
    assert_eq!(fee, GATEWAY_TURN_FEE as u64);
    let lying = VmEffect::GrainTurn {
        values,
        fee: fee - 1,
    };
    let Err(err) = grain_turn::mint_grain_leg_with(rec, &[rec.turn_hash], lying) else {
        panic!("a fee that is not the debit has no proof")
    };
    eprintln!("fee-witness tamper refusal: {err}");
    assert!(err.contains("rotated-leg mint failed"), "{err}");
}
