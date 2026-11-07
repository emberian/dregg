//! R3 over a MULTI-turn grain session: `finalize_session_threaded` makes the chain continuous
//! across turn boundaries, so the whole session folds into one aggregate. SLOW (leg proves +
//! a recursive fold), `#[ignore]`d; run with
//! `cargo test -p grain-turn --features prover --test r3_threaded_session -- --ignored --nocapture`.
//! The Lean decision is not exercised here (the fold and the byte verify are); the Lean-routed
//! accept over these bytes is `grain_verify::r3_verify_aggregate`'s test.
#![cfg(feature = "prover")]

use dregg_agent::agent::GrainTurnMinter;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, prove_turn_chain_recursive_without_host_gate, verify_whole_chain_proof_bytes,
};
use dregg_circuit_prove::joint_turn_aggregation::verify_descriptor_participant;
use grain_turn::{
    ToolGatewayMinter, finalize_session, finalize_session_threaded, session_head_openings,
    session_model_nonce,
};

fn seam_breaks(legs: &[FinalizedTurn]) -> usize {
    legs.windows(2)
        .filter(|w| {
            w[0].participant.rotated.wide_new_root8() != w[1].participant.rotated.wide_old_root8()
        })
        .count()
}

#[test]
#[ignore = "SLOW: leg proves + a recursive fold; run with --ignored"]
fn a_three_turn_session_folds_when_threaded_and_not_otherwise() {
    let turns: usize = std::env::var("R3_TURNS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(3);
    let mut minter = ToolGatewayMinter::open("grain-r3-threaded", 64).expect("open");
    for t in 0..turns {
        minter
            .mint_turn(&format!("w{t}"), 1, (t + 1) as i64, [t as u8; 32])
            .expect("turn commits");
    }
    let t0 = std::time::Instant::now();
    let naive = finalize_session(minter.records()).expect("naive finalize (per-turn sub-chains)");
    let threaded = finalize_session_threaded(minter.records()).expect("threaded finalize");
    let fin = t0.elapsed();
    let naive_breaks = seam_breaks(&naive);
    let threaded_breaks = seam_breaks(&threaded);
    eprintln!(
        "turns={turns} legs={} naive seam breaks={naive_breaks} threaded seam breaks={threaded_breaks} finalize(both)={fin:?}",
        threaded.len()
    );
    assert!(
        naive_breaks >= 1,
        "the naive concatenation breaks at a turn boundary"
    );
    assert_eq!(threaded_breaks, 0, "the threaded chain is continuous");

    // OPEN THE HEAD before folding: the last leg's committed AFTER anchor must be the last cell
    // under the session context, as the EffectVM model carries it.
    let turn_hashes: Vec<[u8; 32]> = minter.records().iter().map(|r| r.turn_hash).collect();
    let last = &minter.records().last().unwrap().after_cell;
    let model_nonce = session_model_nonce(minter.records()).unwrap();
    let balance0 = minter.records()[0].before_cell.state.balance();
    let (real, model) = session_head_openings(last, &turn_hashes, model_nonce, balance0).unwrap();
    let leg_head: [u32; 8] = {
        let w = threaded
            .last()
            .unwrap()
            .participant
            .rotated
            .wide_new_root8()
            .unwrap();
        core::array::from_fn(|i| w[i].as_u32())
    };
    eprintln!(
        "head opening vs last leg: ledger={} model={}",
        real == leg_head,
        model == leg_head
    );
    assert_eq!(
        model, leg_head,
        "the folded head opens to the last cell (model nonce/balance)"
    );
    assert_ne!(
        real, leg_head,
        "the ledger head is NOT the folded head (the named residual)"
    );

    let selectors: Vec<usize> = threaded
        .iter()
        .map(|t| verify_descriptor_participant(&t.participant).expect("leg admitted"))
        .collect();
    let t1 = std::time::Instant::now();
    let proof = prove_turn_chain_recursive_without_host_gate(&threaded, &selectors).expect("folds");
    let fold = t1.elapsed();
    // The anchor is NOT taken from the proof under test: an independent session of the same shape
    // (a fresh minter, different labels, costs and heap roots) is finalized and folded by the
    // setup party, and its root fingerprint is the anchor the real aggregate must verify against.
    let mut setup_minter = ToolGatewayMinter::open("grain-r3-threaded-setup", 64).expect("open");
    for t in 0..turns {
        setup_minter
            .mint_turn(
                &format!("setup-{t}"),
                1,
                (t + 1) as i64,
                [0xA0 ^ t as u8; 32],
            )
            .expect("setup turn commits");
    }
    let setup_legs = finalize_session_threaded(setup_minter.records()).expect("setup finalize");
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
    let env =
        dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes::from_postcard(&bytes).unwrap();
    assert_eq!(
        env.final_root, model,
        "the aggregate's committed head is the opened head"
    );
    // THE R3 DECISION, through the Lean-proven core (no Rust fallback): accept at the opened
    // head; refuse a head one lane off, and refuse a foreign VK anchor.
    let v = grain_verify::r3_verify_aggregate(&bytes, &model, &vk)
        .expect("the Lean r3VerifyCore accepts the multi-turn session at its opened head");
    assert_eq!(v.num_turns, threaded.len());
    let mut off = model;
    off[3] = off[3].wrapping_add(1);
    assert!(matches!(
        grain_verify::r3_verify_aggregate(&bytes, &off, &vk),
        Err(grain_verify::R3Error::Rejected {
            aggregate_verified: true,
            ..
        })
    ));
    let mut foreign = vk;
    foreign.0[0] ^= 1;
    assert!(matches!(
        grain_verify::r3_verify_aggregate(&bytes, &model, &foreign),
        Err(grain_verify::R3Error::Rejected { .. })
    ));
    eprintln!(
        "fold={fold:?} verify={:?} bytes={} num_turns={}",
        t2.elapsed(),
        bytes.len(),
        proof.num_turns
    );
}
