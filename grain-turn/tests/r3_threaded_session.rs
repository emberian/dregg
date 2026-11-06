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
    let naive = finalize_session(minter.records()).expect("naive finalize");
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

    let selectors: Vec<usize> = threaded
        .iter()
        .map(|t| verify_descriptor_participant(&t.participant).expect("leg verifies"))
        .collect();
    let t1 = std::time::Instant::now();
    let proof = prove_turn_chain_recursive_without_host_gate(&threaded, &selectors).expect("folds");
    let fold = t1.elapsed();
    let vk = proof.root_vk_fingerprint();
    let bytes = proof.to_bytes();
    let t2 = std::time::Instant::now();
    verify_whole_chain_proof_bytes(&bytes, &vk)
        .expect("aggregate verifies against the setup anchor");
    let env =
        dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes::from_postcard(&bytes).unwrap();
    let turn_hashes: Vec<[u8; 32]> = minter.records().iter().map(|r| r.turn_hash).collect();
    let last = &minter.records().last().unwrap().after_cell;
    let model_nonce = session_model_nonce(minter.records()).unwrap();
    let (real, model) = session_head_openings(last, &turn_hashes, model_nonce).unwrap();
    let mut frozen = last.clone();
    frozen
        .state
        .set_balance(minter.records()[0].before_cell.state.balance());
    let (_, model_frozen) = session_head_openings(&frozen, &turn_hashes, model_nonce).unwrap();
    eprintln!(
        "head opening (model nonce + turn-0 balance): {}",
        model_frozen == env.final_root
    );
    eprintln!(
        "head opening: aggregate={:?} ledger-nonce={} model-nonce({model_nonce})={}",
        env.final_root,
        real == env.final_root,
        model == env.final_root
    );
    eprintln!(
        "fold={fold:?} verify={:?} bytes={} num_turns={}",
        t2.elapsed(),
        bytes.len(),
        proof.num_turns
    );
}
