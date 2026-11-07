//! # R3 on a REAL driven grain session — the adapter end-to-end.
//!
//! Drives a tiny grain session through the genuine R2 weld ([`ToolGatewayMinter`] — each
//! `mint_turn` is a committed `ToolGateway::invoke` executor turn), FINALIZES it into a
//! `Vec<FinalizedTurn>` via [`grain_turn::finalize_session`] (the rotated wide-anchored
//! EffectVM legs, minted from the REAL captured turn data), and hands them to
//! [`grain_verify::r3_verify`] — the Lean-proven R3 decision. This is R3 running on a real
//! driven session, not a hand-minted fixture.
//!
//! SLOW: every leg is a full IR-v2 batch prove and the fold is the recursive step
//! (~minutes), so `#[ignore]`'d — run with
//! `cargo test -p grain-turn --features prover --test r3_grain_adapter -- --ignored --nocapture`.
//!
//! Scope note: one executor grain turn is ONE leg through the single-tick grain member
//! (`grainTurnVmDescriptor2R24`), minted over the real pre- and post-cells, so the head this fold
//! binds is the executor's on-ledger grain-cell head (`grain-session/SINGLE-TICK-DESCRIPTOR.md`).

#![cfg(feature = "prover")]

use dregg_agent::agent::GrainTurnMinter;
use grain_turn::{ToolGatewayMinter, finalize_session};
use grain_verify::{R3Error, r3_setup_anchor, r3_verify};

/// The FULL wide (8-felt, ~124-bit) head commit of the last leg in the chain — the fold's
/// committed head, exactly the anchor the honest case pins. All eight lanes: the pre-repair
/// seam projected this to lane 0 (~31 bits), which is wound #22.
fn chain_head(legs: &[dregg_circuit_prove::ivc_turn_chain::FinalizedTurn]) -> [u32; 8] {
    let wide = legs
        .last()
        .expect("non-empty chain")
        .participant
        .rotated
        .wide_new_root8()
        .expect("deployed grain leg is wide-anchored");
    core::array::from_fn(|i| wide[i].as_u32())
}

#[test]
#[ignore = "SLOW: per-field-write IR-v2 batch proves + a recursive fold (~minutes); run with --ignored"]
fn r3_verifies_a_real_driven_grain_session() {
    // The DECISION is the Lean-proven verifier; without the extracted core linked there is
    // NO Rust fallback (by design).
    //
    // ⚑ ARMED (2026-08-08). This was the raw availability bit + `eprintln!` + `return`, which is
    // the BR-3 shape: cargo prints `ok`, the eprintln is swallowed without `--nocapture`, and the
    // whole R3 adapter claim is unasserted. `grain-turn` and `grain-verify` were the last two
    // crates depending on `dregg-lean-ffi` with a runtime skip guard and ZERO `demand_lean` —
    // `persist/` was converted on 2026-08-08 and these two were missed by the same sweep.
    // `demand_lean` PANICS naming the capability unless `DREGG_TEST_ALLOW_MISSING_LEAN=1` is the
    // declared opt-IN, in which case it returns false and this `return` is the honest skip.
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::grain_r3_verify_core_available(),
        "the Lean-proven R3 verifier core (dregg_grain_r3_verify / Dregg2.Grain.R3Verify) — \
         rebuild dregg-lean-ffi to splice it; there is NO Rust fallback for this decision",
    ) {
        return;
    }

    // ── DRIVE a tiny grain session (ONE admitted action → ONE committed executor turn). ──
    // One committed turn, one leg; the multi-turn fold is `r3_threaded_session.rs`.
    let mut minter = ToolGatewayMinter::open("grain-r3-adapter", 8).expect("open grain minter");
    let cell_root = [9u8; 32];
    let t_mint = std::time::Instant::now();
    minter
        .mint_turn("search", 1, 1, cell_root)
        .expect("the grain turn commits (admitted, in-rate)");
    let mint_elapsed = t_mint.elapsed();
    assert_eq!(
        minter.records().len(),
        1,
        "one committed grain turn captured"
    );

    // ── FINALIZE: mint the rotated wide-anchored EffectVM legs from the REAL turn data. ──
    let t_fin = std::time::Instant::now();
    let legs = finalize_session(minter.records()).expect("real grain turn finalizes to legs");
    let finalize_elapsed = t_fin.elapsed();
    assert_eq!(
        legs.len(),
        1,
        "one executor grain turn is ONE leg (the single-tick grain member writes all five slots, \
         debits the fee and ticks the nonce once); got {}",
        legs.len()
    );
    let head = chain_head(&legs);

    // SETUP — the honest party mints its OWN trust anchor from a fold IT produced (the
    // `fold_and_attest` role). Verifying against the presented proof's own fingerprint is
    // what wound #22 removed.
    let anchor = r3_setup_anchor(&legs).expect("the honest setup fold mints an anchor");

    // (i) HONEST — the real driven session, anchored at its genuine folded 8-felt head → "1".
    let t_fold = std::time::Instant::now();
    let v = r3_verify(&legs, &head, &anchor).expect("a real driven grain session R3-verifies");
    let fold_elapsed = t_fold.elapsed();
    assert_eq!(v.num_turns, legs.len());
    assert_eq!(v.anchored_head, head);
    assert_eq!(
        v.aggregate_head, head,
        "the aggregate's committed 8-felt head IS the genuine fold head, in every lane"
    );

    // (ii) WOUND #22 — THE WIDTH TOOTH, on a real driven session. The SAME chain anchored at
    // a head byte-identical in LANE 0 and different only at lane 1: everything the pre-repair
    // seam compared is equal, so it ACCEPTED this. The widened binding must REJECT.
    let mut lane1_forged = head;
    lane1_forged[1] = lane1_forged[1].wrapping_add(1);
    assert_eq!(lane1_forged[0], head[0], "invisible to the lane-0 seam");
    match r3_verify(&legs, &lane1_forged, &anchor) {
        Err(R3Error::Rejected {
            aggregate_verified,
            anchored_head,
            ..
        }) => {
            assert!(
                aggregate_verified,
                "the aggregate itself DID verify — only the anchor is foreign"
            );
            assert_eq!(anchored_head, lane1_forged);
        }
        other => panic!(
            "a foreign anchor differing ONLY OUTSIDE LANE 0 must be Lean-REJECTED (wound #22); \
             got {other:?}"
        ),
    }

    // ⚑ The two `R3Error::Rejected` matches in this test became load-bearing on 2026-08-07.
    // Before then `r3VerifyFFI` rendered an UNREADABLE wire as `"0"` — the same code the
    // whole-history refusal renders as — and `r3_verify` decoded everything that was not `"1"`
    // into `Rejected`, so both poles were also satisfied by "the wire drifted and nothing was
    // decided". An unreadable wire is now `R3Error::WireMalformed`, which the `other => panic!`
    // arms catch. No edit was needed here; the assertions simply started meaning what they say.

    // (iii) TAMPER — forge the last leg's claimed post-state PI → the fold does not verify.
    let forged = forge_last_post_state(minter.records());
    match r3_verify(&forged, &head, &anchor) {
        Err(R3Error::Rejected {
            aggregate_verified, ..
        }) => assert!(
            !aggregate_verified,
            "a forged post-state's aggregate must NOT verify — verified-status is false"
        ),
        other => panic!("a tampered history must be R3-REJECTED; got {other:?}"),
    }

    eprintln!(
        "R3 on a REAL grain session: mint={mint_elapsed:?}, finalize({} legs)={finalize_elapsed:?}, \
         honest fold={fold_elapsed:?} — the ACCEPT decision rendered by the Lean-proven r3VerifyCore.",
        legs.len()
    );
}

/// Re-finalize the session, then forge the LAST leg's claimed post-state PI (the 8-felt
/// wide AFTER-commit): the execution witness stays honest, only the CLAIM is forged, so the
/// leaf re-verify is UNSAT and the fold does not verify. Mirrors the whole-history test's
/// `forge_last_post_state`.
fn forge_last_post_state(
    records: &[grain_turn::GrainTurnRecord],
) -> Vec<dregg_circuit_prove::ivc_turn_chain::FinalizedTurn> {
    use dregg_circuit::field::BabyBear;
    use dregg_circuit_prove::ivc_turn_chain::FinalizedTurn;
    use dregg_circuit_prove::joint_turn_aggregation::{
        DescriptorParticipant, RotatedParticipantLeg,
    };

    let mut legs = finalize_session(records).expect("finalize for the tamper case");
    let last = legs.len() - 1;
    let DescriptorParticipant { rotated } = legs.remove(last).participant;
    let RotatedParticipantLeg {
        proof,
        descriptor,
        mut public_inputs,
        carrier_witness,
    } = rotated;
    let pi_wide_new = public_inputs.len() - 8;
    public_inputs[pi_wide_new] = public_inputs[pi_wide_new] + BabyBear::ONE;
    legs.push(FinalizedTurn::new(DescriptorParticipant::rotated(
        RotatedParticipantLeg {
            proof,
            descriptor,
            public_inputs,
            carrier_witness,
        },
    )));
    legs
}
