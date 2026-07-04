//! R2 — both-polarity, on the REAL executor: an admitted agent action becomes a
//! GENUINE committed kernel turn (its `turn_hash` sealed into the receipt), and the
//! executor's own `calls_made` caveat REFUSES a turn host-side.
//!
//! Unlike the `SyntheticMinter` unit tests in `dregg-agent` (which exercise only
//! the seam), these drive a real `dregg_sdk::ToolGateway` over the verified
//! executor — so `turn_receipt_hash` is a hash the kernel actually committed, not a
//! fabricated stub. This is the non-vacuity witness for the whole R2 weld.
//!
//! These tests are PRODUCER-side: grain-turn mints genuine committed kernel turns.
//! The cross-repo R2 end-to-end (grain-turn's manifest satisfying the downstream
//! `grain-verify::verify_r2`) lives in a downstream verifier crate, where the consumer and this producer
//! meet — breadstuffs references the downstream layer zero times.

use std::collections::BTreeMap;

use dregg_agent::agent::{AgentAction, AgentSpec, PlannedBrain, ToolKit, ToolOutcome};
use dregg_agent::session::Session;
use grain_turn::{ACTION_SLOT, CONSUMED_SLOT, ToolGatewayMinter, action_commit};

/// A trivial toolkit — the R2 tests exercise the kernel-turn weld, not a live tool.
struct NoKit;
impl ToolKit for NoKit {
    fn invoke(
        &self,
        _service: &str,
        _amount_cents: Option<i64>,
        _cells: &BTreeMap<String, String>,
    ) -> ToolOutcome {
        ToolOutcome::pass("ok")
    }
}

fn work_plan(n: usize) -> PlannedBrain {
    PlannedBrain::new(
        (0..n)
            .map(|_| AgentAction::Invoke {
                service: "work".into(),
            })
            .collect(),
    )
}

// ── GENUINE: each admitted receipt is a VIEW over a committed kernel turn ─────
#[test]
fn an_admitted_action_seals_a_receipt_linked_to_a_genuine_committed_turn() {
    let budget = 10;
    let mut minter = ToolGatewayMinter::open("grain-link", budget).expect("admit grain turn-cell");
    let spec = AgentSpec::new("ignored", budget).with_service("work");
    let mut sess = Session::open_seeded([71u8; 32], "dga1_renter", spec).unwrap();

    // The executor's on-ledger counter starts at 0 — nothing committed yet.
    assert_eq!(minter.calls_made(), 0);

    let gr = sess.run_goal_minted("do three", &mut work_plan(3), &NoKit, Some(&mut minter));
    assert_eq!(gr.admitted, 3, "all three in-budget actions admitted");

    // The executor really committed three turns (the on-ledger calls_made advanced).
    assert_eq!(
        minter.calls_made(),
        3,
        "the grain turn-cell's calls_made advanced 0 -> 3 on the real ledger"
    );
    let manifest = minter.committed_turns().to_vec();
    assert_eq!(manifest.len(), 3, "three genuine committed turns");

    // Every admitted receipt is a VIEW: its turn_receipt_hash is Some AND equals the
    // hash of the turn the executor committed for that action, in order.
    let report = sess.report();
    assert_eq!(report.receipts.len(), 3);
    for (r, want) in report.receipts.iter().zip(&manifest) {
        let linked = r
            .attestation
            .as_ref()
            .and_then(|a| a.turn_receipt_hash)
            .expect("an admitted receipt carries a kernel-turn link");
        assert_eq!(&linked, want, "the receipt views the committed turn's hash");
    }

    // The whole session still re-witnesses (the turn link rode the signed body).
    sess.verify().expect("the minted session re-witnesses");

    // ── SLOT WITNESS: the COMMITTED kernel state (read from the real ledger, not
    //    a tracked mirror) carries the last action's commit + consumed total ────
    let last = report.receipts.last().unwrap();
    assert_eq!(
        minter.read_slot(ACTION_SLOT),
        Some(action_commit(&last.action, last.cost)),
        "the committed turn witnesses WHICH action it was minted for"
    );
    // Negative polarity: a DIFFERENT action/cost commits differently — the slot
    // is a binding witness, not a constant.
    assert_ne!(
        minter.read_slot(ACTION_SLOT),
        Some(action_commit("invoke:something-else", last.cost)),
        "a different action label yields a different witnessed commit"
    );
    assert_ne!(
        minter.read_slot(ACTION_SLOT),
        Some(action_commit(&last.action, last.cost + 1)),
        "a different cost yields a different witnessed commit"
    );
    // The consumed slot carries the session meter's post-draw total (the
    // `field_from_u64` encoding: big-endian in the last 8 bytes).
    let consumed = minter.read_slot(CONSUMED_SLOT).expect("consumed witnessed");
    assert_eq!(
        u64::from_be_bytes(consumed[24..32].try_into().unwrap()),
        last.consumed_after as u64,
        "the committed turn witnesses the meter's post-draw consumed total"
    );
}

// (The R2 end-to-end weld — grain-turn's real manifest satisfying grain-verify::verify_r2
//  — is a cross-repo integration test that lives in a downstream verifier crate, beside the consumer (a downstream verifier crate). The
//  PRODUCER non-vacuity it needs is exactly what `committed_turns()` above exposes.)

// ── REFUSAL: the executor's calls_made caveat bounds the run host-side ────────
#[test]
fn the_executor_calls_made_caveat_refuses_over_rate_turns_host_side() {
    // The session budget (100) would admit all five actions, but the grain turn-cell
    // is admitted at rate 2 — so the EXECUTOR itself refuses the 3rd..5th turns, and
    // the agent admits nothing for them. The meter is enforced host-side, not merely
    // session-local.
    let mut minter = ToolGatewayMinter::open("grain-refuse", 2).expect("admit grain turn-cell");
    let spec = AgentSpec::new("ignored", 100).with_service("work");
    let mut sess = Session::open_seeded([72u8; 32], "dga1_renter", spec).unwrap();

    let gr = sess.run_goal_minted("try five", &mut work_plan(5), &NoKit, Some(&mut minter));
    assert_eq!(gr.admitted, 2, "only the 2 executor-admitted turns ran");

    let report = sess.report();
    assert_eq!(
        report.turn_refused, 3,
        "the executor refused the 3rd..5th turns host-side"
    );
    assert_eq!(report.receipts.len(), 2, "a refused turn seals no receipt");
    assert_eq!(report.consumed, 2, "a refused turn draws no budget");
    assert_eq!(
        minter.calls_made(),
        2,
        "the on-ledger counter never passed the rate-2 ceiling"
    );
    assert_eq!(
        minter.committed_turns().len(),
        2,
        "only two turns committed"
    );

    // The run re-witnesses after the host-side refusals (chain/meter consistent).
    sess.verify()
        .expect("re-witnesses after host-side refusals");
    // Both admitted receipts are genuine views.
    assert!(report.receipts.iter().all(|r| {
        r.attestation
            .as_ref()
            .and_then(|a| a.turn_receipt_hash)
            .is_some()
    }));
}
