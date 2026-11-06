//! The executor's per-turn transition on the grain worker cell, MEASURED (no prover).
//!
//! `SINGLE-TICK-DESCRIPTOR.md` (branch `i10-single-tick-grain-descriptor`) designs a rotated
//! descriptor whose one active row is the executor's whole grain turn. Its spec is read off
//! THIS measurement, not off prose: per committed grain turn, the worker cell's nonce moves by
//! exactly one (Phase 1 `increment_nonce`), its balance moves by exactly `-turn.fee` (Phase 1
//! `debit_balance`), slots 3..=7 take the written values, slots 0..=2 are untouched, and every
//! committed effect is a `SetField` on the worker cell. If any of these stops holding, the
//! descriptor's row intent no longer describes the executor and this test goes red first.
//!
//! Run: `cargo test -p grain-turn --no-default-features --test ledger_head_delta -- --nocapture`.

use dregg_agent::agent::GrainTurnMinter;
use dregg_sdk::{CALLS_MADE_SLOT, Effect};
use grain_turn::{
    ACTION_SLOT, CONSUMED_SLOT, HEAP_ROOT_SLOT, HISTORY_ROOT_SLOT, ToolGatewayMinter,
};

/// The fee the SDK's `execute_method` stamps on every `ToolGateway::invoke` turn
/// (`sdk/src/runtime.rs`, `fee: 5_000`). Phase 1 debits it from the agent = the worker cell.
const GATEWAY_TURN_FEE: i64 = 5_000;

#[test]
fn a_grain_turn_ticks_the_worker_nonce_once_and_debits_the_fee_once() {
    let turns = 3usize;
    let mut minter = ToolGatewayMinter::open("grain-ledger-head-delta", 64).expect("open");
    for t in 0..turns {
        minter
            .mint_turn(&format!("w{t}"), 1, (t + 1) as i64, [t as u8 + 1; 32])
            .expect("turn commits");
    }
    let recs = minter.records();
    assert_eq!(recs.len(), turns);
    let worker = recs[0].before_cell.id();
    for (i, r) in recs.iter().enumerate() {
        let (b, a) = (&r.before_cell.state, &r.after_cell.state);
        let dn = a.nonce() as i128 - b.nonce() as i128;
        let db = a.balance() as i128 - b.balance() as i128;
        eprintln!(
            "turn {i}: effects={} nonce {}->{} (d={dn}) balance {}->{} (d={db})",
            r.effects.len(),
            b.nonce(),
            a.nonce(),
            b.balance(),
            a.balance()
        );
        // ONE nonce tick per turn, regardless of how many SetFields the turn carries.
        assert_eq!(
            dn, 1,
            "turn {i}: the executor ticks the worker nonce once per turn"
        );
        // ONE fee debit per turn.
        assert_eq!(
            db,
            -(GATEWAY_TURN_FEE as i128),
            "turn {i}: Phase 1 debits turn.fee once"
        );
        // Five SetFields, all on the worker cell, slots {4,3,5,6,7} in that order.
        let slots: Vec<u64> = r
            .effects
            .iter()
            .map(|e| match e {
                Effect::SetField { cell, index, .. } => {
                    assert_eq!(
                        *cell, worker,
                        "turn {i}: a grain SetField targets the worker"
                    );
                    *index
                }
                other => panic!("turn {i}: non-SetField grain effect {other:?}"),
            })
            .collect();
        assert_eq!(
            slots,
            vec![
                CALLS_MADE_SLOT as u64,
                HISTORY_ROOT_SLOT as u64,
                CONSUMED_SLOT as u64,
                HEAP_ROOT_SLOT as u64,
                ACTION_SLOT as u64
            ],
            "turn {i}: the grain write set"
        );
        // Slots 0..=2 are untouched; 3..=7 hold the written values.
        for s in 0..3usize {
            assert_eq!(
                b.get_field(s),
                a.get_field(s),
                "turn {i}: slot {s} untouched"
            );
        }
        for e in &r.effects {
            if let Effect::SetField { index, value, .. } = e {
                assert_eq!(
                    a.get_field(*index as usize),
                    Some(value),
                    "turn {i}: slot {index} written"
                );
            }
        }
        // Consecutive turns chain on the LEDGER: turn i+1's pre-cell is turn i's post-cell.
        if i + 1 < recs.len() {
            let n = &recs[i + 1].before_cell.state;
            assert_eq!(n.nonce(), a.nonce());
            assert_eq!(n.balance(), a.balance());
        }
    }
}
