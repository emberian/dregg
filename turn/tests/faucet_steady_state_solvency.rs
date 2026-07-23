//! THE FEE LOOP (revolving fund) steady-state solvency property.
//!
//! Models the harness of `turn/tests/conservation_burn_property.rs` (`open_cell`
//! + `TurnExecutor`), but for the DEPLOYED drain: on a genesis-less devnet cave
//! node the fee well was a PURE SINK — `distribute_fee_shares` credited the
//! undelivered fee remainder into a cell nothing ever moved value OUT of — while
//! the faucet, a pure payer-out, drained monotonically on every agent top-up.
//! ~800 fee-bearing turns later: "insufficient balance on cell <id>: need 1254,
//! have <X>" → signing DEGRADED.
//!
//! THE FIX (proven load-bearing here): point the executor's fee well AT the
//! faucet cell (`set_fee_well_cell(faucet_id)`), so every committed turn's
//! `fee - delivered` credit recirculates straight back into the pool the faucet
//! pays out of. NO fee is zeroed — the per-turn debit remains the oversight
//! leash. Two invariants, both asserted:
//!   (1) PER-TURN: Σ(balance_change over every cell) == 0 — no ex-nihilo mint or
//!       burn on any committed turn.
//!   (2) STANDING (closed system): Σ(faucet + every agent) == const across N
//!       turns, because the fee no longer escapes to a dead sink.
//! The CONTROL (`fee_well` UNSET) reproduces the drain — locking in that the
//! pointer change is the CAUSE of solvency.
//!
//! HARNESS NOTE: like `conservation_burn_property.rs`, each `execute()` runs on
//! a FRESH `TurnExecutor` (`run_turn`) — the executor enforces per-agent receipt
//! chaining (`check_previous_receipt_hash`), and cell nonces / balances live on
//! the LEDGER, which persists across executors. This isolates the value
//! invariants (the subject under test) from receipt-chain bookkeeping.

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::{Turn, TurnResult},
};

/// The observed real per-turn coordination fee on the deployed chain.
const FEE: u64 = 1254;

fn open_permissions() -> Permissions {
    Permissions {
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

/// An open hosted cell (default asset) with a chosen balance.
fn open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37).wrapping_add(1);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn base_action(target: CellId, effects: Vec<Effect>) -> Action {
    Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    }
}

fn base_turn(agent: CellId, nonce: u64, fee: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(base_action(agent, effects));
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// A fee-bearing COORDINATION turn: an empty-effects action (the ~99% a2a-chat
/// workload). It commits, debits `fee` from the agent, and — with the well set —
/// credits `fee` to the faucet.
fn coordination_turn(agent: CellId, nonce: u64, fee: u64) -> Turn {
    base_turn(agent, nonce, fee, vec![])
}

/// The faucet's OWN top-up turn: agent == faucet, a Transfer of `amount` to the
/// recipient. Fee-bearing like any turn; with well == faucet the -fee/+fee legs
/// net zero, so the faucet's net per top-up is exactly -amount.
fn faucet_topup_turn(faucet: CellId, recipient: CellId, nonce: u64, fee: u64, amount: u64) -> Turn {
    base_turn(
        faucet,
        nonce,
        fee,
        vec![Effect::Transfer {
            from: faucet,
            to: recipient,
            amount,
        }],
    )
}

/// Run one turn on a fresh executor with an optional fee well. See HARNESS NOTE.
fn run_turn(ledger: &mut Ledger, turn: &Turn, fee_well: Option<CellId>) -> TurnResult {
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    if let Some(well) = fee_well {
        executor.set_fee_well_cell(well);
    }
    executor.execute(turn, ledger)
}

/// Snapshot every cell's balance keyed by id.
fn balances(ledger: &Ledger) -> std::collections::HashMap<CellId, i64> {
    ledger
        .iter()
        .map(|(id, c)| (*id, c.state.balance()))
        .collect()
}

/// Sum of ALL per-cell balance deltas across the whole ledger (any lazily-created
/// cell appears as a delta from 0).
fn total_delta(
    before: &std::collections::HashMap<CellId, i64>,
    after: &std::collections::HashMap<CellId, i64>,
) -> i128 {
    let mut keys: std::collections::HashSet<&CellId> = before.keys().collect();
    keys.extend(after.keys());
    keys.into_iter()
        .map(|k| {
            let b = before.get(k).copied().unwrap_or(0) as i128;
            let a = after.get(k).copied().unwrap_or(0) as i128;
            a - b
        })
        .sum()
}

/// Whole-ledger balance sum (the standing closed-system total).
fn ledger_total(ledger: &Ledger) -> i128 {
    ledger.iter().map(|(_, c)| c.state.balance() as i128).sum()
}

fn bal(ledger: &Ledger, id: &CellId) -> i64 {
    ledger.get(id).unwrap().state.balance()
}

// =============================================================================
// UNIT: per-turn conservation + the faucet is credited exactly (fee - delivered)
// on every coordination turn, so it can never trend to zero under load.
// =============================================================================
#[test]
fn unit_fee_well_is_faucet_credits_each_coordination_turn() {
    let agent = open_cell(1, 1_000_000);
    let faucet = open_cell(2, 1_000_000);
    let agent_id = agent.id();
    let faucet_id = faucet.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(faucet).unwrap();

    // No proposer / treasury configured → delivered == 0 → the whole fee moves
    // to the well (== faucet) on every turn.
    let delivered: u64 = 0;
    let per_turn_credit = FEE - delivered;

    let n = 500u64;
    for nonce in 0..n {
        let faucet_before = bal(&ledger, &faucet_id);
        let agent_before = bal(&ledger, &agent_id);
        let before = balances(&ledger);

        let result = run_turn(
            &mut ledger,
            &coordination_turn(agent_id, nonce, FEE),
            Some(faucet_id),
        );
        assert!(
            matches!(result, TurnResult::Committed { .. }),
            "coordination turn {nonce} must commit: {result:?}"
        );

        let after = balances(&ledger);
        // (1) PER-TURN CONSERVATION.
        assert_eq!(
            total_delta(&before, &after),
            0,
            "per-turn Σδ must be zero on turn {nonce} (agent -fee == faucet +fee)"
        );
        // The faucet gained exactly (fee - delivered).
        assert_eq!(
            bal(&ledger, &faucet_id),
            faucet_before + per_turn_credit as i64,
            "faucet credited exactly (fee - delivered) on turn {nonce}"
        );
        // The agent paid exactly fee.
        assert_eq!(
            bal(&ledger, &agent_id),
            agent_before - FEE as i64,
            "agent debited exactly fee on turn {nonce}"
        );
    }

    // After N turns the faucet is UP by N*fee, not drained.
    assert_eq!(
        bal(&ledger, &faucet_id),
        1_000_000 + (n * per_turn_credit) as i64,
        "faucet accrued every coordination fee — the opposite of draining"
    );
}

// =============================================================================
// INTEGRATION: closed-loop sim over N=10_000 coordination turns with faucet
// top-ups. The standing total is invariant and the faucet holds a positive
// floor — it NEVER hits the 'need <fee>, have <X>' insufficient-balance wall.
// =============================================================================
#[test]
fn integration_closed_loop_solvent_over_10k_turns() {
    const FAUCET_START: i64 = 1_000_000;
    const AGENT_BUFFER: u64 = 50_000; // the agent's working balance target

    let agent = open_cell(3, AGENT_BUFFER as i64);
    let faucet = open_cell(4, FAUCET_START);
    let agent_id = agent.id();
    let faucet_id = faucet.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(faucet).unwrap();

    let standing_before = ledger_total(&ledger);
    assert_eq!(standing_before, FAUCET_START + AGENT_BUFFER as i64);

    let mut agent_nonce = 0u64;
    let mut faucet_nonce = 0u64;
    // Fees the faucet has skimmed back since the last top-up — the amount it
    // returns to the agent so the loop reaches exact steady state.
    let mut skim_since_topup: u64 = 0;
    let mut floor = i64::MAX;

    let turns = 10_000u64;
    for _ in 0..turns {
        // Top up the agent BEFORE it would fall below one fee — modeling the
        // real faucet, funded from fees it accrued since the last top-up.
        if bal(&ledger, &agent_id) < FEE as i64 {
            // Return EXACTLY the fees skimmed since the last top-up: agent +
            // skim is invariant between top-ups, so this restores the agent to
            // its post-previous-top-up level and the faucet nets zero per cycle
            // (true steady state).
            let amount = skim_since_topup;
            let before = balances(&ledger);
            let r = run_turn(
                &mut ledger,
                &faucet_topup_turn(faucet_id, agent_id, faucet_nonce, FEE, amount),
                Some(faucet_id),
            );
            assert!(
                matches!(r, TurnResult::Committed { .. }),
                "faucet top-up must commit (faucet solvent): {r:?}"
            );
            faucet_nonce += 1;
            skim_since_topup = 0;
            // The top-up turn is itself conservation-closed (fee legs net zero,
            // Transfer moves `amount`).
            assert_eq!(
                total_delta(&before, &balances(&ledger)),
                0,
                "faucet top-up turn must be conservation-closed (Σδ == 0)"
            );
        }

        // One coordination turn: agent -fee, faucet +fee.
        let r = run_turn(
            &mut ledger,
            &coordination_turn(agent_id, agent_nonce, FEE),
            Some(faucet_id),
        );
        assert!(
            matches!(r, TurnResult::Committed { .. }),
            "coordination turn must commit — the agent is never starved: {r:?}"
        );
        agent_nonce += 1;
        skim_since_topup += FEE;

        floor = floor.min(bal(&ledger, &faucet_id));
    }

    // (2) STANDING INVARIANT: the closed {faucet + agent} total is unchanged.
    assert_eq!(
        ledger_total(&ledger),
        standing_before,
        "standing total must be invariant across {turns} turns (no dead sink)"
    );
    // The faucet held a strictly POSITIVE floor and never approached zero: the
    // deepest dip is bounded by the agent's working buffer, not by the run
    // length. THIS is the property the drain violated.
    assert!(
        floor >= FAUCET_START - AGENT_BUFFER as i64 - FEE as i64,
        "faucet floor {floor} must stay near start (bounded by the agent buffer, not turn count)"
    );
    assert!(floor > 0, "faucet never insolvent (floor {floor} > 0)");
}

// =============================================================================
// CONTROL / REGRESSION: the IDENTICAL loop with the fee well UNSET. The fee is
// now BURNED every coordination turn (debited from the agent, credited nowhere),
// so the closed total bleeds away and the faucet drains monotonically to
// insolvency. Proves the pointer change is the CAUSE of solvency.
// =============================================================================
#[test]
fn control_no_fee_well_drains_faucet_to_insolvency() {
    const FAUCET_START: i64 = 1_000_000;
    const AGENT_BUFFER: u64 = 50_000;

    let agent = open_cell(5, AGENT_BUFFER as i64);
    let faucet = open_cell(6, FAUCET_START);
    let agent_id = agent.id();
    let faucet_id = faucet.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(faucet).unwrap();

    let standing_before = ledger_total(&ledger);

    let mut agent_nonce = 0u64;
    let mut faucet_nonce = 0u64;
    let mut last_faucet = FAUCET_START;
    let mut monotone_nonincreasing = true;
    let mut insolvency_turn: Option<u64> = None;

    // A generous bound: the faucet MUST go insolvent well within this many turns
    // (FAUCET_START / FEE ≈ 797 fee-burns' worth of runway).
    let cap = 5_000u64;
    for t in 0..cap {
        // Fund the agent when it can't cover a fee, IF the faucet still can.
        if bal(&ledger, &agent_id) < FEE as i64 {
            if bal(&ledger, &faucet_id) < (AGENT_BUFFER + FEE) as i64 {
                // Faucet can no longer fund a full buffer + its own fee: the
                // observed "insufficient balance ... need <fee>" wall.
                insolvency_turn = Some(t);
                break;
            }
            // NO fee well — fees BURN, so the faucet is never replenished.
            let r = run_turn(
                &mut ledger,
                &faucet_topup_turn(faucet_id, agent_id, faucet_nonce, FEE, AGENT_BUFFER),
                None,
            );
            assert!(matches!(r, TurnResult::Committed { .. }), "top-up: {r:?}");
            faucet_nonce += 1;
        }

        let r = run_turn(
            &mut ledger,
            &coordination_turn(agent_id, agent_nonce, FEE),
            None,
        );
        assert!(matches!(r, TurnResult::Committed { .. }), "coord: {r:?}");
        agent_nonce += 1;

        let f = bal(&ledger, &faucet_id);
        if f > last_faucet {
            monotone_nonincreasing = false; // the well-less faucet only ever loses value
        }
        last_faucet = f;
    }

    // The closed total STRICTLY DECREASED — value escaped to the burn sink.
    assert!(
        ledger_total(&ledger) < standing_before,
        "well-less: standing total must bleed (fees burned, not recirculated)"
    );
    // The faucet trended monotonically down and reached the insolvency wall.
    assert!(
        monotone_nonincreasing,
        "well-less faucet must only ever lose value (monotone non-increasing)"
    );
    assert!(
        insolvency_turn.is_some(),
        "well-less faucet MUST hit the insufficient-balance wall within {cap} turns"
    );
}

// =============================================================================
// PROPERTY: over randomized fee / top-up schedules (deterministic LCG so it is
// reproducible without a proptest dependency), the fee-well-as-faucet loop keeps
// the faucet bounded BELOW by a positive constant — steady-state, not draining —
// and every turn stays conservation-closed.
// =============================================================================
#[test]
fn property_randomized_schedule_faucet_bounded_below() {
    const FAUCET_START: i64 = 2_000_000;
    const AGENT_START: i64 = 200_000;

    // Simple reproducible LCG (Numerical Recipes constants).
    let mut rng: u64 = 0x9E3779B97F4A7C15;
    let mut next = || {
        rng = rng
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (rng >> 33) as u64
    };

    let agent = open_cell(7, AGENT_START);
    let faucet = open_cell(8, FAUCET_START);
    let agent_id = agent.id();
    let faucet_id = faucet.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(faucet).unwrap();

    let standing_before = ledger_total(&ledger);

    let mut agent_nonce = 0u64;
    let mut faucet_nonce = 0u64;
    let mut skim_since_topup: u64 = 0;
    let mut floor = i64::MAX;

    for _ in 0..8_000u64 {
        // Randomized fee in a plausible coordination band [200, 2000].
        let fee = 200 + next() % 1801;

        // Randomized top-up policy: sometimes refill early, sometimes only when
        // forced. Never let the agent starve (that would just reject, not drain).
        let refill_threshold = (fee as i64) * (1 + (next() % 5) as i64);
        if skim_since_topup > 0 && bal(&ledger, &agent_id) < refill_threshold {
            // Return EXACTLY the fees skimmed since the last top-up. agent +
            // skim is invariant between top-ups (each coordination turn moves
            // fee from agent to skim), so this restores the agent to its
            // post-previous-top-up level (>= AGENT_START) and the faucet nets
            // zero per cycle — steady state under ANY schedule.
            let amount = skim_since_topup;
            if bal(&ledger, &faucet_id) >= (amount + fee) as i64 {
                let before = balances(&ledger);
                let r = run_turn(
                    &mut ledger,
                    &faucet_topup_turn(faucet_id, agent_id, faucet_nonce, fee, amount),
                    Some(faucet_id),
                );
                assert!(matches!(r, TurnResult::Committed { .. }), "topup: {r:?}");
                faucet_nonce += 1;
                skim_since_topup = 0;
                assert_eq!(
                    total_delta(&before, &balances(&ledger)),
                    0,
                    "randomized top-up turn must be conservation-closed"
                );
            }
        }

        if bal(&ledger, &agent_id) < fee as i64 {
            continue; // skip this coordination turn; agent momentarily short
        }
        let before = balances(&ledger);
        let r = run_turn(
            &mut ledger,
            &coordination_turn(agent_id, agent_nonce, fee),
            Some(faucet_id),
        );
        assert!(matches!(r, TurnResult::Committed { .. }), "coord: {r:?}");
        agent_nonce += 1;
        skim_since_topup += fee;

        assert_eq!(
            total_delta(&before, &balances(&ledger)),
            0,
            "randomized coordination turn must be conservation-closed (Σδ == 0)"
        );

        floor = floor.min(bal(&ledger, &faucet_id));
    }

    // STANDING INVARIANT holds under any schedule.
    assert_eq!(
        ledger_total(&ledger),
        standing_before,
        "standing total invariant under randomized schedule"
    );
    // Faucet bounded below by a positive constant: the deepest it can dip is one
    // agent top-up cycle, independent of the 8000-turn length.
    assert!(
        floor >= FAUCET_START - AGENT_START - 100_000,
        "faucet bounded below (floor {floor}) — steady-state, not draining"
    );
    assert!(floor > 0, "faucet never insolvent under randomized schedule");
}
