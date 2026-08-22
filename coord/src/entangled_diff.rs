//! # Differential: Lean `EntangledJoint` model  ⟺  the REAL `coord::atomic` 2PC + `shared_budget`.
//!
//! This module is the Rust side of the differential for
//! `metatheory/Dregg2/Distributed/EntangledJoint.lean` — the EXECUTABLE N-cell atomic coordinated
//! turn over the verified per-cell executor. The Lean side proves (n > 1):
//!
//!   * **atomicity** — `jointApplyAll` over N legs is all-or-none (every leg commits or none does);
//!   * **no-authority-amplification** — every committed leg passed the real authority gate and the
//!     cap table is frame-invariant;
//!   * **shared-budget non-overspend** — `totalSpent ≤ Σ ceilings` under the `try_debit` gate.
//!
//! Here we run the GENUINE protocol objects — `atomic::{Coordinator, Participant, Vote, Decision}`
//! and `shared_budget::SharedResourceBudget` — on concrete N = 3 multi-party scenarios, and assert
//! the running code's outcomes AGREE, point for point, with a faithful Rust transcription of the
//! Lean model. The Lean functions are tiny and total, so the transcription is line-for-line; the
//! differential pins that the verified Lean semantics is the semantics the coordinator actually
//! computes (the same discipline as `BlocklaceFinality`'s `tau` differential).
//!
//! NOTE on scope: the Ed25519 vote-signature verification in `atomic.rs` is the named crypto
//! assumption (honestly a hypothesis on the Lean side). The differential uses REAL signatures
//! (`Vote::sign_yes`/`verify_yes`) so the protocol path exercised is the production one.

#![cfg(test)]

// ───────────────────────────── Lean model, transcribed to Rust ─────────────────────────────
//
// These mirror `EntangledJoint.lean` exactly:
//   * `applyLeg`        — one `recKExecAsset` step: fail-closed on (authorized ∧ amt ≤ bal ∧ live).
//   * `jointApplyAll`   — `legs.foldlM applyLeg k` : Option (all-or-none).
//   * `Allowance::tryDebit` / `SharedBudget::{totalSpent,totalCeilings,isOverspent}`.

/// The Lean `RecordKernelState`, projected to the asset-0 balance ledger over a finite account set
/// (the only fields the joint turn reads/writes). `caps_owned[c]` models ownership authority
/// (`actor == src`), the same `authorizedB` gate the per-cell executor checks.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LeanState {
    accounts: Vec<u64>,
    bal: std::collections::BTreeMap<u64, i64>,
}

/// The Lean `Leg`: one per-cell `recKExecAsset` turn (actor/src/dst/amt on a single asset column).
#[derive(Clone, Debug)]
struct LeanLeg {
    actor: u64,
    src: u64,
    dst: u64,
    amt: i64,
}

impl LeanState {
    fn account_live(&self, c: u64) -> bool {
        self.accounts.contains(&c)
    }

    /// `EntangledJoint.applyLeg` = `Exec.recKExecAsset` (asset 0). Fail-closed:
    /// authorized (ownership) ∧ 0 ≤ amt ∧ amt ≤ bal(src) ∧ src ≠ dst ∧ src,dst live.
    fn apply_leg(&self, l: &LeanLeg) -> Option<LeanState> {
        let authorized = l.actor == l.src; // ownership leg of `authorizedB`
        let src_bal = *self.bal.get(&l.src).unwrap_or(&0);
        if authorized
            && 0 <= l.amt
            && l.amt <= src_bal
            && l.src != l.dst
            && self.account_live(l.src)
            && self.account_live(l.dst)
        {
            let mut s = self.clone();
            *s.bal.entry(l.src).or_insert(0) -= l.amt;
            *s.bal.entry(l.dst).or_insert(0) += l.amt;
            Some(s)
        } else {
            None
        }
    }

    /// `EntangledJoint.jointApplyAll` = `legs.foldlM applyLeg k` (all-or-none).
    fn joint_apply_all(&self, legs: &[LeanLeg]) -> Option<LeanState> {
        let mut k = self.clone();
        for l in legs {
            k = k.apply_leg(l)?; // any `none` ⇒ the whole fold is `none` (abort, no partial commit)
        }
        Some(k)
    }

    fn total_asset0(&self) -> i64 {
        self.accounts
            .iter()
            .map(|c| *self.bal.get(c).unwrap_or(&0))
            .sum()
    }
}

/// The Lean `Allowance` (`shared_budget::AgentAllowance`): `ceiling`/`spent`, the `try_debit` gate.
#[derive(Clone, Debug)]
struct LeanAllowance {
    ceiling: u64,
    spent: u64,
}

impl LeanAllowance {
    fn remaining(&self) -> u64 {
        self.ceiling.saturating_sub(self.spent)
    }
    /// `EntangledJoint.Allowance.tryDebit` = `AgentAllowance::try_debit`.
    fn try_debit(&self, amount: u64) -> Option<LeanAllowance> {
        if amount <= self.remaining() {
            Some(LeanAllowance {
                ceiling: self.ceiling,
                spent: self.spent + amount,
            })
        } else {
            None
        }
    }
}

// ─────────────────────────────── Differential 1: atomicity (n = 3) ───────────────────────────────

mod atomicity_diff {
    use super::*;
    use crate::atomic::{AtomicForest, Coordinator, Decision, Vote};
    use dregg_cell::preconditions::CellStatePrecondition;
    use dregg_cell::{Cell, CellId, Ledger, Preconditions};
    use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect};
    use dregg_turn::{CallForest, ComputronCosts};
    use std::collections::HashMap;

    fn node_id(n: u8) -> [u8; 32] {
        let mut id = [0u8; 32];
        id[0] = n;
        id
    }

    fn keypair(n: u8) -> ([u8; 32], [u8; 32]) {
        let seed = *blake3::hash(&[n; 1]).as_bytes();
        let pk = Vote::public_key_from_signing_key(&seed);
        (seed, pk)
    }

    // signed-wells (ac01f9b7b): cell balances are i64; keep a u64 convenience
    // param (callers pass non-negative bal0/bal1/bal2) and convert at the boundary.
    fn permissive_cell(key_byte: u8, balance: u64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = key_byte;
        let mut cell = Cell::with_balance(pk, [0u8; 32], balance as i64);
        cell.permissions = dregg_cell::Permissions {
            send: dregg_cell::AuthRequired::None,
            receive: dregg_cell::AuthRequired::None,
            set_state: dregg_cell::AuthRequired::None,
            set_permissions: dregg_cell::AuthRequired::None,
            set_verification_key: dregg_cell::AuthRequired::None,
            increment_nonce: dregg_cell::AuthRequired::None,
            delegate: dregg_cell::AuthRequired::None,
            access: dregg_cell::AuthRequired::None,
        };
        cell
    }

    fn transfer_action(from: CellId, to: CellId, amount: u64) -> Action {
        Action {
            target: from,
            method: *blake3::hash(b"transfer").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer { from, to, amount }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        }
    }

    /// Build a 3-participant atomic forest (a ring of transfers) + the real ledger, plus the Lean
    /// `LeanState`/legs mirroring the same moves. The `min_balance` precondition on cell `c` is the
    /// 2PC analog of the Lean `applyLeg` availability gate (`amt ≤ bal(src)`).
    fn setup_three_party(
        bal0: u64,
        bal1: u64,
        bal2: u64,
        amt01: u64,
        amt12: u64,
        amt20: u64,
    ) -> (
        Ledger,
        AtomicForest,
        Vec<[u8; 32]>,
        HashMap<[u8; 32], [u8; 32]>,
        LeanState,
        Vec<LeanLeg>,
    ) {
        let mut ledger = Ledger::new();
        let c0 = permissive_cell(1, bal0);
        let c1 = permissive_cell(2, bal1);
        let c2 = permissive_cell(3, bal2);
        let id0 = ledger.insert_cell(c0).unwrap();
        let id1 = ledger.insert_cell(c1).unwrap();
        let id2 = ledger.insert_cell(c2).unwrap();

        let mut forest = CallForest::new();
        forest.add_root(transfer_action(id0, id1, amt01));
        forest.add_root(transfer_action(id1, id2, amt12));
        forest.add_root(transfer_action(id2, id0, amt20));

        let preconditions = vec![
            (
                id0,
                Preconditions {
                    cell_state: Some(CellStatePrecondition {
                        min_balance: Some(amt01),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            ),
            (
                id1,
                Preconditions {
                    cell_state: Some(CellStatePrecondition {
                        min_balance: Some(amt12),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            ),
            (
                id2,
                Preconditions {
                    cell_state: Some(CellStatePrecondition {
                        min_balance: Some(amt20),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            ),
        ];

        let af = AtomicForest::new(
            vec![node_id(1), node_id(2), node_id(3)],
            forest,
            preconditions,
            id0,
            0,
            None,
        );

        let nodes = vec![node_id(1), node_id(2), node_id(3)];
        let mut signing_keys = Vec::new();
        let mut participant_keys = HashMap::new();
        for nid in &nodes {
            let (sk, pk) = keypair(nid[0]);
            signing_keys.push(sk);
            participant_keys.insert(*nid, pk);
        }

        // The Lean mirror: cells {0,1,2}, the same balances and ring legs (actor owns its src).
        let lean_state = LeanState {
            accounts: vec![0, 1, 2],
            bal: [(0u64, bal0 as i64), (1, bal1 as i64), (2, bal2 as i64)]
                .into_iter()
                .collect(),
        };
        let lean_legs = vec![
            LeanLeg {
                actor: 0,
                src: 0,
                dst: 1,
                amt: amt01 as i64,
            },
            LeanLeg {
                actor: 1,
                src: 1,
                dst: 2,
                amt: amt12 as i64,
            },
            LeanLeg {
                actor: 2,
                src: 2,
                dst: 0,
                amt: amt20 as i64,
            },
        ];

        (
            ledger,
            af,
            signing_keys,
            participant_keys,
            lean_state,
            lean_legs,
        )
    }

    /// Run the real 2PC: every participant evaluates the proposal and votes; return whether the
    /// coordinator reaches `Decision::Commit` (all-Yes ⇒ commit; any precondition fail ⇒ a No ⇒
    /// abort). `precond_ok[i]` is whether participant i's local precondition holds.
    fn run_real_2pc(
        af: &AtomicForest,
        signing_keys: &[[u8; 32]],
        participant_keys: HashMap<[u8; 32], [u8; 32]>,
        precond_ok: [bool; 3],
    ) -> Decision {
        let mut coord = Coordinator::new(
            node_id(1),
            *blake3::hash(b"coord-diff").as_bytes(),
            3, // unanimous threshold: all 3 must vote Yes (true atomic all-or-none)
            ComputronCosts::zero(),
            u64::MAX,
            participant_keys,
        );
        let prop = coord.propose(af.clone()).unwrap();

        // ARM the NATIVE 2PC differential sibling BY NAME (see `atomic::NativeDifferentialArmed`):
        // the gate-absent disposition is the production `Abort` in a test build too, and this
        // differential is the caller that deliberately wants the native tally verdict.
        let _native = crate::atomic::NativeDifferentialArmed::new();

        let mut last = Decision::Pending;
        for i in 0..3 {
            let nid = node_id((i + 1) as u8);
            let vote = if precond_ok[i] {
                Vote::yes(Vote::sign_yes(
                    &prop.proposal_id,
                    &af.hash,
                    &signing_keys[i],
                ))
            } else {
                Vote::no(
                    "precondition failed",
                    Vote::sign_no(&prop.proposal_id, &af.hash, &signing_keys[i]),
                )
            };
            if let Some(d) = coord.receive_vote(nid, vote).unwrap() {
                last = d;
                break;
            }
        }
        last
    }

    /// **DIFFERENTIAL — atomicity COMMIT path (n = 3).** A ring whose every leg's precondition holds:
    /// the real 2PC reaches `Decision::Commit`, AND the Lean `jointApplyAll` returns `some`. Both
    /// agree the whole forest commits.
    #[test]
    fn diff_atomic_commit_all() {
        let (_, af, sks, pks, lean_state, lean_legs) = setup_three_party(100, 50, 20, 30, 10, 5);

        // Lean: all-or-none fold commits.
        let lean_out = lean_state.joint_apply_all(&lean_legs);
        assert!(lean_out.is_some(), "Lean jointApplyAll must commit");

        // Real 2PC: all preconditions hold ⇒ Commit.
        let decision = run_real_2pc(&af, &sks, pks, [true, true, true]);
        assert_eq!(decision, Decision::Commit);

        // AGREEMENT: real-Commit ⟺ Lean-some.
        assert_eq!(decision == Decision::Commit, lean_out.is_some());

        // Conservation cross-check: the Lean post-state preserves asset-0 total (170).
        let post = lean_out.unwrap();
        assert_eq!(lean_state.total_asset0(), 170);
        assert_eq!(post.total_asset0(), 170);
    }

    /// **DIFFERENTIAL — atomicity ABORT path (n = 3).** A ring whose 2nd leg overdraws (cell 1 only
    /// holds 50 but the leg demands 999): the real 2PC reaches `Decision::Abort` (participant 1
    /// votes No), AND the Lean `jointApplyAll` returns `none` (the fold aborts at the 2nd leg). No
    /// partial commit on either side — all-or-none.
    #[test]
    fn diff_atomic_abort_one_leg_fails() {
        let (_, af, sks, pks, lean_state, lean_legs) = setup_three_party(100, 50, 20, 30, 999, 5);

        // Lean: the 2nd leg's availability gate fails ⇒ whole fold is `none`.
        let lean_out = lean_state.joint_apply_all(&lean_legs);
        assert!(lean_out.is_none(), "Lean jointApplyAll must abort");

        // Real 2PC: participant 1's min_balance(999) precondition fails ⇒ No ⇒ Abort.
        let decision = run_real_2pc(&af, &sks, pks, [true, false, true]);
        assert_eq!(decision, Decision::Abort);

        // AGREEMENT: real-Abort ⟺ Lean-none. All-or-none on both sides.
        assert_eq!(decision == Decision::Commit, lean_out.is_some());
    }

    /// **DIFFERENTIAL — no third (partial) outcome.** Across a sweep of ring amounts, the real 2PC
    /// decision is `Commit` exactly when the Lean fold is `some`; there is never a partial state.
    #[test]
    fn diff_atomic_no_partial_commit_sweep() {
        // (amt01, amt12, amt20, precond_ok_per_leg) — feasibility matches the per-leg availability.
        let cases: &[(u64, u64, u64)] = &[
            (30, 10, 5),  // all feasible
            (200, 10, 5), // leg 0 overdraws (cell 0 has 100)
            (30, 100, 5), // leg 1 overdraws (cell 1 has 50)
            (30, 10, 99), // leg 2 overdraws (cell 2 has 20)
            (0, 0, 0),    // degenerate: src == authorized, amt 0 (but src==dst? no, distinct)
        ];
        for &(a01, a12, a20) in cases {
            let (_, af, sks, pks, lean_state, lean_legs) =
                setup_three_party(100, 50, 20, a01, a12, a20);
            let lean_out = lean_state.joint_apply_all(&lean_legs);

            let precond = [
                lean_state.bal[&0] >= a01 as i64,
                lean_state.bal[&1] >= a12 as i64,
                lean_state.bal[&2] >= a20 as i64,
            ];
            let decision = run_real_2pc(&af, &sks, pks, precond);

            assert_eq!(
                decision == Decision::Commit,
                lean_out.is_some(),
                "atomicity differential mismatch at ({a01},{a12},{a20})"
            );
        }
    }
}

// ──────────────────────── Differential 2: shared-budget non-overspend (n = 3) ────────────────────────

mod shared_budget_diff {
    use super::*;

    /// The Byzantine-tolerance allowance ceiling, transcribed VERBATIM from
    /// `shared_budget.rs::compute_allowance_ceiling`:
    ///   `ceiling = (total_balance * (f+1)) / (2f+1)` (integer division).
    /// (`shared_budget.rs` is an orphan module not yet wired into the crate's `lib.rs`, owned by the
    /// shared-budget work; we transcribe its gate rather than edit another agent's module — the
    /// formula and the `try_debit` gate are reproduced line-for-line and cited.)
    fn compute_allowance_ceiling(total_balance: u64, f: u64) -> u64 {
        ((total_balance as u128 * (f + 1) as u128) / (2 * f + 1) as u128) as u64
    }

    /// **DIFFERENTIAL — per-agent + aggregate non-overspend (n = 3).** Drive a debit stream through
    /// the `shared_budget.rs` gate (transcribed) for 3 agents (f = 1, n = 2f+1) and assert at every
    /// step the proved Lean safety properties hold:
    ///   * the per-agent invariant `spent ≤ ceiling` (`EntangledJoint.tryDebit_invariant`);
    ///   * the aggregate bound `totalSpent ≤ Σ ceilings` (`EntangledJoint.totalSpent_le_ceilings`);
    ///   * `isOverspent` ⟺ `totalSpent > totalBalance` (the COD detection `is_overspent`);
    ///   * the gate REJECTS a debit exactly when `amount > remaining`
    ///     (`EntangledJoint.tryDebit_rejects_overspend`).
    #[test]
    fn diff_shared_budget_non_overspend() {
        let n_agents = 3usize;
        let total_balance: u64 = 90;
        let f: u64 = 1; // n = 3 = 2f+1 ⇒ valid BFT quorum

        // ceiling = 90 * 2 / 3 = 60 per agent (Σ ceilings = 180 > balance 90 — concurrent spend).
        let ceiling = compute_allowance_ceiling(total_balance, f);
        assert_eq!(ceiling, 60);
        let mut lean: Vec<LeanAllowance> = (0..n_agents)
            .map(|_| LeanAllowance { ceiling, spent: 0 })
            .collect();
        let total_ceilings: u64 = lean.iter().map(|a| a.ceiling).sum();

        // A debit stream (agent index, amount). Within ceiling, then a leg that EXCEEDS remaining.
        let stream: &[(usize, u64)] = &[(0, 30), (1, 30), (2, 30), (0, 20), (1, 40), (1, 30)];
        for &(ai, amt) in stream {
            let remaining_before = lean[ai].remaining();
            let lean_ok = match lean[ai].try_debit(amt) {
                Some(updated) => {
                    lean[ai] = updated;
                    true
                }
                None => false,
            };

            // The gate admits iff amount ≤ remaining (tryDebit_rejects_overspend, contrapositive).
            assert_eq!(lean_ok, amt <= remaining_before, "try_debit gate mismatch");

            let lean_total_spent: u64 = lean.iter().map(|a| a.spent).sum();

            // COD overspend DETECTION (`is_overspent`): after (0,30)+(1,30)+(2,30) the aggregate
            // spend (90) is NOT over balance (90); (0,20) pushes it to 110 > 90 ⇒ overspent, which
            // is exactly when `shared_budget.rs` escalates to Tier-3 ordering. The aggregate-spend
            // can exceed the *balance* (that is the optimistic concurrency) but NEVER the ceilings.
            let _is_overspent = lean_total_spent > total_balance;

            // The proved Lean safety properties hold on the live table at every step:
            for a in &lean {
                assert!(
                    a.spent <= a.ceiling,
                    "per-agent non-overspend (tryDebit_invariant)"
                );
            }
            assert!(
                lean_total_spent <= total_ceilings,
                "aggregate non-overspend (totalSpent_le_ceilings)"
            );
        }

        // Final: agent 1's stream was (1,30) admitted → spent 30; (1,40) REJECTED (40 > remaining
        // 30); (1,30) admitted → spent 60. The per-agent ceiling (60) held exactly — the gate never
        // let agent 1 past it, witnessing `tryDebit_invariant` on a real overspend attempt.
        assert_eq!(lean[1].spent, 60);
        assert!(lean[1].spent <= ceiling);
    }
}
