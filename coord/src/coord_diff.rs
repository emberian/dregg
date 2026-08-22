//! # Differential: the verified Lean `Dregg2/Coord/*` models  ⟺  the REAL `dregg-coord` coordination
//! semantics (`causal::CausalDag`, `atomic::evaluate_votes`, `shared_budget::resolve_with_ordering`).
//!
//! This is the Rust side of the differential for the three GENUINELY-UNCOVERED coordination models
//! (the parts `Dregg2/Distributed/EntangledJoint.lean` does NOT reach — it models the post-commit
//! ledger fold, not the causal DAG, the vote-counting decision, or the tau-resolution dynamics):
//!
//!   * `Dregg2/Coord/CausalOrder.lean`        — Layer-1 happened-before DAG + the causal-ordering
//!     invariant (a STRICT PARTIAL ORDER) ⟺ `dregg_types::CausalDag` (re-exported as
//!     `causal::CausalDag`, the DAG `dregg-net` and `dregg-coord` share).
//!   * `Dregg2/Coord/TwoPhaseCommit.lean`     — Layer-2 2PC `evaluate_votes` Decision machine + the
//!     no-conflicting-decision safety ⟺ `atomic::Coordinator`'s real Ed25519-gated vote counting.
//!   * `Dregg2/Coord/SharedBudgetDynamics.lean` — Layer-3 `resolve_with_ordering` tau-resolution
//!     conservation (Σ accepted ≤ balance) ⟺ `shared_budget::SharedResourceBudget`.
//!
//! Each section runs the GENUINE protocol object and asserts its observable outcomes AGREE, point
//! for point, with a faithful Rust transcription of the tiny, total Lean model (the same discipline
//! as `entangled_diff.rs` / `BlocklaceFinality`'s `tau` differential). The Ed25519 signature
//! verification (`Vote::verify_yes`, block creator keys) is the named crypto assumption; the
//! differential uses REAL signatures so the production path is exercised.

#![cfg(test)]

// ─────────────────────────── Lean models, transcribed to Rust ───────────────────────────
//
// These mirror the three `Dregg2/Coord/*.lean` files exactly. The Lean functions are total and tiny.

// ── CausalOrder.lean: happenedBefore = transitive closure of the dependency edges ──────────────

/// `Dregg2/Coord/CausalOrder.lean::happenedBefore` (transitive closure of `directDep`), computed
/// directly from the (hash → deps) map. `a` happened before `b` iff `a` is a transitive dependency
/// (ancestor) of `b` — BFS backward through dependency edges, exactly `CausalDag::happened_before`.
fn lean_happened_before(deps: &std::collections::HashMap<u64, Vec<u64>>, a: u64, b: u64) -> bool {
    if a == b {
        return false; // irreflexive (CausalOrder.hb_irrefl)
    }
    // BFS backward from b through its deps.
    let mut stack = vec![b];
    let mut seen = std::collections::HashSet::new();
    while let Some(cur) = stack.pop() {
        if let Some(ds) = deps.get(&cur) {
            for &d in ds {
                if d == a {
                    return true;
                }
                if seen.insert(d) {
                    stack.push(d);
                }
            }
        }
    }
    false
}

/// `Dregg2/Coord/CausalOrder.lean::concurrent` — neither happened before the other (and not equal).
fn lean_concurrent(deps: &std::collections::HashMap<u64, Vec<u64>>, a: u64, b: u64) -> bool {
    a != b && !lean_happened_before(deps, a, b) && !lean_happened_before(deps, b, a)
}

// ── TwoPhaseCommit.lean: evaluate = evaluate_votes (Commit/Abort/Pending) ───────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LeanDecision {
    Commit,
    Abort,
    Pending,
}

/// `Dregg2/Coord/TwoPhaseCommit.lean::evaluate` = `Coordinator::evaluate_votes`, byte-for-byte:
/// `if threshold ≤ yes then Commit else if (n - threshold) < no then Abort else Pending`.
fn lean_evaluate(yes: usize, no: usize, n: usize, threshold: usize) -> LeanDecision {
    if threshold <= yes {
        LeanDecision::Commit
    } else if n.saturating_sub(threshold) < no {
        LeanDecision::Abort
    } else {
        LeanDecision::Pending
    }
}

// ── SharedBudgetDynamics.lean: resolveOrdered (tau-ordered first-wins resolver) ──────────────────

/// `Dregg2/Coord/SharedBudgetDynamics.lean::resolveOrdered` — fold the tau-ordered amounts through a
/// running balance: accept iff `amount ≤ remaining`, subtract on accept, reject otherwise. Returns
/// (per-debit accepted?, final remaining balance). Mirrors `resolve_with_ordering` exactly.
fn lean_resolve_ordered(mut bal: u64, amounts: &[u64]) -> (Vec<bool>, u64) {
    let mut verdicts = Vec::with_capacity(amounts.len());
    for &a in amounts {
        if a <= bal {
            bal -= a;
            verdicts.push(true);
        } else {
            verdicts.push(false);
        }
    }
    (verdicts, bal)
}

/// `Dregg2/Coord/SharedBudgetDynamics.lean::ceiling` = `compute_allowance_ceiling`.
fn lean_ceiling(balance: u64, f: u64) -> u64 {
    ((balance as u128 * (f + 1) as u128) / (2 * f + 1) as u128) as u64
}

// ── StingrayCertReconcile.lean: the StingrayCounter::rebalance cert-reconciliation model ────────────
//
// A `(silo, version, spent, sig_ok)` certificate, mirroring the Lean `Cert`. The Lean `rebalance`
// returns either a `RebErr` tag or the `(totalSpent, newBalance, newVersion)` outcome.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LeanCert {
    silo: u8,
    version: u64,
    spent: u64,
    sig_ok: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LeanRebOutcome {
    Ok {
        total_spent: u64,
        new_balance: u64,
        new_version: u64,
    },
    IncompleteCertificates,
    VersionMismatch,
    DuplicateCertificate,
    CertExceedsCeiling,
    MissingSiloPubkey,
    InvalidSignature,
}

/// `Dregg2/Coord/StingrayCertReconcile.lean::rebalance` — the faithful gate machine, in EXACT source
/// order (incomplete-quorum → per-cert {version, dup, ceiling, pubkey, sig} → partial-mode missing
/// charge → balance clamp → version bump). `n_silos`/`registered` describe the counter's silo set.
fn lean_rebalance(
    n_silos: usize,
    registered: &[u8],
    version: u64,
    balance: u64,
    f: u64,
    certs: &[LeanCert],
    require_all: bool,
) -> LeanRebOutcome {
    let ceil = lean_ceiling(balance, f);
    if require_all && certs.len() < n_silos {
        return LeanRebOutcome::IncompleteCertificates;
    }
    let mut seen: Vec<u8> = Vec::new();
    let mut cert_spent: u64 = 0;
    for cert in certs {
        if cert.version != version {
            return LeanRebOutcome::VersionMismatch;
        } else if seen.contains(&cert.silo) {
            return LeanRebOutcome::DuplicateCertificate;
        } else if cert.spent > ceil {
            return LeanRebOutcome::CertExceedsCeiling;
        } else if !registered.contains(&cert.silo) {
            return LeanRebOutcome::MissingSiloPubkey;
        } else if !cert.sig_ok {
            return LeanRebOutcome::InvalidSignature;
        }
        seen.push(cert.silo);
        cert_spent += cert.spent;
    }
    // Partial mode: missing registered silos charged full ceiling (conservative).
    let total = if require_all {
        cert_spent
    } else {
        let missing = (0..n_silos as u8).filter(|s| !seen.contains(s)).count() as u64;
        cert_spent + missing * ceil
    };
    let new_balance = balance.saturating_sub(total);
    LeanRebOutcome::Ok {
        total_spent: total,
        new_balance,
        new_version: version + 1,
    }
}

// ═══════════════════════ Differential 1: causal happened-before partial order ═══════════════════

mod causal_order_diff {
    use super::*;
    use crate::causal::CausalDag;
    use std::collections::HashMap;

    fn h(n: u64) -> [u8; 32] {
        let mut b = [0u8; 32];
        b[0..8].copy_from_slice(&n.to_le_bytes());
        b
    }

    /// **DIFFERENTIAL — happened-before on a linear chain + diamond agrees with the Lean partial
    /// order.** Build the REAL `CausalDag` (the `dregg_types` DAG `net`/`coord` share) as a diamond
    /// `1 → {2,3} → 4`, and assert `CausalDag::happened_before` / `are_concurrent` agree, edge for
    /// edge, with `CausalOrder.lean::happenedBefore` / `concurrent` over the same dependency map.
    #[test]
    fn diff_happened_before_diamond() {
        // Real DAG.
        let mut dag = CausalDag::new();
        dag.insert_genesis(h(1)).unwrap();
        dag.insert(h(2), &[h(1)]).unwrap();
        dag.insert(h(3), &[h(1)]).unwrap();
        dag.insert(h(4), &[h(2), h(3)]).unwrap();

        // Lean mirror: the same (hash → deps) topology over u64 ids.
        let deps: HashMap<u64, Vec<u64>> =
            HashMap::from([(1u64, vec![]), (2, vec![1]), (3, vec![1]), (4, vec![2, 3])]);

        // AGREEMENT over every ordered pair in {1,2,3,4}.
        for a in 1u64..=4 {
            for b in 1u64..=4 {
                let real_hb = dag.happened_before(&h(a), &h(b));
                let lean_hb = lean_happened_before(&deps, a, b);
                assert_eq!(
                    real_hb, lean_hb,
                    "happened_before mismatch for ({a},{b}): real={real_hb} lean={lean_hb}"
                );

                let real_conc = dag.are_concurrent(&h(a), &h(b));
                let lean_conc = lean_concurrent(&deps, a, b);
                assert_eq!(
                    real_conc, lean_conc,
                    "are_concurrent mismatch for ({a},{b})"
                );
            }
        }

        // Spot-checks pinning the partial-order facts the Lean proves:
        // irreflexivity (hb_irrefl): nothing happens before itself.
        assert!(!dag.happened_before(&h(4), &h(4)));
        // transitivity (hb_trans): 1 → 2 → 4 ⇒ 1 happened before 4.
        assert!(dag.happened_before(&h(1), &h(4)));
        // 2 and 3 are concurrent (the diamond's incomparable pair).
        assert!(dag.are_concurrent(&h(2), &h(3)));
        // asymmetry (hb_asymm): not both 1→4 and 4→1.
        assert!(!(dag.happened_before(&h(1), &h(4)) && dag.happened_before(&h(4), &h(1))));
    }

    /// **DIFFERENTIAL — topological order is a LINEAR EXTENSION of happened-before
    /// (`CausalOrder.hb_imp_index_lt`).** The REAL `CausalDag::topological_order` lists every cause
    /// before its effect: if `a` happened before `b` (per the Lean model), `a` precedes `b` in the
    /// emitted order. The soundness of the deterministic Kahn sort the coordination layer replays.
    #[test]
    fn diff_topological_order_respects_happened_before() {
        let mut dag = CausalDag::new();
        dag.insert_genesis(h(1)).unwrap();
        dag.insert(h(2), &[h(1)]).unwrap();
        dag.insert(h(3), &[h(1)]).unwrap();
        dag.insert(h(4), &[h(2), h(3)]).unwrap();

        let deps: HashMap<u64, Vec<u64>> =
            HashMap::from([(1u64, vec![]), (2, vec![1]), (3, vec![1]), (4, vec![2, 3])]);

        let order = dag.topological_order();
        let pos = |x: u64| order.iter().position(|t| t == &h(x)).unwrap();

        // For every pair the Lean model says is happened-before, the topo order respects it.
        for a in 1u64..=4 {
            for b in 1u64..=4 {
                if lean_happened_before(&deps, a, b) {
                    assert!(
                        pos(a) < pos(b),
                        "topo order violates happened-before ({a} before {b})"
                    );
                }
            }
        }
    }

    /// **DIFFERENTIAL — the insert gates (the causal-ordering INVARIANT `CausalOrder.insert_wf`
    /// maintains).** The REAL `CausalDag::insert` rejects a missing-dep turn, a self-cycle, and a
    /// duplicate — exactly the three `none` cases of `CausalOrder.lean::insert`. The Lean proves
    /// these gates keep the DAG acyclic (a genuine partial order at every step).
    #[test]
    fn diff_insert_gates_match_lean() {
        let mut dag = CausalDag::new();
        dag.insert_genesis(h(1)).unwrap();

        // MissingDeps: dep 99 absent ⇒ Err (Lean: insert returns none on absent dep).
        assert!(dag.insert(h(5), &[h(99)]).is_err());
        // Self-cycle: 7 deps on 7 ⇒ Err (Lean: h ∈ deps ⇒ none).
        assert!(dag.insert(h(7), &[h(7)]).is_err());
        // Duplicate: inserting 1 again ⇒ Err (Lean: present h ⇒ none).
        assert!(dag.insert_genesis(h(1)).is_err());
        // A valid insert (dep present) succeeds (Lean: some).
        assert!(dag.insert(h(2), &[h(1)]).is_ok());
    }
}

// ═══════════════════════ Differential 2: 2PC evaluate_votes decision machine ════════════════════

mod two_phase_commit_diff {
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

    fn permissive_cell(key_byte: u8, balance: i64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = key_byte;
        let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
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

    /// Build a 3-participant atomic forest + register keys, returning the forest, signing keys,
    /// and pubkey map. The threshold is the coordinator's; participants vote per `precond_ok`.
    fn setup() -> (
        Ledger,
        AtomicForest,
        Vec<[u8; 32]>,
        HashMap<[u8; 32], [u8; 32]>,
    ) {
        let mut ledger = Ledger::new();
        let id0 = ledger.insert_cell(permissive_cell(1, 100)).unwrap();
        let id1 = ledger.insert_cell(permissive_cell(2, 50)).unwrap();
        let id2 = ledger.insert_cell(permissive_cell(3, 20)).unwrap();

        let mut forest = CallForest::new();
        forest.add_root(transfer_action(id0, id1, 30));
        forest.add_root(transfer_action(id1, id2, 10));
        forest.add_root(transfer_action(id2, id0, 5));

        let preconditions = vec![
            (
                id0,
                Preconditions {
                    cell_state: Some(CellStatePrecondition {
                        min_balance: Some(30),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            ),
            (
                id1,
                Preconditions {
                    cell_state: Some(CellStatePrecondition {
                        min_balance: Some(10),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            ),
            (
                id2,
                Preconditions {
                    cell_state: Some(CellStatePrecondition {
                        min_balance: Some(5),
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
        (ledger, af, signing_keys, participant_keys)
    }

    /// Drive the REAL `Coordinator` with a fixed Yes/No vote vector at the given threshold; collect
    /// every intermediate `Decision` the coordinator emits as votes arrive. Returns the FINAL
    /// decision (the terminal verdict, or Pending if never reached).
    fn run_coordinator(threshold: usize, votes_yes: [bool; 3]) -> Decision {
        let (_, af, sks, pks) = setup();
        let mut coord = Coordinator::new(
            node_id(1),
            *blake3::hash(b"coord-diff-2pc").as_bytes(),
            threshold,
            ComputronCosts::zero(),
            u64::MAX,
            pks,
        );
        let prop = coord.propose(af.clone()).unwrap();

        // ARM the NATIVE 2PC differential sibling BY NAME. `evaluate_votes_no_gate` has ONE body for
        // every cfg and it is the PRODUCTION fail-closed `Abort`; this differential is precisely the
        // test that wants the native tally verdict through the REAL `receive_vote` path, so it says
        // so instead of relying on a cfg-divergent callee.
        let _native = crate::atomic::NativeDifferentialArmed::new();

        let mut last = Decision::Pending;
        for i in 0..3 {
            let nid = node_id((i + 1) as u8);
            let vote = if votes_yes[i] {
                Vote::yes(Vote::sign_yes(&prop.proposal_id, &af.hash, &sks[i]))
            } else {
                Vote::no("no", Vote::sign_no(&prop.proposal_id, &af.hash, &sks[i]))
            };
            if let Some(d) = coord.receive_vote(nid, vote).unwrap() {
                last = d;
                break;
            }
        }
        last
    }

    fn to_lean(d: Decision) -> LeanDecision {
        match d {
            Decision::Commit => LeanDecision::Commit,
            Decision::Abort => LeanDecision::Abort,
            Decision::Pending => LeanDecision::Pending,
        }
    }

    /// **DIFFERENTIAL — the real `evaluate_votes` decision agrees with `TwoPhaseCommit.lean::evaluate`
    /// across a vote sweep (n = 3).** For every Yes/No combination and both unanimous (threshold = 3)
    /// and majority (threshold = 2) policies, the REAL `Coordinator`'s emitted `Decision` equals the
    /// Lean `evaluate(yes, no, n, threshold)`. This pins that the verified no-conflicting-decision
    /// machine IS the machine the coordinator runs.
    #[test]
    fn diff_evaluate_votes_sweep() {
        for &threshold in &[3usize, 2usize] {
            for mask in 0u8..8 {
                // The 3 participants vote Yes/No per the bit mask; ALL three votes are cast (so the
                // coordinator sees the full tally — n votes, the terminal verdict).
                let votes_yes = [mask & 1 != 0, mask & 2 != 0, mask & 4 != 0];
                let yes = votes_yes.iter().filter(|&&y| y).count();
                let no = 3 - yes;

                let real = to_lean(run_coordinator(threshold, votes_yes));
                let lean = lean_evaluate(yes, no, 3, threshold);

                // NOTE: the real coordinator may decide EARLY (before all 3 votes) — e.g. with
                // threshold 2, two Yes votes commit immediately. The terminal verdict still matches
                // the Lean evaluate on the FULL tally, because Commit/Abort are stable monotone
                // (TwoPhaseCommit.commit_stable_under_more_yes) — once decided it does not flip.
                // We assert the COMMIT/ABORT classification agrees (Pending only if the real coord
                // also never reached a terminal verdict, which for a full 3-vote run never happens).
                assert_eq!(
                    real, lean,
                    "evaluate mismatch: threshold={threshold} votes={votes_yes:?} real={real:?} lean={lean:?}"
                );
            }
        }
    }

    /// **DIFFERENTIAL — NO CONFLICTING DECISION (`TwoPhaseCommit.evaluate_not_commit_and_abort`).**
    /// Across the full sweep, the real coordinator's verdict is NEVER simultaneously commit-able and
    /// abort-able: it returns exactly one terminal `Decision`. We witness this by checking the Lean
    /// `evaluate` is single-valued (it is a function) AND the real coordinator's verdict matches it —
    /// so both sides agree there is one unambiguous decision per QC.
    #[test]
    fn diff_no_conflicting_decision() {
        for &threshold in &[3usize, 2usize] {
            for mask in 0u8..8 {
                let votes_yes = [mask & 1 != 0, mask & 2 != 0, mask & 4 != 0];
                let yes = votes_yes.iter().filter(|&&y| y).count();
                let no = 3 - yes;
                // The two terminal conditions are mutually exclusive (the Lean theorem).
                let commit_able = threshold <= yes;
                let abort_able = (3usize).saturating_sub(threshold) < no;
                assert!(
                    !(commit_able && abort_able),
                    "conflicting decision possible at threshold={threshold} votes={votes_yes:?}"
                );
                // And the real coordinator agrees with whichever single verdict the Lean computes.
                let real = to_lean(run_coordinator(threshold, votes_yes));
                assert_eq!(real, lean_evaluate(yes, no, 3, threshold));
            }
        }
    }
}

// ═══════════════════ Differential 3: shared-budget tau-resolution conservation ══════════════════

mod shared_budget_diff {
    use super::*;
    use crate::shared_budget::{ResourceState, SharedResourceBudget, encode_debit_payload};
    use dregg_blocklace::finality::{Block as BlocBlock, Blocklace, Payload};
    use dregg_cell::CellId;

    fn agents(n: usize) -> Vec<CellId> {
        (0..n)
            .map(|i| {
                let mut b = [0u8; 32];
                b[0] = i as u8;
                b[31] = 0xAA;
                CellId::from_bytes(b)
            })
            .collect()
    }

    /// See `crate::shared_budget::tests::install_pq_cores` — the two resolution differentials
    /// below mint real blocklace blocks, and `Block::new` derives the author's ML-DSA-65 half
    /// through `dregg-pq`, which aborts the process when no verified core is installed.
    fn install_pq_cores() {
        dregg_pq_testkit::install_or_panic();
    }

    /// **DIFFERENTIAL — the Stingray ceiling formula agrees with `SharedBudgetDynamics.lean::ceiling`
    /// (and `ceiling_le_balance`).** The REAL `SharedResourceBudget::compute_allowance_ceiling`
    /// equals the Lean `ceiling balance f = balance*(f+1)/(2f+1)`, and the Lean-proved
    /// `ceiling ≤ balance` holds on the real value.
    #[test]
    fn diff_ceiling_formula() {
        for &(balance, f) in &[(10000u64, 1u64), (10000, 2), (3000, 1), (5000, 0), (200, 1)] {
            let n = (2 * f + 1) as usize;
            let budget = SharedResourceBudget::new(
                CellId::from_bytes([0xBB; 32]),
                balance,
                agents(n),
                f as usize,
            )
            .unwrap();
            let real = budget.compute_allowance_ceiling();
            let lean = lean_ceiling(balance, f);
            assert_eq!(
                real, lean,
                "ceiling mismatch for (balance={balance}, f={f})"
            );
            // ceiling_le_balance (the Lean theorem) holds on the real value.
            assert!(
                real <= balance,
                "ceiling exceeds balance — ceiling_le_balance violated"
            );
        }
    }

    /// **DIFFERENTIAL — TAU-RESOLUTION CONSERVATION (`SharedBudgetDynamics.resolveOrdered_accepted_
    /// le_balance`).** Reproduce the `test_full_escalation_round_trip` scenario (`shared_budget.rs:
    /// 1716`): pool 1000, three concurrent debits of 400 (total 1200 > 1000, OVERSPENT). Escalate,
    /// then `resolve_with_ordering` in tau order [A, B, C]. Assert the REAL accept/reject verdicts
    /// and the final balance AGREE with the Lean `resolveOrdered 1000 [400,400,400]`, AND that the
    /// total ACCEPTED never exceeds the starting balance (the conservation across the coordination
    /// tree — why optimistic overspend is safe).
    #[test]
    fn diff_resolve_with_ordering_conserves() {
        install_pq_cores();
        let ags = agents(3);
        let mut budget =
            SharedResourceBudget::new(CellId::from_bytes([0xBB; 32]), 1000, ags.clone(), 1)
                .unwrap();
        let resource_id = [0xBB; 32];

        // Phase 1: three optimistic debits of 400 each → overspend (1200 > 1000).
        for &a in &ags {
            let _ = budget.try_optimistic_debit(a, 400, [0u8; 32]);
        }
        assert!(
            budget.is_overspent(),
            "scenario must overspend to exercise resolution"
        );

        // Build a blocklace with one debit block per agent (the tau-ordered conflict set).
        let sk = ed25519_dalek::SigningKey::from_bytes(&[0x77; 32]);
        let mut blocklace = Blocklace::new_simple(sk);
        let mut ids = Vec::new();
        for a in &ags {
            let ska = ed25519_dalek::SigningKey::from_bytes(a.as_bytes());
            let block = BlocBlock::new(
                &ska,
                1,
                Payload::Turn(encode_debit_payload(&resource_id, 400)),
                vec![],
            );
            ids.push(block.id());
            blocklace.receive_block(block).unwrap();
        }

        // Phase 2: escalate + resolve in tau order [A, B, C].
        budget.escalate(ids.clone());
        budget.resolve_with_ordering(&ids, &blocklace, &resource_id);

        // Real verdicts: A accepted, B accepted, C rejected (first-come-wins under tau).
        let real_verdicts: Vec<bool> = ids
            .iter()
            .map(|id| budget.is_accepted(id).unwrap())
            .collect();
        let real_remaining = budget.total_balance;

        // Lean mirror: resolveOrdered 1000 [400, 400, 400].
        let (lean_verdicts, lean_remaining) = lean_resolve_ordered(1000, &[400, 400, 400]);

        // AGREEMENT: per-debit verdicts and the final remaining balance match.
        assert_eq!(
            real_verdicts, lean_verdicts,
            "tau-resolution verdict mismatch"
        );
        assert_eq!(
            real_remaining, lean_remaining,
            "post-resolution balance mismatch"
        );

        // TAU-RESOLUTION CONSERVATION (the Lean keystone): Σ accepted ≤ starting balance.
        let accepted_sum: u64 = lean_verdicts
            .iter()
            .zip([400u64, 400, 400])
            .filter_map(|(&ok, amt)| ok.then_some(amt))
            .sum();
        assert!(
            accepted_sum <= 1000,
            "accepted debits exceeded the balance — conservation broken"
        );
        assert_eq!(accepted_sum, 800);
        assert_eq!(real_remaining, 200);

        // After resolution the resource is back Open with a fresh epoch (the lifecycle the Lean's
        // rebalance models): new ceiling from remaining 200 = 200*2/3 = 133.
        assert_eq!(budget.state, ResourceState::Open);
        assert_eq!(budget.compute_allowance_ceiling(), lean_ceiling(200, 1));
        assert_eq!(budget.compute_allowance_ceiling(), 133);
    }

    /// **DIFFERENTIAL — a balance-respecting debit set is fully accepted (non-vacuity).** If the
    /// tau-ordered debits all fit (300 + 300 + 300 ≤ 1000), `resolve_with_ordering` accepts ALL of
    /// them and the Lean `resolveOrdered` agrees — the conservation bound is tight, not achieved by
    /// rejecting everything.
    #[test]
    fn diff_resolve_all_fit_accepts_all() {
        install_pq_cores();
        let ags = agents(3);
        let mut budget =
            SharedResourceBudget::new(CellId::from_bytes([0xBB; 32]), 1000, ags.clone(), 1)
                .unwrap();
        let resource_id = [0xBB; 32];

        let sk = ed25519_dalek::SigningKey::from_bytes(&[0x88; 32]);
        let mut blocklace = Blocklace::new_simple(sk);
        let mut ids = Vec::new();
        for a in &ags {
            let ska = ed25519_dalek::SigningKey::from_bytes(a.as_bytes());
            let block = BlocBlock::new(
                &ska,
                1,
                Payload::Turn(encode_debit_payload(&resource_id, 300)),
                vec![],
            );
            ids.push(block.id());
            blocklace.receive_block(block).unwrap();
        }
        budget.escalate(ids.clone());
        budget.resolve_with_ordering(&ids, &blocklace, &resource_id);

        let real_verdicts: Vec<bool> = ids
            .iter()
            .map(|id| budget.is_accepted(id).unwrap())
            .collect();
        let (lean_verdicts, lean_remaining) = lean_resolve_ordered(1000, &[300, 300, 300]);
        assert_eq!(real_verdicts, lean_verdicts);
        assert_eq!(real_verdicts, vec![true, true, true]);
        assert_eq!(budget.total_balance, lean_remaining);
        assert_eq!(budget.total_balance, 100);
    }
}

// ═══════════════════ Differential 4: StingrayCounter::rebalance cert-reconciliation ═════════════════
//
// The CROSS-EPOCH half of Stingray (`budget.rs::StingrayCounter::rebalance`) — the residue named-OPEN
// in `Proof/Stingray` §9 and now modelled+proved in `Dregg2/Coord/StingrayCertReconcile.lean`. This
// runs the GENUINE `StingrayCounter` with REAL Ed25519 certificates (so the production signature path
// is exercised) and asserts its observable rebalance outcomes / error tags AGREE, point for point,
// with `lean_rebalance` (the Rust transcription of the Lean gate machine).

#[cfg(test)]
mod stingray_cert_reconcile_diff {
    use super::*;
    use crate::budget::{SpendingCertificate, StingrayCounter};
    use dregg_cell::CellId;

    type SiloId = [u8; 32];

    fn agent() -> CellId {
        CellId::from_bytes([0xAA; 32])
    }
    fn silos(n: usize) -> Vec<SiloId> {
        (0..n)
            .map(|i| {
                let mut id = [0u8; 32];
                id[0] = i as u8;
                id
            })
            .collect()
    }
    fn signing_key(silo: &SiloId) -> [u8; 32] {
        *blake3::hash(silo).as_bytes()
    }
    fn pubkey(sk: &[u8; 32]) -> [u8; 32] {
        ed25519_dalek::SigningKey::from_bytes(sk)
            .verifying_key()
            .to_bytes()
    }
    fn register_all(coord: &mut StingrayCounter) {
        for silo in coord.silos.clone() {
            coord.register_silo_pubkey(silo, pubkey(&signing_key(&silo)));
        }
    }

    /// Map the real `Result<u64, BudgetError>` onto the Lean `LeanRebOutcome` shape, reading the
    /// post-state the same way the Lean `Outcome` exposes it.
    fn real_outcome(
        res: Result<u64, crate::budget::BudgetError>,
        coord: &StingrayCounter,
    ) -> LeanRebOutcome {
        use crate::budget::BudgetError;
        match res {
            Ok(total) => LeanRebOutcome::Ok {
                total_spent: total,
                new_balance: coord.total_balance,
                new_version: coord.version,
            },
            Err(e) => match e {
                BudgetError::IncompleteCertificates { .. } => {
                    LeanRebOutcome::IncompleteCertificates
                }
                BudgetError::VersionMismatch { .. } => LeanRebOutcome::VersionMismatch,
                BudgetError::DuplicateCertificate { .. } => LeanRebOutcome::DuplicateCertificate,
                BudgetError::CertificateExceedsCeiling { .. } => LeanRebOutcome::CertExceedsCeiling,
                BudgetError::MissingSiloPubkey { .. } => LeanRebOutcome::MissingSiloPubkey,
                BudgetError::InvalidCertificateSignature { .. } => LeanRebOutcome::InvalidSignature,
                other => panic!("unexpected budget error in differential: {other:?}"),
            },
        }
    }

    /// Produce a genuine signed certificate for silo `i` claiming `spent` (drives `try_debit` so the
    /// real `BudgetSlice` produces the Ed25519 signature).
    fn signed_cert(coord: &StingrayCounter, ss: &[SiloId], i: usize) -> SpendingCertificate {
        let silo = ss[i];
        let sk = signing_key(&silo);
        coord.silo_states[&silo].certificate(silo, &sk)
    }

    // ── §9(2) PARTIAL-MODE quorum reconstruction (`test_rebalance_partial_mode`) ──
    #[test]
    fn rebalance_partial_mode_agrees() {
        let ss = silos(4);
        let mut coord = StingrayCounter::new(agent(), 1000, ss.clone(), 1).unwrap();
        register_all(&mut coord);
        coord
            .try_debit(ss[0], 50, *blake3::hash(b"d").as_bytes())
            .unwrap();
        let cert_a = signed_cert(&coord, &ss, 0);

        // Lean model: 1 cert (silo 0, spent 50), partial mode, ceiling 666, 3 missing → 50 + 3*666.
        let lean = lean_rebalance(
            4,
            &[0, 1, 2, 3],
            0,
            1000,
            1,
            &[LeanCert {
                silo: 0,
                version: 0,
                spent: 50,
                sig_ok: true,
            }],
            false,
        );
        let real = real_outcome(coord.rebalance_partial(&[cert_a]), &coord);
        assert_eq!(real, lean);
        // The Byzantine-conservative reconstruction: 50 + 3*666 = 2048.
        assert_eq!(
            lean,
            LeanRebOutcome::Ok {
                total_spent: 2048,
                new_balance: 0,
                new_version: 1
            }
        );
    }

    // ── §9(2) full-mode quorum completeness gate (`test_rebalance_rejects_incomplete_certificates`) ──
    #[test]
    fn rebalance_full_mode_incomplete_agrees() {
        let ss = silos(4);
        let mut coord = StingrayCounter::new(agent(), 1000, ss.clone(), 1).unwrap();
        register_all(&mut coord);
        coord
            .try_debit(ss[0], 50, *blake3::hash(b"d").as_bytes())
            .unwrap();
        let cert_a = signed_cert(&coord, &ss, 0);

        let lean = lean_rebalance(
            4,
            &[0, 1, 2, 3],
            0,
            1000,
            1,
            &[LeanCert {
                silo: 0,
                version: 0,
                spent: 50,
                sig_ok: true,
            }],
            true,
        );
        let real = real_outcome(coord.rebalance(&[cert_a]), &coord);
        assert_eq!(real, lean);
        assert_eq!(lean, LeanRebOutcome::IncompleteCertificates);
    }

    // ── §9(3) EPOCH MONOTONICITY / no-replay (`test_rebalance_rejects_wrong_version`) ──
    #[test]
    fn rebalance_stale_cert_rejected_agrees() {
        let ss = silos(4);
        let mut coord = StingrayCounter::new(agent(), 1000, ss.clone(), 1).unwrap();
        register_all(&mut coord);
        coord
            .try_debit(ss[0], 50, *blake3::hash(b"d").as_bytes())
            .unwrap();
        let mut cert = signed_cert(&coord, &ss, 0);
        cert.version = 99; // stale / wrong epoch

        let lean = lean_rebalance(
            4,
            &[0, 1, 2, 3],
            0,
            1000,
            1,
            &[LeanCert {
                silo: 0,
                version: 99,
                spent: 50,
                sig_ok: true,
            }],
            false,
        );
        let real = real_outcome(coord.rebalance_partial(&[cert]), &coord);
        assert_eq!(real, lean);
        assert_eq!(lean, LeanRebOutcome::VersionMismatch);
    }

    // ── §9 ceiling gate (`test_rebalance_rejects_overspend_certificate`) — fires BEFORE sig check ──
    #[test]
    fn rebalance_over_ceiling_rejected_agrees() {
        let ss = silos(4);
        let mut coord = StingrayCounter::new(agent(), 1000, ss.clone(), 1).unwrap();
        register_all(&mut coord);
        // A hand-built certificate claiming more than the ceiling (666), forged sig.
        let cert = SpendingCertificate {
            silo: ss[0],
            agent: agent(),
            version: 0,
            total_spent: 9999,
            debits: vec![],
            signature: [0u8; 64],
        };
        let lean = lean_rebalance(
            4,
            &[0, 1, 2, 3],
            0,
            1000,
            1,
            &[LeanCert {
                silo: 0,
                version: 0,
                spent: 9999,
                sig_ok: false,
            }],
            false,
        );
        let real = real_outcome(coord.rebalance_partial(&[cert]), &coord);
        assert_eq!(real, lean);
        assert_eq!(lean, LeanRebOutcome::CertExceedsCeiling);
    }

    // ── §9(1) forged-signature rejection (`test_rebalance_rejects_forged_certificate_signature`) ──
    #[test]
    fn rebalance_forged_sig_rejected_agrees() {
        let ss = silos(4);
        let mut coord = StingrayCounter::new(agent(), 1000, ss.clone(), 1).unwrap();
        register_all(&mut coord);
        // valid spend (≤ ceiling) but a forged (all-zero) signature.
        let cert = SpendingCertificate {
            silo: ss[0],
            agent: agent(),
            version: 0,
            total_spent: 50,
            debits: vec![],
            signature: [0u8; 64],
        };
        let lean = lean_rebalance(
            4,
            &[0, 1, 2, 3],
            0,
            1000,
            1,
            &[LeanCert {
                silo: 0,
                version: 0,
                spent: 50,
                sig_ok: false,
            }],
            false,
        );
        let real = real_outcome(coord.rebalance_partial(&[cert]), &coord);
        assert_eq!(real, lean);
        assert_eq!(lean, LeanRebOutcome::InvalidSignature);
    }

    // ── §9(2) full-mode reconstruction = Σ certified spend + epoch bump ──
    #[test]
    fn rebalance_full_mode_reconstructs_and_bumps_epoch() {
        let ss = silos(4);
        let mut coord = StingrayCounter::new(agent(), 1000, ss.clone(), 1).unwrap();
        register_all(&mut coord);
        let mut certs = Vec::new();
        for i in 0..4 {
            coord
                .try_debit(ss[i], 100, *blake3::hash(&[i as u8]).as_bytes())
                .unwrap();
            certs.push(signed_cert(&coord, &ss, i));
        }
        let lean = lean_rebalance(
            4,
            &[0, 1, 2, 3],
            0,
            1000,
            1,
            &[
                LeanCert {
                    silo: 0,
                    version: 0,
                    spent: 100,
                    sig_ok: true,
                },
                LeanCert {
                    silo: 1,
                    version: 0,
                    spent: 100,
                    sig_ok: true,
                },
                LeanCert {
                    silo: 2,
                    version: 0,
                    spent: 100,
                    sig_ok: true,
                },
                LeanCert {
                    silo: 3,
                    version: 0,
                    spent: 100,
                    sig_ok: true,
                },
            ],
            true,
        );
        let real = real_outcome(coord.rebalance(&certs), &coord);
        assert_eq!(real, lean);
        // Reconstruction = Σ spend = 400; balance 600; version bumped 0→1 (no-replay boundary).
        assert_eq!(
            lean,
            LeanRebOutcome::Ok {
                total_spent: 400,
                new_balance: 600,
                new_version: 1
            }
        );
        // CONSERVATION (rebalance_conserves_on_exact): new_balance + total = old_balance.
        if let LeanRebOutcome::Ok {
            total_spent,
            new_balance,
            ..
        } = lean
        {
            assert_eq!(new_balance + total_spent, 1000);
        }
    }
}
