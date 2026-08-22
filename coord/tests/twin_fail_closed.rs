//! FAIL-CLOSED proof for the three coordination twins (#3 2PC, #4 causal, #5 shared-budget).
//!
//! These twins used to fall back to a NATIVE Rust decider when the verified Lean gate was not
//! registered (`Some(verified).unwrap_or(native)`). That native decider has been removed from the
//! live path: the verdict is now the verified Lean gate, or — when no gate is registered — a
//! FAIL-CLOSED refusal. This integration test links `dregg-coord` as a NORMAL dependency (compiled
//! WITHOUT `cfg(test)`, so the release/consumer path runs, not the in-crate differential sibling) and
//! registers NO verified gate, forcing the no-export branch. It asserts each twin REFUSES rather than
//! silently native-deciding.
//!
//! (The verified path deciding on a full-Lean target is exercised in `dregg-exec-lean`'s tests, which
//! register the real `register_distributed_gates()` gate over the linked archive.)

use std::collections::HashMap;

use dregg_blocklace::finality::{Block as BlocBlock, Blocklace, Payload};
use dregg_cell::{CellId, Preconditions};
use dregg_coord::atomic::{AtomicForest, Coordinator, Decision, Vote};
use dregg_coord::causal::{CausalDag, verified_happened_before};
use dregg_coord::shared_budget::{SharedResourceBudget, encode_debit_payload};
use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode};
use dregg_turn::{CallForest, ComputronCosts};

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

// ── #3 — 2PC decide: a full-Yes tally that WOULD commit under the verified gate aborts fail-closed ──
#[test]
fn twoc_pc_fails_closed_without_gate() {
    // 3 participants, threshold 2 (a majority policy that a verified gate would COMMIT on two Yes).
    let nodes = vec![node_id(1), node_id(2), node_id(3)];
    let mut signing_keys = Vec::new();
    let mut participant_keys: HashMap<[u8; 32], [u8; 32]> = HashMap::new();
    for nid in &nodes {
        let (sk, pk) = keypair(nid[0]);
        signing_keys.push(sk);
        participant_keys.insert(*nid, pk);
    }

    // A non-empty forest so `propose` passes structural validation — the fail-closed decision we are
    // testing happens at the VOTING tally (`evaluate_votes`), not at propose.
    let initiator = CellId::from_bytes([9u8; 32]);
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: initiator,
        method: *blake3::hash(b"noop").as_bytes(),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    });
    let af = AtomicForest::new(nodes.clone(), forest, vec![], initiator, 0, None);

    let mut coord = Coordinator::new(
        node_id(1),
        *blake3::hash(b"twin-fail-closed-2pc").as_bytes(),
        2, // threshold
        ComputronCosts::zero(),
        u64::MAX,
        participant_keys,
    );
    let prop = coord.propose(af.clone()).expect("propose");

    // Cast all three Yes votes with REAL Ed25519 signatures. Under the verified gate this reaches the
    // threshold and COMMITS; with NO gate registered the live path must FAIL CLOSED to Abort.
    let mut terminal = Decision::Pending;
    for (i, nid) in nodes.iter().enumerate() {
        let sig = Vote::sign_yes(&prop.proposal_id, &af.hash, &signing_keys[i]);
        if let Some(d) = coord
            .receive_vote(*nid, Vote::yes(sig))
            .expect("receive_vote")
        {
            terminal = d;
            break;
        }
    }

    assert_ne!(
        terminal,
        Decision::Commit,
        "2PC must NOT commit when the verified gate is absent — it must fail closed"
    );
    assert_eq!(
        terminal,
        Decision::Abort,
        "2PC must fail closed to Abort without the verified gate"
    );
}

// ── #4 — causal happened-before: a genuine ancestor pair is reported UNORDERED without the gate ──
#[test]
fn causal_happened_before_fails_closed_without_gate() {
    // A linear chain 1 -> 2 -> 3: 1 genuinely happened-before 3 (the DAG's own method agrees).
    let h = |n: u8| {
        let mut b = [0u8; 32];
        b[0] = n;
        b
    };
    let mut dag = CausalDag::new();
    dag.insert_genesis(h(1)).unwrap();
    dag.insert(h(2), &[h(1)]).unwrap();
    dag.insert(h(3), &[h(2)]).unwrap();

    // The DAG's own (non-verified) method confirms the ordering exists...
    assert!(dag.happened_before(&h(1), &h(3)));
    // ...but the verified decider FAILS CLOSED to "not ordered" without the gate.
    assert!(
        !verified_happened_before(&dag, &h(1), &h(3)),
        "causal order must fail closed (not-ordered) when the verified gate is absent"
    );
}

// ── #5 — shared-budget resolve: fitting debits are ALL REJECTED without the gate ──
#[test]
fn shared_budget_resolve_fails_closed_without_gate() {
    // This test mints real blocklace blocks, and `Block::new` derives the author's ML-DSA-65 half
    // through `dregg-pq`, which refuses with `process::abort()` when no verified core is installed.
    // `dregg-coord` cannot link the archive from `[dependencies]` (it is FFI-free by construction),
    // so the dev-only `dregg-pq-testkit` installs the cores here.
    dregg_pq_testkit::install_or_panic();
    let resource_id = [0xBB; 32];
    let agents: Vec<CellId> = (0..3u8)
        .map(|i| {
            let mut b = [0u8; 32];
            b[0] = i;
            b[31] = 0xAA;
            CellId::from_bytes(b)
        })
        .collect();
    let mut budget =
        SharedResourceBudget::new(CellId::from_bytes([0xBB; 32]), 1000, agents.clone(), 1).unwrap();

    // Three debits of 300 (900 <= 1000) — under the verified gate ALL would be accepted.
    let sk = ed25519_dalek::SigningKey::from_bytes(&[0x88; 32]);
    let mut blocklace = Blocklace::new_simple(sk);
    let mut ids = Vec::new();
    for a in &agents {
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

    // FAIL CLOSED: every debit rejected, balance untouched — never silently accepted by a native fold.
    for id in &ids {
        assert_eq!(
            budget.is_accepted(id),
            Some(false),
            "shared-budget debit must be REJECTED (fail closed) when the verified gate is absent"
        );
    }
    assert_eq!(
        budget.total_balance, 1000,
        "balance must be untouched when the verified shared-budget gate is absent"
    );
}
