//! Integration test: node HTTP turn submission logic.
//!
//! These tests exercise the `TurnExecutor` + cipherclerk turn-submission
//! pipeline at the library level — the same code path that
//! `POST /turn/submit` invokes — without spinning up an HTTP server.
//!
//! Covers:
//!   1. Valid turn → committed receipt.
//!   2. Receipts are appended to the cipherclerk chain on commit.
//!   3. Chain links are correct after multiple commits.
//!   4. `was_encrypted = false` on the cleartext path.

use dregg_cell::{Cell, CellId, Ledger};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::{
    ActionBuilder, CallForest, ComputronCosts, Turn, TurnExecutor, TurnResult, verify_receipt_chain,
};
use zeroize::Zeroizing;

// ---------------------------------------------------------------------------
// Helper
// ---------------------------------------------------------------------------

fn test_key(label: &str) -> [u8; 32] {
    *blake3::hash(format!("node-http-test:{label}").as_bytes()).as_bytes()
}

fn make_turn(agent: CellId, nonce: u64, prev: Option<[u8; 32]>) -> Turn {
    let mut call_forest = CallForest::new();
    call_forest
        .add_root(ActionBuilder::new_unchecked_for_tests(agent, "http_submit_noop", agent).build());

    Turn {
        agent,
        nonce,
        fee: 100,
        memo: None,
        valid_until: None,
        call_forest,
        depends_on: vec![],
        previous_receipt_hash: prev,
        conservation_proof: None,
        sovereign_witnesses: Default::default(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: vec![],
        cross_effect_dependencies: vec![],
        effect_witness_index_map: vec![],
    }
}

fn make_cclerk(label: &str) -> AgentCipherclerk {
    AgentCipherclerk::from_key_bytes(Zeroizing::new(test_key(label)))
}

fn make_ledger(cclerk: &AgentCipherclerk) -> Ledger {
    let mut ledger = Ledger::new();
    let cell = Cell::with_balance(cclerk.public_key().0, [0u8; 32], 1_000_000);
    ledger
        .insert_cell(cell)
        .expect("test cell insert must succeed");
    ledger
}

/// Derive the agent CellId from a cipherclerk the same way the node handler does.
fn agent_from_cclerk(cclerk: &AgentCipherclerk) -> CellId {
    CellId(dregg_cell::CellId::derive_raw(&cclerk.public_key().0, &[0u8; 32]).0)
}

// ---------------------------------------------------------------------------
// 1. Valid turn commits and returns a receipt with was_encrypted=false
// ---------------------------------------------------------------------------

#[test]
fn valid_cleartext_turn_commits_and_has_was_encrypted_false() {
    let cclerk = make_cclerk("valid-submit");
    let agent = agent_from_cclerk(&cclerk);

    let executor = TurnExecutor::new(ComputronCosts::default());
    let mut ledger = make_ledger(&cclerk);

    let turn = make_turn(agent, 0, None);
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed { receipt, .. } => {
            assert_eq!(receipt.agent, agent);
            assert!(
                !receipt.was_encrypted,
                "cleartext turn must have was_encrypted=false"
            );
        }
        other => panic!("expected Committed, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 2. Sequential turns: receipts appended to cipherclerk chain, chain verifies
// ---------------------------------------------------------------------------

/// Mirrors the /turn/submit handler loop: for each committed turn, call
/// `cclerk.append_receipt()`. Assert the chain grows and verifies.
///
/// Each turn carries the previous receipt hash (strict mode in both the
/// executor and the cipherclerk require this after the first turn).
#[test]
fn committed_receipts_appended_to_cclerk_chain_verify() {
    let mut cclerk = make_cclerk("chain-append");
    let agent = agent_from_cclerk(&cclerk);

    let executor = TurnExecutor::new(ComputronCosts::default());
    let mut ledger = make_ledger(&cclerk);

    // Genesis turn.
    let t0 = make_turn(agent, 0, None);
    match executor.execute(&t0, &mut ledger) {
        TurnResult::Committed { receipt, .. } => {
            cclerk
                .append_receipt(receipt)
                .expect("genesis append must succeed");
        }
        other => panic!("genesis turn must commit, got: {other:?}"),
    }

    // Turns 1 and 2 must carry the previous receipt hash.
    for nonce in 1u64..3 {
        let prev = Some(cclerk.receipt_head().unwrap().receipt_hash());
        let t = make_turn(agent, nonce, prev);
        match executor.execute(&t, &mut ledger) {
            TurnResult::Committed { receipt, .. } => {
                cclerk
                    .append_receipt(receipt)
                    .expect("non-genesis append must succeed");
            }
            other => panic!("turn nonce={nonce} must commit, got: {other:?}"),
        }
    }

    assert_eq!(cclerk.receipt_chain_length(), 3);
    assert!(
        verify_receipt_chain(cclerk.receipt_chain()).is_ok(),
        "receipt chain after 3 commits must verify"
    );
}

// ---------------------------------------------------------------------------
// 3. Chain links are correct after sequential commits
// ---------------------------------------------------------------------------

#[test]
fn chain_links_correct_after_sequential_commits() {
    let mut cclerk = make_cclerk("chain-links");
    let agent = agent_from_cclerk(&cclerk);

    let executor = TurnExecutor::new(ComputronCosts::default());
    let mut ledger = make_ledger(&cclerk);

    // Genesis.
    let t0 = make_turn(agent, 0, None);
    if let TurnResult::Committed { receipt, .. } = executor.execute(&t0, &mut ledger) {
        cclerk.append_receipt(receipt).unwrap();
    }

    // Two more turns.
    for nonce in 1u64..3 {
        let prev = Some(cclerk.receipt_head().unwrap().receipt_hash());
        let t = make_turn(agent, nonce, prev);
        if let TurnResult::Committed { receipt, .. } = executor.execute(&t, &mut ledger) {
            cclerk.append_receipt(receipt).unwrap();
        }
    }

    let chain = cclerk.receipt_chain();
    assert_eq!(
        chain[0].previous_receipt_hash, None,
        "genesis must have no predecessor"
    );
    for i in 1..chain.len() {
        assert_eq!(
            chain[i].previous_receipt_hash,
            Some(chain[i - 1].receipt_hash()),
            "link broken at index {i}"
        );
    }
}

// ---------------------------------------------------------------------------
// 4. Rejected turn does not grow the cipherclerk chain
// ---------------------------------------------------------------------------

/// Only `TurnResult::Committed` results in an `append_receipt` call.
/// A rejected turn (e.g., nonce reused on a fresh executor) must not
/// grow the chain.
#[test]
fn rejected_turn_does_not_append_to_chain() {
    let mut cclerk = make_cclerk("reject-no-append");
    let agent = agent_from_cclerk(&cclerk);

    let executor = TurnExecutor::new(ComputronCosts::default());
    let mut ledger = make_ledger(&cclerk);

    // First turn commits.
    let t0 = make_turn(agent, 0, None);
    if let TurnResult::Committed { receipt, .. } = executor.execute(&t0, &mut ledger) {
        cclerk.append_receipt(receipt).unwrap();
    }
    assert_eq!(cclerk.receipt_chain_length(), 1);

    // Second turn reuses nonce 0. It carries the correct chain head, but must
    // be rejected by the executor's nonce gate and must not append a receipt.
    let t1 = make_turn(
        agent,
        0,
        Some(cclerk.receipt_head().unwrap().receipt_hash()),
    );
    match executor.execute(&t1, &mut ledger) {
        TurnResult::Committed { receipt, .. } => {
            panic!("replayed nonce must reject; got committed receipt {receipt:?}");
        }
        TurnResult::Rejected { .. } | TurnResult::Expired => {
            // Do not append — mirrors the handler's behavior.
        }
        TurnResult::Pending => {
            // Do not append.
        }
    }

    assert_eq!(cclerk.receipt_chain_length(), 1);
    assert!(
        verify_receipt_chain(cclerk.receipt_chain()).is_ok(),
        "chain must verify after rejected replay"
    );
}
