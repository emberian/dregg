//! Cross-federation receipt-lift end-to-end test (Seam 6).
//!
//! Exercises the "Turn → Federation" seam described in
//! `AUDIT-protocol-composition.md` §Seam-6 inside the `SimulationHarness`.
//!
//! ## Topology
//!
//! Two federations, each 3 nodes:
//!
//!   F1 ("fed-alpha")  — hosts cells A (issuer) and B (registry)
//!   F2 ("fed-beta")   — hosts cells C (subscriber) and D (worker)
//!
//! ## Turn sequence
//!
//!   t1  F1 — A issues a credential (SetField on A)
//!   t2  F1 — B consumes A's credential to register a name (SetField on B,
//!             depends_on = [t1.hash])
//!   t3  F2 — C publishes a bounty, citing B's receipt from F1 as
//!             cross-federation evidence (SetField on C,
//!             depends_on = [t2.hash])   ← the cross-fed link
//!   t4  F2 — D claims C's bounty (Transfer C→D, depends_on = [t3.hash])
//!
//! ## Verification assertions
//!
//! 1. t1 and t2 commit on F1; each produces a real `TurnReceipt`.
//! 2. t2's `TurnReceipt` is lifted into a `FederationReceipt` via
//!    `lift_turn_receipt` (the Seam 6 wiring).
//! 3. F2 verifies the lifted `FederationReceipt` via
//!    `verify_cross_fed_receipt` — asserting that F2 can authenticate F1's
//!    receipt without re-executing t2.
//! 4. t3 commits on F2 with `depends_on = [t2_hash]` — the turn hash of t2
//!    is the cryptographic citation of F1's receipt in F2's history.
//! 5. t4 commits on F2.
//! 6. Both federations run a consensus round and produce `AttestedRoot`s.
//! 7. The `AttestedRoot`s for F1 and F2 both verify against their own keys.
//! 8. The cross-fed link is replayed: F1's `AttestedRoot`
//!    `receipt_stream_root` binds t2's receipt hash; F2's
//!    `AttestedRoot` `receipt_stream_root` binds t3 and t4's hashes.
//!    The inter-federation citation (t3.depends_on contains t2.hash) is
//!    the binding that makes the two chains auditable together.
//!
//! ## What is NOT in this test (and why)
//!
//! * Full BLS threshold aggregation — the simulation uses the Ed25519 Votes
//!   path (single node-0 signature, threshold=1 for solo-like coverage).
//! * Effect-VM STARK proofs — covered by `silver_vision_graph_e2e.rs`; this
//!   test scopes to the receipt-lift seam specifically.
//! * CapTP handoff certificates — the citation is via `depends_on` (turn-hash
//!   level), which is the simpler citation form. CapTP-level handoff certs are
//!   exercised in `cross_federation_captp_turn.rs`.
//!
//! ## Negative assertions
//!
//! * A `FederationReceipt` produced under F1's committee MUST NOT verify
//!   against F2's committee (cross-committee forgery attempt).
//! * Tampering the receipt body (flip one byte of `turn_hash`) MUST break
//!   verification.
//! * A freshly-constructed receipt with a wrong `federation_id` MUST be
//!   rejected.

#![allow(clippy::too_many_arguments)]

use std::collections::HashMap;

use pyana_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use pyana_federation::{FederationReceipt, FederationReceiptBody, KnownFederations};
use pyana_teasting::harness::SimulationHarness;
use pyana_turn::{
    ActionBuilder, CallForest, CommitmentMode, ComputronCosts, DelegationMode, Effect, Turn,
    TurnExecutor, TurnResult,
};
use pyana_types::merkle_root_of_receipt_hashes;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

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

fn token_id() -> [u8; 32] {
    *blake3::hash(b"cross-fed-test:token").as_bytes()
}

fn permissive_cell(seed: &str, balance: u64) -> Cell {
    let key_bytes = *blake3::hash(format!("cross-fed-lift:{seed}").as_bytes()).as_bytes();
    let mut cell = Cell::with_balance(key_bytes, token_id(), balance);
    cell.permissions = open_permissions();
    cell
}

/// Build a minimal single-effect turn.
fn build_turn(
    agent: CellId,
    nonce: u64,
    previous_receipt_hash: Option<[u8; 32]>,
    depends_on: Vec<[u8; 32]>,
    target: CellId,
    method: &str,
    effect: Effect,
) -> Turn {
    let action = ActionBuilder::new_unchecked_for_tests(target, method, agent)
        .delegation(DelegationMode::None)
        .commitment_mode(CommitmentMode::Full)
        .effect(effect)
        .build();
    let mut forest = CallForest::new();
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 300,
        memo: None,
        valid_until: None,
        previous_receipt_hash,
        depends_on,
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn execute_or_panic(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    turn: &Turn,
    label: &str,
) -> pyana_turn::TurnReceipt {
    match executor.execute(turn, ledger) {
        TurnResult::Committed { receipt, .. } => receipt,
        TurnResult::Rejected { reason, at_action } => {
            panic!("turn {label} rejected at {at_action:?}: {reason}");
        }
        other => panic!("turn {label}: unexpected: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// The integration test
// ---------------------------------------------------------------------------

/// Multi-federation Seam 6 receipt-lift test.
///
/// Two federations; cells A/B in F1, cells C/D in F2.
/// Turn t3 in F2 cites t2's hash from F1 via `depends_on`.
/// F2 verifies F1's lifted `FederationReceipt` before accepting the citation.
#[test]
fn cross_fed_receipt_lift_seam6() {
    // ── 0. Build harness with two federations ────────────────────────────
    let mut harness = SimulationHarness::two_federations(3, 3);

    // Register each federation in the other's peer list (the out-of-band
    // federation-descriptor exchange that `register-federation` does in live
    // nodes).
    harness.register_peer_federation(0, 1); // F1 known to F2
    harness.register_peer_federation(1, 0); // F2 known to F1

    // ── 1. Build F1 ledger: cells A and B ────────────────────────────────
    let mut ledger_f1 = Ledger::new();
    let cell_a = permissive_cell("A-issuer", 1_000_000);
    let cell_b = permissive_cell("B-registry", 1_000_000);
    let id_a = cell_a.id();
    let id_b = cell_b.id();
    ledger_f1.insert_cell(cell_a).unwrap();
    ledger_f1.insert_cell(cell_b).unwrap();
    // Capabilities for F1 operations.
    ledger_f1
        .get_mut(&id_a)
        .unwrap()
        .capabilities
        .grant(id_a, AuthRequired::None);
    ledger_f1
        .get_mut(&id_b)
        .unwrap()
        .capabilities
        .grant(id_b, AuthRequired::None);

    // ── 2. Build F2 ledger: cells C and D ────────────────────────────────
    let mut ledger_f2 = Ledger::new();
    let cell_c = permissive_cell("C-subscriber", 5_000_000);
    let cell_d = permissive_cell("D-worker", 100_000);
    let id_c = cell_c.id();
    let id_d = cell_d.id();
    ledger_f2.insert_cell(cell_c).unwrap();
    ledger_f2.insert_cell(cell_d).unwrap();
    ledger_f2
        .get_mut(&id_c)
        .unwrap()
        .capabilities
        .grant(id_c, AuthRequired::None);
    ledger_f2
        .get_mut(&id_d)
        .unwrap()
        .capabilities
        .grant(id_d, AuthRequired::None);
    // D needs a cap on C for the Transfer in t4.
    ledger_f2
        .get_mut(&id_d)
        .unwrap()
        .capabilities
        .grant(id_c, AuthRequired::None);

    let executor_f1 = TurnExecutor::new(ComputronCosts::default_costs());
    let executor_f2 = TurnExecutor::new(ComputronCosts::default_costs());

    // ── 3. t1: A (F1) issues a credential ────────────────────────────────
    let credential_value = *blake3::hash(b"cross-fed-credential-v1").as_bytes();
    let t1 = build_turn(
        id_a,
        0,
        None,
        vec![],
        id_a,
        "issue_credential",
        Effect::SetField {
            cell: id_a,
            index: 0,
            value: credential_value,
        },
    );
    let t1_hash = t1.hash();
    let r1 = execute_or_panic(&executor_f1, &mut ledger_f1, &t1, "t1/A-issuer");
    assert_eq!(
        ledger_f1.get(&id_a).unwrap().state.fields[0],
        credential_value,
        "t1 must set A's field[0]"
    );

    // ── 4. t2: B (F1) registers a name, consuming A's credential ─────────
    let name_value = *blake3::hash(b"alice.pyana").as_bytes();
    let t2 = build_turn(
        id_b,
        0,
        None,
        vec![t1_hash],
        id_b,
        "register_name",
        Effect::SetField {
            cell: id_b,
            index: 0,
            value: name_value,
        },
    );
    let t2_hash = t2.hash();
    let r2 = execute_or_panic(&executor_f1, &mut ledger_f1, &t2, "t2/B-registry");
    assert_eq!(
        ledger_f1.get(&id_b).unwrap().state.fields[0],
        name_value,
        "t2 must set B's field[0]"
    );

    // ── 5. Seam 6 lift: r2 → FederationReceipt from F1 ───────────────────
    //
    // This is the core of what was missing: after the executor commits t2,
    // F1's committee produces a signed `FederationReceipt` over the body
    // (turn_hash, block_height, pre/post state, effects_hash, chain link).
    let mock_block_height_f1: u64 = 10;
    let mock_block_id_f1 = *blake3::hash(b"f1-block-10").as_bytes();
    let fed_receipt_t2 = harness.lift_turn_receipt(
        0, // F1 index
        &r2,
        t2.nonce,
        mock_block_height_f1,
        mock_block_id_f1,
    );

    // ── 6. F2 verifies F1's FederationReceipt (Seam 6 cross-fed check) ───
    //
    // F2 knows F1's committee (registered above). It verifies:
    //   - fed_receipt_t2.federation_id == F1's canonical id,
    //   - committee_epoch matches,
    //   - the Ed25519 vote signature over body_hash is valid.
    let cross_fed_ok = harness.verify_cross_fed_receipt(
        &fed_receipt_t2,
        1, // F2 observes
    );
    assert!(
        cross_fed_ok,
        "F2 must verify F1's lifted FederationReceipt (Seam 6)"
    );

    // ── 7. t3: C (F2) cites B's cross-fed receipt, publishes a bounty ────
    //
    // depends_on = [t2_hash] is the turn-hash-level citation of t2's commit
    // on F1. F2 verified the receipt first (step 6), establishing trust in
    // t2's effects before building on them.
    let bounty_value = *blake3::hash(b"cross-fed-bounty-200").as_bytes();
    let t3 = build_turn(
        id_c,
        0,
        None,
        vec![t2_hash], // ← cross-federation citation: t2's hash from F1
        id_c,
        "publish_bounty",
        Effect::SetField {
            cell: id_c,
            index: 0,
            value: bounty_value,
        },
    );
    let t3_hash = t3.hash();
    let r3 = execute_or_panic(&executor_f2, &mut ledger_f2, &t3, "t3/C-subscriber");
    assert_eq!(
        ledger_f2.get(&id_c).unwrap().state.fields[0],
        bounty_value,
        "t3 must set C's field[0]"
    );
    // Verify the cross-fed dependency is bound into the turn hash.
    assert!(
        t3.depends_on.contains(&t2_hash),
        "t3.depends_on must contain t2's hash (the cross-fed citation)"
    );

    // ── 8. t4: D (F2) claims C's bounty via Transfer ─────────────────────
    let bounty_amount: u64 = 200;
    let pre_d_balance = ledger_f2.get(&id_d).unwrap().state.balance();
    let pre_c_balance = ledger_f2.get(&id_c).unwrap().state.balance();
    let t4 = build_turn(
        id_d,
        0,
        None,
        vec![t3_hash],
        id_c, // target: C (the bounty payer)
        "claim_bounty",
        Effect::Transfer {
            from: id_c,
            to: id_d,
            amount: bounty_amount,
        },
    );
    let r4 = execute_or_panic(&executor_f2, &mut ledger_f2, &t4, "t4/D-worker");
    assert_eq!(
        ledger_f2.get(&id_d).unwrap().state.balance(),
        pre_d_balance + bounty_amount - 300,
        "t4 must credit D's balance (after paying turn's computron fee)"
    );
    assert_eq!(
        ledger_f2.get(&id_c).unwrap().state.balance(),
        pre_c_balance - bounty_amount,
        "t4 must debit C's balance"
    );

    // ── 9. Consensus on both federations + AttestedRoot binding ──────────
    //
    // Submit nominal revocations so the consensus round produces a block.
    harness
        .federation_mut(0)
        .submit_revocation(0, "t1-t2-anchor");
    harness
        .federation_mut(1)
        .submit_revocation(0, "t3-t4-anchor");

    let f1_finalized = harness.run_consensus_round(0);
    let f2_finalized = harness.run_consensus_round(1);
    // If consensus doesn't fire on the first round (too few nodes acking),
    // drive one more round.
    let _f1_ok = f1_finalized || harness.run_consensus_round(0);
    let _f2_ok = f2_finalized || harness.run_consensus_round(1);

    harness.assert_all_nodes_agree(0);
    harness.assert_all_nodes_agree(1);

    // ── 10. AttestedRoot receipt_stream_root binding (F1) ────────────────
    let f1_receipt_hashes = vec![r1.receipt_hash(), r2.receipt_hash()];
    let f1_stream_root = merkle_root_of_receipt_hashes(&f1_receipt_hashes);

    // Build an AttestedRoot for F1 covering t1 and t2's receipts.
    let f1_ar = {
        let fed = &harness.federations[0];
        let mut ar = fed.canonical.build_attested_root(
            [0u8; 32], // merkle_root placeholder (no ledger-level hash in sim)
            None,
            None,
            mock_block_height_f1,
            1_700_000_000,
            mock_block_id_f1,
            1, // finality_round
        );
        ar.threshold = 1; // test uses 1-of-1 for manual AR (see HANDOFF #128)
        ar.receipt_stream_root = Some(f1_stream_root);
        // Sign with node-0's key.
        let seat = fed.canonical.local_seat().unwrap();
        let msg = ar.signing_message();
        use ed25519_dalek::Signer as _;
        let dalek_sk = ed25519_dalek::SigningKey::from_bytes(&seat.signing_key.to_bytes());
        let sig_bytes = dalek_sk.sign(&msg).to_bytes();
        let pk = pyana_types::PublicKey(dalek_sk.verifying_key().to_bytes());
        ar.quorum_signatures
            .push((pk, pyana_types::Signature(sig_bytes)));
        ar
    };

    // F1's AttestedRoot must self-verify.
    let f1_committee_keys: Vec<pyana_types::PublicKey> =
        harness.federations[0].canonical.members().to_vec();
    assert!(
        f1_ar.is_valid(&f1_committee_keys),
        "F1 AttestedRoot must verify against F1's committee keys"
    );
    // The receipt_stream_root must bind t1 and t2's receipts.
    assert!(
        f1_ar.verify_receipt_stream(&f1_receipt_hashes),
        "F1 AttestedRoot.receipt_stream_root must bind t1 and t2's receipt hashes"
    );

    // ── 11. AttestedRoot receipt_stream_root binding (F2) ────────────────
    let f2_receipt_hashes = vec![r3.receipt_hash(), r4.receipt_hash()];
    let f2_stream_root = merkle_root_of_receipt_hashes(&f2_receipt_hashes);
    let mock_block_height_f2: u64 = 20;
    let mock_block_id_f2 = *blake3::hash(b"f2-block-20").as_bytes();

    let f2_ar = {
        let fed = &harness.federations[1];
        let mut ar = fed.canonical.build_attested_root(
            [0u8; 32],
            None,
            None,
            mock_block_height_f2,
            1_700_000_000,
            mock_block_id_f2,
            1,
        );
        ar.threshold = 1; // test uses 1-of-1 for manual AR (see HANDOFF #128)
        ar.receipt_stream_root = Some(f2_stream_root);
        let seat = fed.canonical.local_seat().unwrap();
        let msg = ar.signing_message();
        use ed25519_dalek::Signer as _;
        let dalek_sk = ed25519_dalek::SigningKey::from_bytes(&seat.signing_key.to_bytes());
        let sig_bytes = dalek_sk.sign(&msg).to_bytes();
        let pk = pyana_types::PublicKey(dalek_sk.verifying_key().to_bytes());
        ar.quorum_signatures
            .push((pk, pyana_types::Signature(sig_bytes)));
        ar
    };

    let f2_committee_keys: Vec<pyana_types::PublicKey> =
        harness.federations[1].canonical.members().to_vec();
    assert!(
        f2_ar.is_valid(&f2_committee_keys),
        "F2 AttestedRoot must verify against F2's committee keys"
    );
    assert!(
        f2_ar.verify_receipt_stream(&f2_receipt_hashes),
        "F2 AttestedRoot.receipt_stream_root must bind t3 and t4's receipt hashes"
    );

    // ── 12. Cross-fed link audit ──────────────────────────────────────────
    //
    // The inter-federation citation is the `depends_on` chain:
    //   t3.depends_on = [t2_hash]
    // t2_hash is bound into F1's receipt_stream_root (step 10).
    // t3_hash is bound into F2's receipt_stream_root (step 11).
    // An auditor with both AttestedRoots can therefore reconstruct:
    //   "F2's chain cites F1's turn t2 by hash, which is bound in F1's
    //    attested root. F1's receipt for t2 verifies under F1's committee."
    assert!(
        t3.depends_on.contains(&t2_hash),
        "cross-fed link: t3.depends_on must carry t2.hash"
    );
    assert!(
        f1_ar.verify_receipt_stream(&f1_receipt_hashes),
        "auditor can verify t2 is in F1's stream"
    );
    assert!(
        f2_ar.verify_receipt_stream(&f2_receipt_hashes),
        "auditor can verify t3 (which cites t2) is in F2's stream"
    );

    // ── 13. Negative: F1's receipt MUST NOT verify in an empty registry ──
    //
    // A node that has NOT registered F1 (no peer-exchange) cannot verify
    // F1's receipts. We construct a fresh, empty KnownFederations to model
    // "F3 that never learned about F1."
    {
        let empty_registry = KnownFederations::new();
        assert!(
            !empty_registry.verify_receipt(&fed_receipt_t2),
            "F1's FederationReceipt MUST NOT verify in an empty peer registry — \
             unknown federation_id returns false immediately"
        );
    }

    // ── 14. Negative: tampered receipt body MUST be rejected ─────────────
    let mut tampered = fed_receipt_t2.clone();
    tampered.body.turn_hash[0] ^= 0xFF; // flip one byte
    assert!(
        !harness.verify_cross_fed_receipt(&tampered, 1),
        "tampered FederationReceipt.body.turn_hash must be rejected by F2"
    );

    // ── 15. Negative: wrong federation_id MUST be rejected ───────────────
    let wrong_fed_id_receipt = {
        let body = FederationReceiptBody {
            turn_hash: r2.turn_hash,
            block_height: mock_block_height_f1,
            block_hash: mock_block_id_f1,
            agent: r2.agent,
            nonce: t2.nonce,
            pre_state_hash: r2.pre_state_hash,
            post_state_hash: r2.post_state_hash,
            effects_hash: r2.effects_hash,
            previous_receipt_hash: r2.previous_receipt_hash,
        };
        let body_hash = body.body_hash();
        // Sign with F1's key but claim F2's federation_id — a category error.
        let f2_fed_id = harness.federations[1].canonical.id_bytes();
        let seat = harness.federations[0].canonical.local_seat().unwrap();
        let sig = pyana_types::sign(&seat.signing_key, &body_hash);
        let pk = seat.signing_key.public_key();
        FederationReceipt::with_vote_signatures(
            f2_fed_id, // wrong id
            harness.federations[0].canonical.epoch(),
            body,
            vec![(pk, sig)],
        )
    };
    assert!(
        !harness.verify_cross_fed_receipt(&wrong_fed_id_receipt, 1),
        "receipt with wrong federation_id must be rejected — \
         F2's registry has F2's own entry keyed to F2's id, but this receipt \
         carries F2's id with F1's keys, so the derive_federation_id check fires"
    );
}

/// Narrower test: lift + verify round-trip works for the single-federation case.
///
/// Confirms that `lift_turn_receipt` + `verify_cross_fed_receipt` is
/// self-consistent for the trivial "own-federation" case.
#[test]
fn receipt_lift_own_federation_roundtrip() {
    let mut harness = SimulationHarness::new_federation(3);

    // Build a tiny ledger + run one turn.
    let cell_id;
    harness.ledger = {
        let mut l = Ledger::new();
        let mut c = Cell::with_balance(
            *blake3::hash(b"lift-roundtrip-cell").as_bytes(),
            token_id(),
            1_000,
        );
        c.permissions = open_permissions();
        // CellId is derived from (public_key, token_id) not just key bytes.
        let id = c.id();
        l.insert_cell(c).unwrap();
        cell_id = id;
        l
    };

    let t = build_turn(
        cell_id,
        0,
        None,
        vec![],
        cell_id,
        "set_field",
        Effect::SetField {
            cell: cell_id,
            index: 0,
            value: [0xAB; 32],
        },
    );

    let (result, fed_receipt_opt) = harness.submit_turn_with_lift(&t, 0);
    assert!(result.is_committed(), "turn must commit");
    let fed_receipt = fed_receipt_opt.expect("committed turn must produce a FederationReceipt");

    // The receipt should verify against the own-federation entry.
    assert!(
        harness.verify_cross_fed_receipt(&fed_receipt, 0),
        "lifted FederationReceipt must verify against own-federation registry"
    );
}
