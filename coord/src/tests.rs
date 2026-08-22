//! Comprehensive tests for both coordination layers.
//!
//! Layer 1: Causal Chaining — CausalDag construction, ordering verification, frontier tracking.
//! Layer 2: Atomic Multi-Party — 2PC protocol, success and failure paths.

use std::collections::HashMap;

use dregg_cell::preconditions::CellStatePrecondition;
use dregg_cell::{Cell, CellId, Ledger, Preconditions};
use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect};
use dregg_turn::{CallForest, ComputronCosts, Turn};

use crate::atomic::{AtomicForest, AtomicForestBuilder, Coordinator, Decision, Participant, Vote};
use crate::causal::CausalDag;
use crate::error::CoordError;

// ─── Test Helpers ──────────────────────────────────────────────────────────────

/// Create a test node ID from a simple integer.
fn node_id(n: u8) -> [u8; 32] {
    let mut id = [0u8; 32];
    id[0] = n;
    id
}

/// Create a deterministic Ed25519 signing key from a byte.
/// Returns (signing_key_bytes, public_key_bytes).
fn make_keypair(n: u8) -> ([u8; 32], [u8; 32]) {
    // Derive a deterministic 32-byte seed from the byte.
    let seed = *blake3::hash(&[n; 1]).as_bytes();
    let pubkey = Vote::public_key_from_signing_key(&seed);
    (seed, pubkey)
}

/// Build participant_keys map for a set of node IDs.
/// Returns (signing_keys_vec, participant_keys_map).
fn make_participant_keys(node_ids: &[[u8; 32]]) -> (Vec<[u8; 32]>, HashMap<[u8; 32], [u8; 32]>) {
    let mut signing_keys = Vec::new();
    let mut participant_keys = HashMap::new();
    for nid in node_ids {
        let (sk, pk) = make_keypair(nid[0]);
        signing_keys.push(sk);
        participant_keys.insert(*nid, pk);
    }
    (signing_keys, participant_keys)
}

/// Zero costs for tests that don't care about metering.
fn zero_costs() -> ComputronCosts {
    ComputronCosts::zero()
}

/// A large budget that won't interfere with tests.
const TEST_MAX_BUDGET: u64 = u64::MAX;

/// Default coordinator signing key for tests.
fn coord_signing_key() -> [u8; 32] {
    *blake3::hash(b"coordinator-signing-key-test").as_bytes()
}

/// Create a test cell with a given public key byte and balance.
/// Permissions are set to AuthRequired::None for all actions (permissive, for testing).
fn make_cell(key_byte: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = key_byte;
    let token_id = [0u8; 32]; // default token domain
    let mut cell = Cell::with_balance(pk, token_id, balance);
    // Make permissions fully permissive for tests.
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

/// Create a simple turn that transfers computrons from one cell to another.
fn make_transfer_turn(
    agent: CellId,
    from: CellId,
    to: CellId,
    amount: u64,
    nonce: u64,
    fee: u64,
) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
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
    };
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee,
        memo: Some("test transfer".to_string()),
        valid_until: None,
        depends_on: vec![],
        previous_receipt_hash: None,
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

/// Create a simple turn that sets a field on the agent's cell.
fn make_set_field_turn(agent: CellId, index: u64, value: [u8; 32], nonce: u64) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: agent,
        method: *blake3::hash(b"set_field").as_bytes(),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![Effect::SetField {
            cell: agent,
            index,
            value,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        depends_on: vec![],
        previous_receipt_hash: None,
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

/// Create a noop turn (increments nonce only).
fn make_noop_turn(agent: CellId, nonce: u64) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: agent,
        method: *blake3::hash(b"noop").as_bytes(),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![Effect::IncrementNonce { cell: agent }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        depends_on: vec![],
        previous_receipt_hash: None,
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

// ═══════════════════════════════════════════════════════════════════════════════
//  LAYER 1: CAUSAL DAG TESTS
// ═══════════════════════════════════════════════════════════════════════════════

mod causal_dag {
    use super::*;

    #[test]
    fn empty_dag() {
        let dag = CausalDag::new();
        assert!(dag.is_empty());
        assert_eq!(dag.len(), 0);
        assert!(dag.frontier().is_empty());
    }

    #[test]
    fn insert_genesis() {
        let mut dag = CausalDag::new();
        let h1 = *blake3::hash(b"turn1").as_bytes();
        dag.insert_genesis(h1).unwrap();

        assert_eq!(dag.len(), 1);
        assert!(dag.contains(&h1));
        assert_eq!(dag.frontier(), vec![h1]);
    }

    #[test]
    fn linear_chain() {
        let mut dag = CausalDag::new();
        let h1 = *blake3::hash(b"turn1").as_bytes();
        let h2 = *blake3::hash(b"turn2").as_bytes();
        let h3 = *blake3::hash(b"turn3").as_bytes();

        dag.insert_genesis(h1).unwrap();
        dag.insert(h2, &[h1]).unwrap();
        dag.insert(h3, &[h2]).unwrap();

        assert_eq!(dag.len(), 3);
        // Frontier should be only h3.
        assert_eq!(dag.frontier(), vec![h3]);

        // Happened-before checks.
        assert!(dag.happened_before(&h1, &h2));
        assert!(dag.happened_before(&h1, &h3));
        assert!(dag.happened_before(&h2, &h3));
        assert!(!dag.happened_before(&h3, &h1));
        assert!(!dag.happened_before(&h2, &h1));
    }

    #[test]
    fn concurrent_turns() {
        // Diamond DAG:
        //      h1
        //     /  \
        //    h2   h3
        //     \  /
        //      h4
        let mut dag = CausalDag::new();
        let h1 = *blake3::hash(b"turn1").as_bytes();
        let h2 = *blake3::hash(b"turn2").as_bytes();
        let h3 = *blake3::hash(b"turn3").as_bytes();
        let h4 = *blake3::hash(b"turn4").as_bytes();

        dag.insert_genesis(h1).unwrap();
        dag.insert(h2, &[h1]).unwrap();
        dag.insert(h3, &[h1]).unwrap();
        dag.insert(h4, &[h2, h3]).unwrap();

        // h2 and h3 are concurrent.
        assert!(dag.are_concurrent(&h2, &h3));
        assert!(!dag.happened_before(&h2, &h3));
        assert!(!dag.happened_before(&h3, &h2));

        // h1 happened before everything.
        assert!(dag.happened_before(&h1, &h2));
        assert!(dag.happened_before(&h1, &h3));
        assert!(dag.happened_before(&h1, &h4));

        // h4 is after everything.
        assert!(dag.happened_before(&h2, &h4));
        assert!(dag.happened_before(&h3, &h4));

        // Frontier should be h4.
        let frontier = dag.frontier();
        assert_eq!(frontier.len(), 1);
        assert!(frontier.contains(&h4));
    }

    #[test]
    fn multiple_genesis_turns() {
        let mut dag = CausalDag::new();
        let h1 = *blake3::hash(b"node_a_genesis").as_bytes();
        let h2 = *blake3::hash(b"node_b_genesis").as_bytes();

        dag.insert_genesis(h1).unwrap();
        dag.insert_genesis(h2).unwrap();

        assert_eq!(dag.len(), 2);
        assert!(dag.are_concurrent(&h1, &h2));

        let frontier = dag.frontier();
        assert_eq!(frontier.len(), 2);
        assert!(frontier.contains(&h1));
        assert!(frontier.contains(&h2));
    }

    #[test]
    fn duplicate_turn_error() {
        let mut dag = CausalDag::new();
        let h1 = *blake3::hash(b"turn1").as_bytes();
        dag.insert_genesis(h1).unwrap();

        let err = dag.insert_genesis(h1).unwrap_err();
        assert_eq!(err, dregg_types::CausalError::Duplicate(h1));
    }

    #[test]
    fn missing_dependency_error() {
        let mut dag = CausalDag::new();
        let h1 = *blake3::hash(b"turn1").as_bytes();
        let h2 = *blake3::hash(b"turn2").as_bytes();

        // Try to insert h2 depending on h1, but h1 is not in the DAG.
        let err = dag.insert(h2, &[h1]).unwrap_err();
        assert!(matches!(err, dregg_types::CausalError::MissingDeps { .. }));
    }

    #[test]
    fn topological_order() {
        let mut dag = CausalDag::new();
        let h1 = *blake3::hash(b"turn1").as_bytes();
        let h2 = *blake3::hash(b"turn2").as_bytes();
        let h3 = *blake3::hash(b"turn3").as_bytes();

        dag.insert_genesis(h1).unwrap();
        dag.insert(h2, &[h1]).unwrap();
        dag.insert(h3, &[h2]).unwrap();

        let order = dag.topological_order();
        assert_eq!(order.len(), 3);
        // h1 must come before h2, h2 before h3.
        let pos_h1 = order.iter().position(|h| h == &h1).unwrap();
        let pos_h2 = order.iter().position(|h| h == &h2).unwrap();
        let pos_h3 = order.iter().position(|h| h == &h3).unwrap();
        assert!(pos_h1 < pos_h2);
        assert!(pos_h2 < pos_h3);
    }

    #[test]
    fn depth_calculation() {
        let mut dag = CausalDag::new();
        let h1 = *blake3::hash(b"turn1").as_bytes();
        let h2 = *blake3::hash(b"turn2").as_bytes();
        let h3 = *blake3::hash(b"turn3").as_bytes();

        dag.insert_genesis(h1).unwrap();
        dag.insert(h2, &[h1]).unwrap();
        dag.insert(h3, &[h2]).unwrap();

        assert_eq!(dag.depth(&h1), Some(0));
        assert_eq!(dag.depth(&h2), Some(1));
        assert_eq!(dag.depth(&h3), Some(2));
    }

    #[test]
    fn complex_dag_frontier() {
        // Three nodes producing turns concurrently.
        //
        //  Node A: a1 ──► a2
        //  Node B: b1 ──────► b2 (depends on a1)
        //  Node C: c1 ──────────► c2 (depends on a2 and b1)
        let mut dag = CausalDag::new();
        let a1 = *blake3::hash(b"a1").as_bytes();
        let a2 = *blake3::hash(b"a2").as_bytes();
        let b1 = *blake3::hash(b"b1").as_bytes();
        let b2 = *blake3::hash(b"b2").as_bytes();
        let c1 = *blake3::hash(b"c1").as_bytes();
        let c2 = *blake3::hash(b"c2").as_bytes();

        dag.insert_genesis(a1).unwrap();
        dag.insert_genesis(b1).unwrap();
        dag.insert_genesis(c1).unwrap();
        dag.insert(a2, &[a1]).unwrap();
        dag.insert(b2, &[b1, a1]).unwrap();
        dag.insert(c2, &[a2, b1]).unwrap();

        // Frontier should be: a2 (superseded by c2), b2, c1, c2.
        // Wait — a2 has successor c2. b1 has successors b2 and c2. a1 has successors a2, b2.
        // c1 has no successor. b2 has no successor. c2 has no successor.
        let frontier = dag.frontier();
        assert_eq!(frontier.len(), 3);
        assert!(frontier.contains(&b2));
        assert!(frontier.contains(&c1));
        assert!(frontier.contains(&c2));
    }
}

// CausalLedger, CausalTurn, and CausalTurnBuilder were deleted in Block 4.
// The node uses dregg_types::CausalDag directly; the ledger wrapper was dead production code.
// Tests for CausalDag remain in the causal_dag module above.

// ═══════════════════════════════════════════════════════════════════════════════
//  LAYER 2: ATOMIC MULTI-PARTY TESTS
// ═══════════════════════════════════════════════════════════════════════════════

mod atomic_forest_tests {
    use super::*;

    #[test]
    fn create_valid_atomic_forest() {
        let cell_a = make_cell(1, 10000);
        let cell_b = make_cell(2, 5000);

        let mut forest = CallForest::new();
        forest.add_root(Action {
            target: cell_a.id(),
            method: *blake3::hash(b"transfer").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: cell_a.id(),
                to: cell_b.id(),
                amount: 500,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });

        let af = AtomicForest::new(
            vec![node_id(1), node_id(2)],
            forest,
            vec![(
                cell_a.id(),
                Preconditions {
                    cell_state: Some(CellStatePrecondition {
                        min_balance: Some(500),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            )],
            cell_a.id(),
            0,
            None,
        );

        assert!(af.validate().is_ok());
        assert_eq!(af.participant_count(), 2);
        assert!(af.is_participant(&node_id(1)));
        assert!(af.is_participant(&node_id(2)));
        assert!(!af.is_participant(&node_id(3)));
    }

    #[test]
    fn empty_forest_rejected() {
        let af = AtomicForest::new(
            vec![node_id(1)],
            CallForest::new(), // empty
            vec![],
            CellId::from_bytes([0u8; 32]),
            0,
            None,
        );
        assert_eq!(af.validate().unwrap_err(), CoordError::EmptyForest);
    }

    #[test]
    fn no_participants_rejected() {
        let mut forest = CallForest::new();
        let cell_a = make_cell(1, 10000);
        forest.add_root(Action {
            target: cell_a.id(),
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::IncrementNonce { cell: cell_a.id() }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });

        let af = AtomicForest::new(vec![], forest, vec![], cell_a.id(), 0, None);
        assert_eq!(af.validate().unwrap_err(), CoordError::NoParticipants);
    }

    #[test]
    fn atomic_forest_builder() {
        let cell_a = make_cell(1, 10000);
        let _cell_b = make_cell(2, 5000);

        let mut forest = CallForest::new();
        forest.add_root(Action {
            target: cell_a.id(),
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::IncrementNonce { cell: cell_a.id() }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });

        let mut builder = AtomicForestBuilder::new();
        builder
            .add_participant(node_id(1))
            .add_participant(node_id(2))
            .set_forest(forest)
            .set_initiator(cell_a.id())
            .set_fee(0)
            .add_precondition(
                cell_a.id(),
                Preconditions {
                    cell_state: Some(CellStatePrecondition {
                        min_balance: Some(100),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            );

        let af = builder.build().unwrap();
        assert_eq!(af.participant_count(), 2);
        assert_eq!(af.preconditions.len(), 1);
    }
}

mod coordinator_tests {
    use super::*;
    use crate::atomic::CoordinatorState;

    fn setup_two_party() -> (
        Ledger,
        CellId,
        CellId,
        AtomicForest,
        Vec<[u8; 32]>,
        HashMap<[u8; 32], [u8; 32]>,
    ) {
        let mut ledger = Ledger::new();
        let cell_a = make_cell(1, 10000);
        let cell_b = make_cell(2, 5000);
        let id_a = ledger.insert_cell(cell_a).unwrap();
        let id_b = ledger.insert_cell(cell_b).unwrap();

        // Forest: A transfers 500 to B.
        let mut forest = CallForest::new();
        forest.add_root(Action {
            target: id_a,
            method: *blake3::hash(b"transfer").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: id_a,
                to: id_b,
                amount: 500,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });

        let af = AtomicForest::new(
            vec![node_id(1), node_id(2)],
            forest,
            vec![
                (
                    id_a,
                    Preconditions {
                        cell_state: Some(CellStatePrecondition {
                            min_balance: Some(500),
                            ..Default::default()
                        }),
                        ..Default::default()
                    },
                ),
                (id_b, Preconditions::default()),
            ],
            id_a,
            0,
            None,
        );

        let nodes = vec![node_id(1), node_id(2)];
        let (signing_keys, participant_keys) = make_participant_keys(&nodes);

        (ledger, id_a, id_b, af, signing_keys, participant_keys)
    }

    #[test]
    fn propose_from_idle() {
        let (_, _, _, af, _, participant_keys) = setup_two_party();
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );

        let msg = coord.propose(af).unwrap();
        assert_eq!(msg.coordinator, node_id(1));
        assert!(matches!(coord.state, CoordinatorState::Proposing { .. }));
    }

    #[test]
    fn propose_not_idle_error() {
        let (_, _, _, af, _, participant_keys) = setup_two_party();
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );
        let _prop_msg = coord.propose(af.clone()).unwrap();

        // Try to propose again while already proposing.
        let err = coord.propose(af).unwrap_err();
        assert!(matches!(
            err,
            CoordError::InvalidCoordinatorState {
                expected: "Idle",
                actual: "Proposing"
            }
        ));
    }

    #[test]
    fn invalid_threshold_error() {
        let (_, _, _, af, _, participant_keys) = setup_two_party();

        // Threshold 0.
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            0,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys.clone(),
        );
        let err = coord.propose(af.clone()).unwrap_err();
        assert!(matches!(
            err,
            CoordError::InvalidThreshold {
                threshold: 0,
                participants: 2
            }
        ));

        // Threshold 3 > 2 participants.
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            3,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );
        let err = coord.propose(af).unwrap_err();
        assert!(matches!(
            err,
            CoordError::InvalidThreshold {
                threshold: 3,
                participants: 2
            }
        ));
    }

    /// ⚑ THE cfg(test) DIVERGENCE, CLOSED — twin#3's gate-absent disposition is now IDENTICAL in a
    /// test build and in production.
    ///
    /// `Coordinator::evaluate_votes_no_gate` used to be TWO functions: fail-closed `Decision::Abort`
    /// under `cfg(not(test))`, and `evaluate_votes_native()` (which CAN RETURN `Commit`) under
    /// `cfg(test)`. So `cargo test -p dregg-coord` — the suite that would catch a regression in the
    /// production refusal — never ran the production refusal at all. Only
    /// `coord/tests/twin_fail_closed.rs`, which links this crate WITHOUT `cfg(test)`, ever did.
    ///
    /// This test is that integration test's IN-CRATE twin: same scenario, same crate, `cfg(test)` ON,
    /// no verified gate registered, no differential armed ⇒ the SAME `Abort`. The second half is its
    /// non-vacuity: with `NativeDifferentialArmed` held, the identical sequence reaches `Commit`, so
    /// the assertion above is a real property of the disposition and not a coordinator that cannot
    /// commit in this binary at all.
    #[test]
    fn gate_absent_disposition_is_identical_under_cfg_test_and_in_production() {
        let (_, _, _, af, signing_keys, participant_keys) = setup_two_party();
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );
        let prop_msg = coord.propose(af.clone()).unwrap();
        let sig_a = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &signing_keys[0]);
        coord.receive_vote(node_id(1), Vote::yes(sig_a)).unwrap();
        let sig_b = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &signing_keys[1]);
        let decided = coord.receive_vote(node_id(2), Vote::yes(sig_b)).unwrap();

        if decided == Some(Decision::Commit) {
            panic!(
                "cfg(test) DIVERGENCE: a full 2-of-2 Yes quorum COMMITTED with no verified 2PC gate \
                 registered. A deployed node returns Abort here (`evaluate_votes_no_gate`), so this \
                 test binary is exercising a DIFFERENT gate-absent disposition than production and \
                 cannot catch a regression in the real refusal."
            );
        }
        assert_eq!(
            decided,
            Some(Decision::Abort),
            "with no verified 2PC gate the live path must FAIL CLOSED to Abort under cfg(test) \
             exactly as it does in a release build"
        );

        // NON-VACUITY: the same sequence CAN reach Commit in this binary — via the DECLARED,
        // per-test native differential arming, and only via it.
        let (_, _, _, af2, sks2, pks2) = setup_two_party();
        let mut coord2 = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            pks2,
        );
        let prop2 = coord2.propose(af2.clone()).unwrap();
        let _native = crate::atomic::NativeDifferentialArmed::new();
        coord2
            .receive_vote(
                node_id(1),
                Vote::yes(Vote::sign_yes(&prop2.proposal_id, &af2.hash, &sks2[0])),
            )
            .unwrap();
        assert_eq!(
            coord2
                .receive_vote(
                    node_id(2),
                    Vote::yes(Vote::sign_yes(&prop2.proposal_id, &af2.hash, &sks2[1])),
                )
                .unwrap(),
            Some(Decision::Commit),
            "with the native differential ARMED the same quorum must commit — otherwise the \
             fail-closed assertion above is vacuous (a coordinator that can never commit trivially \
             satisfies it)"
        );
    }

    #[test]
    fn full_commit_path() {
        // ARM the NATIVE 2PC differential sibling BY NAME: `evaluate_votes_no_gate` has ONE
        // body for every cfg and it is the PRODUCTION fail-closed `Abort`, so a test that
        // asserts the native tally verdict through `receive_vote` says so explicitly.
        let _native = crate::atomic::NativeDifferentialArmed::new();
        let (mut ledger, id_a, id_b, af, signing_keys, participant_keys) = setup_two_party();
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );

        // Propose.
        let prop_msg = coord.propose(af.clone()).unwrap();

        // Node A votes yes with real Ed25519 signature.
        let sig_a = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &signing_keys[0]);
        let decision = coord.receive_vote(node_id(1), Vote::yes(sig_a)).unwrap();
        assert_eq!(decision, None); // Still pending.

        // Node B votes yes.
        let sig_b = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &signing_keys[1]);
        let decision = coord.receive_vote(node_id(2), Vote::yes(sig_b)).unwrap();
        assert_eq!(decision, Some(Decision::Commit));

        // Commit.
        let commit_msg = coord.commit(&mut ledger).unwrap();
        assert_eq!(commit_msg.signatures.len(), 2);

        // Verify state changes.
        assert_eq!(ledger.get(&id_a).unwrap().state.balance(), 9500);
        assert_eq!(ledger.get(&id_b).unwrap().state.balance(), 5500);

        // Coordinator is now Committed.
        assert!(matches!(coord.state, CoordinatorState::Committed { .. }));
    }

    #[test]
    fn abort_on_no_vote() {
        // ARM the NATIVE 2PC differential sibling BY NAME: `evaluate_votes_no_gate` has ONE
        // body for every cfg and it is the PRODUCTION fail-closed `Abort`, so a test that
        // asserts the native tally verdict through `receive_vote` says so explicitly.
        let _native = crate::atomic::NativeDifferentialArmed::new();
        let (_, _, _, af, signing_keys, participant_keys) = setup_two_party();
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );

        let prop_msg = coord.propose(af.clone()).unwrap();

        // Node A votes yes.
        let sig_a = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &signing_keys[0]);
        coord.receive_vote(node_id(1), Vote::yes(sig_a)).unwrap();

        // Node B votes no.
        let decision = coord
            .receive_vote(
                node_id(2),
                Vote::no(
                    "insufficient balance",
                    Vote::sign_no(&prop_msg.proposal_id, &af.hash, &signing_keys[1]),
                ),
            )
            .unwrap();
        assert_eq!(decision, Some(Decision::Abort));

        // Abort.
        let abort_msg = coord.abort("participant rejected").unwrap();
        assert_eq!(abort_msg.rejectors, vec![node_id(2)]);
        assert!(matches!(coord.state, CoordinatorState::Aborted { .. }));
    }

    #[test]
    fn unknown_participant_error() {
        let (_, _, _, af, _, participant_keys) = setup_two_party();
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );
        let _prop_msg = coord.propose(af).unwrap();

        // Unknown node votes.
        let err = coord
            .receive_vote(node_id(99), Vote::no("who am i", [0u8; 64]))
            .unwrap_err();
        assert!(matches!(err, CoordError::UnknownParticipant { .. }));
    }

    #[test]
    fn duplicate_vote_error() {
        let (_, _, _, af, signing_keys, participant_keys) = setup_two_party();
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );
        let prop_msg = coord.propose(af.clone()).unwrap();

        let sig = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &signing_keys[0]);
        coord.receive_vote(node_id(1), Vote::yes(sig)).unwrap();

        // Try to vote again.
        let err = coord
            .receive_vote(
                node_id(1),
                Vote::no(
                    "changed my mind",
                    Vote::sign_no(&prop_msg.proposal_id, &af.hash, &signing_keys[0]),
                ),
            )
            .unwrap_err();
        assert!(matches!(err, CoordError::DuplicateVote { .. }));
    }

    #[test]
    fn commit_without_threshold_error() {
        let (mut ledger, _, _, af, signing_keys, participant_keys) = setup_two_party();
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );
        let prop_msg = coord.propose(af.clone()).unwrap();

        // Only one vote.
        let sig = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &signing_keys[0]);
        coord.receive_vote(node_id(1), Vote::yes(sig)).unwrap();

        // Try to commit with only 1/2 votes.
        let err = coord.commit(&mut ledger).unwrap_err();
        assert!(matches!(
            err,
            CoordError::ThresholdNotMet {
                required: 2,
                received: 1
            }
        ));
    }

    #[test]
    fn threshold_one_of_two() {
        // ARM the NATIVE 2PC differential sibling BY NAME: `evaluate_votes_no_gate` has ONE
        // body for every cfg and it is the PRODUCTION fail-closed `Abort`, so a test that
        // asserts the native tally verdict through `receive_vote` says so explicitly.
        let _native = crate::atomic::NativeDifferentialArmed::new();
        let (mut ledger, id_a, id_b, af, signing_keys, participant_keys) = setup_two_party();
        // Only need 1 of 2 to commit.
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            1,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );

        let prop_msg = coord.propose(af.clone()).unwrap();

        // Single yes vote is enough.
        let sig = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &signing_keys[0]);
        let decision = coord.receive_vote(node_id(1), Vote::yes(sig)).unwrap();
        assert_eq!(decision, Some(Decision::Commit));

        let commit_msg = coord.commit(&mut ledger).unwrap();
        assert_eq!(commit_msg.signatures.len(), 1);

        assert_eq!(ledger.get(&id_a).unwrap().state.balance(), 9500);
        assert_eq!(ledger.get(&id_b).unwrap().state.balance(), 5500);
    }

    #[test]
    fn coordinator_reset() {
        let (_, _, _, af, _, participant_keys) = setup_two_party();
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );
        let _prop_msg = coord.propose(af).unwrap();
        assert!(matches!(coord.state, CoordinatorState::Proposing { .. }));

        coord.reset();
        assert!(matches!(coord.state, CoordinatorState::Idle));
    }

    #[test]
    fn invalid_signature_rejected() {
        let (_, _, _, af, _, participant_keys) = setup_two_party();
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );
        let _prop_msg = coord.propose(af.clone()).unwrap();

        // Fabricate a bad signature (all zeros).
        let bad_sig = [0u8; 64];
        let err = coord
            .receive_vote(node_id(1), Vote::yes(bad_sig))
            .unwrap_err();
        assert!(matches!(err, CoordError::InvalidVoteSignature { .. }));
    }

    #[test]
    fn wrong_key_signature_rejected() {
        let (_, _, _, af, _, participant_keys) = setup_two_party();
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );
        let prop_msg = coord.propose(af.clone()).unwrap();

        // Sign with the wrong key (node 2's key for node 1's vote).
        let (wrong_sk, _) = make_keypair(2);
        let wrong_sig = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &wrong_sk);
        let err = coord
            .receive_vote(node_id(1), Vote::yes(wrong_sig))
            .unwrap_err();
        assert!(matches!(err, CoordError::InvalidVoteSignature { .. }));
    }

    #[test]
    fn budget_exceeded_rejected() {
        let (_, _, _, af, _, participant_keys) = setup_two_party();
        // Use default costs with a very tight budget.
        let costs = ComputronCosts::default_costs();
        // The forest has 1 action, so estimated cost = action_base + effect_base = 150.
        // Set max_budget to 10 (way too low).
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            costs,
            10,
            participant_keys,
        );
        let err = coord.propose(af).unwrap_err();
        assert!(matches!(err, CoordError::BudgetExceeded { .. }));
    }

    /// This is the property the whole `AtomicForest::valid_until` field exists for:
    /// a stale proposal must be REFUSED at commit, not silently accepted.
    ///
    /// Non-vacuity matters more here than in most tests: before this fix, this exact
    /// scenario committed successfully — twice over. `Turn { valid_until: None, .. }`
    /// skipped the executor's expiration check entirely
    /// (`turn/src/executor/execute.rs:426`), AND even with a real `Some(past)` deadline,
    /// `TurnExecutor::new`'s default `current_timestamp: 0` meant `0 > valid_until` was
    /// false for any realistic (positive, post-1970) deadline — the check could never
    /// fire either way. Both gaps are closed by this commit; this test would have
    /// FAILED (committed instead of rejecting) against the pre-fix code on either count.
    #[test]
    fn commit_refuses_a_forest_whose_deadline_has_already_passed() {
        let _native = crate::atomic::NativeDifferentialArmed::new();
        let (mut ledger, _id_a, _id_b, stale_af, signing_keys, participant_keys) =
            setup_two_party();
        // Rebuild the SAME forest with a deadline far in the past (1970 + 1 day).
        let stale_af = AtomicForest::new(
            stale_af.participants,
            stale_af.forest,
            stale_af.preconditions,
            stale_af.initiator,
            stale_af.fee,
            Some(86_400),
        );
        let mut coord = Coordinator::new(
            node_id(1),
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );

        let prop_msg = coord.propose(stale_af.clone()).unwrap();
        let sig_a = Vote::sign_yes(&prop_msg.proposal_id, &stale_af.hash, &signing_keys[0]);
        coord.receive_vote(node_id(1), Vote::yes(sig_a)).unwrap();
        let sig_b = Vote::sign_yes(&prop_msg.proposal_id, &stale_af.hash, &signing_keys[1]);
        let decision = coord.receive_vote(node_id(2), Vote::yes(sig_b)).unwrap();
        assert_eq!(decision, Some(Decision::Commit), "quorum reached, as normal");

        let err = coord
            .commit(&mut ledger)
            .expect_err("a Turn whose valid_until is in 1970 must be refused, not committed");
        assert!(
            matches!(
                err,
                CoordError::TurnExecution(dregg_turn::TurnError::Expired { .. })
            ),
            "expected TurnError::Expired, got: {err:?}"
        );
    }
}

mod participant_tests {
    use super::*;
    use crate::atomic::CommitMessage;
    use dregg_turn::TurnReceipt;

    fn setup_participant_scenario() -> (
        Ledger,
        CellId,
        CellId,
        AtomicForest,
        Vec<[u8; 32]>,
        HashMap<[u8; 32], [u8; 32]>,
    ) {
        let mut ledger = Ledger::new();
        let cell_a = make_cell(1, 10000);
        let cell_b = make_cell(2, 5000);
        let id_a = ledger.insert_cell(cell_a).unwrap();
        let id_b = ledger.insert_cell(cell_b).unwrap();

        let mut forest = CallForest::new();
        forest.add_root(Action {
            target: id_a,
            method: *blake3::hash(b"transfer").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: id_a,
                to: id_b,
                amount: 500,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });

        let af = AtomicForest::new(
            vec![node_id(1), node_id(2)],
            forest,
            vec![
                (
                    id_a,
                    Preconditions {
                        cell_state: Some(CellStatePrecondition {
                            min_balance: Some(500),
                            ..Default::default()
                        }),
                        ..Default::default()
                    },
                ),
                (id_b, Preconditions::default()),
            ],
            id_a,
            0,
            None,
        );

        let nodes = vec![node_id(1), node_id(2)];
        let (signing_keys, participant_keys) = make_participant_keys(&nodes);

        (ledger, id_a, id_b, af, signing_keys, participant_keys)
    }

    #[test]
    fn participant_votes_yes_when_preconditions_met() {
        let (ledger, id_a, _, af, signing_keys, _) = setup_participant_scenario();
        let mut participant =
            Participant::with_costs(id_a, node_id(1), signing_keys[0], ledger, zero_costs());

        let vote = participant.evaluate_proposal(&af.hash, &af);
        assert!(vote.is_yes());
    }

    #[test]
    fn participant_votes_no_when_preconditions_fail() {
        let (mut ledger, id_a, _, af, signing_keys, _) = setup_participant_scenario();

        // Drain A's balance so precondition (min_balance: 500) fails.
        ledger.get_mut(&id_a).unwrap().state.set_balance(100);

        let mut participant =
            Participant::with_costs(id_a, node_id(1), signing_keys[0], ledger, zero_costs());
        let vote = participant.evaluate_proposal(&af.hash, &af);
        assert!(vote.is_no());
    }

    #[test]
    fn participant_votes_no_when_not_participant() {
        let (ledger, id_a, _, af, _, _) = setup_participant_scenario();

        // Create participant with node_id(99) which is not in the forest.
        let (sk_99, _) = make_keypair(99);
        let mut participant =
            Participant::with_costs(id_a, node_id(99), sk_99, ledger, zero_costs());
        let vote = participant.evaluate_proposal(&af.hash, &af);
        assert!(vote.is_no());
        if let Vote::No { reason, .. } = vote {
            assert!(reason.contains("not listed as participant"));
        }
    }

    #[test]
    fn participant_applies_commit() {
        let (ledger, id_a, id_b, af, signing_keys, participant_keys) = setup_participant_scenario();
        let mut participant =
            Participant::with_costs(id_a, node_id(1), signing_keys[0], ledger, zero_costs());

        // Build a mock commit message with valid QC signatures.
        let proposal_id = af.hash; // Use forest hash as proposal_id for test.
        let sig_1 = Vote::sign_yes(&proposal_id, &af.hash, &signing_keys[0]);
        let sig_2 = Vote::sign_yes(&proposal_id, &af.hash, &signing_keys[1]);
        let commit = CommitMessage {
            proposal_id,
            receipt: dregg_turn::TurnReceipt {
                turn_hash: [0u8; 32],
                forest_hash: [0u8; 32],
                pre_state_hash: [0u8; 32],
                post_state_hash: [0u8; 32],
                timestamp: 0,
                effects_hash: [0u8; 32],
                computrons_used: 0,
                action_count: 1,
                previous_receipt_hash: None,
                agent: id_a,
                federation_id: [0u8; 32],
                routing_directives: vec![],
                introduction_exports: vec![],
                derivation_records: vec![],
                emitted_events: vec![],
                executor_signature: None,
                finality: Default::default(),
                was_encrypted: false,
                was_burn: false,
                consumed_capabilities: vec![],
            },
            signatures: vec![(node_id(1), sig_1), (node_id(2), sig_2)],
        };

        let receipt = participant
            .apply_commit(&commit, &af, &participant_keys, 2)
            .unwrap();
        assert_eq!(receipt.action_count, 1);

        // Verify local state updated.
        assert_eq!(participant.ledger.get(&id_a).unwrap().state.balance(), 9500);
        assert_eq!(participant.ledger.get(&id_b).unwrap().state.balance(), 5500);
    }

    /// The participant-side twin of
    /// `coordinator_tests::commit_refuses_a_forest_whose_deadline_has_already_passed`:
    /// `apply_commit` must refuse a forest whose `valid_until` has already passed too,
    /// not just `commit`. This is the scenario the whole design exists for — a
    /// participant applying a QC-certified commit long after the coordinator built it —
    /// so it is deliberately NOT the same forest object as the coordinator's test, only
    /// the same shape: this participant only ever sees what arrives over the wire.
    #[test]
    fn apply_commit_refuses_a_forest_whose_deadline_has_already_passed() {
        let (ledger, id_a, id_b, af, signing_keys, participant_keys) =
            setup_participant_scenario();
        let stale_af = AtomicForest::new(
            af.participants,
            af.forest,
            af.preconditions,
            af.initiator,
            af.fee,
            Some(86_400), // 1970 + 1 day — long expired by wall-clock "now".
        );
        let mut participant =
            Participant::with_costs(id_a, node_id(1), signing_keys[0], ledger, zero_costs());

        let proposal_id = stale_af.hash;
        let sig_1 = Vote::sign_yes(&proposal_id, &stale_af.hash, &signing_keys[0]);
        let sig_2 = Vote::sign_yes(&proposal_id, &stale_af.hash, &signing_keys[1]);
        let commit = CommitMessage {
            proposal_id,
            receipt: dregg_turn::TurnReceipt {
                turn_hash: [0u8; 32],
                forest_hash: [0u8; 32],
                pre_state_hash: [0u8; 32],
                post_state_hash: [0u8; 32],
                timestamp: 0,
                effects_hash: [0u8; 32],
                computrons_used: 0,
                action_count: 1,
                previous_receipt_hash: None,
                agent: id_a,
                federation_id: [0u8; 32],
                routing_directives: vec![],
                introduction_exports: vec![],
                derivation_records: vec![],
                emitted_events: vec![],
                executor_signature: None,
                finality: Default::default(),
                was_encrypted: false,
                was_burn: false,
                consumed_capabilities: vec![],
            },
            signatures: vec![(node_id(1), sig_1), (node_id(2), sig_2)],
        };

        let err = participant
            .apply_commit(&commit, &stale_af, &participant_keys, 2)
            .expect_err("a Turn whose valid_until is in 1970 must be refused, not applied");
        assert!(
            matches!(
                err,
                CoordError::TurnExecution(dregg_turn::TurnError::Expired { .. })
            ),
            "expected TurnError::Expired, got: {err:?}"
        );
        // And the ledger must be UNTOUCHED — a refused apply must not partially move state.
        assert_eq!(participant.ledger.get(&id_a).unwrap().state.balance(), 10000);
        assert_eq!(participant.ledger.get(&id_b).unwrap().state.balance(), 5000);
    }

    #[test]
    fn participant_verifies_commit_signatures() {
        let (ledger, id_a, _, af, signing_keys, participant_keys) = setup_participant_scenario();
        let participant = Participant::with_costs(
            id_a,
            node_id(1),
            signing_keys[0],
            ledger.clone(),
            zero_costs(),
        );

        // Build valid commit message with real Ed25519 signatures.
        let proposal_id = af.hash; // Use forest hash as proposal_id for test.
        let sig_1 = Vote::sign_yes(&proposal_id, &af.hash, &signing_keys[0]);
        let sig_2 = Vote::sign_yes(&proposal_id, &af.hash, &signing_keys[1]);

        let commit = CommitMessage {
            proposal_id,
            receipt: TurnReceipt {
                turn_hash: [0u8; 32],
                forest_hash: [0u8; 32],
                pre_state_hash: [0u8; 32],
                post_state_hash: [0u8; 32],
                timestamp: 0,
                effects_hash: [0u8; 32],
                computrons_used: 0,
                action_count: 1,
                previous_receipt_hash: None,
                agent: id_a,
                federation_id: [0u8; 32],
                routing_directives: vec![],
                introduction_exports: vec![],
                derivation_records: vec![],
                emitted_events: vec![],
                executor_signature: None,
                finality: Default::default(),
                was_encrypted: false,
                was_burn: false,
                consumed_capabilities: vec![],
            },
            signatures: vec![(node_id(1), sig_1), (node_id(2), sig_2)],
        };

        assert!(participant.verify_commit(&commit, &af, &participant_keys));

        // Corrupt a signature.
        let mut bad_commit = commit;
        bad_commit.signatures[0].1[0] ^= 0xff;
        assert!(!participant.verify_commit(&bad_commit, &af, &participant_keys));
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  INTEGRATION TESTS: BOTH LAYERS TOGETHER
// ═══════════════════════════════════════════════════════════════════════════════

mod integration {
    use super::*;

    /// Test that sequential turns and atomic turns can coexist on the same ledger.
    #[test]
    fn causal_then_atomic_on_same_ledger() {
        // ARM the NATIVE 2PC differential sibling BY NAME: `evaluate_votes_no_gate` has ONE
        // body for every cfg and it is the PRODUCTION fail-closed `Abort`, so a test that
        // asserts the native tally verdict through `receive_vote` says so explicitly.
        let _native = crate::atomic::NativeDifferentialArmed::new();
        let mut ledger = Ledger::new();
        let mut cell_a = make_cell(1, 10000);
        let cell_b = make_cell(2, 5000);
        let id_b = cell_b.id();
        // Grant cell_a a capability to reach cell_b (needed for cross-cell actions).
        cell_a
            .capabilities
            .grant(id_b, dregg_cell::AuthRequired::None);
        let id_a = ledger.insert_cell(cell_a).unwrap();
        ledger.insert_cell(cell_b).unwrap();

        let node_a = node_id(1);
        let node_b = node_id(2);
        let (signing_keys, participant_keys) = make_participant_keys(&[node_a, node_b]);

        // Phase 1: Apply a turn directly against the ledger (no CausalLedger wrapper).
        // CausalLedger was deleted; production code routes through dregg_turn::TurnExecutor.
        {
            use dregg_turn::TurnExecutor;
            let executor = TurnExecutor::new(zero_costs());
            let t1 = make_transfer_turn(id_a, id_a, id_b, 1000, 0, 0);
            executor.execute(&t1, &mut ledger);
        }

        // After direct turn: A=9000, B=6000.
        assert_eq!(ledger.get(&id_a).unwrap().state.balance(), 9000);
        assert_eq!(ledger.get(&id_b).unwrap().state.balance(), 6000);

        // Phase 2: Atomic turn on the same ledger state.

        let mut forest = CallForest::new();
        forest.add_root(Action {
            target: id_b,
            method: *blake3::hash(b"atomic_swap").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: id_b,
                to: id_a,
                amount: 2000,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });

        let af = AtomicForest::new(
            vec![node_a, node_b],
            forest,
            vec![
                (id_a, Preconditions::default()),
                (
                    id_b,
                    Preconditions {
                        cell_state: Some(CellStatePrecondition {
                            min_balance: Some(2000),
                            ..Default::default()
                        }),
                        ..Default::default()
                    },
                ),
            ],
            id_a,
            0,
            None,
        );

        let mut coord = Coordinator::new(
            node_a,
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );
        let prop_msg = coord.propose(af.clone()).unwrap();

        // Both vote yes.
        let sig_a = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &signing_keys[0]);
        coord.receive_vote(node_a, Vote::yes(sig_a)).unwrap();
        let sig_b = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &signing_keys[1]);
        let decision = coord.receive_vote(node_b, Vote::yes(sig_b)).unwrap();
        assert_eq!(decision, Some(Decision::Commit));

        // Note: agent nonce is 1 now (after the direct turn).
        // The coordinator builds a turn with the current nonce.
        coord.commit(&mut ledger).unwrap();

        // Final state: A=9000+2000=11000, B=6000-2000=4000.
        assert_eq!(ledger.get(&id_a).unwrap().state.balance(), 11000);
        assert_eq!(ledger.get(&id_b).unwrap().state.balance(), 4000);
    }

    /// Test three-party atomic turn with majority threshold.
    #[test]
    fn three_party_majority_threshold() {
        // ARM the NATIVE 2PC differential sibling BY NAME: `evaluate_votes_no_gate` has ONE
        // body for every cfg and it is the PRODUCTION fail-closed `Abort`, so a test that
        // asserts the native tally verdict through `receive_vote` says so explicitly.
        let _native = crate::atomic::NativeDifferentialArmed::new();
        let mut ledger = Ledger::new();
        let cell_a = make_cell(1, 10000);
        let cell_b = make_cell(2, 5000);
        let cell_c = make_cell(3, 3000);
        let id_a = ledger.insert_cell(cell_a).unwrap();
        let id_b = ledger.insert_cell(cell_b).unwrap();
        let id_c = ledger.insert_cell(cell_c).unwrap();

        let node_a = node_id(1);
        let node_b = node_id(2);
        let node_c = node_id(3);
        let (signing_keys, participant_keys) = make_participant_keys(&[node_a, node_b, node_c]);

        // A transfers 100 to both B and C.
        let mut forest = CallForest::new();
        forest.add_root(Action {
            target: id_a,
            method: *blake3::hash(b"multi_transfer").as_bytes(),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![
                Effect::Transfer {
                    from: id_a,
                    to: id_b,
                    amount: 100,
                },
                Effect::Transfer {
                    from: id_a,
                    to: id_c,
                    amount: 100,
                },
            ],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });

        let af = AtomicForest::new(
            vec![node_a, node_b, node_c],
            forest,
            vec![
                (
                    id_a,
                    Preconditions {
                        cell_state: Some(CellStatePrecondition {
                            min_balance: Some(200),
                            ..Default::default()
                        }),
                        ..Default::default()
                    },
                ),
                (id_b, Preconditions::default()),
                (id_c, Preconditions::default()),
            ],
            id_a,
            0,
            None,
        );

        // Threshold 2 of 3 (majority).
        let mut coord = Coordinator::new(
            node_a,
            coord_signing_key(),
            2,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );
        let prop_msg = coord.propose(af.clone()).unwrap();

        // A votes yes.
        let sig_a = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &signing_keys[0]);
        coord.receive_vote(node_a, Vote::yes(sig_a)).unwrap();

        // B votes yes — threshold reached!
        let sig_b = Vote::sign_yes(&prop_msg.proposal_id, &af.hash, &signing_keys[1]);
        let decision = coord.receive_vote(node_b, Vote::yes(sig_b)).unwrap();
        assert_eq!(decision, Some(Decision::Commit));

        // Commit even though C hasn't voted.
        coord.commit(&mut ledger).unwrap();

        assert_eq!(ledger.get(&id_a).unwrap().state.balance(), 9800);
        assert_eq!(ledger.get(&id_b).unwrap().state.balance(), 5100);
        assert_eq!(ledger.get(&id_c).unwrap().state.balance(), 3100);
    }

    /// Test early abort: if enough No votes come in that threshold can never be met.
    #[test]
    fn early_abort_on_enough_no_votes() {
        // ARM the NATIVE 2PC differential sibling BY NAME: `evaluate_votes_no_gate` has ONE
        // body for every cfg and it is the PRODUCTION fail-closed `Abort`, so a test that
        // asserts the native tally verdict through `receive_vote` says so explicitly.
        let _native = crate::atomic::NativeDifferentialArmed::new();
        let mut ledger = Ledger::new();
        let cell_a = make_cell(1, 10000);
        let cell_b = make_cell(2, 5000);
        let cell_c = make_cell(3, 3000);
        let id_a = ledger.insert_cell(cell_a).unwrap();
        let _id_b = ledger.insert_cell(cell_b).unwrap();
        let _id_c = ledger.insert_cell(cell_c).unwrap();

        let node_a = node_id(1);
        let node_b = node_id(2);
        let node_c = node_id(3);
        let (signing_keys, participant_keys) = make_participant_keys(&[node_a, node_b, node_c]);

        let mut forest = CallForest::new();
        forest.add_root(Action {
            target: id_a,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::IncrementNonce { cell: id_a }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });

        let af = AtomicForest::new(vec![node_a, node_b, node_c], forest, vec![], id_a, 0, None);

        // Need all 3.
        let mut coord = Coordinator::new(
            node_a,
            coord_signing_key(),
            3,
            zero_costs(),
            TEST_MAX_BUDGET,
            participant_keys,
        );
        let prop_msg = coord.propose(af.clone()).unwrap();

        // B votes no — now max possible yes is 2, but threshold is 3.
        let decision = coord
            .receive_vote(
                node_b,
                Vote::no(
                    "nope",
                    Vote::sign_no(&prop_msg.proposal_id, &af.hash, &signing_keys[1]),
                ),
            )
            .unwrap();
        assert_eq!(decision, Some(Decision::Abort));
    }
}

mod valid_until_tests {
    use super::*;
    use crate::atomic::default_valid_until;

    /// The sentinel must be `Some` — `None` here skips the executor's expiration check
    /// entirely (`turn/src/executor/execute.rs:426`), so a `Turn` built from a forest
    /// that used this default would never expire, no matter how stale.
    #[test]
    fn default_valid_until_is_some() {
        assert!(
            default_valid_until().is_some(),
            "a None here means every atomic turn using this default never expires — see \
             the doc comment on default_valid_until"
        );
    }

    /// The stamped deadline must be a future wall-clock second count.
    #[test]
    fn default_valid_until_is_a_future_wall_clock_horizon() {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        let stamped =
            default_valid_until().expect("must be Some, see default_valid_until_is_some");
        assert!(
            stamped > now,
            "stamped valid_until ({stamped}) must be strictly after now ({now})"
        );
    }

    /// `AtomicForestBuilder::new()` must default to an expiring deadline, not `None` — a
    /// caller who forgets to call `set_valid_until` should still get a safe forest.
    #[test]
    fn builder_defaults_to_an_expiring_deadline_not_none() {
        let cell_a = make_cell(1, 10000);
        let mut forest = CallForest::new();
        forest.add_root(Action {
            target: cell_a.id(),
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::IncrementNonce { cell: cell_a.id() }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });
        let mut builder = AtomicForestBuilder::new();
        builder
            .add_participant(node_id(1))
            .set_forest(forest)
            .set_initiator(cell_a.id());
        // Deliberately never calls set_valid_until().
        let af = builder.build().unwrap();
        assert!(
            af.valid_until.is_some(),
            "a builder whose caller never calls set_valid_until() must still default to \
             Some(..), not None"
        );
    }

    /// `AtomicForest`'s hash MUST change when `valid_until` changes — it travels inside
    /// the same hashed/signed envelope every Yes vote is bound to (see the field's doc
    /// comment on why: the deadline must be decided ONCE and be tamper-evident, not
    /// re-derivable independently by whoever later turns the forest into a `Turn`).
    #[test]
    fn hash_changes_when_valid_until_changes() {
        let mut forest = CallForest::new();
        forest.add_root(Action {
            target: CellId::from_bytes([1u8; 32]),
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });
        let participants = vec![node_id(1)];
        let initiator = CellId::from_bytes([1u8; 32]);

        let af_none = AtomicForest::new(
            participants.clone(),
            forest.clone(),
            vec![],
            initiator,
            0,
            None,
        );
        let af_some = AtomicForest::new(participants, forest, vec![], initiator, 0, Some(12345));

        assert_ne!(
            af_none.hash, af_some.hash,
            "changing valid_until must change the forest hash, or a participant's Yes vote \
             would not actually bind them to the deadline they were shown"
        );
    }

    /// Ratchet against the unbounded `valid_until` sentinel regrowing in the two places
    /// this module builds a `Turn` from an `AtomicForest`: `Coordinator::commit` and
    /// `Participant::apply_commit`. `include_str!` reads `atomic.rs` at COMPILE time, so
    /// this cannot go stale against what actually ships.
    #[test]
    fn no_atomic_turn_rebuilds_the_unbounded_valid_until_sentinel() {
        let src = include_str!("atomic.rs");
        let sentinel_field = "valid_until";
        let sentinel_value = "None";
        let needle = format!("{sentinel_field}: {sentinel_value},");
        assert!(
            !src.contains(&needle),
            "atomic.rs builds a Turn with `{sentinel_field}` bound to a bare \
             `{sentinel_value}` — this turn will NEVER expire (the executor's expiration \
             check is skipped entirely when this field is `{sentinel_value}`, \
             turn/src/executor/execute.rs:426). Read it from the AtomicForest instead, as \
             both commit() and apply_commit() now do."
        );
    }
}
