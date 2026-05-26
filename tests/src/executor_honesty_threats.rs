//! Executor-honesty threat tests, T1-T15 from `EXECUTOR-HONESTY-AUDIT.md`.
//!
//! Layer: AIR + canonical signing message + verifier-side replay.
//!
//! Each test exercises *one* of the threats from the audit and proves the
//! corresponding defense triggers. Tests that depend on yet-to-land
//! single-cell AIR-binding work are marked `#[ignore]` with the audit's
//! `[stage7-cont]` or other unblock-by-lane label.
//!
//! Threats are the audit's enumeration — keep this file's order matched to
//! the audit so a reader can cross-reference.

use std::collections::HashMap;

use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
use dregg_turn::action::{Action, Authorization, symbol};
use dregg_turn::{CallForest, DelegationMode, Effect, Turn};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn permissive_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(31);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

fn one_action_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: symbol("test"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
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

// ===========================================================================
// T1 — Reorder effects within a turn
// ===========================================================================

#[test]
fn t1_turn_hash_covers_effect_order() {
    // The defense: effects_hash is ordered. Two turns with the same effects
    // in different order must produce different turn hashes.
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let e1 = Effect::Transfer {
        from: a,
        to: b,
        amount: 10,
    };
    let e2 = Effect::Transfer {
        from: a,
        to: b,
        amount: 20,
    };
    let t_12 = one_action_turn(a, 0, vec![e1.clone(), e2.clone()]);
    let t_21 = one_action_turn(a, 0, vec![e2, e1]);
    assert_ne!(
        t_12.hash(),
        t_21.hash(),
        "effect order must change turn hash"
    );
}

#[test]
#[ignore = "blocked on Stage 7 cont §B verification: AIR's EFFECTS_HASH_BASE row-0 boundary binds to in-trace effect bytes; this test reconstructs a trace with reordered effects and shows the AIR rejects the resulting proof"]
fn t1_air_rejects_reordered_effects_in_trace() {
    panic!("blocked");
}

// ===========================================================================
// T2 — Invent effects the actor did not sign
// ===========================================================================

#[test]
fn t2_turn_hash_covers_effect_count() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let e1 = Effect::Transfer {
        from: a,
        to: b,
        amount: 10,
    };
    let e2 = Effect::Transfer {
        from: a,
        to: b,
        amount: 5,
    };
    let t_one = one_action_turn(a, 0, vec![e1.clone()]);
    let t_two = one_action_turn(a, 0, vec![e1, e2]);
    assert_ne!(
        t_one.hash(),
        t_two.hash(),
        "inventing an extra effect must change turn hash"
    );
}

#[test]
#[ignore = "blocked on EXECUTOR-HONESTY-AUDIT.md T2 gap: confirm verify path is THE ONLY way into TurnExecutor; CI guard for new Authorization::Unchecked regressions"]
fn t2_no_authorization_unchecked_in_production_paths() {
    panic!("blocked");
}

// ===========================================================================
// T3 — Skip / omit effects from a signed turn
// ===========================================================================

#[test]
#[ignore = "blocked on Stage 7 cont §B AIR termination constraint: EFFECTS_HASH_GLOBAL must terminate at the PI-exposed effects_hash; omitting an effect breaks the chain"]
fn t3_air_rejects_omitted_effect() {
    panic!("blocked");
}

// ===========================================================================
// T4 — Lie about pre/post state hash
// ===========================================================================

#[test]
#[ignore = "blocked on EXECUTOR-HONESTY-AUDIT.md T4 open question: row-0/row-last aux-bind of STATE_BEFORE_BASE / STATE_AFTER_BASE in effect_vm.rs"]
fn t4_air_binds_pre_state_hash_to_trace() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on T4: same for post-state"]
fn t4_air_binds_post_state_hash_to_trace() {
    panic!("blocked");
}

// ===========================================================================
// T5 — Reuse a nonce
// ===========================================================================

#[test]
fn t5_executor_rejects_replayed_nonce() {
    // The executor's runtime check: it increments cell.nonce when a turn
    // executes and rejects any turn whose `nonce` doesn't match the current
    // cell.nonce.
    let cell = permissive_cell(1, 1_000);
    let agent = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let t1 = one_action_turn(agent, 0, vec![]);
    let r1 = executor.execute(&t1, &mut ledger);
    assert!(matches!(
        r1,
        TurnResult::Committed { .. } | TurnResult::Rejected { .. }
    ));

    // Submit a turn with nonce=0 again — must reject (nonce should now be 1).
    let t1_replay = one_action_turn(agent, 0, vec![]);
    let r_replay = executor.execute(&t1_replay, &mut ledger);
    assert!(
        matches!(r_replay, TurnResult::Rejected { .. }),
        "expected nonce-replay reject, got: {r_replay:?}"
    );
}

#[test]
#[ignore = "blocked on Stage 7 cont §B: AIR's row-0 BoundaryConstraint on STATE_BEFORE_BASE+NONCE == PI[ACTOR_NONCE]; this test confirms the AIR layer's defense (executor-layer covered above)"]
fn t5_air_rejects_proof_with_wrong_nonce_pi() {
    panic!("blocked");
}

// ===========================================================================
// T6 — Replay a turn from another federation / ledger
// ===========================================================================

#[test]
#[ignore = "blocked on EXECUTOR-HONESTY-AUDIT.md T6 open question: canonical signing message must include federation_id"]
fn t6_signed_turn_for_federation_a_rejects_on_federation_b() {
    panic!("blocked");
}

// ===========================================================================
// T7 — Forge a receipt signature
// ===========================================================================

#[test]
#[ignore = "blocked on EXECUTOR-HONESTY-AUDIT.md T7: a receipt signed by a non-executor key must reject"]
fn t7_receipt_signed_by_wrong_key_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on T7 tail: receipt must explicitly name the executor whose key is verified"]
fn t7_receipt_carries_executor_identity() {
    panic!("blocked");
}

// ===========================================================================
// T8 — Insert a fake previous_receipt_hash link
// ===========================================================================

#[test]
#[ignore = "blocked on stage7-cont trace-side binding of PREVIOUS_RECEIPT_HASH (EXECUTOR-HONESTY-AUDIT.md T8)"]
fn t8_verifier_rejects_fake_previous_receipt_hash() {
    panic!("blocked");
}

// ===========================================================================
// T9 — Skip sovereign-witness verification
// ===========================================================================

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth (AUDIT-sovereign-witness-teeth.md, Stage 9 polish)"]
fn t9_sovereign_witness_skip_rejected_by_air() {
    panic!("blocked");
}

// ===========================================================================
// T10 — Skip a permission / capability check
// ===========================================================================

#[test]
fn t10_executor_rejects_transfer_without_required_capability() {
    // Setup: A → B Transfer, but A has no cap to B and B's `send`
    // permission requires a signature.
    let a_cell = {
        let mut c = permissive_cell(10, 1_000);
        // Tighten send permission to require a sig, but DON'T grant any
        // capabilities — so the action should fail authorization.
        c.permissions.send = AuthRequired::Signature;
        c
    };
    let a = a_cell.id();
    let b_cell = permissive_cell(11, 0);
    let b = b_cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(a_cell).unwrap();
    ledger.insert_cell(b_cell).unwrap();

    let turn = one_action_turn(
        a,
        0,
        vec![Effect::Transfer {
            from: a,
            to: b,
            amount: 1,
        }],
    );
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "transfer without auth must reject, got: {result:?}"
    );
}

#[test]
#[ignore = "blocked on stage7-cont P1.C: 4 CapTP variants (ExportSturdyRef, EnlivenRef, DropRef, ValidateHandoff) verify Merkle membership and are not tautological"]
fn t10_captp_variants_use_real_merkle_membership() {
    panic!("blocked");
}

// ===========================================================================
// T11 — Submit a stale / cached proof for a new turn
// ===========================================================================

#[test]
#[ignore = "blocked on EXECUTOR-HONESTY-AUDIT.md T11 confirmation: verifier requires TURN_HASH PI matches the receipt's claimed turn_hash"]
fn t11_stale_proof_replay_rejected_by_verifier() {
    // Build proof P_1 for Turn_1, then submit a receipt that claims to be
    // for Turn_2 but attaches P_1. Verifier must reject — TURN_HASH PI
    // mismatch.
    panic!("blocked");
}

// ===========================================================================
// T12 — Lie about balance deltas
// ===========================================================================

#[test]
#[ignore = "blocked on EXECUTOR-HONESTY-AUDIT.md T12 confirmation: Stage 8 P2.D conservation derivation in the builder; gallery file consistent"]
fn t12_balance_delta_must_match_transfer_amounts() {
    panic!("blocked");
}

// ===========================================================================
// T13 — Cross-cell aliasing (same cell_id in two federations)
// ===========================================================================

#[test]
#[ignore = "blocked on EXECUTOR-HONESTY-AUDIT.md T13: Cell::remote_stub_with_id escape hatch must be constrained by federation membership + CapTP origin attestation"]
fn t13_remote_stub_with_id_cannot_mint_arbitrary_cell_ids() {
    panic!("blocked");
}

// ===========================================================================
// T14 — Skip the AIR proof entirely
// ===========================================================================

#[test]
#[ignore = "blocked on protocol requirement: a receipt without a proof must be invalid at the wire level (not merely unverifiable)"]
fn t14_receipt_without_proof_rejected_at_wire_level() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on protocol requirement: standalone dregg-verifier binary rejects receipt with malformed proof bytes"]
fn t14_malformed_proof_bytes_rejected() {
    panic!("blocked");
}

// ===========================================================================
// T15 — Forge the effects_hash → AIR pass over a different effect list
// ===========================================================================

#[test]
#[ignore = "blocked on stage7-cont trace-side binding: in-trace effects must derive the PI-exposed effects_hash (EFFECTS_HASH_GLOBAL termination)"]
fn t15_trace_effects_must_match_pi_effects_hash() {
    panic!("blocked");
}

// ===========================================================================
// Cross-cutting (audit §"Cross-cutting open questions")
// ===========================================================================

#[test]
#[ignore = "blocked on T-cross-cutting #1: trace-side binding completeness audit (ACTOR_NONCE, EFFECTS_HASH_GLOBAL, TURN_HASH, PRE/POST_STATE, PREVIOUS_RECEIPT_HASH)"]
fn cross_cutting_all_pi_fields_trace_bound() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on T-cross-cutting #2: canonical signing message contains {domain, federation_id, actor_id, nonce, effects_hash, previous_receipt_hash}"]
fn cross_cutting_canonical_signing_message_fields() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on T-cross-cutting #3: verifier walks every PI and checks it (not just deserialized)"]
fn cross_cutting_verifier_checks_all_pi() {
    panic!("blocked");
}

// ===========================================================================
// Bonus: Bearer-cap T2 cousin — verify bearer permissions cannot exceed
// delegator (E-language facet attenuation).
// ===========================================================================

#[test]
fn bearer_cap_permissions_cannot_amplify_unchecked_baseline() {
    // Sanity: BearerCapProof has an `allowed_effects: Option<EffectMask>` field;
    // verify the construction round-trips and the executor's verify path
    // is at least exercised. The actual attenuation enforcement is in
    // protocol-tests/src/invariants/facet_attenuation.rs.
    let target = CellId([42u8; 32]);
    let bearer = BearerCapProof {
        target,
        permissions: AuthRequired::None,
        delegation_proof: DelegationProofData::SignedDelegation {
            delegator_pk: [1u8; 32],
            signature: [0u8; 64],
            bearer_pk: [2u8; 32],
        },
        expires_at: 100,
        revocation_channel: None,
        allowed_effects: None,
    };
    let auth = Authorization::Bearer(bearer);
    let a = CellId([99u8; 32]);
    let act = Action {
        target: a,
        method: symbol("test"),
        args: vec![],
        authorization: auth,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    let _ = act.hash(); // does not panic.
}
