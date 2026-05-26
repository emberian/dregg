//! Sovereign-witness tests — Phase 1 algebraic teeth + wire-malleability.
//!
//! Layer: AIR (Effect VM) + canonical signing message + verifier-side
//! replay. See `AUDIT-sovereign-witness-teeth.md`,
//! `SOVEREIGN-WITNESS-AIR-DESIGN.md`, and `EXECUTOR-HONESTY-AUDIT.md` T9.
//!
//! Three concerns:
//!
//!   1. Phase 1: legal witness accepted; tampered key / sequence-regression
//!      rejected.
//!   2. T9 (executor skips sovereign witness): AIR must algebraically
//!      constrain the witness; it can't just decorate the receipt.
//!   3. Wire-malleability: turn v3 signing message must cover sovereign
//!      witnesses so tamper-then-sign fails.
//!
//! All currently `#[ignore]`d on the sovereign-witness AIR teeth lane.

// ===========================================================================
// Phase 1: legal witness path
// ===========================================================================

#[test]
#[ignore = "blocked on SOVEREIGN-WITNESS-AIR-DESIGN.md Phase 1: AIR algebraically constrains sovereign witness (currently only decorates the receipt per AUDIT-sovereign-witness-teeth.md)"]
fn sovereign_witness_with_legal_key_accepts() {
    // Build a sovereign cell, sign a witness payload with its key, attach
    // to a turn, execute. Expect Committed + proof verifies.
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: tampered key (witness signed by a different key) must reject"]
fn sovereign_witness_with_tampered_key_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: witness sequence regression must reject"]
fn sovereign_witness_sequence_regression_rejects() {
    // Two turns with sovereign witnesses; the second turn's witness sequence
    // must be > the first's.
    panic!("blocked");
}

// ===========================================================================
// T9: executor cannot skip sovereign witness verification
// ===========================================================================

#[test]
#[ignore = "blocked on T9 (EXECUTOR-HONESTY-AUDIT.md T9): a turn against a sovereign cell with NO witness must reject"]
fn sovereign_cell_turn_without_witness_rejects() {
    // The whole point of sovereign cells is they can only mutate when the
    // owner signs a witness; a turn omitting the witness must reject.
    panic!("blocked");
}

#[test]
#[ignore = "blocked on T9: AIR-side constraint binds the sovereign witness to the cell transition (not just the receipt)"]
fn air_proof_constrains_sovereign_witness_to_transition() {
    // Build a turn with a valid witness payload but mismatched effect
    // (e.g., the witness authorized Transfer(10), the executor applies
    // Transfer(20)). The AIR's per-transition witness check must reject.
    panic!("blocked");
}

// ===========================================================================
// Wire-malleability (T9 tail)
// ===========================================================================

#[test]
#[ignore = "blocked on turn-canonical-signing-message audit: v3 signing message MUST cover sovereign_witnesses field (Turn::hash currently checks Turn::sovereign_witnesses, audit per EXECUTOR-HONESTY-AUDIT.md)"]
fn signing_message_covers_sovereign_witness_payload() {
    // 1. Sign a turn with witness W.
    // 2. Replace W with W' in the on-the-wire envelope (same shape, different
    //    payload bytes).
    // 3. Verifier MUST reject — the signature is over the hash that includes
    //    the witness bytes.
    panic!("blocked");
}

#[test]
#[ignore = "blocked on wire-malleability: tamper-then-sign workflow (attacker mutates witness AFTER signing, recomputes signature) — should still reject because re-signing requires the cell key"]
fn tamper_then_sign_witness_workflow_rejects() {
    panic!("blocked");
}

// ===========================================================================
// Cross-cutting: sovereign + bilateral + slot caveats
// ===========================================================================

#[test]
#[ignore = "blocked on sovereign witness AIR teeth + γ.2 + caveat-correctness: full composition"]
fn sovereign_witness_plus_bilateral_transfer_plus_slot_caveats() {
    // Composition mandate — see CAVEAT-LAYER-COVERAGE composition row.
    panic!("blocked");
}

// ===========================================================================
// Sanity: presence of sovereign_witnesses field on Turn does not by itself
// authorize a non-sovereign mutation.
// ===========================================================================

// ===========================================================================
// Extended adversarial scenarios (Phase 1 + AIR teeth)
// ===========================================================================

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth + verifier-replay: a sovereign witness signed for cell A presented on a turn that mutates cell B (cross-cell reuse) must reject"]
fn sovereign_witness_cross_cell_reuse_rejects() {
    // The cell_id is part of what the witness signs; presenting Alice's
    // signed witness on a turn that targets Bob's cell must fail because
    // the witness payload says "for cell A" but the executor is
    // applying it to cell B.
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: replaying the EXACT same witness payload (same sequence, same cell, same effect) twice must reject the second occurrence — sequence must strictly increase"]
fn sovereign_witness_exact_replay_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: witness signed under an OLD key after the cell rotated keys must reject (per-key rotation seq number bound into witness payload)"]
fn sovereign_witness_after_key_rotation_old_key_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: witness with VALID signature but stale sequence (==current, not >) must reject — sequence must strictly increase per Phase 1 design"]
fn sovereign_witness_equal_sequence_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: tampered witness payload (modify the effect bytes, leave signature valid for old payload) must reject — signature recomputation must require the cell key"]
fn sovereign_witness_payload_tamper_with_intact_signature_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: two sovereign cells in one turn, both witnessed — if EITHER witness is invalid, the whole turn must reject"]
fn turn_with_two_sovereign_cells_one_witness_invalid_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: a turn with sovereign_witnesses populated for a NON-sovereign cell — the extra witness must be ignored (not cause acceptance for a non-sovereign mutation that lacked normal authorization)"]
fn extra_witness_for_non_sovereign_cell_does_not_grant_authorization() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth: tx-time vs verify-time consistency — the witness's sequence number bound in the AIR PI must equal the sequence number in the witness payload AND in the on-chain cell state"]
fn sovereign_witness_sequence_pi_state_payload_must_agree() {
    panic!("blocked");
}

// ===========================================================================
// Composition: sovereign witness + slot caveats
// ===========================================================================

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth + caveat-correctness: sovereign cell with Monotonic slot caveat — the witness authorizes the effect, but the slot caveat must fire INDEPENDENTLY (sovereign mode bypasses normal Authorization but NOT slot caveats)"]
fn sovereign_cell_slot_caveats_still_fire() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth + caveat-correctness: sovereign cell with PreimageGate slot caveat — sovereign witness authorizes the action, but the preimage gate also requires a fresh-reveal witness, distinct from the sovereign witness"]
fn sovereign_with_preimage_gate_requires_both_witnesses() {
    panic!("blocked");
}

// ===========================================================================
// Sovereign + cross-federation
// ===========================================================================

#[test]
#[ignore = "blocked on sovereign-witness AIR teeth + cross-federation: sovereign witness signed for federation F1 presented in F2 must reject; the witness payload includes federation_id (per AUDIT-federation.md F1/F2 closure expectation)"]
fn sovereign_witness_cross_federation_replay_rejects() {
    panic!("blocked");
}

// ===========================================================================
// Sanity: Turn::hash covers the sovereign_witnesses field
// ===========================================================================

#[test]
fn sovereign_witnesses_field_is_covered_by_turn_hash() {
    use dregg_cell::Cell;
    use dregg_cell::CellId;
    use dregg_turn::SovereignCellWitness;
    use dregg_turn::Turn;
    use std::collections::HashMap;

    let agent = CellId([1u8; 32]);

    let make_turn = |witnesses: HashMap<CellId, SovereignCellWitness>| Turn {
        agent,
        nonce: 0,
        call_forest: dregg_turn::CallForest::new(),
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: witnesses,
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let empty = make_turn(HashMap::new());

    // Construct a non-empty witness — bytes only need to differ from the
    // default for the hash check (we're NOT validating the witness's
    // signature here, only that Turn::hash sees the witness map).
    let cell_pk = [0xCA; 32];
    let cell = Cell::with_balance(cell_pk, [0u8; 32], 0);
    let cell_id = cell.id();
    let mut witnesses = HashMap::new();
    let w = SovereignCellWitness {
        cell_id,
        old_commitment: [0xAA; 32],
        new_commitment: [0xBB; 32],
        effects_hash: [0xCC; 32],
        timestamp: 0,
        sequence: 1,
        signature: [0xAB; 64],
        cell_state: cell,
        transition_proof: None,
    };
    witnesses.insert(cell_id, w);
    let with_witness = make_turn(witnesses);

    assert_ne!(
        empty.hash(),
        with_witness.hash(),
        "Turn::hash MUST cover sovereign_witnesses — see EXECUTOR-HONESTY-AUDIT.md T9 wire-malleability"
    );

    // SovereignCellWitness::signing_message must be a publicly callable
    // function so verifier-side replay can recompute the signing
    // message and reject witnesses whose payload was tampered.
    let msg = SovereignCellWitness::signing_message(
        &cell_id,
        &[0xAA; 32],
        &[0xBB; 32],
        &[0xCC; 32],
        0,
        1,
    );
    assert!(
        msg.starts_with(b"dregg-sovereign-witness-v1:"),
        "signing message must begin with the v1 domain separator"
    );
}

#[test]
fn turn_sovereign_witnesses_field_is_a_map_and_constructs_empty() {
    use dregg_turn::Turn;
    use std::collections::HashMap;
    let agent = CellId([1u8; 32]);
    let turn = Turn {
        agent,
        nonce: 0,
        call_forest: dregg_turn::CallForest::new(),
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
    };
    assert!(turn.sovereign_witnesses.is_empty());
}
