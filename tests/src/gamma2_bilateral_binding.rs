//! γ.2 bilateral binding tests (STAGE-7-GAMMA-2-PI-DESIGN.md).
//!
//! Layer: cross-cell PI binding + off-AIR verifier algorithm.
//!
//! Phase 1 of γ.2 defines three canonical instance ids derived from public
//! surface data:
//!
//!   transfer_id = Poseidon2(b"dregg-transfer-id-v1" || from || to || amount_be || sender_nonce_be)
//!   grant_id    = Poseidon2(b"dregg-grant-id-v1"    || from || to || cap_entry_hash || sender_nonce_be)
//!   intro_id    = Poseidon2(b"dregg-intro-id-v1"    || introducer || recipient || target || permissions_bits || introducer_nonce_be)
//!
//! Each test in this file covers one of:
//!   - happy-path symmetric/asymmetric/trilateral binding;
//!   - sender-outgoing vs receiver-incoming disagreement → off-AIR reject;
//!   - tampered transfer_id (substitute a different id) → AIR reject;
//!   - permissions-bit tamper on `Introduce` → AIR reject;
//!   - federation-id binding across cross-federation `Introduce` (§1.3 tail).
//!
//! AIR-side γ.2 tests remain `#[ignore]`d until trace-to-PI binding lands.
//! Phase 1 off-AIR verifier tests below use fabricated WR public inputs to
//! demonstrate the verifier schedule checks without paying proving cost.

use dregg_cell::{AuthRequired, CapabilityRef, CellId};
use dregg_turn::{
    bilateral_schedule::{derive_intro_id, derive_intro_id_for_federation},
    ActionBuilder, Turn, TurnBuilder, TurnReceipt,
};
use dregg_verifier::{
    fabricate_witnessed_receipt, verify_bilateral_bundle, BilateralBundle, BilateralEntry,
};

// ---------------------------------------------------------------------------
// Canonical id derivations (testable today: pure-public-data functions)
// ---------------------------------------------------------------------------

/// Compute the canonical Phase-1 `transfer_id` preimage per
/// STAGE-7-GAMMA-2-PI-DESIGN.md §3.1.
fn transfer_id_preimage(from: &CellId, to: &CellId, amount: u64, sender_nonce: u64) -> Vec<u8> {
    let mut v = Vec::with_capacity(128);
    v.extend_from_slice(b"dregg-transfer-id-v1");
    v.extend_from_slice(&from.0);
    v.extend_from_slice(&to.0);
    v.extend_from_slice(&amount.to_be_bytes());
    v.extend_from_slice(&sender_nonce.to_be_bytes());
    v
}

fn grant_id_preimage(
    from: &CellId,
    to: &CellId,
    cap_entry_hash: &[u8; 32],
    sender_nonce: u64,
) -> Vec<u8> {
    let mut v = Vec::with_capacity(128);
    v.extend_from_slice(b"dregg-grant-id-v1");
    v.extend_from_slice(&from.0);
    v.extend_from_slice(&to.0);
    v.extend_from_slice(cap_entry_hash);
    v.extend_from_slice(&sender_nonce.to_be_bytes());
    v
}

fn intro_id_preimage(
    introducer: &CellId,
    recipient: &CellId,
    target: &CellId,
    permissions_bits: u32,
    introducer_nonce: u64,
) -> Vec<u8> {
    let mut v = Vec::with_capacity(128);
    v.extend_from_slice(b"dregg-intro-id-v1");
    v.extend_from_slice(&introducer.0);
    v.extend_from_slice(&recipient.0);
    v.extend_from_slice(&target.0);
    v.extend_from_slice(&permissions_bits.to_be_bytes());
    v.extend_from_slice(&introducer_nonce.to_be_bytes());
    v
}

fn dummy_receipt(agent: CellId) -> TurnReceipt {
    TurnReceipt {
        turn_hash: [0u8; 32],
        forest_hash: [0u8; 32],
        pre_state_hash: [0u8; 32],
        post_state_hash: [0u8; 32],
        timestamp: 0,
        effects_hash: [0u8; 32],
        computrons_used: 0,
        action_count: 0,
        previous_receipt_hash: None,
        agent,
        federation_id: [0u8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
    }
}

fn make_transfer_turn(alice: CellId, bob: CellId, amount: u64, nonce: u64) -> Turn {
    let mut builder = TurnBuilder::new(alice, nonce);
    let action = ActionBuilder::new_unchecked_for_tests(alice, "transfer", alice)
        .effect_transfer(alice, bob, amount)
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

fn make_transfer_ring_turn(a: CellId, b: CellId, c: CellId, nonce: u64) -> Turn {
    let mut builder = TurnBuilder::new(a, nonce);
    let action = ActionBuilder::new_unchecked_for_tests(a, "ring", a)
        .effect_transfer(a, b, 10)
        .effect_transfer(b, c, 20)
        .effect_transfer(c, a, 30)
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

fn make_transfer_five_ring_turn(cells: [CellId; 5], nonce: u64) -> Turn {
    let mut builder = TurnBuilder::new(cells[0], nonce);
    let action = ActionBuilder::new_unchecked_for_tests(cells[0], "five_ring", cells[0])
        .effect_transfer(cells[0], cells[1], 10)
        .effect_transfer(cells[1], cells[2], 20)
        .effect_transfer(cells[2], cells[3], 30)
        .effect_transfer(cells[3], cells[4], 40)
        .effect_transfer(cells[4], cells[0], 50)
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

fn make_grant_turn(alice: CellId, bob: CellId, target: CellId, nonce: u64) -> Turn {
    let mut builder = TurnBuilder::new(alice, nonce);
    let action = ActionBuilder::new_unchecked_for_tests(alice, "grant", alice)
        .effect_grant_capability(
            alice,
            bob,
            CapabilityRef {
                target,
                slot: 0,
                permissions: AuthRequired::Signature,
                expires_at: None,
                breadstuff: None,
                allowed_effects: None,
            },
        )
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

fn make_intro_turn(
    introducer: CellId,
    recipient: CellId,
    target: CellId,
    permissions: AuthRequired,
    nonce: u64,
) -> Turn {
    let mut builder = TurnBuilder::new(introducer, nonce);
    let action = ActionBuilder::new_unchecked_for_tests(introducer, "introduce", introducer)
        .effect_introduce(introducer, recipient, target, permissions)
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

fn fabricated_bundle(turn: &Turn, cells: &[CellId]) -> BilateralBundle {
    BilateralBundle {
        turn: turn.clone(),
        entries: cells
            .iter()
            .map(|cell_id| BilateralEntry {
                cell_id: *cell_id,
                witnessed_receipt: fabricate_witnessed_receipt(
                    turn,
                    cell_id,
                    dummy_receipt(turn.agent),
                ),
            })
            .collect(),
        unilateral_attestations: std::collections::BTreeMap::new(),
    }
}

// ===========================================================================
// Preimage shape + injectivity (testable today; design-level)
// ===========================================================================

#[test]
fn transfer_id_preimage_includes_domain_separator() {
    let pre = transfer_id_preimage(&CellId([1u8; 32]), &CellId([2u8; 32]), 10, 0);
    assert!(pre.starts_with(b"dregg-transfer-id-v1"));
}

#[test]
fn transfer_id_preimage_changes_with_direction() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let p_ab = transfer_id_preimage(&a, &b, 10, 0);
    let p_ba = transfer_id_preimage(&b, &a, 10, 0);
    assert_ne!(p_ab, p_ba, "direction must be in the preimage");
}

#[test]
fn transfer_id_preimage_changes_with_amount() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    assert_ne!(
        transfer_id_preimage(&a, &b, 10, 0),
        transfer_id_preimage(&a, &b, 11, 0)
    );
}

#[test]
fn transfer_id_preimage_changes_with_sender_nonce() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    assert_ne!(
        transfer_id_preimage(&a, &b, 10, 7),
        transfer_id_preimage(&a, &b, 10, 8),
        "same transfer at two nonces must yield different transfer_id (§3.4)"
    );
}

#[test]
fn grant_id_preimage_changes_with_cap_entry() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    assert_ne!(
        grant_id_preimage(&a, &b, &[1u8; 32], 0),
        grant_id_preimage(&a, &b, &[2u8; 32], 0)
    );
}

#[test]
fn intro_id_preimage_distinguishes_roles() {
    // introducer / recipient / target distinctness — swapping any two
    // must change the preimage.
    let i = CellId([1u8; 32]);
    let r = CellId([2u8; 32]);
    let t = CellId([3u8; 32]);
    let base = intro_id_preimage(&i, &r, &t, 0, 0);
    let swap_ir = intro_id_preimage(&r, &i, &t, 0, 0);
    let swap_rt = intro_id_preimage(&i, &t, &r, 0, 0);
    assert_ne!(base, swap_ir);
    assert_ne!(base, swap_rt);
}

#[test]
fn intro_id_preimage_changes_with_permissions_bits() {
    let i = CellId([1u8; 32]);
    let r = CellId([2u8; 32]);
    let t = CellId([3u8; 32]);
    assert_ne!(
        intro_id_preimage(&i, &r, &t, 0, 0),
        intro_id_preimage(&i, &r, &t, 1, 0),
        "permissions_bits tampering must change preimage (and thus intro_id)"
    );
}

// ===========================================================================
// End-to-end binding: needs γ.2 Phase 1 wiring
// ===========================================================================

#[test]
fn bilateral_transfer_happy_path_two_cells_verify_matched_transfer_id() {
    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let turn = make_transfer_turn(alice, bob, 10, 7);
    let bundle = fabricated_bundle(&turn, &[alice, bob]);

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(verdict.verified, "honest transfer bundle: {verdict:?}");
    assert_eq!(verdict.transfer_count, 1);
    assert_eq!(verdict.entry_count, 2);
}

#[test]
fn sender_outflow_vs_receiver_inflow_mismatch_rejects() {
    use dregg_circuit::effect_vm::pi;

    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let turn = make_transfer_turn(alice, bob, 10, 7);
    let mut bundle = fabricated_bundle(&turn, &[alice, bob]);
    bundle.entries[1].witnessed_receipt.public_inputs[pi::INCOMING_TRANSFER_ROOT_BASE] ^= 1;

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(!verdict.verified, "receiver mismatch must reject");
    assert!(
        verdict.reason.contains("incoming_transfer") || verdict.reason.contains("root"),
        "expected transfer root mismatch, got: {}",
        verdict.reason
    );
}

#[test]
#[ignore = "blocked on γ.2 Phase 1 AIR-side binding: tamper transfer_id between trace and PI; AIR rejects"]
fn tampered_transfer_id_in_pi_rejected_by_air() {
    // Build a proof where the prover claims transfer_id = X but the in-trace
    // transfer effect derives id = Y; AIR's "in-trace transfer-effect data
    // ties to PI transfer_id" constraint fires.
    panic!("blocked");
}

#[test]
fn bilateral_grant_happy_path_two_cells() {
    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let target = CellId([0xC3; 32]);
    let turn = make_grant_turn(alice, bob, target, 7);
    let bundle = fabricated_bundle(&turn, &[alice, bob]);

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(verdict.verified, "honest grant bundle: {verdict:?}");
    assert_eq!(verdict.grant_count, 1);
}

#[test]
fn bilateral_grant_tampered_cap_entry_rejects() {
    use dregg_circuit::effect_vm::pi;

    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let target = CellId([0xC3; 32]);
    let turn = make_grant_turn(alice, bob, target, 7);
    let mut bundle = fabricated_bundle(&turn, &[alice, bob]);
    bundle.entries[1].witnessed_receipt.public_inputs[pi::INCOMING_GRANT_ROOT_BASE] ^= 1;

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(!verdict.verified, "grant-root tamper must reject");
}

#[test]
fn trilateral_introduce_happy_path_three_cells() {
    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let carol = CellId([0xC3; 32]);
    let turn = make_intro_turn(alice, bob, carol, AuthRequired::Signature, 7);
    let bundle = fabricated_bundle(&turn, &[alice, bob, carol]);

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(verdict.verified, "honest introduce bundle: {verdict:?}");
    assert_eq!(verdict.introduce_count, 1);
    assert_eq!(verdict.entry_count, 3);
}

#[test]
fn trilateral_introduce_permissions_bit_tamper_rejects() {
    use dregg_circuit::effect_vm::pi;

    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let carol = CellId([0xC3; 32]);
    let turn = make_intro_turn(alice, bob, carol, AuthRequired::Signature, 7);
    let mut bundle = fabricated_bundle(&turn, &[alice, bob, carol]);
    bundle.entries[1].witnessed_receipt.public_inputs[pi::INTRO_AS_RECIPIENT_ROOT_BASE] ^= 1;

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(!verdict.verified, "permissions/root tamper must reject");
}

#[test]
fn cross_federation_introduce_includes_federation_id_in_intro_id_preimage() {
    let introducer = CellId([0xA1; 32]);
    let recipient = CellId([0xB2; 32]);
    let target = CellId([0xC3; 32]);
    let fed_a = [0xFA; 32];
    let fed_b = [0xFB; 32];

    let legacy = derive_intro_id(
        &introducer,
        &recipient,
        &target,
        &AuthRequired::Signature,
        7,
    );
    let zero_fed = derive_intro_id_for_federation(
        &[0u8; 32],
        &introducer,
        &recipient,
        &target,
        &AuthRequired::Signature,
        7,
    );
    assert_eq!(
        legacy, zero_fed,
        "zero federation id must preserve existing local intro_id derivation"
    );

    let id_a = derive_intro_id_for_federation(
        &fed_a,
        &introducer,
        &recipient,
        &target,
        &AuthRequired::Signature,
        7,
    );
    let id_b = derive_intro_id_for_federation(
        &fed_b,
        &introducer,
        &recipient,
        &target,
        &AuthRequired::Signature,
        7,
    );
    assert_ne!(
        id_a, id_b,
        "same Introduce surface data under two federations must derive distinct intro_id values"
    );
}

// ===========================================================================
// Three-cell bilateral compositions (ring trade)
// ===========================================================================

#[test]
fn three_cell_ring_transfer_all_pairings_bound() {
    let a = CellId([0xA1; 32]);
    let b = CellId([0xB2; 32]);
    let c = CellId([0xC3; 32]);
    let turn = make_transfer_ring_turn(a, b, c, 7);
    let bundle = fabricated_bundle(&turn, &[a, b, c]);

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(verdict.verified, "honest ring bundle: {verdict:?}");
    assert_eq!(verdict.transfer_count, 3);
    assert_eq!(verdict.entry_count, 3);
}

#[test]
fn three_cell_ring_with_tampered_pair_rejects() {
    use dregg_circuit::effect_vm::pi;

    let a = CellId([0xA1; 32]);
    let b = CellId([0xB2; 32]);
    let c = CellId([0xC3; 32]);
    let turn = make_transfer_ring_turn(a, b, c, 7);
    let mut bundle = fabricated_bundle(&turn, &[a, b, c]);
    bundle.entries[2].witnessed_receipt.public_inputs[pi::INCOMING_TRANSFER_ROOT_BASE] ^= 1;

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(!verdict.verified, "tampered ring pair must reject");
}

// ===========================================================================
// Compositions with slot caveats / sovereign witness
// ===========================================================================

#[test]
#[ignore = "blocked on γ.2 + slot caveats on both cells (composition target from CAVEAT-LAYER-COVERAGE.md row 24)"]
fn bilateral_transfer_with_bound_delta_caveat_on_both_sides() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on γ.2 + sovereign witness AIR teeth: bilateral transfer between two sovereign cells must bind transfer_id AND verify sovereign witnesses"]
fn bilateral_transfer_with_sovereign_witness_on_both_sides() {
    panic!("blocked");
}

// ===========================================================================
// Preimage byte-level injectivity (additional adversarial scenarios)
// ===========================================================================

#[test]
fn transfer_id_preimage_disambiguates_self_transfer_from_zero_amount() {
    // The canonical preimage must distinguish "A→A, amount=0" from a
    // trivially-empty transfer that some malicious projection might
    // pretend was equivalent.
    let a = CellId([1u8; 32]);
    let p_self_zero = transfer_id_preimage(&a, &a, 0, 0);
    let p_self_one = transfer_id_preimage(&a, &a, 1, 0);
    assert_ne!(
        p_self_zero, p_self_one,
        "self-transfer amounts must be distinguished by preimage"
    );
}

#[test]
fn grant_id_preimage_distinguishes_zero_cap_entry_from_default() {
    // grant_id = ...|| cap_entry_hash || ... The [0u8; 32] cap_entry is
    // a "default" that some careless projection might use; it must be
    // distinguishable from any non-default hash.
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let zero_cap = [0u8; 32];
    let other_cap = [1u8; 32];
    assert_ne!(
        grant_id_preimage(&a, &b, &zero_cap, 0),
        grant_id_preimage(&a, &b, &other_cap, 0)
    );
}

#[test]
fn intro_id_preimage_distinguishes_self_introduce_combinations() {
    // i=r=t (degenerate self-introduce) must still have a distinct
    // preimage from i=r, t different; the role distinction is on cell
    // bytes, not on the *relation* between introducer/recipient/target.
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let p_all_self = intro_id_preimage(&a, &a, &a, 0, 0);
    let p_partial = intro_id_preimage(&a, &a, &b, 0, 0);
    assert_ne!(p_all_self, p_partial);
}

#[test]
fn transfer_id_preimage_endian_stability() {
    // amount and sender_nonce are big-endian in the preimage per §3.1.
    // Verify directly that endianness is what the design says, so that
    // verifier implementations on other languages can match byte-for-
    // byte.
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let pre = transfer_id_preimage(&a, &b, 0x0102030405060708u64, 0x0A0B0C0D0E0F1011u64);
    // Domain separator (20 bytes) + 2*32 (cells) = 84 — amount starts here.
    assert_eq!(pre.len(), 20 + 32 + 32 + 8 + 8);
    assert_eq!(
        &pre[84..92],
        &[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]
    );
    assert_eq!(
        &pre[92..100],
        &[0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11]
    );
}

// ===========================================================================
// γ.2 + sovereign witness composition (additional)
// ===========================================================================

#[test]
#[ignore = "blocked on γ.2 Phase 1 + sovereign witness AIR teeth + cross-fed extension: trilateral introduce across three federations where each cell is sovereign and each emits its own sovereign witness"]
fn trilateral_introduce_three_federations_each_sovereign() {
    panic!("blocked");
}

#[test]
fn five_cell_ring_all_pairs_bound() {
    use dregg_circuit::effect_vm::pi;

    let cells = [
        CellId([0xA1; 32]),
        CellId([0xB2; 32]),
        CellId([0xC3; 32]),
        CellId([0xD4; 32]),
        CellId([0xE5; 32]),
    ];
    let turn = make_transfer_five_ring_turn(cells, 7);
    let bundle = fabricated_bundle(&turn, &cells);

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(verdict.verified, "honest five-cell ring: {verdict:?}");
    assert_eq!(verdict.transfer_count, 5);
    assert_eq!(verdict.entry_count, 5);

    let mut tampered = fabricated_bundle(&turn, &cells);
    tampered.entries[3].witnessed_receipt.public_inputs[pi::INCOMING_TRANSFER_ROOT_BASE] ^= 1;

    let verdict = verify_bilateral_bundle(&tampered);
    assert!(
        !verdict.verified,
        "tampered five-cell ring pair must reject"
    );
}

#[test]
fn bilateral_bound_delta_disagreement_on_nonce_rejects() {
    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let real_turn = make_transfer_turn(alice, bob, 10, 7);
    let nonce_lie_turn = make_transfer_turn(alice, bob, 10, 8);

    let bundle = BilateralBundle {
        turn: real_turn.clone(),
        entries: vec![
            BilateralEntry {
                cell_id: alice,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &real_turn,
                    &alice,
                    dummy_receipt(alice),
                ),
            },
            BilateralEntry {
                cell_id: bob,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &nonce_lie_turn,
                    &bob,
                    dummy_receipt(alice),
                ),
            },
        ],
        unilateral_attestations: std::collections::BTreeMap::new(),
    };

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(
        !verdict.verified,
        "nonce-derived transfer_id mismatch must reject"
    );
}

#[test]
#[ignore = "blocked on γ.2 Phase 1: Transfer effect against a cell that has BOTH a BoundDelta caveat AND a Monotonic caveat on the same slot — the per-cell slot caveat must fire AFTER the γ.2 binding succeeds"]
fn bilateral_with_layered_slot_caveats_evaluation_order() {
    panic!("blocked");
}

// ===========================================================================
// γ.2 adversarial: forged direction bit on one side
// ===========================================================================

#[test]
fn direction_bit_both_outflow_rejects() {
    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let real_turn = make_transfer_turn(alice, bob, 10, 7);
    let reversed_turn = make_transfer_turn(bob, alice, 10, 7);

    let bundle = BilateralBundle {
        turn: real_turn.clone(),
        entries: vec![
            BilateralEntry {
                cell_id: alice,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &real_turn,
                    &alice,
                    dummy_receipt(alice),
                ),
            },
            BilateralEntry {
                cell_id: bob,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &reversed_turn,
                    &bob,
                    dummy_receipt(alice),
                ),
            },
        ],
        unilateral_attestations: std::collections::BTreeMap::new(),
    };

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(!verdict.verified, "receiver claiming outflow must reject");
}

#[test]
fn direction_bit_inverted_on_sender_rejects() {
    let alice = CellId([0xA1; 32]);
    let bob = CellId([0xB2; 32]);
    let real_turn = make_transfer_turn(alice, bob, 10, 7);
    let reversed_turn = make_transfer_turn(bob, alice, 10, 7);

    let bundle = BilateralBundle {
        turn: real_turn.clone(),
        entries: vec![
            BilateralEntry {
                cell_id: alice,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &reversed_turn,
                    &alice,
                    dummy_receipt(alice),
                ),
            },
            BilateralEntry {
                cell_id: bob,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &real_turn,
                    &bob,
                    dummy_receipt(alice),
                ),
            },
        ],
        unilateral_attestations: std::collections::BTreeMap::new(),
    };

    let verdict = verify_bilateral_bundle(&bundle);
    assert!(!verdict.verified, "sender claiming inflow must reject");
}

// ===========================================================================
// γ.2 + bridge composition
// ===========================================================================

#[test]
#[ignore = "blocked on γ.2 + bridge phase log: cross-federation Transfer where the sender's federation FED_A emits a Phase-1 lock with bridge_id, the receiver's FED_B emits a Phase-2 witness; the γ.2 transfer_id binding must compose with the bridge_id binding"]
fn cross_federation_transfer_binds_both_transfer_id_and_bridge_id() {
    panic!("blocked");
}
