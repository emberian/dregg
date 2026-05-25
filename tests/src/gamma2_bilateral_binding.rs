//! γ.2 bilateral binding tests (STAGE-7-GAMMA-2-PI-DESIGN.md).
//!
//! Layer: cross-cell PI binding + off-AIR verifier algorithm.
//!
//! Phase 1 of γ.2 defines three canonical instance ids derived from public
//! surface data:
//!
//!   transfer_id = Poseidon2(b"pyana-transfer-id-v1" || from || to || amount_be || sender_nonce_be)
//!   grant_id    = Poseidon2(b"pyana-grant-id-v1"    || from || to || cap_entry_hash || sender_nonce_be)
//!   intro_id    = Poseidon2(b"pyana-intro-id-v1"    || introducer || recipient || target || permissions_bits || introducer_nonce_be)
//!
//! Each test in this file covers one of:
//!   - happy-path symmetric/asymmetric/trilateral binding;
//!   - sender-outgoing vs receiver-incoming disagreement → off-AIR reject;
//!   - tampered transfer_id (substitute a different id) → AIR reject;
//!   - permissions-bit tamper on `Introduce` → AIR reject;
//!   - federation-id binding across cross-federation `Introduce` (§1.3 tail).
//!
//! Most are `#[ignore]`d on γ.2 wiring — the PI fields exist on the design
//! doc but Phase 1 lands the off-AIR verifier independently from any
//! Phase 2 joint-aggregation AIR.

use pyana_cell::CellId;

// ---------------------------------------------------------------------------
// Canonical id derivations (testable today: pure-public-data functions)
// ---------------------------------------------------------------------------

/// Compute the canonical Phase-1 `transfer_id` preimage per
/// STAGE-7-GAMMA-2-PI-DESIGN.md §3.1.
fn transfer_id_preimage(from: &CellId, to: &CellId, amount: u64, sender_nonce: u64) -> Vec<u8> {
    let mut v = Vec::with_capacity(128);
    v.extend_from_slice(b"pyana-transfer-id-v1");
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
    v.extend_from_slice(b"pyana-grant-id-v1");
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
    v.extend_from_slice(b"pyana-intro-id-v1");
    v.extend_from_slice(&introducer.0);
    v.extend_from_slice(&recipient.0);
    v.extend_from_slice(&target.0);
    v.extend_from_slice(&permissions_bits.to_be_bytes());
    v.extend_from_slice(&introducer_nonce.to_be_bytes());
    v
}

// ===========================================================================
// Preimage shape + injectivity (testable today; design-level)
// ===========================================================================

#[test]
fn transfer_id_preimage_includes_domain_separator() {
    let pre = transfer_id_preimage(&CellId([1u8; 32]), &CellId([2u8; 32]), 10, 0);
    assert!(pre.starts_with(b"pyana-transfer-id-v1"));
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
#[ignore = "blocked on γ.2 Phase 1 PI extension: per-cell proof exposes transfer_id at canonical PI offset, off-AIR verifier joins sender + receiver"]
fn bilateral_transfer_happy_path_two_cells_verify_matched_transfer_id() {
    // 1. Build A=sender + B=receiver cells.
    // 2. Submit Transfer(A→B, 10) turn at A's nonce=7.
    // 3. Produce per-cell proofs for A and B (executor's per-cell projection).
    // 4. Run the off-AIR γ.2 verifier; it must:
    //      - compute transfer_id = Poseidon2(transfer_id_preimage(A, B, 10, 7))
    //      - assert PI[TRANSFER_ID_BASE..+4] on A's proof equals it
    //      - assert PI[TRANSFER_ID_BASE..+4] on B's proof equals it
    //      - assert A's direction-bit = 1 (outflow), B's = 0 (inflow).
    panic!("blocked");
}

#[test]
#[ignore = "blocked on γ.2 Phase 1: sender outgoing disagrees with receiver incoming → off-AIR verifier rejects"]
fn sender_outflow_vs_receiver_inflow_mismatch_rejects() {
    // E.g., A's projection says amount=10, B's says amount=11 → off-AIR
    // verifier sees mismatched transfer_id and rejects.
    panic!("blocked");
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
#[ignore = "blocked on γ.2 Phase 1: GrantCapability bilateral binding"]
fn bilateral_grant_happy_path_two_cells() {
    // grantor + grantee proofs must both expose grant_id; off-AIR verifier
    // joins.
    panic!("blocked");
}

#[test]
#[ignore = "blocked on γ.2 Phase 1: GrantCapability tampered cap_entry"]
fn bilateral_grant_tampered_cap_entry_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on γ.2 Phase 1: Introduce trilateral binding"]
fn trilateral_introduce_happy_path_three_cells() {
    // introducer + recipient + target all expose intro_id; off-AIR verifier
    // joins the three proofs on intro_id agreement.
    panic!("blocked");
}

#[test]
#[ignore = "blocked on γ.2 Phase 1: Introduce permissions_bits tamper"]
fn trilateral_introduce_permissions_bit_tamper_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on γ.2 Phase 1 cross-federation extension (§1.3): federation_id appended to Introduce preimage"]
fn cross_federation_introduce_includes_federation_id_in_intro_id_preimage() {
    panic!("blocked");
}

// ===========================================================================
// Three-cell bilateral compositions (ring trade)
// ===========================================================================

#[test]
#[ignore = "blocked on γ.2 Phase 2 (joint aggregation AIR sketch) — three-cell ring of bilateral effects"]
fn three_cell_ring_transfer_all_pairings_bound() {
    // A→B, B→C, C→A; three transfer_ids must each match across their two
    // touched cells; off-AIR verifier walks each pair.
    panic!("blocked");
}

#[test]
#[ignore = "blocked on γ.2 Phase 2: ring with one tampered transfer_id (between any two cells) rejects"]
fn three_cell_ring_with_tampered_pair_rejects() {
    panic!("blocked");
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
#[ignore = "blocked on γ.2 Phase 2 AIR aggregation: ring of 5 cells, each Transfer pair must agree on its transfer_id; one tampered pair must reject the whole ring"]
fn five_cell_ring_all_pairs_bound() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on γ.2 Phase 1: BoundDelta with DeltaRelation::EqualAndOpposite on bilateral pair must agree on amount AND on sender_nonce derivation order"]
fn bilateral_bound_delta_disagreement_on_nonce_rejects() {
    // Subtle attack: A's projection uses sender_nonce=7, B's uses
    // sender_nonce=8 (each side claims a different nonce in its trace).
    // The γ.2 verifier must detect the disagreement because transfer_id
    // depends on sender_nonce.
    panic!("blocked");
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
#[ignore = "blocked on γ.2 Phase 1: per-cell direction_bit (1=outflow, 0=inflow) bound in PI; A claims outflow, B's projection ALSO claims outflow (i.e. B's projection says it sent to A) — off-AIR verifier must detect the direction mismatch"]
fn direction_bit_both_outflow_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on γ.2 Phase 1: direction bit tamper — A says inflow when it was actually outflow; transfer_id matches B's but direction reversed"]
fn direction_bit_inverted_on_sender_rejects() {
    panic!("blocked");
}

// ===========================================================================
// γ.2 + bridge composition
// ===========================================================================

#[test]
#[ignore = "blocked on γ.2 + bridge phase log: cross-federation Transfer where the sender's federation FED_A emits a Phase-1 lock with bridge_id, the receiver's FED_B emits a Phase-2 witness; the γ.2 transfer_id binding must compose with the bridge_id binding"]
fn cross_federation_transfer_binds_both_transfer_id_and_bridge_id() {
    panic!("blocked");
}
