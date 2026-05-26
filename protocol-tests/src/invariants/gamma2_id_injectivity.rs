//! Protocol invariant: γ.2 canonical id preimages are injective in their
//! public components.
//!
//! Per STAGE-7-GAMMA-2-PI-DESIGN.md §3 the three canonical preimages are:
//!
//!   transfer_id = Poseidon2(b"dregg-transfer-id-v1" || from || to || amount_be || sender_nonce_be)
//!   grant_id    = Poseidon2(b"dregg-grant-id-v1"    || from || to || cap_entry_hash || sender_nonce_be)
//!   intro_id    = Poseidon2(b"dregg-intro-id-v1"    || introducer || recipient || target || permissions_bits || introducer_nonce_be)
//!
//! Invariant: changing **any** preimage component changes the preimage
//! bytes. (This is a necessary condition for the id-hash to differ; the
//! injectivity of Poseidon2 itself is a separate cryptographic
//! assumption.)

use crate::Invariant;
use dregg_cell::id::CellId;
use proptest::prelude::*;

pub struct Gamma2IdInjectivity;
impl Invariant for Gamma2IdInjectivity {
    const NAME: &'static str = "gamma2_id_injectivity";
    const DESCRIPTION: &'static str = "γ.2 transfer_id / grant_id / intro_id preimage byte vectors are injective in their public components";
}

fn transfer_pre(from: &CellId, to: &CellId, amount: u64, sender_nonce: u64) -> Vec<u8> {
    let mut v = Vec::with_capacity(128);
    v.extend_from_slice(b"dregg-transfer-id-v1");
    v.extend_from_slice(&from.0);
    v.extend_from_slice(&to.0);
    v.extend_from_slice(&amount.to_be_bytes());
    v.extend_from_slice(&sender_nonce.to_be_bytes());
    v
}

fn grant_pre(from: &CellId, to: &CellId, cap: &[u8; 32], sender_nonce: u64) -> Vec<u8> {
    let mut v = Vec::with_capacity(128);
    v.extend_from_slice(b"dregg-grant-id-v1");
    v.extend_from_slice(&from.0);
    v.extend_from_slice(&to.0);
    v.extend_from_slice(cap);
    v.extend_from_slice(&sender_nonce.to_be_bytes());
    v
}

fn intro_pre(
    introducer: &CellId,
    recipient: &CellId,
    target: &CellId,
    perms: u32,
    nonce: u64,
) -> Vec<u8> {
    let mut v = Vec::with_capacity(160);
    v.extend_from_slice(b"dregg-intro-id-v1");
    v.extend_from_slice(&introducer.0);
    v.extend_from_slice(&recipient.0);
    v.extend_from_slice(&target.0);
    v.extend_from_slice(&perms.to_be_bytes());
    v.extend_from_slice(&nonce.to_be_bytes());
    v
}

fn arb_cell_id() -> impl Strategy<Value = CellId> {
    any::<[u8; 32]>().prop_map(CellId)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    #[test]
    fn transfer_pre_changes_with_any_field(
        from in arb_cell_id(),
        to in arb_cell_id(),
        amount in any::<u64>(),
        nonce in any::<u64>(),
        delta_amount in 1u64..u64::MAX / 2,
    ) {
        let base = transfer_pre(&from, &to, amount, nonce);
        prop_assert_ne!(
            base.clone(),
            transfer_pre(&to, &from, amount, nonce),
            "direction must change preimage"
        );
        prop_assert_ne!(
            base.clone(),
            transfer_pre(&from, &to, amount.wrapping_add(delta_amount), nonce),
            "amount must change preimage"
        );
        prop_assert_ne!(
            base,
            transfer_pre(&from, &to, amount, nonce.wrapping_add(1)),
            "sender_nonce must change preimage"
        );
    }

    #[test]
    fn grant_pre_changes_with_cap_entry(
        from in arb_cell_id(),
        to in arb_cell_id(),
        cap_a in any::<[u8; 32]>(),
        cap_b in any::<[u8; 32]>(),
        nonce in any::<u64>(),
    ) {
        prop_assume!(cap_a != cap_b);
        prop_assert_ne!(
            grant_pre(&from, &to, &cap_a, nonce),
            grant_pre(&from, &to, &cap_b, nonce)
        );
    }

    #[test]
    fn intro_pre_changes_with_permissions(
        introducer in arb_cell_id(),
        recipient in arb_cell_id(),
        target in arb_cell_id(),
        nonce in any::<u64>(),
        p_a in any::<u32>(),
        p_delta in 1u32..u32::MAX / 2,
    ) {
        prop_assert_ne!(
            intro_pre(&introducer, &recipient, &target, p_a, nonce),
            intro_pre(
                &introducer,
                &recipient,
                &target,
                p_a.wrapping_add(p_delta),
                nonce
            )
        );
    }

    #[test]
    fn intro_pre_distinguishes_roles(
        a in arb_cell_id(),
        b in arb_cell_id(),
        c in arb_cell_id(),
        p in any::<u32>(),
        nonce in any::<u64>(),
    ) {
        prop_assume!(a != b);
        prop_assert_ne!(
            intro_pre(&a, &b, &c, p, nonce),
            intro_pre(&b, &a, &c, p, nonce),
            "swapping introducer ↔ recipient must change preimage"
        );
    }
}
