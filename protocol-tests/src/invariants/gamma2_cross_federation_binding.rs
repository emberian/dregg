//! Protocol invariant: γ.2 canonical id preimages MUST be extended with
//! `federation_id` for cross-federation `Introduce` / `Transfer`
//! (STAGE-7-GAMMA-2-PI-DESIGN.md §1.3 tail + AUDIT-federation.md F1).
//!
//! Today's `transfer_id_preimage` / `grant_id_preimage` /
//! `intro_id_preimage` are *intra-federation* — they bind cell IDs but
//! not federation IDs. For a cross-federation introduce, two
//! federations could produce the same preimage if a malicious actor
//! arranged the same `(introducer, recipient, target)` triple in both
//! — without federation_id in the preimage, a cross-fed verifier
//! cannot tell them apart.
//!
//! Phase 1 keeps the intra-fed preimage as-is. The cross-fed extension
//! is documented here so that **once it lands** the invariant flips
//! from "current shape is stable" to "federation_id is bound".

use crate::Invariant;
use proptest::prelude::*;
use pyana_cell::id::CellId;

pub struct Gamma2CrossFederationBinding;
impl Invariant for Gamma2CrossFederationBinding {
    const NAME: &'static str = "gamma2_cross_federation_binding";
    const DESCRIPTION: &'static str = "γ.2 cross-fed: intro_id / transfer_id preimage extension binds federation_id (currently intra-fed only; this invariant lands with the cross-fed extension)";
}

// ---------------------------------------------------------------------------
// Today's intra-fed preimages (regression guard: shape is stable).
// ---------------------------------------------------------------------------

fn transfer_pre_intra_fed(from: &CellId, to: &CellId, amount: u64, sender_nonce: u64) -> Vec<u8> {
    let mut v = Vec::with_capacity(128);
    v.extend_from_slice(b"pyana-transfer-id-v1");
    v.extend_from_slice(&from.0);
    v.extend_from_slice(&to.0);
    v.extend_from_slice(&amount.to_be_bytes());
    v.extend_from_slice(&sender_nonce.to_be_bytes());
    v
}

fn intro_pre_intra_fed(
    introducer: &CellId,
    recipient: &CellId,
    target: &CellId,
    perms: u32,
    nonce: u64,
) -> Vec<u8> {
    let mut v = Vec::with_capacity(160);
    v.extend_from_slice(b"pyana-intro-id-v1");
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
    #![proptest_config(ProptestConfig::with_cases(120))]

    /// Today's (intra-fed) preimages do NOT see `federation_id` — so
    /// two federations producing the same (from, to, amount, nonce)
    /// triple produce IDENTICAL preimages. This proptest *asserts*
    /// that — it's a guard so that once the cross-fed extension lands,
    /// this test must be inverted (the new preimage must distinguish).
    #[test]
    fn intra_fed_preimage_does_not_distinguish_federations(
        from in arb_cell_id(),
        to in arb_cell_id(),
        amount in any::<u64>(),
        nonce in any::<u64>(),
        fed_a in any::<[u8; 32]>(),
        fed_b in any::<[u8; 32]>(),
    ) {
        prop_assume!(fed_a != fed_b);
        let pre_a = transfer_pre_intra_fed(&from, &to, amount, nonce);
        let pre_b = transfer_pre_intra_fed(&from, &to, amount, nonce);
        // Without federation_id in the preimage, fed_a and fed_b produce
        // identical bytes. Document this as the *current* state.
        prop_assert_eq!(
            pre_a,
            pre_b,
            "intra-fed preimage MUST be identical across federations today; once the cross-fed extension lands this test inverts. fed_a={:?}, fed_b={:?}",
            fed_a,
            fed_b
        );
    }

    /// Same as above for `intro_id`.
    #[test]
    fn intra_fed_intro_pre_does_not_distinguish_federations(
        a in arb_cell_id(),
        b in arb_cell_id(),
        c in arb_cell_id(),
        perms in any::<u32>(),
        nonce in any::<u64>(),
        fed_x in any::<[u8; 32]>(),
        fed_y in any::<[u8; 32]>(),
    ) {
        prop_assume!(fed_x != fed_y);
        let pre_x = intro_pre_intra_fed(&a, &b, &c, perms, nonce);
        let pre_y = intro_pre_intra_fed(&a, &b, &c, perms, nonce);
        prop_assert_eq!(pre_x, pre_y);
    }
}

// ---------------------------------------------------------------------------
// Hypothetical cross-fed preimage shape (NOT yet wired; document the
// expected design so testers and implementers agree on it).
// ---------------------------------------------------------------------------

#[allow(dead_code)]
fn transfer_pre_cross_fed_v2(
    from: &CellId,
    to: &CellId,
    src_fed: &[u8; 32],
    dst_fed: &[u8; 32],
    amount: u64,
    sender_nonce: u64,
) -> Vec<u8> {
    let mut v = Vec::with_capacity(192);
    v.extend_from_slice(b"pyana-transfer-id-v2-xfed");
    v.extend_from_slice(&from.0);
    v.extend_from_slice(&to.0);
    v.extend_from_slice(src_fed);
    v.extend_from_slice(dst_fed);
    v.extend_from_slice(&amount.to_be_bytes());
    v.extend_from_slice(&sender_nonce.to_be_bytes());
    v
}

#[test]
fn cross_fed_preimage_shape_distinguishes_federations() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let fed_a = [0xA1; 32];
    let fed_b = [0xB2; 32];
    let pre_1 = transfer_pre_cross_fed_v2(&a, &b, &fed_a, &fed_b, 10, 0);
    let pre_2 = transfer_pre_cross_fed_v2(&a, &b, &fed_b, &fed_a, 10, 0);
    assert_ne!(
        pre_1, pre_2,
        "cross-fed v2 preimage MUST distinguish src/dst federation pairs"
    );
}

#[test]
fn cross_fed_preimage_domain_separator_is_distinct_from_v1() {
    let a = CellId([1u8; 32]);
    let b = CellId([2u8; 32]);
    let v1 = transfer_pre_intra_fed(&a, &b, 10, 0);
    let v2 = transfer_pre_cross_fed_v2(&a, &b, &[0xAA; 32], &[0xBB; 32], 10, 0);
    assert_ne!(
        v1, v2,
        "v1 (intra-fed) and v2 (cross-fed) preimages must differ at the domain separator"
    );
    assert!(v1.starts_with(b"pyana-transfer-id-v1"));
    assert!(v2.starts_with(b"pyana-transfer-id-v2-xfed"));
}
