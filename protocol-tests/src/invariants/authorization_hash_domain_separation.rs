//! Protocol invariant: every `Authorization` variant occupies a distinct
//! domain in the action hash, and tampering with any field changes the
//! hash.
//!
//! This is the **soundness floor** for executor honesty threats T1/T2/T15
//! (EXECUTOR-HONESTY-AUDIT.md): if the action hash didn't separate the
//! variants and didn't cover each field, the executor could swap one
//! Authorization for another without invalidating the signed-turn hash.
//!
//! Source: `turn/src/action.rs::Action::hash`.

use crate::Invariant;
use dregg_cell::CellId;
use dregg_turn::DelegationMode;
use dregg_turn::action::{Action, Authorization};
use proptest::prelude::*;

pub struct AuthorizationHashDomainSeparation;
impl Invariant for AuthorizationHashDomainSeparation {
    const NAME: &'static str = "authorization_hash_domain_separation";
    const DESCRIPTION: &'static str =
        "Authorization variants and their fields are domain-separated in Action::hash";
}

fn dummy_action(target: CellId, auth: Authorization) -> Action {
    Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: auth,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    }
}

fn arb_cell_id() -> impl Strategy<Value = CellId> {
    any::<[u8; 32]>().prop_map(CellId)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// Two different `Signature` halves produce different action hashes.
    #[test]
    fn signature_tamper_changes_hash(
        target in arb_cell_id(),
        r1 in any::<[u8; 32]>(),
        r2 in any::<[u8; 32]>(),
        s in any::<[u8; 32]>(),
    ) {
        prop_assume!(r1 != r2);
        let h1 = dummy_action(target, Authorization::Signature(r1, s)).hash();
        let h2 = dummy_action(target, Authorization::Signature(r2, s)).hash();
        prop_assert_ne!(h1, h2);
    }

    /// `Breadstuff` token tamper changes hash.
    #[test]
    fn breadstuff_tamper_changes_hash(
        target in arb_cell_id(),
        tok1 in any::<[u8; 32]>(),
        tok2 in any::<[u8; 32]>(),
    ) {
        prop_assume!(tok1 != tok2);
        let h1 = dummy_action(target, Authorization::Breadstuff(tok1)).hash();
        let h2 = dummy_action(target, Authorization::Breadstuff(tok2)).hash();
        prop_assert_ne!(h1, h2);
    }

    /// `Proof` bound_resource is part of the hash (it's the audience
    /// binding from the verifier-side and must be tamper-evident).
    #[test]
    fn proof_bound_resource_changes_hash(
        target in arb_cell_id(),
        res_a in "[a-z]{1,16}",
        res_b in "[a-z]{1,16}",
    ) {
        prop_assume!(res_a != res_b);
        let h1 = dummy_action(
            target,
            Authorization::Proof {
                proof_bytes: vec![],
                bound_action: "act".to_string(),
                bound_resource: res_a,
            },
        )
        .hash();
        let h2 = dummy_action(
            target,
            Authorization::Proof {
                proof_bytes: vec![],
                bound_action: "act".to_string(),
                bound_resource: res_b,
            },
        )
        .hash();
        prop_assert_ne!(h1, h2);
    }

    /// `Bearer` expires_at changes hash — the expiry is part of the bearer cap.
    #[test]
    fn bearer_expires_at_changes_hash(
        target in arb_cell_id(),
        delegator in any::<[u8; 32]>(),
        bearer in any::<[u8; 32]>(),
        expiry_a in 0u64..1_000_000,
        expiry_b in 1_000_000u64..2_000_000,
    ) {
        prop_assume!(expiry_a != expiry_b);
        let mk = |exp: u64| {
            Authorization::Bearer(BearerCapProof {
                target,
                permissions: dregg_cell::AuthRequired::None,
                delegation_proof: DelegationProofData::SignedDelegation {
                    delegator_pk: delegator,
                    signature: [0u8; 64],
                    bearer_pk: bearer,
                },
                expires_at: exp,
                revocation_channel: None,
                allowed_effects: None,
            })
        };
        prop_assert_ne!(
            dummy_action(target, mk(expiry_a)).hash(),
            dummy_action(target, mk(expiry_b)).hash()
        );
    }

    /// `Authorization::Custom` predicate tamper (kind change) → hash diff.
    #[test]
    fn custom_predicate_tamper_changes_hash(
        target in arb_cell_id(),
        commit_a in any::<[u8; 32]>(),
        commit_b in any::<[u8; 32]>(),
    ) {
        use dregg_cell::predicate::WitnessedPredicate;
        use dregg_cell::InputRef;
        prop_assume!(commit_a != commit_b);
        let pa = WitnessedPredicate::dfa(commit_a, InputRef::SigningMessage, 0);
        let pb = WitnessedPredicate::dfa(commit_b, InputRef::SigningMessage, 0);
        prop_assert_ne!(
            dummy_action(target, Authorization::Custom { predicate: pa }).hash(),
            dummy_action(target, Authorization::Custom { predicate: pb }).hash()
        );
    }

    /// Cross-variant distinctness: Signature, Breadstuff, Unchecked are
    /// pairwise distinct for any input.
    #[test]
    fn cross_variant_distinctness(
        target in arb_cell_id(),
        sig_r in any::<[u8; 32]>(),
        sig_s in any::<[u8; 32]>(),
        tok in any::<[u8; 32]>(),
    ) {
        let h_sig =
            dummy_action(target, Authorization::Signature(sig_r, sig_s)).hash();
        let h_brd =
            dummy_action(target, Authorization::Breadstuff(tok)).hash();
        let h_unc = dummy_action(target, Authorization::Unchecked).hash();
        prop_assert_ne!(h_sig, h_brd);
        prop_assert_ne!(h_sig, h_unc);
        prop_assert_ne!(h_brd, h_unc);
    }
}
