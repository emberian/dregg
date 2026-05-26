//! Facet attenuation invariant.
//!
//! > A bearer capability's facet mask must be a bitwise-subset of the
//! > delegator's mask. No bit set in child that isn't set in parent.
//!
//! Operationally: we build a 3-cell ledger (delegator, bearer, target),
//! grant `delegator` a *faceted* capability to `target` with a random
//! `parent_mask`, and then submit a turn from `bearer` exercising
//! `Authorization::Bearer` carrying a `BearerCapProof` whose
//! `allowed_effects` field is a random `child_mask`. INVARIANT: the
//! executor accepts iff `(child_mask & !parent_mask) == 0`, i.e.
//! `is_facet_attenuation(parent, child)`. When it rejects, it must do so
//! with `BearerCapFacetAmplification`.
//!
//! The action's effect is a single `EmitEvent` (cheap, no side effects to
//! reason about) — we're testing the gating predicate, not what runs
//! after.

use crate::Invariant;

use ed25519_dalek::{SigningKey, VerifyingKey};
use proptest::prelude::*;

pub struct FacetAttenuation;

impl Invariant for FacetAttenuation {
    const NAME: &'static str = "facet_attenuation";
    const DESCRIPTION: &'static str =
        "bearer-cap allowed_effects masks are bitwise-subset of the delegator's mask";
}

/// Build a real-Ed25519 keypair from a single-byte seed (matches the
/// pattern in `turn/src/tests.rs::TestKeypair::from_seed`).
fn keypair_from_seed(seed: u8) -> (SigningKey, [u8; 32]) {
    let mut seed_bytes = [0u8; 32];
    seed_bytes[0] = seed;
    let sk = SigningKey::from_bytes(&seed_bytes);
    let vk: VerifyingKey = (&sk).into();
    (sk, vk.to_bytes())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// For any (parent_mask, child_mask) pair where parent_mask is non-zero
    /// (so the facet restriction actually applies), the executor accepts the
    /// bearer turn iff `is_facet_attenuation(parent, child)`.
    #[test]
    fn facet_attenuation_holds(
        parent_mask in 1u32..=u32::MAX,
        child_mask in 0u32..=u32::MAX,
    ) {
        // We use real Ed25519 keys for delegator + bearer so the signed
        // delegation actually verifies. Target uses a synthetic key (it
        // doesn't sign anything).
        let (delegator_sk, delegator_pk) = keypair_from_seed(101);
        let (_bearer_sk, bearer_pk) = keypair_from_seed(102);
        let token_id = [0u8; 32];

        let permissive = dregg_cell::Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };

        // Build the 3 cells by hand because the delegator + bearer need to
        // be tied to specific public keys (so the delegation signature
        // verifies). The `build_open_ledger` helper assigns synthetic keys
        // we can't sign with.
        let mut ledger = dregg_cell::Ledger::new();

        let mut delegator_cell = Cell::with_balance(delegator_pk, token_id, 10_000);
        delegator_cell.permissions = permissive.clone();

        let mut bearer_cell = Cell::with_balance(bearer_pk, token_id, 10_000);
        bearer_cell.permissions = permissive.clone();
        let bearer_id = bearer_cell.id();

        let mut target_pk = [0u8; 32];
        target_pk[0] = 200;
        let mut target_cell = Cell::with_balance(target_pk, token_id, 10_000);
        target_cell.permissions = permissive.clone();
        let target_id = target_cell.id();

        // Delegator must hold a faceted capability to target.
        delegator_cell.capabilities.grant_faceted(
            target_id,
            AuthRequired::None,
            parent_mask as EffectMask,
        );

        ledger.insert_cell(delegator_cell).unwrap();
        ledger.insert_cell(bearer_cell).unwrap();
        ledger.insert_cell(target_cell).unwrap();

        let expires_at: u64 = 1_000_000;

        // Build and sign the bearer-cap delegation. The bearer's claimed
        // permission is `AuthRequired::None` (matches delegator's), so the
        // permission-attenuation check passes — leaving facet-attenuation
        // as the only gate.
        let message = TurnExecutor::compute_bearer_delegation_message(
            &target_id,
            &AuthRequired::None,
            &bearer_pk,
            expires_at,
            &[0u8; 32],
        );
        let signature = delegator_sk.sign(&message).to_bytes();
        let bearer_proof = BearerCapProof {
            target: target_id,
            permissions: AuthRequired::None,
            delegation_proof: DelegationProofData::SignedDelegation {
                delegator_pk,
                signature,
                bearer_pk,
            },
            expires_at,
            revocation_channel: None,
            allowed_effects: Some(child_mask as EffectMask),
        };

        // Action: emit a no-op event on target. Authorization is Bearer.
        let action = Action {
            target: target_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Bearer(bearer_proof),
            preconditions: Default::default(),
            effects: vec![Effect::EmitEvent {
                cell: target_id,
                event: dregg_turn::Event {
                    topic: [0u8; 32],
                    data: vec![],
                },
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = CallForest::new();
        forest.add_root(action);

        let turn = Turn {
            agent: bearer_id,
            nonce: 0,
            call_forest: forest,
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let result = executor.execute(&turn, &mut ledger);

        let expected_accept = is_facet_attenuation(
            parent_mask as EffectMask,
            child_mask as EffectMask,
        );

        if expected_accept {
            prop_assert!(
                result.is_committed(),
                "is_facet_attenuation({:#x}, {:#x}) is true but executor rejected: {:?}",
                parent_mask, child_mask, result,
            );
        } else {
            prop_assert!(
                result.is_rejected(),
                "is_facet_attenuation({:#x}, {:#x}) is false but executor accepted: {:?}",
                parent_mask, child_mask, result,
            );
            match &result {
                TurnResult::Rejected { reason, .. } => {
                    let kind = format!("{:?}", reason);
                    prop_assert!(
                        kind.contains("BearerCapFacetAmplification"),
                        "expected BearerCapFacetAmplification for non-attenuating facet \
                         (parent={:#x}, child={:#x}), got {:?}",
                        parent_mask, child_mask, reason,
                    );
                }
                other => prop_assert!(
                    false,
                    "expected Rejected, got {:?}",
                    other,
                ),
            }
        }
    }
}
