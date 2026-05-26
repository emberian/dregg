//! Capability monotone attenuation invariant.
//!
//! > No turn can grant a capability that's broader than the granter's own
//! > held capability.
//!
//! Operationally: we set up a `parent` cell holding a capability over a
//! `target` cell with random `parent_perms`. We then issue a turn from
//! `parent` carrying `Effect::GrantCapability` that hands a copy of that
//! capability to `recipient` with random `grant_perms`. INVARIANT: the
//! executor commits iff `is_attenuation(parent_perms, grant_perms)` (i.e.
//! the grant is narrower-or-equal). Otherwise it must reject with
//! `DelegationDenied` and `recipient`'s c-list must be unchanged.
//!
//! Note: a key edge case is the *self-grant* path — the executor short-
//! circuits attenuation checks when `cap.target == from` because the
//! signing cell holds an implicit strongest-cap over itself. We exclude
//! self-grants from the strategy so every iteration exercises the real
//! attenuation check.

use crate::Invariant;

use proptest::prelude::*;

pub struct CapabilityAttenuation;

impl Invariant for CapabilityAttenuation {
    const NAME: &'static str = "capability_attenuation";
    const DESCRIPTION: &'static str = "granted capability permissions are always narrower-or-equal to the granter's held permissions";
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// For any (parent_perms, grant_perms) pair, `Effect::GrantCapability`
    /// commits iff `is_attenuation(parent_perms, grant_perms)`.
    #[test]
    fn capability_attenuation_holds(
        parent_perms in arb_auth_required(),
        grant_perms in arb_auth_required(),
    ) {
        // 3-cell ledger: 0 = parent (granter), 1 = recipient, 2 = target.
        let spec = LedgerSpec {
            n_cells: 3,
            balance_each: 10_000,
            wide_open: true,
        };
        let (mut ledger, ids) = build_open_ledger(&spec);
        let parent_id = ids[0];
        let recipient_id = ids[1];
        let target_id = ids[2];

        // Replace parent's auto-granted capability to `target` with one
        // whose permissions are exactly `parent_perms`. The wide_open
        // ledger gave parent an `AuthRequired::None` cap to every other
        // cell — we revoke and re-grant so the attenuation check sees the
        // expected ceiling.
        {
            let parent_cell = ledger.get_mut(&parent_id).unwrap();
            // Find and revoke the existing slot pointing at `target`.
            let slot = parent_cell
                .capabilities
                .lookup_by_target(&target_id)
                .map(|c| c.slot);
            if let Some(s) = slot {
                parent_cell.capabilities.revoke(s);
            }
            parent_cell
                .capabilities
                .grant(target_id, parent_perms.clone());
        }

        // Recipient's c-list count before the grant — we'll compare after
        // to detect whether the grant landed.
        let recipient_caps_before: usize = ledger
            .get(&recipient_id)
            .unwrap()
            .capabilities
            .iter()
            .count();

        // Build the grant turn: parent issues GrantCapability(target,
        // grant_perms) to recipient.
        let nonce = ledger.get(&parent_id).unwrap().state.nonce();
        let cap = CapabilityRef {
            target: target_id,
            // Slot is rewritten by the executor on grant; the value here
            // is irrelevant.
            slot: 0,
            permissions: grant_perms.clone(),
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
        };
        let action = Action {
            target: parent_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![Effect::GrantCapability {
                from: parent_id,
                to: recipient_id,
                cap,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = CallForest::new();
        forest.add_root(action);
        let turn = Turn {
            agent: parent_id,
            nonce,
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

        let expected_accept = is_attenuation(&parent_perms, &grant_perms);

        if expected_accept {
            prop_assert!(
                result.is_committed(),
                "is_attenuation({:?}, {:?}) is true but executor rejected: {:?}",
                parent_perms, grant_perms, result,
            );
            // Recipient's c-list must have grown by exactly one entry
            // pointing at `target` with `grant_perms`.
            let recipient_caps_after: Vec<_> = ledger
                .get(&recipient_id)
                .unwrap()
                .capabilities
                .iter()
                .cloned()
                .collect();
            prop_assert_eq!(
                recipient_caps_after.len(),
                recipient_caps_before + 1,
                "successful grant must add exactly one cap to recipient",
            );
            let found = recipient_caps_after.iter().any(|c| {
                c.target == target_id && c.permissions == grant_perms
            });
            prop_assert!(
                found,
                "grant succeeded but recipient lacks an entry to target with the granted perms",
            );
        } else {
            // is_attenuation returned false → grant_perms is wider than
            // parent_perms. Must reject (DelegationDenied) and leave the
            // recipient's c-list untouched.
            prop_assert!(
                result.is_rejected(),
                "is_attenuation({:?}, {:?}) is false but executor accepted: {:?}",
                parent_perms, grant_perms, result,
            );
            match &result {
                TurnResult::Rejected { reason, .. } => {
                    // The executor must reject specifically because the
                    // grant was non-attenuating, not for some other reason
                    // (CellNotFound, AuthorizationFailed, etc).
                    let kind = format!("{:?}", reason);
                    prop_assert!(
                        kind.contains("DelegationDenied"),
                        "expected DelegationDenied for non-attenuating grant, got {:?}",
                        reason,
                    );
                }
                other => prop_assert!(
                    false,
                    "expected Rejected, got {:?}",
                    other,
                ),
            }
            let recipient_caps_after = ledger
                .get(&recipient_id)
                .unwrap()
                .capabilities
                .iter()
                .count();
            prop_assert_eq!(
                recipient_caps_after,
                recipient_caps_before,
                "rejected grant must not mutate recipient's c-list",
            );
            // Sanity: parent_perms is strictly narrower than grant_perms
            // (the predicate is "granted narrower-or-equal to held"; if
            // it's false, grant_perms is wider).
            prop_assert!(
                !AuthRequired::is_narrower_or_equal(&grant_perms, &parent_perms),
                "consistency: is_attenuation returned false but grant_perms IS narrower-or-equal",
            );
        }
    }
}
