//! Permission enforcement invariant.
//!
//! > For each permission slot on a target cell, the executor accepts an
//! > action iff the action's authorization satisfies the cell's
//! > `AuthRequired` for that slot.
//!
//! Operationally: build an agent cell with a controlled `AuthRequired` on
//! its `set_state` permission, submit a turn carrying `Effect::SetField`
//! against the agent itself with a chosen `Authorization`, and assert
//! that the executor's accept/reject decision matches the cell-level
//! predicate `AuthRequired::is_satisfied_by(AuthKind)` (or `true` for
//! `AuthRequired::None` regardless of provided auth).
//!
//! Test surface:
//! - `AuthRequired::{None, Signature, Proof, Either, Impossible}` × 5
//! - `Authorization::{Unchecked, Signature(real_sig)}` × 2
//!
//! We don't randomize over `Authorization::Proof` because random proof
//! bytes always fail verification — the executor would reject for the
//! wrong reason and we'd be testing crypto, not the invariant. Likewise
//! we keep the action at the agent itself so capability and delegation
//! gates don't interfere.
//!
//! Why pick `set_state` as the slot under test? It's exercised by
//! `Effect::SetField`, which the executor routes through the
//! `SetState` permission path with no other side-checks (unlike Send,
//! which also requires balance, or Delegate, which also requires c-list
//! lookup). That keeps the only failing gate the one we're studying.

use crate::Invariant;

use ed25519_dalek::{Signer, SigningKey, VerifyingKey};
use proptest::prelude::*;
use pyana_cell::{AuthKind, AuthRequired, Cell, Permissions};
use pyana_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    TurnResult, turn::Turn,
};

pub struct PermissionEnforcement;

impl Invariant for PermissionEnforcement {
    const NAME: &'static str = "permission_enforcement";
    const DESCRIPTION: &'static str =
        "executor accepts an action iff cell.permissions for the action's slot is satisfied by the provided authorization";
}

/// Strategy: any `AuthRequired`.
fn arb_auth_required_all() -> impl Strategy<Value = AuthRequired> {
    prop_oneof![
        Just(AuthRequired::None),
        Just(AuthRequired::Signature),
        Just(AuthRequired::Proof),
        Just(AuthRequired::Either),
        Just(AuthRequired::Impossible),
    ]
}

/// Subset of `Authorization` whose use doesn't require real crypto
/// verification of fake bytes. `Signature` is generated with a real
/// signing key tied to the cell, so it verifies; `Unchecked` carries no
/// auth claim.
#[derive(Clone, Debug, Copy)]
enum AuthChoice {
    Unchecked,
    Signature,
}

fn arb_auth_choice() -> impl Strategy<Value = AuthChoice> {
    prop_oneof![Just(AuthChoice::Unchecked), Just(AuthChoice::Signature),]
}

/// Permissions with `set_state` set to `req` and everything else open.
fn permissions_with_set_state(req: AuthRequired) -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: req,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn keypair_from_seed(seed: u8) -> (SigningKey, [u8; 32]) {
    let mut seed_bytes = [0u8; 32];
    seed_bytes[0] = seed;
    let sk = SigningKey::from_bytes(&seed_bytes);
    let vk: VerifyingKey = (&sk).into();
    (sk, vk.to_bytes())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Across every `(AuthRequired, AuthChoice)` cross-product, the
    /// executor's accept/reject decision agrees with the cell-side
    /// predicate.
    #[test]
    fn permission_enforcement_holds(
        req in arb_auth_required_all(),
        choice in arb_auth_choice(),
    ) {
        let (sk, pk) = keypair_from_seed(50);
        let token_id = [0u8; 32];

        let mut agent = Cell::with_balance(pk, token_id, 10_000);
        agent.permissions = permissions_with_set_state(req.clone());
        let agent_id = agent.id();

        let mut ledger = pyana_cell::Ledger::new();
        ledger.insert_cell(agent).unwrap();

        // Build the action (SetField on self), with placeholder
        // authorization that we'll replace after computing the action
        // hash if `choice == Signature`.
        let mut action = Action {
            target: agent_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![Effect::SetField {
                cell: agent_id,
                index: 0,
                value: [7u8; 32],
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
        };

        let provided_kind: Option<AuthKind> = match choice {
            AuthChoice::Unchecked => {
                action.authorization = Authorization::Unchecked;
                None
            }
            AuthChoice::Signature => {
                // Sign over the canonical signing message (matches the
                // executor's `compute_signing_message`).
                let msg = TurnExecutor::compute_signing_message(&action, &[0u8; 32]);
                let sig = sk.sign(&msg).to_bytes();
                let mut r = [0u8; 32];
                let mut s = [0u8; 32];
                r.copy_from_slice(&sig[..32]);
                s.copy_from_slice(&sig[32..]);
                action.authorization = Authorization::Signature(r, s);
                Some(AuthKind::Signature)
            }
        };

        let mut forest = CallForest::new();
        forest.add_root(action);
        let turn = Turn {
            agent: agent_id,
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
        };

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let result = executor.execute(&turn, &mut ledger);

        // Reconstruct the cell-side predicate:
        // `AuthRequired::None` always accepts (no auth required);
        // otherwise we need an AuthKind that `is_satisfied_by` returns true.
        let cell_side_accepts = match (&req, &provided_kind) {
            (AuthRequired::None, _) => true,
            (_, None) => false,
            (r, Some(k)) => r.is_satisfied_by(k),
        };

        if cell_side_accepts {
            prop_assert!(
                result.is_committed(),
                "cell predicate says accept ({:?} satisfied by {:?}) but executor rejected: {:?}",
                req, choice, result,
            );
            // Sanity: the field actually moved.
            prop_assert_eq!(
                ledger.get(&agent_id).unwrap().state.fields[0],
                [7u8; 32],
                "accepted SetField should have written the field",
            );
        } else {
            prop_assert!(
                result.is_rejected(),
                "cell predicate says reject ({:?} NOT satisfied by {:?}) but executor accepted: {:?}",
                req, choice, result,
            );
            // The rejection must specifically be a PermissionDenied —
            // anything else means the executor rejected for an unrelated
            // reason and we're not actually testing the permission gate.
            match &result {
                TurnResult::Rejected { reason, .. } => {
                    let kind = format!("{:?}", reason);
                    prop_assert!(
                        kind.contains("PermissionDenied")
                            || kind.contains("InvalidSignature")
                            || kind.contains("AuthorizationFailed"),
                        "expected PermissionDenied/InvalidSignature/AuthorizationFailed \
                         for ({:?}, {:?}), got {:?}",
                        req, choice, reason,
                    );
                }
                other => prop_assert!(
                    false,
                    "expected Rejected, got {:?}",
                    other,
                ),
            }
            // Field must not have been written (rollback on rejection).
            prop_assert_ne!(
                ledger.get(&agent_id).unwrap().state.fields[0],
                [7u8; 32],
                "rejected turn should not write the field",
            );
        }
    }
}
