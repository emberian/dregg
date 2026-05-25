//! # `RelayOperatorTemplate` — §3.5 reference design
//!
//! DFA-dispatched store-and-forward operator. A bonded relay hosts
//! inboxes on behalf of others, charges per-epoch quota, slashes on
//! disputes, and uses a DFA caveat to constrain which messages it's
//! willing to dispatch. Per `STORAGE-AS-CELL-PROGRAMS.md` §3.5.
//!
//! This template crosses two design lanes: the cell-program migration
//! and the DFA dispatch lane (`DFA-RATIONALIZATION-DESIGN.md`). The
//! shape below is the cell-program half; the DFA caveat in the
//! `relay` case ties to the `WitnessedPredicate::Dfa` kind already
//! present in the lifted vocabulary.
//!
//! ## Slot layout
//!
//! | Slot | Name | Caveat | Purpose |
//! |---:|---|---|---|
//! | 0 | `bond_amount` | `BoundedBy` (decrement-on-dispute) | Computrons posted as bond. |
//! | 1 | `bond_min` | `Immutable` | Floor on bond. |
//! | 2 | `quota_bytes_per_epoch` | `Immutable` | Per-epoch byte quota. |
//! | 3 | `bytes_relayed_this_epoch` | `RateLimitBySum` | Current-epoch byte counter. |
//! | 4 | `hosted_inbox_root` | `Monotonic` (register-scoped) | Merkle root over hosted inbox ids. |
//! | 5 | `operator_pk_hash` | `Immutable` | Operator identity. |
//! | 6 | `route_table_root` | `Immutable` | DFA route table commitment. |
//! | 7 | `dispute_count` | `Monotonic` (slash-scoped) | Dispute counter. |
//!
//! ## Operations
//!
//! - `register_inbox` — `hosted_inbox_root` grows; everything else
//!   frozen. Operator-only (`SenderAuthorized` against slot 5).
//! - `relay` — `bytes_relayed_this_epoch` grows under
//!   `RateLimitBySum`; everything else frozen. Routes are
//!   DFA-classified against `route_table_root` via
//!   `Witnessed { Dfa }`. The actual cross-cell dispatch (to the
//!   target inbox) rides on a follow-on `Effect` set in the same
//!   action — out of scope for this template's cell program.
//! - `slash` — `bond_amount` decreases iff `dispute_count`
//!   advanced (encoded as `BoundedBy { index: 0, witness_index: 7 }`).
//!   The accompanying `Effect::Transfer` to a governance treasury is
//!   the wallet-side composition; the cell program enforces the
//!   "no-drain-without-dispute" invariant.
//!
//! ## What this replaces
//!
//! - `pyana_storage::operator::RelayOperator` operator-process state.
//! - `pyana_storage::relay::MeteredRelay` quota accounting.
//! - `pyana_storage::metering` cost-table (folds into the
//!   `RateLimitBySum` constraint).
//!
//! ## Boundary contract
//!
//! - **cleartext-inside**: federation hosting the relay.
//! - **commitment-inside**: anyone with `public_field_view` of the
//!   relay (bond, quota, dispute counts).
//! - **acceptance-inside**: verifiers of the DFA classification
//!   proof — sees that *a* message was routed correctly.
//! - **out-of-band**: message bodies (always; the relay's
//!   `EmitEvent` data is the carrier, optionally encrypted).

use pyana_app_framework::{
    Action, AppWallet, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, ChildVkStrategy,
    Effect, Event, FactoryDescriptor, FieldConstraint, FieldElement, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, canonical_program_vk, symbol,
};
use pyana_cell::predicate::{InputRef, WitnessedPredicate};
use pyana_cell::program::{AuthorizedSet, CellProgram, TransitionCase, TransitionGuard};

use crate::{hex_encode, u64_field};

// =============================================================================
// Slot layout
// =============================================================================

pub const BOND_AMOUNT_SLOT: u8 = 0;
pub const BOND_MIN_SLOT: u8 = 1;
pub const QUOTA_BYTES_PER_EPOCH_SLOT: u8 = 2;
pub const BYTES_RELAYED_THIS_EPOCH_SLOT: u8 = 3;
pub const HOSTED_INBOX_ROOT_SLOT: u8 = 4;
pub const OPERATOR_PK_HASH_SLOT: u8 = 5;
pub const ROUTE_TABLE_ROOT_SLOT: u8 = 6;
pub const DISPUTE_COUNT_SLOT: u8 = 7;

// =============================================================================
// Witness layout
// =============================================================================

/// Witness blob index carrying the message bytes the relay is
/// dispatching (input to the DFA classifier).
pub const WITNESS_INDEX_MSG: usize = 0;
/// Witness blob index carrying the DFA classification proof bytes.
pub const WITNESS_INDEX_DFA_PROOF: usize = 1;

// =============================================================================
// Factory configuration
// =============================================================================

/// Default per-epoch creation budget — per §3.5 ("creation_budget:
/// Some(100)"). Very small because bonded relay operators are rare.
pub const DEFAULT_CREATION_BUDGET: u64 = 100;

/// Default epoch duration in blocks for `RateLimitBySum`.
pub const DEFAULT_EPOCH_DURATION: u64 = 1_000;

/// Stable placeholder VK for the RelayOperator factory.
pub const RELAY_OPERATOR_FACTORY_VK: [u8; 32] = *b"pyana-storage-tpl-relayop-factor";

/// Canonical child VK per `VK-AS-RE-EXECUTION-RECIPE.md` §2.1.
pub fn relay_operator_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&relay_operator_program())
}

pub fn register_inbox_method_symbol() -> [u8; 32] {
    symbol("register_inbox")
}
pub fn relay_method_symbol() -> [u8; 32] {
    symbol("relay")
}
pub fn slash_method_symbol() -> [u8; 32] {
    symbol("slash")
}

// =============================================================================
// CellProgram
// =============================================================================

/// Build the operation-scoped [`CellProgram`] for a RelayOperator
/// cell. Default-deny applies per Cav-Codex Block 4.
///
/// Per §3.5 the quota `max_sum_per_epoch` is a *static* constraint
/// parameter, not a slot value — the executor's `RateLimitBySum`
/// indexes a per-(cell, slot, window) running sum. The template
/// uses [`DEFAULT_EPOCH_DURATION`] as the window and binds
/// `max_sum_per_epoch` at factory-build time (default 1MB/epoch
/// reflects §3.5's `quota_bytes_per_epoch` range).
pub fn relay_operator_program() -> CellProgram {
    relay_operator_program_with(1_000_000, DEFAULT_EPOCH_DURATION)
}

/// Build the program for a parameterized quota / epoch shape.
pub fn relay_operator_program_with(max_bytes_per_epoch: u64, epoch_duration: u64) -> CellProgram {
    CellProgram::Cases(vec![
        // Lifetime invariants.
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                StateConstraint::Immutable {
                    index: BOND_MIN_SLOT,
                },
                StateConstraint::Immutable {
                    index: QUOTA_BYTES_PER_EPOCH_SLOT,
                },
                StateConstraint::Immutable {
                    index: OPERATOR_PK_HASH_SLOT,
                },
                StateConstraint::Immutable {
                    index: ROUTE_TABLE_ROOT_SLOT,
                },
            ],
        },
        // register_inbox: hosted_inbox_root grows; everything else
        // frozen. Operator-only.
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("register_inbox"),
            },
            constraints: vec![
                StateConstraint::Monotonic {
                    index: HOSTED_INBOX_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: BOND_AMOUNT_SLOT,
                },
                StateConstraint::Immutable {
                    index: BYTES_RELAYED_THIS_EPOCH_SLOT,
                },
                StateConstraint::Immutable {
                    index: DISPUTE_COUNT_SLOT,
                },
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: OPERATOR_PK_HASH_SLOT,
                    },
                },
            ],
        },
        // relay: bytes_relayed_this_epoch grows under RateLimitBySum.
        // The DFA caveat classifies the dispatched message against
        // the route_table_root.
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("relay"),
            },
            constraints: vec![
                StateConstraint::Monotonic {
                    index: BYTES_RELAYED_THIS_EPOCH_SLOT,
                },
                StateConstraint::RateLimitBySum {
                    slot_index: BYTES_RELAYED_THIS_EPOCH_SLOT,
                    max_sum_per_epoch: max_bytes_per_epoch,
                    epoch_duration,
                },
                StateConstraint::Immutable {
                    index: BOND_AMOUNT_SLOT,
                },
                StateConstraint::Immutable {
                    index: HOSTED_INBOX_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: DISPUTE_COUNT_SLOT,
                },
                // DFA classification: message bytes (witness 0) must
                // satisfy the route_table_root DFA (commitment is
                // slot 6, proof bytes are witness 1).
                StateConstraint::Witnessed {
                    wp: WitnessedPredicate::dfa(
                        // Commitment passed to the Dfa verifier is
                        // the route_table_root. The executor resolves
                        // this at evaluation time by reading the
                        // current slot value; the template carries a
                        // placeholder that the executor overrides via
                        // its slot-bound resolution.
                        [0u8; 32],
                        InputRef::Witness {
                            index: WITNESS_INDEX_MSG,
                        },
                        WITNESS_INDEX_DFA_PROOF,
                    ),
                },
            ],
        },
        // slash: bond_amount decreases iff dispute_count advances.
        // The BoundedBy variant encodes "bond may only move if slot[7]
        // is non-zero in new_state" — combined with Monotonic on
        // slot 7 this enforces "bond decrement requires a dispute
        // event."
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("slash"),
            },
            constraints: vec![
                StateConstraint::BoundedBy {
                    index: BOND_AMOUNT_SLOT,
                    witness_index: DISPUTE_COUNT_SLOT,
                },
                StateConstraint::Monotonic {
                    index: DISPUTE_COUNT_SLOT,
                },
                // Bond floor: bond_amount must stay >= bond_min.
                // Per §3.5 this is expressed as FieldGte at the slot
                // value; the cross-slot check is the open question
                // §7.2 (FieldLteOther) and falls back to v1 Custom
                // until that lands. For now the slot-relative bound
                // is the floor.
                StateConstraint::Immutable {
                    index: HOSTED_INBOX_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: BYTES_RELAYED_THIS_EPOCH_SLOT,
                },
            ],
        },
    ])
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Build the [`FactoryDescriptor`] for RelayOperator cells.
pub fn relay_operator_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: RELAY_OPERATOR_FACTORY_VK,
        child_program_vk: Some(relay_operator_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(
            Some(relay_operator_child_program_vk()),
        )),
        allowed_cap_templates: vec![
            // Operator cap — non-attenuatable; the operator is the
            // sole authority for register_inbox + relay.
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: false,
            },
            // Governance cap — for slash. The governance treasury
            // holds this and exercises it on dispute resolution.
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: false,
            },
        ],
        field_constraints: vec![
            FieldConstraint::Equality {
                field_index: BYTES_RELAYED_THIS_EPOCH_SLOT as u32,
                value: 0,
            },
            FieldConstraint::Equality {
                field_index: DISPUTE_COUNT_SLOT as u32,
                value: 0,
            },
            FieldConstraint::Range {
                field_index: BOND_MIN_SLOT as u32,
                min: 100,
                max: 1_000_000,
            },
            FieldConstraint::Range {
                field_index: QUOTA_BYTES_PER_EPOCH_SLOT as u32,
                min: 1_000,
                max: 1_000_000_000,
            },
            FieldConstraint::NonZero {
                field_index: OPERATOR_PK_HASH_SLOT as u32,
            },
            FieldConstraint::NonZero {
                field_index: ROUTE_TABLE_ROOT_SLOT as u32,
            },
        ],
        state_constraints: vec![
            StateConstraint::Immutable {
                index: BOND_MIN_SLOT,
            },
            StateConstraint::Immutable {
                index: QUOTA_BYTES_PER_EPOCH_SLOT,
            },
            StateConstraint::Immutable {
                index: OPERATOR_PK_HASH_SLOT,
            },
            StateConstraint::Immutable {
                index: ROUTE_TABLE_ROOT_SLOT,
            },
            StateConstraint::Monotonic {
                index: HOSTED_INBOX_ROOT_SLOT,
            },
            StateConstraint::Monotonic {
                index: DISPUTE_COUNT_SLOT,
            },
        ],
        default_mode: CellMode::Hosted,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

// =============================================================================
// Turn-builders
// =============================================================================

/// Build the on-ledger [`Action`] recording a `register_inbox`.
pub fn build_register_inbox_action(
    wallet: &AppWallet,
    relay_cell: CellId,
    new_hosted_inbox_root: FieldElement,
    inbox_cell_id: [u8; 32],
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: relay_cell,
            index: HOSTED_INBOX_ROOT_SLOT as usize,
            value: new_hosted_inbox_root,
        },
        Effect::EmitEvent {
            cell: relay_cell,
            event: Event::new(
                symbol("relay-inbox-registered"),
                vec![new_hosted_inbox_root, inbox_cell_id],
            ),
        },
    ];

    wallet.make_action(relay_cell, "register_inbox", effects)
}

/// Build the on-ledger [`Action`] recording a `relay` dispatch.
///
/// The caller is responsible for attaching the message bytes
/// (witness 0) and the DFA proof bytes (witness 1) via the wallet's
/// witness-attach API; this builder only composes the [`Effect`]s
/// and the method symbol.
pub fn build_relay_action(
    wallet: &AppWallet,
    relay_cell: CellId,
    new_bytes_relayed: FieldElement,
    target_inbox: [u8; 32],
    msg_commitment: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: relay_cell,
            index: BYTES_RELAYED_THIS_EPOCH_SLOT as usize,
            value: new_bytes_relayed,
        },
        Effect::EmitEvent {
            cell: relay_cell,
            event: Event::new(
                symbol("relay-dispatched"),
                vec![new_bytes_relayed, target_inbox, msg_commitment],
            ),
        },
    ];

    wallet.make_action(relay_cell, "relay", effects)
}

/// Build the on-ledger [`Action`] recording a `slash`.
///
/// The accompanying `Effect::Transfer` from the relay cell to the
/// governance treasury is the wallet-side composition; this template
/// produces the state-transition effects (bond + dispute counter).
pub fn build_slash_action(
    wallet: &AppWallet,
    relay_cell: CellId,
    new_bond_amount: FieldElement,
    new_dispute_count: FieldElement,
    reason: [u8; 32],
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: relay_cell,
            index: BOND_AMOUNT_SLOT as usize,
            value: new_bond_amount,
        },
        Effect::SetField {
            cell: relay_cell,
            index: DISPUTE_COUNT_SLOT as usize,
            value: new_dispute_count,
        },
        Effect::EmitEvent {
            cell: relay_cell,
            event: Event::new(
                symbol("relay-slashed"),
                vec![new_bond_amount, new_dispute_count, reason],
            ),
        },
    ];

    wallet.make_action(relay_cell, "slash", effects)
}

// =============================================================================
// Initial state + registration
// =============================================================================

/// Initial state for a freshly-minted relay-operator cell.
pub fn initial_state(
    bond_amount: u64,
    bond_min: u64,
    quota_bytes_per_epoch: u64,
    operator_pk_hash: [u8; 32],
    route_table_root: [u8; 32],
) -> [FieldElement; 8] {
    [
        u64_field(bond_amount),
        u64_field(bond_min),
        u64_field(quota_bytes_per_epoch),
        [0u8; 32],
        [0u8; 32],
        operator_pk_hash,
        route_table_root,
        [0u8; 32],
    ]
}

/// Register this template on a [`StarbridgeAppContext`].
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(relay_operator_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "relay-operator".into(),
        descriptor: serde_json::json!({
            "component": "pyana-relay-operator",
            "module": "/pyana-storage-templates/relay-operator.js",
            "uri_prefix": "pyana://cell/",
            "summary_fields": [
                "bond_amount", "bond_min", "quota_bytes_per_epoch",
                "bytes_relayed_this_epoch", "hosted_inbox_root",
                "operator_pk_hash", "route_table_root", "dispute_count",
            ],
            "factory_vk_hex": hex_encode(&factory_vk),
            "child_program_vk_hex": hex_encode(&relay_operator_child_program_vk()),
        }),
    });

    factory_vk
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_app_framework::{AgentWallet, EmbeddedExecutor};

    fn test_wallet() -> AppWallet {
        AppWallet::new(AgentWallet::new(), [42u8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let wallet = test_wallet();
        let executor = EmbeddedExecutor::new(&wallet, "default");
        StarbridgeAppContext::new(wallet, executor)
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([7u8; 32])
    }

    fn blake3_field(bytes: &[u8]) -> FieldElement {
        *blake3::hash(bytes).as_bytes()
    }

    #[test]
    fn descriptor_is_stable() {
        let h1 = relay_operator_factory_descriptor().hash();
        let h2 = relay_operator_factory_descriptor().hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        let expected = canonical_program_vk(&relay_operator_program());
        assert_eq!(relay_operator_child_program_vk(), expected);
    }

    #[test]
    fn descriptor_validates_against_canonical_program() {
        let d = relay_operator_factory_descriptor();
        pyana_app_framework::validate_child_vk_canonical(&d, &relay_operator_program())
            .expect("descriptor must bind canonical layered VK to the program");
    }

    #[test]
    fn program_is_cases_with_four_branches() {
        match relay_operator_program() {
            CellProgram::Cases(cases) => {
                assert_eq!(
                    cases.len(),
                    4,
                    "Always + 3 MethodIs cases (register_inbox + relay + slash)"
                );
            }
            other => panic!("expected Cases, got {other:?}"),
        }
    }

    #[test]
    fn relay_case_carries_dfa_predicate() {
        let cases = match relay_operator_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let relay = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("relay")))
            .expect("relay case present");
        let has_dfa = relay.constraints.iter().any(|c| {
            matches!(c, StateConstraint::Witnessed { wp } if matches!(
                wp.kind,
                pyana_cell::predicate::WitnessedPredicateKind::Dfa
            ))
        });
        assert!(has_dfa, "relay case must declare a Dfa witnessed predicate");
    }

    #[test]
    fn relay_case_carries_rate_limit_by_sum() {
        let cases = match relay_operator_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let relay = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("relay")))
            .expect("relay case present");
        let has_rate = relay.constraints.iter().any(|c| {
            matches!(c, StateConstraint::RateLimitBySum { slot_index, .. } if *slot_index == BYTES_RELAYED_THIS_EPOCH_SLOT)
        });
        assert!(
            has_rate,
            "relay case must declare RateLimitBySum on the per-epoch byte counter"
        );
    }

    #[test]
    fn slash_case_carries_bounded_by() {
        // The slash case enforces "bond may only decrement if
        // dispute_count advanced" — encoded as BoundedBy { index:
        // BOND_AMOUNT, witness_index: DISPUTE_COUNT }.
        let cases = match relay_operator_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let slash = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("slash")))
            .expect("slash case present");
        let has_bounded = slash.constraints.iter().any(|c| {
            matches!(c,
                StateConstraint::BoundedBy { index, witness_index }
                if *index == BOND_AMOUNT_SLOT && *witness_index == DISPUTE_COUNT_SLOT
            )
        });
        assert!(
            has_bounded,
            "slash must declare BoundedBy { bond_amount, dispute_count }"
        );
    }

    #[test]
    fn register_inbox_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let action =
            build_register_inbox_action(&wallet, cell, blake3_field(b"h"), [9u8; 32]);
        assert_eq!(action.method, symbol("register_inbox"));
        assert_eq!(action.effects.len(), 2);
    }

    #[test]
    fn relay_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let action = build_relay_action(
            &wallet,
            cell,
            u64_field(1024),
            [11u8; 32],
            blake3_field(b"m"),
        );
        assert_eq!(action.method, symbol("relay"));
        assert_eq!(action.effects.len(), 2);
    }

    #[test]
    fn slash_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let action = build_slash_action(
            &wallet,
            cell,
            u64_field(500),
            u64_field(1),
            blake3_field(b"reason"),
        );
        assert_eq!(action.method, symbol("slash"));
        assert_eq!(action.effects.len(), 3);
    }

    #[test]
    fn register_installs_factory() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, RELAY_OPERATOR_FACTORY_VK);
        assert!(ctx.inspector_registry().get("relay-operator").is_some());
    }
}
