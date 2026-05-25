//! # `PubSubTopicTemplate` — §3.3 reference design
//!
//! Append-only log with per-subscriber cursors. One publisher, many
//! subscribers; subscribers commit cursors to a Merkle root and
//! advance them as they read events Merkle-proven against the
//! `event_root`. Per `STORAGE-AS-CELL-PROGRAMS.md` §3.3.
//!
//! ## Slot layout
//!
//! | Slot | Name | Caveat | Purpose |
//! |---:|---|---|---|
//! | 0 | `head_seq` | `MonotonicSequence` (publish-scoped) | Publisher's monotonic seq counter. |
//! | 1 | `subscriber_cursors_root` | `Monotonic` (subscribe-scoped) | Merkle root over `(subscriber_pk, last_read_seq)` pairs. |
//! | 2 | `publisher_pk_hash` | `Immutable` | Publisher identity. |
//! | 3 | `subscriber_set_root` | `Monotonic` | Optional authorized-subscriber roll. |
//! | 4 | `topic_id_hash` | `Immutable` | Stable topic identity. |
//! | 5 | `event_root` | `Monotonic` (publish-scoped) | Merkle root over published events. |
//! | 6 | `topic_filter_root` | `Immutable` | DFA route table commitment (optional, bound at creation). |
//! | 7 | `dedup_root` | `Monotonic` (publish-scoped) | Merkle root of content hashes for idempotent publish. |
//!
//! ## Operations
//!
//! - `publish` — head + 1; event_root grows; dedup_root grows.
//!   Cursors/identities/sets frozen. Sender must be the publisher
//!   (`SenderAuthorized` against slot 2's pubkey hash).
//! - `subscribe` — subscriber_cursors_root advances; everything else
//!   frozen. When `subscriber_set_root` is set, sender must be in it.
//! - `grant_subscriber` — subscriber_set_root advances; everything
//!   else frozen.
//!
//! ## What this replaces
//!
//! - `pyana_storage::pubsub::PubSubTopic` operator-process state.
//! - `pyana_storage::dedup::DeduplicationFilter` — folds into slot 7's
//!   monotonic-growing Merkle root. The contains/insert pattern
//!   becomes a structural check by the consumer (Merkle non-membership
//!   on publish to reject re-publish at the same content hash).
//!
//! ## Boundary contract
//!
//! - **cleartext-inside**: federation hosting the cell.
//! - **commitment-inside**: anyone with `topic_id_hash` (knows the
//!   topic exists, can verify events against `event_root`).
//! - **acceptance-inside**: STARK verifiers of any topic-filter DFA
//!   classification proof.
//! - **out-of-band**: the rest.

use pyana_app_framework::{
    Action, AppWallet, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, ChildVkStrategy,
    Effect, Event, FactoryDescriptor, FieldConstraint, FieldElement, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, canonical_program_vk, symbol,
};
use pyana_cell::program::{AuthorizedSet, CellProgram, TransitionCase, TransitionGuard};

use crate::hex_encode;

// =============================================================================
// Slot layout
// =============================================================================

pub const HEAD_SEQ_SLOT: u8 = 0;
pub const SUBSCRIBER_CURSORS_ROOT_SLOT: u8 = 1;
pub const PUBLISHER_PK_HASH_SLOT: u8 = 2;
pub const SUBSCRIBER_SET_ROOT_SLOT: u8 = 3;
pub const TOPIC_ID_HASH_SLOT: u8 = 4;
pub const EVENT_ROOT_SLOT: u8 = 5;
pub const TOPIC_FILTER_ROOT_SLOT: u8 = 6;
pub const DEDUP_ROOT_SLOT: u8 = 7;

// =============================================================================
// Factory configuration
// =============================================================================

/// Default per-epoch creation budget.
pub const DEFAULT_CREATION_BUDGET: u64 = 1_000;

/// Stable placeholder VK for the PubSubTopic factory.
pub const PUBSUB_TOPIC_FACTORY_VK: [u8; 32] = *b"pyana-storage-tpl-pubsub-factory";

/// Canonical child VK per `VK-AS-RE-EXECUTION-RECIPE.md` §2.1.
pub fn pubsub_topic_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&pubsub_topic_program())
}

pub fn publish_method_symbol() -> [u8; 32] {
    symbol("publish")
}
pub fn subscribe_method_symbol() -> [u8; 32] {
    symbol("subscribe")
}
pub fn grant_subscriber_method_symbol() -> [u8; 32] {
    symbol("grant_subscriber")
}

// =============================================================================
// CellProgram
// =============================================================================

/// Build the operation-scoped [`CellProgram`] for a PubSubTopic cell.
pub fn pubsub_topic_program() -> CellProgram {
    CellProgram::Cases(vec![
        // Lifetime invariants.
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                StateConstraint::Immutable {
                    index: PUBLISHER_PK_HASH_SLOT,
                },
                StateConstraint::Immutable {
                    index: TOPIC_ID_HASH_SLOT,
                },
                StateConstraint::Immutable {
                    index: TOPIC_FILTER_ROOT_SLOT,
                },
            ],
        },
        // publish: head + 1; event_root + dedup_root grow; cursors,
        // identities, sets frozen. Publisher-only.
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("publish"),
            },
            constraints: vec![
                StateConstraint::MonotonicSequence {
                    seq_index: HEAD_SEQ_SLOT,
                },
                StateConstraint::Monotonic {
                    index: EVENT_ROOT_SLOT,
                },
                StateConstraint::Monotonic {
                    index: DEDUP_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: SUBSCRIBER_CURSORS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: SUBSCRIBER_SET_ROOT_SLOT,
                },
                // Per §3.3: the publisher is authorized as
                // SenderAuthorized against the slot-2 pubkey-hash.
                // Encoded as a single-leaf Merkle root (the slot
                // stores the publisher's pk hash directly, so the
                // PublicRoot variant collapses to an equality check
                // at the executor's evaluator).
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: PUBLISHER_PK_HASH_SLOT,
                    },
                },
            ],
        },
        // subscribe: subscriber_cursors_root advances; everything else
        // frozen. When subscriber_set_root is non-zero, sender must
        // be in it (caller layers SenderAuthorized via the gated
        // subscribe variant; the unrestricted variant accepts all).
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("subscribe"),
            },
            constraints: vec![
                StateConstraint::Monotonic {
                    index: SUBSCRIBER_CURSORS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: HEAD_SEQ_SLOT,
                },
                StateConstraint::Immutable {
                    index: SUBSCRIBER_SET_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: EVENT_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: DEDUP_ROOT_SLOT,
                },
            ],
        },
        // grant_subscriber: subscriber_set_root grows; everything
        // else frozen. Publisher-only (owns the topic's roll).
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("grant_subscriber"),
            },
            constraints: vec![
                StateConstraint::Monotonic {
                    index: SUBSCRIBER_SET_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: HEAD_SEQ_SLOT,
                },
                StateConstraint::Immutable {
                    index: SUBSCRIBER_CURSORS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: EVENT_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: DEDUP_ROOT_SLOT,
                },
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: PUBLISHER_PK_HASH_SLOT,
                    },
                },
            ],
        },
    ])
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Build the [`FactoryDescriptor`] for PubSubTopic cells.
pub fn pubsub_topic_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: PUBSUB_TOPIC_FACTORY_VK,
        child_program_vk: Some(pubsub_topic_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(
            Some(pubsub_topic_child_program_vk()),
        )),
        allowed_cap_templates: vec![
            // Publisher cap — exclusive: only the topic creator
            // holds this. Non-attenuatable (no sub-delegation).
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: false,
            },
            // Subscriber cap — attenuatable so members can re-grant
            // restricted views to peers (per `ResourcePrefix` caveats).
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
        ],
        field_constraints: vec![
            FieldConstraint::Equality {
                field_index: HEAD_SEQ_SLOT as u32,
                value: 0,
            },
            FieldConstraint::NonZero {
                field_index: PUBLISHER_PK_HASH_SLOT as u32,
            },
            FieldConstraint::NonZero {
                field_index: TOPIC_ID_HASH_SLOT as u32,
            },
        ],
        state_constraints: vec![
            StateConstraint::Immutable {
                index: PUBLISHER_PK_HASH_SLOT,
            },
            StateConstraint::Immutable {
                index: TOPIC_ID_HASH_SLOT,
            },
            StateConstraint::Immutable {
                index: TOPIC_FILTER_ROOT_SLOT,
            },
            StateConstraint::Monotonic {
                index: HEAD_SEQ_SLOT,
            },
            StateConstraint::Monotonic {
                index: SUBSCRIBER_CURSORS_ROOT_SLOT,
            },
            StateConstraint::Monotonic {
                index: SUBSCRIBER_SET_ROOT_SLOT,
            },
            StateConstraint::Monotonic {
                index: EVENT_ROOT_SLOT,
            },
            StateConstraint::Monotonic {
                index: DEDUP_ROOT_SLOT,
            },
        ],
        default_mode: CellMode::Hosted,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

// =============================================================================
// Turn-builders
// =============================================================================

/// Build the on-ledger [`Action`] recording a `publish`.
pub fn build_publish_action(
    wallet: &AppWallet,
    topic_cell: CellId,
    new_head: FieldElement,
    new_event_root: FieldElement,
    new_dedup_root: FieldElement,
    payload_commitment: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: topic_cell,
            index: HEAD_SEQ_SLOT as usize,
            value: new_head,
        },
        Effect::SetField {
            cell: topic_cell,
            index: EVENT_ROOT_SLOT as usize,
            value: new_event_root,
        },
        Effect::SetField {
            cell: topic_cell,
            index: DEDUP_ROOT_SLOT as usize,
            value: new_dedup_root,
        },
        Effect::EmitEvent {
            cell: topic_cell,
            event: Event::new(
                symbol("topic-published"),
                vec![new_head, new_event_root, payload_commitment],
            ),
        },
    ];

    wallet.make_action(topic_cell, "publish", effects)
}

/// Build the on-ledger [`Action`] recording a `subscribe` (cursor
/// advance).
pub fn build_subscribe_action(
    wallet: &AppWallet,
    topic_cell: CellId,
    new_subscriber_cursors_root: FieldElement,
    subscriber_pk: [u8; 32],
    new_cursor: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: topic_cell,
            index: SUBSCRIBER_CURSORS_ROOT_SLOT as usize,
            value: new_subscriber_cursors_root,
        },
        Effect::EmitEvent {
            cell: topic_cell,
            event: Event::new(
                symbol("topic-subscribed"),
                vec![new_subscriber_cursors_root, subscriber_pk, new_cursor],
            ),
        },
    ];

    wallet.make_action(topic_cell, "subscribe", effects)
}

/// Build the on-ledger [`Action`] adding a subscriber to the
/// authorized-subscribers set.
pub fn build_grant_subscriber_action(
    wallet: &AppWallet,
    topic_cell: CellId,
    new_subscriber_set_root: FieldElement,
    new_subscriber_pk: [u8; 32],
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: topic_cell,
            index: SUBSCRIBER_SET_ROOT_SLOT as usize,
            value: new_subscriber_set_root,
        },
        Effect::EmitEvent {
            cell: topic_cell,
            event: Event::new(
                symbol("topic-subscriber-granted"),
                vec![new_subscriber_set_root, new_subscriber_pk],
            ),
        },
    ];

    wallet.make_action(topic_cell, "grant_subscriber", effects)
}

// =============================================================================
// Initial state + registration
// =============================================================================

/// Initial state for a freshly-minted topic cell.
pub fn initial_state(
    publisher_pk_hash: [u8; 32],
    topic_id_hash: [u8; 32],
    topic_filter_root: [u8; 32],
) -> [FieldElement; 8] {
    [
        [0u8; 32],
        [0u8; 32],
        publisher_pk_hash,
        [0u8; 32],
        topic_id_hash,
        [0u8; 32],
        topic_filter_root,
        [0u8; 32],
    ]
}

/// Register this template on a [`StarbridgeAppContext`].
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(pubsub_topic_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "pubsub-topic".into(),
        descriptor: serde_json::json!({
            "component": "pyana-pubsub-topic",
            "module": "/pyana-storage-templates/pubsub-topic.js",
            "uri_prefix": "pyana://cell/",
            "summary_fields": [
                "head_seq", "subscriber_cursors_root", "publisher_pk_hash",
                "subscriber_set_root", "topic_id_hash", "event_root",
                "topic_filter_root", "dedup_root",
            ],
            "factory_vk_hex": hex_encode(&factory_vk),
            "child_program_vk_hex": hex_encode(&pubsub_topic_child_program_vk()),
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
    use crate::u64_field;
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
        let h1 = pubsub_topic_factory_descriptor().hash();
        let h2 = pubsub_topic_factory_descriptor().hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        let expected = canonical_program_vk(&pubsub_topic_program());
        assert_eq!(pubsub_topic_child_program_vk(), expected);
    }

    #[test]
    fn descriptor_validates_against_canonical_program() {
        let d = pubsub_topic_factory_descriptor();
        pyana_app_framework::validate_child_vk_canonical(&d, &pubsub_topic_program())
            .expect("descriptor must bind canonical layered VK to the program");
    }

    #[test]
    fn program_is_cases_with_four_branches() {
        match pubsub_topic_program() {
            CellProgram::Cases(cases) => {
                assert_eq!(cases.len(), 4, "Always + 3 MethodIs cases");
            }
            other => panic!("expected Cases, got {other:?}"),
        }
    }

    #[test]
    fn publish_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let action = build_publish_action(
            &wallet,
            cell,
            u64_field(1),
            blake3_field(b"e"),
            blake3_field(b"d"),
            blake3_field(b"p"),
        );
        assert_eq!(action.method, symbol("publish"));
        assert_eq!(action.effects.len(), 4);
    }

    #[test]
    fn subscribe_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let action = build_subscribe_action(
            &wallet,
            cell,
            blake3_field(b"c"),
            [9u8; 32],
            u64_field(1),
        );
        assert_eq!(action.method, symbol("subscribe"));
        assert_eq!(action.effects.len(), 2);
    }

    #[test]
    fn grant_subscriber_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let action =
            build_grant_subscriber_action(&wallet, cell, blake3_field(b"s"), [11u8; 32]);
        assert_eq!(action.method, symbol("grant_subscriber"));
        assert_eq!(action.effects.len(), 2);
    }

    #[test]
    fn register_installs_factory() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, PUBSUB_TOPIC_FACTORY_VK);
        assert!(ctx.inspector_registry().get("pubsub-topic").is_some());
    }
}
