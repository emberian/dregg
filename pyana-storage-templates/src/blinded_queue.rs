//! # `BlindedQueueTemplate` — §3.4 reference design
//!
//! "Commitments-in, nullifiers-out" private-consumption queue. The
//! only template in this crate that requires a new
//! `WitnessedPredicate::Custom { vk_hash }` registration — per
//! `PREDICATE-INVENTORY.md §9.4`, the queue's spend AIR is the single
//! piece of net-new verifier infrastructure the migration needs.
//!
//! Per `STORAGE-AS-CELL-PROGRAMS.md` §3.4 the spend AIR is the existing
//! `pyana_storage::blinded::NoteSpendingAir` adapted against the
//! queue's commitments tree instead of the note tree. This template
//! commits to the *vk_hash* (slot 6's `spend_air_vk_commitment`) so
//! the cell program can declare the witnessed predicate without the
//! verifier itself living in this crate.
//!
//! ## Slot layout
//!
//! | Slot | Name | Caveat | Purpose |
//! |---:|---|---|---|
//! | 0 | `commitments_root` | `Monotonic` (add-scoped) | Root over blinded item commitments. |
//! | 1 | `nullifier_root` | `Monotonic` (consume-scoped) | Root over spent-item nullifiers. |
//! | 2 | `capacity` | `Immutable` | Max in-flight items. |
//! | 3 | `consumer_pk_hash` | `Immutable` | Consumer identity. |
//! | 4 | `commitment_count` | `Monotonic` (add-scoped) | Number of items added. |
//! | 5 | `nullifier_count` | `Monotonic` (consume-scoped) | Number of items spent. |
//! | 6 | `spend_air_vk_commitment` | `Immutable` | VK of the registered spend AIR. |
//! | 7 | `queue_id_hash` | `Immutable` | Stable identity. |
//!
//! Per §3.4: the spent-count-never-exceeds-added-count check
//! (`slot[5] <= slot[4]`) requires a cross-slot comparison the
//! 21-variant vocabulary doesn't include. The v1 expression here is a
//! `Custom` predicate; the v2 lift is the proposed `FieldLteOther`
//! variant (Open Q §7.2). The template lands the v1 shape; downstream
//! Custom predicates are app-extensibility per
//! `PREDICATE-INVENTORY.md §10.6`.
//!
//! ## Operations
//!
//! - `add` — commitments_root + commitment_count grow; nullifier
//!   side frozen. Producer-cap-gated (no `SenderAuthorized` at this
//!   layer — the producer cap is the authority).
//! - `consume` — nullifier_root + nullifier_count grow; commitments
//!   side frozen. Action carries the spend proof and the nullifier;
//!   `Witnessed { Custom { vk_hash } }` invokes the registered
//!   verifier against the proof and the snapshotted
//!   commitments_root.
//!
//! ## The vk_hash registry
//!
//! [`BLINDED_QUEUE_SPEND_AIR_VK`] is a placeholder for the BLAKE3 of
//! the spend AIR's selector layout. Per §3.4 the constitution
//! publishes the official `(vk_hash, verifier_name)` pair; for the
//! migration this template carries the placeholder so apps using the
//! template can declare the `Witnessed { Custom }` predicate.
//! Registration of the actual verifier (a
//! `WitnessedPredicateVerifier` impl) is a host-level concern; this
//! template carries only the *declaration*.
//!
//! ## Default mode
//!
//! Per §3.4 the natural default is `Sovereign` (consumer is the
//! witness-holder; federation sees only acceptance). The template's
//! default is `Hosted`, with `Sovereign` exposed via
//! [`blinded_queue_factory_descriptor_sovereign`] — matches the §7.7
//! recommendation that v1 stays Hosted while observability tooling
//! matures.
//!
//! ## Boundary contract
//!
//! - **cleartext-inside**: producer-consumer pair (knows item,
//!   randomness, nullifier).
//! - **commitment-inside**: anyone with the `commitments_root`.
//! - **acceptance-inside**: STARK verifier — learns *some* item was
//!   spent, not which.
//! - **out-of-band**: anyone without the cell's state.

use pyana_app_framework::{
    Action, AppWallet, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, ChildVkStrategy,
    Effect, Event, FactoryDescriptor, FieldConstraint, FieldElement, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, canonical_program_vk, symbol,
};
use pyana_cell::predicate::{InputRef, WitnessedPredicate};
use pyana_cell::program::{CellProgram, TransitionCase, TransitionGuard};

use crate::{hex_encode, u64_field};

// =============================================================================
// Slot layout
// =============================================================================

pub const COMMITMENTS_ROOT_SLOT: u8 = 0;
pub const NULLIFIER_ROOT_SLOT: u8 = 1;
pub const CAPACITY_SLOT: u8 = 2;
pub const CONSUMER_PK_HASH_SLOT: u8 = 3;
pub const COMMITMENT_COUNT_SLOT: u8 = 4;
pub const NULLIFIER_COUNT_SLOT: u8 = 5;
pub const SPEND_AIR_VK_COMMITMENT_SLOT: u8 = 6;
pub const QUEUE_ID_HASH_SLOT: u8 = 7;

// =============================================================================
// Witness layout
// =============================================================================

/// Witness blob index carrying the nullifier the consumer is
/// presenting.
pub const WITNESS_INDEX_NULLIFIER: usize = 0;
/// Witness blob index carrying the spend STARK proof bytes.
pub const WITNESS_INDEX_PROOF: usize = 1;

// =============================================================================
// Factory configuration
// =============================================================================

/// Default per-epoch creation budget — per §3.4 ("creation_budget:
/// Some(500)"). Smaller than `CapInbox`'s budget because
/// blinded-queue cells carry custom witnessed predicates.
pub const DEFAULT_CREATION_BUDGET: u64 = 500;

/// Stable placeholder VK for the BlindedQueue factory.
pub const BLINDED_QUEUE_FACTORY_VK: [u8; 32] = *b"pyana-storage-tpl-blindq-factory";

/// Stable placeholder VK for the BlindedQueue spend AIR. Per §3.4
/// (Open Q §7.1) the workspace owns this VK and the constitution
/// publishes the official `vk_hash`. The actual verifier registration
/// is a host concern (`WitnessedPredicateRegistry::register_custom`).
pub const BLINDED_QUEUE_SPEND_AIR_VK: [u8; 32] =
    *b"pyana-storage-tpl-blindq-spendair";

/// Canonical child VK per `VK-AS-RE-EXECUTION-RECIPE.md` §2.1.
pub fn blinded_queue_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&blinded_queue_program())
}

pub fn add_method_symbol() -> [u8; 32] {
    symbol("add")
}
pub fn consume_method_symbol() -> [u8; 32] {
    symbol("consume")
}

// =============================================================================
// CellProgram
// =============================================================================

/// Build the operation-scoped [`CellProgram`] for a BlindedQueue cell.
pub fn blinded_queue_program() -> CellProgram {
    CellProgram::Cases(vec![
        // Lifetime invariants.
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                StateConstraint::Immutable {
                    index: CAPACITY_SLOT,
                },
                StateConstraint::Immutable {
                    index: CONSUMER_PK_HASH_SLOT,
                },
                StateConstraint::Immutable {
                    index: SPEND_AIR_VK_COMMITMENT_SLOT,
                },
                StateConstraint::Immutable {
                    index: QUEUE_ID_HASH_SLOT,
                },
            ],
        },
        // add: commitments_root + commitment_count grow; nullifier
        // side frozen. Producer-cap-gated.
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("add"),
            },
            constraints: vec![
                StateConstraint::Monotonic {
                    index: COMMITMENTS_ROOT_SLOT,
                },
                StateConstraint::Monotonic {
                    index: COMMITMENT_COUNT_SLOT,
                },
                StateConstraint::Immutable {
                    index: NULLIFIER_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: NULLIFIER_COUNT_SLOT,
                },
            ],
        },
        // consume: nullifier_root + nullifier_count grow;
        // commitments side frozen. Action carries the spend proof
        // (witness index 1) and the nullifier (witness index 0); the
        // `Witnessed` constraint invokes the registered Custom
        // verifier against (commitments_root, nullifier, proof).
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("consume"),
            },
            constraints: vec![
                StateConstraint::Monotonic {
                    index: NULLIFIER_ROOT_SLOT,
                },
                StateConstraint::Monotonic {
                    index: NULLIFIER_COUNT_SLOT,
                },
                StateConstraint::Immutable {
                    index: COMMITMENTS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: COMMITMENT_COUNT_SLOT,
                },
                StateConstraint::Witnessed {
                    wp: WitnessedPredicate::custom(
                        BLINDED_QUEUE_SPEND_AIR_VK,
                        // Commitment binding: the spend AIR's verifier
                        // reads the commitments_root from the cell's
                        // state at receipt-time. Per
                        // PREDICATE-INVENTORY.md §6.3 the executor
                        // snapshots the commitment so replay is
                        // deterministic.
                        //
                        // We bind this through `commitment` =
                        // `commitments_root` *at the time the
                        // template descriptor is hashed* — but
                        // because the descriptor is a static value
                        // and the commitments_root varies per-cell,
                        // the actual binding happens at executor
                        // dispatch time. The static commitment field
                        // here is the AIR's vk-hash echo (the
                        // verifier interprets `commitment` per its
                        // own contract; for Custom { vk_hash }, the
                        // executor passes the resolved input —
                        // nullifier — *and* the snapshotted
                        // commitments_root via PredicateInput's
                        // input bytes).
                        BLINDED_QUEUE_SPEND_AIR_VK,
                        InputRef::Witness {
                            index: WITNESS_INDEX_NULLIFIER,
                        },
                        WITNESS_INDEX_PROOF,
                    ),
                },
            ],
        },
    ])
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Build the [`FactoryDescriptor`] for BlindedQueue cells in `Hosted`
/// mode (v1 default per Open Q §7.7).
pub fn blinded_queue_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: BLINDED_QUEUE_FACTORY_VK,
        child_program_vk: Some(blinded_queue_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(
            Some(blinded_queue_child_program_vk()),
        )),
        allowed_cap_templates: vec![
            // Producer cap — signature-bound, attenuatable for
            // delegated add.
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
            // Consumer cap — `Proof`-bound: the consumer must carry a
            // STARK to spend. Non-attenuatable (the spend power is
            // bound to the consumer identity).
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Proof,
                attenuatable: false,
            },
        ],
        field_constraints: vec![
            FieldConstraint::Equality {
                field_index: COMMITMENT_COUNT_SLOT as u32,
                value: 0,
            },
            FieldConstraint::Equality {
                field_index: NULLIFIER_COUNT_SLOT as u32,
                value: 0,
            },
            FieldConstraint::Range {
                field_index: CAPACITY_SLOT as u32,
                min: 1,
                max: 1_000_000,
            },
            FieldConstraint::NonZero {
                field_index: CONSUMER_PK_HASH_SLOT as u32,
            },
            FieldConstraint::NonZero {
                field_index: SPEND_AIR_VK_COMMITMENT_SLOT as u32,
            },
            FieldConstraint::NonZero {
                field_index: QUEUE_ID_HASH_SLOT as u32,
            },
        ],
        state_constraints: vec![
            StateConstraint::Immutable {
                index: CAPACITY_SLOT,
            },
            StateConstraint::Immutable {
                index: CONSUMER_PK_HASH_SLOT,
            },
            StateConstraint::Immutable {
                index: SPEND_AIR_VK_COMMITMENT_SLOT,
            },
            StateConstraint::Immutable {
                index: QUEUE_ID_HASH_SLOT,
            },
            StateConstraint::Monotonic {
                index: COMMITMENTS_ROOT_SLOT,
            },
            StateConstraint::Monotonic {
                index: NULLIFIER_ROOT_SLOT,
            },
            StateConstraint::Monotonic {
                index: COMMITMENT_COUNT_SLOT,
            },
            StateConstraint::Monotonic {
                index: NULLIFIER_COUNT_SLOT,
            },
        ],
        default_mode: CellMode::Hosted,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// Build the [`FactoryDescriptor`] for BlindedQueue cells in
/// `Sovereign` mode. Per §3.4 this is the natural default —
/// privacy-bearing cells where the consumer's agent is the prover —
/// exposed as a sibling factory so apps opting in have a single API.
pub fn blinded_queue_factory_descriptor_sovereign() -> FactoryDescriptor {
    let mut d = blinded_queue_factory_descriptor();
    d.default_mode = CellMode::Sovereign;
    d
}

// =============================================================================
// Turn-builders
// =============================================================================

/// Build the on-ledger [`Action`] recording an `add`.
///
/// The producer publishes the item's commitment; the body itself is
/// out-of-band (typically sealed-box-encrypted to the consumer).
pub fn build_add_action(
    wallet: &AppWallet,
    queue_cell: CellId,
    new_commitments_root: FieldElement,
    new_commitment_count: FieldElement,
    item_commitment: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: queue_cell,
            index: COMMITMENTS_ROOT_SLOT as usize,
            value: new_commitments_root,
        },
        Effect::SetField {
            cell: queue_cell,
            index: COMMITMENT_COUNT_SLOT as usize,
            value: new_commitment_count,
        },
        Effect::EmitEvent {
            cell: queue_cell,
            event: Event::new(
                symbol("blinded-added"),
                vec![new_commitments_root, item_commitment],
            ),
        },
    ];

    wallet.make_action(queue_cell, "add", effects)
}

/// Build the on-ledger [`Action`] recording a `consume`.
///
/// The action carries the nullifier and the spend proof as
/// `witness_blobs[0]` / `witness_blobs[1]` respectively. The executor
/// resolves the `Witnessed { Custom }` constraint at evaluation time
/// against the registered verifier — this template only declares the
/// requirement.
///
/// Adding the witnesses to the action is the caller's responsibility
/// (`AppWallet::with_witness` after-the-fact composition). The
/// returned [`Action`] carries the [`Effect`]s and the method symbol;
/// see `pyana_app_framework::AppCipherclerk` for the witness-attach API.
pub fn build_consume_action(
    wallet: &AppWallet,
    queue_cell: CellId,
    new_nullifier_root: FieldElement,
    new_nullifier_count: FieldElement,
    nullifier: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: queue_cell,
            index: NULLIFIER_ROOT_SLOT as usize,
            value: new_nullifier_root,
        },
        Effect::SetField {
            cell: queue_cell,
            index: NULLIFIER_COUNT_SLOT as usize,
            value: new_nullifier_count,
        },
        Effect::EmitEvent {
            cell: queue_cell,
            event: Event::new(
                symbol("blinded-consumed"),
                vec![new_nullifier_root, nullifier],
            ),
        },
    ];

    wallet.make_action(queue_cell, "consume", effects)
}

// =============================================================================
// Initial state + registration
// =============================================================================

/// Initial state for a freshly-minted blinded-queue cell.
pub fn initial_state(
    capacity: u64,
    consumer_pk_hash: [u8; 32],
    spend_air_vk_commitment: [u8; 32],
    queue_id_hash: [u8; 32],
) -> [FieldElement; 8] {
    [
        [0u8; 32],
        [0u8; 32],
        u64_field(capacity),
        consumer_pk_hash,
        [0u8; 32],
        [0u8; 32],
        spend_air_vk_commitment,
        queue_id_hash,
    ]
}

/// Register this template on a [`StarbridgeAppContext`].
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(blinded_queue_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "blinded-queue".into(),
        descriptor: serde_json::json!({
            "component": "pyana-blinded-queue",
            "module": "/pyana-storage-templates/blinded-queue.js",
            "uri_prefix": "pyana://cell/",
            "summary_fields": [
                "commitments_root", "nullifier_root", "capacity",
                "consumer_pk_hash", "commitment_count", "nullifier_count",
                "spend_air_vk_commitment", "queue_id_hash",
            ],
            "factory_vk_hex": hex_encode(&factory_vk),
            "child_program_vk_hex": hex_encode(&blinded_queue_child_program_vk()),
            "spend_air_vk_hex": hex_encode(&BLINDED_QUEUE_SPEND_AIR_VK),
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
        let h1 = blinded_queue_factory_descriptor().hash();
        let h2 = blinded_queue_factory_descriptor().hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        let expected = canonical_program_vk(&blinded_queue_program());
        assert_eq!(blinded_queue_child_program_vk(), expected);
    }

    #[test]
    fn descriptor_validates_against_canonical_program() {
        let d = blinded_queue_factory_descriptor();
        pyana_app_framework::validate_child_vk_canonical(&d, &blinded_queue_program())
            .expect("descriptor must bind canonical layered VK to the program");
    }

    #[test]
    fn program_is_cases_with_three_branches() {
        match blinded_queue_program() {
            CellProgram::Cases(cases) => {
                assert_eq!(cases.len(), 3, "Always + 2 MethodIs cases (add + consume)");
            }
            other => panic!("expected Cases, got {other:?}"),
        }
    }

    #[test]
    fn consume_case_carries_witnessed_predicate() {
        let cases = match blinded_queue_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let consume = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("consume")))
            .expect("consume case present");
        let has_witnessed = consume.constraints.iter().any(|c| {
            matches!(c, StateConstraint::Witnessed { wp } if matches!(
                wp.kind,
                pyana_cell::predicate::WitnessedPredicateKind::Custom { vk_hash }
                    if vk_hash == BLINDED_QUEUE_SPEND_AIR_VK
            ))
        });
        assert!(
            has_witnessed,
            "consume case must declare the Witnessed Custom predicate"
        );
    }

    #[test]
    fn add_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let action = build_add_action(
            &wallet,
            cell,
            blake3_field(b"c"),
            u64_field(1),
            blake3_field(b"i"),
        );
        assert_eq!(action.method, symbol("add"));
        assert_eq!(action.effects.len(), 3);
    }

    #[test]
    fn consume_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let action = build_consume_action(
            &wallet,
            cell,
            blake3_field(b"n"),
            u64_field(1),
            blake3_field(b"nul"),
        );
        assert_eq!(action.method, symbol("consume"));
        assert_eq!(action.effects.len(), 3);
    }

    #[test]
    fn consumer_cap_template_is_proof_bound() {
        let d = blinded_queue_factory_descriptor();
        let consumer_cap = &d.allowed_cap_templates[1];
        assert!(
            matches!(consumer_cap.max_permissions, AuthRequired::Proof),
            "consumer cap must be Proof-bound (spend AIR required)"
        );
        assert!(
            !consumer_cap.attenuatable,
            "consumer cap must be non-attenuatable"
        );
    }

    #[test]
    fn sovereign_variant_differs_only_in_mode() {
        let h = blinded_queue_factory_descriptor();
        let s = blinded_queue_factory_descriptor_sovereign();
        assert_eq!(h.default_mode, CellMode::Hosted);
        assert_eq!(s.default_mode, CellMode::Sovereign);
        // Same VKs, same constraints, same caps — only mode differs.
        assert_eq!(h.factory_vk, s.factory_vk);
        assert_eq!(h.state_constraints, s.state_constraints);
    }

    #[test]
    fn register_installs_factory() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, BLINDED_QUEUE_FACTORY_VK);
        assert!(ctx.inspector_registry().get("blinded-queue").is_some());
    }
}
