//! # `ProgrammableQueueTemplate` — §3.2 reference design
//!
//! The canonical mapping per `STORAGE-AS-CELL-PROGRAMS.md` §3.2. Where
//! [`crate::cap_inbox`] is a **fixed-shape** inbox queue, the
//! programmable-queue is **parameterized by the factory builder**:
//! the caller supplies a [`Vec<StateConstraint>`] menu drawn from the
//! lifted 21-variant slot-caveat vocabulary, and the template wires
//! them into operation-scoped cases.
//!
//! The §3.2 design calls this the "proof of pattern" because the
//! storage-side `QueueConstraint` vocabulary
//! (`storage/src/programmable.rs:78-103`) is already (Phase 1) aliased
//! to `pyana_cell::program::StateConstraint`. The migration finishes
//! the collapse: the storage-side evaluator and the cell-side
//! evaluator are the same function, called from the executor.
//!
//! ## Slot layout
//!
//! | Slot | Name | Caveat | Purpose |
//! |---:|---|---|---|
//! | 0 | `head_seq` | `MonotonicSequence` (enqueue-scoped) | Producer cursor. |
//! | 1 | `tail_seq` | `MonotonicSequence` (dequeue-scoped) | Consumer cursor. |
//! | 2 | `capacity` | `Immutable` | Max in-flight. |
//! | 3 | `program_vk` | `Immutable` | Hash of the cell-program's `state_constraints`. Bound at creation. |
//! | 4 | `owner_pk_hash` | `Immutable` | Owner identity. |
//! | 5 | `sender_set_root` | `Monotonic` | Authorized senders (Merkle or BlindedSet). |
//! | 6 | `content_pattern_root` | `Monotonic` | DFA route table commitment (optional). |
//! | 7 | `ring_root` | `Monotonic` | Message ring root. |
//!
//! ## Operations
//!
//! - `enqueue` — head + 1; ring_root grows; sender_set/owner/capacity
//!   frozen. Caller-supplied `extra_constraints` (e.g. `RateLimit`,
//!   `TemporalGate`, `Witnessed { Dfa }` for content-pattern) attach
//!   to this case.
//! - `dequeue` — tail + 1; head/ring_root frozen.
//! - `grant_sender` — sender_set_root advances; everything else
//!   frozen.
//!
//! ## Parameterization
//!
//! [`ProgrammableQueueConfig`] holds the per-instance constraint
//! menu. The factory hashes the menu into `child_vk_strategy: Derived
//! { param_hash }` so each constraint configuration produces a unique
//! child VK — observers can extract the `param_hash` from the cell's
//! `Provenance` and reproduce the exact constraint set.
//!
//! ## What this replaces
//!
//! - `pyana_storage::programmable::{QueueProgram, QueueConstraint,
//!   ValidationContext, evaluate_constraint}` — the entire
//!   storage-side evaluator. Per §3.2, the constraint vocabulary is
//!   already aliased; what survives migration is the slot data
//!   structure (`MerkleQueue` for the ring) — the predicate logic
//!   moves to the executor.
//! - `pyana_storage::programmable::QueueFactory` — subsumed by
//!   [`FactoryDescriptor`].
//! - `app-framework::queue_endpoint` HTTP shim's enforcement loop.
//!
//! ## Boundary contract
//!
//! Identical to [`crate::cap_inbox`] (cleartext-inside the
//! federation; commitment-inside `public_field_view` holders;
//! acceptance-inside STARK verifiers of any attached
//! `WitnessedPredicate`; out-of-band the rest). The
//! `content_pattern_root` (slot 6) adds an extra layer:
//! cleartext-inside the route-table author, commitment-inside anyone
//! holding only the root.

use pyana_app_framework::{
    Action, AppWallet, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, ChildVkStrategy,
    Effect, Event, FactoryDescriptor, FieldConstraint, FieldElement, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, canonical_program_vk, symbol,
};
use pyana_cell::program::{AuthorizedSet, CellProgram, TransitionCase, TransitionGuard};

use crate::{hex_encode, u64_field};

// =============================================================================
// Slot layout
// =============================================================================

/// Slot 0 — `head_seq`. Producer cursor.
pub const HEAD_SEQ_SLOT: u8 = 0;
/// Slot 1 — `tail_seq`. Consumer cursor.
pub const TAIL_SEQ_SLOT: u8 = 1;
/// Slot 2 — `capacity`. Immutable.
pub const CAPACITY_SLOT: u8 = 2;
/// Slot 3 — `program_vk`. Immutable. Hash of the cell-program's
/// `state_constraints` (i.e., the param_hash for `ChildVkStrategy::Derived`).
pub const PROGRAM_VK_SLOT: u8 = 3;
/// Slot 4 — `owner_pk_hash`. Immutable.
pub const OWNER_PK_HASH_SLOT: u8 = 4;
/// Slot 5 — `sender_set_root`. Authorized senders.
pub const SENDER_SET_ROOT_SLOT: u8 = 5;
/// Slot 6 — `content_pattern_root`. DFA route-table commitment (optional).
pub const CONTENT_PATTERN_ROOT_SLOT: u8 = 6;
/// Slot 7 — `ring_root`. Message ring root.
pub const RING_ROOT_SLOT: u8 = 7;

// =============================================================================
// Factory configuration
// =============================================================================

/// Default per-epoch creation budget. Per §3.2 ("creation_budget:
/// Some(1_000)") — smaller than `CapInbox`'s budget because
/// programmable queues are more powerful (constraint-set bearing).
pub const DEFAULT_CREATION_BUDGET: u64 = 1_000;

/// Stable placeholder VK for the ProgrammableQueue factory.
pub const PROGRAMMABLE_QUEUE_FACTORY_VK: [u8; 32] = *b"pyana-storage-tpl-pqueue-factory";

/// Parameterization of a ProgrammableQueue instance: the extra
/// per-operation constraints to attach beyond the base sequencing
/// and immutability invariants.
///
/// Per §3.2 the most common shapes are:
///   - a *work-queue* (`SenderAuthorized` + `RateLimit` +
///     `TemporalGate` + optional `Witnessed { Dfa }` for content).
///   - an *auction-bid queue* (`StrictMonotonic` on a bid slot +
///     `FieldGte` on a min-bid floor + `FieldGteHeight` on
///     valid_until).
///
/// The default ([`Self::work_queue_default`]) is the work-queue shape.
#[derive(Clone, Debug, Default)]
pub struct ProgrammableQueueConfig {
    /// Extra constraints attached to the `enqueue` case (e.g.
    /// `RateLimit`, `TemporalGate`, `Witnessed { Dfa }`).
    pub enqueue_extras: Vec<StateConstraint>,
    /// Extra constraints attached to the `dequeue` case (e.g.
    /// `PreimageGate`).
    pub dequeue_extras: Vec<StateConstraint>,
    /// Initial capacity. Bounds `field_constraints` Range.
    pub capacity: u64,
}

impl ProgrammableQueueConfig {
    /// The canonical "work-queue" shape per §3.2: senders authorized
    /// by Merkle root in slot 5, rate-limited at 10/epoch with
    /// 100-block epochs. No extra dequeue constraints.
    pub fn work_queue_default(capacity: u64) -> Self {
        Self {
            enqueue_extras: vec![
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: SENDER_SET_ROOT_SLOT,
                    },
                },
                StateConstraint::RateLimit {
                    max_per_epoch: 10,
                    epoch_duration: 100,
                },
            ],
            dequeue_extras: vec![],
            capacity,
        }
    }

    /// Compute the param_hash binding this config to a derived child
    /// VK. The hash domain-separates `"pyana-pqueue-config"` to
    /// prevent collision with other parameterization protocols.
    pub fn param_hash(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"pyana-pqueue-config-v1");
        h.update(&self.capacity.to_be_bytes());
        h.update(&(self.enqueue_extras.len() as u32).to_be_bytes());
        for c in &self.enqueue_extras {
            let bytes = serde_json::to_vec(c).unwrap_or_default();
            h.update(&(bytes.len() as u32).to_be_bytes());
            h.update(&bytes);
        }
        h.update(&(self.dequeue_extras.len() as u32).to_be_bytes());
        for c in &self.dequeue_extras {
            let bytes = serde_json::to_vec(c).unwrap_or_default();
            h.update(&(bytes.len() as u32).to_be_bytes());
            h.update(&bytes);
        }
        *h.finalize().as_bytes()
    }
}

/// Method symbol for `enqueue`.
pub fn enqueue_method_symbol() -> [u8; 32] {
    symbol("enqueue")
}
/// Method symbol for `dequeue`.
pub fn dequeue_method_symbol() -> [u8; 32] {
    symbol("dequeue")
}
/// Method symbol for `grant_sender`.
pub fn grant_sender_method_symbol() -> [u8; 32] {
    symbol("grant_sender")
}

// =============================================================================
// CellProgram
// =============================================================================

/// Build the [`CellProgram`] for the default work-queue configuration.
/// For non-default configurations, use [`programmable_queue_program_with`].
pub fn programmable_queue_program() -> CellProgram {
    programmable_queue_program_with(&ProgrammableQueueConfig::work_queue_default(1_000))
}

/// Build the [`CellProgram`] for a ProgrammableQueue cell with the
/// given configuration. Per Cav-Codex Block 4 default-deny applies.
pub fn programmable_queue_program_with(cfg: &ProgrammableQueueConfig) -> CellProgram {
    let mut enqueue = vec![
        StateConstraint::MonotonicSequence {
            seq_index: HEAD_SEQ_SLOT,
        },
        StateConstraint::Immutable {
            index: TAIL_SEQ_SLOT,
        },
        StateConstraint::Immutable {
            index: SENDER_SET_ROOT_SLOT,
        },
        StateConstraint::Immutable {
            index: CONTENT_PATTERN_ROOT_SLOT,
        },
        StateConstraint::Monotonic {
            index: RING_ROOT_SLOT,
        },
    ];
    enqueue.extend(cfg.enqueue_extras.iter().cloned());

    let mut dequeue = vec![
        StateConstraint::MonotonicSequence {
            seq_index: TAIL_SEQ_SLOT,
        },
        StateConstraint::Immutable {
            index: HEAD_SEQ_SLOT,
        },
        StateConstraint::Immutable {
            index: RING_ROOT_SLOT,
        },
        StateConstraint::Immutable {
            index: SENDER_SET_ROOT_SLOT,
        },
        StateConstraint::Immutable {
            index: CONTENT_PATTERN_ROOT_SLOT,
        },
    ];
    dequeue.extend(cfg.dequeue_extras.iter().cloned());

    CellProgram::Cases(vec![
        // Lifetime invariants.
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                StateConstraint::Immutable {
                    index: CAPACITY_SLOT,
                },
                StateConstraint::Immutable {
                    index: PROGRAM_VK_SLOT,
                },
                StateConstraint::Immutable {
                    index: OWNER_PK_HASH_SLOT,
                },
            ],
        },
        // enqueue.
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("enqueue"),
            },
            constraints: enqueue,
        },
        // dequeue.
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("dequeue"),
            },
            constraints: dequeue,
        },
        // grant_sender — sender_set_root grows; everything else frozen.
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("grant_sender"),
            },
            constraints: vec![
                StateConstraint::Monotonic {
                    index: SENDER_SET_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: HEAD_SEQ_SLOT,
                },
                StateConstraint::Immutable {
                    index: TAIL_SEQ_SLOT,
                },
                StateConstraint::Immutable {
                    index: CONTENT_PATTERN_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: RING_ROOT_SLOT,
                },
            ],
        },
    ])
}

/// Compute the canonical child program VK for the default work-queue.
pub fn programmable_queue_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&programmable_queue_program())
}

/// Compute the canonical child program VK for the parameterized
/// configuration. Per `VK-AS-RE-EXECUTION-RECIPE.md` §2.1 the VK is
/// the layered hash over the actual `CellProgram`, so different
/// configurations naturally derive different VKs.
pub fn programmable_queue_child_program_vk_with(cfg: &ProgrammableQueueConfig) -> [u8; 32] {
    canonical_program_vk(&programmable_queue_program_with(cfg))
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Build the default-configuration [`FactoryDescriptor`]
/// (work-queue, capacity 1000). For non-default configurations use
/// [`programmable_queue_factory_descriptor_with`].
pub fn programmable_queue_factory_descriptor() -> FactoryDescriptor {
    programmable_queue_factory_descriptor_with(&ProgrammableQueueConfig::work_queue_default(1_000))
}

/// Build a [`FactoryDescriptor`] for the parameterized configuration.
/// Uses `ChildVkStrategy::Derived { base_vk }` so the per-cell child
/// VK is reproducible from the descriptor + the per-cell `param_hash`
/// recorded in `Provenance`.
pub fn programmable_queue_factory_descriptor_with(
    cfg: &ProgrammableQueueConfig,
) -> FactoryDescriptor {
    let child_vk = programmable_queue_child_program_vk_with(cfg);
    FactoryDescriptor {
        factory_vk: PROGRAMMABLE_QUEUE_FACTORY_VK,
        child_program_vk: Some(child_vk),
        child_vk_strategy: Some(ChildVkStrategy::Derived {
            base_vk: PROGRAMMABLE_QUEUE_FACTORY_VK,
        }),
        allowed_cap_templates: vec![
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
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
            FieldConstraint::Equality {
                field_index: TAIL_SEQ_SLOT as u32,
                value: 0,
            },
            FieldConstraint::Range {
                field_index: CAPACITY_SLOT as u32,
                min: 1,
                max: cfg.capacity,
            },
            FieldConstraint::NonZero {
                field_index: PROGRAM_VK_SLOT as u32,
            },
            FieldConstraint::NonZero {
                field_index: OWNER_PK_HASH_SLOT as u32,
            },
        ],
        state_constraints: vec![
            StateConstraint::Immutable {
                index: CAPACITY_SLOT,
            },
            StateConstraint::Immutable {
                index: PROGRAM_VK_SLOT,
            },
            StateConstraint::Immutable {
                index: OWNER_PK_HASH_SLOT,
            },
            StateConstraint::Monotonic {
                index: HEAD_SEQ_SLOT,
            },
            StateConstraint::Monotonic {
                index: TAIL_SEQ_SLOT,
            },
            StateConstraint::Monotonic {
                index: SENDER_SET_ROOT_SLOT,
            },
            StateConstraint::Monotonic {
                index: RING_ROOT_SLOT,
            },
        ],
        default_mode: CellMode::Hosted,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

// =============================================================================
// Turn-builders
// =============================================================================

/// Build the on-ledger [`Action`] recording an `enqueue`.
pub fn build_enqueue_action(
    wallet: &AppWallet,
    queue_cell: CellId,
    new_head: FieldElement,
    new_ring_root: FieldElement,
    message_commitment: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: queue_cell,
            index: HEAD_SEQ_SLOT as usize,
            value: new_head,
        },
        Effect::SetField {
            cell: queue_cell,
            index: RING_ROOT_SLOT as usize,
            value: new_ring_root,
        },
        Effect::EmitEvent {
            cell: queue_cell,
            event: Event::new(
                symbol("pqueue-enqueued"),
                vec![new_head, new_ring_root, message_commitment],
            ),
        },
    ];

    wallet.make_action(queue_cell, "enqueue", effects)
}

/// Build the on-ledger [`Action`] recording a `dequeue`.
pub fn build_dequeue_action(
    wallet: &AppWallet,
    queue_cell: CellId,
    new_tail: FieldElement,
    dequeued_commitment: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: queue_cell,
            index: TAIL_SEQ_SLOT as usize,
            value: new_tail,
        },
        Effect::EmitEvent {
            cell: queue_cell,
            event: Event::new(
                symbol("pqueue-dequeued"),
                vec![new_tail, dequeued_commitment],
            ),
        },
    ];

    wallet.make_action(queue_cell, "dequeue", effects)
}

/// Build the on-ledger [`Action`] adding a sender to the
/// authorized-senders set.
pub fn build_grant_sender_action(
    wallet: &AppWallet,
    queue_cell: CellId,
    new_sender_set_root: FieldElement,
    new_sender_pk: [u8; 32],
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: queue_cell,
            index: SENDER_SET_ROOT_SLOT as usize,
            value: new_sender_set_root,
        },
        Effect::EmitEvent {
            cell: queue_cell,
            event: Event::new(
                symbol("pqueue-sender-granted"),
                vec![new_sender_set_root, new_sender_pk],
            ),
        },
    ];

    wallet.make_action(queue_cell, "grant_sender", effects)
}

// =============================================================================
// Initial state + registration
// =============================================================================

/// Initial state for a freshly-minted programmable-queue cell.
pub fn initial_state(
    capacity: u64,
    program_vk: [u8; 32],
    owner_pk_hash: [u8; 32],
    sender_set_root: [u8; 32],
    content_pattern_root: [u8; 32],
) -> [FieldElement; 8] {
    [
        [0u8; 32],
        [0u8; 32],
        u64_field(capacity),
        program_vk,
        owner_pk_hash,
        sender_set_root,
        content_pattern_root,
        [0u8; 32],
    ]
}

/// Register this template on a [`StarbridgeAppContext`].
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(programmable_queue_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "programmable-queue".into(),
        descriptor: serde_json::json!({
            "component": "pyana-programmable-queue",
            "module": "/pyana-storage-templates/programmable-queue.js",
            "uri_prefix": "pyana://cell/",
            "summary_fields": [
                "head_seq", "tail_seq", "capacity", "program_vk",
                "owner_pk_hash", "sender_set_root",
                "content_pattern_root", "ring_root",
            ],
            "factory_vk_hex": hex_encode(&factory_vk),
            "child_program_vk_hex": hex_encode(&programmable_queue_child_program_vk()),
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
        let h1 = programmable_queue_factory_descriptor().hash();
        let h2 = programmable_queue_factory_descriptor().hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        let expected = canonical_program_vk(&programmable_queue_program());
        assert_eq!(programmable_queue_child_program_vk(), expected);
    }

    #[test]
    fn descriptor_validates_against_canonical_program() {
        let d = programmable_queue_factory_descriptor();
        pyana_app_framework::validate_child_vk_canonical(&d, &programmable_queue_program())
            .expect("descriptor must bind canonical layered VK to the program");
    }

    #[test]
    fn program_is_cases_with_four_branches() {
        match programmable_queue_program() {
            CellProgram::Cases(cases) => {
                assert_eq!(cases.len(), 4, "Always + 3 MethodIs cases");
            }
            other => panic!("expected Cases, got {other:?}"),
        }
    }

    #[test]
    fn enqueue_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let action = build_enqueue_action(
            &wallet,
            cell,
            u64_field(1),
            blake3_field(b"r"),
            blake3_field(b"m"),
        );
        assert_eq!(action.method, symbol("enqueue"));
        assert_eq!(action.effects.len(), 3);
    }

    #[test]
    fn dequeue_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let action = build_dequeue_action(&wallet, cell, u64_field(1), blake3_field(b"d"));
        assert_eq!(action.method, symbol("dequeue"));
        assert_eq!(action.effects.len(), 2);
    }

    #[test]
    fn grant_sender_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let action =
            build_grant_sender_action(&wallet, cell, blake3_field(b"set-v1"), [9u8; 32]);
        assert_eq!(action.method, symbol("grant_sender"));
        assert_eq!(action.effects.len(), 2);
    }

    #[test]
    fn different_configs_yield_different_param_hashes() {
        let work = ProgrammableQueueConfig::work_queue_default(100);
        let auction = ProgrammableQueueConfig {
            enqueue_extras: vec![StateConstraint::StrictMonotonic {
                index: RING_ROOT_SLOT,
            }],
            dequeue_extras: vec![],
            capacity: 100,
        };
        assert_ne!(work.param_hash(), auction.param_hash());
    }

    #[test]
    fn different_configs_yield_different_child_program_vks() {
        let work = ProgrammableQueueConfig::work_queue_default(100);
        let auction = ProgrammableQueueConfig {
            enqueue_extras: vec![StateConstraint::StrictMonotonic {
                index: RING_ROOT_SLOT,
            }],
            dequeue_extras: vec![],
            capacity: 100,
        };
        assert_ne!(
            programmable_queue_child_program_vk_with(&work),
            programmable_queue_child_program_vk_with(&auction),
            "different configs must produce different VKs (per VK-AS-RE-EXECUTION-RECIPE)"
        );
    }

    #[test]
    fn descriptor_uses_derived_strategy() {
        let d = programmable_queue_factory_descriptor();
        match d.child_vk_strategy {
            Some(ChildVkStrategy::Derived { base_vk }) => {
                assert_eq!(base_vk, PROGRAMMABLE_QUEUE_FACTORY_VK);
            }
            other => panic!("expected Derived, got {other:?}"),
        }
    }

    #[test]
    fn register_installs_factory() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, PROGRAMMABLE_QUEUE_FACTORY_VK);
        assert!(ctx.inspector_registry().get("programmable-queue").is_some());
    }
}
