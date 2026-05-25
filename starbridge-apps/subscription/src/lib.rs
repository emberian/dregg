//! # starbridge-subscription
//!
//! Greenfield rebuild of the **storage-layer** of `apps/subscription/`
//! as a starbridge-app, and the **first concrete proof-of-pattern for
//! `STORAGE-AS-CELL-PROGRAMS.md`**.
//!
//! The original `apps/subscription/` used
//! `pyana_storage::inbox::CapInbox` as an operator-process data
//! structure with HTTP shims around it (`app-framework::inbox_endpoint`).
//! Per `STORAGE-AS-CELL-PROGRAMS.md` §1 that arrangement has five
//! distinct failure modes, the headline one being **the executor
//! never sees the queue's `SenderAuthorized` / `MonotonicSequence` /
//! `WriteOnce` constraints** — those are evaluated by a parallel
//! storage-side enforcement loop that produces no `TurnReceipt` and
//! cannot be audited against the cell-program substrate.
//!
//! This crate inverts that arrangement: a subscription cell *is* a
//! `CapInbox`-shaped cell-program. Its slot layout, slot caveats,
//! per-method operation-scoping, and capability surface live in a
//! [`subscription_factory_descriptor`] that anyone can audit by
//! hashing. The executor enforces the constraints on every turn.
//! Publish, consume, and the two grant operations are
//! [`AppCipherclerk`]-signed [`Action`]s composed only of existing
//! `Effect::SetField` and `Effect::EmitEvent` variants. No new Effect
//! is introduced; no storage-side enforcement loop survives.
//!
//! ## Companion docs
//!
//! - `STORAGE-AS-CELL-PROGRAMS.md` §3.1 — the CapInbox reference design
//!   (slot layout, declared `StateConstraint`s, factory descriptor,
//!   app-side `Effect` composition, observability, what-it-replaces).
//! - `STARBRIDGE-APPS-PLAN.md` §3.8 — subscription's place in the
//!   starbridge-app order. (The plan framed subscription as a
//!   *delegated-debit* shape; this crate is the *queue* shape that
//!   was the subscription app's real load-bearing primitive. The
//!   debit shape can layer on top in a follow-on crate.)
//! - `SLOT-CAVEATS-DESIGN.md` — the slot-caveat vocabulary the
//!   factory descriptor draws from.
//! - `SLOT-CAVEATS-EVALUATION.md` — the 21-variant lifted enum +
//!   operation-scoped `CellProgram::Cases(_)` shape used below.
//! - `starbridge-apps/nameservice/src/lib.rs` — the pattern anchor.
//!   This crate mirrors its structure.
//!
//! ## What this crate exports
//!
//! 1. [`subscription_factory_descriptor`] — the `FactoryDescriptor`
//!    pinning the constructor contract: slot layout, immutable
//!    capacity + owner, monotonic head/tail/roots, plus the
//!    operation-scoped state constraints via [`subscription_program`].
//! 2. [`subscription_program`] — the `CellProgram::Cases(_)` value
//!    that the descriptor bakes in. Exported separately so tests can
//!    directly drive `program.evaluate_with_meta(..)` against
//!    hand-rolled `(old_state, new_state, meta)` triples.
//! 3. [`factory_descriptors`] — the slice of all factory descriptors
//!    this starbridge-app contributes. Today: just one.
//! 4. Turn-builders (signed actions composed of generic Effects):
//!    - [`build_publish_action`] — publisher writes a payload hash
//!      and advances head.
//!    - [`build_consume_action`] — consumer advances tail and emits
//!      a dequeue event.
//!    - [`build_grant_publisher_action`] — owner adds a publisher key.
//!    - [`build_grant_consumer_action`] — owner adds a consumer key.
//! 5. [`register`] — `StarbridgeAppContext` mount hook that wires the
//!    factory + inspector descriptors into a shared host context.
//!
//! ## The slot layout
//!
//! `STATE_SLOTS = 8`. The 8 slots are:
//!
//! | Slot | Name | Caveat | Purpose |
//! |---:|---|---|---|
//! | 0 | `seq_head` | `MonotonicSequence` (publish-scoped) | Next sequence number a publisher will write. Advanced exactly +1 per publish. Bookmark for consumers. |
//! | 1 | `seq_tail` | `MonotonicSequence` (consume-scoped) | Next sequence number a consumer will read. Advanced exactly +1 per consume. Invariant: `tail <= head` (verified at the app-builder boundary; head==tail means empty). |
//! | 2 | `capacity` | `Immutable` | Max in-flight messages. Set at creation; never changes. |
//! | 3 | `authorized_publishers_root` | `Monotonic` | Merkle root over the set of authorized publisher pubkeys. Insertions only (set grows). |
//! | 4 | `authorized_consumers_root` | `Monotonic` | Merkle root over authorized consumers. Insertions only. |
//! | 5 | `owner_pk_hash` | `Immutable` | Hash of the subscription owner's pubkey. Only the owner may grant publishers/consumers. |
//! | 6 | `message_root` | `Monotonic` | Poseidon2/BLAKE3 root over the (seq, payload_hash) tuples published into the queue. Grows monotonically. |
//! | 7 | `latest_payload_hash` | per-method | The hash of the most recently published payload. On publish: written. On consume: unchanged. Inspectors read it as the head-of-queue summary. |
//!
//! ### Why a `message_root` and not 8 dedicated `message_slot[i]` slots?
//!
//! The spec in `STORAGE-AS-CELL-PROGRAMS.md` §3.1 talks about per-message
//! `WriteOnce` slots as an *idealized* surface. The cell substrate has
//! `STATE_SLOTS = 8` total (`pyana_cell::state::STATE_SLOTS`), which is
//! not enough to host an unbounded message ring. The actual data path
//! is the same one `MerkleQueue::root` uses today in `pyana_storage`:
//! a root commitment in slot 6, with the per-message tuples stored
//! out-of-band (in an off-cell content store keyed by the root). The
//! `WriteOnce` semantic at the *individual-message* level is enforced
//! by the root: once an `(i, payload_hash)` pair has been folded into
//! the root, the root commits to that payload at position `i`, and
//! any subsequent attempt to write a different payload at the same
//! index would have to produce the same root (and so would be
//! rejected by the consumer's Merkle membership check). The slot-level
//! `Monotonic { index: 6 }` constraint enforces that the root only
//! grows; the per-message `WriteOnce` semantic is structural.
//!
//! For deployments that want a tiny, slot-resident message ring (no
//! off-cell content store), the message_root slot can be replaced by
//! a fixed set of `WriteOnce { index: k }` constraints over slots
//! 6..N. That variant is a follow-on; the root-commitment shape is
//! the canonical pattern.
//!
//! ## Operation-scoping
//!
//! Per `SLOT-CAVEATS-EVALUATION.md` §7.1, the `CellProgram::Cases(_)`
//! shape (Cav-Codex Block 4) lets us scope constraints to specific
//! operations. The four operations on a subscription cell each get
//! their own case, guarded on the action's method symbol:
//!
//! - `publish` — head advances by exactly 1 (`MonotonicSequence`),
//!   tail must be unchanged (`Immutable { index: 1 }`),
//!   the message_root must advance (`Monotonic { index: 6 }`),
//!   sender must be in `authorized_publishers_root`
//!   (`SenderAuthorized { set: PublicRoot { set_root_index: 3 } }`),
//!   roots-of-membership stay frozen on publish.
//! - `consume` — tail advances by exactly 1 (`MonotonicSequence`),
//!   head must be unchanged (`Immutable { index: 0 }`),
//!   sender must be in `authorized_consumers_root`
//!   (`SenderAuthorized { set: PublicRoot { set_root_index: 4 } }`),
//!   message_root + latest_payload_hash stay frozen, membership
//!   roots frozen.
//! - `grant_publisher` — `authorized_publishers_root` advances
//!   (`Monotonic { index: 3 }`); head, tail, capacity, owner, msg
//!   root, latest payload, and the consumers root all immutable.
//!   The owner authorization is enforced by the per-cell capability
//!   layer (action sender is the owner of the cell).
//! - `grant_consumer` — symmetric to `grant_publisher` over slot 4.
//!
//! Plus an `Always`-guarded base case carrying the *invariants* that
//! hold across every transition: capacity and owner immutable. These
//! invariants AND with whatever per-method case fires.
//!
//! Per Cav-Codex Block 4, if **no** case matches a transition the
//! program default-denies. That is: an action with an unrecognized
//! method symbol is rejected outright. The four operations above are
//! the *only* legal transitions.
//!
//! ## Dependency on the caveat-correctness lane
//!
//! `STORAGE-AS-CELL-PROGRAMS.md` notes the operation-scoped case
//! shape is exactly what the caveat-correctness lane is adding. If
//! that lane has not landed at the executor / AIR level by the time
//! this crate ships, the descriptor and turn-builders still produce
//! correct Actions and Effects — what gates on the in-flight lane is
//! the *executor-side* rejection of off-pattern transitions
//! (`evaluate_with_meta` against the `MethodIs` guard). The unit
//! tests in this crate and the adversarial tests in `tests/program.rs`
//! drive `evaluate_with_meta` directly so they exercise the
//! operation-scoped semantics regardless of the executor's wiring
//! state. See the README for the dependency note.

use pyana_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode,
    ChildVkStrategy, Effect, Event, FactoryDescriptor, FieldConstraint, FieldElement,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, canonical_program_vk, symbol,
};
use pyana_cell::program::{AuthorizedSet, CellProgram, TransitionCase, TransitionGuard};

// =============================================================================
// Slot layout
// =============================================================================

/// Slot 0 — `seq_head`. Producer cursor. Advanced exactly +1 per `publish`.
pub const SEQ_HEAD_SLOT: u8 = 0;
/// Slot 1 — `seq_tail`. Consumer cursor. Advanced exactly +1 per `consume`.
pub const SEQ_TAIL_SLOT: u8 = 1;
/// Slot 2 — `capacity`. Immutable upper bound on in-flight messages.
pub const CAPACITY_SLOT: u8 = 2;
/// Slot 3 — `authorized_publishers_root`. Merkle root of allowed publisher pubkeys.
pub const PUBLISHERS_ROOT_SLOT: u8 = 3;
/// Slot 4 — `authorized_consumers_root`. Merkle root of allowed consumer pubkeys.
pub const CONSUMERS_ROOT_SLOT: u8 = 4;
/// Slot 5 — `owner_pk_hash`. Immutable owner identity.
pub const OWNER_PK_HASH_SLOT: u8 = 5;
/// Slot 6 — `message_root`. Monotonic root over published (seq, payload_hash) tuples.
pub const MESSAGE_ROOT_SLOT: u8 = 6;
/// Slot 7 — `latest_payload_hash`. The most recently published payload hash.
pub const LATEST_PAYLOAD_SLOT: u8 = 7;

// =============================================================================
// Factory configuration
// =============================================================================

/// Default per-epoch creation budget. Rate-limits Sybil creation of
/// subscription cells from this factory.
pub const DEFAULT_CREATION_BUDGET: u64 = 1_000;

/// The factory VK we publish for the subscription factory.
///
/// Like the nameservice factory, this is a stable placeholder for the
/// BLAKE3 hash of the subscription cell-program VK. Replacing it with
/// the real VK is a single constant change once the cell-program AIR
/// for `subscription_program` is authored.
pub const SUBSCRIPTION_FACTORY_VK: [u8; 32] = *b"starbridge-subscription-factory!";

/// The child cell-program VK installed on per-subscription cells.
///
/// Per `VK-AS-RE-EXECUTION-RECIPE.md` §2.1: computed canonically as
/// `canonical_program_vk(&subscription_program())`. A validator with
/// [`subscription_program`] in scope can re-derive the VK and
/// re-execute the program against witness data.
///
/// Previously a byte-string placeholder
/// (`*b"starbridge-subscription-childprg"`); the canonical version
/// makes the substrate honest pre-recursion.
pub fn subscription_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&subscription_program())
}

/// Method symbol for `publish`.
pub fn publish_method_symbol() -> [u8; 32] {
    symbol("publish")
}
/// Method symbol for `consume`.
pub fn consume_method_symbol() -> [u8; 32] {
    symbol("consume")
}
/// Method symbol for `grant_publisher`.
pub fn grant_publisher_method_symbol() -> [u8; 32] {
    symbol("grant_publisher")
}
/// Method symbol for `grant_consumer`.
pub fn grant_consumer_method_symbol() -> [u8; 32] {
    symbol("grant_consumer")
}

// =============================================================================
// CellProgram: operation-scoped Cases
// =============================================================================

/// Build the `CellProgram` enforcing the subscription cell's
/// lifetime invariants and per-operation transitions.
///
/// Per the design notes in the crate docs: this is a
/// `CellProgram::Cases(_)` with five cases — one `Always`-guarded
/// invariants case plus four `MethodIs`-guarded operation cases.
/// Cases default-deny when no case matches (per Cav-Codex Block 4),
/// so any action whose method symbol is not one of the four legal
/// operations is rejected outright.
pub fn subscription_program() -> CellProgram {
    CellProgram::Cases(vec![
        // ────────────────────────────────────────────────────────────────
        // Invariants: every transition, regardless of operation.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                StateConstraint::Immutable {
                    index: CAPACITY_SLOT,
                },
                StateConstraint::Immutable {
                    index: OWNER_PK_HASH_SLOT,
                },
            ],
        },
        // ────────────────────────────────────────────────────────────────
        // publish: head advances by +1; tail, capacity, owner, roots stay
        // unchanged; message_root advances monotonically; sender must be
        // a member of authorized_publishers_root.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("publish"),
            },
            constraints: vec![
                StateConstraint::MonotonicSequence {
                    seq_index: SEQ_HEAD_SLOT,
                },
                StateConstraint::Immutable {
                    index: SEQ_TAIL_SLOT,
                },
                StateConstraint::Immutable {
                    index: PUBLISHERS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: CONSUMERS_ROOT_SLOT,
                },
                StateConstraint::Monotonic {
                    index: MESSAGE_ROOT_SLOT,
                },
                // The latest_payload slot is overwritten per publish; the
                // per-message WriteOnce semantic is structurally enforced
                // by the message_root commitment (see crate docs).
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: PUBLISHERS_ROOT_SLOT,
                    },
                },
            ],
        },
        // ────────────────────────────────────────────────────────────────
        // consume: tail advances by +1; head, message_root, latest_payload,
        // capacity, owner, roots stay unchanged; sender must be a member
        // of authorized_consumers_root.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("consume"),
            },
            constraints: vec![
                StateConstraint::MonotonicSequence {
                    seq_index: SEQ_TAIL_SLOT,
                },
                StateConstraint::Immutable {
                    index: SEQ_HEAD_SLOT,
                },
                StateConstraint::Immutable {
                    index: MESSAGE_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: LATEST_PAYLOAD_SLOT,
                },
                StateConstraint::Immutable {
                    index: PUBLISHERS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: CONSUMERS_ROOT_SLOT,
                },
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: CONSUMERS_ROOT_SLOT,
                    },
                },
            ],
        },
        // ────────────────────────────────────────────────────────────────
        // grant_publisher: publishers_root advances; everything else frozen.
        // Owner authorization rides on the per-cell capability layer.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("grant_publisher"),
            },
            constraints: vec![
                StateConstraint::Monotonic {
                    index: PUBLISHERS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: SEQ_HEAD_SLOT,
                },
                StateConstraint::Immutable {
                    index: SEQ_TAIL_SLOT,
                },
                StateConstraint::Immutable {
                    index: CONSUMERS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: MESSAGE_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: LATEST_PAYLOAD_SLOT,
                },
            ],
        },
        // ────────────────────────────────────────────────────────────────
        // grant_consumer: symmetric to grant_publisher over consumers_root.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("grant_consumer"),
            },
            constraints: vec![
                StateConstraint::Monotonic {
                    index: CONSUMERS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: SEQ_HEAD_SLOT,
                },
                StateConstraint::Immutable {
                    index: SEQ_TAIL_SLOT,
                },
                StateConstraint::Immutable {
                    index: PUBLISHERS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: MESSAGE_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: LATEST_PAYLOAD_SLOT,
                },
            ],
        },
    ])
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Build the `FactoryDescriptor` for per-subscription sovereign cells.
///
/// The descriptor pins the constructor-transparency contract anyone
/// can audit by hashing:
///
/// - `child_program_vk = subscription_child_program_vk()` — the
///   operation-scoped cell-program (`subscription_program`).
/// - `default_mode = Hosted` — subscription queues are naturally
///   federation-hosted (the federation sees cleartext events for
///   producers and consumers; the payload bodies themselves live in
///   the off-cell content store). Sovereign cells with private
///   payload bodies are a follow-on factory.
/// - `creation_budget = DEFAULT_CREATION_BUDGET` (Sybil cap).
/// - `allowed_cap_templates` = a `[owner, publisher, consumer]` triple:
///   the factory may issue an owner cap (full control over grants)
///   plus an attenuatable publisher cap and an attenuatable consumer
///   cap. Sub-delegation rides on `Caveat::ResourcePrefix`.
/// - `field_constraints` (creation-time): head, tail initialize to
///   zero; capacity within a sane range; owner_pk_hash non-zero.
/// - `state_constraints` (perpetual / Lane G slot caveats): the
///   `Immutable` invariants flattened from
///   [`subscription_program`]'s `Always` case plus the cell-wide
///   `Monotonic` invariants for head, tail, the membership roots,
///   and the message root. The full operation-scoped shape is bound
///   by `child_program_vk` (which is the VK of an AIR that enforces
///   [`subscription_program`]).
///
/// The split between `state_constraints` (descriptor) and
/// `subscription_program` (cell-program) is intentional. The
/// descriptor's field is `Vec<StateConstraint>` — a flat list, no
/// `Cases` shape — because the descriptor is hashed for constructor
/// transparency before the cell-program AIR exists. The flat list
/// commits to the *invariants*; the AIR commits to the full
/// operation-scoped shape.
pub fn subscription_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: SUBSCRIPTION_FACTORY_VK,
        child_program_vk: Some(subscription_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(
            Some(subscription_child_program_vk()),
        )),
        allowed_cap_templates: vec![
            // Owner cap — full control over publisher/consumer grants.
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
            // Publisher cap — may publish.
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
            // Consumer cap — may consume.
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
        ],
        field_constraints: vec![
            // Initial state: head == tail == 0 (empty queue).
            FieldConstraint::Equality {
                field_index: SEQ_HEAD_SLOT as u32,
                value: 0,
            },
            FieldConstraint::Equality {
                field_index: SEQ_TAIL_SLOT as u32,
                value: 0,
            },
            // Capacity must be in [1, 1_000_000].
            FieldConstraint::Range {
                field_index: CAPACITY_SLOT as u32,
                min: 1,
                max: 1_000_000,
            },
            // Owner must be non-zero (no null-owned subscription).
            FieldConstraint::NonZero {
                field_index: OWNER_PK_HASH_SLOT as u32,
            },
        ],
        state_constraints: vec![
            // Lifetime invariants — flattened from the `Always` case.
            // The full operation-scoped shape is in `subscription_program`.
            StateConstraint::Immutable {
                index: CAPACITY_SLOT,
            },
            StateConstraint::Immutable {
                index: OWNER_PK_HASH_SLOT,
            },
            // The roots and counters are monotonic across the cell's
            // lifetime, regardless of which operation moved them. Per-op
            // cases narrow this further (which op may move which slot).
            StateConstraint::Monotonic {
                index: SEQ_HEAD_SLOT,
            },
            StateConstraint::Monotonic {
                index: SEQ_TAIL_SLOT,
            },
            StateConstraint::Monotonic {
                index: PUBLISHERS_ROOT_SLOT,
            },
            StateConstraint::Monotonic {
                index: CONSUMERS_ROOT_SLOT,
            },
            StateConstraint::Monotonic {
                index: MESSAGE_ROOT_SLOT,
            },
        ],
        default_mode: CellMode::Hosted,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// The full slice of factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![subscription_factory_descriptor()]
}

// =============================================================================
// Turn-builders
// =============================================================================

/// Build the on-ledger [`Action`] that records a `publish`.
///
/// The action carries three `SetField` effects (head advances,
/// message_root advances, latest_payload slot updated) plus an
/// `EmitEvent("subscription-published", ...)` for off-chain
/// indexers. The cipherclerk's `make_action` produces a real
/// `Authorization::Signature(..)`; the executor checks the
/// `publish`-case constraints against the (old, new) state pair
/// and the action's sender on every turn.
///
/// # Parameters
///
/// - `cipherclerk` — the [`AppCipherclerk`] signing the publish (must hold a
///   publisher cap or have its public key under
///   `authorized_publishers_root`).
/// - `subscription_cell` — the target subscription cell.
/// - `new_head` — the new value of slot 0 (`old_head + 1`). The
///   caller computes this from the cell's current state.
/// - `new_message_root` — the new value of slot 6 (the root after
///   folding `(new_head, payload_hash)` into the prior root).
/// - `payload_hash` — the hash of the payload being published. Stored
///   verbatim in slot 7 as `latest_payload_hash`; also published in
///   the event payload for indexers.
pub fn build_publish_action(
    cipherclerk: &AppCipherclerk,
    subscription_cell: CellId,
    new_head: FieldElement,
    new_message_root: FieldElement,
    payload_hash: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: subscription_cell,
            index: SEQ_HEAD_SLOT as usize,
            value: new_head,
        },
        Effect::SetField {
            cell: subscription_cell,
            index: MESSAGE_ROOT_SLOT as usize,
            value: new_message_root,
        },
        Effect::SetField {
            cell: subscription_cell,
            index: LATEST_PAYLOAD_SLOT as usize,
            value: payload_hash,
        },
        Effect::EmitEvent {
            cell: subscription_cell,
            event: Event::new(
                symbol("subscription-published"),
                vec![new_head, new_message_root, payload_hash],
            ),
        },
    ];

    cipherclerk.make_action(subscription_cell, "publish", effects)
}

/// Build the on-ledger [`Action`] that records a `consume`.
///
/// The action carries one `SetField` (tail advances) plus an
/// `EmitEvent("subscription-consumed", ...)`. The consumer fetches
/// the payload body out-of-band by Merkle-proving inclusion against
/// slot 6's `message_root`; the on-cell state only commits to the
/// cursor and the root.
///
/// # Parameters
///
/// - `cipherclerk` — the [`AppCipherclerk`] signing the consume (must hold a
///   consumer cap or have its public key under
///   `authorized_consumers_root`).
/// - `subscription_cell` — the target subscription cell.
/// - `new_tail` — the new value of slot 1 (`old_tail + 1`). The
///   caller computes this from the cell's current state.
/// - `consumed_payload_hash` — the payload hash that was just
///   consumed. Surfaced in the event for off-chain indexers; not
///   written to state (per the `consume` case's `Immutable` set on
///   slot 7).
pub fn build_consume_action(
    cipherclerk: &AppCipherclerk,
    subscription_cell: CellId,
    new_tail: FieldElement,
    consumed_payload_hash: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: subscription_cell,
            index: SEQ_TAIL_SLOT as usize,
            value: new_tail,
        },
        Effect::EmitEvent {
            cell: subscription_cell,
            event: Event::new(
                symbol("subscription-consumed"),
                vec![new_tail, consumed_payload_hash],
            ),
        },
    ];

    cipherclerk.make_action(subscription_cell, "consume", effects)
}

/// Build the on-ledger [`Action`] that adds a new publisher to the
/// authorized-publishers set.
///
/// The action carries one `SetField` (the publishers_root advances
/// to a new root that includes `new_publisher_pk`) plus an
/// `EmitEvent("subscription-publisher-granted", ...)` for indexers.
/// Per the `grant_publisher` case, every other slot stays frozen on
/// this turn.
///
/// # Parameters
///
/// - `cipherclerk` — the [`AppCipherclerk`] signing the grant. Must be the
///   owner of the subscription cell (the `owner_pk_hash` slot's
///   preimage); the per-cell capability layer enforces this.
/// - `subscription_cell` — the target subscription cell.
/// - `new_publishers_root` — the new Merkle root over the publishers
///   set after adding `new_publisher_pk`. The caller computes this
///   from the prior root + the new pubkey.
/// - `new_publisher_pk` — the pubkey being added (for the event).
pub fn build_grant_publisher_action(
    cipherclerk: &AppCipherclerk,
    subscription_cell: CellId,
    new_publishers_root: FieldElement,
    new_publisher_pk: [u8; 32],
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: subscription_cell,
            index: PUBLISHERS_ROOT_SLOT as usize,
            value: new_publishers_root,
        },
        Effect::EmitEvent {
            cell: subscription_cell,
            event: Event::new(
                symbol("subscription-publisher-granted"),
                vec![new_publishers_root, new_publisher_pk],
            ),
        },
    ];

    cipherclerk.make_action(subscription_cell, "grant_publisher", effects)
}

/// Build the on-ledger [`Action`] that adds a new consumer to the
/// authorized-consumers set.
///
/// Symmetric to [`build_grant_publisher_action`].
pub fn build_grant_consumer_action(
    cipherclerk: &AppCipherclerk,
    subscription_cell: CellId,
    new_consumers_root: FieldElement,
    new_consumer_pk: [u8; 32],
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: subscription_cell,
            index: CONSUMERS_ROOT_SLOT as usize,
            value: new_consumers_root,
        },
        Effect::EmitEvent {
            cell: subscription_cell,
            event: Event::new(
                symbol("subscription-consumer-granted"),
                vec![new_consumers_root, new_consumer_pk],
            ),
        },
    ];

    cipherclerk.make_action(subscription_cell, "grant_consumer", effects)
}

// =============================================================================
// Cross-app composition: bounty-state notifications
// =============================================================================
//
// A subscription cell is a generic publish/consume queue, but the
// canonical cross-app load it carries in the cross-app-e2e composition
// story is **bounty-state notifications**: when a bounty's state
// transitions (posted → claimed → fulfilled → settled), the bounty's
// posting cell wants to notify subscribers (the original poster, the
// claimant, watchers) without leaking the bounty body cleartext.
//
// The integration is data-only: the bounty app computes a canonical
// `bounty_state_payload_hash` over the (bounty_id, prior_state,
// new_state, actor_pk_hash) tuple and publishes it via
// [`build_publish_action`]. Subscribers consume the event stream and
// resolve the payload body out-of-band from a content store keyed by
// the published hash.

/// Canonical bounty lifecycle states. Used to seed the state-change
/// payload hash so each transition is uniquely identifiable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BountyState {
    /// Bounty has been posted; no claimant yet.
    Posted,
    /// A worker has claimed the bounty; fulfillment pending.
    Claimed,
    /// A fulfillment proof has been submitted; pending dispute window.
    Fulfilled,
    /// Settlement has occurred — bounty paid (or refunded on dispute).
    Settled,
    /// Bounty was canceled before fulfillment.
    Canceled,
}

impl BountyState {
    /// Single-byte canonical tag for the state. Used inside the payload
    /// hash and surfaced as a 32-byte event datum so off-chain indexers
    /// can filter by state without parsing the full payload.
    pub fn tag(self) -> u8 {
        match self {
            BountyState::Posted => 1,
            BountyState::Claimed => 2,
            BountyState::Fulfilled => 3,
            BountyState::Settled => 4,
            BountyState::Canceled => 5,
        }
    }

    /// Encode the state tag as a 32-byte `FieldElement` (zero-padded
    /// LSB-style). Suitable as a fact term in event data.
    pub fn tag_field(self) -> FieldElement {
        let mut out = [0u8; 32];
        out[31] = self.tag();
        out
    }
}

/// Compute the canonical payload hash for a bounty-state transition.
///
/// `blake3_derive_key("pyana-bounty-state-v1") || bounty_id ||
/// prior_state.tag() || new_state.tag() || actor_pk_hash`. Distinct
/// (bounty_id, prior, new, actor) tuples produce distinct payload
/// hashes — replay-safe at the commitment level. The matching
/// fulfillment / settlement payloads carry the same shape so the
/// receipt chain composes deterministically.
///
/// Returns a 32-byte `FieldElement` ready to feed into
/// [`build_publish_action`]'s `payload_hash` argument.
pub fn bounty_state_payload_hash(
    bounty_id: &[u8; 32],
    prior_state: BountyState,
    new_state: BountyState,
    actor_pk_hash: &[u8; 32],
) -> FieldElement {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-bounty-state-v1");
    hasher.update(bounty_id);
    hasher.update(&[prior_state.tag()]);
    hasher.update(&[new_state.tag()]);
    hasher.update(actor_pk_hash);
    *hasher.finalize().as_bytes()
}

/// Convenience: build a `publish` action that notifies a subscription
/// cell of a bounty state change.
///
/// Wraps [`build_publish_action`] with [`bounty_state_payload_hash`] so
/// callers compose the cross-app pipeline in one call. The caller still
/// supplies `new_head` (the advanced cursor) and `new_message_root`
/// (the advanced root) — these are queue invariants the executor's
/// `publish`-case constraints enforce regardless of payload contents.
pub fn build_bounty_state_publish_action(
    cipherclerk: &AppCipherclerk,
    subscription_cell: CellId,
    new_head: FieldElement,
    new_message_root: FieldElement,
    bounty_id: &[u8; 32],
    prior_state: BountyState,
    new_state: BountyState,
    actor_pk_hash: &[u8; 32],
) -> Action {
    let payload_hash = bounty_state_payload_hash(bounty_id, prior_state, new_state, actor_pk_hash);
    build_publish_action(
        cipherclerk,
        subscription_cell,
        new_head,
        new_message_root,
        payload_hash,
    )
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// Register this starbridge-app on a [`StarbridgeAppContext`].
///
/// Wires the subscription factory descriptor and the
/// `<pyana-subscription>` family of inspector descriptors into the
/// shared host registry. Returns the registered `factory_vk` so the
/// host can log it.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(subscription_factory_descriptor());

    // Per-subscription inspector — the head-of-queue summary mount.
    ctx.register_inspector(InspectorDescriptor {
        kind: "subscription".into(),
        descriptor: serde_json::json!({
            "component": "pyana-subscription",
            "module": "/starbridge-apps/subscription/inspectors.js",
            "uri_prefix": "pyana://cell/",
            "summary_fields": [
                "seq_head", "seq_tail", "capacity",
                "publishers_root", "consumers_root", "message_root",
                "latest_payload_hash",
            ],
            "factory_vk_hex": hex_encode(&factory_vk),
            "child_program_vk_hex": hex_encode(&subscription_child_program_vk()),
        }),
    });

    // Publisher's compose-and-publish form. Distinct kind so the
    // Studio can mount a different React component.
    ctx.register_inspector_with("subscription-publish-form", || {
        serde_json::json!({
            "component": "pyana-subscription-publish-form",
            "module": "/starbridge-apps/subscription/inspectors.js",
            "uri_prefix": "pyana://cell/",
            "factory_vk_hex": hex_encode(&SUBSCRIPTION_FACTORY_VK),
        })
    });

    // Consumer's live feed view (the head-of-queue stream).
    ctx.register_inspector_with("subscription-feed", || {
        serde_json::json!({
            "component": "pyana-subscription-feed",
            "module": "/starbridge-apps/subscription/inspectors.js",
            "uri_prefix": "pyana://cell/",
            "factory_vk_hex": hex_encode(&SUBSCRIPTION_FACTORY_VK),
        })
    });

    factory_vk
}

/// Hex-encode a 32-byte array (used by inspector JSON descriptors).
fn hex_encode(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// =============================================================================
// Tests — adversarial transition tests live in tests/program.rs
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([7u8; 32])
    }

    fn u64_field(value: u64) -> FieldElement {
        let mut out = [0u8; 32];
        out[24..32].copy_from_slice(&value.to_be_bytes());
        out
    }

    fn blake3_field(bytes: &[u8]) -> FieldElement {
        *blake3::hash(bytes).as_bytes()
    }

    // ─── FactoryDescriptor tests ────────────────────────────────────────

    #[test]
    fn factory_descriptor_is_stable() {
        let h1 = subscription_factory_descriptor().hash();
        let h2 = subscription_factory_descriptor().hash();
        assert_eq!(h1, h2, "descriptor hash must be deterministic");
    }

    #[test]
    fn factory_descriptor_pins_program_vk() {
        let d = subscription_factory_descriptor();
        assert_eq!(d.factory_vk, SUBSCRIPTION_FACTORY_VK);
        assert_eq!(d.child_program_vk, Some(subscription_child_program_vk()));
        assert_eq!(d.default_mode, CellMode::Hosted);
        assert_eq!(d.creation_budget, Some(DEFAULT_CREATION_BUDGET));
    }

    #[test]
    fn subscription_child_program_vk_is_canonical_recipe() {
        // Per VK-AS-RE-EXECUTION-RECIPE.md §2.1: validators with
        // `subscription_program()` in scope re-derive the VK and re-execute.
        let expected = pyana_app_framework::canonical_program_vk(&subscription_program());
        assert_eq!(
            subscription_child_program_vk(),
            expected,
            "subscription_child_program_vk must equal canonical_program_vk(&subscription_program())"
        );
    }

    #[test]
    fn subscription_child_program_vk_is_not_placeholder_bytes() {
        let old_placeholder: [u8; 32] = *b"starbridge-subscription-childprg";
        assert_ne!(
            subscription_child_program_vk(),
            old_placeholder,
            "canonical VK must differ from the pre-recipe placeholder"
        );
    }

    #[test]
    fn subscription_child_program_vk_is_v2_layered_hash() {
        // VK v2 (VK-AS-RE-EXECUTION-RECIPE.md §v2): the layered hash
        // must differ from the v1 program-bytes-only hash.
        let program = subscription_program();
        let v2 = subscription_child_program_vk();
        let v1 = pyana_app_framework::canonical_program_bytes_hash(&program);
        assert_ne!(
            v2, v1,
            "v2 layered hash must differ from v1 program-bytes-only hash"
        );
    }

    #[test]
    fn factory_descriptor_validates_against_canonical_program() {
        // VK v2: the app-framework wrapper validates against the
        // *layered* canonical hash (program bytes + Effect VM AIR +
        // verifier + Plonky3 proving system).
        let d = subscription_factory_descriptor();
        let program = subscription_program();
        pyana_app_framework::validate_child_vk_canonical(&d, &program)
            .expect("descriptor's child_program_vk must bind to subscription_program() under v2");
    }

    #[test]
    fn factory_descriptor_bakes_invariant_immutables() {
        let d = subscription_factory_descriptor();
        assert!(
            d.state_constraints.iter().any(
                |c| matches!(c, StateConstraint::Immutable { index } if *index == CAPACITY_SLOT)
            ),
            "factory must install Immutable on CAPACITY_SLOT"
        );
        assert!(
            d.state_constraints
                .iter()
                .any(|c| matches!(c, StateConstraint::Immutable { index } if *index == OWNER_PK_HASH_SLOT)),
            "factory must install Immutable on OWNER_PK_HASH_SLOT"
        );
    }

    #[test]
    fn factory_descriptor_bakes_monotonic_invariants() {
        let d = subscription_factory_descriptor();
        for slot in [
            SEQ_HEAD_SLOT,
            SEQ_TAIL_SLOT,
            PUBLISHERS_ROOT_SLOT,
            CONSUMERS_ROOT_SLOT,
            MESSAGE_ROOT_SLOT,
        ] {
            assert!(
                d.state_constraints
                    .iter()
                    .any(|c| matches!(c, StateConstraint::Monotonic { index } if *index == slot)),
                "factory must install Monotonic on slot {slot}"
            );
        }
    }

    #[test]
    fn factory_descriptor_initial_head_tail_zero() {
        let d = subscription_factory_descriptor();
        let mut found_head = false;
        let mut found_tail = false;
        for c in &d.field_constraints {
            if let FieldConstraint::Equality { field_index, value } = c {
                if *field_index == SEQ_HEAD_SLOT as u32 && *value == 0 {
                    found_head = true;
                }
                if *field_index == SEQ_TAIL_SLOT as u32 && *value == 0 {
                    found_tail = true;
                }
            }
        }
        assert!(found_head, "factory must init head==0");
        assert!(found_tail, "factory must init tail==0");
    }

    #[test]
    fn factory_descriptors_slice_contains_subscription() {
        let all = factory_descriptors();
        assert_eq!(all.len(), 1);
        assert_eq!(all[0].factory_vk, SUBSCRIPTION_FACTORY_VK);
    }

    // ─── Turn-builder shape tests ───────────────────────────────────────

    #[test]
    fn publish_action_shape() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let new_head = u64_field(1);
        let new_root = blake3_field(b"root-after-1");
        let payload = blake3_field(b"payload");
        let action = build_publish_action(&cipherclerk, cell, new_head, new_root, payload);

        assert_eq!(action.target, cell);
        assert_eq!(action.method, symbol("publish"));
        assert_eq!(action.effects.len(), 4, "publish has 3 SetField + 1 Event");
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == SEQ_HEAD_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, .. } if *index == MESSAGE_ROOT_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, .. } if *index == LATEST_PAYLOAD_SLOT as usize
        ));
        assert!(matches!(&action.effects[3], Effect::EmitEvent { .. }));
    }

    #[test]
    fn consume_action_shape() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let action =
            build_consume_action(&cipherclerk, cell, u64_field(1), blake3_field(b"payload"));

        assert_eq!(action.method, symbol("consume"));
        assert_eq!(action.effects.len(), 2);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == SEQ_TAIL_SLOT as usize
        ));
        assert!(matches!(&action.effects[1], Effect::EmitEvent { .. }));
    }

    #[test]
    fn grant_publisher_action_shape() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let new_root = blake3_field(b"publishers-root-v1");
        let action = build_grant_publisher_action(&cipherclerk, cell, new_root, [9u8; 32]);

        assert_eq!(action.method, symbol("grant_publisher"));
        assert_eq!(action.effects.len(), 2);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. }
            if *index == PUBLISHERS_ROOT_SLOT as usize && *value == new_root
        ));
    }

    #[test]
    fn grant_consumer_action_shape() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let new_root = blake3_field(b"consumers-root-v1");
        let action = build_grant_consumer_action(&cipherclerk, cell, new_root, [11u8; 32]);

        assert_eq!(action.method, symbol("grant_consumer"));
        assert_eq!(action.effects.len(), 2);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. }
            if *index == CONSUMERS_ROOT_SLOT as usize && *value == new_root
        ));
    }

    #[test]
    fn actions_carry_real_signatures() {
        // No `[0u8; 64]` placeholders anywhere.
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let actions = [
            build_publish_action(
                &cipherclerk,
                cell,
                u64_field(1),
                blake3_field(b"r"),
                blake3_field(b"p"),
            ),
            build_consume_action(&cipherclerk, cell, u64_field(1), blake3_field(b"p")),
            build_grant_publisher_action(&cipherclerk, cell, blake3_field(b"r"), [9u8; 32]),
            build_grant_consumer_action(&cipherclerk, cell, blake3_field(b"r"), [11u8; 32]),
        ];
        for a in &actions {
            match &a.authorization {
                Authorization::Signature(r, s) => {
                    assert!(
                        *r != [0u8; 32] || *s != [0u8; 32],
                        "signature must be non-zero (no [0u8; 64] placeholders!)"
                    );
                }
                other => panic!("expected Signature variant, got {other:?}"),
            }
        }
    }

    #[test]
    fn different_cipherclerks_produce_different_signatures() {
        let cc1 = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let cc2 = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let cell = test_cell();
        let payload = blake3_field(b"payload");
        let a1 = build_publish_action(&cc1, cell, u64_field(1), blake3_field(b"r"), payload);
        let a2 = build_publish_action(&cc2, cell, u64_field(1), blake3_field(b"r"), payload);
        let (Authorization::Signature(r1, _), Authorization::Signature(r2, _)) =
            (&a1.authorization, &a2.authorization)
        else {
            panic!("expected Signature variants");
        };
        assert_ne!(
            r1, r2,
            "different cipherclerks must produce different signatures"
        );
    }

    // ─── CellProgram: structural shape ──────────────────────────────────

    #[test]
    fn program_is_cases_with_five_branches() {
        match subscription_program() {
            CellProgram::Cases(cases) => {
                assert_eq!(cases.len(), 5, "expected one Always + four MethodIs cases");
            }
            other => panic!("expected CellProgram::Cases, got {other:?}"),
        }
    }

    #[test]
    fn program_covers_all_four_methods() {
        let cases = match subscription_program() {
            CellProgram::Cases(c) => c,
            _ => panic!("expected Cases"),
        };
        let mut seen_publish = false;
        let mut seen_consume = false;
        let mut seen_grant_pub = false;
        let mut seen_grant_con = false;
        for case in &cases {
            if let TransitionGuard::MethodIs { method } = &case.guard {
                if *method == symbol("publish") {
                    seen_publish = true;
                }
                if *method == symbol("consume") {
                    seen_consume = true;
                }
                if *method == symbol("grant_publisher") {
                    seen_grant_pub = true;
                }
                if *method == symbol("grant_consumer") {
                    seen_grant_con = true;
                }
            }
        }
        assert!(seen_publish, "publish case missing");
        assert!(seen_consume, "consume case missing");
        assert!(seen_grant_pub, "grant_publisher case missing");
        assert!(seen_grant_con, "grant_consumer case missing");
    }

    #[test]
    fn publish_case_advances_head_only() {
        let cases = match subscription_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let publish_case = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("publish")))
            .expect("publish case present");
        assert!(
            publish_case.constraints.iter().any(|c| matches!(c,
                StateConstraint::MonotonicSequence { seq_index } if *seq_index == SEQ_HEAD_SLOT
            )),
            "publish must MonotonicSequence head"
        );
        assert!(
            publish_case.constraints.iter().any(|c| matches!(c,
                StateConstraint::Immutable { index } if *index == SEQ_TAIL_SLOT
            )),
            "publish must lock tail Immutable (no tail advance)"
        );
    }

    #[test]
    fn consume_case_advances_tail_only() {
        let cases = match subscription_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let consume_case = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("consume")))
            .expect("consume case present");
        assert!(
            consume_case.constraints.iter().any(|c| matches!(c,
                StateConstraint::MonotonicSequence { seq_index } if *seq_index == SEQ_TAIL_SLOT
            )),
            "consume must MonotonicSequence tail"
        );
        assert!(
            consume_case.constraints.iter().any(|c| matches!(c,
                StateConstraint::Immutable { index } if *index == SEQ_HEAD_SLOT
            )),
            "consume must lock head Immutable (no head advance)"
        );
    }

    // ─── StarbridgeAppContext registration ──────────────────────────────

    #[test]
    fn register_installs_subscription_factory() {
        let ctx = test_context();
        assert_eq!(ctx.factory_registry().len(), 0);
        let vk = register(&ctx);
        assert_eq!(vk, SUBSCRIPTION_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        let got = ctx
            .factory_registry()
            .get(&SUBSCRIPTION_FACTORY_VK)
            .expect("subscription factory registered");
        assert_eq!(got.factory_vk, SUBSCRIPTION_FACTORY_VK);
        assert_eq!(got.child_program_vk, Some(subscription_child_program_vk()));
        assert_eq!(got.default_mode, CellMode::Hosted);
    }

    #[test]
    fn register_installs_three_inspectors() {
        let ctx = test_context();
        register(&ctx);
        for kind in [
            "subscription",
            "subscription-publish-form",
            "subscription-feed",
        ] {
            assert!(
                ctx.inspector_registry().get(kind).is_some(),
                "missing inspector kind: {kind}"
            );
        }
    }

    #[test]
    fn register_is_idempotent_on_factory() {
        let ctx = test_context();
        register(&ctx);
        register(&ctx);
        assert_eq!(ctx.factory_registry().len(), 1);
    }

    // ── Cross-app composition: bounty-state notifications ───────────────

    #[test]
    fn bounty_state_payload_hash_is_deterministic() {
        let id = [9u8; 32];
        let actor = [11u8; 32];
        let a = bounty_state_payload_hash(&id, BountyState::Posted, BountyState::Claimed, &actor);
        let b = bounty_state_payload_hash(&id, BountyState::Posted, BountyState::Claimed, &actor);
        assert_eq!(a, b);
    }

    #[test]
    fn bounty_state_payload_hash_distinguishes_transitions() {
        let id = [9u8; 32];
        let actor = [11u8; 32];
        let claim =
            bounty_state_payload_hash(&id, BountyState::Posted, BountyState::Claimed, &actor);
        let fulfill =
            bounty_state_payload_hash(&id, BountyState::Claimed, BountyState::Fulfilled, &actor);
        let settle =
            bounty_state_payload_hash(&id, BountyState::Fulfilled, BountyState::Settled, &actor);
        assert_ne!(claim, fulfill);
        assert_ne!(fulfill, settle);
        assert_ne!(claim, settle);
    }

    #[test]
    fn bounty_state_payload_hash_distinguishes_actors() {
        let id = [9u8; 32];
        let a1 =
            bounty_state_payload_hash(&id, BountyState::Posted, BountyState::Claimed, &[1u8; 32]);
        let a2 =
            bounty_state_payload_hash(&id, BountyState::Posted, BountyState::Claimed, &[2u8; 32]);
        assert_ne!(a1, a2);
    }

    #[test]
    fn bounty_state_payload_hash_distinguishes_bounties() {
        let actor = [11u8; 32];
        let h1 = bounty_state_payload_hash(
            &[1u8; 32],
            BountyState::Posted,
            BountyState::Claimed,
            &actor,
        );
        let h2 = bounty_state_payload_hash(
            &[2u8; 32],
            BountyState::Posted,
            BountyState::Claimed,
            &actor,
        );
        assert_ne!(h1, h2);
    }

    #[test]
    fn build_bounty_state_publish_action_emits_bounty_payload_hash() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let bounty_id = blake3_field(b"CVE-2025-1234");
        let actor_hash = blake3_field(b"dan-pk");
        let new_head = u64_field(1);
        let new_root = blake3_field(b"queue-root-1");

        let action = build_bounty_state_publish_action(
            &cipherclerk,
            cell,
            new_head,
            new_root,
            &bounty_id,
            BountyState::Claimed,
            BountyState::Fulfilled,
            &actor_hash,
        );

        assert_eq!(action.method, symbol("publish"));
        // Payload-bearing SetField is the third effect (LATEST_PAYLOAD_SLOT).
        match &action.effects[2] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, LATEST_PAYLOAD_SLOT as usize);
                assert_eq!(
                    *value,
                    bounty_state_payload_hash(
                        &bounty_id,
                        BountyState::Claimed,
                        BountyState::Fulfilled,
                        &actor_hash
                    )
                );
            }
            other => panic!("expected SetField on LATEST_PAYLOAD_SLOT, got {other:?}"),
        }
    }

    #[test]
    fn bounty_state_tag_field_distinguishes_states() {
        let states = [
            BountyState::Posted,
            BountyState::Claimed,
            BountyState::Fulfilled,
            BountyState::Settled,
            BountyState::Canceled,
        ];
        for i in 0..states.len() {
            for j in (i + 1)..states.len() {
                assert_ne!(states[i].tag_field(), states[j].tag_field());
            }
        }
    }
}
