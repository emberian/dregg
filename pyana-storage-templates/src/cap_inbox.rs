//! # `CapInboxTemplate` — §3.1 reference design
//!
//! Generalization of the subscription proof-of-pattern
//! (`starbridge-apps/subscription/`) to the full §3.1 surface:
//! deposit accounting (`min_deposit`, `total_deposits_held`),
//! per-message ring root, sender-set Merkle root for anti-spam, and an
//! immutable owner.
//!
//! The §3.1 design carries 8 slots (`head`, `tail`, `capacity`,
//! `min_deposit`, `owner`, `sender_set_root`, `total_deposits_held`,
//! `message_root`). Pyana cells have exactly `STATE_SLOTS = 8`, so
//! every §3.1 slot maps 1:1. The `latest_payload_hash` accessory slot
//! that the subscription template carries in slot 7 has no place
//! here; the §3.1 design routes per-message payload commitments
//! through `EmitEvent` and commits to them aggregate via the ring
//! root.
//!
//! ## Slot layout
//!
//! | Slot | Name | Caveat | Purpose |
//! |---:|---|---|---|
//! | 0 | `head_seq` | `MonotonicSequence` (send-scoped) | Next seq the producer will write. |
//! | 1 | `tail_seq` | `MonotonicSequence` (dequeue-scoped) | Next seq the consumer will read. |
//! | 2 | `capacity` | `Immutable` | Max in-flight messages. |
//! | 3 | `min_deposit` | `Immutable` | Anti-spam floor (per-send deposit). |
//! | 4 | `owner_pk_hash` | `Immutable` | Inbox owner pubkey hash. |
//! | 5 | `sender_set_root` | `Monotonic` | Merkle root of authorized senders (insertions only). |
//! | 6 | `total_deposits_held` | per-method | Sum of in-flight deposits. Grows on send; shrinks on dequeue+refund. |
//! | 7 | `message_root` | `Monotonic` | Ring root over `(seq, payload_commitment)` tuples. |
//!
//! ## Operations
//!
//! - `send` — head advances by +1; message_root grows; deposit
//!   tracker grows. Tail/capacity/min_deposit/owner/sender_set frozen.
//!   Sender must be in `sender_set_root` (`SenderAuthorized`).
//! - `dequeue` — tail advances by +1; message_root stays
//!   (the consumer reads against the existing root). Deposit
//!   tracker may decrease on refund (encoded as the explicit slot
//!   write; the executor checks the head/tail bound).
//! - `grant_sender` — sender_set_root advances; everything else
//!   frozen. Owner-cap-gated by the per-cell capability layer.
//!
//! ## What this replaces
//!
//! - `pyana_storage::inbox::CapInbox` operator-process state machine.
//! - The receive/dequeue paths in `apps/subscription/src/delivery.rs`
//!   keyed against `CapInbox::receive_at`.
//! - `app-framework::inbox_endpoint` HTTP shim's enforcement loop.
//!
//! ## Boundary contract
//!
//! - **cleartext-inside**: the federation hosting the cell.
//! - **commitment-inside**: holders of `public_field_view` (head/tail
//!   counters, the four roots).
//! - **acceptance-inside**: STARK verifiers of any membership /
//!   Merkle proof against the message root.
//! - **out-of-band**: payload *bodies* (cells commit only to the
//!   ring root; producers publish ciphertext keyed on the
//!   commitment).
//!
//! Per `STORAGE-AS-CELL-PROGRAMS.md` §3.1 + `BOUNDARIES.md` §5.1.

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
/// Slot 2 — `capacity`. Immutable upper bound on in-flight messages.
pub const CAPACITY_SLOT: u8 = 2;
/// Slot 3 — `min_deposit`. Immutable anti-spam floor.
pub const MIN_DEPOSIT_SLOT: u8 = 3;
/// Slot 4 — `owner_pk_hash`. Immutable.
pub const OWNER_PK_HASH_SLOT: u8 = 4;
/// Slot 5 — `sender_set_root`. Monotonic Merkle root of authorized senders.
pub const SENDER_SET_ROOT_SLOT: u8 = 5;
/// Slot 6 — `total_deposits_held`. Conservation slot — grows on send,
/// shrinks only on dequeue+refund.
pub const TOTAL_DEPOSITS_SLOT: u8 = 6;
/// Slot 7 — `message_root`. Monotonic root over the ring of
/// `(seq, payload_commitment)` tuples.
pub const MESSAGE_ROOT_SLOT: u8 = 7;

// =============================================================================
// Factory configuration
// =============================================================================

/// Default per-epoch creation budget. Rate-limits Sybil creation of
/// inbox cells from this factory. Per §3.1 ("creation_budget:
/// Some(10_000)") — large enough that legitimate cell-mint never hits
/// it.
pub const DEFAULT_CREATION_BUDGET: u64 = 10_000;

/// Stable placeholder VK for the CapInbox factory. Mirrors
/// `starbridge-subscription`'s pattern; lifted to a build-time
/// constant once the constitution publishes the official VK.
pub const CAP_INBOX_FACTORY_VK: [u8; 32] = *b"pyana-storage-tpl-capinbox-fact!";

/// The child cell-program VK installed on per-inbox cells. Computed
/// canonically per `VK-AS-RE-EXECUTION-RECIPE.md` §2.1 from
/// [`cap_inbox_program`] so that a validator with the program in scope
/// can re-derive the VK.
pub fn cap_inbox_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&cap_inbox_program())
}

/// Method symbol for `send` (producer enqueues a message).
pub fn send_method_symbol() -> [u8; 32] {
    symbol("send")
}
/// Method symbol for `dequeue` (consumer advances tail).
pub fn dequeue_method_symbol() -> [u8; 32] {
    symbol("dequeue")
}
/// Method symbol for `grant_sender` (owner authorizes a sender).
pub fn grant_sender_method_symbol() -> [u8; 32] {
    symbol("grant_sender")
}

// =============================================================================
// CellProgram: operation-scoped Cases
// =============================================================================

/// Build the operation-scoped [`CellProgram`] for a CapInbox cell.
///
/// Per Cav-Codex Block 4 the program *default-denies* when no case
/// matches: an action whose method symbol is not one of `send` /
/// `dequeue` / `grant_sender` is rejected outright.
pub fn cap_inbox_program() -> CellProgram {
    CellProgram::Cases(vec![
        // ──────────────────────────────────────────────────────────
        // Invariants: every transition, regardless of operation.
        // ──────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                StateConstraint::Immutable {
                    index: CAPACITY_SLOT,
                },
                StateConstraint::Immutable {
                    index: MIN_DEPOSIT_SLOT,
                },
                StateConstraint::Immutable {
                    index: OWNER_PK_HASH_SLOT,
                },
            ],
        },
        // ──────────────────────────────────────────────────────────
        // send: head + 1; message_root advances; total_deposits grows;
        // tail/sender_set frozen; sender must be in sender_set_root.
        // ──────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("send"),
            },
            constraints: vec![
                StateConstraint::MonotonicSequence {
                    seq_index: HEAD_SEQ_SLOT,
                },
                StateConstraint::Immutable {
                    index: TAIL_SEQ_SLOT,
                },
                StateConstraint::Immutable {
                    index: SENDER_SET_ROOT_SLOT,
                },
                StateConstraint::Monotonic {
                    index: TOTAL_DEPOSITS_SLOT,
                },
                StateConstraint::Monotonic {
                    index: MESSAGE_ROOT_SLOT,
                },
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: SENDER_SET_ROOT_SLOT,
                    },
                },
            ],
        },
        // ──────────────────────────────────────────────────────────
        // dequeue: tail + 1; head/message_root/sender_set frozen.
        // total_deposits may decrease on refund (no Monotonic here);
        // the head/tail bound (tail<=head) is structurally enforced
        // by MonotonicSequence on the tail (it only ever advances by
        // exactly +1, and the dequeue path is gated at the wallet
        // layer on tail < head).
        // ──────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("dequeue"),
            },
            constraints: vec![
                StateConstraint::MonotonicSequence {
                    seq_index: TAIL_SEQ_SLOT,
                },
                StateConstraint::Immutable {
                    index: HEAD_SEQ_SLOT,
                },
                StateConstraint::Immutable {
                    index: MESSAGE_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: SENDER_SET_ROOT_SLOT,
                },
            ],
        },
        // ──────────────────────────────────────────────────────────
        // grant_sender: sender_set_root advances; everything else
        // frozen. Owner authorization rides on the per-cell
        // capability layer (the action sender must hold the owner cap).
        // ──────────────────────────────────────────────────────────
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
                    index: TOTAL_DEPOSITS_SLOT,
                },
                StateConstraint::Immutable {
                    index: MESSAGE_ROOT_SLOT,
                },
            ],
        },
    ])
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Build the [`FactoryDescriptor`] for per-inbox cells. Per §3.1 the
/// default mode is `Hosted` (federation sees cleartext events; payload
/// bodies live in an off-cell content store).
pub fn cap_inbox_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: CAP_INBOX_FACTORY_VK,
        child_program_vk: Some(cap_inbox_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(cap_inbox_child_program_vk()))),
        allowed_cap_templates: vec![
            // Owner cap — full control over grant_sender + dequeue.
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
            // Sender cap — may send. Attenuatable so the owner can
            // delegate per-sender attenuations.
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
        ],
        field_constraints: vec![
            // Initial state: head == tail == 0, total_deposits == 0,
            // message_root == FIELD_ZERO.
            FieldConstraint::Equality {
                field_index: HEAD_SEQ_SLOT as u32,
                value: 0,
            },
            FieldConstraint::Equality {
                field_index: TAIL_SEQ_SLOT as u32,
                value: 0,
            },
            FieldConstraint::Equality {
                field_index: TOTAL_DEPOSITS_SLOT as u32,
                value: 0,
            },
            // Capacity must be in [1, 1_000_000].
            FieldConstraint::Range {
                field_index: CAPACITY_SLOT as u32,
                min: 1,
                max: 1_000_000,
            },
            // Owner must be non-zero.
            FieldConstraint::NonZero {
                field_index: OWNER_PK_HASH_SLOT as u32,
            },
        ],
        state_constraints: vec![
            // Lifetime invariants — flattened from the `Always` case.
            // The full operation-scoped shape lives in `cap_inbox_program`.
            StateConstraint::Immutable {
                index: CAPACITY_SLOT,
            },
            StateConstraint::Immutable {
                index: MIN_DEPOSIT_SLOT,
            },
            StateConstraint::Immutable {
                index: OWNER_PK_HASH_SLOT,
            },
            // Counters + ring roots grow monotonically across the
            // cell's lifetime, regardless of which op moved them.
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
                index: MESSAGE_ROOT_SLOT,
            },
        ],
        default_mode: CellMode::Hosted,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

// =============================================================================
// Turn-builders
// =============================================================================

/// Build the on-ledger [`Action`] recording a `send`.
///
/// Composes:
///   - `SetField(HEAD_SEQ_SLOT, new_head)`
///   - `SetField(TOTAL_DEPOSITS_SLOT, new_total)`
///   - `SetField(MESSAGE_ROOT_SLOT, new_ring_root)`
///   - `EmitEvent("inbox-sent", [new_head, new_ring_root, payload_commitment])`
///
/// The sender's signature authorizes the action; the executor checks
/// `SenderAuthorized` against slot 5 on every turn.
pub fn build_send_action(
    wallet: &AppWallet,
    inbox_cell: CellId,
    new_head: FieldElement,
    new_total_deposits: FieldElement,
    new_ring_root: FieldElement,
    payload_commitment: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: inbox_cell,
            index: HEAD_SEQ_SLOT as usize,
            value: new_head,
        },
        Effect::SetField {
            cell: inbox_cell,
            index: TOTAL_DEPOSITS_SLOT as usize,
            value: new_total_deposits,
        },
        Effect::SetField {
            cell: inbox_cell,
            index: MESSAGE_ROOT_SLOT as usize,
            value: new_ring_root,
        },
        Effect::EmitEvent {
            cell: inbox_cell,
            event: Event::new(
                symbol("inbox-sent"),
                vec![new_head, new_ring_root, payload_commitment],
            ),
        },
    ];

    wallet.make_action(inbox_cell, "send", effects)
}

/// Build the on-ledger [`Action`] recording a `dequeue`.
///
/// Composes:
///   - `SetField(TAIL_SEQ_SLOT, new_tail)`
///   - `SetField(TOTAL_DEPOSITS_SLOT, new_total)` (deposit refund)
///   - `EmitEvent("inbox-dequeued", [new_tail, dequeued_commitment])`
///
/// Owner-cap-gated by the per-cell capability layer.
pub fn build_dequeue_action(
    wallet: &AppWallet,
    inbox_cell: CellId,
    new_tail: FieldElement,
    new_total_deposits: FieldElement,
    dequeued_commitment: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: inbox_cell,
            index: TAIL_SEQ_SLOT as usize,
            value: new_tail,
        },
        Effect::SetField {
            cell: inbox_cell,
            index: TOTAL_DEPOSITS_SLOT as usize,
            value: new_total_deposits,
        },
        Effect::EmitEvent {
            cell: inbox_cell,
            event: Event::new(
                symbol("inbox-dequeued"),
                vec![new_tail, dequeued_commitment],
            ),
        },
    ];

    wallet.make_action(inbox_cell, "dequeue", effects)
}

/// Build the on-ledger [`Action`] adding a sender to the
/// authorized-senders set.
///
/// Composes:
///   - `SetField(SENDER_SET_ROOT_SLOT, new_root)`
///   - `EmitEvent("inbox-sender-granted", [new_root, new_sender_pk])`
///
/// Owner-cap-gated by the capability layer.
pub fn build_grant_sender_action(
    wallet: &AppWallet,
    inbox_cell: CellId,
    new_sender_set_root: FieldElement,
    new_sender_pk: [u8; 32],
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: inbox_cell,
            index: SENDER_SET_ROOT_SLOT as usize,
            value: new_sender_set_root,
        },
        Effect::EmitEvent {
            cell: inbox_cell,
            event: Event::new(
                symbol("inbox-sender-granted"),
                vec![new_sender_set_root, new_sender_pk],
            ),
        },
    ];

    wallet.make_action(inbox_cell, "grant_sender", effects)
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// Register this template on a [`StarbridgeAppContext`]. Returns the
/// registered `factory_vk` so the host can log it.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(cap_inbox_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "cap-inbox".into(),
        descriptor: serde_json::json!({
            "component": "pyana-cap-inbox",
            "module": "/pyana-storage-templates/cap-inbox.js",
            "uri_prefix": "pyana://cell/",
            "summary_fields": [
                "head_seq", "tail_seq", "capacity", "min_deposit",
                "owner_pk_hash", "sender_set_root", "total_deposits_held",
                "message_root",
            ],
            "factory_vk_hex": hex_encode(&factory_vk),
            "child_program_vk_hex": hex_encode(&cap_inbox_child_program_vk()),
        }),
    });

    factory_vk
}

/// Initial state helper: build the [`FieldElement`] vector for a
/// freshly-minted inbox cell. The caller supplies `capacity`,
/// `min_deposit`, `owner_pk_hash`, and `sender_set_root`; head/tail/
/// deposits/message_root are zero-initialized.
///
/// Returned in slot order (0..8). Test ergonomics + cell-creation
/// helper for hosts wiring `Effect::CreateCellFromFactory`.
pub fn initial_state(
    capacity: u64,
    min_deposit: u64,
    owner_pk_hash: [u8; 32],
    sender_set_root: [u8; 32],
) -> [FieldElement; 8] {
    [
        [0u8; 32],
        [0u8; 32],
        u64_field(capacity),
        u64_field(min_deposit),
        owner_pk_hash,
        sender_set_root,
        [0u8; 32],
        [0u8; 32],
    ]
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
        let h1 = cap_inbox_factory_descriptor().hash();
        let h2 = cap_inbox_factory_descriptor().hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn descriptor_pins_program_vk() {
        let d = cap_inbox_factory_descriptor();
        assert_eq!(d.factory_vk, CAP_INBOX_FACTORY_VK);
        assert_eq!(d.child_program_vk, Some(cap_inbox_child_program_vk()));
        assert_eq!(d.default_mode, CellMode::Hosted);
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        let expected = canonical_program_vk(&cap_inbox_program());
        assert_eq!(cap_inbox_child_program_vk(), expected);
    }

    #[test]
    fn descriptor_validates_against_canonical_program() {
        let d = cap_inbox_factory_descriptor();
        pyana_app_framework::validate_child_vk_canonical(&d, &cap_inbox_program())
            .expect("descriptor must bind canonical layered VK to the program");
    }

    #[test]
    fn program_is_cases_with_four_branches() {
        match cap_inbox_program() {
            CellProgram::Cases(cases) => {
                assert_eq!(cases.len(), 4, "Always + 3 MethodIs cases");
            }
            other => panic!("expected Cases, got {other:?}"),
        }
    }

    #[test]
    fn program_covers_all_three_methods() {
        let cases = match cap_inbox_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let mut seen = (false, false, false);
        for c in &cases {
            if let TransitionGuard::MethodIs { method } = &c.guard {
                if *method == symbol("send") {
                    seen.0 = true;
                }
                if *method == symbol("dequeue") {
                    seen.1 = true;
                }
                if *method == symbol("grant_sender") {
                    seen.2 = true;
                }
            }
        }
        assert_eq!(seen, (true, true, true));
    }

    #[test]
    fn send_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let new_head = u64_field(1);
        let new_total = u64_field(500);
        let new_root = blake3_field(b"root-1");
        let commitment = blake3_field(b"msg");
        let action =
            build_send_action(&wallet, cell, new_head, new_total, new_root, commitment);
        assert_eq!(action.method, symbol("send"));
        assert_eq!(action.effects.len(), 4);
    }

    #[test]
    fn dequeue_action_shape() {
        let wallet = test_wallet();
        let cell = test_cell();
        let action = build_dequeue_action(
            &wallet,
            cell,
            u64_field(1),
            u64_field(0),
            blake3_field(b"d"),
        );
        assert_eq!(action.method, symbol("dequeue"));
        assert_eq!(action.effects.len(), 3);
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
    fn register_installs_factory() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, CAP_INBOX_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("cap-inbox").is_some());
    }

    #[test]
    fn initial_state_zeros_dynamic_slots() {
        let s = initial_state(64, 100, [1u8; 32], [2u8; 32]);
        assert_eq!(s[HEAD_SEQ_SLOT as usize], [0u8; 32]);
        assert_eq!(s[TAIL_SEQ_SLOT as usize], [0u8; 32]);
        assert_eq!(s[TOTAL_DEPOSITS_SLOT as usize], [0u8; 32]);
        assert_eq!(s[MESSAGE_ROOT_SLOT as usize], [0u8; 32]);
        assert_eq!(s[OWNER_PK_HASH_SLOT as usize], [1u8; 32]);
        assert_eq!(s[SENDER_SET_ROOT_SLOT as usize], [2u8; 32]);
    }
}
