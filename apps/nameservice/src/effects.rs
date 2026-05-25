//! Effect emission for nameservice.
//!
//! ## The userspace stance
//!
//! Apps are *userspace* — they should not reach past the framework into
//! `pyana_turn::builder::ActionBuilder` or hand-encode placeholder
//! signatures. This module is the canonical userspace pattern: it takes
//! a framework-issued [`AppCipherclerk`] and produces a real signed
//! [`Action`] carrying `Authorization::Signature(..)` — no `[0u8; 64]`,
//! no direct `pyana_turn::*` imports.
//!
//! ## Why no `Effect::RegisterName`?
//!
//! "Register a name" is *userspace policy*, not a pyana primitive. The
//! ledger only needs to see two things:
//!
//! 1. **A name binding** — `SetField(NAME_STORAGE_SLOT, name_hash)` —
//!    so the cell's state carries proof of the binding.
//! 2. **An event for off-chain indexers** — `EmitEvent("name-registered",
//!    [name_hash, owner_hash])`.
//!
//! If we needed *cell-program-enforced uniqueness* ("the slot at index
//! `(NAME_STORAGE_SLOT, name_hash)` may only be set if its prior value is
//! zero"), that's a **cell program caveat**, not a new `Effect` variant.
//! See `APPS-USERSPACE-GAPS.md` for the gap analysis on cell-side
//! caveats (the userspace primitive that isn't yet ergonomic from
//! apps).
//!
//! ## Receipt-chain visibility
//!
//! The action's `EmitEvent` row surfaces the registration to off-chain
//! indexers; the `SetField` row anchors the binding in the cell's
//! state. Both project to the Effect VM trace (per
//! `turn/src/executor.rs::convert_turn_effects_to_vm`), so the
//! registration is provable on the cell side.

use pyana_app_framework::{Action, AppCipherclerk, CellId, Effect, Event, FieldElement};

/// State field slot at which registered name hashes are stored. Picked
/// arbitrarily for now; a real deployment binds this to the registry
/// cell's published schema. Kept distinct from cell-defaults to avoid
/// collisions with `nonce` (slot 0) and `balance` (slot 1).
pub const NAME_STORAGE_SLOT: usize = 8;

/// Build the on-ledger [`Action`] that records a name registration.
///
/// The action carries two effects:
///
/// 1. `EmitEvent(cell=registry_cell, topic="name-registered", data=[name_hash, owner_hash])`
///    — surfaces the registration for off-chain indexers.
/// 2. `SetField(cell=registry_cell, index=NAME_STORAGE_SLOT, value=name_hash)`
///    — anchors the name binding in the cell's state field at the
///    pre-agreed storage slot.
///
/// The action is signed by the framework's [`AppCipherclerk`] — no placeholder
/// signatures, no direct `pyana_turn::builder::ActionBuilder` imports.
/// The signature binds to the cipherclerk's federation_id.
pub fn build_register_action(
    cipherclerk: &AppCipherclerk,
    registry_cell: CellId,
    name: &str,
    owner: [u8; 32],
) -> Action {
    let name_hash = blake3_field(name.as_bytes());
    let owner_hash = blake3_field(&owner);

    let effects = vec![
        Effect::EmitEvent {
            cell: registry_cell,
            event: Event::new(
                pyana_app_framework::symbol("name-registered"),
                vec![name_hash, owner_hash],
            ),
        },
        Effect::SetField {
            cell: registry_cell,
            index: NAME_STORAGE_SLOT,
            value: name_hash,
        },
    ];

    cipherclerk.make_action(registry_cell, "register_name", effects)
}

/// Hash arbitrary bytes into a [`FieldElement`] (32-byte) suitable for
/// effect data fields.
fn blake3_field(bytes: &[u8]) -> FieldElement {
    *blake3::hash(bytes).as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_app_framework::{AgentCipherclerk, Authorization, Effect};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
    }

    #[test]
    fn register_action_emits_event_and_setfield() {
        let cipherclerk = test_cipherclerk();
        let registry_cell = CellId::from_bytes([1u8; 32]);
        let action = build_register_action(&cipherclerk, registry_cell, "alice.pyana", [3u8; 32]);

        assert_eq!(action.effects.len(), 2);
        assert!(matches!(action.effects[0], Effect::EmitEvent { .. }));
        assert!(matches!(action.effects[1], Effect::SetField { .. }));
    }

    #[test]
    fn register_action_has_real_signature() {
        // The whole point of the userspace migration: actions carry a real
        // framework-issued signature, not a `[0u8; 64]` placeholder.
        let cipherclerk = test_cipherclerk();
        let registry_cell = CellId::from_bytes([1u8; 32]);
        let action = build_register_action(&cipherclerk, registry_cell, "alice.pyana", [3u8; 32]);
        match action.authorization {
            Authorization::Signature(a, b) => {
                assert!(
                    a != [0u8; 32] || b != [0u8; 32],
                    "signature must be non-zero (no [0u8; 64] placeholders!)"
                );
            }
            other => panic!("expected Signature variant, got {other:?}"),
        }
    }

    #[test]
    fn different_names_produce_different_setfield_values() {
        let cipherclerk = test_cipherclerk();
        let registry_cell = CellId::from_bytes([1u8; 32]);
        let a = build_register_action(&cipherclerk, registry_cell, "alice.pyana", [3u8; 32]);
        let b = build_register_action(&cipherclerk, registry_cell, "bob.pyana", [3u8; 32]);
        let pick = |action: &Action| match &action.effects[1] {
            Effect::SetField { value, .. } => *value,
            _ => panic!("unexpected effect"),
        };
        assert_ne!(pick(&a), pick(&b));
    }

    #[test]
    fn cipherclerk_signs_with_its_own_identity() {
        // Two different cipherclerks sign the same logical action with different
        // signatures — confirms the cipherclerk's identity is actually bound in.
        let cc1 = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let cc2 = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let cell = CellId::from_bytes([1u8; 32]);
        let a1 = build_register_action(&cc1, cell, "alice", [3u8; 32]);
        let a2 = build_register_action(&cc2, cell, "alice", [3u8; 32]);
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
}
