//! Permission enforcement invariant. **STUB.**
//!
//! > No effect runs against a cell whose permissions reject the action's
//! > authorization mode.
//!
//! ## What this test would check
//!
//! Generate:
//! - A target cell with `Permissions { effect_kind: AuthRequired::P }`.
//! - A turn whose action carries `Authorization::A` where `A` does NOT
//!   satisfy `P` (e.g. `A = Unchecked` while `P = Signature`, or
//!   `A = Signature` while `P = Proof`).
//!
//! INVARIANT: the executor must reject this turn at the action level. The
//! effect must NOT be applied — verify post-execution that the cell's
//! state is unchanged.
//!
//! Cover all 8 permission slots: `send`, `receive`, `set_state`,
//! `set_permissions`, `set_verification_key`, `increment_nonce`,
//! `delegate`, `access`.
//!
//! ## Why stubbed
//!
//! Cross-product (8 slots × 5 AuthRequired levels × 5 Authorization
//! kinds) is a non-trivial generator design — needs care so the
//! generator produces a turn that ACTUALLY exercises that permission
//! check (the executor has different code paths per effect type, and
//! some effects check multiple permissions). Punted to next session.

use crate::Invariant;

pub struct PermissionEnforcement;

impl Invariant for PermissionEnforcement {
    const NAME: &'static str = "permission_enforcement";
    const DESCRIPTION: &'static str =
        "executor rejects every action whose authorization does not satisfy the target cell's permission for that action kind";
}

#[test]
#[ignore = "stubbed: implement in next session — see module docs"]
fn permission_enforcement_holds() {
    unimplemented!(
        "For each permission slot × AuthRequired level × Authorization kind, build a turn \
         and assert executor accept iff Authorization satisfies Permission.AuthRequired."
    );
}
