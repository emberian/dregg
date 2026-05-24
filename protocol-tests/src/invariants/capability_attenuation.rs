//! Capability monotone attenuation invariant. **STUB.**
//!
//! > No turn can grant a capability that's broader than the granter's own
//! > held capability.
//!
//! ## What this test would check
//!
//! Generate:
//! - A ledger with `parent` and `recipient` cells.
//! - A `parent`-held capability with random `AuthRequired::P` permissions.
//! - A `Grant` turn from `parent` to `recipient` with random `Q`
//!   permissions.
//!
//! INVARIANT: After execution, if the grant succeeds, `Q.is_narrower_or_equal(&P)`
//! holds (the grant was attenuating). If `Q` is *wider* than `P` (not
//! narrower-or-equal), the executor must reject — never granting wider
//! capabilities than the parent holds.
//!
//! ## Why stubbed
//!
//! The capability-grant code path requires:
//! - Setting up `parent` with the right initial c-list entry (and a
//!   self-cap for `from`).
//! - Constructing the `Effect::GrantCapability` action with the correct
//!   `CapabilityRef` target/permissions.
//! - Configuring `parent`'s `Permissions { delegate: ... }` to allow the
//!   grant under `Authorization::Unchecked`.
//!
//! That's straightforward but it's a wider strategy surface than the three
//! initial invariants and we're scoping this session to "ship 3, stub 4".
//!
//! Existing test that does roughly this in scenario form:
//! `turn/tests/proptest_invariants.rs::proptest_capability_confinement_holds`.

use crate::Invariant;

pub struct CapabilityAttenuation;

impl Invariant for CapabilityAttenuation {
    const NAME: &'static str = "capability_attenuation";
    const DESCRIPTION: &'static str =
        "granted capability permissions are always narrower-or-equal to the granter's held permissions";
}

#[test]
#[ignore = "stubbed: implement in next session — see module docs"]
fn capability_attenuation_holds() {
    unimplemented!(
        "Generate (parent_perms, grant_perms) pairs; execute Effect::GrantCapability \
         through TurnExecutor; assert grant succeeds iff grant_perms.is_narrower_or_equal(&parent_perms)."
    );
}
