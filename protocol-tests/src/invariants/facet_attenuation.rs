//! Facet attenuation invariant. **STUB.**
//!
//! > For any delegated `CapabilityRef`, the child's `allowed_effects`
//! > bitmask is a subset of the parent's. No bit set in child not set in
//! > parent.
//!
//! ## What this test would check
//!
//! Generate:
//! - A parent `EffectMask` (random `u32`).
//! - A child `EffectMask` that the strategy will sometimes generate as a
//!   subset, sometimes as a superset, of the parent.
//!
//! Construct a delegation operation (likely `Effect::GrantCapability` with
//! a `CapabilityRef` carrying `allowed_effects = Some(child_mask)`) and
//! execute. INVARIANT: success iff `(child_mask & !parent_mask) == 0`,
//! i.e. `child_mask` has no bits set that aren't set in `parent_mask`.
//!
//! Also (negative direction): for any cell that *does* hold a faceted cap,
//! attempting `ExerciseViaCapability` for an effect whose kind-bit is
//! outside the mask must reject.
//!
//! ## Why stubbed
//!
//! Requires plumbing `is_facet_attenuation` checks through a generator
//! that builds `Effect::GrantCapability` with the faceted-cap form. The
//! cell crate exports `is_facet_attenuation` (see `cell/src/facet.rs`),
//! so this is mechanical — just out of session scope.

use crate::Invariant;

pub struct FacetAttenuation;

impl Invariant for FacetAttenuation {
    const NAME: &'static str = "facet_attenuation";
    const DESCRIPTION: &'static str =
        "delegated CapabilityRef.allowed_effects masks are bitwise-subset of the granter's mask";
}

#[test]
#[ignore = "stubbed: implement in next session — see module docs"]
fn facet_attenuation_holds() {
    unimplemented!(
        "Generate (parent_mask, child_mask) u32 pairs; execute a Grant of a faceted \
         CapabilityRef; assert is_facet_attenuation(parent, child) is equivalent to executor accept."
    );
}
