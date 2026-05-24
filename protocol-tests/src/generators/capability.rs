//! Strategies for generating capabilities and `AuthRequired` levels.
//!
//! Used directly by `capability_attenuation` / `facet_attenuation`
//! invariants (currently stubbed) and indirectly by the open-ledger setup
//! in [`super::cell`].

use proptest::prelude::*;
use pyana_cell::AuthRequired;

/// Strategy: any non-`Impossible` `AuthRequired` level.
///
/// We exclude `Impossible` from generators feeding executor input because
/// the executor flat-rejects any action requiring an impossible permission
/// — exercising that path doesn't tell us anything about *invariants*,
/// only about rejection.
pub fn arb_auth_required() -> impl Strategy<Value = AuthRequired> {
    prop_oneof![
        Just(AuthRequired::None),
        Just(AuthRequired::Signature),
        Just(AuthRequired::Proof),
        Just(AuthRequired::Either),
    ]
}

/// Strategy: pairs `(parent, child)` of `AuthRequired` such that `child` is
/// a valid attenuation of `parent` (narrower-or-equal). Useful for the
/// capability attenuation invariant when it is implemented.
pub fn arb_attenuation_pair() -> impl Strategy<Value = (AuthRequired, AuthRequired)> {
    arb_auth_required().prop_flat_map(|parent| {
        let attenuations = attenuations_of(&parent);
        let parent_clone = parent.clone();
        proptest::sample::select(attenuations).prop_map(move |child| (parent_clone.clone(), child))
    })
}

/// Enumerate every `AuthRequired` strictly narrower than or equal to
/// `parent` (including parent itself, including `Impossible` as the bottom).
pub fn attenuations_of(parent: &AuthRequired) -> Vec<AuthRequired> {
    let mut out = Vec::new();
    for candidate in [
        AuthRequired::None,
        AuthRequired::Signature,
        AuthRequired::Proof,
        AuthRequired::Either,
        AuthRequired::Impossible,
    ] {
        if candidate.is_narrower_or_equal(parent) {
            out.push(candidate);
        }
    }
    out
}
