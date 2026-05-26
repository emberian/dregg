//! Strategies for generating individual `Effect` values.
//!
//! Scope note: the initial invariant set (balance conservation, nonce
//! monotonicity, receipt chain) only needs `Transfer` and `IncrementNonce`,
//! so that's all we expose. Future invariants (`facet_attenuation`,
//! `permission_enforcement`) will widen this once they're implemented.

use dregg_cell::CellId;
use dregg_turn::Effect;
use proptest::prelude::*;

/// Strategy: a `Transfer` effect between two cells in `ids`. Self-transfers
/// are not produced — they're either no-ops or rejected depending on
/// executor variant, and either way they're noise for the conservation
/// invariant.
pub fn arb_transfer_effect(ids: Vec<CellId>, max_amount: u64) -> impl Strategy<Value = Effect> {
    let n = ids.len();
    (0..n, 0..n, 1u64..=max_amount).prop_filter_map(
        "no self-transfers",
        move |(from_idx, to_idx, amount)| {
            if from_idx == to_idx {
                None
            } else {
                Some(Effect::Transfer {
                    from: ids[from_idx],
                    to: ids[to_idx],
                    amount,
                })
            }
        },
    )
}

/// Strategy: an `IncrementNonce` effect targeting a cell from `ids`.
pub fn arb_increment_nonce_effect(ids: Vec<CellId>) -> impl Strategy<Value = Effect> {
    let n = ids.len();
    (0..n).prop_map(move |idx| Effect::IncrementNonce { cell: ids[idx] })
}
