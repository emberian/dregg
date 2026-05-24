//! Re-derive the `gen_air` descriptor's accept/reject from the IR-shape
//! using `pyana_dsl_runtime::diff_witness`.
//!
//! The AIR descriptor (returned by `{name}_air_constraints()`) is a
//! topology-only representation: column counts, constraint variants. The
//! semantic predicate isn't *in* the descriptor — it's in the IR walked
//! by the generator. To check the AIR backend in agreement with the
//! others we therefore (a) confirm the descriptor's gross shape matches
//! what `gen_air` should have emitted for this requirement list, and (b)
//! re-derive the accept/reject decision via the IR-aligned
//! [`diff_witness`](pyana_dsl_runtime::diff_witness) primitives — the
//! same helpers `gen_diff_test` uses to algebraically witness each
//! constraint.

use pyana_dsl_runtime::diff_witness::{
    DiffOutcome, DiffValue, check_equal, check_ge, check_le, check_membership, check_not_equal,
    combine_and,
};
use pyana_dsl_runtime::{AirConstraintSet, Constraint};

use crate::predicates::Requirement;

pub fn evaluate(
    descriptor: &AirConstraintSet,
    requirements: &[Requirement],
) -> Result<bool, String> {
    // Structural sanity: requirement count matches descriptor constraint
    // count. Bytes-equality + Bytes-non-equality both emit a single
    // Constraint each — same as their u64 counterparts.
    if descriptor.constraints.len() != requirements.len() {
        return Err(format!(
            "AIR constraint count mismatch: descriptor has {}, expected {}",
            descriptor.constraints.len(),
            requirements.len()
        ));
    }
    // Spot-check constraint variant matches the requirement variant.
    for (req, c) in requirements.iter().zip(&descriptor.constraints) {
        match (req, c) {
            (
                Requirement::LessEqualU64(..) | Requirement::GreaterEqualU64(..),
                Constraint::RangeCheck { .. },
            )
            | (
                Requirement::EqualU64(..) | Requirement::EqualBytes32(..),
                Constraint::Equality { .. },
            )
            | (
                Requirement::NotEqualU64(..) | Requirement::NotEqualBytes32(..),
                Constraint::NonEquality { .. },
            )
            | (Requirement::Membership { .. }, Constraint::MerkleMembership { .. }) => {}
            (req, c) => {
                return Err(format!(
                    "AIR constraint variant mismatch: requirement {req:?} produced {c:?}",
                ));
            }
        }
    }

    // Re-derive accept/reject.
    let outcomes: Vec<DiffOutcome> = requirements
        .iter()
        .map(|req| match req {
            Requirement::LessEqualU64(l, r) => check_le(*l, *r),
            Requirement::GreaterEqualU64(l, r) => check_ge(*l, *r),
            Requirement::EqualU64(l, r) => check_equal(&DiffValue::U64(*l), &DiffValue::U64(*r)),
            Requirement::NotEqualU64(l, r) => {
                check_not_equal(&DiffValue::U64(*l), &DiffValue::U64(*r))
            }
            Requirement::EqualBytes32(l, r) => {
                check_equal(&DiffValue::Bytes32(*l), &DiffValue::Bytes32(*r))
            }
            Requirement::NotEqualBytes32(l, r) => {
                check_not_equal(&DiffValue::Bytes32(*l), &DiffValue::Bytes32(*r))
            }
            Requirement::Membership { set, element } => check_membership(set, *element),
        })
        .collect();

    Ok(matches!(combine_and(outcomes), DiffOutcome::Accept))
}
