//! Compile-time canaries for SDK-root compatibility exports used by downstream crates.

use dregg_sdk::{Attenuation, AuthRequest, BudgetSpec, CellId, SignedTurn};

const _: Option<(Attenuation, AuthRequest, BudgetSpec, CellId, SignedTurn)> = None;
