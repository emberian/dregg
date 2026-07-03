//! **The spend cap** — a per-account ceiling on the proven rate-limited-allowance
//! capacity ([`dregg_cell::allowance`], `cell/src/allowance.rs`).
//!
//! ## A spend cap IS an allowance ceiling — no new primitive
//!
//! A billing spend cap says: this account may be charged at most `cap` value within a
//! billing period. That is *exactly* the rate-limited-allowance ceiling the substrate
//! already proves: the ceiling is committed into the cell's sorted-Poseidon2 heap, a
//! charge is bounded by the committed `spent_this_epoch` (`spent + amount ≤ limit`), and
//! the counter cannot be forged down to fake headroom nor refilled early (the epoch is
//! DERIVED from the block, not asserted). A [`SpendCap`] models one billing period as a
//! single allowance epoch: a **flat ceiling within the period** (a large `epoch_length`
//! so nothing refills mid-period — the whole horizon is one budget window), refilling only
//! when a genuinely later period is opened. This is the shape a prior imperative billing
//! module's `limits.rs` enforced through a replenishing-budget ceiling, re-homed onto the
//! native, forge-detecting [`AllowanceState::check_spend`].
//!
//! ## The 402 shape
//!
//! A charge that fits under the cap is **admitted** (the committed counter advances); a
//! charge that would exceed the cap is **refused** ([`SpendDecision::Refused`]) — nothing
//! is drawn, so new spend is genuinely stopped. That refusal IS the "402 Payment Required"
//! shape: the cell reports the cap, the accrued spend, and the attempted amount, and moves
//! no value. The executor-enforced twin of this refusal (a charge *turn* the kernel
//! rejects when it would push the mirrored spent slot over the ceiling) is
//! [`crate::charge_under_cap`] + the [`crate::cap_invariants`] `FieldLteField(spent ≤
//! cap)` tooth — this module is the forge-detecting ledger core the turn desugars over.

use dregg_cell::Cell;
use dregg_cell::allowance::{
    AllowanceError, AllowanceState, AllowanceTerms, Spend, open_allowance, remaining_at, spend,
};
use dregg_types::CellId;

/// A large per-period budget window: within one billing period the ceiling is FLAT (no
/// mid-period refill). A later period genuinely crosses the epoch boundary and refills. A
/// quarter of `i64::MAX` leaves ample headroom above any realistic period `start`.
pub const PERIOD_WINDOW_BLOCKS: i64 = i64::MAX / 4;

/// The outcome of one charge against a [`SpendCap`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpendDecision {
    /// The charge fit under the cap and was drawn. Carries the accrued spend after the
    /// charge and the remaining headroom under the cap.
    Admitted {
        /// The accrued spend within the period after this charge.
        spent_units: i64,
        /// The headroom still available under the cap.
        remaining_units: i64,
    },
    /// The charge would exceed the hard cap — **refused, nothing drawn** (the 402 shape).
    Refused {
        /// The hard cap (the per-period ceiling).
        cap_units: i64,
        /// The accrued spend at the moment of refusal (unchanged by the refusal).
        spent_units: i64,
        /// The amount the refused charge attempted.
        attempted: i64,
    },
}

impl SpendDecision {
    /// Whether the charge was admitted.
    pub fn is_admitted(&self) -> bool {
        matches!(self, SpendDecision::Admitted { .. })
    }

    /// Whether the charge was refused (the 402 shape).
    pub fn is_refused(&self) -> bool {
        matches!(self, SpendDecision::Refused { .. })
    }
}

/// A live **spend cap** — a [`dregg_cell::Cell`] carrying the proven rate-limited
/// allowance, plus the [`AllowanceTerms`] it was opened under. Every state-changing charge
/// routes through the proven capacity ([`open_allowance`] / [`spend`] /
/// [`AllowanceState::check_spend`]); no ceiling arithmetic lives here that the capacity
/// does not prove.
#[derive(Clone, Debug)]
pub struct SpendCap {
    /// The cap cell carrying the committed allowance ledger (terms digest, epoch cursor,
    /// `spent_this_epoch`, cumulative — all in the sorted-Poseidon2 heap).
    pub cell: Cell,
    /// The allowance terms in force (the ceiling, the period window, the start block).
    pub terms: AllowanceTerms,
}

/// Why a spend-cap operation could not even be attempted (distinct from the in-band
/// [`SpendDecision::Refused`], which is a well-formed over-cap 402).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CapError {
    /// The terms are ill-formed (non-positive ceiling / period).
    IllFormedTerms,
    /// A proven-capacity rejection other than the ceiling (a forged counter, stale epoch).
    Allowance(AllowanceError),
}

impl std::fmt::Display for CapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CapError::IllFormedTerms => write!(f, "spend-cap terms are not well-formed"),
            CapError::Allowance(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for CapError {}

impl SpendCap {
    /// **Open** a spend cap on a fresh cell for `account`, denominated in `asset`, with a
    /// per-period ceiling of `cap_units`, the period beginning at block `start`. Seals the
    /// allowance terms digest into the cell's committed heap and initializes the epoch
    /// cursor with nothing spent. Rejects a non-positive cap.
    pub fn open(
        account: CellId,
        asset: CellId,
        cap_units: i64,
        start: i64,
    ) -> Result<SpendCap, CapError> {
        let terms = AllowanceTerms::new(
            account,
            asset,
            cap_units,
            PERIOD_WINDOW_BLOCKS,
            start.max(0),
        );
        if !terms.is_well_formed() {
            return Err(CapError::IllFormedTerms);
        }
        let mut cell = Cell::with_balance(*account.as_bytes(), *asset.as_bytes(), 0);
        open_allowance(&mut cell, &terms).map_err(CapError::Allowance)?;
        Ok(SpendCap { cell, terms })
    }

    /// The hard cap (the per-period ceiling).
    pub fn cap(&self) -> i64 {
        self.terms.limit_per_epoch
    }

    /// The accrued spend within the current period (the committed `spent_this_epoch`).
    pub fn spent(&self) -> i64 {
        AllowanceState::read(&self.cell)
            .map(|s| s.spent_this_epoch)
            .unwrap_or(0)
    }

    /// The remaining headroom under the cap at `at_block`.
    pub fn remaining(&self, at_block: i64) -> i64 {
        match AllowanceState::read(&self.cell) {
            Ok(state) => remaining_at(&state, &self.terms, at_block),
            Err(_) => 0,
        }
    }

    /// **Charge** `amount` against the cap at `at_block`.
    ///
    /// A non-positive charge is a no-op admit. Otherwise the charge routes through the
    /// proven [`spend`]: under the cap it is admitted and the committed counter advances;
    /// at or over the cap it is **refused** ([`SpendDecision::Refused`] — the 402), and
    /// nothing is drawn (the proven capacity is fail-closed). A rejection that is NOT the
    /// ceiling (a stale epoch / forged terms) surfaces as [`CapError`].
    pub fn charge(&mut self, amount: i64, at_block: i64) -> Result<SpendDecision, CapError> {
        if amount <= 0 {
            return Ok(SpendDecision::Admitted {
                spent_units: self.spent(),
                remaining_units: self.remaining(at_block),
            });
        }
        let step = Spend { amount, at_block };
        match spend(&mut self.cell, &self.terms, &step) {
            Ok(_moved) => Ok(SpendDecision::Admitted {
                spent_units: self.spent(),
                remaining_units: self.remaining(at_block),
            }),
            Err(AllowanceError::ExceedsCeiling {
                spent,
                amount,
                limit,
            }) => Ok(SpendDecision::Refused {
                cap_units: limit,
                spent_units: spent,
                attempted: amount,
            }),
            Err(e) => Err(CapError::Allowance(e)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    /// Account cell 1, asset 9, cap 100, period starting at block 1000.
    fn cap100() -> SpendCap {
        SpendCap::open(cid(1), cid(9), 100, 1000).unwrap()
    }

    // ── THE HONEST PATH: charges under the cap are admitted and draw down ──
    #[test]
    fn charges_under_the_cap_are_admitted() {
        let mut c = cap100();
        assert_eq!(c.cap(), 100);

        match c.charge(40, 1500).unwrap() {
            SpendDecision::Admitted {
                spent_units,
                remaining_units,
            } => {
                assert_eq!(spent_units, 40);
                assert_eq!(remaining_units, 60);
            }
            other => panic!("expected admit, got {other:?}"),
        }
        // A second charge of 50 (40 + 50 = 90 ≤ 100) still fits.
        assert!(c.charge(50, 1600).unwrap().is_admitted());
        assert_eq!(c.spent(), 90);
    }

    // ── THE 402: a charge that would exceed the cap is refused, nothing drawn ──
    #[test]
    fn an_over_cap_charge_is_refused_nothing_drawn() {
        let mut c = cap100();
        assert!(c.charge(90, 1500).unwrap().is_admitted());
        assert_eq!(c.spent(), 90);

        // 20 more would exceed the 100 cap → refused, spend unchanged (the 402).
        match c.charge(20, 1600).unwrap() {
            SpendDecision::Refused {
                cap_units,
                spent_units,
                attempted,
            } => {
                assert_eq!(cap_units, 100);
                assert_eq!(spent_units, 90, "nothing drawn on a refusal");
                assert_eq!(attempted, 20);
            }
            other => panic!("expected a 402 refusal, got {other:?}"),
        }
        assert_eq!(c.spent(), 90, "the refused charge left spend untouched");

        // Exactly filling the cap is admitted; the very next unit is refused.
        assert!(c.charge(10, 1700).unwrap().is_admitted());
        assert_eq!(c.spent(), 100);
        assert!(c.charge(1, 1800).unwrap().is_refused());
        assert_eq!(c.remaining(1800), 0);
    }

    // ── the ceiling is bound into the commitment: a charge re-seals it ──
    #[test]
    fn charging_moves_the_committed_state() {
        let mut c = cap100();
        let before = c.cell.state_commitment();
        c.charge(40, 1500).unwrap();
        assert_ne!(
            before,
            c.cell.state_commitment(),
            "a charge re-seals the commitment"
        );
    }

    #[test]
    fn a_nonpositive_charge_is_a_noop_admit() {
        let mut c = cap100();
        assert!(c.charge(0, 1500).unwrap().is_admitted());
        assert_eq!(c.spent(), 0);
    }

    #[test]
    fn a_zero_cap_is_ill_formed() {
        assert!(matches!(
            SpendCap::open(cid(1), cid(9), 0, 1000),
            Err(CapError::IllFormedTerms)
        ));
    }
}
