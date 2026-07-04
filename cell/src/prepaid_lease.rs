//! Prepaid lease — a FUSED budget-escrow ⊗ obligation: a per-period rent discharge that ATOMICALLY
//! draws its rent from a sealed prepaid budget, so meter/pay DRIFT is unrepresentable.
//!
//! # The capacity (Track 2) — and the bug class it closes
//!
//! An autonomous agent living inside dregg leases resources: it owes `rent` every `period` blocks.
//! Today that lease is THREE separately-enforced pieces coupled only by a shared rent constant and
//! app control flow — a [`crate::obligation_standing`] meter (the per-period cursor), a payable
//! transfer (the draw), and a lapse backstop. "Budget never over-drawn" and "metered == drawn" are
//! NOT one theorem; they are maintained by DISCIPLINE. That gap is the meter/pay-DRIFT bug class:
//! the meter advances but the draw is skipped, or a draw happens with no metered period, and the two
//! ledgers silently diverge — caught (if ever) after the fact.
//!
//! A **prepaid lease** FUSES the two proven house-capacity reuse bases —
//! [`crate::escrow_sealed`]'s value-hold and [`crate::obligation_standing`]'s StrictMonotonic
//! per-period cursor — into ONE object. Opening a lease HOLDS a prepaid `budget` of rent in the
//! cell's committed heap (the escrow leg). Each [`discharge_period`] performs a SINGLE atomic write
//! that (a) advances the committed `next_due` cursor by exactly one period AND (b) draws exactly the
//! sealed `rent` from the escrowed remaining budget, refusing when the remaining budget cannot cover
//! the draw. Because the meter-advance and the rent-draw are the SAME write, drift is a kernel/type
//! error, not a discipline: there is no expressible discharge that advances the meter without
//! drawing rent, or draws rent without advancing the meter.
//!
//! # The weld (what already existed, disconnected)
//!
//! This welds onto substrate already in the tree, the same vehicles [`crate::escrow_sealed`] and
//! [`crate::obligation_standing`] use:
//!
//!  * **The committed heap** ([`crate::state::CellState::set_heap`] /
//!    [`crate::state::compute_heap_root`]) is an openable sorted-Poseidon2
//!    `(collection, key) → FieldElement` map ALREADY folded into the canonical state commitment. We
//!    reserve a collection id ([`PREPAID_LEASE_COLL`]) for the lease ledger: the terms digest, the
//!    `next_due` cursor, the discharged count, the REMAINING prepaid budget (the escrow leg), and the
//!    cumulative DRAWN total all live there — bound into the commitment FOR FREE, no VK bump.
//!
//!  * **The signed `i64` balance ledger** is the value primitive: the prepaid budget is a quantity
//!    of value held in the lease, drawn down one `rent` per discharge.
//!
//!  * **The StrictMonotonic cursor** ([`crate::obligation_standing`]'s `next_due`) is the meter: a
//!    discharge for period `k` is admissible only when the cursor sits at `start + k·period`, and it
//!    advances the cursor to `start + (k+1)·period`. A replay finds the cursor past it and is
//!    REFUSED — a spent period is a spent nullifier.
//!
//!  * **The sealed value-hold** ([`crate::escrow_sealed`]'s leg) is the budget: the remaining budget
//!    is a committed scalar the draw decrements, and the draw is refused when it cannot cover the
//!    rent (the fused lapse backstop).
//!
//! # The soundness story (what binds the fused discharge)
//!
//! The binding enforces, against a holder of the commitment + heap openings:
//!
//! 1. **No over/under-draw.** The asserted draw must equal the schedule's committed `rent`.
//! 2. **No double-discharge (one-shot per period).** The `next_due` cursor moves forward by exactly
//!    one period; a replay of a discharged period finds the cursor advanced and is REJECTED.
//! 3. **No off-schedule discharge.** A discharge presented before its period's due block is REJECTED.
//! 4. **No draw exceeding the remaining prepaid budget (the fused backstop).** A discharge whose
//!    remaining budget cannot cover the rent is REJECTED — the meter cannot advance past what was
//!    prepaid.
//! 5. **Budget never over-drawn + metered == drawn (the fusion).** After `n` discharges the
//!    committed remaining budget is EXACTLY `budget − n·rent` and the drawn total is EXACTLY
//!    `n·rent = count·rent`; remaining + drawn == budget is conserved (Σδ = 0) at every step. The
//!    meter count, the budget draw-down, and the drawn total cannot disagree.
//!
//! The honest-accept path ([`discharge_period`] accepting) and every forge-reject path run through
//! the SAME [`LeaseState::check_discharge`] / [`LeaseState::audit`] verification core, so a stub in
//! either direction fails one polarity (non-vacuity by construction).
//!
//! # The Lean rung
//!
//! `metatheory/Dregg2/Deos/PrepaidLease.lean` proves the invariant BY REUSE of
//! `Substrate.Heap.root_binds_get` (the committed cursor/budget/drawn are bound), the StrictMonotonic
//! cursor discipline (the one-shot meter), and the sealed budget-hold — `#assert_all_clean`, both
//! polarities. [`tests::invariant_matches_lean_rung`] mirrors that rung's `#guard` witnesses.
//!
//! # The next slice (named, not built here)
//!
//! The executor check here is the genuine forge/drift rejection. The remaining slice is the
//! **in-circuit witness** (`PrepaidLease.lean` §6b): an off-AIR `DischargeLease` manifest entry whose
//! gate binds "due ∧ budget-covered ∧ cursor advanced by one period ∧ remaining drawn by exactly rent
//! ∧ drawn recorded by exactly rent" into PUBLIC INPUTS, re-evaluated against the bound
//! `state_before`/`state_after` views — the AIR constraint polynomials (the VK bytes) UNCHANGED, so a
//! verifier-code epoch, not a proving-key rotation.

use serde::{Deserialize, Serialize};

use crate::cell::Cell;
use crate::id::CellId;
use crate::state::FieldElement;

/// Reserved heap collection id for the prepaid-lease ledger. Lives inside the cell's committed heap
/// (so the whole lease is folded into the canonical state commitment). Chosen high to avoid colliding
/// with application heap collections, in the same spirit as
/// [`crate::obligation_standing::OBLIGATION_COLL`].
pub const PREPAID_LEASE_COLL: u32 = 0x091E_A5ED_u32; // a fixed reserved id ("prepaId lEASED")

/// Heap key holding the 32-byte digest of the lease's [`LeaseTerms`]. Binds *which* lease this cell
/// owes.
pub const KEY_TERMS_DIGEST: u32 = 0;
/// Heap key: the `next_due` cursor — the block at which the NEXT undischarged period falls due
/// (canonical little-endian `i64`). Starts at `terms.start`; each discharge advances it by
/// `terms.period`. THE METER.
pub const KEY_NEXT_DUE: u32 = 1;
/// Heap key: the count of periods discharged so far. Starts at `0`; each discharge increments by `1`.
pub const KEY_DISCHARGED_COUNT: u32 = 2;
/// Heap key: the REMAINING prepaid budget held in escrow (canonical little-endian `i64`). Starts at
/// `terms.budget`; each discharge draws exactly `terms.rent`. THE ESCROW LEG.
pub const KEY_REMAINING_BUDGET: u32 = 3;
/// Heap key: the cumulative DRAWN total (canonical little-endian `i64`). Starts at `0`; each
/// discharge adds `terms.rent`. Always equals `discharged_count · rent`, and
/// `remaining_budget + drawn_total == budget`.
pub const KEY_DRAWN_TOTAL: u32 = 4;

/// Encode an `i64` as a 32-byte heap [`FieldElement`] (little-endian, low 8 bytes). Round-trips with
/// [`decode_i64`].
pub fn encode_i64(value: i64) -> FieldElement {
    let mut f = [0u8; 32];
    f[0..8].copy_from_slice(&value.to_le_bytes());
    f
}

/// Decode a heap field back to the `i64` it encodes (low 8 bytes).
pub fn decode_i64(f: &FieldElement) -> i64 {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&f[0..8]);
    i64::from_le_bytes(buf)
}

/// The sealed terms of a prepaid lease: who leases from whom, in what asset, the rent per period, the
/// period length, the first due block, an optional bounded count, and the prepaid `budget` held in
/// escrow at open. The digest is bound into the cell's commitment, so lessee and lessor cannot
/// disagree about the lease.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeaseTerms {
    /// The cell that LEASES (and from whose prepaid budget each rent is drawn).
    pub lessee: CellId,
    /// The cell that is PAID (the recipient of each rent draw).
    pub lessor: CellId,
    /// The asset the rent is denominated in.
    pub asset: CellId,
    /// The rent drawn each period. Must be `> 0`.
    pub rent: i64,
    /// The period length in blocks. Must be `> 0` — period `k` falls due at `start + k·period`.
    pub period: i64,
    /// The block at which period `0` falls due.
    pub start: i64,
    /// The bounded number of periods, or `0` for unbounded (the prepaid budget bounds it anyway).
    pub count: i64,
    /// The prepaid budget HELD in escrow at open. Must be `>= 0`.
    pub budget: i64,
}

impl LeaseTerms {
    /// A prepaid lease: `lessee` owes `rent` of `asset` to `lessor` every `period` blocks from block
    /// `start`, for `count` periods (`0` = unbounded), prepaying `budget` into escrow.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        lessee: CellId,
        lessor: CellId,
        asset: CellId,
        rent: i64,
        period: i64,
        start: i64,
        count: i64,
        budget: i64,
    ) -> Self {
        LeaseTerms {
            lessee,
            lessor,
            asset,
            rent,
            period,
            start,
            count,
            budget,
        }
    }

    /// Whether these terms are internally well-formed (positive rent/period, non-negative
    /// start/count/budget). Ill-formed terms cannot be opened.
    pub fn is_well_formed(&self) -> bool {
        self.rent > 0 && self.period > 0 && self.start >= 0 && self.count >= 0 && self.budget >= 0
    }

    /// The block at which period `k` (0-indexed) falls due.
    pub fn due_block(&self, k: i64) -> i64 {
        self.start.saturating_add(k.saturating_mul(self.period))
    }

    /// How many periods MUST have been discharged by the time the schedule clock reaches `clock`
    /// (capped at a bounded `count`). The schedule's ground truth the audit compares against.
    pub fn periods_due_by(&self, clock: i64) -> i64 {
        if clock < self.start {
            return 0;
        }
        let elapsed = clock - self.start;
        let due = elapsed / self.period + 1;
        if self.count > 0 && due > self.count {
            self.count
        } else {
            due
        }
    }

    /// A 32-byte canonical digest of the terms. Domain-separated so it can never collide with any
    /// other heap value's preimage. Bound at [`KEY_TERMS_DIGEST`].
    pub fn digest(&self) -> FieldElement {
        let mut h = blake3::Hasher::new_derive_key("dregg.prepaid-lease.terms.v1");
        h.update(self.lessee.as_bytes());
        h.update(self.lessor.as_bytes());
        h.update(self.asset.as_bytes());
        h.update(&self.rent.to_le_bytes());
        h.update(&self.period.to_le_bytes());
        h.update(&self.start.to_le_bytes());
        h.update(&self.count.to_le_bytes());
        h.update(&self.budget.to_le_bytes());
        *h.finalize().as_bytes()
    }
}

/// A discharge step presented to the verifier: the lessee asserts it is discharging period
/// `period_index`, drawing `amount` rent, with the schedule clock at `clock`. The verifier checks the
/// step against the committed cursor, budget, and schedule WITHOUT trusting any field of it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DischargePeriod {
    /// Which period (0-indexed) the lessee asserts it is discharging. Must equal the committed
    /// cursor's current period — no skip, no replay.
    pub period_index: i64,
    /// The rent the lessee asserts it is drawing. Must equal the committed `rent` — over/under-draw
    /// is rejected.
    pub amount: i64,
    /// The schedule clock (block height) at the moment of discharge. Must have reached the period's
    /// due block — an off-schedule (early) discharge is rejected.
    pub clock: i64,
}

/// Why a prepaid-lease operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeaseError {
    /// The cell carries no prepaid-lease binding (no terms digest).
    NotALease,
    /// The supplied terms' digest does not match the one bound in the cell.
    TermsMismatch,
    /// The terms are not well-formed (non-positive rent/period, negative budget, etc).
    IllFormedTerms,
    /// THE OFF-SCHEDULE / EARLY REJECTION: the schedule clock has not yet reached the period's due
    /// block.
    NotYetDue {
        /// The block at which the period falls due.
        due_block: i64,
        /// The presented clock, which is `< due_block`.
        clock: i64,
    },
    /// THE ONE-SHOT / SKIP REJECTION: the presented `period_index` is not the current period the
    /// cursor expects (replay of a discharged period, or a jump ahead).
    WrongPeriod {
        /// The period the cursor expects next.
        expected: i64,
        /// The period the discharge presented.
        presented: i64,
    },
    /// THE OVER/UNDER-DRAW REJECTION: the asserted draw does not equal the committed rent.
    DrawMismatch {
        /// What the schedule committed (the rent).
        owed: i64,
        /// What the discharge asserted.
        presented: i64,
    },
    /// The lease is bounded and all `count` periods are already discharged.
    Completed {
        /// The bounded count of periods.
        count: i64,
    },
    /// THE INSUFFICIENT-BUDGET / LAPSE REJECTION (the fused backstop): the committed remaining prepaid
    /// budget cannot cover the rent — the meter cannot advance past what was prepaid.
    InsufficientBudget {
        /// The committed remaining prepaid budget.
        remaining: i64,
        /// The rent the draw requires.
        rent: i64,
    },
    /// THE SILENT-SKIP / STALENESS REJECTION (the audit tooth): at the presented clock the committed
    /// discharged count is below the number of periods the schedule says MUST be discharged by now.
    BehindSchedule {
        /// How many periods the schedule requires discharged by the audited clock.
        required: i64,
        /// How many the committed cursor actually reflects.
        committed: i64,
    },
}

impl std::fmt::Display for LeaseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LeaseError::NotALease => write!(f, "cell carries no prepaid-lease binding"),
            LeaseError::TermsMismatch => write!(f, "supplied terms do not match the bound lease"),
            LeaseError::IllFormedTerms => write!(f, "lease terms are not well-formed"),
            LeaseError::NotYetDue { due_block, clock } => write!(
                f,
                "off-schedule: period falls due at block {due_block}, clock is {clock}"
            ),
            LeaseError::WrongPeriod {
                expected,
                presented,
            } => write!(
                f,
                "wrong period: cursor expects {expected}, discharge presented {presented}"
            ),
            LeaseError::DrawMismatch { owed, presented } => write!(
                f,
                "draw mismatch: rent {owed}, discharge presented {presented}"
            ),
            LeaseError::Completed { count } => {
                write!(f, "lease completed: all {count} periods discharged")
            }
            LeaseError::InsufficientBudget { remaining, rent } => write!(
                f,
                "insufficient prepaid budget: {remaining} remaining cannot cover rent {rent}"
            ),
            LeaseError::BehindSchedule {
                required,
                committed,
            } => write!(
                f,
                "behind schedule: {required} periods due, only {committed} committed"
            ),
        }
    }
}

impl std::error::Error for LeaseError {}

/// A read-only view of a prepaid lease's committed state, recovered from the cell's heap. The single
/// source of truth every verification path consults — the honest accept and every forge reject run
/// through THIS, so a stub in either direction fails one polarity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeaseState {
    /// The bound terms digest.
    pub terms_digest: FieldElement,
    /// The committed `next_due` cursor (the meter).
    pub next_due: i64,
    /// The committed count of periods discharged so far.
    pub discharged_count: i64,
    /// The committed REMAINING prepaid budget (the escrow leg).
    pub remaining_budget: i64,
    /// The committed cumulative DRAWN total.
    pub drawn_total: i64,
}

impl LeaseState {
    /// Recover a lease's committed state from a cell, or [`LeaseError::NotALease`].
    pub fn read(cell: &Cell) -> Result<LeaseState, LeaseError> {
        let terms_digest = cell
            .state
            .get_heap(PREPAID_LEASE_COLL, KEY_TERMS_DIGEST)
            .ok_or(LeaseError::NotALease)?;
        let next_due = cell
            .state
            .get_heap(PREPAID_LEASE_COLL, KEY_NEXT_DUE)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        let discharged_count = cell
            .state
            .get_heap(PREPAID_LEASE_COLL, KEY_DISCHARGED_COUNT)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        let remaining_budget = cell
            .state
            .get_heap(PREPAID_LEASE_COLL, KEY_REMAINING_BUDGET)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        let drawn_total = cell
            .state
            .get_heap(PREPAID_LEASE_COLL, KEY_DRAWN_TOTAL)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        Ok(LeaseState {
            terms_digest,
            next_due,
            discharged_count,
            remaining_budget,
            drawn_total,
        })
    }

    /// **The fused discharge forge-detector.** Verify a [`DischargePeriod`] against the committed
    /// lease and the terms WITHOUT mutating anything. Returns the `rent` that will be drawn only when:
    ///
    /// - the presented terms match the committed digest;
    /// - the lease is not already completed (bounded count exhausted);
    /// - the presented `period_index` is exactly the cursor's current period (no replay/skip);
    /// - the presented `clock` has reached that period's due block (no off-schedule discharge);
    /// - the presented `amount` equals the committed `rent` (no over/under-draw);
    /// - the committed remaining prepaid budget covers the rent (the fused backstop).
    pub fn check_discharge(
        &self,
        terms: &LeaseTerms,
        step: &DischargePeriod,
    ) -> Result<i64, LeaseError> {
        if !terms.is_well_formed() {
            return Err(LeaseError::IllFormedTerms);
        }
        if self.terms_digest != terms.digest() {
            return Err(LeaseError::TermsMismatch);
        }
        // Which period does the committed cursor expect next? Derived from the cursor, NOT trusted.
        let expected_period = (self.next_due - terms.start) / terms.period;

        if terms.count > 0 && expected_period >= terms.count {
            return Err(LeaseError::Completed { count: terms.count });
        }
        // ONE-SHOT / NO-SKIP.
        if step.period_index != expected_period {
            return Err(LeaseError::WrongPeriod {
                expected: expected_period,
                presented: step.period_index,
            });
        }
        // NO OFF-SCHEDULE DISCHARGE.
        let due_block = terms.due_block(expected_period);
        if step.clock < due_block {
            return Err(LeaseError::NotYetDue {
                due_block,
                clock: step.clock,
            });
        }
        // NO OVER/UNDER-DRAW.
        if step.amount != terms.rent {
            return Err(LeaseError::DrawMismatch {
                owed: terms.rent,
                presented: step.amount,
            });
        }
        // THE FUSED BACKSTOP: the prepaid budget must cover the rent draw.
        if self.remaining_budget < terms.rent {
            return Err(LeaseError::InsufficientBudget {
                remaining: self.remaining_budget,
                rent: terms.rent,
            });
        }
        Ok(terms.rent)
    }

    /// **The silent-skip / staleness forge-detector.** At the audited `clock`, the schedule says
    /// [`LeaseTerms::periods_due_by`] periods MUST be discharged; this checks the committed count is
    /// not behind that. Returns `Ok(required)` when at-or-ahead of schedule.
    pub fn audit(&self, terms: &LeaseTerms, clock: i64) -> Result<i64, LeaseError> {
        if !terms.is_well_formed() {
            return Err(LeaseError::IllFormedTerms);
        }
        if self.terms_digest != terms.digest() {
            return Err(LeaseError::TermsMismatch);
        }
        let required = terms.periods_due_by(clock);
        if self.discharged_count < required {
            return Err(LeaseError::BehindSchedule {
                required,
                committed: self.discharged_count,
            });
        }
        Ok(required)
    }

    /// The conservation invariant: remaining budget + drawn total == initial prepaid budget (Σδ = 0).
    /// Every rent leaving the escrow leg appears in the drawn total; value neither appears nor
    /// vanishes. A holder of the commitment can check this at any point.
    pub fn conserves(&self, terms: &LeaseTerms) -> bool {
        self.remaining_budget.saturating_add(self.drawn_total) == terms.budget
    }
}

/// **Open** a prepaid lease on a cell: seal the terms digest, initialize the cursor to the first due
/// block, zero the discharged count and drawn total, and HOLD the full prepaid `budget` in the escrow
/// (remaining) slot. After this the cell's commitment binds the lease and holds the prepaid budget;
/// nothing is discharged yet. Rejects ill-formed terms.
pub fn open_lease(cell: &mut Cell, terms: &LeaseTerms) -> Result<(), LeaseError> {
    if !terms.is_well_formed() {
        return Err(LeaseError::IllFormedTerms);
    }
    let st = &mut cell.state;
    st.set_heap(PREPAID_LEASE_COLL, KEY_TERMS_DIGEST, terms.digest());
    st.set_heap(PREPAID_LEASE_COLL, KEY_NEXT_DUE, encode_i64(terms.start));
    st.set_heap(PREPAID_LEASE_COLL, KEY_DISCHARGED_COUNT, encode_i64(0));
    st.set_heap(
        PREPAID_LEASE_COLL,
        KEY_REMAINING_BUDGET,
        encode_i64(terms.budget),
    );
    st.set_heap(PREPAID_LEASE_COLL, KEY_DRAWN_TOTAL, encode_i64(0));
    Ok(())
}

/// **Discharge** the current period: verify the step via [`LeaseState::check_discharge`], then in ONE
/// atomic mutation advance the committed cursor by one period, increment the discharged count, DRAW
/// exactly `rent` from the remaining prepaid budget, and add `rent` to the cumulative drawn total.
///
/// The meter advance and the rent draw are the SAME mutation — there is no code path that advances
/// one without the other. One-shot per period; if `check_discharge` rejects (including the fused
/// insufficient-budget backstop), NOTHING is mutated.
///
/// Returns the `rent` the caller (the executor) moves from the escrowed budget to the lessor.
pub fn discharge_period(
    cell: &mut Cell,
    terms: &LeaseTerms,
    step: &DischargePeriod,
) -> Result<i64, LeaseError> {
    let view = LeaseState::read(cell)?;
    let rent = view.check_discharge(terms, step)?;
    // THE FUSED WRITE: meter advance ⊗ budget draw, atomically.
    let new_next_due = view.next_due.saturating_add(terms.period);
    let new_count = view.discharged_count.saturating_add(1);
    let new_remaining = view.remaining_budget.saturating_sub(rent);
    let new_drawn = view.drawn_total.saturating_add(rent);
    let st = &mut cell.state;
    st.set_heap(PREPAID_LEASE_COLL, KEY_NEXT_DUE, encode_i64(new_next_due));
    st.set_heap(
        PREPAID_LEASE_COLL,
        KEY_DISCHARGED_COUNT,
        encode_i64(new_count),
    );
    st.set_heap(
        PREPAID_LEASE_COLL,
        KEY_REMAINING_BUDGET,
        encode_i64(new_remaining),
    );
    st.set_heap(PREPAID_LEASE_COLL, KEY_DRAWN_TOTAL, encode_i64(new_drawn));
    Ok(rent)
}

/// Whether a cell carries a prepaid-lease binding (a terms digest in its reserved heap collection).
pub fn is_lease(cell: &Cell) -> bool {
    cell.state
        .get_heap(PREPAID_LEASE_COLL, KEY_TERMS_DIGEST)
        .is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }
    fn lease_cell() -> Cell {
        Cell::with_balance([5u8; 32], [5u8; 32], 0)
    }

    /// Lessee cell 1 leases from lessor cell 2 in asset 9: rent 50 every 100 blocks from block 1000,
    /// unbounded, prepaid budget 150 — which covers EXACTLY three periods.
    fn sample_terms() -> LeaseTerms {
        LeaseTerms::new(cid(1), cid(2), cid(9), 50, 100, 1000, 0, 150)
    }

    /// THE HONEST PATH: three on-schedule discharges drain the prepaid budget exactly. Each advances
    /// the cursor by one period AND draws exactly the rent; the fourth is refused by the budget
    /// backstop (nothing left to prepay).
    #[test]
    fn honest_lease_drains_budget_exactly() {
        let terms = sample_terms();
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms).unwrap();
        assert!(is_lease(&cell));

        for (k, clk, expect_remaining, expect_drawn) in
            [(0, 1000, 100, 50), (1, 1100, 50, 100), (2, 1200, 0, 150)]
        {
            let moved = discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: k,
                    amount: 50,
                    clock: clk,
                },
            )
            .expect("on-schedule discharge must accept");
            assert_eq!(moved, 50);
            let view = LeaseState::read(&cell).unwrap();
            assert_eq!(
                view.next_due,
                1000 + (k + 1) * 100,
                "meter advances one period"
            );
            assert_eq!(view.discharged_count, k + 1);
            assert_eq!(
                view.remaining_budget, expect_remaining,
                "budget drawn by exactly rent"
            );
            assert_eq!(view.drawn_total, expect_drawn, "drawn records exactly rent");
            assert!(view.conserves(&terms), "remaining + drawn == budget (Σδ=0)");
        }

        // The fourth discharge (period 3, due 1300) is refused: the prepaid budget is exhausted.
        assert_eq!(
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: 3,
                    amount: 50,
                    clock: 1300,
                },
            ),
            Err(LeaseError::InsufficientBudget {
                remaining: 0,
                rent: 50,
            }),
            "the meter cannot advance past the prepaid budget"
        );
        // ...and nothing moved.
        let view = LeaseState::read(&cell).unwrap();
        assert_eq!(view.discharged_count, 3);
        assert_eq!(view.drawn_total, 150);
    }

    /// The whole lease is bound into the canonical commitment: discharging re-seals it (a light
    /// client sees the cursor advance AND the budget draw). This is WHY a forge cannot hide.
    #[test]
    fn lease_state_is_bound_into_commitment() {
        let terms = sample_terms();
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms).unwrap();
        let before = cell.state_commitment();
        discharge_period(
            &mut cell,
            &terms,
            &DischargePeriod {
                period_index: 0,
                amount: 50,
                clock: 1000,
            },
        )
        .unwrap();
        assert_ne!(
            before,
            cell.state_commitment(),
            "discharge re-seals the commitment"
        );
    }

    // ── FORGE-DETECTOR 1: over/under-draw ────────────────────────────────────

    /// A discharge drawing MORE (or LESS) than the committed rent is rejected. The lease owes 50; a
    /// draw of 9999 (or 1) is REFUSED — the same `check_discharge` the honest path passes.
    #[test]
    fn over_draw_is_rejected() {
        let terms = sample_terms();
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms).unwrap();
        let view = LeaseState::read(&cell).unwrap();
        // honest exactly-50 accepts (non-vacuity).
        assert_eq!(
            view.check_discharge(
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50)
        );
        assert_eq!(
            view.check_discharge(
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 9_999,
                    clock: 1000
                }
            ),
            Err(LeaseError::DrawMismatch {
                owed: 50,
                presented: 9_999
            })
        );
        assert_eq!(
            view.check_discharge(
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 1,
                    clock: 1000
                }
            ),
            Err(LeaseError::DrawMismatch {
                owed: 50,
                presented: 1
            })
        );
    }

    // ── FORGE-DETECTOR 2: double-discharge (one-shot) ────────────────────────

    /// After an honest discharge of period 0, a second discharge of period 0 is rejected: the cursor
    /// has advanced to expect period 1. The SAME core that accepted period 0 refuses its replay.
    #[test]
    fn double_discharge_is_rejected() {
        let terms = sample_terms();
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms).unwrap();
        assert_eq!(
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50)
        );
        let view = LeaseState::read(&cell).unwrap();
        assert_eq!(
            view.check_discharge(
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Err(LeaseError::WrongPeriod {
                expected: 1,
                presented: 0
            }),
            "a discharged period cannot be discharged again (one-shot)"
        );
        // and the mutating replay refuses too — the budget is NOT double-drawn.
        assert_eq!(
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Err(LeaseError::WrongPeriod {
                expected: 1,
                presented: 0
            })
        );
        assert_eq!(
            LeaseState::read(&cell).unwrap().drawn_total,
            50,
            "no double-draw"
        );
        assert_eq!(LeaseState::read(&cell).unwrap().remaining_budget, 100);
    }

    // ── FORGE-DETECTOR 3: off-schedule (early) discharge ─────────────────────

    /// Discharging before the period's due block is rejected. Period 0 is due at 1000; a discharge at
    /// clock 999 is REFUSED — the same `check_discharge` the honest path passes at clock 1000.
    #[test]
    fn off_schedule_discharge_is_rejected() {
        let terms = sample_terms();
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms).unwrap();
        let view = LeaseState::read(&cell).unwrap();
        // on-time at 1000 WOULD accept (non-vacuity).
        assert_eq!(
            view.check_discharge(
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50)
        );
        assert_eq!(
            view.check_discharge(
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 999
                }
            ),
            Err(LeaseError::NotYetDue {
                due_block: 1000,
                clock: 999
            })
        );
        // the mutating path refuses too, leaving the cursor and budget untouched.
        assert_eq!(
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 999
                }
            ),
            Err(LeaseError::NotYetDue {
                due_block: 1000,
                clock: 999
            })
        );
        assert_eq!(LeaseState::read(&cell).unwrap().discharged_count, 0);
        assert_eq!(LeaseState::read(&cell).unwrap().remaining_budget, 150);
    }

    // ── FORGE-DETECTOR 4: draw exceeds remaining prepaid budget (the fused backstop) ──

    /// THE FUSION BACKSTOP: once the prepaid budget cannot cover the rent, the discharge is refused —
    /// the meter CANNOT advance past what was prepaid. A lease with budget covering only two periods
    /// accepts periods 0 and 1, then refuses period 2 for InsufficientBudget (NOT for schedule).
    #[test]
    fn insufficient_budget_is_rejected() {
        // budget 100 = exactly two rents of 50.
        let terms = LeaseTerms::new(cid(1), cid(2), cid(9), 50, 100, 1000, 0, 100);
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms).unwrap();

        assert_eq!(
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50)
        );
        assert_eq!(
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: 1,
                    amount: 50,
                    clock: 1100
                }
            ),
            Ok(50)
        );
        // period 2 is ON schedule (due 1200) and correctly formed — but the budget is exhausted.
        let view = LeaseState::read(&cell).unwrap();
        assert_eq!(view.remaining_budget, 0);
        assert_eq!(
            view.check_discharge(
                &terms,
                &DischargePeriod {
                    period_index: 2,
                    amount: 50,
                    clock: 1200
                }
            ),
            Err(LeaseError::InsufficientBudget {
                remaining: 0,
                rent: 50
            }),
            "the fused backstop refuses a draw the prepaid budget cannot cover"
        );
        assert_eq!(
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: 2,
                    amount: 50,
                    clock: 1200
                }
            ),
            Err(LeaseError::InsufficientBudget {
                remaining: 0,
                rent: 50
            })
        );
        // Boundary: with EXACTLY the rent remaining, the draw is covered.
        let terms3 = LeaseTerms::new(cid(1), cid(2), cid(9), 50, 100, 1000, 0, 50);
        let mut cell3 = lease_cell();
        open_lease(&mut cell3, &terms3).unwrap();
        assert_eq!(
            discharge_period(
                &mut cell3,
                &terms3,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50)
        );
        assert_eq!(LeaseState::read(&cell3).unwrap().remaining_budget, 0);
    }

    // ── THE FUSION: budget-never-overdrawn + metered-equals-drawn ─────────────

    /// BUDGET NEVER OVER-DRAWN + METERED == DRAWN: after N discharges the committed remaining budget
    /// is EXACTLY budget − N·rent, the drawn total is EXACTLY N·rent == count·rent, and
    /// remaining + drawn == budget (Σδ=0) at every step. The meter, the budget, and the draw cannot
    /// disagree — drift is unrepresentable because the SINGLE mutation moves all three.
    #[test]
    fn metered_equals_drawn_and_budget_never_overdrawn() {
        let terms = sample_terms(); // rent 50, budget 150
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms).unwrap();

        for k in 0..3i64 {
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: k,
                    amount: 50,
                    clock: 1000 + k * 100,
                },
            )
            .unwrap();
            let n = k + 1;
            let view = LeaseState::read(&cell).unwrap();
            // budget never over-drawn: remaining == budget − n·rent.
            assert_eq!(view.remaining_budget, terms.budget - n * terms.rent);
            // metered == drawn: drawn == n·rent == count·rent.
            assert_eq!(view.drawn_total, n * terms.rent);
            assert_eq!(view.drawn_total, view.discharged_count * terms.rent);
            // conservation Σδ=0.
            assert_eq!(view.remaining_budget + view.drawn_total, terms.budget);
        }
    }

    // ── FORGE-DETECTOR 5: silent skip / staleness (the audit tooth) ──────────

    /// A cell that claims "all met" but whose committed cursor lags the schedule is REJECTED by
    /// `audit`. By block 1250, periods 0,1,2 MUST be discharged — three. A cell that discharged only
    /// period 0 is BEHIND; an on-schedule cell passes the SAME audit.
    #[test]
    fn behind_schedule_is_rejected() {
        let terms = sample_terms();
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms).unwrap();
        discharge_period(
            &mut cell,
            &terms,
            &DischargePeriod {
                period_index: 0,
                amount: 50,
                clock: 1000,
            },
        )
        .unwrap();
        let view = LeaseState::read(&cell).unwrap();
        assert_eq!(terms.periods_due_by(1250), 3);
        assert_eq!(
            view.audit(&terms, 1250),
            Err(LeaseError::BehindSchedule {
                required: 3,
                committed: 1
            })
        );

        let mut honest = lease_cell();
        open_lease(&mut honest, &terms).unwrap();
        for (k, clk) in [(0, 1000), (1, 1100), (2, 1200)] {
            discharge_period(
                &mut honest,
                &terms,
                &DischargePeriod {
                    period_index: k,
                    amount: 50,
                    clock: clk,
                },
            )
            .unwrap();
        }
        assert_eq!(
            LeaseState::read(&honest).unwrap().audit(&terms, 1250),
            Ok(3)
        );
    }

    // ── additional teeth ─────────────────────────────────────────────────────

    /// A discharge presented against the WRONG terms is rejected at the terms digest.
    #[test]
    fn wrong_terms_is_rejected() {
        let terms = sample_terms();
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms).unwrap();
        // same lease but a different rent → different digest.
        let other = LeaseTerms::new(cid(1), cid(2), cid(9), 51, 100, 1000, 0, 150);
        let view = LeaseState::read(&cell).unwrap();
        assert_eq!(
            view.check_discharge(
                &other,
                &DischargePeriod {
                    period_index: 0,
                    amount: 51,
                    clock: 1000
                }
            ),
            Err(LeaseError::TermsMismatch)
        );
        assert_eq!(view.audit(&other, 1250), Err(LeaseError::TermsMismatch));
    }

    /// Opening ill-formed terms is refused (non-positive rent/period, negative budget).
    #[test]
    fn ill_formed_terms_are_rejected() {
        let mut cell = lease_cell();
        assert_eq!(
            open_lease(
                &mut cell,
                &LeaseTerms::new(cid(1), cid(2), cid(9), 0, 100, 1000, 0, 150)
            ),
            Err(LeaseError::IllFormedTerms)
        );
        assert_eq!(
            open_lease(
                &mut cell,
                &LeaseTerms::new(cid(1), cid(2), cid(9), 50, 0, 1000, 0, 150)
            ),
            Err(LeaseError::IllFormedTerms)
        );
        assert_eq!(
            open_lease(
                &mut cell,
                &LeaseTerms::new(cid(1), cid(2), cid(9), 50, 100, 1000, 0, -1)
            ),
            Err(LeaseError::IllFormedTerms)
        );
    }

    /// `read`/`check_discharge` on a non-lease cell reports NotALease.
    #[test]
    fn non_lease_cell_is_rejected() {
        assert_eq!(LeaseState::read(&lease_cell()), Err(LeaseError::NotALease));
    }

    /// A bounded lease refuses a discharge past its count (even with budget remaining).
    #[test]
    fn bounded_lease_completes() {
        // 2-period bounded lease, budget covers 5 (so completion, not budget, bites).
        let terms = LeaseTerms::new(cid(1), cid(2), cid(9), 50, 100, 1000, 2, 250);
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms).unwrap();
        assert_eq!(
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50)
        );
        assert_eq!(
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: 1,
                    amount: 50,
                    clock: 1100
                }
            ),
            Ok(50)
        );
        assert_eq!(
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: 2,
                    amount: 50,
                    clock: 1200
                }
            ),
            Err(LeaseError::Completed { count: 2 })
        );
        // budget was NOT exhausted — 150 remains — yet the lease is complete.
        assert_eq!(LeaseState::read(&cell).unwrap().remaining_budget, 150);
    }

    /// The i64 encode/decode round-trips, including negatives.
    #[test]
    fn amount_encoding_roundtrips() {
        for v in [0i64, 1, -1, 50, 150, i64::MAX, i64::MIN] {
            assert_eq!(decode_i64(&encode_i64(v)), v);
        }
    }

    /// **The Lean rung: this executor invariant is PROVEN, not just smoke-tested.**
    ///
    /// The fused per-period discharge enforced here — a period is metered once (StrictMonotonic
    /// cursor), never early, never double, never over/under-drawn, and each metered period draws
    /// EXACTLY its rent from the prepaid budget which is never over-drawn — is the EXECUTOR image of
    /// the proven Lean rung `metatheory/Dregg2/Deos/PrepaidLease.lean`, grounded BY REUSE of the
    /// committed-heap root (`Substrate.Heap.root_binds_get`), the StrictMonotonic `next_due` cursor,
    /// and the sealed budget-hold. This test mirrors that rung's `#guard` witnesses (rent 50 every
    /// 100 blocks from 1000, prepaid budget 150 = exactly three periods):
    ///
    ///   * `opened_cursor` / `opened_remaining` — opening commits `next_due = start` AND holds
    ///     `budget`; a period-0 discharge of exactly 50 at clock 1000 accepts and, in ONE write,
    ///     advances the cursor to 1100 (`cursor_strict_mono`), draws remaining to 100
    ///     (`advance_draws_exactly_rent`), records drawn 50 (`advance_records_draw`), moving the root;
    ///   * `replay_rejected` — a replay of period 0 is refused (cursor expects 1);
    ///   * `off_schedule_rejected` — a discharge at clock 999 (due 1000) refused;
    ///   * `over_draw_rejected` — draws 9999 and 1 both refused;
    ///   * `insufficient_budget_rejected` + `budget_never_overdrawn` — with the budget exhausted the
    ///     fourth draw is refused; remaining after N == 150 − N·50;
    ///   * `drawn_eq_count_rent` + `remaining_plus_drawn_conserved` — drawn == count·rent, and
    ///     remaining + drawn == budget (Σδ=0).
    #[test]
    fn invariant_matches_lean_rung() {
        let terms = sample_terms(); // rent 50 / 100 blocks / start 1000 / unbounded / budget 150

        // `opened_cursor` + `opened_remaining`: opening commits next_due = start AND holds budget.
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms).unwrap();
        let opened = LeaseState::read(&cell).unwrap();
        assert_eq!(opened.next_due, 1000);
        assert_eq!(opened.remaining_budget, 150);
        assert_eq!(opened.drawn_total, 0);

        // The fused write: cursor→1100, remaining→100, drawn→50, moving the root.
        let before = cell.state_commitment();
        assert_eq!(
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50)
        );
        assert_ne!(
            before,
            cell.state_commitment(),
            "forged_budget_moves_root: the discharge moves the root"
        );
        let view = LeaseState::read(&cell).unwrap();
        assert_eq!(view.next_due, 1100, "cursor_strict_mono: 1000 < 1100");
        assert_eq!(view.remaining_budget, 100, "advance_draws_exactly_rent");
        assert_eq!(view.drawn_total, 50, "advance_records_draw");

        // `replay_rejected`: replay of period 0 refused (cursor expects 1).
        assert_eq!(
            view.check_discharge(
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Err(LeaseError::WrongPeriod {
                expected: 1,
                presented: 0
            })
        );

        // `off_schedule_rejected` + `over_draw_rejected` on a fresh lease.
        let mut fresh = lease_cell();
        open_lease(&mut fresh, &terms).unwrap();
        let fview = LeaseState::read(&fresh).unwrap();
        assert_eq!(
            fview.check_discharge(
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 50,
                    clock: 999
                }
            ),
            Err(LeaseError::NotYetDue {
                due_block: 1000,
                clock: 999
            })
        );
        assert!(matches!(
            fview.check_discharge(
                &terms,
                &DischargePeriod {
                    period_index: 0,
                    amount: 9_999,
                    clock: 1000
                }
            ),
            Err(LeaseError::DrawMismatch {
                owed: 50,
                presented: 9_999
            })
        ));

        // `budget_never_overdrawn` + `drawn_eq_count_rent` + conservation: drain the budget; the
        // fourth draw is refused (`insufficient_budget_rejected`).
        for k in 1..3i64 {
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: k,
                    amount: 50,
                    clock: 1000 + k * 100,
                },
            )
            .unwrap();
            let n = k + 1;
            let v = LeaseState::read(&cell).unwrap();
            assert_eq!(v.remaining_budget, 150 - n * 50); // budget_never_overdrawn (bound)
            assert_eq!(v.drawn_total, n * 50); // drawn_eq_count_rent
            assert_eq!(v.remaining_budget + v.drawn_total, 150); // remaining_plus_drawn_conserved
        }
        assert_eq!(
            discharge_period(
                &mut cell,
                &terms,
                &DischargePeriod {
                    period_index: 3,
                    amount: 50,
                    clock: 1300
                }
            ),
            Err(LeaseError::InsufficientBudget {
                remaining: 0,
                rent: 50
            }) // insufficient_budget_rejected
        );
    }
}
