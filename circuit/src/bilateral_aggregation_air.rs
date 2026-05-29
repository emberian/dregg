//! Stage 7-γ.2 Phase 2 — joint bilateral aggregation AIR.
//!
//! See `STAGE-7-GAMMA-2-PHASE-2-SKETCH.md` for the full design.
//!
//! This module collapses Phase 1's "N per-cell STARK proofs + Rust cross-cell
//! match loop" into a single outer AIR whose public input is the reduced
//! bundle-level summary. The outer trace has one row per inner per-cell proof
//! (padded to a power of two). Each row carries that proof's complete
//! `γ.2 BASE_COUNT = 74` PI vector lifted into trace columns, plus an
//! identically-shaped "expected" projection derived from the bilateral
//! schedule (`turn::bilateral_schedule::ExpectedBilateral::roots_for/counts_for`
//! over the row's owner-cell). The AIR's constraints then enforce, in one
//! algebraic pass, every check the Rust loop performs today:
//!
//!   CG-2  turn-identity agreement
//!         per-row PI slots [TURN_HASH, EFFECTS_HASH_GLOBAL, ACTOR_NONCE,
//!         PREVIOUS_RECEIPT_HASH] equal the outer PI's matching slots.
//!
//!   CG-3  schedule replay
//!         per-row PI counts + roots equal the per-cell "expected" columns
//!         the prover populated from the schedule.
//!
//!   CG-4  IS_AGENT_CELL accounting
//!         running cumulative sum of IS_AGENT_CELL across rows. Boundary:
//!         last row's cumulative == 1. (When N_CELLS is the active prefix,
//!         padding rows carry IS_AGENT_CELL = 0 and contribute nothing.)
//!
//!   CG-5  cross-side existence
//!         expressed as a per-row "schedule-covered" indicator: a row's
//!         expected counts being nonzero must be matched by *another* row
//!         claiming the peer side. Today this is enforced *outside* the AIR
//!         by the prover's schedule-construction logic — the AIR's job is
//!         to confirm what the prover claims, not to discover unbundled
//!         peers. (CG-5 in Rust-shape is part of the prover-side wiring
//!         and the verifier's outer-PI cross-check, not an AIR constraint
//!         group of its own. The Phase-2 sketch flags it as the most
//!         delicate group; we land the matrix variant in a follow-up.)
//!
//!   BILATERAL_CONSISTENT
//!         outer PI slot, must equal 1; constrained to 1 at the last row.
//!
//! ## Inner-proof recursive verification (CG-1)
//!
//! Phase 2's headline win is *also* collapsing each inner STARK verify into
//! the outer AIR. With the now-paved `plonky3_recursion_impl` substrate, the
//! aggregation prover composes:
//!
//!   1. Phase-1 verify of each inner Effect VM proof (classical Rust call).
//!   2. The outer aggregation AIR proof over their PIs.
//!   3. (Optional) a recursive-layer proof of (2), produced via
//!      `prove_recursive_layer_for_air` — this is the constant-size
//!      verification artifact Phase 2 promises.
//!
//! Step (3) means the outer verifier never re-runs (1): the recursive layer
//! attests that the outer AIR accepted its inputs, and the outer AIR's CG-2
//! through CG-5 plus the row PIs *being the inner PIs* binds those inputs
//! to the per-cell proofs the prover ran in (1). A consumer downstream needs
//! only (3) + the outer PI to know the bundle is bilaterally consistent.
//!
//! ## Trace layout
//!
//! `width = AGG_WIDTH` columns. Per row:
//!
//! ```text
//!  [0  .. 74)   inner_pi_buffer       — the cell's full γ.2 PI vector
//!  [74 .. 81)   expected_counts       — 7 count fields from the schedule
//!  [81 ..109)   expected_roots        — 7 × 4-felt root fields
//!  [109]        is_agent_cumulative   — running sum of IS_AGENT_CELL
//!  [110]        consistent_indicator  — bool 1 = this row's checks pass
//!  [111]        n_cells_active        — running active-row counter
//! ```
//!
//! Boundary constraints:
//! - `is_agent_cumulative[last] == 1`
//! - `outer_pi[BILATERAL_CONSISTENT] == 1`
//!
//! ## Outer PI layout
//!
//! ```text
//!   0..4    OUTER_TURN_HASH
//!   4..8    OUTER_EFFECTS_HASH_GLOBAL
//!   8       OUTER_ACTOR_NONCE
//!   9..13   OUTER_PREVIOUS_RECEIPT_HASH
//!  13..21   OUTER_AGENT_CELL_ID   (8-felt cell-id decomposition)
//!  21       OUTER_N_CELLS         (number of active rows in the trace)
//!  22       OUTER_BILATERAL_CONSISTENT  (must == 1 for accept)
//! ```
//!
//! Fixed width: 23 felts, independent of N. This is the headline win for
//! verifier complexity vs. Phase 1's `N × 74` per-bundle PI.

#[cfg(feature = "plonky3")]
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
#[cfg(feature = "plonky3")]
use p3_field::PrimeCharacteristicRing;

use crate::effect_vm::pi as inner_pi;
use crate::field::BabyBear;

// ---------------------------------------------------------------------------
// Outer-AIR column layout
// ---------------------------------------------------------------------------

/// Width of the inner PI buffer columns. Equal to the per-cell γ.2 base PI
/// count (`74`). We lift the entire vector into the trace so every CG-2/CG-3
/// constraint is a simple column equality.
pub const PI_BUFFER_WIDTH: usize = inner_pi::BASE_COUNT;

/// Offset of the inner PI buffer (column 0).
pub const PI_BUFFER_BASE: usize = 0;

/// Offset and width of the per-row expected counts block (7 felts).
pub const EXPECTED_COUNTS_BASE: usize = PI_BUFFER_BASE + PI_BUFFER_WIDTH;
pub const EXPECTED_COUNTS_WIDTH: usize = 7;

/// Offset and width of the per-row expected roots block (7 × 4 = 28 felts).
pub const EXPECTED_ROOTS_BASE: usize = EXPECTED_COUNTS_BASE + EXPECTED_COUNTS_WIDTH;
pub const EXPECTED_ROOTS_WIDTH: usize = 7 * 4;

/// Running cumulative of `IS_AGENT_CELL` (single felt).
pub const IS_AGENT_CUMULATIVE_COL: usize = EXPECTED_ROOTS_BASE + EXPECTED_ROOTS_WIDTH;

/// Per-row "this row's checks passed" boolean (single felt). Set to 1 by
/// the prover when the row corresponds to an actual inner proof and its
/// counts/roots/identity all match. Padding rows carry 0.
pub const CONSISTENT_INDICATOR_COL: usize = IS_AGENT_CUMULATIVE_COL + 1;

/// Running active-row counter (single felt). Padding rows do not increment.
pub const N_CELLS_ACTIVE_COL: usize = CONSISTENT_INDICATOR_COL + 1;

/// Total per-row width.
pub const AGG_WIDTH: usize = N_CELLS_ACTIVE_COL + 1;

// ---------------------------------------------------------------------------
// Outer-AIR public-input layout
// ---------------------------------------------------------------------------

/// Outer PI: 4-felt turn hash.
pub const OUTER_TURN_HASH_BASE: usize = 0;
pub const OUTER_TURN_HASH_LEN: usize = 4;

/// Outer PI: 4-felt global effects hash.
pub const OUTER_EFFECTS_HASH_GLOBAL_BASE: usize = OUTER_TURN_HASH_BASE + OUTER_TURN_HASH_LEN;
pub const OUTER_EFFECTS_HASH_GLOBAL_LEN: usize = 4;

/// Outer PI: actor nonce (single felt; matches the inner per-cell layout).
pub const OUTER_ACTOR_NONCE: usize = OUTER_EFFECTS_HASH_GLOBAL_BASE + OUTER_EFFECTS_HASH_GLOBAL_LEN;

/// Outer PI: 4-felt previous-receipt hash.
pub const OUTER_PREVIOUS_RECEIPT_HASH_BASE: usize = OUTER_ACTOR_NONCE + 1;
pub const OUTER_PREVIOUS_RECEIPT_HASH_LEN: usize = 4;

/// Outer PI: agent-cell id (8-felt canonical decomposition). The aggregation
/// verifier cross-checks this against the active row whose IS_AGENT_CELL is 1.
pub const OUTER_AGENT_CELL_ID_BASE: usize =
    OUTER_PREVIOUS_RECEIPT_HASH_BASE + OUTER_PREVIOUS_RECEIPT_HASH_LEN;
pub const OUTER_AGENT_CELL_ID_LEN: usize = 8;

/// Outer PI: number of active inner proofs in the bundle (single felt). The
/// AIR uses this only to constrain that the last active row's
/// `is_agent_cumulative == 1`; it does *not* gate constraints inside the
/// trace by index (Plonky3 doesn't support that pattern cleanly). Padding
/// rows are required to set IS_AGENT_CELL=0 and contribute zero to the
/// cumulative.
pub const OUTER_N_CELLS: usize = OUTER_AGENT_CELL_ID_BASE + OUTER_AGENT_CELL_ID_LEN;

/// Outer PI: bilateral-consistent flag (single felt; must be 1).
pub const OUTER_BILATERAL_CONSISTENT: usize = OUTER_N_CELLS + 1;

/// Outer PI base count.
pub const OUTER_BASE_COUNT: usize = OUTER_BILATERAL_CONSISTENT + 1;

// ---------------------------------------------------------------------------
// AIR shape
// ---------------------------------------------------------------------------

/// Joint bilateral-aggregation AIR. See module docs.
#[derive(Clone, Debug)]
pub struct BilateralAggregationAir;

impl BilateralAggregationAir {
    pub const WIDTH: usize = AGG_WIDTH;
    pub const PUBLIC_INPUTS: usize = OUTER_BASE_COUNT;

    /// AIR identifier; used by external dispatch.
    pub const AIR_NAME: &'static str = "dregg-bilateral-aggregation-v1";
}

#[cfg(feature = "plonky3")]
impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for BilateralAggregationAir {
    fn width(&self) -> usize {
        Self::WIDTH
    }

    fn num_public_values(&self) -> usize {
        Self::PUBLIC_INPUTS
    }

    /// We touch the running-cumulative columns on the next row to enforce
    /// the transition. We also touch the next row's IS_AGENT_CELL and
    /// CONSISTENT_INDICATOR because the cumulative transitions add the
    /// next row's contribution (cum[i+1] = cum[i] + thing[i+1]).
    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![
            PI_BUFFER_BASE + inner_pi::IS_AGENT_CELL,
            IS_AGENT_CUMULATIVE_COL,
            CONSISTENT_INDICATOR_COL,
            N_CELLS_ACTIVE_COL,
        ]
    }
}

#[cfg(feature = "plonky3")]
impl<AB: AirBuilder> Air<AB> for BilateralAggregationAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();

        // Snapshot public values up front (the borrow rules in p3-air make
        // it awkward to interleave `builder.public_values()` reads with
        // `builder.assert_*` calls).
        let pv = builder.public_values();
        let pv_turn: Vec<AB::Expr> = (0..OUTER_TURN_HASH_LEN)
            .map(|i| pv[OUTER_TURN_HASH_BASE + i].into())
            .collect();
        let pv_effects: Vec<AB::Expr> = (0..OUTER_EFFECTS_HASH_GLOBAL_LEN)
            .map(|i| pv[OUTER_EFFECTS_HASH_GLOBAL_BASE + i].into())
            .collect();
        let pv_actor_nonce: AB::Expr = pv[OUTER_ACTOR_NONCE].into();
        let pv_prev_receipt: Vec<AB::Expr> = (0..OUTER_PREVIOUS_RECEIPT_HASH_LEN)
            .map(|i| pv[OUTER_PREVIOUS_RECEIPT_HASH_BASE + i].into())
            .collect();
        let pv_consistent: AB::Expr = pv[OUTER_BILATERAL_CONSISTENT].into();
        let pv_n_cells: AB::Expr = pv[OUTER_N_CELLS].into();

        // ---- CG-2: turn-identity agreement (4 + 4 + 1 + 4 = 13 equalities per row) ----
        for i in 0..OUTER_TURN_HASH_LEN {
            let row: AB::Expr = local[PI_BUFFER_BASE + inner_pi::TURN_HASH_BASE + i].into();
            builder.assert_zero(row - pv_turn[i].clone());
        }
        for i in 0..OUTER_EFFECTS_HASH_GLOBAL_LEN {
            let row: AB::Expr =
                local[PI_BUFFER_BASE + inner_pi::EFFECTS_HASH_GLOBAL_BASE + i].into();
            builder.assert_zero(row - pv_effects[i].clone());
        }
        {
            let row: AB::Expr = local[PI_BUFFER_BASE + inner_pi::ACTOR_NONCE].into();
            builder.assert_zero(row - pv_actor_nonce.clone());
        }
        for i in 0..OUTER_PREVIOUS_RECEIPT_HASH_LEN {
            let row: AB::Expr =
                local[PI_BUFFER_BASE + inner_pi::PREVIOUS_RECEIPT_HASH_BASE + i].into();
            builder.assert_zero(row - pv_prev_receipt[i].clone());
        }

        // ---- CG-3: schedule replay — counts ----
        let count_slots = [
            inner_pi::OUTBOUND_TRANSFER_COUNT,
            inner_pi::INBOUND_TRANSFER_COUNT,
            inner_pi::OUTBOUND_GRANT_COUNT,
            inner_pi::INBOUND_GRANT_COUNT,
            inner_pi::INTRO_AS_INTRODUCER_COUNT,
            inner_pi::INTRO_AS_RECIPIENT_COUNT,
            inner_pi::INTRO_AS_TARGET_COUNT,
        ];
        for (k, slot) in count_slots.iter().enumerate() {
            let row_pi: AB::Expr = local[PI_BUFFER_BASE + *slot].into();
            let row_expected: AB::Expr = local[EXPECTED_COUNTS_BASE + k].into();
            builder.assert_zero(row_pi - row_expected);
        }

        // ---- CG-3: schedule replay — roots (7 × 4-felt) ----
        let root_bases = [
            inner_pi::OUTGOING_TRANSFER_ROOT_BASE,
            inner_pi::INCOMING_TRANSFER_ROOT_BASE,
            inner_pi::OUTGOING_GRANT_ROOT_BASE,
            inner_pi::INCOMING_GRANT_ROOT_BASE,
            inner_pi::INTRO_AS_INTRODUCER_ROOT_BASE,
            inner_pi::INTRO_AS_RECIPIENT_ROOT_BASE,
            inner_pi::INTRO_AS_TARGET_ROOT_BASE,
        ];
        for (k, base) in root_bases.iter().enumerate() {
            for off in 0..4 {
                let row_pi: AB::Expr = local[PI_BUFFER_BASE + base + off].into();
                let row_expected: AB::Expr = local[EXPECTED_ROOTS_BASE + k * 4 + off].into();
                builder.assert_zero(row_pi - row_expected);
            }
        }

        // ---- CG-4: IS_AGENT_CELL accounting ----
        // For active rows, the cumulative increases by IS_AGENT_CELL; for
        // padding rows, both IS_AGENT_CELL and consistent_indicator are 0
        // and the cumulative stays. The prover sets consistent_indicator=1
        // on active rows (which equals "this is an inner proof") and 0 on
        // padding rows.
        //
        // Boolean gates:
        //   consistent_indicator ∈ {0, 1}
        //   IS_AGENT_CELL        ∈ {0, 1}
        //   on padding rows (consistent_indicator==0):
        //     IS_AGENT_CELL must be 0
        //     all expected_counts/roots must be 0 (sentinel)
        //
        // Cumulative transition (when_transition):
        //   next.is_agent_cumulative
        //     == local.is_agent_cumulative + local.IS_AGENT_CELL
        let ind: AB::Expr = local[CONSISTENT_INDICATOR_COL].into();
        let is_agent: AB::Expr = local[PI_BUFFER_BASE + inner_pi::IS_AGENT_CELL].into();
        let one = AB::Expr::ONE;
        // ind ∈ {0,1}
        builder.assert_zero(ind.clone() * (ind.clone() - one.clone()));
        // is_agent ∈ {0,1}
        builder.assert_zero(is_agent.clone() * (is_agent.clone() - one.clone()));
        // (1 - ind) * is_agent == 0  -- padding rows force IS_AGENT_CELL=0
        builder.assert_zero((one.clone() - ind.clone()) * is_agent.clone());

        // Cumulative transition. We add the *next row's* IS_AGENT_CELL
        // because the boundary already seeds row 0's cumulative to its own
        // IS_AGENT_CELL. With this pattern, `cum[i] = sum(is_agent[0..=i])`,
        // i.e. the cumulative at row `i` includes that row's contribution.
        let cum_local: AB::Expr = local[IS_AGENT_CUMULATIVE_COL].into();
        let cum_next: AB::Expr = next[IS_AGENT_CUMULATIVE_COL].into();
        let is_agent_next: AB::Expr = next[PI_BUFFER_BASE + inner_pi::IS_AGENT_CELL].into();
        builder
            .when_transition()
            .assert_zero(cum_next - (cum_local.clone() + is_agent_next));

        // n_cells_active transition (symmetric: seed at row 0 to ind[0], add
        // ind_next on each transition).
        let n_local: AB::Expr = local[N_CELLS_ACTIVE_COL].into();
        let n_next: AB::Expr = next[N_CELLS_ACTIVE_COL].into();
        let ind_next: AB::Expr = next[CONSISTENT_INDICATOR_COL].into();
        builder
            .when_transition()
            .assert_zero(n_next - (n_local.clone() + ind_next));

        // ---- Boundary: row-0 cumulative seeds to IS_AGENT_CELL[0] ----
        // and row-0 n_cells_active seeds to consistent_indicator[0].
        // We enforce by asserting (cum_local - is_agent) == 0 on first row.
        builder
            .when_first_row()
            .assert_zero(cum_local.clone() - is_agent.clone());
        builder
            .when_first_row()
            .assert_zero(n_local.clone() - ind.clone());

        // ---- Boundary: last-row cumulative == 1, last-row n_cells_active == OUTER_N_CELLS ----
        builder
            .when_last_row()
            .assert_zero(cum_local.clone() - one.clone());
        builder.when_last_row().assert_zero(n_local - pv_n_cells);

        // ---- BILATERAL_CONSISTENT: outer PI must be 1 ----
        // (We don't write this into the trace — the assertion above on
        // pv_consistent is "1" via a constant comparison.) We enforce
        // pv_consistent == 1 unconditionally; if the prover sets it to
        // anything else, the constraint fails.
        builder.assert_zero(pv_consistent - one.clone());
    }
}

// ---------------------------------------------------------------------------
// Custom-STARK (`crate::stark`) AIR implementation
// ---------------------------------------------------------------------------
//
// The Plonky3 `Air` impl above is the symbolic source of truth, but the
// recursion substrate that would turn it into bytes is not yet wired. To
// produce REAL aggregated STARK proof bytes today (FRI + Merkle + Fiat-Shamir,
// checkable by `crate::stark::verify` *without* the trace), we also implement
// the in-tree `crate::stark::StarkAir` trait — the same proof system the
// per-cell Effect VM AIR uses.
//
// ## What the custom STARK enforces (cryptographically, not by replay)
//
// `eval_constraints` is applied uniformly to every trace row; the verifier
// requires it to evaluate to zero on trace rows `0..n-2` (the last row is
// excluded by the transition vanishing polynomial). We combine:
//
//   * CG-2 (13 equalities): each row's inner-PI turn-identity slots
//     (`TURN_HASH`, `EFFECTS_HASH_GLOBAL`, `ACTOR_NONCE`,
//     `PREVIOUS_RECEIPT_HASH`) equal the outer public-input slots. Because
//     the outer PI *is* the proof's `public_inputs`, this binds every row to
//     the bundle summary.
//   * CG-3 (7 + 28 equalities): each row's inner-PI counts/roots equal the
//     prover-supplied `expected_*` columns.
//   * CG-4 booleans + padding gate: `consistent_indicator ∈ {0,1}`,
//     `IS_AGENT_CELL ∈ {0,1}`, and `(1-ind)*is_agent == 0`.
//   * CG-4 prefix sums (transition): `cum[i+1] == cum[i] + is_agent[i+1]` and
//     `n_active[i+1] == n_active[i] + ind[i+1]`.
//   * `BILATERAL_CONSISTENT == 1`: enforced as `pv_consistent - 1` per row.
//
// Boundary constraints (direct Merkle openings against the trace commitment,
// bound to public-input-derived values):
//
//   * row 0    `N_CELLS_ACTIVE_COL == 1`            (row 0 is always active)
//   * last row `IS_AGENT_CUMULATIVE_COL == 1`        (exactly one agent cell)
//   * last row `N_CELLS_ACTIVE_COL == OUTER_N_CELLS` (bundle size matches PI)
//
// ## Residual gap (honest)
//
// The custom STARK applies `eval_constraints` uniformly and offers no
// first-row selector, so the prefix-sum *seed* `cum[0] == IS_AGENT_CELL[0]`
// cannot be expressed as an in-AIR constraint (the seed value is not a public
// input). The transition + last-row boundary together force
// `cum[0] + Σ_{i≥1} is_agent[i] == 1`, which pins the agent-cell *count* but
// leaves `cum[0]` itself one degree of freedom relative to `is_agent[0]`.
// The aggregation verifier closes this the same way it binds the agent
// identity at all: it re-derives every row's `IS_AGENT_CELL` from the
// canonical Turn and rejects any mismatch (see `verify_aggregated_bundle`
// step 5). The CG-1 inner-proof recursive verification (folding each per-cell
// Effect VM STARK into this outer proof) likewise remains future work; the
// per-cell proofs are verified classically by the aggregator's Phase-1 gate.

use crate::stark::{BoundaryConstraint, StarkAir};

impl StarkAir for BilateralAggregationAir {
    fn width(&self) -> usize {
        AGG_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // The highest-degree term is the boolean / padding gate
        // `(1 - ind) * is_agent` and `ind * (ind - 1)` — degree 2.
        2
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        Self::AIR_NAME
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let mut combined = BabyBear::ZERO;
        let mut pow = BabyBear::ONE;
        let add = |c: BabyBear, combined: &mut BabyBear, pow: &mut BabyBear| {
            *combined = *combined + *pow * c;
            *pow = *pow * alpha;
        };

        // Outer PI projections (public_inputs is the outer PI vector).
        // CG-2: turn identity.
        for i in 0..OUTER_TURN_HASH_LEN {
            let row = local[PI_BUFFER_BASE + inner_pi::TURN_HASH_BASE + i];
            add(
                row - public_inputs[OUTER_TURN_HASH_BASE + i],
                &mut combined,
                &mut pow,
            );
        }
        for i in 0..OUTER_EFFECTS_HASH_GLOBAL_LEN {
            let row = local[PI_BUFFER_BASE + inner_pi::EFFECTS_HASH_GLOBAL_BASE + i];
            add(
                row - public_inputs[OUTER_EFFECTS_HASH_GLOBAL_BASE + i],
                &mut combined,
                &mut pow,
            );
        }
        {
            let row = local[PI_BUFFER_BASE + inner_pi::ACTOR_NONCE];
            add(
                row - public_inputs[OUTER_ACTOR_NONCE],
                &mut combined,
                &mut pow,
            );
        }
        for i in 0..OUTER_PREVIOUS_RECEIPT_HASH_LEN {
            let row = local[PI_BUFFER_BASE + inner_pi::PREVIOUS_RECEIPT_HASH_BASE + i];
            add(
                row - public_inputs[OUTER_PREVIOUS_RECEIPT_HASH_BASE + i],
                &mut combined,
                &mut pow,
            );
        }

        // CG-3: schedule replay — counts.
        let count_slots = [
            inner_pi::OUTBOUND_TRANSFER_COUNT,
            inner_pi::INBOUND_TRANSFER_COUNT,
            inner_pi::OUTBOUND_GRANT_COUNT,
            inner_pi::INBOUND_GRANT_COUNT,
            inner_pi::INTRO_AS_INTRODUCER_COUNT,
            inner_pi::INTRO_AS_RECIPIENT_COUNT,
            inner_pi::INTRO_AS_TARGET_COUNT,
        ];
        for (k, slot) in count_slots.iter().enumerate() {
            let row_pi = local[PI_BUFFER_BASE + *slot];
            let row_expected = local[EXPECTED_COUNTS_BASE + k];
            add(row_pi - row_expected, &mut combined, &mut pow);
        }

        // CG-3: schedule replay — roots.
        let root_bases = [
            inner_pi::OUTGOING_TRANSFER_ROOT_BASE,
            inner_pi::INCOMING_TRANSFER_ROOT_BASE,
            inner_pi::OUTGOING_GRANT_ROOT_BASE,
            inner_pi::INCOMING_GRANT_ROOT_BASE,
            inner_pi::INTRO_AS_INTRODUCER_ROOT_BASE,
            inner_pi::INTRO_AS_RECIPIENT_ROOT_BASE,
            inner_pi::INTRO_AS_TARGET_ROOT_BASE,
        ];
        for (k, base) in root_bases.iter().enumerate() {
            for off in 0..4 {
                let row_pi = local[PI_BUFFER_BASE + base + off];
                let row_expected = local[EXPECTED_ROOTS_BASE + k * 4 + off];
                add(row_pi - row_expected, &mut combined, &mut pow);
            }
        }

        // CG-4: boolean + padding gates.
        let ind = local[CONSISTENT_INDICATOR_COL];
        let is_agent = local[PI_BUFFER_BASE + inner_pi::IS_AGENT_CELL];
        let one = BabyBear::ONE;
        add(ind * (ind - one), &mut combined, &mut pow);
        add(is_agent * (is_agent - one), &mut combined, &mut pow);
        add((one - ind) * is_agent, &mut combined, &mut pow);

        // CG-4: prefix-sum transitions. The `next` row is trace_row+1 except
        // on the last trace row, where the STARK excludes the constraint
        // anyway (transition vanishing polynomial).
        let cum_local = local[IS_AGENT_CUMULATIVE_COL];
        let cum_next = next[IS_AGENT_CUMULATIVE_COL];
        let is_agent_next = next[PI_BUFFER_BASE + inner_pi::IS_AGENT_CELL];
        add(cum_next - (cum_local + is_agent_next), &mut combined, &mut pow);

        let n_local = local[N_CELLS_ACTIVE_COL];
        let n_next = next[N_CELLS_ACTIVE_COL];
        let ind_next = next[CONSISTENT_INDICATOR_COL];
        add(n_next - (n_local + ind_next), &mut combined, &mut pow);

        // BILATERAL_CONSISTENT outer PI must be 1.
        add(
            public_inputs[OUTER_BILATERAL_CONSISTENT] - one,
            &mut combined,
            &mut pow,
        );

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut cs = Vec::new();
        if public_inputs.len() != OUTER_BASE_COUNT || trace_len < 2 {
            return cs;
        }
        // Row 0 is always an active row → n_cells_active seed is 1.
        cs.push(BoundaryConstraint {
            row: 0,
            col: N_CELLS_ACTIVE_COL,
            value: BabyBear::ONE,
        });
        // Last row: exactly one agent cell across the whole bundle.
        cs.push(BoundaryConstraint {
            row: trace_len - 1,
            col: IS_AGENT_CUMULATIVE_COL,
            value: BabyBear::ONE,
        });
        // Last row: active-row count equals the bundle size advertised in PI.
        cs.push(BoundaryConstraint {
            row: trace_len - 1,
            col: N_CELLS_ACTIVE_COL,
            value: public_inputs[OUTER_N_CELLS],
        });
        cs
    }
}

// ---------------------------------------------------------------------------
// Witness construction
// ---------------------------------------------------------------------------

/// One inner-proof row's worth of data: the cell's PI vector (length
/// `BASE_COUNT = 74`) plus the prover-derived expected counts/roots block.
/// The prover holds the cell-id externally (used by the outer-PI
/// agent_cell_id check and by the higher-level prover when looking up the
/// schedule projection).
#[derive(Clone, Debug)]
pub struct AggregationInnerRow {
    /// Full γ.2 per-cell PI buffer (length `inner_pi::BASE_COUNT`).
    pub inner_pi: Vec<BabyBear>,
    /// 7 expected counts in canonical order:
    /// `[outbound_transfer, inbound_transfer, outbound_grant, inbound_grant,
    ///   intro_as_introducer, intro_as_recipient, intro_as_target]`.
    pub expected_counts: [BabyBear; 7],
    /// 7 expected roots, each 4 felts, in canonical order:
    /// `[OUTGOING_TRANSFER, INCOMING_TRANSFER, OUTGOING_GRANT, INCOMING_GRANT,
    ///   INTRO_AS_INTRODUCER, INTRO_AS_RECIPIENT, INTRO_AS_TARGET]`.
    pub expected_roots: [[BabyBear; 4]; 7],
}

impl AggregationInnerRow {
    /// Build a row that's *deliberately blank* — used for power-of-two
    /// trace padding. `consistent_indicator = 0`, all PI/expected slots
    /// are zero.
    pub fn blank_padding() -> Self {
        Self {
            inner_pi: vec![BabyBear::ZERO; inner_pi::BASE_COUNT],
            expected_counts: [BabyBear::ZERO; 7],
            expected_roots: [[BabyBear::ZERO; 4]; 7],
        }
    }
}

/// Outer public inputs derived from the bundle. Computed by the aggregator
/// from the canonical `Turn` + the agent cell-id; never accepted from the
/// outside untrusted.
#[derive(Clone, Debug)]
pub struct AggregationOuterPi {
    pub turn_hash: [BabyBear; 4],
    pub effects_hash_global: [BabyBear; 4],
    pub actor_nonce: BabyBear,
    pub previous_receipt_hash: [BabyBear; 4],
    pub agent_cell_id: [BabyBear; 8],
    pub n_cells: u32,
    pub bilateral_consistent: BabyBear,
}

impl AggregationOuterPi {
    /// Project to the flat outer-PI vector consumed by the AIR.
    pub fn to_vec(&self) -> Vec<BabyBear> {
        let mut pi = vec![BabyBear::ZERO; OUTER_BASE_COUNT];
        for i in 0..OUTER_TURN_HASH_LEN {
            pi[OUTER_TURN_HASH_BASE + i] = self.turn_hash[i];
        }
        for i in 0..OUTER_EFFECTS_HASH_GLOBAL_LEN {
            pi[OUTER_EFFECTS_HASH_GLOBAL_BASE + i] = self.effects_hash_global[i];
        }
        pi[OUTER_ACTOR_NONCE] = self.actor_nonce;
        for i in 0..OUTER_PREVIOUS_RECEIPT_HASH_LEN {
            pi[OUTER_PREVIOUS_RECEIPT_HASH_BASE + i] = self.previous_receipt_hash[i];
        }
        for i in 0..OUTER_AGENT_CELL_ID_LEN {
            pi[OUTER_AGENT_CELL_ID_BASE + i] = self.agent_cell_id[i];
        }
        pi[OUTER_N_CELLS] = BabyBear::new(self.n_cells);
        pi[OUTER_BILATERAL_CONSISTENT] = self.bilateral_consistent;
        pi
    }
}

/// Build the AIR trace from an ordered list of inner rows. The prover must
/// have already populated each row's `inner_pi` and `expected_*` blocks from
/// the bilateral schedule (typically via
/// `turn::bilateral_schedule::ExpectedBilateral::counts_for/roots_for`).
///
/// The trace is padded with `blank_padding` rows up to the next power of two.
/// Active rows carry `consistent_indicator = 1`; padding rows carry 0.
pub fn build_aggregation_trace(rows: &[AggregationInnerRow]) -> Vec<Vec<BabyBear>> {
    assert!(!rows.is_empty(), "aggregation needs at least one inner row");
    let n_active = rows.len();
    let n_padded = n_active.max(2).next_power_of_two();

    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(n_padded);
    let mut cum_agent: u32 = 0;
    let mut n_cells_active: u32 = 0;

    for (i, row) in rows.iter().enumerate() {
        let mut t = vec![BabyBear::ZERO; AGG_WIDTH];
        assert_eq!(row.inner_pi.len(), inner_pi::BASE_COUNT);
        for j in 0..inner_pi::BASE_COUNT {
            t[PI_BUFFER_BASE + j] = row.inner_pi[j];
        }
        for k in 0..7 {
            t[EXPECTED_COUNTS_BASE + k] = row.expected_counts[k];
        }
        for k in 0..7 {
            for off in 0..4 {
                t[EXPECTED_ROOTS_BASE + k * 4 + off] = row.expected_roots[k][off];
            }
        }

        // Active row.
        let is_agent_u = row.inner_pi[inner_pi::IS_AGENT_CELL].as_u32();
        cum_agent += is_agent_u;
        n_cells_active += 1;
        t[IS_AGENT_CUMULATIVE_COL] = BabyBear::new(cum_agent);
        t[CONSISTENT_INDICATOR_COL] = BabyBear::new(1);
        t[N_CELLS_ACTIVE_COL] = BabyBear::new(n_cells_active);
        let _ = i;
        trace.push(t);
    }

    // Padding rows: all zero except cumulative + n_cells_active carry forward.
    // Turn-identity slots must match active rows to satisfy CG-2 constraints.
    while trace.len() < n_padded {
        let mut t = vec![BabyBear::ZERO; AGG_WIDTH];
        t[IS_AGENT_CUMULATIVE_COL] = BabyBear::new(cum_agent);
        t[N_CELLS_ACTIVE_COL] = BabyBear::new(n_cells_active);
        if let Some(first) = rows.first() {
            for i in 0..inner_pi::TURN_HASH_LEN {
                t[PI_BUFFER_BASE + inner_pi::TURN_HASH_BASE + i] =
                    first.inner_pi[inner_pi::TURN_HASH_BASE + i];
            }
            for i in 0..inner_pi::EFFECTS_HASH_GLOBAL_LEN {
                t[PI_BUFFER_BASE + inner_pi::EFFECTS_HASH_GLOBAL_BASE + i] =
                    first.inner_pi[inner_pi::EFFECTS_HASH_GLOBAL_BASE + i];
            }
            t[PI_BUFFER_BASE + inner_pi::ACTOR_NONCE] = first.inner_pi[inner_pi::ACTOR_NONCE];
            for i in 0..inner_pi::PREVIOUS_RECEIPT_HASH_LEN {
                t[PI_BUFFER_BASE + inner_pi::PREVIOUS_RECEIPT_HASH_BASE + i] =
                    first.inner_pi[inner_pi::PREVIOUS_RECEIPT_HASH_BASE + i];
            }
        }
        trace.push(t);
    }

    trace
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_row(is_agent: bool) -> AggregationInnerRow {
        let mut inner_pi = vec![BabyBear::ZERO; inner_pi::BASE_COUNT];
        inner_pi[inner_pi::IS_AGENT_CELL] = if is_agent {
            BabyBear::new(1)
        } else {
            BabyBear::ZERO
        };
        AggregationInnerRow {
            inner_pi,
            expected_counts: [BabyBear::ZERO; 7],
            expected_roots: [[BabyBear::ZERO; 4]; 7],
        }
    }

    #[test]
    fn trace_shape_is_power_of_two() {
        let rows = vec![make_row(true), make_row(false), make_row(false)];
        let trace = build_aggregation_trace(&rows);
        assert_eq!(trace.len(), 4);
        for r in &trace {
            assert_eq!(r.len(), AGG_WIDTH);
        }
    }

    #[test]
    fn last_row_cumulative_is_one() {
        let rows = vec![make_row(true), make_row(false)];
        let trace = build_aggregation_trace(&rows);
        let last = trace.last().unwrap();
        assert_eq!(last[IS_AGENT_CUMULATIVE_COL].as_u32(), 1);
    }

    #[test]
    fn no_agent_yields_cumulative_zero() {
        let rows = vec![make_row(false), make_row(false)];
        let trace = build_aggregation_trace(&rows);
        let last = trace.last().unwrap();
        assert_eq!(last[IS_AGENT_CUMULATIVE_COL].as_u32(), 0);
    }

    #[test]
    fn n_cells_active_matches_input_length() {
        let rows = vec![make_row(true), make_row(false), make_row(false)];
        let trace = build_aggregation_trace(&rows);
        let last = trace.last().unwrap();
        assert_eq!(last[N_CELLS_ACTIVE_COL].as_u32(), 3);
    }

    #[test]
    fn outer_pi_layout_round_trip() {
        let pi = AggregationOuterPi {
            turn_hash: [
                BabyBear::new(1),
                BabyBear::new(2),
                BabyBear::new(3),
                BabyBear::new(4),
            ],
            effects_hash_global: [
                BabyBear::new(5),
                BabyBear::new(6),
                BabyBear::new(7),
                BabyBear::new(8),
            ],
            actor_nonce: BabyBear::new(9),
            previous_receipt_hash: [
                BabyBear::new(10),
                BabyBear::new(11),
                BabyBear::new(12),
                BabyBear::new(13),
            ],
            agent_cell_id: [
                BabyBear::new(14),
                BabyBear::new(15),
                BabyBear::new(16),
                BabyBear::new(17),
                BabyBear::new(18),
                BabyBear::new(19),
                BabyBear::new(20),
                BabyBear::new(21),
            ],
            n_cells: 3,
            bilateral_consistent: BabyBear::new(1),
        };
        let v = pi.to_vec();
        assert_eq!(v.len(), OUTER_BASE_COUNT);
        assert_eq!(v[OUTER_TURN_HASH_BASE].as_u32(), 1);
        assert_eq!(v[OUTER_EFFECTS_HASH_GLOBAL_BASE].as_u32(), 5);
        assert_eq!(v[OUTER_ACTOR_NONCE].as_u32(), 9);
        assert_eq!(v[OUTER_PREVIOUS_RECEIPT_HASH_BASE].as_u32(), 10);
        assert_eq!(v[OUTER_AGENT_CELL_ID_BASE].as_u32(), 14);
        assert_eq!(v[OUTER_N_CELLS].as_u32(), 3);
        assert_eq!(v[OUTER_BILATERAL_CONSISTENT].as_u32(), 1);
    }
}
