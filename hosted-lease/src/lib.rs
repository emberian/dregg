//! # hosted-lease — the hosting lease, dregg-native.
//!
//! The operated layer rents durable execution to agents. This crate is that lease built on
//! the proven [`starbridge_execution_lease`] capacity rather than a local struct:
//! the meter is a real [`StandingObligation`](dregg_cell::obligation_standing)
//! whose forge-detectors bite (no early / double / over / under / skipped
//! discharge), the durable execution image is the lease cell's committed umem
//! heap (`EXEC_COLL`), and the checkpoint cursor is `Monotonic` — a rewind or
//! forge of the durable image is a real refusal the executor re-enforces.
//!
//! [`HostedLease`] is the seam a hosted runtime binds to. A Hermes/webcell
//! runtime reads the lease's durable image, runs the agent's code, and calls
//! [`HostedLease::checkpoint`] to advance the cursor with the new state digest and
//! whatever working memory the run produced — so the durable state survives, is
//! passable (a cell + its heap is a portable image), and is witnessed (a light
//! client sees the checkpoint cursor move). The rent is [`HostedLease::meter`] a
//! period (the amount a conserving `Transfer` must move to the provider) plus the
//! lapse audit that reclaims a delinquent slot.

use dregg_cell::Cell;

pub use starbridge_execution_lease::{
    EXEC_COLL, FieldElement, KEY_DIGEST, KEY_STEP, LeaseError, LeaseTerms, WORKING_BASE,
    advance_checkpoint, checkpoint_step, field_from_u64, is_lapsed, lapse_if_behind, meter_period,
    open_lease,
};

/// A durable-execution lease the operated layer hosts: the lease cell (rent obligor, payer,
/// and holder of the committed execution image) paired with its sealed terms.
/// The seam a hosted Hermes/webcell runtime binds to.
pub struct HostedLease {
    cell: Cell,
    terms: LeaseTerms,
}

impl HostedLease {
    /// Open a durable-execution lease on `cell` under `terms`, initialised to
    /// `genesis_digest` (the checkpoint of the agent's genesis execution image).
    /// Seals the rent obligation, pins the `WriteOnce` economics, and writes the
    /// genesis checkpoint into both the scalar slots and the committed heap.
    pub fn open(
        mut cell: Cell,
        terms: LeaseTerms,
        genesis_digest: FieldElement,
    ) -> Result<HostedLease, LeaseError> {
        open_lease(&mut cell, &terms, genesis_digest)?;
        Ok(HostedLease { cell, terms })
    }

    /// Meter one rent period: discharge the period on the standing obligation (the
    /// recurring forge-detectors bite) and return the rent amount a conserving
    /// `Transfer` must move from the lease to the provider. Does not itself move
    /// value — pair it with the platform's settlement (a real on-chain transfer).
    pub fn meter(&mut self, period_index: i64, clock: i64) -> Result<u64, LeaseError> {
        meter_period(&mut self.cell, &self.terms, period_index, clock)
    }

    /// Advance the durable execution image: move the checkpoint cursor forward,
    /// re-bind the state digest, and write the run's `working` memory (keys must be
    /// `>= WORKING_BASE`) into the committed image. Refuses on a lapsed lease. This
    /// is what a hosted runtime calls after a step of the agent's execution.
    pub fn checkpoint(
        &mut self,
        new_digest: FieldElement,
        working: &[(u32, FieldElement)],
    ) -> Result<u64, LeaseError> {
        advance_checkpoint(&mut self.cell, new_digest, working)
    }

    /// Lapse the lease if a rent period went undischarged by `clock` (the provider
    /// reclaims the slot; further delivery is refused). Returns whether it lapsed.
    pub fn lapse_if_behind(&mut self, clock: i64) -> Result<bool, LeaseError> {
        lapse_if_behind(&mut self.cell, &self.terms, clock)
    }

    /// Whether the lease has lapsed (non-payment).
    pub fn is_lapsed(&self) -> bool {
        is_lapsed(&self.cell)
    }

    /// The current durable checkpoint step (how many times the execution image has
    /// advanced).
    pub fn step(&self) -> u64 {
        checkpoint_step(&self.cell)
    }

    /// Read a working-memory value from the durable execution image (a key the
    /// hosted runtime wrote via [`checkpoint`](HostedLease::checkpoint)).
    pub fn read_working(&self, key: u32) -> Option<FieldElement> {
        self.cell.state.get_heap(EXEC_COLL, key)
    }

    /// The lease's sealed terms.
    pub fn terms(&self) -> &LeaseTerms {
        &self.terms
    }

    /// Borrow the underlying lease cell (for settlement / commitment / witnessing).
    pub fn cell(&self) -> &Cell {
        &self.cell
    }

    /// Mutably borrow the underlying lease cell — for a lifecycle layer that seals or
    /// advances its OWN state slots on the same cell (e.g. the vat lifecycle machine,
    /// slots disjoint from the lease's own `KEY_STEP`/`KEY_DIGEST`/working range). The
    /// caller is responsible for keeping the lease's economic slots intact; this does
    /// not re-open or re-meter the lease.
    pub fn cell_mut(&mut self) -> &mut Cell {
        &mut self.cell
    }

    /// Wrap an ALREADY-OPENED lease cell under `terms` — the constructor for a caller
    /// that opened the lease itself (e.g. via `starbridge_vat::lifecycle::open_vat`,
    /// which opens the lease AND seals the vat lifecycle in one pass), rather than
    /// through [`HostedLease::open`]. Does NOT call `open_lease`, so it never
    /// double-opens the (WriteOnce-sealed) economic slots.
    pub fn from_cell(cell: Cell, terms: LeaseTerms) -> HostedLease {
        HostedLease { cell, terms }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::{Cell, CellId};

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    fn lease_cell() -> Cell {
        Cell::with_balance([7u8; 32], [9u8; 32], 10_000)
    }

    /// provider=2, lease=7, asset=9; rent 100 every 50 blocks from block 1000.
    fn terms() -> LeaseTerms {
        LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0)
    }

    #[test]
    fn the_dregg_native_lease_lifecycle_holds_end_to_end() {
        let mut lease = HostedLease::open(lease_cell(), terms(), field_from_u64(0xB0))
            .expect("open a well-formed lease");
        assert_eq!(lease.step(), 0);
        assert!(!lease.is_lapsed());

        // Meter period 0: the rent is the sealed 100.
        assert_eq!(lease.meter(0, 1000), Ok(100));
        // The recurring forge-detector bites a double-discharge of the same period.
        assert!(lease.meter(0, 1000).is_err());
        // And a not-yet-due future period.
        assert!(lease.meter(1, 1000).is_err());

        // The hosted runtime advances the durable image twice, writing working mem.
        let s1 = lease
            .checkpoint(field_from_u64(0xA1), &[(WORKING_BASE, field_from_u64(42))])
            .expect("advance the checkpoint");
        assert_eq!(s1, 1);
        assert_eq!(lease.read_working(WORKING_BASE), Some(field_from_u64(42)));
        let s2 = lease
            .checkpoint(field_from_u64(0xA2), &[])
            .expect("advance again");
        assert_eq!(s2, 2);

        // Non-payment past the next due block lapses the lease; delivery then stops.
        let lapsed = lease.lapse_if_behind(1100).expect("audit the schedule");
        assert!(lapsed);
        assert!(lease.is_lapsed());
        assert!(
            lease.checkpoint(field_from_u64(0xA3), &[]).is_err(),
            "a lapsed lease refuses further delivery"
        );
    }

    #[test]
    fn ill_formed_terms_are_refused() {
        let bad = LeaseTerms::new(cid(2), cid(7), cid(9), 0, 50, 1000, 0);
        assert!(HostedLease::open(lease_cell(), bad, field_from_u64(0)).is_err());
    }
}
