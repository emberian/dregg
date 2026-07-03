//! **The lifecycle apply layer** — pure operations over a vat `Cell` (unit-testable
//! and executor-seedable), the same shape [`starbridge_execution_lease`] uses for
//! `open_lease` / `advance_checkpoint`.
//!
//! A vat cell IS a lease cell (its economics + durable image are the lease's), so
//! [`open_vat`] first opens the lease, then seals the vat's lifecycle slots at
//! [`VatState::Created`]. Every lifecycle move — launch / sleep / wake / lapse /
//! reap — is [`apply_transition`]: it reads the current two-axis state, refuses an
//! illegal move ([`VatTransition::is_legal_from`]), and writes the new
//! `(phase, up)` slots. Because the phase slot is `Monotonic` and up is free, the
//! executor re-enforces exactly this machine on the committed turn — a caller that
//! hand-writes an illegal state (e.g. un-lapsing) is bitten by the tooth, and this
//! pure layer refuses it up front so the two agree.

use dregg_cell::Cell;
use starbridge_execution_lease::{
    self as lease, FieldElement, LeaseError, LeaseTerms, field_from_u64, field_to_u64,
};

use crate::{
    ENDPOINT_SLOT, MACHINE_SLOT, VAT_PHASE_SLOT, VAT_UP_SLOT, VatState, VatTransition, WITNESS_SLOT,
};

/// Why a vat lifecycle operation failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VatError {
    /// The underlying lease could not be opened (ill-formed terms / meter error).
    Lease(LeaseError),
    /// The vat's lifecycle slots are missing or hold a forged/contradictory pair
    /// (e.g. `up` set on a terminal phase) — the cell is not a well-formed vat.
    MalformedState,
    /// The requested transition is not legal from the vat's current state (the
    /// lifecycle machine refused it — see [`VatTransition::is_legal_from`]). This is
    /// the same refusal the executor's `Monotonic(VAT_PHASE)` tooth would deliver.
    IllegalTransition {
        from: VatState,
        transition: VatTransition,
    },
}

impl From<LeaseError> for VatError {
    fn from(e: LeaseError) -> Self {
        VatError::Lease(e)
    }
}

/// The renter's witness stance for a vat (mirrors the slot encoding in
/// [`WITNESS_SLOT`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WitnessStance {
    /// Cheap, verify-later — deferred witnesses re-derived on collapse.
    Symbolic,
    /// Proof-as-you-go.
    Full,
}

impl WitnessStance {
    fn as_u64(self) -> u64 {
        match self {
            WitnessStance::Symbolic => 0,
            WitnessStance::Full => 1,
        }
    }
}

/// **Open a vat** on a cell: open the underlying durable-execution lease (the
/// economics + genesis execution image), then seal the vat's lifecycle at
/// [`VatState::Created`] — phase `Provisioned`, not up, no box/endpoint, and the
/// renter's sealed [`WitnessStance`]. After this the cell's commitment binds a
/// provisioned-but-never-run Dregg Computer.
pub fn open_vat(
    cell: &mut Cell,
    terms: &LeaseTerms,
    genesis_digest: FieldElement,
    witness: WitnessStance,
) -> Result<(), VatError> {
    lease::open_lease(cell, terms, genesis_digest)?;
    let st = &mut cell.state;
    // The lifecycle machine, at Created: phase Provisioned, up = 0.
    st.set_field(
        VAT_PHASE_SLOT as usize,
        field_from_u64(VatState::Created.phase().rank()),
    );
    st.set_field(VAT_UP_SLOT as usize, field_from_u64(0));
    st.set_field(MACHINE_SLOT as usize, field_from_u64(0));
    st.set_field(ENDPOINT_SLOT as usize, field_from_u64(0));
    // The renter's witness stance — WriteOnce, sealed at open.
    st.set_field(WITNESS_SLOT as usize, field_from_u64(witness.as_u64()));
    Ok(())
}

/// Read the vat's current two-axis lifecycle state off the cell, or
/// [`VatError::MalformedState`] if the slots are missing / a forged pair.
pub fn read_state(cell: &Cell) -> Result<VatState, VatError> {
    let phase = cell
        .state
        .get_field(VAT_PHASE_SLOT as usize)
        .map(|f| field_to_u64(&f))
        .ok_or(VatError::MalformedState)?;
    let up = cell
        .state
        .get_field(VAT_UP_SLOT as usize)
        .map(|f| field_to_u64(&f))
        .ok_or(VatError::MalformedState)?
        != 0;
    VatState::from_slots(phase, up).ok_or(VatError::MalformedState)
}

/// **Apply a lifecycle transition** to a vat cell — the pure (unit-test / seed)
/// form of every lifecycle move. Reads the current state, refuses an illegal
/// transition (the machine's own tooth, up front so it agrees with the executor's
/// `Monotonic(VAT_PHASE)` re-enforcement), then writes the new `(phase, up)` slots.
///
///   * a **BringUp** (launch/wake) → phase `Live`, up = 1, and binds `machine` +
///     `endpoint` (the box the World is placed on, re-bound freely each placement);
///   * a **Sleep** → phase held `Live`, up = 0, box/endpoint cleared (the durable
///     image is what follows, not the box);
///   * a **Lapse** → phase `Lapsed`, up = 0 (the lifecycle mirror of the lease's own
///     LAPSED tooth — a lapsed vat's delivery is dark);
///   * a **Reap** → phase `Reaped` (terminal), up = 0.
///
/// Returns the new [`VatState`]. `machine`/`endpoint` are ignored except on BringUp.
pub fn apply_transition(
    cell: &mut Cell,
    transition: VatTransition,
    machine: u64,
    endpoint: u64,
) -> Result<VatState, VatError> {
    let from = read_state(cell)?;
    if !transition.is_legal_from(from) {
        return Err(VatError::IllegalTransition { from, transition });
    }
    let to = transition.target();
    let st = &mut cell.state;
    st.set_field(VAT_PHASE_SLOT as usize, field_from_u64(to.phase().rank()));
    st.set_field(
        VAT_UP_SLOT as usize,
        field_from_u64(if to.is_up() { 1 } else { 0 }),
    );
    match transition {
        VatTransition::BringUp => {
            // Place the box: bind the machine + reachable endpoint the starbridge
            // attaches to. Re-bound freely each (re)placement — the box is fungible.
            st.set_field(MACHINE_SLOT as usize, field_from_u64(machine));
            st.set_field(ENDPOINT_SLOT as usize, field_from_u64(endpoint));
        }
        VatTransition::Sleep | VatTransition::Lapse | VatTransition::Reap => {
            // No box while not Running. The durable image (the lease's EXEC_COLL)
            // is what follows; the box + address go dark.
            st.set_field(MACHINE_SLOT as usize, field_from_u64(0));
            st.set_field(ENDPOINT_SLOT as usize, field_from_u64(0));
        }
    }
    Ok(to)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::{Cell, CellId};

    /// Build a fresh vat cell opened with a simple well-formed lease.
    fn fresh_vat() -> Cell {
        // A minimal cell + lease terms (mirrors execution-lease's own test setup:
        // provider/lease/asset ids, positive rent + period).
        let lease_id = CellId::from_bytes([0x01; 32]);
        let provider = CellId::from_bytes([0x02; 32]);
        let asset = CellId::from_bytes([0x03; 32]);
        let mut cell = Cell::with_balance([0x01; 32], [0x03; 32], 0);
        let terms = LeaseTerms::new(provider, lease_id, asset, 100, 50, 1000, 0);
        let genesis = field_from_u64(0);
        open_vat(&mut cell, &terms, genesis, WitnessStance::Symbolic)
            .expect("a well-formed vat opens");
        cell
    }

    #[test]
    fn a_fresh_vat_opens_at_created() {
        let cell = fresh_vat();
        assert_eq!(read_state(&cell).unwrap(), VatState::Created);
        // The witness stance sealed at open.
        assert_eq!(
            field_to_u64(
                cell.state
                    .get_field(WITNESS_SLOT as usize)
                    .as_ref()
                    .unwrap()
            ),
            0,
            "Symbolic sealed"
        );
    }

    #[test]
    fn the_full_lifecycle_walk_is_legal_and_binds_the_box() {
        let mut cell = fresh_vat();
        // launch: Created → Running, binds a box + endpoint.
        assert_eq!(
            apply_transition(&mut cell, VatTransition::BringUp, 0xB0, 0xE0).unwrap(),
            VatState::Running
        );
        assert_eq!(read_state(&cell).unwrap(), VatState::Running);
        assert_eq!(
            field_to_u64(
                cell.state
                    .get_field(MACHINE_SLOT as usize)
                    .as_ref()
                    .unwrap()
            ),
            0xB0
        );
        // sleep: Running → Sleeping, box goes dark, phase held Live.
        assert_eq!(
            apply_transition(&mut cell, VatTransition::Sleep, 0, 0).unwrap(),
            VatState::Sleeping
        );
        assert_eq!(
            field_to_u64(
                cell.state
                    .get_field(MACHINE_SLOT as usize)
                    .as_ref()
                    .unwrap()
            ),
            0,
            "no box while asleep"
        );
        // wake: Sleeping → Running, re-placed on a FRESH box (fungible).
        assert_eq!(
            apply_transition(&mut cell, VatTransition::BringUp, 0xB1, 0xE1).unwrap(),
            VatState::Running
        );
        assert_eq!(
            field_to_u64(
                cell.state
                    .get_field(MACHINE_SLOT as usize)
                    .as_ref()
                    .unwrap()
            ),
            0xB1,
            "re-placed on a new box on wake"
        );
        // reap: Running → Reaped (terminal).
        assert_eq!(
            apply_transition(&mut cell, VatTransition::Reap, 0, 0).unwrap(),
            VatState::Reaped
        );
    }

    #[test]
    fn an_illegal_transition_is_refused_before_it_writes() {
        let mut cell = fresh_vat();
        // Cannot sleep a vat that never ran (Created).
        let err = apply_transition(&mut cell, VatTransition::Sleep, 0, 0).unwrap_err();
        assert_eq!(
            err,
            VatError::IllegalTransition {
                from: VatState::Created,
                transition: VatTransition::Sleep
            }
        );
        // The state is untouched by the refused move.
        assert_eq!(read_state(&cell).unwrap(), VatState::Created);
    }

    #[test]
    fn a_reaped_vat_admits_nothing() {
        let mut cell = fresh_vat();
        apply_transition(&mut cell, VatTransition::Reap, 0, 0).unwrap();
        for t in [
            VatTransition::BringUp,
            VatTransition::Sleep,
            VatTransition::Lapse,
            VatTransition::Reap,
        ] {
            assert!(
                apply_transition(&mut cell, t, 0, 0).is_err(),
                "{t:?} must be refused from the terminal Reaped state"
            );
        }
    }
}
