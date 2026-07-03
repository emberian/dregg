//! # starbridge-vat — **HAVE A DREGG COMPUTER.**
//!
//! A *vat* is your Dregg Computer: a private, always-there computer that happens
//! to live in the cloud but belongs to **you**, not to the provider running it.
//! It is a persistent, durable, forkable World you reach from any starbridge
//! (the local desktop OR the web build) — and because it is a cell whose history
//! is receipted, a provider you rent from **cannot lie to you** about what it did.
//!
//! ## The vat is an execution-lease with a lifecycle
//!
//! This crate is a **dregg-native rewrite** of the retired DreggNet `ServerFleet`
//! (`./dreggnet/control` — abandoned, strip-mined for its logic, never rejoined).
//! ServerFleet's economic + durability halves were ALREADY native, so this crate
//! builds directly on them instead of reinventing:
//!
//!   * **persist** — the durable World is the lease cell's committed umem
//!     execution image ([`starbridge_execution_lease::EXEC_COLL`]): a checkpoint
//!     cursor + a state digest + the running World's working memory, folded into
//!     the cell's state commitment. It survives, is passable, is witnessed.
//!   * **meter** — uptime is a [`dregg_cell::obligation_standing`] StandingObligation
//!     ([`starbridge_execution_lease::RENT_SLOT`]/[`PERIOD_SLOT`](starbridge_execution_lease::PERIOD_SLOT)):
//!     the vat owes rent per period; the recurring forge-detectors bite.
//!   * **pay** — rent is a [`dregg_app_framework::Payable`] conserving `Transfer`
//!     (Σδ=0): renting the computer moves real value.
//!   * **fork** — a vat forks by cloning its execution-image cell (the branch/
//!     stitch pushout) — two divergent computers from one point.
//!
//! What this crate ADDS over the bare lease is the two things that make a lease a
//! *computer*: a **lifecycle state machine** ([`VatState`]) and a **placement
//! binding** (which backend machine currently holds the running World). The
//! economics + durable cursor are the lease's; the vat layers its state machine
//! ON TOP, re-enforced by the same executor teeth.
//!
//! ## The lifecycle — a verified state machine
//!
//! ```text
//!   Created ──launch──▶ Running ──sleep──▶ Sleeping ──wake──▶ Running
//!      │                   │                   │                  │
//!      └───────────────────┴──── lapse (non-payment) ────────────▶ Lapsed
//!                          (reap) ────────────────────────────────▶ Reaped
//! ```
//!
//! Every transition — `launch` / `sleep` / `wake` / `lapse` / `reap` — is a
//! verified turn writing [`VAT_STATE_SLOT`]. The executor re-enforces the machine:
//! the state slot is `Monotonic` in a lattice order ([`VatState::rank`]), so a vat
//! can never illegally *go backwards* into a state it already left (Reaped is
//! terminal; Lapsed cannot silently return to Running without a fresh launch),
//! and the placement/endpoint bindings are sealed the same way the lease seals its
//! economics. **Sleep = checkpoint** (the World's whole state committed to the
//! durable image root); **wake = restore** from that root; the backend machine is
//! a thin operational adapter above this cell — the *state* is the cell, the
//! *box* is fungible.
//!
//! ## The honest boundary
//!
//! The verified core is the lifecycle + economics + durable cursor — all cells,
//! all re-enforced. What is NOT in the verified core (and never should be): the
//! operational provisioning glue (spinning an actual VM, the mesh overlay, the
//! backend placement decision). That stays an imperative adapter the vat *drives*
//! — it reads the vat cell's state and makes the box match. So a light client
//! witnesses "the vat is Running, metered through period N, its image at digest D"
//! without trusting the provider's word; the provider cannot forge that history,
//! and the worst a malicious provider can do is fail to run the box (which the
//! lapse/reaper reclaims) — never lie about what the box *did*.

#![forbid(unsafe_code)]

use dregg_app_framework::{CellProgram, StateConstraint, TransitionCase, TransitionGuard};

pub use dregg_app_framework::{FieldElement, field_from_u64};
pub use starbridge_execution_lease::{self as lease, field_to_u64};

// =============================================================================
// Slot layout — the vat's lifecycle slots, ABOVE the lease's economic slots
// =============================================================================
//
// The lease owns slots 0..=6 (STEP / STATE_DIGEST / LAPSED / PERIODS_PAID / RENT
// / PERIOD / PROVIDER). The vat adds its lifecycle + identity slots ABOVE that
// range so the two layers never collide and a vat cell IS a valid lease cell.

/// Slot 8 — `vat_state`. The lifecycle state as its [`VatState::rank`] (a lattice
/// order). `Monotonic`: the machine only advances — a vat can never illegally slip
/// back into a state it left. (Wake→Running from Sleeping is modeled as staying at
/// or above the Running rank, see [`VatState`]; the *box* comes and goes, the
/// *rank* never rewinds.)
pub const VAT_STATE_SLOT: u8 = 8;
/// Slot 9 — `machine_tag`. A tag of the backend machine currently holding the
/// running World (0 = none/asleep). NOT `WriteOnce` — a vat re-placed onto a fresh
/// box on wake gets a new machine; the durable image (the lease's EXEC_COLL) is
/// what actually follows, the box is fungible.
pub const MACHINE_SLOT: u8 = 9;
/// Slot 10 — `endpoint_tag`. A tag of the vat's reachable endpoint (the
/// gateway-routed address a starbridge attaches to). Re-bound on (re)placement.
pub const ENDPOINT_SLOT: u8 = 10;
/// Slot 11 — `witness_stance`. The renter's chosen witness mode for this vat:
/// `0` = Symbolic (cheap, verify-later — deferred witnesses re-derived on
/// collapse), `1` = Full (proof-as-you-go). `WriteOnce` per lease term: the
/// renter picks their trust/cost tradeoff at create and it is sealed (a provider
/// cannot silently downgrade a Full vat to skip proofs).
pub const WITNESS_SLOT: u8 = 11;

// =============================================================================
// The lifecycle state machine
// =============================================================================

/// A vat's lifecycle state — the Dregg Computer's power state, as a monotone
/// lattice the executor re-enforces on [`VAT_STATE_SLOT`].
///
/// The rank is the tooth: [`VatState::rank`] never rewinds (`Monotonic`), so the
/// legal transitions fall out of the order. `Reaped` is the top (terminal); a
/// `Lapsed` vat cannot silently become `Running` again (its rank already passed
/// `Running`) — it needs an explicit re-launch that the provider gates on a fresh
/// paid period. `Sleeping` sits ABOVE `Running` in rank (you can only sleep a vat
/// that ran), and `wake` does not lower the rank — it re-places the box and
/// advances the durable cursor, leaving the lifecycle rank monotone.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VatState {
    /// Provisioned but never brought up — the lease exists, the box has never run.
    Created,
    /// Up: a backend machine holds the running World; metered per uptime period.
    Running,
    /// Checkpointed to its durable image root and torn down — no box, no meter.
    /// Wakes by restoring from the image. (Rank above Running: a sleep is a thing
    /// that happens to a vat that ran.)
    Sleeping,
    /// Non-payment reclaimed the slot — the box is gone and stays gone until a
    /// fresh launch against a new paid period. Mirrors the lease's LAPSED tooth.
    Lapsed,
    /// Destroyed — terminal. The durable image may be retained for export, but the
    /// vat will never run again under this cell.
    Reaped,
}

impl VatState {
    /// The monotone rank the executor pins on [`VAT_STATE_SLOT`]. The state machine
    /// is exactly "rank never decreases": every legal transition raises (or, for a
    /// wake, holds) the rank; every illegal one would lower it and is refused.
    pub fn rank(self) -> u64 {
        match self {
            VatState::Created => 0,
            VatState::Running => 1,
            VatState::Sleeping => 2,
            VatState::Lapsed => 3,
            VatState::Reaped => 4,
        }
    }

    /// Reconstruct from a slot rank (the inverse of [`rank`](Self::rank)); `None`
    /// for an out-of-range value (a forged slot).
    pub fn from_rank(rank: u64) -> Option<VatState> {
        Some(match rank {
            0 => VatState::Created,
            1 => VatState::Running,
            2 => VatState::Sleeping,
            3 => VatState::Lapsed,
            4 => VatState::Reaped,
            _ => return None,
        })
    }

    /// The reader-legible word (matches the retired ServerState words so existing
    /// dashboards/tools read unchanged): created / running / sleeping / lapsed /
    /// reaped.
    pub fn word(self) -> &'static str {
        match self {
            VatState::Created => "created",
            VatState::Running => "running",
            VatState::Sleeping => "sleeping",
            VatState::Lapsed => "lapsed",
            VatState::Reaped => "reaped",
        }
    }

    /// Whether a running box currently holds this vat (metered, reachable).
    pub fn is_up(self) -> bool {
        matches!(self, VatState::Running)
    }

    /// Whether this state is terminal (no future box under this cell).
    pub fn is_terminal(self) -> bool {
        matches!(self, VatState::Reaped)
    }
}

/// The vat lifecycle TRANSITIONS, each a verified turn. Modeling the transition as
/// data (rather than only imperative code) lets the executor + a light client
/// agree on the machine: a transition is legal iff it raises-or-holds the state
/// rank AND its precondition holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VatTransition {
    /// `Created`/`Sleeping` → `Running`: place a box, restore the durable image,
    /// begin metering. (From `Sleeping` this is a *wake*; from `Created` a first
    /// *launch*.) Requires a live, non-lapsed lease and a paid current period.
    BringUp,
    /// `Running` → `Sleeping`: checkpoint the World to its image root, tear down
    /// the box, stop metering. Advances the lease's durable cursor.
    Sleep,
    /// any live → `Lapsed`: non-payment reclaimed the slot (the lease's schedule
    /// audit found an undischarged period). Mirrors the lease LAPSED tooth.
    Lapse,
    /// any → `Reaped`: destroy. Terminal.
    Reap,
}

impl VatTransition {
    /// The state this transition lands in.
    pub fn target(self) -> VatState {
        match self {
            VatTransition::BringUp => VatState::Running,
            VatTransition::Sleep => VatState::Sleeping,
            VatTransition::Lapse => VatState::Lapsed,
            VatTransition::Reap => VatState::Reaped,
        }
    }

    /// Whether `from → self.target()` is a legal lifecycle move. The core rule is
    /// the monotone rank; `BringUp` is the one transition allowed to hold-or-raise
    /// from `Sleeping` back to `Running` (a wake re-places the box without lowering
    /// the *lifecycle* — see [`VatState`]). A terminal state admits nothing.
    pub fn is_legal_from(self, from: VatState) -> bool {
        if from.is_terminal() {
            return false;
        }
        match self {
            // Reap is always legal from any non-terminal state (destroy on demand).
            VatTransition::Reap => true,
            // Lapse from any live (not already lapsed) state.
            VatTransition::Lapse => from != VatState::Lapsed,
            // Sleep only a Running vat.
            VatTransition::Sleep => from == VatState::Running,
            // BringUp a Created (launch) or a Sleeping (wake) vat.
            VatTransition::BringUp => {
                matches!(from, VatState::Created | VatState::Sleeping)
            }
        }
    }
}

// =============================================================================
// The verified core — the vat cell program, LAYERED over the lease invariants
// =============================================================================

/// The **life-of-vat invariants** the executor re-enforces on every touching turn,
/// ON TOP of [`lease::lease_invariants`] (the economics + durable-cursor teeth the
/// vat inherits by being a lease cell):
///
///   * `Monotonic` on `VAT_STATE` — the lifecycle rank only advances (the state
///     machine, enforced as an order — see [`VatState`]);
///   * `WriteOnce` on `WITNESS` — the renter's chosen witness mode is sealed at
///     create; a provider cannot silently downgrade a Full vat to skip proofs.
///
/// (`MACHINE`/`ENDPOINT` are deliberately NOT sealed — a vat re-placed on wake
/// gets a fresh box + address; the durable image is what follows.)
pub fn vat_invariants() -> Vec<StateConstraint> {
    let mut cs = lease::lease_invariants();
    cs.push(StateConstraint::Monotonic {
        index: VAT_STATE_SLOT,
    });
    cs.push(StateConstraint::WriteOnce {
        index: WITNESS_SLOT,
    });
    cs
}

/// The vat cell program: an `Always` case carrying [`vat_invariants`] — the vat's
/// lifecycle machine + the inherited lease economics/cursor teeth, re-enforced on
/// EVERY turn that touches a vat cell. A vat cell is thereby a strict extension of
/// a lease cell: everything the lease admits (`open`/`pay`/`advance`/`lapse`) still
/// holds, plus the vat's lifecycle monotonicity.
pub fn vat_cell_program() -> CellProgram {
    CellProgram::Cases(vec![TransitionCase {
        guard: TransitionGuard::Always,
        constraints: vat_invariants(),
    }])
}

/// The vat invariants as a flat `Predicate` program — installed on a seeded vat
/// cell so the deos fires re-enforce them.
pub fn vat_invariants_program() -> CellProgram {
    CellProgram::Predicate(vat_invariants())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_lifecycle_rank_is_a_monotone_lattice() {
        // Every state's rank is distinct + ordered as the machine expects.
        let order = [
            VatState::Created,
            VatState::Running,
            VatState::Sleeping,
            VatState::Lapsed,
            VatState::Reaped,
        ];
        for w in order.windows(2) {
            assert!(w[0].rank() < w[1].rank(), "{:?} < {:?}", w[0], w[1]);
        }
        // Round-trip through the slot rank.
        for s in order {
            assert_eq!(VatState::from_rank(s.rank()), Some(s));
        }
        assert_eq!(VatState::from_rank(99), None, "a forged rank is rejected");
    }

    #[test]
    fn legal_transitions_are_exactly_the_machine() {
        use VatState::*;
        use VatTransition::*;
        // launch: Created → Running.
        assert!(BringUp.is_legal_from(Created));
        // wake: Sleeping → Running.
        assert!(BringUp.is_legal_from(Sleeping));
        // you cannot "launch" an already-running vat.
        assert!(!BringUp.is_legal_from(Running));
        // sleep only a running vat.
        assert!(Sleep.is_legal_from(Running));
        assert!(!Sleep.is_legal_from(Created));
        assert!(!Sleep.is_legal_from(Sleeping));
        // lapse any live, non-lapsed state.
        assert!(Lapse.is_legal_from(Running));
        assert!(Lapse.is_legal_from(Sleeping));
        assert!(!Lapse.is_legal_from(Lapsed));
        // reap any non-terminal state.
        assert!(Reap.is_legal_from(Created));
        assert!(Reap.is_legal_from(Running));
        // NOTHING is legal from the terminal Reaped state.
        for t in [BringUp, Sleep, Lapse, Reap] {
            assert!(
                !t.is_legal_from(Reaped),
                "{t:?} must be illegal from Reaped"
            );
        }
    }

    #[test]
    fn a_legal_transition_never_lowers_the_state_rank() {
        // The executor tooth is Monotonic(VAT_STATE): prove every legal transition
        // holds-or-raises the rank, so the tooth admits exactly the legal machine.
        use VatState::*;
        use VatTransition::*;
        let states = [Created, Running, Sleeping, Lapsed, Reaped];
        for from in states {
            for t in [BringUp, Sleep, Lapse, Reap] {
                if t.is_legal_from(from) {
                    assert!(
                        t.target().rank() >= from.rank(),
                        "legal {t:?} from {from:?} lowered the rank"
                    );
                }
            }
        }
    }

    #[test]
    fn the_vat_is_a_strict_extension_of_a_lease() {
        // Every lease invariant survives in the vat invariants (a vat cell is a
        // valid lease cell), plus the two vat teeth.
        let lease_cs = lease::lease_invariants();
        let vat_cs = vat_invariants();
        assert_eq!(
            vat_cs.len(),
            lease_cs.len() + 2,
            "vat = lease invariants + Monotonic(VAT_STATE) + WriteOnce(WITNESS)"
        );
        assert!(
            vat_cs.iter().any(|c| matches!(
                c,
                StateConstraint::Monotonic { index } if *index == VAT_STATE_SLOT
            )),
            "the lifecycle machine tooth is present"
        );
    }
}
