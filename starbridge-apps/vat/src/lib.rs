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
//! This crate is a **dregg-native rewrite** of a prior imperative fleet-controller
//! (ported from a prior imperative controller; the substrate is the source of truth).
//! the prior fleet-controller's economic + durability halves were ALREADY native, so this crate
//! builds directly on them instead of reinventing:
//!
//! * **persist** — the durable World is the lease cell's committed umem
//! execution image ([`starbridge_execution_lease::EXEC_COLL`]): a checkpoint
//! cursor + a state digest + the running World's working memory, folded into
//! the cell's state commitment. It survives, is passable, is witnessed.
//! * **meter** — uptime is a [`dregg_cell::obligation_standing`] StandingObligation
//! ([`starbridge_execution_lease::RENT_SLOT`]/[`PERIOD_SLOT`](starbridge_execution_lease::PERIOD_SLOT)):
//! the vat owes rent per period; the recurring forge-detectors bite.
//! * **pay** — rent is a [`dregg_app_framework::Payable`] conserving `Transfer`
//! (Σδ=0): renting the computer moves real value.
//! * **fork** — a vat forks by cloning its execution-image cell (the branch/
//! stitch pushout) — two divergent computers from one point.
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
//! Created ──launch──▶ Running ──sleep──▶ Sleeping ──wake──▶ Running
//! │ │ │ │
//! └───────────────────┴──── lapse (non-payment) ────────────▶ Lapsed
//! (reap) ────────────────────────────────▶ Reaped
//! ```
//!
//! Every transition — `launch` / `sleep` / `wake` / `lapse` / `reap` — is a
//! verified turn. The machine is encoded on TWO executor-enforced axes (because it
//! is not linear — sleep/wake move up and down *within* being alive):
//!
//! * the **phase** slot ([`VAT_PHASE_SLOT`], `Monotonic`): the one-way terminality
//! axis `Provisioned < Live < Lapsed < Reaped` — Reaped is terminal, Lapsed
//! cannot un-lapse, and Running/Sleeping share the `Live` phase;
//! * the **up** slot ([`VAT_UP_SLOT`], not monotone): whether a box currently runs
//! the World — sleep flips it down, wake flips it back up, without ever moving
//! the monotone phase.
//!
//! **Sleep = checkpoint** (the World's whole state committed to the durable image
//! root); **wake = restore** from that root. Splitting liveness out of the
//! terminality rank is what lets a wake be a legal turn under the phase tooth. The
//! backend machine is a thin operational adapter above this cell — the *state* is
//! the cell, the *box* is fungible.
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

/// The lifecycle apply layer — pure open_vat + apply_transition over a vat Cell.
pub mod lifecycle;

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

/// Slot 8 — `vat_phase`. The **terminality rank** (the phase rank ([`VatPhase::rank`])): how
/// far along the one-way lifecycle a vat is — `Provisioned(0) < Live(1) <
/// Lapsed(2) < Reaped(3)`. `Monotonic`: a vat only ever moves FORWARD along this
/// axis (Reaped is terminal; Lapsed cannot un-lapse). Crucially this rank does NOT
/// distinguish Running from Sleeping — both are `Live` — so sleep/wake (which
/// toggle the *liveness* axis below) never rewind it, and the `Monotonic` tooth is
/// exactly the terminality machine, no more no less.
pub const VAT_PHASE_SLOT: u8 = 8;
/// Slot 7 — `up`. The **liveness axis**: `1` = a box currently holds the running
/// World (Running), `0` = no box (Provisioned/Sleeping/Lapsed/Reaped). This slot is
/// NOT monotone — sleep flips it 1→0, wake flips it 0→1 — and it is meaningful only
/// while the phase is `Live` (a Lapsed/Reaped vat is definitionally down). Splitting
/// liveness OUT of the terminality rank is what lets a wake be a legal turn under
/// the phase's `Monotonic` tooth (the earlier single-rank encoding made wake
/// illegally *lower* the rank — the tooth would have refused a legal wake).
pub const VAT_UP_SLOT: u8 = 7;
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

/// A vat's lifecycle state — the Dregg Computer's power state. Encoded on TWO
/// executor-enforced axes rather than one linear rank, because the machine is not
/// linear: sleep/wake move a vat up and down *within* being alive, while the
/// terminality axis only ever advances.
///
/// * **phase** ([`VatState::phase`] → [`VatPhase::rank`], slot [`VAT_PHASE_SLOT`],
/// `Monotonic`): `Provisioned < Live < Lapsed < Reaped` — the one-way axis.
/// * **up** ([`VatState::is_up`], slot [`VAT_UP_SLOT`], NOT monotone): whether a
/// box currently runs the World. Meaningful only while `Live`.
///
/// So `Running` and `Sleeping` are BOTH `Live` (same phase rank) and differ only in
/// the `up` bit — a wake (`Sleeping`→`Running`) flips `up` 0→1 and leaves the
/// monotone phase untouched, which is what makes it a legal turn. `Reaped` is the
/// top phase (terminal); `Lapsed` cannot un-lapse (its phase already passed `Live`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VatState {
    /// Provisioned but never brought up — the lease exists, the box has never run.
    Created,
    /// Up: a backend machine holds the running World; metered per uptime period.
    Running,
    /// Alive but checkpointed to its durable image root and torn down — no box, no
    /// meter. Wakes by restoring from the image. Same PHASE as Running (`Live`);
    /// differs only in the `up` bit.
    Sleeping,
    /// Non-payment reclaimed the slot — the box is gone and stays gone until a
    /// fresh launch against a new paid period. Mirrors the lease's LAPSED tooth.
    Lapsed,
    /// Destroyed — terminal. The durable image may be retained for export, but the
    /// vat will never run again under this cell.
    Reaped,
}

/// The one-way terminality axis a vat travels — the `Monotonic`-enforced half of
/// the two-axis state (see [`VatState`]). `Running` and `Sleeping` share the `Live`
/// phase; only `up` tells them apart.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VatPhase {
    /// The lease exists; the box has never run.
    Provisioned,
    /// Alive — a box either runs the World (`up`) or is checkpointed asleep.
    Live,
    /// Non-payment reclaimed the slot.
    Lapsed,
    /// Destroyed — terminal.
    Reaped,
}

impl VatPhase {
    /// The monotone rank the executor pins on [`VAT_PHASE_SLOT`].
    pub fn rank(self) -> u64 {
        match self {
            VatPhase::Provisioned => 0,
            VatPhase::Live => 1,
            VatPhase::Lapsed => 2,
            VatPhase::Reaped => 3,
        }
    }

    /// Reconstruct from a slot rank; `None` for a forged out-of-range value.
    pub fn from_rank(rank: u64) -> Option<VatPhase> {
        Some(match rank {
            0 => VatPhase::Provisioned,
            1 => VatPhase::Live,
            2 => VatPhase::Lapsed,
            3 => VatPhase::Reaped,
            _ => return None,
        })
    }
}

impl VatState {
    /// This state's terminality phase (the monotone axis).
    pub fn phase(self) -> VatPhase {
        match self {
            VatState::Created => VatPhase::Provisioned,
            VatState::Running | VatState::Sleeping => VatPhase::Live,
            VatState::Lapsed => VatPhase::Lapsed,
            VatState::Reaped => VatPhase::Reaped,
        }
    }

    /// Whether a running box currently holds this vat (the `up` bit — metered,
    /// reachable). Only `Running` is up.
    pub fn is_up(self) -> bool {
        matches!(self, VatState::Running)
    }

    /// Reconstruct the full state from the two slot axes (`phase_rank`, `up`) — the
    /// inverse of `(phase().rank(), is_up())`. `None` for a forged/contradictory
    /// pair (e.g. `up` set on a non-Live phase).
    pub fn from_slots(phase_rank: u64, up: bool) -> Option<VatState> {
        Some(match (VatPhase::from_rank(phase_rank)?, up) {
            (VatPhase::Provisioned, false) => VatState::Created,
            (VatPhase::Live, true) => VatState::Running,
            (VatPhase::Live, false) => VatState::Sleeping,
            (VatPhase::Lapsed, false) => VatState::Lapsed,
            (VatPhase::Reaped, false) => VatState::Reaped,
            // `up` is only ever set while Live; any other pairing is a forged slot.
            _ => return None,
        })
    }

    /// The reader-legible word (matches the retired the prior state enum words so existing
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
/// * `Monotonic` on `VAT_STATE` — the lifecycle rank only advances (the state
/// machine, enforced as an order — see [`VatState`]);
/// * `WriteOnce` on `WITNESS` — the renter's chosen witness mode is sealed at
/// create; a provider cannot silently downgrade a Full vat to skip proofs.
///
/// (`MACHINE`/`ENDPOINT` are deliberately NOT sealed — a vat re-placed on wake
/// gets a fresh box + address; the durable image is what follows.)
pub fn vat_invariants() -> Vec<StateConstraint> {
    let mut cs = lease::lease_invariants();
    cs.push(StateConstraint::Monotonic {
        index: VAT_PHASE_SLOT,
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
    fn the_phase_axis_is_a_monotone_lattice_and_states_round_trip_two_slots() {
        // The MONOTONE axis is the phase; Running and Sleeping share it (both Live).
        assert_eq!(VatState::Running.phase(), VatPhase::Live);
        assert_eq!(VatState::Sleeping.phase(), VatPhase::Live);
        assert_eq!(
            VatState::Running.phase().rank(),
            VatState::Sleeping.phase().rank(),
            "Running and Sleeping share the Live phase rank — sleep/wake never move it"
        );
        // The phase ranks are strictly ordered.
        let phases = [
            VatPhase::Provisioned,
            VatPhase::Live,
            VatPhase::Lapsed,
            VatPhase::Reaped,
        ];
        for w in phases.windows(2) {
            assert!(w[0].rank() < w[1].rank(), "{:?} < {:?}", w[0], w[1]);
        }
        // Every state round-trips through its two slot axes (phase_rank, up).
        for s in [
            VatState::Created,
            VatState::Running,
            VatState::Sleeping,
            VatState::Lapsed,
            VatState::Reaped,
        ] {
            assert_eq!(
                VatState::from_slots(s.phase().rank(), s.is_up()),
                Some(s),
                "{s:?} round-trips through (phase_rank, up)"
            );
        }
        // A forged slot pair (up set on a non-Live phase) is rejected.
        assert_eq!(
            VatState::from_slots(VatPhase::Reaped.rank(), true),
            None,
            "up on a terminal phase is a forged, rejected pairing"
        );
        assert_eq!(
            VatState::from_slots(99, false),
            None,
            "a forged phase rank is rejected"
        );
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
    fn a_legal_transition_never_lowers_the_phase_rank() {
        // The executor tooth is Monotonic(VAT_PHASE): prove every legal transition
        // holds-or-raises the PHASE rank, so the tooth admits exactly the legal
        // machine — AND a wake (Sleeping→Running), which lowers the old single
        // linear rank, HOLDS the phase (both Live) so the tooth admits it. This is
        // the regression the two-axis split fixes.
        use VatState::*;
        use VatTransition::*;
        let states = [Created, Running, Sleeping, Lapsed, Reaped];
        for from in states {
            for t in [BringUp, Sleep, Lapse, Reap] {
                if t.is_legal_from(from) {
                    assert!(
                        t.target().phase().rank() >= from.phase().rank(),
                        "legal {t:?} from {from:?} lowered the phase rank"
                    );
                }
            }
        }
        // Explicitly: the wake that used to be refused now holds the phase.
        assert!(BringUp.is_legal_from(Sleeping));
        assert_eq!(
            BringUp.target().phase().rank(),
            Sleeping.phase().rank(),
            "wake holds the monotone phase (Live→Live) — the tooth admits it"
        );
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
            "vat = lease invariants + Monotonic(VAT_PHASE) + WriteOnce(WITNESS)"
        );
        assert!(
            vat_cs.iter().any(|c| matches!(
            c,
            StateConstraint::Monotonic { index } if *index == VAT_PHASE_SLOT
            )),
            "the lifecycle machine tooth is present"
        );
    }
}
