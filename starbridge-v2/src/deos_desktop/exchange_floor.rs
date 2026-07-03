//! **THE EXCHANGE FLOOR** — the $DREGG agent economy as a desktop surface.
//!
//! The three closest crates to the services story already carry every tooth the
//! floor needs — `starbridge-apps/compute-exchange` (a job market whose installed
//! `CellProgram` IS the rules: `FieldLteField(BID <= BUDGET)`, `WriteOnce`
//! identity/amount registers, the settle-scoped FLASHWELL `AffineEq(PAID +
//! REFUNDED == BUDGET)`, `StrictMonotonic(STATE)`) and
//! `starbridge-apps/execution-lease` (durable execution metered per checkpoint,
//! `Monotonic(STEP)`) — but until this module the flagship desktop had no room
//! where an agent economy is WATCHABLE. This is that room: an **Exchange window**
//! where compute OFFERS are real CELLS on the desktop's LIVE `World`, where
//! posting an offer, taking it under a lease, and settling it are each a REAL
//! verified turn with a receipt on `World::receipts()`, and where a settled offer
//! shows **Σδ = 0** read straight off the live ledger (the executor-enforced
//! conservation, not a caption).
//!
//! ## What is REAL here (the honest ledger of teeth)
//!
//! * **An offer is a cell.** [`ExchangeFloorState::post_offer`] seeds a FRESH cell
//!   onto the live `World` carrying the compute-exchange crate's own
//!   [`starbridge_compute_exchange::job_program`] — then commits the `post` turn
//!   ([`post_effects`], the same effect-set the crate's `build_post_action`
//!   builds) through [`AppWorldSpine::commit`]. The cell stands on the desktop as
//!   an icon within one PULSE beat; the receipt is in the Transcript.
//! * **Taking a lease is two turns.** The floor's `take` commits the REAL `bid`
//!   turn on the offer cell (the executor re-enforces the BUDGET gate — an
//!   over-budget take is a REAL refusal, wired to a button so the tooth is
//!   demonstrable on the glass), and the desktop verb then advances one metered
//!   checkpoint on the App Shelf's execution-lease cell (the metering rail).
//! * **Settlement is Σδ = 0 by executor law.** `settle` reads the LIVE `BID` +
//!   `BUDGET` and pays the provider in full (`PAID := BID`, `REFUNDED := BUDGET −
//!   BID`); the installed `AffineEq(PAID + REFUNDED − BUDGET = 0)` is re-enforced
//!   by `World`'s executor on the commit. The window's settled row shows the
//!   delta recomputed from the live slots — 0, always, or the turn never landed.
//! * **The substrate is the App Shelf's.** The compute-exchange and
//!   execution-lease shelf apps are launched (if not installed) when the floor
//!   opens — the SAME [`super::app_shelf::AppShelfState::install_on_world`] flow,
//!   so the house job + the metering lease live beside the floor's own offers.
//!
//! ## The clobber-safe split
//!
//! * **gpui-free model** — [`ExchangeFloorState`] (the order book),
//!   [`ExchangeOffer`] (one posted offer: its cell + its committing spine),
//!   [`OfferFacts`] (the render-ready LIVE projection of one offer), the pure
//!   helpers ([`post_effects`], [`fair_price`], [`OfferPhase`],
//!   [`settlement_delta`]), and [`exchange_spotter_candidates`]. All of it
//!   compiles and `cargo test`s without a renderer.
//! * **presentation + actuation** — an `impl DeosDesktop` block (the house
//!   pattern `app_shelf.rs` uses): the View owns the `cx.listener` wiring, the NT
//!   order-book body, and the post/take/settle/cheat dispatch. Every actuation is
//!   a real committed turn on the shared `World`; every read is the LIVE ledger.
//!
//! ## Honest scope (the named seams)
//!
//! * **Phase 1 is one requester, one provider, fair-price takes.** The floor's
//!   verbs act for the operator (`requester-desk` posts, `provider-desk` takes at
//!   [`fair_price`]); a picker for counterparties / free-typed prices is the
//!   named follow-on. The teeth do not care — the executor refuses an over-budget
//!   take regardless of who asks (the cheat button proves it).
//! * **The lease rail is the shelf's single lease cell.** Every take advances the
//!   SAME execution-lease cell's durable cursor (one metering rail for the whole
//!   floor); per-take lease cells + rent settlement over promise-hole escrow
//!   (`app-framework/src/service_promise.rs`, which runs over `WideLedger`, not
//!   `World`) are the scout plan's later phases.
//! * **Offers are session-scoped** like the shelf's installs — re-seeding a
//!   reopened desktop's book is part of the receipted install-ceremony seam.

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, px, AnyElement, Context, InteractiveElement, IntoElement, MouseButton, MouseDownEvent,
    ParentElement, Styled,
};

use dregg_app_framework::{symbol, Effect, Event, TurnReceipt};
use dregg_types::CellId;

use starbridge_compute_exchange as job;
use starbridge_execution_lease as lease;

use crate::app_worldspine::{default_domain_token, AppWorldSpine};
use crate::world::World;

use super::chrome::{
    bevel_raised, face_row, face_row_color, face_section, id_short, NT_DIM, NT_OK, NT_PANEL,
    NT_SELECT, NT_TITLE_TEXT, NT_WARN,
};
use super::spotter::{SpotterEntry, SpotterTarget};
use super::{DeosDesktop, WinKindTag};

/// The registry id of the compute-exchange shelf app — the floor's job-market
/// substrate (its crate's program + effect-builders are what every offer cell runs).
pub const COMPUTE_APP: &str = "compute-exchange";
/// The registry id of the execution-lease shelf app — the floor's metering rail
/// (every take advances its durable checkpoint cursor as a real verified turn).
pub const LEASE_APP: &str = "execution-lease";

/// The requester identity the floor's posts bind into `REQUESTER_HASH` (phase 1's
/// one operator-driven requester; a counterparty picker is the named seam).
pub const FLOOR_REQUESTER: &str = "requester-desk";
/// The provider identity the floor's takes bind into `PROVIDER_HASH`.
pub const FLOOR_PROVIDER: &str = "provider-desk";
/// The budget a floor-posted offer escrows (the `line` a take may draw against).
pub const DEFAULT_OFFER_BUDGET: u64 = 1_000;

// ── The pure offer/lease model ────────────────────────────────────────────────────

/// The deterministic public key of the floor's `ordinal`-th offer cell — a blake3
/// derive-key over the ordinal, so every posted offer is a DISTINCT cell with a
/// reproducible identity (the same recipe kind the sentinel cells use; no new deps).
pub fn offer_pk(ordinal: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("deos exchange-floor offer v1");
    h.update(&ordinal.to_le_bytes());
    *h.finalize().as_bytes()
}

/// The floor's fair take price for a `budget`-bound offer — three quarters of the
/// budget (the registry's own 750-of-1000 posture), never below 1. Always within
/// the BUDGET gate, so an honest take commits.
pub fn fair_price(budget: u64) -> u64 {
    (budget * 3 / 4).max(1)
}

/// A deliberately OVER-BUDGET take price — what the cheat button offers so the
/// executor's `FieldLteField(BID <= BUDGET)` refusal is demonstrable on the glass.
pub fn overbudget_price(budget: u64) -> u64 {
    budget.saturating_add(250)
}

/// **The `post` effect-set** — open the job: bind `REQUESTER_HASH`, `BUDGET` (the
/// most a take may cost; `WriteOnce`-frozen after), the sealed `SPEC_HASH`, advance
/// `STATE -> POSTED`, and emit `job-posted`. This mirrors the compute-exchange
/// crate's own `build_post_action` effect-for-effect (built from its public slot
/// constants + encoders), so the floor fires the SAME turn the app does — the
/// 4-axis invariant the wired cards keep.
pub fn post_effects(cell: CellId, requester: &str, budget: u64) -> Vec<Effect> {
    let requester_h = job::party_hash(requester);
    let budget_f = job::amount_field(budget);
    vec![
        Effect::SetField {
            cell,
            index: job::REQUESTER_HASH_SLOT,
            value: requester_h,
        },
        Effect::SetField {
            cell,
            index: job::BUDGET_SLOT,
            value: budget_f,
        },
        Effect::SetField {
            cell,
            index: job::SPEC_HASH_SLOT,
            value: job::spec_digest(b"exchange-floor compute offer"),
        },
        Effect::SetField {
            cell,
            index: job::STATE_SLOT,
            value: job::state_field(job::STATE_POSTED),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("job-posted"), vec![requester_h, budget_f]),
        },
    ]
}

/// Read the `u64` tail of a 32-byte big-endian field element (the inverse of the
/// amount/state encoders the job slots use) — the same read every wired card makes.
fn field_tail_u64(fe: &dregg_app_framework::FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[24..32]);
    u64::from_be_bytes(b)
}

/// Where an offer stands on its ONE-WAY lifecycle (`StrictMonotonic(STATE)` — no
/// replay, no regress, no double-settle), read off the live `STATE` slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OfferPhase {
    /// Open on the book — a take may draw against the budget.
    Posted,
    /// Taken under lease — a provider + price are bound; settle is the next turn.
    Leased,
    /// Settled — `PAID + REFUNDED == BUDGET` held on the committed split (Σδ = 0).
    Settled,
    /// No live state / an unrecognized code (fail-soft: the row says so).
    Unborn,
}

impl OfferPhase {
    /// Map the live `STATE` slot code onto the phase vocabulary.
    pub fn from_state_code(code: u64) -> OfferPhase {
        match code {
            c if c == job::STATE_POSTED => OfferPhase::Posted,
            c if c == job::STATE_BID => OfferPhase::Leased,
            c if c == job::STATE_SETTLED => OfferPhase::Settled,
            _ => OfferPhase::Unborn,
        }
    }

    /// The dense row caption.
    pub fn label(self) -> &'static str {
        match self {
            OfferPhase::Posted => "POSTED",
            OfferPhase::Leased => "LEASED",
            OfferPhase::Settled => "SETTLED",
            OfferPhase::Unborn => "unborn",
        }
    }
}

/// **Σδ** — the settlement's value delta `paid + refunded − budget`. Exactly `0`
/// on any executor-accepted settle (the FLASHWELL `AffineEq` is re-enforced on the
/// commit); the window recomputes it from the LIVE slots so the caption is a read,
/// never a promise.
pub fn settlement_delta(paid: u64, refunded: u64, budget: u64) -> i64 {
    paid as i64 + refunded as i64 - budget as i64
}

/// One **posted offer** — a real cell on the live `World` carrying the
/// compute-exchange job program, plus the [`AppWorldSpine`] that commits its
/// lifecycle turns. Identity only: the phase / amounts are ALWAYS read live
/// ([`ExchangeOffer::facts`]), never cached.
pub struct ExchangeOffer {
    /// The floor's book ordinal (offer #N — drives the derived cell identity).
    pub ordinal: u64,
    /// The offer cell on the LIVE World ledger (the icon + inspector pointer).
    pub cell: CellId,
    /// The committing bridge — every lifecycle turn goes through
    /// [`AppWorldSpine::commit`] (cap tooth in-band; the job program re-enforced
    /// by `World`'s executor).
    spine: AppWorldSpine,
    /// The requester bound at post (the status lines name it).
    pub requester: String,
}

impl ExchangeOffer {
    /// The render-ready LIVE projection of this offer — every number read off the
    /// World ledger through the spine (the same read the inspector makes).
    pub fn facts(&self) -> OfferFacts {
        let live = self.spine.live_state();
        let read = |slot: usize| {
            live.as_ref()
                .and_then(|s| s.fields.get(slot))
                .map(field_tail_u64)
                .unwrap_or(0)
        };
        let budget = read(job::BUDGET_SLOT);
        let bid = read(job::BID_SLOT);
        let paid = read(job::PAID_SLOT);
        let refunded = read(job::REFUNDED_SLOT);
        let phase = if live.is_some() {
            OfferPhase::from_state_code(read(job::STATE_SLOT))
        } else {
            OfferPhase::Unborn
        };
        OfferFacts {
            ordinal: self.ordinal,
            cell: self.cell,
            requester: self.requester.clone(),
            phase,
            budget,
            bid,
            paid,
            refunded,
            delta: settlement_delta(paid, refunded, budget),
        }
    }
}

/// One offer row's render-ready facts — pure data off the LIVE ledger; the window
/// body maps these to elements (the same inversion [`super::app_shelf::shelf_rows`]
/// keeps).
pub struct OfferFacts {
    pub ordinal: u64,
    pub cell: CellId,
    pub requester: String,
    pub phase: OfferPhase,
    pub budget: u64,
    pub bid: u64,
    pub paid: u64,
    pub refunded: u64,
    /// Σδ = `paid + refunded − budget` — `0` exactly at an executor-accepted settle.
    pub delta: i64,
}

/// **The floor's whole state** — the order book of floor-posted offers, in post
/// order. Owned by [`DeosDesktop`]; gpui-free, so the post/take/settle loop is
/// `cargo test`-able against a real `World`.
#[derive(Default)]
pub struct ExchangeFloorState {
    offers: Vec<ExchangeOffer>,
    /// The next offer's ordinal — bumped BEFORE the post attempt so a refused post
    /// can never re-derive (and re-genesis) an already-seeded offer cell.
    next_ordinal: u64,
}

impl ExchangeFloorState {
    /// A fresh floor — an empty book.
    pub fn new() -> Self {
        ExchangeFloorState::default()
    }

    /// The book, in post order.
    pub fn offers(&self) -> &[ExchangeOffer] {
        &self.offers
    }

    /// The offer standing at `cell`, if the floor posted one there.
    pub fn find(&self, cell: &CellId) -> Option<&ExchangeOffer> {
        self.offers.iter().find(|o| &o.cell == cell)
    }

    /// The render-ready LIVE projection of the whole book, in post order.
    pub fn rows(&self) -> Vec<OfferFacts> {
        self.offers.iter().map(ExchangeOffer::facts).collect()
    }

    /// The NEWEST offer currently standing in `phase` (the bake verbs' default
    /// target: take the newest posted, settle the newest leased).
    pub fn newest_in(&self, phase: OfferPhase) -> Option<CellId> {
        self.offers
            .iter()
            .rev()
            .find(|o| o.facts().phase == phase)
            .map(|o| o.cell)
    }

    /// The desktop-icon face for a floor-posted offer's cell — `("compute offer",
    /// "$")` so an offer reads as ECONOMY substance on the desktop, not a
    /// balance-classified account. `None` for every other cell.
    pub fn icon_face(&self, cell: &CellId) -> Option<(&'static str, &'static str)> {
        self.find(cell).map(|_| ("compute offer", "$"))
    }

    /// **POST an offer onto the live `World`** — the floor's opening verb.
    ///
    /// Seeds a FRESH cell (a derived identity per ordinal — every offer is its own
    /// cell) carrying the compute-exchange crate's own
    /// [`starbridge_compute_exchange::job_program`] and an EMPTY genesis state,
    /// then commits the REAL `post` turn ([`post_effects`]): requester + budget +
    /// sealed spec bound (`WriteOnce`), `STATE -> POSTED`
    /// (`StrictMonotonic` from the empty genesis). The receipt lands in
    /// `World::receipts()`; the cell is on `World::ledger()` (the icon census sees
    /// it on the next PULSE beat). Returns the offer cell + the post receipt.
    ///
    /// Refusals are surfaced strings, never panics — and a refused post is never
    /// recorded on the book (the seeded husk stays inert; the bumped ordinal
    /// guarantees the next post derives a fresh identity).
    pub fn post_offer(
        &mut self,
        world: Rc<RefCell<World>>,
        requester: &str,
        budget: u64,
    ) -> Result<(CellId, TurnReceipt), String> {
        let ordinal = self.next_ordinal;
        self.next_ordinal += 1;
        let pk = offer_pk(ordinal);
        let token = default_domain_token();
        let cell = dregg_cell::Cell::with_balance(pk, token, 1_000_000).id();
        // Genesis: the job program installed, NO seeded fields — the posting itself
        // is the first verified turn (post is a turn here, not a baked-in baseline).
        let spine = AppWorldSpine::seed(world, cell, pk, token, job::job_program(), &[]);
        let receipt = spine
            .commit(
                job::service::METHOD_POST,
                &job::REQUESTER_RIGHTS,
                &job::REQUESTER_RIGHTS,
                |_live| post_effects(cell, requester, budget),
            )
            .map_err(|e| e.to_string())?;
        self.offers.push(ExchangeOffer {
            ordinal,
            cell,
            spine,
            requester: requester.to_string(),
        });
        Ok((cell, receipt))
    }

    /// **TAKE the offer at `cell`** — commit the REAL `bid` turn binding
    /// `PROVIDER_HASH` + `BID := price` and advancing `STATE -> BID` (the lease
    /// binding). `World`'s executor re-enforces the installed BUDGET gate
    /// (`FieldLteField(BID <= BUDGET)`): an over-budget `price` is a REAL refusal
    /// that commits NOTHING — the surfaced string carries the executor's own
    /// reason. (The desktop verb pairs this with one metered checkpoint on the
    /// execution-lease rail.)
    pub fn take(&self, cell: &CellId, provider: &str, price: u64) -> Result<TurnReceipt, String> {
        let offer = self
            .find(cell)
            .ok_or_else(|| format!("no offer at {} on this floor", id_short(cell)))?;
        let target = offer.cell;
        offer
            .spine
            .commit(
                job::service::METHOD_BID,
                &job::PROVIDER_RIGHTS,
                &job::PROVIDER_RIGHTS,
                |_live| job::bid_effects(target, provider, price),
            )
            .map_err(|e| e.to_string())
    }

    /// **SETTLE the offer at `cell`** — read the LIVE `BID` + `BUDGET` off the
    /// World ledger and commit the REAL `settle` turn paying the provider IN FULL
    /// (`PAID := BID`, `REFUNDED := BUDGET − BID`, `STATE -> SETTLED`). The
    /// executor re-enforces the FLASHWELL `AffineEq(PAID + REFUNDED − BUDGET = 0)`
    /// on the commit — Σδ = 0 by law, and [`OfferFacts::delta`] re-reads it off
    /// the live slots afterwards. A second settle is refused by
    /// `StrictMonotonic(STATE)` (no double-settle).
    pub fn settle(&self, cell: &CellId) -> Result<TurnReceipt, String> {
        let offer = self
            .find(cell)
            .ok_or_else(|| format!("no offer at {} on this floor", id_short(cell)))?;
        let target = offer.cell;
        offer
            .spine
            .commit(
                job::service::METHOD_SETTLE,
                &job::REQUESTER_RIGHTS,
                &job::REQUESTER_RIGHTS,
                |live| {
                    let budget = field_tail_u64(&live.fields[job::BUDGET_SLOT]);
                    let bid = field_tail_u64(&live.fields[job::BID_SLOT]);
                    job::settle_effects(target, bid, budget.saturating_sub(bid))
                },
            )
            .map_err(|e| e.to_string())
    }
}

/// The floor window's summary line — the book's phase census.
pub fn exchange_summary(rows: &[OfferFacts]) -> String {
    let posted = rows
        .iter()
        .filter(|r| r.phase == OfferPhase::Posted)
        .count();
    let leased = rows
        .iter()
        .filter(|r| r.phase == OfferPhase::Leased)
        .count();
    let settled = rows
        .iter()
        .filter(|r| r.phase == OfferPhase::Settled)
        .count();
    format!(
        "{} offer(s) on the book · {posted} posted · {leased} leased · {settled} settled (Σδ=0 each)",
        rows.len()
    )
}

// ── The Spotter vocabulary ────────────────────────────────────────────────────────

/// The Spotter's exchange candidate: the ONE entry that reaches the floor (the
/// per-offer vocabulary rides the existing per-cell candidates — an offer IS a
/// cell). Appended by the desktop's candidate builder beside the shelf's.
pub fn exchange_spotter_candidates() -> Vec<SpotterEntry> {
    vec![SpotterEntry {
        label: "Exchange Floor  ($DREGG agent economy · post → lease → settle)".to_string(),
        sublabel:
            "surface · offers & leases as live cells · Σδ=0 settlement · executor-refused cheats"
                .to_string(),
        target: SpotterTarget::ExchangeFloor,
        score: 0,
    }]
}

// ── The View half: actuation + the NT floor body (the View owns the listeners) ────

impl DeosDesktop {
    /// Open (or focus) the EXCHANGE FLOOR window — anchored on the user sentinel
    /// like the App Shelf, landed mold-ready. Ensures the substrate first: the
    /// compute-exchange + execution-lease shelf apps are launched onto the LIVE
    /// World if not yet installed (each launch a real verified turn).
    pub(super) fn open_exchange_floor(&mut self) {
        if !self.ensure_exchange_substrate() {
            return; // the refusal is already on the status bar
        }
        self.land_in(self.user, WinKindTag::ExchangeFloor);
        self.say(format!(
            "Exchange Floor — {} · POST puts an offer CELL on the LIVE World, TAKE \
             binds a lease (the executor refuses over-budget draws), SETTLE splits \
             the budget Σδ=0.",
            exchange_summary(&self.exchange_floor.rows())
        ));
    }

    /// **Ensure the floor's substrate is installed** — the compute-exchange (job
    /// market) and execution-lease (metering rail) shelf apps, launched onto the
    /// LIVE World through the SAME
    /// [`super::app_shelf::AppShelfState::install_on_world`] flow the shelf's own
    /// button runs (each install seeds the app cell + program and commits its
    /// representative affordance as a real verified turn). Idempotent; a launch
    /// refusal is surfaced on the status bar and answers `false`.
    fn ensure_exchange_substrate(&mut self) -> bool {
        for id in [COMPUTE_APP, LEASE_APP] {
            if self.app_shelf.find(id).is_none() {
                let world = Rc::clone(&self.world);
                if let Err(reason) = self.app_shelf.install_on_world(id, world) {
                    self.say(format!(
                        "Exchange Floor substrate: LAUNCH '{id}' refused: {reason}"
                    ));
                    return false;
                }
            }
        }
        self.refresh_cells_from_ledger();
        true
    }

    /// **POST an offer** — the floor's opening verb: a fresh offer CELL seeded with
    /// the job program + the REAL `post` turn committed (requester/budget/spec
    /// bound, `STATE -> POSTED`). The receipt lands in the Transcript; the icon
    /// census grows. Returns whether the post COMMITTED.
    pub(super) fn exchange_post_offer(&mut self) -> bool {
        if !self.ensure_exchange_substrate() {
            return false;
        }
        let world = Rc::clone(&self.world);
        match self
            .exchange_floor
            .post_offer(world, FLOOR_REQUESTER, DEFAULT_OFFER_BUDGET)
        {
            Ok((cell, _receipt)) => {
                self.refresh_cells_from_ledger();
                self.say(format!(
                    "OFFER #{} POSTED — cell {} · budget {} escrow-bound by the job \
                     program (a real verified 'post' turn; height {}).",
                    self.exchange_floor.offers().len(),
                    id_short(&cell),
                    DEFAULT_OFFER_BUDGET,
                    self.world.borrow().height()
                ));
                true
            }
            Err(reason) => {
                self.say(format!("POST offer refused: {reason}"));
                false
            }
        }
    }

    /// **TAKE the offer at `cell` under a lease** — two real verified turns: the
    /// `bid` on the offer cell (provider + fair price bound; the BUDGET gate
    /// re-enforced by the executor) and one metered checkpoint (`advance`) on the
    /// execution-lease rail (the SAME wired card fire the shelf uses). Returns
    /// whether the lease-binding bid COMMITTED (the checkpoint's verdict rides the
    /// status line).
    pub(super) fn exchange_take_lease(&mut self, cell: CellId) -> bool {
        let Some(budget) = self.exchange_floor.find(&cell).map(|o| o.facts().budget) else {
            self.say(format!(
                "TAKE refused: no offer at {} on this floor.",
                id_short(&cell)
            ));
            return false;
        };
        let price = fair_price(budget);
        match self.exchange_floor.take(&cell, FLOOR_PROVIDER, price) {
            Ok(receipt) => {
                // The metering rail: one durable checkpoint on the execution-lease
                // cell — the leased compute visibly RUNS (Monotonic(STEP) advances).
                let meter = match self
                    .app_shelf
                    .fire(LEASE_APP, lease::service::METHOD_ADVANCE, 1)
                {
                    Some(Ok(_)) => "checkpoint advanced on the lease rail".to_string(),
                    Some(Err(e)) => format!("lease checkpoint refused: {e}"),
                    None => "lease rail not installed (substrate seam)".to_string(),
                };
                self.say(format!(
                    "LEASE TAKEN on {} — bid {} of {} committed by {} · {} (height {}).",
                    id_short(&cell),
                    price,
                    budget,
                    id_short(&receipt.agent),
                    meter,
                    self.world.borrow().height()
                ));
                true
            }
            Err(reason) => {
                self.say(format!("TAKE on {} REFUSED: {reason}", id_short(&cell)));
                false
            }
        }
    }

    /// **Try an OVER-BUDGET take** — the cheat button: offer `budget + 250` against
    /// the budget gate and let the REAL executor refuse it
    /// (`FieldLteField(BID <= BUDGET)`); nothing commits, the receipt log does not
    /// grow, and the status bar carries the executor's own reason. Returns whether
    /// the cheat was REFUSED (i.e. `true` means the tooth bit, as it must).
    pub(super) fn exchange_take_overbudget(&mut self, cell: CellId) -> bool {
        let Some(budget) = self.exchange_floor.find(&cell).map(|o| o.facts().budget) else {
            self.say(format!("no offer at {} on this floor.", id_short(&cell)));
            return false;
        };
        let price = overbudget_price(budget);
        match self.exchange_floor.take(&cell, FLOOR_PROVIDER, price) {
            Err(reason) => {
                self.say(format!(
                    "OVER-BUDGET take ({price} > {budget}) REFUSED by the executor — \
                     nothing committed: {reason}"
                ));
                true
            }
            Ok(_) => {
                // Must be unreachable while the job program stands — surfaced, not
                // asserted, so a program regression is VISIBLE rather than a panic.
                self.say(format!(
                    "over-budget take ({price} > {budget}) COMMITTED — the BUDGET \
                     gate did not bite; the job program on {} needs eyes.",
                    id_short(&cell)
                ));
                false
            }
        }
    }

    /// **SETTLE the offer at `cell`** — the REAL `settle` turn splitting the budget
    /// (provider paid in full, remainder refunded); the executor re-enforces
    /// `AffineEq(PAID + REFUNDED − BUDGET = 0)` — Σδ=0 by law, re-read off the
    /// LIVE slots for the status line. Returns whether the settle COMMITTED.
    pub(super) fn exchange_settle_offer(&mut self, cell: CellId) -> bool {
        match self.exchange_floor.settle(&cell) {
            Ok(_receipt) => {
                let facts = self.exchange_floor.find(&cell).map(|o| o.facts());
                let (paid, refunded, budget, delta) = facts
                    .map(|f| (f.paid, f.refunded, f.budget, f.delta))
                    .unwrap_or((0, 0, 0, 0));
                self.say(format!(
                    "SETTLED {} — paid {paid} + refunded {refunded} = budget {budget} · \
                     Σδ = {delta} (AffineEq re-enforced by the executor; height {}).",
                    id_short(&cell),
                    self.world.borrow().height()
                ));
                true
            }
            Err(reason) => {
                self.say(format!("SETTLE on {} REFUSED: {reason}", id_short(&cell)));
                false
            }
        }
    }

    // ── Bake / test hooks (drive the floor headlessly) ────────────────────────────

    /// Open the Exchange Floor (what the desktop menu's "Exchange Floor…" does) —
    /// installs the substrate shelf apps if needed (real launch receipts).
    pub fn bake_open_exchange(&mut self) {
        self.open_exchange_floor();
    }

    /// POST an offer (what the floor's "Post offer" button does) — a real verified
    /// `post` turn on a fresh offer cell. Returns whether it committed.
    pub fn bake_post_offer(&mut self) -> bool {
        self.exchange_post_offer()
    }

    /// TAKE the newest POSTED offer under a lease (bid + metered checkpoint — two
    /// real verified turns). Returns whether the lease-binding bid committed.
    pub fn bake_take_lease(&mut self) -> bool {
        match self.exchange_floor.newest_in(OfferPhase::Posted) {
            Some(cell) => self.exchange_take_lease(cell),
            None => {
                self.say("TAKE: no posted offer on the book — post one first.");
                false
            }
        }
    }

    /// SETTLE the newest LEASED offer (the Σδ=0 split). Returns whether it committed.
    pub fn bake_settle_offer(&mut self) -> bool {
        match self.exchange_floor.newest_in(OfferPhase::Leased) {
            Some(cell) => self.exchange_settle_offer(cell),
            None => {
                self.say("SETTLE: no leased offer on the book — take one first.");
                false
            }
        }
    }

    /// Fire the OVER-BUDGET cheat at the newest POSTED offer; `true` means the
    /// executor REFUSED it (the tooth bit) and nothing committed.
    pub fn bake_exchange_cheat_refused(&mut self) -> bool {
        match self.exchange_floor.newest_in(OfferPhase::Posted) {
            Some(cell) => self.exchange_take_overbudget(cell),
            None => false,
        }
    }

    /// How many offers stand on the floor's book (a bake assertion).
    pub fn bake_exchange_offer_count(&self) -> usize {
        self.exchange_floor.offers().len()
    }

    /// The newest SETTLED offer's Σδ, re-read off the LIVE ledger — `Some(0)` after
    /// any executor-accepted settle; `None` while nothing is settled.
    pub fn bake_exchange_settlement_delta(&self) -> Option<i64> {
        self.exchange_floor
            .rows()
            .iter()
            .rev()
            .find(|r| r.phase == OfferPhase::Settled)
            .map(|r| r.delta)
    }

    /// The LIVE World's receipt count — the growth witness the exchange bake
    /// asserts around every floor verb (each verb is a real committed turn).
    pub fn bake_world_receipt_count(&self) -> usize {
        self.world.borrow().receipts().len()
    }

    // ── The NT floor body ─────────────────────────────────────────────────────────

    /// **The Exchange Floor window body** — the substrate strip (the two shelf apps
    /// with their LIVE facts) over the order book (one card per offer: phase ·
    /// live amounts · the per-phase verbs, every button a real verified turn or a
    /// demonstrable executor refusal). Rows come from the pure LIVE projection
    /// ([`ExchangeFloorState::rows`]); this method owns only the listeners.
    pub(super) fn render_exchange_floor_body(
        &self,
        scroll: &gpui::ScrollHandle,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let rows = self.exchange_floor.rows();
        let summary = exchange_summary(&rows);

        let mut col = div()
            .id("exchange-floor-body")
            .bg(gpui::rgb(NT_PANEL))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section(&format!("Exchange Floor · {summary}")))
            .child(
                div()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_DIM))
                    .child(
                        "The $DREGG agent economy on live substance: an OFFER is a cell whose \
                         installed program IS the market rules. POST / TAKE / SETTLE each commit \
                         a REAL verified turn (receipt in the Transcript); an over-budget take is \
                         REFUSED by the executor itself; a settlement conserves the budget Σδ=0.",
                    ),
            );

        // The substrate strip — the two shelf apps the floor rides on, LIVE.
        col = col.child(face_section("Substrate · the App Shelf's economy apps"));
        col = col.child(self.render_exchange_substrate_row(
            COMPUTE_APP,
            "job market — every offer cell runs its program (BUDGET gate · FLASHWELL Σ · lifecycle)",
        ));
        col = col.child(self.render_exchange_substrate_row(
            LEASE_APP,
            "metering rail — every take advances its durable checkpoint (a real turn)",
        ));

        // The floor's opening verb.
        col = col.child(
            floor_button_chrome("exchange-post-offer".to_string())
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.exchange_post_offer();
                        cx.notify();
                    }),
                )
                .child(format!(
                    "Post offer  (verified 'post' turn · budget {DEFAULT_OFFER_BUDGET})"
                )),
        );

        // The order book.
        col = col.child(face_section("Order book"));
        if rows.is_empty() {
            col = col.child(
                div()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_DIM))
                    .child("The book is empty — post the first offer above."),
            );
        }
        for row in rows {
            col = col.child(self.render_exchange_offer_row(row, cx));
        }
        // The order book scrolls behind a REAL NT scrollbar — a deep book reads
        // as depth, not truncation, and the persistent handle keeps the place.
        super::chrome::nt_scroll_face(scroll, col).into_any_element()
    }

    /// One substrate row: the shelf app's install verdict + its LIVE detail line
    /// (read through the installed app's substance — the same witnessed read its
    /// card binds make).
    fn render_exchange_substrate_row(&self, id: &'static str, role: &str) -> AnyElement {
        let detail = match self.app_shelf.find(id) {
            Some(app) => {
                let live = match id {
                    COMPUTE_APP => {
                        let code = app.substance.get_u64(job::STATE_SLOT);
                        format!(
                            "house job {} · budget {} · bid {} · cell {}",
                            OfferPhase::from_state_code(code).label(),
                            app.substance.get_u64(job::BUDGET_SLOT),
                            app.substance.get_u64(job::BID_SLOT),
                            id_short(&app.cell)
                        )
                    }
                    _ => format!(
                        "checkpoint step {} · rent {}/period {} · cell {}",
                        app.substance.get_u64(lease::STEP_SLOT as usize),
                        app.substance.get_u64(lease::RENT_SLOT as usize),
                        app.substance.get_u64(lease::PERIOD_SLOT as usize),
                        id_short(&app.cell)
                    ),
                };
                format!("INSTALLED · {live}")
            }
            None => "not installed — the floor launches it on its first gesture".to_string(),
        };
        bevel_raised(
            div()
                .p_1()
                .flex()
                .flex_col()
                .gap_1()
                .child(face_row(id, role))
                .child(face_row("live", &detail)),
        )
        .into_any_element()
    }

    /// One order-book card: the offer's heading (ordinal · phase), its LIVE facts,
    /// and the per-phase verbs (take / cheat / settle / open).
    fn render_exchange_offer_row(&self, row: OfferFacts, cx: &mut Context<Self>) -> AnyElement {
        let cell = row.cell;
        let phase_color = match row.phase {
            OfferPhase::Posted => NT_WARN,
            OfferPhase::Leased => NT_SELECT,
            OfferPhase::Settled => NT_OK,
            OfferPhase::Unborn => NT_DIM,
        };
        let mut card = bevel_raised(
            div()
                .id(gpui::SharedString::from(format!(
                    "exchange-offer-{}",
                    row.ordinal
                )))
                .p_2()
                .flex()
                .flex_col()
                .gap_1(),
        );

        card = card.child(
            div()
                .flex()
                .flex_row()
                .gap_2()
                .items_center()
                .child(
                    div()
                        .text_size(px(12.0))
                        .font_weight(gpui::FontWeight::BOLD)
                        .child(format!("OFFER #{}", row.ordinal + 1)),
                )
                .child(
                    div()
                        .text_size(px(10.0))
                        .text_color(gpui::rgb(NT_DIM))
                        .child(format!("cell {}", id_short(&cell))),
                )
                .child(
                    div()
                        .ml_auto()
                        .text_size(px(10.0))
                        .text_color(gpui::rgb(phase_color))
                        .child(row.phase.label()),
                ),
        );
        card = card.child(face_row(
            "terms",
            &format!(
                "requester {} · budget {} · bid {}",
                row.requester, row.budget, row.bid
            ),
        ));
        if row.phase == OfferPhase::Settled {
            card = card.child(face_row_color(
                "Σδ",
                &format!(
                    "paid {} + refunded {} − budget {} = {}  (AffineEq, executor-enforced)",
                    row.paid, row.refunded, row.budget, row.delta
                ),
                NT_OK,
            ));
        }

        let mut buttons = div().flex().flex_row().flex_wrap().gap_1();
        match row.phase {
            OfferPhase::Posted => {
                let price = fair_price(row.budget);
                buttons = buttons.child(
                    floor_button_chrome(format!("exchange-take-{}", row.ordinal))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                this.exchange_take_lease(cell);
                                cx.notify();
                            }),
                        )
                        .child(format!(
                            "Take lease @ {price}  (verified 'bid' + metered checkpoint)"
                        )),
                );
                buttons = buttons.child(
                    floor_button_chrome(format!("exchange-cheat-{}", row.ordinal))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                this.exchange_take_overbudget(cell);
                                cx.notify();
                            }),
                        )
                        .child(format!(
                            "Try over-budget take @ {}  (the executor refuses)",
                            overbudget_price(row.budget)
                        )),
                );
            }
            OfferPhase::Leased => {
                buttons = buttons.child(
                    floor_button_chrome(format!("exchange-settle-{}", row.ordinal))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                                this.exchange_settle_offer(cell);
                                cx.notify();
                            }),
                        )
                        .child("Settle  (Σδ=0 · verified 'settle' turn)"),
                );
            }
            OfferPhase::Settled | OfferPhase::Unborn => {}
        }
        buttons = buttons.child(
            floor_button_chrome(format!("exchange-open-{}", row.ordinal))
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.land_in(cell, WinKindTag::Inspector);
                        this.status = format!(
                            "Inspecting offer cell {} — its live slots on the World ledger.",
                            id_short(&cell)
                        );
                        cx.notify();
                    }),
                )
                .child("Open  (live cell inspector)"),
        );
        card = card.child(buttons);
        card.into_any_element()
    }
}

/// The raised NT chrome of one floor button (id + dense padding + navy hover). The
/// CALLER chains its own `.on_mouse_down(…, cx.listener(…))` + `.child(label)` —
/// the View owns the listeners (the clobber-safe split); this is dumb chrome.
fn floor_button_chrome(elem_id: String) -> gpui::Stateful<gpui::Div> {
    bevel_raised(
        div()
            .id(gpui::SharedString::from(elem_id))
            .px_2()
            .py_1()
            .text_size(px(10.0))
            .hover(|s| {
                s.bg(gpui::rgb(NT_SELECT))
                    .text_color(gpui::rgb(NT_TITLE_TEXT))
            }),
    )
}

// ── Unit tests for the gpui-free core (real Worlds, real verified turns) ──────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::deos_desktop::app_shelf::AppShelfState;

    /// The whole floor loop against a LIVE `World`: POST births an offer cell and
    /// commits the `post` turn (one receipt), TAKE commits the `bid` turn plus a
    /// metered checkpoint on the lease rail (two receipts), SETTLE commits the
    /// Σδ=0 split (one receipt) — every count on `World::receipts()` and every
    /// phase read off the LIVE ledger.
    #[test]
    fn post_take_settle_land_real_receipts_and_sigma_is_zero() {
        let world = Rc::new(RefCell::new(World::new()));
        let mut floor = ExchangeFloorState::new();

        // The metering rail: the execution-lease shelf app installed onto the SAME
        // World (its launch commits its representative advance — the substrate).
        let mut shelf = AppShelfState::new();
        shelf
            .install_on_world(LEASE_APP, Rc::clone(&world))
            .expect("the lease rail installs onto the live World");
        let step_before = shelf
            .find(LEASE_APP)
            .expect("installed")
            .substance
            .get_u64(lease::STEP_SLOT as usize);

        let receipts0 = world.borrow().receipts().len();

        // POST — the offer cell lands on the ledger; the post turn is receipted.
        let (cell, receipt) = floor
            .post_offer(Rc::clone(&world), FLOOR_REQUESTER, 1_000)
            .expect("posting an offer commits");
        assert_eq!(receipt.agent, cell, "the offer cell authored its post");
        assert!(
            world.borrow().ledger().get(&cell).is_some(),
            "the offer is a REAL cell on the live ledger"
        );
        assert_eq!(world.borrow().receipts().len(), receipts0 + 1);
        let rows = floor.rows();
        assert_eq!(rows[0].phase, OfferPhase::Posted);
        assert_eq!(rows[0].budget, 1_000);
        assert_eq!(rows[0].bid, 0);

        // TAKE — the bid turn (fair price, within the BUDGET gate) + the metered
        // checkpoint on the lease rail (the desktop verb's composition, mirrored).
        floor
            .take(&cell, FLOOR_PROVIDER, fair_price(1_000))
            .expect("a fair-price take commits");
        shelf
            .fire(LEASE_APP, lease::service::METHOD_ADVANCE, 1)
            .expect("installed")
            .expect("the metered checkpoint advances");
        assert_eq!(world.borrow().receipts().len(), receipts0 + 3);
        let rows = floor.rows();
        assert_eq!(rows[0].phase, OfferPhase::Leased);
        assert_eq!(rows[0].bid, 750);
        let step_after = shelf
            .find(LEASE_APP)
            .expect("installed")
            .substance
            .get_u64(lease::STEP_SLOT as usize);
        assert_eq!(step_after, step_before + 1, "the durable cursor advanced");

        // SETTLE — the Σδ=0 split, re-read off the LIVE slots.
        floor.settle(&cell).expect("the honest settle commits");
        assert_eq!(world.borrow().receipts().len(), receipts0 + 4);
        let rows = floor.rows();
        assert_eq!(rows[0].phase, OfferPhase::Settled);
        assert_eq!(rows[0].paid, 750);
        assert_eq!(rows[0].refunded, 250);
        assert_eq!(
            rows[0].delta, 0,
            "Σδ = 0 — the executor-enforced conservation"
        );
    }

    /// An over-budget take is a REAL executor refusal (`FieldLteField(BID <=
    /// BUDGET)`) that commits NOTHING — the receipt log does not grow and the
    /// offer stays POSTED, still takeable at an honest price.
    #[test]
    fn an_overbudget_take_is_refused_and_commits_nothing() {
        let world = Rc::new(RefCell::new(World::new()));
        let mut floor = ExchangeFloorState::new();
        let (cell, _) = floor
            .post_offer(Rc::clone(&world), FLOOR_REQUESTER, 1_000)
            .expect("posts");
        let receipts = world.borrow().receipts().len();

        let refused = floor.take(&cell, FLOOR_PROVIDER, overbudget_price(1_000));
        assert!(refused.is_err(), "1250 > 1000 must be refused");
        assert_eq!(
            world.borrow().receipts().len(),
            receipts,
            "a refusal commits NOTHING (anti-ghost)"
        );
        let rows = floor.rows();
        assert_eq!(rows[0].phase, OfferPhase::Posted);

        // The honest path still stands after the refused cheat.
        floor
            .take(&cell, FLOOR_PROVIDER, fair_price(1_000))
            .expect("the fair take still commits");
        let rows = floor.rows();
        assert_eq!(rows[0].phase, OfferPhase::Leased);
    }

    /// A second settle is refused by the LIFECYCLE tooth (`StrictMonotonic(STATE)`
    /// — no double-settle) and commits nothing.
    #[test]
    fn a_double_settle_is_refused_by_the_lifecycle_tooth() {
        let world = Rc::new(RefCell::new(World::new()));
        let mut floor = ExchangeFloorState::new();
        let (cell, _) = floor
            .post_offer(Rc::clone(&world), FLOOR_REQUESTER, 400)
            .expect("posts");
        floor.take(&cell, FLOOR_PROVIDER, 300).expect("takes");
        floor.settle(&cell).expect("settles once");
        let receipts = world.borrow().receipts().len();

        let again = floor.settle(&cell);
        assert!(again.is_err(), "a double-settle must be refused");
        assert_eq!(world.borrow().receipts().len(), receipts);
        let rows = floor.rows();
        assert_eq!(rows[0].phase, OfferPhase::Settled);
        assert_eq!(rows[0].delta, 0, "the first settlement stands, conserved");
    }

    /// Every posted offer is its OWN cell (distinct derived identities), the book
    /// keeps post order, `newest_in` finds the newest by phase, and `icon_face`
    /// answers for offer cells only.
    #[test]
    fn offers_are_distinct_cells_in_book_order() {
        let world = Rc::new(RefCell::new(World::new()));
        let mut floor = ExchangeFloorState::new();
        let (a, _) = floor
            .post_offer(Rc::clone(&world), FLOOR_REQUESTER, 500)
            .expect("posts a");
        let (b, _) = floor
            .post_offer(Rc::clone(&world), FLOOR_REQUESTER, 900)
            .expect("posts b");
        assert_ne!(a, b, "each offer is its own cell");
        let rows = floor.rows();
        assert_eq!(rows.len(), 2);
        assert_eq!((rows[0].cell, rows[1].cell), (a, b), "post order");
        assert_eq!(floor.newest_in(OfferPhase::Posted), Some(b));
        floor.take(&b, FLOOR_PROVIDER, 600).expect("takes b");
        assert_eq!(floor.newest_in(OfferPhase::Posted), Some(a));
        assert_eq!(floor.newest_in(OfferPhase::Leased), Some(b));
        assert_eq!(floor.icon_face(&a), Some(("compute offer", "$")));
        assert_eq!(floor.icon_face(&CellId::from_bytes([0u8; 32])), None);
    }

    /// The pure helpers: the fair/overbudget prices bracket the BUDGET gate, the
    /// phase codes map onto the vocabulary, and Σδ is the plain signed identity.
    #[test]
    fn the_pure_offer_lease_model_holds() {
        assert_eq!(fair_price(1_000), 750);
        assert_eq!(fair_price(1), 1, "never below 1");
        assert!(fair_price(1_000) <= 1_000, "fair is within the gate");
        assert!(overbudget_price(1_000) > 1_000, "the cheat is outside it");

        assert_eq!(OfferPhase::from_state_code(1), OfferPhase::Posted);
        assert_eq!(OfferPhase::from_state_code(2), OfferPhase::Leased);
        assert_eq!(OfferPhase::from_state_code(3), OfferPhase::Settled);
        assert_eq!(OfferPhase::from_state_code(0), OfferPhase::Unborn);

        assert_eq!(settlement_delta(750, 250, 1_000), 0);
        assert_eq!(
            settlement_delta(750, 200, 1_000),
            -50,
            "a burn shows negative"
        );
        assert_eq!(
            settlement_delta(900, 200, 1_000),
            100,
            "a mint shows positive"
        );

        // The post effect-set carries the four bindings + the event (the same
        // shape the crate's own build_post_action emits).
        let cell = CellId::from_bytes([7u8; 32]);
        let fx = post_effects(cell, FLOOR_REQUESTER, 1_000);
        assert_eq!(fx.len(), 5);
        let summary = exchange_summary(&[]);
        assert!(summary.starts_with("0 offer(s)"));
    }

    /// The Spotter vocabulary: one floor entry targeting the Exchange surface.
    #[test]
    fn spotter_candidates_reach_the_floor() {
        let cands = exchange_spotter_candidates();
        assert_eq!(cands.len(), 1);
        assert!(matches!(cands[0].target, SpotterTarget::ExchangeFloor));
        assert!(cands[0].label.contains("Exchange Floor"));
    }
}
