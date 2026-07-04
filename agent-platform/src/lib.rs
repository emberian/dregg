//! # agent-platform — rent, host, meter, and reap confined agent grains.
//!
//! The agent-side twin of the hosting substrate's webcell platform. A tenant is a
//! [`dregg_agent::session::Session`] — a hosted, cap+budget-bounded, receipted
//! agent, "the unit a hosting layer rents out per user" — opened under
//! [`Confinement::Hosted`] (lexically-confinable tools only; a raw `shell` is
//! refused) over a [`HostedLease`]. [`AgentPlatform::rent`] provisions the grain,
//! [`drive`](AgentPlatform::drive) runs one goal (metered, receipted) and advances
//! the lease's durable checkpoint with a **verified binding** of the session
//! (digest + chain tip + turn count + consumed — read back and re-checked on
//! every [`verify`](AgentPlatform::verify)),
//! [`bill_period`](AgentPlatform::bill_period) meters and settles the rent
//! (in-process or on-chain via the injected [`Settlement`]), and
//! [`reap_if_behind`](AgentPlatform::reap_if_behind) reclaims a delinquent grain.
//! This is the first stone of THE GRAIN (`docs/THE-GRAIN.md`): a hosted agent is
//! a rentable, verifiable grain.
//!
//! ## What a renter can check — the honest R-ladder (`docs/THE-GRAIN.md` face #1)
//!
//! - **R0 (landed, in `dregg-agent`):** the receipt-chain key is a fresh RANDOM
//!   secret, never derived from the public agent id — a third party holding a
//!   report cannot forge a self-consistent chain. The HOST still runs the signer,
//!   so R0 alone is tamper-evidence, not host-independence.
//! - **R1 (landed, here):** rent with a [`RenterAnchor`] and countersign
//!   checkpoints ([`checkpoint_offer`](AgentPlatform::checkpoint_offer) /
//!   [`submit_checkpoint`](AgentPlatform::submit_checkpoint)) — third-party-
//!   verifiable anti-rewrite + anti-truncation relative to a renter-acknowledged
//!   checkpoint, no circuits.
//! - **R2 (the weld is here; the turn is as real as the minter):**
//!   [`drive_minted`](AgentPlatform::drive_minted) welds every admitted action
//!   to a turn committed through the supplied [`GrainTurnMinter`], and
//!   [`verify_r2`](AgentPlatform::verify_r2) rejects any receipt that is not a
//!   view over a committed turn. With `grain-turn`'s real `ToolGatewayMinter`
//!   that is a GENUINE kernel turn and the meter becomes a host-side executor
//!   caveat; `dregg_agent`'s `SyntheticMinter` exercises only the seam (tests).
//! - **R3 (the named gap):** proving the committed turns genuinely RAN is the
//!   whole-history STARK leg — [`grain_verify::WHOLE_HISTORY_GAP`], VK-terminal.

/// Serve the platform over HTTP (rent/drive/verify a grain over the mesh).
pub mod serve;
/// Roles as an attenuable facet lattice — the per-grain share model.
pub mod share;
/// The SSE transcript wire — replay a grain's drive as meta/step/done frames.
pub mod transcript;

pub use share::Role;

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use dregg_agent::agent::{AgentBrain, AgentRunReport, AgentVerified, GrainTurnMinter};
use dregg_agent::receipt::ReceiptBody;
use dregg_agent::session::{Confinement, GoalReport, Session, parse_caps_confined};
use dregg_agent::toolkit::Toolkit;
use dregg_agent::tools::OperatorTools;
use dregg_cell::{Cell, CellId};
use hosted_durable::{LeaseCharge, SettleReceipt, Settlement};
use hosted_lease::{FieldElement, HostedLease, LeaseTerms, WORKING_BASE, field_from_u64};
// THE FOLD: the vat's verified lifecycle machine. A tenant's grain lifecycle is a
// `VatState` sealed on the SAME lease cell (slots disjoint from the lease economics),
// advanced only through the legality-checked `apply_transition` — no ad-hoc state.
use starbridge_vat::lifecycle::{WitnessStance, apply_transition, open_vat, read_state};
pub use starbridge_vat::{VatState, VatTransition};

/// **The R1 renter finality anchor**, supplied whole at rent: the renter-chosen
/// `nonce` (the genesis pin, re-exposed bound to the session signer in every
/// attestation so the renter recognizes their own session) AND the renter's
/// ed25519 `pubkey` (the key the platform pins checkpoint countersignatures
/// against, so it can never forge an acknowledgement). One struct on purpose:
/// the R1 teeth ([`grain_verify::GrainAttestation::verify_for_renter`]) need
/// BOTH, so half an anchor is unrepresentable — a grain either has the full
/// anchor or is honestly bare tamper-evidence.
#[derive(Clone, Copy, Debug)]
pub struct RenterAnchor {
    /// The renter-chosen genesis nonce (the pin a renter recognizes).
    pub nonce: [u8; 32],
    /// The renter's ed25519 public key countersignatures are pinned against.
    pub pubkey: [u8; 32],
}

/// Prepaid rent funding: a fresh grain's lease cell is opened holding enough to
/// cover this many rent periods. An operator-facing sizing knob, overflow-checked
/// against attacker-facing `rent_per_period` at rent.
///
/// Honest scope: this pool and [`HostedLease`]'s meter are still TWO separately
/// enforced pieces coupled by app control flow (see the settle-before-meter note
/// on [`AgentPlatform::bill_period`]). The proven FUSED capacity that makes that
/// drift unrepresentable already exists — `dregg_cell::prepaid_lease` (escrow ⊗
/// obligation in ONE atomic discharge, Lean rung `PrepaidLease.lean`) — but
/// riding it is a `hosted-lease` seam (its cell + meter live inside
/// [`HostedLease`]), named for the main loop.
const FUNDED_PERIODS: i64 = 1024;

/// Durable-image working keys (all `>= WORKING_BASE`): where the grain's lease
/// checkpoint binds the session, so the committed `EXEC_COLL` heap carries — and
/// [`AgentPlatform::verify`] re-checks — the mind's advance.
/// The head receipt hash of the session's cumulative chain (zero = empty chain).
pub const WK_CHAIN_TIP: u32 = WORKING_BASE;
/// The number of committed receipts (turns) in the chain.
pub const WK_NUM_TURNS: u32 = WORKING_BASE + 1;
/// The session's cumulative consumed budget.
pub const WK_CONSUMED: u32 = WORKING_BASE + 2;

/// One rented agent grain: the confined session, its hosting lease, the terms, and
/// the workdir its fs-grants resolve against (the platform roots every drive's
/// toolkit here — a caller cannot hand a grain tools rooted outside its rented
/// confinement).
struct Tenant {
    session: Session,
    lease: HostedLease,
    /// **THE FOLD — the grain's verified lifecycle state.** A vat lifecycle
    /// (`Created`/`Running`/`Sleeping`/`Lapsed`/`Reaped`) sealed on the lease cell
    /// (slots disjoint from the lease economics) at rent. This field is the cached
    /// read of [`starbridge_vat::lifecycle::read_state`] over `lease.cell()`; every
    /// mutation goes through [`Tenant::transition`], which advances it ONLY via the
    /// legality-checked [`apply_transition`] (the executor's `Monotonic(VAT_PHASE)`
    /// tooth), so an illegal move (e.g. waking a reaped grain) is refused up front.
    vat: VatState,
    terms: LeaseTerms,
    workdir: std::path::PathBuf,
    /// The account that owns this grain — the only subject authorized to drive it.
    owner: String,
    /// **R1 — the renter finality anchor** ([`RenterAnchor`]), or `None` when the
    /// renter supplied none at rent (R1 is then unavailable — the grain falls back
    /// to bare tamper-evidence).
    anchor: Option<RenterAnchor>,
    /// The latest renter-countersigned checkpoint (`POST <host>/checkpoint`), stored
    /// so `attest` can hand it to a third-party verifier for the anti-rewrite/anti-
    /// truncation teeth. Monotone in `num_turns` (never regresses on store).
    checkpoint: Option<grain_verify::CountersignedCheckpoint>,
    /// **R2 — the committed-turn manifest**: every kernel-turn hash a
    /// [`GrainTurnMinter`] committed for this grain across every
    /// [`drive_minted`](AgentPlatform::drive_minted), in order. What
    /// [`verify_r2`](AgentPlatform::verify_r2) checks the receipts' links against.
    committed_turns: Vec<[u8; 32]>,
    /// **The share ACL** — `(verified X-Dregg-Subject → [`Role`])` grants beyond the
    /// owner. The owner is NOT stored here (they are implicit [`Role::Admin`] via
    /// [`AgentPlatform::role_of`]); a subject absent from both the owner slot and
    /// this map is a non-member (fail-closed → the routes 404, no existence oracle).
    acl: HashMap<String, Role>,
}

impl Tenant {
    /// Advance the grain's lifecycle by ONE vat transition on the lease cell — the
    /// single seam every lifecycle move flows through. It calls the legality-checked
    /// [`apply_transition`] (so an illegal move — waking a reaped grain, sleeping a
    /// non-running one — is refused by the machine's own tooth, agreeing with the
    /// executor's `Monotonic(VAT_PHASE)` re-enforcement), then caches the new state.
    /// On `BringUp` it binds the box + endpoint to a stable per-host token (the box
    /// is re-placed on every wake); the other transitions clear them (no box while
    /// not Running).
    fn transition(&mut self, host: &str, t: VatTransition) -> Result<VatState, AgentPlatformError> {
        let (machine, endpoint) = match t {
            VatTransition::BringUp => (box_token(host), box_token(host) ^ 0x01),
            VatTransition::Sleep | VatTransition::Lapse | VatTransition::Reap => (0, 0),
        };
        let to = apply_transition(self.lease.cell_mut(), t, machine, endpoint)
            .map_err(|e| AgentPlatformError::Lifecycle(format!("{e:?}")))?;
        self.vat = to;
        Ok(to)
    }
}

/// A stable, nonzero box/endpoint token for a host — the vat's `MACHINE`/`ENDPOINT`
/// slots want a placement identity, and a hosted agent grain's "box" is the
/// in-process session, so we bind a deterministic per-host token (the first 8 bytes
/// of `blake3(host)`, forced nonzero) re-bound on each `BringUp`.
fn box_token(host: &str) -> u64 {
    let h = blake3::hash(host.as_bytes());
    let mut b = [0u8; 8];
    b.copy_from_slice(&h.as_bytes()[..8]);
    u64::from_le_bytes(b) | 1
}

/// The platform every rented agent grain is hosted on, keyed by host.
pub struct AgentPlatform {
    /// Keyed by host. The value is a **per-tenant** `Arc<Mutex<Tenant>>`: every
    /// method locks this outer map only *briefly* — to clone the grain's Arc (or
    /// insert/remove/scan) — then DROPS the map lock and locks the individual
    /// tenant for the operation. So a long-running drive (esp. `drive_live`'s
    /// blocking provider round-trip) holds only its OWN grain's lock and never
    /// stalls another tenant's rent/drive/verify/bill/attest (no head-of-line DoS).
    tenants: Mutex<HashMap<String, Arc<Mutex<Tenant>>>>,
    /// The current block height, advanced by the operator (from the node) via
    /// [`set_clock`](AgentPlatform::set_clock). `drive` audits each grain's rent
    /// schedule against it, so a delinquent grain lapses on use rather than being
    /// hosted free forever. Stays `0` (nothing lapses) until an operator ticks it.
    clock: std::sync::atomic::AtomicI64,
}

/// Why an agent-platform operation was refused.
#[derive(Debug)]
pub enum AgentPlatformError {
    /// The cap bundle string was ill-formed or requested a hosted-forbidden tool.
    Caps(String),
    /// Opening the confined session failed.
    Session(String),
    /// No grain is hosted at that host.
    NoSuchGrain(String),
    /// A grain is already hosted at that host (rent does not evict an incumbent).
    GrainOccupied(String),
    /// **R1** — a checkpoint could not be offered / accepted (see the message):
    /// the session has committed nothing yet, no renter key was pinned at rent, the
    /// countersignature is wrong, or the checkpoint does not match the chain.
    Checkpoint(String),
    /// The caller is not authorized for this grain (not its owner).
    Unauthorized(String),
    /// The rental terms are ill-formed (e.g. a rent that overflows the funding).
    BadTerms(String),
    /// The grain's hosting lease has lapsed (non-payment): the slot is reclaimed.
    Lapsed,
    /// A vat lifecycle transition was refused by the machine (an illegal move —
    /// e.g. waking a reaped grain, or a malformed lifecycle slot).
    Lifecycle(String),
    /// Advancing the lease's durable checkpoint was refused.
    Lease(String),
    /// Settling a rent period was refused.
    Settle(String),
    /// Re-witnessing the session failed (a tampered receipt in some goal).
    Verify(String),
    /// The lease's durable image does not bind the session (the committed digest /
    /// chain tip / turn count / consumed disagree with the live session — a stale,
    /// tampered, or diverged image).
    ImageDiverged(String),
}

impl std::fmt::Display for AgentPlatformError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AgentPlatformError::Caps(e) => write!(f, "cap bundle refused: {e}"),
            AgentPlatformError::Session(e) => write!(f, "session open refused: {e}"),
            AgentPlatformError::NoSuchGrain(h) => write!(f, "no agent grain hosted at `{h}`"),
            AgentPlatformError::GrainOccupied(h) => write!(f, "a grain is already hosted at `{h}`"),
            AgentPlatformError::Checkpoint(e) => write!(f, "renter checkpoint refused: {e}"),
            AgentPlatformError::Unauthorized(s) => write!(f, "not authorized for this grain: {s}"),
            AgentPlatformError::BadTerms(e) => write!(f, "ill-formed rental terms: {e}"),
            AgentPlatformError::Lapsed => {
                write!(f, "the hosting lease has lapsed: grain reclaimed")
            }
            AgentPlatformError::Lifecycle(e) => write!(f, "vat lifecycle transition refused: {e}"),
            AgentPlatformError::Lease(e) => write!(f, "durable checkpoint refused: {e}"),
            AgentPlatformError::Settle(e) => write!(f, "rent settlement refused: {e}"),
            AgentPlatformError::Verify(e) => write!(f, "session re-witness failed: {e}"),
            AgentPlatformError::ImageDiverged(e) => {
                write!(f, "the durable image does not bind the session: {e}")
            }
        }
    }
}

impl std::error::Error for AgentPlatformError {}

impl Default for AgentPlatform {
    fn default() -> Self {
        Self::new()
    }
}

impl AgentPlatform {
    /// An empty platform.
    pub fn new() -> AgentPlatform {
        AgentPlatform {
            tenants: Mutex::new(HashMap::new()),
            clock: std::sync::atomic::AtomicI64::new(0),
        }
    }

    /// Advance the platform's notion of the current block height (from the node). A
    /// production operator ticks this each block; `drive` audits every grain's rent
    /// schedule against it, so a grain behind on rent lapses on next use. (The
    /// separate biller loop calls [`bill_period`](AgentPlatform::bill_period) to
    /// actually collect + settle the rent.)
    ///
    /// **Monotone**: block height never rewinds, so a regression is ignored (a
    /// rewound clock would silently re-extend credit to a delinquent-but-not-yet-
    /// lapsed grain). Returns the effective clock after the tick.
    pub fn set_clock(&self, block: i64) -> i64 {
        self.clock
            .fetch_max(block, std::sync::atomic::Ordering::Relaxed)
            .max(block)
    }

    /// The current block height the platform audits against.
    pub fn clock(&self) -> i64 {
        self.clock.load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Clone the per-tenant handle for `host` under a BRIEF map lock (dropped on
    /// return), so the caller can then lock just that one grain for a long
    /// operation without holding the platform-wide map lock across it.
    fn tenant_arc(&self, host: &str) -> Result<Arc<Mutex<Tenant>>, AgentPlatformError> {
        self.tenants
            .lock()
            .expect("platform poisoned")
            .get(host)
            .cloned()
            .ok_or_else(|| AgentPlatformError::NoSuchGrain(host.to_string()))
    }

    /// Provision an agent grain for `account` at `host`: parse `caps` under
    /// [`Confinement::Hosted`] (a raw `shell` is refused), open a confined session
    /// with `budget`, and open the rental lease (funded to cover
    /// [`FUNDED_PERIODS`]). The grain's tools resolve fs grants against `workdir`
    /// (every drive's toolkit is rooted there by the platform).
    ///
    /// `anchor` is the optional **R1 renter finality anchor** ([`RenterAnchor`] —
    /// the genesis nonce + the renter's countersign pubkey, whole or absent).
    /// With it, the grain supports the anti-rewrite/anti-truncation
    /// `GET`/`POST <host>/checkpoint` protocol; without it, the grain is honestly
    /// bare tamper-evidence.
    #[allow(clippy::too_many_arguments)] // one rent verb > two half-anchored ones
    pub fn rent(
        &self,
        host: impl Into<String>,
        account: &str,
        caps: &str,
        budget: i64,
        workdir: &str,
        terms: LeaseTerms,
        anchor: Option<RenterAnchor>,
    ) -> Result<String, AgentPlatformError> {
        let host = host.into();
        // Never evict an incumbent: renting an occupied host is refused, not a
        // silent overwrite (which would destroy a live tenant's session + lease).
        {
            let tenants = self.tenants.lock().expect("platform poisoned");
            if tenants.contains_key(&host) {
                return Err(AgentPlatformError::GrainOccupied(host));
            }
        }
        // Prepaid rent funding, overflow-checked (rent_per_period is attacker-facing
        // over the wire): a huge rent must fail closed, not wrap to garbage or panic.
        let funding = (terms.rent_per_period as i64)
            .checked_mul(FUNDED_PERIODS)
            .ok_or_else(|| {
                AgentPlatformError::BadTerms("rent_per_period funding overflows".into())
            })?;

        let bundle = parse_caps_confined(caps, account, budget, workdir, Confinement::Hosted)
            .map_err(AgentPlatformError::Caps)?;
        let session = Session::open(account, bundle.spec)
            .map_err(|e| AgentPlatformError::Session(e.to_string()))?;

        // THE FOLD: rent = open_vat (opens the durable-execution lease AND seals the
        // vat lifecycle at `Created` on the same cell) + a `BringUp` transition to
        // `Running` (the launch). The lease is then wrapped read/meter-side by a
        // `HostedLease` over the SAME already-opened cell (`from_cell`, never a second
        // open of the WriteOnce economic slots). A hosted agent grain rents Symbolic
        // (verify-later) — proofs are re-derived on collapse, not proof-as-you-go.
        let mut lease_cell =
            Cell::with_balance(bytes32(terms.lease), bytes32(terms.asset), funding);
        open_vat(
            &mut lease_cell,
            &terms,
            field_from_u64(0),
            WitnessStance::Symbolic,
        )
        .map_err(|e| AgentPlatformError::Lease(format!("{e:?}")))?;
        // Launch: Created → Running, binding the box + endpoint for this host.
        apply_transition(
            &mut lease_cell,
            VatTransition::BringUp,
            box_token(&host),
            box_token(&host) ^ 0x01,
        )
        .map_err(|e| AgentPlatformError::Lifecycle(format!("{e:?}")))?;
        let vat =
            read_state(&lease_cell).map_err(|e| AgentPlatformError::Lifecycle(format!("{e:?}")))?;
        let lease = HostedLease::from_cell(lease_cell, terms.clone());

        let mut tenants = self.tenants.lock().expect("platform poisoned");
        // Re-check under the write lock (TOCTOU with the read check above).
        if tenants.contains_key(&host) {
            return Err(AgentPlatformError::GrainOccupied(host));
        }
        tenants.insert(
            host.clone(),
            Arc::new(Mutex::new(Tenant {
                session,
                lease,
                vat,
                terms,
                workdir: std::path::PathBuf::from(workdir),
                owner: account.to_string(),
                anchor,
                checkpoint: None,
                committed_turns: Vec::new(),
                acl: HashMap::new(),
            })),
        );
        Ok(host)
    }

    /// The account that owns the grain at `host` (the only subject authorized to
    /// drive it), if hosted. The serve layer checks the caller's verified subject
    /// against this before driving.
    pub fn owner_of(&self, host: &str) -> Option<String> {
        // Brief map lock to clone the Arc, then read the owner off the tenant.
        let arc = self
            .tenants
            .lock()
            .expect("platform poisoned")
            .get(host)
            .cloned()?;
        let owner = arc.lock().expect("tenant poisoned").owner.clone();
        Some(owner)
    }

    /// **The caller's role on the grain at `host`, if any.** The owner is implicit
    /// [`Role::Admin`]; a shared subject gets its ACL-granted role; a non-member — or
    /// no grain here at all — is `None`. The serve layer turns `None` into a `404`
    /// on every route, so a non-member gets no existence oracle (a grain that isn't
    /// theirs is indistinguishable from a grain that isn't there).
    pub fn role_of(&self, host: &str, subject: &str) -> Option<Role> {
        let arc = self
            .tenants
            .lock()
            .expect("platform poisoned")
            .get(host)
            .cloned()?;
        let t = arc.lock().expect("tenant poisoned");
        if t.owner == subject {
            return Some(Role::Admin);
        }
        t.acl.get(subject).copied()
    }

    /// **Share the grain at `host` with `subject` at `role`** (owner/Admin only).
    /// The `caller` must resolve to an Admin role on the grain; a member below Admin
    /// is [`Unauthorized`](AgentPlatformError::Unauthorized) (403) and a non-member
    /// is [`NoSuchGrain`](AgentPlatformError::NoSuchGrain) (404 — no existence
    /// oracle). Granting a role to the owner is a no-op (they stay implicit Admin).
    pub fn share(
        &self,
        host: &str,
        caller: &str,
        subject: &str,
        role: Role,
    ) -> Result<(), AgentPlatformError> {
        match self.role_of(host, caller) {
            Some(Role::Admin) => {}
            Some(_) => {
                return Err(AgentPlatformError::Unauthorized(caller.to_string()));
            }
            None => return Err(AgentPlatformError::NoSuchGrain(host.to_string())),
        }
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        if guard.owner == subject {
            // The owner is already implicit Admin; do not shadow them in the ACL.
            return Ok(());
        }
        guard.acl.insert(subject.to_string(), role);
        Ok(())
    }

    /// **Revoke `subject`'s share on the grain at `host`** (owner/Admin only). Same
    /// authorization shape as [`share`](AgentPlatform::share). Un-sharing a subject
    /// that holds no grant succeeds (idempotent); the owner cannot be un-shared
    /// (they are never in the ACL, and stay implicit Admin).
    pub fn unshare(
        &self,
        host: &str,
        caller: &str,
        subject: &str,
    ) -> Result<(), AgentPlatformError> {
        match self.role_of(host, caller) {
            Some(Role::Admin) => {}
            Some(_) => {
                return Err(AgentPlatformError::Unauthorized(caller.to_string()));
            }
            None => return Err(AgentPlatformError::NoSuchGrain(host.to_string())),
        }
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        guard.acl.remove(subject);
        Ok(())
    }

    /// **The grain's drive transcript as an SSE `text/event-stream` body** —
    /// meta/step/done frames replaying every committed reason→act→observe step (see
    /// [`transcript`](crate::transcript) for the honest replay-not-live scope).
    /// Any member (Viewer+) may read it; the serve layer gates that.
    pub fn transcript(&self, host: &str) -> Result<String, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        Ok(transcript::transcript_stream(host, &guard.session))
    }

    /// The hosts currently served.
    pub fn hosts(&self) -> Vec<String> {
        let mut hosts: Vec<String> = self
            .tenants
            .lock()
            .expect("platform poisoned")
            .keys()
            .cloned()
            .collect();
        hosts.sort();
        hosts
    }

    /// Drive one typed `goal` through the grain at `host`: run the confined session's
    /// reason→act→observe loop against `brain` (metered, receipted, gated by the
    /// fixed cap bundle; the toolkit is the platform's operator tools ROOTED AT THE
    /// GRAIN'S RENTED WORKDIR — a caller cannot substitute tools rooted outside the
    /// confinement), then advance the lease's durable checkpoint with the verified
    /// session binding. Refuses on a lapsed lease. Returns the goal's delta report.
    ///
    /// The receipts this path seals carry NO kernel-turn link (the honest default:
    /// no executor is attached). For receipts that are views over genuine committed
    /// kernel turns — the R2 rung — use [`drive_minted`](Self::drive_minted).
    pub fn drive(
        &self,
        host: &str,
        goal: impl Into<String>,
        brain: &mut dyn AgentBrain,
    ) -> Result<GoalReport, AgentPlatformError> {
        self.drive_in(host, goal, brain, None)
    }

    /// **R2 — [`drive`](Self::drive) welded to genuine kernel turns.** Every
    /// admitted action is first minted as a REAL committed executor turn through
    /// `minter` (refusal admits nothing — the executor's own caveat is the
    /// host-side meter), and the committed turn hash is sealed into the action's
    /// receipt as its `turn_receipt_hash`. The platform records each committed
    /// hash into the grain's manifest, which [`verify_r2`](Self::verify_r2) checks
    /// every receipt against.
    ///
    /// The real kernel minter is `grain-turn`'s `ToolGatewayMinter` (the verified
    /// executor + proven `ToolGateway`); `dregg_agent`'s `SyntheticMinter` only
    /// exercises the seam and never stands in for it silently — the caller always
    /// chooses, explicitly.
    pub fn drive_minted(
        &self,
        host: &str,
        goal: impl Into<String>,
        brain: &mut dyn AgentBrain,
        minter: &mut dyn GrainTurnMinter,
    ) -> Result<GoalReport, AgentPlatformError> {
        self.drive_in(host, goal, brain, Some(minter))
    }

    /// The one drive path both public drives share: audit the rent schedule, run
    /// the goal (optionally minted), record any committed turn hashes, checkpoint.
    fn drive_in(
        &self,
        host: &str,
        goal: impl Into<String>,
        brain: &mut dyn AgentBrain,
        minter: Option<&mut dyn GrainTurnMinter>,
    ) -> Result<GoalReport, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        let tenant = &mut *guard;
        // Audit the rent schedule at the operator's clock — a grain behind on rent
        // lapses ON USE rather than trusting a stale flag (the "free hosting" fix).
        let _ = tenant
            .lease
            .lapse_if_behind(self.clock.load(std::sync::atomic::Ordering::Relaxed));
        if tenant.lease.is_lapsed() {
            return Err(AgentPlatformError::Lapsed);
        }
        let toolkit = OperatorTools::new(Toolkit::new(), &tenant.workdir);
        let report = match minter {
            None => tenant.session.run_goal(goal, brain, &toolkit),
            Some(inner) => {
                // Record every hash the minter commits into the grain's manifest —
                // the host-side committed-turn set verify_r2 audits receipts against.
                let mut recording = RecordingMinter {
                    inner,
                    minted: Vec::new(),
                };
                let report =
                    tenant
                        .session
                        .run_goal_minted(goal, brain, &toolkit, Some(&mut recording));
                tenant.committed_turns.extend(recording.minted);
                report
            }
        };
        checkpoint_tenant(tenant)?;
        Ok(report)
    }

    /// Drive one `goal` through the grain at `host` with a LIVE model brain: wire
    /// dregg-agent's OpenAI-compatible HTTP transport (a BYO key resolved from env)
    /// as the session's brain over the grain's granted `tools`, run it, and
    /// checkpoint. Each tool-call the model reaches for still crosses the fixed cap
    /// bundle before it becomes a receipt. Refuses on a lapsed lease or a missing
    /// key. `model`/base URL come from `DREGG_LLM_MODEL`/`DREGG_LLM_BASE` (defaults
    /// otherwise).
    ///
    /// Honest scope: this path is UNMINTED (receipts carry no kernel-turn link), so
    /// a live-driven grain verifies at R0/R1, not R2 — welding the live drive
    /// through a real `GrainTurnMinter` rides the `grain-turn` kernel weld once
    /// that crate reconciles into this workspace (named for the main loop).
    #[cfg(feature = "live-brain")]
    pub fn drive_live(
        &self,
        host: &str,
        goal: impl Into<String>,
        tools: &[String],
    ) -> Result<GoalReport, AgentPlatformError> {
        use dregg_agent::brain::{LiveOpenAICompatCaller, OpenAICompatBrain};

        let goal = goal.into();
        // Lock ONLY this grain across the blocking provider round-trip below — the
        // platform-wide map lock is already dropped, so a slow/stalled live drive
        // here never stalls another tenant (the head-of-line fix).
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        let tenant = &mut *guard;
        // Audit the rent schedule at the operator's clock — a grain behind on rent
        // lapses ON USE rather than trusting a stale flag (the "free hosting" fix).
        let _ = tenant
            .lease
            .lapse_if_behind(self.clock.load(std::sync::atomic::Ordering::Relaxed));
        if tenant.lease.is_lapsed() {
            return Err(AgentPlatformError::Lapsed);
        }
        let key = live_key()
            .ok_or_else(|| AgentPlatformError::Session("no LLM key in env (DREGG_LLM_API_KEY / ANTHROPIC_API_KEY / OPENAI_API_KEY / NVIDIA_API_KEY)".into()))?;
        let base = std::env::var("DREGG_LLM_BASE")
            .unwrap_or_else(|_| "https://api.openai.com".to_string());
        let model = std::env::var("DREGG_LLM_MODEL").unwrap_or_else(|_| "gpt-4o-mini".to_string());
        let mut brain = OpenAICompatBrain::with_base(
            &goal,
            tools.to_vec(),
            vec![],
            key,
            &base,
            &model,
            LiveOpenAICompatCaller::new(),
        );
        let toolkit = OperatorTools::new(Toolkit::new(), &tenant.workdir);
        let report = tenant.session.run_goal(&goal, &mut brain, &toolkit);
        checkpoint_tenant(tenant)?;
        Ok(report)
    }

    /// Bill one rent `period` for `host` at `clock`: meter it on the lease (the
    /// obligation forge-detector bites an early/double/off-schedule charge) and
    /// settle the rent through `settlement` — the in-process double in tests, or the
    /// on-chain node rail in production.
    ///
    /// Honest shape: meter and settle here are TWO enforced pieces sequenced by
    /// this method (the ordering note below is app-level discipline against
    /// meter/pay drift). The proven FUSED capacity where that drift is
    /// UNREPRESENTABLE — `dregg_cell::prepaid_lease` (escrow ⊗ obligation, one
    /// atomic discharge, Lean rung) — is the named upgrade, gated on
    /// `hosted-lease` adopting it (the meter and the cell live inside
    /// [`HostedLease`], not here).
    pub fn bill_period<S: Settlement>(
        &self,
        host: &str,
        period: i64,
        clock: i64,
        settlement: &S,
    ) -> Result<SettleReceipt, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        let tenant = &mut *guard;
        // SETTLE BEFORE METER. The rent for a period is the sealed terms.rent_per_
        // period (exactly what meter would discharge), so we can build the charge
        // without advancing the meter. Settling first means a settlement FAILURE
        // leaves the meter cursor un-advanced and the whole bill retryable — vs.
        // meter-first, where a settle failure would strand the period
        // discharged-but-unpaid (the meter's one-shot forbids re-discharge). The
        // Settlement rail is exactly-once by (lease_id, period), so a retry replays
        // the settle rather than double-paying.
        let terms = &tenant.terms;
        let charge = LeaseCharge::new(
            hex32(terms.lease),
            hex32(terms.provider),
            hex32(terms.asset),
            host,
            period,
            terms.rent_per_period as i64,
        );
        let receipt = settlement
            .settle(&charge)
            .map_err(|e| AgentPlatformError::Settle(e.to_string()))?;
        // Advance the meter only after the rent has settled.
        tenant
            .lease
            .meter(period, clock)
            .map_err(|e| AgentPlatformError::Lease(e.to_string()))?;
        Ok(receipt)
    }

    /// Re-witness the session at `host`: the cumulative receipt chain is
    /// signature-consistent, unbroken, monotone, and the consumed budget stays
    /// at/under the ceiling — AND the lease's durable image binds this session
    /// (the committed digest / chain tip / turn count / consumed read back from
    /// the `EXEC_COLL` heap agree with the live session; a stale or tampered
    /// image is [`ImageDiverged`](AgentPlatformError::ImageDiverged)).
    ///
    /// Honest strength (the R-ladder, crate docs): the chain key is a fresh
    /// RANDOM secret (R0 — a third party holding the report cannot forge), but
    /// the HOST runs the signer, so this alone is tamper-evidence, not
    /// host-independence. R1 ([`RenterAnchor`] + the checkpoint countersign) adds
    /// third-party-verifiable anti-rewrite/anti-truncation; R2
    /// ([`verify_r2`](Self::verify_r2)) binds each receipt to a committed kernel
    /// turn; proving those turns RAN is R3's whole-history STARK leg
    /// ([`grain_verify::WHOLE_HISTORY_GAP`]).
    pub fn verify(&self, host: &str) -> Result<AgentVerified, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        let verified = guard
            .session
            .verify()
            .map_err(|e| AgentPlatformError::Verify(format!("{e:?}")))?;
        image_binds(&guard)?;
        Ok(verified)
    }

    /// **R2 — re-witness the grain at `host` against its committed-turn manifest**:
    /// [`verify`](Self::verify) (chain + budget + durable-image bind) PLUS every
    /// admitted receipt must be a view over a kernel turn the platform's minter
    /// actually committed ([`drive_minted`](Self::drive_minted)'s recorded
    /// manifest). A receipt with no turn link — e.g. from a plain unminted
    /// [`drive`](Self::drive) — or with a link naming no committed turn is
    /// REFUSED, both teeth per `grain_verify::GrainAttestation::verify_r2`.
    ///
    /// Honest scope (R2, not R3): this proves the receipts are bound to turns the
    /// executor host committed and that the meter was executor-enforced; it does
    /// not re-execute the turns (that is the whole-history STARK leg).
    pub fn verify_r2(&self, host: &str) -> Result<grain_verify::R2Verified, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        image_binds(&guard)?;
        self.attestation_of(&guard)
            .verify_r2(&guard.committed_turns)
            .map_err(|e| AgentPlatformError::Verify(format!("{e:?}")))
    }

    /// Lapse the lease at `host` if it is behind schedule at `clock` (non-payment):
    /// the grain is reclaimed and driving it is refused. Returns whether it lapsed.
    pub fn reap_if_behind(&self, host: &str, clock: i64) -> Result<bool, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        let lapsed = guard
            .lease
            .lapse_if_behind(clock)
            .map_err(|e| AgentPlatformError::Lease(e.to_string()))?;
        // THE FOLD: mirror the lease's LAPSED tooth in the vat lifecycle — any live
        // grain moves to `Lapsed` (routed through the legality-checked transition, so
        // an already-lapsed/terminal grain is a no-op, never a double-lapse).
        if lapsed && guard.vat != VatState::Lapsed && !guard.vat.is_terminal() {
            guard.transition(host, VatTransition::Lapse)?;
        }
        Ok(lapsed)
    }

    /// **Sleep the grain at `host`** — checkpoint-and-tear-down. Routes the vat
    /// `Running → Sleeping` transition: the box goes dark and metering stops; the
    /// durable image is what follows. Refused if the grain is not Running (the
    /// machine's own tooth). The session + committed history are retained for the wake.
    pub fn sleep(&self, host: &str) -> Result<VatState, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        guard.transition(host, VatTransition::Sleep)
    }

    /// **Wake the grain at `host` from its lease** — the named *wake-from-lease* move,
    /// delivered for free by the fold: the vat's `BringUp` from `Sleeping → Running`
    /// re-places the box, restores from the durable image, and resumes metering.
    /// Refused if the grain is not Sleeping (the machine's own tooth).
    pub fn wake(&self, host: &str) -> Result<VatState, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        guard.transition(host, VatTransition::BringUp)
    }

    /// The grain's current verified lifecycle state at `host` — the vat [`VatState`]
    /// read off the lease cell (created / running / sleeping / lapsed / reaped), or
    /// [`NoSuchGrain`](AgentPlatformError::NoSuchGrain).
    pub fn grain_state(&self, host: &str) -> Result<VatState, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        read_state(guard.lease.cell()).map_err(|e| AgentPlatformError::Lifecycle(format!("{e:?}")))
    }

    /// The renter's artifact for the grain at `host`: a
    /// [`grain_verify::GrainAttestation`] over the session's cumulative receipt
    /// chain, carrying whatever R1 anchor material the grain holds (the genesis
    /// pin bound to THIS chain's signer + the latest renter-countersigned
    /// checkpoint), so a third party can run the anti-rewrite/anti-truncation
    /// teeth via `verify_for_renter`.
    ///
    /// Honest strength: with no anchor this is a **tamper-evident receipt log**
    /// under a random secret signer (R0) — the HOST runs the signer, so a
    /// malicious host could still present a self-consistent alternate history;
    /// that is exactly what the R1 anchor pins and the R3 whole-history STARK leg
    /// ([`grain_verify::WHOLE_HISTORY_GAP`]) will remove. Nothing below R3 forces
    /// completeness ("did nothing else").
    pub fn attest(&self, host: &str) -> Result<grain_verify::GrainAttestation, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        Ok(self.attestation_of(&guard))
    }

    /// Assemble the grain's attestation with its R1 anchor material attached
    /// (shared by [`attest`](Self::attest) and [`verify_r2`](Self::verify_r2)).
    fn attestation_of(&self, tenant: &Tenant) -> grain_verify::GrainAttestation {
        let mut att = grain_verify::GrainAttestation::attest(&tenant.session);
        if let Some(anchor) = &tenant.anchor {
            att = att.with_genesis(grain_verify::GenesisPin {
                renter_nonce: anchor.nonce,
                signer: tenant.session.report().signer,
            });
        }
        if let Some(cs) = &tenant.checkpoint {
            att = att.with_checkpoint(cs.clone());
        }
        att
    }

    /// **R1** — the checkpoint a renter should countersign for the grain's CURRENT
    /// chain tip: `(head_root, num_turns)`. This is what `GET <host>/checkpoint`
    /// returns; the renter countersigns it with
    /// [`grain_verify::countersign_checkpoint`] and POSTs it back. Refused if the
    /// session has committed nothing yet (no tip to acknowledge).
    pub fn checkpoint_offer(
        &self,
        host: &str,
    ) -> Result<grain_verify::RenterCheckpoint, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        grain_verify::GrainAttestation::attest(&guard.session)
            .checkpoint_to_countersign()
            .ok_or_else(|| {
                AgentPlatformError::Checkpoint(
                    "the grain has committed no turns to checkpoint yet".into(),
                )
            })
    }

    /// **R1** — accept a renter's countersigned checkpoint (`POST <host>/checkpoint`)
    /// and store it as the grain's latest acknowledgement. Fail-closed: a renter
    /// pubkey must have been pinned at rent, the countersignature must be BY that
    /// pinned key and verify, the checkpoint must match a real committed prefix of
    /// the current chain (so the platform never stores a bogus root), and it must
    /// not regress below the stored acknowledgement (`num_turns` monotone).
    pub fn submit_checkpoint(
        &self,
        host: &str,
        cs: grain_verify::CountersignedCheckpoint,
    ) -> Result<(), AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        let tenant = &mut *guard;
        let pinned = tenant.anchor.map(|a| a.pubkey).ok_or_else(|| {
            AgentPlatformError::Checkpoint(
                "no renter anchor pinned at rent; R1 unavailable for this grain".into(),
            )
        })?;
        if cs.renter_pubkey != pinned {
            return Err(AgentPlatformError::Checkpoint(
                "countersignature is not by the pinned renter key".into(),
            ));
        }
        if !cs.sig_verifies() {
            return Err(AgentPlatformError::Checkpoint(
                "renter countersignature does not verify".into(),
            ));
        }
        // The acknowledged checkpoint must match a genuine committed prefix — the
        // platform never stores a root the chain does not actually have.
        let report = tenant.session.report();
        let n = cs.checkpoint.num_turns;
        if n == 0 || n as usize > report.receipts.len() {
            return Err(AgentPlatformError::Checkpoint(format!(
                "checkpoint num_turns {n} is not a committed prefix (chain has {} turns)",
                report.receipts.len()
            )));
        }
        let at = report.receipts[(n - 1) as usize].receipt_hash();
        if at != Some(cs.checkpoint.head_root) {
            return Err(AgentPlatformError::Checkpoint(
                "checkpoint head_root does not match the chain at that position".into(),
            ));
        }
        // Monotone: never regress the acknowledged tip (an old checkpoint replayed
        // to enable a later truncation is refused on store).
        if let Some(prev) = &tenant.checkpoint
            && n < prev.checkpoint.num_turns
        {
            return Err(AgentPlatformError::Checkpoint(format!(
                "checkpoint regresses: num_turns {n} < stored {}",
                prev.checkpoint.num_turns
            )));
        }
        tenant.checkpoint = Some(cs);
        Ok(())
    }

    /// The consumed budget of the grain at `host` (its running meter).
    pub fn consumed(&self, host: &str) -> Result<i64, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let consumed = arc.lock().expect("tenant poisoned").session.consumed();
        Ok(consumed)
    }
}

/// Advance the grain's lease checkpoint (the `Monotonic` cursor moves, so a light
/// client sees the mind advance and it cannot rewind) and write the **session
/// binding** into the durable image: the `blake3(report)` digest (the cursor's
/// bound state) plus the chain tip / turn count / consumed working keys
/// ([`WK_CHAIN_TIP`]/[`WK_NUM_TURNS`]/[`WK_CONSUMED`]). [`image_binds`] reads all
/// four back on every platform `verify`, so a stale/tampered image is a refusal,
/// not a decoration.
///
/// Honest scope: the image BINDS the session (verified read-back), it does not
/// yet carry the full receipt bytes — a grain is not yet WAKEABLE from the lease
/// heap alone (that is THE-GRAIN's `AgentMemoryCheckpoint`-onto-`EXEC_COLL` weld,
/// named for the main loop; the binding here is the cursor it will verify
/// against).
fn checkpoint_tenant(tenant: &mut Tenant) -> Result<(), AgentPlatformError> {
    let report = tenant.session.report();
    let digest = session_digest(&report);
    tenant
        .lease
        .checkpoint(digest, &session_binding(&report))
        .map_err(|e| AgentPlatformError::Lease(e.to_string()))?;
    Ok(())
}

/// The working-memory binding of a session report: chain tip (zero for an empty
/// chain), committed turn count, cumulative consumed.
fn session_binding(report: &AgentRunReport) -> [(u32, FieldElement); 3] {
    let tip = report
        .receipts
        .last()
        .and_then(|r| r.receipt_hash())
        .unwrap_or([0u8; 32]);
    [
        (WK_CHAIN_TIP, tip),
        (WK_NUM_TURNS, field_from_u64(report.receipts.len() as u64)),
        (WK_CONSUMED, field_from_u64(report.consumed.max(0) as u64)),
    ]
}

/// **Read the durable image back and check it binds the live session** — the
/// other half that makes the checkpoint a verified binding instead of a stamp
/// nothing reads. Compares the committed digest ([`hosted_lease::KEY_DIGEST`])
/// and every [`session_binding`] working key against values re-derived from the
/// session right now. Skipped only before the first checkpoint (`step == 0`, the
/// genesis image — there is nothing bound yet). Any disagreement — a divergence
/// between the witnessed durable image and the mind it claims to bind — is
/// [`AgentPlatformError::ImageDiverged`].
fn image_binds(tenant: &Tenant) -> Result<(), AgentPlatformError> {
    if tenant.lease.step() == 0 {
        return Ok(());
    }
    let report = tenant.session.report();
    let want_digest = session_digest(&report);
    let got_digest = tenant.lease.read_working(hosted_lease::KEY_DIGEST);
    if got_digest != Some(want_digest) {
        return Err(AgentPlatformError::ImageDiverged(
            "committed state digest disagrees with the live session".into(),
        ));
    }
    for (key, want) in session_binding(&report) {
        if tenant.lease.read_working(key) != Some(want) {
            let name = match key {
                WK_CHAIN_TIP => "chain tip",
                WK_NUM_TURNS => "turn count",
                _ => "consumed",
            };
            return Err(AgentPlatformError::ImageDiverged(format!(
                "committed {name} disagrees with the live session"
            )));
        }
    }
    Ok(())
}

/// A field-element digest of the session's cumulative report — the state the
/// lease checkpoint cursor binds (see [`checkpoint_tenant`] / [`image_binds`]).
fn session_digest(report: &AgentRunReport) -> FieldElement {
    let bytes = serde_json::to_vec(report).unwrap_or_default();
    *blake3::hash(&bytes).as_bytes()
}

/// Forwards to a caller-supplied [`GrainTurnMinter`] and RECORDS every committed
/// turn hash, so [`AgentPlatform::drive_minted`] can append exactly what was
/// minted to the grain's manifest (the minter trait itself exposes no history).
struct RecordingMinter<'a> {
    inner: &'a mut dyn GrainTurnMinter,
    minted: Vec<[u8; 32]>,
}

impl GrainTurnMinter for RecordingMinter<'_> {
    fn mint_turn(
        &mut self,
        label: &str,
        cost: i64,
        consumed_after: i64,
        cell_root: [u8; 32],
    ) -> Result<[u8; 32], String> {
        let hash = self
            .inner
            .mint_turn(label, cost, consumed_after, cell_root)?;
        self.minted.push(hash);
        Ok(hash)
    }
}

/// Resolve a BYO LLM provider key from the env chain (redacted-Debug preserved by
/// `ProviderKey`). Same order the live brain honors.
#[cfg(feature = "live-brain")]
fn live_key() -> Option<dregg_agent::brain::ProviderKey> {
    use dregg_agent::brain::ProviderKey;
    ProviderKey::from_env("dregg", "DREGG_LLM_API_KEY")
        .or_else(|| ProviderKey::from_env("anthropic", "ANTHROPIC_API_KEY"))
        .or_else(|| ProviderKey::from_env("openai", "OPENAI_API_KEY"))
        .or_else(|| ProviderKey::from_env("nvidia", "NVIDIA_API_KEY"))
}

fn bytes32(cell: CellId) -> [u8; 32] {
    let mut a = [0u8; 32];
    a.copy_from_slice(cell.as_bytes());
    a
}

fn hex32(cell: CellId) -> String {
    cell.as_bytes().iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_agent::agent::{AgentAction, PlannedBrain, SyntheticMinter, ToolCall};
    use hosted_durable::TestConservingLedger;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    fn terms() -> LeaseTerms {
        // provider=2, lease cell=7, asset=9; rent 100 every 50 blocks from 1000.
        LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0)
    }

    fn workdir() -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!("dregg-grain-{}", std::process::id()));
        std::fs::create_dir_all(&p).unwrap();
        p
    }

    /// A recorded brain: a fixed plan of fs writes (hosted-safe — no shell).
    fn fs_plan(files: &[(&str, &str)]) -> PlannedBrain {
        let plan = files
            .iter()
            .map(|(path, content)| {
                AgentAction::Op(ToolCall::new(
                    "fs_write",
                    [
                        ("path".to_string(), path.to_string()),
                        ("content".to_string(), content.to_string()),
                    ],
                ))
            })
            .collect();
        PlannedBrain::new(plan)
    }

    #[test]
    fn an_agent_grain_is_rented_driven_metered_witnessed_and_reaped() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "alice.agents.dregg",
                "dga1_alice",
                "fs", // hosted-safe cap bundle (a raw `shell` would be refused)
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision the agent grain");

        // Drive a goal — the confined agent writes two files, metered + receipted.
        let mut brain = fs_plan(&[("notes.txt", "hello"), ("plan.txt", "world")]);
        let report = platform
            .drive(&host, "write my notes", &mut brain)
            .expect("drive the grain");
        assert!(report.admitted > 0, "the grain did admitted work");
        assert!(platform.consumed(&host).unwrap() > 0, "the meter drew down");

        // Re-witness the session (chain + budget + the durable-image bind).
        platform.verify(&host).expect("the session re-witnesses");

        // Bill period 0 (rent due at 1000): meter + settle a real conserving transfer.
        let ledger = TestConservingLedger::new();
        ledger.fund(&hex32(cid(9)), &hex32(cid(7)), 100_000);
        let settled = platform
            .bill_period(&host, 0, 1000, &ledger)
            .expect("meter + settle rent");
        assert_eq!(settled.amount, 100);
        assert_eq!(
            ledger.balance(&hex32(cid(9)), &hex32(cid(2))),
            100,
            "the provider was paid the rent"
        );

        // Miss period 1's rent → the grain is reaped → driving refuses.
        assert!(platform.reap_if_behind(&host, 1100).expect("audit"));
        let mut brain2 = fs_plan(&[("late.txt", "x")]);
        assert!(matches!(
            platform.drive(&host, "too late", &mut brain2),
            Err(AgentPlatformError::Lapsed)
        ));
    }

    /// **THE FOLD, end to end.** A rented grain's lifecycle IS a vat: it launches to
    /// `Running`, sleeps to `Sleeping`, wakes back to `Running` (the wake-from-lease),
    /// refuses every illegal move by the machine's own tooth, and a delinquent grain
    /// moves to `Lapsed` — from which it can never wake again.
    #[test]
    fn the_grain_lifecycle_is_a_vat_machine() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "vat.agents.dregg",
                "dga1_vic",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision the grain");

        // rent = open_vat + BringUp → the grain launches Running.
        assert_eq!(platform.grain_state(&host).unwrap(), VatState::Running);

        // sleep = Running → Sleeping (checkpoint-and-tear-down).
        assert_eq!(platform.sleep(&host).unwrap(), VatState::Sleeping);
        assert_eq!(platform.grain_state(&host).unwrap(), VatState::Sleeping);

        // Illegal by the machine's tooth: you cannot sleep an already-sleeping grain.
        assert!(matches!(
            platform.sleep(&host),
            Err(AgentPlatformError::Lifecycle(_))
        ));

        // wake = Sleeping → Running (the named wake-from-lease, delivered by the fold).
        assert_eq!(platform.wake(&host).unwrap(), VatState::Running);
        assert_eq!(platform.grain_state(&host).unwrap(), VatState::Running);

        // Illegal: you cannot wake a grain that is already up.
        assert!(matches!(
            platform.wake(&host),
            Err(AgentPlatformError::Lifecycle(_))
        ));

        // Miss the rent → the lease lapses AND the vat lifecycle mirrors it to Lapsed.
        assert!(platform.reap_if_behind(&host, 1100).expect("audit"));
        assert_eq!(platform.grain_state(&host).unwrap(), VatState::Lapsed);

        // A lapsed grain can never wake again (BringUp is illegal from Lapsed).
        assert!(matches!(
            platform.wake(&host),
            Err(AgentPlatformError::Lifecycle(_))
        ));
    }

    #[test]
    fn drive_audits_the_schedule_and_lapses_a_delinquent_grain() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "del.agents.dregg",
                "dga1_del",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");
        // The operator advances the clock past period 1's due block (1050) with no
        // rent ever paid — drive must AUDIT the schedule and lapse, not host free.
        platform.set_clock(1100);
        let mut brain = fs_plan(&[("x.txt", "y")]);
        assert!(matches!(
            platform.drive(&host, "go", &mut brain),
            Err(AgentPlatformError::Lapsed)
        ));
    }

    /// The platform clock is MONOTONE: a regression is ignored (block height never
    /// rewinds — a rewound clock would re-extend credit to a delinquent grain).
    #[test]
    fn the_platform_clock_never_rewinds() {
        let platform = AgentPlatform::new();
        assert_eq!(platform.set_clock(100), 100);
        assert_eq!(platform.set_clock(50), 100, "a clock regression is ignored");
        assert_eq!(platform.clock(), 100);
        assert_eq!(platform.set_clock(150), 150, "a genuine advance lands");
    }

    /// The platform-wide map lock is NOT held across a drive. A slow/stalled drive
    /// on grain A (here simulated by holding A's *tenant* lock, exactly what
    /// `drive_live` holds across its blocking provider round-trip) must not block a
    /// concurrent rent/drive/verify/bill on grain B — no head-of-line DoS.
    #[test]
    fn two_grains_can_be_driven_without_head_of_line_blocking() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        platform
            .rent(
                "a.agents.dregg",
                "dga1_a",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("rent A");
        platform
            .rent(
                "b.agents.dregg",
                "dga1_b",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("rent B");

        // Clone A's per-tenant handle under a brief map lock, then HOLD A's tenant
        // lock — simulating a live drive mid HTTP round-trip inside grain A.
        let a_arc = platform
            .tenants
            .lock()
            .expect("map lock")
            .get("a.agents.dregg")
            .cloned()
            .expect("A is hosted");
        let a_guard = a_arc.lock().expect("hold A's tenant lock");

        // With A's tenant lock held for the whole scope, grain B stays fully
        // operable. If any of these held the map lock across A's drive, this thread
        // would deadlock on the map lock and never join.
        std::thread::scope(|s| {
            let handle = s.spawn(|| {
                assert_eq!(
                    platform.owner_of("b.agents.dregg").as_deref(),
                    Some("dga1_b"),
                    "owner_of(B) resolves while A is held"
                );
                assert_eq!(platform.consumed("b.agents.dregg").unwrap(), 0);
                let mut brain = fs_plan(&[("b.txt", "hi")]);
                let report = platform
                    .drive("b.agents.dregg", "go", &mut brain)
                    .expect("drive B while A is held");
                assert!(report.admitted > 0, "B did admitted work");
                platform.verify("b.agents.dregg").expect("B re-witnesses");
            });
            handle
                .join()
                .expect("B operates without blocking on A's held tenant lock");
        });

        // A's tenant lock was reachable throughout via its own Arc; release it and
        // confirm A itself is still hosted + operable.
        drop(a_guard);
        assert_eq!(
            platform.owner_of("a.agents.dregg").as_deref(),
            Some("dga1_a")
        );
    }

    /// **R1 — the renter finality anchor, end-to-end over the platform.** A pinned
    /// grain: the renter supplies a nonce + pubkey at rent; drives commit turns; the
    /// renter fetches + countersigns a checkpoint and POSTs it back; the chain then
    /// extends; and a third party re-witnesses the attestation with the renter's
    /// pins — anti-rewrite + anti-truncation, trusting no host. Plus the store teeth:
    /// a wrong-key countersignature and a fabricated head_root are refused.
    #[test]
    fn r1_the_checkpoint_protocol_anchors_a_grain_end_to_end() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let renter_seed = [0x5au8; 32];
        let renter_pub = dregg_agent::receipt::ReceiptSigner::from_seed(renter_seed).public();
        let nonce = [0x11u8; 32];
        let host = platform
            .rent(
                "anchored.agents.dregg",
                "dga1_anchor",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                Some(RenterAnchor {
                    nonce,
                    pubkey: renter_pub,
                }),
            )
            .expect("provision a pinned grain");

        // Before any drive there is nothing to checkpoint.
        assert!(matches!(
            platform.checkpoint_offer(&host),
            Err(AgentPlatformError::Checkpoint(_))
        ));

        // Drive a goal → the grain commits turns.
        let mut brain = fs_plan(&[("a.txt", "1"), ("b.txt", "2")]);
        platform
            .drive(&host, "write", &mut brain)
            .expect("drive the grain");

        // The renter fetches, countersigns, and submits the checkpoint.
        let cp = platform
            .checkpoint_offer(&host)
            .expect("offer a checkpoint");
        assert!(cp.num_turns >= 1);
        let cs = grain_verify::countersign_checkpoint(renter_seed, cp);
        platform
            .submit_checkpoint(&host, cs)
            .expect("store the renter countersignature");

        // A WRONG-KEY countersignature (not the pinned renter key) is refused.
        let cp_again = platform.checkpoint_offer(&host).unwrap();
        let evil = grain_verify::countersign_checkpoint([0x99u8; 32], cp_again);
        assert!(matches!(
            platform.submit_checkpoint(&host, evil),
            Err(AgentPlatformError::Checkpoint(_))
        ));

        // A FABRICATED head_root under the RIGHT key is refused (does not match chain).
        let bogus = grain_verify::RenterCheckpoint {
            head_root: [0xEEu8; 32],
            num_turns: 1,
        };
        let cs_bogus = grain_verify::countersign_checkpoint(renter_seed, bogus);
        assert!(matches!(
            platform.submit_checkpoint(&host, cs_bogus),
            Err(AgentPlatformError::Checkpoint(_))
        ));

        // Drive more → the chain extends past the acknowledged checkpoint.
        let mut brain2 = fs_plan(&[("c.txt", "3")]);
        platform
            .drive(&host, "more", &mut brain2)
            .expect("drive more");

        // The attestation carries the genesis pin + the countersigned checkpoint; a
        // third party holding (attestation + renter pubkey + nonce) re-witnesses it.
        let att = platform.attest(&host).expect("attest");
        assert!(att.genesis.is_some(), "the genesis pin is exposed");
        assert!(
            att.checkpoint.is_some(),
            "the countersigned checkpoint is carried"
        );
        att.verify_for_renter(&renter_pub, &nonce)
            .expect("the renter/third-party anti-rewrite/anti-truncation check passes");

        // A grain with NO renter anchor pinned cannot accept a checkpoint (R1 off).
        let host2 = platform
            .rent(
                "bare.agents.dregg",
                "dga1_bare",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision a bare grain");
        let mut b3 = fs_plan(&[("d.txt", "4")]);
        platform.drive(&host2, "x", &mut b3).expect("drive");
        let cp3 = platform.checkpoint_offer(&host2).unwrap();
        let cs3 = grain_verify::countersign_checkpoint(renter_seed, cp3);
        assert!(matches!(
            platform.submit_checkpoint(&host2, cs3),
            Err(AgentPlatformError::Checkpoint(_))
        ));
    }

    /// **The durable image BINDS the session — both polarities.** After a drive,
    /// the lease's committed heap carries the chain tip / turn count / consumed /
    /// digest and `verify` re-checks them (positive). Tampering any of them in the
    /// durable image — or stamping a digest of a different mind — is caught as
    /// `ImageDiverged` (negative): the checkpoint is a verified binding, not a
    /// stamp nothing reads.
    #[test]
    fn the_durable_image_binds_the_session_and_a_tamper_is_caught() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "bound.agents.dregg",
                "dga1_bound",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");

        // Before any drive the image is genesis (step 0) — verify passes vacuously
        // on the image leg (nothing bound yet), receipts empty.
        platform.verify(&host).expect("a fresh grain verifies");

        let mut brain = fs_plan(&[("a.txt", "1"), ("b.txt", "2")]);
        platform.drive(&host, "write", &mut brain).expect("drive");

        // Positive: the image carries the real binding and verify re-checks it.
        {
            let arc = platform
                .tenants
                .lock()
                .unwrap()
                .get(&host)
                .cloned()
                .unwrap();
            let t = arc.lock().unwrap();
            let report = t.session.report();
            assert!(t.lease.step() > 0, "the cursor advanced");
            assert_eq!(
                t.lease.read_working(WK_NUM_TURNS),
                Some(field_from_u64(report.receipts.len() as u64)),
                "the committed turn count is the session's"
            );
            assert_eq!(
                t.lease.read_working(WK_CHAIN_TIP),
                Some(report.receipts.last().unwrap().receipt_hash().unwrap()),
                "the committed chain tip is the session's"
            );
        }
        platform.verify(&host).expect("the bound image verifies");

        // Negative 1: overwrite the committed chain tip (digest kept honest) —
        // the read-back bites.
        {
            let arc = platform
                .tenants
                .lock()
                .unwrap()
                .get(&host)
                .cloned()
                .unwrap();
            let mut t = arc.lock().unwrap();
            let digest = session_digest(&t.session.report());
            t.lease
                .checkpoint(digest, &[(WK_CHAIN_TIP, [0xEEu8; 32])])
                .expect("tamper the image");
        }
        assert!(
            matches!(
                platform.verify(&host),
                Err(AgentPlatformError::ImageDiverged(_))
            ),
            "a tampered chain tip in the durable image is refused"
        );

        // Heal it, then Negative 2: stamp a digest of a DIFFERENT mind.
        {
            let arc = platform
                .tenants
                .lock()
                .unwrap()
                .get(&host)
                .cloned()
                .unwrap();
            let mut t = arc.lock().unwrap();
            let tenant = &mut *t;
            let report = tenant.session.report();
            let digest = session_digest(&report);
            tenant
                .lease
                .checkpoint(digest, &session_binding(&report))
                .expect("heal the image");
        }
        platform
            .verify(&host)
            .expect("the healed image binds again");
        {
            let arc = platform
                .tenants
                .lock()
                .unwrap()
                .get(&host)
                .cloned()
                .unwrap();
            let mut t = arc.lock().unwrap();
            let tenant = &mut *t;
            let report = tenant.session.report();
            tenant
                .lease
                .checkpoint([0xABu8; 32], &session_binding(&report))
                .expect("stamp a foreign digest");
        }
        assert!(
            matches!(
                platform.verify(&host),
                Err(AgentPlatformError::ImageDiverged(_))
            ),
            "a digest of a different mind is refused"
        );
    }

    /// **R2 — receipts become views over committed kernel turns, both polarities.**
    /// A minted drive links every admitted receipt to a turn the minter committed,
    /// and `verify_r2` passes against the platform-recorded manifest. An UNMINTED
    /// drive fails `verify_r2` (unlinked receipts — the honest default is below
    /// R2). And an executor-style refusal (the minter's host-side caveat biting)
    /// admits NOTHING: no receipt, no budget draw.
    #[test]
    fn r2_minted_drives_verify_and_unminted_or_refused_do_not_inflate() {
        let wd = workdir();
        let platform = AgentPlatform::new();

        // ── minted: every admitted action rides a committed kernel turn ────────
        let minted_host = platform
            .rent(
                "r2.agents.dregg",
                "dga1_r2",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");
        let mut minter = SyntheticMinter::new();
        let mut brain = fs_plan(&[("m1.txt", "a"), ("m2.txt", "b")]);
        let report = platform
            .drive_minted(&minted_host, "write minted", &mut brain, &mut minter)
            .expect("minted drive");
        assert!(report.admitted > 0, "the minted grain did admitted work");
        let r2 = platform.verify_r2(&minted_host).expect("R2 verifies");
        assert_eq!(
            r2.linked as u64, report.admitted,
            "every admitted receipt is a view over a committed turn"
        );
        // A second minted drive extends the same manifest (it accumulates).
        let mut brain2 = fs_plan(&[("m3.txt", "c")]);
        platform
            .drive_minted(&minted_host, "more", &mut brain2, &mut minter)
            .expect("minted drive 2");
        let r2b = platform.verify_r2(&minted_host).expect("R2 still verifies");
        assert!(r2b.linked > r2.linked, "the manifest accumulated");

        // ── unminted: verify_r2 refuses (below R2 is not laundered as R2) ──────
        let bare_host = platform
            .rent(
                "r2bare.agents.dregg",
                "dga1_r2b",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");
        let mut brain3 = fs_plan(&[("u1.txt", "x")]);
        platform
            .drive(&bare_host, "write unminted", &mut brain3)
            .expect("drive");
        platform
            .verify(&bare_host)
            .expect("R0 tamper-evidence still holds");
        assert!(
            matches!(
                platform.verify_r2(&bare_host),
                Err(AgentPlatformError::Verify(_))
            ),
            "an unminted grain does not pass R2"
        );

        // ── refusal: the executor-style caveat biting admits NOTHING ───────────
        let refused_host = platform
            .rent(
                "r2ref.agents.dregg",
                "dga1_r2r",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");
        let mut refusing = SyntheticMinter::refusing_after(1);
        let mut brain4 = fs_plan(&[("r1.txt", "x"), ("r2.txt", "y"), ("r3.txt", "z")]);
        let refused_report = platform
            .drive_minted(&refused_host, "mostly refused", &mut brain4, &mut refusing)
            .expect("the drive itself completes");
        assert_eq!(
            refused_report.admitted, 1,
            "only the pre-refusal action admitted"
        );
        let r2r = platform
            .verify_r2(&refused_host)
            .expect("the admitted turn verifies");
        assert_eq!(r2r.linked, 1, "exactly the committed turn is linked");
    }

    /// A rented grain thinks LIVE: with `--features live-brain` and a provider key
    /// in env, drive_live has a real model reason→act→observe over the grain's
    /// granted tools, each tool-call crossing the cap gate. Ignored (needs a key +
    /// network); run on demand:
    /// `DREGG_LLM_API_KEY=… cargo test -p agent-platform --features live-brain -- --ignored`
    #[cfg(feature = "live-brain")]
    #[test]
    #[ignore]
    fn a_rented_grain_thinks_live() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "bob.agents.dregg",
                "dga1_bob",
                "fs",
                100_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision the grain");
        let report = platform
            .drive_live(
                &host,
                "Write a file called hello.txt containing the word dregg, then finish.",
                &["fs_write".to_string()],
            )
            .expect("the live model drives the grain");
        assert!(
            report.admitted > 0,
            "the live model took an admitted action"
        );
        platform
            .verify(&host)
            .expect("the live session re-witnesses");
    }
}
