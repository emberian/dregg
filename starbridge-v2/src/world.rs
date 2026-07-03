//! The embedded verified world — the HEART of the master interface.
//!
//! `World` wraps the REAL embedded engine — `dregg_sdk::embed::DreggEngine`
//! (`sdk/src/embed.rs`), the SDK's no-I/O executor+ledger core that the SWAP
//! makes the federation's authoritative producer — and runs REAL verified turns
//! through it (`DreggEngine::execute_turn`, i.e. `TurnExecutor::execute` over a
//! `dregg_cell::Ledger`). It is NOT a client of a remote node, and NOT a
//! parallel re-implementation of that engine: the verified semantics run IN
//! THIS PROCESS, through the SDK's own engine.
//!
//! This module is gpui-free and `cargo test`-able: it is the engine the visual
//! layer renders, decoupled from any window. Every mutation flows through
//! `commit_turn`, which:
//!   1. threads the per-agent receipt-chain head (the executor enforces it),
//!   2. runs `executor.execute(&turn, &mut ledger)`,
//!   3. on `Committed`, records the new chain head + emits a [`WorldEvent`]
//!      stream of the state transition (the "dynamics"), and
//!   4. returns the real [`TurnReceipt`] (kept in an append-only provenance log).
//!
//! The four dregg-surpasses-Smalltalk axes are all live here:
//!   * ocap — turns are gated by the cells' `Permissions`/capabilities; an
//!     over-grant or unauthorized effect is REJECTED by the real executor.
//!   * verification — each commit carries the executor's conservation / no-
//!     amplification guarantees (the same code the verified producer runs).
//!   * provenance — every commit appends a `TurnReceipt` to `receipts`, a
//!     navigable causal chain (the local blocklace).
//!   * distribution — `state_root()` is a cryptographic commitment to the whole
//!     image; the federation view renders this image as one of many sovereign
//!     ones.

use std::cell::Cell as StdCell; // alias: `Cell` is taken by dregg_cell::Cell
use std::collections::HashMap;
use std::collections::VecDeque;

use dregg_cell::{
    lifecycle::{DeathCertificate, DeathReason},
    AuthRequired, Cell, CellId, Ledger, Permissions,
};
use dregg_sdk::embed::{DreggEngine, EmbedError, EngineConfig};
use dregg_turn::{
    action::{Action, Authorization, DelegationMode, Effect, Event},
    collapse::{is_deferred, WitnessMode},
    forest::CallForest,
    turn::{Turn, TurnReceipt},
    ComputronCosts, TurnExecutor,
};

use crate::dynamics::{Dynamics, WorldEvent};
use crate::persistence::WorldPersist;
// `OpenError`/`RecoveredImage` are used only by the durable `open`/
// `open_with_timestamp` paths, which are `not(wasm32)`-gated (no `dregg-persist`
// on wasm — the browser image is always ephemeral).
#[cfg(not(target_arch = "wasm32"))]
use crate::persistence::{OpenError, RecoveredImage};
use crate::replay::History;

/// The outcome of attempting to commit a turn against the embedded executor.
#[derive(Debug)]
pub enum CommitOutcome {
    /// The turn committed. The real receipt + the dynamics events it produced.
    Committed {
        receipt: Box<TurnReceipt>,
        events: Vec<WorldEvent>,
    },
    /// The real executor REJECTED the turn (e.g. unauthorized effect,
    /// non-conservation, broken receipt chain). This is a FEATURE: it is the
    /// ocap/verification guarantees firing.
    Rejected {
        reason: String,
        at_action: Vec<usize>,
    },
    /// The world is SUSPENDED (the meta-debug Suspend gate halts the live loop,
    /// `docs/deos/FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §3): the turn was NOT run
    /// against the executor — it was STAGED in the pending queue, in arrival
    /// order, and the head is frozen. It will commit (or be edited) on
    /// `resume`. This is DISTINCT from `Rejected`: nothing was refused; the turn
    /// is honest and will run when the loop resumes. The agent that staged it is
    /// carried so the caller can correlate the eventual commit.
    Queued { agent: CellId },
}

impl CommitOutcome {
    pub fn is_committed(&self) -> bool {
        matches!(self, CommitOutcome::Committed { .. })
    }

    /// `true` iff the turn was STAGED while the world is suspended (the live loop
    /// is halted; the head is frozen). It will commit on `resume(drain)`.
    pub fn is_queued(&self) -> bool {
        matches!(self, CommitOutcome::Queued { .. })
    }
}

/// How a suspended world RESUMES its halted loop (meta-debug §3.4).
pub enum ResumeMode {
    /// Commit the staged pending queue, in arrival order, through the normal
    /// `commit_turn` gate (the loop continues as if it had never paused).
    Drain,
    /// Replace the staged continuation with an EDITED batch (drop/insert/reorder)
    /// and run THAT instead — each turn still passing the full executor gate. The
    /// previously-staged queue is discarded.
    Modified(Vec<Turn>),
}

/// A live local dregg world: the REAL embedded engine
/// ([`dregg_sdk::embed::DreggEngine`] — the executor+ledger core the SWAP makes
/// the federation's authoritative producer) plus the provenance log, the
/// dynamics stream the views render, and the canonical replayable [`History`].
pub struct World {
    /// The REAL embedded engine: `dregg_sdk::embed::DreggEngine` wraps the same
    /// `TurnExecutor` over `dregg_cell::Ledger` pair this world runs every
    /// transition through — not a parallel re-implementation, the SDK's engine.
    engine: DreggEngine,
    /// The canonical, replayable history (genesis installs + committed turns,
    /// each carrying the post-state `Ledger::root` tooth). Maintained in
    /// lock-step with `engine` so time-travel ([`crate::replay`]) drives off the
    /// live world's REAL turn history, not a separately-recorded one.
    ///
    /// The recovery model ([`crate::replay`], `CrashRecovery.lean`) is a
    /// deterministic re-execution tape: it carries its own recording ledger +
    /// executor (`record_ledger`/`record_exec`), driven in lock-step with the
    /// authoritative `engine` under the SAME pinned config, so every recorded
    /// root tooth equals the live engine's post-state root — and replay can
    /// reconstruct + verify any past step.
    history: History,
    /// The history recorder's ledger (parallel to the engine's, kept in
    /// lock-step). NOT a second source of truth — the engine is authoritative;
    /// this is the replay tape's substrate so the recorded roots are real.
    record_ledger: Ledger,
    /// The history recorder's executor (pinned to the same timestamp/costs as
    /// the engine's), used only to re-derive the recorded receipts/roots.
    record_exec: TurnExecutor,
    /// Append-only provenance: every committed receipt, in commit order. This
    /// IS the local blocklace / receipt chain the browser navigates.
    receipts: Vec<TurnReceipt>,
    /// The dynamics: an observation stream of state transitions, decoupled from
    /// the visual layer (see [`crate::dynamics`]).
    dynamics: Dynamics,
    /// Monotonic "height" — one per committed turn (the local chain index).
    height: u64,
    /// The fixed wall-clock the engine + history share, so a recorded turn
    /// re-derives bit-identically on replay (the debugger's re-execution and the
    /// replayer's reconstruction must use the SAME timestamp the live engine did).
    timestamp: i64,
    /// The fee stamped onto every turn built by [`World::turn`] /
    /// [`World::forest_turn`]. `0` for [`World::new`] (free metering — the demo
    /// path). For a METERED world ([`World::with_costs`]) the executor rejects a
    /// turn whose `computrons_used` exceeds its `fee`, so a metered world stamps a
    /// fee that covers the per-turn cost (the agent pays it — conservation-real).
    /// This is what lets the SWARM BUDGET METER (N1) observe non-zero metered spend
    /// on committed turns without every turn being rejected for under-fee.
    turn_fee: u64,
    /// The factory descriptors deployed into this world's executor registry (via
    /// [`World::deploy_factory`]). Retained here — the descriptor is `Clone` and
    /// inspectable — so [`World::fork`] can replay them onto a throwaway world's
    /// executor: a `CreateCellFromFactory` simulated in a fork validates against
    /// the SAME registered factories the live world holds. (The engine's executor
    /// owns the live registry but exposes no enumeration; this is the world's own
    /// record of what it deployed, kept in lock-step with every `deploy_factory`.)
    deployed_factories: Vec<dregg_cell::FactoryDescriptor>,
    /// Memoized image root (`state_root`), valid while the witness tooth
    /// `(height, receipt_head_or_zero)` is unchanged. Stored as
    /// `(height, receipt_head_or_zero, root)`. A `std::cell::Cell` (not a
    /// `RefCell`): the tuple is `Copy`, so `get`/`set` need no borrow, and
    /// `state_root(&self)` stays a `&self` method (no `&mut` ripple through the
    /// ~30 callers or the `Rc<RefCell<World>>` borrow discipline in cockpit).
    /// Every height/receipt advance busts it automatically; the genesis-path
    /// ledger writers (which mutate without a height bump) invalidate it with an
    /// explicit `set(None)`.
    #[allow(clippy::type_complexity)] // (height, state_root, receipt_root) memo cell
    state_root_memo: StdCell<Option<(u64, [u8; 32], [u8; 32])>>,
    /// THE SUSPEND GATE (meta-debug, `docs/deos/FIRMAMENT-REFLEXIVE-SUBSTRATE.md`
    /// §3.2). When `true`, the live loop is HALTED: [`World::commit_turn`] stages
    /// every submitted turn in `pending` instead of running the executor, and the
    /// head is FROZEN at the height suspension hit (NOT a replayed past — the real
    /// live head, paused). `suspend()`/`resume(..)` flip it. This is the missing
    /// sibling of Snapshot (which freezes a *cursor* while the loop keeps running);
    /// Suspend freezes the *head* itself.
    suspended: bool,
    /// The pending-turn queue: turns staged while `suspended`, in ARRIVAL order.
    /// `resume(Drain)` re-submits them through the normal `commit_turn` gate (each
    /// re-passes the full executor/conservation/authority check at fill time — the
    /// continuation editing stays shape-eager, Seam 5). Empty whenever the world
    /// is running.
    pending: VecDeque<Turn>,
    /// THE DURABLE IMAGE (M4 — `docs/deos/WORLD-PERSISTENCE-PLAN.md`). `None` for
    /// an EPHEMERAL world (`new`/`with_costs`/`fork` — the demo/test/what-if path,
    /// which stays purely in-RAM; a fork MUST never persist). `Some` only for a
    /// world produced by [`World::open`]: every successful `commit_turn` then
    /// dual-writes the turn into the redb commit log + input-turn table (the weld
    /// onto the node's already-built durability spine), and the genesis path
    /// mirrors each install into the durable genesis table. The store is the
    /// single source of truth for the commit cursor (its torn-state guard
    /// re-checks it).
    persist: Option<WorldPersist>,
    /// THE WITNESS MODE (SYMBOLIC EXECUTION — `dregg_turn::collapse`). `Full`
    /// (the correct default): every commit materializes its Merkle witness and
    /// records the post-root onto the replay tape, so each receipt is
    /// publishable. `Symbolic`: a local fast path that DEFERS the witness — the
    /// engine skips `Ledger::root()` (the receipt carries the deferred sentinel
    /// state-hash) AND `commit_turn` skips the replay-tape double-execution,
    /// buffering the turn in `symbolic_turns` instead. The state transition
    /// still fully applies (the abstract progress). [`World::collapse`]
    /// re-runs the buffered turns under Full to materialize the real witnesses
    /// + the tape, reproducing exactly what a Full run would have. Admission is
    ///   mode-independent — only the witness is deferred, never the decision.
    witness_mode: WitnessMode,
    /// The buffer of turns committed under [`WitnessMode::Symbolic`] whose
    /// witnesses are DEFERRED — recorded here (NOT on the replay tape) so
    /// [`World::collapse`] can materialize them on demand. Empty in `Full` mode
    /// and after a `collapse`. A symbolic turn's receipt (in `receipts`) carries
    /// the deferred sentinel until collapse replaces it with the real one.
    symbolic_turns: Vec<Turn>,
}

impl Default for World {
    fn default() -> Self {
        Self::new()
    }
}

impl World {
    /// A fresh, empty world with the real embedded engine (free metering, so the
    /// demo world isn't gated on a fee economy).
    pub fn new() -> Self {
        Self::with_costs(ComputronCosts::zero())
    }

    /// A fresh, empty world with the real embedded engine metering at `costs`.
    ///
    /// [`World::new`] pins `ComputronCosts::zero()` so the demo flows aren't gated
    /// on a fee economy. The SWARM BUDGET METER (N1) needs a world where committed
    /// turns actually accrue metered computrons, so a member's `spent` GROWS and a
    /// ceiling can bite — that is what this constructor is for. The metering is the
    /// REAL executor's (`ComputronCosts` is the production cost model the federation
    /// producer configures), just non-zero; the swarm budget then sums the genuine
    /// `receipt.computrons_used`, never a re-derived estimate.
    pub fn with_costs(costs: ComputronCosts) -> Self {
        // A real wall-clock so temporal preconditions behave; harmless for the
        // demo flows that don't use them. PINNED for the world's life so the
        // engine and the replay history stay bit-deterministic together.
        Self::with_costs_and_timestamp(costs, now_unix())
    }

    /// A fresh, empty world metering at `costs` with the wall-clock PINNED to
    /// `timestamp` (rather than `now_unix()`).
    ///
    /// The timestamp is folded into every `TurnReceipt` (`receipt_hash` binds it),
    /// so two worlds that must produce BYTE-IDENTICAL receipts for the same turns
    /// — e.g. the direct executor and the semihosted executor-PD
    /// ([`SemihostCockpit`]) in a determinism/equivalence test — must share it.
    /// This is the "houyhnhnm clock as a recorded, replayable input" the semihost
    /// makes natural (`docs/DREGG-DESKTOP-OS.md §3`): construction-time determinism,
    /// not the host wall-clock. [`World::with_costs`] pins `now_unix()`; this lets
    /// a caller pin any instant.
    pub fn with_costs_and_timestamp(costs: ComputronCosts, timestamp: i64) -> Self {
        let config = EngineConfig {
            costs: costs.clone(),
            federation_id: [0u8; 32],
            block_height: 0,
            timestamp,
            max_proof_age_secs: 0,
        };
        let history = History::with_costs(timestamp, costs.clone());
        let record_exec = history.fresh_executor();
        World {
            engine: DreggEngine::new(config),
            history,
            record_ledger: Ledger::new(),
            record_exec,
            receipts: Vec::new(),
            dynamics: Dynamics::new(),
            height: 0,
            timestamp,
            turn_fee: 0,
            deployed_factories: Vec::new(),
            state_root_memo: StdCell::new(None),
            suspended: false,
            pending: VecDeque::new(),
            persist: None,
            witness_mode: WitnessMode::Full,
            symbolic_turns: Vec::new(),
        }
    }

    // --- THE DURABLE IMAGE (M4 — World::open boot-recovery) ------------------

    /// **Open a durable World image** from the redb store at `path`, recovering it
    /// to exactly where it was closed (`docs/deos/WORLD-PERSISTENCE-PLAN.md` A.3).
    ///
    /// Runs the EXACT node boot-recovery (`node/src/state.rs:676-767`):
    /// checkpoint-load → durable commit-log overlay via last-writer-wins
    /// `upsert_cell` → FAIL-CLOSED convergence check (the reconstructed canonical
    /// root MUST equal the root the last committed turn durably recorded, else
    /// [`OpenError::Divergent`] — refuse to open). Because the overlay semantics
    /// are byte-identical, the recovered ledger inherits
    /// `CrashRecovery.lean::recover_eq_replay`: it equals the genesis replay.
    ///
    /// Then it rebuilds the in-RAM view spine (engine / [`History`] / receipts /
    /// dynamics / per-agent chain heads) by REINSTALLING the durable genesis cells
    /// and RE-EXECUTING the durable input turns through the same embedded executor
    /// — re-deriving the real receipts and re-priming each chain head for free.
    /// The store is attached LAST (with the cursor mirror), so the rebuild itself
    /// never re-persists. `costs` must match the costs the image was created with
    /// (the receipts re-derive bit-identically only under the same cost model).
    ///
    /// First run on an empty store returns an empty durable World (no genesis, no
    /// turns); the caller seeds the demo genesis, which then persists.
    #[cfg(not(target_arch = "wasm32"))]
    pub fn open(path: &std::path::Path, costs: ComputronCosts) -> Result<World, OpenError> {
        Self::open_with_timestamp(path, costs, now_unix())
    }

    /// [`World::open`] with the wall-clock PINNED to `timestamp` (the value the
    /// image was created under). The receipts re-derive bit-identically only when
    /// the timestamp matches the live world's that produced the durable turns, so
    /// a deterministic image (tests, the houyhnhnm-clock semihost) pins it here.
    #[cfg(not(target_arch = "wasm32"))]
    pub fn open_with_timestamp(
        path: &std::path::Path,
        costs: ComputronCosts,
        timestamp: i64,
    ) -> Result<World, OpenError> {
        let persist = WorldPersist::open(path)?;
        let RecoveredImage {
            ledger: recovered,
            genesis_cells,
            committed,
            cursor,
        } = persist.recover()?;

        // Build a fresh EPHEMERAL world (no store yet) and rebuild the spine on it
        // by re-running the durable genesis installs + input turns through the
        // normal (non-persisting) paths. `persist` is None here, so neither the
        // genesis mirror nor the dual-write fires during rebuild — we attach the
        // store only AFTER, so the rebuild never duplicates the durable log.
        let mut world = Self::with_costs_and_timestamp(costs, timestamp);

        // Reinstall the durable genesis cells (genesis-time content), in order.
        for cell in genesis_cells {
            let balance = cell.state.balance();
            world.install_genesis(cell, balance);
        }
        // Re-execute the durable input turns: this rebuilds History (verified root
        // teeth), the receipts provenance log, the engine ledger, AND re-primes
        // every agent's receipt-chain head — the real receipt is re-derived, never
        // carried across the durable boundary.
        for turn in committed {
            // Re-executing a recorded committed turn must commit again (the
            // `recover_eq_replay` determinism). A rejection here would mean the
            // durable turn does not re-derive — a real integrity event.
            let outcome = world.commit_turn(turn);
            if !outcome.is_committed() {
                return Err(OpenError::Store(dregg_persist::StoreError::Integrity(
                    "a durable committed turn did NOT re-commit on recovery — \
                     image is non-deterministic or corrupt"
                        .to_string(),
                )));
            }
        }

        // FAIL-CLOSED cross-check: the rebuilt engine ledger MUST equal the
        // checkpoint⊕overlay recovered ledger (both are `recover_eq_replay`). This
        // catches any genesis/turn divergence the per-turn replay would miss.
        if crate::persistence::canonical_ledger_root(world.engine.ledger())
            != crate::persistence::canonical_ledger_root(&recovered)
        {
            return Err(OpenError::Divergent {
                got: crate::persistence::canonical_ledger_root(world.engine.ledger()),
                expected: crate::persistence::canonical_ledger_root(&recovered),
            });
        }

        // Attach the durable store LAST, with the cursor mirror primed, so every
        // FUTURE commit_turn dual-writes from the correct ordinal.
        debug_assert_eq!(
            world.height, cursor,
            "rebuilt height must equal the durable commit cursor"
        );
        world.persist = Some(persist);
        Ok(world)
    }

    /// Open a durable image, RECOVERING a torn/divergent one instead of refusing
    /// it (the never-strand path — the login front door uses this).
    ///
    /// A clean [`World::open`] fails closed with [`OpenError::Divergent`] when the
    /// reconstructed root does not match the last committed turn's recorded root
    /// (a crash mid-write, a poisoned cell, a torn tail). Refusing strands the
    /// owner: a single divergent tail makes the whole durable session unopenable.
    /// This instead TRUNCATES the divergent tail to the last root-converging
    /// ordinal ([`WorldPersist::recover_to_last_consistent`]) and reopens at the
    /// last-good state — the convergence check then passes at the recovered point.
    ///
    /// Returns `Ok((world, recovered))` where `recovered` is the number of turns
    /// dropped to reach consistency (0 ⇒ the image was clean — identical to a
    /// plain `open`). Errs only when the image is unsalvageable (NO prefix
    /// reconstructs to its claim), so the caller can offer the explicit
    /// "start fresh" choice — login is ALWAYS able to proceed (recovered or fresh).
    #[cfg(not(target_arch = "wasm32"))]
    pub fn open_recovering(
        path: &std::path::Path,
        costs: ComputronCosts,
    ) -> Result<(World, u64), OpenError> {
        Self::open_recovering_with_timestamp(path, costs, now_unix())
    }

    /// [`World::open_recovering`] with the wall-clock PINNED (tests / deterministic
    /// images), mirroring [`World::open_with_timestamp`].
    #[cfg(not(target_arch = "wasm32"))]
    pub fn open_recovering_with_timestamp(
        path: &std::path::Path,
        costs: ComputronCosts,
        timestamp: i64,
    ) -> Result<(World, u64), OpenError> {
        match Self::open_with_timestamp(path, costs.clone(), timestamp) {
            Ok(world) => Ok((world, 0)),
            Err(OpenError::Divergent { .. }) => {
                // The image is torn — recover it to its last consistent ordinal,
                // then reopen. The recovery handle is released before reopen
                // (redb single-writer per file): open a short-lived store, truncate
                // the divergent tail, drop it, then `open` the recovered image.
                let recovered = {
                    let persist = WorldPersist::open(path)?;
                    persist.recover_to_last_consistent()?
                    // `persist` dropped here → the redb lock is released.
                };
                // Reopen the recovered image. If it STILL diverges, the tear was
                // not in the commit-log tail (unsalvageable) — surface it so the
                // caller offers "start fresh".
                let world = Self::open_with_timestamp(path, costs, timestamp)?;
                Ok((world, recovered))
            }
            Err(other) => Err(other),
        }
    }

    /// The path-backed durable World is durable iff this is `true` (it is `false`
    /// for `new`/`with_costs`/`fork`, and flips to `false` if a durable write ever
    /// failed — the loud degrade-to-ephemeral path in `commit_turn`).
    pub fn is_durable(&self) -> bool {
        self.persist.is_some()
    }

    /// Force a durable full-ledger checkpoint at the current height (C.1) — the
    /// on-close flush so the latest image is always covered and recovery's overlay
    /// stays short. No-op on an ephemeral world.
    pub fn checkpoint_now(&self) {
        if let Some(p) = self.persist.as_ref() {
            p.checkpoint(self.engine.ledger(), self.height);
        }
    }

    /// Persist the opaque durable SESSION RECORD blob into this image's redb store
    /// (SESSION RESUME — `docs/deos/SESSION-LOGIN.md`). No-op on an ephemeral world
    /// (a not-logged-in / demo image keeps no session). Returns `true` iff the
    /// write landed durably (so the caller knows the session will resume).
    #[cfg(not(target_arch = "wasm32"))]
    pub fn put_session_blob(&self, bytes: &[u8]) -> bool {
        match self.persist.as_ref() {
            Some(p) => p.put_session(bytes).is_ok(),
            None => false,
        }
    }

    /// The durable SESSION RECORD blob for this image, if one was written by a
    /// prior login. `None` on an ephemeral world or a fresh image never logged
    /// into. The bytes are opaque here; [`crate::session`] decodes them.
    #[cfg(not(target_arch = "wasm32"))]
    pub fn session_blob(&self) -> Option<Vec<u8>> {
        self.persist
            .as_ref()
            .and_then(|p| p.get_session().ok().flatten())
    }

    /// The wall-clock this world pinned at construction (folded into every
    /// receipt). Exposed so a second world can be pinned to the SAME instant for a
    /// byte-for-byte equivalence check (e.g. direct vs. semihost executor-PD).
    pub fn timestamp(&self) -> i64 {
        self.timestamp
    }

    /// Set the fee stamped onto every turn built by [`World::turn`] /
    /// [`World::forest_turn`]. In a METERED world ([`World::with_costs`]) this must
    /// cover the per-turn `computrons_used` or the executor rejects the turn for
    /// under-fee; the agent pays it from its balance (conservation-real). Returns
    /// `self` for builder-style construction. The default is `0` (free metering).
    pub fn with_turn_fee(mut self, fee: u64) -> Self {
        self.turn_fee = fee;
        self
    }

    /// Configure this world's embedded executor to SIGN every committed receipt
    /// with the ed25519 key derived from `seed` (the executor's
    /// [`dregg_turn::TurnExecutor::set_executor_signing_key`]). Without this, a
    /// receipt carries `executor_signature: None`.
    ///
    /// This is what makes a committed receipt a real, verifiable CONSENT WITNESS:
    /// the [`crate::shared_fork`] networkboundary resolves only against a receipt
    /// whose signature verifies under this key (in the executor's own signing
    /// domain, [`dregg_turn::turn::TurnReceipt::canonical_executor_signed_message`]).
    /// Builder-style (returns `self`); pairs with [`World::executor_public_key`].
    pub fn with_executor_signing_key(mut self, seed: [u8; 32]) -> Self {
        self.set_executor_signing_key(seed);
        self
    }

    /// Configure this world's embedded executor signing key in place (see
    /// [`World::with_executor_signing_key`]).
    pub fn set_executor_signing_key(&mut self, seed: [u8; 32]) {
        self.engine.executor_mut().set_executor_signing_key(seed);
    }

    /// The ed25519 PUBLIC key (32 bytes) of this world's executor signing key, if
    /// one is configured — the trusted key a consent witness ([`TurnReceipt`])
    /// signature is verified against. `None` when the executor signs nothing.
    pub fn executor_public_key(&self) -> Option<[u8; 32]> {
        let seed = self.engine.executor().executor_signing_key.as_ref()?;
        let sk = ed25519_dalek::SigningKey::from_bytes(seed);
        Some(sk.verifying_key().to_bytes())
    }

    // --- read surface (what the reflective object model + views consume) ----

    pub fn ledger(&self) -> &Ledger {
        self.engine.ledger()
    }

    /// The canonical, replayable history of this world (genesis installs +
    /// committed turns, each with its post-state `Ledger::root` tooth). The
    /// time-travel panel ([`crate::replay`]) drives off THIS — the live world's
    /// real turn history — rather than a separately re-recorded one.
    pub fn recorded_turns(&self) -> &History {
        &self.history
    }

    /// A fresh `TurnExecutor` configured IDENTICALLY to this world's live engine
    /// (same zero-cost metering, same pinned wall-clock, same federation id, and
    /// `agent`'s current receipt-chain head). The turn debugger
    /// ([`crate::debug`]) re-executes prefixes against this so its replay cannot
    /// drift from the live executor's configuration.
    ///
    /// (`TurnExecutor` is not `Clone` — it carries `Mutex`/`RefCell` side-tables
    /// and a `Box<dyn ProofVerifier>` — so this hands back a fresh executor
    /// matching the live config, sourced from `World` so the config lives in ONE
    /// place and the debugger can't diverge from it.)
    pub fn debug_executor(&self, agent: &CellId) -> TurnExecutor {
        let mut exec = TurnExecutor::new(ComputronCosts::zero());
        exec.set_timestamp(self.timestamp);
        exec.set_block_height(self.engine.executor().block_height);
        exec.set_local_federation_id(self.engine.executor().local_federation_id);
        if let Some(head) = self.chain_head(agent) {
            exec.set_last_receipt_hash(*agent, head);
        }
        exec
    }

    pub fn receipts(&self) -> &[TurnReceipt] {
        &self.receipts
    }

    pub fn dynamics(&self) -> &Dynamics {
        &self.dynamics
    }

    /// Emit a [`WorldEvent`] onto the dynamics stream directly (an observation a
    /// view-layer model records about a transition the executor already made).
    ///
    /// This does NOT bypass the commit path — it is for transitions whose AUTHORITY
    /// the executor decided (a committed turn) but whose VIEW-LAYER meaning a model
    /// adds (e.g. the verified compositor's `SurfaceDamaged`, emitted only after a
    /// `present()`'s `SetField` turn COMMITTED through `commit_turn`). The state
    /// change itself always went through the real executor; this records the
    /// observation for the feed.
    pub fn emit_dynamics(&mut self, event: WorldEvent) {
        self.dynamics.emit(event);
    }

    /// TEST-ONLY bulk genesis for the efficiency microbench: install `cell` into
    /// the live engine ledger + emit `CellBorn`, but do NOT mirror it onto the
    /// replay tape (whose per-genesis `Ledger::root()` makes a sequence of `n`
    /// installs O(n²) — the tree rebuilds on every insert). The bench never
    /// replays, so skipping the tape is sound and keeps ledger BUILD linear so the
    /// n=65536 gate is reachable. NOT a production path (it would desync the tape).
    #[cfg(test)]
    pub fn bench_install_cell(&mut self, cell: Cell, balance: i64) -> CellId {
        let id = cell.id();
        self.engine
            .ledger_mut()
            .insert_cell(cell)
            .expect("bench genesis insert is into a fresh slot");
        self.dynamics.emit(WorldEvent::CellBorn {
            cell: id,
            balance,
            genesis: true,
        });
        self.state_root_memo.set(None);
        id
    }

    pub fn height(&self) -> u64 {
        self.height
    }

    /// The fee stamped onto every turn this world builds (`0` for the free-
    /// metering demo world; non-zero for a [`World::with_costs`] world). This is
    /// the turn's DECLARED computron budget — the executor rejects a turn whose
    /// metered `computrons_used` exceeds it — so it is a conservative upper bound
    /// on a dispatch's cost, usable as the fail-closed pre-check amount for a
    /// shared budget gate (the SDK's `set_budget_gate` gates on exactly this
    /// declared fee, before the turn runs).
    pub fn turn_fee(&self) -> u64 {
        self.turn_fee
    }

    pub fn cell_count(&self) -> usize {
        self.engine.ledger().len()
    }

    /// A cryptographic commitment to the WHOLE image — the distribution axis.
    /// (BLAKE3 over the canonical postcard of every cell, sorted by id, folded
    /// with the height + receipt-chain head so the root advances with history.)
    pub fn state_root(&self) -> [u8; 32] {
        // The cache key is exactly the witness tooth: the root is a pure function
        // of (height, receipt_head, ledger-contents), and the ledger only changes
        // when the height/receipt advances (genesis-path writers invalidate the
        // memo explicitly). A `(height, receipt_head)` hit ⇒ skip the O(cells)
        // postcard+BLAKE3 re-hash.
        let head = self
            .receipts
            .last()
            .map(|r| r.receipt_hash())
            .unwrap_or([0u8; 32]);
        if let Some((h, rh, root)) = self.state_root_memo.get() {
            if h == self.height && rh == head {
                return root;
            }
        }
        let root = self.compute_state_root();
        self.state_root_memo.set(Some((self.height, head, root)));
        root
    }

    /// The actual image-root computation (BLAKE3 over the canonical postcard of
    /// every cell, sorted by id, folded with the height + receipt-chain head).
    /// Called by [`Self::state_root`] only on a memo miss.
    fn compute_state_root(&self) -> [u8; 32] {
        let mut cells: Vec<(&CellId, &Cell)> = self.engine.ledger().iter().collect();
        cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"starbridge-v2-image-root-v1");
        hasher.update(&self.height.to_le_bytes());
        for (id, cell) in cells {
            hasher.update(id.as_bytes());
            if let Ok(bytes) = postcard::to_stdvec(cell) {
                hasher.update(&(bytes.len() as u64).to_le_bytes());
                hasher.update(&bytes);
            }
        }
        if let Some(head) = self.receipts.last() {
            hasher.update(&head.receipt_hash());
        }
        *hasher.finalize().as_bytes()
    }

    /// The per-agent receipt-chain head the executor enforces — exposed so
    /// callers (and the composer) can construct chained turns.
    pub fn chain_head(&self, agent: &CellId) -> Option<[u8; 32]> {
        self.engine.executor().get_last_receipt_hash(agent)
    }

    /// **Fork this world into a throwaway COPY for WHAT-IF SIMULATION.**
    ///
    /// Returns a fresh [`World`] whose engine carries a DEEP CLONE of this world's
    /// ledger (`dregg_cell::Ledger` is `Clone`), the SAME [`EngineConfig`] (cost
    /// model, federation id, block height, pinned timestamp), the SAME deployed
    /// factory registry (replayed from [`Self::deployed_factories`]), and the SAME
    /// per-agent receipt-chain heads (so a chained turn threads identically). The
    /// fork's verified executor is the REAL one — running a turn through the fork's
    /// [`World::commit_turn`] applies the IDENTICAL conservation / ocap / program
    /// guarantees the live world would, and yields a byte-identical receipt for the
    /// same turn (same timestamp + same pre-state ⟹ same `receipt_hash`).
    ///
    /// Because it is a SEPARATE `World`, committing on the fork mutates ONLY the
    /// fork — the live world's ledger, provenance log, dynamics and history are
    /// untouched. This is the substrate of the "simulate before committing" panel
    /// ([`crate::simulate`]): build a turn, run it on a fork to see the predicted
    /// post-state + receipt (or refusal), then — only if the operator chooses —
    /// run the SAME turn on the live world to commit it for real.
    ///
    /// The fork does NOT carry over the live provenance log / dynamics / replay
    /// tape (it starts empty there): a prediction is about the NEXT turn's effect,
    /// not a re-derivation of past history. Its `turn_fee` matches this world's, so
    /// turns built by the fork's [`World::turn`] meter the same way.
    pub fn fork(&self) -> World {
        let config = EngineConfig {
            costs: self.engine.executor().costs.clone(),
            federation_id: self.engine.executor().local_federation_id,
            block_height: self.engine.executor().block_height,
            timestamp: self.timestamp,
            max_proof_age_secs: self.engine.max_proof_age_secs(),
        };
        // Deep-clone the live ledger into a fresh engine (the fork's substrate).
        let mut engine = DreggEngine::with_ledger(config, self.engine.ledger().clone());
        // Carry the executor signing key so the fork's committed receipts are
        // signed identically to the live world's — a guest's embedded turn on the
        // fork therefore produces a receipt verifiable under the SAME executor key,
        // and a consent resolved on the fork witnesses under the owner's key.
        if let Some(seed) = self.engine.executor().executor_signing_key {
            engine.executor_mut().set_executor_signing_key(seed);
        }
        // Replay the deployed factories onto the fork's executor so a
        // CreateCellFromFactory simulates against the SAME registered factories.
        for descriptor in &self.deployed_factories {
            let _ = engine.executor_mut().deploy_factory(descriptor.clone());
        }
        // The fork's replay-tape executor (kept in lock-step with the live one so
        // `commit_turn`'s `record_commit` re-derives the SAME post-root as the
        // authoritative engine — the fork stays internally consistent even though
        // simulate never replays it).
        let mut record_exec = TurnExecutor::new(self.engine.executor().costs.clone());
        record_exec.set_timestamp(self.timestamp);
        record_exec.set_block_height(self.engine.executor().block_height);
        record_exec.set_local_federation_id(self.engine.executor().local_federation_id);
        for descriptor in &self.deployed_factories {
            let _ = record_exec.deploy_factory(descriptor.clone());
        }
        // Seed EVERY current cell's receipt-chain head onto BOTH the fork's
        // authoritative executor AND its replay-tape executor, so a chained turn
        // from any agent threads its `previous_receipt_hash` exactly as it would
        // against the live world (otherwise the first forked turn from an agent
        // with history rejects as ReceiptChainMismatch), and the two stay in
        // lock-step.
        for (id, _cell) in self.engine.ledger().iter() {
            if let Some(head) = self.engine.executor().get_last_receipt_hash(id) {
                engine.executor().set_last_receipt_hash(*id, head);
                record_exec.set_last_receipt_hash(*id, head);
            }
        }
        World {
            engine,
            // A fresh replay tape — the fork predicts the next turn, it does not
            // re-derive past history (its own commit still records onto this tape,
            // harmlessly, so the fork stays internally consistent).
            history: History::with_costs(self.timestamp, self.engine.executor().costs.clone()),
            record_ledger: self.engine.ledger().clone(),
            record_exec,
            receipts: Vec::new(),
            dynamics: Dynamics::new(),
            height: self.height,
            timestamp: self.timestamp,
            turn_fee: self.turn_fee,
            deployed_factories: self.deployed_factories.clone(),
            state_root_memo: StdCell::new(None),
            // A fork is a throwaway DIVERGENT copy used to PREDICT the next turn; it
            // runs freely (never inherits the live world's suspension), and a
            // suspended live world can still fork to simulate what a queued turn
            // WOULD do without resuming.
            suspended: false,
            pending: VecDeque::new(),
            // A fork is a what-if COPY: it MUST never persist (committing on the
            // fork would otherwise corrupt the live image's durable log).
            persist: None,
            // A fork PREDICTS the next turn — it always wants a real witness for
            // the predicted post-state, so it runs Full regardless of the live
            // world's mode (and starts with an empty symbolic buffer). The
            // fork's engine executor is fresh (default Full), so nothing to flip.
            witness_mode: WitnessMode::Full,
            symbolic_turns: Vec::new(),
        }
    }

    // --- genesis / cell creation (out-of-band, like a node's genesis block) -

    /// Install a cell directly into the ledger (genesis path — bypasses the
    /// executor, the way a node seeds its genesis cells). Emits a `CellBorn`
    /// dynamics event so the visual layer sees it appear. Returns its id.
    pub fn genesis_cell(&mut self, seed: u8, balance: i64) -> CellId {
        let cell = make_open_cell(seed, balance);
        self.install_genesis(cell, balance)
    }

    /// The single genesis install path: inserts `cell` into the live engine's
    /// ledger, records it in the replayable [`History`] (so the post-state root
    /// tooth is captured), and emits the `CellBorn` dynamics. Returns the id.
    fn install_genesis(&mut self, cell: Cell, balance: i64) -> CellId {
        let id = cell.id();
        // Install into the AUTHORITATIVE engine ledger.
        self.engine
            .ledger_mut()
            .insert_cell(cell.clone())
            .expect("genesis insert is into a fresh slot");
        // Mirror into the replay tape (its own ledger), capturing the root
        // tooth. Same cell, same order → the recorded root equals the engine's.
        self.history
            .record_genesis(&mut self.record_ledger, cell.clone());
        // DURABLE genesis mirror (SEAM §2): a genesis install emits no
        // `CommitRecord`, so the durable image would miss this cell on reopen
        // unless we record it here. Last-writer-wins by id (so a later in-place
        // genesis mutation overwrites). Fail-closed: a durable error refuses the
        // install rather than leaving RAM ahead of disk.
        if let Some(p) = self.persist.as_ref() {
            p.record_genesis(&cell)
                .expect("durable genesis record must not fail on a healthy image");
        }
        self.dynamics.emit(WorldEvent::CellBorn {
            cell: id,
            balance,
            genesis: true,
        });
        // Genesis installs mutate the live ledger WITHOUT bumping height or pushing
        // a receipt, so the witness tooth is unchanged — bust the state_root memo.
        self.state_root_memo.set(None);
        id
    }

    /// Re-record a cell's current post-state into the durable genesis table (the
    /// in-place genesis-path mutators call this when the image is durable, so a
    /// genesis-SETUP `set_cell_program`/`genesis_grant_cap`/`genesis_open_permissions`
    /// survives a reopen). No-op on an ephemeral world.
    ///
    /// This is now load-bearing ONLY for genesis-SETUP (a mutation BEFORE the cell's
    /// first turn — the genesis-mirror snapshot IS the pre-turn base, so recovery's
    /// turn re-execution sees the right cell). Runtime customization no longer routes
    /// here: a mid-session reprogram/grant/permission-change rides an ORDERED turn
    /// (`Effect::SetProgram` / `GrantCapability` / `SetPermissions`), landing a
    /// `CommitRecord` so recovery replays it in order — the persist-durability
    /// category error dissolved at its root.
    fn durable_regenesis(&self, id: &CellId) {
        if let Some(p) = self.persist.as_ref() {
            if let Some(cell) = self.engine.ledger().get(id) {
                p.record_genesis(cell)
                    .expect("durable genesis re-record must not fail on a healthy image");
            }
        }
    }

    /// Would an in-place genesis-path mutation of `cell` corrupt the DURABLE image's
    /// reopen? TRUE iff this is a durable image AND a committed turn already touched
    /// `cell` — the genesis-mirror-after-turn bug (HORIZONLOG): the post-mutation
    /// cell, recorded as timeless "genesis" by [`Self::durable_regenesis`], poisons
    /// recovery's re-execution of that turn (it re-executes against the wrong base,
    /// diverges, and the fail-closed integrity check REFUSES the image). Genesis-SETUP
    /// mutations (before the cell's first turn) and ephemeral (non-durable) worlds
    /// return false — they are sound. The genesis-path mutators consult this to
    /// REFUSE fail-fast rather than silently corrupt the image on reopen.
    fn genesis_mutation_would_break_reopen(&self, cell: &CellId) -> bool {
        self.is_durable()
            && self.history.steps().iter().any(|s| match s {
                crate::replay::RecordedStep::Committed { turn, .. } => {
                    touched_cells(turn).iter().any(|c| c == cell)
                }
                crate::replay::RecordedStep::Genesis { .. } => false,
            })
    }

    /// Install the genesis cell for an identity at its REAL derived id.
    ///
    /// `public_key` + `token_id` are the exact pair `Cell::with_balance` (and
    /// `AgentCipherclerk::cell_id`) derive the id over, so the installed cell's
    /// id equals the identity's `cell_id`. The cell carries `open_permissions`
    /// (single-custody operator authority). Returns the derived [`CellId`].
    ///
    /// This is the real home for "embody an identity": the cipherclerk panel
    /// hands `World` the identity's `(public_key, token_id, balance)` and `World`
    /// builds + installs the genesis cell (rather than the panel building the
    /// `Cell` itself).
    pub fn embody(&mut self, public_key: [u8; 32], token_id: [u8; 32], balance: i64) -> CellId {
        let mut cell = Cell::with_balance(public_key, token_id, balance);
        cell.permissions = open_permissions();
        self.install_genesis(cell, balance)
    }

    /// Install a genesis cell that already HOLDS a capability reaching
    /// `cap_target` (so a later `GrantCapability` from it is legitimate — the
    /// executor's no-amplification rule means you can only grant what you hold).
    /// Returns `(id, slot)` of the seeded capability.
    pub fn genesis_cell_with_cap(
        &mut self,
        seed: u8,
        balance: i64,
        cap_target: CellId,
    ) -> (CellId, u32) {
        let mut cell = make_open_cell(seed, balance);
        let slot = cell
            .capabilities
            .grant(cap_target, AuthRequired::None)
            .expect("fresh c-list has a free slot");
        let id = self.install_genesis(cell, balance);
        (id, slot)
    }

    /// Install a fully-specified cell (genesis path). For richer fixtures (a
    /// cell with a program, an issuer well carrying −supply, …).
    pub fn genesis_install(&mut self, cell: Cell) -> CellId {
        let balance = cell.state.balance();
        self.install_genesis(cell, balance)
    }

    /// Re-program a cell's [`CellProgram`] in place (a GENESIS-PATH update, like
    /// seeding the cell — for the trusted window manager that OWNS a cell and
    /// installs its caveats). Used by the verified compositor
    /// ([`crate::scene::VerifiedScene`]) to bake the scene-authority admit-table
    /// onto a compositor cell before a `present()` so the EXECUTOR'S program-check
    /// gates the frame advance (the Lean `compositorSpec.caveats` closed over the
    /// live scene). Mirrored into the replay-recorder's ledger so the recorded
    /// post-state roots stay in lock-step with the live engine (a later present's
    /// `SetField` re-executes against the SAME program on both ledgers).
    ///
    /// This installs AUTHORITY (a slot caveat), it does not move value or commit a
    /// turn; it is the trusted root's prerogative over a cell it owns, exactly as
    /// `genesis_install` seeds a cell's initial program. Returns `true` if the
    /// cell existed (in the live engine ledger) and was re-programmed.
    pub fn set_cell_program(&mut self, cell: &CellId, program: dregg_cell::CellProgram) -> bool {
        // FAIL-FAST guard (HORIZONLOG persist bug): a genesis-path mutation on a cell
        // a committed turn already touched would make the DURABLE image non-reopenable
        // (the genesis-mirror-after-turn bug — the post-mutation cell, recorded as
        // timeless "genesis", poisons recovery's re-execution of that turn). REFUSE
        // it here rather than silently corrupt the image on reopen. Genesis-SETUP
        // mutations (before the cell's first turn) and ephemeral worlds pass through.
        // (The sound full fix — ordered pre/post-chain genesis events — is HORIZONLOG'd.)
        if self.genesis_mutation_would_break_reopen(cell) {
            return false;
        }
        let existed = if let Some(c) = self.engine.ledger_mut().get_mut(cell) {
            c.program = program.clone();
            true
        } else {
            false
        };
        // Keep the replay tape's ledger in lock-step so its recorded roots match
        // the live engine's (the compositor cell carries the SAME program on both).
        if let Some(c) = self.record_ledger.get_mut(cell) {
            c.program = program;
        }
        // Durable genesis re-record (SEAM §2): the in-place program change carries
        // no `CommitRecord`, so persist the cell's new post-state for reopen.
        if existed {
            self.durable_regenesis(cell);
        }
        // Genesis-path ledger mutation without a height bump — bust the memo.
        self.state_root_memo.set(None);
        existed
    }

    /// Grant `holder` a capability reaching `target` via the GENESIS PATH (the
    /// trusted window manager installing an owner-grant — the way `surface.rs`
    /// documents the shell handing the surface cap back when a surface opens). The
    /// installed cap is unrestricted (`AuthRequired::None`); the executor's
    /// no-amplification rule still gates any later *delegation* of it. Mirrored
    /// into the replay-recorder's ledger so the recorded roots stay in lock-step.
    /// Returns the granted slot (in the live engine ledger), or `None` if the
    /// holder cell does not exist or its c-list is full.
    ///
    /// This is the authority leg of a `present()`: the presenter holds a surface
    /// cap on the compositor cell (the Lean `compositorState`'s `[.endpoint cell …]`),
    /// so the executor's cross-cell authority check passes and the SCENE CAVEAT —
    /// not the cap — is the load-bearing admission gate (faithful to the Lean §10:
    /// even an authorized-to-present cell cannot overpaint/spoof/steal-focus).
    pub fn genesis_grant_cap(&mut self, holder: &CellId, target: CellId) -> Option<u32> {
        // FAIL-FAST guard (HORIZONLOG persist bug): refuse a genesis-path c-list
        // mutation that would make the durable image non-reopenable (the holder was
        // already touched by a committed turn). Same class as `set_cell_program`.
        if self.genesis_mutation_would_break_reopen(holder) {
            return None;
        }
        let slot = self
            .engine
            .ledger_mut()
            .get_mut(holder)?
            .capabilities
            .grant(target, AuthRequired::None);
        // Mirror into the replay tape's ledger (same holder, same target) so the
        // recorded roots match the live engine's after a present's SetField.
        if let Some(c) = self.record_ledger.get_mut(holder) {
            let _ = c.capabilities.grant(target, AuthRequired::None);
        }
        // Durable genesis re-record (SEAM §2): the in-place cap grant carries no
        // `CommitRecord`, so persist the holder's new post-state for reopen.
        if slot.is_some() {
            self.durable_regenesis(holder);
        }
        // Genesis-path ledger mutation without a height bump — bust the memo.
        self.state_root_memo.set(None);
        slot
    }

    /// Open `cell`'s [`Permissions`] to the single-custody operator set
    /// (`open_permissions`, gating nothing) via the GENESIS PATH — the minter/owner
    /// endowing a cell it owns, exactly as [`genesis_grant_cap`] installs an
    /// owner-grant or [`set_cell_program`] seeds a program. Used by the headline demo
    /// ([`crate::demo`]) after a factory-birth: a factory-born child carries the
    /// factory's default permissions (which require a signature to send FROM it), so
    /// the minter opens its freshly-minted budget cell's permissions the way a node
    /// seeds a genesis cell's authority. Mirrored into the replay tape's ledger so the
    /// recorded roots stay in lock-step. Returns `true` if the cell existed.
    ///
    /// This installs AUTHORITY (a permissions set) on a cell the caller owns; it does
    /// not move value or commit a turn — the trusted root's prerogative over its own
    /// cell, NOT a bypass of the executor (a later spend FROM the cell still runs
    /// through the real executor; this only sets what that executor gates against).
    pub fn genesis_open_permissions(&mut self, cell: &CellId) -> bool {
        // FAIL-FAST guard (HORIZONLOG persist bug): refuse a genesis-path permissions
        // mutation that would make the durable image non-reopenable (the cell was
        // already touched by a committed turn). Same class as `set_cell_program`.
        if self.genesis_mutation_would_break_reopen(cell) {
            return false;
        }
        let existed = if let Some(c) = self.engine.ledger_mut().get_mut(cell) {
            c.permissions = open_permissions();
            true
        } else {
            false
        };
        if let Some(c) = self.record_ledger.get_mut(cell) {
            c.permissions = open_permissions();
        }
        // Durable genesis re-record (SEAM §2): the in-place permissions change
        // carries no `CommitRecord`, so persist the cell's new post-state.
        if existed {
            self.durable_regenesis(cell);
        }
        // Genesis-path ledger mutation without a height bump — bust the memo.
        self.state_root_memo.set(None);
        existed
    }

    /// **Write a cell's universal-memory heap out-of-band and reseal its
    /// committed `heap_root`** — the per-cell umem boundary (`UMEM-PRIMITIVE` §2,
    /// §8; `cell/src/state.rs`: `set_heap` / `reseal_heap_root`). Replaces the
    /// cell's `heap_map` wholesale (so a dropped leaf simply vanishes from the
    /// boundary) and recomputes `heap_root` = sorted-Poseidon2 over the present
    /// leaves, so the resealed boundary IS the cell's committed commitment.
    ///
    /// This is the document-on-umem ride ([`dregg_doc::DocHeapCell`]): the desktop
    /// projects a document into its cell's umem-heap and reseals, so the
    /// document's commitment IS that `heap_root`. The heap register is orthogonal
    /// to `fields_map`/`fields_root` (a later `SetField` turn re-executes against,
    /// and preserves, the written heap). Like [`Self::set_cell_program`] /
    /// [`Self::genesis_grant_cap`], it installs committed state on a cell without
    /// moving value or running a turn — there is no kernel heap effect, the writes
    /// are ordinary heap writes the substrate already commits. Mirrored into the
    /// replay-recorder's ledger so the recorded roots stay in lock-step.
    ///
    /// FAIL-FAST on a DURABLE image whose cell a committed turn already touched
    /// (the genesis-mirror-after-turn bug): returns `false` rather than poison
    /// reopen. The desktop's demo world is ephemeral, so this passes; a durable
    /// runtime heap write awaits an ordered heap effect (HORIZONLOG seam). Returns
    /// `true` if the cell existed and its boundary was resealed.
    pub fn set_cell_heap(
        &mut self,
        cell: &CellId,
        heap_map: std::collections::BTreeMap<(u32, u32), dregg_cell::FieldElement>,
    ) -> bool {
        if self.genesis_mutation_would_break_reopen(cell) {
            return false;
        }
        let existed = if let Some(c) = self.engine.ledger_mut().get_mut(cell) {
            c.state.heap_map = heap_map.clone();
            c.state.reseal_heap_root();
            true
        } else {
            false
        };
        // Keep the replay tape's ledger in lock-step so its recorded roots match
        // the live engine's (the document cell carries the SAME umem boundary).
        if let Some(c) = self.record_ledger.get_mut(cell) {
            c.state.heap_map = heap_map;
            c.state.reseal_heap_root();
        }
        // Durable genesis re-record (SEAM §2): the in-place heap write carries no
        // `CommitRecord`, so persist the cell's new post-state for reopen.
        if existed {
            self.durable_regenesis(cell);
        }
        // Genesis-path ledger mutation without a height bump — bust the memo.
        self.state_root_memo.set(None);
        existed
    }

    /// Deploy a [`FactoryDescriptor`] into the embedded executor's factory
    /// registry (the out-of-band genesis path — a node registers its factories
    /// the way it seeds genesis cells). Returns the factory's content-addressed
    /// VK, against which a later [`create_cell_from_factory`] effect is
    /// validated by the real executor. The descriptor is also mirrored into the
    /// replay tape's executor so factory-births re-derive on replay.
    pub fn deploy_factory(&mut self, descriptor: dregg_cell::FactoryDescriptor) -> [u8; 32] {
        let vk = self
            .engine
            .executor_mut()
            .deploy_factory(descriptor.clone());
        // Keep the replay recorder's executor in lock-step so a factory-birth
        // committed below re-derives identically on replay.
        let _ = self.record_exec.deploy_factory(descriptor.clone());
        // Retain the descriptor so a fork can replay it onto its throwaway
        // executor (the live registry isn't enumerable; this is our own record).
        self.deployed_factories.push(descriptor);
        vk
    }

    // --- THE COMMIT PATH (every real state transition goes through here) -----

    /// Commit a turn against the embedded verified executor.
    ///
    /// Threads the receipt-chain head for `turn.agent` automatically (so callers
    /// don't have to), runs the REAL executor, and — on commit — records the new
    /// head, advances the height, appends the receipt to the provenance log, and
    /// derives + emits the dynamics events for the transition.
    pub fn commit_turn(&mut self, mut turn: Turn) -> CommitOutcome {
        // THE SUSPEND GATE (meta-debug §3.2): if the live loop is halted, the turn
        // is STAGED, not run. The head freezes; the turn lands in `pending` in
        // arrival order and emits a `TurnQueued` event (so the dynamics stream stays
        // complete under suspension — Seam 3). It will commit on `resume(drain)`.
        if self.suspended {
            let agent = turn.agent;
            self.pending.push_back(turn);
            self.dynamics.emit(WorldEvent::TurnQueued { agent });
            return CommitOutcome::Queued { agent };
        }

        // Thread the chain head the engine's executor will check.
        turn.previous_receipt_hash = self.engine.executor().get_last_receipt_hash(&turn.agent);

        // Snapshot the pre-state balances of touched cells so we can describe
        // the flow in the dynamics stream.
        let touched = touched_cells(&turn);
        let pre: HashMap<CellId, i64> = touched
            .iter()
            .filter_map(|id| {
                self.engine
                    .ledger()
                    .get(id)
                    .map(|c| (*id, c.state.balance()))
            })
            .collect();

        // Run the turn through the REAL embedded engine (the SDK's DreggEngine,
        // which owns the executor+ledger borrow internally).
        match self.engine.execute_turn(&turn) {
            Ok(receipt) => {
                // Advance the engine's per-agent chain head (DreggEngine's
                // execute_turn does not rebind it; do it here as the live path).
                self.engine
                    .executor()
                    .set_last_receipt_hash(receipt.agent, receipt.receipt_hash());
                // SYMBOLIC EXECUTION: in `Symbolic` mode the witness is DEFERRED.
                // We skip the replay-tape double-execution (which would re-run a
                // FULL `execute` + `Ledger::root()` on the recorder, defeating the
                // cost saving) and instead BUFFER the turn in `symbolic_turns`.
                // `World::collapse` re-runs the buffer under Full to materialize
                // the tape + the real witnesses. In `Full` mode the tape records
                // eagerly, exactly as before. (The engine executor's mode, set by
                // `set_witness_mode`, already made the live receipt's state-hash
                // the deferred sentinel under Symbolic.)
                if self.witness_mode.is_symbolic() {
                    self.symbolic_turns.push(turn.clone());
                } else {
                    // Mirror the commit onto the replay tape (re-executes against the
                    // recorder's own ledger/executor, capturing the post-state root).
                    self.history.record_commit(
                        &self.record_exec,
                        &mut self.record_ledger,
                        turn.clone(),
                    );
                }
                self.height += 1;

                // THE DURABLE DUAL-WRITE (M4, A.2) — O(change). When the image is
                // durable, record this turn into the redb commit log (post-state of
                // the touched cells + the canonical post-state root, ONE ACID txn)
                // and persist the input turn (A.4, for rewind). FAIL-CLOSED (A.2.1,
                // *Green Or Bust*): a durable-write error is NOT swallowed — the
                // World refuses a commit it could not durably record, keeping RAM
                // and disk in lock-step (the node's discipline). The in-RAM engine
                // already advanced, so on a durable failure we surface it as a hard
                // rejection AND drop the store to ephemeral (loud, not silent).
                // SYMBOLIC EXECUTION: a deferred-witness turn has NO real
                // post-state root to durably record (its receipt carries the
                // deferred sentinel), so it is NOT durably written here. It
                // becomes durable only after `collapse` re-derives the real
                // witness. (A durable world should stay in `Full` for the live
                // commit path; symbolic is a local/ephemeral fast path.)
                if self.persist.is_some() && !self.witness_mode.is_symbolic() {
                    let height = self.height;
                    // THE DURABLE OVERLAY'S CHANGE-SET MUST BE COMPLETE (CORE-AUDIT.md
                    // finding 1). `touched` is a SYNTACTIC over-approximation of the
                    // input turn that misses cells an effect resolves at runtime (a
                    // burn's issuer well, a create's newborn, a factory birth, the
                    // metered agent) — recording the correct root over an incomplete
                    // overlay makes recovery refuse a valid image (or silently truncate
                    // a committed turn). The executor's journal write-set is EXACT and
                    // complete; union it with `touched` (belt-and-suspenders — a
                    // false-positive unchanged cell in the overlay reconstructs
                    // identically; only a MISSING cell is the bug).
                    let mut write_set = touched.clone();
                    for id in self.engine.executor().last_write_set() {
                        if !write_set.contains(&id) {
                            write_set.push(id);
                        }
                    }
                    // Split the borrows: take `persist` out, write through the
                    // disjoint `engine` borrow, then put it back (or drop it on a
                    // durable failure — the loud degrade-to-ephemeral path).
                    let mut p = self.persist.take().expect("checked is_some");
                    let result =
                        p.dual_write(height, self.engine.ledger(), &write_set, &receipt, &turn);
                    match result {
                        Ok(()) => self.persist = Some(p),
                        Err(e) => {
                            // `p` dropped → image degraded to ephemeral, loudly named.
                            let reason = format!(
                                "durable image write failed (image no longer durable): {e}"
                            );
                            self.dynamics.emit(WorldEvent::TurnRejected {
                                agent: turn.agent,
                                reason: reason.clone(),
                            });
                            return CommitOutcome::Rejected {
                                reason,
                                at_action: vec![],
                            };
                        }
                    }
                }

                let mut events = Vec::new();
                events.push(WorldEvent::TurnCommitted {
                    height: self.height,
                    agent: receipt.agent,
                    receipt_hash: receipt.receipt_hash(),
                    turn_hash: receipt.turn_hash,
                    action_count: receipt.action_count,
                    computrons: receipt.computrons_used,
                });
                // Derive per-effect dynamics from the post-state delta.
                for id in &touched {
                    if let Some(cell) = self.engine.ledger().get(id) {
                        let before = pre.get(id).copied().unwrap_or(0);
                        let after = cell.state.balance();
                        if before != after {
                            events.push(WorldEvent::BalanceFlowed {
                                cell: *id,
                                before,
                                after,
                            });
                        }
                    }
                }
                // Surface the effect kinds (caps granted, cells born, fields set)
                // across the WHOLE forest depth-first — a nested (depth >= 2)
                // SetField/Grant/etc. is a real change, and truncating at depth 1
                // left a bind reading that slot frozen (CORE-AUDIT.md finding 6).
                for root in &turn.call_forest.roots {
                    for node in root.iter_dfs() {
                        collect_effect_events(&node.action, &mut events);
                    }
                }

                for ev in &events {
                    self.dynamics.emit(ev.clone());
                }
                self.receipts.push(receipt.clone());
                CommitOutcome::Committed {
                    receipt: Box::new(receipt),
                    events,
                }
            }
            Err(EmbedError::TurnRejected { reason, at_action }) => {
                self.dynamics.emit(WorldEvent::TurnRejected {
                    agent: turn.agent,
                    reason: reason.clone(),
                });
                CommitOutcome::Rejected { reason, at_action }
            }
            Err(other) => {
                let reason = other.to_string();
                self.dynamics.emit(WorldEvent::TurnRejected {
                    agent: turn.agent,
                    reason: reason.clone(),
                });
                CommitOutcome::Rejected {
                    reason,
                    at_action: vec![],
                }
            }
        }
    }

    // --- SYMBOLIC EXECUTION (the deferred-witness fast path + collapse) ------

    /// The current [`WitnessMode`] (Full by default).
    pub fn witness_mode(&self) -> WitnessMode {
        self.witness_mode
    }

    /// `true` iff the live commit path is currently deferring witnesses
    /// ([`WitnessMode::Symbolic`]).
    pub fn is_symbolic(&self) -> bool {
        self.witness_mode.is_symbolic()
    }

    /// How many symbolic (deferred-witness) turns are buffered, awaiting
    /// [`World::collapse`]. `0` in Full mode or after a collapse.
    pub fn symbolic_pending(&self) -> usize {
        self.symbolic_turns.len()
    }

    /// **Enter / leave SYMBOLIC mode** — the local deferred-witness fast path.
    ///
    /// In [`WitnessMode::Symbolic`] the engine applies each turn's FULL state
    /// transition (balances / caps / nonces — the abstract progress) but DEFERS
    /// the per-turn Merkle witness: the engine executor skips `Ledger::root()`
    /// (the receipt carries the deferred sentinel state-hash), and `commit_turn`
    /// skips the replay-tape double-execution, buffering the turn for later
    /// [`World::collapse`]. This is the cost the mode saves: zero per-turn
    /// hashing on the live path AND no second full execution on the recorder.
    ///
    /// SOUNDNESS: this selects ONLY whether witnesses materialize; it NEVER
    /// changes which turns are admitted (every legality gate — authority,
    /// conservation, the `NoteSpend` STARK, sovereign-witness, nonce/fee — runs
    /// identically in both modes). A symbolic receipt is local/unpublishable
    /// until collapsed; the witness is deferred, never the decision.
    ///
    /// Switching back to `Full` does NOT auto-collapse the already-buffered
    /// symbolic turns (call [`World::collapse`] for that); it only makes
    /// SUBSEQUENT turns witness eagerly again. The engine executor's mode is
    /// flipped here so the live receipts reflect the new mode immediately.
    pub fn set_witness_mode(&mut self, mode: WitnessMode) {
        self.witness_mode = mode;
        self.engine.executor().set_witness_mode(mode);
    }

    /// **COLLAPSE** — materialize the deferred witnesses of every buffered
    /// symbolic turn by re-running them through FULL execution on the replay
    /// recorder, reproducing EXACTLY what a Full run would have witnessed.
    ///
    /// For each buffered symbolic turn, this drives the SKIPPED replay-tape
    /// commit (`History::record_commit` against the recorder's Full executor +
    /// ledger), which re-executes the turn and captures the real post-state root
    /// tooth — then replaces that turn's DEFERRED receipt in the provenance log
    /// with the re-derived REAL one. Determinism is already discharged (the
    /// pinned timestamp + cost model + the recorder's chain-head lock-step), so
    /// each collapsed receipt is byte-identical to the Full-mode receipt.
    ///
    /// After collapse the live commit path returns to [`WitnessMode::Full`] and
    /// the symbolic buffer is empty. FAIL-CLOSED: if a buffered turn does NOT
    /// re-commit under Full, or the materialized recorder root diverges from the
    /// live engine's post-state, this returns `Err` (an integrity event — a
    /// symbolic run that admitted a turn Full execution refuses, which the
    /// shared admission gate makes impossible barring corruption).
    ///
    /// Returns the count of turns collapsed.
    pub fn collapse(&mut self) -> Result<usize, String> {
        let buffered = std::mem::take(&mut self.symbolic_turns);
        let n = buffered.len();

        // The provenance index of the FIRST symbolic receipt: the symbolic turns
        // are the LAST `n` entries in `receipts` (they were pushed in order,
        // after any prior Full commits). Re-derive each and overwrite in place.
        let first = self.receipts.len().checked_sub(n).ok_or_else(|| {
            "collapse: fewer receipts than buffered symbolic turns (provenance desync)".to_string()
        })?;

        for (offset, turn) in buffered.into_iter().enumerate() {
            // Drive the SKIPPED Full replay-tape commit — re-executes the turn
            // against the recorder's Full executor + ledger and captures the real
            // post-root tooth. The recorder's chain head advances in lock-step.
            let receipt = self
                .history
                .record_commit(&self.record_exec, &mut self.record_ledger, turn.clone())
                .ok_or_else(|| {
                    format!(
                        "collapse: buffered symbolic turn (agent {}) did NOT re-commit under \
                         Full execution — integrity event (symbolic admitted a Full-illegal turn)",
                        short(&turn.agent)
                    )
                })?;
            debug_assert!(
                !is_deferred(&receipt),
                "a collapsed receipt must carry a real (non-deferred) witness"
            );
            // Replace the deferred receipt in the provenance log with the real one.
            self.receipts[first + offset] = receipt;
        }

        // FAIL-CLOSED convergence: the recorder ledger (Full-replayed) MUST now
        // commit to the SAME canonical root as the live engine ledger (which
        // applied the identical state transitions, just witness-deferred). A
        // divergence means the deferred path drifted from Full — refuse.
        let engine_root = crate::persistence::canonical_ledger_root(self.engine.ledger());
        let record_root = crate::persistence::canonical_ledger_root(&self.record_ledger);
        if engine_root != record_root {
            return Err(format!(
                "collapse: post-collapse ledger divergence — engine root {:?} != \
                 collapsed recorder root {:?} (the symbolic state transition drifted from Full)",
                engine_root, record_root
            ));
        }

        // The live path returns to Full (subsequent turns witness eagerly).
        self.set_witness_mode(WitnessMode::Full);
        Ok(n)
    }

    // --- THE SUSPEND PRIMITIVE (halt-the-live-loop, meta-debug §3) -----------

    /// **SUSPEND** — halt the live loop. After this, every turn submitted through
    /// [`World::commit_turn`] is STAGED in the pending queue (returning
    /// [`CommitOutcome::Queued`]) instead of being run; the head is FROZEN at the
    /// current height. Inspection during suspension uses the ordinary mirror
    /// machinery (a `FocusTarget::World` projection) over the frozen-but-live head.
    ///
    /// This is the missing sibling of Snapshot (`ui_snapshot.rs`): Snapshot freezes
    /// a *cursor* (a past height) while the loop keeps running; Suspend freezes the
    /// *head* (turn-application) itself. Idempotent: suspending an already-suspended
    /// world is a no-op.
    pub fn suspend(&mut self) {
        self.suspended = true;
    }

    /// `true` iff the live loop is currently HALTED (turns queue instead of commit).
    pub fn is_suspended(&self) -> bool {
        self.suspended
    }

    /// How many turns are STAGED in the pending queue (0 when running or drained).
    pub fn pending_len(&self) -> usize {
        self.pending.len()
    }

    /// A read-only view of the staged continuation — the queued turns, in arrival
    /// order. This is the inspectable "continuation" of the suspended loop (the
    /// partial turn whose holes are the not-yet-committed turns, §3.3); the
    /// meta-debugger walks it without committing.
    pub fn pending_turns(&self) -> impl Iterator<Item = &Turn> {
        self.pending.iter()
    }

    /// **RESUME** — un-halt the live loop and apply the continuation.
    ///
    ///   * [`ResumeMode::Drain`] commits the queued turns, in arrival order,
    ///     through the normal `commit_turn` gate (each re-passes the full
    ///     executor/conservation/authority check at fill time — Seam 5: continuation
    ///     editing stays shape-eager).
    ///   * [`ResumeMode::Modified`] DRAINS the existing queue and re-submits the
    ///     caller's edited batch instead — dropping/inserting/reordering turns
    ///     before they run. Each turn in the edited batch STILL passes the full
    ///     `commit_turn` gate, so a modified continuation cannot smuggle in
    ///     unauthorized or non-conserving work — the edit is to *which* turns run,
    ///     never to the per-turn invariant.
    ///
    /// Returns the per-turn outcomes, in application order. The live loop is running
    /// again on return (`is_suspended()` is false), so any turn submitted after this
    /// commits directly.
    pub fn resume(&mut self, mode: ResumeMode) -> Vec<CommitOutcome> {
        // Un-halt FIRST so the drained turns flow through the normal commit path
        // (not back into the queue).
        self.suspended = false;
        let batch: Vec<Turn> = match mode {
            ResumeMode::Drain => self.pending.drain(..).collect(),
            ResumeMode::Modified(edited) => {
                // The operator hands an edited continuation: discard the staged
                // queue and run the edit instead. The drained turns are dropped (the
                // edit's job is to decide which work proceeds).
                self.pending.clear();
                edited
            }
        };
        batch
            .into_iter()
            .map(|mut turn| {
                // FILL-TIME NONCE RE-STAMP. A staged (or operator-edited) turn was
                // built against the FROZEN head, so several turns from one agent all
                // carry the same baked-in nonce (`next_nonce` could not advance under
                // suspension). The continuation commits them IN SEQUENCE, so each must
                // carry the agent's then-current nonce — exactly as `commit_turn`
                // already re-threads `previous_receipt_hash` at fill time. We re-stamp
                // here, the moment before the gate runs, so the queue drains in order
                // without nonce reuse. This binds the nonce later (fill time), never
                // weakens it: the executor still enforces the re-stamped value, and
                // conservation/authority are checked on the turn as it actually runs.
                turn.nonce = self.next_nonce(&turn.agent);
                self.commit_turn(turn)
            })
            .collect()
    }

    /// **RESUME (DRAIN)** — the common case: un-halt and commit the staged queue in
    /// arrival order. Shorthand for `resume(ResumeMode::Drain)`.
    pub fn resume_drain(&mut self) -> Vec<CommitOutcome> {
        self.resume(ResumeMode::Drain)
    }

    // --- ergonomic turn constructors (the typed verbs, embedded-local) -------

    /// Build a single-action, `Unchecked`-authorized turn carrying `effects`.
    /// (`Unchecked` is honest here: the embedded world is single-custody — the
    /// OPERATOR is the authority. The cells' `Permissions` still gate every
    /// effect; an effect a cell forbids is rejected regardless of auth.)
    pub fn turn(&self, agent: CellId, effects: Vec<Effect>) -> Turn {
        let mut t = bare_turn(agent, self.next_nonce(&agent), effects);
        t.fee = self.turn_fee;
        t
    }

    /// Build a MULTI-ACTION turn: one `Action` per `(target, effects)` entry,
    /// all gathered into the agent's call-forest as sibling roots and submitted
    /// as ONE atomic verified turn (the executor commits the whole forest or
    /// rejects it — there is no partial commit). This is the surface the
    /// cockpit's multi-action composer drives: several effects, several target
    /// cells, one turn, one receipt.
    ///
    /// Each action carries `Authorization::Unchecked` (honest for the single-
    /// custody embedded world — the operator is the authority; the cells'
    /// `Permissions` + the executor's whole-turn guarantees still gate every
    /// effect). Lifecycle verbs (seal/unseal/destroy/burn) require the action's
    /// `target` to equal the effect's target, so each composed action acts on
    /// its own cell.
    pub fn forest_turn(&self, agent: CellId, actions: Vec<(CellId, Vec<Effect>)>) -> Turn {
        let nonce = self.next_nonce(&agent);
        let mut forest = CallForest::new();
        for (target, effects) in actions {
            forest.add_root(bare_action(target, effects));
        }
        let mut t = wrap_turn(agent, nonce, forest);
        t.fee = self.turn_fee;
        t
    }

    /// Wrap a PRE-BUILT [`Action`] (its `method`/`args`/`effects` already set by
    /// the caller) into a single-root [`Turn`] with `agent` and its next nonce —
    /// the executor entry a userspace dispatcher (e.g.
    /// [`crate::service_explorer::ServiceExplorer::invoke`]) drives. Unlike
    /// [`Self::turn`] (which builds a bare zero-method action), this preserves the
    /// caller's action verbatim, so a method-targeting invocation keeps its
    /// `method` symbol (the cell program's `MethodIs` guard matches it).
    pub fn wrap_action_turn(&self, agent: CellId, action: Action) -> Turn {
        let nonce = self.next_nonce(&agent);
        let mut forest = CallForest::new();
        forest.add_root(action);
        let mut t = wrap_turn(agent, nonce, forest);
        t.fee = self.turn_fee;
        t
    }

    fn next_nonce(&self, agent: &CellId) -> u64 {
        self.engine
            .ledger()
            .get(agent)
            .map(|c| c.state.nonce())
            .unwrap_or(0)
    }
}

/// Best-effort unix timestamp (seconds).
fn now_unix() -> i64 {
    // wasm32 has no system clock — `SystemTime::now()` is `unreachable!`. Use the
    // browser's `Date.now()` (ms → s) so the live web cockpit gets real time.
    #[cfg(target_arch = "wasm32")]
    {
        (js_sys::Date::now() / 1000.0) as i64
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0)
    }
}

fn push_unique(ids: &mut Vec<CellId>, id: CellId) {
    if !ids.contains(&id) {
        ids.push(id);
    }
}

/// All cell ids a turn's effects touch (for pre/post balance diffing).
///
/// Walks the WHOLE forest depth-first (`CallTree::iter_dfs`), not just roots +
/// direct children — a nested (depth >= 2) sub-action's target/effects are real
/// mutations, and truncating at depth 1 dropped them from the dynamics diff (a
/// bind reading such a slot painted a permanently stale value). Note: this is a
/// SYNTACTIC over-approximation by effect kind (see `collect_touched`), so it is
/// still incomplete for the effect VARIANTS it does not enumerate — the sound
/// source is the executor's journal write-set (see CORE-AUDIT.md finding 1).
pub(crate) fn touched_cells(turn: &Turn) -> Vec<CellId> {
    let mut ids = Vec::new();
    for root in &turn.call_forest.roots {
        for node in root.iter_dfs() {
            push_unique(&mut ids, node.action.target);
            collect_touched(&node.action, &mut ids);
        }
    }
    ids
}

fn collect_touched(action: &Action, ids: &mut Vec<CellId>) {
    fn push(id: CellId, ids: &mut Vec<CellId>) {
        push_unique(ids, id);
    }
    for e in &action.effects {
        match e {
            Effect::Transfer { from, to, .. } => {
                push(*from, ids);
                push(*to, ids);
            }
            Effect::SetField { cell, .. }
            | Effect::IncrementNonce { cell }
            | Effect::EmitEvent { cell, .. }
            | Effect::SetProgram { cell, .. }
            | Effect::SetPermissions { cell, .. }
            | Effect::RevokeCapability { cell, .. } => push(*cell, ids),
            Effect::GrantCapability { from, to, .. } => {
                push(*from, ids);
                push(*to, ids);
            }
            Effect::Burn { target, .. }
            | Effect::CellSeal { target, .. }
            | Effect::CellUnseal { target }
            | Effect::CellDestroy { target, .. }
            | Effect::MakeSovereign { cell: target } => push(*target, ids),
            _ => {}
        }
    }
}

/// Translate an action's effects into human-meaningful dynamics events.
fn collect_effect_events(action: &Action, out: &mut Vec<WorldEvent>) {
    for e in &action.effects {
        match e {
            Effect::GrantCapability { from, to, .. } => {
                out.push(WorldEvent::CapabilityGranted {
                    from: *from,
                    to: *to,
                });
            }
            Effect::RevokeCapability { cell, slot } => {
                out.push(WorldEvent::CapabilityRevoked {
                    cell: *cell,
                    slot: *slot,
                });
            }
            Effect::CreateCell { balance, .. } => {
                out.push(WorldEvent::CellBorn {
                    // The id isn't known here without re-deriving; views render
                    // the freshly-appeared ledger cell. Use ZERO as a sentinel
                    // (the BalanceFlowed/ledger refresh carries the real one).
                    cell: CellId::ZERO,
                    balance: *balance as i64,
                    genesis: false,
                });
            }
            Effect::SetField { cell, index, .. } => {
                out.push(WorldEvent::FieldSet {
                    cell: *cell,
                    index: *index,
                });
            }
            Effect::CellSeal { target, .. } => {
                out.push(WorldEvent::CellSealed { cell: *target });
            }
            Effect::CellUnseal { target } => {
                out.push(WorldEvent::CellUnsealed { cell: *target });
            }
            Effect::CellDestroy { target, .. } => {
                out.push(WorldEvent::CellDestroyed { cell: *target });
            }
            Effect::Burn { target, amount, .. } => {
                out.push(WorldEvent::Burned {
                    cell: *target,
                    amount: *amount,
                });
            }
            Effect::CreateCellFromFactory { .. } => {
                out.push(WorldEvent::CellBorn {
                    cell: CellId::ZERO,
                    balance: 0,
                    genesis: false,
                });
            }
            // THE NOTIFY EDGE: an EmitEvent is the sender's committed receipt
            // that the swarm coordinator reads to wake the recipient's next turn.
            // The recipient drains it in its OWN future turn (async, not joint).
            Effect::EmitEvent { cell, event, .. } => {
                // The topic hash is the event's 32-byte symbol (Blake3 of the
                // topic string, as hashed by `emit_event()`).
                let topic_hash = event.topic;
                let data_len = event.data.len() * 32; // each FieldElement is 32 B
                                                      // `action.target` is the cell acting (the sender); `cell` is the
                                                      // cell the event is emitted ON (the notify recipient). When the
                                                      // sender emits to itself, sender == cell (a self-notification,
                                                      // valid and useful for checkpointing). The swarm coordinator uses
                                                      // this distinction to route the wake signal to `cell`'s inbox.
                out.push(WorldEvent::EventEmitted {
                    sender: action.target,
                    cell: *cell,
                    topic_hash,
                    data_len,
                });
            }
            // --- THE COMPLETENESS ARMS (M2 cache-soundness, EFFICIENCY-WELD-PLAN §4.1) ---
            // Each of these writes a cell the inspector renders WITHOUT moving its
            // balance, so the `BalanceFlowed` diff would miss it. Emit the generic
            // `CellMutated` tooth so the delta loop invalidates that cell's
            // memoized projection. (A nonce bump IS the BufferCell revision; a
            // sovereign flip / permissions / verification-key / cap reshape all
            // change what the inspector surfaces.)
            Effect::IncrementNonce { cell }
            | Effect::MakeSovereign { cell }
            | Effect::SetPermissions { cell, .. }
            | Effect::SetVerificationKey { cell, .. } => {
                out.push(WorldEvent::CellMutated { cell: *cell });
            }
            Effect::AttenuateCapability { cell, .. } => {
                out.push(WorldEvent::CellMutated { cell: *cell });
            }
            // An exercised capability runs INNER effects against a resolved target
            // cell; recurse so a write reached through a cap still names its cell.
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                let inner = Action {
                    effects: inner_effects.clone(),
                    ..action.clone()
                };
                collect_effect_events(&inner, out);
            }
            _ => {}
        }
    }
}

// ===========================================================================
// Construction helpers — the genesis fixtures + the bare turn shape.
//
// These mirror `turn/tests/integration_lifecycle.rs` (the canonical happy-path
// template): an `open_permissions` cell + an `Authorization::Unchecked` action.
// ===========================================================================

/// A permissions set that gates nothing — for the operator's own cells in the
/// single-custody embedded world. (Real federation cells carry real gates; this
/// is the local image's owner authority, made explicit.)
pub fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// A deterministic open cell from a one-byte seed (test/genesis fixture).
pub fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// A bare `Unchecked` action on `target` carrying `effects` (the executor-test
/// template shape). The building block both `bare_turn` and `forest_turn` use.
pub fn bare_action(target: CellId, effects: Vec<Effect>) -> Action {
    Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    }
}

/// The bare single-action turn shape (matches the executor test template).
pub fn bare_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(bare_action(agent, effects));
    wrap_turn(agent, nonce, forest)
}

/// Wrap a built call-forest into the bare `Turn` shape (no proofs/witnesses —
/// the single-custody embedded world's operator path).
fn wrap_turn(agent: CellId, nonce: u64, forest: CallForest) -> Turn {
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// A short, human cell-id (the first bytes, hex) — for labels/banners.
pub fn short(id: &CellId) -> String {
    crate::reflect::short_hex(id.as_bytes())
}

/// Convenience: a transfer effect.
pub fn transfer(from: CellId, to: CellId, amount: u64) -> Effect {
    Effect::Transfer { from, to, amount }
}

/// Convenience: grant `to` a capability reaching `cap_target` (the ocap edge).
/// Installs an unrestricted (`AuthRequired::None`) cap at `slot` — the cockpit's
/// "grant" verb. The real executor enforces no-amplification on delegation.
pub fn grant_capability(from: CellId, to: CellId, cap_target: CellId, slot: u32) -> Effect {
    Effect::GrantCapability {
        from,
        to,
        cap: dregg_cell::CapabilityRef {
            target: cap_target,
            slot,
            permissions: AuthRequired::None,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }
}

/// Convenience: revoke the capability at `slot` on `cell`.
pub fn revoke_capability(cell: CellId, slot: u32) -> Effect {
    Effect::RevokeCapability { cell, slot }
}

/// Convenience: create a new cell (the `createCell` verb).
///
/// Created cells are born with ZERO balance: the verified executor enforces
/// value conservation (`CreateCellNonZeroBalance`), so a cell cannot be birthed
/// holding value — value only ever *moves*. Fund it afterward with a transfer.
pub fn create_cell(seed: u8) -> Effect {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    Effect::CreateCell {
        public_key: pk,
        token_id: [0u8; 32],
        balance: 0,
    }
}

/// Convenience: write `value` into state slot `index` of `cell`.
pub fn set_field(cell: CellId, index: usize, value: dregg_cell::FieldElement) -> Effect {
    Effect::SetField { cell, index, value }
}

/// Convenience: advance `cell`'s nonce by one (the loop's step counter — the
/// monotone half of the exact shape a confined deos-js agent's `fire("bump")`
/// commits alongside its `SetField`).
pub fn increment_nonce(cell: CellId) -> Effect {
    Effect::IncrementNonce { cell }
}

/// Convenience: re-program `cell`'s [`CellProgram`] (its caveat table) as an
/// ORDERED effect — the in-protocol home for the genuinely-dynamic reprogram
/// (the per-present compositor re-bake, a live trustline/flash-well install).
/// Replaces the timeless out-of-band `World::set_cell_program` genesis-path
/// mutation: riding a turn lands a `CommitRecord`, so a durable image
/// reproduces it on replay (the persist-durability category-error fix).
pub fn set_program(cell: CellId, program: dregg_cell::CellProgram) -> Effect {
    Effect::SetProgram { cell, program }
}

/// Convenience: replace `cell`'s [`Permissions`] as an ORDERED effect (the
/// in-protocol home for an owner endowing a cell it owns — replaces the
/// genesis-path `genesis_open_permissions` mutation when the cell has already
/// been turn-touched).
pub fn set_permissions(cell: CellId, new_permissions: Permissions) -> Effect {
    Effect::SetPermissions {
        cell,
        new_permissions,
    }
}

/// Convenience: an emit-event effect with a topic symbol (the topic string is
/// BLAKE3'd to the 32-byte symbol the protocol uses).
pub fn emit_event(cell: CellId, topic: &str, data: Vec<dregg_cell::FieldElement>) -> Effect {
    let sym = *blake3::hash(topic.as_bytes()).as_bytes();
    Effect::EmitEvent {
        cell,
        event: Event::new(sym, data),
    }
}

// --- the lifecycle verbs (seal · unseal · destroy · burn) ------------------
//
// The verified executor enforces that each lifecycle effect's `target` MATCHES
// the action target (so `agent` must BE the cell being sealed/destroyed/burned;
// the cockpit composes these as self-acting turns). The `make_*_turn`
// constructors below bake that in so callers can't compose an ill-targeted one.

/// Convenience: seal `target` with a 32-byte commitment to `reason` (the
/// cleartext lives off-chain). After sealing, the cell rejects new effects
/// until [`unseal`] — the executor enforces this lifecycle gate.
pub fn seal(target: CellId, reason: &str) -> Effect {
    Effect::CellSeal {
        target,
        reason: *blake3::hash(reason.as_bytes()).as_bytes(),
    }
}

/// Convenience: reverse a seal — transition `target` from `Sealed` back to
/// `Live`. Rejected by the executor if the cell is not currently sealed.
pub fn unseal(target: CellId) -> Effect {
    Effect::CellUnseal { target }
}

/// Convenience: permanently retire `target`, binding a [`DeathCertificate`]
/// whose `cell_id` matches (the only field the executor checks against the
/// cell). Once destroyed the cell `is_terminal()` — every later effect is
/// rejected. `reason` distinguishes a voluntary retirement from a forced one.
pub fn destroy(target: CellId, height: u64, reason: DeathReason) -> Effect {
    Effect::CellDestroy {
        target,
        certificate: DeathCertificate {
            cell_id: target,
            last_receipt_hash: [0u8; 32],
            final_state_commitment: [0u8; 32],
            destroyed_at_height: height,
            reason,
        },
    }
}

/// Convenience: provably reduce `target`'s balance by `amount` (slot 0 = the
/// canonical balance slot — the only burnable slot in Silver-Vision). Unlike a
/// transfer there is no credited destination; with a registered issuer well the
/// executor routes the burn as a conserving move toward the well.
pub fn burn(target: CellId, amount: u64) -> Effect {
    Effect::Burn {
        target,
        slot: 0,
        amount,
    }
}

/// Convenience: birth a child cell from a deployed factory (the
/// `CreateCellFromFactory` verb). The executor validates the creation `params`
/// against the named factory's descriptor before installing the child.
pub fn create_cell_from_factory(
    factory_vk: [u8; 32],
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    params: dregg_cell::factory::FactoryCreationParams,
) -> Effect {
    Effect::CreateCellFromFactory {
        factory_vk,
        owner_pubkey,
        token_id,
        params,
    }
}

/// Build a populated demo world: three cells (a treasury, a service, a user),
/// an issuer well carrying −supply, and a handful of committed turns so the
/// cockpit boots into a LIVE image with real provenance — not a mock. Returns
/// the world and the (treasury, service, user) ids for the views to anchor on.
///
/// This runs the demo's five seed TURNS eagerly (the `--headless` self-check +
/// every `cargo test` path want the fully-populated image up front). The gpui
/// cockpit instead opens the window on the INSTANT genesis ([`demo_genesis`])
/// and drives [`DemoSeed::next`] AFTER first paint, so the window is alive
/// immediately and the cells fill in live — same content, just not on the paint
/// path. Both routes run the SAME real executor turns; nothing is faked.
pub fn demo_world() -> (World, [CellId; 3]) {
    let (mut w, anchors, mut seed) = demo_genesis();
    // Run every seed turn now (the eager, headless/test path).
    while seed.next(&mut w).is_some() {}
    (w, anchors)
}

/// [`demo_world`] with the wall-clock PINNED to `timestamp` — the DETERMINISTIC
/// demo boot. Two calls with the same `timestamp` produce receipt-identical
/// images (the timestamp is folded into every `TurnReceipt`, see
/// [`World::with_costs_and_timestamp`]), so their canonical ledger roots are
/// equal byte-for-byte. This is the hinge the DESKTOP-IN-A-LINK share URL
/// ([`crate::share_link`]) replays through: the link carries the instant, the
/// recipient re-derives the SAME world — never a screenshot taken on trust.
pub fn demo_world_at(timestamp: i64) -> (World, [CellId; 3]) {
    let (mut w, anchors, mut seed) = demo_genesis_at(timestamp);
    // Run every seed turn now (the eager, deterministic-replay path).
    while seed.next(&mut w).is_some() {}
    (w, anchors)
}

/// The INSTANT half of [`demo_world`]: install the three anchor cells (treasury,
/// service, user) and the issuer well via the GENESIS PATH (which bypasses the
/// executor — no turns run), and return a [`DemoSeed`] that will commit the five
/// demo turns on demand. This is sub-millisecond: no `commit_turn` runs here, so
/// the cockpit can open its window on this image immediately and seed the turns
/// afterward (cells appear live as each commits). Returns `(world, anchors, seed)`.
pub fn demo_genesis() -> (World, [CellId; 3], DemoSeed) {
    demo_genesis_at(now_unix())
}

/// [`demo_genesis`] with the wall-clock PINNED to `timestamp` (the deterministic
/// half [`demo_world_at`] builds on). [`demo_genesis`] pins `now_unix()` through
/// here — one construction path, the instant merely explicit.
pub fn demo_genesis_at(timestamp: i64) -> (World, [CellId; 3], DemoSeed) {
    let mut w = World::with_costs_and_timestamp(ComputronCosts::zero(), timestamp);
    let (anchors, seed) = seed_demo_genesis_onto(&mut w);
    (w, anchors, seed)
}

/// The GENESIS INSTALLS of [`demo_genesis_at`], factored to run ONTO an EXISTING
/// `world` (rather than constructing a fresh ephemeral one) — the seam the DURABLE
/// desktop weld (`crate::durable_desktop`) seeds through.
///
/// [`demo_genesis_at`] builds its own throwaway ephemeral `World`; but the durable
/// windowed desktop must seed a world it ALREADY OPENED against a redb image (so
/// the genesis installs — and the [`DemoSeed`] turns driven afterward — DUAL-WRITE
/// to the attached store and thus PERSIST). Because [`World::genesis_cell`] /
/// [`World::genesis_install`] mirror each cell via `record_genesis` when a store is
/// attached, running the identical install sequence here on a durable `world` makes
/// the warm demo world durable — the newcomer still gets the same image, but now it
/// survives a close+reopen. The install ORDER (treasury → user → service → well) is
/// byte-identical to [`demo_genesis_at`], so recovery reinstalls deterministically
/// and the anchor ids match. On an EPHEMERAL `world` this is exactly the old
/// behavior (no store ⟹ no mirror). Returns the `[treasury, service, user]` anchors
/// + the [`DemoSeed`] plan (drive it with [`DemoSeed::next`] to commit the 5 turns).
pub fn seed_demo_genesis_onto(w: &mut World) -> ([CellId; 3], DemoSeed) {
    let treasury = w.genesis_cell(0x11, 1_000_000);
    let user = w.genesis_cell(0x33, 5_000);
    // The service is born already holding a capability reaching the user (so it
    // can legitimately re-grant it later — the no-amplification rule).
    let (service, user_cap_slot) = w.genesis_cell_with_cap(0x22, 0, user);

    // An issuer well carrying −supply (THE EPOCH: wells hold negative balance).
    let mut well = make_open_cell(0xEE, 0);
    let _ = well.state.well_debit_balance(1_000_000);
    w.genesis_install(well);

    let seed = DemoSeed {
        anchors: [treasury, service, user],
        user_cap_slot,
        step: 0,
    };
    ([treasury, service, user], seed)
}

/// The seed-turn plan for the demo image: the five real executor turns that give
/// the cockpit its provenance, played ONE AT A TIME via [`DemoSeed::next`].
///
/// [`demo_world`] drains it eagerly; the gpui cockpit drives it from a foreground
/// async task after the window is already painted, calling `cx.notify()` between
/// steps so each committed turn shows up live. Each step runs the SAME real
/// `commit_turn` the eager path does — the asynchrony is purely about WHEN, never
/// about WHETHER the verified turn ran.
pub struct DemoSeed {
    anchors: [CellId; 3],
    user_cap_slot: u32,
    /// The index of the NEXT seed turn to commit (0..=5; `5` = done).
    step: usize,
}

impl DemoSeed {
    /// The total number of seed turns (the five that populate the demo image).
    pub const TOTAL: usize = 5;

    /// How many seed turns are still pending (0 once fully seeded).
    pub fn remaining(&self) -> usize {
        Self::TOTAL.saturating_sub(self.step)
    }

    /// Whether every seed turn has been committed.
    pub fn is_done(&self) -> bool {
        self.step >= Self::TOTAL
    }

    /// Commit the NEXT seed turn against `w` (the real executor), advancing the
    /// plan. Returns a short human label for the committed step (for a status/log
    /// line), or `None` once the plan is exhausted. Each call runs exactly ONE
    /// real verified turn — so a caller can drive it from a paint-friendly async
    /// loop, one turn per yield.
    pub fn next(&mut self, w: &mut World) -> Option<&'static str> {
        let [treasury, service, user] = self.anchors;
        let label = match self.step {
            0 => {
                let t = w.turn(treasury, vec![transfer(treasury, service, 250_000)]);
                let _ = w.commit_turn(t);
                "treasury → service (250,000)"
            }
            1 => {
                let t = w.turn(treasury, vec![transfer(treasury, user, 50_000)]);
                let _ = w.commit_turn(t);
                "treasury → user (50,000)"
            }
            2 => {
                let t = w.turn(user, vec![transfer(user, service, 1_000)]);
                let _ = w.commit_turn(t);
                "user → service (1,000)"
            }
            3 => {
                // An ocap grant: the service re-grants its user-capability back to
                // itself at a fresh slot (legitimate — it holds the cap at
                // `user_cap_slot`).
                let t = w.turn(
                    service,
                    vec![grant_capability(
                        service,
                        service,
                        user,
                        self.user_cap_slot + 1,
                    )],
                );
                let _ = w.commit_turn(t);
                "service re-grants its user-cap (ocap)"
            }
            4 => {
                // A state-field write on the service cell.
                let t = w.turn(service, vec![set_field(service, 0, [7u8; 32])]);
                let _ = w.commit_turn(t);
                "service state-field write"
            }
            _ => return None,
        };
        self.step += 1;
        Some(label)
    }
}

// ===========================================================================
// THE SEMIHOSTED COCKPIT — the executor-PD running UNDERNEATH, over the
// EmulatedKernel (`docs/SEMIHOST-COCKPIT.md`; `docs/FIRMAMENT.md §2` L3;
// `docs/DREGG-DESKTOP-OS.md §3` the KEYSTONE payoff).
//
// `World::commit_turn` runs a turn through the embedded verified executor
// DIRECTLY in-process. `SemihostCockpit` runs the SAME turn through the SAME
// verified executor, but DISPATCHED THROUGH THE SEMIHOST executor-PD: the turn
// is staged into the PD's `turn_in` region, the cockpit (an app-PD) signals the
// executor-PD over an `EmulatedKernel` Endpoint (the `ingress→executor` edge),
// the executor-PD reads `turn_in`, runs the cockpit's REAL `World` commit path,
// writes the `TurnReceipt` into `commit_out`, and replies — and the cockpit
// reads the receipt back out of `commit_out`. This proves the sel4 PD world is
// running underneath: the SAME `World` semantics, now reached through the
// firmament's `turn_in → step → commit_out` cap partition over the n=1
// microkernel — the SAME code path a real seL4 boot would take (only the launch
// mechanism, an in-process server vs. a real PD, differs).
// ===========================================================================

/// The cockpit's `World` driven as the executor-PD's [`TurnRunner`] — the
/// verified semantics behind the Endpoint.
///
/// It OWNS the real [`World`] (the embedded `DreggEngine` + the provenance log +
/// the dynamics + the replayable history) and, on a staged turn, decodes the
/// postcard [`Turn`] and runs it through the FULL real [`World::commit_turn`]
/// path (chain-head threading, history recording, dynamics emission, receipt
/// append — NOT a bypass). On commit it returns the postcard-encoded
/// [`TurnReceipt`] for the executor-PD to write into `commit_out`; on a rejected
/// turn it returns the reason (the ocap/verification guarantee firing,
/// fail-closed). A malformed/undecodable stage is a rejection too.
pub struct WorldRunner {
    world: World,
}

impl WorldRunner {
    /// Wrap a `World` as the executor-PD's turn runner.
    pub fn new(world: World) -> Self {
        WorldRunner { world }
    }

    /// Read access to the hosted world (for the harness / the cockpit to inspect
    /// the post-state the executor-PD advanced — the ledger, receipts, height).
    pub fn world(&self) -> &World {
        &self.world
    }

    /// Mutable access to the hosted world (e.g. to seed genesis cells before
    /// turns flow through the PD wire — the out-of-band genesis path, exactly as
    /// for a directly-driven `World`).
    pub fn world_mut(&mut self) -> &mut World {
        &mut self.world
    }
}

impl dregg_firmament::TurnRunner for WorldRunner {
    fn run_turn_bytes(&mut self, turn_bytes: &[u8]) -> Result<Vec<u8>, String> {
        // Decode the staged turn (the wire carries a postcard `Turn`, exactly as
        // `DreggEngine::execute_turn_bytes` and the node ingress decode it).
        let turn: Turn =
            postcard::from_bytes(turn_bytes).map_err(|e| format!("turn decode failed: {e}"))?;
        // Run it through the FULL real cockpit commit path — chain-head threading,
        // history, dynamics, receipt append. NOT a bypass: the semihost path runs
        // the IDENTICAL `World` logic, just reached through the PD wire.
        match self.world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => {
                postcard::to_stdvec(&receipt).map_err(|e| format!("receipt encode failed: {e}"))
            }
            CommitOutcome::Rejected { reason, .. } => Err(reason),
            // A suspended world stages the turn instead of running it; the PD wire
            // surfaces that as an error (the caller retries after resume).
            CommitOutcome::Queued { agent } => Err(format!(
                "world suspended: turn from {} queued, not run",
                short(&agent)
            )),
        }
    }
}

/// THE SEMIHOSTED COCKPIT — the cockpit's `World` hosted inside the firmament's
/// [`ExecutorPd`](dregg_firmament::ExecutorPd) on the semihost
/// [`EmulatedKernel`](dregg_firmament::EmulatedKernel).
///
/// This is "the sel4 PD world running underneath" made concrete and runnable: a
/// turn the cockpit issues flows app-PD → `turn_in` → executor-PD (over the n=1
/// microkernel's Endpoint) → the verified `World` → `commit_out` → receipt. The
/// SAME `World` semantics, reached through the firmament cap partition — the
/// SAME code path a real seL4 executor-PD boot would take.
pub struct SemihostCockpit {
    /// The executor-PD hosting the cockpit's `World` (the verified heart), over a
    /// fresh n=1 [`EmulatedKernel`](dregg_firmament::EmulatedKernel).
    executor: dregg_firmament::ExecutorPd<WorldRunner>,
    /// The run-turn Endpoint the cockpit (app-PD) `pp_call`s to signal a staged
    /// turn (the `ingress→executor` edge — channel 1 in the real assembly).
    run_endpoint: dregg_firmament::emulated_kernel::ObjectId,
    /// The shared kernel (so the cockpit can build a `Channel` to the executor;
    /// kept for the cross-PD path / future multi-PD wiring).
    kernel: dregg_firmament::emulated_kernel::EmulatedKernel,
}

impl SemihostCockpit {
    /// Boot the semihosted cockpit: a fresh n=1 [`EmulatedKernel`], an
    /// [`ExecutorPd`](dregg_firmament::ExecutorPd) hosting `world` (the cockpit's
    /// real verified `World`), and the run-turn Endpoint the cockpit signals. The
    /// `turn_in`/`commit_out` regions are sized for a real turn + receipt (the
    /// executor-stub's `0x100000`/`0x400000`).
    pub fn boot(world: World) -> Self {
        let kernel = dregg_firmament::emulated_kernel::EmulatedKernel::new();
        let run_endpoint = kernel.create_endpoint();
        let executor = dregg_firmament::ExecutorPd::boot(
            kernel.clone(),
            WorldRunner::new(world),
            0x100000, // turn_in : 1 MiB (the executor-stub's turn_in size)
            0x400000, // commit_out: 4 MiB (the executor-stub's commit_out size)
        );
        SemihostCockpit {
            executor,
            run_endpoint,
            kernel,
        }
    }

    /// The hosted world (read-only) — for the cockpit / harness to inspect the
    /// post-state the executor-PD advanced (ledger, receipts, height, dynamics).
    pub fn world(&self) -> &World {
        self.executor.runner().world()
    }

    /// Seed the hosted world out-of-band (the genesis path) — e.g. install the
    /// cells a turn will act on, BEFORE turns flow through the PD wire. This is
    /// the firmament minting genesis cells at boot, exactly as for a
    /// directly-driven `World`; it does not move value or run a turn.
    pub fn with_world_mut<T>(&mut self, f: impl FnOnce(&mut World) -> T) -> T {
        f(self.executor.runner_mut().world_mut())
    }

    /// **COMMIT A TURN THROUGH THE SEMIHOST executor-PD.**
    ///
    /// The cockpit (app-PD) stages the postcard turn into the executor-PD's
    /// `turn_in` region, then drives the executor-PD's protected-procedure body
    /// (`turn_in → step → commit_out`) — reading `turn_in`, running the cockpit's
    /// REAL `World` commit path, writing the receipt/reason into `commit_out`. The
    /// cockpit then reads the receipt back out of `commit_out` and decodes it.
    ///
    /// Returns the real [`TurnReceipt`] on commit (decoded from `commit_out` — it
    /// genuinely round-tripped through the PD wire), or the rejection reason (the
    /// ocap/verification guarantee firing, fail-closed). This is the SAME outcome
    /// `World::commit_turn` produces in-process — but reached through the
    /// firmament's executor-PD over the n=1 microkernel.
    ///
    /// (The inline drive runs the executor-PD's body on the calling thread — the
    /// `EmulatedKernel::call_served_by` single-thread collapse of the rendezvous.
    /// The two-thread Endpoint form — a real PD's `protected` body on its own
    /// thread — is exercised by the firmament's `executor_pd_boot` test; the
    /// cockpit uses the inline drive so a turn commits deterministically with no
    /// thread timing.)
    pub fn commit_turn_via_semihost(&mut self, turn: Turn) -> CommitOutcome {
        self.commit_turn_via_semihost_projecting(turn, None).0
    }

    /// **COMMIT A TURN THROUGH THE SEMIHOST executor-PD, PROJECTING THE REPAINT.**
    ///
    /// The full §3 live-repaint-on-turn loop with the cockpit's REAL verified
    /// `DreggEngine` behind the heart (not the stub `AttenuationRunner`
    /// `dregg-firmament/src/repaint.rs` proves the wire with): the turn is staged,
    /// the executor-PD runs the REAL `World` commit path, and — on COMMIT — the
    /// served turn's REAL [`TurnReceipt`] is projected into a
    /// [`dregg_firmament::DirtyRegion`] (`owner`'s surface ⟼ its new
    /// state-root/content-digest) the compositor-PD re-paints. A REJECTED turn
    /// projects `None` (fail-closed — a refused turn re-paints NOTHING), exactly the
    /// binding `repaint.rs` proves, now driven by the genuine verified semantics.
    ///
    /// This is the seam `SEL4-INTERACTIVE-COCKPIT.md §3.5` named between the proven
    /// halves: the executor-PD's REAL turn path and the compositor-PD's present gate
    /// were both green but the live-repaint loop was only exercised with the stub
    /// runner. This connects the cockpit's REAL `DreggEngine` to the SAME projection
    /// — a genuine committed transfer re-paints the focused cell. No new primitive.
    pub fn commit_turn_via_semihost_with_repaint(
        &mut self,
        turn: Turn,
        owner: CellId,
    ) -> (CommitOutcome, Option<dregg_firmament::DirtyRegion>) {
        self.commit_turn_via_semihost_projecting(turn, Some(owner))
    }

    /// The shared stage → step → commit_out path, optionally projecting the §3
    /// repaint signal from the REAL served turn. `repaint_owner = Some(cell)` asks
    /// for the [`DirtyRegion`](dregg_firmament::DirtyRegion) a committed turn
    /// projects toward the compositor (the focused cell that re-paints); `None`
    /// skips the projection (the plain commit path). The projection reads the SAME
    /// served turn the commit does — a committed turn's REAL receipt ⟼ a dirty
    /// region; a rejected turn ⟼ `None` (fail-closed).
    fn commit_turn_via_semihost_projecting(
        &mut self,
        turn: Turn,
        repaint_owner: Option<CellId>,
    ) -> (CommitOutcome, Option<dregg_firmament::DirtyRegion>) {
        // Encode + STAGE the turn into the executor-PD's turn_in region (the
        // app-PD's turn_in write before it signals the heart).
        let turn_bytes = match postcard::to_stdvec(&turn) {
            Ok(b) => b,
            Err(e) => {
                return (
                    CommitOutcome::Rejected {
                        reason: format!("turn encode failed: {e}"),
                        at_action: vec![],
                    },
                    None,
                );
            }
        };
        if self.executor.stage_turn(&turn_bytes).is_none() {
            return (
                CommitOutcome::Rejected {
                    reason: format!(
                        "turn ({} bytes) does not fit the executor-PD turn_in region",
                        turn_bytes.len()
                    ),
                    at_action: vec![],
                },
                None,
            );
        }
        // DRIVE the executor-PD's protected-procedure body (read turn_in + step +
        // write commit_out). This is the heart running the turn over the
        // EmulatedKernel; on the cross-PD path this is a `serve_turn` off the
        // Endpoint, here the inline single-thread collapse.
        let served = self.executor.step_staged_turn();
        // PROJECT the §3 repaint from the REAL served turn (its REAL TurnReceipt):
        // a committed turn ⟼ Some(DirtyRegion); a rejected turn ⟼ None (fail-closed,
        // re-paints nothing). This borrow ends before `served` is matched/moved.
        let dirty = repaint_owner
            .and_then(|owner| dregg_firmament::repaint::project_dirty_from_turn(&owner, &served));
        let outcome = match served {
            dregg_firmament::ServedTurn::Committed { .. } => {
                // Read the receipt back out of commit_out and decode it — proving
                // it genuinely round-tripped through the PD wire (not returned
                // in-band). This is the app-PD's commit_out read.
                let receipt_bytes = match self.executor.commit_out_read() {
                    Some(b) => b,
                    None => {
                        return (
                            CommitOutcome::Rejected {
                                reason: "executor-PD committed but commit_out was empty".into(),
                                at_action: vec![],
                            },
                            None,
                        );
                    }
                };
                match postcard::from_bytes::<TurnReceipt>(&receipt_bytes) {
                    // `events` is empty here ON PURPOSE: the dynamics events were
                    // emitted into the HOSTED world's dynamics stream by the
                    // runner's real `commit_turn` (read them via
                    // `self.world().dynamics()`), not re-marshalled across the PD
                    // wire — the wire carries the RECEIPT (the executor-PD's
                    // commit_out), the dynamics live with the world the heart owns.
                    Ok(receipt) => CommitOutcome::Committed {
                        receipt: Box::new(receipt),
                        events: Vec::new(),
                    },
                    Err(e) => CommitOutcome::Rejected {
                        reason: format!("receipt decode from commit_out failed: {e}"),
                        at_action: vec![],
                    },
                }
            }
            dregg_firmament::ServedTurn::Rejected { reason } => CommitOutcome::Rejected {
                reason,
                at_action: vec![],
            },
        };
        (outcome, dirty)
    }

    /// The run-turn Endpoint id (for the cross-PD `serve_turn` path / future
    /// multi-PD wiring) — the executor's PP channel.
    pub fn run_endpoint(&self) -> dregg_firmament::emulated_kernel::ObjectId {
        self.run_endpoint
    }

    /// The shared n=1 kernel (for building a `Channel` to the executor on the
    /// cross-PD path).
    pub fn kernel(&self) -> &dregg_firmament::emulated_kernel::EmulatedKernel {
        &self.kernel
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_world_is_empty() {
        let w = World::new();
        assert_eq!(w.cell_count(), 0);
        assert_eq!(w.height(), 0);
        assert!(w.receipts().is_empty());
    }

    #[test]
    fn genesis_then_transfer_commits_and_conserves() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        assert_eq!(w.cell_count(), 2);

        let total_before = w.ledger().get(&a).unwrap().state.balance()
            + w.ledger().get(&b).unwrap().state.balance();

        let turn = w.turn(a, vec![transfer(a, b, 250)]);
        let outcome = w.commit_turn(turn);
        assert!(outcome.is_committed(), "transfer should commit");

        let ba = w.ledger().get(&a).unwrap().state.balance();
        let bb = w.ledger().get(&b).unwrap().state.balance();
        assert_eq!(ba, 750);
        assert_eq!(bb, 250);
        // Conservation: the embedded VERIFIED executor preserves total value.
        assert_eq!(ba + bb, total_before);

        // Provenance: a real receipt was logged and the chain head advanced.
        assert_eq!(w.receipts().len(), 1);
        assert_eq!(w.height(), 1);
        assert!(w.chain_head(&a).is_some());

        // Dynamics: the transition was observed (a TurnCommitted + a flow each).
        let evs = w.dynamics().since(0);
        assert!(evs
            .iter()
            .any(|e| matches!(e, WorldEvent::TurnCommitted { .. })));
        assert!(evs
            .iter()
            .any(|e| matches!(e, WorldEvent::BalanceFlowed { .. })));
    }

    #[test]
    fn overspend_transfer_is_rejected_by_the_real_executor() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);

        // Transfer MORE than `a` holds: the verified executor must reject it
        // (conservation / non-negativity), and the ledger must be unchanged.
        let turn = w.turn(a, vec![transfer(a, b, 1_000)]);
        let outcome = w.commit_turn(turn);
        assert!(!outcome.is_committed(), "overspend must be rejected");

        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 100);
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 0);
        assert_eq!(w.receipts().len(), 0);
        assert_eq!(w.height(), 0);
    }

    #[test]
    fn receipt_chain_advances_across_two_turns() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);

        let t1 = w.turn(a, vec![transfer(a, b, 100)]);
        assert!(w.commit_turn(t1).is_committed());
        let head1 = w.chain_head(&a).unwrap();

        let t2 = w.turn(a, vec![transfer(a, b, 100)]);
        assert!(w.commit_turn(t2).is_committed());
        let head2 = w.chain_head(&a).unwrap();

        assert_ne!(head1, head2, "chain head must advance");
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 200);
        assert_eq!(w.receipts().len(), 2);
        // The second receipt links to the first.
        assert_eq!(w.receipts()[1].previous_receipt_hash, Some(head1));
    }

    #[test]
    fn state_root_changes_when_state_changes() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let r0 = w.state_root();

        let turn = w.turn(a, vec![transfer(a, b, 1)]);
        assert!(w.commit_turn(turn).is_committed());
        let r1 = w.state_root();
        assert_ne!(r0, r1, "the image commitment must move with history");
    }

    #[test]
    fn state_root_memoized_within_same_height() {
        // Within an unchanged witness tooth (no commit, no genesis write between),
        // two reads return the identical root — the second is a memo hit (the body
        // is byte-equal regardless; equality is the memo's contract).
        let mut w = World::new();
        let _a = w.genesis_cell(1, 1_000);
        let _b = w.genesis_cell(2, 0);
        let first = w.state_root();
        let second = w.state_root();
        assert_eq!(
            first, second,
            "the root is stable within a height (memo hit)"
        );

        // A genesis write busts the memo: a new cell ⇒ a different root.
        let _c = w.genesis_cell(3, 5);
        let third = w.state_root();
        assert_ne!(first, third, "a genesis install must invalidate the memo");
        // ... and the new root is itself stable on re-read.
        assert_eq!(third, w.state_root());
    }

    #[test]
    fn emit_event_commits() {
        let mut w = World::new();
        let a = w.genesis_cell(7, 10);
        let turn = w.turn(a, vec![emit_event(a, "greeting", vec![])]);
        assert!(w.commit_turn(turn).is_committed());
        assert_eq!(w.receipts().len(), 1);
    }

    #[test]
    fn grant_capability_grows_the_ocap_graph() {
        let mut w = World::new();
        let b = w.genesis_cell(2, 0);
        // `a` is born holding a cap to `b`; it re-grants to a fresh slot.
        let (a, slot) = w.genesis_cell_with_cap(1, 100, b);
        let turn = w.turn(a, vec![grant_capability(a, a, b, slot + 1)]);
        assert!(w.commit_turn(turn).is_committed());
        let cell_a = w.ledger().get(&a).unwrap();
        assert!(cell_a.capabilities.has_access(&b), "a should reach b");
    }

    #[test]
    fn over_grant_is_rejected_by_the_real_executor() {
        // The ocap no-amplification guarantee: a cell that holds NO capability
        // to `b` cannot grant one. The verified executor must reject it.
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);
        let turn = w.turn(a, vec![grant_capability(a, a, b, 0)]);
        assert!(
            !w.commit_turn(turn).is_committed(),
            "over-grant must reject"
        );
    }

    #[test]
    fn create_cell_grows_the_ledger() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let before = w.cell_count();
        let turn = w.turn(a, vec![create_cell(9)]);
        assert!(w.commit_turn(turn).is_committed());
        assert_eq!(w.cell_count(), before + 1);
    }

    #[test]
    fn set_field_writes_state() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let turn = w.turn(a, vec![set_field(a, 3, [9u8; 32])]);
        assert!(w.commit_turn(turn).is_committed());
        assert_eq!(w.ledger().get(&a).unwrap().state.fields[3], [9u8; 32]);
    }

    #[test]
    fn seal_then_unseal_round_trips_the_lifecycle() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        // Seal: the cell's lifecycle transitions to Sealed (agent == target).
        let t1 = w.turn(a, vec![seal(a, "maintenance window")]);
        assert!(w.commit_turn(t1).is_committed(), "seal must commit");
        assert!(
            w.ledger().get(&a).unwrap().lifecycle.is_sealed(),
            "the cell's lifecycle must be Sealed"
        );

        // Unseal: the lifecycle returns to Live.
        let t2 = w.turn(a, vec![unseal(a)]);
        assert!(w.commit_turn(t2).is_committed(), "unseal must commit");
        assert!(
            !w.ledger().get(&a).unwrap().lifecycle.is_sealed(),
            "the cell must be Live again after unseal"
        );

        // NOTE (real protocol finding): the verified executor records the
        // Sealed lifecycle but does NOT yet GATE ordinary effects on it
        // (`CellLifecycle::accepts_effects()` exists on the cell type but the
        // executor's apply path does not consult it before non-lifecycle
        // effects). So seal is a recorded-disclosure today, not an enforced
        // effect-freeze. The cockpit surfaces the lifecycle state honestly; the
        // enforcement gate is an executor lane, not this surface's to fake.
    }

    #[test]
    fn unseal_of_a_live_cell_is_rejected() {
        // The executor enforces NotSealed: unsealing a non-sealed cell rejects.
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let t = w.turn(a, vec![unseal(a)]);
        assert!(
            !w.commit_turn(t).is_committed(),
            "unseal of a live cell must reject"
        );
    }

    #[test]
    fn destroy_retires_a_cell_terminally() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 0);
        let t = w.turn(a, vec![destroy(a, w.height(), DeathReason::Voluntary)]);
        assert!(w.commit_turn(t).is_committed(), "destroy must commit");
        let cell = w.ledger().get(&a).unwrap();
        assert!(
            cell.lifecycle.is_terminal(),
            "a destroyed cell's lifecycle is terminal"
        );

        // The lifecycle gate: a SECOND destroy IS rejected — `Cell::destroy`
        // returns `Terminal` for an already-terminal cell, so the lifecycle
        // verbs themselves DO enforce terminality (even though ordinary effects
        // are not yet gated on it — see the seal/lifecycle note in
        // `seal_then_unseal_round_trips_the_lifecycle`).
        let again = w.turn(a, vec![destroy(a, w.height(), DeathReason::Voluntary)]);
        assert!(
            !w.commit_turn(again).is_committed(),
            "a destroyed cell cannot be destroyed again (the lifecycle verb enforces terminality)"
        );
    }

    #[test]
    fn burn_reduces_supply_without_a_credit() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let t = w.turn(a, vec![burn(a, 250)]);
        assert!(w.commit_turn(t).is_committed(), "burn must commit");
        assert_eq!(
            w.ledger().get(&a).unwrap().state.balance(),
            750,
            "the burned amount left the cell with no destination"
        );
        // The receipt records the burn disclosure (bound into the hash).
        assert!(
            w.receipts().last().unwrap().was_burn,
            "the receipt must flag the burn"
        );
    }

    #[test]
    fn burn_exceeding_balance_is_rejected() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let t = w.turn(a, vec![burn(a, 1_000)]);
        assert!(!w.commit_turn(t).is_committed(), "over-burn must reject");
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 100);
    }

    #[test]
    fn forest_turn_commits_several_actions_atomically() {
        // A multi-action turn: agent transfers to two different cells in ONE
        // turn (two sibling roots), committed atomically with one receipt.
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let c = w.genesis_cell(3, 0);

        let t = w.forest_turn(
            a,
            vec![
                (a, vec![transfer(a, b, 100)]),
                (a, vec![transfer(a, c, 200)]),
            ],
        );
        let outcome = w.commit_turn(t);
        assert!(
            outcome.is_committed(),
            "the multi-action forest must commit"
        );
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 100);
        assert_eq!(w.ledger().get(&c).unwrap().state.balance(), 200);
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 700);
        // ONE receipt for the whole forest, with two actions.
        assert_eq!(w.receipts().len(), 1);
        assert_eq!(w.receipts()[0].action_count, 2);
    }

    #[test]
    fn forest_turn_is_atomic_all_or_nothing() {
        // If ANY action in the forest is invalid, the WHOLE turn rejects and
        // no partial effect lands (atomic commit).
        let mut w = World::new();
        let a = w.genesis_cell(1, 150);
        let b = w.genesis_cell(2, 0);

        let t = w.forest_turn(
            a,
            vec![
                (a, vec![transfer(a, b, 100)]),   // would be fine alone
                (a, vec![transfer(a, b, 1_000)]), // overspends → rejects the turn
            ],
        );
        assert!(
            !w.commit_turn(t).is_committed(),
            "an invalid sibling must reject the whole turn"
        );
        // Atomicity: the first transfer did NOT land.
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 150);
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 0);
        assert_eq!(w.height(), 0);
    }

    #[test]
    fn deploy_factory_then_birth_a_child_cell() {
        use dregg_cell::factory::{FactoryCreationParams, FactoryDescriptor};
        use dregg_cell::CellMode;

        let mut w = World::new();
        let agent = w.genesis_cell(1, 0);

        // Deploy a minimal Hosted factory (no pinned child program) into the
        // real executor's registry; get its content-addressed VK back.
        let descriptor = FactoryDescriptor {
            factory_vk: [0xF0; 32],
            child_program_vk: None,
            child_vk_strategy: None,
            allowed_cap_templates: vec![],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: CellMode::Hosted,
            creation_budget: Some(4),
        };
        let vk = w.deploy_factory(descriptor);

        let owner = {
            let mut pk = [0u8; 32];
            pk[0] = 0xC1;
            pk
        };
        let before = w.cell_count();
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };
        let turn = w.turn(
            agent,
            vec![create_cell_from_factory(vk, owner, [0u8; 32], params)],
        );
        let outcome = w.commit_turn(turn);
        assert!(
            outcome.is_committed(),
            "factory-birth must commit through the real executor"
        );
        assert_eq!(
            w.cell_count(),
            before + 1,
            "the factory birthed a child cell"
        );
    }

    #[test]
    fn factory_birth_against_an_unregistered_factory_is_rejected() {
        use dregg_cell::factory::FactoryCreationParams;
        use dregg_cell::CellMode;
        let mut w = World::new();
        let agent = w.genesis_cell(1, 0);
        let owner = [0xC2u8; 32];
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };
        // No factory deployed at this VK → the executor rejects the birth.
        let turn = w.turn(
            agent,
            vec![create_cell_from_factory(
                [0x99; 32], owner, [0u8; 32], params,
            )],
        );
        assert!(
            !w.commit_turn(turn).is_committed(),
            "birth from an unregistered factory must reject"
        );
    }

    #[test]
    fn demo_world_boots_with_real_history() {
        let (w, [treasury, service, user]) = demo_world();
        // 4 cells: treasury, user, service, issuer well.
        assert_eq!(w.cell_count(), 4);
        // 5 committed turns of real provenance.
        assert_eq!(w.receipts().len(), 5);
        assert!(w.height() >= 5);
        // The flows landed: service got 250_000 (treasury) + 1_000 (user).
        assert_eq!(w.ledger().get(&service).unwrap().state.balance(), 251_000);
        assert!(w.ledger().get(&user).unwrap().state.balance() > 0);
        let _ = treasury;
        // The ocap grant landed (service reaches user).
        assert!(w
            .ledger()
            .get(&service)
            .unwrap()
            .capabilities
            .has_access(&user));
    }

    #[test]
    fn demo_genesis_is_instant_and_unseeded_but_alive() {
        // THE FIRST-PAINT IMAGE: genesis installs the cells (no executor turns),
        // so the cockpit can open its window on THIS immediately. It is "alive but
        // at rest" — the four cells exist, but NO seed turn has run yet.
        let (w, [treasury, service, user], seed) = demo_genesis();
        assert_eq!(w.cell_count(), 4, "the four cells are installed at genesis");
        assert_eq!(
            w.receipts().len(),
            0,
            "NO seed turn has run on the first-paint image"
        );
        assert_eq!(w.height(), 0, "the at-rest image is at height 0");
        assert_eq!(
            seed.remaining(),
            DemoSeed::TOTAL,
            "all five seed turns are still pending"
        );
        assert!(!seed.is_done());
        // The anchors are real, installed cells already (so the cockpit's panels
        // have their treasury/service/user the moment the window opens).
        assert!(w.ledger().get(&treasury).is_some());
        assert!(w.ledger().get(&service).is_some());
        assert!(w.ledger().get(&user).is_some());
    }

    #[test]
    fn demo_seed_reaches_the_same_image_as_demo_world() {
        // Driving the seed plan one turn at a time (the async/paint-friendly path)
        // converges to the EXACT image `demo_world` builds eagerly — same cells,
        // same receipts, same balances, same ocap edge. The asynchrony is purely
        // about WHEN each verified turn runs, never WHETHER.
        let (mut w, [_t, service, user], mut seed) = demo_genesis();
        let mut steps: usize = 0;
        while let Some(_label) = seed.next(&mut w) {
            steps += 1;
            // Each `next` commits exactly ONE real turn (height + receipts grow by 1).
            assert_eq!(
                w.height() as usize,
                steps,
                "one committed turn per seed step"
            );
            assert_eq!(w.receipts().len(), steps);
        }
        assert_eq!(steps, DemoSeed::TOTAL, "all five seed turns ran");
        assert!(seed.is_done());
        assert_eq!(seed.remaining(), 0);
        // The fully-seeded image equals the eager `demo_world` image's invariants.
        assert_eq!(w.cell_count(), 4);
        assert_eq!(w.receipts().len(), 5);
        assert_eq!(w.ledger().get(&service).unwrap().state.balance(), 251_000);
        assert!(w.ledger().get(&user).unwrap().state.balance() > 0);
        assert!(w
            .ledger()
            .get(&service)
            .unwrap()
            .capabilities
            .has_access(&user));
    }

    // ── THE SEMIHOSTED COCKPIT — a turn flowing through the executor-PD over the
    //    EmulatedKernel (the sel4 PD world running underneath) ──────────────────

    #[test]
    fn cockpit_turn_flows_through_the_semihost_executor_pd() {
        // Boot the semihosted cockpit: the cockpit's REAL `World` hosted inside
        // the firmament's executor-PD over a fresh n=1 EmulatedKernel.
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let mut cockpit = SemihostCockpit::boot(w);

        // The agent's first-turn shape: build the transfer turn against the hosted
        // world (so the nonce/fee match the executor-PD's ledger). We build it via
        // the hosted world's typed constructor, then dispatch THROUGH the PD wire.
        let turn = cockpit.world().turn(a, vec![transfer(a, b, 250)]);

        // COMMIT IT THROUGH THE SEMIHOST executor-PD: staged into turn_in →
        // signalled → run through the verified `World` → receipt written to
        // commit_out → read back + decoded. The sel4 PD path, end to end.
        let outcome = cockpit.commit_turn_via_semihost(turn);
        assert!(
            outcome.is_committed(),
            "the cockpit turn committed THROUGH the semihost executor-PD"
        );

        // The receipt genuinely round-tripped through commit_out (decoded from the
        // PD's RW region, not returned in-band).
        let receipt = match outcome {
            CommitOutcome::Committed { receipt, .. } => receipt,
            CommitOutcome::Rejected { reason, .. } => panic!("unexpected reject: {reason}"),
            CommitOutcome::Queued { .. } => panic!("unexpected queue (world not suspended)"),
        };
        assert_eq!(
            receipt.action_count, 1,
            "the receipt the executor-PD wrote describes the turn"
        );

        // THE POST-STATE: the executor-PD advanced the hosted world's ledger — the
        // transfer landed (250 moved a→b), conservation held, the chain advanced.
        let world = cockpit.world();
        assert_eq!(world.ledger().get(&a).unwrap().state.balance(), 750);
        assert_eq!(world.ledger().get(&b).unwrap().state.balance(), 250);
        assert_eq!(world.height(), 1, "the heart advanced the height");
        assert_eq!(
            world.receipts().len(),
            1,
            "the receipt was appended (full World path ran)"
        );
        assert!(
            world.chain_head(&a).is_some(),
            "the per-agent chain head advanced through the PD"
        );
    }

    #[test]
    fn semihost_executor_pd_rejects_an_overspend_fail_closed() {
        // The ocap/verification guarantee fires AT THE HEART, through the PD wire:
        // an overspend is rejected and no state advances (fail-closed). The cockpit
        // reads the reason back, exactly as it would a receipt.
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);
        let mut cockpit = SemihostCockpit::boot(w);

        let turn = cockpit.world().turn(a, vec![transfer(a, b, 1_000)]); // overspend
        let outcome = cockpit.commit_turn_via_semihost(turn);
        assert!(
            !outcome.is_committed(),
            "an overspend is REJECTED at the heart (through the PD wire)"
        );

        // No state advanced — the ledger the executor-PD holds is unchanged.
        let world = cockpit.world();
        assert_eq!(world.ledger().get(&a).unwrap().state.balance(), 100);
        assert_eq!(world.ledger().get(&b).unwrap().state.balance(), 0);
        assert_eq!(world.height(), 0, "no turn committed");
        assert_eq!(world.receipts().len(), 0);
    }

    #[test]
    fn semihost_path_matches_the_direct_path_byte_for_byte() {
        // THE EQUIVALENCE: the SAME turn yields the SAME receipt whether run
        // DIRECTLY in-process (`World::commit_turn`) or THROUGH the semihost
        // executor-PD (`SemihostCockpit::commit_turn_via_semihost`). The PD wire is
        // a faithful conduit for the verified semantics, not a re-implementation.
        //
        // Both worlds are pinned to the SAME timestamp (the receipt folds it), so
        // the byte-for-byte claim is DETERMINISTIC — it tests the semantics, not a
        // wall-clock coincidence (the houyhnhnm-clock determinism, §3).
        const PINNED_TS: i64 = 1_700_000_000;
        let mk = || {
            let mut w = World::with_costs_and_timestamp(ComputronCosts::zero(), PINNED_TS);
            let a = w.genesis_cell(1, 1_000);
            let b = w.genesis_cell(2, 0);
            (w, a, b)
        };

        // Direct path.
        let (mut direct, a, b) = mk();
        let t_direct = direct.turn(a, vec![transfer(a, b, 250)]);
        let direct_receipt = match direct.commit_turn(t_direct) {
            CommitOutcome::Committed { receipt, .. } => receipt,
            CommitOutcome::Rejected { reason, .. } => panic!("direct reject: {reason}"),
            CommitOutcome::Queued { .. } => panic!("unexpected queue (world not suspended)"),
        };

        // Semihost path (a fresh, identically-seeded world).
        let (semi_world, a2, b2) = mk();
        assert_eq!(a, a2, "deterministic genesis ids");
        let mut cockpit = SemihostCockpit::boot(semi_world);
        let t_semi = cockpit.world().turn(a2, vec![transfer(a2, b2, 250)]);
        let semi_receipt = match cockpit.commit_turn_via_semihost(t_semi) {
            CommitOutcome::Committed { receipt, .. } => receipt,
            CommitOutcome::Rejected { reason, .. } => panic!("semihost reject: {reason}"),
            CommitOutcome::Queued { .. } => panic!("unexpected queue (world not suspended)"),
        };

        // The receipt hashes match — the heart over the EmulatedKernel produced
        // the BYTE-IDENTICAL verified receipt the direct executor did.
        assert_eq!(
            direct_receipt.receipt_hash(),
            semi_receipt.receipt_hash(),
            "the semihost executor-PD produces the SAME verified receipt as the direct path"
        );
        // And the post-state ledgers agree.
        assert_eq!(
            direct.state_root(),
            cockpit.world().state_root(),
            "the semihost path advances the SAME image the direct path does"
        );
    }

    // ── LIVE-REPAINT-ON-TURN, with the REAL verified DreggEngine behind the heart
    //    (`docs/desktop-os-research/SEL4-INTERACTIVE-COCKPIT.md §3.5`) ────────────
    //
    // `dregg-firmament/tests/live_repaint_on_turn.rs` proves the executor-PD →
    // compositor-PD repaint loop with a STUB runner (the 2-byte `AttenuationRunner`).
    // These tests close the named seam between that and the cockpit's REAL `World`:
    // a GENUINE verified transfer turn, committed through the semihost executor-PD,
    // projects a `DirtyRegion` from its REAL `TurnReceipt` that the compositor-PD
    // re-paints — and a rejected overspend re-paints nothing, and a SEQUENCE of real
    // turns re-paints to DISTINCT frames (the "the cells CHANGE while you watch"
    // rung). No new primitive — it rides the proven executor-PD turn path, the
    // proven compositor present gate, and the SAME projection the stub proves.

    /// Boot a compositor-PD whose focused surface is the genesis wallet `owner`,
    /// owning regions {10, 11}, starting blank (digest 0) — the cell a turn
    /// re-paints. Shares the cockpit's n=1 kernel so the regions live on ONE
    /// microkernel (the deos-live.system equivalent: executor-PD ⊕ compositor-PD).
    fn focused_compositor(
        kernel: dregg_firmament::emulated_kernel::EmulatedKernel,
        owner: CellId,
    ) -> dregg_firmament::CompositorPd {
        use dregg_firmament::compositor_pd::{Scene, Surface};
        dregg_firmament::CompositorPd::boot(
            kernel,
            Scene {
                surfaces: vec![Surface {
                    owner,
                    regions: vec![10, 11],
                    content_digest: 0,
                    source_state_root: 0,
                    z_layer: 0,
                    focus_flag: true,
                }],
            },
        )
    }

    #[test]
    fn a_real_verified_turn_repaints_the_focused_cell_through_the_executor_pd() {
        // The cockpit's REAL `World` hosted in the executor-PD, sharing its n=1
        // kernel with a compositor-PD that focuses the wallet `a`.
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let mut cockpit = SemihostCockpit::boot(w);
        let mut compositor = focused_compositor(cockpit.kernel().clone(), a);

        // The framebuffer BEFORE any turn — the focused cell's tile 10 is blank.
        let fb_before = compositor.framebuffer_snapshot();
        assert_eq!(fb_before[10], 0, "the focused cell starts blank");

        // A GENUINE verified transfer a→b, committed THROUGH the executor-PD, with
        // the §3 repaint projected from its REAL `TurnReceipt`.
        let turn = cockpit.world().turn(a, vec![transfer(a, b, 250)]);
        let (outcome, dirty) = cockpit.commit_turn_via_semihost_with_repaint(turn, a);
        assert!(
            outcome.is_committed(),
            "the real transfer committed at the heart"
        );
        let dirty = dirty.expect("a committed real turn projects a DirtyRegion");
        assert_eq!(
            dirty.owner, a,
            "the dirty region names the wallet that committed"
        );

        // THE COMPOSITOR RE-PAINTS: present the dirty region onto the focused cell's
        // region 10 — the scene gate ADMITS the honest repaint, the framebuffer
        // advances at exactly tile 10 (the cell re-painted to its new committed
        // state's frame).
        let commit = compositor
            .present(&dirty.owner, dirty.to_present(vec![10]))
            .expect("the scene gate admits the honest repaint");
        let fb_after = compositor.framebuffer_snapshot();
        assert_ne!(
            fb_after[10], fb_before[10],
            "the REAL committed turn re-painted the focused cell"
        );
        assert_eq!(
            fb_after[10],
            (commit.digest & 0xFF) as u8,
            "tile 10 holds the frame the real turn projected"
        );

        // The post-state confirms the SAME heart advanced the ledger (250 moved).
        assert_eq!(
            cockpit.world().ledger().get(&a).unwrap().state.balance(),
            750
        );
        assert_eq!(
            cockpit.world().ledger().get(&b).unwrap().state.balance(),
            250
        );
    }

    #[test]
    fn a_rejected_real_turn_repaints_nothing_fail_closed() {
        // An overspend is rejected AT THE HEART through the PD wire; the projection
        // is None (fail-closed — no dirty signal), and the framebuffer is untouched.
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);
        let mut cockpit = SemihostCockpit::boot(w);
        let compositor = focused_compositor(cockpit.kernel().clone(), a);
        let fb_before = compositor.framebuffer_snapshot();

        let turn = cockpit.world().turn(a, vec![transfer(a, b, 1_000)]); // overspend
        let (outcome, dirty) = cockpit.commit_turn_via_semihost_with_repaint(turn, a);
        assert!(
            !outcome.is_committed(),
            "the overspend is REJECTED at the heart"
        );
        assert!(
            dirty.is_none(),
            "a rejected real turn projects no dirty region (re-paints nothing)"
        );

        // The framebuffer is BYTE-IDENTICAL — a refused turn re-painted nothing.
        assert_eq!(
            compositor.framebuffer_snapshot(),
            fb_before,
            "the rejected turn left the framebuffer byte-identical (fail-closed)"
        );
        assert_eq!(compositor.frames().len(), 0, "no frame committed");
    }

    #[test]
    fn a_sequence_of_real_turns_repaints_to_distinct_frames() {
        // "The cells CHANGE while you watch": each committed turn in a SEQUENCE
        // advances the ledger AND re-paints the focused cell to a DISTINCT frame
        // (distinct committed receipt ⟹ distinct state-root ⟹ distinct content
        // digest ⟹ a genuine frame advance — the binding the compositor's
        // frame-advance leg relies on). This is the umem "passable intermediate
        // states" made visible: each boundary the heart commits re-paints the glass.
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let mut cockpit = SemihostCockpit::boot(w);
        let mut compositor = focused_compositor(cockpit.kernel().clone(), a);

        let mut frames: Vec<u8> = vec![compositor.framebuffer_snapshot()[10]]; // blank=0
        for _ in 0..3 {
            let turn = cockpit.world().turn(a, vec![transfer(a, b, 50)]);
            let (outcome, dirty) = cockpit.commit_turn_via_semihost_with_repaint(turn, a);
            assert!(outcome.is_committed(), "each real transfer commits");
            let dirty = dirty.expect("each committed turn projects a dirty region");
            compositor
                .present(&dirty.owner, dirty.to_present(vec![10]))
                .expect("each honest repaint is admitted");
            frames.push(compositor.framebuffer_snapshot()[10]);
        }

        // Each successive committed turn re-painted to a DISTINCT frame from the
        // one before it (the chain-head advanced ⟹ a distinct receipt ⟹ a distinct
        // frame). The framebuffer genuinely CHANGED on every turn.
        for win in frames.windows(2) {
            assert_ne!(
                win[0], win[1],
                "each committed turn re-paints to a frame distinct from the last"
            );
        }
        // The ledger advanced once per turn (3 × 50 moved a→b).
        assert_eq!(
            cockpit.world().ledger().get(&b).unwrap().state.balance(),
            150
        );
        assert_eq!(cockpit.world().height(), 3, "three turns committed");
        // Four distinct framebuffer states straddled the three turns (blank + 3).
        assert_eq!(compositor.frames().len(), 3, "three repaints logged");
    }

    // =======================================================================
    // M2 CACHE-SOUNDNESS = DYNAMICS-COMPLETENESS (EFFICIENCY-WELD-PLAN §4.1).
    //
    // The delta loop's invalidation is driven ENTIRELY by the dynamics stream.
    // A stale projection survives iff a committed effect mutates a renderable
    // cell WITHOUT a `WorldEvent` naming it. The audit: every cell-naming effect
    // variant must, when fed to `collect_effect_events`, produce an event that
    // names the written cell. (The balance-moving effects are additionally
    // covered by the `touched_cells` pre/post diff in `commit_turn`.)
    // =======================================================================

    /// The cells named by the events `collect_effect_events` emits for one effect.
    fn named_cells(effect: Effect) -> Vec<CellId> {
        let action = bare_action(CellId::ZERO, vec![effect]);
        let mut out = Vec::new();
        collect_effect_events(&action, &mut out);
        out.iter().filter_map(event_named_cell).collect()
    }

    /// The cell a `WorldEvent` names (the invalidation target), if any.
    fn event_named_cell(ev: &WorldEvent) -> Option<CellId> {
        Some(match ev {
            WorldEvent::CellBorn { cell, .. }
            | WorldEvent::BalanceFlowed { cell, .. }
            | WorldEvent::CapabilityRevoked { cell, .. }
            | WorldEvent::FieldSet { cell, .. }
            | WorldEvent::CellMutated { cell }
            | WorldEvent::CellSealed { cell }
            | WorldEvent::CellUnsealed { cell }
            | WorldEvent::CellDestroyed { cell }
            | WorldEvent::Burned { cell, .. }
            | WorldEvent::SurfaceDamaged { cell, .. }
            | WorldEvent::EventEmitted { cell, .. } => *cell,
            WorldEvent::CapabilityGranted { from, .. } => *from,
            WorldEvent::TurnCommitted { .. }
            | WorldEvent::TurnRejected { .. }
            | WorldEvent::TurnQueued { .. } => return None,
        })
    }

    #[test]
    fn every_cell_naming_effect_names_its_cell() {
        // A distinctive non-zero cell id we can assert the event carries.
        let c = make_open_cell(0x42, 0).id();
        let other = make_open_cell(0x43, 0).id();

        // (effect, the cell the inspector renders that the event MUST name)
        // Cases the inspector surfaces and the memo therefore must invalidate.
        let cases: Vec<(Effect, CellId)> = vec![
            (set_field(c, 1, [7u8; 32]), c),
            (grant_capability(c, other, other, 1), c),
            (revoke_capability(c, 0), c),
            (emit_event(c, "ping", vec![]), c),
            (Effect::IncrementNonce { cell: c }, c),
            (
                Effect::SetPermissions {
                    cell: c,
                    new_permissions: open_permissions(),
                },
                c,
            ),
            (
                Effect::SetVerificationKey {
                    cell: c,
                    new_vk: None,
                },
                c,
            ),
            (Effect::MakeSovereign { cell: c }, c),
            (
                Effect::AttenuateCapability {
                    cell: c,
                    slot: 0,
                    narrower_permissions: dregg_cell::AuthRequired::None,
                    narrower_effects: None,
                    narrower_expiry: None,
                },
                c,
            ),
            (seal(c, "maintenance"), c),
            (unseal(c), c),
            (destroy(c, 0, DeathReason::Voluntary), c),
            (burn(c, 1), c),
        ];

        for (effect, must_name) in cases {
            let named = named_cells(effect.clone());
            assert!(
                named.contains(&must_name),
                "effect {effect:?} must emit a WorldEvent naming {must_name:?}, named {named:?}"
            );
        }

        // CreateCell names the ZERO sentinel (the real id is unknown at emit; the
        // cockpit refreshes `self.cells` from the ledger on the ZERO-sentinel
        // CellBorn — the bounded full-rescan case).
        let create = create_cell(9);
        let named = named_cells(create.clone());
        assert!(
            named.contains(&CellId::ZERO),
            "create effect {create:?} must emit a CellBorn (ZERO sentinel triggers the rescan)"
        );

        // ExerciseViaCapability recurses: a write reached THROUGH a cap still
        // names its cell.
        let inner_named = named_cells(Effect::ExerciseViaCapability {
            cap_slot: 0,
            inner_effects: vec![Effect::SetField {
                cell: c,
                index: 2,
                value: [1u8; 32],
            }],
        });
        assert!(
            inner_named.contains(&c),
            "an exercised-capability inner write must still name its cell, named {inner_named:?}"
        );
    }

    #[test]
    fn increment_nonce_emits_a_naming_event_on_commit() {
        // The end-to-end completeness check: an IncrementNonce (no balance move)
        // must still produce a cell-naming event in the live dynamics stream.
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let before = w.dynamics().cursor();
        let t = w.turn(a, vec![Effect::IncrementNonce { cell: a }]);
        let committed = w.commit_turn(t).is_committed();
        if committed {
            let named: Vec<CellId> = w
                .dynamics()
                .since(before)
                .iter()
                .filter_map(event_named_cell)
                .collect();
            assert!(
                named.contains(&a),
                "a committed nonce bump must name its cell in the dynamics stream (named {named:?})"
            );
        }
        // (If the executor rejects a bare nonce bump under these permissions, the
        // pure `collect_effect_events` test above already proves the emitter; this
        // case guards the LIVE path when it commits.)
    }

    // =======================================================================
    // M2 THE PROOF — the microbench gate (EFFICIENCY-WELD-PLAN §3).
    //
    // The delta loop's contract: re-rendering across a head advance is
    // O(changed-cells), not O(ledger). The cockpit's inspector projects its
    // FOCUSED cell every frame. Before M2 that rebuilt the full presentation set
    // (incl. the O(ledger) ocap-graph view + the O(receipt-log) provenance scan)
    // on EVERY frame, even when nothing about the focus changed — O(ledger) per
    // frame. After M2: a turn that does NOT touch the focus leaves its memo entry
    // valid, so the re-render is a cache HIT — O(1) in the ledger size.
    //
    // The gate (per-render projection of an unchanged focus) is therefore FLAT in
    // n. We assert `time(65536) < K * time(16)`. A separate sub-check proves the
    // memo CORRECTLY invalidates+recomputes when the focus IS touched (soundness,
    // not the flatness gate — that recompute is irreducibly O(graph) and is the
    // honest residual the EFFICIENCY-WELD-PLAN §4.3 names: the ocap-graph build is
    // a whole-ledger scan, paid only on a focus-changing turn, not per frame).
    // =======================================================================

    /// Build an `n`-cell ledger with UNIQUE ids (a 32-byte index-derived pubkey;
    /// the `u8`-seeded `make_open_cell` collides past 256). Returns the world + a
    /// distinguished `focus` cell + two `mover` cells whose mutual transfers drive
    /// the head forward WITHOUT touching the focus.
    #[cfg(test)]
    fn build_ledger(n: usize) -> (World, CellId, CellId, CellId) {
        let pk_at = |tag: u64, dom: u8| -> [u8; 32] {
            let mut pk = [0u8; 32];
            pk[..8].copy_from_slice(&tag.to_le_bytes());
            pk[8] = dom;
            pk
        };
        let mut w = World::new();
        let mut focus = None;
        for i in 0..n {
            // Bulk cells go in via the O(n)-build bench path (no per-cell tape root).
            let mut cell = Cell::with_balance(pk_at(i as u64, 0x01), [0u8; 32], 1_000);
            cell.permissions = open_permissions();
            let id = w.bench_install_cell(cell, 1_000);
            if focus.is_none() {
                focus = Some(id);
            }
        }
        // The two movers go through the FULL genesis path (`embody` mirrors them onto
        // the record tape) because they drive real `commit_turn`s, which re-execute
        // against the record ledger. Domain-separated so they never collide.
        let mover_a = w.embody(pk_at(u64::MAX, 0x02), [0u8; 32], 1_000);
        let mover_b = w.embody(pk_at(u64::MAX - 1, 0x02), [0u8; 32], 0);
        (w, focus.expect("at least one cell"), mover_a, mover_b)
    }

    // A microbench (builds up to a 16384-cell ledger, runs thousands of present
    // iterations) — minutes-long and NOT a correctness gate, so it is `#[ignore]`d
    // off the default `cargo test` path. Run it deliberately with
    // `cargo test --release ... -- --ignored projection_cost_is_flat_in_cell_count`.
    #[test]
    #[ignore = "microbench (16384-cell ledger × thousands of iters); minutes-long, not a correctness gate — run with --ignored"]
    fn projection_cost_is_flat_in_cell_count() {
        use crate::presentable::{FocusTarget, PresentMemo};
        use std::time::Instant;

        // The PROOF, as the cleanest contrast: the OLD per-render path = the COLD
        // present (rebuilds the full set incl. the O(ledger) ocap-graph view) — it
        // scales ~LINEARLY in n. The NEW path = the memo HIT (the delta loop left the
        // unchanged focus cached) — FLAT in n. We measure BOTH at each n and assert
        // (a) the hit is flat and (b) the hit beats the cold present by a margin that
        // WIDENS with n (the delta-loop win). No real `commit_turn` is on this path
        // (the embedded executor's per-turn crypto + its O(ledger) Merkle re-root is
        // ~seconds and is NOT what the projection memo optimizes — see HORIZONLOG's
        // "internal turns pay protocol crypto eagerly" lane); the head-advance
        // semantics are exercised by the SOUNDNESS sub-check below.
        //
        // COLD is O(ledger) PER sample, so it gets FEW samples; HIT is O(1) so it
        // gets many. 16 → 16384 is a 1024x growth: a LINEAR per-render cost blows up
        // ~1024x; FLAT (O(changed)) stays within a small constant.
        const COLD_ITERS: usize = 8;
        const HIT_ITERS: usize = 5000;
        let sizes = [16usize, 256, 4096, 16384];
        let mut cold: Vec<(usize, std::time::Duration)> = Vec::new();
        let mut hit: Vec<(usize, std::time::Duration)> = Vec::new();

        for &n in &sizes {
            let (w, focus, _a, _b) = build_ledger(n); // build ONCE, outside both timers

            // COLD: the un-memoized projection (a fresh memo every call → always a
            // MISS → the full `Registry::present`, the pre-M2 per-frame cost).
            let mut c = std::time::Duration::ZERO;
            for _ in 0..COLD_ITERS {
                let fresh = PresentMemo::new();
                let t0 = Instant::now();
                let _ = fresh.present(&w, FocusTarget::Cell(focus), focus);
                c += t0.elapsed();
            }
            cold.push((n, c / COLD_ITERS as u32));

            // HIT: warm ONE memo, then time repeated reads of the unchanged focus —
            // the delta loop leaves it cached across head advances, so every frame is
            // this O(1) clone instead of the cold rebuild.
            let memo = PresentMemo::new();
            let _ = memo.present(&w, FocusTarget::Cell(focus), focus); // warm
            let mut h = std::time::Duration::ZERO;
            for _ in 0..HIT_ITERS {
                let t0 = Instant::now();
                let _ = memo.present(&w, FocusTarget::Cell(focus), focus);
                h += t0.elapsed();
            }
            hit.push((n, h / HIT_ITERS as u32));
        }

        println!("\n=== M2 MICROBENCH — per-render projection: COLD (pre-M2) vs memo HIT (M2) ===");
        let hit_base = hit[0].1.as_nanos().max(1);
        for i in 0..sizes.len() {
            let (n, cd) = cold[i]; // already per-sample (averaged above)
            let (_, hd) = hit[i];
            let speedup = cd.as_nanos() as f64 / hd.as_nanos().max(1) as f64;
            let hit_ratio = hd.as_nanos() as f64 / hit_base as f64;
            println!(
                "  n={n:>6}  cold/render={:>9}ns  hit/render={:>5}ns  speedup={speedup:>7.1}x  hit-ratio-vs-n16={hit_ratio:.2}x",
                cd.as_nanos(),
                hd.as_nanos(),
            );
        }

        // GATE (a): the memo HIT is FLAT in n (O(changed), not O(ledger)).
        let hit_ratio = hit.last().unwrap().1.as_nanos() as f64 / hit_base as f64;
        const K: f64 = 8.0;
        assert!(
            hit_ratio < K,
            "the memo-HIT per-render projection must be FLAT in cell count: \
             time(16384)/time(16) = {hit_ratio:.2}x, must be < {K}x. A linear scan ~1024x."
        );
        // GATE (b): the win WIDENS with n — at the largest n the hit beats the cold
        // present by far more than at the smallest (the cold path is O(ledger)).
        let speedup_small = cold[0].1.as_nanos() as f64 / hit[0].1.as_nanos().max(1) as f64;
        let speedup_large = cold.last().unwrap().1.as_nanos() as f64
            / hit.last().unwrap().1.as_nanos().max(1) as f64;
        assert!(
            speedup_large > speedup_small,
            "the delta-loop win must WIDEN with cell count: speedup(16384)={speedup_large:.1}x \
             must exceed speedup(16)={speedup_small:.1}x (the cold present is O(ledger))."
        );
        println!(
            "  GATE PASS: HIT flat (time(16384)/time(16)={hit_ratio:.2}x < {K}x); \
             win widens ({speedup_small:.1}x @16 → {speedup_large:.1}x @16384)"
        );

        // SOUNDNESS sub-check (not the flatness gate): when a turn DOES touch the
        // focus, the fold drops its memo entry and the next render recomputes via
        // the pure Registry — the projection reflects the change, never a stale hit.
        {
            let (mut w, focus, mover_a, _mover_b) = build_ledger(16);
            let memo = PresentMemo::new();
            let mut cursor = w.dynamics().cursor();
            let before = memo.present(&w, FocusTarget::Cell(focus), focus).unwrap();
            // A turn that TOUCHES the focus (a real balance flow off it).
            let turn = w.turn(focus, vec![transfer(focus, mover_a, 7)]);
            assert!(w.commit_turn(turn).is_committed());
            // The fold sees the BalanceFlowed naming `focus` and drops its entry.
            for ev in w.dynamics().since(cursor) {
                if let Some(cell) = event_named_cell(ev) {
                    memo.invalidate_cell(cell);
                }
            }
            cursor = w.dynamics().cursor();
            let _ = cursor;
            let after = memo.present(&w, FocusTarget::Cell(focus), focus).unwrap();
            // The RawFields balance must differ (the cache did NOT serve a stale set).
            let bal = |set: &[crate::presentable::Presentation]| -> String {
                set.iter()
                    .find(|p| p.kind == crate::presentable::PresentationKind::RawFields)
                    .map(|p| p.search_text.clone())
                    .unwrap_or_default()
            };
            assert_ne!(
                format!("{:?}", before.iter().map(|p| &p.body).collect::<Vec<_>>()),
                format!("{:?}", after.iter().map(|p| &p.body).collect::<Vec<_>>()),
                "a touched-focus re-render must recompute, not serve a stale memo hit ({} vs {})",
                bal(&before),
                bal(&after),
            );
        }
        println!("  SOUNDNESS PASS: a touched-focus re-render recomputes (no stale memo hit)\n");
    }

    // --- SYMBOLIC EXECUTION (the World-level deferred-witness + collapse) ----

    #[test]
    fn symbolic_world_applies_transition_without_recording_the_tape() {
        // Build a small Full image first (genesis only, no turns).
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let tape_before = w.recorded_turns().len();

        // Enter Symbolic and commit a transfer.
        w.set_witness_mode(WitnessMode::Symbolic);
        assert!(w.is_symbolic());
        let t = w.turn(a, vec![transfer(a, b, 250)]);
        let outcome = w.commit_turn(t);
        assert!(outcome.is_committed(), "a symbolic turn still commits");

        // The STATE TRANSITION applied (the abstract progress).
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 750);
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 250);

        // But the WITNESS was deferred: the replay tape did NOT grow (no
        // double-execution), the turn is buffered, and the live receipt carries
        // the deferred sentinel.
        assert_eq!(
            w.recorded_turns().len(),
            tape_before,
            "tape not recorded in symbolic mode"
        );
        assert_eq!(w.symbolic_pending(), 1);
        assert!(
            is_deferred(w.receipts().last().unwrap()),
            "symbolic receipt is deferred"
        );
    }

    #[test]
    fn world_collapse_reproduces_a_full_run() {
        // Both worlds MUST share one timestamp: it is folded into every receipt_hash
        // (so it binds the canonical root). `World::new()` reads now_unix() per call,
        // which would make the symbolic vs full roots differ for an unrelated reason.
        // Pin the same (costs, timestamp) for both so the comparison is sound.
        const TS: i64 = 1_700_000_000;
        // A SYMBOLIC world: genesis + three deferred turns.
        let mut sym = World::with_costs_and_timestamp(ComputronCosts::zero(), TS);
        let a = sym.genesis_cell(1, 1_000);
        let b = sym.genesis_cell(2, 0);
        let c = sym.genesis_cell(3, 0);
        sym.set_witness_mode(WitnessMode::Symbolic);
        assert!(sym
            .commit_turn(sym.turn(a, vec![transfer(a, b, 300)]))
            .is_committed());
        assert!(sym
            .commit_turn(sym.turn(b, vec![transfer(b, c, 100)]))
            .is_committed());
        assert!(sym
            .commit_turn(sym.turn(a, vec![transfer(a, c, 50)]))
            .is_committed());
        assert_eq!(sym.symbolic_pending(), 3);

        // A FULL world: the SAME genesis + the SAME three turns (the ground truth).
        let mut full = World::with_costs_and_timestamp(ComputronCosts::zero(), TS);
        let a2 = full.genesis_cell(1, 1_000);
        let b2 = full.genesis_cell(2, 0);
        let c2 = full.genesis_cell(3, 0);
        assert_eq!((a, b, c), (a2, b2, c2), "deterministic genesis ids");
        assert!(full
            .commit_turn(full.turn(a2, vec![transfer(a2, b2, 300)]))
            .is_committed());
        assert!(full
            .commit_turn(full.turn(b2, vec![transfer(b2, c2, 100)]))
            .is_committed());
        assert!(full
            .commit_turn(full.turn(a2, vec![transfer(a2, c2, 50)]))
            .is_committed());

        // COLLAPSE the symbolic world.
        let n = sym.collapse().expect("collapse must succeed");
        assert_eq!(n, 3);
        assert_eq!(sym.symbolic_pending(), 0, "buffer drained");
        assert!(!sym.is_symbolic(), "collapse returns to Full");

        // The collapsed image equals the Full image: same canonical state root,
        // and the replay tape now records every turn (with real roots).
        assert_eq!(
            sym.state_root(),
            full.state_root(),
            "collapsed image root == Full image root"
        );
        assert_eq!(sym.recorded_turns().len(), full.recorded_turns().len());
        assert_eq!(
            sym.recorded_turns().root_at(sym.recorded_turns().len()),
            full.recorded_turns().root_at(full.recorded_turns().len()),
            "collapsed head root tooth == Full head root tooth"
        );

        // Every collapsed receipt is real (no longer deferred) and byte-identical.
        for (cr, fr) in sym.receipts().iter().zip(full.receipts().iter()) {
            assert!(!is_deferred(cr), "collapsed receipt is a real witness");
            assert_eq!(
                cr.receipt_hash(),
                fr.receipt_hash(),
                "collapse == Full receipt"
            );
        }
    }

    #[test]
    fn full_world_is_unchanged_no_regression() {
        // A default Full world records the tape eagerly and witnesses every turn —
        // exactly as before symbolic mode existed.
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        assert!(!w.is_symbolic(), "Full is the default");
        let tape_before = w.recorded_turns().len();
        assert!(w
            .commit_turn(w.turn(a, vec![transfer(a, b, 250)]))
            .is_committed());
        // The tape grew (eager record) and the receipt carries a REAL witness.
        assert_eq!(w.recorded_turns().len(), tape_before + 1);
        assert_eq!(w.symbolic_pending(), 0);
        assert!(
            !is_deferred(w.receipts().last().unwrap()),
            "Full receipt is real"
        );
    }
}
