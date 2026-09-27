//! `dregg-lean-ffi` library — marshal codec + optional Lean kernel shadow execution.
//!
//! When `libdregg_lean.a` is present at build time (`cfg(lean_lib_present)`), the crate
//! links the verified Lean kernel and exposes `shadow_exec_full_forest_auth`. When the
//! archive is absent the crate still builds (marshal-only); `lean_available()` is false.

#[path = "marshal.rs"]
pub mod marshal;

/// THE NO-COPY (`lean_object*`) boundary — construct/read the Lean inductives directly across the
/// FFI, no JSON serialize/parse in either direction (the JSON path in `marshal` is the oracle).
#[path = "lean_direct.rs"]
pub mod lean_direct;

pub use lean_direct::{
    direct_available, identity_floor_median, shadow_exec_direct, shadow_exec_direct_profiled,
    WireTurnHdr,
};

/// The VERIFIED DISTRIBUTED exports (federation strand-admission, etc.) — kept in a module distinct
/// from the executor-facing marshal/lib plumbing.
#[path = "distributed_ffi.rs"]
pub mod distributed_ffi;

pub use distributed_ffi::{
    ack_admit_available, decode_tau_order, distributed_exports_available, round_advance_available,
    shadow_ack_admit, shadow_captp_pipeline_resolve, shadow_captp_process_drop,
    shadow_captp_validate_handoff, shadow_coord_2pc_decide, shadow_coord_causal_order,
    shadow_coord_shared_budget, shadow_round_advance, shadow_strand_admit, shadow_tau_order,
    strand_admit_available, tau_order_available, verified_2pc_decide, verified_admits,
    verified_handoff_non_amplifying, verified_happened_before, verified_tau_order, Decision2pc,
};

/// The VERIFIED LIGHT-CLIENT verify-logic gates (ETH sync-committee / Tendermint stake-weighted /
/// EVM state-inclusion) — the foreign-chain admission decisions the interchain bridge routes
/// through, sibling to `distributed_ffi` above.
///
/// ⚠ THIS `mod` LINE IS LOAD-BEARING AND WAS MISSING. `bridge_lc_ffi.rs` existed on disk, fully
/// written and documented, referenced by NO `mod` declaration and no `[[bin]]` — so rustc never
/// compiled a byte of it. That is a strictly WORSE failure than the `#[cfg]` holes it sat behind:
/// a cfg-gated module at least compiles its absent arm, whereas an undeclared file has no arms at
/// all, `cargo test` reports the surviving tests green, and `eth_lc_verify_available()` is not
/// merely false — it does not exist. Four independent layers had to be closed for this gate to
/// bite (archive facet, `cfg`, C `_str` shim, and this line); each one alone kept the ETH relayer
/// un-gated, and none announced itself.
#[path = "bridge_lc_ffi.rs"]
pub mod bridge_lc_ffi;

/// Internal Path of Angels evaluator boundary. This module transports a complete canonical Signal
/// state through the Lean judge; it does not authenticate caller-authored carrier/state and is not
/// a public node-authority adapter.
#[path = "poa_ffi.rs"]
pub mod poa_ffi;

/// Lean-owned per-run instance derivation (slot commitment, live run seed, target).
/// The judge re-derives all three and refuses on mismatch, which is only a check if
/// the node derived them independently — so the node derives, and it derives HERE,
/// by calling Lean. There is no Rust sponge.
#[path = "poa_slot_derive_ffi.rs"]
pub mod poa_slot_derive_ffi;

/// Lean-owned mid-run LOCKED/DRIFT classification for judged Signal. The rule is
/// `SignalTriangulation.feedback` — the same function that decides whether a transcript
/// settles — so it is not re-typed in Rust. The reply is two counts and nothing else,
/// which is what makes this the one PoA export whose answer may reach a route.
#[path = "poa_signal_feedback_ffi.rs"]
pub mod poa_signal_feedback_ffi;

/// Lean-owned bounded first-head ceremony. The host transports the exact emitted config/Canon
/// bytes and does not reconstruct or persist them in this crate.
#[path = "poa_network_genesis_ffi.rs"]
pub mod poa_network_genesis_ffi;

/// Lean-owned Path of Angels Records read model: the finalized-run projection rebuilt from the
/// retained genesis blobs and the durable finalized rows. Rust transports the request and serves
/// the emitted view verbatim; there is no host-side record projection.
#[path = "poa_records_ffi.rs"]
pub mod poa_records_ffi;

/// Lean-owned Path of Angels station daily READ: the communal ship instrument panel and the
/// crate's curator-authored VISIBLE rotation. Rust transports the request and serves the emitted
/// document verbatim; there is no host-side projection, and none is possible — the crate's
/// receipt and result constructors are private precisely so that only an accepted opening can
/// move a gauge. Read-only because ITS REQUEST CARRIES NO OPEN HISTORY, not because writing is
/// unreachable — see `poa_crate_open_ffi` below, which is the write.
#[path = "poa_station_daily_ffi.rs"]
pub mod poa_station_daily_ffi;

/// Lean-owned Path of Angels station crate OPEN: the daily ritual's only write path. Rust
/// transports the authenticated opener's key plus the node's durable open log and serves the
/// emitted document verbatim; Lean replays the log from `SalvageCrate.genesis` under the
/// capability chain, appends the open, and folds the crate's own sealed receipt into the communal
/// panel. There is no host-side write and none is possible — `OpenResult`, `OpenReceipt`,
/// `Receipt` and `CurrentStateCapability` all have private constructors.
#[path = "poa_crate_open_ffi.rs"]
pub mod poa_crate_open_ffi;

/// Lean-owned bounded private batch-settlement evaluator. Rust transports the
/// canonical wire and has no settlement/authorization fallback.
#[path = "poa_dark_bazaar_ffi.rs"]
pub mod poa_dark_bazaar_ffi;

/// Lean-owned, replay-first Galley daily evaluator. Public play and the server-sealed holder
/// sponsor ingress are distinct exports; both refuse rather than fall back to Rust semantics.
#[path = "poa_galley_ffi.rs"]
pub mod poa_galley_ffi;

/// Lean-owned Night Watch campaign judge. Takes no authority argument: the rulebook is
/// what the audited world's content root commits to, never a caller's claim. ⚠ Its input
/// wire carries the node-held slot secret and must never be echoed.
#[path = "poa_night_watch_ffi.rs"]
pub mod poa_night_watch_ffi;

/// Lean-owned post-finality planner for atomic, replayable Path of Angels event batches.
#[path = "poa_event_batch_ffi.rs"]
pub mod poa_event_batch_ffi;

/// Lean-owned signed active-world lineage and exact EventBatch world selector.
#[path = "poa_world_activation_ffi.rs"]
pub mod poa_world_activation_ffi;

/// Lean-owned exact activated-content manifest and named Galley-policy membership authority.
#[path = "poa_activated_content_ffi.rs"]
pub mod poa_activated_content_ffi;

/// Exact-byte durable restart/CAS substrate for the Lean-owned PoA Bazaar.
/// It stores only opaque canonical StateKey images and contains no Rust game-semantic fallback.
#[path = "poa_bazaar_restart_portal.rs"]
pub mod poa_bazaar_restart_portal;

/// Lean-owned canonical Bazaar codec plus journal-backed checked persistence boundary.
#[path = "poa_bazaar_runtime_ffi.rs"]
pub mod poa_bazaar_runtime_ffi;

#[path = "poa_bazaar_native_callbacks.rs"]
#[cfg(all(lean_lib_present, dregg_poa_bazaar_runtime_present))]
mod poa_bazaar_native_callbacks;

pub use bridge_lc_ffi::{
    eth_committee_rotation_available, eth_committee_rotation_wire, eth_lc_verify_available,
    eth_lc_verify_wire, mina_account_opening_wire, mina_account_state_ok_available,
    mina_better_tip_available, mina_better_tip_wire, mina_checkpoint_advance_available,
    mina_checkpoint_advance_wire, mina_head_advance_available, mina_head_advance_wire,
    mina_lc_verify_available, mina_lc_verify_wire, mina_proof_chain_ok_available,
    mina_proof_chain_wire, mina_state_hash_word_ok_available, mina_state_hash_word_wire,
    mina_wrap_challenges_available, mina_wrap_ft_eval0_available, mina_wrap_shape_ok_available,
    mina_wrap_shape_wire, mpt_lc_verify_available, mpt_lc_verify_wire,
    shadow_eth_committee_rotation, shadow_eth_lc_verify, shadow_mina_account_state_ok,
    shadow_mina_better_tip, shadow_mina_checkpoint_advance, shadow_mina_head_advance,
    shadow_mina_lc_verify, shadow_mina_proof_chain_ok, shadow_mina_state_hash_word_ok,
    shadow_mina_wrap_challenges, shadow_mina_wrap_ft_eval0, shadow_mina_wrap_shape_ok,
    shadow_mpt_lc_verify, shadow_tm_lc_verify, shadow_tm_skip_verify, tm_lc_verify_available,
    tm_lc_verify_wire, tm_skip_verify_available, tm_skip_verify_wire,
    verified_eth_committee_rotation, verified_eth_lc_verify, verified_mina_account_state_ok,
    verified_mina_better_tip, verified_mina_checkpoint_advance, verified_mina_head_advance,
    verified_mina_lc_verify, verified_mina_proof_chain_ok, verified_mina_state_hash_word_ok,
    verified_mina_wrap_challenges, verified_mina_wrap_ft_eval0, verified_mina_wrap_shape_ok,
    verified_mpt_lc_verify, verified_tm_lc_verify, verified_tm_skip_verify,
    EthCommitteeRotationVerdict, EthLcVerdict, MinaAccountOpeningInput, MinaAccountPermissions,
    MinaCheckpointRoll, MinaCheckpointSides, MinaForkChoiceVerdict, MinaHeadRoll, MinaLcVerdict,
    MinaProofChainVerdict, MinaStateHashWordVerdict, MinaWrapChallenges, MinaWrapFtEval0,
    MinaWrapShapeVerdict, MptLcVerdict, TmLcVerdict, TmSkipVerdict,
};
pub use marshal::{AdmissionReason, TurnStatus, WireState};

// STORAGE-IN-LEAN EXTRACTION — force-link circuit's `dregg_poseidon2_2to1` into the binary. The
// leanc-compiled storage content-root logic (`Dregg2.Storage.Deployed.poseidon2Hash`) calls it via
// `@[extern "dregg_poseidon2_2to1"]`, but NO Rust code references circuit, so without this `#[used]`
// pointer the linker dead-strips the whole `dregg_circuit` rlib and the symbol goes undefined.
#[cfg(dregg_storage_content_root_present)]
#[used]
static _FORCE_LINK_POSEIDON2: unsafe extern "C" fn(u64, u64) -> u64 =
    dregg_circuit::storage_ffi::dregg_poseidon2_2to1;

/// Decoded Lean gated-forest verdict (T9 output envelope).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowVerdict {
    /// `true` ONLY when the gated forest BODY committed (`status == BodyCommitted`). A
    /// prologue-only result (forged credential / violated caveat / failed effect → the fee was
    /// charged as anti-spam but the body rolled back) is `committed == false` — the turn is
    /// REJECTED, NOT accepted (boundary-P1 bug 2).
    pub committed: bool,
    pub loglen: u64,
    /// The three-way status (boundary-P1 bug 2). `None` only for the legacy no-`status` wire.
    pub status: Option<TurnStatus>,
    /// The theorem-backed admission reason — the legible "why" of a refused turn. `None` for the
    /// legacy no-`reason` wire. When the turn was refused at admission (`status == Rejected`),
    /// this names the FIRST failing gate; on an admitted turn it is `Some(Admitted)`.
    pub reason: Option<AdmissionReason>,
    pub divergence_note: Option<String>,
}

impl ShadowVerdict {
    /// Whether the prologue (fee/nonce) was committed but the BODY FAILED — the fee was charged
    /// as anti-spam but the turn is REJECTED (must NOT be treated as accepted).
    pub fn prologue_only(&self) -> bool {
        self.status == Some(TurnStatus::PrologueCommittedBodyFailed)
    }
    /// Whether the body genuinely committed (the turn is ACCEPTED).
    pub fn body_committed(&self) -> bool {
        // Fall back to `committed` for the legacy no-`status` wire.
        match self.status {
            Some(s) => s == TurnStatus::BodyCommitted,
            None => self.committed,
        }
    }
    /// The human-readable refusal reason, if the turn was rejected at admission and the wire
    /// carried a (non-`Admitted`) reason. `None` for an admitted turn, a body-rollback (whose
    /// "why" is the body's, not admission's), or a legacy no-`reason` wire.
    pub fn admission_refusal(&self) -> Option<AdmissionReason> {
        match self.reason {
            Some(r) if !r.is_admitted() => Some(r),
            _ => None,
        }
    }
}

/// Whether the Lean static archive was linked and runtime init succeeded.
pub fn lean_available() -> bool {
    lean_init_once().is_ok()
}

/// Observe the default Lean runtime initializer without starting it.
///
/// `None` means the process has not completed an initialization attempt. `Some(Ok(()))`
/// means initialization succeeded, and `Some(Err(_))` preserves the exact cached failure.
/// This is primarily an embedding/test diagnostic: export discovery must remain able to
/// distinguish a linked symbol from an initialized runtime without paying the initializer tax.
pub fn lean_runtime_init_status() -> Option<Result<(), String>> {
    ffi::lean_init_status()
}

/// The process-wide Lean runtime prefix. A process cannot switch prefixes after startup.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeanRuntimeMode {
    Default,
    /// Static linkage omits libuv; shared linkage retains its documented libuv limitation.
    SingleThreaded,
}

/// Read-only initialization evidence. Narrow admission does not imply full executor readiness.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LeanInitializationStatus {
    pub runtime_mode: Option<LeanRuntimeMode>,
    pub delegated_admission_ready: bool,
    /// The generated FFIDirect/FFI import closure is ready, without implying full readiness.
    pub executor_ready: bool,
    /// The verified ML-DSA/ML-KEM core modules are ready, without implying full readiness.
    pub pq_ready: bool,
    pub default_full: Option<Result<(), String>>,
    pub single_threaded_full: Option<Result<(), String>>,
    /// A module can set its generated guard before failing. Such failure forbids all retries.
    pub failure: Option<String>,
}

/// Inspect module-family readiness without starting Lean or changing its initialization mode.
pub fn lean_initialization_status() -> LeanInitializationStatus {
    ffi::initialization_status()
}

/// Native ABI compatibility entrypoint, shared with the Rust API's lifecycle coordinator.
/// Repeated calls are safe; an incompatible ST prefix or initialization failure returns 1.
/// This API owns runtime and host-thread attachment; callers must not separately
/// initialize/finalize the same Lean runtime or attach those threads a second time.
#[no_mangle]
pub extern "C" fn dregg_ffi_init() -> i32 {
    i32::from(ffi::lean_init_once().is_err())
}

/// Native ABI compatibility entrypoint for the existing ST module family.
/// Its selecting host thread owns subsequent ST calls; no second runtime is started.
#[no_mangle]
pub extern "C" fn dregg_ffi_init_st() -> i32 {
    i32::from(ffi::lean_init_st_once().is_err())
}

/// Whether verified-gate tests must refuse an absent Lean archive/export instead
/// of reporting a hollow `ok` after self-skipping.
///
/// ── ⚠ ARMED BY DEFAULT (flipped 2026-07-27), and why ────────────────────────────
/// `libtest` has exactly TWO runtime outcomes: pass and fail. There is no runtime
/// "skip" — `#[ignore]` is decided at COMPILE time. So a test that discovers at run
/// time that it cannot exercise its subject has only one honest option left, and it
/// is not `return`. `ok` is the same word cargo prints for a test that ran every
/// assertion, and no reader downstream can tell the two apart.
///
/// This gate existed and was correct, and it was OFF wherever a human actually
/// looks. `.github/workflows/ci.yml` arms it only when the seed fetch succeeded;
/// `armed-teeth.yml`'s `lean-hard-mode` lane is `github.event_name != 'pull_request'`
/// and needs a published seed; and of the last 60 `ci.yml` runs, 37 cancelled, 21
/// failed, 0 succeeded. `scripts/local-gates.sh` — the instrument this repo actually
/// reads — never set it at all. A mechanism that is only armed on a lane that never
/// reaches a verdict is a documented wound, not a detected one.
///
/// The premise it was written under has also expired. When these guards were added,
/// building the archive meant a cold mathlib bootstrap. Today it is committed at
/// `dregg-lean-ffi/libdregg_lean.a`, `scripts/fetch-lean-seed.sh` pulls a
/// HEAD-keyed seed in minutes, and `scripts/pbuild` auto-provisions it. "The archive
/// might be missing" is now the exceptional case, so it is the one that should have
/// to say a word.
///
/// There are exactly TWO ways to disarm, and both are a WORD someone typed:
///
///   * `DREGG_TEST_ALLOW_MISSING_LEAN=1` — the developer-facing opt-out. Restores
///     the old skip-and-report-`ok` behaviour for someone who genuinely has no
///     archive, visibly, in their shell history rather than silently for everyone.
///   * `DREGG_TEST_REQUIRE_LEAN=0` (or `false`/`off`) — an EXPLICIT FALSY value on
///     the existing variable. ⚠ This one is load-bearing and is not decoration:
///     `.github/workflows/ci.yml:521` sets `DREGG_TEST_REQUIRE_LEAN: ${{ steps.arm
///     .outputs.armed }}`, and that step emits `armed=0` for the sanctioned
///     `LEAN_GATE_INTENTIONALLY_UNARMED=1` bootstrap — a disarm that is already
///     committed to `lean-seed.pin` and visible in review. Treating `"0"` as "arm
///     anyway" would red that declared path for saying out loud what this change
///     exists to make people say.
///
/// UNSET is ARMED. That asymmetry is the entire change: the condition under which
/// every verified-gate test used to report `ok` was nobody having set anything.
pub fn test_require_lean() -> bool {
    if armed_from_env_value(
        std::env::var("DREGG_TEST_ALLOW_MISSING_LEAN")
            .ok()
            .as_deref(),
    ) {
        return false;
    }
    match std::env::var("DREGG_TEST_REQUIRE_LEAN").ok().as_deref() {
        // An explicit falsy value is a declared disarm (see ci.yml's `armed=0`).
        Some("0") | Some("false") | Some("FALSE") | Some("off") | Some("OFF") => false,
        // Set-truthy re-asserts the default; UNSET is now the same thing.
        _ => true,
    }
}

/// Keep the test gate's grammar byte-for-byte aligned with build.rs's explicit
/// `DREGG_REQUIRE_LEAN` grammar.
fn armed_from_env_value(value: Option<&str>) -> bool {
    matches!(
        value,
        Some("1") | Some("true") | Some("TRUE") | Some("on") | Some("ON")
    )
}

/// Return `true` when a linked Lean capability is present.  When it is absent this
/// PANICS by default, naming the missing capability — because the alternative,
/// returning `false` so the caller can `return`, makes cargo print `ok` for a test
/// that asserted nothing about the verified core it is named after.
///
/// `DREGG_TEST_ALLOW_MISSING_LEAN=1` restores the old skip. See
/// [`test_require_lean`] for why that is the opt-IN and not the default.
pub fn demand_lean(available: bool, what: &str) -> bool {
    demand_lean_armed(available, what, test_require_lean())
}

/// Whether build.rs refused to advertise the linked archive because it was NOT built from this
/// checkout's Lean source (a VERIFIED-RUNTIME PROVENANCE DOWNGRADE: `lake build` was skipped, could
/// not run, failed to elaborate, or failed to splice, so a seed / previous build is what is
/// linkable). When this is true every `*_available()` is deliberately FALSE — see the provenance
/// gate in `dregg-lean-ffi/build.rs`.
///
/// It exists so a refusal can name the RIGHT cause. "The archive lacks the export" and "the archive
/// is from another day" want opposite fixes, and telling someone to fetch a seed when their Lean
/// build is red sends them the wrong way.
pub fn lean_archive_provenance_downgraded() -> bool {
    cfg!(dregg_lean_stale_archive)
}

fn demand_lean_armed(available: bool, what: &str, armed: bool) -> bool {
    demand_lean_full(available, what, armed, lean_archive_provenance_downgraded())
}

/// The refusal, with BOTH axes as parameters so each is testable. `downgraded` is a genuinely
/// different failure from an absent export and wants the OPPOSITE remedy: fetching a seed fixes an
/// absent archive and actively entrenches a stale one.
fn demand_lean_full(available: bool, what: &str, armed: bool, downgraded: bool) -> bool {
    if available {
        return true;
    }
    let cause = if downgraded {
        "PROVENANCE DOWNGRADE — the Lean archive in this build was NOT produced from this \
         checkout. `lake build` was skipped, could not run, or FAILED TO ELABORATE, so build.rs \
         withheld every verified-export cfg rather than let you measure another day's Lean.\n\
         \x20  FIX: repair the Lean build (`lake build Dregg2.FFI` in metatheory/) and rebuild.\n\
         \x20  ⚠ Do NOT fetch a seed to silence this — that entrenches the stale archive.\n\
         \x20  ⚠ Until 2026-07-28 this case did NOT refuse: it linked the stale archive and the \
         verified-rule tests RAN against it. One such run reported a consensus finality gate as \
         OPEN when it was closed and green at HEAD."
    } else {
        "the linked archive lacks that export — no verified runtime was linked.\n\
         \x20  FIX: get the archive (minutes, not hours):\n\
         \x20     bash scripts/fetch-lean-seed.sh        # HEAD-keyed prebuilt seed\n\
         \x20     scripts/pbuild <lane> cargo test …     # auto-provisions it remotely"
    };
    assert!(
        !armed,
        "MISSING VERIFIED CAPABILITY: cannot exercise {what}.\n\
         \n\
         CAUSE: {cause}\n\
         \n\
         This test asserts something about a machine-checked Lean core. Without that \
         core it cannot assert it — and `libtest` has no runtime `skip`, so the only \
         alternative to this failure is printing `ok`, which would be a claim about \
         the verified kernel that nobody checked.\n\
         \n\
         If you genuinely mean to test without the verified cores, say so out loud:\n\
         \x20   DREGG_TEST_ALLOW_MISSING_LEAN=1 cargo test …\n\
         and know that the resulting green is evidence about the Rust half only."
    );
    eprintln!(
        "SKIP: {what} not linked (DREGG_TEST_ALLOW_MISSING_LEAN=1) — this test will report `ok` \
         having asserted NOTHING about the verified core. That `ok` is not evidence."
    );
    false
}

#[cfg(test)]
mod test_require_lean_gate {
    use super::*;

    #[test]
    fn present_export_runs_under_both_modes() {
        assert!(demand_lean_armed(true, "present", false));
        assert!(demand_lean_armed(true, "present", true));
    }

    #[test]
    fn absent_export_panics_when_armed() {
        let error = std::panic::catch_unwind(|| demand_lean_armed(false, "missing export", true))
            .expect_err("an absent export under hard mode must panic");
        let message = error
            .downcast_ref::<String>()
            .map(String::as_str)
            .expect("the gate panic must carry an actionable String");
        assert!(message.contains("missing export"));
        // Actionable, not merely loud: it must name BOTH the way to get the archive
        // and the way to opt out, or the first person to hit it just deletes the gate.
        assert!(message.contains("fetch-lean-seed.sh"));
        assert!(message.contains("DREGG_TEST_ALLOW_MISSING_LEAN=1"));
    }

    #[test]
    fn absent_export_skips_when_unarmed() {
        assert!(!demand_lean_armed(false, "missing export", false));
    }

    /// ⚑ THE TWO CAUSES ARE NOT THE SAME REFUSAL, and confusing them costs a day.
    ///
    /// A stale archive that build.rs refused to advertise is a DIFFERENT failure from an archive
    /// that never had the export, and the remedies are OPPOSITE: fetching a seed fixes the second
    /// and entrenches the first. Before 2026-07-28 the downgrade did not refuse at all — the
    /// stale archive was linked and `node/src/finality_gate.rs`'s enrollment falsifier ran against
    /// a `tauOrder` from before `c6f00c228` and reported "The gate is OPEN" on a tree where it was
    /// closed. This pins that the refusal now NAMES which of the two it is.
    #[test]
    fn the_downgrade_and_the_absence_are_told_apart() {
        let msg = |downgraded: bool| {
            let e = std::panic::catch_unwind(move || {
                demand_lean_full(false, "the finality-gate export", true, downgraded)
            })
            .expect_err("an unusable verified capability under hard mode must panic");
            e.downcast_ref::<String>()
                .map(String::as_str)
                .expect("the gate panic must carry an actionable String")
                .to_string()
        };

        let stale = msg(true);
        assert!(
            stale.contains("PROVENANCE DOWNGRADE"),
            "a stale archive must be NAMED as such, not reported as a missing export: {stale}"
        );
        assert!(
            stale.contains("lake build Dregg2.FFI"),
            "the stale-archive refusal must point at the Lean build, the actual fix: {stale}"
        );
        assert!(
            !stale.contains("bash scripts/fetch-lean-seed.sh"),
            "the stale-archive refusal must NOT prescribe fetching a seed — that entrenches the \
             stale archive rather than fixing it: {stale}"
        );

        let absent = msg(false);
        assert!(
            !absent.contains("PROVENANCE DOWNGRADE"),
            "a genuinely absent export must not be blamed on provenance: {absent}"
        );
        assert!(
            absent.contains("bash scripts/fetch-lean-seed.sh"),
            "an absent archive must still teach the one-command fix: {absent}"
        );
        assert_ne!(
            stale, absent,
            "the two causes must produce DIFFERENT text — one message for both is the confusion \
             this test exists to prevent"
        );
    }

    /// THE FLIPPED DEFAULT, asserted rather than assumed.
    ///
    /// This is the whole change: with NO environment variable set, an absent export
    /// must be a FAILURE. Before 2026-07-27 it was a `return` and an `ok`, and the
    /// only thing standing between the verified estate and a hollow green was a
    /// variable that `scripts/local-gates.sh` never set and that `ci.yml` set only
    /// when a seed fetch it could not guarantee had succeeded.
    ///
    /// ⚠ Serialized against the other env-mutating test in this module by running
    /// both from one `#[test]`: `std::env::set_var` is process-global and this
    /// binary runs `--test-threads=4`.
    #[test]
    fn the_default_is_armed_and_the_opt_out_is_a_named_word() {
        // SAFETY: single test fn owns these two vars for its duration; both are
        // removed before it returns, and no other test in this crate reads them.
        unsafe {
            std::env::remove_var("DREGG_TEST_ALLOW_MISSING_LEAN");
            std::env::remove_var("DREGG_TEST_REQUIRE_LEAN");
        }
        assert!(
            test_require_lean(),
            "with NO env set the gate must be ARMED — an unset variable is exactly the \
             condition under which every verified-gate test used to report `ok` having \
             asserted nothing"
        );

        // The opt-out is a WORD, and it is the same grammar as the build gate.
        for truthy in ["1", "true", "TRUE", "on", "ON"] {
            unsafe { std::env::set_var("DREGG_TEST_ALLOW_MISSING_LEAN", truthy) };
            assert!(
                !test_require_lean(),
                "DREGG_TEST_ALLOW_MISSING_LEAN={truthy} must disarm"
            );
        }
        // A value OUTSIDE the grammar does NOT disarm — a typo'd opt-out must fail
        // loud rather than silently restoring the hollow green it was meant to name.
        for falsy in ["0", "false", "off", "yes", "2", ""] {
            unsafe { std::env::set_var("DREGG_TEST_ALLOW_MISSING_LEAN", falsy) };
            assert!(
                test_require_lean(),
                "DREGG_TEST_ALLOW_MISSING_LEAN={falsy:?} is not the opt-out grammar and must \
                 leave the gate ARMED"
            );
        }
        unsafe { std::env::remove_var("DREGG_TEST_ALLOW_MISSING_LEAN") };
        assert!(test_require_lean(), "removing the opt-out must re-arm");

        // THE ci.yml PATH. `steps.arm.outputs.armed` is `0` on the sanctioned
        // `LEAN_GATE_INTENTIONALLY_UNARMED=1` bootstrap, and that lane must keep
        // working — a declared, reviewable disarm is exactly what this change wants
        // people to do, so redding it would punish the honest spelling.
        for falsy in ["0", "false", "FALSE", "off", "OFF"] {
            unsafe { std::env::set_var("DREGG_TEST_REQUIRE_LEAN", falsy) };
            assert!(
                !test_require_lean(),
                "DREGG_TEST_REQUIRE_LEAN={falsy} is ci.yml's declared disarm and must be honoured"
            );
        }
        for truthy in ["1", "true", "on"] {
            unsafe { std::env::set_var("DREGG_TEST_REQUIRE_LEAN", truthy) };
            assert!(
                test_require_lean(),
                "DREGG_TEST_REQUIRE_LEAN={truthy} re-asserts the default"
            );
        }
        unsafe { std::env::remove_var("DREGG_TEST_REQUIRE_LEAN") };
        assert!(
            test_require_lean(),
            "UNSET is ARMED — that asymmetry IS the change"
        );
    }

    #[test]
    fn env_grammar_matches_the_build_gate() {
        for truthy in ["1", "true", "TRUE", "on", "ON"] {
            assert!(armed_from_env_value(Some(truthy)));
        }
        for falsy in ["0", "false", "FALSE", "off", "OFF", "", "yes", "2"] {
            assert!(!armed_from_env_value(Some(falsy)));
        }
        assert!(!armed_from_env_value(None));
    }
}

/// Marshal a wire string through `dregg_exec_full_forest_auth_str` and return the raw
/// output wire. Requires `lean_available()`.
pub fn shadow_exec_full_forest_auth(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    lean_forest_auth(wire)
}

/// Credential-preserving handler-cutover shadow: host-fed admission, then the
/// four-leg per-node auth gate before each registered-handler dispatch.
///
/// Available only when the linked archive exports `dregg_exec_handler_turn`
/// (cfg `dregg_handler_present`, set by build.rs). The forest-auth gate
/// ([`shadow_exec_full_forest_auth`]) is the load-bearing path and is always present.
pub fn shadow_exec_handler_turn(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    lean_handler_turn(wire)
}

/// Whether the linked archive exports the verified finality-gate
/// (`dregg_blocklace_finalize`). When false, the node cannot Lean-gate finality and falls back to
/// the un-gated path. Distinct from [`lean_available`] (which is about the executor exports): a
/// stale archive can have the executor but lack the finality gate.
pub fn finality_gate_available() -> bool {
    ffi::finality_gate_present() && lean_init_once().is_ok()
}

/// Run the verified PER-ASSET kernel step `@[export] dregg_record_kernel_step` (the PROVED
/// `Exec.recKExec`) over a single-column cell state.
///
/// The input/output wire is the canonical JSON the export reads:
///   * in:  `{"cells":[[ID,{"rec":[["balance",{"int":N}],…]}],…],"actor":N,"src":N,"dst":N,"amt":N}`
///   * out: `{"cells":CELLS,"ok":B}`
///
/// This is the verified executor the intent crate's `verified_settle` routes each ring leg
/// through, ONE call per leg over that leg's asset-projected column (`Dregg2.Intent.RingFFI`'s
/// `projAsset`). By the Lean keystone `ffi_export_realises_settleRing_leg`, the export's `ok` bit
/// and the post-state `balance` column ARE the verified per-asset executor's, so folding the legs
/// through this entry computes EXACTLY `settleRing` — not a Rust mirror.
///
/// Requires [`lean_available`]; returns `Err` if the archive was not linked.
pub fn shadow_record_kernel_step(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    lean_record_kernel_step(wire)
}

/// Verified FINALITY GATE — run the verified `BlocklaceFinality.tauOrder` rule over a wire-encoded
/// `(wavelength, participants, lace)` and return the verified finalized `(creator, seq)` order
/// (`"F=<c>:<s>,..."`) or `"ERR"` (fail-closed on a malformed wire).
///
/// The node calls this at the live commit point: it computes finality FROM the verified rule and
/// admits a turn to the executor ONLY when the verified rule finalizes it. The wire grammar mirrors
/// `Dregg2.Distributed.FinalityGate.encodeLaceWire` byte-for-byte (`finality_gate` module).
pub fn shadow_blocklace_finalize(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    lean_blocklace_finalize(wire)
}

/// Whether the linked archive exports the verified flow-refinement decision gate
/// (`dregg_decide_refines`, the C-ABI entry over the PROVED `decideRefines`). When false, the deploy
/// gate (`dregg-deploy::refine`) falls back to its in-process σ-free mirror. Distinct from
/// [`lean_available`] (the executor exports): a stale archive can have the executor but lack this gate.
pub fn decide_refines_gate_available() -> bool {
    ffi::decide_refines_present() && lean_init_once().is_ok()
}

/// Run the verified FLOW-REFINEMENT DECISION `@[export] dregg_decide_refines` (the PROVED
/// `Dregg2.Deos.FlowRefine.decideRefines`, sound+complete for the online-simulation refinement order
/// `≤ᶠ` per `decideRefines_iff`) over a wire-encoded pair of σ-free `Proc`s.
///
/// The input/output wire is the canonical grammar the export reads:
///   * in:  `"A=<preorder-tokens>;B=<preorder-tokens>"` (each `Proc` as a space-separated preorder
///     token stream: `d` done · `e<n>` emit ℓ · `c` ch(2) · `s` seqp(2)).
///   * out: `"1"` (A ≤ᶠ B) · `"0"` (A ⋠ B) · `"ERR"` (fail-closed on a malformed wire).
///
/// `dregg-deploy/src/refine.rs` routes its safe-upgrade / intent-conformance decision through this
/// entry when [`decide_refines_gate_available`], so the deploy gate runs the verified procedure
/// rather than a Rust mirror of it. Requires the archive to export the gate; returns `Err` otherwise.
pub fn shadow_decide_refines(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    lean_decide_refines(wire)
}

/// Whether the linked archive exports the verified deployed-constraint evaluator.
pub fn constraint_admits_available() -> bool {
    ffi::constraint_admits_present() && lean_init_once().is_ok()
}

/// Run the Lean-authored pure-constraint admission evaluator over its canonical wire.
pub fn shadow_constraint_admits(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_constraint_admits(wire)
}

/// Whether the linked archive exports the verified cross-cell per-asset conservation decision
/// (`dregg_cross_cell_conserves`, the C-ABI entry over
/// `Dregg2.Circuit.CrossCellConserveDecision.conservesFFI` — proved EQUAL to the committed Σδ=0 AIR
/// boundary by `CrossCellConserveRefine.decision_conserves_iff_air_boundary`). When false, the
/// conservation oracle cannot be installed and a full node's per-asset conservation gate fails closed.
pub fn cross_cell_conserves_available() -> bool {
    ffi::cross_cell_conserves_present() && lean_init_once().is_ok()
}

/// The verdict of the verified cross-cell per-asset conservation decision.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CrossCellVerdict {
    /// Every asset's signed delta sum is zero — the block conserves (ADMIT).
    Conserves,
    /// Asset `asset` nets to `imbalance != 0` (the first imbalanced asset in ascending key order) —
    /// REFUSE with a hidden mint/burn.
    Imbalanced { asset: u32, imbalance: i64 },
}

/// Run the VERIFIED, Lean-authored cross-cell per-asset conservation decision `@[export]
/// dregg_cross_cell_conserves` over the turn's `(asset, delta)` rows.
///
/// This is the object `turn/src/executor/atomic.rs`'s per-asset conservation gate routes through (via
/// `dregg-exec-lean`'s conservation oracle) so the deployed executor's `Σδ=0`-per-asset decision is
/// COMPUTED BY the proven Lean decision — NOT the hand-written Rust `BlockConservation` twin. The
/// decision is proved to equal the committed `Dregg2.Circuit.CrossCellConservation` AIR boundary
/// (`creditSum = debitSum` per asset), so the route-through and the proof the prover commits to cannot
/// drift.
///
/// `rows`: `(asset_class, signed_net_delta)` per verified per-cell contribution — issuer-well legs
/// included, which is how a disclosed mint/burn reaches the sum. Returns `Err` if the archive lacks
/// the export (the caller then fails closed) or the wire round-trip fails.
///
/// ⚑ THE DECLARED-SUPPLY ARGUMENT WAS DELETED on 2026-07-28. This function used to take a second
/// `supply: &[(u32, i64)]` slice and encode it into the wire's optional supply section. It had NO
/// producer anywhere in the tree — every caller, production and test, passed an empty slice — because
/// the ratified supply model (`.docs-history-noclaude/SUPPLY-MODEL.md`) discloses supply as the issuer
/// well's paired ledger delta, not as an asserted row. The wire still carries an explicit `0` supply
/// count: that is this executor telling the Lean rule, in the rule's own vocabulary, that it discloses
/// no supply rows. The Lean rule keeps its supply section (and its `#guard` for it) — the spec is
/// legitimately more general than the deployment; a Rust parameter with no producer is not.
pub fn shadow_cross_cell_conserves(rows: &[(u32, i64)]) -> Result<CrossCellVerdict, String> {
    ensure_lean_init()?;
    // Build the canonical wire: `nRows [asset delta]* nSupply [asset mag mint]*`, with `nSupply = 0`.
    let mut wire = String::new();
    wire.push_str(&rows.len().to_string());
    for (asset, delta) in rows {
        wire.push(' ');
        wire.push_str(&asset.to_string());
        wire.push(' ');
        wire.push_str(&delta.to_string());
    }
    wire.push_str(" 0");
    let out = ffi::lean_cross_cell_conserves(&wire)?;
    let mut toks = out.split_whitespace();
    match toks.next() {
        Some("1") => Ok(CrossCellVerdict::Conserves),
        Some("0") => {
            // `"0"` bare = malformed wire (fail-closed); `"0 <asset> <imbalance>"` = a real imbalance.
            match (toks.next(), toks.next()) {
                (Some(a), Some(i)) => {
                    let asset = a
                        .parse::<u32>()
                        .map_err(|e| format!("cross-cell verdict asset not u32: {e}"))?;
                    let imbalance = i
                        .parse::<i64>()
                        .map_err(|e| format!("cross-cell verdict imbalance not i64: {e}"))?;
                    Ok(CrossCellVerdict::Imbalanced { asset, imbalance })
                }
                _ => Err(format!(
                    "cross-cell conservation decision refused a malformed wire (fail-closed): {out:?}"
                )),
            }
        }
        _ => Err(format!(
            "unexpected cross-cell conservation verdict wire: {out:?}"
        )),
    }
}

/// Whether the linked archive exports the extracted, Lean-verified ML-DSA verify core
/// (`dregg_fips204_verify`, the C-ABI entry over `Dregg2.Crypto.Fips204Verify.verifyFFI` =
/// `Fips204Spec.verifyB` at the deployed ML-DSA-65 parameters). When false, a caller must fall back to
/// the `fips204` crate verify. Distinct from [`lean_available`]: a stale archive can lack this export.
pub fn fips204_verify_core_available() -> bool {
    ffi::fips204_verify_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED, extracted ML-DSA verify core `@[export] dregg_fips204_verify` (the executable
/// `Dregg2.Crypto.Fips204Verify.verifyCore`, proved equal to the `Fips204Spec.verifyB` predicate and to
/// discharge `DreggPqRefinement.Fips204Correct` for the verify direction). This runs the SECURITY-CRITICAL
/// verify as a Lean-verified object (leanc-native) — a forged signature REJECTS.
///
/// Wire grammar the export reads:
///   * in:  `"thi μ c̃ z h"` (five decimal ints — the deployed-parameter public high part, message,
///     challenge digest, response, hint). STRICT: `mapM`, not `filterMap`, so a token that is not a
///     decimal integer is refused rather than silently dropped.
///   * out: `"1"` (accept) · `"0"` (reject) · `"2 <fault>"` (⚑ the wire could not be READ, so nothing
///     was verified — `0` scalar arity, `1` scalar token).
///
/// ⚑ 2026-08-07: `"0"` used to be BOTH "this signature does not verify" AND the fail-closed answer for
/// a malformed wire, so no reader could tell a forgery from a grammar disagreement and every negative
/// test on this wire was satisfied by "nothing was verified". The separation is proved both ways in
/// `Dregg2.Crypto.Fips204Verify` (`verifyWire_eq_reject_iff` / `verifyWire_malformed_iff`).
///
/// `dregg-pq` routes its ML-DSA verify through this entry when [`fips204_verify_core_available`], so the
/// verify runs the verified Lean core rather than a trusted primitive. Returns `Err` if the archive lacks
/// the export.
pub fn shadow_fips204_verify(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_fips204_verify(wire)
}

/// Whether the linked archive exports the extracted, Lean-verified REAL, FULL-BYTE ML-DSA verify core
/// (`dregg_fips204_verify_real`, BRICK 8 — the C-ABI entry over `Dregg2.Crypto.Fips204Verify.verifyRealFFI`
/// = the FULL-DIMENSION `MlDsaVerifyReal.verifyCore` over the real 1952/3309-byte key/signature). When
/// false, a caller must fall back to the `fips204` crate verify. Distinct from [`lean_available`]: a stale
/// archive can lack this export.
pub fn fips204_verify_real_core_available() -> bool {
    ffi::fips204_verify_real_present() && ffi::pq_init_once().is_ok()
}

/// Whether the linked archive exports the real ML-DSA verify core, without initializing Lean.
///
/// Use this to register a lazy function-pointer route. The first actual call must still go
/// through [`shadow_fips204_verify_real`], which initializes Lean once and returns its error.
pub fn fips204_verify_real_export_present() -> bool {
    ffi::fips204_verify_real_present()
}

/// Run the VERIFIED, extracted REAL, FULL-BYTE ML-DSA verify core `@[export] dregg_fips204_verify_real`
/// (the executable `Dregg2.Crypto.Fips204Verify.verifyRealFFI` over `MlDsaVerifyReal.verifyCore`). This
/// runs the SECURITY-CRITICAL verify of a REAL ML-DSA-65 key + signature as a Lean-verified object
/// (leanc-native) — a forged/tampered signature REJECTS, PROVED by `verify_accepts_real` /
/// `verify_rejects_tampered`.
///
/// Wire grammar the export reads:
///   * in:  `"hex(pk) hex(msg) hex(ctx) hex(sig)"` (four space-separated lowercase-hex fields; an empty
///     field, e.g. `ctx = ε`, is the empty token between two spaces).
///   * out: `"1"` (accept) · `"0"` (reject) · `"2 <fault>"` (⚑ the wire could not be READ, so nothing
///     was verified — `2` byte-field arity, `3` byte-field hex).
///
/// ⚑ 2026-08-07: `"0"` used to be BOTH the cryptographic reject AND the fail-closed malformed answer.
/// `dregg_pq::ml_dsa_verify`'s `reply == "1"` therefore turned a `real_verify_wire` / `parseByteE`
/// disagreement into "this signature is forged" on ~10 gating surfaces. It now decodes to
/// `MlDsaVerifyRefusal::VerifiedCoreWireMalformed`, which still REJECTS (fail-closed) but names the
/// stage instead of the signer. Proved both ways by `Fips204Verify.verifyRealWire_eq_reject_iff` /
/// `verifyRealWire_malformed_iff`.
///
/// `dregg-pq::ml_dsa_verify` routes its verify through this entry (installed via
/// `dregg_pq::install_lean_verify_core_real`), so the deployed verify runs the verified Lean core over the
/// real bytes rather than the trusted `fips204` primitive. Returns `Err` if the archive lacks the export.
pub fn shadow_fips204_verify_real(wire: &str) -> Result<String, String> {
    ffi::with_pq(|| ffi::lean_fips204_verify_real(wire))
}

/// Whether the linked archive exports the extracted, Lean-verified ML-DSA sign core
/// (`dregg_fips204_sign`, the C-ABI entry over `Dregg2.Crypto.Fips204Verify.signFFI` = the extracted
/// `signCore`, the Fiat–Shamir-with-aborts signer at the deployed ML-DSA-65 parameters). When false, a
/// caller must fall back to the `fips204` crate sign. Distinct from [`lean_available`]: a stale archive
/// can lack this export.
pub fn fips204_sign_core_available() -> bool {
    ffi::fips204_sign_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED, extracted ML-DSA sign core `@[export] dregg_fips204_sign` (the executable
/// `Dregg2.Crypto.Fips204Verify.signCore`, proved to agree with the spec `Fips204Spec.MlDsaParams.sign`
/// and — together with `verifyCore` — to discharge `DreggPqRefinement.Fips204Correct` FULLY). This runs
/// the SIGNING direction as a Lean-verified object (leanc-native).
///
/// Wire grammar the export reads:
///   * in:  `"s1 s2 t0 μ y"` (five decimal ints — the deployed-parameter secret `(s₁,s₂,t₀)`, message,
///     and the sampled randomness/mask `y`).
///   * out: `"1 c̃ z h"` (an accepted signature — the tag, then three decimal ints) · `"0"` (a REJECTED
///     sample; the caller resamples `y`, the Dilithium rejection loop) · `"2 <fault>"` (⚑ the wire
///     could not be READ, so nothing was signed — the caller must STOP, not resample).
///
/// ⚑ 2026-08-07 RETAG: the reply alphabet was `"c̃ z h"` / `"REJECT"`, where `"REJECT"` meant BOTH the
/// honest rejection-sampling abort AND a wire the Lean side could not read — so a caller could resample
/// forever against a wire that would never parse. `dregg_pq::ml_dsa_sign_core` decodes the new alphabet;
/// its pre-retag form treated every non-`"REJECT"` string as signature bytes.
///
/// `dregg-pq` routes its ML-DSA sign path through this entry when [`fips204_sign_core_available`], so the
/// signing runs the verified Lean core rather than a trusted primitive. Returns `Err` if the archive
/// lacks the export.
pub fn shadow_fips204_sign(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_fips204_sign(wire)
}

/// Whether the linked archive exports the extracted, Lean-verified REAL, FULL-BYTE ML-DSA sign core
/// (`dregg_fips204_sign_real`, the brick-8 SIGN analog — the C-ABI entry over
/// `Dregg2.Crypto.MlDsaSignReal.signRealFFI` = the FULL-DIMENSION `signCore` over the real 4032/3309-byte
/// key/signature). When false, a caller must fall back to the `fips204` crate sign. Distinct from
/// [`lean_available`]: a stale archive can lack this export.
pub fn fips204_sign_real_core_available() -> bool {
    ffi::fips204_sign_real_present() && ffi::pq_init_once().is_ok()
}

/// Whether the linked archive exports the real ML-DSA sign core, without initializing Lean.
pub fn fips204_sign_real_export_present() -> bool {
    ffi::fips204_sign_real_present()
}

/// Run the VERIFIED, extracted REAL, FULL-BYTE ML-DSA sign core `@[export] dregg_fips204_sign_real`
/// (the executable `Dregg2.Crypto.MlDsaSignReal.signRealFFI` over `signCore`). This PRODUCES the signature
/// of a REAL ML-DSA-65 key over the real `sk ‖ msg ‖ ctx` bytes as a Lean-verified object (leanc-native) —
/// PROVED to reproduce a genuine crate DETERMINISTIC signature byte-for-byte by
/// `signRealFFI_matches_crate_deterministic`.
///
/// Wire grammar the export reads:
///   * in:  `"hex(sk) hex(msg) hex(ctx)"` (three space-separated lowercase-hex fields; an empty field,
///     e.g. `ctx = ε`, is the empty token between two spaces).
///   * out: `hex(sig)` (the 3309-byte signature as lowercase hex) · `"ERR"` (the fail-closed answer for a
///     malformed wire).
///
/// `dregg-pq::MlDsaKey::sign` routes its signing through this entry (installed via
/// `dregg_pq::install_lean_sign_core_real`), so the deployed signer PRODUCES the signature from the verified
/// Lean core over the real bytes rather than the `fips204` primitive. Returns `Err` if the archive lacks the
/// export.
pub fn shadow_fips204_sign_real(wire: &str) -> Result<String, String> {
    ffi::with_pq(|| ffi::lean_fips204_sign_real(wire))
}

/// Whether the linked archive exports the extracted, Lean-verified ML-KEM (FIPS 203) encaps core
/// (`dregg_fips203_encaps`, the C-ABI entry over `Dregg2.Crypto.Fips203Kem.encapsFFI`). When false, a
/// caller must fall back to the `ml-kem` crate encaps. Distinct from [`lean_available`]: a stale archive
/// can lack this export.
pub fn fips203_encaps_core_available() -> bool {
    ffi::fips203_encaps_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED, extracted ML-KEM encaps core `@[export] dregg_fips203_encaps` (the executable
/// `Dregg2.Crypto.Fips203Kem.encapsCore`, proved equal to `MlKemIndCca.foEncaps` and — with the decaps
/// core — to discharge `DreggKemRefinement.Fips203Correct`).
///
/// Wire grammar the export reads:
///   * in:  `"A t m"` (three decimal ints — the deployed-parameter public key `(A,t)` and message bit `m`).
///   * out: `"u v K"` (the ciphertext `(u,v)` and the encapsulated shared secret `K = H(m)`);
///     `"ERR"` for a malformed wire.
///
/// `dregg-pq` routes its ML-KEM encaps through this entry when [`fips203_encaps_core_available`]. Returns
/// `Err` if the archive lacks the export.
pub fn shadow_fips203_encaps(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_fips203_encaps(wire)
}

/// Whether the linked archive exports the extracted, Lean-verified ML-KEM (FIPS 203) decaps core
/// (`dregg_fips203_decaps`, the C-ABI entry over `Dregg2.Crypto.Fips203Kem.decapsFFI`). When false, a
/// caller must fall back to the `ml-kem` crate decaps. Distinct from [`lean_available`]: a stale archive
/// can lack this export.
pub fn fips203_decaps_core_available() -> bool {
    ffi::fips203_decaps_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED, extracted ML-KEM decaps core `@[export] dregg_fips203_decaps` (the executable
/// `Dregg2.Crypto.Fips203Kem.decapsCore`, proved equal to `MlKemIndCca.foDecaps` — the re-encryption
/// check + implicit reject). This runs the SECURITY-CRITICAL decaps as a Lean-verified object: a
/// tampered ciphertext implicit-rejects to a DIFFERENT (message-independent) secret, it does not leak.
///
/// Wire grammar the export reads:
///   * in:  `"A t s z u v"` (six decimal ints — the encapsulation key `(A,t)`, secret `s`, implicit-reject
///     seed `z`, ciphertext `(u,v)`).
///   * out: the recovered shared secret `K` as a decimal string (`H(m′)` on a matching re-encryption, else
///     the implicit-reject secret `J(z‖c)`); `"ERR"` for a malformed wire.
///
/// `dregg-pq` routes its ML-KEM decaps through this entry when [`fips203_decaps_core_available`]. Returns
/// `Err` if the archive lacks the export.
pub fn shadow_fips203_decaps(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_fips203_decaps(wire)
}

/// Whether the linked archive exports the extracted, Lean-verified REAL, FULL-BYTE ML-KEM-768 decaps core
/// (`dregg_mlkem_decaps_real`, BRICK K6 — the C-ABI entry over `Dregg2.Crypto.MlKemDecaps.mlkemDecapsRealFFI`
/// = the FULL-DIMENSION `mlkemDecaps` over the real 2400/1088-byte decapsulation key/ciphertext). When false,
/// a caller must fall back to the `ml-kem` crate decaps. Distinct from [`lean_available`]: a stale archive can
/// lack this export.
pub fn mlkem_decaps_real_core_available() -> bool {
    ffi::mlkem_decaps_real_present() && ffi::pq_init_once().is_ok()
}

/// Whether the linked archive exports the real ML-KEM decaps core, without initializing Lean.
pub fn mlkem_decaps_real_export_present() -> bool {
    ffi::mlkem_decaps_real_present()
}

/// Run the VERIFIED, extracted REAL, FULL-BYTE ML-KEM-768 decaps core `@[export] dregg_mlkem_decaps_real`
/// (the executable `Dregg2.Crypto.MlKemDecaps.mlkemDecapsRealFFI` over `mlkemDecaps` — the full FO pipeline:
/// K-PKE decrypt, `G = SHA3-512` split, re-encryption, byte-exact `c' = c` implicit-reject check). This runs
/// the SECURITY-CRITICAL decaps of a REAL ML-KEM-768 key + ciphertext as a Lean-verified object (leanc-native)
/// — a tampered ciphertext implicit-rejects to a DIFFERENT secret, PROVED by `mlkemDecapsRealFFI_recovers_real_secret`
/// / `mlkemDecapsRealFFI_rejects_tampered`.
///
/// Wire grammar the export reads:
///   * in:  `"hex(dk) hex(ct)"` (two space-separated lowercase-hex fields over the real 2400-byte
///     decapsulation key / 1088-byte ciphertext).
///   * out: `hex(K)` — the recovered 32-byte shared secret as lowercase hex; `"ERR"` for a malformed wire
///     (the fail-closed answer the Rust caller treats as a decaps fault).
///
/// `dregg-pq::HybridResponder::finish` routes its ML-KEM decaps through this entry (installed via
/// `dregg_pq::install_lean_kem_decaps_core_real`), so the deployed decaps runs the verified Lean core over the
/// real bytes rather than the trusted `ml-kem` primitive. Returns `Err` if the archive lacks the export.
pub fn shadow_mlkem_decaps_real(wire: &str) -> Result<String, String> {
    ffi::with_pq(|| ffi::lean_mlkem_decaps_real(wire))
}

/// Whether the linked archive exports the extracted, Lean-verified REAL, FULL-BYTE ML-KEM-768 encaps core
/// (`dregg_mlkem_encaps_real`, BRICK K5 — the C-ABI entry over `Dregg2.Crypto.MlKemEncaps.mlkemEncapsRealFFI`
/// = the FULL-DIMENSION `mlkemEncaps` over the real 1184/1088-byte encapsulation key/ciphertext). When false,
/// a caller must fall back to the `ml-kem` crate encaps. Distinct from [`lean_available`]: a stale archive can
/// lack this export.
pub fn mlkem_encaps_real_core_available() -> bool {
    ffi::mlkem_encaps_real_present() && ffi::pq_init_once().is_ok()
}

/// Whether the linked archive exports the real ML-KEM encaps core, without initializing Lean.
pub fn mlkem_encaps_real_export_present() -> bool {
    ffi::mlkem_encaps_real_present()
}

/// Run the VERIFIED, extracted REAL, FULL-BYTE ML-KEM-768 encaps core `@[export] dregg_mlkem_encaps_real`
/// (the executable `Dregg2.Crypto.MlKemEncaps.mlkemEncapsRealFFI` over `mlkemEncaps` — the deterministic FIPS
/// 203 Alg 16 FO encaps: `H(ek)` SHA3-256, `G(m ‖ H(ek))` SHA3-512 split, K-PKE.Encrypt). This runs the
/// KEM-ENCAPS as a Lean-verified object (leanc-native), PROVED BYTE-EXACT vs the `ml-kem` crate's
/// `EncapsulateDeterministic` by `encaps_matches_crate`.
///
/// Wire grammar the export reads:
///   * in:  `"hex(ek) hex(m)"` (two space-separated lowercase-hex fields over the real 1184-byte
///     encapsulation key / 32-byte message).
///   * out: `"hex(ct) hex(K)"` — the 1088-byte ciphertext + 32-byte shared secret as lowercase hex; `"ERR"`
///     for a malformed wire (the fail-closed answer the Rust caller treats as an encaps fault).
///
/// `dregg-pq::hybrid_kem::initiate` routes its ML-KEM encaps through this entry (installed via
/// `dregg_pq::install_lean_kem_encaps_core_real`), so the deployed encaps runs the verified Lean core over the
/// real bytes rather than the trusted `ml-kem` primitive. Returns `Err` if the archive lacks the export.
pub fn shadow_mlkem_encaps_real(wire: &str) -> Result<String, String> {
    ffi::with_pq(|| ffi::lean_mlkem_encaps_real(wire))
}

/// Whether the linked archive exports the extracted, Lean-verified REAL, FULL-BYTE ML-KEM-768 KEYGEN core
/// (`dregg_mlkem_keygen_real`, BRICK K7 — the C-ABI entry over `Dregg2.Crypto.MlKemKeygen.mlkemKeygenRealFFI`
/// = the deterministic FIPS 203 ML-KEM.KeyGen_internal over a 64-byte (d,z) seed). When false, a caller must
/// fall back to the `ml-kem` crate keygen. Distinct from [`lean_available`]: a stale archive can lack this
/// export.
pub fn mlkem_keygen_real_core_available() -> bool {
    ffi::mlkem_keygen_real_present() && ffi::pq_init_once().is_ok()
}

/// Whether the linked archive exports the real ML-KEM keygen core, without initializing Lean.
pub fn mlkem_keygen_real_export_present() -> bool {
    ffi::mlkem_keygen_real_present()
}

/// Run the VERIFIED, extracted REAL, FULL-BYTE ML-KEM-768 keygen core `@[export] dregg_mlkem_keygen_real`
/// (the executable `Dregg2.Crypto.MlKemKeygen.mlkemKeygenRealFFI` over `mlkemKeygen` — the deterministic FIPS
/// 203 ML-KEM.KeyGen_internal: G(d||k) SHA3-512 split, ExpandMatrix, CBD sampling, NTT, t = A*s + e, ByteEncode,
/// dk = dkPKE || ek || H(ek) || z). KAT-anchored vs the NIST ACVP `ML-KEM-keyGen-FIPS203` vectors (single-vector
/// `native_decide`); the byte<->ring `kpkeKeyGen_refines_ring` forall is OPEN.
///
/// Wire grammar the export reads:
///   * in:  `"hex(d z)"` (one lowercase-hex field over the real 64-byte (d,z) seed).
///   * out: `"hex(ek) hex(dk)"` — the 1184-byte encapsulation key + 2400-byte decapsulation key as lowercase
///     hex; `"ERR"` for a malformed wire (the fail-closed answer the Rust caller treats as a keygen fault).
///
/// `dregg-pq::hybrid_kem::ml_kem768_keygen` routes its ML-KEM keygen through this entry (installed via
/// `dregg_pq::install_verified_mlkem_keygen_core`), so the deployed keygen runs the verified Lean core over the
/// real bytes rather than the trusted `ml-kem` primitive. Returns `Err` if the archive lacks the export.
pub fn shadow_mlkem_keygen_real(wire: &str) -> Result<String, String> {
    ffi::with_pq(|| ffi::lean_mlkem_keygen_real(wire))
}

/// Whether the linked archive exports the extracted, Lean-verified REAL, FULL-BYTE ML-DSA-65 KEYGEN core
/// (`dregg_mldsa_keygen_real` — the C-ABI entry over `Dregg2.Crypto.MlDsaKeygen.mldsaKeygenRealFFI` = the
/// deterministic FIPS 204 ML-DSA.KeyGen_internal over a 32-byte ξ seed). When false, a caller must fall back
/// to the `fips204` crate keygen. Distinct from [`lean_available`]: a stale archive can lack this export.
pub fn mldsa_keygen_real_core_available() -> bool {
    ffi::mldsa_keygen_real_present() && ffi::pq_init_once().is_ok()
}

/// Whether the linked archive exports the real ML-DSA keygen core, without initializing Lean.
pub fn mldsa_keygen_real_export_present() -> bool {
    ffi::mldsa_keygen_real_present()
}

/// Run the VERIFIED, extracted REAL, FULL-BYTE ML-DSA-65 keygen core `@[export] dregg_mldsa_keygen_real`
/// (the executable `Dregg2.Crypto.MlDsaKeygen.mldsaKeygenRealFFI` over `mldsaKeygenInternal` — the
/// deterministic FIPS 204 ML-DSA.KeyGen_internal: H(ξ‖k‖ℓ) split, ExpandA, ExpandS, t = NTT⁻¹(Â∘NTT(s1))+s2,
/// Power2Round, pkEncode / skEncode). KAT-anchored vs the NIST ACVP `ML-DSA-keyGen-FIPS204` ML-DSA-65 vectors
/// (single-vector `native_decide`); the byte↔ring KeyGen refinement forall is OPEN.
///
/// Wire grammar the export reads:
///   * in:  `"hex(xi)"` (one lowercase-hex field over the real 32-byte ξ seed).
///   * out: `"hex(pk) hex(sk)"` — the 1952-byte public key + 4032-byte secret key as lowercase hex; `"ERR"`
///     for a malformed wire (the fail-closed answer the Rust caller treats as a keygen fault).
///
/// `dregg-pq::MlDsaKey::from_ed25519_seed` routes its ML-DSA keygen through this entry (installed via
/// `dregg_pq::install_verified_mldsa_keygen_core_real`), so the deployed IDENTITY-key derivation runs the
/// verified Lean core over the real bytes rather than the trusted `fips204` primitive. Returns `Err` if the
/// archive lacks the export.
pub fn shadow_mldsa_keygen_real(wire: &str) -> Result<String, String> {
    ffi::with_pq(|| ffi::lean_mldsa_keygen_real(wire))
}

/// Whether the linked archive exports the extracted, Lean-verified GRAIN R3 whole-history verify core
/// (`dregg_grain_r3_verify`, the C-ABI entry over `Dregg2.Grain.R3Verify.r3VerifyFFI` = the PROVED
/// `r3VerifyCore`). When false, a caller (`grain-verify::r3_verify`) cannot render the Lean-proven R3
/// decision and must surface the archive gap. Distinct from [`lean_available`]: a stale archive can
/// lack this export.
pub fn grain_r3_verify_core_available() -> bool {
    ffi::grain_r3_verify_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED, extracted GRAIN R3 whole-history verify core `@[export] dregg_grain_r3_verify`
/// (the executable `Dregg2.Grain.R3Verify.r3VerifyCore`, PROVED `r3_unfoolable` to reduce a grain's
/// `WHOLE_HISTORY_GAP` to the named `EngineSound` boundary + the R1 head binding). This runs the
/// R3-ACCEPT DECISION as a Lean-verified object (leanc-native): a whole-history proof cannot be
/// re-pointed at a foreign anchor (`r3_head_mismatch_rejected`), and a non-verifying aggregate rejects.
///
/// Wire grammar the export reads (WIDENED by wound #22 — `docs/WOUND-felt-width-boundaries-2026-07-19.md`;
/// the pre-repair three-int form now fails CLOSED, so a stale caller cannot re-open the ~31-bit binding):
///   * in:  33 decimal ints — `"aggregateVerified presentedVk[0..8] expectedVk[0..8]
///     aggregateHead[0..8] anchoredHead[0..8]"`. The status is the whole-chain STARK verifier's 0/1
///     (run against the CALLER'S anchor); `presentedVk` is the fingerprint RECOMPUTED from the
///     presented root and `expectedVk` the caller's out-of-band anchor, each as a `RecursionVk`'s 32
///     bytes in eight big-endian `u32` lanes; the two heads are the FULL 8-felt (~124-bit) state
///     anchors (`SEG_ANCHOR_WIDTH` lanes), not a lane-0 projection.
///   * out: `"1"` (accept) · `"0"` (reject) · `"2 <fault>"` (⚑ the wire could not be READ, so no R3
///     decision was made about anybody's history — `0` a token that is not a decimal integer, `1` a
///     token COUNT that is not 33, which is where a stale caller's pre-repair three-int wire lands).
///
/// ⚑ 2026-08-07: `"0"` used to be BOTH the whole-history REFUSAL and the fail-closed answer for a wire
/// the Lean parser could not read, and `grain_verify::r3_verify` turned both into
/// `R3Error::Rejected { aggregate_verified, aggregate_head, presented_vk, … }` — a diagnosis about the
/// renter's chain for a fault in how the binary was built. It now decodes to `R3Error::WireMalformed`.
/// The separation is proved both ways in `Dregg2.Grain.R3Verify` (`r3VerifyWire_eq_reject_iff` /
/// `r3VerifyWire_malformed_iff`).
///
/// `grain-verify::r3_verify` folds the finalized-turn chain, reads the verified-status from
/// `verify_whole_chain_proof_bytes`, and routes the accept decision through THIS entry — the DECISION is
/// the Lean-proven object, Rust is the thin marshaller. Returns `Err` if the archive lacks the export.
pub fn shadow_grain_r3_verify(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_grain_r3_verify(wire)
}

/// Whether the linked archive exports the extracted, Lean-verified HOLDING grant-weight verdict core
/// (`dregg_holding_grant_weight`, the C-ABI entry over `Metatheory.Bridge.ProofOfHoldings.grantWeightFFI`
/// = the PROVED `grantWeightCore`). When false, a caller (`dregg-governance::holding_weight::grant_weight`)
/// cannot render the Lean-proven weight verdict and must surface the archive gap. Distinct from
/// [`lean_available`]: a stale archive can lack this export.
pub fn holding_grant_weight_core_available() -> bool {
    ffi::holding_grant_weight_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED, extracted HOLDING grant-weight verdict core `@[export] dregg_holding_grant_weight`
/// (the executable `Metatheory.Bridge.ProofOfHoldings.grantWeightCore`, PROVED to REALIZE the
/// `grantsWeight` spec by `grantWeightCore_eq_grantsWeight`). This runs the fail-closed weight VERDICT as
/// a Lean-verified object (leanc-native): an `rpc`/StructureOnly tier or an unfinalized slot grants `0`
/// (refused), a consensus-proven finalized holding grants its full proven amount.
///
/// Wire grammar the export reads:
///   * in:  `"isConsensusProven slotFinal amount"` (three decimal ints — the holding's consensus-proof
///     status as 0/1, the light client's finality verdict as 0/1, and the proven balance).
///   * out: the granted weight as a decimal string (`= amount` when granted, `"0"` when refused; `"0"`
///     is also the fail-closed answer for a negative amount or a malformed wire).
///
/// `dregg-governance::holding_weight::grant_weight` does the fast-Rust PRE-CHECKS (the ed25519 owner→voter
/// binding, the consensus-proof read, the positive-amount check) and routes the weight VERDICT through
/// THIS entry — the DECISION is the Lean-proven object, Rust is the thin marshaller. Returns `Err` if the
/// archive lacks the export.
pub fn shadow_holding_grant_weight(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_holding_grant_weight(wire)
}

/// Whether the linked archive exports the extracted, Lean-verified INTERCHAIN reached-consensus
/// verdict core (`dregg_interchain_reached_consensus`, the C-ABI entry over
/// `Dregg2.Bridge.InterchainAdapterDecision.reachedConsensusFFI` = the PROVED `reachedConsensusWire`
/// over `reachedConsensusCore`). When false, a caller (`dregg-bridge::interchain_adapter`'s
/// `TrustRung::reached_consensus`) cannot render the Lean-proven trust verdict and MUST fail closed
/// (`consensus_verified = false`). Distinct from [`lean_available`]: a stale archive can lack this
/// export.
pub fn interchain_reached_consensus_core_available() -> bool {
    ffi::interchain_reached_consensus_present() && lean_init_once().is_ok()
}

/// Run the VERIFIED, extracted INTERCHAIN reached-consensus verdict core
/// `@[export] dregg_interchain_reached_consensus` (the executable
/// `Dregg2.Bridge.InterchainAdapterDecision.reachedConsensusWire`, PROVED to realize the
/// `reachesConsensusSpec` fail-closed spec by `reachedConsensusCore_correct` +
/// `reachedConsensusWire_realizes_core`). This runs the fail-closed bridge TRUST verdict as a
/// Lean-verified object (leanc-native): the `rpc` rung, an unresolved/fraud watchtower, a no-quorum
/// committee, and any unknown tag all yield `"0"` (refused — the Nomad-law default); a cryptographic
/// proof, a resolved-valid watchtower, and a quorum committee yield `"1"` (reached).
///
/// Wire grammar the export reads:
///   * in:  `"tag payload"` (two decimal ints — the rung selector `tag ∈ {0,1,2,3}` = proof /
///     watchtower / committee / rpc, and the watchtower/committee resolution bit `payload`).
///   * out: `"1"` (reached consensus) · `"0"` (refused; also the fail-closed answer for an unknown
///     tag or a malformed wire).
///
/// `dregg-bridge::interchain_adapter`'s `TrustRung::reached_consensus` marshals the rung onto the wire
/// and routes the verdict through THIS entry — the DECISION is the Lean-proven object, Rust is the
/// thin marshaller (the per-chain dial→rung `From`-conversions stay fast-Rust). Returns `Err` if the
/// archive lacks the export (the caller fails closed).
pub fn shadow_interchain_reached_consensus(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_interchain_reached_consensus(wire)
}

/// One shipped FRI knob set, as the [`fri_ledger`] wire carries it. The five deployed knobs plus the
/// extension degree that fixes the challenge-field size `|F| = babyBearP ^ ext_deg` — and the two
/// ε_C inputs that are NOT knobs at all (see [`FriKnobs::log_d0`] / [`FriKnobs::bciks_m`]).
///
/// This struct is a MARSHALLER, not a model: it computes nothing. Every soundness number for a knob
/// set comes back from Lean's `friLedger` (see [`fri_ledger`]).
///
/// ⚑ **No `Default`, and no defaulting inside `to_wire`.** `log_d0` and `bciks_m` change the reported
/// `commit_bits` (a `log_d0` move is worth ~2 bits per trace doubling), so a silent default here
/// would be this crate quietly choosing a soundness number on a caller's behalf. Callers name both
/// explicitly, at the call site, with a comment saying where the value came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FriKnobs {
    pub log_blowup: usize,
    pub num_queries: usize,
    pub query_pow_bits: usize,
    pub max_log_arity: usize,
    pub log_final_poly_len: usize,
    /// The degree of the challenge extension field. It lives in Rust as a TYPE
    /// (`BinomialExtensionField<P3BabyBear, 4>`) or a private `const D`, never as an exported `usize`
    /// — so a caller supplies it explicitly and the pin against the Lean model names it.
    pub ext_deg: usize,
    /// **NOT AN FRI KNOB.** `|D⁽⁰⁾| = 2 ^ log_d0` — the FRI domain size, i.e. trace height × blowup.
    /// It is a property of the STATEMENT being proved, not of the prover config: two turns run the
    /// same knobs at different trace heights and get different `commit_bits`. It rides this struct
    /// only because it rides the same wire; the model pin in the FRI gate does not pin it, because
    /// there is no Lean literal for "the height dregg's turns have".
    pub log_d0: usize,
    /// **NOT AN FRI KNOB.** BCIKS20's proximity parameter `m ≥ 3` (Thm 8.3) — a parameter of the
    /// ANALYSIS, not of the deployed prover. Nothing in the prover reads it; it selects which of a
    /// family of bounds the paper's theorem is instantiated at. Lean REFUSES `m < 3` (the paper's own
    /// hypothesis), so a caller cannot ask for a number no theorem backs.
    pub bciks_m: usize,
    /// **plonky3's SECOND grinding knob** — `commit_proof_of_work_bits` (`fri/src/config.rs:18`),
    /// ground per fold round after the round commitment is observed and before the folding challenge
    /// `β` is drawn (`fri/src/prover.rs:224`, checked `verifier.rs:222`). Unlike `query_pow_bits` it
    /// grinds against exactly the phase BCIKS20's `ε_C` bounds, so it moves
    /// [`FriLedger::commit_pow_branch`] one-for-one — the ONLY lever on that branch that is not a
    /// field-extension flag day.
    ///
    /// ⚑ It rides the wire but is NOT in Lean's `FriParams`, for the same reason `log_d0` is not:
    /// the four columns that predate it are functions of `FriParams` alone, and widening that
    /// structure would have silently moved them. ⚑ Lean REFUSES `commit_pow > 30`
    /// (`FriLedger.maxGrindBits`), because plonky3's `grind` asserts
    /// `(1u64 << bits) < F::ORDER_U64` over a single BabyBear witness — above 30 there is no prover,
    /// only a number.
    pub commit_pow: usize,
}

impl FriKnobs {
    /// The NINE-field wire the Lean export reads: the six knob fields, the two ε_C inputs
    /// (`logD0 bciksM`) that are not knobs, and the commit-phase grinding bits. Lean's
    /// `friLedgerFFI` refuses any other arity — including the EIGHT-field wire this replaced, which
    /// now fails closed rather than being read as nine with a defaulted `commit_pow`.
    pub fn to_wire(self) -> String {
        format!(
            "{} {} {} {} {} {} {} {} {}",
            self.log_blowup,
            self.num_queries,
            self.query_pow_bits,
            self.max_log_arity,
            self.log_final_poly_len,
            self.ext_deg,
            self.log_d0,
            self.bciks_m,
            self.commit_pow
        )
    }
}

/// The FRI soundness ledger of ONE config, as Lean's `friLedger` computed it. Every field is a
/// distinct quantity with a distinct justification; they are deliberately NOT collapsed into a single
/// headline. Rust never derives any of these — they are read off the wire.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FriLedger {
    /// Fold arity `m = 2 ^ max_log_arity`.
    pub arity: usize,
    /// Folded domain size `|κ| = 2 ^ log_blowup`.
    pub folded_domain: usize,
    /// `(m − 1) · C(|κ|, 2)` — the good-challenge count
    /// `FriArityTransfer.good_card_le_of_phase_injective` proves.
    pub good_count: usize,
    /// The PROVEN per-fold proximity-gap error exponent: `|Good| / |F| < 2 ^ (−perFoldBits)`
    /// (`FriLedgerSound.ledger_perFold_soundness`). Carries the `M = 1` fiber bound as a per-config
    /// HYPOTHESIS — discharged only at arity 2, `log_blowup = 6` in this tree.
    pub per_fold_bits: usize,
    /// `num_queries · log_blowup / 2 + query_pow_bits` — the Johnson query ledger, proven for any code.
    ///
    /// ⚑ **This is the `m → ∞` IDEALISATION of BCIKS20 Thm 8.3, and it DROPS ε_C.** `log_blowup/2` is
    /// `−log₂ α` in the limit of `α = √ρ·(1 + 1/2m)`; the paper's bound is `ε_FRI = ε_C + α^s`. The
    /// dropped term is [`FriLedger::commit_bits`], and at the deployed wrap it BINDS: this column
    /// reads `73`, but ethSTARK (eprint 2021/582) eq. (20) composes the two as
    /// `λ ≥ min{−log₂ ε_C, ζ − s·log₂ α} − 1` ⇒ **~70**. Read this as the query ledger it is, never as
    /// "the proven FRI soundness".
    pub johnson_bits: usize,
    /// `num_queries · log_blowup + query_pow_bits` — the capacity query ledger. The conjecture beneath
    /// it is REFUTED; a drift baseline, NOT a security number.
    ///
    /// ⚑ **THE CITATION, CORRECTED (2026-07-15).** This tree carried *"REFUTED (Kambiré, eprint
    /// 2025/2046)"*. That conflated two papers by different authors:
    ///
    ///   * **eprint 2025/2046 is Crites–Stewart** — Elizabeth Crites & Alistair Stewart (Web3
    ///     Foundation), *On Reed–Solomon Proximity Gaps Conjectures*. They disprove the BCIKS
    ///     up-to-capacity correlated-agreement conjecture (and WHIR's mutual-CA conjecture).
    ///   * **Kambiré is arXiv 2604.09724** — *Proximity Gaps Conjecture Fails Near Capacity over Prime
    ///     Fields*. His counterexample chooses the prime AS A FUNCTION OF the block length (`p < n^A`
    ///     with `p ≡ 1 mod n`, via a quantitative Linnik theorem), so `p` must GROW with `n` — it does
    ///     **not** instantiate at BabyBear's FIXED 31-bit prime.
    ///
    /// Both refute; attribute them correctly. ⚑ **The posture does NOT rest on that escape.** A
    /// conjecture refuted in general cannot be a security basis for anyone, whatever the
    /// field-cardinality technicality — "no counterexample reaches BabyBear" is true and is NOT a
    /// defence. This column stays a drift canary either way, and every claim stands on
    /// [`FriLedger::johnson_bits`] / [`FriLedger::commit_bits`].
    pub capacity_bits: usize,
    /// **The BCIKS20 COMMIT-PHASE error `ε_C`, as `⌊−log₂ ε_C⌋`** — the term [`FriLedger::johnson_bits`]
    /// drops. From **BCIKS20 (eprint 2020/654), Lemma 8.2 / Theorem 8.3, printed pp. 40–41**:
    ///
    /// ```text
    /// ε_FRI = ε_C + α^s ,   α = √ρ·(1 + 1/2m) ,   m ≥ 3
    /// ε_C   = (m+½)⁷·|D⁽⁰⁾|² / (2ρ^{3/2}|F|)  +  (2m+1)(|D⁽⁰⁾|+1)/√ρ · (Σᵢ l⁽ⁱ⁾)/|F|
    /// ```
    ///
    /// A LOWER bound on `−log₂ ε_C`: Lean's `friCommitLedger` over-estimates `ε_C` at every rounding,
    /// so this column rounds DOWN, never up.
    ///
    /// ⚑ **It is NOT trace-invariant.** `ε_C ∝ |D⁽⁰⁾|²/|F|`, and `|D⁽⁰⁾|` is the trace height × blowup
    /// — not an FRI knob. At the deployed wrap it reads `71` at `log_d0 = 12`, `69` at `13`, `55` at
    /// `20`: ~2 bits per trace DOUBLING. So there is no single "dregg's commit-phase bits"; there is
    /// one per trace height, and nobody has measured dregg's deployed trace-height distribution.
    ///
    /// ⚑ **It is a CEILING no knob can buy past.** `ε_C` contains no `num_queries` and no
    /// `query_pow_bits`, so raising queries or PoW moves this column by exactly ZERO. The only lever
    /// is `ext_deg`, worth `log₂ p ≈ 30.91` bits per degree (`ε_C ∝ 1/|F| = 1/p^ext_deg`).
    ///
    /// ⚑ **Kept SEPARATE.** This is never multiplied or `min`-ed into `johnson_bits` here. The `min`
    /// of ethSTARK eq. (20) is a reading a CALLER may take; the ledger reports the terms.
    pub commit_bits: usize,
    /// **The commit branch WITH grinding** — `commit_bits + commit_pow`, in the work-factor
    /// convention [`FriLedger::johnson_bits`] already uses for its own `query_pow_bits`. At
    /// `commit_pow = 0` it IS `commit_bits`, so this column cannot move a number the tree already
    /// reported (`FriCommitPow.commitPowBranch_at_zero_is_the_old_column`).
    pub commit_pow_branch: usize,
    /// **The Johnson branch at the SAME finite `m`** the commit branch is read at — `⌊−s·log₂ α⌋ +
    /// query_pow_bits` with `α = √ρ·(1 + 1/2m)`.
    ///
    /// ⚑ Strictly BELOW [`FriLedger::johnson_bits`], which is the `m → ∞` idealisation. The tree's
    /// standing composite took `min` of the commit branch at `m = 7` against `johnson_bits` at
    /// `m = ∞` — two different `m`, so not ethSTARK eq. (20) at all. This is the column that makes
    /// the `min` mean something.
    pub johnson_bits_at_m: usize,
    /// **ethSTARK eq. (20) at ONE `m`, with BOTH grinding terms** —
    /// `min{commit_pow_branch, johnson_bits_at_m} − 1`.
    ///
    /// ⚑ This is a CALCULATOR READING at the knobs named, never "the system has N bits". There is no
    /// adversary object anywhere in the Lean this comes from: the FRI extraction guarantee the apex
    /// consumes (`FriLdtExtractV3`) is still ASSUMED and none of these bits discharge it. Read it as
    /// the one number that moves when a knob moves, and check it against a config the prover RUNS —
    /// `circuit-prove/tests/fri_hundred_bit_cutover.rs` is the instrument for the second half.
    pub composite_bits: usize,
}

/// Whether the linked archive exports the FRI soundness ledger (`dregg_fri_ledger`, the C-ABI entry
/// over `Dregg2.Circuit.FriLedger.friLedgerFFI`). When false, a caller
/// (`circuit-prove/tests/fri_params_soundness_budget.rs`) cannot render the Lean-proved per-config
/// numbers and must surface the archive gap rather than fall back to computing them itself. Distinct
/// from [`lean_available`]: a stale archive can lack this export.
pub fn fri_ledger_available() -> bool {
    ffi::fri_ledger_present() && lean_init_once().is_ok()
}

/// **Run the FRI SOUNDNESS LEDGER `@[export] dregg_fri_ledger`** — the executable
/// `Dregg2.Circuit.FriLedger.friLedger`, the function `Dregg2.Circuit.FriLedgerSound` proves about
/// (`ledger_perFold_soundness`: at any config, a phase-injective word's good folding challenges have
/// density `< 2 ^ (−per_fold_bits)` in the degree-`ext_deg` extension, instantiating
/// `FriArityTransfer.good_card_le_of_phase_injective` at that config's arity and folded domain).
///
/// This is why the FRI params gate has no soundness arithmetic in it: the metatheory modeled these
/// numbers in detail, so Rust CALLS the model rather than re-typing its formulas and calling the
/// agreement a check. A re-derivation agrees with itself by construction; a call cannot.
///
/// Returns `Err` if the archive lacks the export, or if the wire came back malformed / fail-closed
/// (an out-of-window knob set — see `FriLedger.knobsInWindow`, or ε_C inputs outside
/// `FriLedger.epsCInWindow`, notably `bciks_m < 3`, which is BCIKS20 Thm 8.3's OWN hypothesis: below
/// it the formula is not the paper's, so Lean refuses rather than return a number no theorem backs).
pub fn fri_ledger(knobs: FriKnobs) -> Result<FriLedger, String> {
    ensure_lean_init()?;
    let out = ffi::lean_fri_ledger(&knobs.to_wire())?;
    let cols: Vec<&str> = out.split_whitespace().collect();
    if cols.len() != 10 {
        return Err(format!(
            "dregg_fri_ledger refused {:?} (fail-closed) or returned a malformed ledger: {out:?}",
            knobs.to_wire()
        ));
    }
    let n = |i: usize| -> Result<usize, String> {
        cols[i]
            .parse::<usize>()
            .map_err(|e| format!("ledger column {i} ({:?}) is not a nat: {e}", cols[i]))
    };
    Ok(FriLedger {
        arity: n(0)?,
        folded_domain: n(1)?,
        good_count: n(2)?,
        per_fold_bits: n(3)?,
        johnson_bits: n(4)?,
        capacity_bits: n(5)?,
        commit_bits: n(6)?,
        commit_pow_branch: n(7)?,
        johnson_bits_at_m: n(8)?,
        composite_bits: n(9)?,
    })
}

/// The grantor's pinned delegation parameters — the wire shape of the Lean
/// `Dregg2.Apps.DelegAdmit.Grant`. This is a MARSHALLING struct, not a policy: it carries the three
/// numbers to the boundary and holds no decision of its own.
///
/// * `tool_id` — the single allowlisted tool / MCP id the worker is scoped to (the SCOPE);
/// * `rate_limit` — the granted invocation ceiling `N` (the RATE);
/// * `deadline` — the expiry height/clock (the DEADLINE).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DelegGrant {
    /// The single allowlisted tool / MCP id (the SCOPE).
    pub tool_id: i64,
    /// The granted invocation ceiling `N` (the RATE).
    pub rate_limit: i64,
    /// The expiry height/clock (the DEADLINE).
    pub deadline: i64,
}

/// Whether the linked archive exports the DELEGATED TOOL/MCP-ACCESS admission decision
/// (`dregg_deleg_admit`, the C-ABI entry over `Dregg2.Apps.DelegAdmit.delegAdmitFFI`).
///
/// When false there is NO answer source: every gateway that used to carry its own `deleg_admit`
/// refuses. That is deliberate — the three Rust re-implementations this replaced are deleted, and a
/// wasm32 / `no-lean-link` build (which cannot link `libdregg_lean.a` at all) reads false here and
/// must say so rather than quietly re-deciding the policy in Rust. Distinct from [`lean_available`]:
/// a stale archive can lack this export. This initializes only the exact Init-only
/// admission module; full executor initialization remains deferred.
pub fn deleg_admit_available() -> bool {
    ffi::deleg_admit_present() && ffi::deleg_admit_init_once().is_ok()
}

/// **Run the DELEGATED TOOL/MCP-ACCESS admission decision `@[export] dregg_deleg_admit`** — the
/// executable `Dregg2.Apps.DelegAdmit.delegAdmit`, the five-conjunct predicate
/// `Dregg2.Apps.ToolAccessDelegation.tool_invocation_commit_iff_admit` proves the production
/// caveat-gated executor COMMITS a metered `calls_made : c → c+1` write IFF (and whose negations are
/// the `tool_invocation_over_rate_rejected` / `_past_deadline_rejected` / `_out_of_scope_rejected`
/// teeth):
///
/// 1. SCOPE — `tool == g.tool_id`;
/// 2. DEADLINE — `now <= g.deadline`;
/// 3. STEP — `new == old + 1`;
/// 4. SANE — `0 <= old`;
/// 5. RATE — `new <= g.rate_limit`.
///
/// `Ok(true)` = the delegated policy ADMITS the invocation; `Ok(false)` = it REFUSES. `Err` = **no
/// verdict was reached** (the archive lacks the export, the Lean runtime would not initialize, or the
/// wire came back malformed). The two are deliberately distinguishable and callers must treat `Err`
/// as a refusal WITH a distinct reason — an unanswered gate is not an open gate.
///
/// ⚑ This is a CALL, not a check. It exists because three Rust functions used to decide this — each
/// documented as "the byte-faithful Rust mirror" of the Lean, each maintained by hand, each backed by
/// a differential test that (there being no formal semantics of Rust) pinned drift and proved nothing
/// about any input the test did not enumerate. They are deleted; this is the only answer source.
pub fn deleg_admit(g: DelegGrant, now: i64, tool: i64, old: i64, new: i64) -> Result<bool, String> {
    let wire = format!(
        "{} {} {} {now} {tool} {old} {new}",
        g.tool_id, g.rate_limit, g.deadline
    );
    match ffi::lean_deleg_admit(&wire)?.trim() {
        "1" => Ok(true),
        "0" => Ok(false),
        other => Err(format!(
            "dregg_deleg_admit returned no verdict for {wire:?} (fail-closed): {other:?}"
        )),
    }
}

/// The five settled-line registers — the marshalling shape the `dregg_trustline_step` wire
/// carries, mirroring `Dregg2.Apps.TrustlineCore.SLine` (a `Line` plus the `settled` redemption
/// register).
///
/// ⚑ `settled` IS LOAD-BEARING AND ITS ABSENCE WOULD WIDEN A MONEY CHECK. The deployed cell
/// carries it (`node/src/trustline_service.rs:319-321`) and gates repay on `drawn − settled`
/// (`:1155-1161`), which is STRICTLY TIGHTER than the plain `amt ≤ drawn`. A shape without it
/// would admit every repay in `(drawn − settled, drawn]` that the node refuses today.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustlineChannel {
    /// The extended line `N` — the attenuation bound. Immutable for the line's life.
    pub ceiling: u64,
    /// Outstanding drawn amount (the Stingray `Slice::spent`).
    pub drawn: u64,
    /// Cumulative drawn value already redeemed to the holder. MONOTONE; `settled ≤ drawn`.
    pub settled: u64,
    /// The holder's credit balance in the issuer-asset: `+drawn` at every well-formed state.
    pub holder_acct: i64,
    /// The issuer's signed well: `−drawn`. The draw is PRODUCTION here, never a mint.
    pub issuer_well: i64,
    /// The committed draw-digest registry — the no-double-draw set. A digest is one-shot FOREVER;
    /// repayment does not resurrect it (`Dregg2.Apps.Trustline.repay_draws_fixed`).
    pub draws: Vec<[u8; 32]>,
}

impl TrustlineChannel {
    /// Outstanding unsettled draw — the deployed repay/settle budget.
    pub fn outstanding(&self) -> u64 {
        self.drawn.saturating_sub(self.settled)
    }
}

/// One trustline verb — the DEPLOYED verbs (`drawS` / `repayS` / `settleS`).
///
/// There is deliberately no verb for the fullReserve close. `trustline_service.rs:1424-1435`
/// moves `outstanding` from the trustline ESCROW to the HOLDER; the Lean `settlePay` moves the
/// opposite way over a different amount. No mapping is invented to make that arm look routed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustlineOp {
    /// Exercise the line: burn `digest`, draw `amount`.
    Draw {
        /// The one-shot debit digest (content-addressed; a repeat is REFUSED).
        digest: [u8; 32],
        /// The amount to draw.
        amount: u64,
    },
    /// Restore the line by `amount`, gated by the SETTLED FLOOR (`amount ≤ drawn − settled`).
    /// The digest registry is untouched.
    Repay {
        /// The amount to repay.
        amount: u64,
    },
    /// March the redemption register up by `paid`, leaving `drawn` and the registry in place.
    Settle {
        /// The amount redeemed to the holder this epoch.
        paid: u64,
    },
}

/// Render a 32-byte digest as its FULL decimal (schoolbook base-256 → base-10).
///
/// ⚑ This exists so a digest CANNOT be silently truncated. Lean's `draws` are arbitrary-precision
/// `Nat`, and folding a 32-byte hash into a `u64` would map distinct debits onto one burned digest
/// — defeating the very anti-replay leg (`draw_replay_refused`) this export is here to provide. A
/// `[u8; 32]` in the signature makes that mistake unrepresentable at the type level.
fn digest_to_decimal(digest: &[u8; 32]) -> String {
    let mut out: Vec<u8> = vec![0];
    for &byte in digest.iter() {
        let mut carry = byte as u32;
        for d in out.iter_mut() {
            let v = (*d as u32) * 256 + carry;
            *d = (v % 10) as u8;
            carry = v / 10;
        }
        while carry > 0 {
            out.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    out.iter().rev().map(|d| (b'0' + d) as char).collect()
}

/// Whether the linked archive exports the TRUSTLINE draw/repay/settle decision
/// (`dregg_trustline_step`, the C-ABI entry over `Dregg2.Apps.TrustlineCore.trustlineStepFFI`).
///
/// ⚠ READ THE TENSE. Today nothing routes through it, so `false` costs only a failing probe — the
/// ~16 Rust spend-authority implementations still decide it themselves. It is probed and REQUIRED
/// anyway so the `Dregg2/FFI.lean` rooting cannot silently regress in the window before routing
/// lands. Distinct from [`lean_available`]: a stale archive can lack this export.
pub fn trustline_step_available() -> bool {
    ffi::trustline_step_present() && lean_init_once().is_ok()
}

/// **Run the TRUSTLINE step decision `@[export] dregg_trustline_step`** — the executable
/// `Dregg2.Apps.TrustlineCore.{draw, repay, settlePay, settleAll}`, the objects
/// `Dregg2.Apps.Trustline`'s 101 kernel-clean theorems are stated over.
///
/// `Ok(Some(post))` = the op COMMITTED, and `post` is the verified post-state.
/// `Ok(None)` = the policy REFUSED it (a replayed digest, an over-line draw, or an over-repay) —
/// a verdict.
/// `Err` = **no verdict was reached** (the archive lacks the export, the Lean runtime would not
/// initialize, or the wire came back malformed). The three are deliberately distinguishable, and a
/// caller must treat `Err` as a refusal WITH a distinct reason — an unanswered gate is not an open
/// gate.
///
/// ⚑ The FULL digest registry travels in both directions on purpose. The anti-replay verdict is
/// decided in Lean, never summarised into a Rust-computed freshness bit — which is precisely the
/// check `turn/src/budget_gate.rs:29` keeps a `debits` list for and never performs.
pub fn trustline_step(
    channel: &TrustlineChannel,
    op: TrustlineOp,
) -> Result<Option<TrustlineChannel>, String> {
    ensure_lean_init()?;
    let (opcode, a1, a2) = match op {
        TrustlineOp::Draw { digest, amount } => {
            (0u8, digest_to_decimal(&digest), amount.to_string())
        }
        TrustlineOp::Repay { amount } => (1u8, amount.to_string(), "0".to_string()),
        TrustlineOp::Settle { paid } => (2u8, paid.to_string(), "0".to_string()),
    };
    let mut wire = format!(
        "{opcode} {} {} {} {} {} {a1} {a2} {}",
        channel.ceiling,
        channel.drawn,
        channel.settled,
        channel.holder_acct,
        channel.issuer_well,
        channel.draws.len()
    );
    for d in &channel.draws {
        wire.push(' ');
        wire.push_str(&digest_to_decimal(d));
    }
    let reply = ffi::lean_trustline_step(&wire)?;
    let reply = reply.trim();
    if reply.is_empty() {
        return Err(format!(
            "dregg_trustline_step returned no verdict for {wire:?} (fail-closed)"
        ));
    }
    if reply == "0" {
        return Ok(None);
    }
    // A COMMITTED draw burns its digest, so the post-state registry is `digest :: pre-state`. The
    // known set must therefore include the op's digest — it is fresh by construction (that freshness
    // is exactly what Lean just decided), so it is absent from `channel.draws`.
    let mut known = channel.draws.clone();
    if let TrustlineOp::Draw { digest, .. } = op {
        known.push(digest);
    }
    parse_trustline_reply(reply, &known)
        .map(Some)
        .ok_or_else(|| format!("dregg_trustline_step returned an unparsable post-state: {reply:?}"))
}

/// Decode the post-state wire. The digest registry comes back as decimals; we re-associate them
/// with the caller's `[u8; 32]` digests by decimal equality rather than re-deriving bytes from
/// decimal, so a mismatch is a parse failure (fail-closed) and never a silently wrong digest.
///
/// ⚑ The index is built ONCE. The first version of this function ran a linear `find` that
/// re-rendered `digest_to_decimal` per candidate per token — O(n²) renders, each itself a
/// 32-byte schoolbook base conversion. That is bomb #6 (`coord/src/budget.rs` using a `Vec` as
/// the anti-replay debit set) rebuilt at the FFI boundary, and
/// `coord/tests/perf_growth.rs::budget_anti_replay_is_subquadratic_in_debit_count` exists
/// precisely to keep it dead. n renders, then hash lookups.
fn parse_trustline_reply(reply: &str, known: &[[u8; 32]]) -> Option<TrustlineChannel> {
    let t: Vec<&str> = reply.split_whitespace().collect();
    if t.len() < 6 {
        return None;
    }
    let n: usize = t[5].parse().ok()?;
    if t.len() != 6 + n {
        return None;
    }
    let index: std::collections::HashMap<String, [u8; 32]> =
        known.iter().map(|d| (digest_to_decimal(d), *d)).collect();
    let mut draws = Vec::with_capacity(n);
    for tok in t.iter().skip(6) {
        // The post-state registry is the pre-state registry plus at most the digest just drawn, so
        // every decimal here must match one the caller already holds. Anything else is a wire fault.
        draws.push(*index.get(*tok)?);
    }
    Some(TrustlineChannel {
        ceiling: t[0].parse().ok()?,
        drawn: t[1].parse().ok()?,
        settled: t[2].parse().ok()?,
        holder_acct: t[3].parse().ok()?,
        issuer_well: t[4].parse().ok()?,
        draws,
    })
}

/// Whether the linked archive exports the automatafl GAME ORACLE (`dregg_automatafl_rules`, the
/// C-ABI entry over `Dregg2.Games.AutomataflFFI.rulesFFI`). When false, `dregg-automatafl` has NO
/// answer source for a board transition and its oracle calls fail closed — there is no Rust twin to
/// fall back to, by design (see [`automatafl_rules`]). Distinct from [`lean_available`]: a stale
/// archive can lack this export.
pub fn automatafl_rules_available() -> bool {
    ffi::automatafl_rules_present() && lean_init_once().is_ok()
}

/// **Run the automatafl GAME ORACLE `@[export] dregg_automatafl_rules`** — the verb-dispatched wire
/// over `Dregg2.Games.AutomataflRules`, the rules-faithful Lean spec the emitted Leg-R / Leg-A
/// descriptors are refined against.
///
/// `wire` is a verb-first token line (`stock` · `goals SIZE` · `sense TIE BOARD` · `step TIE BOARD` ·
/// `mid BOARD MARKS MOVES` · `turn TIE BOARD GOALS MARKS MOVES` · `legal BOARD MARKS MOVE` ·
/// `clash BOARD MARKS MOVES` · `round TIE BOARD GOALS MARKS LOCKED WAITING SUBS`); the grammar is
/// documented in that module's header, and `dregg-automatafl/src/board.rs` is the marshaller that
/// builds it. The reply is `"1 …"` on success and `"0"` fail-closed on a malformed wire.
///
/// ⚑ This exists because the thing it replaces was WRONG, not merely unproven.
/// `dregg-automatafl/src/reference.rs` was a hand transcription of `~/dev/automatafl/logic` — a
/// non-canonical experiment — and the conformance audit found that lineage divergent from the
/// Creator-Approved ruleset on 2-cycles (it SWAPPED the pair where the ruleset keeps both pieces put)
/// and on the path check (its occlusion scan skipped the DESTINATION, so a mover DESTROYED a
/// stationary piece). The witness generator consulted it as an oracle while the descriptor it fills
/// implements the ruleset — a divergence `resolve_witness.rs` documented rather than fixed. It is
/// deleted; this call is the only remaining answer source.
///
/// Returns `Err` if the archive lacks the export or Lean refused the wire.
pub fn automatafl_rules(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_automatafl_rules(wire)
}

/// Whether the linked archive exports the multiway-tug RULES ORACLE (`dregg_multiway_tug_rules`, the
/// C-ABI entry over `Dregg2.Games.MultiwayTugFFI.rulesFFI`). When false, every call below fails
/// closed. Distinct from [`lean_available`]: a stale archive can lack this export.
pub fn multiway_tug_rules_available() -> bool {
    ffi::multiway_tug_rules_present() && lean_init_once().is_ok()
}

/// **Run the multiway-tug RULES ORACLE `@[export] dregg_multiway_tug_rules`** — the verb-dispatched
/// wire over `Dregg2.Games.MultiwayTug`, the proven pure-transition spec whose conservation,
/// one-action-per-round, offer-interlock, scoring and win-safety theorems the emitted
/// `MultiwayTugProgram` teeth are pinned against.
///
/// `wire` is a verb-first token line (`charm` · `turns` · `legal STATE SEAT ACTION` ·
/// `legalresp STATE SEAT RESP` · `kinds STATE SEAT` · `split PEND RESP` · `act STATE SEAT ACTION` ·
/// `respond STATE SEAT RESP` · `control STATE` · `count STATE SEAT g` · `score STATE` ·
/// `won STATE SEAT` · `winner STATE` · `total STATE`); the grammar is documented in that module's
/// header. The reply is `"1 …"` on success and `"0"` fail-closed on a malformed wire.
///
/// ⚑ This exists because the Rust twin it replaces had already DRIFTED, not merely because it was
/// unproven. `dregg-multiway-tug/src/reference.rs::winner_of` is the model's `roundWinner` truncated
/// to its two absolute-threshold branches — no charm tie-break, no row tie-break — so on every round
/// where neither seat clears the bar it answers "no winner" where the model ADJUDICATES a seat
/// (`undecidedState_adjudicates`; the §7B fix that took the draw rate from 66.1% to 5.1%). It is also
/// the second known member of a class the twin-deletion sweep structurally could not see: that sweep
/// hunted twins of Lean AIR, and this is a twin of a Lean SPEC.
///
/// Returns `Err` if the archive lacks the export or Lean refused the wire.
pub fn multiway_tug_rules(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    ffi::lean_multiway_tug_rules(wire)
}

/// Parse a shadow output wire into a [`ShadowVerdict`], surfacing marshal/parse errors.
pub fn decode_shadow_verdict(output: &str) -> Result<ShadowVerdict, String> {
    match marshal::unmarshal_result(output) {
        Ok(r) => Ok(ShadowVerdict {
            // `committed` is the body-committed bit (status:2). The Lean export's `ok` already
            // narrows to BodyCommitted, but we recompute from `status` when present so a
            // prologue-only result (status:1) is NEVER reported as committed.
            committed: match r.status {
                Some(s) => s == TurnStatus::BodyCommitted,
                None => r.committed,
            },
            loglen: r.loglen,
            status: r.status,
            reason: r.reason,
            divergence_note: None,
        }),
        Err(e) => Err(e.to_string()),
    }
}

/// The verified Lean executor's verdict PAIRED WITH the full post-state it produced.
///
/// THE SWAP (authority inversion): `decode_shadow_verdict` keeps only the {committed, loglen,
/// status} bits and THROWS AWAY the `state` the verified executor produced — which is exactly the
/// gap that forces the legacy Rust `TurnExecutor` to remain the state PRODUCER. This decoder keeps
/// the post-state `WireState` so a caller can reconstitute the authoritative ledger from the
/// VERIFIED executor's output (see `dregg_turn::lean_apply::wire_state_to_ledger`).
///
/// `decode_shadow_verdict` is left intact (veto-only callers are unaffected); this is the additive
/// state-producing path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowState {
    /// The veto-shaped verdict bits (same as [`decode_shadow_verdict`]).
    pub verdict: ShadowVerdict,
    /// The FULL post-state the verified executor committed (on `committed`/rollback the echoed
    /// pre-state). This is the state-producer payload the swap installs as authoritative.
    pub state: WireState,
}

/// Parse a shadow output wire into a [`ShadowState`] — the verdict bits AND the produced
/// post-state. This is the state-PRODUCING decode (THE SWAP), as opposed to the veto-only
/// [`decode_shadow_verdict`] which discards `.state`.
pub fn decode_shadow_state(output: &str) -> Result<ShadowState, String> {
    match marshal::unmarshal_result(output) {
        Ok(r) => {
            let committed = match r.status {
                Some(s) => s == TurnStatus::BodyCommitted,
                None => r.committed,
            };
            Ok(ShadowState {
                verdict: ShadowVerdict {
                    committed,
                    loglen: r.loglen,
                    status: r.status,
                    reason: r.reason,
                    divergence_note: None,
                },
                state: r.state,
            })
        }
        Err(e) => Err(e.to_string()),
    }
}

// =============================================================================
// Lean FFI (present only when libdregg_lean.a was linked at build time)
// =============================================================================

#[cfg(lean_lib_present)]
mod ffi {
    use super::{LeanInitializationStatus, LeanRuntimeMode};
    use std::cell::Cell;
    use std::ffi::{CStr, CString};
    use std::os::raw::c_char;
    use std::sync::{Mutex, MutexGuard};
    use std::thread::ThreadId;

    extern "C" {
        // Private phases: only InitLifecycle may call these while holding INIT.
        fn dregg_ffi_start_runtime();
        fn dregg_ffi_start_runtime_st();
        fn dregg_ffi_init_modules() -> i32;
        fn dregg_ffi_init_st_modules() -> i32;
        fn dregg_ffi_init_deleg_admit_module() -> i32;
        fn dregg_ffi_init_executor_module() -> i32;
        fn dregg_ffi_init_pq_modules() -> i32;
        fn dregg_ffi_finish_initialization();
        fn dregg_ffi_last_failed_module() -> *const c_char;
        fn lean_initialize_thread();
        fn lean_finalize_thread();
        fn dregg_exec_full_forest_auth_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        fn dregg_record_kernel_step_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_handler_present)]
        fn dregg_exec_handler_turn_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_finalize_gate_present)]
        fn dregg_blocklace_finalize_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_decide_refines_present)]
        fn dregg_decide_refines_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_constraint_admits_present)]
        fn dregg_constraint_admits_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_cross_cell_conserves_present)]
        fn dregg_cross_cell_conserves_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_storage_content_root_present)]
        fn dregg_storage_content_root_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_fips204_verify_present)]
        fn dregg_fips204_verify_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_fips204_verify_real_present)]
        fn dregg_fips204_verify_real_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_fips204_sign_present)]
        fn dregg_fips204_sign_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_fips204_sign_real_present)]
        fn dregg_fips204_sign_real_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_fips203_encaps_present)]
        fn dregg_fips203_encaps_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_fips203_decaps_present)]
        fn dregg_fips203_decaps_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_mlkem_decaps_real_present)]
        fn dregg_mlkem_decaps_real_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_mlkem_encaps_real_present)]
        fn dregg_mlkem_encaps_real_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_mlkem_keygen_real_present)]
        fn dregg_mlkem_keygen_real_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_mldsa_keygen_real_present)]
        fn dregg_mldsa_keygen_real_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_grain_r3_verify_present)]
        fn dregg_grain_r3_verify_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_holding_grant_weight_present)]
        fn dregg_holding_grant_weight_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_interchain_reached_consensus_present)]
        fn dregg_interchain_reached_consensus_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_fri_ledger_present)]
        fn dregg_fri_ledger_str(in_utf8: *const c_char, out: *mut c_char, out_cap: usize) -> usize;
        #[cfg(dregg_deleg_admit_present)]
        fn dregg_deleg_admit_str(in_utf8: *const c_char, out: *mut c_char, out_cap: usize)
            -> usize;

        #[cfg(dregg_trustline_step_present)]
        fn dregg_trustline_step_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_automatafl_rules_present)]
        fn dregg_automatafl_rules_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_multiway_tug_rules_present)]
        fn dregg_multiway_tug_rules_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    // Lean 4.30's generated guard is a plain bool set BEFORE its imports run.
    // Independent OnceLocks can race shared imports or accept a failed initializer
    // on retry. One owner serializes all families and retains the first failure.
    struct InitLifecycle {
        status: LeanInitializationStatus,
        st_owner: Option<ThreadId>,
    }

    trait InitBackend {
        fn start_runtime(&mut self, mode: LeanRuntimeMode) -> Result<(), String>;
        fn attach_thread(&mut self);
        fn deleg_present(&self) -> bool;
        fn init_deleg(&mut self) -> Result<(), String>;
        fn executor_present(&self) -> bool;
        fn init_executor(&mut self) -> Result<(), String>;
        fn pq_present(&self) -> bool;
        fn init_pq(&mut self) -> Result<(), String>;
        fn init_full(&mut self, mode: LeanRuntimeMode) -> Result<(), String>;
        fn finish(&mut self);
    }

    impl InitLifecycle {
        const fn new() -> Self {
            Self {
                status: LeanInitializationStatus {
                    runtime_mode: None,
                    delegated_admission_ready: false,
                    executor_ready: false,
                    pq_ready: false,
                    default_full: None,
                    single_threaded_full: None,
                    failure: None,
                },
                st_owner: None,
            }
        }

        fn retain_failure(&mut self, result: Result<(), String>) -> Result<(), String> {
            if let Err(error) = result {
                let original = self.status.failure.get_or_insert(error).clone();
                Err(original)
            } else {
                Ok(())
            }
        }

        fn ensure_runtime(
            &mut self,
            mode: LeanRuntimeMode,
            backend: &mut impl InitBackend,
        ) -> Result<(), String> {
            if let Some(error) = &self.status.failure {
                return Err(error.clone());
            }
            if let Some(selected) = self.status.runtime_mode {
                if selected != mode {
                    return Err(format!(
                        "Lean runtime mode is {selected:?}; refusing incompatible {mode:?} initialization"
                    ));
                }
                if selected == LeanRuntimeMode::SingleThreaded
                    && self.st_owner != Some(std::thread::current().id())
                {
                    return Err(
                        "single-threaded Lean runtime belongs to another host thread".into(),
                    );
                }
            } else {
                self.status.runtime_mode = Some(mode);
                if mode == LeanRuntimeMode::SingleThreaded {
                    self.st_owner = Some(std::thread::current().id());
                }
                self.retain_failure(backend.start_runtime(mode))?;
            }
            backend.attach_thread();
            Ok(())
        }

        fn ensure_deleg(&mut self, backend: &mut impl InitBackend) -> Result<(), String> {
            if !backend.deleg_present() {
                return Err("Lean DelegAdmit export/initializer pair is not linked".into());
            }
            let mode = self.status.runtime_mode.unwrap_or(LeanRuntimeMode::Default);
            self.ensure_runtime(mode, backend)?;
            if !self.status.delegated_admission_ready {
                self.retain_failure(backend.init_deleg())?;
                self.status.delegated_admission_ready = true;
            }
            // Do not end initialization here. The pure Init-only admission body
            // is allowed, but a later full closure still needs registration open.
            Ok(())
        }

        fn ensure_executor(&mut self, backend: &mut impl InitBackend) -> Result<(), String> {
            if !backend.executor_present() {
                return Err(
                    "Lean FFIDirect export/builder/initializer family is not linked".into(),
                );
            }
            // The ST family's historical module list does not include FFIDirect.
            // Do not change its contract or add modules after its end marker.
            self.ensure_runtime(LeanRuntimeMode::Default, backend)?;
            if !self.status.executor_ready {
                self.retain_failure(backend.init_executor())?;
                self.status.executor_ready = true;
            }
            Ok(())
        }

        /// The verified PQ cores alone. Signing, verifying and key generation
        /// need these modules and none of the executor or game families, whose
        /// initializers are the whole cost of a full init. Like `ensure_deleg`,
        /// this leaves registration open for a later full init.
        fn ensure_pq(&mut self, backend: &mut impl InitBackend) -> Result<(), String> {
            if !backend.pq_present() {
                return Err("no verified PQ core export/initializer pair is linked".into());
            }
            let mode = self.status.runtime_mode.unwrap_or(LeanRuntimeMode::Default);
            self.ensure_runtime(mode, backend)?;
            if !self.status.pq_ready {
                // A successful default full init lists these modules and sets
                // `pq_ready`. The single-threaded list does not, and it has
                // already ended registration, so running them now is refused.
                if self.status.single_threaded_full.is_some() {
                    return Err(
                        "single-threaded Lean initialization ended without the PQ family".into(),
                    );
                }
                self.retain_failure(backend.init_pq())?;
                self.status.pq_ready = true;
            }
            Ok(())
        }

        fn ensure_full(
            &mut self,
            mode: LeanRuntimeMode,
            backend: &mut impl InitBackend,
        ) -> Result<(), String> {
            // Even a cached success must check the mode/owner and attach this
            // native caller thread before it allocates any Lean objects.
            self.ensure_runtime(mode, backend)?;
            let previous = match mode {
                LeanRuntimeMode::Default => &self.status.default_full,
                LeanRuntimeMode::SingleThreaded => &self.status.single_threaded_full,
            };
            if let Some(result) = previous {
                return result.clone();
            }
            let result = (|| {
                // Full-first callers must also initialize this family before
                // the one-way end marker; absent optional exports stay absent.
                if backend.deleg_present() {
                    self.ensure_deleg(backend)?;
                }
                self.retain_failure(backend.init_full(mode))?;
                if mode == LeanRuntimeMode::Default {
                    self.status.executor_ready = backend.executor_present();
                    self.status.pq_ready = backend.pq_present();
                }
                backend.finish();
                Ok(())
            })();
            match mode {
                LeanRuntimeMode::Default => self.status.default_full = Some(result.clone()),
                LeanRuntimeMode::SingleThreaded => {
                    self.status.single_threaded_full = Some(result.clone())
                }
            }
            result
        }
    }

    static INIT: Mutex<InitLifecycle> = Mutex::new(InitLifecycle::new());

    fn lock_lifecycle(
        lock: &Mutex<InitLifecycle>,
    ) -> Result<MutexGuard<'_, InitLifecycle>, String> {
        lock.lock().map_err(|poisoned| {
            poisoned
                .into_inner()
                .status
                .failure
                .clone()
                .unwrap_or_else(|| {
                    "Lean initialization lifecycle unwound; process restart required".into()
                })
        })
    }

    fn lifecycle() -> Result<MutexGuard<'static, InitLifecycle>, String> {
        lock_lifecycle(&INIT)
    }

    // A runtime-starting thread already owns its allocator heap. Attaching it
    // again is invalid with LEAN_SMALL_ALLOCATOR; finalizing it here would also
    // claim ownership of the process's original runtime thread lifecycle.
    #[derive(Clone, Copy)]
    enum ThreadAttachment {
        None,
        RuntimeOwner,
        Attached,
    }

    struct HostThread(Cell<ThreadAttachment>);
    impl Drop for HostThread {
        fn drop(&mut self) {
            if matches!(self.0.get(), ThreadAttachment::Attached) {
                unsafe { lean_finalize_thread() };
            }
        }
    }
    thread_local! {
        static HOST_THREAD: HostThread = const { HostThread(Cell::new(ThreadAttachment::None)) };
    }

    struct NativeInit;
    impl NativeInit {
        fn module_result(rc: i32, family: &str) -> Result<(), String> {
            if rc == 0 {
                return Ok(());
            }
            let failed = unsafe { dregg_ffi_last_failed_module() };
            let name = if failed.is_null() {
                family.to_owned()
            } else {
                unsafe { CStr::from_ptr(failed) }
                    .to_string_lossy()
                    .into_owned()
            };
            Err(format!(
                "Lean initializer {name} failed (rc={rc}); process restart required"
            ))
        }
    }
    impl InitBackend for NativeInit {
        fn start_runtime(&mut self, mode: LeanRuntimeMode) -> Result<(), String> {
            let profile = std::env::var("DREGG_LEAN_INIT_PROFILE").as_deref() == Ok("1");
            let started = profile.then(std::time::Instant::now);
            unsafe {
                match mode {
                    LeanRuntimeMode::Default => dregg_ffi_start_runtime(),
                    LeanRuntimeMode::SingleThreaded => dregg_ffi_start_runtime_st(),
                }
            }
            HOST_THREAD.with(|thread| thread.0.set(ThreadAttachment::RuntimeOwner));
            if let Some(started) = started {
                use std::io::Write;
                let _ = writeln!(
                    std::io::stderr().lock(),
                    "[dregg lean init] runtime={mode:?} elapsed_ms={:.3}",
                    started.elapsed().as_secs_f64() * 1000.0
                );
            }
            Ok(())
        }
        fn attach_thread(&mut self) {
            HOST_THREAD.with(|thread| {
                if matches!(thread.0.get(), ThreadAttachment::None) {
                    unsafe { lean_initialize_thread() };
                    thread.0.set(ThreadAttachment::Attached);
                }
            });
        }
        fn deleg_present(&self) -> bool {
            deleg_admit_present()
        }
        fn init_deleg(&mut self) -> Result<(), String> {
            Self::module_result(unsafe { dregg_ffi_init_deleg_admit_module() }, "DelegAdmit")
        }
        fn executor_present(&self) -> bool {
            cfg!(dregg_direct_present)
        }
        fn init_executor(&mut self) -> Result<(), String> {
            Self::module_result(unsafe { dregg_ffi_init_executor_module() }, "FFIDirect")
        }
        fn pq_present(&self) -> bool {
            fips204_verify_real_present()
                || fips204_sign_real_present()
                || mldsa_keygen_real_present()
                || mlkem_encaps_real_present()
                || mlkem_decaps_real_present()
                || mlkem_keygen_real_present()
        }
        fn init_pq(&mut self) -> Result<(), String> {
            Self::module_result(unsafe { dregg_ffi_init_pq_modules() }, "PQ family")
        }
        fn init_full(&mut self, mode: LeanRuntimeMode) -> Result<(), String> {
            let rc = unsafe {
                match mode {
                    LeanRuntimeMode::Default => dregg_ffi_init_modules(),
                    LeanRuntimeMode::SingleThreaded => dregg_ffi_init_st_modules(),
                }
            };
            Self::module_result(rc, "full module family")
        }
        fn finish(&mut self) {
            unsafe { dregg_ffi_finish_initialization() };
        }
    }

    fn status_of(lock: &Mutex<InitLifecycle>) -> LeanInitializationStatus {
        match lock.lock() {
            Ok(state) => state.status.clone(),
            Err(poisoned) => {
                let mut status = poisoned.into_inner().status.clone();
                status.failure.get_or_insert_with(|| {
                    "Lean initialization lifecycle unwound; process restart required".into()
                });
                status
            }
        }
    }
    pub fn initialization_status() -> LeanInitializationStatus {
        status_of(&INIT)
    }
    pub fn lean_init_status() -> Option<Result<(), String>> {
        match lifecycle() {
            Ok(state) => state.status.default_full.clone(),
            Err(error) => Some(Err(error)),
        }
    }
    pub fn lean_init_once() -> Result<(), String> {
        lifecycle()?.ensure_full(LeanRuntimeMode::Default, &mut NativeInit)
    }
    pub fn lean_init_st_once() -> Result<(), String> {
        lifecycle()?.ensure_full(LeanRuntimeMode::SingleThreaded, &mut NativeInit)
    }
    pub fn deleg_admit_init_once() -> Result<(), String> {
        lifecycle()?.ensure_deleg(&mut NativeInit)
    }

    pub fn executor_init_once() -> Result<(), String> {
        lifecycle()?.ensure_executor(&mut NativeInit)
    }

    pub fn with_executor<T>(body: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
        let mut state = lifecycle()?;
        state.ensure_executor(&mut NativeInit)?;
        if matches!(state.status.default_full, Some(Ok(()))) {
            // All module globals are frozen. Preserve normal parallel execution.
            drop(state);
            return body();
        }
        // Keep partial-initialization execution serialized with module registration.
        // Callers must drain all Lean objects before returning owned Rust values.
        let result = body();
        drop(state);
        result
    }

    pub fn pq_init_once() -> Result<(), String> {
        lifecycle()?.ensure_pq(&mut NativeInit)
    }

    /// Run a verified PQ core under the narrow PQ family, with the same
    /// serialization rule as `with_executor`.
    pub fn with_pq<T>(body: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
        let mut state = lifecycle()?;
        state.ensure_pq(&mut NativeInit)?;
        if matches!(state.status.default_full, Some(Ok(()))) {
            drop(state);
            return body();
        }
        let result = body();
        drop(state);
        result
    }

    #[cfg(test)]
    mod initialization_failure_tests {
        use super::*;

        #[derive(Default)]
        struct Backend {
            calls: Vec<&'static str>,
            fail: Option<&'static str>,
            unwind: bool,
        }
        impl Backend {
            fn step(&mut self, name: &'static str) -> Result<(), String> {
                self.calls.push(name);
                if name == "deleg" && self.unwind {
                    panic!("test-owned initializer unwind");
                }
                if self.fail == Some(name) {
                    Err(format!("{name} failed after guard set"))
                } else {
                    Ok(())
                }
            }
        }
        impl InitBackend for Backend {
            fn start_runtime(&mut self, _: LeanRuntimeMode) -> Result<(), String> {
                self.step("runtime")
            }
            fn attach_thread(&mut self) {}
            fn deleg_present(&self) -> bool {
                true
            }
            fn init_deleg(&mut self) -> Result<(), String> {
                self.step("deleg")
            }
            fn executor_present(&self) -> bool {
                true
            }
            fn init_executor(&mut self) -> Result<(), String> {
                self.step("executor")
            }
            fn pq_present(&self) -> bool {
                true
            }
            fn init_pq(&mut self) -> Result<(), String> {
                self.step("pq")
            }
            fn init_full(&mut self, _: LeanRuntimeMode) -> Result<(), String> {
                self.step("full")
            }
            fn finish(&mut self) {
                self.calls.push("end");
            }
        }

        #[test]
        fn init_lifecycle_failed_executor_refuses_every_family() {
            let mut state = InitLifecycle::new();
            let mut backend = Backend {
                fail: Some("executor"),
                ..Default::default()
            };
            let error = state.ensure_executor(&mut backend).unwrap_err();
            backend.fail = None;
            let calls = backend.calls.clone();
            assert_eq!(state.ensure_executor(&mut backend), Err(error.clone()));
            assert_eq!(state.ensure_deleg(&mut backend), Err(error.clone()));
            assert_eq!(
                state.ensure_full(LeanRuntimeMode::Default, &mut backend),
                Err(error)
            );
            assert_eq!(backend.calls, calls);
            assert!(!state.status.executor_ready);
            assert_eq!(state.status.default_full, None);
        }

        #[test]
        fn init_lifecycle_pq_family_is_narrow_and_leaves_registration_open() {
            let mut state = InitLifecycle::new();
            let mut backend = Backend::default();
            state.ensure_pq(&mut backend).unwrap();
            state.ensure_pq(&mut backend).unwrap();
            assert_eq!(backend.calls, ["runtime", "pq"], "once, and only the PQ family");
            assert!(state.status.pq_ready);
            assert!(!state.status.executor_ready);
            assert!(!state.status.delegated_admission_ready);
            assert_eq!(state.status.default_full, None);
            state
                .ensure_full(LeanRuntimeMode::Default, &mut backend)
                .unwrap();
            assert_eq!(backend.calls, ["runtime", "pq", "deleg", "full", "end"]);
            assert!(state.status.pq_ready);
        }

        #[test]
        fn init_lifecycle_full_first_makes_the_pq_family_a_no_op() {
            let mut state = InitLifecycle::new();
            let mut backend = Backend::default();
            state
                .ensure_full(LeanRuntimeMode::Default, &mut backend)
                .unwrap();
            let calls = backend.calls.clone();
            state.ensure_pq(&mut backend).unwrap();
            assert_eq!(backend.calls, calls, "the default full list already ran the PQ modules");
            assert!(state.status.pq_ready);
        }

        #[test]
        fn init_lifecycle_failed_pq_family_refuses_every_family() {
            let mut state = InitLifecycle::new();
            let mut backend = Backend {
                fail: Some("pq"),
                ..Default::default()
            };
            let error = state.ensure_pq(&mut backend).unwrap_err();
            backend.fail = None;
            let calls = backend.calls.clone();
            assert_eq!(state.ensure_pq(&mut backend), Err(error.clone()));
            assert_eq!(
                state.ensure_full(LeanRuntimeMode::Default, &mut backend),
                Err(error)
            );
            assert_eq!(backend.calls, calls);
            assert!(!state.status.pq_ready);
            assert!(!backend.calls.contains(&"end"));
        }

        #[test]
        fn init_lifecycle_pq_after_single_threaded_full_is_refused() {
            let mut state = InitLifecycle::new();
            let mut backend = Backend::default();
            state
                .ensure_full(LeanRuntimeMode::SingleThreaded, &mut backend)
                .unwrap();
            let calls = backend.calls.clone();
            assert!(state
                .ensure_pq(&mut backend)
                .unwrap_err()
                .contains("without the PQ family"));
            assert_eq!(backend.calls, calls, "no module initializer after the end marker");
            assert!(!state.status.pq_ready);
        }

        #[test]
        fn init_lifecycle_failed_module_never_retries_a_set_generated_guard() {
            for fail in ["deleg", "full"] {
                let mut state = InitLifecycle::new();
                let mut backend = Backend {
                    fail: Some(fail),
                    ..Default::default()
                };
                let error = state
                    .ensure_full(LeanRuntimeMode::Default, &mut backend)
                    .unwrap_err();
                let completed_calls = backend.calls.clone();
                backend.fail = None;
                assert_eq!(state.ensure_deleg(&mut backend), Err(error.clone()));
                assert_eq!(
                    state.ensure_full(LeanRuntimeMode::Default, &mut backend),
                    Err(error.clone())
                );
                assert_eq!(
                    state.ensure_full(LeanRuntimeMode::SingleThreaded, &mut backend),
                    Err(error)
                );
                assert_eq!(
                    backend.calls, completed_calls,
                    "failure is sticky across every family"
                );
                assert!(
                    !backend.calls.contains(&"end"),
                    "failed init cannot mark initialization complete"
                );
            }
        }

        #[test]
        fn init_lifecycle_unwind_refuses_without_reentering_partial_modules() {
            let state = Mutex::new(InitLifecycle::new());
            let mut backend = Backend {
                unwind: true,
                ..Default::default()
            };
            let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                lock_lifecycle(&state)
                    .unwrap()
                    .ensure_deleg(&mut backend)
                    .unwrap();
            }));
            assert!(panic.is_err());
            for _ in 0..2 {
                assert!(lock_lifecycle(&state)
                    .err()
                    .unwrap()
                    .contains("process restart required"));
            }
            let status = status_of(&state);
            assert_eq!(status.runtime_mode, Some(LeanRuntimeMode::Default));
            assert!(!status.delegated_admission_ready);
            assert!(status.failure.unwrap().contains("process restart required"));
            assert_eq!(backend.calls, ["runtime", "deleg"]);
        }

        #[test]
        fn init_lifecycle_mode_refusal_preserves_the_selected_runtime() {
            let mut state = InitLifecycle::new();
            let mut backend = Backend::default();
            state
                .ensure_full(LeanRuntimeMode::SingleThreaded, &mut backend)
                .unwrap();
            let status = state.status.clone();
            assert!(state
                .ensure_full(LeanRuntimeMode::Default, &mut backend)
                .is_err());
            let (mut state, mut backend) = std::thread::spawn(move || {
                assert!(state
                    .ensure_deleg(&mut backend)
                    .unwrap_err()
                    .contains("another host thread"));
                (state, backend)
            })
            .join()
            .unwrap();
            state.ensure_deleg(&mut backend).unwrap();
            assert_eq!(state.status, status);
            assert_eq!(backend.calls, ["runtime", "deleg", "full", "end"]);
        }
    }

    fn lean_string_bridge(
        wire: &str,
        f: unsafe extern "C" fn(*const c_char, *mut c_char, usize) -> usize,
        err_label: &str,
    ) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 1024;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe { f(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap) };
            if full == usize::MAX {
                return Err(format!("{err_label}: unusable output buffer"));
            }
            if full < cap {
                let nul = buf.iter().position(|&b| b == 0).unwrap_or(full);
                return String::from_utf8(buf[..nul].to_vec())
                    .map_err(|e| format!("result not UTF-8: {e}"));
            }
            cap = full + 1;
        }
    }

    pub fn lean_forest_auth(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_exec_full_forest_auth_str,
            "dregg_exec_full_forest_auth_str",
        )
    }

    pub fn lean_record_kernel_step(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_record_kernel_step_str,
            "dregg_record_kernel_step_str",
        )
    }

    #[cfg(dregg_handler_present)]
    pub fn lean_handler_turn(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_exec_handler_turn_str,
            "dregg_exec_handler_turn_str",
        )
    }

    #[cfg(not(dregg_handler_present))]
    pub fn lean_handler_turn(_wire: &str) -> Result<String, String> {
        Err("dregg_exec_handler_turn not exported by the linked archive (rebuild to enable)".into())
    }

    #[cfg(dregg_finalize_gate_present)]
    pub fn finality_gate_present() -> bool {
        true
    }

    #[cfg(not(dregg_finalize_gate_present))]
    pub fn finality_gate_present() -> bool {
        false
    }

    #[cfg(dregg_finalize_gate_present)]
    pub fn lean_blocklace_finalize(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_blocklace_finalize_str,
            "dregg_blocklace_finalize_str",
        )
    }

    #[cfg(not(dregg_finalize_gate_present))]
    pub fn lean_blocklace_finalize(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_blocklace_finalize not exported by the linked archive (rebuild to enable)"
                .into(),
        )
    }

    #[cfg(dregg_decide_refines_present)]
    pub fn decide_refines_present() -> bool {
        true
    }

    #[cfg(not(dregg_decide_refines_present))]
    pub fn decide_refines_present() -> bool {
        false
    }

    #[cfg(dregg_decide_refines_present)]
    pub fn lean_decide_refines(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_decide_refines_str, "dregg_decide_refines_str")
    }

    #[cfg(not(dregg_decide_refines_present))]
    pub fn lean_decide_refines(_wire: &str) -> Result<String, String> {
        Err("dregg_decide_refines not exported by the linked archive (rebuild to enable)".into())
    }

    #[cfg(dregg_constraint_admits_present)]
    pub fn constraint_admits_present() -> bool {
        true
    }

    #[cfg(not(dregg_constraint_admits_present))]
    pub fn constraint_admits_present() -> bool {
        false
    }

    #[cfg(dregg_constraint_admits_present)]
    pub fn lean_constraint_admits(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_constraint_admits_str,
            "dregg_constraint_admits_str",
        )
    }

    #[cfg(not(dregg_constraint_admits_present))]
    pub fn lean_constraint_admits(_wire: &str) -> Result<String, String> {
        Err("dregg_constraint_admits not exported by the linked archive (rebuild to enable)".into())
    }

    #[cfg(dregg_cross_cell_conserves_present)]
    pub fn cross_cell_conserves_present() -> bool {
        true
    }

    #[cfg(not(dregg_cross_cell_conserves_present))]
    pub fn cross_cell_conserves_present() -> bool {
        false
    }

    #[cfg(dregg_cross_cell_conserves_present)]
    pub fn lean_cross_cell_conserves(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_cross_cell_conserves_str,
            "dregg_cross_cell_conserves_str",
        )
    }

    #[cfg(not(dregg_cross_cell_conserves_present))]
    pub fn lean_cross_cell_conserves(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_cross_cell_conserves not exported by the linked archive (rebuild to enable)"
                .into(),
        )
    }

    /// STORAGE-IN-LEAN EXTRACTION — run the VERIFIED Lean content-root over the deployed Poseidon2.
    /// Input: space-separated object int-triples; output: the content root as a decimal string.
    #[cfg(dregg_storage_content_root_present)]
    pub fn lean_storage_content_root(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_storage_content_root_str,
            "dregg_storage_content_root_str",
        )
    }

    /// FIPS-204-VERIFY EXTRACTION — run the VERIFIED Lean ML-DSA verify core (leanc-native).
    /// Input: `"thi μ c̃ z h"` (five decimal ints); output: `"1"` (accept) / `"0"` (reject). This is
    /// the SECURITY-CRITICAL verify direction as a Lean-verified object: the extracted `verifyCore`
    /// (= `Fips204Spec.verifyB` at the deployed ML-DSA-65 parameters), proved to reject forgeries.
    #[cfg(dregg_fips204_verify_present)]
    pub fn lean_fips204_verify(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_fips204_verify_str, "dregg_fips204_verify_str")
    }

    #[cfg(not(dregg_fips204_verify_present))]
    pub fn lean_fips204_verify(_wire: &str) -> Result<String, String> {
        Err("dregg_fips204_verify not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted ML-DSA verify core.
    #[cfg(dregg_fips204_verify_present)]
    pub fn fips204_verify_present() -> bool {
        true
    }

    #[cfg(not(dregg_fips204_verify_present))]
    pub fn fips204_verify_present() -> bool {
        false
    }

    /// FIPS-204-VERIFY-REAL extraction (BRICK 8) — run the VERIFIED Lean ML-DSA verify core over the REAL,
    /// FULL-BYTE key/signature (leanc-native). Input: `"hex(pk) hex(msg) hex(ctx) hex(sig)"` (four
    /// space-separated lowercase-hex fields); output: `"1"` (accept) / `"0"` (reject, and the fail-closed
    /// answer for a malformed wire). This is the FULL-DIMENSION `MlDsaVerifyReal.verifyCore` (n=256 ring /
    /// NTT / SampleInBall / ExpandA / real 1952/3309-byte codec, proved to accept a genuine crate
    /// signature and reject tampers) — the object `dregg-pq::ml_dsa_verify` routes through to take the
    /// `fips204` crate OUT of the verify TCB.
    #[cfg(dregg_fips204_verify_real_present)]
    pub fn lean_fips204_verify_real(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_fips204_verify_real_str,
            "dregg_fips204_verify_real_str",
        )
    }

    #[cfg(not(dregg_fips204_verify_real_present))]
    pub fn lean_fips204_verify_real(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_fips204_verify_real not exported by the linked archive (rebuild to enable)"
                .into(),
        )
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-DSA verify core.
    #[cfg(dregg_fips204_verify_real_present)]
    pub fn fips204_verify_real_present() -> bool {
        true
    }

    #[cfg(not(dregg_fips204_verify_real_present))]
    pub fn fips204_verify_real_present() -> bool {
        false
    }

    /// FIPS-204-SIGN EXTRACTION — run the VERIFIED Lean ML-DSA sign core (leanc-native).
    /// Input: `"s1 s2 t0 μ y"` (secret + message + the sampled randomness/mask); output: the signature
    /// wire `"c̃ z h"` (an accepted iteration) or `"REJECT"` (a rejected sample / malformed wire, retry).
    /// This is the SIGNING direction as a Lean-verified object: the extracted `signCore` (the
    /// Fiat–Shamir-with-aborts signer at the deployed ML-DSA-65 parameters), proved to round-trip
    /// through `verifyCore`.
    #[cfg(dregg_fips204_sign_present)]
    pub fn lean_fips204_sign(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_fips204_sign_str, "dregg_fips204_sign_str")
    }

    #[cfg(not(dregg_fips204_sign_present))]
    pub fn lean_fips204_sign(_wire: &str) -> Result<String, String> {
        Err("dregg_fips204_sign not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted ML-DSA sign core.
    #[cfg(dregg_fips204_sign_present)]
    pub fn fips204_sign_present() -> bool {
        true
    }

    #[cfg(not(dregg_fips204_sign_present))]
    pub fn fips204_sign_present() -> bool {
        false
    }

    /// FIPS-204-SIGN-REAL extraction (the brick-8 SIGN analog) — run the VERIFIED Lean ML-DSA sign core over
    /// the REAL, FULL-BYTE key (leanc-native). Input: `"hex(sk) hex(msg) hex(ctx)"` (three space-separated
    /// lowercase-hex fields over the real 4032-byte secret key); output: `hex(sig)` (the 3309-byte signature
    /// as lowercase hex) / `"ERR"` (the fail-closed answer for a malformed wire). This is the FULL-DIMENSION
    /// `MlDsaSignReal.signCore` (n=256 ring / NTT / SampleInBall / ExpandA / MakeHint / rejection loop / real
    /// 4032/3309-byte codec, proved to reproduce a genuine crate deterministic signature byte-for-byte) — the
    /// object `dregg-pq::MlDsaKey::sign` routes through to take the `fips204` crate OUT of the sign TCB.
    #[cfg(dregg_fips204_sign_real_present)]
    pub fn lean_fips204_sign_real(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_fips204_sign_real_str,
            "dregg_fips204_sign_real_str",
        )
    }

    #[cfg(not(dregg_fips204_sign_real_present))]
    pub fn lean_fips204_sign_real(_wire: &str) -> Result<String, String> {
        Err("dregg_fips204_sign_real not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-DSA sign core.
    #[cfg(dregg_fips204_sign_real_present)]
    pub fn fips204_sign_real_present() -> bool {
        true
    }

    #[cfg(not(dregg_fips204_sign_real_present))]
    pub fn fips204_sign_real_present() -> bool {
        false
    }

    /// FIPS-203-ENCAPS EXTRACTION — run the VERIFIED Lean ML-KEM encaps core (leanc-native).
    /// Input: `"A t m"` (three decimal ints); output: `"u v K"` (ciphertext + encapsulated secret).
    #[cfg(dregg_fips203_encaps_present)]
    pub fn lean_fips203_encaps(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_fips203_encaps_str, "dregg_fips203_encaps_str")
    }

    #[cfg(not(dregg_fips203_encaps_present))]
    pub fn lean_fips203_encaps(_wire: &str) -> Result<String, String> {
        Err("dregg_fips203_encaps not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted ML-KEM encaps core.
    #[cfg(dregg_fips203_encaps_present)]
    pub fn fips203_encaps_present() -> bool {
        true
    }

    #[cfg(not(dregg_fips203_encaps_present))]
    pub fn fips203_encaps_present() -> bool {
        false
    }

    /// FIPS-203-DECAPS EXTRACTION — run the VERIFIED Lean ML-KEM decaps core (leanc-native).
    /// Input: `"A t s z u v"`; output: the recovered shared secret K (implicit reject folded in;
    /// "ERR" only on a malformed wire). The SECURITY-CRITICAL direction as a Lean-verified object.
    #[cfg(dregg_fips203_decaps_present)]
    pub fn lean_fips203_decaps(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_fips203_decaps_str, "dregg_fips203_decaps_str")
    }

    #[cfg(not(dregg_fips203_decaps_present))]
    pub fn lean_fips203_decaps(_wire: &str) -> Result<String, String> {
        Err("dregg_fips203_decaps not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted ML-KEM decaps core.
    #[cfg(dregg_fips203_decaps_present)]
    pub fn fips203_decaps_present() -> bool {
        true
    }

    #[cfg(not(dregg_fips203_decaps_present))]
    pub fn fips203_decaps_present() -> bool {
        false
    }

    /// ML-KEM-768-DECAPS-REAL extraction (BRICK K6) — run the VERIFIED Lean ML-KEM decaps core over the REAL,
    /// FULL-BYTE decapsulation key/ciphertext (leanc-native). Input: `"hex(dk) hex(ct)"` (two space-separated
    /// lowercase-hex fields over the real 2400/1088-byte dk/ct); output: `hex(K)` (the recovered 32-byte shared
    /// secret) or `"ERR"` (the fail-closed answer for a malformed wire). This is the FULL-DIMENSION FO
    /// `mlkemDecaps` (SHA3-512 `G` split / K-PKE decrypt / re-encryption / byte-exact implicit-reject check,
    /// proved to recover a genuine crate secret and diverge on a tamper) — the object
    /// `dregg-pq::HybridResponder::finish` routes through to take the `ml-kem` crate OUT of the decaps TCB.
    #[cfg(dregg_mlkem_decaps_real_present)]
    pub fn lean_mlkem_decaps_real(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_mlkem_decaps_real_str,
            "dregg_mlkem_decaps_real_str",
        )
    }

    #[cfg(not(dregg_mlkem_decaps_real_present))]
    pub fn lean_mlkem_decaps_real(_wire: &str) -> Result<String, String> {
        Err("dregg_mlkem_decaps_real not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-KEM-768 decaps core.
    #[cfg(dregg_mlkem_decaps_real_present)]
    pub fn mlkem_decaps_real_present() -> bool {
        true
    }

    #[cfg(not(dregg_mlkem_decaps_real_present))]
    pub fn mlkem_decaps_real_present() -> bool {
        false
    }

    /// ML-KEM-768-ENCAPS-REAL extraction (BRICK K5) — run the VERIFIED Lean ML-KEM encaps core over the REAL,
    /// FULL-BYTE encapsulation key + message (leanc-native). Input: `"hex(ek) hex(m)"` (two space-separated
    /// lowercase-hex fields over the real 1184-byte ek / 32-byte m); output: `"hex(ct) hex(K)"` (the 1088-byte
    /// ciphertext + 32-byte shared secret) or `"ERR"` (the fail-closed answer for a malformed wire). This is the
    /// FULL-DIMENSION deterministic FO `mlkemEncaps` (`H(ek)` / `G(m ‖ H(ek))` split / K-PKE.Encrypt, proved
    /// byte-exact vs the crate's `EncapsulateDeterministic`) — the object `dregg-pq::hybrid_kem::initiate` routes
    /// through to take the `ml-kem` crate OUT of the encaps TCB.
    #[cfg(dregg_mlkem_encaps_real_present)]
    pub fn lean_mlkem_encaps_real(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_mlkem_encaps_real_str,
            "dregg_mlkem_encaps_real_str",
        )
    }

    #[cfg(not(dregg_mlkem_encaps_real_present))]
    pub fn lean_mlkem_encaps_real(_wire: &str) -> Result<String, String> {
        Err("dregg_mlkem_encaps_real not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-KEM-768 encaps core.
    #[cfg(dregg_mlkem_encaps_real_present)]
    pub fn mlkem_encaps_real_present() -> bool {
        true
    }

    #[cfg(not(dregg_mlkem_encaps_real_present))]
    pub fn mlkem_encaps_real_present() -> bool {
        false
    }

    /// ML-KEM-768-KEYGEN-REAL extraction (BRICK K7) — run the VERIFIED Lean ML-KEM keygen core over the REAL,
    /// FULL-BYTE (d,z) seed (leanc-native). Input: `"hex(d z)"` (one lowercase-hex field over the real 64-byte
    /// seed); output: `"hex(ek) hex(dk)"` (the 1184-byte ek + 2400-byte dk) or `"ERR"` (the fail-closed answer
    /// for a malformed wire). This is the deterministic FIPS 203 ML-KEM.KeyGen_internal (KAT-anchored vs the
    /// NIST ACVP keyGen vectors) — the object `dregg-pq::ml_kem768_keygen` routes through to take the `ml-kem`
    /// crate OUT of the keygen TCB.
    #[cfg(dregg_mlkem_keygen_real_present)]
    pub fn lean_mlkem_keygen_real(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_mlkem_keygen_real_str,
            "dregg_mlkem_keygen_real_str",
        )
    }

    #[cfg(not(dregg_mlkem_keygen_real_present))]
    pub fn lean_mlkem_keygen_real(_wire: &str) -> Result<String, String> {
        Err("dregg_mlkem_keygen_real not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-KEM-768 keygen core.
    #[cfg(dregg_mlkem_keygen_real_present)]
    pub fn mlkem_keygen_real_present() -> bool {
        true
    }

    #[cfg(not(dregg_mlkem_keygen_real_present))]
    pub fn mlkem_keygen_real_present() -> bool {
        false
    }

    /// Identity-key KEYGEN mirror — run the VERIFIED Lean real ML-DSA-65 keygen core (leanc-native). Input:
    /// `"hex(xi)"` (one lowercase-hex field over the 32-byte ξ seed); output: `"hex(pk) hex(sk)"` (the
    /// 1952-byte pk + 4032-byte sk) or `"ERR"` (the fail-closed answer for a malformed wire). This is the
    /// deterministic FIPS 204 ML-DSA.KeyGen_internal (KAT-anchored vs the NIST ACVP ML-DSA-65 keyGen vectors)
    /// — the object `dregg-pq::MlDsaKey::from_ed25519_seed` routes through to take the `fips204` crate OUT of
    /// the IDENTITY-KEY keygen TCB.
    #[cfg(dregg_mldsa_keygen_real_present)]
    pub fn lean_mldsa_keygen_real(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_mldsa_keygen_real_str,
            "dregg_mldsa_keygen_real_str",
        )
    }

    #[cfg(not(dregg_mldsa_keygen_real_present))]
    pub fn lean_mldsa_keygen_real(_wire: &str) -> Result<String, String> {
        Err("dregg_mldsa_keygen_real not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-DSA-65 keygen core.
    #[cfg(dregg_mldsa_keygen_real_present)]
    pub fn mldsa_keygen_real_present() -> bool {
        true
    }

    #[cfg(not(dregg_mldsa_keygen_real_present))]
    pub fn mldsa_keygen_real_present() -> bool {
        false
    }

    /// GRAIN-R3 extraction — run the VERIFIED Lean whole-history R3-accept core (leanc-native).
    /// Input: `"aggregateVerified aggregateHead anchoredHead"` (three decimal ints); output: `"1"`
    /// (accept) / `"0"` (reject, and the fail-closed answer for a malformed wire). This is the PROVED
    /// `Dregg2.Grain.R3Verify.r3VerifyCore` (`aggregateVerified && aggregateHead == anchoredHead`) — the
    /// R3 whole-history-unfoolable accept decision, reduced to the named `EngineSound` boundary + the R1
    /// head binding — as a Lean-verified object, the object `grain-verify::r3_verify` routes its accept
    /// decision through.
    #[cfg(dregg_grain_r3_verify_present)]
    pub fn lean_grain_r3_verify(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_grain_r3_verify_str, "dregg_grain_r3_verify_str")
    }

    #[cfg(not(dregg_grain_r3_verify_present))]
    pub fn lean_grain_r3_verify(_wire: &str) -> Result<String, String> {
        Err("dregg_grain_r3_verify not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted GRAIN R3 whole-history verify core.
    #[cfg(dregg_grain_r3_verify_present)]
    pub fn grain_r3_verify_present() -> bool {
        true
    }

    #[cfg(not(dregg_grain_r3_verify_present))]
    pub fn grain_r3_verify_present() -> bool {
        false
    }

    /// HOLDING-GRANT-WEIGHT extraction — run the VERIFIED Lean fail-closed weight verdict core
    /// (leanc-native). Input: `"isConsensusProven slotFinal amount"` (three decimal ints); output: the
    /// granted weight as a decimal string (`= amount` when granted, `"0"` when refused, and the
    /// fail-closed answer for a negative amount / malformed wire). This is the PROVED
    /// `Metatheory.Bridge.ProofOfHoldings.grantWeightCore` (`if isConsensusProven && slotFinal then amount
    /// else 0`), proved to REALIZE the `grantsWeight` spec by `grantWeightCore_eq_grantsWeight` — the
    /// non-custodial proof-of-holdings → governance-weight decision as a Lean-verified object, the object
    /// `dregg-governance::holding_weight::grant_weight` routes its weight verdict through.
    #[cfg(dregg_holding_grant_weight_present)]
    pub fn lean_holding_grant_weight(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_holding_grant_weight_str,
            "dregg_holding_grant_weight_str",
        )
    }

    #[cfg(not(dregg_holding_grant_weight_present))]
    pub fn lean_holding_grant_weight(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_holding_grant_weight not exported by the linked archive (rebuild to enable)"
                .into(),
        )
    }

    /// `true` iff the linked archive carries the extracted HOLDING grant-weight verdict core.
    #[cfg(dregg_holding_grant_weight_present)]
    pub fn holding_grant_weight_present() -> bool {
        true
    }

    #[cfg(not(dregg_holding_grant_weight_present))]
    pub fn holding_grant_weight_present() -> bool {
        false
    }

    /// INTERCHAIN reached-consensus extraction — run the VERIFIED Lean bridge-trust verdict core
    /// (leanc-native). Input: `"tag payload"` (two decimal ints — the rung selector + the
    /// watchtower/committee resolution bit); output: `"1"` (reached consensus) / `"0"` (refused;
    /// also the fail-closed answer for an unknown tag or a malformed wire). This is the PROVED
    /// `Dregg2.Bridge.InterchainAdapterDecision.reachedConsensusWire` (over `reachedConsensusCore`,
    /// realizing the `reachesConsensusSpec` fail-closed spec) — the object
    /// `dregg-bridge::interchain_adapter`'s `TrustRung::reached_consensus` routes its verdict through.
    #[cfg(dregg_interchain_reached_consensus_present)]
    pub fn lean_interchain_reached_consensus(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_interchain_reached_consensus_str,
            "dregg_interchain_reached_consensus_str",
        )
    }

    #[cfg(not(dregg_interchain_reached_consensus_present))]
    pub fn lean_interchain_reached_consensus(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_interchain_reached_consensus not exported by the linked archive (rebuild to enable)"
                .into(),
        )
    }

    /// `true` iff the linked archive carries the extracted INTERCHAIN reached-consensus verdict core.
    #[cfg(dregg_interchain_reached_consensus_present)]
    pub fn interchain_reached_consensus_present() -> bool {
        true
    }

    #[cfg(not(dregg_interchain_reached_consensus_present))]
    pub fn interchain_reached_consensus_present() -> bool {
        false
    }

    /// Run the FRI soundness ledger: `"logBlowup numQueries powBits maxLogArity logFinalPolyLen
    /// extDeg logD0 bciksM"` → `"arity foldedDomain goodCount perFoldBits johnsonBits
    /// capacityBits commitBits"` (`""` fail-closed). This is the computable
    /// `Dregg2.Circuit.FriLedger.friLedger` (plus `friCommitLedger`'s ε_C column), the object
    /// `FriLedgerSound`'s parametric per-fold theorem is stated over.
    #[cfg(dregg_fri_ledger_present)]
    pub fn lean_fri_ledger(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_fri_ledger_str, "dregg_fri_ledger_str")
    }

    #[cfg(not(dregg_fri_ledger_present))]
    pub fn lean_fri_ledger(_wire: &str) -> Result<String, String> {
        Err("dregg_fri_ledger not exported by the linked archive (rebuild to enable)".into())
    }

    /// `true` iff the linked archive carries the extracted FRI soundness ledger.
    #[cfg(dregg_automatafl_rules_present)]
    pub fn lean_automatafl_rules(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_automatafl_rules_str,
            "dregg_automatafl_rules_str",
        )
    }

    #[cfg(not(dregg_automatafl_rules_present))]
    pub fn lean_automatafl_rules(_wire: &str) -> Result<String, String> {
        Err("dregg_automatafl_rules not exported by the linked archive (rebuild to enable)".into())
    }

    #[cfg(dregg_automatafl_rules_present)]
    pub fn automatafl_rules_present() -> bool {
        true
    }

    #[cfg(not(dregg_automatafl_rules_present))]
    pub fn automatafl_rules_present() -> bool {
        false
    }

    #[cfg(dregg_multiway_tug_rules_present)]
    pub fn lean_multiway_tug_rules(wire: &str) -> Result<String, String> {
        lean_string_bridge(
            wire,
            dregg_multiway_tug_rules_str,
            "dregg_multiway_tug_rules_str",
        )
    }

    #[cfg(not(dregg_multiway_tug_rules_present))]
    pub fn lean_multiway_tug_rules(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_multiway_tug_rules not exported by the linked archive (rebuild to enable)"
                .into(),
        )
    }

    #[cfg(dregg_multiway_tug_rules_present)]
    pub fn multiway_tug_rules_present() -> bool {
        true
    }

    #[cfg(not(dregg_multiway_tug_rules_present))]
    pub fn multiway_tug_rules_present() -> bool {
        false
    }

    #[cfg(dregg_fri_ledger_present)]
    pub fn fri_ledger_present() -> bool {
        true
    }

    #[cfg(not(dregg_fri_ledger_present))]
    pub fn fri_ledger_present() -> bool {
        false
    }

    /// Run the DELEGATED TOOL/MCP-ACCESS admission decision:
    /// `"toolId rateLimit deadline now tool old new"` → `"1"` (ADMIT) / `"0"` (REFUSE) / `""`
    /// (malformed wire — NO VERDICT). This is `Dregg2.Apps.DelegAdmit.delegAdmit`, the predicate
    /// `Dregg2.Apps.ToolAccessDelegation.tool_invocation_commit_iff_admit` is stated over.
    #[cfg(dregg_deleg_admit_present)]
    pub fn lean_deleg_admit(wire: &str) -> Result<String, String> {
        // Keep the real call inside the lock: a later full initializer may
        // register shared globals while Lean's initialization phase is open.
        let mut state = lifecycle()?;
        state.ensure_deleg(&mut NativeInit)?;
        lean_string_bridge(wire, dregg_deleg_admit_str, "dregg_deleg_admit_str")
    }

    #[cfg(not(dregg_deleg_admit_present))]
    pub fn lean_deleg_admit(_wire: &str) -> Result<String, String> {
        Err("dregg_deleg_admit not exported by the linked archive (rebuild to enable)".into())
    }

    #[cfg(dregg_deleg_admit_present)]
    pub fn deleg_admit_present() -> bool {
        true
    }

    #[cfg(dregg_trustline_step_present)]
    pub fn lean_trustline_step(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_trustline_step_str, "dregg_trustline_step_str")
    }

    #[cfg(not(dregg_trustline_step_present))]
    pub fn lean_trustline_step(_wire: &str) -> Result<String, String> {
        Err("dregg_trustline_step not exported by the linked archive (rebuild to enable)".into())
    }

    #[cfg(dregg_trustline_step_present)]
    pub fn trustline_step_present() -> bool {
        true
    }

    #[cfg(not(dregg_trustline_step_present))]
    pub fn trustline_step_present() -> bool {
        false
    }

    #[cfg(not(dregg_deleg_admit_present))]
    pub fn deleg_admit_present() -> bool {
        false
    }

    #[cfg(all(test, dregg_fips204_verify_present))]
    mod fips204_verify_extraction {
        use super::*;
        /// THE ROUND-TRIP: the verified Lean ML-DSA verify core runs (leanc-compiled native). An honest
        /// deployed-parameter signature ACCEPTS ("1"); a tampered `c̃`/`z` and an out-of-range `z` REJECT
        /// ("0") — the extracted `verifyCore` is the real gate, not `fun _ => true`.
        #[test]
        fn verified_ml_dsa_verify_runs_in_lean() {
            lean_init_once().expect("init the Lean runtime");
            // Honest: thi=3, μ=7, sig=(c̃=7, z=45, h=0) — the `realParams` round-trip.
            assert_eq!(lean_fips204_verify("3 7 7 45 0").expect("round-trip"), "1");
            // Tampered c̃ (breaks the challenge fixed-point) REJECTS.
            assert_eq!(lean_fips204_verify("3 7 8 45 0").unwrap(), "0");
            // Out-of-range z (fails ‖z‖ < γ₁−β) REJECTS.
            assert_eq!(lean_fips204_verify("3 7 7 100000000 0").unwrap(), "0");
            // Malformed wire fails CLOSED.
            assert_eq!(lean_fips204_verify("garbage").unwrap(), "0");
        }
    }

    #[cfg(all(test, dregg_grain_r3_verify_present))]
    mod grain_r3_verify_extraction {
        use super::*;
        /// THE R3 DECISION IN LEAN: the verified GRAIN R3 whole-history verify core runs
        /// (leanc-compiled native) — the object `grain-verify::r3_verify` routes its accept decision
        /// through. Mirrors the Lean `#guard`s in `Dregg2.Grain.R3Verify` on the POST-WOUND-#22 wire
        /// (33 ints: status ‖ presentedVk[8] ‖ expectedVk[8] ‖ aggregateHead[8] ‖ anchoredHead[8]):
        /// honest facts ACCEPT ("1"); an aggregate head differing ONLY OUTSIDE LANE 0 REJECTS ("0" —
        /// the anti-ghost tooth at full 8-felt width, where the pre-repair lane-0 core ACCEPTED); a
        /// presented VK that is not the caller's anchor REJECTS ("0" — the anti-self-anchor tooth); a
        /// NON-verifying aggregate REJECTS ("0"); and the PRE-REPAIR three-int wire plus any malformed
        /// wire fail CLOSED ("0"). The extracted `r3VerifyCore` is the real gate, not `fun _ => true`.
        #[test]
        fn verified_grain_r3_verify_runs_in_lean() {
            lean_init_once().expect("init the Lean runtime");
            // One wire: status, then four eight-lane values.
            let wire = |st: u8, p: [u32; 8], e: [u32; 8], a: [u32; 8], b: [u32; 8]| -> String {
                let mut s = st.to_string();
                for v in p.iter().chain(&e).chain(&a).chain(&b) {
                    s.push(' ');
                    s.push_str(&v.to_string());
                }
                s
            };
            let vk_a = [11u32, 22, 33, 44, 55, 66, 77, 88];
            // A DIFFERENT circuit's fingerprint (lane 0 bumped).
            let vk_b = [12u32, 22, 33, 44, 55, 66, 77, 88];
            let head = [7u32, 101, 102, 103, 104, 105, 106, 107];
            // The ~2^31 grind product: lane 0 IDENTICAL, lane 1 different.
            let forged = [7u32, 999, 102, 103, 104, 105, 106, 107];

            // Verified aggregate + the caller's own anchor + matching 8-felt heads ACCEPT.
            assert_eq!(
                lean_grain_r3_verify(&wire(1, vk_a, vk_a, head, head)).expect("round-trip"),
                "1"
            );
            // THE WIDTH TOOTH: a head differing ONLY OUTSIDE LANE 0 REJECTS. Everything the
            // pre-repair seam compared (`final_root[0]`) is equal here, so it accepted this.
            assert_eq!(
                lean_grain_r3_verify(&wire(1, vk_a, vk_a, forged, head)).unwrap(),
                "0"
            );
            // THE ANTI-SELF-ANCHOR TOOTH: a presented fingerprint that is not the caller's anchor
            // REJECTS …
            assert_eq!(
                lean_grain_r3_verify(&wire(1, vk_b, vk_a, head, head)).unwrap(),
                "0"
            );
            // … while the self-anchored shape (presented == expected, as the pre-repair seam had it)
            // accepts that very same foreign fingerprint — the vacuity the repair removed.
            assert_eq!(
                lean_grain_r3_verify(&wire(1, vk_b, vk_b, head, head)).unwrap(),
                "1"
            );
            // Non-verifying aggregate REJECTS regardless of the VKs and heads.
            assert_eq!(
                lean_grain_r3_verify(&wire(0, vk_a, vk_a, head, head)).unwrap(),
                "0"
            );
            // The PRE-REPAIR three-int wire fails CLOSED — a stale caller cannot re-open the
            // ~31-bit binding by accident.
            assert_eq!(lean_grain_r3_verify("1 42 42").unwrap(), "0");
            // Malformed wire fails CLOSED.
            assert_eq!(lean_grain_r3_verify("garbage").unwrap(), "0");
        }
    }

    #[cfg(all(test, dregg_fips204_sign_present))]
    mod fips204_sign_extraction {
        use super::*;
        /// THE SIGN → VERIFY ROUND-TRIP: the verified Lean ML-DSA SIGN core runs (leanc-compiled native)
        /// and its accepted output VERIFIES through the extracted verify core — the full `Fips204Correct`
        /// round-trip across two extracted objects. The honest secret `(5,1,3)` with mask `y=40`, message
        /// `μ=7` SIGNS to `"7 45 0"`, which verifies as `"1"` under `thi = 5+1−3 = 3`. A bad-mask sample
        /// (`lowGap` fails) and an out-of-norm response are honestly `"REJECT"` (retry, not faked); a
        /// malformed wire fails closed.
        #[test]
        fn verified_ml_dsa_sign_verify_roundtrips_in_lean() {
            lean_init_once().expect("init the Lean runtime");
            // Honest accepted iteration ⇒ the signature wire.
            let sig = lean_fips204_sign("5 1 3 7 40").expect("sign round-trip");
            assert_eq!(sig, "7 45 0", "honest sign emits the signature wire");
            // ROUND-TRIP: the accepted signature, prefixed `thi μ`, VERIFIES via the extracted verify core.
            assert_eq!(
                lean_fips204_verify(&format!("3 7 {sig}")).expect("verify"),
                "1",
                "the extracted sign output round-trips through verifyCore"
            );
            // Rejected samples are honest "REJECT" (retry): bad mask (lowGap fails) / out-of-norm z.
            assert_eq!(lean_fips204_sign("5 1 3 7 261888").unwrap(), "REJECT");
            assert_eq!(lean_fips204_sign("5 1 3 7 1000000").unwrap(), "REJECT");
            // Malformed wire fails CLOSED.
            assert_eq!(lean_fips204_sign("garbage").unwrap(), "REJECT");
        }
    }

    #[cfg(all(test, dregg_fips204_verify_real_present))]
    mod fips204_verify_real_extraction {
        use super::*;
        /// BRICK 8 smoke test: the REAL, full-byte ML-DSA verify export links and runs (leanc-native), and
        /// a malformed byte wire fails CLOSED ("0"). The real-vector accept/reject is exercised end-to-end
        /// with genuine `fips204` crate keys/signatures in `dregg-pq`'s `mldsa_lean_verify` gate (which has
        /// the crate as a dev-dep); here we only confirm the bridge is wired and fail-closed on garbage.
        #[test]
        fn verified_real_ml_dsa_verify_bridge_links_and_fails_closed() {
            lean_init_once().expect("init the Lean runtime");
            // Non-hex fields fail closed (parser rejects before verifyCore).
            assert_eq!(lean_fips204_verify_real("zz zz zz zz").unwrap(), "0");
            // Wrong field count fails closed (not exactly four space-separated fields).
            assert_eq!(lean_fips204_verify_real("00 00").unwrap(), "0");
            // Odd-length hex fails closed (decodeHexChars rejects an unpaired nibble).
            assert_eq!(lean_fips204_verify_real("0 0 0 0").unwrap(), "0");
        }
    }

    #[cfg(all(test, dregg_fips204_sign_real_present))]
    mod fips204_sign_real_extraction {
        use super::*;
        /// The brick-8 SIGN analog smoke test: the REAL, full-byte ML-DSA sign export links and runs
        /// (leanc-native), and a malformed byte wire fails CLOSED ("ERR"). The real-vector byte-exact sign is
        /// exercised end-to-end with genuine `fips204` crate keys in `dregg-pq`/`node`'s live-sign gate; here
        /// we only confirm the bridge is wired and fail-closed on garbage.
        #[test]
        fn verified_real_ml_dsa_sign_bridge_links_and_fails_closed() {
            lean_init_once().expect("init the Lean runtime");
            // Non-hex fields fail closed (parser rejects before signCore).
            assert_eq!(lean_fips204_sign_real("zz zz zz").unwrap(), "ERR");
            // Wrong field count fails closed (not exactly three space-separated fields).
            assert_eq!(lean_fips204_sign_real("00 00").unwrap(), "ERR");
            // Odd-length hex fails closed (decodeHexChars rejects an unpaired nibble).
            assert_eq!(lean_fips204_sign_real("0 0 0").unwrap(), "ERR");
        }
    }

    #[cfg(all(test, dregg_fips203_encaps_present, dregg_fips203_decaps_present))]
    mod fips203_kem_extraction {
        use super::*;
        /// THE ENCAPS → DECAPS ROUND-TRIP: the verified Lean ML-KEM cores run (leanc-compiled native).
        /// The honest deployed data `(A,t,s)=(1,2,1)`, message bit `m=1` ENCAPS to `"1 1667 3"` (ct=(1,1667),
        /// K=3); DECAPS of that ciphertext recovers `"3"` — the extracted encaps→decaps round trip that
        /// discharges `Fips203Correct`. A TAMPERED ciphertext implicit-rejects to a DIFFERENT
        /// (message-independent) secret (`"3536"` ≠ `"3"`) — the re-encryption check is the real gate,
        /// not `fun _ => K`. A malformed wire fails closed.
        #[test]
        fn verified_ml_kem_encaps_decaps_roundtrips_in_lean() {
            lean_init_once().expect("init the Lean runtime");
            // Honest encaps ⇒ the ciphertext + secret wire.
            let enc = lean_fips203_encaps("1 2 1").expect("encaps round-trip");
            assert_eq!(
                enc, "1 1667 3",
                "honest encaps emits the ciphertext + secret"
            );
            // ROUND-TRIP: decaps of the honest ciphertext recovers the encapsulated secret K=3.
            assert_eq!(
                lean_fips203_decaps("1 2 1 0 1 1667").expect("decaps"),
                "3",
                "the extracted encaps output round-trips through decapsCore"
            );
            // TAMPERED ciphertext: implicit reject to a DIFFERENT secret (the parties diverge).
            assert_eq!(
                lean_fips203_decaps("1 2 1 0 1 1767").unwrap(),
                "3536",
                "a tampered ciphertext implicit-rejects to a different secret"
            );
            assert_ne!(
                lean_fips203_decaps("1 2 1 0 1 1767").unwrap(),
                lean_fips203_decaps("1 2 1 0 1 1667").unwrap(),
                "tampering the ML-KEM ciphertext breaks key agreement"
            );
            // Malformed wires fail CLOSED.
            assert_eq!(lean_fips203_encaps("garbage").unwrap(), "ERR");
            assert_eq!(lean_fips203_decaps("garbage").unwrap(), "ERR");
        }
    }

    #[cfg(all(test, dregg_mlkem_decaps_real_present))]
    mod mlkem_decaps_real_extraction {
        use super::*;
        /// BRICK K6 smoke test: the REAL, full-byte ML-KEM-768 decaps export links and runs (leanc-native),
        /// and a malformed byte wire fails CLOSED ("ERR"). The real-vector recover/diverge is exercised
        /// end-to-end with a genuine `ml-kem` crate encaps → the deployed `hybrid_kem` decaps path in
        /// `node`'s `mlkem_live_decaps` gate; here we only confirm the bridge is wired and fail-closed.
        #[test]
        fn verified_real_ml_kem_decaps_bridge_links_and_fails_closed() {
            lean_init_once().expect("init the Lean runtime");
            // Wrong field count fails closed (not exactly two space-separated fields).
            assert_eq!(lean_mlkem_decaps_real("zz zz").unwrap(), "ERR");
            assert_eq!(lean_mlkem_decaps_real("00").unwrap(), "ERR");
            // Odd-length hex fails closed (decodeHexChars rejects an unpaired nibble).
            assert_eq!(lean_mlkem_decaps_real("0 0").unwrap(), "ERR");
        }
    }

    #[cfg(all(test, dregg_mlkem_encaps_real_present))]
    mod mlkem_encaps_real_extraction {
        use super::*;
        /// BRICK K5 smoke test: the REAL, full-byte ML-KEM-768 encaps export links and runs (leanc-native),
        /// and a malformed byte wire fails CLOSED ("ERR"). The real-vector byte-exact encaps + the full
        /// Lean-routed handshake is exercised end-to-end in `node`'s `mlkem_live_encaps` gate; here we only
        /// confirm the bridge is wired and fail-closed.
        #[test]
        fn verified_real_ml_kem_encaps_bridge_links_and_fails_closed() {
            lean_init_once().expect("init the Lean runtime");
            // Wrong field count fails closed (not exactly two space-separated fields).
            assert_eq!(lean_mlkem_encaps_real("zz zz").unwrap(), "ERR");
            assert_eq!(lean_mlkem_encaps_real("00").unwrap(), "ERR");
            // Odd-length hex fails closed (decodeHexChars rejects an unpaired nibble).
            assert_eq!(lean_mlkem_encaps_real("0 0").unwrap(), "ERR");
        }
    }

    #[cfg(all(test, dregg_storage_content_root_present))]
    mod storage_extraction {
        use super::*;
        /// THE ROUND-TRIP: the verified Lean content-root logic runs (leanc-compiled native),
        /// calling the fast Rust Poseidon2 through `@[extern "dregg_poseidon2_2to1"]` — the real
        /// "Lean is the runtime" for storage, end to end.
        #[test]
        fn verified_content_root_runs_in_lean_calling_rust_poseidon2() {
            lean_init_once().expect("init the Lean runtime");
            let r1 = lean_storage_content_root("1 2 3").expect("round-trip");
            assert!(
                !r1.is_empty() && r1 != "0",
                "a real content root felt: {r1}"
            );
            assert_eq!(
                r1,
                lean_storage_content_root("1 2 3").unwrap(),
                "deterministic"
            );
            assert_ne!(
                r1,
                lean_storage_content_root("1 2 4").unwrap(),
                "the root binds the object set"
            );
        }
    }
}

#[cfg(not(lean_lib_present))]
mod ffi {
    pub fn initialization_status() -> super::LeanInitializationStatus {
        super::LeanInitializationStatus::default()
    }

    pub fn deleg_admit_init_once() -> Result<(), String> {
        Err("libdregg_lean.a was not present at build time".into())
    }

    pub fn executor_init_once() -> Result<(), String> {
        Err("libdregg_lean.a was not present at build time".into())
    }

    pub fn pq_init_once() -> Result<(), String> {
        Err("libdregg_lean.a was not present at build time".into())
    }

    pub fn with_pq<T>(_body: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
        Err("libdregg_lean.a was not present at build time".into())
    }

    pub fn lean_init_status() -> Option<Result<(), String>> {
        None
    }

    pub fn lean_init_once() -> Result<(), String> {
        Err("libdregg_lean.a was not present at build time".into())
    }

    pub fn lean_init_st_once() -> Result<(), String> {
        Err("libdregg_lean.a was not present at build time".into())
    }

    pub fn lean_forest_auth(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn lean_record_kernel_step(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn lean_handler_turn(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn finality_gate_present() -> bool {
        false
    }

    pub fn lean_blocklace_finalize(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn decide_refines_present() -> bool {
        false
    }

    pub fn lean_decide_refines(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn constraint_admits_present() -> bool {
        false
    }

    pub fn lean_constraint_admits(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    // No-Lean stub for the verified cross-cell per-asset conservation decision (twin #1). The
    // `#[cfg(lean_lib_present)]` module implements these over the archive; the guest/marshal-only
    // build reports the export absent (⇒ `cross_cell_conserves_available()` is false and the
    // conservation gate fails closed), mirroring `constraint_admits_present`/`lean_constraint_admits`.
    pub fn cross_cell_conserves_present() -> bool {
        false
    }

    pub fn lean_cross_cell_conserves(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn fips204_verify_present() -> bool {
        false
    }

    pub fn lean_fips204_verify(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-DSA verify
    /// core. Unlinked stub: the archive is absent, so the real core is never present.
    pub fn fips204_verify_real_present() -> bool {
        false
    }

    pub fn lean_fips204_verify_real(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-KEM decaps
    /// core. Unlinked stub: the archive is absent, so the real core is never present.
    pub fn mlkem_decaps_real_present() -> bool {
        false
    }

    pub fn lean_mlkem_decaps_real(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-KEM encaps
    /// core. Unlinked stub: the archive is absent, so the real core is never present.
    pub fn mlkem_encaps_real_present() -> bool {
        false
    }

    pub fn lean_mlkem_encaps_real(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-KEM keygen
    /// core. Unlinked stub: the archive is absent, so the real core is never present.
    pub fn mlkem_keygen_real_present() -> bool {
        false
    }

    pub fn lean_mlkem_keygen_real(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-DSA keygen
    /// core. Unlinked stub: the archive is absent, so the real core is never present.
    pub fn mldsa_keygen_real_present() -> bool {
        false
    }

    pub fn lean_mldsa_keygen_real(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn fips204_sign_present() -> bool {
        false
    }

    pub fn lean_fips204_sign(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    /// `true` iff the linked archive carries the extracted REAL, full-byte ML-DSA sign
    /// core. Unlinked stub: the archive is absent, so the real core is never present.
    pub fn fips204_sign_real_present() -> bool {
        false
    }

    pub fn lean_fips204_sign_real(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn fips203_encaps_present() -> bool {
        false
    }

    pub fn lean_fips203_encaps(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn fips203_decaps_present() -> bool {
        false
    }

    pub fn lean_fips203_decaps(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn grain_r3_verify_present() -> bool {
        false
    }

    pub fn lean_grain_r3_verify(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn holding_grant_weight_present() -> bool {
        false
    }

    pub fn lean_holding_grant_weight(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn interchain_reached_consensus_present() -> bool {
        false
    }

    pub fn lean_interchain_reached_consensus(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn fri_ledger_present() -> bool {
        false
    }

    pub fn lean_fri_ledger(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn automatafl_rules_present() -> bool {
        false
    }

    pub fn lean_automatafl_rules(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn multiway_tug_rules_present() -> bool {
        false
    }

    pub fn lean_multiway_tug_rules(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn deleg_admit_present() -> bool {
        false
    }

    pub fn lean_deleg_admit(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn trustline_step_present() -> bool {
        false
    }

    pub fn lean_trustline_step(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }
}

fn lean_init_once() -> Result<(), String> {
    ffi::lean_init_once()
}

fn lean_init_st_once() -> Result<(), String> {
    ffi::lean_init_st_once()
}

fn ensure_lean_init() -> Result<(), String> {
    lean_init_once()
}

/// Initialize the Lean runtime in the **single-threaded / libuv-thread-free** mode
/// (the pg-Tier-D-embeddable path — see `docs/EMBEDDABLE-LEAN-RUNTIME.md`). Unlike
/// [`lean_available`], this init does NOT start the libuv event-loop thread, so the
/// runtime executes entirely on the caller's thread — the property a single-threaded
/// host (a postgres backend) requires. Returns `true` on a successful init.
///
/// A process must commit to ONE init flavor. The shared coordinator refuses a
/// default-mode request after this succeeds, and refuses ST calls from another
/// host thread. Shared linkage still starts libuv; its ST property is only the
/// single runtime instance, as documented in `src/lean_init_st.cpp`.
pub fn init_single_threaded() -> bool {
    lean_init_st_once().is_ok()
}

/// Run the gated complete-turn executor (`execFullForestG`) after a **single-threaded**
/// init (no libuv event-loop thread). Semantically identical to
/// [`shadow_exec_full_forest_auth`]; the only difference is the runtime init flavor.
pub fn shadow_exec_full_forest_auth_single_threaded(wire: &str) -> Result<String, String> {
    lean_init_st_once()?;
    lean_forest_auth(wire)
}

fn lean_forest_auth(wire: &str) -> Result<String, String> {
    ffi::lean_forest_auth(wire)
}

fn lean_record_kernel_step(wire: &str) -> Result<String, String> {
    ffi::lean_record_kernel_step(wire)
}

fn lean_handler_turn(wire: &str) -> Result<String, String> {
    ffi::lean_handler_turn(wire)
}

fn lean_blocklace_finalize(wire: &str) -> Result<String, String> {
    ffi::lean_blocklace_finalize(wire)
}

fn lean_decide_refines(wire: &str) -> Result<String, String> {
    ffi::lean_decide_refines(wire)
}
