//! # PRODUCER≡DESCRIPTOR COVERAGE GATE (census R3 — the structural producer-drift blind spot).
//!
//! The drift gate proves Lean-emit ≡ committed-JSON. But `producer ≡ committed-descriptor` — that the
//! Rust trace producer emits a trace whose SHAPE/host-consts match the descriptor the light client
//! verifies against — lives ONLY in whatever prove+verify roundtrip coverage exists. `be732a9dd` (the
//! v13 stale wide-descriptor catch) proved this diverges SILENTLY: 7 wide members laid their AFTER
//! carrier chain at a stale base while the honest producers read the v13 base, so `verify` failed on
//! honest turns — a class the drift gate CANNOT see.
//!
//! This file is the anti-regression tooth for that class:
//!   1. **The classification gate** (`*_registry_every_member_classified`): every DEPLOYED descriptor
//!      member of the two registries WITHOUT an existing completeness gate (V3-live, bare-wide) MUST
//!      be classified in the coverage ledger below (COVERED / PARTIAL / UNCOVERED). A NEW deployed
//!      member with no classification FAILS the build — so the producer≡descriptor question can never
//!      again silently open for a new member. (The umem-welded registry already has its own
//!      completeness gate: `wide_umem_weld_matrix_gauntlet::matrix_enumerates_all_57`.)
//!   2. **The live R3 probes** (`cell_*_v3_producer_descriptor_roundtrip`): the two DEPLOYED V3 members
//!      with ZERO prove+verify roundtrip anywhere on the live path — `cellUnseal` / `cellDestroy`. This
//!      closes the purest R3 gap by actually driving the producer trace through
//!      `prove_vm_descriptor2` + `verify_vm_descriptor2` against the committed V3 descriptor. If the
//!      producer's shape ever diverges from the committed descriptor (the v13 class), these RED.
//!
//! Run: `cargo test -p dregg-circuit --test producer_descriptor_coverage_gate`.

use dregg_cell::lifecycle::{DeathCertificate, DeathReason};
use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect, bytes32_to_8_limbs};
use dregg_circuit::effect_vm_descriptors::{V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV};
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// THE COVERAGE LEDGER
// ─────────────────────────────────────────────────────────────────────────────────────────────────

/// The producer≡descriptor coverage status of a single deployed descriptor member.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Cov {
    /// A REAL, non-`#[ignore]` prove+verify roundtrip drives the producer's trace through
    /// `prove_vm_descriptor2` + `verify_vm_descriptor2` against THIS registry's committed descriptor.
    /// The `&str` names the covering test (the roundtrip pointer).
    Covered(&'static str),
    /// The descriptor is parsed / width-/shape-checked, OR a roundtrip exists but is `#[ignore]`d
    /// behind a NAMED seam (never a silent gap). The `&str` names the seam.
    Partial(&'static str),
    /// NO prove+verify roundtrip against this registry's descriptor — the silent-divergence risk. The
    /// `&str` gives the reason / route.
    Uncovered(&'static str),
}

/// V3-live (`rotation-v3-staged-registry.tsv`, 58 members) — the CURRENTLY-DEPLOYED 1-felt registry
/// (the prover keeps using the per-map V3 registry until the gated VK epoch flips). This is the
/// highest-priority coverage surface: it is what a light client verifies against TODAY.
fn v3_coverage_ledger() -> Vec<(&'static str, Cov)> {
    use Cov::*;
    vec![
        // ── value / balance family — COVERED
        (
            "transferVmDescriptor2R24",
            Covered(
                "effect_vm_rotation_flip::rotated_transfer_proves_verifies_differential_and_refuses_ghost + vk_epoch_value",
            ),
        ),
        (
            "burnVmDescriptor2R24",
            Covered(
                "effect_vm_rotation_flip::rotated_burn_cohort_member_proves_verifies + vk_epoch_value",
            ),
        ),
        (
            "mintVmDescriptor2R24",
            Covered("effect_vm_rotation_flip (mint) + vk_epoch_value"),
        ),
        (
            "supplyMintVmDescriptor2R24",
            Covered(
                "effect_vm_rotation_flip::rotated_supply_mint_self_verifies_under_dedicated_selector",
            ),
        ),
        (
            "transferFeeVmDescriptor2R24",
            Covered("effect_vm_rotation_flip"),
        ),
        ("incrementNonceVmDescriptor2R24", Covered("vk_epoch_value")),
        (
            "settleEscrowSatVmDescriptor2R24",
            Covered("settle_escrow_weld_prove"),
        ),
        // ── notes grow-gate — COVERED
        (
            "noteSpendVmDescriptor2R24",
            Covered("effect_vm_rotation_flip::rotated_note_spend_pins_nullifier + vk_epoch_notes"),
        ),
        ("noteCreateVmDescriptor2R24", Covered("vk_epoch_notes")),
        // ── birth grow-gate — COVERED
        (
            "createCellVmDescriptor2R24",
            Covered("effect_vm_rotation_flip::rotated_create_cell_pins_accounts + vk_epoch_birth"),
        ),
        ("factoryVmDescriptor2R24", Covered("vk_epoch_birth")),
        ("spawnVmDescriptor2R24", Covered("vk_epoch_birth")),
        // ── perms / vk / lifecycle — COVERED
        ("setPermsVmDescriptor2R24", Covered("vk_epoch_perms_vk")),
        ("setVKVmDescriptor2R24", Covered("vk_epoch_perms_vk")),
        (
            "refusalVmDescriptor2R24",
            Covered("vk_epoch_refusal_lifecycle"),
        ),
        (
            "cellSealVmDescriptor2R24",
            Covered("vk_epoch_refusal_lifecycle"),
        ),
        (
            "makeSovereignVmDescriptor2R24",
            Covered("vk_epoch_misc (makeSovereign forced-on-wire)"),
        ),
        (
            "receiptArchiveVmDescriptor2R24",
            Covered("effect_vm_rotation_flip"),
        ),
        // ── passthrough / misc — COVERED
        (
            "emitEventVmDescriptor2R24",
            Covered("vk_epoch_misc::no_cell_write_audit"),
        ),
        (
            "pipelinedSendVmDescriptor2R24",
            Covered("vk_epoch_misc::no_cell_write_audit"),
        ),
        (
            "exerciseVmDescriptor2R24",
            Covered("vk_epoch_misc::no_cell_write_audit"),
        ),
        (
            "setFieldDynVmDescriptor2R24",
            Covered("vk_epoch_misc (setFieldDyn dynamic overflow write proves)"),
        ),
        // ── the turn-bound cap-open transfer — COVERED (the ONLY green cap-open prove-through)
        (
            "transferCapOpenTBVmDescriptor2R24",
            Covered("cap_open_turn_bound_verify"),
        ),
        // ── LIVE R3 PROBES — this file (cellUnseal/cellDestroy had ZERO roundtrip before)
        (
            "cellUnsealVmDescriptor2R24",
            Covered(
                "producer_descriptor_coverage_gate::cell_unseal_v3_producer_descriptor_roundtrip (THIS file — R3 probe)",
            ),
        ),
        (
            "cellDestroyVmDescriptor2R24",
            Covered(
                "producer_descriptor_coverage_gate::cell_destroy_v3_producer_descriptor_roundtrip (THIS file — R3 probe)",
            ),
        ),
        // ── setField 0..7 — PARTIAL (NAMED seam): the V1 setField producer does not yet fill the
        //    written-slot value8; the vk_epoch_value setField roundtrip is #[ignore]d behind it.
        (
            "setFieldVmDescriptor2-0R24",
            Partial("v13 setField written-slot value8 completion seam (vk_epoch_value #[ignore])"),
        ),
        (
            "setFieldVmDescriptor2-1R24",
            Partial("v13 setField value8 seam"),
        ),
        (
            "setFieldVmDescriptor2-2R24",
            Partial("v13 setField value8 seam"),
        ),
        (
            "setFieldVmDescriptor2-3R24",
            Partial("v13 setField value8 seam"),
        ),
        (
            "setFieldVmDescriptor2-4R24",
            Partial("v13 setField value8 seam"),
        ),
        (
            "setFieldVmDescriptor2-5R24",
            Partial("v13 setField value8 seam"),
        ),
        (
            "setFieldVmDescriptor2-6R24",
            Partial("v13 setField value8 seam"),
        ),
        (
            "setFieldVmDescriptor2-7R24",
            Partial("v13 setField value8 seam"),
        ),
        // ── heapWrite — PARTIAL: structural-only on V3 (heap_write_deployed_root_forced parses +
        //    checks the `.write` map_op; no prove+verify roundtrip against the committed V3 descriptor).
        //    DISTINCT splice producer → highest-priority PARTIAL (the v13 special-member class).
        (
            "heapWriteVmDescriptor2R24",
            Partial(
                "structural-only (heap_write_deployed_root_forced); DISTINCT splice producer, no V3 roundtrip",
            ),
        ),
        // ── custom — PARTIAL: proves on the WIDE path (wide_completeness_ledger); the deeper V3
        //    per-turn proofBind engine tests are gated/#[ignore]d (custom_binding_*).
        (
            "customVmDescriptor2R24",
            Partial(
                "proves on WIDE only; V3 proofBind roundtrip gated (custom_binding_* #[ignore])",
            ),
        ),
        // ── bare cap-WRITE family — UNCOVERED on the bare V3 path BY DESIGN: forbidden/UNSAT on the
        //    bare producer; the light-client route is the cap-open path.
        (
            "attenuateVmDescriptor2R24",
            Uncovered("bare cap-write forbidden; route = attenuateCapOpenEff"),
        ),
        (
            "grantCapVmDescriptor2R24",
            Uncovered("bare cap-write forbidden; route = grantCapCapOpen"),
        ),
        (
            "revokeVmDescriptor2R24",
            Uncovered("bare cap-write forbidden; route = revokeCapOpen"),
        ),
        (
            "refreshVmDescriptor2R24",
            Uncovered("bare cap-write forbidden; route = refreshDelegationCapOpen"),
        ),
        (
            "introduceVmDescriptor2R24",
            Uncovered("bare cap-write forbidden; route = introduceCapOpen"),
        ),
        (
            "revokeCapabilityVmDescriptor2R24",
            Uncovered("bare cap-write forbidden; route = revokeCapabilityCapOpen"),
        ),
        // ── cap-OPEN family — UNCOVERED: the non-TB cap-open prove-through is #[ignore]d behind a
        //    NAMED shared Rust handoff (the IR-v2 cap-node lookup multiplicity reconciliation gap).
        //    Only transferCapOpenTB is green. These are route-blocked + seam-named, not silent — but
        //    they carry NO green producer≡descriptor roundtrip on the deployed path.
        (
            "attenuateCapOpenEffVmDescriptor2R24",
            Uncovered("cap-open prove-through #[ignore]d (IR-v2 cap-node lookup handoff)"),
        ),
        (
            "exerciseCapOpenVmDescriptor2R24",
            Uncovered("cap-open prove-through #[ignore]d (IR-v2 cap-node lookup handoff)"),
        ),
        (
            "transferCapOpenEffVmDescriptor2R24",
            Uncovered("cap-open prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "delegateCapOpenVmDescriptor2R24",
            Uncovered("cap-open prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "introduceCapOpenVmDescriptor2R24",
            Uncovered("cap-open prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "grantCapCapOpenVmDescriptor2R24",
            Uncovered("cap-open prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "revokeCapOpenVmDescriptor2R24",
            Uncovered("cap-open prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "refreshDelegationCapOpenVmDescriptor2R24",
            Uncovered("cap-open prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "revokeCapabilityCapOpenVmDescriptor2R24",
            Uncovered("cap-open prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "spawnCapOpenVmDescriptor2R24",
            Uncovered("cap-open prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "delegateWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open write prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "introduceWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open write prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "delegateAttenWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open write prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "revokeDelegationWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open write prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "revokeCapabilityWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open write prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "refreshDelegationWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open write prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
        (
            "spawnWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open write prove-through #[ignore]d (shared IR-v2 handoff)"),
        ),
    ]
}

/// Bare-wide (`rotation-wide-registry-staged.tsv`, 57 members) — the STAGED 8-felt wide registry (the
/// v13-affected surface; NOT yet the deployed default). The wide-native effects have a strong existing
/// gate: `wide_completeness_ledger::provability_scoreboard_deployed_wide_path` proves+verifies exactly
/// the 26 wide-native effects and asserts the cap-write set is the NAMED unprovable-on-wide residual.
fn wide_coverage_ledger() -> Vec<(&'static str, Cov)> {
    use Cov::*;
    let scoreboard = "wide_completeness_ledger::provability_scoreboard_deployed_wide_path";
    vec![
        ("transferVmDescriptor2R24", Covered(scoreboard)),
        ("burnVmDescriptor2R24", Covered(scoreboard)),
        (
            "mintVmDescriptor2R24",
            Covered("wide_completeness_ledger (bridgeMint/mint)"),
        ),
        (
            "noteSpendVmDescriptor2R24",
            Covered("effect_vm_wide_roundtrip + wide_completeness_ledger"),
        ),
        (
            "noteCreateVmDescriptor2R24",
            Covered("effect_vm_wide_roundtrip + wide_completeness_ledger"),
        ),
        ("cellSealVmDescriptor2R24", Covered(scoreboard)),
        ("cellDestroyVmDescriptor2R24", Covered(scoreboard)),
        ("cellUnsealVmDescriptor2R24", Covered(scoreboard)),
        ("refusalVmDescriptor2R24", Covered(scoreboard)),
        ("setPermsVmDescriptor2R24", Covered(scoreboard)),
        ("setVKVmDescriptor2R24", Covered(scoreboard)),
        (
            "exerciseVmDescriptor2R24",
            Covered("wide_completeness_ledger (exerciseViaCapability)"),
        ),
        ("pipelinedSendVmDescriptor2R24", Covered(scoreboard)),
        (
            "refreshVmDescriptor2R24",
            Covered("wide_completeness_ledger (refreshDelegation)"),
        ),
        ("incrementNonceVmDescriptor2R24", Covered(scoreboard)),
        (
            "revokeVmDescriptor2R24",
            Covered("wide_completeness_ledger (revokeDelegation)"),
        ),
        ("introduceVmDescriptor2R24", Covered(scoreboard)),
        (
            "customVmDescriptor2R24",
            Covered("wide_completeness_ledger::custom_proves_on_deployed_wide_path"),
        ),
        (
            "setFieldDynVmDescriptor2R24",
            Covered("effect_vm_wide_roundtrip + wide_completeness_ledger"),
        ),
        ("makeSovereignVmDescriptor2R24", Covered(scoreboard)),
        (
            "createCellVmDescriptor2R24",
            Covered("effect_vm_wide_roundtrip + wide_completeness_ledger"),
        ),
        (
            "factoryVmDescriptor2R24",
            Covered("effect_vm_wide_roundtrip + wide_completeness_ledger"),
        ),
        (
            "spawnVmDescriptor2R24",
            Covered("effect_vm_wide_roundtrip + wide_completeness_ledger"),
        ),
        ("receiptArchiveVmDescriptor2R24", Covered(scoreboard)),
        ("emitEventVmDescriptor2R24", Covered(scoreboard)),
        ("transferFeeVmDescriptor2R24", Covered(scoreboard)),
        (
            "supplyMintVmDescriptor2R24",
            Covered("wide_new_members_cover (supplyMint proves + LC verifies)"),
        ),
        ("setFieldVmDescriptor2-0R24", Covered(scoreboard)),
        ("setFieldVmDescriptor2-1R24", Covered(scoreboard)),
        ("setFieldVmDescriptor2-2R24", Covered(scoreboard)),
        ("setFieldVmDescriptor2-3R24", Covered(scoreboard)),
        ("setFieldVmDescriptor2-4R24", Covered(scoreboard)),
        ("setFieldVmDescriptor2-5R24", Covered(scoreboard)),
        ("setFieldVmDescriptor2-6R24", Covered(scoreboard)),
        ("setFieldVmDescriptor2-7R24", Covered(scoreboard)),
        // ── heapWrite (wide) — PARTIAL: pinned structurally by wide_new_members_cover (16 wide-commit
        //    PIs); no end-to-end prove+verify (the DISTINCT wide splice producer, the v13 host-const class).
        (
            "heapWriteVmDescriptor2R24",
            Partial(
                "wide_new_members_cover structural pin; no end-to-end wide roundtrip (v13 host-const class)",
            ),
        ),
        (
            "transferCapOpenTBVmDescriptor2R24",
            Partial(
                "wide_new_members_cover structural pin (16 wide-commit PIs); no wide roundtrip",
            ),
        ),
        // ── cap-write / cap-open family (wide) — UNCOVERED on the bare wide path BY DESIGN: the
        //    scoreboard NAMES these as the cap-open route residual (grantCapability panics UNSAT).
        (
            "attenuateVmDescriptor2R24",
            Uncovered("NAMED cap-open route residual (scoreboard unprovable-on-wide)"),
        ),
        (
            "grantCapVmDescriptor2R24",
            Uncovered("NAMED cap-open route residual (scoreboard unprovable-on-wide)"),
        ),
        (
            "revokeCapabilityVmDescriptor2R24",
            Uncovered("NAMED cap-open route residual (scoreboard unprovable-on-wide)"),
        ),
        (
            "delegateCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "introduceCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "grantCapCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "revokeCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "refreshDelegationCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "revokeCapabilityCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "transferCapOpenEffVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "attenuateCapOpenEffVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "exerciseCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "spawnCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "spawnWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "delegateWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "introduceWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "delegateAttenWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "revokeDelegationWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "revokeCapabilityWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
        (
            "refreshDelegationWriteCapOpenVmDescriptor2R24",
            Uncovered("cap-open route; bare wide producer UNSAT"),
        ),
    ]
}

/// The member keys of a registry TSV (column 0).
fn registry_keys(tsv: &str) -> std::collections::BTreeSet<&str> {
    tsv.lines()
        .filter(|l| !l.is_empty())
        .map(|l| l.split('\t').next().expect("key column"))
        .collect()
}

/// The classification gate: assert EXACT completeness (every registry member classified; no stale
/// ledger entries). Prints the COVERED/PARTIAL/UNCOVERED breakdown + the uncovered set.
fn assert_classified(tsv: &str, ledger: &[(&'static str, Cov)], name: &str) {
    let keys = registry_keys(tsv);
    let ledger_keys: std::collections::BTreeSet<&str> = ledger.iter().map(|(k, _)| *k).collect();
    assert_eq!(
        ledger_keys.len(),
        ledger.len(),
        "[{name}] the coverage ledger has duplicate keys"
    );
    for k in &keys {
        assert!(
            ledger_keys.contains(k),
            "[{name}] DEPLOYED member `{k}` is NOT classified in the coverage ledger — a new deployed \
             descriptor member has NO producer≡descriptor coverage classification. Add it as \
             Covered(test) / Partial(seam) / Uncovered(reason) so the R3 blind spot cannot silently \
             open (census R3)."
        );
    }
    for k in &ledger_keys {
        assert!(
            keys.contains(k),
            "[{name}] ledger key `{k}` is not a deployed registry member (stale entry — remove it)"
        );
    }
    assert_eq!(
        keys, ledger_keys,
        "[{name}] ledger must EXACTLY cover the registry"
    );

    let (mut c, mut p, mut u) = (0, 0, 0);
    let mut uncovered = Vec::new();
    for (k, cov) in ledger {
        match cov {
            Cov::Covered(_) => c += 1,
            Cov::Partial(_) => p += 1,
            Cov::Uncovered(r) => {
                u += 1;
                uncovered.push((*k, *r));
            }
        }
    }
    eprintln!(
        "=== [{name}] producer≡descriptor coverage: {} members ===",
        ledger.len()
    );
    eprintln!("    COVERED={c}  PARTIAL={p}  UNCOVERED={u}");
    for (k, r) in &uncovered {
        eprintln!("    UNCOVERED {k}: {r}");
    }
}

#[test]
fn v3_registry_every_member_classified() {
    assert_classified(V3_STAGED_REGISTRY_TSV, &v3_coverage_ledger(), "v3-live");
}

#[test]
fn wide_registry_every_member_classified() {
    assert_classified(
        WIDE_REGISTRY_STAGED_TSV,
        &wide_coverage_ledger(),
        "bare-wide",
    );
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// THE LIVE R3 PROBES — cellUnseal / cellDestroy had ZERO prove+verify roundtrip on the deployed V3
// path (they appeared only in the STAGED wide/welded sdk gauntlets). Drive the producer trace through
// the committed V3 descriptor end-to-end.
// ─────────────────────────────────────────────────────────────────────────────────────────────────

fn v3_json(name: &str) -> &'static str {
    V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"))
}

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("37 pre-iroot limbs")
}

fn h8(b: &[u8; 32]) -> [BabyBear; 8] {
    bytes32_to_8_limbs(blake3::hash(b).as_bytes())
}

/// Drive an honest single-effect V3 turn through the producer + prove+verify against the committed
/// V3 descriptor. `before` is the pre-cell; `kernel` is applied to derive the after-cell (the deployed
/// executor projection); `vm_effect` is the circuit lead. RED iff the producer's shape diverges from
/// the committed descriptor (the v13 producer-drift class).
fn prove_verify_v3(name: &str, before: Cell, kernel: dregg_turn::Effect, vm_effect: Effect) {
    let cell_id = before.id();
    let resolved =
        rotated_descriptor_name_for_effect(&vm_effect).expect("is a rotated cohort member");
    assert_eq!(resolved, name, "the effect routes to the committed member");
    let desc = parse_vm_descriptor2(v3_json(name)).expect("committed V3 descriptor parses");

    let balance = before.state.balance() as u64;
    let st = CellState::new(balance, before.state.nonce() as u32);

    let mut after = before.clone();
    rw::apply_effect_to_cell(&mut after, &cell_id, &kernel, 100);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after.clone()).unwrap();
    let null_root = [0u8; 32];
    let commit_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w = rw::produce(
        &before,
        &Ledger::new(),
        &null_root,
        &commit_root,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after,
        &ledger,
        &null_root,
        &commit_root,
        &receipt_log,
        &Default::default(),
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &[vm_effect],
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .unwrap_or_else(|e| panic!("[{name}] the live V3 producer must emit a trace: {e:?}"));

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps).unwrap_or_else(
        |e| {
            panic!(
                "[{name}] R3 PRODUCER≡DESCRIPTOR DIVERGENCE: the honest producer trace does NOT prove \
                 against the committed V3 descriptor — {e:?}"
            )
        },
    );
    verify_vm_descriptor2(&desc, &proof, &dpis).unwrap_or_else(|e| {
        panic!(
            "[{name}] R3 PRODUCER≡DESCRIPTOR DIVERGENCE: the honest producer proof does NOT \
             light-client-verify against the committed V3 descriptor — {e:?}"
        )
    });
    eprintln!(
        "[{name}] R3 PROBE GREEN: producer trace proves + verifies against the committed V3 descriptor."
    );
}

#[test]
fn cell_unseal_v3_producer_descriptor_roundtrip() {
    // The before-cell must be SEALED so the unseal moves the lifecycle limb (Sealed → Live).
    let mut before = producer_cell(50_000, 0);
    let cell_id = before.id();
    before.seal([9u8; 32], 42).expect("seal the before-cell");
    prove_verify_v3(
        "cellUnsealVmDescriptor2R24",
        before,
        dregg_turn::Effect::CellUnseal { target: cell_id },
        Effect::CellUnseal {
            target: h8(cell_id.as_bytes()),
        },
    );
}

#[test]
fn cell_destroy_v3_producer_descriptor_roundtrip() {
    let before = producer_cell(50_000, 0);
    let cell_id = before.id();
    let certificate = DeathCertificate {
        cell_id,
        last_receipt_hash: [4u8; 32],
        final_state_commitment: [5u8; 32],
        destroyed_at_height: 100,
        reason: DeathReason::Voluntary,
    };
    let cert_hash = certificate.certificate_hash();
    prove_verify_v3(
        "cellDestroyVmDescriptor2R24",
        before,
        dregg_turn::Effect::CellDestroy {
            target: cell_id,
            certificate,
        },
        Effect::CellDestroy {
            target_hash: h8(cell_id.as_bytes()),
            death_certificate_hash: h8(&cert_hash),
        },
    );
}
