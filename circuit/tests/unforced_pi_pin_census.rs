//! **The unforced-PI-pin census, measured on the DEPLOYED bytes through the DEPLOYED decoder.**
//!
//! A `PiBinding { row, col, pi_index }` is `local[col] == pv[pi_index]` on the tagged row
//! (`descriptor_ir2.rs`, the `Ir2Air` eval). That is a BINDING only when something else in the
//! member forces `local[col]`. When no other constraint reads the column, the prover chooses BOTH
//! sides — it picks the column value, publishes it, and the pin is satisfied by construction. The
//! published slot is then host trust wearing an AIR's clothes: a full node compensates by
//! OVERWRITING the slot from its own trusted turn before verifying, and **a light client has no
//! host to do the overwriting.**
//!
//! This file authors no constraint. It parses the three deployed registry TSVs with
//! `parse_vm_descriptor2` — the same decoder the prover feeds — and measures. The AIR-side repair
//! is Lean-authored: `metatheory/Dregg2/Circuit/Emit/UnforcedPiPins.lean` defines `forcedCols` /
//! `unforcedPins` / `dropUnforcedPins`, proves the subtraction a weakening
//! (`satisfied2_dropUnforcedPins`), proves it a FIXPOINT (`unforcedPins_dropUnforcedPins`), proves
//! the dropped column DEAD afterwards (`dropUnforcedPins_col_dead`, so the already-proven E1
//! kill-set removes it), and proves the dropped pin a no-op
//! (`unforced_pin_row_admits_any_value`: overwrite the column and every slot its pins publish with
//! an ARBITRARY value and every constraint still holds — a real binding refuses an inconsistent
//! publication; this one accepts every publication).
//!
//! ## The two reference notions, and why both are here
//!
//! * **row-blind** — `col` appears in NO non-pin constraint anywhere. The Lean subtraction's
//!   condition, and the strongest statement: nothing in the member relates the column to anything.
//! * **row-aware** — `col` appears only in constraints that are INACTIVE on the row the pin fires
//!   on. The live instance is the `.transition { hi, lo }` continuity chain, which is
//!   `is_transition`-gated: it forces row `i+1`'s `state_before[hi]` from row `i`'s
//!   `state_after[lo]` for `i < n-1`. So the FIRST row's `state_before` column has no predecessor
//!   to be forced from, and the LAST row's `state_after` column has no successor. That is exactly
//!   the multiplier vacuity the last-row anchor forge was: a column can look referenced and be
//!   free precisely where the pin reads it.
//!
//! ## Expected counts — the convergence re-emit LANDED (2026-07-31)
//!
//! This file used to carry the 2026-07-30 pre-re-emit measurement and say: *"When that re-emit
//! lands `dropUnforcedPins`, the row-blind counts go to ZERO and this test goes RED — which is the
//! point: whoever lands it must state the new number here."* It landed, this went red, and the new
//! numbers are stated below. They are not transcribed off the failure: each was re-derived by an
//! independent second implementation of `collect`/`free_row_*` run over the same committed TSVs,
//! and the two agree exactly.
//!
//!   v3     839 → 682 → 830 pins, blind 165 → **0**, aware 216 → **51**
//!   wide  1639 → 1480 → 1628 pins, blind 167 → **0**, aware 215 → **48**
//!   welded  (identical to wide)
//!
//! ⚑ The THIRD number in each row is the rc FOLD (2026-07-31, same day). It restored 148 pins —
//! the `withDfaRcPins` DFA route-commitment quartet on each of the 37 rc-wrapped members — WITHOUT
//! touching `dropUnforcedPins`: `EffectVmEmitRotationV3.caveatV3SitesAt` now absorbs the carrier
//! into the published caveat commitment, so those columns are READ and the pins survive the
//! subtraction on their own merits. That is the only honest way to bring a censused pin back.
//!
//! **`blind = 0` is the theorem, not a coincidence.** `unforcedPins_dropUnforcedPins` proves the
//! subtraction is a FIXPOINT: `forcedCols` counts only NON-pin constraints, the subtraction removes
//! only pins, so the forced surface is invariant and a second pass finds nothing. Measuring 0 here
//! is the deployed-bytes witness of that theorem, and any nonzero value means a member was emitted
//! without passing through `dropUnforcedPins`.
//!
//! **`aware` fell 216 → 51 purely as a consequence:** `aware` counts pins free ON THEIR OWN ROW,
//! which is a superset of `blind`. Before: 216 = 165 blind + 51 aware-only. After: 51 = 0 + 51. The
//! aware-only residue — the legacy 1-felt state-commitment pins — is UNCHANGED at (51, 48, 48),
//! because the row-blind subtraction cannot reach it. That is stated as its own assertion below.
//!
//! ⚑ AND `forcedCols` OVER-COUNTS BY EXACTLY SIXTEEN. A `proof_bind` has no row denotation — the
//! deployed `Ir2Air::eval` `continue`s on it and emits no bus interaction, and Lean's
//! `VmConstraint2.holdsAt` is `trivial` for it — yet `forcedCols` counts its `commit`/`vk` column
//! references. So `customVmDescriptor2R24`'s surviving exposure pins (PI slots 39..54 — they were
//! 46..61 before the 2026-08-07 seven-slot PI compaction: an eight-lane
//! proof commitment and an eight-lane program VK) are as prover-chosen as the 159 that were deleted;
//! they survive on the strength of a DECLARATION. That is measured, not asserted in prose, by
//! [`proof_bind_is_the_only_reader_of_the_custom_exposure_columns`].
//!
//! ⚑⚑ **SIXTEEN, AND IT USED TO SAY TWO — because this file DID NOT COMPILE for the whole interval.**
//! The `ProofBindSpec` lane-vector widening turned `commit`/`vk` from one `LeanExpr` each into
//! vectors; the `ProofBind` arm of `collect` kept destructuring single expressions, so `cargo test
//! -p dregg-circuit --test unforced_pi_pin_census` was a BUILD FAILURE and none of these six numbers
//! were being read by anything. A gate that cannot build cannot go red. Repaired 2026-08-05 together
//! with the identical arm in `decider_experiments.rs`; the pins moved 830 → 844 and 1628 → 1642,
//! which is the fourteen real columns the widening added, counted for the first time.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, VmConstraint2, WindowExpr, parse_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::CAP_OPEN_TB_PI_SRC;
use dregg_circuit::effect_vm_descriptors::{
    V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV, welded_wide_members,
};
use dregg_circuit::lean_descriptor_air::{HashInput, LeanExpr, VmConstraint, VmRow};

/// The parsed members of a committed `key\tname\tjson` registry TSV.
fn members(tsv: &str) -> Vec<(String, EffectVmDescriptor2)> {
    tsv.lines()
        .filter(|l| !l.is_empty())
        .map(|line| {
            let key = line.split('\t').next().expect("registry key").to_string();
            let json = line.split('\t').nth(2).expect("member json");
            let d = parse_vm_descriptor2(json).expect("deployed member parses");
            (key, d)
        })
        .collect()
}

/// The welded set, DERIVED from the bare wide registry plus the Lean-emitted weld contract
/// (`welded_wide_members`) — there is no committed welded TSV.
fn welded_members() -> Vec<(String, EffectVmDescriptor2)> {
    welded_wide_members()
        .into_iter()
        .map(|(key, d)| (key.to_string(), d))
        .collect()
}

/// The EffectVM state-block bases the offset-encoded `Transition { hi, lo }` reads through
/// (`lean_descriptor_air::EFFECTVM_STATE_{BEFORE,AFTER}_BASE`, re-derived here so a layout move
/// breaks this file rather than silently mis-attributing a reference).
const STATE_BEFORE_BASE: usize = 54;
const STATE_AFTER_BASE: usize = 76;

fn expr_cols(e: &LeanExpr, out: &mut Vec<usize>) {
    match e {
        LeanExpr::Var(v) => out.push(*v),
        LeanExpr::Const(_) => {}
        LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => {
            expr_cols(a, out);
            expr_cols(b, out);
        }
    }
}

fn wexpr_cols(e: &WindowExpr, loc: &mut Vec<usize>, nxt: &mut Vec<usize>) {
    match e {
        WindowExpr::Loc(c) => loc.push(*c),
        WindowExpr::Nxt(c) => nxt.push(*c),
        WindowExpr::Const(_) => {}
        WindowExpr::Add(a, b) | WindowExpr::Mul(a, b) => {
            wexpr_cols(a, loc, nxt);
            wexpr_cols(b, loc, nxt);
        }
    }
}

/// What a constraint reads, split by which row slice it reads it from. `pi_binding` contributes
/// NOTHING — the whole question is whether anything OTHER than the pin forces the column.
#[derive(Default)]
struct Reads {
    /// current-row reads, active on every row
    loc_all: Vec<usize>,
    /// current-row reads, active only on non-last rows (`is_transition`)
    loc_trans: Vec<usize>,
    /// next-row reads, active on every row (wrap included)
    nxt_all: Vec<usize>,
    /// next-row reads, active only on non-last rows
    nxt_trans: Vec<usize>,
    /// reads guarded to the first row
    first_only: Vec<usize>,
    /// reads guarded to the last row
    last_only: Vec<usize>,
}

fn cexpr_cols(
    e: &dregg_circuit::descriptor_ir2::ChalExpr,
    loc: &mut Vec<usize>,
    nxt: &mut Vec<usize>,
) {
    use dregg_circuit::descriptor_ir2::ChalExpr as CE;
    match e {
        CE::Loc(c) => loc.push(*c),
        CE::Nxt(c) => nxt.push(*c),
        CE::Const(_) | CE::Chal(_) => {}
        CE::Add(a, b) | CE::Mul(a, b) => {
            cexpr_cols(a, loc, nxt);
            cexpr_cols(b, loc, nxt);
        }
    }
}

fn collect(d: &EffectVmDescriptor2) -> Reads {
    let mut r = Reads::default();
    for c in &d.constraints {
        match c {
            VmConstraint2::Base(VmConstraint::PiBinding { .. }) => {}
            VmConstraint2::Base(VmConstraint::Gate(body)) => expr_cols(body, &mut r.loc_trans),
            VmConstraint2::Base(VmConstraint::Transition { hi, lo }) => {
                // `next[BEFORE + hi] - local[AFTER + lo]`, gated by `is_transition`
                r.nxt_trans.push(STATE_BEFORE_BASE + hi);
                r.loc_trans.push(STATE_AFTER_BASE + lo);
            }
            VmConstraint2::Base(VmConstraint::Boundary { row, body }) => match row {
                VmRow::First => expr_cols(body, &mut r.first_only),
                VmRow::Last => expr_cols(body, &mut r.last_only),
            },
            VmConstraint2::Lookup(l) => {
                for e in &l.tuple {
                    expr_cols(e, &mut r.loc_all);
                }
            }
            VmConstraint2::MemOp(m) => {
                for e in [&m.guard, &m.addr, &m.value, &m.prev_value, &m.prev_serial] {
                    expr_cols(e, &mut r.loc_all);
                }
            }
            VmConstraint2::MapOp(m) => {
                for e in [&m.guard, &m.key, &m.value] {
                    expr_cols(e, &mut r.loc_all);
                }
                for e in m.root.iter().chain(m.new_root.iter()) {
                    expr_cols(e, &mut r.loc_all);
                }
            }
            VmConstraint2::UMemOp(m) => {
                for e in [
                    &m.guard,
                    &m.key,
                    &m.present,
                    &m.value,
                    &m.prev_present,
                    &m.prev_value,
                    &m.prev_serial,
                ] {
                    expr_cols(e, &mut r.loc_all);
                }
            }
            // ⚑ `commit`/`vk` are LANE VECTORS since the 2026-08-05 `ProofBindSpec` widening (they
            // were one `LeanExpr` each). This arm did not follow and the whole census stopped
            // COMPILING — a gate that cannot build cannot go red. Every lane of both vectors is
            // counted, so a nine-lane seam contributes nine columns and not one.
            VmConstraint2::ProofBind(p) => {
                expr_cols(&p.guard, &mut r.loc_all);
                for e in p.commit.iter().chain(p.vk.iter()) {
                    expr_cols(e, &mut r.loc_all);
                }
            }
            // ⚑ A challenge gate reads the SAME two row slices a window gate does, under the same
            // guard. Its `Chal(i)` leaves read no column, so they enter no bucket — a census that
            // invented one for them would over-count the forced set.
            VmConstraint2::ChalGate(g) => {
                if g.on_transition {
                    cexpr_cols(&g.body, &mut r.loc_trans, &mut r.nxt_trans);
                } else {
                    cexpr_cols(&g.body, &mut r.loc_all, &mut r.nxt_all);
                }
            }
            VmConstraint2::WindowGate(w) => {
                if w.on_transition {
                    wexpr_cols(&w.body, &mut r.loc_trans, &mut r.nxt_trans);
                } else {
                    wexpr_cols(&w.body, &mut r.loc_all, &mut r.nxt_all);
                }
            }
        }
    }
    for e in &d.hash_sites {
        r.loc_all.push(e.digest_col);
        for i in &e.inputs {
            if let HashInput::Col(c) = i {
                r.loc_all.push(*c);
            }
        }
    }
    for rg in &d.ranges {
        r.loc_all.push(rg.wire);
    }
    r
}

/// row-BLIND: the column appears in no non-pin reference anywhere.
fn free_row_blind(r: &Reads, col: usize) -> bool {
    ![
        &r.loc_all,
        &r.loc_trans,
        &r.nxt_all,
        &r.nxt_trans,
        &r.first_only,
        &r.last_only,
    ]
    .iter()
    .any(|v| v.contains(&col))
}

/// row-AWARE: nothing active on the pinned row reads the column.
fn free_row_aware(r: &Reads, row: VmRow, col: usize) -> bool {
    if r.loc_all.contains(&col) || r.nxt_all.contains(&col) {
        return false;
    }
    match row {
        // `is_transition` fires on row 0 (any >=2-row trace), so a transition-gated read counts;
        // a `next[..]` read of a transition-gated constraint reaches rows 1.., never row 0.
        VmRow::First => !(r.loc_trans.contains(&col) || r.first_only.contains(&col)),
        // on the last row `is_transition` is 0, so `loc_trans` reads nothing there; but the
        // PREVIOUS row's transition-gated `next[..]` does reach it.
        VmRow::Last => !(r.nxt_trans.contains(&col) || r.last_only.contains(&col)),
    }
}

struct Census {
    members: usize,
    pins: usize,
    free_blind: usize,
    free_aware: usize,
    /// (member key, row, col, pi) for the row-blind free set
    blind_detail: Vec<(String, VmRow, usize, usize)>,
    /// (member key, row, col, pi) for the pins free ONLY on the pinned row
    aware_only_detail: Vec<(String, VmRow, usize, usize)>,
}

fn census(set: &[(String, EffectVmDescriptor2)]) -> Census {
    let mut out = Census {
        members: 0,
        pins: 0,
        free_blind: 0,
        free_aware: 0,
        blind_detail: Vec::new(),
        aware_only_detail: Vec::new(),
    };
    for (key, d) in set {
        out.members += 1;
        let reads = collect(d);
        for c in &d.constraints {
            if let VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) = c {
                out.pins += 1;
                if free_row_blind(&reads, *col) {
                    out.free_blind += 1;
                    out.blind_detail.push((key.clone(), *row, *col, *pi_index));
                }
                if free_row_aware(&reads, *row, *col) {
                    out.free_aware += 1;
                    if !free_row_blind(&reads, *col) {
                        out.aware_only_detail
                            .push((key.clone(), *row, *col, *pi_index));
                    }
                }
            }
        }
    }
    out
}

/// **THE CENSUS.** Measured 2026-07-31 on the deployed bytes, after the rc FOLD. `free_blind` is
/// the set the Lean-side `dropUnforcedPins` removes, and it is ZERO — the subtraction's FIXPOINT
/// theorem made good on the emitted bytes.
///
/// ⚑ THE PIN TOTALS ROSE 682 → 830 (v3) and 1480 → 1628 (wide/welded) WITHOUT `dropUnforcedPins`
/// changing at all. `EffectVmEmitRotationV3.caveatV3SitesAt` now absorbs the 4-felt DFA
/// route-commitment carrier into the PUBLISHED caveat commitment, so those columns are READ, they
/// enter `forcedCols`, and the same unchanged subtraction keeps the `withDfaRcPins` pins on their
/// own merits. +148 on each registry = 4 pins × 37 rc-wrapped members (the v3 TSV's 60 rows and
/// the wide 57 both contain exactly 37 of them; `heapWrite`, `supplyMint` and the three staged
/// capacity-satisfaction welds are rc-EXEMPT, and the setField family shares the count).
/// `aware` did NOT move (51/48/48): it counts pins free on their own row, a superset of `blind`
/// whose residue is the legacy 1-felt state-commitment pins the row-blind subtraction cannot reach.
#[test]
fn unforced_pi_pin_census_is_pinned() {
    let v3 = census(&members(V3_STAGED_REGISTRY_TSV));
    let wide = census(&members(WIDE_REGISTRY_STAGED_TSV));
    let welded = census(&welded_members());

    // ONE comparison, so a drift shows every number at once instead of stopping at the first.
    // `blind` is the set the Lean-side `dropUnforcedPins` removes, and it is now ZERO in all three
    // registries — which is `unforcedPins_dropUnforcedPins` (the subtraction is a FIXPOINT) made
    // good on the deployed bytes. A NONZERO `blind` from here on means a member reached a registry
    // without passing through `dropUnforcedPins`, not that a new hazard was invented.
    let measured = format!(
        "v3 {}/{} blind={} aware={} | wide {}/{} blind={} aware={} | welded {}/{} blind={} aware={}",
        v3.members,
        v3.pins,
        v3.free_blind,
        v3.free_aware,
        wide.members,
        wide.pins,
        wide.free_blind,
        wide.free_aware,
        welded.members,
        welded.pins,
        welded.free_blind,
        welded.free_aware,
    );
    assert_eq!(
        measured,
        "v3 60/844 blind=0 aware=51 | wide 57/1642 blind=0 aware=48 \
         | welded 57/1642 blind=0 aware=48",
        "the unforced-PI-pin census moved"
    );

    // ⚑ THE THREE NAMED CANDIDATES, NOW ASSERTED ABSENT. These were `assert!(has(...))` — the
    // audit's three exhibits, each measured PRESENT on the emitted bytes: the TB weld's `actor`
    // (wide col 928 → PI 47) and `dst` (col 929 → PI 48), and the mint-hash pin (col 68 → PI 46).
    // All three are gone. The polarity flip is the whole content of this test now, so it is spelled
    // out per-exhibit rather than folded into `blind == 0`: a bare zero would also be produced by a
    // census that stopped looking.
    let has = |c: &Census, key: &str, col: usize, pi: usize| {
        c.blind_detail
            .iter()
            .any(|(k, _, cc, pp)| k == key && *cc == col && *pp == pi)
    };
    assert!(
        !has(&wide, "transferCapOpenTBVmDescriptor2R24", 928, 47),
        "the TB weld's `actor` pin must be GONE — it published a prover-chosen felt for WHO ACTED"
    );
    assert!(
        !has(&wide, "transferCapOpenTBVmDescriptor2R24", 929, 48),
        "the TB weld's `dst` pin must be GONE — it published a prover-chosen felt for WHO RECEIVED"
    );
    assert!(
        !has(&wide, "mintVmDescriptor2R24", 68, 46),
        "the mint-hash pin must be GONE — it published a prover-chosen mint identity"
    );

    // …and the POSITIVE half, which is what makes the deletion a subtraction of lies rather than a
    // subtraction of checks: the TB weld's `src` pin SURVIVED, because `targetBindGate` and the
    // depth-16 membership open read that column. A census that deleted everything would pass the
    // three assertions above and fail this one.
    let tb_pins: Vec<usize> = {
        let d = parse_vm_descriptor2(
            WIDE_REGISTRY_STAGED_TSV
                .lines()
                .find_map(|l| {
                    let mut it = l.splitn(3, '\t');
                    (it.next() == Some("transferCapOpenTBVmDescriptor2R24"))
                        .then(|| it.nth(1))
                        .flatten()
                })
                .expect("the TB member is deployed"),
        )
        .expect("TB member parses");
        d.constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Base(VmConstraint::PiBinding { pi_index, .. })
                    if *pi_index >= CAP_OPEN_TB_PI_SRC =>
                {
                    Some(*pi_index)
                }
                _ => None,
            })
            .collect()
    };
    assert!(
        tb_pins.contains(&CAP_OPEN_TB_PI_SRC),
        "the TB weld's `src` pin (PI {CAP_OPEN_TB_PI_SRC}, the literal 46 before the 2026-08-07 \
         seven-slot compaction) must SURVIVE the subtraction: it is FORCED \
         (targetBindGate pins leaf.target == src, and the depth-16 open chains that leaf to the \
         committed cap root). Its survival is the evidence `dropUnforcedPins` discriminates."
    );

    // ⚑ **THE ROW-AWARE-ONLY RESIDUE, CLASSIFIED — the part the row-blind subtraction does NOT
    // remove.** Every one of these is a LEGACY 1-felt state-commitment pin: `PI[OLD_COMMIT] =
    // state_before.STATE_COMMIT` on the FIRST row (col 54+12 = 66), or `PI[NEW_COMMIT] =
    // state_after.STATE_COMMIT` on the LAST row (col 76+12 = 88) in the three members whose col 88
    // is not a chip output. The `.transition {12,12}` chain links them to each other and to
    // NOTHING ELSE, and it is `is_transition`-gated, so the first row's before-commit has no
    // predecessor and the last row's after-commit has no successor: the prover picks the chain's
    // endpoints. What makes this a DUPLICATE rather than a hole is that the bound replacement is
    // published in the SAME PI vector — the wide 8-felt BEFORE/AFTER anchors, whose carrier columns
    // ARE poseidon2-chip outputs over the rotated limbs the `weldsAt` welds tie to these very state
    // columns. Deleting the legacy pins is "prefer deleting the old thing to keeping both"; it
    // needs the ROW-AWARE subtraction, whose no-op argument is a single-row trace edit rather than
    // the whole-column one `unforced_pin_row_admits_any_value` proves.
    //
    // This assertion is the DETECTION: if a row-aware-only free pin appears that is NOT one of
    // those two commitment slots, it is a new hole of an unknown kind and this goes red.
    const OLD_COMMIT_COL: usize = STATE_BEFORE_BASE + 12;
    const NEW_COMMIT_COL: usize = STATE_AFTER_BASE + 12;
    for c in [&v3, &wide, &welded] {
        for (key, row, col, pi) in &c.aware_only_detail {
            let known = matches!(
                (row, *col, *pi),
                (VmRow::First, OLD_COMMIT_COL, 0) | (VmRow::Last, NEW_COMMIT_COL, 8)
            );
            assert!(
                known,
                "{key}: an unforced-on-its-row pin that is NOT a legacy state-commitment slot — \
                 row {row:?} col {col} pi {pi}"
            );
        }
    }
    assert_eq!(
        (
            v3.aware_only_detail.len(),
            wide.aware_only_detail.len(),
            welded.aware_only_detail.len()
        ),
        (51, 48, 48),
        "the legacy 1-felt commitment pins whose 8-felt bound replacement rides beside them"
    );
}

/// **⚑ `forcedCols` OVER-COUNTS BY EXACTLY TWO, AND THIS MEASURES IT.**
///
/// The Lean subtraction keeps a pin when some NON-PIN constraint references its column
/// (`UnforcedPiPins.forcedCols`). `proof_bind` is a non-pin constraint and its `commit`/`vk`
/// expressions ARE references — but a `proof_bind` has **no row denotation at all**: the deployed
/// `Ir2Air::eval` groups it with the bus kinds and `continue`s without emitting a bus interaction,
/// and Lean's `VmConstraint2.holdsAt` is `trivial` for it. So a column whose ONLY non-pin reader is
/// a `proof_bind` is exactly as prover-chosen as the 159 columns the subtraction deleted; its pin
/// survives on the strength of a DECLARATION.
///
/// Exactly two such pins exist, both on `customVmDescriptor2R24`: the exposure base → col 72
/// (`PARAM_BASE + CUSTOM_PROOF_COMMIT_BASE`, commit limb 0) and base+8 → col 68
/// (`PARAM_BASE + CUSTOM_VK_HASH_BASE`, VK limb 0) — 46 / 54 before the 2026-08-07 seven-slot PI
/// compaction, 39 / 47 after. This is not a defect being tolerated — it is
/// the already-documented shape of the custom member (`require_no_unbacked_proof_bind`: *"The
/// declaration is NOT an in-AIR check … the ONLY thing that makes the published claim mean anything
/// is the per-turn fold connecting it to a re-proven sub-proof leaf"*). What this test adds is that
/// the statement is now MEASURED on the deployed bytes and cannot rot:
///
///   * if a third such pin appears, some member gained a proof-bind-only exposure and whoever added
///     it needs to know the AIR forces nothing about it;
///   * if these two disappear, the custom member has NO in-bytes evidence of its exposure layout
///     left and `effect_vm_descriptors::custom_commit_version` must stop keying on pins entirely.
#[test]
fn proof_bind_is_the_only_reader_of_the_custom_exposure_columns() {
    for (label, set) in [
        ("v3", members(V3_STAGED_REGISTRY_TSV)),
        ("wide", members(WIDE_REGISTRY_STAGED_TSV)),
        ("welded", welded_members()),
    ] {
        let mut declaration_only: Vec<(String, usize, usize)> = Vec::new();
        for (key, d) in &set {
            // `collect` folds a `ProofBind`'s commit/vk references into `loc_all` — exactly as
            // Lean's `forcedCols` does, which is the over-count under measurement. So take the
            // reference surface of the descriptor WITHOUT its proof-bind declarations: what is
            // free there, and pinned, is published on the strength of a declaration alone.
            let mut without_proof_bind = d.clone();
            without_proof_bind
                .constraints
                .retain(|c| !matches!(c, VmConstraint2::ProofBind(_)));
            let reads = collect(&without_proof_bind);
            for c in &d.constraints {
                if let VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) = c
                    && free_row_blind(&reads, *col)
                {
                    declaration_only.push((key.clone(), *col, *pi_index));
                }
            }
        }
        declaration_only.sort();

        // ⚑ SIXTEEN, not two — an 8-lane commitment and an 8-lane program VK, since the
        // `ProofBindSpec` lane-vector widening made `commit`/`vk` vectors where each was one
        // `LeanExpr`. The two-entry pin recorded here was the pre-widening picture, and after the
        // widening this whole file stopped COMPILING (the `ProofBind` arm of `collect` still
        // destructured single expressions), so the list was UNREADABLE rather than red. The claim
        // below is unchanged and is the point: every one of these publishes on a DECLARATION alone.
        //
        // ⚑ The assertion is on `(member, PI SLOT)`, not on the column index. The same member sits
        // at a different column base in each registry — 68..76 / 707..715 / 1813..1821 — so a
        // column-indexed literal can only be true for one of the three, which is how this
        // assertion would have read green for `v3` and red for `wide` on identical content. The PI
        // slots ARE registry-independent, and they are what a light client sees.
        let by_slot: Vec<(String, usize)> = declaration_only
            .iter()
            .map(|(k, _col, pi)| (k.clone(), *pi))
            .collect();
        // ⚑ The base is DERIVED, not a literal. It was `46..=61` until 2026-08-07, and the
        // seven-slot PI compaction moved it — the Lean side had those four bases written as
        // literals while the member's `piCount` was symbolic, so for one build the descriptor
        // declared 59 PIs and pinned three past the end. Deriving here means this test measures
        // the exposure block wherever the rotated tail puts it, and disagrees loudly if the two
        // sides ever drift again.
        let exposure_lo = dregg_circuit::effect_vm::trace_rotated::ROT_PI_COUNT;
        let mut want: Vec<(String, usize)> = (exposure_lo..exposure_lo + 16)
            .map(|pi| ("customVmDescriptor2R24".to_string(), pi))
            .collect();
        want.sort();
        let mut got = by_slot.clone();
        got.sort();
        assert_eq!(
            got, want,
            "{label}: the pins whose only non-pin reader is a `proof_bind` — a constraint with no \
             row denotation in either the Lean model or the deployed `Ir2Air`. These publish; they \
             do not bind. The custom member's proof commitment and program VK are bound by the \
             per-turn FOLD over PI slots and by nothing in the AIR."
        );

        // And they are SIXTEEN DISTINCT COLUMNS, so the count above is not sixteen names for two.
        let mut cols: Vec<usize> = declaration_only.iter().map(|(_, c, _)| *c).collect();
        cols.sort_unstable();
        cols.dedup();
        assert_eq!(
            cols.len(),
            16,
            "{label}: the eight commitment lanes and eight program-VK lanes must be distinct columns"
        );
    }
}

/// **How many published slots are pinned AT ALL** — the other half of the light-client answer.
/// A slot no constraint pins is not "trusted", it is IGNORED by the AIR: the verifier supplies it
/// and no equation reads it. The danger is a consumer that believes it attested.
#[test]
fn published_slot_accounting_is_pinned() {
    let mut total_slots = 0usize;
    let mut pinned_slots = 0usize;
    for line in WIDE_REGISTRY_STAGED_TSV.lines().filter(|l| !l.is_empty()) {
        let json = line.split('\t').nth(2).expect("member json");
        let d = parse_vm_descriptor2(json).expect("deployed member parses");
        total_slots += d.public_input_count;
        let mut seen = vec![false; d.public_input_count];
        for c in &d.constraints {
            if let VmConstraint2::Base(VmConstraint::PiBinding { pi_index, .. }) = c {
                if *pi_index < seen.len() {
                    seen[*pi_index] = true;
                }
            }
        }
        pinned_slots += seen.iter().filter(|b| **b).count();
    }
    // 3815 -> 3821. DERIVED, per-member, from the two shape changes in that flag day:
    //   +8  the eight `setFieldVmDescriptor2-{0..7}` members each gained ONE PI (73 -> 74) for the
    //       ninth VALUE8 lane's completion pin;
    //   -2  `transferCapOpenTBVmDescriptor2R24` lost the `actor`/`dst` slots (65 -> 63).
    // No other member's `public_input_count` moved (checked member-by-member against the registry
    // at `e662ade32^`). 3815 + 8 - 2 = 3821.
    //
    // ⚑ 3821 -> 3429, THE SEVEN-SLOT PI COMPACTION (2026-08-07, `docs/PI-DISPOSITION.md` §6). v1
    // offsets 26..32 — `CURRENT_BLOCK_HEIGHT`, `MAX_CUSTOM_EFFECTS`, `CUSTOM_EFFECT_COUNT`,
    // `APPROVED_HANDOFFS[4]` — were deleted, and 56 of the 57 wide members carry the v1 window:
    // 3821 - 7*56 = 3429, to the felt. `pi_disposition_census.py` reports the same number off the
    // same bytes, and `docs/PI-DISPOSITION.md` §6 PRICED it before the emit ran.
    //
    // ⚠ The 57th member is `heapWriteVmDescriptor2R24` (20 PIs — no v1 window at all), which is
    // why this is `7*56` and not `7*57`, and why the arithmetic is worth writing out rather than
    // transcribing the number the test printed when it went red. Read out of the emitted TSV, not
    // recalled.
    assert_eq!(total_slots, 3429, "wide registry published PI slots");
    // ⚑ UNMOVED by the rc FOLD: `piCount` is invariant under `dropUnforcedPins` in both directions,
    // so restoring 148 pins published no new slot — it bound slots that were already there.
    // 1639 -> 1480 -> 1628. The first move was EXACTLY the 159 pins `dropUnforcedPins` removed; the
    // second is the 148 the rc FOLD brought back by making their columns forced (the subtraction
    // itself is unchanged). The equality of
    // "pins removed" with "distinct pinned slots lost" is not an accident: the pin relation is a
    // partial injection over every deployed member, which `pin_relation_is_injective_so_the_no_op_theorem_applies`
    // (below) measures. So no surviving pin ever backfilled a slot a deleted one vacated.
    // ⚑⚑ **1628 -> 1642, 2026-08-05, and this file could not report it.** The `ProofBindSpec`
    // widening made `commit`/`vk` LANE VECTORS where each was one `LeanExpr`; the `ProofBind` arm of
    // `collect` above still destructured them as single expressions, so this whole census stopped
    // COMPILING and every number in it went unread until the arm was repaired. `customVmDescriptor2`
    // carries an 8-lane commitment and an 8-lane program VK, so the deployed object has SIXTEEN
    // proof-bind-referenced columns where the pre-widening one had two: +14, in `pins` and in
    // `pinned_slots` alike. Nothing was widened, relaxed or admitted here — the object grew fourteen
    // real columns and the census is finally counting them.
    //
    // ⚑ UNMOVED by the 2026-08-07 seven-slot PI compaction, and that is the finding: the seven
    // slots it deleted carried ZERO pins on every member, so removing them changed `total_slots`
    // by 392 and this number by nothing at all. A compaction that moved this would have removed a
    // binding, not dead surface.
    assert_eq!(pinned_slots, 1642, "…of which some constraint pins");
}

/// **The `hsole` side condition of `unforced_pin_row_admits_any_value`, MEASURED.**
///
/// The Lean no-op theorem needs "no OTHER column shares a PI slot with this one" — otherwise
/// overwriting the slot could break a second pin that lands on a different column. That hypothesis
/// is not decorative and it is not assumed: across all three deployed registries the pin relation
/// is a partial INJECTION — no PI slot is pinned by two different columns, and no column is pinned
/// to two different slots. So the theorem applies to every censused pin, and if a future member
/// ever double-pins a slot this goes red before the subtraction is trusted on it.
#[test]
fn pin_relation_is_injective_so_the_no_op_theorem_applies() {
    for (label, set) in [
        ("v3", members(V3_STAGED_REGISTRY_TSV)),
        ("wide", members(WIDE_REGISTRY_STAGED_TSV)),
        ("welded", welded_members()),
    ] {
        for (key, d) in &set {
            let mut pairs: Vec<(usize, usize)> = Vec::new();
            for c in &d.constraints {
                if let VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) = c {
                    pairs.push((*pi_index, *col));
                }
            }
            for (i, (pi_a, col_a)) in pairs.iter().enumerate() {
                for (pi_b, col_b) in &pairs[i + 1..] {
                    assert!(
                        !(pi_a == pi_b && col_a != col_b),
                        "{label}/{key}: PI {pi_a} is pinned by two columns ({col_a}, {col_b})"
                    );
                    assert!(
                        !(col_a == col_b && pi_a != pi_b),
                        "{label}/{key}: column {col_a} is pinned to two PI slots ({pi_a}, {pi_b})"
                    );
                }
            }
        }
    }
}

/// **The v1 window has no slack — the seven-slot compaction, kept true.**
///
/// This test used to be `approved_handoffs_sentinel_is_pinned_by_no_member`: a standing
/// measurement that no member pinned `pi::APPROVED_HANDOFFS_BASE..+4`, ending "deleting the
/// slots is a PI-layout flag day … this test is the standing statement that nothing in-circuit
/// is lost by doing it." **The flag day landed on 2026-08-07** — `APPROVED_HANDOFFS`,
/// `CURRENT_BLOCK_HEIGHT`, `MAX_CUSTOM_EFFECTS` and `CUSTOM_EFFECT_COUNT` (the old v1 offsets
/// 26..32) are gone, so there is no window left to measure.
///
/// What replaces it is the property that makes a re-addition visible: **the published v1 window
/// is exactly as wide as its highest pin.** `V1_PI_COUNT == pi::ACTOR_NONCE + 1`, and no member
/// of any deployed registry pins a v1 index above `ACTOR_NONCE`. If a future lane appends a v1
/// slot that nothing binds, `V1_PI_COUNT` grows past the highest pin and this goes RED — which
/// is the check the seven dead slots evaded for a year by being added below the nonce, not above
/// it. (A pin at or above `V1_PI_COUNT` is a ROTATED-tail pin and is out of scope here; the
/// rotated tail is audited by the pins census above.)
///
/// ⚠ Read the "no member pins it" half the way `docs/PI-DISPOSITION.md` §6 teaches: it says no
/// constraint IN THESE REGISTRIES reads the index, never "nothing reads the slot".
/// `TURN_HASH` and `EFFECTS_HASH_GLOBAL` are unpinned here and FORCED in
/// `dregg-bilateral-aggregation-v3`, which consumes the window.
#[test]
fn v1_pi_window_has_no_slack_above_its_highest_pin() {
    use dregg_circuit::effect_vm::pi::ACTOR_NONCE;
    use dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT;

    assert_eq!(
        V1_PI_COUNT,
        ACTOR_NONCE + 1,
        "the published v1 window is wider than its highest named pin — a dead slot was added"
    );

    for (label, set) in [
        ("v3", members(V3_STAGED_REGISTRY_TSV)),
        ("wide", members(WIDE_REGISTRY_STAGED_TSV)),
        ("welded", welded_members()),
    ] {
        for (key, d) in &set {
            for c in &d.constraints {
                if let VmConstraint2::Base(VmConstraint::PiBinding { pi_index, .. }) = c {
                    assert!(
                        *pi_index >= V1_PI_COUNT || *pi_index <= ACTOR_NONCE,
                        "{label}/{key}: PI {pi_index} is inside the v1 window but above \
                         ACTOR_NONCE ({ACTOR_NONCE}) — the window layout and the pins disagree"
                    );
                }
            }
        }
    }
}

/// **The `RETIRED_SELECTORS` claim, corrected into a measurement.**
///
/// `circuit/src/effect_vm/columns.rs` used to state that "the AIR pins every retired selector to
/// ZERO on every row, so no valid trace can carry a doomed effect (the refusal is in-circuit)".
/// That was FALSE: measured here, across every emitted member of the two registries, the retired
/// selector columns (24 until index 6 was repurposed for `sel::GRAIN_TURN`, 23 since) are
/// referenced by **zero** constraints — no pin-to-zero, no gate, no
/// lookup. What makes them harmless is not a refusal but INERTNESS: nothing reads them, so their
/// value cannot reach any published slot. This test is that fact, and it goes red the day one of
/// them becomes load-bearing.
/// **The repurposed index 6 (`sel::GRAIN_TURN`) is read by the grain member ONLY.** Repurposing a
/// retired selector is safe exactly when no OTHER member reads its column (the `MINT = 14`
/// precedent): a member that read column 6 would change meaning the day grain rows carry 1 there.
/// Measured: every member except `grainTurnVmDescriptor2R24` is blind to column 6 and pins nothing
/// at it, and the grain member does read it (else the selector would be decorative).
#[test]
fn grain_turn_selector_column_is_read_only_by_the_grain_member() {
    use dregg_circuit::effect_vm::columns::sel::GRAIN_TURN;
    use dregg_circuit::effect_vm::trace_rotated::GRAIN_TURN_DESCRIPTOR_NAME;
    for (label, tsv) in [
        ("v3", V3_STAGED_REGISTRY_TSV),
        ("wide", WIDE_REGISTRY_STAGED_TSV),
    ] {
        let mut grain_seen = false;
        for line in tsv.lines().filter(|l| !l.is_empty()) {
            let key = line.split('\t').next().expect("key");
            let json = line.split('\t').nth(2).expect("member json");
            let d = parse_vm_descriptor2(json).expect("deployed member parses");
            let r = collect(&d);
            let blind = free_row_blind(&r, GRAIN_TURN);
            if key == GRAIN_TURN_DESCRIPTOR_NAME {
                grain_seen = true;
                assert!(
                    !blind,
                    "{label}/{key}: the grain member must read its own selector"
                );
            } else {
                assert!(
                    blind,
                    "{label}/{key}: reads column {GRAIN_TURN} (the grain selector)"
                );
            }
        }
        assert!(grain_seen, "{label}: the grain member is in the registry");
    }
}

#[test]
fn retired_selector_columns_are_referenced_by_nothing() {
    use dregg_circuit::effect_vm::columns::sel::RETIRED_SELECTORS;
    for (label, tsv) in [
        ("v3", V3_STAGED_REGISTRY_TSV),
        ("wide", WIDE_REGISTRY_STAGED_TSV),
    ] {
        for line in tsv.lines().filter(|l| !l.is_empty()) {
            let key = line.split('\t').next().expect("key");
            let json = line.split('\t').nth(2).expect("member json");
            let d = parse_vm_descriptor2(json).expect("deployed member parses");
            let r = collect(&d);
            let pinned: Vec<usize> = d
                .constraints
                .iter()
                .filter_map(|c| match c {
                    VmConstraint2::Base(VmConstraint::PiBinding { col, .. }) => Some(*col),
                    _ => None,
                })
                .collect();
            for s in RETIRED_SELECTORS {
                assert!(
                    free_row_blind(&r, s) && !pinned.contains(&s),
                    "{label}/{key}: retired selector column {s} is referenced — the layout note \
                     claims these are inert, and a reference makes that claim false"
                );
            }
        }
    }
}
