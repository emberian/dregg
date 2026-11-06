//! # parse-as-derivation — the Dyck pushdown stack, TAMPER CANARIES ON THE DEPLOYED PATH.
//!
//! Mirrors `circuit-prove/tests/derivation_emit_audit_extra.rs`: HONEST witnesses
//! ACCEPT and every single-tooth TAMPER REJECTS, so the acceptance is non-vacuous.
//!
//! The circuit is the Lean-emitted, byte-pinned `DyckStackEmit.dyckParseDesc`
//! (`metatheory/Dregg2/Circuit/Emit/DyckStackEmit.lean`), served by `descriptor_by_name`
//! as `dregg-dyck-parse-v1` — the `D = 5` bounded pushdown stack routing the Dyck
//! grammar `S → [ S ] | ε` (`metatheory/Dregg2/Crypto/CfgCompact.lean` `Reference`),
//! per `docs/DESIGN-parse-as-derivation.md`. The Rust witness builders live in
//! `dregg_circuit::dsl::dyck_stack` (`build_witness` + `lift_witness_to_v2`).
//!
//! **THE v1→v2 PORT (this file's second life).** The original file drove a hand-authored
//! Rust IR-v1 mirror (`dyck_parse_descriptor` + `dyck_satisfied`) for its per-tooth
//! ISOLATION, and the emitted descriptor only for whole-path accept/reject. That mirror
//! was the last test-side Rust IR-v1 — a re-authored twin of the deployed object, exactly
//! the "real gate pointed at a re-authored mirror" smell. It is now RETIRED: every
//! isolation finder below pattern-matches the **`VmConstraint2` shapes of the LOADED
//! emitted descriptor itself** (`Base(Gate)` bodies by column-set + per-column degree,
//! `WindowGate` bodies by loc/nxt column-set, `Boundary` bodies by column-set), so each
//! tamper credits its reject to a named tooth of the DEPLOYED object, not a mirror.
//!
//! Two honest words:
//!
//!   * `"[]"` — the word `CfgCompact.Reference.brackets_replays` accepts via the
//!     compact certificate `[rBracket, rEmpty]`.
//!   * `"[[]]"` — the **nested** word whose second `rBracket` fires at stack `[S, cl]`;
//!     the outer `cl` must survive beneath the pushed `op S cl` (the slice-2 remainder
//!     shift) or there is nothing left to close with.
//!
//! Each canary follows the same discipline: FIND the single named constraint in the
//! emitted descriptor (the finder panics if the tooth was never emitted), evaluate it on
//! the honest rows (zero), evaluate it on the tampered rows (NONZERO — the isolation:
//! the reject cannot be credited to a neighbouring tooth), then drive the whole tampered
//! witness through the deployed `prove_vm_descriptor2`/`verify_vm_descriptor2` and watch
//! it REFUSE. Refusals are classified via `refusal::classify` so a stray panic reads as
//! RED, never as "rejected".

use std::collections::BTreeSet;

use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, WindowExpr, eval_lean_expr,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::dsl::dyck_stack::{
    DYCK_V2_WIDTH, RULE_EMPTY, STACK_D, SYM_CL, SYM_EMPTY, SYM_S, build_brackets_witness,
    build_nested_witness, col, lift_witness_to_v2, pi,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::refusal::{Outcome, classify};

const NAME: &str = "dregg-dyck-parse-v1";

/// The `"[]"` trace rows: `0 = rule rBracket`, `1 = term '['`, `2 = rule rEmpty`,
/// `3 = term ']'`, `4.. = done`.
const ROW_RULE_BRACKET: usize = 0;
const ROW_TERM_OPEN: usize = 1;
const ROW_TERM_CLOSE: usize = 3;

/// The `"[[]]"` trace rows: `0 = rule rBracket`, `1 = term '['`,
/// **`2 = rule rBracket` (the nested push, stack `[S, cl]`)**, `3 = term '['`,
/// `4 = rule rEmpty`, `5 = term ']'`, `6 = term ']'`, `7 = done`.
const NROW_NESTED_PUSH: usize = 2;
const NROW_AFTER_NESTED_PUSH: usize = 3;

// ============================================================================
// The deployed descriptor + accept/reject drivers
// ============================================================================

/// The dispatched, Lean-emitted Dyck descriptor.
fn emitted_desc() -> EffectVmDescriptor2 {
    let desc = descriptor_by_name(NAME)
        .expect("the deployed by-name dispatch must serve the Lean-emitted Dyck descriptor");
    assert_eq!(
        desc.trace_width, DYCK_V2_WIDTH,
        "the emitted 24-wide shape (E7 narrowed \
             both chip lookups, deleting the 2 x 7 lane columns)"
    );
    desc
}

/// Prove + verify through the emitted descriptor; `true` only on a REAL refusal (the
/// pre-flight replay's `Err`, the p3 debug prover's documented unsat panic, or a verifier
/// reject). Any OTHER panic is a RED test failure, not a "reject".
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("rejects", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

// ============================================================================
// Expression probes — column sets, per-column degree, concrete evaluation
// ============================================================================

/// Signed integer constant reduced into BabyBear (the emitted `Const` carrier is `i64`).
fn felt(c: i64) -> BabyBear {
    if c >= 0 {
        BabyBear::new(c as u32)
    } else {
        -BabyBear::new((-c) as u32)
    }
}

/// The set of columns a per-row `Gate` body reads.
fn gate_cols(e: &LeanExpr) -> BTreeSet<usize> {
    fn walk(e: &LeanExpr, acc: &mut BTreeSet<usize>) {
        match e {
            LeanExpr::Var(i) => {
                acc.insert(*i);
            }
            LeanExpr::Const(_) => {}
            LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => {
                walk(a, acc);
                walk(b, acc);
            }
        }
    }
    let mut s = BTreeSet::new();
    walk(e, &mut s);
    s
}

/// The polynomial degree of `e` in the single column `v` (`Const`/other-`Var` = 0,
/// `Var(v)` = 1, `Add` = max, `Mul` = sum) — how the finders tell the cubic is-empty
/// indicator from the linear occupancy gate over the same column pair.
fn deg_in(e: &LeanExpr, v: usize) -> usize {
    match e {
        LeanExpr::Var(i) => usize::from(*i == v),
        LeanExpr::Const(_) => 0,
        LeanExpr::Add(a, b) => deg_in(a, v).max(deg_in(b, v)),
        LeanExpr::Mul(a, b) => deg_in(a, v) + deg_in(b, v),
    }
}

/// The (loc, nxt) column sets a two-row `WindowGate` body reads.
fn window_cols(e: &WindowExpr) -> (BTreeSet<usize>, BTreeSet<usize>) {
    fn walk(e: &WindowExpr, loc: &mut BTreeSet<usize>, nxt: &mut BTreeSet<usize>) {
        match e {
            WindowExpr::Loc(i) => {
                loc.insert(*i);
            }
            WindowExpr::Nxt(i) => {
                nxt.insert(*i);
            }
            WindowExpr::Const(_) => {}
            WindowExpr::Add(a, b) | WindowExpr::Mul(a, b) => {
                walk(a, loc, nxt);
                walk(b, loc, nxt);
            }
        }
    }
    let (mut l, mut n) = (BTreeSet::new(), BTreeSet::new());
    walk(e, &mut l, &mut n);
    (l, n)
}

/// Concrete evaluation of a `WindowGate` body over a (local, next) row pair — the
/// two-row twin of the deployed `eval_lean_expr`.
fn eval_window(e: &WindowExpr, loc: &[BabyBear], nxt: &[BabyBear]) -> BabyBear {
    match e {
        WindowExpr::Loc(i) => loc[*i],
        WindowExpr::Nxt(i) => nxt[*i],
        WindowExpr::Const(c) => felt(*c),
        WindowExpr::Add(a, b) => eval_window(a, loc, nxt) + eval_window(b, loc, nxt),
        WindowExpr::Mul(a, b) => eval_window(a, loc, nxt) * eval_window(b, loc, nxt),
    }
}

// ============================================================================
// Constraint-isolating finders — so a canary names the tooth that bit.
// Each finds the UNIQUE matching constraint of the emitted descriptor (panics on
// zero matches — the tooth was never emitted — and on >1 — the shape is ambiguous
// and the isolation claim would be unearned).
// ============================================================================

/// The unique per-row `Base(Gate)` whose body satisfies `pred`.
fn find_unique_gate<'a>(
    desc: &'a EffectVmDescriptor2,
    what: &str,
    pred: impl Fn(&LeanExpr) -> bool,
) -> &'a LeanExpr {
    let hits: Vec<&LeanExpr> = desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Base(VmConstraint::Gate(body)) if pred(body) => Some(body),
            _ => None,
        })
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "the emitted descriptor must contain exactly one {what} gate (found {})",
        hits.len()
    );
    hits[0]
}

/// The unique per-row gate reading exactly the columns `cols`.
fn find_gate_on<'a>(desc: &'a EffectVmDescriptor2, what: &str, cols: &[usize]) -> &'a LeanExpr {
    let want: BTreeSet<usize> = cols.iter().copied().collect();
    find_unique_gate(desc, what, |b| gate_cols(b) == want)
}

/// The unique two-row `WindowGate` reading exactly `loc_cols` from the local row and
/// `nxt_cols` from the next row.
fn find_window_on<'a>(
    desc: &'a EffectVmDescriptor2,
    what: &str,
    loc_cols: &[usize],
    nxt_cols: &[usize],
) -> &'a WindowExpr {
    let want_l: BTreeSet<usize> = loc_cols.iter().copied().collect();
    let want_n: BTreeSet<usize> = nxt_cols.iter().copied().collect();
    let hits: Vec<&WindowExpr> = desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::WindowGate(w) => {
                let (l, n) = window_cols(&w.body);
                (l == want_l && n == want_n).then_some(&w.body)
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "the emitted descriptor must contain exactly one {what} window gate (found {})",
        hits.len()
    );
    hits[0]
}

/// The `SEL_BRACKET`-gated push/shift leg `next[next_col] <- local[local_col]` — emitted
/// as the window gate `loc[SEL_BRACKET] · (nxt[next_col] − loc[local_col])`. Panics if the
/// shift was never wired (the slice-1 hole).
fn find_bracket_shift<'a>(
    desc: &'a EffectVmDescriptor2,
    next_col: usize,
    local_col: usize,
) -> &'a WindowExpr {
    find_window_on(
        desc,
        "SEL_BRACKET push/shift",
        &[col::SEL_BRACKET, local_col],
        &[next_col],
    )
}

/// The `SEL_BRACKET` overflow guard pinning `local.STACK[stack_col]` to EMPTY — the
/// per-row gate over exactly `{STACK[stack_col], SEL_BRACKET}` — the constraint that
/// refuses a push whose remainder leaves the buffer.
fn find_bracket_overflow_guard(desc: &EffectVmDescriptor2, stack_col: usize) -> &LeanExpr {
    find_gate_on(
        desc,
        "SEL_BRACKET overflow guard",
        &[stack_col, col::SEL_BRACKET],
    )
}

/// The depth-range vanishing poly on `depth_col` — the degree-`(D+1)` product
/// `∏_{v=0}^{D} (depth − v)`, recognised as the only gate reading `depth_col` alone at
/// grid degree. Panics if it was never wired (which would mean the depth is pinned only
/// by congruences — the pre-range hole).
fn find_depth_range(desc: &EffectVmDescriptor2, depth_col: usize) -> &LeanExpr {
    find_unique_gate(desc, "depth-range", |b| {
        gate_cols(b) == BTreeSet::from([depth_col]) && deg_in(b, depth_col) == STACK_D + 1
    })
}

/// The **non-empty-below-pointer occupancy gate** for `cell` — the gate over exactly
/// `{STACK[cell], STACK_DEPTH}` in which the cell appears CUBED (the is-empty indicator
/// `(x−1)(x−2)(x−3)`). This is the tooth that refuses an `EMPTY` hole strictly below the
/// pointer; the linear empty-above gate over the same column pair is excluded by the
/// degree. Panics if the depth↔occupancy tooth was never wired.
fn find_occupancy_nonempty_below(desc: &EffectVmDescriptor2, cell: usize) -> &LeanExpr {
    find_unique_gate(desc, "non-empty-below occupancy", |b| {
        gate_cols(b) == BTreeSet::from([cell, col::STACK_DEPTH]) && deg_in(b, cell) == 3
    })
}

/// The **empty-above-pointer occupancy gate** for `cell` — the same column pair with the
/// cell appearing LINEARLY (`STACK[cell] · ∏_{v=cell+1}^{D} (depth − v)`), the tooth that
/// refuses a live symbol at or above the pointer.
fn find_occupancy_empty_above(desc: &EffectVmDescriptor2, cell: usize) -> &LeanExpr {
    find_unique_gate(desc, "empty-above occupancy", |b| {
        gate_cols(b) == BTreeSet::from([cell, col::STACK_DEPTH]) && deg_in(b, cell) == 1
    })
}

/// The **terminal-top gate** — `IS_TERM · (STACK0 − op)(STACK0 − cl)`, the only gate over
/// exactly `{STACK0, IS_TERM}` with `STACK0` squared. Panics if the tooth was never
/// wired — the state before the tape↔word correspondence was decodable.
fn find_terminal_top(desc: &EffectVmDescriptor2) -> &LeanExpr {
    find_unique_gate(desc, "IS_TERM terminal-top", |b| {
        gate_cols(b) == BTreeSet::from([col::STACK0, col::IS_TERM]) && deg_in(b, col::STACK0) == 2
    })
}

/// The **term top-match** — `IS_TERM · (STACK0 − INPUT_TOKEN)`, the only gate over
/// exactly `{STACK0, IS_TERM, INPUT_TOKEN}`.
fn find_term_top_match(desc: &EffectVmDescriptor2) -> &LeanExpr {
    find_gate_on(
        desc,
        "IS_TERM top-match",
        &[col::STACK0, col::IS_TERM, col::INPUT_TOKEN],
    )
}

/// The **rule sub-selector pin** — `SEL_BRACKET · (RULE_ID − rBracket)`, the only gate
/// over exactly `{RULE_ID, SEL_BRACKET}`.
fn find_bracket_rule_pin(desc: &EffectVmDescriptor2) -> &LeanExpr {
    find_gate_on(
        desc,
        "SEL_BRACKET rule-id pin",
        &[col::RULE_ID, col::SEL_BRACKET],
    )
}

/// The **term depth delta** — `IS_TERM · (DEPTH_NEXT − STACK_DEPTH + 1)`, the only gate
/// over exactly `{STACK_DEPTH, DEPTH_NEXT, IS_TERM}`. Used to PROVE a wrapped depth is
/// invisible to the congruence tooth before crediting the range tooth.
fn find_term_depth_delta(desc: &EffectVmDescriptor2) -> &LeanExpr {
    find_gate_on(
        desc,
        "IS_TERM depth delta",
        &[col::STACK_DEPTH, col::DEPTH_NEXT, col::IS_TERM],
    )
}

/// The **first-row initial-depth boundary** — the `Boundary{First}` whose body reads
/// exactly `{STACK_DEPTH}` (the `STACK_DEPTH == 1` pin).
fn find_first_row_depth_pin(desc: &EffectVmDescriptor2) -> &LeanExpr {
    let hits: Vec<&LeanExpr> = desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Base(VmConstraint::Boundary {
                row: VmRow::First,
                body,
            }) if gate_cols(body) == BTreeSet::from([col::STACK_DEPTH]) => Some(body),
            _ => None,
        })
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "the emitted descriptor must contain exactly one first-row STACK_DEPTH boundary"
    );
    hits[0]
}

// ============================================================================
// Honest acceptance — the deployed prove/verify accepts both words
// ============================================================================

/// **The headline**: the honest `"[]"` parse PROVES and VERIFIES through the LOADED
/// emitted descriptor — and a forged `route_commitment` public input is REJECTED by the
/// verifier on the SAME proof, so the accept is non-vacuous and the PI binding is real.
#[test]
fn emitted_dyck_brackets_proves_and_verifies() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let v2 = lift_witness_to_v2(&trace);

    let proof = prove_vm_descriptor2(&desc, &v2, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest '[]' parse must prove through the emitted descriptor");
    verify_vm_descriptor2(&desc, &proof, &pis).expect("the honest proof must verify");
    use dregg_circuit::dsl::dyck_stack::{SYM_OP, record_public_inputs, verify_record};
    let record = [SYM_OP, SYM_CL];
    let (height, computed_pis) = record_public_inputs(&record).expect("bracket alphabet");
    assert_eq!(height, v2.len());
    assert_eq!(computed_pis, pis);
    verify_record(&proof, &record).expect("record-facing verifier accepts the honest word");
    assert!(
        verify_record(&proof, &[SYM_CL, SYM_OP]).is_err(),
        "same-length record splice refuses"
    );
    use dregg_circuit::dsl::dyck_stack::{Action, RULE_BRACKET, build_witness};
    let actions = [
        Action::Rule(RULE_BRACKET),
        Action::Term(SYM_OP),
        Action::Rule(RULE_EMPTY),
        Action::Term(SYM_CL),
        Action::Done,
        Action::Done,
        Action::Done,
        Action::Done,
        Action::Done,
    ];
    let (padded_trace, padded_pis) = build_witness(&record, &actions);
    let padded = lift_witness_to_v2(&padded_trace);
    assert_eq!(padded.len(), 16);
    let padded_proof = prove_vm_descriptor2(
        &desc,
        &padded,
        &padded_pis,
        &MemBoundaryWitness::default(),
        &[],
    )
    .expect("raw descriptor permits extra done padding");
    verify_vm_descriptor2(&desc, &padded_proof, &padded_pis)
        .expect("weak raw verifier really accepts alternate padding");
    let err =
        verify_record(&padded_proof, &record).expect_err("record verifier pins canonical padding");
    assert!(err.contains("main-trace height"));

    let mut forged = pis.clone();
    forged[pi::ROUTE_COMMITMENT] += BabyBear::ONE;
    assert!(
        verify_vm_descriptor2(&desc, &proof, &forged).is_err(),
        "a forged route_commitment must be REJECTED by the verifier (last-row PiBinding)"
    );
}

/// The honest **nested** `"[[]]"` parse — the slice-2 remainder-shift word — proves and
/// verifies through the emitted descriptor too, and it really is the nested case: the
/// push at row 2 happens with `cl` under the popped `S`, and that `cl` reappears at
/// `STACK3` of row 3.
#[test]
fn emitted_dyck_nested_proves_and_verifies() {
    let desc = emitted_desc();
    let (trace, pis) = build_nested_witness();
    assert_eq!(
        trace[NROW_NESTED_PUSH][col::STACK1],
        BabyBear::new(SYM_CL),
        "row 2 must fire rBracket with a non-empty remainder"
    );
    assert_eq!(
        trace[NROW_AFTER_NESTED_PUSH][col::STACK3],
        BabyBear::new(SYM_CL),
        "the remainder must be shifted under the pushed RHS"
    );
    let v2 = lift_witness_to_v2(&trace);
    let proof = prove_vm_descriptor2(&desc, &v2, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest '[[]]' parse must prove through the emitted descriptor");
    verify_vm_descriptor2(&desc, &proof, &pis).expect("the honest nested proof must verify");
    use dregg_circuit::dsl::dyck_stack::{SYM_OP, record_public_inputs, verify_record};
    let record = [SYM_OP, SYM_OP, SYM_CL, SYM_CL];
    let (height, computed_pis) = record_public_inputs(&record).expect("bracket alphabet");
    assert_eq!(height, v2.len());
    assert_eq!(
        height, 16,
        "the first done has a successor under canonical padding"
    );
    assert_eq!(computed_pis, pis);
    verify_record(&proof, &record).expect("record-facing verifier accepts nested word");
}

/// The **nested** run's `route_commitment` binds too: the `"[[]]"` parse commits to its
/// own 8-step fold, not `"[]"`'s.
#[test]
fn nested_and_flat_commitments_differ() {
    let (_, flat_pi) = build_brackets_witness();
    let (_, nested_pi) = build_nested_witness();
    assert_ne!(
        flat_pi[pi::ROUTE_COMMITMENT],
        nested_pi[pi::ROUTE_COMMITMENT],
        "different parses must fold to different route_commitments"
    );
}

/// A **forged table-commitment seed** — claiming this parse under a DIFFERENT grammar's
/// rule table — is REJECTED: the first-row `ACC` PiBinding pins the seed the running hash
/// folded from, so a route cannot be re-homed onto another table.
#[test]
fn emitted_dyck_forged_table_commitment_rejects() {
    let desc = emitted_desc();
    let (trace, mut pis) = build_brackets_witness();
    let v2 = lift_witness_to_v2(&trace);
    pis[pi::TABLE_COMMITMENT] += BabyBear::ONE;
    assert!(
        rejects(&desc, &v2, &pis),
        "a forged table_commitment must REJECT through the emitted descriptor"
    );
}

// ============================================================================
// The terminal-top canary: a term row consumes a TERMINAL, never the nonterminal S
// ============================================================================

/// Canary — **a term row claims to consume the nonterminal `S`**. The `term` top-match
/// (`STACK0 == INPUT_TOKEN`) only ties the stack top to the tape symbol; nothing else
/// forbids the consumed top being `S` rather than a terminal. That was the hole that
/// blocked DECODING the parsed word from the trace: a `term` row consuming `S` decodes
/// to no `Brk`.
///
/// The reject is ISOLATED to the tooth: the single emitted `IS_TERM·(STACK0−op)(STACK0−cl)`
/// gate goes from zero (honest, `STACK0 = op`) to nonzero (tampered, `STACK0 = S`).
#[test]
fn tamper_term_consumes_nonterminal_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let v2 = lift_witness_to_v2(&trace);

    let gate = find_terminal_top(&desc);
    assert_eq!(
        eval_lean_expr(gate, &v2[ROW_TERM_OPEN]),
        BabyBear::ZERO,
        "an honest term row consumes a terminal (op)"
    );

    let mut tampered = v2.clone();
    tampered[ROW_TERM_OPEN][col::STACK0] = BabyBear::new(SYM_S);
    assert_ne!(
        eval_lean_expr(gate, &tampered[ROW_TERM_OPEN]),
        BabyBear::ZERO,
        "THE TOOTH: a term row consuming the nonterminal S is off the terminal grid"
    );
    assert!(
        rejects(&desc, &tampered, &pis),
        "a term row consuming the nonterminal S must REJECT"
    );
}

// ============================================================================
// The depth↔occupancy canaries: STACK_DEPTH must count the non-EMPTY prefix
// ============================================================================

/// Canary — **a hole below the pointer**. `STACK_DEPTH` pins a value but the occupancy
/// tooth is what ties it to WHICH cells are nonzero; without it a trace could claim
/// depth 4 while a cell strictly below the pointer sat `EMPTY`. The nested run's row 3
/// is `[op, S, cl, cl]` at depth 4; blank cell 1 (`S`) to `EMPTY` while leaving depth 4.
///
/// The reject is ISOLATED to the tooth: the single emitted non-empty-below gate for
/// cell 1 — `(STACK1−1)(STACK1−2)(STACK1−3) · (STACK_DEPTH)(STACK_DEPTH−1)` — goes from
/// zero (honest) to nonzero (hole), so it cannot be credited to the neighbouring shift
/// equations.
#[test]
fn tamper_occupancy_hole_below_pointer_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_nested_witness();
    let v2 = lift_witness_to_v2(&trace);

    let gate = find_occupancy_nonempty_below(&desc, col::STACK1);
    assert_eq!(
        eval_lean_expr(gate, &v2[NROW_AFTER_NESTED_PUSH]),
        BabyBear::ZERO,
        "cell 1 is a live symbol below the pointer on the honest run"
    );

    let mut tampered = v2.clone();
    tampered[NROW_AFTER_NESTED_PUSH][col::STACK1] = BabyBear::new(SYM_EMPTY);
    assert_ne!(
        eval_lean_expr(gate, &tampered[NROW_AFTER_NESTED_PUSH]),
        BabyBear::ZERO,
        "THE TOOTH: an EMPTY hole strictly below the pointer is off-occupancy"
    );
    assert!(
        rejects(&desc, &tampered, &pis),
        "a hole below the pointer must REJECT"
    );
}

/// Canary — **the pointer overclaims occupancy**. Take the `"[]"` run's row 3 (`[cl]`,
/// depth 1) and push the pointer to depth 2 while cell 1 stays `EMPTY`: `STACK_DEPTH`
/// now counts two live cells but only one is nonzero. The non-empty-below gate for
/// cell 1 refuses the phantom cell.
#[test]
fn tamper_occupancy_overclaimed_depth_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let v2 = lift_witness_to_v2(&trace);

    let gate = find_occupancy_nonempty_below(&desc, col::STACK1);
    let mut tampered = v2.clone();
    // Row 3 is `term ']'` at depth 1 (cell 0 = cl live, cells 1.. EMPTY). Claim depth 2.
    tampered[ROW_TERM_CLOSE][col::STACK_DEPTH] = BabyBear::new(2);
    tampered[ROW_TERM_CLOSE][col::DEPTH_NEXT] = BabyBear::new(1);

    assert_ne!(
        eval_lean_expr(gate, &tampered[ROW_TERM_CLOSE]),
        BabyBear::ZERO,
        "THE TOOTH: cell 1 EMPTY while the pointer claims it is occupied is off-occupancy"
    );
    assert!(
        rejects(&desc, &tampered, &pis),
        "an over-claimed STACK_DEPTH must REJECT"
    );
}

/// Canary — **a live symbol AT/ABOVE the pointer**. The `"[]"` run's row 3 is `[cl]` at
/// depth 1, so cells 1..D must be `EMPTY`. Park a `cl` in cell 1 (`i = 1 ≥ depth = 1`):
/// the emitted empty-above gate for cell 1 — `STACK1 · ∏_{v=2}^{D}(STACK_DEPTH − v)` —
/// refuses it.
#[test]
fn tamper_occupancy_symbol_above_pointer_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let v2 = lift_witness_to_v2(&trace);

    let gate = find_occupancy_empty_above(&desc, col::STACK1);
    assert_eq!(
        eval_lean_expr(gate, &v2[ROW_TERM_CLOSE]),
        BabyBear::ZERO,
        "cell 1 is EMPTY above the pointer on the honest run"
    );

    let mut tampered = v2.clone();
    tampered[ROW_TERM_CLOSE][col::STACK1] = BabyBear::new(SYM_CL);
    assert_ne!(
        eval_lean_expr(gate, &tampered[ROW_TERM_CLOSE]),
        BabyBear::ZERO,
        "THE TOOTH: a live symbol above the pointer is off-occupancy"
    );
    assert!(
        rejects(&desc, &tampered, &pis),
        "a symbol above the pointer must REJECT"
    );
}

// ============================================================================
// The depth-range canaries: a WRAPPED depth is REFUSED
// ============================================================================

/// Canary — **wrap the stack depth**. On the honest `"[]"` run, row 3 is `term ']'` at
/// depth `1 → 0`. Rewrite it as depth `p − 1` (`= −1`) with `DEPTH_NEXT = p − 2` (`= −2`):
/// a stack that popped below empty and wrapped the field.
///
/// The reject is ISOLATED to the range tooth, and the test first PROVES the wrap is
/// invisible to the constraint that was supposed to be pinning the depth: the emitted
/// `term` delta `IS_TERM·(DEPTH_NEXT − STACK_DEPTH + 1)` still evaluates to zero, because
/// `(−2) − (−1) + 1 = 0` holds over the field just as it does over ℤ. Only the vanishing
/// poly sees that `p − 1` is not one of `{0, …, D}`.
#[test]
fn tamper_wrapped_depth_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let v2 = lift_witness_to_v2(&trace);

    let mut tampered = v2.clone();
    tampered[ROW_TERM_CLOSE][col::STACK_DEPTH] = -BabyBear::ONE; // p - 1
    tampered[ROW_TERM_CLOSE][col::DEPTH_NEXT] = -BabyBear::new(2); // p - 2

    // The wrapped cells really are the huge field elements, not small negatives.
    assert_eq!(
        tampered[ROW_TERM_CLOSE][col::STACK_DEPTH],
        BabyBear::new(BABYBEAR_P - 1),
        "the tampered depth is p - 1"
    );

    // FIRST: the depth DELTA — the tooth that was supposed to pin depth — does NOT bite.
    let delta = find_term_depth_delta(&desc);
    assert_eq!(
        eval_lean_expr(delta, &tampered[ROW_TERM_CLOSE]),
        BabyBear::ZERO,
        "the wrap is INVISIBLE to the depth delta — this is the hole the range closes"
    );

    // SECOND: the RANGE tooth, isolated — honest zero, tampered nonzero.
    let range = find_depth_range(&desc, col::STACK_DEPTH);
    assert_eq!(
        eval_lean_expr(range, &v2[ROW_TERM_CLOSE]),
        BabyBear::ZERO,
        "the honest depth is ON the grid"
    );
    assert_ne!(
        eval_lean_expr(range, &tampered[ROW_TERM_CLOSE]),
        BabyBear::ZERO,
        "THE TOOTH: the wrapped depth is OFF the grid"
    );

    // And the whole deployed path refuses the trace.
    assert!(
        rejects(&desc, &tampered, &pis),
        "a wrapped STACK_DEPTH must REJECT"
    );
}

/// Canary — **an over-deep depth**. `STACK_DEPTH = D + 1` is one push past the buffer: a
/// legal-looking small integer that is nonetheless not an occupancy the `D`-cell stack
/// can have. The range tooth refuses it.
#[test]
fn tamper_overflowing_depth_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let v2 = lift_witness_to_v2(&trace);
    let range = find_depth_range(&desc, col::STACK_DEPTH);

    let mut tampered = v2.clone();
    tampered[ROW_TERM_OPEN][col::STACK_DEPTH] = BabyBear::new(STACK_D as u32 + 1);

    assert_ne!(
        eval_lean_expr(range, &tampered[ROW_TERM_OPEN]),
        BabyBear::ZERO,
        "a depth of D + 1 is off the grid"
    );
    assert!(
        rejects(&desc, &tampered, &pis),
        "an over-deep STACK_DEPTH must REJECT"
    );
}

/// The `DEPTH_NEXT` witness column carries its OWN range tooth — it is not left to be
/// read back through the depth threading (which would leave the last row's `DEPTH_NEXT`
/// free).
#[test]
fn depth_next_carries_its_own_range() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let v2 = lift_witness_to_v2(&trace);
    let range = find_depth_range(&desc, col::DEPTH_NEXT);

    let mut tampered = v2.clone();
    tampered[ROW_RULE_BRACKET][col::DEPTH_NEXT] = -BabyBear::ONE;
    assert_ne!(
        eval_lean_expr(range, &tampered[ROW_RULE_BRACKET]),
        BabyBear::ZERO,
        "a wrapped DEPTH_NEXT is off the grid"
    );
    assert!(
        rejects(&desc, &tampered, &pis),
        "a wrapped DEPTH_NEXT must REJECT"
    );
}

// ============================================================================
// The slice-2 canaries: the remainder shift is REAL
// ============================================================================

/// Canary — **drop the shifted remainder**. On the honest `"[[]]"` run, zero the cell
/// the remainder shift wrote (`row 3`'s `STACK3`, the outer `cl`). This is exactly what
/// slice 1's push did: write `(op, S, cl)` and let whatever was under the popped `S`
/// evaporate.
///
/// The reject is ISOLATED to the shift: the test evaluates the single emitted window
/// gate `SEL_BRACKET · (next.STACK3 − local.STACK1)` at the push row, and it goes from
/// zero (honest) to nonzero (tampered). So this canary cannot be credited to a
/// neighbouring tooth — the remainder shift itself is what bites.
#[test]
fn tamper_dropped_remainder_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_nested_witness();
    let mut v2 = lift_witness_to_v2(&trace);

    let shift = find_bracket_shift(&desc, col::STACK3, col::STACK1);
    assert_eq!(
        eval_window(shift, &v2[NROW_NESTED_PUSH], &v2[NROW_AFTER_NESTED_PUSH]),
        BabyBear::ZERO,
        "the remainder shift must hold on the honest nested run"
    );

    // The slice-1 push: the remainder under the popped S evaporates.
    v2[NROW_AFTER_NESTED_PUSH][col::STACK3] = BabyBear::new(SYM_EMPTY);
    assert_ne!(
        eval_window(shift, &v2[NROW_NESTED_PUSH], &v2[NROW_AFTER_NESTED_PUSH]),
        BabyBear::ZERO,
        "the remainder shift ALONE must reject a dropped remainder"
    );
    assert!(rejects(&desc, &v2, &pis), "a dropped remainder must REJECT");
}

/// Canary — **forge the shifted remainder**: keep a symbol there, but the wrong one
/// (`S` where the run carries `cl`). A shift that merely required "something nonzero"
/// would pass; the window gate pins the exact source cell.
#[test]
fn tamper_forged_remainder_symbol_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_nested_witness();
    let mut v2 = lift_witness_to_v2(&trace);

    let shift = find_bracket_shift(&desc, col::STACK3, col::STACK1);
    v2[NROW_AFTER_NESTED_PUSH][col::STACK3] = BabyBear::new(SYM_S);
    assert_ne!(
        eval_window(shift, &v2[NROW_NESTED_PUSH], &v2[NROW_AFTER_NESTED_PUSH]),
        BabyBear::ZERO,
        "the remainder shift pins the SOURCE cell, not merely occupancy"
    );
    assert!(
        rejects(&desc, &v2, &pis),
        "a forged remainder symbol must REJECT"
    );
}

/// Canary — **the overflow guard**. Park a live symbol in the deepest cell a `rBracket`
/// push cannot carry (`STACK3` of the push row, whose shifted destination `STACK5` is
/// outside the `D = 5` buffer). Without the guard the push would silently DROP it — the
/// slice-1 unsoundness wearing a wider hat. The guard turns it into a refusal.
///
/// Isolated the same way: the single emitted `SEL_BRACKET · STACK3` gate goes from zero
/// to nonzero.
#[test]
fn tamper_overflowing_push_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_nested_witness();
    let mut v2 = lift_witness_to_v2(&trace);

    let guard = find_bracket_overflow_guard(&desc, col::STACK3);
    assert_eq!(
        eval_lean_expr(guard, &v2[NROW_NESTED_PUSH]),
        BabyBear::ZERO,
        "the honest nested push does not overflow"
    );

    // a symbol whose shifted home would be STACK5 — off the end of the buffer.
    v2[NROW_NESTED_PUSH][col::STACK3] = BabyBear::new(SYM_CL);
    assert_ne!(
        eval_lean_expr(guard, &v2[NROW_NESTED_PUSH]),
        BabyBear::ZERO,
        "the overflow guard ALONE must reject a push whose remainder leaves the buffer"
    );
    assert!(rejects(&desc, &v2, &pis), "an overflowing push must REJECT");
}

/// Canary — **mutate the nested run's remainder SOURCE**: the `cl` sitting under the
/// popped `S` at the push row. The remainder shift carries whatever is there, so the
/// forged source must fail to reconcile with the row it came from (the preceding
/// `term`'s shift-down) and with the row it feeds. No SINGLE tooth owns this reject —
/// it is the seam between two neighbouring shift windows — so this canary is whole-path
/// only, as it was against the v1 mirror.
#[test]
fn tamper_nested_remainder_source_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_nested_witness();
    let mut v2 = lift_witness_to_v2(&trace);

    v2[NROW_NESTED_PUSH][col::STACK1] = BabyBear::new(SYM_EMPTY);
    assert!(
        rejects(&desc, &v2, &pis),
        "a mutated remainder source must REJECT"
    );
}

// ============================================================================
// The slice-1 canaries (retained — the teeth they cover did not move)
// ============================================================================

/// Canary — mutate a **stack cell**: flip the `term '['` row's stack top from `op` to
/// `cl`. The emitted `term` top-match (`IS_TERM·(STACK0 − INPUT_TOKEN)`) breaks —
/// isolated here — and so does the `rBracket` push leg feeding the row.
#[test]
fn tamper_stack_cell_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let mut v2 = lift_witness_to_v2(&trace);

    let top_match = find_term_top_match(&desc);
    assert_eq!(
        eval_lean_expr(top_match, &v2[ROW_TERM_OPEN]),
        BabyBear::ZERO,
        "the honest term row's top matches the tape"
    );

    v2[ROW_TERM_OPEN][col::STACK0] = BabyBear::new(SYM_CL);
    assert_ne!(
        eval_lean_expr(top_match, &v2[ROW_TERM_OPEN]),
        BabyBear::ZERO,
        "THE TOOTH: the mutated top no longer matches the consumed token"
    );
    assert!(
        rejects(&desc, &v2, &pis),
        "a mutated stack cell must REJECT"
    );
}

/// Canary — mutate the **`RULE_ID`**: claim the first row fires `rEmpty` while its
/// `SEL_BRACKET` selector is still 1. The emitted rule sub-selector pin
/// `SEL_BRACKET·(RULE_ID − rBracket)` breaks — isolated here.
#[test]
fn tamper_rule_id_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let mut v2 = lift_witness_to_v2(&trace);

    let pin = find_bracket_rule_pin(&desc);
    assert_eq!(
        eval_lean_expr(pin, &v2[ROW_RULE_BRACKET]),
        BabyBear::ZERO,
        "the honest rBracket row's RULE_ID matches its selector"
    );

    v2[ROW_RULE_BRACKET][col::RULE_ID] = BabyBear::new(RULE_EMPTY);
    assert_ne!(
        eval_lean_expr(pin, &v2[ROW_RULE_BRACKET]),
        BabyBear::ZERO,
        "THE TOOTH: a forged RULE_ID under a live SEL_BRACKET is refused by the pin"
    );
    assert!(
        rejects(&desc, &v2, &pis),
        "a forged RULE_ID (selector/rule mismatch) must REJECT"
    );
}

/// Canary — mutate the **input token**: the `term '['` row reads `']'` off the tape
/// instead of `'['`. The same emitted top-match gate breaks, from the tape side.
#[test]
fn tamper_input_token_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let mut v2 = lift_witness_to_v2(&trace);

    let top_match = find_term_top_match(&desc);
    v2[ROW_TERM_OPEN][col::INPUT_TOKEN] = BabyBear::new(SYM_CL);
    assert_ne!(
        eval_lean_expr(top_match, &v2[ROW_TERM_OPEN]),
        BabyBear::ZERO,
        "THE TOOTH: the forged token no longer matches the consumed top"
    );
    assert!(
        rejects(&desc, &v2, &pis),
        "a forged input token must REJECT"
    );
}

/// Canary — mutate the **first-row stack depth**: start at depth 2 instead of 1. The
/// emitted first-row `Boundary` pin (`STACK_DEPTH == 1`) breaks — isolated here.
#[test]
fn tamper_initial_depth_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let mut v2 = lift_witness_to_v2(&trace);

    let bpin = find_first_row_depth_pin(&desc);
    assert_eq!(
        eval_lean_expr(bpin, &v2[0]),
        BabyBear::ZERO,
        "the honest run starts at depth 1"
    );

    v2[0][col::STACK_DEPTH] = BabyBear::new(2);
    assert_ne!(
        eval_lean_expr(bpin, &v2[0]),
        BabyBear::ZERO,
        "THE TOOTH: the [initial] boundary pin refuses a depth-2 start"
    );
    assert!(
        rejects(&desc, &v2, &pis),
        "a forged initial stack depth must REJECT"
    );
}

/// Rehash a mutated preimage so the new refusal cannot be credited to a stale
/// route, accumulator, or chip output. This changes no shared descriptor on disk.
fn rehash_route(trace: &mut [Vec<BabyBear>], pis: &mut [BabyBear]) {
    use dregg_circuit::dsl::dyck_stack::V2_ACC;
    use dregg_circuit::poseidon2::{hash_2_to_1, hash_4_to_1};
    let mut acc = pis[pi::TABLE_COMMITMENT];
    for row in trace {
        row[V2_ACC] = acc;
        row[col::ENTRY_HASH] = hash_4_to_1(&[
            row[col::RULE_ID],
            row[col::STACK0],
            row[col::INPUT_TOKEN],
            row[col::LANE_ZERO],
        ]);
        acc = hash_2_to_1(acc, row[col::ENTRY_HASH]);
        row[col::RUNNING_HASH] = acc;
    }
    pis[pi::ROUTE_COMMITMENT] = acc;
}

#[test]
fn tamper_route_preimage_canonicalization() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let honest = lift_witness_to_v2(&trace);
    let last = honest.len() - 1;
    for (row_index, column, selector) in [
        (ROW_TERM_OPEN, col::RULE_ID, Some(col::IS_RULE)),
        (ROW_RULE_BRACKET, col::INPUT_TOKEN, Some(col::IS_TERM)),
        (last, col::RULE_ID, None),
        (last, col::INPUT_TOKEN, None),
        (last, col::LANE_ZERO, None),
    ] {
        let hits: Vec<usize> = desc
            .constraints
            .iter()
            .enumerate()
            .filter_map(|(i, c)| {
                let matches = match (selector, c) {
                    (Some(sel), VmConstraint2::Base(VmConstraint::Gate(body))) => {
                        gate_cols(body) == BTreeSet::from([sel, column])
                            && deg_in(body, column) == 1
                    }
                    (
                        None,
                        VmConstraint2::Base(VmConstraint::Boundary {
                            row: VmRow::Last,
                            body,
                        }),
                    ) => gate_cols(body) == BTreeSet::from([column]),
                    _ => false,
                };
                matches.then_some(i)
            })
            .collect();
        assert_eq!(
            hits.len(),
            1,
            "one canonicalization constraint for row {row_index}, col {column}"
        );
        let body = match &desc.constraints[hits[0]] {
            VmConstraint2::Base(VmConstraint::Gate(body))
            | VmConstraint2::Base(VmConstraint::Boundary { body, .. }) => body,
            _ => unreachable!(),
        };
        assert_eq!(eval_lean_expr(body, &honest[row_index]), BabyBear::ZERO);
        let mut forged = honest.clone();
        let mut forged_pis = pis.clone();
        forged[row_index][column] = BabyBear::ONE;
        rehash_route(&mut forged, &mut forged_pis);
        assert_ne!(eval_lean_expr(body, &forged[row_index]), BabyBear::ZERO);
        assert!(
            rejects(&desc, &forged, &forged_pis),
            "canonical field must be enforced"
        );
        let mut weak = desc.clone();
        weak.constraints.remove(hits[0]);
        let proof = prove_vm_descriptor2(
            &weak,
            &forged,
            &forged_pis,
            &MemBoundaryWitness::default(),
            &[],
        )
        .expect("omitting only this tooth admits the rehashed forgery");
        verify_vm_descriptor2(&weak, &proof, &forged_pis)
            .expect("weak comparator must really verify");
    }
    // The top pin is explicit even though stack threading also forces it on
    // this multirow witness. Name and evaluate that exact final boundary.
    let pins: Vec<_> = desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Base(VmConstraint::Boundary {
                row: VmRow::Last,
                body,
            }) if gate_cols(body) == BTreeSet::from([col::STACK0]) => Some(body),
            _ => None,
        })
        .collect();
    assert_eq!(pins.len(), 1);
    assert_eq!(eval_lean_expr(pins[0], &honest[last]), BabyBear::ZERO);
    let mut forged = honest[last].clone();
    forged[col::STACK0] = BabyBear::ONE;
    assert_ne!(eval_lean_expr(pins[0], &forged), BabyBear::ZERO);
}
