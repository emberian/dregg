//! `dregg-dyck-parse-v1`: the *parse-as-derivation* circuit's **witness side**
//! (`docs/DESIGN-parse-as-derivation.md`, the zk-succinct path).
//!
//! The DEPLOYED descriptor is the Lean-emitted, byte-pinned `DyckStackEmit.dyckParseDesc`
//! (`metatheory/Dregg2/Circuit/Emit/DyckStackEmit.lean`), served by
//! [`crate::descriptor_by_name::descriptor_by_name`] as `dregg-dyck-parse-v1` and proven
//! through the IR-v2 batch prover (`descriptor_ir2::prove_vm_descriptor2`). This module
//! carries **no AIR constraints**: it is the column/PI layout, the symbol/rule alphabet,
//! the honest trace builders ([`build_witness`] and the two bundled words), the rule-table
//! commitment, and the [`lift_witness_to_v2`] lift onto the emitted 24-wide shape.
//!
//! (History: the descriptor was first authored here in Rust IR-v1 — `dyck_parse_descriptor`
//! plus the `dyck_satisfied` predicate — on the `dfa_routing` template. The loader flip
//! moved authorship to Lean, and the v1 mirror was RETIRED once the per-tooth tamper
//! canaries in `circuit-prove/tests/dyck_parse_tamper.rs` were ported to isolate the
//! emitted `VmConstraint2` shapes directly. The teeth documented below now live in
//! `DyckStackEmit.lean`; this header keeps the semantic story because the WITNESS builder
//! must lay traces those teeth accept.)
//!
//! # What the deployed descriptor proves
//!
//! A trace satisfying it IS an accepting **leftmost pushdown replay**
//! (`Dregg2.Crypto.CfgCompact.Replay`) of the one-bracket **Dyck** grammar
//! `S → [ S ] | ε` (`CfgCompact.lean` `Reference`: `dyck`, rules `rBracket`/`rEmpty`)
//! on its input word, with the parse's per-step commitments folded into a public
//! `route_commitment`.
//!
//! # The variable-length RHS push with a remainder shift
//!
//! A production with RHS length `L` pops one cell and writes
//!
//! ```text
//!   next.STACK[j] = rhs[j]                  for j < L          (the pushed RHS)
//!   next.STACK[j] = local.STACK[j - (L-1)]  for L ≤ j < D      (the REMAINDER SHIFT)
//!   local.STACK[i] == 0                     for i ≥ D - (L-1)  (the OVERFLOW GUARD)
//! ```
//!
//! The remainder shift is what makes a nested word verify: `"[[]]"`'s second
//! `rBracket` fires with `cl` still sitting under the popped `S`, and that `cl` must
//! reappear beneath the pushed RHS or the closing bracket has nothing to match.
//! The overflow guard is the honest statement of the depth bound: a push whose
//! remainder does not fit in the `D`-wide buffer **REJECTS** — it never silently drops
//! a symbol. Alongside them ride the depth-range vanishing polys (`0 ≤ depth ≤ D` as a
//! real constraint, refusing a field-wrapped depth) and the depth↔occupancy tooth
//! (`STACK_DEPTH` counts EXACTLY the non-`EMPTY` prefix of the stack cells).
//!
//! # Stack sizing (honest)
//!
//! Stack cells hold **symbol ids**; `0` is the reserved EMPTY cell. The `rBracket`
//! spike pushes three symbols for one popped `S`, so bracket-nesting `k` bounds the
//! stack at depth `k + 2` for nonempty words. `D = 5` therefore covers `k ≤ 3` — enough for both
//! bundled witnesses: `"[]"` (peak 3) and `"[[]]"` (peak 4). A word needing more
//! nesting than `D` allows is not mis-proved; it fails the overflow guard, and
//! [`build_witness`] panics rather than emit such a truncated row.
//!
//! # Symbol / rule encoding
//!
//! `S = 1` (the sole nonterminal), `op = '[' = 2`, `cl = ']' = 3`.
//! Rule ids: `0 = none` (term/done rows), `rBracket = 1` (`S → [ S ]`),
//! `rEmpty = 2` (`S → ε`).

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_4_to_1};

// ============================================================================
// Symbol / rule alphabet
// ============================================================================

/// Reserved EMPTY stack-cell marker (a cell holding no symbol).
pub const SYM_EMPTY: u32 = 0;
/// The sole nonterminal `S` (`CfgCompact.Reference.NTs.S`).
pub const SYM_S: u32 = 1;
/// Terminal `op` = `'['` (`CfgCompact.Reference.Brk.op`).
pub const SYM_OP: u32 = 2;
/// Terminal `cl` = `']'` (`CfgCompact.Reference.Brk.cl`).
pub const SYM_CL: u32 = 3;

/// No rule fires on this row (term / done rows).
pub const RULE_NONE: u32 = 0;
/// `rBracket : S → [ S ]` (`CfgCompact.Reference.rBracket`).
pub const RULE_BRACKET: u32 = 1;
/// `rEmpty : S → ε` (`CfgCompact.Reference.rEmpty`).
pub const RULE_EMPTY: u32 = 2;

/// Bounded stack depth carried in columns (top at `STACK0`). Bracket-nesting `k`
/// needs `k + 2` for nonempty words; `D = 5` covers `k ≤ 3`. Words that would exceed
/// it fail the overflow guard rather than being mis-proved.
pub const STACK_D: usize = 5;

/// The RHS symbol lengths of the grammar's productions, for reference:
/// `rBracket` pushes 3 (`op S cl`), `rEmpty` pushes 0.
pub const RHS_LEN_BRACKET: usize = 3;

// ============================================================================
// Column / public-input indices
// ============================================================================

/// Column indices for the Dyck-parse trace.
pub mod col {
    use super::STACK_D;

    /// `STACK[i]` — cell `i` of the bounded stack (`STACK[0]` is the top, the symbol
    /// a `rule`/`term` step reads). Valid for `i < STACK_D`.
    pub const fn stack(i: usize) -> usize {
        assert!(i < STACK_D, "stack cell index out of the D-wide buffer");
        i
    }

    /// `STACK[0]` — the stack top.
    pub const STACK0: usize = 0;
    /// `STACK[1]` — the first remainder cell (the top of what sits under a popped top).
    pub const STACK1: usize = 1;
    /// `STACK[2]`.
    pub const STACK2: usize = 2;
    /// `STACK[3]` — the first cell a `rBracket` remainder shift WRITES.
    pub const STACK3: usize = 3;
    /// `STACK[4]` — the deepest cell the `D = 5` buffer carries.
    pub const STACK4: usize = 4;

    /// Current stack depth (pointer), pinned `0` at `done`, `1` at the first row.
    pub const STACK_DEPTH: usize = STACK_D;
    /// The stack depth AFTER this row's action (witness helper; threaded into
    /// `next.STACK_DEPTH` by a `Transition`). Constrained per action selector.
    pub const DEPTH_NEXT: usize = STACK_D + 1;
    /// `STEP_KIND = rule` selector (binary).
    pub const IS_RULE: usize = STACK_D + 2;
    /// `STEP_KIND = term` selector (binary).
    pub const IS_TERM: usize = STACK_D + 3;
    /// `STEP_KIND = done` selector (binary).
    pub const IS_DONE: usize = STACK_D + 4;
    /// The production id this row fires (`RULE_*`); `RULE_NONE` on term/done rows.
    pub const RULE_ID: usize = STACK_D + 5;
    /// The input token read on a `term` step (the tape symbol at `INPUT_POS`).
    pub const INPUT_TOKEN: usize = STACK_D + 6;
    /// Input-tape pointer.
    pub const INPUT_POS: usize = STACK_D + 7;
    /// `INPUT_POS + 1` (witness helper; threaded into `next.INPUT_POS` on a `term`).
    pub const INPUT_POS_P1: usize = STACK_D + 8;
    /// Rule selector: `1` iff this row fires `rBracket` (binary, `⊆ IS_RULE`).
    pub const SEL_BRACKET: usize = STACK_D + 9;
    /// Rule selector: `1` iff this row fires `rEmpty` (binary, `⊆ IS_RULE`).
    pub const SEL_EMPTY: usize = STACK_D + 10;
    /// Per-step commitment `hash_4_to_1(RULE_ID, STACK0, INPUT_TOKEN, 0)`.
    pub const ENTRY_HASH: usize = STACK_D + 11;
    /// Rolling parse commitment up to and including this row.
    pub const RUNNING_HASH: usize = STACK_D + 12;
    /// First-row selector (gates the running-hash seed).
    pub const IS_FIRST: usize = STACK_D + 13;
    /// Fixed lane `= op` (a `Transition` source for pushing the constant `op`).
    pub const LANE_OP: usize = STACK_D + 14;
    /// Fixed lane `= cl`.
    pub const LANE_CL: usize = STACK_D + 15;
    /// Fixed lane `= S`.
    pub const LANE_S: usize = STACK_D + 16;
    /// Fixed lane `= 0` (the EMPTY push source + the 4th entry-hash lane).
    pub const LANE_ZERO: usize = STACK_D + 17;
}

/// Public-input indices.
pub mod pi {
    /// The grammar's initial nonterminal (`S`) — pins the first row's stack top.
    pub const INITIAL_SYMBOL: usize = 0;
    /// The input word length (the `done` step pins `INPUT_POS == INPUT_LEN`).
    pub const INPUT_LEN: usize = 1;
    /// The rule-table commitment (the running-hash seed; ties the parse to `dyck`).
    pub const TABLE_COMMITMENT: usize = 2;
    /// The parse `route_commitment` (last row's `RUNNING_HASH`).
    pub const ROUTE_COMMITMENT: usize = 3;
}

/// Trace width.
pub const DYCK_WIDTH: usize = STACK_D + 18;

/// Number of public inputs.
pub const DYCK_PI_COUNT: usize = 4;

/// The rule-table commitment: `hash_2_to_1(enc(rBracket), enc(rEmpty))`, where each
/// rule is encoded `hash_4_to_1(rule_id, lhs, rhs0, rhs1)`. This is the `pi[2]`
/// running-hash seed — it ties the parse to *this* grammar (analogue of
/// `dfa_routing::compute_table_commitment`).
pub fn dyck_rule_table_commitment() -> BabyBear {
    // rBracket: S → [ S ] ; encode (id, lhs=S, rhs head = op, rhs next = S).
    let e_bracket = hash_4_to_1(&[
        BabyBear::new(RULE_BRACKET),
        BabyBear::new(SYM_S),
        BabyBear::new(SYM_OP),
        BabyBear::new(SYM_S),
    ]);
    // rEmpty: S → ε ; encode (id, lhs=S, empty, empty).
    let e_empty = hash_4_to_1(&[
        BabyBear::new(RULE_EMPTY),
        BabyBear::new(SYM_S),
        BabyBear::new(SYM_EMPTY),
        BabyBear::new(SYM_EMPTY),
    ]);
    hash_2_to_1(e_bracket, e_empty)
}

// ============================================================================
// Trace generation — honest accepting runs
// ============================================================================

/// One machine action, before power-of-two padding.
#[derive(Clone, Copy)]
pub enum Action {
    Rule(u32), // fire production `rule_id`
    Term(u32), // match terminal `token` on top against the input tape
    Done,
}

/// The record-facing statement of `DyckStackBound.recordPre`: canonical rule
/// entries, terminal entries, and at least two done rows, padded to a power of
/// two. Returns `(main_rows, public_inputs)` without constructing a witness.
/// An arbitrary bracket word has a commitment; proving it still requires a
/// valid parse. Out-of-alphabet input and arithmetic overflow are refused.
pub fn record_public_inputs(input: &[u32]) -> Option<(usize, Vec<BabyBear>)> {
    if input.iter().any(|&x| x != SYM_OP && x != SYM_CL) {
        return None;
    }
    let opens = input.iter().take_while(|&&x| x == SYM_OP).count();
    let core_len = input.len().checked_add(opens)?.checked_add(1)?;
    let rows = 1usize.checked_shl(core_len.checked_add(1)?.ilog2() + 1)?;
    let input_len = u32::try_from(input.len()).ok()?;
    if core_len >= crate::field::BABYBEAR_P as usize || input_len >= crate::field::BABYBEAR_P {
        return None;
    }
    let seed = dyck_rule_table_commitment();
    let mut route = seed;
    let mut absorb = |entry: [u32; 4]| {
        route = hash_2_to_1(route, hash_4_to_1(&entry.map(BabyBear::new)));
    };
    for _ in 0..opens {
        absorb([RULE_BRACKET, SYM_S, 0, 0]);
        absorb([0, SYM_OP, SYM_OP, 0]);
    }
    absorb([RULE_EMPTY, SYM_S, 0, 0]);
    for &token in &input[opens..] {
        absorb([0, token, token, 0]);
    }
    for _ in core_len..rows {
        absorb([0, 0, 0, 0]);
    }
    Some((
        rows,
        vec![BabyBear::new(SYM_S), BabyBear::new(input_len), seed, route],
    ))
}

/// Verify a Dyck proof against the caller's record. Both the route public input
/// and main-trace height are recomputed, so padding cannot be chosen by the prover.
pub fn verify_record(
    proof: &crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
    input: &[u32],
) -> Result<(), String> {
    use p3_uni_stark::StarkGenericConfig;
    let (rows, pis) = record_public_inputs(input).ok_or("invalid Dyck record encoding")?;
    // The production v1/v2 configs have the same PCS type and hiding mode;
    // FRI parameter differences do not affect the degree's ZK offset.
    let zk = crate::plonky3_prover::create_config().is_zk();
    let expected_degree = rows.ilog2() as usize + zk;
    if proof.degree_bits.first().copied() != Some(expected_degree) {
        return Err("Dyck proof main-trace height does not match record padding".into());
    }
    let desc = crate::descriptor_by_name::descriptor_by_name("dregg-dyck-parse-v1")
        .ok_or("Dyck descriptor unavailable")?;
    crate::descriptor_ir2::verify_vm_descriptor2(&desc, proof, &pis)
}

/// Build the accepting-parse trace + public inputs for the word `"[]"` (`[op, cl]`),
/// the exact word `CfgCompact.Reference.brackets_replays` accepts.
///
/// The rows are the faithful pushdown replay:
///   `rule rBracket · term '[' · rule rEmpty · term ']' · done`,
/// padded to a power of two with `done` self-loops. Returns the row-major trace
/// (width [`DYCK_WIDTH`]) and the public inputs
/// `[initial_symbol, input_len, table_commitment, route_commitment]`.
pub fn build_brackets_witness() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let input: Vec<u32> = vec![SYM_OP, SYM_CL];
    let actions = vec![
        Action::Rule(RULE_BRACKET),
        Action::Term(SYM_OP),
        Action::Rule(RULE_EMPTY),
        Action::Term(SYM_CL),
        Action::Done,
    ];
    build_witness(&input, &actions)
}

/// Build the accepting-parse trace + public inputs for the **nested** word `"[[]]"`
/// (`[op, op, cl, cl]`) — the slice-2 witness.
///
/// `S ⟹ [S] ⟹ [[S]] ⟹ [[]]`, replayed as
/// `rule rBracket · term '[' · rule rBracket · term '[' · rule rEmpty · term ']' ·
/// term ']' · done` — 8 action rows, padded to 16 so the accepting row has a successor.
///
/// This is the word slice 1 could not verify: the SECOND `rBracket` (row 2) fires
/// with the stack at `[S, cl]`, so the outer `cl` sits under the popped `S` and must
/// survive the push. The remainder shift carries it to `STACK3`, whence the two
/// `term ']'` rows consume it. Without the shift the run has nothing to close with.
pub fn build_nested_witness() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let input: Vec<u32> = vec![SYM_OP, SYM_OP, SYM_CL, SYM_CL];
    let actions = vec![
        Action::Rule(RULE_BRACKET),
        Action::Term(SYM_OP),
        Action::Rule(RULE_BRACKET),
        Action::Term(SYM_OP),
        Action::Rule(RULE_EMPTY),
        Action::Term(SYM_CL),
        Action::Term(SYM_CL),
        Action::Done,
    ];
    build_witness(&input, &actions)
}

/// General trace builder: fold `actions` over the pushdown machine, laying out one
/// row per action and padding to a power of two with `done`. Used by
/// [`build_brackets_witness`], [`build_nested_witness`], and by the tamper test's
/// honest baseline.
///
/// This is the prover-side companion of the descriptor: it fills every witness
/// helper column (`DEPTH_NEXT`, `INPUT_POS_P1`, `SEL_*`, the lanes, the running
/// hash) so the honest run satisfies the descriptor. The live stack is a `Vec`, so
/// the push here is the *unbounded* pushdown step; the descriptor's overflow guard is
/// what refuses a run whose stack outgrows the `D`-wide buffer, and
/// [`build_witness`] panics rather than emit such a truncated row.
pub fn build_witness(input: &[u32], actions: &[Action]) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let table_commitment = dyck_rule_table_commitment();

    // Live machine state.
    let mut stack: Vec<u32> = vec![SYM_S]; // starts at [initial]
    let mut input_pos: u32 = 0;

    // Keep a successor after the first done, including a power-of-two action count.
    let n_pad = (actions.len() + 1).next_power_of_two().max(2);
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(n_pad);
    let mut running = table_commitment;

    let emit = |stack: &[u32],
                depth_next: u32,
                input_pos: u32,
                kind: (bool, bool, bool),
                rule_id: u32,
                input_token: u32,
                sel_bracket: u32,
                sel_empty: u32,
                is_first: u32,
                running: &mut BabyBear,
                first: bool|
     -> Vec<BabyBear> {
        assert!(
            stack.len() <= STACK_D,
            "the live stack ({}) outgrew the D = {STACK_D} buffer — widen STACK_D; \
             the descriptor's overflow guard would REJECT a truncated row",
            stack.len()
        );
        let top = stack.first().copied().unwrap_or(SYM_EMPTY);
        let depth = stack.len() as u32;
        let entry = hash_4_to_1(&[
            BabyBear::new(rule_id),
            BabyBear::new(top),
            BabyBear::new(input_token),
            BabyBear::ZERO,
        ]);
        if first {
            *running = hash_2_to_1(table_commitment_of(), entry);
        } else {
            *running = hash_2_to_1(*running, entry);
        }
        let mut row = vec![BabyBear::ZERO; DYCK_WIDTH];
        for i in 0..STACK_D {
            row[col::stack(i)] = BabyBear::new(stack.get(i).copied().unwrap_or(SYM_EMPTY));
        }
        row[col::STACK_DEPTH] = BabyBear::new(depth);
        row[col::DEPTH_NEXT] = BabyBear::new(depth_next);
        row[col::IS_RULE] = BabyBear::new(kind.0 as u32);
        row[col::IS_TERM] = BabyBear::new(kind.1 as u32);
        row[col::IS_DONE] = BabyBear::new(kind.2 as u32);
        row[col::RULE_ID] = BabyBear::new(rule_id);
        row[col::INPUT_TOKEN] = BabyBear::new(input_token);
        row[col::INPUT_POS] = BabyBear::new(input_pos);
        row[col::INPUT_POS_P1] = BabyBear::new(input_pos + 1);
        row[col::SEL_BRACKET] = BabyBear::new(sel_bracket);
        row[col::SEL_EMPTY] = BabyBear::new(sel_empty);
        row[col::ENTRY_HASH] = entry;
        row[col::RUNNING_HASH] = *running;
        row[col::IS_FIRST] = BabyBear::new(is_first);
        row[col::LANE_OP] = BabyBear::new(SYM_OP);
        row[col::LANE_CL] = BabyBear::new(SYM_CL);
        row[col::LANE_S] = BabyBear::new(SYM_S);
        row[col::LANE_ZERO] = BabyBear::ZERO;
        row
    };

    for (i, action) in actions.iter().enumerate() {
        let is_first = if i == 0 { 1 } else { 0 };
        let first = i == 0;
        match *action {
            Action::Rule(rule_id) => {
                // depth after: pop 1, push |rhs| — and the REMAINDER (everything under
                // the popped top) rides along, which is the slice-2 correction.
                let (sel_bracket, sel_empty, new_stack) = match rule_id {
                    RULE_BRACKET => {
                        // pop S, push [op, S, cl] OVER the surviving remainder.
                        let mut s = vec![SYM_OP, SYM_S, SYM_CL];
                        s.extend_from_slice(&stack[1..]);
                        (1u32, 0u32, s)
                    }
                    RULE_EMPTY => {
                        // pop S, push nothing → shift down.
                        (0u32, 1u32, stack[1..].to_vec())
                    }
                    _ => (0, 0, stack.clone()),
                };
                let depth_next = new_stack.len() as u32;
                rows.push(emit(
                    &stack,
                    depth_next,
                    input_pos,
                    (true, false, false),
                    rule_id,
                    /*token*/ 0,
                    sel_bracket,
                    sel_empty,
                    is_first,
                    &mut running,
                    first,
                ));
                stack = new_stack;
            }
            Action::Term(token) => {
                let depth_next = (stack.len() as u32).saturating_sub(1);
                rows.push(emit(
                    &stack,
                    depth_next,
                    input_pos,
                    (false, true, false),
                    RULE_NONE,
                    token,
                    0,
                    0,
                    is_first,
                    &mut running,
                    first,
                ));
                // pop the matched terminal, advance the tape.
                stack.remove(0);
                input_pos += 1;
            }
            Action::Done => {
                let depth_next = stack.len() as u32; // 0, unchanged
                rows.push(emit(
                    &stack,
                    depth_next,
                    input_pos,
                    (false, false, true),
                    RULE_NONE,
                    0,
                    0,
                    0,
                    is_first,
                    &mut running,
                    first,
                ));
            }
        }
    }

    // Pad to a power of two with `done` self-loops (stack empty, tape at end).
    while rows.len() < n_pad {
        rows.push(emit(
            &stack,
            0,
            input_pos,
            (false, false, true),
            RULE_NONE,
            0,
            0,
            0,
            0,
            &mut running,
            false,
        ));
    }

    let route_commitment = rows.last().unwrap()[col::RUNNING_HASH];
    let public_inputs = vec![
        BabyBear::new(SYM_S), // initial nonterminal
        BabyBear::new(input.len() as u32),
        dyck_rule_table_commitment(),
        route_commitment,
    ];
    (rows, public_inputs)
}

/// The rule-table commitment as a plain function (used inside the row emitter's
/// seed step). Kept separate so the closure captures nothing borrow-conflicting.
fn table_commitment_of() -> BabyBear {
    dyck_rule_table_commitment()
}

// ============================================================================
// The IR-v2 witness lift — the loader-flip prover side
// ============================================================================

/// The `ACC` copy-forward accumulator column of the Lean-emitted IR-v2 descriptor
/// (`DyckStackEmit.lean` §1): `acc[0] = pi[TABLE_COMMITMENT]`, `acc[i+1] = running[i]` — the
/// prior-accumulator carrier that makes the rolling `hash_2_to_1` chain single-row.
pub const V2_ACC: usize = DYCK_WIDTH;

/// The Lean-emitted IR-v2 trace width: the 23 base columns ([`DYCK_WIDTH`], index for index the
/// `col` layout above) + [`V2_ACC`]. The two chip lookups are now NARROW (`chipLookupTupleNarrow`,
/// `DyckStackEmit.lean` §5), so the descriptor no longer exposes 2×7 lane columns in the main
/// trace — E7 deleted `[24, 38)` as a pure tail truncation. [`V2_ACC`] = 23 sits BELOW the kill-set
/// and does not move (machine-checked Lean-side by `#guard ACC == 23`).
pub const DYCK_V2_WIDTH: usize = DYCK_WIDTH + 1;

/// Lift a base-width witness (from [`build_witness`] / [`build_brackets_witness`] /
/// [`build_nested_witness`]) to the base trace of the Lean-emitted IR-v2 descriptor
/// (`descriptor_by_name("dregg-dyck-parse-v1")`, authored in `DyckStackEmit.lean`).
///
/// The v2 base columns `0..23` are the v1 columns index for index, so the lift is: widen each row
/// to [`DYCK_V2_WIDTH`] (= 24) and fill [`V2_ACC`] with the copy-forward chain
/// (`acc[0] = table_commitment`, `acc[i+1] = running[i]`). The descriptor's two chip lookups are
/// NARROW, so there are no exposed lane columns to leave for the prover — `prove_vm_descriptor2`
/// still derives the chip outputs from the descriptor's lookups (`trace_with_chip_lanes`), it just
/// no longer needs 14 main-trace columns to publish them.
pub fn lift_witness_to_v2(trace: &[Vec<BabyBear>]) -> Vec<Vec<BabyBear>> {
    let mut acc = dyck_rule_table_commitment();
    trace
        .iter()
        .map(|row| {
            let mut v2 = row.clone();
            v2.resize(DYCK_V2_WIDTH, BabyBear::ZERO);
            v2[V2_ACC] = acc;
            acc = row[col::RUNNING_HASH];
            v2
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::ir2_eval_accepts_i64;

    /// The nested run's stack really does carry a remainder under a pushed RHS: at the
    /// SECOND `rBracket` (row 2) the stack is `[S, cl]`, and the row after it is
    /// `[op, S, cl, cl]` — the trailing `cl` is the shifted remainder at `STACK3`.
    #[test]
    fn nested_run_exercises_the_remainder() {
        let (trace, _pi) = build_nested_witness();
        assert_eq!(trace[2][col::STACK0], BabyBear::new(SYM_S));
        assert_eq!(
            trace[2][col::STACK1],
            BabyBear::new(SYM_CL),
            "the remainder"
        );
        assert_eq!(trace[3][col::STACK0], BabyBear::new(SYM_OP));
        assert_eq!(trace[3][col::STACK1], BabyBear::new(SYM_S));
        assert_eq!(trace[3][col::STACK2], BabyBear::new(SYM_CL));
        assert_eq!(
            trace[3][col::STACK3],
            BabyBear::new(SYM_CL),
            "the remainder must survive the push, shifted by |rhs| - 1 = 2"
        );
        assert_eq!(trace[3][col::STACK_DEPTH], BabyBear::new(4));
    }

    /// The v2 lift is the copy-forward accumulator chain the emitted descriptor's
    /// single-row hash step reads: `acc[0] = table_commitment`, `acc[i+1] = running[i]`,
    /// rows widened to the emitted 24 (the narrow-chip descriptor exposes no lane columns).
    #[test]
    fn lift_carries_the_acc_chain() {
        let (trace, pi_vals) = build_brackets_witness();
        let v2 = lift_witness_to_v2(&trace);
        assert_eq!(v2.len(), trace.len());
        for row in &v2 {
            assert_eq!(row.len(), DYCK_V2_WIDTH);
        }
        assert_eq!(
            v2[0][V2_ACC],
            pi_vals[pi::TABLE_COMMITMENT],
            "the chain seeds at the rule-table commitment"
        );
        for i in 1..v2.len() {
            assert_eq!(
                v2[i][V2_ACC],
                trace[i - 1][col::RUNNING_HASH],
                "acc[{i}] must carry the prior row's running hash"
            );
        }
    }

    /// Convert a lifted trace + PIs to the `i64` rows the row-local oracle takes.
    fn to_i64(trace: &[Vec<BabyBear>], pi_vals: &[BabyBear]) -> (Vec<Vec<i64>>, Vec<i64>) {
        let rows = trace
            .iter()
            .map(|r| r.iter().map(|x| x.as_u32() as i64).collect())
            .collect();
        let pis = pi_vals.iter().map(|x| x.as_u32() as i64).collect();
        (rows, pis)
    }

    /// Both honest witnesses satisfy the DEPLOYED (loaded, Lean-emitted) descriptor's
    /// row-local constraints — the real `Ir2Air::Main` evaluator over the real dispatch,
    /// not a hand mirror. (The bus arms — the two Poseidon2 chip lookups — are the batch
    /// assembly's job; the full prove/verify teeth live in
    /// `circuit-prove/tests/dyck_parse_tamper.rs`.)
    #[test]
    fn emitted_descriptor_accepts_the_honest_witnesses_row_locally() {
        let desc = descriptor_by_name("dregg-dyck-parse-v1")
            .expect("the deployed dispatch must serve the Dyck descriptor");
        for (word, (trace, pi_vals)) in [
            ("[]", build_brackets_witness()),
            ("[[]]", build_nested_witness()),
        ] {
            let (rows, pis) = to_i64(&lift_witness_to_v2(&trace), &pi_vals);
            assert!(
                ir2_eval_accepts_i64(&desc, &rows, &pis),
                "the honest '{word}' parse must satisfy the emitted descriptor row-locally"
            );
        }
    }

    /// ...and the acceptance is non-vacuous: a single mutated stack cell (the `term '['`
    /// row's top flipped `op → cl`) fails the same row-local evaluator.
    #[test]
    fn emitted_descriptor_rejects_a_tampered_witness_row_locally() {
        let desc = descriptor_by_name("dregg-dyck-parse-v1")
            .expect("the deployed dispatch must serve the Dyck descriptor");
        let (trace, pi_vals) = build_brackets_witness();
        let mut v2 = lift_witness_to_v2(&trace);
        v2[1][col::STACK0] = BabyBear::new(SYM_CL);
        let (rows, pis) = to_i64(&v2, &pi_vals);
        assert!(
            !ir2_eval_accepts_i64(&desc, &rows, &pis),
            "a mutated stack cell must REJECT row-locally (the term top-match gate)"
        );
    }
}
