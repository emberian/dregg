/-
# Dregg2.Circuit.Emit.DyckStackEmit — the EMIT-FROM-LEAN author of the Dyck pushdown parse
descriptor (`dregg-dyck-parse-v1`, `circuit/src/dsl/dyck_stack.rs`).

## What this file IS, and the law it closes

Law #1: ZERO Rust-authored constraints. Every descriptor is AUTHORED in Lean, BYTE-PINNED here by
an `emitVmJson2` `#guard`, re-derived onto disk by `EmitByName.lean` + `scripts/emit-descriptors.sh`,
and LOADED by Rust. `dyck_parse_descriptor` was authored in RUST with no Lean emit — and the
consequence was named in `DyckStackRefine.lean`'s own header: its `dyckDesc` is a HAND
TRANSCRIPTION, so `dyck_sat_imp_row_valid` (a real, non-vacuous SAT⇒SEM theorem) was about a mirror
that could silently drift from the deployed circuit. This file is the Lean author that ends the
hand transcription: `dyckDesc` (`DyckStackRefine` §2) is now the proof-side reading of a descriptor
that is EMITTED, not re-typed.

It is authored line-for-line on the template `DfaRoutingEmit.lean` — the same IR-v2 grammar, the
same chip-lookup lowering of the hash chain, the same byte-pin discipline.

## The constraint set (Rust `dyck_stack.rs` ↦ IR-v2 carrier)

| hand-AIR constraint (`dyck_stack.rs`)                          | IR-v2 carrier                          |
|-----------------------------------------------------------------|----------------------------------------|
| `Binary{c}` (the six selectors)                                  | `Base(Gate(c·(c−1)))`                  |
| `IS_RULE + IS_TERM + IS_DONE == 1`                               | `Base(Gate)`                           |
| `SEL_BRACKET + SEL_EMPTY == IS_RULE`                             | `Base(Gate)`                           |
| `sel·(RULE_ID − r) == 0` (the sub-selector rule pins)            | `Base(Gate)`                           |
| rule-table membership `IS_RULE·(RULE_ID−1)(RULE_ID−2) == 0`      | `Base(Gate)` (vanishing poly)          |
| LHS match `IS_RULE·(STACK0 − S) == 0`                            | `Base(Gate)`                           |
| terminal top-match `IS_TERM·(STACK0 − INPUT_TOKEN) == 0`         | `Base(Gate)`                           |
| `done`: `STACK0 == 0`, `STACK_DEPTH == 0`                        | `Base(Gate)` ×2                        |
| `INPUT_POS_P1 == INPUT_POS + 1`                                  | `Base(Gate)`                           |
| the four depth deltas (`+2`, `−1`, `−1`, `0`)                    | `Base(Gate)` ×4                        |
| depth range `∏_{v=0}^{D}(STACK_DEPTH − v) == 0` (+ `DEPTH_NEXT`) | `Base(Gate)` ×2 (vanishing poly)       |
| the four fixed lanes (`op`, `cl`, `S`, `0`)                      | `Base(Gate)` ×4                        |
| `rBracket` overflow guard `local.STACK[3..5] == 0`               | `Base(Gate)` ×2                        |
| `Transition{STACK_DEPTH ← DEPTH_NEXT}`                           | `WindowGate` (transition)              |
| `rBracket` push `next.STACK[0..3] = (op, S, cl)`                 | `WindowGate` ×3 (gated on SEL_BRACKET) |
| `rBracket` remainder shift `next.STACK[3+j] = local.STACK[1+j]`  | `WindowGate` ×2                        |
| `rEmpty` / `term` pop-shift + vacated deepest cell               | `WindowGate` ×5 each                   |
| `done` hold                                                      | `WindowGate` ×5                        |
| `Gated{IS_TERM, Transition{INPUT_POS ← INPUT_POS_P1}}`           | `WindowGate`                           |
| `InvertedGated{IS_TERM, Transition{INPUT_POS ← INPUT_POS}}`      | `WindowGate` (`(1 − IS_TERM)·body`)    |
| `Hash4to1{ENTRY_HASH ← (RULE_ID, STACK0, INPUT_TOKEN, LANE_ZERO)}` | arity-4 `Poseidon2Chip` lookup       |
| `ChainedHash2to1` + `SeedHash2to1` running commitment            | arity-2 chip + `acc` copy-forward + pin|
| the four boundary pins + the two PI bindings                     | `Base(PiBinding/Boundary)`             |

The RUNNING-HASH chain is lowered EXACTLY as `DfaRoutingEmit` lowers its own (and as the Rust
adapter `circuit-prove/src/custom_leaf_adapter.rs` does): a fresh COPY-FORWARD accumulator column
`ACC` (`acc[i+1] = running[i]` via a transition `WindowGate`, `acc[0] = pi[table_commitment]` via a
first-row `PiBinding`) makes the per-row hash single-row, so `running[i] = hash_2_to_1(acc[i],
entry[i])` is ONE arity-2 chip lookup. Together these reproduce BOTH the `ChainedHash2to1` rolling
step and its `SeedHash2to1` table-commitment seed — which is why the `IS_FIRST` gating of
`SeedHash2to1` becomes the `IS_FIRST == 1` first-row boundary plus the row-0 `acc` pin.

## The depth range — the gap this file used to name, now CLOSED on both sides

This header previously recorded a deliberate non-reproduction: `dyck_stack.rs` emitted no
`0 ≤ STACK_DEPTH ≤ D` range check, so neither did this emit, and `DyckStackRefine` carried the bound
as the explicit hypothesis `DyckCanon.depth` precisely because the circuit did not enforce it. That
was a real soundness gap, not a modelling choice: the four depth deltas (`+2`/`−1`/`−1`/`0`) are
polynomial gates, hence FIELD congruences, so a WRAPPED depth (`p − 1` reading as `−1`) satisfied
every one of them.

BOTH sides now emit it. `dyck_stack.rs::vanishing_on_grid` pins `STACK_DEPTH` and `DEPTH_NEXT` to
the grid `{0, …, D}` with `∏_{v=0}^{D} (depth − v) == 0` (the `dfa_routing` small-domain idiom), and
`depthRangeBody`/`depthNextRangeBody` below are that same polynomial in this carrier — so the Lean
author is faithful to the deployed Rust, not stronger than it. `depth_range_zero_iff` proves the
tooth means what it says, and `DyckStackRefine.depth_of_sat` DISCHARGES `DyckCanon.depth` from it.

## One carrier this descriptor does NOT reproduce from the Rust — deliberately, and stated

1. **Trace width.** The Rust descriptor is 23 wide; this one is 38 (23 base + `ACC` + 2×7 chip
   lanes). The chip lanes are what the IR-v2 lookup lowering costs; the base columns 0..22 are index
   for index the Rust `dyck_stack::col` layout, so a reader can diff the two by eye.

## The loader flip — LANDED

`descriptor_by_name` (`circuit/src/descriptor_by_name.rs`) now serves `dregg-dyck-parse-v1` from
the byte-pinned `dyck-parse.json` this file emits, so the DEPLOYED dispatch object IS this
descriptor. The prover side is `dyck_stack::lift_witness_to_v2` (the 23 base columns are index for
index the Rust layout; the lift adds the `ACC` copy-forward chain and the descriptor prover fills
the chip lanes), and `circuit-prove/tests/dyck_parse_tamper.rs`'s `emitted_dyck_*` tests drive it
end-to-end: both honest words prove + verify through `prove_vm_descriptor2`, and the wrapped-depth /
occupancy-hole / dropped-remainder / terminal-top / forged-PI tampers all REJECT on the emitted
path.

What REMAINS of the v1 mirror: `dyck_parse_descriptor` + `dyck_satisfied` still exist as the
tamper suite's per-tooth ISOLATION harness (its finders pattern-match IR-v1 `ConstraintExpr`
variants to credit each reject to a named constraint; IR-v2 has no such variants). Retiring them
means porting that isolation to `VmConstraint2` shapes (and `DyckStackRefine`'s reading along with
it) — the tracked residual of the flip, test-side only: no deployed path constructs the Rust AIR.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + three genuinely-proven,
non-vacuous semantic lemmas (the remainder shift, the overflow guard, the rule-table membership —
each TRUE iff its relation holds, FALSE otherwise, with `#guard` non-vacuity witnesses on both
sides). NEW file; imports read-only.
-/
import Dregg2.Circuit.ChipNarrowLookup
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.DyckStackEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId WindowExpr WindowConstraint
   chipLookupTupleNarrow poseidon2narrow CHIP_RATE CHIP_OUT_LANES emitVmJson2)

set_option autoImplicit false

/-! ## §1 — The column layout: base columns 0..22 are `dyck_stack::col` index for index. -/

/-- Bounded stack depth carried in columns (`dyck_stack.rs::STACK_D`). -/
def STACK_D : Nat := 5

/-- `STACK[i]` — cell `i` of the bounded stack; `STACK[0]` is the top. -/
def stk (i : Nat) : Nat := i

/-- Current stack depth (pointer). -/
def STACK_DEPTH : Nat := 5
/-- The stack depth AFTER this row's action (threaded into `next.STACK_DEPTH`). -/
def DEPTH_NEXT : Nat := 6
/-- `STEP_KIND = rule` selector. -/
def IS_RULE : Nat := 7
/-- `STEP_KIND = term` selector. -/
def IS_TERM : Nat := 8
/-- `STEP_KIND = done` selector. -/
def IS_DONE : Nat := 9
/-- The production id this row fires (`RULE_NONE` on term/done rows). -/
def RULE_ID : Nat := 10
/-- The input token read on a `term` step. -/
def INPUT_TOKEN : Nat := 11
/-- Input-tape pointer. -/
def INPUT_POS : Nat := 12
/-- `INPUT_POS + 1` (witness helper). -/
def INPUT_POS_P1 : Nat := 13
/-- Rule selector: `1` iff this row fires `rBracket`. -/
def SEL_BRACKET : Nat := 14
/-- Rule selector: `1` iff this row fires `rEmpty`. -/
def SEL_EMPTY : Nat := 15
/-- Per-step commitment `hash_4_to_1(RULE_ID, STACK0, INPUT_TOKEN, 0)` (chip lookup out0). -/
def ENTRY_HASH : Nat := 16
/-- Rolling parse commitment `hash_2_to_1(acc, entry)` (chip lookup out0). -/
def RUNNING_HASH : Nat := 17
/-- First-row selector (the seed gate). -/
def IS_FIRST : Nat := 18
/-- Fixed lane `= op`. -/
def LANE_OP : Nat := 19
/-- Fixed lane `= cl`. -/
def LANE_CL : Nat := 20
/-- Fixed lane `= S`. -/
def LANE_S : Nat := 21
/-- Fixed lane `= 0` (the EMPTY push source + the 4th entry-hash lane). -/
def LANE_ZERO : Nat := 22

/-- The COPY-FORWARD accumulator: `acc[0] = pi[table_commitment]`, `acc[i+1] = running[i]`. The
`ChainedHash2to1`/`SeedHash2to1` chain's prior-accumulator carrier. Not a `dyck_stack::col` column —
it is what the IR-v2 lowering of a cross-row hash chain costs. -/
def ACC : Nat := 23

/-- Total emitted main-trace width: the 23 hand-AIR columns (Rust `dyck_stack.rs::DYCK_WIDTH`)
+ the copy-forward accumulator at index 23 (Rust `V2_ACC`). The 2 × 7 exposed permutation lane
columns the WIDE `TID_P2` tuples carried are GONE (E7 narrowing, `ChipNarrowLookup.lean`) — they sat
at lane positions 18..24 of the 25-wide tuples and entered no soundness conclusion. Kill-set
`[24, 38)` is exactly the trailing suffix, so NO column index moves — in particular Rust's
`V2_ACC = DYCK_WIDTH = 23` is UNCHANGED; only `DYCK_V2_WIDTH` shrinks (see the install note). -/
def DYCK_WIDTH : Nat := 24

/-- pi[0] `initial_symbol` — the grammar's initial nonterminal, pinning the first row's stack top. -/
def PI_INITIAL : Nat := 0
/-- pi[1] `input_len` — the `done` step pins `INPUT_POS == INPUT_LEN`. -/
def PI_INPUT_LEN : Nat := 1
/-- pi[2] `table_commitment` — the running-hash seed; ties the parse to THIS grammar. -/
def PI_TABLE : Nat := 2
/-- pi[3] `route_commitment` — the parse binding (last row's `RUNNING_HASH`). -/
def PI_ROUTE : Nat := 3
/-- Number of public inputs. -/
def DYCK_PI_COUNT : Nat := 4

/-! ## §2 — The symbol / rule alphabet (`dyck_stack.rs`, `CfgCompact.Reference`). -/

/-- Reserved EMPTY stack-cell marker. -/
def SYM_EMPTY : ℤ := 0
/-- The sole nonterminal `S`. -/
def SYM_S : ℤ := 1
/-- Terminal `op = '['`. -/
def SYM_OP : ℤ := 2
/-- Terminal `cl = ']'`. -/
def SYM_CL : ℤ := 3
/-- `rBracket : S → [ S ]`. -/
def RULE_BRACKET : ℤ := 1
/-- `rEmpty : S → ε`. -/
def RULE_EMPTY : ℤ := 2
/-- `|rBracket's RHS| = 3` (`op S cl`) ⇒ the remainder shifts by `3 − 1 = 2`. -/
def BRACKET_SHIFT : Nat := 2

/-! ## §3 — The small constraint builders (the Rust module's helpers, in IR-v2). -/

/-- `x·(x−1)` — `ConstraintExpr::Binary`. -/
def gBin (c : Nat) : EmittedExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gBoolCanon c)

/-- ⚑ **THE BYTE PIN.** `gBin` is `GateExpr.gBool` at the emitted view -- the SAME object
`AirBuilder.gBin`, `AutomataflResolveEmit.gBin`, `AutomataflStepEmit.gBin`, `DyckStackRefine.gBin`
and `RowLibraryExperiment.gBin` each wrote out separately. `rfl`, for every column: no emitted byte
moved. -/
theorem gBin_eq (c : Nat) :
    gBin c = .add (.mul (.const 1) (.mul (.var c) (.var c))) (.mul (.const (-1)) (.var c)) := rfl
/-- `sel · e` — `ConstraintExpr::Gated`. -/
def gGate (sel : Nat) (e : EmittedExpr) : EmittedExpr := .mul (.var sel) e
/-- `a − b`. -/
def gSub (a b : Nat) : EmittedExpr := .add (.var a) (.mul (.const (-1)) (.var b))
/-- `a − k` — `eq_const`. -/
def gSubK (a : Nat) (k : ℤ) : EmittedExpr := .add (.var a) (.const (-k))
/-- `a − b − k` — `diff_is`. -/
def gDiffIs (a b : Nat) (k : ℤ) : EmittedExpr := .add (gSub a b) (.const (-k))

/-- **The range constraint** `∏_{v ∈ vs} (col − v)` — `dyck_stack.rs`'s `vanishing_on_grid`
(itself copied from `dfa_routing::vanishing_on_grid`). Left-associated, so the emitted tree is
`(((x−v₀)·(x−v₁))·…)`.

The Rust builds the SAME polynomial in the expanded monomial normal form its `ConstraintExpr::
Polynomial{terms}` carrier forces (a sum of `coeff · ∏cols` terms); this tree is the product form
`EmittedExpr` carries naturally. That is the identical value in two normal forms — exactly the
relationship `ruleMembershipBody` already has with its Rust twin (`RULE_ID² − 3·RULE_ID + 2` there,
`(RULE_ID−1)(RULE_ID−2)` here). -/
def gVanishOnGrid (c : Nat) (vs : List ℤ) : EmittedExpr :=
  match vs with
  | []      => .const 1
  | v :: vs => vs.foldl (fun acc w => .mul acc (gSubK c w)) (gSubK c v)

/-- The legal depth grid `{0, …, D}` (`dyck_stack.rs::depth_grid`) — the `D + 1` integers a
`D`-cell stack's occupancy can take. -/
def depthGrid : List ℤ := [0, 1, 2, 3, 4, 5]

/-- The legal SYMBOL grid `{EMPTY, S, op, cl} = {0,1,2,3}` (`dyck_stack.rs::symbol_grid`) — the
ids a stack cell may hold. `gVanishOnGrid` over it is the cell-range leg of the occupancy tooth. -/
def symbolGrid : List ℤ := [0, 1, 2, 3]

/-- **Empty-above-pointer body** for cell `i` (`dyck_stack.rs::occupancy_tooth` family 2):
`STACK[i] · ∏_{v=i+1}^{D} (STACK_DEPTH − v)`. The depth product vanishes iff `i < STACK_DEPTH`,
so on the empty side (`i ≥ STACK_DEPTH`) the gate forces `STACK[i] = 0`. Left-associated over
the same `gSubK` factors `gVanishOnGrid` uses, but seeded with the bare cell `.var (stk i)`. -/
def emptyAboveBody (i : Nat) : EmittedExpr :=
  ((List.range' (i + 1) (STACK_D - i)).map (fun v => gSubK STACK_DEPTH (v : ℤ))).foldl
    (fun acc g => .mul acc g) (.var (stk i))

/-- **Non-empty-below-pointer body** for cell `i` (`dyck_stack.rs::occupancy_tooth` family 3):
`(STACK[i]−1)(STACK[i]−2)(STACK[i]−3) · ∏_{v=0}^{i} (STACK_DEPTH − v)`. The cubic first factor is
nonzero EXACTLY when `STACK[i] = 0` (given the cell range), and the depth product vanishes iff
`i ≥ STACK_DEPTH`; so an `EMPTY` hole strictly below the pointer (`i < STACK_DEPTH`) REJECTS. -/
def nonEmptyBelowBody (i : Nat) : EmittedExpr :=
  ((List.range' 0 (i + 1)).map (fun v => gSubK STACK_DEPTH (v : ℤ))).foldl
    (fun acc g => .mul acc g)
    (.mul (.mul (gSubK (stk i) 1) (gSubK (stk i) 2)) (gSubK (stk i) 3))

/-- `next[nc] − local[lc]` — `ConstraintExpr::Transition`. ⚑ `GateExpr.gThread` at the window view —
one object under one name; see `GateExpr.lean` §7.3. -/
def wThread (nc lc : Nat) : WindowExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow (Dregg2.Circuit.GateExpr.gThread nc lc)

theorem wThread_eq (nc lc : Nat) :
    wThread nc lc = WindowExpr.add (.nxt nc) (.mul (.const (-1)) (.loc lc)) := rfl
/-- `local[sel] · e` — a `Gated` window. -/
def wGate (sel : Nat) (e : WindowExpr) : WindowExpr := .mul (.loc sel) e
/-- `(1 − local[sel]) · e` — an `InvertedGated` window. -/
def wInvGate (sel : Nat) (e : WindowExpr) : WindowExpr :=
  .mul (.add (.const 1) (.mul (.const (-1)) (.loc sel))) e

/-- A per-row gate constraint. -/
def cg (e : EmittedExpr) : VmConstraint2 := .base (.gate e)
/-- A TRANSITION window constraint (every row but the last — the `when_transition` arm the Rust
`references_next` driver mirrors by checking rows `0..n−1`). -/
def cw (b : WindowExpr) : VmConstraint2 := .windowGate ⟨b, true⟩

/-! ### §3.1 — The stack-discipline constraint groups (`dyck_stack.rs`'s three builders). -/

/-- **The general variable-length RHS push with a remainder shift**, gated on `sel`
(`push_with_remainder_shift`). A production `A → γ` pops `local.STACK[0]` and writes `γ` over the
top, with everything under `A` shifted up by `|γ| − 1`:

1. **push** — `next.STACK[j] == rhs_lanes[j]` for `j < |γ|`;
2. **remainder shift** — `next.STACK[j] == local.STACK[j − (|γ|−1)]` for `|γ| ≤ j < D`;
3. **overflow guard** — `local.STACK[i] == 0` for `i ≥ D − (|γ|−1)`, so a push whose remainder does
   not fit REJECTS rather than silently dropping a symbol.

Written at `rhsLanes = [LANE_OP, LANE_S, LANE_CL]` (`|γ| = 3`, shift `= 2`) for the Dyck grammar.
Groups (1)+(2) are transition windows; group (3) is per-row. -/
def bracketOverflowGuards : List VmConstraint2 :=
  [ cg (gGate SEL_BRACKET (gSubK (stk 3) SYM_EMPTY))
  , cg (gGate SEL_BRACKET (gSubK (stk 4) SYM_EMPTY)) ]

/-- The `rBracket` push (`γ = op S cl`) + the remainder shift by `|γ| − 1 = 2`. -/
def bracketPushWindows : List VmConstraint2 :=
  [ cw (wGate SEL_BRACKET (wThread (stk 0) LANE_OP))
  , cw (wGate SEL_BRACKET (wThread (stk 1) LANE_S))
  , cw (wGate SEL_BRACKET (wThread (stk 2) LANE_CL))
  , cw (wGate SEL_BRACKET (wThread (stk 3) (stk 1)))
  , cw (wGate SEL_BRACKET (wThread (stk 4) (stk 2))) ]

/-- **The pop / shift-down** gated on `sel` (`pop_shift`): `next.STACK[j] == local.STACK[j+1]`, the
vacated deepest cell forced EMPTY (read from `LANE_ZERO`, the pinned constant lane). Fired by
`rEmpty` (`S → ε`) and by a `term` step. -/
def popShiftWindows (sel : Nat) : List VmConstraint2 :=
  [ cw (wGate sel (wThread (stk 0) (stk 1)))
  , cw (wGate sel (wThread (stk 1) (stk 2)))
  , cw (wGate sel (wThread (stk 2) (stk 3)))
  , cw (wGate sel (wThread (stk 3) (stk 4)))
  , cw (wGate sel (wThread (stk 4) LANE_ZERO)) ]

/-- **The hold** gated on `sel` (`hold_stack`): every stack cell threads unchanged. `done` rows
(and the `done` self-loop padding) take no action. -/
def holdStackWindows (sel : Nat) : List VmConstraint2 :=
  [ cw (wGate sel (wThread (stk 0) (stk 0)))
  , cw (wGate sel (wThread (stk 1) (stk 1)))
  , cw (wGate sel (wThread (stk 2) (stk 2)))
  , cw (wGate sel (wThread (stk 3) (stk 3)))
  , cw (wGate sel (wThread (stk 4) (stk 4))) ]

/-- The fixed constant lanes (`lane_fixes`) — the `Transition` sources for pushing constants. -/
def laneFixes : List VmConstraint2 :=
  [ cg (gSubK LANE_OP SYM_OP), cg (gSubK LANE_CL SYM_CL)
  , cg (gSubK LANE_S SYM_S), cg (gSubK LANE_ZERO SYM_EMPTY) ]

/-! ## §4 — The hash chain (the `DfaRoutingEmit` lowering, verbatim in shape). -/

/-- The per-step commitment: an arity-4 `Poseidon2Chip` lookup absorbing
`[RULE_ID, STACK0, INPUT_TOKEN, LANE_ZERO]`, binding out0 to `ENTRY_HASH` — the Rust
`Hash4to1{ENTRY_HASH ← (RULE_ID, STACK0, INPUT_TOKEN, LANE_ZERO)}`. -/
def entryHashLookup : VmConstraint2 :=
  .lookup ⟨poseidon2narrow,
    chipLookupTupleNarrow [.var RULE_ID, .var (stk 0), .var INPUT_TOKEN, .var LANE_ZERO]
      ENTRY_HASH⟩

/-- The rolling parse commitment: an arity-2 chip lookup absorbing `[ACC, ENTRY_HASH]`, binding out0
to `RUNNING_HASH`. Together with `copyForwardWindow` + `seedAccPin` this IS the Rust
`ChainedHash2to1` rolling step AND its `SeedHash2to1` table-commitment seed. -/
def runningHashLookup : VmConstraint2 :=
  .lookup ⟨poseidon2narrow,
    chipLookupTupleNarrow [.var ACC, .var ENTRY_HASH] RUNNING_HASH⟩

/-- `acc[i+1] = running[i]` — the prior accumulator carried forward (the cross-row leg of the
running-hash chain). ⚑ `GateExpr.gThread` at the window view. -/
def copyForwardBody : WindowExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gThread ACC RUNNING_HASH)

theorem copyForwardBody_eq :
    copyForwardBody = WindowExpr.add (.nxt ACC) (.mul (.const (-1)) (.loc RUNNING_HASH)) := rfl

/-- The copy-forward `WindowGate`, asserted on the transition. -/
def copyForwardWindow : VmConstraint2 := .windowGate ⟨copyForwardBody, true⟩

/-- The seed pin: first row `acc == pi[table_commitment]`, so
`running₀ = hash_2_to_1(table_commitment, entry₀)` — the `SeedHash2to1` seed, realized as the
chain's first-row accumulator pin. -/
def seedAccPin : VmConstraint2 := .base (.piBinding VmRow.first ACC PI_TABLE)

/-! ## §5 — The constraint list, in the Rust module's order. -/

/-- The remainder-shift body at cell `3` — the slice-2 tooth, named so `bracket_shift_zero_iff`
can state it. -/
def bracketShiftBody : WindowExpr := wGate SEL_BRACKET (wThread (stk 3) (stk 1))

/-- The overflow-guard body at cell `3` — the honest statement of the depth bound. -/
def bracketOverflowBody : EmittedExpr := gGate SEL_BRACKET (gSubK (stk 3) SYM_EMPTY)

/-- The rule-table membership body: `IS_RULE·(RULE_ID − 1)(RULE_ID − 2)`. -/
def ruleMembershipBody : EmittedExpr :=
  gGate IS_RULE (.mul (gSubK RULE_ID RULE_BRACKET) (gSubK RULE_ID RULE_EMPTY))

/-- Hash-preimage fields unused by an action have their unique canonical value. -/
def inactiveRuleBody : EmittedExpr :=
  .mul (.add (.const 1) (.mul (.const (-1)) (.var IS_RULE))) (.var RULE_ID)
def inactiveTokenBody : EmittedExpr :=
  .mul (.add (.const 1) (.mul (.const (-1)) (.var IS_TERM))) (.var INPUT_TOKEN)

/-- **THE TERMINAL-TOP BODY**: `IS_TERM·(STACK0 − op)(STACK0 − cl)`. On a `term` row it forces the
consumed stack top to be a TERMINAL (`op` or `cl`), never the nonterminal `S`. This is the tooth the
whole-parse soundness theorem needs to DECODE the parsed word from the trace: with it,
`DyckStackReplay.decodedWord` reads a genuine `Brk` terminal off every `term` row, so the
tape↔word correspondence a parser-soundness statement must derive is provable-by-construction rather
than assumed. Without it a `term` row could claim to consume `S`, which decodes to no terminal. -/
def terminalTopBody : EmittedExpr :=
  gGate IS_TERM (.mul (gSubK (stk 0) SYM_OP) (gSubK (stk 0) SYM_CL))

/-- **THE DEPTH-RANGE BODY** on `STACK_DEPTH` — the design's `0 ≤ STACK_DEPTH ≤ D` column property,
emitted as a real constraint. Named so `depth_range_zero_iff` can state it. -/
def depthRangeBody : EmittedExpr := gVanishOnGrid STACK_DEPTH depthGrid

/-- The same tooth on `DEPTH_NEXT` — the last row's `DEPTH_NEXT` is not covered by the
`Transition{STACK_DEPTH ← DEPTH_NEXT}` carry-back, so it is pinned directly. -/
def depthNextRangeBody : EmittedExpr := gVanishOnGrid DEPTH_NEXT depthGrid

/-- **THE DEPTH↔OCCUPANCY TOOTH** (`dyck_stack.rs::occupancy_tooth`): per stack cell, the
cell-range gate + the empty-above-pointer gate + the non-empty-below-pointer gate. Together with
the depth range they pin cells `[0, STACK_DEPTH)` to be EXACTLY the non-`EMPTY` ones — the
invariant the general `decode` needs, and the tooth the design named as still owed. -/
def occupancyTooth : List VmConstraint2 :=
  [ cg (gVanishOnGrid (stk 0) symbolGrid), cg (emptyAboveBody 0), cg (nonEmptyBelowBody 0)
  , cg (gVanishOnGrid (stk 1) symbolGrid), cg (emptyAboveBody 1), cg (nonEmptyBelowBody 1)
  , cg (gVanishOnGrid (stk 2) symbolGrid), cg (emptyAboveBody 2), cg (nonEmptyBelowBody 2)
  , cg (gVanishOnGrid (stk 3) symbolGrid), cg (emptyAboveBody 3), cg (nonEmptyBelowBody 3)
  , cg (gVanishOnGrid (stk 4) symbolGrid), cg (emptyAboveBody 4), cg (nonEmptyBelowBody 4) ]

/-- The flat constraint list. -/
def dyckConstraints : List VmConstraint2 :=
  -- the two child hashes (entry + running).
  [ entryHashLookup, runningHashLookup
  -- selector booleans.
  , cg (gBin IS_RULE), cg (gBin IS_TERM), cg (gBin IS_DONE), cg (gBin IS_FIRST)
  , cg (gBin SEL_BRACKET), cg (gBin SEL_EMPTY)
  -- exactly one action kind.
  , cg (.add (.add (.add (.var IS_RULE) (.var IS_TERM)) (.var IS_DONE)) (.const (-1)))
  -- the rule sub-selectors partition IS_RULE.
  , cg (.add (.add (.var SEL_BRACKET) (.var SEL_EMPTY)) (.mul (.const (-1)) (.var IS_RULE)))
  -- rule sub-selectors pinned to their ids.
  , cg (gGate SEL_BRACKET (gSubK RULE_ID RULE_BRACKET))
  , cg (gGate SEL_EMPTY (gSubK RULE_ID RULE_EMPTY))
  -- rule-table membership.
  , ruleMembershipBody |> cg
  , cg inactiveRuleBody, cg inactiveTokenBody
  -- top match: a rule pops S; a term's top IS the consumed token.
  , cg (gGate IS_RULE (gSubK (stk 0) SYM_S))
  , cg (gGate IS_TERM (gSub (stk 0) INPUT_TOKEN))
  -- terminal-top: a term row's stack top is a TERMINAL (op or cl), never the nonterminal S.
  , cg terminalTopBody
  -- done: empty top at depth zero.
  , cg (gGate IS_DONE (gSubK (stk 0) SYM_EMPTY))
  , cg (gGate IS_DONE (gSubK STACK_DEPTH 0))
  -- input-pointer helper.
  , cg (gDiffIs INPUT_POS_P1 INPUT_POS 1)
  -- DEPTH RANGE: 0 ≤ STACK_DEPTH ≤ D, and the same for DEPTH_NEXT. Without these the depth
  -- deltas below are only congruences mod `p` and a WRAPPED depth is not excluded.
  , cg depthRangeBody
  , cg depthNextRangeBody
  -- depth deltas per action.
  , cg (gGate SEL_BRACKET (gDiffIs DEPTH_NEXT STACK_DEPTH 2))
  , cg (gGate SEL_EMPTY (gDiffIs DEPTH_NEXT STACK_DEPTH (-1)))
  , cg (gGate IS_TERM (gDiffIs DEPTH_NEXT STACK_DEPTH (-1)))
  , cg (gGate IS_DONE (gDiffIs DEPTH_NEXT STACK_DEPTH 0)) ]
  ++ laneFixes
  ++ bracketOverflowGuards
  -- depth↔occupancy tooth: STACK_DEPTH counts exactly the non-EMPTY prefix of the cells.
  ++ occupancyTooth
  -- ============ cross-row (transition) constraints ============
  ++ [ cw (wThread STACK_DEPTH DEPTH_NEXT) ]
  ++ bracketPushWindows
  ++ popShiftWindows SEL_EMPTY
  ++ popShiftWindows IS_TERM
  ++ holdStackWindows IS_DONE
  ++ [ cw (wGate IS_TERM (wThread INPUT_POS INPUT_POS_P1))
     , cw (wInvGate IS_TERM (wThread INPUT_POS INPUT_POS))
     , copyForwardWindow
  -- ============ boundaries ============
     , .base (.piBinding VmRow.first (stk 0) PI_INITIAL)
     , .base (.boundary VmRow.first (gSubK STACK_DEPTH 1))
     , .base (.boundary VmRow.first (gSubK INPUT_POS 0))
     , .base (.boundary VmRow.first (gSubK IS_FIRST 1))
     , seedAccPin
     , .base (.boundary VmRow.last (gSubK IS_DONE 1))
     , .base (.boundary VmRow.last (gSubK STACK_DEPTH 0))
     , .base (.piBinding VmRow.last INPUT_POS PI_INPUT_LEN)
     , .base (.piBinding VmRow.last RUNNING_HASH PI_ROUTE)
     -- Base gates skip the final row, but its entry hash is in the route. Pin every
     -- preimage field there; the final row is the canonical done/padding entry.
     , .base (.boundary VmRow.last (gSubK RULE_ID 0))
     , .base (.boundary VmRow.last (gSubK INPUT_TOKEN 0))
     , .base (.boundary VmRow.last (gSubK (stk 0) 0))
     , .base (.boundary VmRow.last (gSubK LANE_ZERO 0)) ]

/-- **`dyckParseDesc`** — the Dyck pushdown parse descriptor, AUTHORED IN LEAN. The chip table
(`TID_P2`) is IMPLICITLY present (Presence-detected from the lookups), so `tables` is empty as the
working descriptors leave it. -/
def dyckParseDesc : EffectVmDescriptor2 :=
  { name        := "dregg-dyck-parse-v1"
  , traceWidth  := DYCK_WIDTH
  , piCount     := DYCK_PI_COUNT
  , tables      := []
  , constraints := dyckConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §6 — The byte-pinned wire golden.

`EmitByName.lean` routes `emitVmJson2 dyckParseDesc` to `circuit/descriptors/by-name/dyck-parse.json`,
and `scripts/check-descriptor-drift.sh` re-derives that file from THIS emission on every run. A drift
on either side breaks this `#guard` (Lean) or the drift gate (disk). -/

#guard emitVmJson2 dyckParseDesc ==
  "{\"name\":\"dregg-dyck-parse-v1\",\"ir\":2,\"trace_width\":24,\"public_input_count\":4,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":8,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":22},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":16}]},{\"t\":\"lookup\",\"table\":8,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":16},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":17}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":7}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":7}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"var\",\"v\":18}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":18}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":8}},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":7}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"const\",\"v\":-2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"const\",\"v\":-1}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"const\",\"v\":-2}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":7}}},\"r\":{\"t\":\"var\",\"v\":10}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"var\",\"v\":11}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-2}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-3}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-3}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-5}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-3}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-5}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"const\",\"v\":-2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"const\",\"v\":1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"const\",\"v\":1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"const\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"const\",\"v\":-2}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"const\",\"v\":-3}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"const\",\"v\":0}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-3}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-5}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-3}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-3}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-5}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-1}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-3}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":0}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-3}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-5}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-1}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-3}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":0}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-5}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-1}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-3}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":0}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-5}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-1}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-3}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":0}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-2}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-3}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-4}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":6}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":19}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":21}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":20}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":3}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":22}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":3}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":22}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":3}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":13}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":8}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":12}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":17}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"const\",\"v\":0}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":23,\"pi_index\":2},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":0}}},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":12,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":17,\"pi_index\":3},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"const\",\"v\":0}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"const\",\"v\":0}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":0}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"const\",\"v\":0}}}],\"hash_sites\":[],\"ranges\":[]}"


/-! ## §7 — Genuinely-proven, non-vacuous semantic teeth. -/

/-- **THE REMAINDER-SHIFT TOOTH** (the slice-2 correction). Under a firing `rBracket`
(`SEL_BRACKET = 1`), the shift body is zero EXACTLY when the next row's `STACK[3]` IS this row's
`STACK[1]` — the cell that sat under the popped `S` reappears beneath the pushed RHS. TRUE when the
remainder survives, FALSE when it is dropped or forged. -/
theorem bracket_shift_zero_iff (env : VmRowEnv) (h : env.loc SEL_BRACKET = 1) :
    bracketShiftBody.eval env = 0 ↔ env.nxt (stk 3) = env.loc (stk 1) := by
  simp only [bracketShiftBody, wGate, wThread_eq, WindowExpr.eval, h, one_mul]
  constructor <;> intro hx <;> omega

/-- **THE OVERFLOW-GUARD TOOTH.** Under a firing `rBracket`, the guard body is zero EXACTLY when
this row's `STACK[3]` is EMPTY — the cell whose shifted destination (`STACK[5]`) leaves the `D = 5`
buffer. A push that does not fit REJECTS; it never silently drops a symbol. -/
theorem bracket_overflow_zero_iff (a : Assignment) (h : a SEL_BRACKET = 1) :
    bracketOverflowBody.eval a = 0 ↔ a (stk 3) = SYM_EMPTY := by
  simp only [bracketOverflowBody, gGate, gSubK, EmittedExpr.eval, h, one_mul, SYM_EMPTY]
  constructor <;> intro hx <;> omega

/-- **THE RULE-TABLE TOOTH.** On a `rule` row the membership body is zero EXACTLY when `RULE_ID` is
one of the Dyck grammar's two productions — the analogue of `dfa_routing`'s transition-table lookup
at 2 rules. Over ℤ this is the `(RULE_ID−1)(RULE_ID−2) = 0` factorization; the deployed field
denotation recovers it from canonicality (`DyckStackRefine.dyck_sat_imp_row_valid`'s
`ruleMembership`). -/
theorem rule_membership_zero_iff (a : Assignment) (h : a IS_RULE = 1) :
    ruleMembershipBody.eval a = 0 ↔ a RULE_ID = RULE_BRACKET ∨ a RULE_ID = RULE_EMPTY := by
  simp only [ruleMembershipBody, gGate, gSubK, EmittedExpr.eval, h, one_mul,
    RULE_BRACKET, RULE_EMPTY]
  constructor
  · intro hx
    rcases mul_eq_zero.mp hx with hy | hy
    · left; omega
    · right; omega
  · intro hx; rcases hx with hy | hy <;> rw [hy] <;> ring

/-- **THE TERMINAL-TOP TOOTH.** On a `term` row the terminal-top body is zero over ℤ EXACTLY when
`STACK0` is one of the two Dyck terminals (`op` or `cl`) — never the nonterminal `S`. This is the
`(STACK0−2)(STACK0−3) = 0` factorization gated on `IS_TERM`; it is what lets the whole-parse
soundness theorem decode a genuine terminal off every `term` row. -/
theorem terminal_top_zero_iff (a : Assignment) (h : a IS_TERM = 1) :
    terminalTopBody.eval a = 0 ↔ a (stk 0) = SYM_OP ∨ a (stk 0) = SYM_CL := by
  simp only [terminalTopBody, gGate, gSubK, EmittedExpr.eval, h, one_mul, SYM_OP, SYM_CL]
  constructor
  · intro hx
    rcases mul_eq_zero.mp hx with hy | hy
    · left; omega
    · right; omega
  · intro hx; rcases hx with hy | hy <;> rw [hy] <;> ring

/-- **THE DEPTH-RANGE TOOTH.** The range body is zero over ℤ EXACTLY when `STACK_DEPTH` is one of
the `D + 1 = 6` legal occupancies of a `D = 5`-cell stack. This is the design's
`0 ≤ STACK_DEPTH ≤ D` column property as a proven biconditional: TRUE on the grid, FALSE off it —
including at the wrapped values (`−1`, `−2`) that satisfy the `±1` depth deltas as congruences and
are exactly what this tooth exists to refuse. -/
theorem depth_range_zero_iff (a : Assignment) :
    depthRangeBody.eval a = 0 ↔ 0 ≤ a STACK_DEPTH ∧ a STACK_DEPTH ≤ 5 := by
  simp only [depthRangeBody, gVanishOnGrid, depthGrid, gSubK, List.foldl, EmittedExpr.eval]
  constructor
  · intro hx
    rcases mul_eq_zero.mp hx with hy | hy
    · rcases mul_eq_zero.mp hy with hz | hz
      · rcases mul_eq_zero.mp hz with hw | hw
        · rcases mul_eq_zero.mp hw with hv | hv
          · rcases mul_eq_zero.mp hv with hu | hu <;> omega
          · omega
        · omega
      · omega
    · omega
  · intro ⟨h0, h5⟩
    interval_cases h : a STACK_DEPTH <;> norm_num

/-- The same tooth on `DEPTH_NEXT`. -/
theorem depth_next_range_zero_iff (a : Assignment) :
    depthNextRangeBody.eval a = 0 ↔ 0 ≤ a DEPTH_NEXT ∧ a DEPTH_NEXT ≤ 5 := by
  simp only [depthNextRangeBody, gVanishOnGrid, depthGrid, gSubK, List.foldl, EmittedExpr.eval]
  constructor
  · intro hx
    rcases mul_eq_zero.mp hx with hy | hy
    · rcases mul_eq_zero.mp hy with hz | hz
      · rcases mul_eq_zero.mp hz with hw | hw
        · rcases mul_eq_zero.mp hw with hv | hv
          · rcases mul_eq_zero.mp hv with hu | hu <;> omega
          · omega
        · omega
      · omega
    · omega
  · intro ⟨h0, h5⟩
    interval_cases h : a DEPTH_NEXT <;> norm_num

/-! ### Non-vacuity witnesses: each tooth ACCEPTS the honest cell and REJECTS the tampered one.
The values are the `"[[]]"` nested run's row 2 → row 3 window (`build_nested_witness`), the exact
window `circuit-prove/tests/dyck_parse_tamper.rs` mutates. -/

/-- Row 2 → row 3 of the honest nested run: `SEL_BRACKET = 1`, `local.STACK[1] = cl`,
`next.STACK[3] = cl` (the shifted remainder), `local.STACK[3] = 0` (no overflow). -/
def honestNestedEnv : VmRowEnv :=
  { loc := fun c => if c = SEL_BRACKET then 1 else if c = stk 1 then SYM_CL else 0
  , nxt := fun c => if c = stk 3 then SYM_CL else 0
  , pub := fun _ => 0 }

/-- The same window with the remainder DROPPED (`tamper_dropped_remainder_rejects`). -/
def droppedRemainderEnv : VmRowEnv :=
  { honestNestedEnv with nxt := fun _ => 0 }

/-- The same window with a symbol parked where the shift cannot carry it
(`tamper_overflowing_push_rejects`). -/
def overflowingEnv : Assignment :=
  fun c => if c = SEL_BRACKET then 1 else if c = stk 3 then SYM_CL else 0

/-- The honest `rBracket` row (`SEL_BRACKET = 1`, no overflow). -/
def honestGuardAsg : Assignment := fun c => if c = SEL_BRACKET then 1 else 0

-- the remainder shift ACCEPTS the surviving remainder and REJECTS the dropped one.
#guard decide (bracketShiftBody.eval honestNestedEnv = 0)
#guard decide (¬ (bracketShiftBody.eval droppedRemainderEnv = 0))
-- the overflow guard ACCEPTS the fitting push and REJECTS the one that would drop a symbol.
#guard decide (bracketOverflowBody.eval honestGuardAsg = 0)
#guard decide (¬ (bracketOverflowBody.eval overflowingEnv = 0))
-- rule-table membership ACCEPTS rBracket and REJECTS an invented rule id (3).
#guard decide (ruleMembershipBody.eval
  (fun c => if c = IS_RULE then 1 else if c = RULE_ID then 1 else 0) = 0)
#guard decide (¬ (ruleMembershipBody.eval
  (fun c => if c = IS_RULE then 1 else if c = RULE_ID then 3 else 0) = 0))
-- terminal-top ACCEPTS a term row consuming op/cl and REJECTS one claiming the nonterminal S.
#guard decide (terminalTopBody.eval
  (fun c => if c = IS_TERM then 1 else if c = stk 0 then SYM_OP else 0) = 0)
#guard decide (terminalTopBody.eval
  (fun c => if c = IS_TERM then 1 else if c = stk 0 then SYM_CL else 0) = 0)
#guard decide (¬ (terminalTopBody.eval
  (fun c => if c = IS_TERM then 1 else if c = stk 0 then SYM_S else 0) = 0))
-- the depth range ACCEPTS every legal occupancy of the D = 5 buffer...
#guard decide (depthRangeBody.eval (fun c => if c = STACK_DEPTH then 0 else 0) = 0)
#guard decide (depthRangeBody.eval (fun c => if c = STACK_DEPTH then 1 else 0) = 0)
#guard decide (depthRangeBody.eval (fun c => if c = STACK_DEPTH then 4 else 0) = 0)
#guard decide (depthRangeBody.eval (fun c => if c = STACK_DEPTH then 5 else 0) = 0)
-- ...and REJECTS the overflow (D + 1) and the WRAPPED depths the deltas cannot see.
#guard decide (¬ (depthRangeBody.eval (fun c => if c = STACK_DEPTH then 6 else 0) = 0))
#guard decide (¬ (depthRangeBody.eval (fun c => if c = STACK_DEPTH then -1 else 0) = 0))
#guard decide (¬ (depthRangeBody.eval (fun c => if c = STACK_DEPTH then 2013265920 else 0) = 0))
#guard decide (depthNextRangeBody.eval (fun c => if c = DEPTH_NEXT then 3 else 0) = 0)
#guard decide (¬ (depthNextRangeBody.eval (fun c => if c = DEPTH_NEXT then 6 else 0) = 0))

/-! ### Shape pins. -/

#guard dyckParseDesc.traceWidth == DYCK_WIDTH
#guard dyckParseDesc.piCount == 4
#guard dyckParseDesc.name == "dregg-dyck-parse-v1"
theorem constraint_count : dyckParseDesc.constraints.length = 85 := rfl
#assert_axioms constraint_count
#guard (chipLookupTupleNarrow [.var RULE_ID, .var (stk 0), .var INPUT_TOKEN, .var LANE_ZERO]
         ENTRY_HASH).length == CHIP_RATE + 1 + 1
#guard (chipLookupTupleNarrow [.var ACC, .var ENTRY_HASH] RUNNING_HASH).length
         == CHIP_RATE + 1 + 1
-- The narrowing dropped exactly 2 × (CHIP_OUT_LANES − 1) = 14 main columns for the same two
-- forced digest equations; the copy-forward accumulator index (Rust `V2_ACC`) does NOT move.
#guard DYCK_WIDTH + 2 * (CHIP_OUT_LANES - 1) == 38
#guard ACC == 23
#guard poseidon2narrow.wireId == 8

#assert_axioms bracket_shift_zero_iff
#assert_axioms bracket_overflow_zero_iff
#assert_axioms rule_membership_zero_iff
#assert_axioms terminal_top_zero_iff
#assert_axioms depth_range_zero_iff
#assert_axioms depth_next_range_zero_iff

end Dregg2.Circuit.Emit.DyckStackEmit
