/-
# `Dregg2.Circuit.Emit.AirProgramRows` — ⚑⚑⚑ THE ROW WINDOW **IS** A STEP OF THE INTERPRETER.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Nothing here is a Rust gate, a Rust builder, or a Rust
`air_accepts`. Every fact cashed below is reached by MEMBERSHIP in
`MinaWrapVerifierProgram.programAir`'s own leg list — the list `lowerTiedAir` lowers — read through
`EffectAirIR.AirLeg.forces`, never re-typed. House Law #1.

## ⚑⚑ THE GAP THIS CLOSES, IN THE WORDS OF THE FILE THAT LEFT IT

`MinaWrapClosingAir` §b, 2026-08-09, after the seven transcript descriptors got their
`CertifiedRefines`:

> **obligation 2, which nothing in this tree discharges**: that a row window satisfying all the
> forced legs IS a step of `runProgAt` — the ALU relations, the one-hot routing, the register
> window and the ROM lookup composed over 2 048 rows into the interpreter's transition function,
> with the routing lemmas' `hsel` one-hot hypotheses supplied by the ROM manifest rather than
> assumed. […] **What is still absent is the composition**: no theorem assembles them into "row
> `k+1`'s register file is `stepRegsAt` of row `k`'s", and none inducts that over 2 048 rows to
> `runRowsAt`.

`rows_track_the_interpreter` (§8) is that theorem. `runs_the_program` (§9) is its `runProgAt` form,
and `MinaWrapVerifierSpongeFp.the_absorb_program_permutes_gen` composes onto it in §10.

## ⚑ THE SHAPE IS `AirCrossRow.rcbSat_of_rows`'s, AND THE PIECES MAP ONE TO ONE

| `AirCrossRow` (RCB row)              | here (the machine)                                  |
|--------------------------------------|-----------------------------------------------------|
| `carried_constant` — the one induction | `pc_is_the_row_index` + `rows_track_the_interpreter` |
| `gather` — 33 rows into 1 assignment | `regVal` — the register block a row PRESENTS         |
| `SlotsCarry` (discharged §7)         | `RowsForced` (the legs, at every row)                |
| `PoolsRanged` (still a premise there)| `RangeTablesHonest` (still a premise here — §11.1)   |

⚠ **EVERY COLUMN FACT IS STATED MOD `P`, AND THE REGISTER FILE IS NOW STATED OVER ℤ.** Keeping the
two apart is most of the work:

* **`P` — BabyBear.** `AirLeg.forces` on a `gate`/`window` is `body ≡ 0 [ZMOD PMOD]` with
  `PMOD = P` by `rfl`, so every COLUMN fact this file derives is a congruence mod `P`. A register
  column is NOT range-checked by `programAir` (§11.2), so `tr t (regCol r + i)` is known only up to
  `P` — which is exactly why `regVal` reads it through `· % P`.
* **`N` — the Pasta modulus.** The ALU's conclusion is a DIVISIBILITY,
  `N ∣ sVal x · sVal y − sVal z`, so the arithmetic relay runs mod `N`.
* ⚑⚑ **AND `Tracks` IS AN ℤ EQUALITY** — `regVal a r = st r`, no modulus. It was a congruence mod
  `N` until 2026-08-10 and could not have been anything else: no leg was a less-than-the-modulus
  certificate on `z`, so `r, r+p, … r+4p` all fit inside the `2^256` window `z`'s limb ranges buy.
  `MinaWrapVerifierProgram.zCanonLegs` is now a leg of `programAir`, `z_is_canonical` reads it, and
  `eq_of_modEq_of_lt` closes the gap: two values in `[0, N)` that agree mod `N` are equal.

`AirCrossRow`'s `PhaseIndicator` was FALSE of the descriptor for exactly one missing `% P`, and
`tr 0 (SEL 0) = 1 + P` refuted it. Every statement below is in the reading
`prove_vm_descriptor2` performs, from the start — including the ℤ one, which is reached THROUGH the
mod-`P` reading of 32 bodies each provably below `P` in absolute value, never around it.

## ⚑ WHY THE TWO MODULI DO NOT COLLIDE — the canonicality relay, and it is the load-bearing idea

A register limb is forced only mod `P`; the ALU speaks about `sVal` over ℤ. Naively these do not
compose, and the composition would need a range check on the register file that `programAir` does
not emit. It closes anyway, and the reason is structural:

* the routing gate forces `x_i ≡ REGᵣ_i [ZMOD P]`, and **`x_i` IS range-checked** (`limbCols X_BASE`
  is a declared `limbs` leg), so the register's residue is pinned to an 8-bit value AT EVERY READ;
* the register window forces `nxt(REGᵣ_i) ≡ z_i [ZMOD P]`, and **`z_i` IS range-checked**, so the
  residue written is an 8-bit value AT EVERY WRITE.

So `regVal` — the block read through `· % P` — is a well-defined field element on any satisfying
trace, `sVal (tr t) X_BASE = regVal (tr t) I.xr` **over ℤ** (`operand_x_is_the_register`), and the
mod-`N` chain runs. ⚑ Nothing in this file assumes a register column is canonical.

## ⚑ WHAT THE MANIFEST BUYS, AND WHY IT IS NOT AN ASSUMPTION ABOUT THE PROVER

`xRoute_forces_operand` takes `hsel : ∀ s < NREG, a (XSEL_BASE + s) = if s = r then 1 else 0` — an
**ℤ equality**, not a congruence. That is not a weakness and it is not assumed here: §6 DERIVES it
from the ROM lookup. `TableSem.exactPublicRows` makes the table the descriptor's own bytes, tuple
membership is list EQUALITY, and `romRow` emits `oneHot I.xr` — so the selector cells are pinned to
`0`/`1` over ℤ by the manifest, and no booleanity-plus-sum argument (which would only ever give a
congruence, and would rest on the prover's own selectors) is needed. The same route pins
`SEL_MUL`/`SEL_ADD`/`SEL_SUB` to the exact `= 1` the ALU forcing theorems want, and the 32 immediate
limbs to the descriptor's constants.

## ⚑ THE MODULUS-GENERAL FORM IS THE ONLY FORM

`programAir` is parametric in the limb vector `pl`; `MinaWrapVerifierSponge` §3 made the interpreter
parametric in the modulus and proved the Fp one is its instance by `rfl`. §8 is stated at
`(pl, N)` with `pl`'s two structural facts as hypotheses, and §9's two corollaries are it at
`(pLimb, pN)` and `(qLimb, qN)`. There is no second proof and no twin.

## ⚠ WHAT THIS DOES NOT CLOSE — §11 is the list, read it before quoting anything here

1. `RangeTablesHonest` is a **premise**, the same one `AirCrossRow`/`AirSelectorForcing` carry as
   `PoolsRanged`. It is the lookup argument's own meaning, one rail below any leg.
2. `Tracks` at row 0 is a **premise** — `programAir` pins no register column on the first row; a
   boundary does (`sboxPins`), and supplying it is that boundary's job.
3. The **last row's transition legs do not fire** (`AirLeg.forces` guards them on `isLast = false`),
   so the final instruction's write is forced only when a row follows it. Named
   `the_last_instruction_needs_a_row_after_it`.
4. `InstrOk` is a well-formedness condition on the PROGRAM — descriptor data, not prover data.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`; zero `#guard`s.
Nothing is emitted by name; no VK rotates; nothing re-emits; no fingerprint moves.
-/
import Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp
import Dregg2.Circuit.Emit.AirCrossRow

namespace Dregg2.Circuit.Emit.AirProgramRows

open Dregg2.Circuit (Assignment Expr)
open Dregg2.Circuit.DescriptorIR2 (TraceFamily WindowExpr TableId exactPublicTable)
open Dregg2.Circuit.EffectAirIR (AirLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.EffectLower (P)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound
  (SK SB CB NG sumL sumL_nil sumL_cons sumL_append sumL_congr sVal limbAt limbAt_bounds
   limbCols rangeTidW
   pLimb qLimb pLimb_bounds qLimb_bounds pLimb_recomposes qLimb_recomposes
   X_BASE Y_BASE Z_BASE)
open Dregg2.Circuit.Emit.PastaAddSubSound
  (NA ACB CBITS cnBody cnExpr_eval cn_gates_force_below_the_modulus)
open Dregg2.Circuit.Emit.MinaWrapVerifierAir
  (ALU_WIDTH ALU_Q_BASE ALU_C_BASE ALU_AC_COL ALU_ACAR_BASE SEL_MUL SEL_ADD SEL_SUB SEL_CHAIN
   aluMulExpr aluAddSubExpr aluCarryCols aluAcarCols)
open Dregg2.Circuit.Emit.MinaWrapVerifierProgram
open Dregg2.Circuit.Emit.MinaWrapVerifierSponge
  (refMul refAdd refSub opResultAt stepRegsAt runProgAt runProgAt_append
   allocAt sboxInstrs mdsRowInstrs)
open Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp
  (rcOf absorbCoreP the_absorb_program_permutes_gen)
open Dregg2.Circuit.Emit.PastaPoseidonFq (Params)
open Dregg2.Circuit.Emit.AirCrossRow (RowTrace rowEnv)

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## §1 — ⚑ THE LIMB RECOMPOSITION, GENERAL.

`pLimb_recomposes` is a `decide` at one value. The immediate route needs the same fact at an
ARBITRARY `Instr.imm`, so it is proved here as an induction on the limb count rather than decided
at a literal — the shape `MinaWrapVerifierProgram.romRow` emits for every instruction. -/

/-- `List.range (k+1)`'s sum is `List.range k`'s plus the last term. -/
theorem sumL_range_succ (f : Nat → ℤ) (k : Nat) :
    sumL (List.range (k + 1)) f = sumL (List.range k) f + f k := by
  rw [List.range_succ, sumL_append]
  simp [sumL]

/-- The value the first `k` `SB`-bit limbs of `v` recompose to: `v` truncated to `SB·k` bits. -/
theorem limbs_recompose (v : Nat) : ∀ k : Nat,
    sumL (List.range k) (fun i => ((2 : ℤ) ^ SB) ^ i * limbAt v i)
      = ((v % 2 ^ (SB * k) : Nat) : ℤ) := by
  intro k
  induction k with
  | zero => simp [sumL]
  | succ k ih =>
      rw [sumL_range_succ, ih]
      have hAB : (2 : Nat) ^ (SB * (k + 1)) = 2 ^ (SB * k) * 2 ^ SB := by
        rw [← pow_add]; ring_nf
      have hnat : v % 2 ^ (SB * (k + 1))
          = v % 2 ^ (SB * k) + 2 ^ (SB * k) * (v / 2 ^ (SB * k) % 2 ^ SB) := by
        rw [hAB]
        have h1 : v % (2 ^ (SB * k) * 2 ^ SB) / 2 ^ (SB * k) = v / 2 ^ (SB * k) % 2 ^ SB :=
          Nat.mod_mul_right_div_self v _ _
        have h2 : v % (2 ^ (SB * k) * 2 ^ SB) % 2 ^ (SB * k) = v % 2 ^ (SB * k) :=
          Nat.mod_mod_of_dvd v ⟨2 ^ SB, rfl⟩
        have h3 := Nat.div_add_mod (v % (2 ^ (SB * k) * 2 ^ SB)) (2 ^ (SB * k))
        rw [← h1, ← h2]
        omega
      rw [hnat]
      have hp : ((2 : ℤ) ^ SB) ^ k = ((2 ^ (SB * k) : Nat) : ℤ) := by
        push_cast; rw [← pow_mul]
      rw [hp]
      simp [limbAt]

/-- ⚑ **THE `SK` LIMBS OF A CANONICAL VALUE RECOMPOSE TO IT.** `SB · SK = 256` and both Pasta
primes are 255-bit, so every `Instr.imm` and every interpreter register is inside the window. -/
theorem limbs_recompose_full (v : Nat) (h : v < 2 ^ (SB * SK)) :
    sumL (List.range SK) (fun i => ((2 : ℤ) ^ SB) ^ i * limbAt v i) = (v : ℤ) := by
  rw [limbs_recompose v SK, Nat.mod_eq_of_lt h]

/-- The encoding window, as a literal: `2^256`. -/
theorem limb_window_eq : (2 : Nat) ^ (SB * SK) = 2 ^ 256 := rfl

/-! ## §2 — ⚑ THE READING OF A ROW, AND WHAT A ROW IS TRACKING.

A `window` leg buys a congruence mod `P` and nothing else, so a register column's CONTENT is its
residue. `regVal` is that reading, and `Tracks` is the relation to the interpreter's register file
— mod the PASTA modulus, because that is the resolution the ALU's conclusion has. -/

/-- ⚑ Every column read mod `P` — the only reading a `gate`/`window` leg can force. -/
def canonRow (a : Assignment) : Assignment := fun c => a c % P

/-- ⚑⚑ **THE FIELD ELEMENT A ROW'S REGISTER BLOCK PRESENTS.** `sVal` at `regCol r`, of the row read
mod `P`. Writing `sVal (tr t) (regCol r)` instead would be a claim about integers the descriptor
never pins. -/
def regVal (a : Assignment) (r : Nat) : ℤ := sVal (canonRow a) (regCol r)

/-- ⚑⚑⚑ **THE TRACE'S REGISTER FILE IS THE INTERPRETER'S — OVER ℤ.**

⚠ **This was `Tracks (N : Nat) (a) (st) : ∀ r < NREG, regVal a r ≡ st r [ZMOD N]` until the
canonicity certificate landed, and the change is the point of that certificate.** An ℤ-equality
`Tracks` was FALSE of the descriptor while no leg was a less-than-the-modulus certificate on `z`:
`z`'s eight-bit limbs bought `sVal z < 2^256` against `pN ≈ 2^254.9`, so `r, r+p, … r+4p` all fit
with their own range-checked quotients, and `AirCrossRow.PhaseIndicator`'s first statement is the
precedent for what stating it anyway would have been. `MinaWrapVerifierProgram.zCanonLegs` is now a
leg of `programAir` and `z_is_canonical` is what it buys, so the equality is now a THEOREM.

⚑ **The modulus parameter is GONE, not defaulted.** An ℤ equality has no modulus to carry, and a
retained-but-unused `N` would let every stale `Tracks N …` call site keep elaborating against a
statement that no longer means what it did. Dropping the argument makes them REFUSE. -/
def Tracks (a : Assignment) (st : RegFile) : Prop :=
  ∀ r, r < NREG → regVal a r = (st r : ℤ)

/-- Two values inside `[0, N)` that agree mod `N` are equal. The one arithmetic step that turns the
ALU's divisibility plus the certificate's bound into an equality. -/
theorem eq_of_modEq_of_lt {N : Nat} {a b : ℤ} (ha : 0 ≤ a) (ha' : a < (N : ℤ))
    (hb : 0 ≤ b) (hb' : b < (N : ℤ)) (h : a ≡ b [ZMOD (N : ℤ)]) : a = b := by
  have h1 : a % (N : ℤ) = a := Int.emod_eq_of_lt ha ha'
  have h2 : b % (N : ℤ) = b := Int.emod_eq_of_lt hb hb'
  rw [Int.ModEq, h1, h2] at h
  exact h

/-- A congruence mod `P` IS equality of residues — `Int.ModEq` is that by definition, and this is
the step that turns the only fact a `window` leg gives into a fact about `regVal`. -/
theorem canonRow_eq_of_modEq {a b : Assignment} {c d : Nat} (h : a c ≡ b d [ZMOD P]) :
    canonRow a c = canonRow b d := h

/-- A column already inside `[0, P)` reads itself. -/
theorem canonRow_of_small {a : Assignment} {c : Nat} (h0 : 0 ≤ a c) (h1 : a c < P) :
    canonRow a c = a c := Int.emod_eq_of_lt h0 h1

/-- An 8-bit limb is inside `[0, P)`: `2^8 = 256 ≤ P`. -/
theorem small_of_byte {v : ℤ} (h0 : 0 ≤ v) (h1 : v < 2 ^ SB) : 0 ≤ v ∧ v < P := by
  refine ⟨h0, lt_of_lt_of_le h1 ?_⟩
  norm_num [SB, Dregg2.Circuit.Emit.EffectLower.P]

/-! ## §3 — ⚑ THE PREMISES, NAMED.

Three, and each is named rather than inlined so §11 can say exactly what is still standing. -/

/-- ⚑ **THE DECLARED RANGE TABLES CONTAIN ONLY WHAT THEY SAY.** The same premise `AirCrossRow`
carries as `PoolsRanged` and `AirSelectorForcing` names as the thing worth building once for the
whole cone: a `limbs` leg's `forces` is MEMBERSHIP in `tf`, and turning that into a numeric bound is
the lookup argument's own meaning, one rail below any leg. -/
def RangeTablesHonest (tf : TraceFamily) : Prop :=
  (∀ v : ℤ, [v] ∈ tf (rangeTidW SB) → 0 ≤ v ∧ v < 2 ^ SB)
  ∧ (∀ v : ℤ, [v] ∈ tf (rangeTidW CB) → 0 ≤ v ∧ v < 2 ^ CB)
  ∧ (∀ v : ℤ, [v] ∈ tf (rangeTidW CBITS) → 0 ≤ v ∧ v < 2)

/-- ⚑ **THE ROM TABLE IS THE DESCRIPTOR'S OWN BYTES.** `TableDef.publicContentsFaithful` at this
table, unfolded — the obligation `PublicTablesFaithful` imposes on every `exactPublicRows`
declaration and the deployed verifier enforces. -/
def RomFaithful (prog : List Instr) (tf : TraceFamily) : Prop :=
  tf ROM_TID = exactPublicTable (romRows prog)

/-- ⚑ **EVERY LEG OF THE MACHINE IS FORCED ON ROWS `0 … n−1`.** `isLast = false` on each of them,
which is what a `.transition` leg needs to fire — see §11.3 for the row that is left out. -/
def RowsForced (pl : Nat → ℤ) (prog : List Instr) (tr : RowTrace) (pub chal : Assignment)
    (tf : TraceFamily) (n : Nat) : Prop :=
  ∀ t, t < n → ∀ l ∈ (programAir pl prog).legs,
    l.forces tf (rowEnv tr pub chal t) (t == 0) false

/-- ⚑ **WELL-FORMEDNESS OF AN INSTRUCTION** — a condition on DESCRIPTOR data, never on the witness.
⚠ `wr` is deliberately unconstrained: `romRow` emits `oneHot I.wr`, all-zero for `I.wr ≥ NREG`, and
`stepRegsAt` writes only when `I.wr < NREG`, so the two agree on "writes nothing" without a side
condition. `xr < NREG` is needed because an all-zero `XSEL` block has no register to route from
(and `xselSumExpr` would refuse the row); `yr ≤ NREG` because `NREG` is the immediate and anything
above it is a register the interpreter would read and the manifest would not name. -/
structure InstrOk (N : Nat) (I : Instr) : Prop where
  hop  : I.op = 1 ∨ I.op = 2 ∨ I.op = 3
  hxr  : I.xr < NREG
  hyr  : I.yr ≤ NREG
  himm : I.imm < N

/-! ## §4 — ⚑ THE LEGS, BY MEMBERSHIP.

Each lemma exhibits ONE leg of `programAir pl prog` and reads its `forces` into the vocabulary the
per-row lemmas of `MinaWrapVerifierProgram` / `MinaWrapVerifierAir` consume: `P ∣ <body>`. ⚠ The
membership is against `(programAir pl prog).legs`, the list `lowerTiedAir` lowers — not against a
re-typed copy. -/

section Legs
variable (pl : Nat → ℤ) (prog : List Instr)

theorem mem_mulGate {m : Nat} (hm : m < NG) :
    AirLeg.gate ⟨aluMulExpr pl m, Expr.const 0⟩ ∈ (programAir pl prog).legs := by
  have h : AirLeg.gate ⟨aluMulExpr pl m, Expr.const 0⟩
      ∈ (List.range NG).map (fun k => AirLeg.gate ⟨aluMulExpr pl k, Expr.const 0⟩) :=
    List.mem_map_of_mem (List.mem_range.mpr hm)
  simp only [programAir, List.mem_append]
  tauto

theorem mem_addGate {m : Nat} (hm : m < NA) :
    AirLeg.gate ⟨aluAddSubExpr SEL_ADD pl 1 (-1) m, Expr.const 0⟩
      ∈ (programAir pl prog).legs := by
  have h : AirLeg.gate ⟨aluAddSubExpr SEL_ADD pl 1 (-1) m, Expr.const 0⟩
      ∈ (List.range NA).map
          (fun k => AirLeg.gate ⟨aluAddSubExpr SEL_ADD pl 1 (-1) k, Expr.const 0⟩) :=
    List.mem_map_of_mem (List.mem_range.mpr hm)
  simp only [programAir, List.mem_append]
  tauto

theorem mem_subGate {m : Nat} (hm : m < NA) :
    AirLeg.gate ⟨aluAddSubExpr SEL_SUB pl (-1) 1 m, Expr.const 0⟩
      ∈ (programAir pl prog).legs := by
  have h : AirLeg.gate ⟨aluAddSubExpr SEL_SUB pl (-1) 1 m, Expr.const 0⟩
      ∈ (List.range NA).map
          (fun k => AirLeg.gate ⟨aluAddSubExpr SEL_SUB pl (-1) 1 k, Expr.const 0⟩) :=
    List.mem_map_of_mem (List.mem_range.mpr hm)
  simp only [programAir, List.mem_append]
  tauto

theorem mem_xRoute {i : Nat} (hi : i < SK) :
    AirLeg.gate ⟨xRouteExpr i, Expr.const 0⟩ ∈ (programAir pl prog).legs := by
  have h : AirLeg.gate ⟨xRouteExpr i, Expr.const 0⟩
      ∈ (List.range SK).map (fun j => AirLeg.gate ⟨xRouteExpr j, Expr.const 0⟩) :=
    List.mem_map_of_mem (List.mem_range.mpr hi)
  simp only [programAir, List.mem_append]
  tauto

theorem mem_yRoute {i : Nat} (hi : i < SK) :
    AirLeg.gate ⟨yRouteExpr i, Expr.const 0⟩ ∈ (programAir pl prog).legs := by
  have h : AirLeg.gate ⟨yRouteExpr i, Expr.const 0⟩
      ∈ (List.range SK).map (fun j => AirLeg.gate ⟨yRouteExpr j, Expr.const 0⟩) :=
    List.mem_map_of_mem (List.mem_range.mpr hi)
  simp only [programAir, List.mem_append]
  tauto

theorem mem_regWindow {r i : Nat} (hr : r < NREG) (hi : i < SK) :
    AirLeg.window ⟨Dregg2.Circuit.TableAirIR.RowSel.transition, regWindowExpr r i⟩
      ∈ (programAir pl prog).legs := by
  have h : AirLeg.window ⟨Dregg2.Circuit.TableAirIR.RowSel.transition, regWindowExpr r i⟩
      ∈ regWindowLegs := by
    refine List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩
    exact List.mem_map_of_mem (List.mem_range.mpr hi)
  simp only [programAir, List.mem_append]
  tauto

theorem mem_pcStart :
    AirLeg.window ⟨Dregg2.Circuit.TableAirIR.RowSel.first, pcStartExpr⟩
      ∈ (programAir pl prog).legs := by
  simp only [programAir, List.mem_append, List.mem_cons]
  tauto

theorem mem_pcThread :
    AirLeg.window ⟨Dregg2.Circuit.TableAirIR.RowSel.transition, pcThreadExpr⟩
      ∈ (programAir pl prog).legs := by
  simp only [programAir, List.mem_append, List.mem_cons]
  tauto

theorem mem_romLookup :
    AirLeg.lookup { table := ROM_TID, tuple := romTuple } ∈ (programAir pl prog).legs := by
  simp only [programAir, List.mem_append, List.mem_cons]
  tauto

theorem mem_limbsX :
    AirLeg.limbs ⟨limbCols X_BASE, SB, rangeTidW SB⟩ ∈ (programAir pl prog).legs := by
  simp only [programAir, List.mem_append, List.mem_cons]
  tauto

theorem mem_limbsY :
    AirLeg.limbs ⟨limbCols Y_BASE, SB, rangeTidW SB⟩ ∈ (programAir pl prog).legs := by
  simp only [programAir, List.mem_append, List.mem_cons]
  tauto

theorem mem_limbsZ :
    AirLeg.limbs ⟨limbCols Z_BASE, SB, rangeTidW SB⟩ ∈ (programAir pl prog).legs := by
  simp only [programAir, List.mem_append, List.mem_cons]
  tauto

theorem mem_limbsQ :
    AirLeg.limbs ⟨limbCols ALU_Q_BASE, SB, rangeTidW SB⟩ ∈ (programAir pl prog).legs := by
  simp only [programAir, List.mem_append, List.mem_cons]
  tauto

theorem mem_limbsCarry :
    AirLeg.limbs ⟨aluCarryCols, CB, rangeTidW CB⟩ ∈ (programAir pl prog).legs := by
  simp only [programAir, List.mem_append, List.mem_cons]
  tauto

theorem mem_limbsAc :
    AirLeg.limbs ⟨[ALU_AC_COL], CBITS, rangeTidW CBITS⟩ ∈ (programAir pl prog).legs := by
  simp only [programAir, List.mem_append, List.mem_cons]
  tauto

theorem mem_limbsAcar :
    AirLeg.limbs ⟨aluAcarCols, ACB, rangeTidW SB⟩ ∈ (programAir pl prog).legs := by
  simp only [programAir, List.mem_append, List.mem_cons]
  tauto

/-- ⚑⚑ **THE CANONICITY CERTIFICATE'S GATE at index `m` IS A LEG OF THE MACHINE.** -/
theorem mem_zCanonGate {m : Nat} (hm : m < NA) :
    AirLeg.gate ⟨zCanonExpr pl m, Expr.const 0⟩ ∈ (programAir pl prog).legs := by
  have h : AirLeg.gate ⟨zCanonExpr pl m, Expr.const 0⟩ ∈ zCanonLegs pl :=
    List.mem_map_of_mem (List.mem_range.mpr hm)
  simp only [programAir, List.mem_append]
  tauto

/-- …and the complement block's range leg. -/
theorem mem_limbsZCan :
    AirLeg.limbs ⟨limbCols ZCAN_BASE, SB, rangeTidW SB⟩ ∈ (programAir pl prog).legs := by
  simp only [programAir, List.mem_append, List.mem_cons]
  tauto

/-- …and its carry chain's. -/
theorem mem_limbsZCCar :
    AirLeg.limbs ⟨zcCarryCols, ACB, rangeTidW SB⟩ ∈ (programAir pl prog).legs := by
  simp only [programAir, List.mem_append, List.mem_cons]
  tauto

end Legs

/-! ## §5 — ⚑ THE BODIES, AS THE PER-ROW LEMMAS WANT THEM.

`AirLeg.forces` gives `≡ 0 [ZMOD PMOD]`; the forcing lemmas take `P ∣ body`. `PMOD = P` by `rfl`,
so the two are the same statement — this section is where that is said once. -/

/-- A `gate` leg against `Expr.const 0`, forced, IS `P ∣ body`. -/
theorem dvd_of_gate_forces {tf : TraceFamily} {env : VmRowEnv} {isFirst : Bool} {e : Expr}
    (h : (AirLeg.gate ⟨e, Expr.const 0⟩).forces tf env isFirst false) :
    P ∣ e.eval env.loc := by
  have h' := h rfl
  simp only [Expr.eval] at h'
  have hd := Int.ModEq.dvd (Int.ModEq.symm h')
  simpa using hd

/-- A `.transition` `window` leg, forced, IS `P ∣ body`. -/
theorem dvd_of_window_forces {tf : TraceFamily} {env : VmRowEnv} {isFirst : Bool}
    {w : WindowExpr}
    (h : (AirLeg.window ⟨Dregg2.Circuit.TableAirIR.RowSel.transition, w⟩).forces
          tf env isFirst false) :
    P ∣ w.eval env := by
  have h' := h rfl
  have hd := Int.ModEq.dvd (Int.ModEq.symm h')
  simpa using hd

/-- A `.first` `window` leg, forced on the first row, IS `P ∣ body`. -/
theorem dvd_of_first_window_forces {tf : TraceFamily} {env : VmRowEnv} {w : WindowExpr}
    (h : (AirLeg.window ⟨Dregg2.Circuit.TableAirIR.RowSel.first, w⟩).forces tf env true false) :
    P ∣ w.eval env := by
  have h' := h rfl
  have hd := Int.ModEq.dvd (Int.ModEq.symm h')
  simpa using hd

/-- ⚑ The register window's rendered body IS `regBody`. Stated so §8 reasons about the EMITTED
`WindowExpr` and not about a re-transcription of it. -/
theorem regWindowExpr_eval (env : VmRowEnv) (r i : Nat) :
    (regWindowExpr r i).eval env = regBody env.loc env.nxt r i := by
  simp only [regWindowExpr, regBody, Dregg2.Circuit.GateExpr.render,
    Dregg2.Circuit.GateExpr.toWindow, Dregg2.Circuit.GateExpr.gEsub,
    Dregg2.Circuit.GateExpr.gNeg, Dregg2.Circuit.GateExpr.gMux,
    Dregg2.Circuit.GateExpr.WLeaf.expr, WindowExpr.eval]
  ring

/-- …and the `pc` thread's IS `pcBody`. -/
theorem pcThreadExpr_eval (env : VmRowEnv) :
    pcThreadExpr.eval env = pcBody env.loc env.nxt := by
  simp only [pcThreadExpr, pcBody, WindowExpr.eval]
  ring

/-- …and the `pc` start's is the first row's counter. -/
theorem pcStartExpr_eval (env : VmRowEnv) : pcStartExpr.eval env = env.loc PC_COL := rfl

/-! ## §6 — ⚑⚑ THE ROM ROW, AND THE CELLS IT PINS.

This is where the `hsel` hypotheses come from. Membership plus the manifest's injective key is a
POINTWISE identification (`PastaMsmBound.row_tuple_is_its_manifest_row`'s argument, at this
manifest), and tuple membership in an `exactPublicRows` table is list EQUALITY — so the cells are
pinned over ℤ and not merely mod `P`. -/

/-- Two `List.range`-indexed maps that are equal agree pointwise. -/
theorem map_range_ext {α : Type} {n : Nat} {f g : Nat → α}
    (h : (List.range n).map f = (List.range n).map g) (i : Nat) (hi : i < n) : f i = g i := by
  have h1 : ((List.range n).map f)[i]? = ((List.range n).map g)[i]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_range hi] at h1
  simpa using h1

/-- Four appended blocks of known lengths split four ways. The manifest row and the queried tuple
are both `xsel ++ ysel ++ wsel ++ imm` after the five scalar cells, and this is what turns their
equality into the four block equalities. -/
theorem append4_inj {α : Type} {a1 a2 a3 a4 b1 b2 b3 b4 : List α}
    (h : a1 ++ a2 ++ a3 ++ a4 = b1 ++ b2 ++ b3 ++ b4)
    (h1 : a1.length = b1.length) (h2 : a2.length = b2.length) (h3 : a3.length = b3.length) :
    a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 := by
  have e12 : (a1 ++ a2).length = (b1 ++ b2).length := by simp [h1, h2]
  have e123 : (a1 ++ a2 ++ a3).length = (b1 ++ b2 ++ b3).length := by simp [h1, h2, h3]
  obtain ⟨h123, h4⟩ := List.append_inj h e123
  obtain ⟨h12, hr3⟩ := List.append_inj h123 e12
  obtain ⟨hr1, hr2⟩ := List.append_inj h12 h1
  exact ⟨hr1, hr2, hr3, h4⟩

/-- The default instruction `romRows` pads with. -/
def padInstr : Instr := ⟨2, 0, NREG, NREG, 0⟩

/-- The instruction the manifest names at `pc`. -/
def instrAt (prog : List Instr) (j : Nat) : Instr := prog.getD j padInstr

/-- The queried tuple at a row. -/
def tupleAt (a : Assignment) : List ℤ := romTuple.map (fun e => e.eval a)

/-- The tuple's KEY is the row's counter, successor-shifted. -/
theorem tupleAt_head (a : Assignment) : (tupleAt a).head? = some (a PC_COL + 1) := rfl

/-- ⚑ **THE MANIFEST ROW AT `pc` IS THE INSTRUCTION AT `pc`.** -/
theorem romRows_mem_iff (prog : List Instr) {m : List Nat} (hm : m ∈ romRows prog) :
    ∃ j, j < prog.length ∧ m = romRow j (instrAt prog j) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
  exact ⟨j, List.mem_range.mp hj, rfl⟩

/-- ⚑⚑ **ROW `t`'s TUPLE IS THE MANIFEST'S ROW `t`.** Membership + the counter + key injectivity;
no counting and no pigeonhole, so `prog.length` occurs in no bound but the `< P` one that makes the
counter's congruence an equality. -/
theorem row_tuple_is_its_instruction (prog : List Instr) (a : Assignment) (tf : TraceFamily)
    (t : Nat) (hrom : RomFaithful prog tf) (hmem : tupleAt a ∈ tf ROM_TID)
    (hpc : a PC_COL ≡ (t : ℤ) [ZMOD P]) (ht : t < prog.length) (hlen : prog.length < P) :
    tupleAt a = (romRow t (instrAt prog t)).map Int.ofNat := by
  rw [hrom] at hmem
  obtain ⟨m, hmM, hmEq⟩ := List.mem_map.mp hmem
  obtain ⟨j, hj, rfl⟩ := romRows_mem_iff prog hmM
  -- the keys agree, over ℤ
  have hhead : (tupleAt a).head? = ((romRow j (instrAt prog j)).map Int.ofNat).head? := by
    rw [hmEq]
  rw [tupleAt_head, List.head?_map, romRow_head] at hhead
  have hpcj : a PC_COL = (j : ℤ) := by simpa using hhead
  -- …and a congruence between two counters below `P` is an equality
  have hjt : (j : ℤ) ≡ (t : ℤ) [ZMOD P] := by rw [← hpcj]; exact hpc
  have hjP : (j : ℤ) < P := by exact_mod_cast lt_trans (by exact_mod_cast hj) hlen
  have htP : (t : ℤ) < P := by exact_mod_cast lt_trans (by exact_mod_cast ht) hlen
  have hje : j = t := by
    have h1 : (j : ℤ) % P = (j : ℤ) := Int.emod_eq_of_lt (Int.natCast_nonneg j) hjP
    have h2 : (t : ℤ) % P = (t : ℤ) := Int.emod_eq_of_lt (Int.natCast_nonneg t) htP
    have : (j : ℤ) = (t : ℤ) := by
      have := hjt
      rw [Int.ModEq, h1, h2] at this
      exact this
    exact_mod_cast this
  subst hje
  exact hmEq.symm

/-- ⚑⚑ **THE CELLS THE MANIFEST PINS, OVER ℤ.** The four opcode selectors, the three one-hot
operand blocks and the 32 immediate limbs — every hypothesis the per-row forcing lemmas take, and
none of them an assumption about the prover. -/
theorem rom_cells (a : Assignment) (pc : Nat) (I : Instr)
    (h : tupleAt a = (romRow pc I).map Int.ofNat) :
    a SEL_MUL = (if I.op = 1 then 1 else 0)
    ∧ a SEL_ADD = (if I.op = 2 then 1 else 0)
    ∧ a SEL_SUB = (if I.op = 3 then 1 else 0)
    ∧ a SEL_CHAIN = 0
    ∧ (∀ r, r < NREG → a (XSEL_BASE + r) = (if r = I.xr then 1 else 0))
    ∧ (∀ r, r < NREG → a (YSEL_BASE + r) = (if r = I.yr then 1 else 0))
    ∧ (∀ r, r < NREG → a (WSEL_BASE + r) = (if r = I.wr then 1 else 0))
    ∧ (∀ i, i < SK → a (IMM_BASE + i) = limbAt I.imm i) := by
  -- peel the five scalar cells, then split the four blocks by their lengths
  simp only [tupleAt, romTuple, romRow, List.map_cons, List.map_append, List.map_map,
    Function.comp_def, Expr.eval, List.cons.injEq] at h
  obtain ⟨hk, hm, ha, hs, hc, hrest⟩ := h
  obtain ⟨hX, hY, hW, hI⟩ :=
    append4_inj hrest (by simp [oneHot]) (by simp [oneHot]) (by simp [oneHot])
  have hX' : (List.range NREG).map (fun r => a (XSEL_BASE + r))
      = (List.range NREG).map (fun r => ((if r = I.xr then 1 else 0 : Nat) : ℤ)) := by
    simpa [oneHot, List.map_map, Function.comp_def] using hX
  have hY' : (List.range NREG).map (fun r => a (YSEL_BASE + r))
      = (List.range NREG).map (fun r => ((if r = I.yr then 1 else 0 : Nat) : ℤ)) := by
    simpa [oneHot, List.map_map, Function.comp_def] using hY
  have hW' : (List.range NREG).map (fun r => a (WSEL_BASE + r))
      = (List.range NREG).map (fun r => ((if r = I.wr then 1 else 0 : Nat) : ℤ)) := by
    simpa [oneHot, List.map_map, Function.comp_def] using hW
  have hI' : (List.range SK).map (fun i => a (IMM_BASE + i))
      = (List.range SK).map (fun i => ((limbNat I.imm i : Nat) : ℤ)) := by
    simpa [List.map_map, Function.comp_def] using hI
  refine ⟨by simpa using hm, by simpa using ha, by simpa using hs, by simpa using hc, ?_, ?_, ?_, ?_⟩
  · intro r hr; have := map_range_ext hX' r hr; simpa using this
  · intro r hr; have := map_range_ext hY' r hr; simpa using this
  · intro r hr; have := map_range_ext hW' r hr; simpa using this
  · intro i hi; have := map_range_ext hI' i hi; simpa [limbAt, limbNat] using this

/-! ## §7 — ⚑ ONE ROW'S FORCED LEGS, IN THE VOCABULARY THE PER-ROW LEMMAS SPEAK.

`RowFacts` is a bookkeeping bundle, not new content: every field is one leg of
`(programAir pl prog).legs` read through `AirLeg.forces`, and `rowFacts_of_forced` is the reading.
Nothing here is assumed — that is what §4's membership lemmas are for. -/

/-- ⚑ Everything row `t` of a satisfying trace says. -/
structure RowFacts (pl : Nat → ℤ) (tr : RowTrace) (tf : TraceFamily) (t : Nat) : Prop where
  mul   : ∀ m, m < NG → P ∣ (aluMulExpr pl m).eval (tr t)
  add   : ∀ m, m < NA → P ∣ (aluAddSubExpr SEL_ADD pl 1 (-1) m).eval (tr t)
  sub   : ∀ m, m < NA → P ∣ (aluAddSubExpr SEL_SUB pl (-1) 1 m).eval (tr t)
  xrt   : ∀ i, i < SK → P ∣ xRouteBody (tr t) i
  yrt   : ∀ i, i < SK → P ∣ yRouteBody (tr t) i
  regw  : ∀ r, r < NREG → ∀ i, i < SK → P ∣ regBody (tr t) (tr (t + 1)) r i
  pcw   : P ∣ pcBody (tr t) (tr (t + 1))
  rom   : tupleAt (tr t) ∈ tf ROM_TID
  rx    : ∀ i, i < SK → 0 ≤ tr t (X_BASE + i) ∧ tr t (X_BASE + i) < 2 ^ SB
  ry    : ∀ i, i < SK → 0 ≤ tr t (Y_BASE + i) ∧ tr t (Y_BASE + i) < 2 ^ SB
  rz    : ∀ i, i < SK → 0 ≤ tr t (Z_BASE + i) ∧ tr t (Z_BASE + i) < 2 ^ SB
  rq    : ∀ i, i < SK → 0 ≤ tr t (ALU_Q_BASE + i) ∧ tr t (ALU_Q_BASE + i) < 2 ^ SB
  rc    : ∀ i, i < NG - 1 → 0 ≤ tr t (ALU_C_BASE + i) ∧ tr t (ALU_C_BASE + i) < 2 ^ CB
  rac   : 0 ≤ tr t ALU_AC_COL ∧ tr t ALU_AC_COL < 2
  racar : ∀ i, i < NA - 1 → 0 ≤ tr t (ALU_ACAR_BASE + i) ∧ tr t (ALU_ACAR_BASE + i) < 2 ^ ACB
  -- ⚑ the canonicity certificate: its 32 gate bodies and the ranges on its two witness blocks.
  zcan  : ∀ m, m < NA → P ∣ cnBody (tr t) Z_BASE ZCAN_BASE ZCCAR_BASE pl m
  rzcan : ∀ i, i < SK → 0 ≤ tr t (ZCAN_BASE + i) ∧ tr t (ZCAN_BASE + i) < 2 ^ SB
  rzcar : ∀ i, i < NA - 1 → 0 ≤ tr t (ZCCAR_BASE + i) ∧ tr t (ZCCAR_BASE + i) < 2 ^ ACB

/-- ⚑⚑ **A FORCED ROW IS A ROW OF FACTS.** Every field is `AirLeg.forces` of a leg the membership
lemmas of §4 exhibit in `programAir`'s own list. -/
theorem rowFacts_of_forced {pl : Nat → ℤ} {prog : List Instr} {tr : RowTrace}
    {pub chal : Assignment} {tf : TraceFamily} {n : Nat}
    (hrange : RangeTablesHonest tf) (hf : RowsForced pl prog tr pub chal tf n)
    {t : Nat} (ht : t < n) : RowFacts pl tr tf t := by
  have hrow := hf t ht
  have hloc : (rowEnv tr pub chal t).loc = tr t := rfl
  have hnxt : (rowEnv tr pub chal t).nxt = tr (t + 1) := rfl
  refine
    { mul := ?_, add := ?_, sub := ?_, xrt := ?_, yrt := ?_, regw := ?_, pcw := ?_, rom := ?_
    , rx := ?_, ry := ?_, rz := ?_, rq := ?_, rc := ?_, rac := ?_, racar := ?_
    , zcan := ?_, rzcan := ?_, rzcar := ?_ }
  · intro m hm
    have := dvd_of_gate_forces (hrow _ (mem_mulGate pl prog hm)); rwa [hloc] at this
  · intro m hm
    have := dvd_of_gate_forces (hrow _ (mem_addGate pl prog hm)); rwa [hloc] at this
  · intro m hm
    have := dvd_of_gate_forces (hrow _ (mem_subGate pl prog hm)); rwa [hloc] at this
  · intro i hi
    have := dvd_of_gate_forces (hrow _ (mem_xRoute pl prog hi))
    rwa [hloc, xRouteExpr_eval] at this
  · intro i hi
    have := dvd_of_gate_forces (hrow _ (mem_yRoute pl prog hi))
    rwa [hloc, yRouteExpr_eval] at this
  · intro r hr i hi
    have := dvd_of_window_forces (hrow _ (mem_regWindow pl prog hr hi))
    rwa [regWindowExpr_eval, hloc, hnxt] at this
  · have := dvd_of_window_forces (hrow _ (mem_pcThread pl prog))
    rwa [pcThreadExpr_eval, hloc, hnxt] at this
  · exact hrow _ (mem_romLookup pl prog)
  · intro i hi
    exact hrange.1 _ (hrow _ (mem_limbsX pl prog) _
      (List.mem_map_of_mem (List.mem_range.mpr hi)))
  · intro i hi
    exact hrange.1 _ (hrow _ (mem_limbsY pl prog) _
      (List.mem_map_of_mem (List.mem_range.mpr hi)))
  · intro i hi
    exact hrange.1 _ (hrow _ (mem_limbsZ pl prog) _
      (List.mem_map_of_mem (List.mem_range.mpr hi)))
  · intro i hi
    exact hrange.1 _ (hrow _ (mem_limbsQ pl prog) _
      (List.mem_map_of_mem (List.mem_range.mpr hi)))
  · intro i hi
    exact hrange.2.1 _ (hrow _ (mem_limbsCarry pl prog) _
      (List.mem_map_of_mem (List.mem_range.mpr hi)))
  · exact hrange.2.2 _ (hrow _ (mem_limbsAc pl prog) _ (List.mem_singleton_self _))
  · intro i hi
    exact hrange.1 _ (hrow _ (mem_limbsAcar pl prog) _
      (List.mem_map_of_mem (List.mem_range.mpr hi)))
  · intro m hm
    have h := dvd_of_gate_forces (hrow _ (mem_zCanonGate pl prog hm))
    have h2 : (zCanonExpr pl m).eval (tr t) = cnBody (tr t) Z_BASE ZCAN_BASE ZCCAR_BASE pl m :=
      cnExpr_eval (tr t) _ _ _ pl m
    rwa [hloc, h2] at h
  · intro i hi
    exact hrange.1 _ (hrow _ (mem_limbsZCan pl prog) _
      (List.mem_map_of_mem (List.mem_range.mpr hi)))
  · intro i hi
    exact hrange.1 _ (hrow _ (mem_limbsZCCar pl prog) _
      (List.mem_map_of_mem (List.mem_range.mpr hi)))

/-- ⚑⚑⚑ **THE ROW'S RESULT IS A CANONICAL FIELD ELEMENT** — `0 ≤ sVal z < N`, from the emitted
certificate's 32 gate bodies read mod `P` plus the ranges on its two witness blocks. This is the
fact §11.5 recorded as ABSENT until the certificate landed, and it is the only thing that stood
between `Tracks` as a congruence and `Tracks` as an equality.

⚑ The proof is one application: the gadget is `PastaAddSubSound` §4b's, at this row's columns, and
nothing about the bound or the telescope is re-derived here. -/
theorem z_is_canonical {N : Nat} {pl : Nat → ℤ} {tr : RowTrace} {tf : TraceFamily} {t : Nat}
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplN : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = (N : ℤ))
    (hfacts : RowFacts pl tr tf t) :
    0 ≤ sVal (tr t) Z_BASE ∧ sVal (tr t) Z_BASE < (N : ℤ) :=
  cn_gates_force_below_the_modulus (tr t) Z_BASE ZCAN_BASE ZCCAR_BASE pl (N : ℤ)
    hfacts.rz hfacts.rzcan hpl hplN hfacts.rzcar hfacts.zcan

/-- ⚑ **THE COUNTER IS THE ROW INDEX**, mod `P` — the `.first` pin plus the `.transition` thread.
This is the only induction §8's ROM identification needs, and it is `AirCrossRow.carried_constant`'s
shape at a column the leg ADVANCES rather than holds. -/
theorem pc_is_the_row_index {pl : Nat → ℤ} {prog : List Instr} {tr : RowTrace}
    {pub chal : Assignment} {tf : TraceFamily} {n : Nat}
    (hf : RowsForced pl prog tr pub chal tf n) :
    ∀ t, t < n → tr t PC_COL ≡ (t : ℤ) [ZMOD P] := by
  intro t
  induction t with
  | zero =>
      intro hn
      have hfirst : (AirLeg.window
            ⟨Dregg2.Circuit.TableAirIR.RowSel.first, pcStartExpr⟩).forces
            tf (rowEnv tr pub chal 0) true false := by
        simpa using hf 0 hn _ (mem_pcStart pl prog)
      have hd := dvd_of_first_window_forces hfirst
      rw [pcStartExpr_eval] at hd
      have : tr 0 PC_COL ≡ 0 [ZMOD P] := Int.modEq_zero_iff_dvd.mpr hd
      simpa using this
  | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hpcw : P ∣ pcBody (tr k) (tr (k + 1)) := by
        have h := dvd_of_window_forces (hf k hkn _ (mem_pcThread pl prog))
        rwa [pcThreadExpr_eval] at h
      have hstep := pc_thread_forces_successor (tr k) (tr (k + 1)) hpcw
      have h2 := hstep.trans ((ih hkn).add_right 1)
      simpa using h2

/-! ## §8 — ⚑⚑⚑ THE STEP: ONE ROW WINDOW **IS** ONE `stepRegsAt`.

This is the theorem `MinaWrapClosingAir` §b named as absent. Everything it uses is either a leg of
`programAir` (§7) or a cell of the ROM manifest (§6); the only premises are the three of §3.

⚠ Read the moduli. The COLUMN facts are mod `P`; the REGISTER FILE is tracked mod `N`. The relay
between them — `operand_x_is_the_register` and `written_register_is_the_result` — is an ℤ EQUALITY,
and it is an equality only because `x`, `y` and `z` are range-checked at every row while the
register columns are not (header, §11.2). -/

/-- Extensionality for `sVal` across two assignments and two bases. -/
theorem sVal_ext {a b : Assignment} {B B' : Nat}
    (h : ∀ i, i < SK → a (B + i) = b (B' + i)) : sVal a B = sVal b B' := by
  unfold sVal
  exact sumL_congr _ _ _ (fun i hi => by rw [h i (List.mem_range.mp hi)])

/-- A cast residue is congruent to what it reduces. -/
theorem cast_mod_modEq (N v : Nat) : ((v % N : Nat) : ℤ) ≡ (v : ℤ) [ZMOD (N : ℤ)] := by
  show ((v % N : Nat) : ℤ) % (N : ℤ) = (v : ℤ) % (N : ℤ)
  rw [Int.natCast_mod, Int.emod_emod_of_dvd _ dvd_rfl]

/-- `refMul`, `refAdd` and `refSub` are the ring operations mod `N`. `refSub`'s `+ N` needs the
subtrahend below the modulus, which is exactly `InstrOk.himm` / the register canonicality
invariant — an interpreter fact, never a trace one. -/
theorem refMul_modEq (N x y : Nat) : ((refMul N x y : Nat) : ℤ) ≡ (x : ℤ) * y [ZMOD (N : ℤ)] := by
  have h := cast_mod_modEq N (x * y)
  simpa [refMul] using h

theorem refAdd_modEq (N x y : Nat) : ((refAdd N x y : Nat) : ℤ) ≡ (x : ℤ) + y [ZMOD (N : ℤ)] := by
  have h := cast_mod_modEq N (x + y)
  simpa [refAdd] using h

theorem refSub_modEq (N x y : Nat) (hy : y ≤ N) :
    ((refSub N x y : Nat) : ℤ) ≡ (x : ℤ) - y [ZMOD (N : ℤ)] := by
  have h1 := cast_mod_modEq N (x + N - y)
  have h2 : ((x + N - y : Nat) : ℤ) = (x : ℤ) + N - y := by omega
  have h3 : (x : ℤ) + N - y ≡ (x : ℤ) - y [ZMOD (N : ℤ)] :=
    Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩)
  rw [h2] at h1
  exact (show ((refSub N x y : Nat) : ℤ) ≡ (x : ℤ) + N - y [ZMOD (N : ℤ)] from h1).trans h3

/-- ⚑⚑ **THE `x` OPERAND IS THE REGISTER THE INSTRUCTION NAMES** — as an ℤ equality of recomposed
values, because `x`'s limbs are range-checked and the routing gate pins the register's residue to
them. The `hsel` the routing lemma wants comes from the MANIFEST (§6), not from the prover. -/
theorem operand_x_is_the_register {pl : Nat → ℤ} {tr : RowTrace} {tf : TraceFamily} {t : Nat}
    (hfacts : RowFacts pl tr tf t) {r : Nat} (hr : r < NREG)
    (hsel : ∀ s, s < NREG → tr t (XSEL_BASE + s) = (if s = r then 1 else 0)) :
    sVal (tr t) X_BASE = regVal (tr t) r := by
  refine sVal_ext (fun i hi => ?_)
  have hmod := xRoute_forces_operand (tr t) i r hr hsel (hfacts.xrt i hi)
  have hc : canonRow (tr t) (X_BASE + i) = canonRow (tr t) (regCol r + i) :=
    canonRow_eq_of_modEq hmod
  obtain ⟨h0, h1⟩ := small_of_byte (hfacts.rx i hi).1 (hfacts.rx i hi).2
  rw [← canonRow_of_small h0 h1, hc]

/-- …and the `y` operand is the register OR the ROM's immediate, by the same relay. -/
theorem operand_y_is_the_register {pl : Nat → ℤ} {tr : RowTrace} {tf : TraceFamily} {t : Nat}
    (hfacts : RowFacts pl tr tf t) {r : Nat} (hr : r < NREG)
    (hsel : ∀ s, s < NREG → tr t (YSEL_BASE + s) = (if s = r then 1 else 0)) :
    sVal (tr t) Y_BASE = regVal (tr t) r := by
  refine sVal_ext (fun i hi => ?_)
  have hmod := yRoute_forces_register (tr t) i r hr hsel (hfacts.yrt i hi)
  have hc : canonRow (tr t) (Y_BASE + i) = canonRow (tr t) (regCol r + i) :=
    canonRow_eq_of_modEq hmod
  obtain ⟨h0, h1⟩ := small_of_byte (hfacts.ry i hi).1 (hfacts.ry i hi).2
  rw [← canonRow_of_small h0 h1, hc]

theorem operand_y_is_the_immediate {pl : Nat → ℤ} {tr : RowTrace} {tf : TraceFamily} {t : Nat}
    (hfacts : RowFacts pl tr tf t) {v : Nat} (hv : v < 2 ^ (SB * SK))
    (hsel : ∀ s, s < NREG → tr t (YSEL_BASE + s) = 0)
    (himm : ∀ i, i < SK → tr t (IMM_BASE + i) = limbAt v i) :
    sVal (tr t) Y_BASE = (v : ℤ) := by
  have hstep : ∀ i, i < SK → tr t (Y_BASE + i) = limbAt v i := by
    intro i hi
    have hmod := yRoute_forces_immediate (tr t) i hsel (hfacts.yrt i hi)
    have hc : canonRow (tr t) (Y_BASE + i) = canonRow (tr t) (IMM_BASE + i) :=
      canonRow_eq_of_modEq hmod
    obtain ⟨h0, h1⟩ := small_of_byte (hfacts.ry i hi).1 (hfacts.ry i hi).2
    have hib : 0 ≤ tr t (IMM_BASE + i) ∧ tr t (IMM_BASE + i) < 2 ^ SB := by
      rw [himm i hi]; exact limbAt_bounds v i
    obtain ⟨g0, g1⟩ := small_of_byte hib.1 hib.2
    rw [← canonRow_of_small h0 h1, hc, canonRow_of_small g0 g1, himm i hi]
  unfold sVal
  rw [sumL_congr _ _ (fun i => ((2 : ℤ) ^ SB) ^ i * limbAt v i)
    (fun i hi => by rw [hstep i (List.mem_range.mp hi)])]
  exact limbs_recompose_full v hv

/-- ⚑⚑ **THE WRITTEN REGISTER TAKES THE ROW'S RESULT** — the `regVal` of the NEXT row is the `sVal`
of THIS row's `z` block, over ℤ, for the same relay reason. -/
theorem written_register_is_the_result {pl : Nat → ℤ} {tr : RowTrace} {tf : TraceFamily} {t : Nat}
    (hfacts : RowFacts pl tr tf t) {r : Nat} (hr : r < NREG)
    (hw : tr t (WSEL_BASE + r) = 1) :
    regVal (tr (t + 1)) r = sVal (tr t) Z_BASE := by
  refine sVal_ext (fun i hi => ?_)
  have hmod := reg_write_forces_result (tr t) (tr (t + 1)) r i hw (hfacts.regw r hr i hi)
  have hc : canonRow (tr (t + 1)) (regCol r + i) = canonRow (tr t) (Z_BASE + i) :=
    canonRow_eq_of_modEq hmod
  obtain ⟨h0, h1⟩ := small_of_byte (hfacts.rz i hi).1 (hfacts.rz i hi).2
  rw [hc, canonRow_of_small h0 h1]

/-- …and every other register is preserved, exactly. -/
theorem held_register_is_preserved {pl : Nat → ℤ} {tr : RowTrace} {tf : TraceFamily} {t : Nat}
    (hfacts : RowFacts pl tr tf t) {r : Nat} (hr : r < NREG)
    (hw : tr t (WSEL_BASE + r) = 0) :
    regVal (tr (t + 1)) r = regVal (tr t) r := by
  refine sVal_ext (fun i hi => ?_)
  exact canonRow_eq_of_modEq
    (reg_hold_forces_preservation (tr t) (tr (t + 1)) r i hw (hfacts.regw r hr i hi))

/-- ⚑ The ALU's multiply polarity at an arbitrary modulus. `MinaWrapVerifierAir` states it at `pN`
and at `qN`; the machine's composition is modulus-general, so it is instantiated here from the same
`PastaFieldSound` core — one function, two points, no twin. -/
theorem alu_mul_forces_gen (a : Assignment) (pl : Nat → ℤ) (M : ℤ) (hsel : a SEL_MUL = 1)
    (hx : ∀ i, i < SK → 0 ≤ a (X_BASE + i) ∧ a (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (Y_BASE + i) ∧ a (Y_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (Z_BASE + i) ∧ a (Z_BASE + i) < 2 ^ SB)
    (hq : ∀ i, i < SK → 0 ≤ a (ALU_Q_BASE + i) ∧ a (ALU_Q_BASE + i) < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (hc : ∀ i, i < NG - 1 → 0 ≤ a (ALU_C_BASE + i) ∧ a (ALU_C_BASE + i) < 2 ^ CB)
    (hgates : ∀ m, m < NG → P ∣ (aluMulExpr pl m).eval a) :
    M ∣ (sVal a X_BASE * sVal a Y_BASE - sVal a Z_BASE) :=
  Dregg2.Circuit.Emit.PastaFieldSound.felt_gates_force_congruence a X_BASE Y_BASE Z_BASE
    ALU_Q_BASE ALU_C_BASE pl M hx hy hz hq hpl hplM hc
    (fun m hm => by
      have h := hgates m hm
      rw [Dregg2.Circuit.Emit.MinaWrapVerifierAir.aluMulExpr_eval, hsel, one_mul] at h
      exact h)

/-- The ALU's add/sub polarities at an arbitrary modulus. -/
theorem alu_addsub_forces_gen (a : Assignment) (pl : Nat → ℤ) (M sy sc : ℤ) (sel : Nat)
    (hsy : sy = 1 ∨ sy = -1) (hsc : sc = 1 ∨ sc = -1) (hsel : a sel = 1)
    (hx : ∀ i, i < SK → 0 ≤ a (X_BASE + i) ∧ a (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (Y_BASE + i) ∧ a (Y_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (Z_BASE + i) ∧ a (Z_BASE + i) < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (hcb : 0 ≤ a ALU_AC_COL ∧ a ALU_AC_COL < 2)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (ALU_ACAR_BASE + i) ∧ a (ALU_ACAR_BASE + i) < 2 ^ ACB)
    (hgates : ∀ m, m < NA → P ∣ (aluAddSubExpr sel pl sy sc m).eval a) :
    M ∣ (sVal a X_BASE + sy * sVal a Y_BASE - sVal a Z_BASE) :=
  Dregg2.Circuit.Emit.PastaAddSubSound.addsub_gates_force_congruence a X_BASE Y_BASE Z_BASE
    ALU_AC_COL ALU_ACAR_BASE pl sy sc M hsy hsc hx hy hz hpl hplM hcb hc
    (fun m hm => by
      have h := hgates m hm
      rw [Dregg2.Circuit.Emit.MinaWrapVerifierAir.aluAddSubExpr_eval, hsel, one_mul] at h
      exact h)

/-- The interpreter's own registers never leave `[0, N)`: every opcode reduces, and the fall-through
is `0`. This is an INTERPRETER invariant — nothing about the trace — and it is what lets `refSub`'s
`+ N` be an ℤ identity. -/
theorem opResultAt_lt (N : Nat) (hN : 0 < N) (op x y : Nat) : opResultAt N op x y < N := by
  unfold opResultAt refMul refAdd refSub
  split_ifs <;> first | exact Nat.mod_lt _ hN | exact hN

theorem stepRegsAt_canonical (N : Nat) (hN : 0 < N) (st : RegFile) (I : Instr)
    (h : ∀ r, st r < N) : ∀ r, stepRegsAt N st I r < N := by
  intro r
  unfold stepRegsAt
  split
  · exact opResultAt_lt N hN _ _ _
  · exact h r

theorem runProgAt_canonical (N : Nat) (hN : 0 < N) :
    ∀ (l : List Instr) (st : RegFile), (∀ r, st r < N) → ∀ r, runProgAt N st l r < N := by
  intro l
  induction l with
  | nil => intro st h r; exact h r
  | cons I rest ih =>
      intro st h r
      exact ih (stepRegsAt N st I) (stepRegsAt_canonical N hN st I h) r

/-- ⚑⚑⚑ **THE STEP.** A row window satisfying `programAir`'s forced legs, whose ROM row the
manifest names, carries the register file from `st` to `stepRegsAt N st I` — the interpreter's own
transition function, at the instruction the DESCRIPTOR put at that program counter.

This is the theorem `MinaWrapClosingAir` §b said nothing in the tree had: *"no theorem assembles
them into 'row `k+1`'s register file is `stepRegsAt` of row `k`'s'."* -/
theorem step_of_row {N : Nat} {pl : Nat → ℤ} {prog : List Instr} {tr : RowTrace}
    {tf : TraceFamily} {t : Nat} {st : RegFile}
    (hN : 0 < N) (hNle : N ≤ 2 ^ (SB * SK))
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplN : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = (N : ℤ))
    (hfacts : RowFacts pl tr tf t)
    (hrom : RomFaithful prog tf) (hpc : tr t PC_COL ≡ (t : ℤ) [ZMOD P])
    (ht : t < prog.length) (hlen : prog.length < P)
    (hI : InstrOk N (instrAt prog t))
    (hcanon : ∀ r, st r < N) (htr : Tracks (tr t) st) :
    Tracks (tr (t + 1)) (stepRegsAt N st (instrAt prog t)) := by
  obtain ⟨hsm, hsa, hss, _hsc, hXs, hYs, hWs, hIm⟩ :=
    rom_cells (tr t) t (instrAt prog t)
      (row_tuple_is_its_instruction prog (tr t) tf t hrom hfacts.rom hpc ht hlen)
  set I := instrAt prog t with hIdef
  -- ⚑ the `x` operand, as a value mod `N`
  have hxmod : sVal (tr t) X_BASE ≡ ((st I.xr : Nat) : ℤ) [ZMOD (N : ℤ)] := by
    rw [operand_x_is_the_register hfacts hI.hxr hXs, htr I.xr hI.hxr]
  -- ⚑ the `y` operand — the register the instruction names, or the ROM's own constant
  have hyv : sVal (tr t) Y_BASE ≡ ((yValue st I : Nat) : ℤ) [ZMOD (N : ℤ)]
      ∧ yValue st I < N := by
    by_cases hyr : I.yr = NREG
    · have hsel0 : ∀ s, s < NREG → tr t (YSEL_BASE + s) = 0 := by
        intro s hs
        have hne : s ≠ I.yr := by rw [hyr]; omega
        rw [hYs s hs, if_neg hne]
      have heq : sVal (tr t) Y_BASE = ((I.imm : Nat) : ℤ) :=
        operand_y_is_the_immediate hfacts (lt_of_lt_of_le hI.himm hNle) hsel0 hIm
      refine ⟨?_, ?_⟩
      · rw [heq]; simp [yValue, hyr]
      · have : yValue st I = I.imm := by simp [yValue, hyr]
        rw [this]; exact hI.himm
    · have hyrlt : I.yr < NREG := lt_of_le_of_ne hI.hyr hyr
      have heq : sVal (tr t) Y_BASE = regVal (tr t) I.yr :=
        operand_y_is_the_register hfacts hyrlt hYs
      have hyval : yValue st I = st I.yr := by simp [yValue, hyr]
      refine ⟨?_, ?_⟩
      · rw [heq, hyval, htr I.yr hyrlt]
      · rw [hyval]; exact hcanon I.yr
  -- ⚑ the RESULT the row's `z` block carries, mod `N`
  have hzmod : sVal (tr t) Z_BASE
      ≡ ((opResultAt N I.op (st I.xr) (yValue st I) : Nat) : ℤ) [ZMOD (N : ℤ)] := by
    rcases hI.hop with hop | hop | hop
    · have hsel : tr t SEL_MUL = 1 := by rw [hsm, if_pos hop]
      have hd := alu_mul_forces_gen (tr t) pl (N : ℤ) hsel hfacts.rx hfacts.ry hfacts.rz
        hfacts.rq hpl hplN hfacts.rc hfacts.mul
      have h1 : sVal (tr t) Z_BASE ≡ sVal (tr t) X_BASE * sVal (tr t) Y_BASE [ZMOD (N : ℤ)] :=
        Int.modEq_iff_dvd.mpr hd
      have h2 := h1.trans (hxmod.mul hyv.1)
      have h3 := h2.trans (refMul_modEq N (st I.xr) (yValue st I)).symm
      simpa [opResultAt, hop] using h3
    · have hsel : tr t SEL_ADD = 1 := by rw [hsa, if_pos hop]
      have hd := alu_addsub_forces_gen (tr t) pl (N : ℤ) 1 (-1) SEL_ADD (Or.inl rfl) (Or.inr rfl)
        hsel hfacts.rx hfacts.ry hfacts.rz hpl hplN hfacts.rac hfacts.racar hfacts.add
      have h1 : sVal (tr t) Z_BASE ≡ sVal (tr t) X_BASE + sVal (tr t) Y_BASE [ZMOD (N : ℤ)] :=
        Int.modEq_iff_dvd.mpr (by simpa using hd)
      have h2 := h1.trans (hxmod.add hyv.1)
      have h3 := h2.trans (refAdd_modEq N (st I.xr) (yValue st I)).symm
      have hop1 : I.op ≠ 1 := by omega
      simpa [opResultAt, hop, hop1] using h3
    · have hsel : tr t SEL_SUB = 1 := by rw [hss, if_pos hop]
      have hd := alu_addsub_forces_gen (tr t) pl (N : ℤ) (-1) 1 SEL_SUB (Or.inr rfl) (Or.inl rfl)
        hsel hfacts.rx hfacts.ry hfacts.rz hpl hplN hfacts.rac hfacts.racar hfacts.sub
      have hd' : (N : ℤ) ∣ (sVal (tr t) X_BASE - sVal (tr t) Y_BASE) - sVal (tr t) Z_BASE := by
        have hring : sVal (tr t) X_BASE + (-1) * sVal (tr t) Y_BASE - sVal (tr t) Z_BASE
            = (sVal (tr t) X_BASE - sVal (tr t) Y_BASE) - sVal (tr t) Z_BASE := by ring
        rwa [hring] at hd
      have h1 : sVal (tr t) Z_BASE ≡ sVal (tr t) X_BASE - sVal (tr t) Y_BASE [ZMOD (N : ℤ)] :=
        Int.modEq_iff_dvd.mpr hd'
      have h2 := h1.trans (hxmod.sub hyv.1)
      have h3 := h2.trans (refSub_modEq N (st I.xr) (yValue st I) (le_of_lt hyv.2)).symm
      have hop1 : I.op ≠ 1 := by omega
      have hop2 : I.op ≠ 2 := by omega
      simpa [opResultAt, hop, hop1, hop2] using h3
  -- ⚑⚑ THE UPGRADE: `hzmod` is a congruence; the certificate makes both sides canonical, and two
  -- values in `[0, N)` that agree mod `N` are EQUAL. This is where the mod-`N` ceiling lifted.
  have hzeq : sVal (tr t) Z_BASE
      = ((opResultAt N I.op (st I.xr) (yValue st I) : Nat) : ℤ) := by
    obtain ⟨hz0, hz1⟩ := z_is_canonical hpl hplN hfacts
    refine eq_of_modEq_of_lt hz0 hz1 (Int.natCast_nonneg _) ?_ hzmod
    exact_mod_cast opResultAt_lt N hN I.op (st I.xr) (yValue st I)
  -- ⚑ and the register file's evolution, with no third option
  intro r hr
  by_cases hrw : r = I.wr
  · have hw : tr t (WSEL_BASE + r) = 1 := by rw [hWs r hr, if_pos hrw]
    have hwlt : I.wr < NREG := by omega
    have hstep : stepRegsAt N st I r = opResultAt N I.op (st I.xr) (yValue st I) := by
      unfold stepRegsAt; rw [if_pos ⟨hwlt, hrw⟩]
    rw [written_register_is_the_result hfacts hr hw, hstep]
    exact hzeq
  · have hw : tr t (WSEL_BASE + r) = 0 := by rw [hWs r hr, if_neg hrw]
    have hne : ¬ (I.wr < NREG ∧ r = I.wr) := fun hcon => hrw hcon.2
    have hstep : stepRegsAt N st I r = st r := by
      unfold stepRegsAt; rw [if_neg hne]
    rw [held_register_is_preserved hfacts hr hw, hstep]
    exact htr r hr

/-- `take (t+1)` is `take t` with the instruction the manifest names at `t` appended. -/
theorem instrAt_eq_getElem (prog : List Instr) (t : Nat) (ht : t < prog.length) :
    instrAt prog t = prog[t] := by
  simp [instrAt, List.getD, List.getElem?_eq_getElem ht]

theorem take_succ_eq (prog : List Instr) (t : Nat) (ht : t < prog.length) :
    prog.take (t + 1) = prog.take t ++ [instrAt prog t] := by
  rw [List.take_add_one, instrAt_eq_getElem prog t ht, List.getElem?_eq_getElem ht]
  rfl

/-! ## §9 — ⚑⚑⚑ THE COMPOSITION OVER THE ROWS. -/

/-- ⚑⚑⚑ **A TRACE SATISFYING `programAir`'s FORCED LEGS RUNS THE PROGRAM.** At every row `t ≤ n`,
the register file the trace presents IS `runProgAt N st₀` of the descriptor's first `t`
instructions — mod the Pasta modulus, the resolution the ALU's own conclusion has.

⚠ Row `n`'s legs are NOT required (`RowsForced … n` quantifies over `t < n`), which is exactly what
makes §11.3 the boundary it is: the trace must have a row `n` for instruction `n−1`'s write to
land. -/
theorem rows_track_the_interpreter {N : Nat} {pl : Nat → ℤ} {prog : List Instr} {tr : RowTrace}
    {pub chal : Assignment} {tf : TraceFamily} {n : Nat} {st0 : RegFile}
    (hN : 0 < N) (hNle : N ≤ 2 ^ (SB * SK))
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplN : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = (N : ℤ))
    (hok : ∀ I ∈ prog, InstrOk N I) (hlen : prog.length < P) (hn : n ≤ prog.length)
    (hrange : RangeTablesHonest tf) (hrom : RomFaithful prog tf)
    (hf : RowsForced pl prog tr pub chal tf n)
    (hcanon : ∀ r, st0 r < N) (h0 : Tracks (tr 0) st0) :
    ∀ t, t ≤ n → Tracks (tr t) (runProgAt N st0 (prog.take t)) := by
  intro t
  induction t with
  | zero => intro _; exact h0
  | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hkl : k < prog.length := by omega
      have hIok : InstrOk N (instrAt prog k) := by
        rw [instrAt_eq_getElem prog k hkl]
        exact hok _ (List.getElem_mem hkl)
      have hrun : runProgAt N st0 (prog.take (k + 1))
          = stepRegsAt N (runProgAt N st0 (prog.take k)) (instrAt prog k) := by
        rw [take_succ_eq prog k hkl, runProgAt_append]
        rfl
      rw [hrun]
      exact step_of_row hN hNle hpl hplN (rowFacts_of_forced hrange hf hkn) hrom
        (pc_is_the_row_index hf k hkn) hkl hlen hIok
        (runProgAt_canonical N hN _ st0 hcanon) (ih (by omega))

/-- ⚑⚑⚑ **AT THE END OF THE PROGRAM.** The `n = prog.length` instance: the trace's row
`prog.length` presents `runProgAt N st₀ prog`. -/
theorem runs_the_program {N : Nat} {pl : Nat → ℤ} {prog : List Instr} {tr : RowTrace}
    {pub chal : Assignment} {tf : TraceFamily} {st0 : RegFile}
    (hN : 0 < N) (hNle : N ≤ 2 ^ (SB * SK))
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplN : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = (N : ℤ))
    (hok : ∀ I ∈ prog, InstrOk N I) (hlen : prog.length < P)
    (hrange : RangeTablesHonest tf) (hrom : RomFaithful prog tf)
    (hf : RowsForced pl prog tr pub chal tf prog.length)
    (hcanon : ∀ r, st0 r < N) (h0 : Tracks (tr 0) st0) :
    Tracks (tr prog.length) (runProgAt N st0 prog) := by
  have h := rows_track_the_interpreter hN hNle hpl hplN hok hlen (le_refl _) hrange hrom hf
    hcanon h0 prog.length (le_refl _)
  simpa using h

/-! ### §9a — ⚑⚑ THE DEPLOYED DESCRIPTOR SUPPLIES `RowsForced`.

The seven transcript descriptors' air is `programAir` **with a boundary appended** —
`{ programAir pl prog with legs := (programAir pl prog).legs ++ pins }` — so their
`CertifiedRefines` hands back `forces` for a SUPERSET of the machine's legs. One `mem_append_left`
is the whole bridge, and it is stated here so a caller never has to re-derive it. -/

/-- ⚑⚑ **A TRACE SATISFYING THE EMITTED CONSTRAINTS FORCES THE MACHINE'S LEGS.** -/
theorem rowsForced_of_certified {pl : Nat → ℤ} {prog : List Instr} {tr : RowTrace}
    {pub chal : Assignment} {tf : TraceFamily} {n : Nat} {pins : List AirLeg}
    {d : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2}
    {cs : Dregg2.Circuit.ConstraintSystem} {hash : List ℤ → ℤ}
    (hcert : Dregg2.Circuit.Emit.EffectLower.CertifiedRefines d cs
        { programAir pl prog with legs := (programAir pl prog).legs ++ pins })
    (hsat : ∀ t, t < n → ∀ vc ∈ d.constraints,
        vc.holdsAt hash tf (rowEnv tr pub chal t) (t == 0) false) :
    RowsForced pl prog tr pub chal tf n := fun t ht l hl =>
  (hcert hash tf (rowEnv tr pub chal t) (t == 0) false (hsat t ht)).1 l
    (List.mem_append_left _ hl)

/-- A `VmTrace`'s rows, as the row-indexed family this file reasons about. `envAt` and `rowEnv`
agree on it by `rfl` — the two are the same window. -/
def rowsOf (t : Dregg2.Circuit.DescriptorIR2.VmTrace) : RowTrace :=
  fun j => t.rows.getD j Dregg2.Circuit.DescriptorIR2.zeroAsg

theorem envAt_is_rowEnv (t : Dregg2.Circuit.DescriptorIR2.VmTrace) (i : Nat) :
    Dregg2.Circuit.DescriptorIR2.envAt t i = rowEnv (rowsOf t) t.pub t.chal i := rfl

/-- ⚑⚑⚑ **AND THE DEPLOYED DENOTATION SUPPLIES IT.** `Satisfied2.rowConstraints` quantifies
`c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)`; on any row that has a
successor the last flag is `false`, and that is exactly `RowsForced`. So `rows_track_the_interpreter`
applies to a trace satisfying the EMITTED DESCRIPTOR, not to a hand-rolled hypothesis.

⚠ `hn : n + 1 ≤ t.rows.length` is §11.3 written as a hypothesis rather than a caveat: the
composition reaches exactly the rows a successor exists for. -/
theorem rowsForced_of_satisfied2 {pl : Nat → ℤ} {prog : List Instr} {n : Nat}
    {pins : List AirLeg} {d : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2}
    {cs : Dregg2.Circuit.ConstraintSystem} {hash : List ℤ → ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hcert : Dregg2.Circuit.Emit.EffectLower.CertifiedRefines d cs
        { programAir pl prog with legs := (programAir pl prog).legs ++ pins })
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash d minit mfin maddrs t)
    (hn : n + 1 ≤ t.rows.length) :
    RowsForced pl prog (rowsOf t) t.pub t.chal t.tf n := by
  intro k hk l hl
  have hklen : k < t.rows.length := by omega
  have hlast : (k + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    omega
  have hrows := hsat.rowConstraints k hklen
  have hforced := (hcert hash t.tf (Dregg2.Circuit.DescriptorIR2.envAt t k) (k == 0)
    (k + 1 == t.rows.length) hrows).1 l (List.mem_append_left _ hl)
  rw [hlast, envAt_is_rowEnv] at hforced
  exact hforced

/-! ## §10 — ⚑⚑ WHAT IT CLOSES, SAID EXACTLY.

`MinaWrapVerifierSpongeFp.the_absorb_program_permutes_gen` is a statement about `runProgAt`. §9 is
a statement about the emitted legs. Their composition is a statement about the EMITTED CONSTRAINTS
reaching `PastaPoseidonFq.Core.perm` — the sentence `MinaWrapClosingAir` §b said the tree could not
make.

⚠ The obligation `∀ I ∈ absorbCoreP Pm, InstrOk Pm.modulus I` is DESCRIPTOR data — the program is
the descriptor's own ROM manifest, not the prover's — and it is discharged for the deployed shape
by `absorbCoreP_instrOk` below from two bounds on the parameter set. -/

/-- The register a round's lane `i` lands in is a register. -/
theorem allocAt_lt (r i : Nat) : allocAt r i < NREG := Nat.mod_lt _ (by decide)

/-- Every instruction of an S-box block is well-formed. -/
theorem sboxInstrs_instrOk (N a d : Nat) (hN : 0 < N) (ha : a < NREG) (hd : d < NREG) :
    ∀ I ∈ sboxInstrs a d, InstrOk N I := by
  intro I hI
  have hNR : NREG = 6 := rfl
  simp only [sboxInstrs, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl
  · exact { hop := Or.inl rfl, hxr := ha, hyr := le_of_lt ha, himm := hN }
  · exact { hop := Or.inl rfl, hxr := ha, hyr := le_of_lt hd, himm := hN }
  · exact { hop := Or.inl rfl, hxr := hd, hyr := le_of_lt hd, himm := hN }
  · exact { hop := Or.inl rfl, hxr := ha, hyr := le_of_lt hd, himm := hN }

/-- …and of an MDS row, given its three coefficients and its round constant are canonical. -/
theorem mdsRowInstrs_instrOk (N a b c d out m0 m1 m2 rc : Nat) (hN : 0 < N)
    (ha : a < NREG) (hb : b < NREG) (hc : c < NREG) (hd : d < NREG) (hout : out < NREG)
    (h0 : m0 < N) (h1 : m1 < N) (h2 : m2 < N) (hrc : rc < N) :
    ∀ I ∈ mdsRowInstrs a b c d out m0 m1 m2 rc, InstrOk N I := by
  intro I hI
  simp only [mdsRowInstrs, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl | rfl | rfl
  · exact { hop := Or.inl rfl, hxr := ha, hyr := le_refl _, himm := h0 }
  · exact { hop := Or.inl rfl, hxr := hb, hyr := le_refl _, himm := h1 }
  · exact { hop := Or.inr (Or.inl rfl), hxr := hout, hyr := le_of_lt hd, himm := hN }
  · exact { hop := Or.inl rfl, hxr := hc, hyr := le_refl _, himm := h2 }
  · exact { hop := Or.inr (Or.inl rfl), hxr := hout, hyr := le_of_lt hd, himm := hN }
  · exact { hop := Or.inr (Or.inl rfl), hxr := hout, hyr := le_refl _, himm := hrc }

/-- ⚑ **THE PARAMETER SET'S CONSTANTS ARE CANONICAL.** A condition on the DESCRIPTOR's numbers —
`fp_kimchi`'s and `fq_kimchi`'s own MDS matrix and round constants — checkable by the emitter, and
never a condition on a witness. -/
def ParamsCanonical (Pm : Params) : Prop :=
  (∀ i j, Dregg2.Circuit.Emit.PastaPoseidonFq.Core.mc Pm i j < Pm.modulus)
  ∧ (∀ r i, rcOf Pm r i < Pm.modulus)

/-- ⚑ **THE ABSORB PROGRAM IS WELL-FORMED**, at any canonical parameter set — the S-box blocks by
construction and the MDS rows from the two bounds. -/
theorem absorbCoreP_instrOk (Pm : Params) (hP : 0 < Pm.modulus) (hc : ParamsCanonical Pm) :
    ∀ I ∈ absorbCoreP Pm, InstrOk Pm.modulus I := by
  intro I hI
  have hNR : NREG = 6 := rfl
  rcases List.mem_append.mp hI with h | h
  · simp only [Dregg2.Circuit.Emit.MinaWrapVerifierSponge.absorbInstrs, List.mem_cons,
      List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact { hop := Or.inr (Or.inl rfl), hxr := by decide, hyr := by decide, himm := hP }
    · exact { hop := Or.inr (Or.inl rfl), hxr := by decide, hyr := by decide, himm := hP }
  · -- the rounds
    have hround : ∀ r, ∀ J ∈ Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.roundAtP Pm r,
        InstrOk Pm.modulus J := by
      intro r J hJ
      simp only [Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.roundAtP,
        Dregg2.Circuit.Emit.MinaWrapVerifierSponge.roundInstrs, List.mem_append] at hJ
      rcases hJ with ((((h1 | h2) | h3) | h4) | h5) | h6
      · exact sboxInstrs_instrOk _ _ _ hP (allocAt_lt _ _) (allocAt_lt _ _) _ h1
      · exact sboxInstrs_instrOk _ _ _ hP (allocAt_lt _ _) (allocAt_lt _ _) _ h2
      · exact sboxInstrs_instrOk _ _ _ hP (allocAt_lt _ _) (allocAt_lt _ _) _ h3
      · exact mdsRowInstrs_instrOk _ _ _ _ _ _ _ _ _ _ hP (allocAt_lt _ _) (allocAt_lt _ _)
          (allocAt_lt _ _) (allocAt_lt _ _) (allocAt_lt _ _) (hc.1 _ _) (hc.1 _ _) (hc.1 _ _)
          (hc.2 _ _) _ h4
      · exact mdsRowInstrs_instrOk _ _ _ _ _ _ _ _ _ _ hP (allocAt_lt _ _) (allocAt_lt _ _)
          (allocAt_lt _ _) (allocAt_lt _ _) (allocAt_lt _ _) (hc.1 _ _) (hc.1 _ _) (hc.1 _ _)
          (hc.2 _ _) _ h5
      · exact mdsRowInstrs_instrOk _ _ _ _ _ _ _ _ _ _ hP (allocAt_lt _ _) (allocAt_lt _ _)
          (allocAt_lt _ _) (allocAt_lt _ _) (allocAt_lt _ _) (hc.1 _ _) (hc.1 _ _) (hc.1 _ _)
          (hc.2 _ _) _ h6
    -- …and the permutation is the concatenation of the rounds
    have hperm : ∀ k, ∀ J ∈ Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.permInstrsUpToP Pm k,
        InstrOk Pm.modulus J := by
      intro k J hJ
      rw [Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.permInstrsUpToP] at hJ
      obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp hJ
      exact hround r J hr
    exact hperm _ _ h

/-- ⚑⚑⚑ **THE EMITTED CONSTRAINTS FORCE THE POSEIDON PERMUTATION.**
`the_absorb_program_permutes_gen` was a statement about `runProgAt`; composed with §9 it becomes a
statement about the rows a satisfying trace presents. The three lanes are read at the registers the
round schedule lands them in, mod the parameter set's own modulus. -/
theorem absorb_rows_force_the_permutation {Pm : Params} {pl : Nat → ℤ} {tr : RowTrace}
    {pub chal : Assignment} {tf : TraceFamily} {st0 : RegFile}
    (hP : 0 < Pm.modulus) (hPle : Pm.modulus ≤ 2 ^ (SB * SK)) (hpc : ParamsCanonical Pm)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplN : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = (Pm.modulus : ℤ))
    (hlen : ((absorbCoreP Pm).length : ℤ) < P)
    (hrange : RangeTablesHonest tf) (hrom : RomFaithful (absorbCoreP Pm) tf)
    (hf : RowsForced pl (absorbCoreP Pm) tr pub chal tf (absorbCoreP Pm).length)
    (hcanon : ∀ r, st0 r < Pm.modulus) (h0 : Tracks (tr 0) st0) :
    ∀ i, i < 3 →
      regVal (tr (absorbCoreP Pm).length) (allocAt PastaPoseidon.rounds i)
        = (((Dregg2.Circuit.Emit.PastaPoseidonFq.Core.perm Pm
              [(st0 0 + st0 3) % Pm.modulus, (st0 1 + st0 4) % Pm.modulus, st0 2]).getD i 0 : Nat)
            : ℤ) := by
  have hrun := runs_the_program (N := Pm.modulus) (pl := pl) (prog := absorbCoreP Pm)
    (tr := tr) (pub := pub) (chal := chal) (tf := tf) (st0 := st0)
    hP hPle hpl hplN (absorbCoreP_instrOk Pm hP hpc) hlen hrange hrom hf hcanon h0
  have hgen := the_absorb_program_permutes_gen Pm hP st0
  intro i hi
  have hreg := hrun (allocAt PastaPoseidon.rounds i) (allocAt_lt _ _)
  have hlane : (Dregg2.Circuit.Emit.PastaPoseidonFq.Core.perm Pm
      [(st0 0 + st0 3) % Pm.modulus, (st0 1 + st0 4) % Pm.modulus, st0 2]).getD i 0
      = runProgAt Pm.modulus st0 (absorbCoreP Pm) (allocAt PastaPoseidon.rounds i) := by
    rw [← hgen]
    interval_cases i <;> rfl
  rw [hlane]
  exact hreg

/-! ## §11 — ⚠ WHAT IS STILL STANDING.

1. **`RangeTablesHonest`** — the same premise `AirCrossRow.PoolsRanged` is, and for the same
   reason: a `limbs` leg's `forces` is MEMBERSHIP in the trace family, and the numeric bound is the
   LogUp argument's own meaning, one rail below any leg. It is not selector plumbing and it is not
   discharged here. ⚑ It is now stated ONCE for a whole descriptor's tables rather than per column
   pool, which is the `RangeTablesHonest tf → PoolsRanged tr` shape `AirSelectorForcing`'s header
   asked for; wiring `AirCrossRow` onto it is a separate, mechanical pass.

2. **The register file carries no range leg.** `programAir` range-checks `x`, `y`, `z`, the
   quotient, the two carry pools and now the certificate's two blocks — and NOT `regCol r + i`.
   This file does not need it (the header's canonicality relay), but the fact is worth stating on
   its own: the ONLY thing forced about a register column is its residue mod `P`, and any future
   consumer that reads `sVal (tr t) (regCol r)` instead of `regVal (tr t) r` is reading integers the
   descriptor does not pin. ⚠ `register_column_is_not_ranged` now carries `r < NREG` and `i < SK`
   and is stated over `machineRangedCols`; without those hypotheses it is FALSE, because
   `regCol 7 + 21 = 471` lands inside the certificate's complement block.

3. **The last row's transition legs do not fire.** `transition_legs_are_vacuous_on_the_last_row` is
   that as a theorem. So `rows_track_the_interpreter` covers instructions `0 … n−1` where the trace
   has a row `n`; the deployed traces reach a power-of-two height by padding
   (`MinaWrapVerifierProgram.padInstr`), so the instruction whose result is read is never the last
   row — but a caller who forgets that is reading an unforced write.

4. **`Tracks` at row 0 is a premise, and it is now a STRICTLY STRONGER one.** `programAir` pins no
   register column on the first row; a boundary does (`sboxPins` and its siblings), and
   `programAir_boundary_pinsTied` is what makes adding one cost a single structural lemma.
   ⚠ Since `Tracks` became an ℤ equality the boundary owes an ℤ-exact row-0 register file — the
   limbs must be BYTES that recompose to `st0 r`, not merely a residue class. That is what the
   honest generator writes (`rowAsg` fills `regCol r + i` with `limbAt (st r) i`, each in
   `[0, 2^8) ⊆ [0, P)`, and `st0 r < N < 2^256`), so the premise is satisfiable and this rung is not
   vacuous — but a boundary that pinned residues would no longer discharge it, and that is a real
   cost of the strengthening rather than a free upgrade.

5. ✅ **CLOSED 2026-08-10 — THE MOD-`N` CEILING IS GONE, AND WHAT REPLACED IT COST 63 COLUMNS.**
   This entry read *"the mod-`N` resolution is a CEILING, not a choice — UNDONE WORK, not a theorem
   of the model"*, and it was right: no leg was a less-than-the-modulus certificate on `z`, the
   limb ranges bought only `sVal z < 2^256` against `pN ≈ 2^254.9`, and `r, r+p, r+2p, r+3p, r+4p`
   all fit with their own range-checked quotients. `programAir` now carries
   `MinaWrapVerifierProgram.zCanonLegs`; `z_is_canonical` reads it; `Tracks` is an ℤ EQUALITY.

   ⚑⚑ **What did NOT transfer is the fix SHAPE, and the reason is the whole lesson.** This entry
   named `PastaMsmScalarDerive` §2.7's certificate — `s + Σ_{p<255} 2^p·CBc p = q − 1` over 255
   boolean columns — and priced it at `+255` columns / `+256` constraints. That shape is correct in
   the model §2.7 is stated in (`PastaField.acceptB`, the ℤ reading of the emitted bodies) and
   **cannot force anything in the model THIS file is stated in.** One gate whose integer body is
   ~`2^256`, read as `P ∣ body` with `P ≈ 2^31`, leaves `2^225` satisfying assignments. Porting it
   verbatim would have restated `AirCrossRow.PhaseIndicator`'s first statement one layer up: an ℤ
   claim over legs that buy a congruence, of which no proof could have existed.

   The shape that survives the mod-`P` reading is the one add/sub already uses — a LIMB-WISE
   identity with a carry chain, every body bounded below `P` so `P ∣ body` forces `body = 0` over
   ℤ, and 32 identities that telescope. `PastaAddSubSound` §4b is it: `z + c + 1 = N` over `SK = 32`
   complement limbs and `NA − 1 = 31` carries.

   ⚑ **RE-DERIVED PRICE, not inherited: `+63` columns and `+32` gate legs (plus 2 `limbs` legs),
   against §2.7's `+255` / `+256`.** Four times cheaper AND forcing where §2.7's is not — the bit
   decomposition spends 255 columns saying "non-negative"; a range-checked byte block says it in 32.

   ⚠ **What this does NOT close, stated so it is not read as more:** `cnHonest_satisfies_gates` is a
   KAT at three values, not the general completeness theorem (*for every `zv < N` the honest carry
   chain's divisions are exact*), which is the `limbs_recompose` truncation argument and is UNDONE.
   Soundness — the direction `Tracks` at ℤ depends on — is fully general.

6. **Everything below this file's floor is untouched** — the ℤ↔felt reading (K1), the FRI/STARK
   floor, and `MinaWrapClosingAir` residuals (a) and (c). This closes (b) and nothing else. -/

/-- ⚑⚑ **A `.transition` LEG CLAIMS NOTHING ON THE LAST ROW** — for EVERY body and every trace
family, so this is the shape of the boundary and not an artefact of the machine. It is why
`RowsForced` is quantified over `t < n` and why the write of instruction `n−1` needs a row `n`. -/
theorem transition_legs_are_vacuous_on_the_last_row (tf : TraceFamily) (env : VmRowEnv)
    (isFirst : Bool) (w : WindowExpr) :
    (AirLeg.window ⟨Dregg2.Circuit.TableAirIR.RowSel.transition, w⟩).forces tf env isFirst true :=
  fun h => absurd h (by simp)

/-- ⚑ **AND THE MACHINE DECLARES NO RANGE TABLE FOR THE REGISTER FILE** — §11.2 as a fact about the
emitted leg list rather than a remark. `aluRangedCols` is EXTRACTED from `programAir`'s own legs by
the kernel, not transcribed. -/
def aluRangedCols : List Nat :=
  limbCols X_BASE ++ limbCols Y_BASE ++ limbCols Z_BASE ++ limbCols ALU_Q_BASE
    ++ aluCarryCols ++ [ALU_AC_COL] ++ aluAcarCols

/-- ⚑ The canonicity certificate's two range-checked blocks: the complement's `SK` limbs and its
`NA − 1` carries. **These are ABOVE the register file**, which is why the register-file fact below
now carries `r < NREG`. -/
def certRangedCols : List Nat := limbCols ZCAN_BASE ++ zcCarryCols

/-- Everything the machine range-checks. -/
def machineRangedCols : List Nat := aluRangedCols ++ certRangedCols

set_option maxHeartbeats 2000000 in
/-- The columns EVERY `limbs` leg of the machine names, read off the emitted leg list.
⚠ The kernel walks the whole leg list to check this, which is why the heartbeat budget is raised —
the same price `sboxTiedAir` pays for `pinsTied`.

⚠ **RENAMED from `aluRangedCols_are_the_limbs_legs_cols`, whose NAME STOPPED BEING TRUE.** The
machine now range-checks 63 columns that are not ALU columns — the certificate's complement block
and its carry chain — so the flattened `limbs`-leg column list is no longer `aluRangedCols`. Keeping
the old name over the new list would have been the quietest possible lie in this file. -/
theorem machineRangedCols_are_the_limbs_legs_cols (pl : Nat → ℤ) (prog : List Instr) :
    ((programAir pl prog).legs.filterMap
        (fun l => match l with | AirLeg.limbs q => some q.cols | _ => none)).flatten
      = machineRangedCols := rfl

/-- Every range-checked column of the ARITHMETIC block is an ALU column. Still true, and still
about `aluRangedCols` — which is now a proper sublist of what the machine ranges. -/
theorem aluRangedCols_below_alu_width : ∀ c ∈ aluRangedCols, c < ALU_WIDTH := by decide

/-- …and every certificate column is at or above `ZCAN_BASE = 469`. -/
theorem certRangedCols_above_the_certificate_base : ∀ c ∈ certRangedCols, ZCAN_BASE ≤ c := by
  decide

/-- ⚑⚑ **AND NO REGISTER COLUMN IS ONE.** The register file sits strictly between the ALU row and
the certificate block — `226 ≤ regCol r + i < 469` for `r < NREG`, `i < SK` — so it is in no
declared range table, which is why §2's `regVal` reads the register block through `· % P` and never
as an integer.

⚠ **The hypotheses `r < NREG` and `i < SK` are NEW and they are not decoration.** The old statement
quantified over ALL `r` and `i` and was true only because every ranged column was below
`ALU_WIDTH`; the certificate's blocks live at `469..531`, and `regCol 7 + 21 = 471` is inside them.
So the unhypothesised form is now FALSE, and stating it would have been the second-quietest lie. -/
theorem register_column_is_not_ranged (r i : Nat) (hr : r < NREG) (hi : i < SK) :
    regCol r + i ∉ machineRangedCols := by
  intro h
  rcases List.mem_append.mp h with h | h
  · have h1 := aluRangedCols_below_alu_width _ h
    have h2 : ALU_WIDTH ≤ regCol r + i := by
      unfold regCol REG_BASE; omega
    omega
  · have h1 := certRangedCols_above_the_certificate_base _ h
    have h2 := the_certificate_block_is_above_the_register_file r i hr hi
    omega

/-! ### §11a — ⚑ BOTH POLES: `Tracks` IS A PREDICATE, NOT A TAUTOLOGY.

An `AirLeg.forces` that said "the lowered constraints hold" would be `P → P`; a `Tracks` that said
nothing would be the same sin one layer up. It is refutable, and here is the refutation. -/

/-- The all-zero row presents the all-zero register file. -/
theorem regVal_zero (r : Nat) : regVal (fun _ => (0 : ℤ)) r = 0 := by
  simp [regVal, canonRow, sVal, sumL]

/-- ⚑⚑ **AND A ROW THAT READS `0` DOES NOT TRACK A REGISTER FILE HOLDING `1`.** -/
theorem tracks_is_refutable : ¬ Tracks (fun _ => (0 : ℤ)) (fun _ => 1) := by
  intro h
  have h0 := h 0 (by decide)
  rw [regVal_zero] at h0
  exact absurd h0 (by decide)

#assert_axioms limbs_recompose_full
#assert_axioms rom_cells
#assert_axioms row_tuple_is_its_instruction
#assert_axioms rowFacts_of_forced
#assert_axioms pc_is_the_row_index
#assert_axioms step_of_row
#assert_axioms rows_track_the_interpreter
#assert_axioms runs_the_program
#assert_axioms transition_legs_are_vacuous_on_the_last_row
#assert_axioms absorbCoreP_instrOk
#assert_axioms absorb_rows_force_the_permutation
#assert_axioms register_column_is_not_ranged
#assert_axioms machineRangedCols_are_the_limbs_legs_cols
#assert_axioms certRangedCols_above_the_certificate_base
#assert_axioms z_is_canonical
#assert_axioms eq_of_modEq_of_lt
#assert_axioms tracks_is_refutable
#assert_axioms rowsForced_of_certified
#assert_axioms rowsForced_of_satisfied2

end Dregg2.Circuit.Emit.AirProgramRows
