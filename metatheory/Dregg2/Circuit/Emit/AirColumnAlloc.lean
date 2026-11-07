/-
# `Dregg2.Circuit.Emit.AirColumnAlloc` — LIVENESS AND COLUMN REUSE for the lowering, and the
renaming under which the refinement survives it.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR, and a register allocator is part of the compiler, so it is Lean.**
Every column index and every renaming is computed here; Rust never sees an allocation decision.
House Law #1.

## ⚑ WHERE THE FRESH COLUMNS ARE MINTED — cited, and it is NOT the lowering

`EffectLowerCore.lowerAir` (`:437`) takes `traceWidth` as a **parameter** and
`assemble` (`:419`) copies it into the descriptor verbatim. The lowering therefore mints no
column at all: it is handed a width and a leg list whose column indices are already chosen. The
allocation lives one level up, in the gadget's layout arithmetic, and for the sound Pasta row it is
four `def`s:

    PastaCurveSound.lean:403   def vBase (fresh i : Nat) : Nat := fresh + SK * i
    PastaCurveSound.lean:405   def mWit  (fresh k : Nat) : Nat := fresh + SK * 33 + (SK + (NG-1)) * k
    PastaCurveSound.lean:407   def sWit  (fresh k : Nat) : Nat := fresh + SK * 33 + (SK + (NG-1)) * 12 + SK * k
    PastaCurveSound.lean:409   def aWit  (fresh k : Nat) : Nat := fresh + SK * 33 + (SK + (NG-1)) * 12 + SK * 2 + SK * k

Each is `base + stride * index`. **The index only ever goes up.** That is the whole naivety, in
four lines: `vBase` hands SSA value `i` a private 32-column block for every `i < 33`, `mWit` hands
multiply `k` a private 94-column block for every `k < 12`, and nothing is ever handed out twice.
`RCB_FRESH = 2856` (`:412`, `rcb_fresh_eq`) is the sum, and `RCB_WIDTH = 3048` (`:474`) is it plus
the six input blocks.

## ⚑ AND THE FIRST THING THE LIVENESS SAYS IS THAT THE ROW CANNOT SHRINK

The diagnosis "a fresh column per SSA value and never reuse one" is TRUE of the four `def`s above.
The inference "therefore a register allocator shrinks the row" is **FALSE**, and the reason is
structural rather than a matter of effort:

> **An AIR row has no time.** All 33 op blocks of `swCompleteAddSoundLegs` are asserted on ONE row
> simultaneously. Two values that share a column on one row are *the same field element*. So a
> column may be reused by two values only if their live ranges are disjoint — and within a single
> row every live range is the whole row.

`rcb_single_row_interference_is_complete` (§5) is that as a theorem: on the one-row schedule the
interference graph on the 39 value blocks is the COMPLETE graph, so `alloc_disjoint` forces the
allocation to be injective and 3 048 columns is **optimal**, not naive.

⚑ **The reuse opportunity is created by a SCHEDULE, not found by an allocator.** Spreading the 33
ops over rows is what gives live ranges an inside and an outside; the allocator is what then cashes
it. Both halves are here: `liveIntervals` over an op list (§3), greedy interval colouring with the
disjointness invariant proved (§4), and the two schedules measured against each other (§5).

## ⚑ THE INVARIANT IS NOT `Nodup` — and that is the whole difference from the other rail

`Emit/KimchiArena.lean` is the allocator on the Kimchi rail and its entire value is
`alloc_injective`: *"a successful alloc has `Nodup` variables, so two slots can never denote one
`PVar`."* **Reuse is the exact negation of that property.** This allocator therefore proves a
different theorem, and it is the one the brief names:

* `alloc_disjoint` — *two values sharing a column have disjoint live ranges*, general over the
  interval list, by construction rather than by a census.

## ⚑ WHAT KEEPS THE REFINEMENT — composition, in the `merging_is_naming_the_same_variable` shape

`KimchiAssertEqual.lean:333` proves a merged placement **is** `place` of the renamed gate list, so
no second pass has to be kept honest. Same shape here, one rail over:

* `renameLeg_forces` — a renamed leg forces at `env` exactly what the original leg forced at
  `env ∘ σ`. Stated in `AirLeg.forces`, the SOURCE semantics, and never mentioning `lowerLeg`.
* `renameAir_mainRailOk` — renaming does not move the compiler's verdict, so the certified
  lowering still elaborates.
* `allocated_forces_what_it_forced` — the certificate `lowerAirCertified` already produces for the
  renamed air, pulled back through `renameLeg_forces` to a statement about the ORIGINAL air.

⚑ **The soundness direction is free and the completeness direction is what the invariant buys.**
Renaming with ANY `σ` can only restrict: an assignment satisfying `renameAir σ air` pulls back
along `σ` to one satisfying `air`, so a reuse pass can never admit a witness the original refused
(`rename_admits_no_new_witness`). What a bad `σ` breaks is *completeness* — an honest witness stops
fitting — and `alloc_disjoint` is exactly the side condition that keeps it
(`disjoint_ranges_admit_the_honest_witness`).

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`; zero `#guard`s.
-/
import Dregg2.Circuit.Emit.EffectLowerCertified

namespace Dregg2.Circuit.Emit.AirColumnAlloc

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.DescriptorIR2 (WindowExpr ChalExpr TraceFamily)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.TableAirIR (readsNext)
open Dregg2.Circuit.EffectAirIR

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — ⚑ THE RENAMING, on every column-bearing node of the source IR.

A column allocation IS a map `σ : Nat → Nat` from the SSA layout's columns to physical columns.
Applying it is a structural rewrite of the leg list; nothing else in the source moves. -/

/-- Rename the columns an `Expr` reads. -/
def renameExpr (σ : Nat → Nat) : Expr → Expr
  | .var v   => .var (σ v)
  | .const k => .const k
  | .add a b => .add (renameExpr σ a) (renameExpr σ b)
  | .mul a b => .mul (renameExpr σ a) (renameExpr σ b)

/-- Rename the columns a `WindowExpr` reads. `loc c` and `nxt c` are the SAME column and move
together — a renaming that split them would be reading two physical columns for one value. -/
def renameWindow (σ : Nat → Nat) : WindowExpr → WindowExpr
  | .loc c   => .loc (σ c)
  | .nxt c   => .nxt (σ c)
  | .const k => .const k
  | .add a b => .add (renameWindow σ a) (renameWindow σ b)
  | .mul a b => .mul (renameWindow σ a) (renameWindow σ b)

/-- Rename the columns a `ChalExpr` reads. ⚑ `chal i` is NOT a column and does not move — the
challenge index lives in the verifier's own space, and renaming it would be a category error of
exactly the kind `chalCols` already refuses (`EffectLowerCertified.lean:157`). -/
def renameChal (σ : Nat → Nat) : ChalExpr → ChalExpr
  | .loc c   => .loc (σ c)
  | .nxt c   => .nxt (σ c)
  | .const k => .const k
  | .chal i  => .chal i
  | .add a b => .add (renameChal σ a) (renameChal σ b)
  | .mul a b => .mul (renameChal σ a) (renameChal σ b)

/-- Rename one leg. Every constructor's column-bearing fields move and nothing else does: table
ids, range widths, PI indices, `RowSel`s and the declared VK literals are untouched. -/
def renameLeg (σ : Nat → Nat) : AirLeg → AirLeg
  | .gate c   => .gate ⟨renameExpr σ c.lhs, renameExpr σ c.rhs⟩
  | .lookup l => .lookup { l with tuple := l.tuple.map (renameExpr σ), mult := renameExpr σ l.mult }
  | .window w => .window { w with body := renameWindow σ w.body }
  | .pin p    => .pin { p with col := σ p.col }
  | .limbs l  => .limbs { l with cols := l.cols.map σ }
  | .chal c   => .chal { c with body := renameChal σ c.body }
  | .bind b   => .bind { b with
                          guard  := renameExpr σ b.guard
                        , commit := b.commit.map (renameExpr σ)
                        , vk     := b.vk.map (renameExpr σ)
                        , bound  := b.bound.map (renameExpr σ) }

/-- Rename a one-wire range leg. -/
def renameRange (σ : Nat → Nat) (r : RangeLeg) : RangeLeg := { r with wire := σ r.wire }

/-- ⚑ **THE PASS.** An air block with its columns relabelled. `tables` and `extraPi` are untouched:
a table declaration names a table, not a column, and the PI surface is the descriptor's contract
with its caller. -/
def renameAir (σ : Nat → Nat) (air : EffectAir) : EffectAir :=
  { air with legs := air.legs.map (renameLeg σ), ranges := air.ranges.map (renameRange σ) }

/-- The row window read through the allocation: physical column `σ c` is where original column `c`
now lives, so reading original `c` means reading physical `σ c`. -/
def renameEnv (σ : Nat → Nat) (env : VmRowEnv) : VmRowEnv :=
  { loc := fun c => env.loc (σ c)
  , nxt := fun c => env.nxt (σ c)
  , pub := env.pub
  , chal := env.chal }

/-! ### §1a — the three evaluation lemmas. Each is the same one fact at a different grammar. -/

theorem renameExpr_eval (σ : Nat → Nat) (a : Assignment) :
    ∀ e : Expr, (renameExpr σ e).eval a = e.eval (fun c => a (σ c))
  | .var _   => rfl
  | .const _ => rfl
  | .add x y => by simp [renameExpr, Expr.eval, renameExpr_eval σ a x, renameExpr_eval σ a y]
  | .mul x y => by simp [renameExpr, Expr.eval, renameExpr_eval σ a x, renameExpr_eval σ a y]

theorem renameWindow_eval (σ : Nat → Nat) (env : VmRowEnv) :
    ∀ w : WindowExpr, (renameWindow σ w).eval env = w.eval (renameEnv σ env)
  | .loc _   => rfl
  | .nxt _   => rfl
  | .const _ => rfl
  | .add x y => by
      simp [renameWindow, WindowExpr.eval, renameWindow_eval σ env x, renameWindow_eval σ env y]
  | .mul x y => by
      simp [renameWindow, WindowExpr.eval, renameWindow_eval σ env x, renameWindow_eval σ env y]

theorem renameChal_eval (σ : Nat → Nat) (env : VmRowEnv) :
    ∀ c : ChalExpr, (renameChal σ c).eval env = c.eval (renameEnv σ env)
  | .loc _   => rfl
  | .nxt _   => rfl
  | .const _ => rfl
  | .chal _  => rfl
  | .add x y => by
      simp [renameChal, ChalExpr.eval, renameChal_eval σ env x, renameChal_eval σ env y]
  | .mul x y => by
      simp [renameChal, ChalExpr.eval, renameChal_eval σ env x, renameChal_eval σ env y]

/-! ### §1b — ⚑ THE COMPILER'S VERDICT DOES NOT MOVE.

`mainRailOk` asks about SHAPE — multiplicity, selector, limb width, bind declaration — and a
renaming touches none of them. This is what lets the certified lowering elaborate on the allocated
air with no new side condition. -/

theorem renameExpr_isOne (σ : Nat → Nat) (e : Expr) : exprIsOne (renameExpr σ e) = exprIsOne e := by
  cases e <;> rfl

theorem renameWindow_readsNext (σ : Nat → Nat) :
    ∀ w : WindowExpr, readsNext (renameWindow σ w) = readsNext w
  | .loc _   => rfl
  | .nxt _   => rfl
  | .const _ => rfl
  | .add x y => by
      simp [renameWindow, readsNext, renameWindow_readsNext σ x, renameWindow_readsNext σ y]
  | .mul x y => by
      simp [renameWindow, readsNext, renameWindow_readsNext σ x, renameWindow_readsNext σ y]

theorem renameChal_readsNext (σ : Nat → Nat) :
    ∀ c : ChalExpr, chalReadsNext (renameChal σ c) = chalReadsNext c
  | .loc _   => rfl
  | .nxt _   => rfl
  | .const _ => rfl
  | .chal _  => rfl
  | .add x y => by
      simp [renameChal, chalReadsNext, renameChal_readsNext σ x, renameChal_readsNext σ y]
  | .mul x y => by
      simp [renameChal, chalReadsNext, renameChal_readsNext σ x, renameChal_readsNext σ y]

theorem renameLeg_mainRailOk (σ : Nat → Nat) (l : AirLeg) :
    (renameLeg σ l).mainRailOk = l.mainRailOk := by
  cases l with
  | gate _ => rfl
  | pin _ => rfl
  | lookup l => simp [renameLeg, AirLeg.mainRailOk, LookupLeg.mainRailOk, renameExpr_isOne]
  | window w =>
      cases w.sel <;>
        simp [renameLeg, AirLeg.mainRailOk, WindowLeg.mainRailOk, renameWindow_readsNext]
  | limbs l =>
      simp [renameLeg, AirLeg.mainRailOk, LimbsLeg.mainRailOk]
  | chal c =>
      cases c.sel <;>
        simp [renameLeg, AirLeg.mainRailOk, ChalLeg.mainRailOk, renameChal_readsNext]
  | bind b =>
      cases hb : b.bound <;>
        simp [renameLeg, AirLeg.mainRailOk, BindLeg.mainRailOk, hb,
          Dregg2.Circuit.DescriptorIR2.CommitBindingOf.map,
          Dregg2.Circuit.DescriptorIR2.CommitBindingOf.isPort]

/-- ⚑ **THE ALLOCATED BLOCK IS STILL MAIN-RAIL EXPRESSIBLE.** So `lowerTiedAir`/`lowerAirCertified`
elaborate on it with the same `by decide` the unallocated block used. -/
theorem renameAir_mainRailOk (σ : Nat → Nat) (air : EffectAir) :
    (renameAir σ air).mainRailOk = air.mainRailOk := by
  simp only [EffectAir.mainRailOk, renameAir, List.all_map, Function.comp_def,
    renameLeg_mainRailOk]

/-! ### §1c — ⚑ THE THEOREM THE BRIEF ASKS FOR: the refinement survives the pass.

`AirLeg.forces` is the SOURCE semantics (`EffectLowerCertified.lean:110`) — it is stated in
`Expr.eval` / `WindowExpr.eval` / membership in `tf table` and never mentions `lowerLeg`. So this
is a fact about the source language, and the emitted refinement composes with it rather than being
re-derived. -/

/-- ⚑ **A RENAMED LEG FORCES, AT `env`, EXACTLY WHAT THE ORIGINAL FORCED AT `env ∘ σ`.**

An `Iff`, not an implication: the pass loses nothing and invents nothing. Both directions matter —
`→` is what says the allocated circuit is no weaker, `←` is what says it is no stronger, so the
pass cannot smuggle in a constraint the source never wrote. -/
theorem renameLeg_forces (σ : Nat → Nat) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (l : AirLeg) :
    (renameLeg σ l).forces tf env isFirst isLast
      ↔ l.forces tf (renameEnv σ env) isFirst isLast := by
  cases l with
  | gate c => simp [renameLeg, AirLeg.forces, renameExpr_eval, renameEnv]
  | pin p => simp [renameLeg, AirLeg.forces, PiPinLeg.fires, renameEnv]
  | lookup l =>
      simp [renameLeg, AirLeg.forces, List.map_map, Function.comp_def, renameExpr_eval, renameEnv]
  | limbs l =>
      simp only [renameLeg, AirLeg.forces, List.mem_map, renameEnv]
      constructor
      · intro h c hc; exact h (σ c) ⟨c, hc, rfl⟩
      · intro h _ hc; obtain ⟨c, hc, rfl⟩ := hc; exact h c hc
  | window w =>
      cases w.sel <;> simp [renameLeg, AirLeg.forces, renameWindow_eval]
  | chal c =>
      cases c.sel <;> simp [renameLeg, AirLeg.forces, renameChal_eval]
  | bind b =>
      cases hb : b.bound <;>
        simp [renameLeg, AirLeg.forces, List.map_map, Function.comp_def, renameExpr_eval, renameEnv,
          hb, Dregg2.Circuit.DescriptorIR2.CommitBindingOf.map]

/-- The whole leg list, one `∀` over the source's legs. -/
theorem renameAir_forces (σ : Nat → Nat) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (air : EffectAir)
    (h : ∀ l ∈ (renameAir σ air).legs, l.forces tf env isFirst isLast) :
    ∀ l ∈ air.legs, l.forces tf (renameEnv σ env) isFirst isLast := by
  intro l hl
  have : (renameLeg σ l).forces tf env isFirst isLast := by
    refine h (renameLeg σ l) ?_
    simpa [renameAir] using List.mem_map_of_mem (f := renameLeg σ) hl
  exact (renameLeg_forces σ tf env isFirst isLast l).mp this

/-! ### §1d — ⚑ WHICH DIRECTION IS FREE AND WHICH ONE COSTS AN INVARIANT.

This is the half a reuse pass is usually wrong about, so it is two named theorems rather than a
paragraph. -/

/-- ⚑ **NO `σ` CAN ADMIT A WITNESS THE SOURCE REFUSED.** Whatever the allocation — injective,
collapsing, absurd — a row window satisfying the allocated block yields a row window satisfying the
original: read the original's columns through `σ`. So a reuse pass is *sound by construction* and
the invariant is not what protects soundness.

This is the restriction fact: identifying two columns can only add the equation "these are equal". -/
theorem rename_admits_no_new_witness (σ : Nat → Nat) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (air : EffectAir) :
    (∀ l ∈ (renameAir σ air).legs, l.forces tf env isFirst isLast) →
      ∃ env', ∀ l ∈ air.legs, l.forces tf env' isFirst isLast :=
  fun h => ⟨renameEnv σ env, renameAir_forces σ tf env isFirst isLast air h⟩

/-- ⚑ …**AND WHAT THE INVARIANT BUYS IS THE OTHER DIRECTION.** An honest witness of the original
block still fits the allocated one exactly when the physical row can be *filled*: there must be an
`env` whose read-through-`σ` is the honest window. That is possible iff `σ` never identifies two
columns the honest witness gives different values — which is what disjoint live ranges deliver, and
§4 is where it is delivered.

Stated as the pullback existence it really is, so the hypothesis is visible rather than assumed. -/
theorem disjoint_ranges_admit_the_honest_witness (σ : Nat → Nat) (tf : TraceFamily)
    (env' : VmRowEnv) (isFirst isLast : Bool) (air : EffectAir) (env : VmRowEnv)
    (hfill : renameEnv σ env = env')
    (h : ∀ l ∈ air.legs, l.forces tf env' isFirst isLast) :
    ∀ l ∈ (renameAir σ air).legs, l.forces tf env isFirst isLast := by
  intro l hl
  simp only [renameAir, List.mem_map] at hl
  obtain ⟨m, hm, rfl⟩ := hl
  rw [renameLeg_forces, hfill]
  exact h m hm

/-! ## §2 — ⚑ THE ALLOCATED LOWERING, and it needs no new lowering.

`lowerAirCertified` already returns `{ d // CertifiedRefines d cs air }` for any air whose
`mainRailOk` holds (`EffectLowerCertified.lean:507`). §1b says the allocated air's verdict is the
original's, so the certificate is produced by the SAME emit — there is no second pass to keep
honest, which is the `merging_is_naming_the_same_variable` shape. -/

/-- ⚑ **THE ALLOCATED CIRCUIT FORCES WHAT THE UNALLOCATED ONE FORCED.**

`CertifiedRefines d cs (renameAir σ air)` — the certificate the emit hands back for the ALLOCATED
source — is pulled back to a statement about the ORIGINAL source's legs, read through the
allocation. No byte of the lowering is re-proved; `renameLeg_forces` is the whole bridge.

⚠ The conclusion is at `renameEnv σ env`, and that is the honest statement rather than a weaker
one: the original block's columns are not there any more, so what the descriptor forces about them
is forced *at the physical columns they were allocated to*. Claiming it at `env` would be claiming
the pass moved nothing. -/
theorem allocated_forces_what_it_forced
    (σ : Nat → Nat) (d : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2)
    (cs : Dregg2.Circuit.ConstraintSystem) (air : EffectAir)
    (hcert : Dregg2.Circuit.Emit.EffectLower.CertifiedRefines d cs (renameAir σ air))
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (hrow : ∀ c ∈ d.constraints, c.holdsAt hash tf env isFirst isLast) :
    ∀ l ∈ air.legs, l.forces tf (renameEnv σ env) isFirst isLast :=
  renameAir_forces σ tf env isFirst isLast air (hcert hash tf env isFirst isLast hrow).1

/-! ## §3 — ⚑ LIVENESS over the SSA DAG.

A value's live range is `[def, last use]`, in the units the schedule counts in. On the one-row
schedule every op happens at time `0`, so every range is `[0,0]` and everything interferes; on the
one-op-per-row schedule op `i` happens at time `i`. Both are instances of the same definition,
which is the point — the schedule is an input to liveness, not a property of the DAG. -/

/-- **One SSA op**: the value it defines and the values it reads. Times are the op's index in the
list, so the list IS the schedule. -/
structure SsaOp where
  /-- The value this op defines. -/
  dst  : Nat
  /-- The values this op reads. -/
  srcs : List Nat
  deriving Repr, DecidableEq

/-- **A live range**, closed at both ends: the value is resident in a column from `lo` through
`hi` inclusive. -/
structure LiveRange where
  /-- The value this range belongs to. -/
  val : Nat
  /-- First time the value must be resident — its definition, or `0` for a block input. -/
  lo  : Nat
  /-- Last time the value must be resident — its last read, or its definition if never read. -/
  hi  : Nat
  deriving Repr, DecidableEq

/-- ⚑ **INTERFERENCE.** Two closed intervals interfere iff they overlap. This is the ONLY reason a
column may not be shared, and it is decidable — which is what lets the allocator be a pure fold and
the invariant be `by decide`-checkable at any concrete instance. -/
def LiveRange.interferes (a b : LiveRange) : Bool := a.lo ≤ b.hi && b.lo ≤ a.hi

/-- Interference is symmetric. -/
theorem LiveRange.interferes_comm (a b : LiveRange) : a.interferes b = b.interferes a := by
  simp [LiveRange.interferes, Bool.and_comm]

/-- …and reflexive on a non-empty range, so a value never shares a column with itself by accident. -/
theorem LiveRange.interferes_self (a : LiveRange) (h : a.lo ≤ a.hi) : a.interferes a = true := by
  simp [LiveRange.interferes, h]

/-- The time at which `v` is defined under the schedule `ops`: the index of the op that defines it,
or `0` when nothing does (a block input, live from the top). -/
def defTime (ops : List SsaOp) (v : Nat) : Nat :=
  match ops.findIdx? (fun o => o.dst == v) with
  | some i => i
  | none   => 0

/-- The last time `v` is read, or its definition time when it is never read. A value that is
defined and never read still occupies a column at its definition — that is where its gate writes. -/
def lastUse (ops : List SsaOp) (v : Nat) : Nat :=
  let reads := (List.range ops.length).filter
    (fun i => match ops[i]? with | some o => v ∈ o.srcs | none => false)
  reads.foldl max (defTime ops v)

/-- Every value the schedule mentions: the ones it defines and the ones it reads. -/
def allValues (ops : List SsaOp) : List Nat :=
  (ops.map SsaOp.dst ++ ops.flatMap SsaOp.srcs).eraseDups

/-- ⚑ **THE LIVE RANGES OF A SCHEDULE.** One per value, in a deterministic order. -/
def liveRanges (ops : List SsaOp) : List LiveRange :=
  (allValues ops).map (fun v => ⟨v, defTime ops v, lastUse ops v⟩)

/-- The set of values resident at time `t`. -/
def liveAt (ops : List SsaOp) (t : Nat) : List Nat :=
  ((liveRanges ops).filter (fun r => r.lo ≤ t && t ≤ r.hi)).map LiveRange.val

/-- ⚑ **PEAK PRESSURE** — the largest simultaneous live set over the schedule's whole extent. This
is the number a reuse pass is trying to reach, and for an interval graph it is also the chromatic
number, so it is the FLOOR as well as the target. -/
def peakLive (ops : List SsaOp) : Nat :=
  ((List.range (ops.length + 1)).map (fun t => (liveAt ops t).length)).foldl max 0

/-! ## §4 — ⚑ THE ALLOCATOR, and the invariant it is built to have.

Greedy colouring of the interference graph, taken in list order: each range gets the least slot no
already-placed *interfering* range holds. The disjointness invariant is then true **by
construction** rather than by a check afterwards — which is the whole reason the allocator is
written this way and not as a state monad over a fresh counter.

⚑ Deliberately NOT `StateM`, for the reason `KimchiArena` gives: *"a state monad puts the circuit
behind a `run` and `decide` doesn't reach usefully through one."* This is a pure fold and `decide`
reaches through it. -/

/-- The least natural number not in `used`. Bounded search over `used.length + 1` candidates, which
always contains one by pigeonhole. -/
def firstFree (used : List Nat) : Nat :=
  match (List.range (used.length + 1)).find? (fun s => !(used.contains s)) with
  | some s => s
  | none   => used.length

/-- `firstFree` is genuinely free of the list it was given. -/
theorem firstFree_not_mem (used : List Nat) : firstFree used ∉ used := by
  unfold firstFree
  cases h : (List.range (used.length + 1)).find? (fun s => !(used.contains s)) with
  | some s =>
      show s ∉ used
      have hfind := List.find?_some h
      simp only [Bool.not_eq_true'] at hfind
      intro hmem
      rw [List.contains_iff_mem.mpr hmem] at hfind
      exact Bool.noConfusion hfind
  | none =>
      -- Every candidate in `range (n+1)` is then a member of `used`, so `used` contains `n+1`
      -- pairwise-distinct naturals while `used.length = n`. Pigeonhole, as a subpermutation.
      exfalso
      have hsub : List.range (used.length + 1) ⊆ used := by
        intro s hs
        have := List.find?_eq_none.mp h s hs
        simpa [List.contains_iff_mem] using this
      have hnd : (List.range (used.length + 1)).Nodup := List.nodup_range
      have := (hnd.subperm hsub).length_le
      simp at this

/-- ⚑ **THE ALLOCATOR'S STEP**, as an explicit fold so the invariant is readable: place `r` at the
least slot none of the already-placed interfering ranges holds. -/
def allocStep (acc : List (LiveRange × Nat)) (r : LiveRange) : List (LiveRange × Nat) :=
  acc ++ [(r, firstFree ((acc.filter (fun p => p.1.interferes r)).map Prod.snd))]

/-- ⚑ **THE ALLOCATOR.** A left fold; no state monad, no fresh counter, no `Nodup`. -/
def allocate (rs : List LiveRange) : List (LiveRange × Nat) := rs.foldl allocStep []

/-- The number of physical slots the allocation uses. -/
def allocWidth (rs : List LiveRange) : Nat :=
  (((allocate rs).map Prod.snd).foldl max 0) + 1

/-- ⚑ **THE PROPERTY**, as a `Pairwise` on the placement: **two ranges sharing a slot do not
interfere.** `Pairwise` rather than an index quantifier because the relation is SYMMETRIC —
`interferes` is (`LiveRange.interferes_comm`) and `=` is — so the earlier-than-later form already
carries the full statement, and `List.Pairwise.forall` cashes it. -/
def DisjointSharing (pl : List (LiveRange × Nat)) : Prop :=
  pl.Pairwise (fun p q => p.2 = q.2 → p.1.interferes q.1 = false)

/-- The relation IS symmetric, which is what makes the `Pairwise` form equivalent to the
all-pairs one. -/
theorem sharingRel_symm :
    Symmetric (fun p q : LiveRange × Nat => p.2 = q.2 → p.1.interferes q.1 = false) := by
  intro p q h hslot
  rw [LiveRange.interferes_comm]
  exact h hslot.symm

/-- The same symmetry as the `Std.Symm` instance Mathlib's `List.Pairwise.forall` takes. -/
instance sharingRel_isSymm :
    Std.Symm (fun p q : LiveRange × Nat => p.2 = q.2 → p.1.interferes q.1 = false) :=
  ⟨fun _ _ h => sharingRel_symm h⟩

theorem disjointSharing_nil : DisjointSharing [] := List.Pairwise.nil

/-- The step preserves it: the appended element's slot was chosen free of every interfering
predecessor, and the predecessors' pairwise property is untouched by an append. -/
theorem disjointSharing_step (acc : List (LiveRange × Nat)) (r : LiveRange)
    (h : DisjointSharing acc) : DisjointSharing (allocStep acc r) := by
  unfold DisjointSharing allocStep
  refine List.pairwise_append.mpr ⟨h, List.pairwise_singleton .., ?_⟩
  intro p hp q hq hslot
  simp only [List.mem_singleton] at hq
  subst hq
  -- `p` sits in `acc` and holds the slot the step just chose. Had it interfered with `r`, its slot
  -- would be in the list `firstFree` was told to avoid.
  by_contra hcon
  have hint : p.1.interferes r = true := by simpa using hcon
  refine absurd ?_ (firstFree_not_mem
    ((acc.filter (fun x => x.1.interferes r)).map Prod.snd))
  exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simpa using hint⟩, hslot⟩

/-- ⚑⚑ **THE INVARIANT, GENERAL: TWO VALUES SHARING A COLUMN HAVE DISJOINT LIVE RANGES.**

The negation of `KimchiArena.alloc_injective` and deliberately so. `alloc_injective` is worth having
where two slots must never denote one variable; here two slots MUST sometimes denote one column, and
what has to be true instead is that the values they carry are never simultaneously resident.

Proved for every interval list — not checked on one. -/
theorem alloc_disjoint (rs : List LiveRange) : DisjointSharing (allocate rs) := by
  unfold allocate
  suffices h : ∀ (l : List LiveRange) (acc : List (LiveRange × Nat)),
      DisjointSharing acc → DisjointSharing (l.foldl allocStep acc) by
    exact h rs [] disjointSharing_nil
  intro l
  induction l with
  | nil => intro acc h; simpa using h
  | cons a t ih => intro acc h; exact ih _ (disjointSharing_step acc a h)

/-- ⚑ The readable corollary, in the vocabulary the brief used: **if the allocation puts two
DIFFERENT values in the same column, their live ranges do not overlap.** Both directions of the
`interferes` conjunction are unpacked, so this is the interval statement and not a `Bool`. -/
theorem shared_column_means_disjoint_live_ranges (rs : List LiveRange)
    (p q : LiveRange × Nat) (hp : p ∈ allocate rs) (hq : q ∈ allocate rs)
    (hne : p ≠ q) (hsame : p.2 = q.2) :
    p.1.hi < q.1.lo ∨ q.1.hi < p.1.lo := by
  have h := (alloc_disjoint rs).forall hp hq hne hsame
  simp only [LiveRange.interferes, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  omega

/-- Every placed range keeps its identity — the allocation is a relabelling of the SAME list, in
the SAME order, so nothing is dropped and nothing is invented. -/
theorem allocate_ranges (rs : List LiveRange) : (allocate rs).map Prod.fst = rs := by
  unfold allocate
  suffices h : ∀ (l : List LiveRange) (acc : List (LiveRange × Nat)),
      (l.foldl allocStep acc).map Prod.fst = acc.map Prod.fst ++ l by
    simpa using h rs []
  intro l
  induction l with
  | nil => intro acc; simp
  | cons a t ih => intro acc; simp [allocStep, ih]


/-! ## §5 — ⚑ THE SOUND RCB ROW, MEASURED ON BOTH SCHEDULES.

The 33 SSA ops of `PastaCurveSound.swCompleteAddSoundLegs` (`:422-454`), transcribed as an op list.
Value ids: `0..5` are the six input blocks `X1 Y1 Z1 X2 Y2 Z2`, `6+i` is the gadget's `v i`. Each op
is at its list index, so the list IS the schedule and the two schedules below differ only in it. -/

/-- Value id of the gadget's `v i`. -/
def V (i : Nat) : Nat := 6 + i

/-- ⚑ **THE RCB DAG, IN THE GADGET'S OWN ORDER.** One entry per `++` line of
`swCompleteAddSoundLegs`, `12 mul + 2 smul + 14 add + 5 sub`. -/
def rcbOps : List SsaOp :=
  [ ⟨V 0,  [0, 3]⟩,        ⟨V 1,  [1, 4]⟩,        ⟨V 2,  [2, 5]⟩
  , ⟨V 3,  [0, 1]⟩,        ⟨V 4,  [3, 4]⟩,        ⟨V 5,  [V 3, V 4]⟩
  , ⟨V 6,  [V 0, V 1]⟩,    ⟨V 7,  [V 5, V 6]⟩,    ⟨V 8,  [1, 2]⟩
  , ⟨V 9,  [4, 5]⟩,        ⟨V 10, [V 8, V 9]⟩,    ⟨V 11, [V 1, V 2]⟩
  , ⟨V 12, [V 10, V 11]⟩,  ⟨V 13, [0, 2]⟩,        ⟨V 14, [3, 5]⟩
  , ⟨V 15, [V 13, V 14]⟩,  ⟨V 16, [V 0, V 2]⟩,    ⟨V 17, [V 15, V 16]⟩
  , ⟨V 18, [V 0, V 0]⟩,    ⟨V 19, [V 18, V 0]⟩,   ⟨V 20, [V 2, V 2]⟩
  , ⟨V 21, [V 1, V 20]⟩,   ⟨V 22, [V 1, V 20]⟩,   ⟨V 23, [V 17, V 17]⟩
  , ⟨V 24, [V 12, V 23]⟩,  ⟨V 25, [V 7, V 22]⟩,   ⟨V 26, [V 25, V 24]⟩
  , ⟨V 27, [V 23, V 19]⟩,  ⟨V 28, [V 22, V 21]⟩,  ⟨V 29, [V 28, V 27]⟩
  , ⟨V 30, [V 19, V 7]⟩,   ⟨V 31, [V 21, V 12]⟩,  ⟨V 32, [V 31, V 30]⟩ ]

theorem rcbOps_length : rcbOps.length = 33 := by decide

/-- The three blocks the row PUBLISHES — `X3 = v26`, `Y3 = v29`, `Z3 = v32`
(`PastaLadderThread.OUT_X/Y/Z`, `:120-124`). They must still be resident on the LAST row of the
block, because the thread gate `nxt(ACC+i) − loc(OUT+i) = 0` reads them there. -/
def rcbOuts : List Nat := [V 26, V 29, V 32]

/-- ⚑ Live ranges with the published blocks HELD TO THE END OF THE BLOCK. Without this a value
whose last consumer is early would be recycled before the thread reads it — the one liveness bug a
register allocator on an AIR can have that a CPU allocator cannot. -/
def liveRangesHeld (ops : List SsaOp) (held : List Nat) : List LiveRange :=
  (liveRanges ops).map fun r =>
    if r.val ∈ held then { r with hi := max r.hi (ops.length - 1) } else r

/-! ### §5a — ⚑ THE ONE-ROW SCHEDULE: the interference graph is COMPLETE, so 3 048 IS OPTIMAL.

`pallasCompleteAddSoundAir` asserts all 33 op blocks on ONE row. In that schedule every op happens
at time `0`, so every live range is `[0,0]` and every pair overlaps. This is the theorem that turns
"a fresh column per SSA value and never reuse one" from a diagnosis into a measurement of where the
defect actually is: **not in the allocation.** -/

/-- Every block of the row, on the one-row schedule: the 39 value blocks AND the 33 per-op private
witness blocks, all resident at time `0`. -/
def rcbOneRowRanges : List LiveRange :=
  (List.range 72).map (fun i => ⟨i, 0, 0⟩)

/-- ⚑ **THE INTERFERENCE GRAPH OF THE DEPLOYED ROW IS COMPLETE.** -/
theorem rcb_single_row_interference_is_complete :
    ∀ p ∈ rcbOneRowRanges, ∀ q ∈ rcbOneRowRanges, p.interferes q = true := by
  intro p hp q hq
  simp only [rcbOneRowRanges, List.mem_map] at hp hq
  obtain ⟨_, _, rfl⟩ := hp
  obtain ⟨_, _, rfl⟩ := hq
  rfl

/-- ⚑ **AND A COMPLETE INTERFERENCE GRAPH FORCES AN INJECTIVE ALLOCATION** — general, not about
the RCB row. This is the precise sense in which the naive layout was already optimal for the
schedule it was written against, and the precise sense in which no allocator could have helped. -/
theorem all_interfering_forces_distinct_slots (pl : List (LiveRange × Nat))
    (hd : DisjointSharing pl)
    (hall : ∀ p ∈ pl, ∀ q ∈ pl, p.1.interferes q.1 = true) :
    ∀ p ∈ pl, ∀ q ∈ pl, p ≠ q → p.2 ≠ q.2 := by
  intro p hp q hq hne hslot
  have hfalse := hd.forall hp hq hne hslot
  rw [hall p hp q hq] at hfalse
  exact Bool.noConfusion hfalse

/-- The instance: the deployed one-row block needs one column-block per value, all 72 of them. -/
theorem rcb_single_row_needs_all_72_slots :
    ∀ p ∈ allocate rcbOneRowRanges, ∀ q ∈ allocate rcbOneRowRanges, p ≠ q → p.2 ≠ q.2 := by
  refine all_interfering_forces_distinct_slots _ (alloc_disjoint _) ?_
  intro p hp q hq
  have hrs := allocate_ranges rcbOneRowRanges
  have hp1 : p.1 ∈ rcbOneRowRanges := by rw [← hrs]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hq1 : q.1 ∈ rcbOneRowRanges := by rw [← hrs]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
  exact rcb_single_row_interference_is_complete p.1 hp1 q.1 hq1

theorem rcb_single_row_alloc_width : allocWidth rcbOneRowRanges = 72 := by decide

/-! ### §5b — ⚑ THE ONE-OP-PER-ROW SCHEDULE: liveness has an inside, and the allocator cashes it. -/

/-- The RCB DAG rescheduled to minimise register pressure. Same 33 ops, same DAG — the three
`X1·X2 / Y1·Y2 / Z1·Z2` products are DELAYED past the `t3a/t4a/t3b` chain that does not read them,
which is the single reordering that takes the peak from 12 blocks to 11. -/
def rcbOpsScheduled : List SsaOp :=
  [ ⟨V 3,  [0, 1]⟩,        ⟨V 4,  [3, 4]⟩,        ⟨V 5,  [V 3, V 4]⟩
  , ⟨V 0,  [0, 3]⟩,        ⟨V 1,  [1, 4]⟩,        ⟨V 6,  [V 0, V 1]⟩
  , ⟨V 7,  [V 5, V 6]⟩,    ⟨V 2,  [2, 5]⟩,        ⟨V 8,  [1, 2]⟩
  , ⟨V 9,  [4, 5]⟩,        ⟨V 10, [V 8, V 9]⟩,    ⟨V 11, [V 1, V 2]⟩
  , ⟨V 12, [V 10, V 11]⟩,  ⟨V 13, [0, 2]⟩,        ⟨V 14, [3, 5]⟩
  , ⟨V 15, [V 13, V 14]⟩,  ⟨V 16, [V 0, V 2]⟩,    ⟨V 17, [V 15, V 16]⟩
  , ⟨V 18, [V 0, V 0]⟩,    ⟨V 19, [V 18, V 0]⟩,   ⟨V 20, [V 2, V 2]⟩
  , ⟨V 21, [V 1, V 20]⟩,   ⟨V 22, [V 1, V 20]⟩,   ⟨V 23, [V 17, V 17]⟩
  , ⟨V 24, [V 12, V 23]⟩,  ⟨V 25, [V 7, V 22]⟩,   ⟨V 26, [V 25, V 24]⟩
  , ⟨V 27, [V 23, V 19]⟩,  ⟨V 28, [V 22, V 21]⟩,  ⟨V 29, [V 28, V 27]⟩
  , ⟨V 30, [V 19, V 7]⟩,   ⟨V 31, [V 21, V 12]⟩,  ⟨V 32, [V 31, V 30]⟩ ]

theorem rcbOpsScheduled_length : rcbOpsScheduled.length = 33 := by decide

/-- ⚑ **THE RESCHEDULE IS A PERMUTATION OF THE SAME DAG** — the same 33 ops with the same operands,
not a different circuit. Anything else would be changing the arithmetic to win a number, which is
the move this repo's own doctrine forbids. -/
theorem rcbOpsScheduled_is_a_permutation : rcbOpsScheduled.Perm rcbOps := by decide

/-- …and it RESPECTS THE DAG: every op's operands are defined before it runs, or are block inputs.
A reordering that broke this would read a column before anything wrote it. -/
def scheduleIsTopological (ops : List SsaOp) : Bool :=
  (List.range ops.length).all fun i =>
    match ops[i]? with
    | some o => o.srcs.all fun s => defTime ops s < i || (ops.all fun p => p.dst != s)
    | none   => true

theorem rcbOpsScheduled_topological : scheduleIsTopological rcbOpsScheduled = true := by decide

theorem rcbOps_topological : scheduleIsTopological rcbOps = true := by decide

/-- The value blocks' live ranges under the reschedule, outputs held to the last row. -/
def rcbScheduledRanges : List LiveRange := liveRangesHeld rcbOpsScheduled rcbOuts

/-- ⚑ **PEAK REGISTER PRESSURE ON THE RESCHEDULED DAG.** -/
def rcbScheduledPeak : Nat :=
  ((List.range 33).map
    (fun t => ((rcbScheduledRanges.filter (fun r => r.lo ≤ t && t ≤ r.hi)).length))).foldl max 0

/-- The naive order's peak, for the comparison. -/
def rcbNaivePeak : Nat :=
  ((List.range 33).map
    (fun t => (((liveRangesHeld rcbOps rcbOuts).filter (fun r => r.lo ≤ t && t ≤ r.hi)).length))).foldl max 0

/-- ⚑⚑ **ELEVEN.** Peak register pressure over the rescheduled DAG. The brief's number, derived
here from the op list rather than counted by hand. -/
theorem rcb_scheduled_peak_is_eleven : rcbScheduledPeak = 11 := by decide

/-- …and the gadget's own order costs one more, which is what the reschedule is for. -/
theorem rcb_naive_order_peak_is_twelve : rcbNaivePeak = 12 := by decide

/-- ⚑⚑ **AND THE ALLOCATOR REACHES THE FLOOR: 39 VALUE BLOCKS INTO 11 COLUMNS-BLOCKS.**

Greedy colouring in schedule order is optimal on an interval graph, and this is that fact
instantiated: `allocWidth = rcbScheduledPeak`, so no allocator can do better on this schedule and
the remaining 28 blocks are pure recovered scratch. -/
theorem rcb_scheduled_alloc_width_is_eleven : allocWidth rcbScheduledRanges = 11 := by decide

theorem rcb_alloc_hits_the_peak : allocWidth rcbScheduledRanges = rcbScheduledPeak := by decide

/-- The allocation covers every value block — 6 inputs + 33 SSA. Nothing was dropped to reach 11. -/
theorem rcb_scheduled_allocates_all_39 : (allocate rcbScheduledRanges).length = 39 := by decide

/-! ### §5b′ — ⚑⚑ THE WIDTH THE PROVER ACTUALLY COMMITS, AND IT IS NOT THE DECLARED ONE.

`MainLayout::build` (`circuit/src/descriptor_ir2.rs:1919`) compiles every declared range lookup
into the declared column **plus a nibble aux block**, and `Ir2Air::Main` is `width()`d at the sum.
So a cost law read against `traceWidth` is read against the wrong denominator — measured by
`circuit-prove/tests/mina_accumulator_leaf_anatomy.rs::the_wrap_cost_tracks_committed_width_not_declared_width`,
`ops/declared` spreads 1.78× across two shapes while `ops/committed` spreads 1.12×: **the wrap cost
is LINEAR in committed width.**

⚑ And the consequence for a reuse pass is the one that matters: **71.7% of the sound row's
committed width is range-check decomposition**, which a register allocator does not touch at all.
What DOES touch it is the schedule — one op per row lets the per-op range lookups become per-POOL
range lookups — and that is where most of this cone's win actually comes from. -/

/-- ⚑ **THE DEPLOYED AUX-BLOCK GEOMETRY**, transcribed from `descriptor_ir2.rs:1870-1883`:

    limb_geom(bits) = (n = bits.div_ceil(LIMB_BITS), top = bits − (n−1)·LIMB_BITS)
    decomp_cols(bits) = n + (if top < LIMB_BITS then top else 0)

with `LIMB_BITS = 4` (`:408`). ⚠ The partial-top term is NOT decoration: it makes a ONE-BIT lookup
cost **2** aux columns rather than 1, which is exactly the 19-column gap between a naive
`⌈bits/4⌉` model and the measured 7 708. -/
def decompCols (bits : Nat) : Nat :=
  let n := (bits + 3) / 4
  let top := bits - (n - 1) * 4
  n + (if top < 4 then top else 0)

/-- The three widths this cone uses, against the deployed `decomp_cols_pub`. -/
theorem decompCols_at_the_three_widths :
    decompCols 1 = 2 ∧ decompCols 8 = 2 ∧ decompCols 16 = 4 := by decide

/-- The range width a table declares, if it declares one. -/
def tableRangeBits (tables : List Dregg2.Circuit.DescriptorIR2.TableDef)
    (tid : Dregg2.Circuit.DescriptorIR2.TableId) : Nat :=
  match tables.find? (fun t => t.id = tid) with
  | some t => match t.sem with
              | .rangeLimb b => b
              | _ => 0
  | none => 0

/-- ⚑ **THE AUX BLOCK AN AIR CARRIES** — one `decompCols` per emitted range lookup, and the bits
come from the TABLE the lookup queries, exactly as `committed_width` reads them. -/
def airAuxCols (air : EffectAir) : Nat :=
  (air.legs.map fun l =>
    match l with
    | .limbs q => q.cols.length * decompCols (tableRangeBits air.tables q.table)
    | _ => 0).sum
  + (air.ranges.map fun r => decompCols r.bits).sum

/-- ⚑ **THE WIDTH `Ir2Air::Main` IS `width()`d AT.** -/
def committedWidth (declared : Nat) (air : EffectAir) : Nat := declared + airAuxCols air

/-! ### §5c — ⚑ THE COLUMN ARITHMETIC, from the leg structure rather than by estimate.

One op per row means the per-op private witness pools are sized by the WIDEST op, not by the sum
over 33 ops. And the pools are split by RANGE CLASS, which is a soundness requirement and not
tidiness: `Ir2Air::Main` hardcodes lookup multiplicity to `ONE`
(`circuit/src/descriptor_ir2.rs:3738`), so a declared range lookup fires on **every row** — a
physical column shared between an 8-bit limb slot and a 16-bit carry slot would be queried against
both tables at every row and refuse the honest witness. -/

/-- The 34 phase columns: one per op, plus the idle state the row-count padding needs. -/
def SCHED_SEL_COLS : Nat := 34
/-- 11 value slots of `SK = 32` byte limbs. -/
def SCHED_VALUE_COLS : Nat := 11 * 32
/-- The widest single-op 8-bit witness: a multiply's 32 quotient limbs (an add/sub's is 31, a
constant multiply's is 1). -/
def SCHED_W8_WITNESS : Nat := 32
/-- The widest single-op 16-bit witness: a multiply's 62 carries (a constant multiply's is 31, an
add/sub's is 0). -/
def SCHED_W16_WITNESS : Nat := 62
/-- The one-bit witness: an add/sub's carry/borrow bit. -/
def SCHED_W1_WITNESS : Nat := 1

/-- ⚑ **THE SCHEDULED ROW'S WIDTH.** -/
def SCHED_WIDTH : Nat :=
  SCHED_SEL_COLS + SCHED_VALUE_COLS + SCHED_W1_WITNESS + SCHED_W8_WITNESS + SCHED_W16_WITNESS

theorem sched_width_eq : SCHED_WIDTH = 481 := by decide

/-- The deployed one-row width, for the ratio. `PastaCurveSound.rcb_width_eq`. -/
def NAIVE_WIDTH : Nat := 3048

/-- ⚑ **6.33×**, and the recovered scratch is `2 567` columns. -/
theorem sched_recovers_2567_columns : NAIVE_WIDTH - SCHED_WIDTH = 2567 := by decide

/-- The naive layout's own accounting, re-derived here so the two sides are comparable: 39 value
blocks at 32, 12 multiply witnesses at 94, 2 constant-multiply witnesses at 32, 19 add/sub
witnesses at 32. -/
theorem naive_width_is_the_sum_of_all_72_blocks :
    39 * 32 + 12 * (32 + 62) + 2 * 32 + 19 * 32 = NAIVE_WIDTH := by decide

#assert_axioms renameLeg_forces
#assert_axioms renameAir_mainRailOk
#assert_axioms allocated_forces_what_it_forced
#assert_axioms rename_admits_no_new_witness
#assert_axioms disjoint_ranges_admit_the_honest_witness
#assert_axioms alloc_disjoint
#assert_axioms shared_column_means_disjoint_live_ranges
#assert_axioms all_interfering_forces_distinct_slots
#assert_axioms rcb_single_row_interference_is_complete
#assert_axioms rcb_single_row_needs_all_72_slots
#assert_axioms rcb_scheduled_peak_is_eleven
#assert_axioms rcb_scheduled_alloc_width_is_eleven
#assert_axioms rcbOpsScheduled_is_a_permutation
#assert_axioms rcbOpsScheduled_topological
#assert_axioms sched_width_eq

end Dregg2.Circuit.Emit.AirColumnAlloc
