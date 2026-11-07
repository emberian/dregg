/-
# `Dregg2.Circuit.Emit.EffectLowerCertified` — ⚑ THE LOWERING EMITS ITS OWN REFINEMENT.

`EffectLowerCore.lowerAir` returns an `EffectVmDescriptor2` and nothing else. Measured at source
(2026-08-06), what follows BY CONSTRUCTION from a leg today is:

  * `lowerLeg_ne_nil` — a leg contributes ≥ 1 constraint. A COUNT fact; it says nothing about what
    the constraint means.
  * `AirNormalForm.headToExpr_isNormal` — the emitted body is canonically RENDERED. A shape fact.
  * `refuse_bites` — an inexpressible leg lowers to an unsatisfiable pair. A refusal, and it needs
    `isFirst ∨ isLast` to bite (both halves are `.boundary`s), so it is a TRACE-level tooth.
  * `lowerConstraint_holdsAt_iff` — the ONE genuine per-leg refinement lemma in the tree, and it
    covers ONE of the seven leg kinds (`.gate`).

For the other six kinds — `lookup`, `window`, `pin`, `limbs`, `chal`, `bind` — there was no lemma
saying "this leg, lowered, forces X". Every consumer re-established it by hand at the descriptor,
from the TARGET constructor's reduction lemmas (`holdsVm_piFirst_true`, `lookup_replaces_range`,
`chip_lookup_sound`, `gateBody_eval`). Measured over `metatheory/Dregg2/Circuit/`: **508
constraint-membership theorems across 141 files**, **88 uses of `holdsVm_piFirst_true`**, **351
uses of the `Int.modEq_iff_dvd` + `omega` mod-`p` lift** — the same handful of facts, re-derived
once per descriptor.

## What this module adds

`AirLeg.forces` — **the SOURCE SEMANTICS of a leg**, by structural recursion, stated in the
SOURCE's vocabulary (`Expr.eval`, `WindowExpr.eval`, membership in `tf table`, the PI equality) and
never mentioning `lowerLeg`. Then one refinement lemma per leg kind, one combined
`lowerLeg_forces`, and the composition `lowerAirLegs_forces` — which is genuinely compositional:
it is `List.mem_flatMap` on the emission and `List.all_eq_true` on the verdict, nothing per-leg.
`lowerAirCertified` is the entry point that returns the descriptor PAIRED WITH that proof.

⚑ **`EffectAir.mainRailOk` is the degenerate instance, and it becomes the side condition.** The
existing decidable verdict is exactly the hypothesis the refinement lemma needs: a leg the main
rail cannot take has no image to refine to. `hok` is discharged `by decide` at every real air block.

## ⚠ WHAT WOULD MAKE THIS VACUOUS, and the discipline against it

A `forces` that said "the lowered constraints hold" would be `P → P` — the identity-carrier sin.
`AirLeg.forces` is defined WITHOUT reference to the lowering, in the source grammar, so the lemma
has to cross a real gap (`emitExpr_eval`, `windowToLocal_eval`, the `RowSel` → `onTransition`
dispatch, the lane-vector `map`). §6 exhibits BOTH POLES on a concrete row: a leg whose `forces`
HOLDS, and a leg whose `forces` is FALSE — refuted, not merely unproved.

## ⚠ WHAT IT DOES NOT BUY — stated here, not in a footnote

`forces` is the deployed mod-`p` denotation, NOT ℤ. The lift needs the canonicality envelope and
that stays a real hypothesis (`EffectLowerCore.eq_of_modEq_canon`). And it cannot make an AIR
*mean* the right thing: it makes the descriptor force what its legs SAY. A leg that says the wrong
thing is refined faithfully into a descriptor that forces the wrong thing. §7 is the largest
measured instance of exactly that, and answers it with a SECOND verdict rather than a better lemma.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. NEW file; imports read-only; ADDITIVE — `lowerAir` is
unchanged and `lowerAirCertified.val` is `lowerAir` by `rfl`, so no emitted byte moves.
-/
import Dregg2.Circuit.Emit.EffectLowerCore

/-! ## §1 — THE SOURCE SEMANTICS. What a leg CLAIMS, in the source's own vocabulary.

⚑ It lives in the SOURCE IR's namespace (`Dregg2.Circuit.EffectAirIR`), not the lowering's. A
denotation that lived with the compiler would be a denotation the compiler could bend; a leg's
meaning belongs to the leg.

Three properties this definition is built to have, and each is a way it could have been vacuous:

1. **It never mentions `lowerLeg`.** A denotation defined as "the emitted constraints hold" proves
   nothing; the refinement lemma would be `rfl`.
2. **It carries the ROW GUARDS the deployed AIR actually applies.** A `.gate` is vacuous on the
   wrap row (`EffectVmEmit.holdsVm_gate_true`), a first-row pin is vacuous off row 0. Stating
   `forces` unguarded would be stating something the descriptor does not force.
3. **It is stated mod `p`.** `VmConstraint.holdsVm` asserts a congruence; claiming ℤ equality here
   would be claiming the deployed canonicality envelope for free. -/

namespace Dregg2.Circuit.EffectAirIR

open Dregg2.Circuit (Assignment Constraint Expr)
open Dregg2.Circuit.DescriptorIR2 (TraceFamily WindowExpr ChalExpr zeroLanes)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow VmRowEnv)
open Dregg2.Circuit.TableAirIR (RowSel)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The deployed BabyBear modulus the row denotation reduces against — the same literal
`VmConstraint.holdsVm` asserts and the same one `Emit.EffectLower.P` abbreviates. -/
abbrev PMOD : ℤ := 2013265921

/-- Which boundary flag a PI pin fires on. -/
def PiPinLeg.fires (p : PiPinLeg) (isFirst isLast : Bool) : Bool :=
  match p.row with
  | .first => isFirst
  | .last  => isLast

/-- ⚑ **`AirLeg.forces` — the leg's own claim about a row window.**

Read the arms as the source language's semantics, one per constructor:

* `gate` — the equation holds on the TRANSITION domain, which is where the deployed
  `when_transition()` arm binds and nowhere else.
* `pin` — the pinned column agrees with the published slot ON THE PIN'S ROW.
* `lookup` — the evaluated tuple is a row of the queried table.
* `limbs` — EVERY limb is a row of the declared range table. One claim per limb, not one for the
  vector: a dropped limb has to move the denotation, not only the constraint count.
* `window` / `chal` — the body vanishes, under the scope the `RowSel` names.
* `bind` — the guard is a bit and the DECLARED halves tie the lane vectors.

⚠ `chal .first`/`.last` are `True`: the target has no first/last challenge form, `ChalLeg.mainRailOk`
refuses them and `lowerChalLeg` emits the refusal. The source genuinely claims nothing there, and
the refusal is what carries that case — not this definition. -/
def AirLeg.forces (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool) : AirLeg → Prop
  | .gate c   => isLast = false → c.lhs.eval env.loc ≡ c.rhs.eval env.loc [ZMOD PMOD]
  | .pin p    => p.fires isFirst isLast = true → env.loc p.col ≡ env.pub p.idx [ZMOD PMOD]
  | .lookup l => (l.tuple.map (fun e => e.eval env.loc)) ∈ tf l.table
  | .limbs l  => ∀ c ∈ l.cols, ([env.loc c] : List ℤ) ∈ tf l.table
  | .window w =>
      match w.sel with
      | .transition => isLast = false → w.body.eval env ≡ 0 [ZMOD PMOD]
      | .all        => w.body.eval env ≡ 0 [ZMOD PMOD]
      | .first      => isFirst = true → w.body.eval env ≡ 0 [ZMOD PMOD]
      | .last       => isLast = true → w.body.eval env ≡ 0 [ZMOD PMOD]
  | .chal c   =>
      match c.sel with
      | .transition => isLast = false → c.body.eval env ≡ 0 [ZMOD PMOD]
      | .all        => c.body.eval env ≡ 0 [ZMOD PMOD]
      | .first      => True
      | .last       => True
  | .bind b   =>
      (b.guard.eval env.loc * (b.guard.eval env.loc - 1) ≡ 0 [ZMOD PMOD])
      ∧ (∀ vs, b.vkPin = some vs →
            zeroLanes (b.guard.eval env.loc) (b.vk.map (fun e => e.eval env.loc)) vs)
      ∧ (∀ bs, b.bound = .bound bs →
            zeroLanes (b.guard.eval env.loc) (b.commit.map (fun e => e.eval env.loc))
              (bs.map (fun e => e.eval env.loc)))

/-! ### §1a — ⚑ THE TIE VERDICT'S VOCABULARY: which columns a leg DERIVES.

Kept here with the IR rather than with the lowering, for the same reason `forces` is: it is a fact
about the source. §7 is what it buys. -/

/-- Columns an expression reads. -/
def exprCols : Expr → List Nat
  | .var v   => [v]
  | .const _ => []
  | .add a b => exprCols a ++ exprCols b
  | .mul a b => exprCols a ++ exprCols b

/-- Columns a window body reads; `loc c` and `nxt c` are the same column. -/
def windowCols : WindowExpr → List Nat
  | .loc c   => [c]
  | .nxt c   => [c]
  | .const _ => []
  | .add a b => windowCols a ++ windowCols b
  | .mul a b => windowCols a ++ windowCols b

/-- Columns a challenge body reads. ⚑ `.chal i` contributes NOTHING: a challenge is not a column,
and folding it in would connect every challenge gate through a phantom node. -/
def chalCols : ChalExpr → List Nat
  | .loc c   => [c]
  | .nxt c   => [c]
  | .const _ => []
  | .chal _  => []
  | .add a b => chalCols a ++ chalCols b
  | .mul a b => chalCols a ++ chalCols b

/-- ⚑ **The columns a LEG relates — and `pin` contributes `[]`, on purpose.** A pin ties a column
to a PUBLIC INPUT, not to another column: it publishes, it does not derive. That asymmetry is the
defect being measured, so it is written into the IR rather than discovered by a census afterwards
(`LightClientAnchorConnectivity.relatedCols` is the same choice, one rail down).

⚑⚑ **`.bind` IS ANSWERED AT THE EMISSION, NOT AT THE DECLARATION (2026-08-08).** This arm used to
return a bind leg's whole IR surface — guard, `commit`, `vk`, `bound` — while the deployed
evaluator (`descriptor_ir2.rs`, `VmConstraint2::ProofBind`) emits polynomials over `vk` only under
a `vkPin` and over `commit` only under a `bound`. Every served Mina light-client seam is
`bound := none`, so `pinsTied` scored their commit lanes as READ by their own DECLARATION — the
verdict passed THROUGH the object it was supposed to judge, and `minaLinkTiedAir` carried a "tied"
`BODY_ACC` block that appeared in NO emitted polynomial. Same reading, same day, as
`Seam.legJoinsAcross`'s `.bind` arm and `LightClientAnchorConnectivity.relatedCols`' `.proofBind`
arm (whose confession moved mina-verify decorative 9 → 36, mina-link 0 → 17, census 53 → 80): one
entry per emitted polynomial. ⚠ THE RED WAS TAKEN, NOT SOFTENED: `minaHeadAir` and `minaLinkAir`
now FAIL `pinsTied` (their commitment/body ports are published-but-underived, which is the truth —
their forcing is the executor welds `MinaSeams` censuses), their `TiedAir`s are demoted to
`lowerAirCertified` at identical bytes, and `PinsTiedCensus` counts them with the reason. -/
def AirLeg.readCols : AirLeg → List Nat
  | .gate c   => exprCols c.lhs ++ exprCols c.rhs
  | .pin _    => []
  | .lookup l => l.tuple.flatMap exprCols
  | .limbs l  => l.cols
  | .window w => windowCols w.body
  | .chal c   => chalCols c.body
  | .bind b   =>
      -- guard·(guard−1) is always emitted; guard·(vkᵢ−pinᵢ) only under a `vkPin`;
      -- guard·(commitᵢ−boundᵢ) only under a `bound`. A declared-but-unemitted vector reads nothing.
      exprCols b.guard
        ++ (if b.vkPin.isSome then b.vk.flatMap exprCols else [])
        ++ (match b.bound with
            | .port _   => []
            | .bound bs => b.commit.flatMap exprCols ++ bs.flatMap exprCols)

/-- ⚑ **A leg JOINS iff it relates at least two distinct columns.** An arity-1 range lookup and a
one-column forcing gate both fail this, and both should: neither ties its column to anything. -/
def AirLeg.joins (l : AirLeg) : Bool := 2 ≤ l.readCols.eraseDups.length

/-- ⚑ **THE TIE VERDICT — every published column is DERIVED by some other leg.** The `mainRailOk`
shape, applied to the defect `mainRailOk` cannot see. Decidable, on the source, before any byte. -/
def EffectAir.pinsTied (air : EffectAir) : Bool :=
  air.legs.all fun l =>
    match l with
    | .pin p => air.legs.any (fun m => p.col ∈ m.readCols)
    | _      => true

/-- ⚑ …and the STRICTER form: the pinned column must be tied by a leg that JOINS it to another
column. The gap between the two verdicts is exactly the unary-thread class of §7. -/
def EffectAir.pinsJoined (air : EffectAir) : Bool :=
  air.legs.all fun l =>
    match l with
    | .pin p => air.legs.any (fun m => m.joins && p.col ∈ m.readCols)
    | _      => true

/-! ### §1c — ⚑ THE TIE VERDICT COMPOSES, so it does not have to be RE-DECIDED per boundary.

Every emitted row in the Pasta/Mina cone is assembled the same way: a reusable MACHINE block whose
legs mention no public input, plus a BOUNDARY of `pin` legs that turns the machine into a statement.
`pinsTied` on the assembled block is `O(pins × legs)` in the kernel, and the deployed transcript
rows are 192–256 pins over 643–707 legs — a `by decide` that costs minutes and has to be paid again
at every new boundary.

⚠ And re-deciding is not only slow, it is the WRONG OBJECT. The fact does not depend on the pin
COUNT or on the pin ROWS; it depends on each pinned COLUMN being read by a leg of the machine. Said
that way it is proved ONCE, generally, and every boundary that reuses the machine inherits it. -/

/-- **The obligation `pinsTied` actually imposes on one pin**, named: some leg of the block READS
the column the pin publishes. `readCols` is the emission-faithful walk, so this is a claim about
polynomials that exist, not about declarations. -/
def EffectAir.readsCol (air : EffectAir) (col : Nat) : Bool :=
  air.legs.any (fun m => col ∈ m.readCols)

/-- ⚑ **THE TIE VERDICT COMPOSES OVER AN APPENDED BOUNDARY.** If the machine block is tied and
every appended pin's column is read by the MACHINE, the assembled block is tied.

⚑ Note which direction the hypothesis runs: the reader must be a leg of `air`, not of the appended
boundary. A boundary that "tied" its own pins by pinning them twice would not discharge this — and
it could not, because `AirLeg.readCols` of a `pin` is `[]` on purpose. That asymmetry is what stops
this lemma from being a way to launder a decorative pin through a composition. -/
theorem EffectAir.pinsTied_append (air : EffectAir) (pins : List AirLeg)
    (hair : air.pinsTied = true)
    (hpins : ∀ p : PiPinLeg, AirLeg.pin p ∈ pins → air.readsCol p.col = true) :
    ({ air with legs := air.legs ++ pins } : EffectAir).pinsTied = true := by
  simp only [EffectAir.pinsTied, List.all_eq_true] at hair
  have key : ∀ p : PiPinLeg, AirLeg.pin p ∈ air.legs ++ pins →
      ((air.legs ++ pins).any fun m => p.col ∈ m.readCols) = true := by
    intro p hp
    have hbase : (air.legs.any fun m => p.col ∈ m.readCols) = true := by
      rcases List.mem_append.mp hp with h | h
      · exact hair _ h
      · exact hpins p h
    rw [List.any_append, hbase, Bool.true_or]
  refine List.all_eq_true.mpr (fun l hl => ?_)
  cases l with
  | pin p => exact key p hl
  | gate _ => rfl
  | lookup _ => rfl
  | window _ => rfl
  | limbs _ => rfl
  | chal _ => rfl
  | bind _ => rfl

/-- **A block with no `pin` leg is vacuously tied.** The machine half of the composition above,
so a caller never has to `decide` the machine's own verdict either. -/
theorem EffectAir.pinsTied_of_no_pins (air : EffectAir)
    (h : ∀ p : PiPinLeg, AirLeg.pin p ∉ air.legs) : air.pinsTied = true := by
  simp only [EffectAir.pinsTied, List.all_eq_true]
  intro l hl
  cases l with
  | pin p => exact absurd hl (h p)
  | gate _ => rfl
  | lookup _ => rfl
  | window _ => rfl
  | limbs _ => rfl
  | chal _ => rfl
  | bind _ => rfl

end Dregg2.Circuit.EffectAirIR

namespace Dregg2.Circuit.Emit.EffectLower

open Dregg2.Circuit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv VmRange)
open Dregg2.Exec.CircuitEmit (EmittedExpr emitExpr emitExpr_eval)
open Dregg2.Circuit.EffectAirIR
  (EffectAir AirLeg ChalLeg BindLeg LookupLeg WindowLeg RangeLeg PiPinLeg LimbsLeg exprIsOne
   chalReadsNext PMOD)
open Dregg2.Circuit.TableAirIR (BusOp RowSel readsNext)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §2 — the bridges the per-leg lemmas cross.

Each of these is a place the source grammar and the target grammar genuinely differ. If any were
`rfl` the refinement would be a restatement. -/

/-- Emitting a source tuple and evaluating it is evaluating it in the source grammar. This is the
`lookup`/`bind` bridge; `CircuitEmit.emitExpr_eval` is its one-expression form. -/
theorem map_emit_eval (ts : List Expr) (a : Assignment) :
    (ts.map emitExpr).map (fun e => e.eval a) = ts.map (fun e => e.eval a) := by
  simp [List.map_map, Function.comp_def, emitExpr_eval]

/-- ⚑ **A body that does not read the next row HAS a row-local form.** `windowToLocal?` is a
genuinely partial conversion; `WindowLeg.mainRailOk` at `.all`/`.first`/`.last` is
`!readsNext body`, and this is what turns that decidable verdict into the totality the lowering
needs. Without it the boundary arms could only be proved by case-splitting on a conversion that
might fail — i.e. not at all. -/
theorem windowToLocal_isSome_of_not_readsNext :
    ∀ (w : WindowExpr), readsNext w = false → (windowToLocal? w).isSome = true := by
  intro w
  induction w with
  | loc c => intro _; rfl
  | nxt c => intro h; simp [readsNext] at h
  | const k => intro _; rfl
  | add a b iha ihb =>
      intro h
      simp only [readsNext, Bool.or_eq_false_iff] at h
      have ha := iha h.1
      have hb := ihb h.2
      cases hxa : windowToLocal? a with
      | none => rw [hxa] at ha; simp at ha
      | some x =>
        cases hxb : windowToLocal? b with
        | none => rw [hxb] at hb; simp at hb
        | some y => simp [windowToLocal?, hxa, hxb]
  | mul a b iha ihb =>
      intro h
      simp only [readsNext, Bool.or_eq_false_iff] at h
      have ha := iha h.1
      have hb := ihb h.2
      cases hxa : windowToLocal? a with
      | none => rw [hxa] at ha; simp at ha
      | some x =>
        cases hxb : windowToLocal? b with
        | none => rw [hxb] at hb; simp at hb
        | some y => simp [windowToLocal?, hxa, hxb]

/-! ## §3 — ⚑ THE PER-LEG REFINEMENT LEMMAS. One per constructor, each NAMED.

Every one has the same shape and it is the shape the design turns on:

    the leg is main-rail expressible  →  its lowered constraints hold on a row window
                                      →  the leg's own claim holds on that row window

`hok` is `mainRailOk`, the verdict that already exists. That is the sense in which `mainRailOk` is
a degenerate instance of this design rather than a separate mechanism. -/

variable (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)

/-- **GATE.** The lowered gate on the transition domain IS the source equation, mod `p`. This is
`lowerConstraint_holdsAt_iff` lifted to the leg. -/
theorem lowerLeg_forces_gate (c : Constraint)
    (h : ∀ vc ∈ lowerLeg (.gate c), vc.holdsAt hash tf env isFirst isLast) :
    (AirLeg.gate c).forces tf env isFirst isLast := by
  show isLast = false → _
  intro hlast
  subst hlast
  exact (lowerConstraint_holdsAt_iff hash tf env isFirst c).mp
    (h (lowerConstraint c) (by simp [lowerLeg]))

/-- **PIN.** The lowered `piBinding` forces the column/slot congruence exactly on the pin's row —
the fact `holdsVm_piFirst_true` states about the TARGET constructor, here stated about the LEG. It
is used 88 times in the tree, re-derived at each site. -/
theorem lowerLeg_forces_pin (p : PiPinLeg)
    (h : ∀ vc ∈ lowerLeg (.pin p), vc.holdsAt hash tf env isFirst isLast) :
    (AirLeg.pin p).forces tf env isFirst isLast := by
  obtain ⟨row, col, idx⟩ := p
  have hmem := h (VmConstraint2.base (.piBinding row col idx))
    (by simp [lowerLeg, lowerPiPinLeg])
  show PiPinLeg.fires _ isFirst isLast = true → _
  cases row with
  | first =>
      intro hf
      simp only [PiPinLeg.fires] at hf
      subst hf
      exact hmem rfl
  | last =>
      intro hf
      simp only [PiPinLeg.fires] at hf
      subst hf
      exact hmem rfl

/-- **LOOKUP.** The queried tuple, evaluated in the SOURCE grammar, is a row of the table. Crosses
`emitExpr` — the lowering carries tuples through the serializer, not the `Head` normalizer. -/
theorem lowerLeg_forces_lookup (l : LookupLeg) (hok : l.mainRailOk = true)
    (h : ∀ vc ∈ lowerLeg (.lookup l), vc.holdsAt hash tf env isFirst isLast) :
    (AirLeg.lookup l).forces tf env isFirst isLast := by
  have hmem := h (VmConstraint2.lookup ⟨l.table, l.tuple.map emitExpr⟩)
    (by simp [lowerLeg, lowerLookupLeg, hok])
  show (l.tuple.map (fun e => e.eval env.loc)) ∈ tf l.table
  simpa only [VmConstraint2.holdsAt, Lookup.holdsAt, map_emit_eval] using hmem

/-- **LIMBS.** ⚑ ONE claim PER LIMB, so a dropped limb is visible in the denotation and not only in
the constraint count. `LimbsLeg.mainRailOk` already refuses the empty vector and any width above
the wrap-free ceiling 29; this is what those refusals buy. -/
theorem lowerLeg_forces_limbs (l : LimbsLeg) (hok : l.mainRailOk = true)
    (h : ∀ vc ∈ lowerLeg (.limbs l), vc.holdsAt hash tf env isFirst isLast) :
    (AirLeg.limbs l).forces tf env isFirst isLast := by
  show ∀ c ∈ l.cols, _
  intro c hc
  have hmem : (VmConstraint2.lookup ⟨l.table, [EmittedExpr.var c]⟩) ∈ lowerLeg (.limbs l) := by
    simp only [lowerLeg, lowerLimbsLeg, hok, if_true]
    exact List.mem_map_of_mem hc
  have hh := h _ hmem
  simpa only [VmConstraint2.holdsAt, Lookup.holdsAt, List.map_cons, List.map_nil,
    EmittedExpr.eval] using hh

/-- **WINDOW.** The four-way `RowSel` against a target with two shapes, and the dispatch is the
content: `.transition`/`.all` land on `windowGate`'s `onTransition` flag, `.first`/`.last` on a
`boundary` whose body is the ROW-LOCAL conversion — so this arm crosses `windowToLocal_eval` as
well as the dispatch. -/
theorem lowerLeg_forces_window (w : WindowLeg) (hok : w.mainRailOk = true)
    (h : ∀ vc ∈ lowerLeg (.window w), vc.holdsAt hash tf env isFirst isLast) :
    (AirLeg.window w).forces tf env isFirst isLast := by
  show (match w.sel with
        | .transition => isLast = false → w.body.eval env ≡ 0 [ZMOD PMOD]
        | .all        => w.body.eval env ≡ 0 [ZMOD PMOD]
        | .first      => isFirst = true → w.body.eval env ≡ 0 [ZMOD PMOD]
        | .last       => isLast = true → w.body.eval env ≡ 0 [ZMOD PMOD])
  cases hs : w.sel with
  | transition =>
      have hmem := h (VmConstraint2.windowGate ⟨w.body, true⟩)
        (by simp [lowerLeg, lowerWindowLeg, hs])
      show isLast = false → w.body.eval env ≡ 0 [ZMOD PMOD]
      simpa only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, if_pos] using hmem
  | all =>
      have hnr : readsNext w.body = false := by
        simp only [WindowLeg.mainRailOk, hs, Bool.not_eq_true'] at hok; exact hok
      have hsome := windowToLocal_isSome_of_not_readsNext w.body hnr
      cases hx : windowToLocal? w.body with
      | none => rw [hx] at hsome; simp at hsome
      | some b =>
          have hmem := h (VmConstraint2.windowGate ⟨w.body, false⟩)
            (by simp [lowerLeg, lowerWindowLeg, hs, hx])
          show w.body.eval env ≡ 0 [ZMOD PMOD]
          simpa only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, if_neg, Bool.false_eq_true,
            ↓reduceIte] using hmem
  | first =>
      have hnr : readsNext w.body = false := by
        simp only [WindowLeg.mainRailOk, hs, Bool.not_eq_true'] at hok; exact hok
      have hsome := windowToLocal_isSome_of_not_readsNext w.body hnr
      cases hx : windowToLocal? w.body with
      | none => rw [hx] at hsome; simp at hsome
      | some b =>
          have hmem := h (VmConstraint2.base (.boundary VmRow.first b))
            (by simp [lowerLeg, lowerWindowLeg, hs, hx])
          show isFirst = true → w.body.eval env ≡ 0 [ZMOD PMOD]
          intro hf
          have hb := hmem hf
          rwa [windowToLocal_eval env w.body b hx] at hb
  | last =>
      have hnr : readsNext w.body = false := by
        simp only [WindowLeg.mainRailOk, hs, Bool.not_eq_true'] at hok; exact hok
      have hsome := windowToLocal_isSome_of_not_readsNext w.body hnr
      cases hx : windowToLocal? w.body with
      | none => rw [hx] at hsome; simp at hsome
      | some b =>
          have hmem := h (VmConstraint2.base (.boundary VmRow.last b))
            (by simp [lowerLeg, lowerWindowLeg, hs, hx])
          show isLast = true → w.body.eval env ≡ 0 [ZMOD PMOD]
          intro hf
          have hb := hmem hf
          rwa [windowToLocal_eval env w.body b hx] at hb

/-- **CHAL.** Same dispatch, onto the target's two-row-only challenge form. The `.first`/`.last`
scopes have no image at all and `mainRailOk` refuses them, so this proof never reaches them. -/
theorem lowerLeg_forces_chal (c : ChalLeg) (hok : c.mainRailOk = true)
    (h : ∀ vc ∈ lowerLeg (.chal c), vc.holdsAt hash tf env isFirst isLast) :
    (AirLeg.chal c).forces tf env isFirst isLast := by
  show (match c.sel with
        | .transition => isLast = false → c.body.eval env ≡ 0 [ZMOD PMOD]
        | .all        => c.body.eval env ≡ 0 [ZMOD PMOD]
        | .first      => True
        | .last       => True)
  cases hs : c.sel with
  | transition =>
      have hmem := h (VmConstraint2.chalGate ⟨c.body, true⟩)
        (by simp [lowerLeg, lowerChalLeg, hs])
      show isLast = false → c.body.eval env ≡ 0 [ZMOD PMOD]
      simpa only [VmConstraint2.holdsAt, ChalConstraint.holdsAt, if_pos] using hmem
  | all =>
      have hnr : chalReadsNext c.body = false := by
        simp only [ChalLeg.mainRailOk, hs, Bool.not_eq_true'] at hok; exact hok
      have hmem := h (VmConstraint2.chalGate ⟨c.body, false⟩)
        (by simp [lowerLeg, lowerChalLeg, hs, hnr])
      show c.body.eval env ≡ 0 [ZMOD PMOD]
      simpa only [VmConstraint2.holdsAt, ChalConstraint.holdsAt, if_neg, Bool.false_eq_true,
        ↓reduceIte] using hmem
  | first => show True; trivial
  | last => show True; trivial

/-- **BIND.** ⚑ The recursion seam, LANE BY LANE. `BindLeg.mainRailOk` refuses the declarative
shape (pins neither program nor commitment), a seam narrower than `PROOF_BIND_MIN_LANES`, and a pin
shorter than the vector it pins; what survives forces the guard bit and the declared lane ties. -/
theorem lowerLeg_forces_bind (b : BindLeg) (hok : b.mainRailOk = true)
    (h : ∀ vc ∈ lowerLeg (.bind b), vc.holdsAt hash tf env isFirst isLast) :
    (AirLeg.bind b).forces tf env isFirst isLast := by
  have hmem := h (VmConstraint2.proofBind
      ⟨emitExpr b.guard, b.commit.map emitExpr, b.vk.map emitExpr, b.vkPin,
       b.bound.map emitExpr⟩)
    (by simp [lowerLeg, lowerBindLeg, hok])
  simp only [VmConstraint2.holdsAt, ProofBind.holdsAt] at hmem
  obtain ⟨hg, hvk, hbd⟩ := hmem
  rw [emitExpr_eval] at hg
  refine ⟨hg, ?_, ?_⟩
  · intro vs hvs
    rw [hvs] at hvk
    rw [emitExpr_eval] at hvk
    simpa only [map_emit_eval] using hvk
  · intro bs hbs
    rw [hbs] at hbd
    rw [emitExpr_eval] at hbd
    simpa only [CommitBindingOf.map, map_emit_eval] using hbd

/-- ⚑ **THE COMBINED PER-LEG LEMMA.** Every leg kind, one statement. -/
theorem lowerLeg_forces (l : AirLeg) (hok : l.mainRailOk = true)
    (h : ∀ vc ∈ lowerLeg l, vc.holdsAt hash tf env isFirst isLast) :
    l.forces tf env isFirst isLast := by
  cases l with
  | gate c   => exact lowerLeg_forces_gate hash tf env isFirst isLast c h
  | pin p    => exact lowerLeg_forces_pin hash tf env isFirst isLast p h
  | lookup q => exact lowerLeg_forces_lookup hash tf env isFirst isLast q hok h
  | limbs q  => exact lowerLeg_forces_limbs hash tf env isFirst isLast q hok h
  | window w => exact lowerLeg_forces_window hash tf env isFirst isLast w hok h
  | chal c   => exact lowerLeg_forces_chal hash tf env isFirst isLast c hok h
  | bind b   => exact lowerLeg_forces_bind hash tf env isFirst isLast b hok h

/-! ## §4 — ⚑ COMPOSITION. The part that makes it a design rather than seven lemmas.

`lowerAirLegs` is a `flatMap`, so leg membership and constraint membership compose by
`List.mem_flatMap`; `EffectAir.mainRailOk` is a `List.all`, so the per-leg verdict composes by
`List.all_eq_true`. Neither step knows anything about any leg kind: adding an eighth constructor
costs one arm of `forces` and one per-leg lemma, and this section is unchanged. -/

/-- **The air block's legs are all forced.** -/
theorem lowerAirLegs_forces (air : EffectAir) (hok : air.mainRailOk = true)
    (h : ∀ vc ∈ lowerAirLegs air, vc.holdsAt hash tf env isFirst isLast) :
    ∀ l ∈ air.legs, l.forces tf env isFirst isLast := by
  intro l hl
  refine lowerLeg_forces hash tf env isFirst isLast l ?_ (fun vc hvc => h vc ?_)
  · exact (List.all_eq_true.mp hok) l hl
  · exact List.mem_flatMap.mpr ⟨l, hl, hvc⟩

/-- **…and so are the flat guard gates**, on the transition domain. Together with the above this is
everything `assemble` put in front of the caller's `framePins`. -/
theorem lowerAir_forces_gates (name : String) (traceWidth piCount : Nat) (cs : ConstraintSystem)
    (air : EffectAir)
    (h : ∀ vc ∈ (lowerAir name traceWidth piCount cs air).constraints,
          vc.holdsAt hash tf env isFirst isLast) :
    ∀ c ∈ cs, isLast = false → c.lhs.eval env.loc ≡ c.rhs.eval env.loc [ZMOD PMOD] := by
  intro c hc hlast
  subst hlast
  refine (lowerConstraint_holdsAt_iff hash tf env isFirst c).mp (h _ ?_)
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hc))

/-- **The descriptor's constraints force every leg.** The air legs sit in the middle of
`gates ++ legs ++ framePins`, so leg membership lifts to descriptor membership by two appends. -/
theorem lowerAir_forces (name : String) (traceWidth piCount : Nat) (cs : ConstraintSystem)
    (air : EffectAir) (hok : air.mainRailOk = true)
    (h : ∀ vc ∈ (lowerAir name traceWidth piCount cs air).constraints,
          vc.holdsAt hash tf env isFirst isLast) :
    ∀ l ∈ air.legs, l.forces tf env isFirst isLast := by
  refine lowerAirLegs_forces hash tf env isFirst isLast air hok (fun vc hvc => h vc ?_)
  exact List.mem_append_left _ (List.mem_append_right _ hvc)

/-! ## §5 — ⚑ THE CERTIFIED ENTRY POINT. `lowerAir` that returns its own soundness.

The dependent pair is the whole proposal in one definition: a caller cannot obtain the descriptor
without obtaining the proof, and cannot obtain the proof for an air block `mainRailOk` refuses.

⚑ **ADOPTION IS FREE.** `.val` is `lowerAir` by `rfl`, so a descriptor that switches to this emits
identical bytes; nothing re-emits, no VK rotates. What changes is that the emit does not ELABORATE
for an air block whose verdict is false — the discipline `PiDeclaration.withPiManifest` applies to
public inputs, applied to the lowering itself. -/

/-- **What a certified lowering promises**, spelled as a `Prop` so the pair's type is readable and
so a consumer can name the obligation without unfolding the subtype. -/
def CertifiedRefines (d : EffectVmDescriptor2) (cs : ConstraintSystem) (air : EffectAir) : Prop :=
  ∀ (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool),
    (∀ vc ∈ d.constraints, vc.holdsAt hash tf env isFirst isLast) →
      (∀ l ∈ air.legs, l.forces tf env isFirst isLast)
      ∧ (∀ c ∈ cs, isLast = false → c.lhs.eval env.loc ≡ c.rhs.eval env.loc [ZMOD PMOD])

/-- ⚑ **`lowerAirCertified` — the descriptor AND the proof that it refines its source.** -/
def lowerAirCertified (name : String) (traceWidth piCount : Nat) (cs : ConstraintSystem)
    (air : EffectAir) (hok : air.mainRailOk = true) :
    { d : EffectVmDescriptor2 // CertifiedRefines d cs air } :=
  ⟨lowerAir name traceWidth piCount cs air,
   fun hash tf env isFirst isLast h =>
     ⟨lowerAir_forces hash tf env isFirst isLast name traceWidth piCount cs air hok h,
      lowerAir_forces_gates hash tf env isFirst isLast name traceWidth piCount cs air h⟩⟩

/-- **The certificate costs no byte.** -/
theorem lowerAirCertified_val (name : String) (traceWidth piCount : Nat) (cs : ConstraintSystem)
    (air : EffectAir) (hok : air.mainRailOk = true) :
    (lowerAirCertified name traceWidth piCount cs air hok).val
      = lowerAir name traceWidth piCount cs air := rfl

/-! ## §6 — ⚑ BOTH POLES, on a concrete row. `forces` is a real predicate, not a tautology.

If `AirLeg.forces` were "the lowered constraints hold" it would be unrefutable. It is refutable. -/

/-- A pin publishing column 3 at slot 1, on the first row. -/
def demoPinLeg : PiPinLeg := ⟨VmRow.first, 3, 1⟩

/-- A row whose column 3 is `7` and whose slot 1 is `7` — the pin's claim HOLDS. -/
def demoEnvOk : VmRowEnv :=
  { loc := fun c => if c = 3 then 7 else 0
  , nxt := fun _ => 0
  , pub := fun k => if k = 1 then 7 else 0
  , chal := fun _ => 0 }

/-- The SAME row with the published slot moved to `8` — the pin's claim is FALSE. -/
def demoEnvForged : VmRowEnv := { demoEnvOk with pub := fun k => if k = 1 then 8 else 0 }

/-- **THE HONEST POLE.** -/
theorem demoPin_forces_holds (tf : TraceFamily) :
    (AirLeg.pin demoPinLeg).forces tf demoEnvOk true false := by
  show _ = true → _
  intro _
  decide

/-- ⚑ **THE RED POLE — `forces` is FALSE on the forged row.** Refuted by the kernel, so the
predicate has content: the certified lowering is not carrying a tautology. -/
theorem demoPin_forces_refuted (tf : TraceFamily) :
    ¬ (AirLeg.pin demoPinLeg).forces tf demoEnvForged true false := by
  intro h
  have hx : (demoEnvForged.loc 3 ≡ demoEnvForged.pub 1 [ZMOD PMOD]) := h rfl
  revert hx
  decide

/-- …and the forged row is refused by the EMITTED constraint too, which is the other half: the
predicate that goes false corresponds to a descriptor that rejects. -/
theorem demoPin_descriptor_rejects (hash : List ℤ → ℤ) (tf : TraceFamily) :
    ¬ (∀ vc ∈ lowerLeg (.pin demoPinLeg), vc.holdsAt hash tf demoEnvForged true false) := by
  intro h
  exact demoPin_forces_refuted tf
    (lowerLeg_forces_pin hash tf demoEnvForged true false demoPinLeg h)

/-! ## §7 — ⚑ THE DEFECT THE REFINEMENT CANNOT SEE, made structural instead.

`lowerAirCertified` makes a descriptor force what its legs SAY. It is structurally incapable of
noticing a leg that says the wrong thing — and the corpus's largest measured defect is exactly
that: a `pin` leg's claim (`loc col ≡ pub idx`) is TRUE of a column nothing else constrains, so the
prover chooses both sides and the refinement is faithful and worthless.

Measured on the emitted corpus 2026-08-06 (`circuit/descriptors/by-name/*.json`, 111 descriptors,
3,912 pins): **157 pins publish a column NO other constraint reads**, and **97 of 111 descriptors
would pass `pinsTied` unchanged**. Under the stricter joins-≥-2-columns reading
(`LightClientAnchorConnectivity.decorativeAnchors`, whose armed baseline is 417) the count is
larger and the largest single row is 192 of 219 published felts.
⚑ **RE-MEASURED 2026-08-08 with the emission-faithful `.bind` arm above: 95 pass / 16 fail on
183 pins** — the 2026-08-06 numbers were taken by a walker that read seam DECLARATIONS as reads;
the two rows the fix moved are the Mina light-client pair, classified with their host welds in
`PinsTiedCensus`'s dated confession.

So the answer is not a better refinement lemma. It is a SECOND decidable verdict, in the same shape
as `mainRailOk`, on the SOURCE — where a pin can still be refused before any byte exists. -/

/-- ⚑ **`TiedAir` — DECORATION IS UNREPRESENTABLE.** Not detectable: unrepresentable. A value of
this type cannot be built for an air block that publishes a column no other leg derives, because
the field is a proof obligation and the `by decide` default fails.

That is the difference from a census: a census reports a number after the fact, and every one of
the measured decorative felts was found by a census after the fact. -/
structure TiedAir where
  air  : EffectAir
  /-- Main-rail expressible. -/
  ok   : air.mainRailOk = true := by decide
  /-- ⚑ Every published column is derived by another leg. -/
  tied : air.pinsTied = true := by decide

/-- **The certified lowering of a tied air block** — the two verdicts and the refinement, together,
in the type of the emit. -/
def lowerTiedAir (name : String) (traceWidth piCount : Nat) (cs : ConstraintSystem) (t : TiedAir) :
    { d : EffectVmDescriptor2 // CertifiedRefines d cs t.air } :=
  lowerAirCertified name traceWidth piCount cs t.air t.ok

theorem lowerTiedAir_val (name : String) (traceWidth piCount : Nat) (cs : ConstraintSystem)
    (t : TiedAir) :
    (lowerTiedAir name traceWidth piCount cs t).val
      = lowerAir name traceWidth piCount cs t.air := rfl

/-! ### §7a — both poles of the tie verdict. A verdict that cannot go red is decoration. -/

/-- A gate deriving column `3` from column `2`, plus a pin publishing `3`. The pin is TIED. -/
def demoTiedAir : EffectAir :=
  { legs := [ .gate ⟨.var 3, .var 2⟩, .pin ⟨VmRow.first, 3, 0⟩ ] }

/-- ⚑ **THE RED POLE** — the SAME pin with the gate deleted. Byte-wise this still publishes public
input `0`; nothing about the emitted pin changed. Its column is now derived by nothing, and the
verdict says so. -/
def demoDecorativeAir : EffectAir :=
  { legs := [ .pin ⟨VmRow.first, 3, 0⟩ ] }

theorem demoTiedAir_tied : demoTiedAir.pinsTied = true := by decide
theorem demoDecorativeAir_untied : demoDecorativeAir.pinsTied = false := by decide

/-- …and BOTH are main-rail expressible, which is the point: `mainRailOk` cannot see this defect,
so the verdict had to be a second one rather than a widening of the first. -/
theorem both_pass_mainRailOk :
    demoTiedAir.mainRailOk = true ∧ demoDecorativeAir.mainRailOk = true := by decide

/-- ⚑ **THE UNARY-THREAD CLASS, exhibited.** A window gate whose body reads ONE column
(`nxt 3 − loc 3`) ties column `3` to nothing — the shape the 192 published ξ-basis felts carry. It
passes `pinsTied` (the column IS read) and fails `pinsJoined` (nothing is joined to it). The two
verdicts disagree here, and the disagreement IS the measured defect. -/
def demoUnaryThreadAir : EffectAir :=
  { legs := [ .window ⟨RowSel.transition, .add (.nxt 3) (.mul (.const (-1)) (.loc 3))⟩
            , .pin ⟨VmRow.first, 3, 0⟩ ] }

theorem demoUnaryThread_passes_tied : demoUnaryThreadAir.pinsTied = true := by decide

theorem demoUnaryThread_fails_joined : demoUnaryThreadAir.pinsJoined = false := by decide

/-- The genuinely tied block passes BOTH. -/
theorem demoTiedAir_joined : demoTiedAir.pinsJoined = true := by decide

/-! ## §8 — axiom-hygiene tripwires. -/

#assert_axioms map_emit_eval
#assert_axioms windowToLocal_isSome_of_not_readsNext
#assert_axioms lowerLeg_forces_gate
#assert_axioms lowerLeg_forces_pin
#assert_axioms lowerLeg_forces_lookup
#assert_axioms lowerLeg_forces_limbs
#assert_axioms lowerLeg_forces_window
#assert_axioms lowerLeg_forces_chal
#assert_axioms lowerLeg_forces_bind
#assert_axioms lowerLeg_forces
#assert_axioms lowerAirLegs_forces
#assert_axioms lowerAir_forces_gates
#assert_axioms lowerAir_forces
#assert_axioms lowerAirCertified_val
#assert_axioms demoPin_forces_holds
#assert_axioms demoPin_forces_refuted
#assert_axioms demoPin_descriptor_rejects
#assert_axioms demoTiedAir_tied
#assert_axioms demoDecorativeAir_untied
#assert_axioms both_pass_mainRailOk
#assert_axioms demoUnaryThread_passes_tied
#assert_axioms demoUnaryThread_fails_joined
#assert_axioms demoTiedAir_joined
#assert_axioms lowerTiedAir_val
#assert_axioms Dregg2.Circuit.EffectAirIR.EffectAir.pinsTied_append
#assert_axioms Dregg2.Circuit.EffectAirIR.EffectAir.pinsTied_of_no_pins

end Dregg2.Circuit.Emit.EffectLower
