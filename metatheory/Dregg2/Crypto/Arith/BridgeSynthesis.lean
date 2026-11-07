/-
# Dregg2.Crypto.Arith.BridgeSynthesis — MVP-2 step A: the Formula-fold Iff synthesizer.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Every object here is a proof ABOUT the
`Program` / `EffectVmDescriptor2` produced by `TypedLinearPredicateDescriptorIR2`, a Lean function;
no Rust hand-writes any of it. This file adds NO field-value computation — nothing here reduces a
`ZMod 2013265921` at a concrete input, and nothing constructs a `Decidable` instance on a `ZMod p`
predicate. The reflection is over the `Formula`/`AffineTerm` SYNTAX; the field input stays symbolic.

## What this file synthesizes

`#arithmetizeTypedRefinement` requires a caller-supplied `bridge : ∀ input, p.Holds input ↔ Spec`.
Per `docs/DESIGN-bridge-synthesis-mvp2.md`, the bridge is a composition of three obligations and
exactly the first two are synthesizable:

```
  p.Holds input                    ↔   canonForm p input   ↔   arbitrary user Spec
  └── (A) Formula fold ────────────┘   └── (C) prose link ──┘
      (B) per-atom canonicalization        (MANUAL, often Iff.rfl)
```

`p.Holds input` unfolds to `Formula.Holds (p.AtomTruth input) p.source`, a Boolean combination of
atom-truth leaves `(atomTerms a).evalField input = 0`. `holds_iff_canonForm` synthesizes (A)+(B):

* (A) the fold `Formula.Holds truth₁ f ↔ Formula.Holds truth₂ f` under a leafwise Iff is the
  structural congruence `holds_congr` — one induction on the concrete `source`, no field touched.
* (B) each affine leaf is canonicalized by `canonAtom` with the fixed `linear_combination` schema
  proven once in `canonAtom_iff` (`input i + c = 0 ↔ input i = -c`); unrecognized shapes fall
  through to the raw affine equation (still exact — `Iff.rfl`), so the canonicalizer is TOTAL.

The command `#arithmetizeTypedCanonical foo := prog` emits the SYNTHESIZED bridge and, composing it
with `sound` / `canonical_iff` from the MVP-1 file, the spec bundle with ZERO caller obligation:
`foo_holds_canon`, `foo_spec_sound : LiveRefinesSpec foo_program (canonForm foo_program)`,
`foo_spec_exact`.

## HONEST SCOPE — do not upgrade these sentences

* Only (A)+(B) are synthesized. The `canonForm ↔ arbitrary-prose-Spec` link (C) STAYS MANUAL — when
  the caller lets their spec BE the canonical form it collapses to `Iff.rfl`, otherwise it is a
  small felt-free / fold-free `Iff` the elaborator cannot read out of unstructured prose.
* `canonAtom` "solves" the `eqConst`/bare-`input` shapes that every in-tree witness uses; a general
  affine atom has no field-safe pivot and canonicalizes to itself (still correct, not simplified).
* Everything inherits the descriptor-level FRI/STARK and witness-generator floor exactly as every
  other theorem in this tree — a synthesized bridge is a program-level `Iff`, no new soundness.

## Pilot

`InterchainRung.program_holds_iff` (the one fully-worked hand `Holds`-bridge in the tree) is
REGENERATED: `rung_holds_iff_synth` proves the identical `program.Holds (inputOf tag payload) ↔
Reaches tag payload` with the synthesized `holds_iff_canonForm` discharging the fold+affine solving,
leaving only the trivial (C) `simp` that recovers the hand `Reaches`. Load-bearing negative canary
armed at build via `#guard_msgs`; every generated theorem is `#assert_axioms`-clean.
-/
import Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2
import Dregg2.Crypto.Arith.ArithmetizeTypedPredicate
import Dregg2.Tactics
import Lean

namespace Dregg2.Crypto.Arith.BridgeSynthesis

open Lean Elab Command
-- SELECTIVE opens: `TypedLinearPredicateDescriptorIR2` also exports its own `Formula` abbrev, which
-- would make the bare `Formula` type ambiguous against the certificate's. Pull only the three IR2
-- vocabulary names; `Formula` resolves unambiguously to the certificate one it aliases.
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2 (AffineTerm Program BabyBear)
open Dregg2.Metatheory.DirectLogicOptimizerCertificate (Formula)
open Dregg2.Crypto.Arith.TypedPredicate (LiveRefinesSpec LiveExact liveRefinesSpecOf liveExactOf)

set_option autoImplicit false

/-! ## 1. (A) The Formula-fold congruence — reflection over the Boolean AST.

`holds_congr` folds a leafwise `Iff` through the concrete `source : Formula n`. This is the exact
`graphEval_iff_holds` pattern already in the tree: structural recursion on the AST, the field never
touched. It is total and exact. -/

theorem holds_congr {n : Nat} {t1 t2 : Fin n → Prop} (h : ∀ a, t1 a ↔ t2 a)
    (f : Formula n) : Formula.Holds t1 f ↔ Formula.Holds t2 f := by
  induction f with
  | atom a => exact h a
  | top => exact Iff.rfl
  | bot => exact Iff.rfl
  | not p ih => exact not_congr ih
  | and p q ihp ihq => exact and_congr ihp ihq
  | or p q ihp ihq => exact or_congr ihp ihq

/-! ## 2. (B) Per-atom affine canonicalization — the fixed `linear_combination` schema.

`canonAtom` classifies over the `AffineTerm` SYNTAX (constructors, no `ZMod` reduction) and emits the
solved field equation for the recognized shapes. `eqConst i k = .add (.input i) (.const (-k))` is the
`.add (.input i) (.const c)` case: `input i + c = 0 ↔ input i = -c`. Everything else canonicalizes to
its own raw affine equation — the canonicalizer is TOTAL and the fallback Iff is definitional. -/

noncomputable def canonAtom {m : Nat} (input : Fin m → BabyBear) : AffineTerm m → Prop
  | .const k => ((k : Int) : BabyBear) = 0
  | .input i => input i = 0
  | .neg x => -(x.evalField input) = 0
  | .add (.input i) (.const c) => input i = -(((c : Int)) : BabyBear)
  | .add x y => (x.evalField input + y.evalField input) = 0
  | .scale k x => ((k : Int) : BabyBear) * x.evalField input = 0

/-- Soundness of the per-atom canonicalizer, proven ONCE by the fixed `linear_combination` schema.
The field stays symbolic; no `Decidable`/`decide` and no concrete `ZMod` reduction. -/
theorem canonAtom_iff {m : Nat} (input : Fin m → BabyBear) (t : AffineTerm m) :
    (t.evalField input = 0) ↔ canonAtom input t := by
  cases t with
  | const k => simp [canonAtom, AffineTerm.evalField]
  | input i => simp [canonAtom, AffineTerm.evalField]
  | neg x => simp [canonAtom, AffineTerm.evalField]
  | scale k x => simp [canonAtom, AffineTerm.evalField]
  | add x y =>
      -- The two recognized shapes need the `linear_combination` schema; every other affine shape
      -- canonicalizes to its own raw equation (`Iff.rfl`, closed by `simp`).
      cases x <;> cases y <;>
        first
          | (simp only [canonAtom, AffineTerm.evalField]
             constructor <;> intro h <;> linear_combination h)
          | simp [canonAtom, AffineTerm.evalField]

/-! ## 3. (A)∘(B) The composed canonical form and the synthesized bridge.

`canonForm p input` is the fold of the canonicalized leaves through `p.source` — a legible
field-equation predicate, not `P → P`, not a felt/trace statement. `holds_iff_canonForm` is the
SYNTHESIZED bridge: `p.Holds input ↔ canonForm p input`, kernel-checked, for every `Program`. -/

noncomputable def canonForm {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) → BabyBear) : Prop :=
  Formula.Holds (fun a => canonAtom input (p.atomTerms a)) p.source

theorem holds_iff_canonForm {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) → BabyBear) :
    p.Holds input ↔ canonForm p input := by
  unfold Program.Holds canonForm
  exact holds_congr (fun a => canonAtom_iff input (p.atomTerms a)) p.source

/-- Terse wrapper so the load-bearing negative canary prints a one-line type mismatch. -/
def HoldsCanon {pub sec atoms : Nat} (p : Program pub sec atoms) : Prop :=
  ∀ input, p.Holds input ↔ canonForm p input

theorem holdsCanonOf {pub sec atoms : Nat} (p : Program pub sec atoms) : HoldsCanon p :=
  fun input => holds_iff_canonForm p input

/-! ## 4. The command: emit the synthesized bridge and the caller-obligation-free spec bundle. -/

private def emitCanonicalCore (name : Ident) (prog : Term) : CommandElabM Unit := do
  let progId    := mkIdent (name.getId.appendAfter "_program")
  let canonId   := mkIdent (name.getId.appendAfter "_holds_canon")
  let specSndId := mkIdent (name.getId.appendAfter "_spec_sound")
  let specExId  := mkIdent (name.getId.appendAfter "_spec_exact")
  -- (a) capture the typed predicate program.
  elabCommand (← `(command| def $progId := $prog))
  -- (b) the SYNTHESIZED bridge — (A) fold ∘ (B) affine solving, no hand proof.
  elabCommand (← `(command|
    theorem $canonId : ∀ input, ($progId).Holds input ↔ canonForm $progId input :=
      fun input => holds_iff_canonForm $progId input))
  -- (c) the spec bundle with ZERO caller obligation: the synthesized bridge composed with the
  --     MVP-1 `sound` / `canonical_iff` combinators. The canonical form IS the spec.
  elabCommand (← `(command|
    theorem $specSndId : LiveRefinesSpec $progId (canonForm $progId) :=
      liveRefinesSpecOf $progId (canonForm $progId) $canonId))
  elabCommand (← `(command|
    theorem $specExId : LiveExact $progId (canonForm $progId) :=
      liveExactOf $progId (canonForm $progId) $canonId))

/-- **`#arithmetizeTypedCanonical foo := prog`** — synthesize the bridge `foo_holds_canon` and emit
the spec bundle `foo_spec_sound` / `foo_spec_exact` against the SYNTHESIZED canonical spec, with NO
caller-supplied bridge. The canonical-form ↔ arbitrary-prose-Spec link (C) is out of scope. -/
elab "#arithmetizeTypedCanonical" name:ident ":=" prog:term : command =>
  emitCanonicalCore name prog

/-! ## 5. Pilot — regenerate `InterchainRung.program_holds_iff`.

`RungPilot.program` is the InterchainRung program with public atom defs (defeq to the private-atom
original — proven by `rfl` below); every atom is `eqConst`, the shape `canonAtom` solves. -/

namespace RungPilot

def i0 : Fin 2 := ⟨0, by omega⟩
def i1 : Fin 2 := ⟨1, by omega⟩
def a0 : Formula 4 := .atom ⟨0, by omega⟩
def a1 : Formula 4 := .atom ⟨1, by omega⟩
def a2 : Formula 4 := .atom ⟨2, by omega⟩
def a3 : Formula 4 := .atom ⟨3, by omega⟩

def atomTerms : Fin 4 → AffineTerm 2
  | ⟨0, _⟩ => .eqConst i0 0
  | ⟨1, _⟩ => .eqConst i0 1
  | ⟨2, _⟩ => .eqConst i0 2
  | ⟨3, _⟩ => .eqConst i1 0
  | ⟨_, _⟩ => .const 1

/-- `tag = 0 ∨ (payload ≠ 0 ∧ (tag = 1 ∨ tag = 2))`, the InterchainRung source, not DNF-expanded. -/
def source : Formula 4 := .or a0 (.and (.not a3) (.or a1 a2))

def program : Program 2 0 4 := { atomTerms := atomTerms, source := source }

/-- A genuinely DIFFERENT program (drops the payload clause) so the negative canary bites on the
program linkage, not on an arity clash. -/
def sourceB : Formula 4 := .or a0 a1

def programB : Program 2 0 4 := { atomTerms := atomTerms, source := sourceB }

/-- The pilot program is the production InterchainRung program, up to the private-atom names. -/
theorem eq_interchain : program = Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2.InterchainRung.program := rfl

end RungPilot

#arithmetizeTypedCanonical rung := RungPilot.program
#arithmetizeTypedCanonical rungB := RungPilot.programB

-- The synthesized bridge really added the LIVE objects.
#check (rung_program : Program 2 0 4)
#check (rung_holds_canon : ∀ input, rung_program.Holds input ↔ canonForm rung_program input)
#check (rung_spec_sound : LiveRefinesSpec rung_program (canonForm rung_program))
#check (rung_spec_exact : LiveExact rung_program (canonForm rung_program))

open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2.InterchainRung in
/-- **REGENERATION.** The hand `InterchainRung.program_holds_iff` (6 `simp` lines over 16 names +
the shared `add_neg_*_zero_iff` lemmas), reproduced with the synthesized `holds_iff_canonForm`
carrying (A) the fold and (B) the affine solving; the only remaining step is the trivial (C) `simp`
that reads the canonical form as the hand `Reaches`. -/
theorem rung_holds_iff_synth (tag payload : BabyBear) :
    RungPilot.program.Holds (inputOf tag payload) ↔ Reaches tag payload :=
  (holds_iff_canonForm RungPilot.program (inputOf tag payload)).trans (by
    have e0 : RungPilot.atomTerms 0 = .eqConst RungPilot.i0 0 := rfl
    have e1 : RungPilot.atomTerms 1 = .eqConst RungPilot.i0 1 := rfl
    have e2 : RungPilot.atomTerms 2 = .eqConst RungPilot.i0 2 := rfl
    have e3 : RungPilot.atomTerms 3 = .eqConst RungPilot.i1 0 := rfl
    have t0 : inputOf tag payload 0 = tag := rfl
    have t1 : inputOf tag payload 1 = payload := rfl
    simp [canonForm, canonAtom, RungPilot.program, RungPilot.source,
      RungPilot.a0, RungPilot.a1, RungPilot.a2, RungPilot.a3,
      e0, e1, e2, e3, RungPilot.i0, RungPilot.i1,
      AffineTerm.eqConst, Formula.Holds, t0, t1, Reaches])

/-! ## 6. Kernel hygiene and the load-bearing canaries. -/

#assert_all_clean [
  holds_congr,
  canonAtom_iff,
  holds_iff_canonForm,
  holdsCanonOf,
  rung_holds_canon,
  rung_spec_sound,
  rung_spec_exact,
  rung_holds_iff_synth
]

-- POSITIVE CONTROL (build-time): the synthesized spec proof reaches its own program. If a future
-- edit made the synthesis program-independent, this reddens.
#assert_depends_on rung_spec_sound [rung_program]
#assert_depends_on rung_holds_iff_synth [canonForm]

/-! ### The NEGATIVE canary, ARMED AT BUILD TIME.

Take one program's synthesized bridge and try to inhabit ANOTHER program's `HoldsCanon` statement.
`HoldsCanon` mentions its program in both `Holds` and `canonForm`, so the two are not defeq and the
kernel refuses. If a future change made `canonForm` program-independent (vacuous), the two unfoldings
would coincide, this `example` would be ACCEPTED, and `#guard_msgs` would go RED. -/
/-- error: Type mismatch
  holdsCanonOf rungB_program
has type
  HoldsCanon rungB_program
but is expected to have type
  HoldsCanon rung_program
-/
#guard_msgs in
example : HoldsCanon rung_program := holdsCanonOf rungB_program

end Dregg2.Crypto.Arith.BridgeSynthesis
