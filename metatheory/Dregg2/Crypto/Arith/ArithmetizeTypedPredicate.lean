/-
# Dregg2.Crypto.Arith.ArithmetizeTypedPredicate — MVP-1: the arithmetizer's MECHANISM
# wired onto the EXISTING Layer-B typed-predicate compiler.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Every constraint emitted here comes
from `Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2.descriptor`, a Lean function; no Rust
hand-writes any of it, and the generated theorems are about that emitted `EffectVmDescriptor2`.

## Why this file exists

Two halves of the arithmetizer were sitting in the tree NOT talking to each other:

* `Dregg2/Crypto/Arith/ArithmetizeMVP.lean` has the proof-PRODUCING MECHANISM — a `#arithmetizeDfa`
  Command elab that adds a `def` AND a kernel-checked `theorem` in one command, with a build-armed
  negative canary — but only at the ABSTRACT altitude (`DfaAccepts`/`ReflTransGen delta`, no felts).
* `Dregg2/Metatheory/TypedLinearPredicateDescriptorIR2.lean` has the ALTITUDE — a sound-AND-complete
  compiler from a typed predicate `Program` to a LIVE `EffectVmDescriptor2` (`sound` over arbitrary
  nonempty traces with NO `hatoms` boundary, `canonical_complete`, `canonical_iff`,
  `descriptor_exact_resources`, `descriptor_constraint_low_degree`, byte-pinned `emitVmJson2`) —
  but every instance of it is HAND-WRITTEN, theorem by theorem (see `InterchainRung`).

NEITHER IMPORTED THE OTHER. This module is the bridge: the mechanism from Arith, the altitude from
the Layer-B compiler. `#arithmetizeTypedPredicate` / `#arithmetizeTypedRefinement` generate, from a
typed predicate program, the LIVE descriptor AND a bundle of kernel-checked theorems about it, each
proof term citing the existing `sound` / `public_sound` / `canonical_iff` /
`descriptor_exact_resources` / `descriptor_constraint_low_degree` / `checkArtifact_*` lemmas —
exactly as MVP-0's generated proof cites `dfaAccepts_reduces`.

ZERO new mathematics. The novel capability is again purely mechanical: a command that turns a
`Program` value into a live descriptor plus its refinement bundle, all kernel-checked on `addDecl`.

## What is GENERATED, and at what resolution

`#arithmetizeTypedPredicate foo := prog` emits

  foo_program        : Program pub sec atoms      -- the captured typed predicate program
  foo_descriptor     : EffectVmDescriptor2        -- the LIVE emitted descriptor
  foo_descriptor_eq  : foo_descriptor = descriptor foo_program
  foo_sound          : LiveRefines foo_program        -- cites `sound`
  foo_public_sound   : LivePublicRefines foo_program  -- cites `public_sound`
  foo_canonical_iff  : LiveCanonicalIff foo_program   -- cites `canonical_iff`
  foo_resources      : LiveResources foo_program      -- cites `descriptor_exact_resources`
  foo_low_degree     : LiveLowDegree foo_program      -- cites `descriptor_constraint_low_degree`
  foo_artifact / foo_json / foo_json_exact            -- cites `checkArtifact_spec/_certify`

and `#arithmetizeTypedRefinement foo := prog refines Spec via bridge` additionally emits

  foo_spec_sound     : LiveRefinesSpec foo_program Spec   -- `sound` ∘ the caller's bridge
  foo_spec_exact     : LiveExact foo_program Spec         -- `canonical_iff` ∘ the caller's bridge

`LiveRefinesSpec p Spec` is the real content: EVERY nonempty trace satisfying the EMITTED descriptor
proves the caller's spec on the descriptor's OWN typed row-input columns. `LiveExact p Spec` is the
two-way version on the compiler's canonical trace. Neither is `P → P`.

## HONEST RESOLUTION CAP — three named gaps, do not upgrade these sentences

1. `Satisfied2` is the descriptor-level constraint-satisfaction predicate. A generated `foo_sound`
   says "any satisfying trace of THIS descriptor witnesses the spec" — it does NOT say the deployed
   prover/verifier is sound, and it inherits the undischarged FRI/STARK floor and the witness-
   generator perimeter exactly as every other descriptor-level theorem in this tree does.
2. The BRIDGE IS NOT SYNTHESIZED. `#arithmetizeTypedRefinement` composes a caller-supplied
   `bridge : ∀ input, p.Holds input ↔ Spec input`; it does not derive it. That obligation is
   program-level (no descriptor, no trace, no felts) and each witness below discharges it in one
   `simp`, but auto-deriving it is future work — deliberately NOT attempted here, since the obvious
   route (`decide` over a `Decidable` instance on a `ZMod 2013265921` predicate) is exactly the
   kernel reduction that must never be run.
3. The source language is the typed-predicate compiler's own fragment: affine atoms plus a Boolean
   AST. No nonlinear atom gadgets, no hash sites, no memory/map ops, no range checks — the emitted
   descriptor has `hashSites := []` and `ranges := []` by construction. Programs outside that
   fragment are simply not expressible as `Program`, so nothing is silently weakened; the fragment
   is the limit, and `InterchainRung`'s `modulus_*_alias_frontier` records the integer/field
   canonicalization boundary that still sits in front of a direct production replacement.

## The load-bearing canary

Positive control: `#assert_depends_on foo_spec_sound [foo_program]` — the generated proof term
genuinely reaches the program it was generated from.

Negative half, ARMED at build time via `#guard_msgs`: taking program ALPHA's refinement STATEMENT
and building it from program BETA's compilation FAILS to typecheck. See §4.
-/
import Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2
import Dregg2.Tactics
import Lean

namespace Dregg2.Crypto.Arith.TypedPredicate

open Lean Elab Command
open Dregg2.Circuit.DescriptorIR2
-- SELECTIVE open: `DirectLogicBoolGraphDescriptorIR2` also exports `BabyBear`/`Formula`, which
-- would collide with the typed-predicate module's own. Only the three emitter-vocabulary names are
-- pulled in; every field/formula name below is the typed-predicate compiler's.
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2 (gate witnessCount exprDegree fieldAssignment)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2

set_option autoImplicit false

/-! ## 1. The refinement predicates the generated theorems inhabit, and the cited proofs.

Each `Live*` is a `Prop` ABOUT a `Program`; each `live*Of` is the corresponding proof, its body a
direct citation of the existing Layer-B lemma. The elaborator emits, per name, the specialization of
the `live*Of` combinator at the generated `foo_program` — so the emitted proof term names the
program's own `foo_program` in BOTH statement and proof. -/

variable {pub sec atoms : Nat}

/-- **Arbitrary-trace soundness of the emitted live descriptor.** Any nonempty trace satisfying the
EMITTED `EffectVmDescriptor2` proves the program's predicate on the descriptor's own typed raw-input
columns. This is `TypedLinearPredicateDescriptorIR2.sound` read as a `Prop` about `p`. -/
def LiveRefines (p : Program pub sec atoms) : Prop :=
  ∀ (hash : List Int → Int) (t : VmTrace), t.rows ≠ [] →
    Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t →
      p.Holds (rowInput p t)

/-- The generated proof of `LiveRefines`, as a reusable term: cites `sound`. -/
theorem liveRefinesOf (p : Program pub sec atoms) : LiveRefines p :=
  fun hash t hne hsat => sound hash p t hne hsat

/-- **Statement soundness**: the public prefix is verifier-bound and the secret suffix is
existentially witnessed by the satisfying trace. Cites `public_sound`. -/
def LivePublicRefines (p : Program pub sec atoms) : Prop :=
  ∀ (hash : List Int → Int) (t : VmTrace), t.rows ≠ [] →
    Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t →
      p.PublicHolds (fun i => fieldAssignment t.pub i.val)

/-- The generated proof of `LivePublicRefines`: cites `public_sound`. -/
theorem livePublicRefinesOf (p : Program pub sec atoms) : LivePublicRefines p :=
  fun hash t hne hsat => public_sound hash p t hne hsat

/-- **Exact semantics on the canonical trace** — soundness AND constructive completeness in one
biconditional. Cites `canonical_iff`. -/
def LiveCanonicalIff (p : Program pub sec atoms) : Prop :=
  ∀ (hash : List Int → Int) (input : Fin (pub + sec) → BabyBear),
    Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) []
        (canonicalTrace p input) ↔ p.Holds input

/-- The generated proof of `LiveCanonicalIff`: cites `canonical_iff`. -/
theorem liveCanonicalIffOf (p : Program pub sec atoms) : LiveCanonicalIff p :=
  fun hash input => canonical_iff hash p input

/-- **Exact emitted resources** — public-input count, trace width, and equation count of the LIVE
descriptor, in closed form. Cites `descriptor_exact_resources`. -/
def LiveResources (p : Program pub sec atoms) : Prop :=
  (descriptor p).piCount = pub ∧
    (descriptor p).traceWidth = atoms + (pub + sec) + witnessCount p.source ∧
    (descriptor p).constraints.length = pub + atoms + p.source.graphCost.equations + 1

/-- The generated proof of `LiveResources`: cites `descriptor_exact_resources`. -/
theorem liveResourcesOf (p : Program pub sec atoms) : LiveResources p :=
  ⟨(descriptor_exact_resources p).1,
    (descriptor_exact_resources p).2.1,
    (descriptor_exact_resources p).2.2.1⟩

/-- **No high-degree escape**: every emitted constraint is a linear public pin or a gate of degree
at most two. Cites `descriptor_constraint_low_degree`. -/
def LiveLowDegree (p : Program pub sec atoms) : Prop :=
  ∀ c ∈ (descriptor p).constraints,
    (∃ row col pi, c = .base (.piBinding row col pi)) ∨
      (∃ body, c = gate body ∧ exprDegree body ≤ 2)

/-- The generated proof of `LiveLowDegree`: cites `descriptor_constraint_low_degree`. -/
theorem liveLowDegreeOf (p : Program pub sec atoms) : LiveLowDegree p :=
  fun c hc => descriptor_constraint_low_degree p c hc

/-! ### The spec-level bundle — the ALTITUDE the bridge exists for.

`LiveRefinesSpec p Spec` is the object MVP-0 could not reach: a refinement of a CALLER-CHOSEN spec
by a LIVE emitted descriptor. The caller supplies one `bridge : ∀ input, p.Holds input ↔ Spec input`
(a statement about the typed program only — no descriptor, no trace, no felts) and the elaborator
composes it with `sound` / `canonical_iff` to generate the descriptor-level theorems. -/

/-- **Live spec refinement.** Every nonempty trace satisfying the EMITTED descriptor proves the
caller's `Spec` on the descriptor's own typed row inputs. -/
def LiveRefinesSpec (p : Program pub sec atoms)
    (Spec : (Fin (pub + sec) → BabyBear) → Prop) : Prop :=
  ∀ (hash : List Int → Int) (t : VmTrace), t.rows ≠ [] →
    Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) [] t →
      Spec (rowInput p t)

/-- The generated proof of `LiveRefinesSpec`: `sound` composed with the caller's bridge. -/
theorem liveRefinesSpecOf (p : Program pub sec atoms)
    (Spec : (Fin (pub + sec) → BabyBear) → Prop)
    (bridge : ∀ input, p.Holds input ↔ Spec input) : LiveRefinesSpec p Spec :=
  fun hash t hne hsat => (bridge (rowInput p t)).mp (sound hash p t hne hsat)

/-- **Live spec exactness** on the compiler's canonical trace: satisfaction of the EMITTED
descriptor is equivalent to the caller's `Spec`. -/
def LiveExact (p : Program pub sec atoms)
    (Spec : (Fin (pub + sec) → BabyBear) → Prop) : Prop :=
  ∀ (hash : List Int → Int) (input : Fin (pub + sec) → BabyBear),
    Satisfied2 hash (descriptor p) (fun _ => 0) (fun _ => (0, 0)) []
        (canonicalTrace p input) ↔ Spec input

/-- The generated proof of `LiveExact`: `canonical_iff` composed with the caller's bridge. -/
theorem liveExactOf (p : Program pub sec atoms)
    (Spec : (Fin (pub + sec) → BabyBear) → Prop)
    (bridge : ∀ input, p.Holds input ↔ Spec input) : LiveExact p Spec :=
  fun hash input => (canonical_iff hash p input).trans (bridge input)

/-! ## 2. The elaborators.

`emitTypedPredicateCore` adds the program, the LIVE descriptor, and the descriptor-level bundle.
Every declaration goes through `elabCommand → addDecl`, so the kernel checks each generated theorem
on insertion; a bad proof term is a hard elaboration error, never a silent `sorry`. -/

open Dregg2.Crypto.Arith.TypedPredicate in
/-- Emit the program, the live descriptor, and the descriptor-level refinement bundle. -/
private def emitTypedPredicateCore (name : Ident) (prog : Term) : CommandElabM Unit := do
  let progId    := mkIdent (name.getId.appendAfter "_program")
  let descId    := mkIdent (name.getId.appendAfter "_descriptor")
  let descEqId  := mkIdent (name.getId.appendAfter "_descriptor_eq")
  let soundId   := mkIdent (name.getId.appendAfter "_sound")
  let pubId     := mkIdent (name.getId.appendAfter "_public_sound")
  let iffId     := mkIdent (name.getId.appendAfter "_canonical_iff")
  let resId     := mkIdent (name.getId.appendAfter "_resources")
  let degId     := mkIdent (name.getId.appendAfter "_low_degree")
  let artId     := mkIdent (name.getId.appendAfter "_artifact")
  let jsonId    := mkIdent (name.getId.appendAfter "_json")
  let jsonEqId  := mkIdent (name.getId.appendAfter "_json_exact")
  -- (a) capture the typed predicate program.
  elabCommand (← `(command| def $progId := $prog))
  -- (b) COMPILE it: the LIVE `EffectVmDescriptor2`, and the pin that it IS the compiler's output.
  elabCommand (← `(command| def $descId : EffectVmDescriptor2 := descriptor $progId))
  elabCommand (← `(command| theorem $descEqId : $descId = descriptor $progId := rfl))
  -- (c) the descriptor-level refinement bundle; each proof term names `foo_program`.
  elabCommand (← `(command| theorem $soundId : LiveRefines $progId := liveRefinesOf $progId))
  elabCommand (← `(command|
    theorem $pubId : LivePublicRefines $progId := livePublicRefinesOf $progId))
  elabCommand (← `(command|
    theorem $iffId : LiveCanonicalIff $progId := liveCanonicalIffOf $progId))
  elabCommand (← `(command| theorem $resId : LiveResources $progId := liveResourcesOf $progId))
  elabCommand (← `(command| theorem $degId : LiveLowDegree $progId := liveLowDegreeOf $progId))
  -- (d) the byte-pinned artifact: the emitted JSON, and the theorem that it IS `emitVmJson2` of the
  --     compiled descriptor (cites `checkArtifact_spec` ∘ `checkArtifact_certify`).
  elabCommand (← `(command| def $artId : Artifact $progId := certify $progId))
  elabCommand (← `(command| def $jsonId : String := ($artId).descriptorBytes))
  elabCommand (← `(command|
    theorem $jsonEqId : $jsonId = emitVmJson2 (descriptor $progId) :=
      (checkArtifact_spec $artId |>.mp (checkArtifact_certify $progId)).2.2))

/-- **`#arithmetizeTypedPredicate foo := prog`** — compile a typed predicate program to a LIVE
`EffectVmDescriptor2` and generate its kernel-checked refinement bundle. -/
elab "#arithmetizeTypedPredicate" name:ident ":=" prog:term : command =>
  emitTypedPredicateCore name prog

/-- **`#arithmetizeTypedRefinement foo := prog refines Spec via bridge`** — everything
`#arithmetizeTypedPredicate` emits, PLUS the spec-level theorems: the generated
`foo_spec_sound : LiveRefinesSpec foo_program Spec` and `foo_spec_exact : LiveExact foo_program Spec`
compose the caller's program-level `bridge` with `sound` / `canonical_iff`. The bridge is the ONLY
caller obligation, and it mentions no descriptor, no trace, and no felts. -/
elab "#arithmetizeTypedRefinement" name:ident ":=" prog:term
    "refines" spec:term "via" bridge:term : command => do
  emitTypedPredicateCore name prog
  let progId     := mkIdent (name.getId.appendAfter "_program")
  let specSndId  := mkIdent (name.getId.appendAfter "_spec_sound")
  let specExId   := mkIdent (name.getId.appendAfter "_spec_exact")
  elabCommand (← `(command|
    theorem $specSndId : LiveRefinesSpec $progId $spec :=
      liveRefinesSpecOf $progId $spec $bridge))
  elabCommand (← `(command|
    theorem $specExId : LiveExact $progId $spec :=
      liveExactOf $progId $spec $bridge))

/-! ## 3. Witnesses — drive both commands on DISTINCT typed predicate programs.

ALPHA and BETA are both `Program 1 1 2`: one public field input (index `0`), one secret field input
(index `1`), and a two-atom affine registry. Same SHAPE, different SEMANTICS — which is what makes
the §4 canary bite on the program linkage rather than on an arity mismatch. GAMMA (`Program 1 0 1`)
drives the base command, which takes no spec and imposes no caller obligation at all. -/

private theorem add_neg_one_zero_iff (x : BabyBear) : x + (-1) = 0 ↔ x = 1 := by
  constructor <;> intro h <;> linear_combination h

private def i0 : Fin 2 := ⟨0, by omega⟩
private def i1 : Fin 2 := ⟨1, by omega⟩
private def a0 : Formula 2 := .atom ⟨0, by omega⟩
private def a1 : Formula 2 := .atom ⟨1, by omega⟩

/-! ### ALPHA — "the public tag is 1 and the secret payload is nonzero". -/

/-- Affine atom registry for ALPHA: `tag - 1` and `payload`. -/
def alphaAtoms : Fin 2 → AffineTerm 2
  | ⟨0, _⟩ => .eqConst i0 1
  | ⟨1, _⟩ => .input i1
  | ⟨_, _⟩ => .const 1

/-- Source AST for ALPHA: `tag = 1 ∧ ¬(payload = 0)`. Not DNF-expanded. -/
def alphaSource : Formula 2 := .and a0 (.not a1)

def alphaProg : Program 1 1 2 := { atomTerms := alphaAtoms, source := alphaSource }

/-- ALPHA's spec, stated with NO reference to any descriptor, trace, or felt column. -/
def AlphaSpec (input : Fin 2 → BabyBear) : Prop := input i0 = 1 ∧ input i1 ≠ 0

/-- The ONLY caller obligation for ALPHA: a program-level bridge. -/
theorem alphaBridge (input : Fin 2 → BabyBear) : alphaProg.Holds input ↔ AlphaSpec input := by
  have e0 : alphaAtoms 0 = .eqConst i0 1 := rfl
  have e1 : alphaAtoms 1 = .input i1 := rfl
  simp [alphaProg, Program.Holds, Program.AtomTruth, alphaSource, e0, e1, a0, a1,
    i0, i1, AffineTerm.eqConst, AffineTerm.evalField, AlphaSpec, add_neg_one_zero_iff,
    Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula.Holds]

#arithmetizeTypedRefinement alpha := alphaProg refines AlphaSpec via alphaBridge

/-! ### BETA — "the public tag is 0, or the secret payload is 1". A genuinely different predicate
over the same shape. -/

/-- Affine atom registry for BETA: `tag` and `payload - 1`. -/
def betaAtoms : Fin 2 → AffineTerm 2
  | ⟨0, _⟩ => .input i0
  | ⟨1, _⟩ => .eqConst i1 1
  | ⟨_, _⟩ => .const 1

/-- Source AST for BETA: `tag = 0 ∨ payload = 1`. -/
def betaSource : Formula 2 := .or a0 a1

def betaProg : Program 1 1 2 := { atomTerms := betaAtoms, source := betaSource }

/-- BETA's spec. -/
def BetaSpec (input : Fin 2 → BabyBear) : Prop := input i0 = 0 ∨ input i1 = 1

theorem betaBridge (input : Fin 2 → BabyBear) : betaProg.Holds input ↔ BetaSpec input := by
  have e0 : betaAtoms 0 = .input i0 := rfl
  have e1 : betaAtoms 1 = .eqConst i1 1 := rfl
  simp [betaProg, Program.Holds, Program.AtomTruth, betaSource, e0, e1, a0, a1,
    i0, i1, AffineTerm.eqConst, AffineTerm.evalField, BetaSpec, add_neg_one_zero_iff,
    Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula.Holds]

#arithmetizeTypedRefinement beta := betaProg refines BetaSpec via betaBridge

/-! ### GAMMA — drives the BASE command, with NO spec clause and hence NO caller obligation at all.
`Program 1 0 1`: one public input, no secrets, a single affine atom `tag - 7`. The whole
descriptor-level bundle is still generated; only the two spec-level theorems are absent. -/

def gammaAtoms : Fin 1 → AffineTerm 1
  | ⟨0, _⟩ => .eqConst ⟨0, by omega⟩ 7
  | ⟨_, _⟩ => .const 1

def gammaSource : Formula 1 := .atom ⟨0, by omega⟩

def gammaProg : Program 1 0 1 := { atomTerms := gammaAtoms, source := gammaSource }

#arithmetizeTypedPredicate gamma := gammaProg

/-! ### The commands really added the LIVE descriptor AND the whole kernel-checked bundle. -/

#check (alpha_program : Program 1 1 2)
#check (alpha_descriptor : EffectVmDescriptor2)
#check (alpha_descriptor_eq : alpha_descriptor = descriptor alpha_program)
#check (alpha_sound : LiveRefines alpha_program)
#check (alpha_public_sound : LivePublicRefines alpha_program)
#check (alpha_canonical_iff : LiveCanonicalIff alpha_program)
#check (alpha_resources : LiveResources alpha_program)
#check (alpha_low_degree : LiveLowDegree alpha_program)
#check (alpha_json : String)
#check (alpha_json_exact : alpha_json = emitVmJson2 (descriptor alpha_program))
#check (alpha_spec_sound : LiveRefinesSpec alpha_program AlphaSpec)
#check (alpha_spec_exact : LiveExact alpha_program AlphaSpec)
#check (beta_spec_sound : LiveRefinesSpec beta_program BetaSpec)
#check (beta_spec_exact : LiveExact beta_program BetaSpec)
-- The base command emits the full descriptor-level bundle too, minus only the spec-level pair.
#check (gamma_descriptor : EffectVmDescriptor2)
#check (gamma_sound : LiveRefines gamma_program)
#check (gamma_canonical_iff : LiveCanonicalIff gamma_program)
#check (gamma_resources : LiveResources gamma_program)
#check (gamma_low_degree : LiveLowDegree gamma_program)
#check (gamma_json_exact : gamma_json = emitVmJson2 (descriptor gamma_program))

/-- The generated live refinement, restated by hand so the STATEMENT is readable in the source and
not only inside a `Live*` wrapper: any nonempty trace satisfying the GENERATED descriptor forces the
public tag column to be `1` and the secret payload column to be nonzero. -/
theorem alpha_live_readable (hash : List Int → Int) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash alpha_descriptor (fun _ => 0) (fun _ => (0, 0)) [] t) :
    fieldAssignment (envAt t 0).loc 2 = 1 ∧ fieldAssignment (envAt t 0).loc 3 ≠ 0 := by
  have h := alpha_spec_sound hash t hne hsat
  have hinput : rowInput alpha_program t =
      fun i => fieldAssignment (envAt t 0).loc (2 + i.val) := rfl
  simpa [AlphaSpec, hinput, i0, i1] using h

/-! Every generated theorem is kernel-clean. -/
#assert_all_clean [
  liveRefinesOf,
  livePublicRefinesOf,
  liveCanonicalIffOf,
  liveResourcesOf,
  liveLowDegreeOf,
  liveRefinesSpecOf,
  liveExactOf,
  alphaBridge,
  betaBridge,
  alpha_sound,
  alpha_public_sound,
  alpha_canonical_iff,
  alpha_resources,
  alpha_low_degree,
  alpha_json_exact,
  alpha_spec_sound,
  alpha_spec_exact,
  alpha_live_readable,
  beta_spec_sound,
  beta_spec_exact,
  gamma_sound,
  gamma_canonical_iff,
  gamma_resources,
  gamma_low_degree,
  gamma_json_exact
]

/-! ## 4. Canaries — the generated bundle is LOAD-BEARING on the program it was generated from.

POSITIVE CONTROL (build-time): each generated proof term reaches its own `foo_program`. If a future
edit made the generation program-independent, this reddens. -/
#assert_depends_on alpha_spec_sound [alpha_program]
#assert_depends_on beta_spec_sound [beta_program]
#assert_depends_on alpha_json_exact [alpha_program]

/-! ### The two live descriptors really are DIFFERENT objects.

A cheap Bool demonstration (no kernel `decide` on a `Decidable` instance): the emitted JSON bytes of
the two generated descriptors differ, so the generation is a function of the program and not a
constant. Same shape `Program 1 1 2`, different atom registry and source AST. -/
-- The two programs have the SAME shape, so the emitted descriptors even share a name...
#guard alpha_descriptor.name == beta_descriptor.name
-- ...yet the generated live descriptors are genuinely different objects, down to their bytes.
#guard alpha_json != beta_json
-- The LIVE emitted ledger, in numbers (`alpha_resources` proves these are the closed forms).
#guard alpha_descriptor.piCount == 1
#guard alpha_descriptor.traceWidth == 10
#guard alpha_descriptor.constraints.length == 14
#guard beta_descriptor.piCount == 1
#guard beta_descriptor.traceWidth == 9
#guard beta_descriptor.constraints.length == 12
#guard gamma_descriptor.piCount == 1
#guard gamma_descriptor.traceWidth == 4
#guard gamma_descriptor.constraints.length == 6
#guard checkArtifact gamma_artifact
#guard alpha_json == emitVmJson2 alpha_descriptor
#guard beta_json == emitVmJson2 beta_descriptor
#guard checkArtifact alpha_artifact
#guard checkArtifact beta_artifact

/-! ### The NEGATIVE canary, ARMED AT BUILD TIME.

Take ALPHA's generated refinement STATEMENT and try to build it from BETA's compilation. The
`liveRefinesSpecOf` combinator's bridge argument is indexed by the program, so BETA's program with
ALPHA's bridge is a type error the kernel refuses. `#guard_msgs` asserts the elaborator REJECTS it,
so the BUILD exercises the load-bearing property; a commented-out canary cannot rot loudly, this one
can. If a future change made the generated proof stop depending on its program, this command would
go RED because the expected error would no longer be produced. -/
/-- error: Application type mismatch: The argument
  alphaBridge
has type
  ∀ (input : Fin 2 → BabyBear), alphaProg.Holds input ↔ AlphaSpec input
but is expected to have type
  ∀ (input : Fin (1 + 1) → BabyBear), beta_program.Holds input ↔ AlphaSpec input
in the application
  liveRefinesSpecOf beta_program AlphaSpec alphaBridge
-/
#guard_msgs in
example : LiveRefinesSpec alpha_program AlphaSpec :=
  liveRefinesSpecOf beta_program AlphaSpec alphaBridge

/-! And the dual: BETA's generated spec theorem cannot be laundered onto ALPHA's live descriptor. -/
/-- error: Type mismatch
  beta_spec_sound
has type
  LiveRefinesSpec beta_program BetaSpec
but is expected to have type
  LiveRefinesSpec alpha_program BetaSpec
-/
#guard_msgs in
example : LiveRefinesSpec alpha_program BetaSpec := beta_spec_sound

/-! And the sharpest form — the one the design names: generate the AIR from program ALPHA but claim
soundness for program BETA. `LiveRefines alpha_program` unfolds to a statement about
`descriptor alpha_program`, so BETA's `sound` cannot inhabit it.

This is load-bearing in the strong sense, not merely an index clash: on a head-congruence failure
Lean UNFOLDS both sides and compares the underlying `Prop`s. If `LiveRefines` ever stopped mentioning
its program (a vacuous or program-independent statement), the two unfoldings would be identical, the
`example` would be ACCEPTED, no error would be produced, and `#guard_msgs` would go RED. -/
/-- error: Type mismatch
  liveRefinesOf beta_program
has type
  LiveRefines beta_program
but is expected to have type
  LiveRefines alpha_program
-/
#guard_msgs in
example : LiveRefines alpha_program := liveRefinesOf beta_program

end Dregg2.Crypto.Arith.TypedPredicate
