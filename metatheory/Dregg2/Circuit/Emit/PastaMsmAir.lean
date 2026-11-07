/-
# Dregg2.Circuit.Emit.PastaMsmAir — the **multi-scalar-multiplication AIR**, emitted, and the
theorem that its gates FORCE the MSM. Lean-authored AIR: a `def`-generator over
`AirBuilder.Head` plus forcing lemmas over the ACTUALLY EMITTED constraint list. No Rust
hand-writes any of it.

## Why this file exists — the category it changes

`MinaWrapGroupGate` / `MinaWrapOpeningGate` / `MinaWrapSg*` are **instance differentials**: they
`decide` a real Mina block's numbers in the kernel and compare against values o1-labs' own code
produced. That is a genuine and load-bearing check — it caught the `prevLen` freeze that was
REJECTING MINA, two transcript-order bugs, and a coset descent reading the wrong index bit — and
those theorems stay exactly where they are.

But an instance differential covers **one block, forever**, and its cost grows with the object:
the `sg == ⟨s, srs.g⟩` leg cost 3.5 h of kernel time to establish a fact `SRS::verify` had
already accepted in milliseconds. Growing that pattern buys nothing.

**This file proves the CHECKER instead.** The emitted gates of an `n`-term MSM force the
accumulator columns to represent the `n`-term reference MSM, for EVERY `n`, EVERY scalar width,
and EVERY assignment that satisfies them — one induction, no `decide`, no per-term lemma. Once
that holds, dregg's own prover can prove *that it ran the check*, and a light client verifies a
dregg STARK proof in milliseconds for any block, instead of anyone grinding a kernel.

## What is composed (nothing here is constructed from scratch)

  * **K4a `PastaCurveComplete.pallasCompleteAdd`** — the unified RCB complete add
    (`add-2015-rcb`, strongly unified, exception-free at cofactor 1), already FORCED by
    `pallasCompleteAdd_forces`.
  * **K4b `PastaScalarMul.pallasLadder_forces`** — `[k]P` by a double-and-add ladder over that
    same gadget, forced by a **gate-count-independent** `List.range` induction. That induction is
    the technique this file lifts one level: an MSM is a fold of ladders exactly as a ladder is a
    fold of RCB steps, so the same argument runs again and the theorem does not grow with `n`.
  * **`AirBuilder`/`PastaField`** — `Head`, `fpValue`, the `fp*Core` gates and their `*_forces`.

## §2's new gadget, and why it is a real check rather than a shape

`fpIsZeroCore b qB` emits ONE gate, `fpValue b − p·fpValue qB`, and `fpIsZeroCore_forces` proves
a satisfied instance pins the reconstructed field element to `0` in `ZMod p`. It is the same
witnessed-quotient shape `fpMulHead` uses, with the product replaced by nothing.

It is **not** "every limb is zero": the forcing chain concludes mod `p`, so an honest prover's
columns need only be CONGRUENT to zero, and a gadget demanding literal zero limbs would refuse
honest proofs — a forcing theorem that is true because nothing satisfies it. §2's `#guard`s
exhibit a satisfying assignment at a non-canonical representative (`p` itself, quotient `1`) and
refute a non-zero one, so the gate is known to be both SATISFIABLE and REFUTABLE.

## Substrate, said out loud

**Lean-authored AIR.** Generators are `def`s producing `List VmConstraint2`; every theorem is
about `acceptB <that list> a = true`. Rust calls the emitted artifact; Rust hand-writes no
constraint, no builder gadget and no `air_accepts` predicate here.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard` KATs reduce in the kernel. Imports read-only (`PastaScalarMul`,
transitively `PastaCurveComplete`/`PastaCurve`/`PastaField`/`AirBuilder`). NEW file; NOT imported
by the `Dregg2` root, per house practice for gates. Import line:
`import Dregg2.Circuit.Emit.PastaMsmAir`
-/
import Dregg2.Circuit.Emit.PastaScalarMul

namespace Dregg2.Circuit.Emit.PastaMsmAir

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.PastaField (pN fpValue fpVal fpVal_eq gateBodyEvalZero acceptB)
open Dregg2.Circuit.Emit.PastaCurveComplete (pallasCompleteAdd)
open Dregg2.Circuit.Emit.PastaScalarMul (PtP PointIsZ rcbAddZmod ladderGatesFrom ladderRefFrom
  pallasLadder_forces pallasRcbStep_forces acceptB_append acceptB_cons acceptB_prefix
  acceptB_suffix gateBodyEvalZero_cgH dstep ladderStep)

set_option autoImplicit false

/-! ## §1 — THE MSM GENERATOR: a fold of ladders, exactly as a ladder is a fold of RCB steps.

One term is `[k_i]·P_i` (K4b's ladder, started at a represented identity) accumulated into the
running total with one more RCB complete add. `n` terms is the `List.range n` fold of that. The
digit bases of term `i` are supplied by `digitsOf i` — the same "represented input" discipline
`pallasLadder_forces` uses for its digits and `perm_forces` uses for its message words. -/

/-- One MSM term: the `nDigits`-step ladder for term `i`, then ONE complete add into the
accumulator. Returns (gates, new-accumulator bases, next fresh column). -/
def msmTermStep (digitsOf : Nat → List (Nat × Nat × Nat)) (nDigits : Nat)
    (zeroBases : Nat × Nat × Nat) :
    List VmConstraint2 × (Nat × Nat × Nat) × Nat → Nat →
    List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  fun st i =>
    let lad := ladderGatesFrom (digitsOf i) nDigits zeroBases st.2.2
    let add := pallasCompleteAdd st.2.1.1 st.2.1.2.1 st.2.1.2.2
                 lad.2.1.1 lad.2.1.2.1 lad.2.1.2.2 lad.2.2
    (st.1 ++ (lad.1 ++ add.1), add.2.1, add.2.2)

/-- **The `n`-term MSM's gates.** `n` is a parameter, not a literal: the whole point. -/
def msmGatesFrom (digitsOf : Nat → List (Nat × Nat × Nat)) (nDigits : Nat)
    (zeroBases : Nat × Nat × Nat) (n : Nat) (acc0 : Nat × Nat × Nat) (fresh0 : Nat) :
    List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  (List.range n).foldl (msmTermStep digitsOf nDigits zeroBases) ([], acc0, fresh0)

/-- **The reference `n`-term MSM** over `ZMod p`: accumulate the ladder folds of each term. This
is the object the gates are proved to force. -/
def msmRefFrom (digitValsOf : Nat → List PtP) (nDigits : Nat) (zeroVal : PtP)
    (n : Nat) (acc0 : PtP) : PtP :=
  (List.range n).foldl
    (fun acc i => rcbAddZmod acc (ladderRefFrom (digitValsOf i) nDigits zeroVal)) acc0

/-- The accumulated constraints keep the starting list as a prefix (mirrors
`PastaScalarMul.dstep_prefix`). -/
theorem msmTermStep_prefix (digitsOf : Nat → List (Nat × Nat × Nat)) (nDigits : Nat)
    (zeroBases : Nat × Nat × Nat) : ∀ (ts : List Nat)
    (X : List VmConstraint2) (acc : Nat × Nat × Nat) (fr : Nat),
    ∃ Y, (ts.foldl (msmTermStep digitsOf nDigits zeroBases) (X, acc, fr)).1 = X ++ Y := by
  intro ts
  induction ts with
  | nil => intro X acc fr; exact ⟨[], by simp⟩
  | cons t rest ih =>
    intro X acc fr
    rw [List.foldl_cons]
    obtain ⟨Y, hY⟩ := ih (msmTermStep digitsOf nDigits zeroBases (X, acc, fr) t).1
      (msmTermStep digitsOf nDigits zeroBases (X, acc, fr) t).2.1
      (msmTermStep digitsOf nDigits zeroBases (X, acc, fr) t).2.2
    refine ⟨(let lad := ladderGatesFrom (digitsOf t) nDigits zeroBases fr
             lad.1 ++ (pallasCompleteAdd acc.1 acc.2.1 acc.2.2
               lad.2.1.1 lad.2.1.2.1 lad.2.1.2.2 lad.2.2).1) ++ Y, ?_⟩
    rw [show (msmTermStep digitsOf nDigits zeroBases (X, acc, fr) t)
        = ((msmTermStep digitsOf nDigits zeroBases (X, acc, fr) t).1,
           (msmTermStep digitsOf nDigits zeroBases (X, acc, fr) t).2.1,
           (msmTermStep digitsOf nDigits zeroBases (X, acc, fr) t).2.2) from rfl] at hY
    rw [hY]; dsimp only [msmTermStep]; rw [List.append_assoc]

/-! ## §2 — THE `n`-INDEPENDENT FORCING.

The induction is over the index LIST, not over a gate count. Each step consumes exactly two
already-proved forcing lemmas — `pallasLadder_forces` for the term's ladder and
`pallasRcbStep_forces` for the accumulation — and hands the invariant to the tail. Nothing in
the proof mentions `n`, `nDigits`, or the length of the emitted list. -/

/-- **The fold forces the reference MSM** — by induction over the term-index list. -/
theorem foldl_msmTermStep_forces (a : Assignment) (digitsOf : Nat → List (Nat × Nat × Nat))
    (nDigits : Nat) (zeroBases : Nat × Nat × Nat) (digitValsOf : Nat → List PtP) (zeroVal : PtP)
    (hzero : PointIsZ a zeroBases.1 zeroBases.2.1 zeroBases.2.2 zeroVal) :
    ∀ (ts : List Nat) (cs0 : List VmConstraint2) (acc0 : Nat × Nat × Nat) (fr0 : Nat) (av0 : PtP),
      PointIsZ a acc0.1 acc0.2.1 acc0.2.2 av0 →
      (∀ i ∈ ts, ∀ t < nDigits,
        PointIsZ a ((digitsOf i).getD t (0,0,0)).1 ((digitsOf i).getD t (0,0,0)).2.1
          ((digitsOf i).getD t (0,0,0)).2.2 ((digitValsOf i).getD t (0,0,0))) →
      acceptB ((ts.foldl (msmTermStep digitsOf nDigits zeroBases) (cs0, acc0, fr0)).1) a = true →
      PointIsZ a (ts.foldl (msmTermStep digitsOf nDigits zeroBases) (cs0, acc0, fr0)).2.1.1
        (ts.foldl (msmTermStep digitsOf nDigits zeroBases) (cs0, acc0, fr0)).2.1.2.1
        (ts.foldl (msmTermStep digitsOf nDigits zeroBases) (cs0, acc0, fr0)).2.1.2.2
        (ts.foldl (fun acc i =>
          rcbAddZmod acc (ladderRefFrom (digitValsOf i) nDigits zeroVal)) av0) := by
  intro ts
  induction ts with
  | nil => intro cs0 acc0 fr0 av0 hav0 _ _; exact hav0
  | cons t rest ih =>
    intro cs0 acc0 fr0 av0 hav0 hD hacc
    rw [List.foldl_cons] at hacc ⊢
    rw [List.foldl_cons]
    set lad := ladderGatesFrom (digitsOf t) nDigits zeroBases fr0 with hlad
    set add := pallasCompleteAdd acc0.1 acc0.2.1 acc0.2.2
                 lad.2.1.1 lad.2.1.2.1 lad.2.1.2.2 lad.2.2 with hadd
    have hstep : msmTermStep digitsOf nDigits zeroBases (cs0, acc0, fr0) t
        = (cs0 ++ (lad.1 ++ add.1), add.2.1, add.2.2) := rfl
    rw [hstep] at hacc ⊢
    -- this term's own gates are accepted
    obtain ⟨Y, hY⟩ := msmTermStep_prefix digitsOf nDigits zeroBases rest
      (cs0 ++ (lad.1 ++ add.1)) _ _
    have haccStep : acceptB (lad.1 ++ add.1) a = true := by
      have h1 : acceptB (cs0 ++ (lad.1 ++ add.1)) a = true :=
        acceptB_prefix (cs0 ++ (lad.1 ++ add.1)) Y a (by rw [hY] at hacc; exact hacc)
      exact acceptB_suffix cs0 (lad.1 ++ add.1) a h1
    have haccLad : acceptB lad.1 a = true := acceptB_prefix _ _ a haccStep
    have haccAdd : acceptB add.1 a = true := acceptB_suffix _ _ a haccStep
    -- the ladder forces `[k_t]·P_t` (K4b, gate-count-independent)
    have hladPt : PointIsZ a lad.2.1.1 lad.2.1.2.1 lad.2.1.2.2
        (ladderRefFrom (digitValsOf t) nDigits zeroVal) :=
      pallasLadder_forces a (digitsOf t) (digitValsOf t) nDigits zeroBases fr0 zeroVal hzero
        (fun tt htt => hD t List.mem_cons_self tt htt) haccLad
    -- the accumulation forces one more RCB step (K4a)
    have hnext : PointIsZ a add.2.1.1 add.2.1.2.1 add.2.1.2.2
        (rcbAddZmod av0 (ladderRefFrom (digitValsOf t) nDigits zeroVal)) :=
      pallasRcbStep_forces a acc0.1 acc0.2.1 acc0.2.2
        lad.2.1.1 lad.2.1.2.1 lad.2.1.2.2 lad.2.2 hav0 hladPt haccAdd
    exact ih (cs0 ++ (lad.1 ++ add.1)) _ _ _ hnext
      (fun i hi => hD i (List.mem_cons_of_mem t hi)) hacc

/-- ⚑ **`msmGatesFrom_forces`** — **the emitted `n`-term MSM AIR forces the `n`-term MSM.** Any
assignment satisfying the generated constraint list has its accumulator columns representing, in
`ZMod p`, the reference multi-scalar multiplication of the represented digits.

`n` and `nDigits` are universally quantified and appear NOWHERE in the proof except as fold
bounds: the statement at `n = 32768` is the same theorem as the statement at `n = 1`. -/
theorem msmGatesFrom_forces (a : Assignment) (digitsOf : Nat → List (Nat × Nat × Nat))
    (nDigits : Nat) (zeroBases : Nat × Nat × Nat) (digitValsOf : Nat → List PtP) (zeroVal : PtP)
    (n : Nat) (acc0 : Nat × Nat × Nat) (fresh0 : Nat) (av0 : PtP)
    (hzero : PointIsZ a zeroBases.1 zeroBases.2.1 zeroBases.2.2 zeroVal)
    (hav0 : PointIsZ a acc0.1 acc0.2.1 acc0.2.2 av0)
    (hD : ∀ i < n, ∀ t < nDigits,
      PointIsZ a ((digitsOf i).getD t (0,0,0)).1 ((digitsOf i).getD t (0,0,0)).2.1
        ((digitsOf i).getD t (0,0,0)).2.2 ((digitValsOf i).getD t (0,0,0)))
    (hacc : acceptB (msmGatesFrom digitsOf nDigits zeroBases n acc0 fresh0).1 a = true) :
    PointIsZ a (msmGatesFrom digitsOf nDigits zeroBases n acc0 fresh0).2.1.1
      (msmGatesFrom digitsOf nDigits zeroBases n acc0 fresh0).2.1.2.1
      (msmGatesFrom digitsOf nDigits zeroBases n acc0 fresh0).2.1.2.2
      (msmRefFrom digitValsOf nDigits zeroVal n av0) :=
  foldl_msmTermStep_forces a digitsOf nDigits zeroBases digitValsOf zeroVal hzero
    (List.range n) [] acc0 fresh0 av0 hav0
    (fun i hi => hD i (List.mem_range.mp hi)) hacc

#assert_axioms msmTermStep_prefix
#assert_axioms foldl_msmTermStep_forces
#assert_axioms msmGatesFrom_forces

/-! ## §3 — THE TERMINAL PREDICATE: "this point is the point at infinity".

`PastaCurveComplete.isInfM m P = (Z ≡ 0 ∧ X ≡ 0 mod m)` — in the RCB projective model `O` is
`(0 : Y : 0)`, so pinning `X` and `Z` to zero mod `p` is the identity check.

The gate is the witnessed-quotient shape: `fpValue b = p · fpValue qB`. Forcing gives a
CONGRUENCE, which is exactly what an honest prover can satisfy — the columns need not be the
canonical representative. `#guard`s below exhibit acceptance at a non-canonical zero and
rejection at a non-zero value, so the gate is satisfiable AND refutable. -/

/-- **`fpIsZeroHead`** — `fpValue b − p·fpValue qB`. Zero forces the reconstructed Pasta base
field element at `b` to be `0` in `ZMod p`, with `qB` the witnessed quotient. -/
def fpIsZeroHead (b qB : Nat) : Head :=
  (fpValue b).append ((fpValue qB).scale (-(pN : ℤ)))

/-- The single emitted gate. -/
def fpIsZeroCore (b qB : Nat) : VmConstraint2 := cgH (fpIsZeroHead b qB)

/-- **`fpIsZeroCore_forces`** — a satisfied instance pins the element to zero mod `p`. -/
theorem fpIsZeroCore_forces (a : Assignment) (b qB : Nat)
    (hg : evalH (fpIsZeroHead b qB) a = 0) : ((fpVal a b : ℤ) : ZMod pN) = 0 := by
  simp only [fpIsZeroHead, evalH_append, evalH_scale, fpVal_eq] at hg
  have h : fpVal a b = (pN : ℤ) * fpVal a qB := by linarith
  rw [h, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

/-- **`pointAtInfinityGates`** — the two-gate terminal predicate on a represented point:
`X ≡ 0` and `Z ≡ 0` (mod `p`), i.e. the point IS `O`. -/
def pointAtInfinityGates (bX bZ qX qZ : Nat) : List VmConstraint2 :=
  [fpIsZeroCore bX qX, fpIsZeroCore bZ qZ]

/-- ⚑ **`pointAtInfinity_forces`** — the emitted terminal gates FORCE the represented point to be
the point at infinity in `ZMod p`. This is the predicate an IPA opening check must land on. -/
theorem pointAtInfinity_forces (a : Assignment) (bX bY bZ qX qZ : Nat) {P : PtP}
    (hP : PointIsZ a bX bY bZ P)
    (hacc : acceptB (pointAtInfinityGates bX bZ qX qZ) a = true) :
    P.1 = 0 ∧ P.2.2 = 0 := by
  simp only [pointAtInfinityGates, fpIsZeroCore, acceptB, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, gateBodyEvalZero_cgH] at hacc
  obtain ⟨gX, gZ⟩ := hacc
  obtain ⟨hPx, _, hPz⟩ := hP
  exact ⟨by rw [← hPx]; exact fpIsZeroCore_forces a bX qX (of_decide_eq_true gX),
         by rw [← hPz]; exact fpIsZeroCore_forces a bZ qZ (of_decide_eq_true gZ)⟩

#assert_axioms fpIsZeroCore_forces
#assert_axioms pointAtInfinity_forces

/-! ### §3b — the terminal gate BITES: satisfiable at a zero, refuted at a non-zero.

`AirBuilder.rangeNonneg` sat in this tree for months as a shape every consumer read as a check
(`StakeWidthRange` finally gave it teeth). These `#guard`s are the same instrument applied at
birth: an assignment that makes the gate ACCEPT, and assignments that make it REJECT. Without
the first, `pointAtInfinity_forces` could be true because nothing satisfies its hypothesis. -/

/-- An assignment putting the 9-limb encoding of `v` at base `0` and of `w` at base `9`. -/
def twoElemAsg (v w : Nat) : Assignment := fun col =>
  if col < 9 then Dregg2.Circuit.Emit.PastaField.Ref.limbOf v col
  else if col < 18 then Dregg2.Circuit.Emit.PastaField.Ref.limbOf w (col - 9)
  else 0

-- SATISFIABLE at the canonical zero (value 0, quotient 0) …
#guard acceptB [fpIsZeroCore 0 9] (twoElemAsg 0 0) == true
-- … and at a NON-CANONICAL zero: the element `p` itself, with quotient `1`. This is the case a
-- "every limb is zero" gadget would have REFUSED, and it is a case an honest prover can produce.
#guard acceptB [fpIsZeroCore 0 9] (twoElemAsg pN 1) == true
#guard acceptB [fpIsZeroCore 0 9] (twoElemAsg (2 * pN) 2) == true
-- REFUTABLE: a non-zero element admits no quotient that satisfies the gate.
#guard acceptB [fpIsZeroCore 0 9] (twoElemAsg 1 0) == false
#guard acceptB [fpIsZeroCore 0 9] (twoElemAsg 1 1) == false
#guard acceptB [fpIsZeroCore 0 9] (twoElemAsg (pN + 1) 1) == false
#guard acceptB [fpIsZeroCore 0 9] (twoElemAsg 0 1) == false

/-! ## §4 — THE OPENING-CHECK AIR.

`SRS::verify`'s statement (B), `poly-commitment/src/ipa.rs:118-300`:

```text
c·Q + delta − z1·sg − z1·b0·U − z2·H == O
```

Every term but `delta` is a scalar multiple of a group element, and `delta` has coefficient 1.
So the whole check is: an `n`-term MSM, one complete add of `delta`, and the terminal
"is the point at infinity" predicate. Nothing about the shape is specific to `n = 34`, which is
why the SAME generator emits the `⟨s, srs.g⟩` leg at `n = 32768`. -/

/-- **`openingCheckGates`** — the emitted AIR of an IPA opening check: `msm(terms) + delta = O`.
`deltaBases` is the coefficient-1 point; `qX`/`qZ` are the two terminal quotient witnesses. -/
def openingCheckGates (digitsOf : Nat → List (Nat × Nat × Nat)) (nDigits : Nat)
    (zeroBases deltaBases : Nat × Nat × Nat) (n : Nat) (acc0 : Nat × Nat × Nat)
    (fresh0 qX qZ : Nat) : List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  let m := msmGatesFrom digitsOf nDigits zeroBases n acc0 fresh0
  let fin := pallasCompleteAdd m.2.1.1 m.2.1.2.1 m.2.1.2.2
               deltaBases.1 deltaBases.2.1 deltaBases.2.2 m.2.2
  (m.1 ++ (fin.1 ++ pointAtInfinityGates fin.2.1.1 fin.2.1.2.2 qX qZ), fin.2.1, fin.2.2)

/-- The reference residual the gates are proved to force: `msm(terms) + delta`. -/
def openingResidualRef (digitValsOf : Nat → List PtP) (nDigits : Nat) (zeroVal : PtP)
    (n : Nat) (acc0 deltaVal : PtP) : PtP :=
  rcbAddZmod (msmRefFrom digitValsOf nDigits zeroVal n acc0) deltaVal

/-- ⚑⚑ **`openingCheck_forces`** — **the emitted opening-check AIR forces the IPA opening
relation.** Any assignment satisfying the generated constraints has
`msm(terms) + delta = O` in `ZMod p`: the residual's `X` and `Z` are both zero, which in the RCB
projective model IS the point at infinity (`PastaCurveComplete.isInfM`).

The forced predicate is the equation an HONEST proof satisfies — it is the same
`msm(terms) + delta` that `MinaWrapOpeningGate.openingResidual` computes on the real block and
`MinaWrapOpeningGate.opening_relation_holds` finds to be `O`, and that the file's ten tamper
poles find is NOT `O` when any single input moves. Nothing here says a passing prover KNOWS an
opening; that is P10, untouched (see §6). -/
theorem openingCheck_forces (a : Assignment) (digitsOf : Nat → List (Nat × Nat × Nat))
    (nDigits : Nat) (zeroBases deltaBases : Nat × Nat × Nat) (digitValsOf : Nat → List PtP)
    (zeroVal deltaVal : PtP) (n : Nat) (acc0 : Nat × Nat × Nat) (fresh0 qX qZ : Nat) (av0 : PtP)
    (hzero : PointIsZ a zeroBases.1 zeroBases.2.1 zeroBases.2.2 zeroVal)
    (hdelta : PointIsZ a deltaBases.1 deltaBases.2.1 deltaBases.2.2 deltaVal)
    (hav0 : PointIsZ a acc0.1 acc0.2.1 acc0.2.2 av0)
    (hD : ∀ i < n, ∀ t < nDigits,
      PointIsZ a ((digitsOf i).getD t (0,0,0)).1 ((digitsOf i).getD t (0,0,0)).2.1
        ((digitsOf i).getD t (0,0,0)).2.2 ((digitValsOf i).getD t (0,0,0)))
    (hacc : acceptB (openingCheckGates digitsOf nDigits zeroBases deltaBases n acc0
      fresh0 qX qZ).1 a = true) :
    (openingResidualRef digitValsOf nDigits zeroVal n av0 deltaVal).1 = 0
    ∧ (openingResidualRef digitValsOf nDigits zeroVal n av0 deltaVal).2.2 = 0 := by
  set m := msmGatesFrom digitsOf nDigits zeroBases n acc0 fresh0 with hm
  set fin := pallasCompleteAdd m.2.1.1 m.2.1.2.1 m.2.1.2.2
               deltaBases.1 deltaBases.2.1 deltaBases.2.2 m.2.2 with hfin
  have hsplit : (openingCheckGates digitsOf nDigits zeroBases deltaBases n acc0
      fresh0 qX qZ).1 = m.1 ++ (fin.1 ++ pointAtInfinityGates fin.2.1.1 fin.2.1.2.2 qX qZ) := rfl
  rw [hsplit] at hacc
  have haccM : acceptB m.1 a = true := acceptB_prefix _ _ a hacc
  have haccRest : acceptB (fin.1 ++ pointAtInfinityGates fin.2.1.1 fin.2.1.2.2 qX qZ) a = true :=
    acceptB_suffix _ _ a hacc
  have haccFin : acceptB fin.1 a = true := acceptB_prefix _ _ a haccRest
  have haccInf : acceptB (pointAtInfinityGates fin.2.1.1 fin.2.1.2.2 qX qZ) a = true :=
    acceptB_suffix _ _ a haccRest
  have hmsm : PointIsZ a m.2.1.1 m.2.1.2.1 m.2.1.2.2
      (msmRefFrom digitValsOf nDigits zeroVal n av0) :=
    msmGatesFrom_forces a digitsOf nDigits zeroBases digitValsOf zeroVal n acc0 fresh0 av0
      hzero hav0 hD haccM
  have hres : PointIsZ a fin.2.1.1 fin.2.1.2.1 fin.2.1.2.2
      (openingResidualRef digitValsOf nDigits zeroVal n av0 deltaVal) :=
    pallasRcbStep_forces a m.2.1.1 m.2.1.2.1 m.2.1.2.2
      deltaBases.1 deltaBases.2.1 deltaBases.2.2 m.2.2 hmsm hdelta haccFin
  exact pointAtInfinity_forces a fin.2.1.1 fin.2.1.2.1 fin.2.1.2.2 qX qZ hres haccInf

#assert_axioms openingCheck_forces

/-! ## §5 — THE PRICE, as theorems rather than as an evaluated list.

A `#guard` on `(msmGatesFrom … 32768 …).1.length` would ask the kernel to build a
half-billion-element list. So the gate count is a THEOREM, proved by the same induction, and the
numbers below are `#guard`s on the closed form. This is the pricing instrument: it answers
"how big is the trace" for every `n` at once, at zero kernel cost. -/

/-- Core gates per RCB complete add (Alg. 7: 12 mul + 2 const-mul + 14 add + 5 sub). -/
def RCB_GATES : Nat := 33
/-- Fresh columns per RCB complete add (33 intermediates × 9 limbs + 14 quotient groups × 9
+ 19 carry/borrow bits). -/
def RCB_COLS : Nat := 442

/-- The gate count of ONE emitted RCB add — `rfl`, at symbolic column bases. -/
theorem pallasCompleteAdd_length (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat) :
    (pallasCompleteAdd X1 Y1 Z1 X2 Y2 Z2 fresh).1.length = RCB_GATES := rfl

/-- And its column stride. -/
theorem pallasCompleteAdd_fresh (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat) :
    (pallasCompleteAdd X1 Y1 Z1 X2 Y2 Z2 fresh).2.2 = fresh + RCB_COLS := rfl

/-- One ladder step is two RCB adds. -/
theorem dstep_one (digitBases : List (Nat × Nat × Nat))
    (st : List VmConstraint2 × (Nat × Nat × Nat) × Nat) (t : Nat) :
    (dstep digitBases st t).1.length = st.1.length + 2 * RCB_GATES
    ∧ (dstep digitBases st t).2.2 = st.2.2 + 2 * RCB_COLS := by
  refine ⟨?_, ?_⟩ <;>
    simp only [dstep, ladderStep, List.length_append, pallasCompleteAdd_length,
      pallasCompleteAdd_fresh, RCB_GATES, RCB_COLS] <;> omega

/-- **The ladder's price, in closed form** — proved by induction over the digit-index list, so it
holds at every digit count at once. -/
theorem dstep_counts (digitBases : List (Nat × Nat × Nat)) : ∀ (ts : List Nat)
    (st : List VmConstraint2 × (Nat × Nat × Nat) × Nat),
    (ts.foldl (dstep digitBases) st).1.length = st.1.length + 2 * RCB_GATES * ts.length
    ∧ (ts.foldl (dstep digitBases) st).2.2 = st.2.2 + 2 * RCB_COLS * ts.length := by
  intro ts
  induction ts with
  | nil => intro st; simp
  | cons t rest ih =>
    intro st
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (dstep digitBases st t)
    obtain ⟨e1, e2⟩ := dstep_one digitBases st t
    rw [h1, h2, e1, e2, List.length_cons]
    exact ⟨by ring, by ring⟩

/-- **`ladderGatesFrom_counts`** — an `n`-digit ladder is `66·n` core gates and `884·n` fresh
columns. -/
theorem ladderGatesFrom_counts (digitBases : List (Nat × Nat × Nat)) (n : Nat)
    (acc0 : Nat × Nat × Nat) (fresh0 : Nat) :
    (ladderGatesFrom digitBases n acc0 fresh0).1.length = 2 * RCB_GATES * n
    ∧ (ladderGatesFrom digitBases n acc0 fresh0).2.2 = fresh0 + 2 * RCB_COLS * n := by
  obtain ⟨h1, h2⟩ := dstep_counts digitBases (List.range n) ([], acc0, fresh0)
  rw [List.length_range] at h1 h2
  exact ⟨by simpa [ladderGatesFrom] using h1, h2⟩

/-- One MSM term is a ladder plus one accumulating RCB add. -/
theorem msmTermStep_one (digitsOf : Nat → List (Nat × Nat × Nat)) (nDigits : Nat)
    (zeroBases : Nat × Nat × Nat) (st : List VmConstraint2 × (Nat × Nat × Nat) × Nat) (t : Nat) :
    (msmTermStep digitsOf nDigits zeroBases st t).1.length
      = st.1.length + (2 * RCB_GATES * nDigits + RCB_GATES)
    ∧ (msmTermStep digitsOf nDigits zeroBases st t).2.2
      = st.2.2 + (2 * RCB_COLS * nDigits + RCB_COLS) := by
  obtain ⟨hl1, hl2⟩ := ladderGatesFrom_counts (digitsOf t) nDigits zeroBases st.2.2
  refine ⟨?_, ?_⟩ <;>
    simp only [msmTermStep, List.length_append, pallasCompleteAdd_length,
      pallasCompleteAdd_fresh, hl1, hl2, RCB_GATES, RCB_COLS] <;> omega

/-- ⚑ **`msmGatesFrom_counts`** — the closed-form price of the `n`-term MSM AIR:
`n · (66·nDigits + 33)` core gates and `n · (884·nDigits + 442)` fresh columns. Proved by
induction; evaluated at no `n` in particular, which is what makes it a pricing INSTRUMENT rather
than a measurement of one instance. -/
theorem msmGatesFrom_counts (digitsOf : Nat → List (Nat × Nat × Nat)) (nDigits : Nat)
    (zeroBases : Nat × Nat × Nat) : ∀ (ts : List Nat)
    (st : List VmConstraint2 × (Nat × Nat × Nat) × Nat),
    (ts.foldl (msmTermStep digitsOf nDigits zeroBases) st).1.length
      = st.1.length + (2 * RCB_GATES * nDigits + RCB_GATES) * ts.length
    ∧ (ts.foldl (msmTermStep digitsOf nDigits zeroBases) st).2.2
      = st.2.2 + (2 * RCB_COLS * nDigits + RCB_COLS) * ts.length := by
  intro ts
  induction ts with
  | nil => intro st; simp
  | cons t rest ih =>
    intro st
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (msmTermStep digitsOf nDigits zeroBases st t)
    obtain ⟨e1, e2⟩ := msmTermStep_one digitsOf nDigits zeroBases st t
    rw [h1, h2, e1, e2, List.length_cons]
    exact ⟨by ring, by ring⟩

/-- Core gates of the whole opening-check AIR: the MSM, one more RCB add for `delta`, and the two
terminal zero gates. -/
def openingCheckGateCount (n nDigits : Nat) : Nat :=
  n * (2 * RCB_GATES * nDigits + RCB_GATES) + RCB_GATES + 2

/-- Fresh columns of the whole opening-check AIR. -/
def openingCheckColCount (n nDigits : Nat) : Nat :=
  n * (2 * RCB_COLS * nDigits + RCB_COLS) + RCB_COLS

/-- ⚑ **`openingCheckGates_counts`** — and the price of the WHOLE emitted opening check, closed
form, for every term count and every scalar width. -/
theorem openingCheckGates_counts (digitsOf : Nat → List (Nat × Nat × Nat)) (nDigits : Nat)
    (zeroBases deltaBases : Nat × Nat × Nat) (n : Nat) (acc0 : Nat × Nat × Nat)
    (fresh0 qX qZ : Nat) :
    (openingCheckGates digitsOf nDigits zeroBases deltaBases n acc0 fresh0 qX qZ).1.length
      = openingCheckGateCount n nDigits
    ∧ (openingCheckGates digitsOf nDigits zeroBases deltaBases n acc0 fresh0 qX qZ).2.2
      = fresh0 + openingCheckColCount n nDigits := by
  obtain ⟨h1, h2⟩ := msmGatesFrom_counts digitsOf nDigits zeroBases (List.range n)
    ([], acc0, fresh0)
  rw [List.length_range] at h1 h2
  have h1' : (msmGatesFrom digitsOf nDigits zeroBases n acc0 fresh0).1.length
      = (2 * RCB_GATES * nDigits + RCB_GATES) * n := by simpa [msmGatesFrom] using h1
  have h2' : (msmGatesFrom digitsOf nDigits zeroBases n acc0 fresh0).2.2
      = fresh0 + (2 * RCB_COLS * nDigits + RCB_COLS) * n := by simpa [msmGatesFrom] using h2
  refine ⟨?_, ?_⟩ <;>
    simp only [openingCheckGates, pointAtInfinityGates, List.length_append,
      List.length_cons, List.length_nil, pallasCompleteAdd_length, pallasCompleteAdd_fresh,
      h1', h2', openingCheckGateCount, openingCheckColCount] <;> ring

#assert_axioms dstep_counts
#assert_axioms ladderGatesFrom_counts
#assert_axioms msmGatesFrom_counts
#assert_axioms openingCheckGates_counts

/-- **RCB complete adds** the check performs — the natural ROW unit of a real dregg trace, where
one complete add occupies one row of `RCB_COLS` columns. -/
def openingCheckRcbAdds (n nDigits : Nat) : Nat := n * (2 * nDigits + 1) + 1

/-! The counts theorem, checked against a MATERIALISED generator at a small instance — so the
closed form is verified against the emitted list and not merely asserted about it. -/
#guard (msmGatesFrom (fun _ => [(100,109,118),(127,136,145)]) 2 (0,9,18) 3 (27,36,45) 300).1.length
    == 3 * (2 * 33 * 2 + 33)
#guard (msmGatesFrom (fun _ => [(100,109,118),(127,136,145)]) 2 (0,9,18) 3 (27,36,45) 300).2.2
    == 300 + 3 * (2 * 442 * 2 + 442)
#guard (openingCheckGates (fun _ => [(100,109,118),(127,136,145)]) 2 (0,9,18) (54,63,72) 3
    (27,36,45) 300 5000 5009).1.length == openingCheckGateCount 3 2
#guard (openingCheckGates (fun _ => [(100,109,118),(127,136,145)]) 2 (0,9,18) (54,63,72) 3
    (27,36,45) 300 5000 5009).2.2 == 300 + openingCheckColCount 3 2

/-! ## §5b — ⚑ THE PRICE AGAINST DREGG'S REAL GEOMETRY.

⚑ **WHAT THE PRICE IS A PRICE OF, before any of the numbers.** Every figure in this section counts
the gates this family EMITS, and the emitted Pasta multiply is `PastaField.fpMulCore` — ONE degree-2
gate, 81 cross-products, no limb ranges, no carry pins. That gate does not enforce the multiply at
BabyBear: its nine quotient limbs are free columns whose weights `p·2^(30 i)` are nonzero mod
`p_felt`, so its `p_felt` reading is satisfiable at every operand triple (`PastaField` §6.4, computed
on the emitted bytes). A multiply that IS sound at BabyBear needs the 13-bit/20-limb re-encoding at
**≈10³ constraints** (`LightClientMinaAir` §1b) rather than 1, so every gate count, row count and
second below **moves by roughly three orders** against a sound gate. Nothing here is softened for
that: these are honest counts of the object on disk, and the object on disk is the unsound one.

The deployed root prover, measured (`circuit-prove/src/ivc_turn_chain.rs`,
`circuit-prove/src/accumulator.rs`, `circuit/src/plonky3_prover.rs`,
`circuit-prove/tests/root_air_constraint_census.rs`, `docs/DESIGN-tiny-automata-fast-proofs.md`):

  * field **BabyBear** `2^31 − 2^27 + 1`, challenge field `BinomialExtensionField<BabyBear,4>`;
  * root evaluation domain **`|D⁰| = 2^22`** = trace `2^16` × `log_blowup 6`, 16 FRI layers at
    arity 2, 19 queries — so the deployed root's **trace height is `2^16 = 65,536` rows**;
  * hard ceiling from `BabyBear::TWO_ADICITY = 27`: at `log_blowup 6`, **`2^21` trace rows**;
  * `MAX_TRACE_WIDTH = 1024` columns (`circuit/src/dsl/circuit.rs:691`);
  * measured prove cost **`F ≈ 0.094 ms` PER TRACE ROW, width-independent for the FRI fold**;
  * and the fold is SEGMENTED: `prove_turn_chain_recursive_streaming` holds
    `O(W + log2(K/W))` proofs for ANY `K`, and `Accumulator::accumulate` is `O(1)`.

`nDigits = 255` throughout — the full Pallas scalar width K4b emits. The GLV/Shamir halving to
128 that `PastaScalarMul` §6.1 names as prover-side preprocessing is NOT applied, so every number
below is a CEILING that a built GLV digit selector would roughly halve. -/

/-- The deployed root's trace height, `WRAP_LOG_CEIL = 16`. -/
def DREGG_ROOT_ROWS : Nat := 65536
/-- The two-adicity ceiling at the deployed `log_blowup = 6`. -/
def DREGG_MAX_ROWS : Nat := 2097152
/-- `MAX_TRACE_WIDTH`, `circuit/src/dsl/circuit.rs:691`. -/
def DREGG_MAX_WIDTH : Nat := 1024

-- ⚑ STATEMENT (B), THE OPENING RELATION — 34 terms (15 `L` + 15 `R` + the 47-term aggregate
-- + `u_base` + `sg` + `srs.h`), `delta` at coefficient 1.
#guard openingCheckRcbAdds 34 255 == 17375
#guard openingCheckGateCount 34 255 == 573377
#guard openingCheckColCount 34 255 == 7679750
-- ⚑ AT ONE COMPLETE ADD PER ROW: 17,375 rows × 442 columns — **inside ONE deployed root
-- segment**, at 26% of its height, and inside `MAX_TRACE_WIDTH` with 582 columns to spare.
#guard openingCheckRcbAdds 34 255 < DREGG_ROOT_ROWS
#guard RCB_COLS < DREGG_MAX_WIDTH
-- 7.68M trace cells — 13× the 578,720 cells of the deployed leaf descriptor, which proves in
-- 638 ms. At the measured 0.094 ms/row the FRI-fold floor is ~1.6 s.
#guard openingCheckRcbAdds 34 255 * RCB_COLS == 7679750

-- STATEMENT (A), the `⟨s, srs.g⟩` leg at Mina's wrap SRS (`|srs.g| = 2^15`), TERM-BY-TERM.
#guard openingCheckRcbAdds 32768 255 == 16744449
-- 16.7M complete adds. Past the `2^21` two-adicity ceiling by 8×, and 256 root segments.
#guard openingCheckRcbAdds 32768 255 > DREGG_MAX_ROWS
#guard (openingCheckRcbAdds 32768 255 + DREGG_ROOT_ROWS - 1) / DREGG_ROOT_ROWS == 256

/-- The bit-plane Horner scan's add count (`PastaIpaFold.hornerAdds`): `nbits` doublings plus one
add per set bit, at an average Hamming weight of `nbits/2`. The identity is PROVED
(`msmHorner_eq_msmN`); the AIR for it is NOT emitted here (§6.2). -/
def hornerRcbAdds (k nbits : Nat) : Nat := nbits + 2 ^ k * (nbits / 2)

-- With the shared doubling chain the same leg is 4.16M adds — 64 root segments, still past the
-- single-proof ceiling by 2×, and a 4× improvement over term-by-term.
#guard hornerRcbAdds 15 255 == 4161791
#guard (hornerRcbAdds 15 255 + DREGG_ROOT_ROWS - 1) / DREGG_ROOT_ROWS == 64
#guard hornerRcbAdds 15 255 > DREGG_MAX_ROWS
#guard openingCheckRcbAdds 32768 255 / hornerRcbAdds 15 255 == 4

/-- The opening check at Mina's real shape, packaged as an `EffectVmDescriptor2`. The constraint
list is a TERM, not a materialised value — `openingCheckGates_counts` is what prices it. -/
def minaOpeningCheckDesc : EffectVmDescriptor2 :=
  { name        := "dregg-mina-ipa-opening-check::v1"
  , traceWidth  := RCB_COLS
  , piCount     := 0
  , tables      := []
  , constraints := (openingCheckGates (fun i => (List.range 255).map
                      (fun t => (1000000 + i * 300000 + t * 27,
                                 1000009 + i * 300000 + t * 27,
                                 1000018 + i * 300000 + t * 27)))
                      255 (0, 9, 18) (27, 36, 45) 34 (54, 63, 72) 1000 999000 999009).1
  , hashSites   := []
  , ranges      := [] }

#guard minaOpeningCheckDesc.traceWidth == 442

/-! ## §6 — WHAT THIS DOES NOT DO. Said at the CURRENT resolution, not the intended one.

1. **P10 is untouched.** `openingCheck_forces` says a satisfying assignment makes the verifier's
   equation HOLD. That a prover which passes it must KNOW an opening is the IPA/dlog extraction
   argument — the rewinding object (`Dregg2.Crypto.IpaOpeningExtractionFloor`'s named-and-
   undischarged forking argument) plus `DLHardQuant`, already ⊤-vacuous with no `Eff`. Passing ≠
   knowing, here as everywhere. A dregg STARK proof OF this AIR inherits that floor unchanged,
   and inherits the FRI floor (51 calculator bits) on top of it.

2. **The `⟨s, srs.g⟩` leg (A) is the SAME theorem at `n = 32768` — but NOT the cheap layout.**
   `msmGatesFrom_forces` applies verbatim; what does not apply is the budget (§5b). The identity
   that fixes it is `PastaIpaFold.msmHorner_eq_msmN` — one shared doubling chain, one add per set
   bit — and **its AIR IS NOT EMITTED HERE.** That is the precise named gap: a bit-plane Horner
   generator plus an `msmHornerGates_forces` in the shape of §2, folding over bit planes instead
   of digits. The IDENTITY is proved and axiom-clean; the CIRCUIT for it does not exist. Note
   also that a Horner AIR must emit a row for every (plane, term) pair or prove the skipped ones
   had a zero bit — the 4.16M figure is the SET-BIT count, and the data-independent layout is
   255 × 32768 = 8.36M. Neither fits one proof.

3. **`srs.g` remains the largest single piece of trusted data in the stack.** On-curve-checked,
   not derived; deriving it needs in-kernel BLAKE2b + SvdW at 32,768 inputs.

4. **The RCB completeness transport is inherited, not re-proved.** The forcing lands on the
   `rcbAddZmod` FORMULA fold. That this fold is the group law on Pallas is RCB'15 Thm 1 — the
   residual every rung 5a–5h already carries. No new assumption is introduced here.

5. **Canonicity is not gated.** The emitted list is the CORE gates. The congruence chain, and
   therefore §4's conclusion, needs no limb ranges — but a deployed descriptor that must reject
   non-canonical limbs pays `PastaField.pastaLimbRange`'s `9·(30+1) = 279` constraints and 270
   bit columns per ranged element, roughly a 30× column blowup that §5b does NOT include.

   ⚠ **The width objection that used to end this item is RETRACTED, and it was hiding the real
   one.** It read *"at that width the check no longer fits `MAX_TRACE_WIDTH = 1024` in one row"*.
   `MAX_TRACE_WIDTH` is the **v1 DSL** cap (`dsl::circuit::ProgramDescriptor::validate`) and the
   IR-v2 path these descriptors ride does not consult it — `check_descriptor2` bounds every column
   against the descriptor's OWN `trace_width` and nothing else, which
   `circuit/tests/pasta_derive_prove.rs::the_v1_width_cap_does_not_bind_the_ir2_path` states as a
   MEASUREMENT: 2131 columns parse, check and prove. §7 of `PastaMsmLayouts` already called the cap
   advisory. So width is not what keeps `pastaLimbRange` out of the emitted objects; it is out
   because its six caller wrappers have zero call sites anywhere (`PastaField` §6.4). And the ranges
   would not close the gap if they were wired: the `fpMul` body still reaches `p² ≈ 2^508`, so the
   `p_felt` reading still admits any witness whose ℤ body is a nonzero multiple of `p_felt`. Ranges
   are necessary, not sufficient.

   The shared K1 residual (the `ℤ ↔ felt` width gap) stands unchanged, and `PastaField` §6.4 now
   says what it costs on the emitted bytes rather than naming it.

6. **The digits are represented inputs, not derived.** As in `pallasLadder_forces`, which
   combination of `{P, φ(P), P+φ(P)}` each digit is remains prover-side; a verifier that must
   CHECK the scalar decomposition needs K2's endo recomposition gate. Named, not built. The
   `nDigits = 255` in §5b is therefore a ceiling: a built GLV selector roughly halves it.

7. **The reality gate is NOT replaced.** `MinaWrapOpeningGate.opening_relation_holds` and its ten
   tamper poles stay exactly where they are and keep doing their job — they are the INSTANCE
   differential against o1-labs' own dumped values, and they are what says the equation this AIR
   forces is the equation o1-labs' verifier actually checks. This file is the CHECKER theorem.
   Both exist; they answer different questions.
-/

end Dregg2.Circuit.Emit.PastaMsmAir
