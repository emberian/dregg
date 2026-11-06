/-
# `Dregg2.Circuit.Emit.MinaWrapXiEndoLift` — ξ STOPS BEING TOLD.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** The emitted object is `MinaWrapCommitMachine.commitAir` — the SAME
machine, the SAME three opcodes, the SAME instruction ROM and register window `MinaWrapCommitStages`
emits its four stages on — carrying a different program and a different pair of boundary pins. This
file authors **no new gate**. Rust parses the descriptor, fills cells and runs the deployed prover.
House Law #1.

## ⚑ THE DEFECT THIS FILE CLOSES, stated as its author left it

`MinaWrapXiAggregateMsm` §4:

> **`ξ` ITSELF.** `SCAL` is the 47 powers as descriptor constants. […] **AND `ξ` IS ITSELF A
> TRANSCRIPT OUTPUT.** Even welded to the chain, `ξ` enters as a public input; binding it to the
> Fq sponge's squeeze is `MinaWrapVerifierSponge`'s cone, not this one.

That cone landed. `MinaBlockFqTranscript.the_machine_squeezes_the_real_blocks_v_and_u` proves the
in-AIR Fq sponge — 2 048 emitted rows, the real `fq_kimchi` constants, a 45-permutation-deep state
derived from Mina devnet block **539508**'s own 91-element phase-2 tape — ends with
`LINK_V_RAW % 2^128 = WRAP_V_CHAL`. And `WRAP_V_CHAL` is `v′`, the **polyscale prechallenge**.

**The step between `v′` and `ξ` is `ScalarChallenge::to_field(endo_r)`** (`sponge.rs:190-226`), and
`MinaWrapChallenges` §2's own note says where it lives and that it is deliberately not there:

> `Circuit.Emit.KimchiVerify.endoMap`, there is exactly one of it in this tree, and it belongs with
> the CONSUMER.

This file is that consumer. It emits the endomorphism lift **as an AIR** — 64 rounds of
double-and-conditional-±1 over `ZMod qN` with a 128-bit in-circuit decomposition whose closing
assertion pins the bits to the challenge — and it proves the emitted program's output is o1-labs'
own `ξ` on the block's own `v′`.

## ⚑ THE WELD, AND ITS WIDTH — read this before citing anything below

Two emitted objects are tied here by a **public-input equality**, and the tie is stated at the width
it actually has rather than at the width a digest would suggest:

  * `dregg-mina-xi-endo-lift::v1`'s LAST-row pin publishes `ξ` as **`SK = 32` eight-bit limbs**;
  * `dregg-mina-xi-scalar-vector::v2`'s FIRST-row pin consumes `ξ` as the same 32 limbs.

`the_endo_output_block_is_the_chain_input_block` is that equality, and it is **32 felts / 255 bits
of agreement, elementwise** — not a one-felt commitment. That distinction is the whole reason this
theorem is stated on the limb LISTS: the `proof_bind` seam's `commit`/`vk`/`bound` are one felt each
against an eight-lane object, which is `2^31` and below this repo's bar. A PI equality between two
descriptors is exactly where that mistake would be free to make, and it is not made here.

⚠ **And the tie is elementwise, so it has no birthday bound at all.** There is no digest to collide;
`a_perturbed_output_limb_breaks_the_weld` moves ONE of the 32 felts and the equality is refuted.

## ⚑ WHAT IS COMPUTED NOW, AND WHAT IS STILL TOLD

  1. `v′` — **COMPUTED**, by `MinaBlockFqTranscript`'s emitted sponge, from the block's tape.
  2. `ξ` — **COMPUTED**, here, from `v′`. `the_machine_computes_the_endo_lift`.
  3. `ξ⁰ … ξ⁴⁶` — **COMPUTED**, by `MinaWrapCommitStages.xiChainProg`'s 46 multiplies, from the ξ
     this file publishes; the two are joined by the PI equality above.
  4. the ξ-AGGREGATE's 47 SCALARS — ⚑ **UPDATED 2026-08-05: the generator of those scalars is now a
     WIRE value.** The obstruction §7.4 named (*"`piCount = 27` publishes only the output `C`"*) was
     a MISSING SURFACE, and the surface exists: `PastaMsmBucketed`'s `chalPinGates`/`chalThreadGates`
     widen the aggregate to `27 + 192` public inputs, the scalar chain publishes the six-value
     squaring basis `(ξ³², ξ¹⁶, ξ⁸, ξ⁴, ξ², ξ)` on 192 felts of its own, and `MinaWrapXiBasisWeld`
     ties the two **elementwise, 192 felts, no digest** — and then maps that basis through
     `PastaMsmScalarDerive`'s tensor to `T_COVER`'s 7 552 declared digits.
     ⚠ The digits themselves are still DESCRIPTOR data (permutation-forced by `T_COVER`, and not
     re-derived by an emitted gate). What moved is *where the challenge comes from*, not *who forces
     the digits*. Read `MinaWrapXiBasisWeld` §4 before citing any of it.

⚑ **THE UNSOUND MULTIPLY IS NOT INHERITED HERE, AND THAT IS WORTH SAYING PLAINLY.** This descriptor
is `PastaFieldSound.qLimb`, like every descriptor in `MinaWrapCommitStages`. The `fpMulCore`
downgrade belongs to `PastaMsmBucketed`'s rows and travels only with the aggregate; it is not
lifted, not repaired and not spread. `MinaWrapXiAggregateMsm` §4's third bullet stands unchanged.

## Axiom hygiene

General theorems are `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). Facts
about concrete data are `native_decide`, pinned `#assert_compiled` (since 2026-11-06). No `sorry`/`admit`. Named theorems, not `#guard`s. NEW file; not imported by the `Dregg2` root, per
house practice for gates. Import line:
`import Dregg2.Circuit.Emit.MinaWrapXiEndoLift`
-/
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.MinaBlockFqTranscript
import Dregg2.Circuit.Emit.MinaWrapCommitStages
import Dregg2.Circuit.Emit.PastaCurve
import Dregg2.Circuit.Emit.EffectLowerCertified

namespace Dregg2.Circuit.Emit.MinaWrapXiEndoLift

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.EffectAirIR (EffectAir)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB limbAt)
open Dregg2.Circuit.Emit.PastaCurve (lambdaPallas)
open Dregg2.Circuit.Emit.KimchiVerify (endoMap bitAt)
open Dregg2.Circuit.Emit.MinaWrapCommitMachine
open Dregg2.Circuit.Emit.MinaWrapCommitStages
  (Step mulR addR subR addI subI eqR wit emitInit padTo instrs witsOf piPair qLimbFast pinPair
   PI64 ZERO TX TY)

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-! ## §1 — THE REFERENCE, AND IT IS THE TREE'S ONLY `to_field`.

⚑ There is no second implementation of the endomorphism lift here. `endoLiftQ` is
`KimchiVerify.endoMap` — the transcription of `sponge.rs:190-226` this tree already had — read at
`ZMod qN` and projected back to a `Nat` by `ZMod.val`. A file that re-authored the fold would be
free to re-author it WRONG, and every theorem below would still be green about its own function. -/

/-- `ScalarChallenge(chal).to_field(endo)` **in the Pallas SCALAR field**, as a canonical `Nat`. -/
def endoLiftQ (endo chal : Nat) : Nat := (endoMap ((endo : ZMod qN)) chal).val

/-- The block's polyscale prechallenge `v′`, from the emitted Fq-sponge cone. -/
def V_CHAL : Nat := MinaBlockFqTranscript.WRAP_V_CHAL

/-- The block's evalscale prechallenge `u′`, the OTHER lane of the same squeeze. -/
def U_CHAL : Nat := MinaBlockFqTranscript.WRAP_U_CHAL

/-- The block's polyscale `ξ`, as `MinaWrapAggregationGate` carries it. -/
def XI : Nat := MinaWrapAggregationGate.XI

/-- ⚑⚑ **ξ IS THE ENDOMORPHISM LIFT OF THE BLOCK'S OWN SPONGE SQUEEZE.**

The left side reads `v′` — the value `MinaBlockFqTranscript`'s emitted 2 048-row absorb ENDS ON,
`the_machine_squeezes_the_real_blocks_v_and_u` — through `sponge.rs`'s `to_field`. The right side is
the polyscale `MinaWrapAggregationGate` uses to build `COMBINED_GOLD`, dumped from `oracles.v`.

Until this line, those two numbers had no relation in this tree: one came out of a sponge, the other
was typed. **This is the join, and one wrong bit anywhere in either would refute it.** -/
theorem the_polyscale_is_the_endo_lift_of_the_squeeze :
    endoLiftQ lambdaPallas V_CHAL = XI := by decide

/-- ⚑ **AND IT IS THE `v′` LANE, NOT THE `u′` ONE.** The same squeeze produces both; a verifier that
read lane 1 for lane 0 would combine the openings at the evalscale. The data refutes it. -/
theorem the_evalscale_prechallenge_lifts_elsewhere :
    endoLiftQ lambdaPallas U_CHAL ≠ XI := by native_decide

/-- ⚑ **AND THE JOIN IS REFUTABLE AT THE SQUEEZE.** One added to `v′` — the smallest possible move
in the sponge's output — misses the polyscale. -/
theorem a_perturbed_squeeze_misses_the_polyscale :
    endoLiftQ lambdaPallas (V_CHAL + 1) ≠ XI := by native_decide

/-- ⚑ **AND THE LIFT IS IN `q`, NOT IN `p`.** The classic Pasta error, refuted rather than avoided
by convention: the SAME fold over the SAME challenge read in the BASE field is a different scalar,
whose leading thirty digits agree with `ξ` — which is exactly how such a bug survives a spot check.
`MinaWrapCommitStages.the_base_field_reduction_of_xi_squared_is_a_different_scalar` is the same
refutation one level up. -/
theorem the_base_field_lift_is_a_different_scalar :
    (endoMap ((lambdaPallas : ZMod pN)) V_CHAL).val ≠ XI := by native_decide

/-- ⚑ **AND THE ENDO SCALAR IS THE CURVE'S, NOT A NUMBER THIS FILE CHOSE.** `lambdaPallas` is
`PastaCurve`'s cube root of unity in `ZMod qN` — the `endo_r` `to_field` multiplies by — and it is
the same constant the Rust bridge pins (`bridge/src/mina_opening_check.rs:563`). -/
theorem the_endo_scalar_is_the_pallas_cube_root :
    lambdaPallas ^ 3 % qN = 1 ∧ lambdaPallas ≠ 1 ∧ lambdaPallas < qN := by
  refine ⟨PastaCurve.lambdaPallas_cube, PastaCurve.lambdaPallas_ne_one, ?_⟩
  decide

/-- ⚑ **AND A `ScalarChallenge` IS 128 BITS.** `DefaultFrSponge::squeeze` keeps two 64-bit limbs
(`sponge.rs:265-277`), so the value the lift consumes is BELOW the truncation — which is what makes
the in-circuit decomposition below exactly 128 places wide and, at `2^128 < q`, CANONICAL with no
certificate: a 128-bit bit vector has exactly one field representative. -/
theorem the_prechallenges_are_below_the_truncation :
    V_CHAL < 2 ^ 128 ∧ U_CHAL < 2 ^ 128 ∧ 2 ^ 128 < qN := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §2 — THE PROGRAM.

Eleven of the machine's twelve registers, and the allocation is the lift's own state:

  * `VP` — the prechallenge, PINNED on the first row and never written.
  * `OUT` — the lifted scalar, PINNED on the last row.
  * `A`, `B` — `to_field`'s two accumulators, both starting at the field `2`.
  * `B0`, `B1` — the round's two bits, each pinned boolean by a multiply and an assert.
  * `S` — `±1`, computed as `2·b₀ − 1` rather than branched on.
  * `SC` — the scalar accumulator that makes the bits the bits OF something. -/

def VP : Nat := TX
def OUT : Nat := TY
def A : Nat := 3
def B : Nat := 4
def B0 : Nat := 5
def B1 : Nat := 6
def S : Nat := 7
def T0 : Nat := 8
def T1 : Nat := 9
def SC : Nat := 10

theorem the_allocation_fits_the_register_file :
    VP < NREG ∧ OUT < NREG ∧ SC < NREG ∧ VP ≠ OUT ∧ NREG = 12 := by native_decide

/-- ⚑ **ONE ROUND OF `to_field_with_length`, AS 18 INSTRUCTIONS.**

`sponge.rs:200-212`: double `a` and `b`; `s = ±1` by bit `2i`; add `s` to `b` when bit `2i+1` is
clear, to `a` when it is set. Written branch-free, because the machine has no branch:

  `s := 2·b₀ − 1` · `a := a + b₁·s` · `b := b + (1 − b₁)·s`

and `(1 − b₁)·s` is `s − b₁·s`, which the round already has in `T0`.

⚑ The last four instructions are the SCALAR FOLD, `sc := 4·sc + 2·b₁ + b₀`, and they are the reason
the bits are not 128 free choices: `emitBit`'s note one file over says it, and the closing
`eqR SC VP` is where it binds. -/
def endoRound (chal i : Nat) : List Step :=
  [ (addR A A A, 0), (addR B B B, 0)
  , (wit B1, bitAt chal (2 * i + 1)), (mulR B1 B1 T0, 0), (eqR T0 B1, 0)
  , (wit B0, bitAt chal (2 * i)),     (mulR B0 B0 T0, 0), (eqR T0 B0, 0)
  , (addR B0 B0 S, 0), (subI S 1 S, 0)
  , (mulR B1 S T0, 0), (addR A T0 A, 0)
  , (subR S T0 T1, 0), (addR B T1 B, 0)
  , (addR SC SC SC, 0), (addR SC B1 SC, 0), (addR SC SC SC, 0), (addR SC B0 SC, 0) ]

/-- The 64 rounds, `i = 63 … 0` — `to_field_with_length`'s own reversed loop, so the bit pair the
first emitted round consumes is the challenge's most significant. -/
def endoRounds (chal : Nat) : Nat → List Step
  | 0 => []
  | n + 1 => endoRound chal n ++ endoRounds chal n

/-- ⚑ **THE WHOLE LIFT.** Init, 64 rounds, the scalar assertion, and `a·endo_r + b`.

`lambdaPallas` enters as a ROM IMMEDIATE — a descriptor cell, so the bus refuses a re-chosen endo
scalar; `V_CHAL` does NOT, it is a register operand pinned from the public input, so the
TRANSCRIPT binding rests on the PIN. That is the same pole split `MinaBlockFqTranscript` names for
its own absorbed value, and it is what the Rust polarities must fire on separately. -/
def endoSteps (chal : Nat) : List Step :=
  emitInit ++ [(addI ZERO 2 A, 0), (addI ZERO 2 B, 0), (subR ZERO ZERO SC, 0)]
  ++ endoRounds chal 64
  ++ [(eqR SC VP, 0), (addI ZERO lambdaPallas T0, 0), (mulR A T0 T0, 0), (addR T0 B OUT, 0)]

/-- The emitted height. ⚑ A power of two, which the deployed prover requires and which the ROM
manifest's length — a PERMUTATION — must equal. -/
def ENDO_HEIGHT : Nat := 2048

def endoProg : List Step := padTo ENDO_HEIGHT (endoSteps V_CHAL)

/-- ⚑ **THE CENSUS.** 1 160 real instructions in a 2 048-row trace: 4 of init, 18 × 64 of lift, 4 of
close. A reader pricing this object should know 43% of the rows are padding bought for the power of
two, and that the padding is `add R0, #0 → ∅`, a real ALU operation with no destination. -/
theorem the_program_is_eleven_hundred_and_sixty_instructions :
    (endoSteps V_CHAL).length = 1160 ∧ endoProg.length = ENDO_HEIGHT
      ∧ ENDO_HEIGHT = 2 ^ 11 ∧ 4 + 18 * 64 + 4 = 1160 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## §3 — WHAT THE EMITTED PROGRAM COMPUTES.

The machine's own strict interpreter, from the pinned input, on the emitted instruction list — not
on a tidied copy of it. `runRegsVecAt` is `runRowsVecAt`'s state thread with the row emission
dropped; both bottom out in the SAME `stepVecAt`, so a program that computed something else here
would emit a trace the descriptor refuses. -/

/-- The register file after a whole program, strictly. -/
def runRegsVecAt (N : Nat) (rs : List Nat) (wits : Nat → Nat) (pc : Nat) :
    List Instr → List Nat
  | [] => rs
  | I :: rest => runRegsVecAt N (stepVecAt N rs (wits pc) I) wits (pc + 1) rest

/-- ⚑ **AND IT IS `runRowsVecAt`'s OWN STATE THREAD.** Stated so "the interpreter below is the
generator above" is a theorem and not a comment: both recurse through `stepVecAt` on the same
witness stream, so a fact about the final register file is a fact about the emitted trace's last
row's inputs. -/
theorem runRegsVecAt_threads_the_trace_generator (N : Nat) (pl : Nat → ℤ) (wits : Nat → Nat) :
    ∀ (prog : List Instr) (rs : List Nat) (pc : Nat),
      (runRowsVecAt N pl rs wits pc prog).length = prog.length
        ∧ runRegsVecAt N rs wits pc prog
          = (match prog with
             | [] => rs
             | I :: rest => runRegsVecAt N (stepVecAt N rs (wits pc) I) wits (pc + 1) rest) := by
  intro prog
  induction prog with
  | nil => intro _ _; exact ⟨rfl, rfl⟩
  | cons I rest ih =>
      intro rs pc
      refine ⟨?_, rfl⟩
      show (runRowsVecAt N pl (stepVecAt N rs (wits pc) I) wits (pc + 1) rest).length + 1
        = rest.length + 1
      exact congrArg (· + 1) (ih _ _).1

/-- The register file the emitted program ends in, from the pinned prechallenge. -/
def endoRegs : List Nat :=
  runRegsVecAt qN (pinVec VP V_CHAL) (witsOf endoProg) 0 (instrs endoProg)

/-- ⚑⚑ **THE MACHINE COMPUTES THE LIFT.** The register the last-row pin publishes holds
`ScalarChallenge(v′).to_field(endo_r)` — which §1 already proved is the block's own `ξ`. This is the
sentence "the aggregate's scalars are the verifier's to be told" stops being true of. -/
theorem the_machine_computes_the_endo_lift :
    readVec endoRegs OUT = endoLiftQ lambdaPallas V_CHAL := by decide

/-- ⚑ **THE SCALAR FOLD LANDS ON THE CHALLENGE — AT THE HONEST WITNESS.** `SC` ends on `v′` itself,
so on this run the 128 witnessed bits ARE the bits of the published prechallenge.

⚠⚠ **CLOSURE KIND, CORRECTED 2026-08-08 — THIS IS A COMPLETENESS `decide`, NOT A FORCING THEOREM.**
It was called `the_scalar_fold_pins_the_challenge` and read *"…and not 128 free choices that happen
to reach a convenient `A` and `B`"*, which is the SOUNDNESS direction — quantified over every
satisfying trace. This file has no `_of_sat` theorem and states nothing over satisfying traces at
all: `endoRegs` is the interpreter run on `witsOf endoProg` at the single constant `V_CHAL`. What is
established is that the honest witness lands where it should. Whether a DIFFERENT bit vector could
also land there is not addressed here, and the sentence that said it was is deleted rather than
softened. -/
theorem the_scalar_fold_lands_on_the_challenge_at_the_honest_witness :
    readVec endoRegs SC = V_CHAL := by native_decide

/-- ⚑ **AND THE ZERO REGISTER IS FORCED, AND THE INPUT IS NEVER WRITTEN.** `VP` ends holding what
the first-row pin put there — so the closing assertion compares the fold against the PUBLIC INPUT
and not against something the program rewrote on the way. -/
theorem the_input_register_survives_the_program :
    readVec endoRegs VP = V_CHAL ∧ readVec endoRegs ZERO = 0 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## §4 — THE EMITTED OBJECT. -/

/-- ⚑ **AT `qLimb`, THE PALLAS SCALAR PRIME.** The lift is scalar-field arithmetic; emitting it at
`pLimb` would be an AIR for the wrong field, and `the_base_field_lift_is_a_different_scalar` is what
that mistake would produce. -/
def endoAir : EffectAir :=
  { commitAir Dregg2.Circuit.Emit.PastaFieldSound.qLimb (instrs endoProg) with
    legs := (commitAir Dregg2.Circuit.Emit.PastaFieldSound.qLimb (instrs endoProg)).legs
              ++ pinPair VP OUT }

theorem endoAir_mainRailOk : endoAir.mainRailOk = true := by
  unfold endoAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨commitAir_mainRailOk _ _, ?_⟩
  simp only [Dregg2.Circuit.Emit.MinaWrapCommitStages.pinPair,
    Dregg2.Circuit.Emit.MinaWrapCommitStages.pinBlock, List.all_append, List.all_map,
    Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- ⚑ **NO PIN IS DECORATIVE** — the 64 pins publish `VP`'s and `OUT`'s limb columns, which the
routing gates and the register window legs read. Named so `endoTiedAir` takes the term instead of
re-deriving it: the `TiedAir` fields are `autoParam`s defaulting to `by decide`. -/
theorem endoAir_pinsTied : endoAir.pinsTied = true := by decide

/-- ⚑ **THE TIED SOURCE** — `endoAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def endoTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := endoAir
  ok   := endoAir_mainRailOk
  tied := endoAir_pinsTied

def endoDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-xi-endo-lift::v1" CM_WIDTH PI64 [] endoTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem endoDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines endoDesc [] endoAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-xi-endo-lift::v1" CM_WIDTH PI64 [] endoTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs that reason through `lowerAir`. -/
theorem endoDesc_eq_lowerAir :
    endoDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-mina-xi-endo-lift::v1" CM_WIDTH PI64 [] endoAir := rfl

/-- ⚑ **THE TRACE, ON THE STRICT REGISTER FILE.** Rust fills no cell. -/
def endoTrace : List (List ℤ) :=
  runRowsVecAt qN qLimbFast (pinVec VP V_CHAL) (witsOf endoProg) 0 (instrs endoProg)

/-- ⚑ **AND NOT ONE BYTE MOVED.** The strict generator emits the closure generator's list, by
`runRowsVecAt_is_runRowsAt` at `regsOf (pinVec VP V_CHAL) = initRegs VP V_CHAL`. -/
theorem endoTrace_is_the_closure_trace :
    endoTrace = runRowsAt qN qLimbFast
      (Dregg2.Circuit.Emit.MinaWrapCommitStages.initRegs VP V_CHAL) (witsOf endoProg) 0
      (instrs endoProg) := by
  unfold endoTrace
  rw [runRowsVecAt_is_runRowsAt _ _ _ _ _ _ (pinVec_length VP V_CHAL),
    Dregg2.Circuit.Emit.MinaWrapCommitStages.regsOf_pinVec VP V_CHAL (by decide)]

/-- ⚑ **THE PUBLIC INPUTS ARE COMPUTED, NOT TYPED.** The output half is read out of the register
file the interpreter above ended in — so a program that computed a different scalar would emit a
different PI file, rather than emitting the same one and failing at prove time for a reason nobody
could localise. -/
def endoPIs : List ℤ := piPair V_CHAL (readVec endoRegs OUT)

/-- …and it IS the block's polyscale. -/
theorem the_emitted_pis_are_the_challenge_and_the_polyscale :
    endoPIs = piPair V_CHAL XI := by
  unfold endoPIs
  rw [the_machine_computes_the_endo_lift, the_polyscale_is_the_endo_lift_of_the_squeeze]

/-! ## §5 — ⚑⚑ THE WELD: A PUBLIC-INPUT EQUALITY AT THE REAL WIDTH.

`MinaWrapXiAggregateMsm` §4: *"The weld is a public-input equality between two descriptors and it is
NOT built."* This section is that equality, and §5b is what it is worth. -/

/-- The 32 limbs `dregg-mina-xi-endo-lift::v1`'s LAST-row pin publishes. -/
def endoOutputBlock : List ℤ := endoPIs.drop SK

/-- The 32 limbs `dregg-mina-xi-scalar-vector::v1`'s FIRST-row pin consumes. -/
def chainInputBlock : List ℤ := MinaWrapCommitStages.xiPIs.take SK

/-- ⚑⚑ **THE WELD.** The scalar chain's input public inputs ARE the endo lift's output public
inputs — elementwise, all 32 of them.

Two separately emitted descriptors, two separately generated traces, one shared 32-felt boundary.
A batch that verifies both proofs and compares these two slices learns that the ξ whose powers the
chain walks is the ξ this file's AIR derived from the block's own sponge squeeze. -/
theorem the_endo_output_block_is_the_chain_input_block :
    endoOutputBlock = chainInputBlock := by decide

/-- ⚑ **AND THE SHARED BLOCK IS A WHOLE FIELD ELEMENT, NOT A TAG.** 32 limbs at `SB = 8` bits is
256 bits of boundary, and the value they carry uses 253 of them. The point of stating this is that
`the_endo_output_block_is_the_chain_input_block` would be equally green over a ONE-felt block, and a
one-felt tie between two descriptors is `2^31` — below this repo's bar and exactly the shape the
`proof_bind` seam already has. -/
theorem the_shared_block_is_a_full_field_element :
    endoOutputBlock.length = SK ∧ SK = 32 ∧ SB = 8 ∧ SK * SB = 256
      ∧ 2 ^ 252 < XI ∧ XI < qN := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **AND THE 32 LIMBS RECOMPOSE TO ξ.** Without this the shared block could be 32 felts of
anything agreed on by two descriptors that both got it wrong; this says the boundary carries the
polyscale itself, read back out of the emitted limbs by the inverse of the map that wrote them. -/
theorem the_shared_block_recomposes_to_the_polyscale :
    ((List.range SK).foldr (fun i acc => acc * 256 + (endoOutputBlock.getD i 0)) 0) = (XI : ℤ) := by
  native_decide

/-- ⚑ **AND THE WELD IS REFUTABLE, ONE FELT AT A TIME.** The most significant limb moved by one —
the smallest change a forger could make to the shared boundary — and the equality is false. This is
what makes the theorem a gate rather than a restatement of how both sides were built. -/
theorem a_perturbed_output_limb_breaks_the_weld :
    endoOutputBlock.set (SK - 1) ((endoOutputBlock.getD (SK - 1) 0) + 1) ≠ chainInputBlock := by
  native_decide

/-- ⚑ **AND THE TWO DESCRIPTORS ARE TWO DESCRIPTORS.** A weld between an artifact and itself is not
a weld; these carry different names, so the batch cannot satisfy both halves with one proof. -/
theorem the_welded_descriptors_are_distinct :
    endoDesc.name = "dregg-mina-xi-endo-lift::v1"
      ∧ MinaWrapCommitStages.xiDesc.name = "dregg-mina-xi-scalar-vector::v2"
      ∧ endoDesc.name ≠ MinaWrapCommitStages.xiDesc.name := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- ⚑ **AND THE OTHER END OF THE CHAIN IS PINNED TOO.** The scalar chain's own second block is
`ξ⁴⁶`, so the two descriptors overlap on ξ and disagree everywhere else — the shape that makes the
pair a chain rather than a duplicate.

⚠ `.drop SK |>.take SK` and not `.drop SK`: since 2026-08-05 the chain publishes EIGHT 32-felt
blocks, not two. -/
theorem the_chain_output_half_is_the_forty_sixth_power :
    (MinaWrapCommitStages.xiPIs.drop SK).take SK
      = (List.range SK).map (limbAt (MinaWrapCommitStages.qpow XI 46))
      ∧ (MinaWrapCommitStages.xiPIs.drop SK).take SK ≠ chainInputBlock := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- ⚑⚑ **AND THE CHAIN NOW PUBLISHES THE SQUARING BASIS, WHOSE HEAD IS THE ξ THIS FILE DERIVES.**

Six further 32-felt blocks — `ξ³², ξ¹⁶, ξ⁸, ξ⁴, ξ², ξ` — and the LAST of them is byte-for-byte this
file's output block. So the value the ξ-aggregate's wire will carry as its sixth challenge is the
same 32 felts the endomorphism lift published, with no re-encoding between them.

`MinaWrapXiBasisWeld` is where those blocks meet the aggregate; this is the statement that the
chain's basis and this file's ξ are one value at the boundary. -/
theorem the_basis_tail_ends_on_this_files_polyscale :
    MinaWrapCommitStages.xiPIs.length = MinaWrapCommitStages.PI_XI
      ∧ MinaWrapCommitStages.PI_XI = 8 * SK
      ∧ MinaWrapCommitStages.xiPIs.drop (7 * SK) = endoOutputBlock := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ### §5b — ⚑ WHAT THE TIE IS WORTH, said out loud.

  * **Elementwise, 32 felts, 255 bits.** There is no digest in it, hence no birthday bound and no
    `2^{n/2}`: a forger must produce a limb list that agrees in all 32 places, which is agreement on
    the value. `a_perturbed_output_limb_breaks_the_weld` moves one felt and it fails.
  * **It is checked where the public inputs are.** A batch verifier compares two slices of two PI
    vectors. It does not recompute the lift and it does not recompute the powers.
  * ⚠ **It ties ξ, and it does not tie the aggregate's digits.** The aggregate has no PI slot for
    them (`PastaMsmBucketed` §7.4). `MinaWrapXiScalarWeld` states the tie that IS available on that
    side and prices it honestly.
  * ⚠ **And a PI equality is not a proof of anything on its own.** It is worth exactly what the two
    proofs it joins are worth, and both of those stand on the undischarged FRI/STARK floor this
    repo has not closed. -/

#assert_axioms the_polyscale_is_the_endo_lift_of_the_squeeze
#assert_compiled the_evalscale_prechallenge_lifts_elsewhere
#assert_compiled a_perturbed_squeeze_misses_the_polyscale
#assert_compiled the_base_field_lift_is_a_different_scalar
#assert_axioms the_endo_scalar_is_the_pallas_cube_root
#assert_axioms the_prechallenges_are_below_the_truncation
#assert_compiled the_allocation_fits_the_register_file
#assert_compiled the_program_is_eleven_hundred_and_sixty_instructions
#assert_axioms runRegsVecAt_threads_the_trace_generator
#assert_axioms the_machine_computes_the_endo_lift
#assert_compiled the_scalar_fold_lands_on_the_challenge_at_the_honest_witness
#assert_compiled the_input_register_survives_the_program
#assert_axioms endoAir_mainRailOk
#assert_axioms endoTrace_is_the_closure_trace
#assert_axioms the_emitted_pis_are_the_challenge_and_the_polyscale
#assert_axioms the_endo_output_block_is_the_chain_input_block
#assert_compiled the_shared_block_is_a_full_field_element
#assert_compiled the_shared_block_recomposes_to_the_polyscale
#assert_compiled a_perturbed_output_limb_breaks_the_weld
#assert_axioms the_welded_descriptors_are_distinct
#assert_compiled the_chain_output_half_is_the_forty_sixth_power
#assert_compiled the_basis_tail_ends_on_this_files_polyscale

end Dregg2.Circuit.Emit.MinaWrapXiEndoLift
