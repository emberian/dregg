/-
# Dregg2.Circuit.Emit.EffectVmRotationWideCommitIff — the `⟺` AT EIGHT FELTS, over the object the
executor ACTUALLY CHAINS.

## Why this file exists (the claim-gap it closes)

`977e73b19` moved the consensus anchor onto the CHIP 8-felt commitment: `TurnReceipt::{pre,post}_
state_hash`, the executor signature, and the federation receipt QC body now all carry
`cell/src/commitment.rs::compute_canonical_state_commitment_v9_felt8`, which is
`Faithful8::from_wire_commit_chip (compute_rotated_pre_limbs cell ctx) ctx.iroot` —
i.e. `circuit/src/poseidon2.rs:522::wire_commit_8_chip`.

The standing `air_accepts ⟺ spec` family certified a DIFFERENT object. Stated precisely, because the
difference is the whole point:

  * `EffectVmFullStateRunnableComplete.runnable_full_commit_iff` and the seventeen per-tag
    `*_commit_iff` (`EffectVmFullStateTagsA/B`) pin `NEW_COMMIT = wireCommitOfRow hash env`, which is
    `wideCommitOf hash` — a GROUP-4 `H4`-of-`H4` sponge collapsing **13 effect-VM columns to ONE
    felt** (`BALANCE_LO`, `BALANCE_HI`, `NONCE`, `FIELD_BASE+0..7`, `CAP_ROOT`, `sysRootsDigestCol`).
  * The deployed anchor is `wireCommitR8` — a chained **8-felt** absorption over the **187 ROTATED
    pre-iroot limbs** plus the iroot, on the rotated block layout.

These are not the same commitment at two widths; they are two different commitments over two
different column sets. So "lift the seventeen to 8 felts" would have produced an 8-felt version of an
object the consensus path no longer carries. What actually closes the gap is the `⟺` for the ROTATED
WIDE block — `EffectVmEmitRotationWide`, the lane that models `trace_rotated.rs::fill_wide_block` —
which held the SOUNDNESS half (`rotV3WidePin`) and had no completeness half at all. This file
supplies the missing `←` and welds the biconditional.

## ⚑ THE REALITY GATE: which Lean object is the CHIP form, and how it was confirmed

The deployed chain has a byte-twin that DIVERGES from it — `rotation_witness.rs:370`'s plain
`Faithful8::from_wire_commit` over `single_perm_compress`, which seeds NO arity tag (its head leaves
`st[4] = 0` where the chip seeds `st[4] = 4`), so the two chains differ from the head on. The theorem
below must be about the CHIP chain. It is, and here is the confirmation, which is structural rather
than asserted:

  1. `wireCommitR8 permW l ir` is ABSTRACT in `permW : List ℤ → List ℤ`. The chip-vs-plain question
     is therefore entirely a question of WHICH `permW` the surrounding theorem binds.
  2. The wide site's lookup tuple is `chipLookupTupleN ins digestCols =
     (.const ins.length) :: padToE CHIP_RATE ins ++ digestCols.map .var`
     (`DescriptorIR2.lean:1220`). The FIRST tuple element is the **arity tag `ins.length`**, and
     `ChipTableSoundN permW tbl` forces every table row to be `chipRowN permW ins =
     (ins.length : ℤ) :: padTo CHIP_RATE ins ++ permW ins`. So the `permW` these theorems bind is
     the arity-TAGGED absorb — `chip_absorb_all_lanes(arity, ins)` with `arity = ins.length` — which
     is exactly the chip. The untagged `single_perm_compress` has no such tag and cannot realize
     `ChipTableSoundN` against an arity-carrying tuple.
  3. The arity at every step of the deployed chain IS its input length, so `arity = ins.length` is
     not an approximation of the chip but the chip itself: `wire_commit_8_chip` seeds
     `chip_absorb_all_lanes(4, l0..l3)` (head, 4 inputs), `chip_absorb_all_lanes(11, d8 ‖ 3 limbs)`
     (body, 11 inputs), `chip_absorb_all_lanes(9, d8 ‖ 1 limb)` (leftover, 9 inputs), and
     `chip_absorb_all_lanes(11, d8 ‖ iroot ‖ 0 ‖ 0)` (final, 11 inputs).
  4. The SHAPE matches step for step. `rotV3WideSpecs` emits head `[l0,l1,l2,l3]` → carrier 0, then
     61 body groups `(carrier ‖ 3 limbs)` (11 inputs), then the final
     `(carrier 61 ‖ iroot ‖ .const 0 ‖ .const 0)` (11 inputs) → carrier 62; `wireCommitR8` folds
     `chainFrom8 permW (permW (l.take 4)) (chunk31 (l.drop 4) ++ [[ir,0,0]])`, and at `l.length =
     187` the body is `chunk31` of 183 limbs = 61 groups of three with NO leftover — 63 carriers,
     matching `wideNumCarriers = 63` and Rust's `WIDE_NUM_CARRIERS`. `chunk31`'s leftover arm emits
     SINGLETONS (`[a,b] => [[a],[b]]`), which is Rust's `else` arm taking ONE limb (arity 9) — never
     a pair — so the correspondence is faithful at limb counts off the deployed 187 too.

So: the object certified below is `wireCommitR8` under an arity-tagged `ChipTableSoundN permW`, over
the 187 rotated limbs — the chip chain, not the plain chain.

## What is proved

  * `WideChain8` — the row's sixty-three 8-column carrier blocks hold the genuine per-site absorption.
  * `wideChipTableOf` / `wideChipTableOf_sound` — the chip table a PROVER BUILDS for this row (the
    sixty-three genuine rows it needs), proved `ChipTableSoundN`. No new floor is assumed: completeness
    exhibits a table rather than positing one that contains every genuine row.
  * `rotV3Wide_commit_iff8` — **THE BICONDITIONAL AT EIGHT FELTS**: the sixty-three wide lookups hold IFF
    the carriers are the genuine chain AND the state-commit carrier is `wireCommitR8` of the row's
    own 187 limbs and iroot. `→` is the deployed pin (`rotV3WidePin`, unchanged); `←` is the
    constructed witness. `rotV3Wide_commit_iff8_of_table` is the table-parametric form.
  * `rotV3Wide_commit8_binds_or_collides` — the binding carried as the HONEST DISJUNCTION, never a
    global injectivity claim the deployment refutes.
  * `rotV3Wide_commit8_binds_of_noColl` — the instance-local restoration. ⚑ This is NOT the deleted
    `Poseidon2WideCR` floor smuggled back: that floor quantified over ALL inputs and is FALSE at
    deployed BabyBear parameters (pigeonhole); `¬ WireColl permW l ir l' ir'` is a claim about the
    TWO SPECIFIC lists a total extractor returns for THIS pair, refutable per instance and carrying
    no universal quantifier.
  * Canaries at EIGHT felts, both polarities.

## Per-tag: there is nothing per-tag to do, and that is a THEOREM not a shortcut

At 1 felt the commitment is emitted INSIDE each effect's descriptor, so each of the seventeen tags
needed its own `*_commit_iff` instance. At 8 felts it is emitted by the ROTATION WRAPPER:
`rotateV3Wide (d : EffectVmDescriptor)` appends the wide BEFORE/AFTER blocks to an ARBITRARY host
descriptor, and `rotV3WidePin` / the results below are quantified over `(base, cbase)` — so every
tag's wide commitment is the SAME theorem at a different base, with zero per-tag obligation. The
seventeen 1-felt `*_commit_iff` stay valid and are NOT subsumed (they certify a different object on
a different column set), so none is deleted.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; every import
read-only; `rotV3WidePin` / `siteLookupsN_sound` / `wireCommitR8_binds_or_collides` are used AS-IS.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide

namespace Dregg2.Circuit.Emit.EffectVmRotationWideCommitIff

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
  (wireCommitR8 Poseidon2Width8 WireColl wireCommitR8_binds_or_collides chunk31 chainFrom8)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (B_IROOT)
open Dregg2.Substrate.Heap (refSponge)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — `WideChain8`: the row's carriers ARE the genuine chained absorption.

This is exactly the conclusion `siteLookupsN_sound` produces from a satisfying lookup family, read
as a predicate ON THE ROW. It is the 8-felt analogue of the 1-felt engine's `WideCarrier` (the
honest-fill shape of the GROUP-4 columns) — at 8 felts the "fill" is sixty-three 8-column blocks. -/

/-- **`WideChain8 permW env base cbase`** — every one of the sixty-three wide sites' 8 output columns
carries the genuine `permW` image of that site's evaluated inputs. Equivalently: the row's carrier
blocks hold the successive `chainFrom8` prefixes of the 187-limb absorption. -/
def WideChain8 (permW : List ℤ → List ℤ) (env : VmRowEnv) (base cbase : Nat) : Prop :=
  ∀ p ∈ rotV3WideSpecs base cbase, p.2.map env.loc = permW (p.1.map (·.eval env.loc))

/-! ## §2 — the chip table a PROVER BUILDS (completeness without a new floor).

The `→` direction rides `ChipTableSoundN` — every table row is a genuine chip row. The `←` direction
needs the converse resource: the table must CONTAIN the rows this block looks up. Positing "the
table contains every genuine row" would be a fresh, unmotivated floor. Instead we EXHIBIT the table
the prover actually builds — precisely the sixty-three rows this block needs — and prove it sound. So the
completeness half assumes nothing that the deployed prover does not itself construct. -/

/-- **`wideChipTableOf permW env base cbase`** — the sixty-three genuine chip rows the wide block at
`(base, cbase)` looks up, in emission order. This is what a prover's `.poseidon2` chip trace holds
for this row. -/
def wideChipTableOf (permW : List ℤ → List ℤ) (env : VmRowEnv) (base cbase : Nat) : Table :=
  (rotV3WideSpecs base cbase).map (fun p => chipRowN permW (p.1.map (·.eval env.loc)))

/-- The prover-built table is SOUND: every row is a genuine `(arity, padded inputs, 8-felt output)`
tuple, with the arity tag inside the chip rate. -/
theorem wideChipTableOf_sound (permW : List ℤ → List ℤ) (env : VmRowEnv) (base cbase : Nat) :
    ChipTableSoundN permW (wideChipTableOf permW env base cbase) := by
  intro r hr
  simp only [wideChipTableOf, List.mem_map] at hr
  obtain ⟨p, hp, hrfl⟩ := hr
  refine ⟨p.1.map (·.eval env.loc), ?_, hrfl.symm⟩
  simpa using rotV3WideSpecs_admitted base cbase p hp

/-- The evaluated wide-lookup tuple of a site whose carriers are genuine IS the genuine chip row.
The bridge between "the lookup tuple as emitted" and "the chip row as tabulated". -/
theorem siteLookupN_tuple_eval (permW : List ℤ → List ℤ) (env : VmRowEnv)
    (ins : List EmittedExpr) (digestCols : List Nat)
    (hAdm : ChipArityAdmitted ins.length)
    (hgen : digestCols.map env.loc = permW (ins.map (·.eval env.loc))) :
    (siteLookupN ins digestCols hAdm).tuple.map (·.eval env.loc)
      = chipRowN permW (ins.map (·.eval env.loc)) := by
  -- ⚠ do NOT unfold `padTo`/`padToE` here: `map_eval_padToE` carries the emitted block onto the
  -- tabulated one directly, and `padTo` is now `take`-shaped (total-correct), so unfolding it
  -- leaves a `List.take` the two sides would have to be re-aligned across.
  simp only [siteLookupN, chipLookupTupleN, chipRowN, map_eval_padToE, List.map_cons,
    List.map_append, List.map_map, Function.comp_def, EmittedExpr.eval,
    List.length_map, hgen]

/-- **THE COMPLETENESS LEG (`←`).** A row whose carriers are the genuine chain satisfies ALL sixty-three
wide lookups against the prover-built table. Uniform in the site — no sixty-three-way case split, because
the table is indexed by the very spec list the lookups walk. -/
theorem wide_lookups_of_chain (permW : List ℤ → List ℤ) (env : VmRowEnv) (base cbase : Nat)
    (hchain : WideChain8 permW env base cbase) :
    ∀ (p : List EmittedExpr × List Nat) (hp : p ∈ rotV3WideSpecs base cbase),
      (siteLookupN p.1 p.2).tuple.map (·.eval env.loc)
        ∈ wideChipTableOf permW env base cbase := by
  intro p hp
  rw [siteLookupN_tuple_eval permW env p.1 p.2 (rotV3WideSpecs_admitted _ _ p hp) (hchain p hp)]
  exact List.mem_map_of_mem hp

/-! ## §3 — ⚑ THE BICONDITIONAL AT EIGHT FELTS. -/

/-- **`rotV3Wide_commit_iff8_of_table` — the table-parametric `⟺`.** Against ANY chip table that is
sound and contains this block's genuine rows, the sixty-three wide lookups hold IFF the carriers are the
genuine chain AND the state-commit carrier (carrier `wideCommitCarrier` = 62 — the published 8-felt block) is
`wireCommitR8` of the row's own 187 limbs and iroot.

`→` is the DEPLOYED pin `rotV3WidePin`, used unchanged: the commit conjunct is FORCED by the lookup
family, not assumed. `←` is `wide_lookups_of_chain`. -/
theorem rotV3Wide_commit_iff8_of_table (permW : List ℤ → List ℤ) (tbl : Table)
    (hSound : ChipTableSoundN permW tbl) (env : VmRowEnv) (base cbase : Nat)
    (hCompl : ∀ (p : List EmittedExpr × List Nat) (hp : p ∈ rotV3WideSpecs base cbase),
      chipRowN permW (p.1.map (·.eval env.loc)) ∈ tbl) :
    (∀ (p : List EmittedExpr × List Nat) (hp : p ∈ rotV3WideSpecs base cbase),
        (siteLookupN p.1 p.2).tuple.map (·.eval env.loc) ∈ tbl)
    ↔ (WideChain8 permW env base cbase
        ∧ carrierVals cbase wideCommitCarrier env.loc
            = wireCommitR8 permW (preLimbsWide base env.loc) (env.loc (base + B_IROOT))) := by
  constructor
  · intro hlk
    refine ⟨siteLookupsN_sound permW tbl hSound env (rotV3WideSpecs base cbase)
              (rotV3WideSpecs_admitted base cbase) hlk, ?_⟩
    exact rotV3WidePin permW tbl hSound env base cbase hlk
  · rintro ⟨hchain, -⟩
    intro p hp
    rw [siteLookupN_tuple_eval permW env p.1 p.2 (rotV3WideSpecs_admitted _ _ p hp) (hchain p hp)]
    exact hCompl p hp

/-- **`rotV3Wide_commit_iff8` — THE FLAGSHIP, over the prover-built table.** The sixty-three wide lookups
of the rotated wide block hold IFF the carriers are the genuine chained absorption AND the published
state-commit carrier IS `wireCommitR8` of the row's own 187 rotated limbs and iroot — the value
`compute_canonical_state_commitment_v9_felt8` computes and the receipt, the executor signature, and
the federation QC body carry.

Unconditional: no collision-resistance floor, no injectivity hypothesis, no assumed table oracle. -/
theorem rotV3Wide_commit_iff8 (permW : List ℤ → List ℤ) (env : VmRowEnv) (base cbase : Nat) :
    (∀ (p : List EmittedExpr × List Nat) (hp : p ∈ rotV3WideSpecs base cbase),
        (siteLookupN p.1 p.2).tuple.map (·.eval env.loc)
          ∈ wideChipTableOf permW env base cbase)
    ↔ (WideChain8 permW env base cbase
        ∧ carrierVals cbase wideCommitCarrier env.loc
            = wireCommitR8 permW (preLimbsWide base env.loc) (env.loc (base + B_IROOT))) :=
  rotV3Wide_commit_iff8_of_table permW (wideChipTableOf permW env base cbase)
    (wideChipTableOf_sound permW env base cbase) env base cbase
    (fun p hp => List.mem_map_of_mem hp)

/-! ## §4 — the binding, carried as the HONEST DISJUNCTION.

The 8-felt commitment's binding is `wireCommitR8_binds_or_collides` (`EffectVmEmitRotationR`, the
EXTRACTION-AS-DATA keystone that replaced the deleted `Poseidon2WideCR`): equal chained commits
either force equal limbs AND equal iroot, or HAND BACK the specific pair at which the deployed
permutation collides. Every statement here carries that disjunction. -/

/-- **`rotV3Wide_commit8_binds_or_collides`** — two rows whose wide lookups hold and whose published
8-felt state-commit carriers AGREE either commit the SAME 187 limbs and the SAME iroot, or exhibit a
genuine collision of the deployed wide permutation at the named pair. -/
theorem rotV3Wide_commit8_binds_or_collides (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (env env' : VmRowEnv) (base cbase base' cbase' : Nat)
    (hlk : ∀ (p : List EmittedExpr × List Nat) (hp : p ∈ rotV3WideSpecs base cbase),
      (siteLookupN p.1 p.2).tuple.map (·.eval env.loc) ∈ wideChipTableOf permW env base cbase)
    (hlk' : ∀ (p : List EmittedExpr × List Nat) (hp : p ∈ rotV3WideSpecs base' cbase'),
      (siteLookupN p.1 p.2).tuple.map (·.eval env'.loc) ∈ wideChipTableOf permW env' base' cbase')
    (hagree : carrierVals cbase wideCommitCarrier env.loc = carrierVals cbase' wideCommitCarrier env'.loc) :
    (preLimbsWide base env.loc = preLimbsWide base' env'.loc
      ∧ env.loc (base + B_IROOT) = env'.loc (base' + B_IROOT))
    ∨ WireColl permW (preLimbsWide base env.loc) (env.loc (base + B_IROOT))
        (preLimbsWide base' env'.loc) (env'.loc (base' + B_IROOT)) := by
  have hp := ((rotV3Wide_commit_iff8 permW env base cbase).mp hlk).2
  have hp' := ((rotV3Wide_commit_iff8 permW env' base' cbase').mp hlk').2
  have hcommit :
      wireCommitR8 permW (preLimbsWide base env.loc) (env.loc (base + B_IROOT))
        = wireCommitR8 permW (preLimbsWide base' env'.loc) (env'.loc (base' + B_IROOT)) := by
    rw [← hp, ← hp', hagree]
  exact wireCommitR8_binds_or_collides permW hW
    (by rw [preLimbsWide_length, preLimbsWide_length]) hcommit

/-- **`rotV3Wide_commit8_binds_of_noColl` — the INSTANCE-LOCAL restoration.** Ruling out a collision
at THE TWO SPECIFIC lists the extractor returns for this pair restores the clean binding.

⚑ This is NOT the deleted floor smuggled back. `Poseidon2WideCR permW : ∀ xs ys, permW xs = permW ys
→ xs = ys` quantified over ALL inputs and is FALSE at deployed BabyBear parameters (a width-8 squeeze
of an infinite domain collides by pigeonhole), which is why every theorem conditioned on it was
VACUOUS. `¬ WireColl permW l ir l' ir'` is a decidable claim about ONE named pair; it is refutable
instance by instance, and asserting it here commits to nothing universal. -/
theorem rotV3Wide_commit8_binds_of_noColl (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (env env' : VmRowEnv) (base cbase base' cbase' : Nat)
    (hlk : ∀ (p : List EmittedExpr × List Nat) (hp : p ∈ rotV3WideSpecs base cbase),
      (siteLookupN p.1 p.2).tuple.map (·.eval env.loc) ∈ wideChipTableOf permW env base cbase)
    (hlk' : ∀ (p : List EmittedExpr × List Nat) (hp : p ∈ rotV3WideSpecs base' cbase'),
      (siteLookupN p.1 p.2).tuple.map (·.eval env'.loc) ∈ wideChipTableOf permW env' base' cbase')
    (hagree : carrierVals cbase wideCommitCarrier env.loc = carrierVals cbase' wideCommitCarrier env'.loc)
    (hno : ¬ WireColl permW (preLimbsWide base env.loc) (env.loc (base + B_IROOT))
        (preLimbsWide base' env'.loc) (env'.loc (base' + B_IROOT))) :
    preLimbsWide base env.loc = preLimbsWide base' env'.loc
    ∧ env.loc (base + B_IROOT) = env'.loc (base' + B_IROOT) := by
  rcases rotV3Wide_commit8_binds_or_collides permW hW env env' base cbase base' cbase'
    hlk hlk' hagree with h | hcoll
  · exact h
  · exact absurd hcoll hno

/-! ## §5 — CANARIES AT EIGHT FELTS.

The `⟺` is only worth its name if both conjuncts are two-valued AT THE DEPLOYED WIDTH. -/

/-- **`canary_tamper_moves_commit8_or_collides` — the commit conjunct BITES at 8 felts,
UNCONDITIONALLY.** Tamper any after-state limb (any index, any value, so long as the list actually
MOVES) and the 8-felt commitment either MOVES with it, or the deployed wide permutation genuinely
collides at the pair the total extractor returns. So a receipt's honest 8-felt anchor cannot ride a
tampered after-state without a real collision being exhibited. -/
theorem canary_tamper_moves_commit8_or_collides (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (limbs : List ℤ) (ir : ℤ) (i : Nat) (v : ℤ)
    (hne : limbs ≠ limbs.set i v) :
    wireCommitR8 permW limbs ir ≠ wireCommitR8 permW (limbs.set i v) ir
    ∨ WireColl permW limbs ir (limbs.set i v) ir := by
  by_cases h : wireCommitR8 permW limbs ir = wireCommitR8 permW (limbs.set i v) ir
  · refine Or.inr ?_
    rcases wireCommitR8_binds_or_collides permW hW (by simp) h with ⟨heq, -⟩ | hcoll
    · exact absurd heq hne
    · exact hcoll
  · exact Or.inl h

/-- **`canary_bogus_commit8_unsat` — the constructed carriers are LOAD-BEARING.** A row whose
state-commit carrier is NOT the genuine `wireCommitR8` cannot satisfy the sixty-three wide lookups: the
contrapositive of the `→` leg. Mutating the built carrier REDS the block, so the completeness
construction is not vacuous. -/
theorem canary_bogus_commit8_unsat (permW : List ℤ → List ℤ) (env : VmRowEnv) (base cbase : Nat)
    (hbogus : carrierVals cbase wideCommitCarrier env.loc
      ≠ wireCommitR8 permW (preLimbsWide base env.loc) (env.loc (base + B_IROOT))) :
    ¬ (∀ (p : List EmittedExpr × List Nat) (hp : p ∈ rotV3WideSpecs base cbase),
        (siteLookupN p.1 p.2).tuple.map (·.eval env.loc)
          ∈ wideChipTableOf permW env base cbase) :=
  fun hlk => hbogus ((rotV3Wide_commit_iff8 permW env base cbase).mp hlk).2

/-! ### §5½ — the tamper canaries EXECUTED at the deployed 187-limb shape.

`refWide` is the width-8 Horner toy (`EffectVmEmitRotationR` §3): each lane is `refSponge (tag :: xs)`,
so every lane avalanches over the whole input. Both polarities, at the SHAPE the deployed block
emits — 187 pre-iroot limbs, 63 carriers. -/

/-- A concrete 187-limb rotated payload (the deployed pre-iroot shape:
`rotatedNumPreLimbs = 187` since the key nonet gave the owner key its ninth lane a column). -/
def demoPreN : List ℤ := (List.range 196).map (fun i => 1000 + (i : ℤ))

/-- The width-8 toy permutation the 8-felt guards ride. -/
def refWide8 : List ℤ → List ℤ :=
  fun xs => (List.range 8).map (fun t => refSponge ((t : ℤ) :: xs))

#guard demoPreN.length == 196
#guard demoPreN.length == rotatedNumPreLimbs   -- ⚑ reality gate: no independent literal
#guard (refWide8 [1, 2, 3]).length == 8
-- the honest recompute is STABLE …
#guard wireCommitR8 refWide8 demoPreN 7 == wireCommitR8 refWide8 demoPreN 7
-- … and every position MOVES it: the head group (absorbed first, deepest in the chain) …
#guard wireCommitR8 refWide8 demoPreN 7 != wireCommitR8 refWide8 (demoPreN.set 0 999) 7
-- … a mid-chain body limb (the intermediate-carrier tooth: no narrow waist swallows it) …
#guard wireCommitR8 refWide8 demoPreN 7 != wireCommitR8 refWide8 (demoPreN.set 88 999) 7
-- … the LAST pre-iroot limb (absorbed in the final body group) …
#guard wireCommitR8 refWide8 demoPreN 7 != wireCommitR8 refWide8 (demoPreN.set 183 999) 7
-- … and the iroot, which rides its own final arity-11 site, literally last.
#guard wireCommitR8 refWide8 demoPreN 7 != wireCommitR8 refWide8 demoPreN 8

/-! ## §5¾ — ⚑ NON-VACUITY: the `⟺`'s right-hand side is INHABITED (not certifying an empty set).

A true `⟺` whose right-hand side is unsatisfiable certifies nothing — the engine this one mirrors
names an unsatisfiable RHS "the sharper form of the disease". Two independent witnesses that it is
not this file's disease:

  * **the honest carrier-fill LANDS on the commitment** — for the realistic avalanching `refWide8`,
    at the deployed 187-limb / 63-carrier shape, the chain of `chainFrom8` prefixes folded through the
    sixty-three sites has its final carrier EQUAL to `wireCommitR8` (the `demoCarrier 62` guard, EXECUTED):
    the completeness construction's fill is the published commitment, not an unrelated value.
  * **a row PROVABLY satisfies the flagship's RHS** — `const_commit_iff8` exhibits a `(permW, env)`
    at which `WideChain8` AND the commit equation both hold (via the flagship's `←` leg), so the
    biconditional's right side is genuinely inhabited. -/

/-- The chunk list the deployed 196-limb chain absorbs after its 4-wide head: 64 three-limb body
groups, then the iroot's own final `[ir, 0, 0]` site. -/
def demoChunks : List (List ℤ) := chunk31 (demoPreN.drop 4) ++ [[7, 0, 0]]

#guard demoChunks.length == 65
#guard demoChunks.all (fun c => c.length == 3)

/-- Carrier `k`'s genuine 8-felt value: the head seed folded over the first `k` chunks. Carrier 0 is
the head; carrier 65 is the published state commitment. -/
def demoCarrier (k : Nat) : List ℤ :=
  chainFrom8 refWide8 (refWide8 (demoPreN.take 4)) (demoChunks.take k)

-- ⚑ EXECUTED: the honest carrier-fill's FINAL carrier IS `wireCommitR8` — the fold lands exactly on
-- the published 8-felt commitment at the deployed shape.
#guard demoCarrier 65 == wireCommitR8 refWide8 demoPreN 7

/-- A width-8 constant permutation (a legitimate `List ℤ → List ℤ` of output width 8): the cheapest
inhabitant that makes both `⟺` conjuncts hold at once, so the RHS is provably non-empty without the
big-integer kernel cost of deciding the full avalanching chain. -/
def constW : List ℤ → List ℤ := fun _ => List.replicate 8 0

/-- The all-zero row. -/
def zLoc : Assignment := fun _ => 0
/-- The all-zero witnessing row. -/
def zEnv : VmRowEnv := ⟨zLoc, zLoc, zLoc, fun _ => 0⟩

/-- **`const_wideChain8` — a row whose sixty-three carriers ARE the genuine chain.** With the constant
width-8 permutation every carrier is `replicate 8 0`, which IS `constW` of the site inputs — so the
chain predicate holds. Decided cheaply (no big integers). -/
theorem const_wideChain8 : WideChain8 constW zEnv 0 200 := by
  unfold WideChain8 constW zEnv zLoc; decide

/-- **`const_commit_iff8` — the flagship RHS is INHABITED.** Feeding `const_wideChain8` through the
completeness leg and the flagship `⟺` yields a `(permW, env)` at which `WideChain8` AND the published
commit equation both hold: the biconditional is not vacuously true. -/
theorem const_commit_iff8 :
    WideChain8 constW zEnv 0 200
    ∧ carrierVals 200 61 zEnv.loc
        = wireCommitR8 constW (preLimbsWide 0 zEnv.loc) (zEnv.loc (0 + B_IROOT)) :=
  (rotV3Wide_commit_iff8 constW zEnv 0 200).mp
    (wide_lookups_of_chain constW zEnv 0 200 const_wideChain8)

/-! ## §6 — axiom-hygiene tripwires (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms wideChipTableOf_sound
#assert_axioms siteLookupN_tuple_eval
#assert_axioms wide_lookups_of_chain
#assert_axioms rotV3Wide_commit_iff8_of_table
#assert_axioms rotV3Wide_commit_iff8
#assert_axioms rotV3Wide_commit8_binds_or_collides
#assert_axioms rotV3Wide_commit8_binds_of_noColl
#assert_axioms canary_tamper_moves_commit8_or_collides
#assert_axioms canary_bogus_commit8_unsat
#assert_axioms const_wideChain8
#assert_axioms const_commit_iff8

end Dregg2.Circuit.Emit.EffectVmRotationWideCommitIff
