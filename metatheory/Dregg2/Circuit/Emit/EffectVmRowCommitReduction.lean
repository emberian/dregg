/-
# `Dregg2.Circuit.Emit.EffectVmRowCommitReduction` — the RUNNABLE EffectVM row's `state_commit`
binding as a SECURITY REDUCTION over EFFICIENT adversaries, on the shared one-felt sponge spine.

## The sin this retires

Every per-effect emission module exported its commitment binding as a BARE DISJUNCTION:

    absorbedCols e₁ = absorbedCols e₂ ∨ TransferColl hash e₁ e₂                            -- narrow
    (baseAbsorbedCols e₁ = baseAbsorbedCols e₂ ∧ roots agree) ∨ WideColl … ∨ RootsColl …   -- wide

Those were a real repair on their predecessors, which carried `Poseidon2Binding.Poseidon2SpongeCR` —
a floor the deployed BabyBear sponge REFUTES (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so
they were VACUOUS exactly where they were supposed to bind the deployed system. But the disjunctions
are still UNCLOSED: a collision EXISTS at deployed parameters by pigeonhole, so `binds ∨ collides` is
satisfiable through the `collides` branch WITHOUT `binds` ever holding. It quantifies over SOLUTIONS.
Cryptographic hardness quantifies over EFFICIENT ADVERSARIES.

## What replaces them, and where the pieces come from

The reduction spine is NOT re-authored here. `Dregg2.Crypto.SpongeCarrierReduction` already provides
it, once, for every one-felt sponge carrier in the tree: `SpongeKeyed` (the deployed sponge keyed by
its domain-separation tag), `spongeFamily`, `carrierBreakGame` (the forgery, with the break IN the win
relation), `carrierBreakToFinder` (the extractor AS A MAP OF ADVERSARIES), `carrier_adv_le` (the
UNCONDITIONAL advantage inequality — the adversary class does not appear in it),
`carrier_binds_advantage_bound` (the conclusion under `FloorGames.HashCRHardQuant (spongeFamily D) Eff`)
and, until 07-24, `carrier_binds_from_polyTime` (`hEff` at `Eff := IsPolyTime` — DELETED with the
floor's refutation; the discharged successor is `RomBindingReduction.romCarrier_binds`).

⚑ Why that spine and not a reduction hosted at `Circuit.Poseidon2KeyedBridge`: that bridge sits ABOVE
the whole `Emit/*` tree in the import graph (`Poseidon2KeyedBridge → FloorRegroundedConsumers →
CommitFaithfulRegrounded → EffectVmEmitRotationR → EffectVmEmitRotation → EffectVmEmitV2 →
EffectVmEmit*`). Importing it from an emission module is a BUILD CYCLE. (A sibling lane's module of
the same shape, `Circuit.Emit.EffectVmCommitReduction`, claimed to host such reductions but was
imported by NOTHING and never elaborated — vapor; it was DELETED 07-23, and the per-effect keystones
it pretended to replace are restored in their emission files, with their collision branch closed on
the PROVED keyed floor by `Circuit.Emit.EffectVmKeyedStateCommit`.) `SpongeCarrierReduction` restates
the same keyed sponge low in the graph for precisely this reason, and `Crypto.SpongeCarrierBridge`
PROVES (by `rfl`) that its family IS `Poseidon2KeyedBridge`'s. So this module is landed on the same
floor, reachable from where the rows live.

What THIS module adds, and it is only this:

  * **§1 — the two deployed EffectVM commitments as `SpongeCarrier`s.** `group4Carrier` is the
    narrow (13-column) `commitOf` — the H4-of-H4 whose fourth outer slot is the record digest;
    `wideStateCarrier` is the wide (`system_roots`-absorbing) `wideCommitOf`, whose fourth slot is the
    side-table digest, so ONE carrier covers BOTH of the wide commitment's collision legs (the GROUP-4
    tree and the ordered root list) and the reduction lands on ONE floor with no union bound. Each
    supplies the ONLY thing the spine asks for: a total extractor and its UNCONDITIONAL correctness.

  * **§2/§3 — the per-effect ROW games.** `narrowRowBreakGame E` / `wideRowBreakGame E` take the
    effect's OWN runnable descriptor: a win is two rows BOTH ACCEPTED by the deployed circuit
    (`satisfiedVm`) that publish the same commitment and yet bind different state. The descriptor is
    IN the game, so `mint`'s game and `burn`'s game are different types — the `FloorGames` lesson
    ("five names, one `Prop`" → five `Game`s) applied at the row layer. The lift into the carrier game
    is a map of adversaries with a win-preservation theorem.

  * **§4 — the TAMPER sub-games**, which are the `_rejects_state_tamper` / `_rejects_root_tamper`
    teeth: the same forgery with the disagreement PINNED to an absorbed state column, or to a named
    side-table root index.

  * **§5 — `winsDec` WITHOUT `Classical.propDecidable`.** The deployed row denotation is DECIDABLE
    (§0), so putting `satisfiedVm` inside a counted win event needs no classical choice and
    `Adversary.hit` stays a genuine computation.

## What is NOT closed (named, not faked)

This closes the SPONGE component of the runnable commitment binding. It does not touch the per-effect
ROW SEMANTICS (`decodeFull`/`fullClause`, proved separately and unconditionally), nor the cross-cell
`accounts` membership (the turn layer), nor the FRI/STARK floor beneath the proof system. And
`Eff := IsPolyTime` is a cost-VECTOR model of efficiency, not a machine model: what it buys is that
the ⊤-collapse witness is PROVED excluded (`CostAdversary.bruteForce_not_polyTime`) and the class is
PROVED inhabited, with both floor poles proved in `SpongeCarrierReduction` §5.

No `sorry`, no `axiom`, no `native_decide`, no `decide` on an opaque `Prop`. Cost stays SYNTACTIC.
-/
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Crypto.SpongeCarrierReduction
import Dregg2.Crypto.RomCarrierSites

namespace Dregg2.Circuit.Emit.EffectVmRowCommitReduction

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols transferBlockA transferBlockB transferBlockC commit_eq_commitOf commitOf)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols wideHashSites wideBlockA wideBlockB wideBlockC wideCommitOf wide_commit_eq)
open Dregg2.Circuit.Poseidon2Binding (group4Find group4Find_spec)
open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest rootList N_SYSTEM_ROOTS systemRootsDigest_eq_hash_rootList)
open Dregg2.Crypto.SpongeCarrierReduction
  (SpongeKeyed SpongeCarrier IsSpongeColl spongeFamily carrierBreakGame carrierBreakToFinder
   carrier_adv_le carrier_binds_advantage_bound carrierAnsSize
   spongeAnsSize carrierFloor_top_false_babyBear carrierFloor_bot_vacuous
   carrierFloor_isPolyTime_inhabited)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv gameAdv_mem_unit hashGame HashCRHardQuant)
open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — DECIDABILITY of the deployed row denotation.

A `Game`'s win event is COUNTED, so `FloorGames.Game.winsDec` is not decoration. Putting the effect's
own `satisfiedVm` INTO the win relation therefore needs the deployed row denotation to be decidable —
supplied here structurally (field congruences and range bounds over `ℤ`; the site walk by recursion on
the site list). No `Classical.propDecidable`, so `Adversary.hit` stays a genuine computation and the
counting probability is the honest finite one. -/

/-- Deciding ONE constraint on a row window: each `holdsVm` arm is a `ZMOD` congruence or `True`,
guarded by a `Bool` flag. -/
instance instDecidableHoldsVm (env : VmRowEnv) (isFirst isLast : Bool) (c : VmConstraint) :
    Decidable (c.holdsVm env isFirst isLast) := by
  cases c with
  | gate body => cases isLast <;> (unfold VmConstraint.holdsVm; infer_instance)
  | transition hi lo => cases isLast <;> (unfold VmConstraint.holdsVm; infer_instance)
  | boundary row body => cases row <;> (unfold VmConstraint.holdsVm; infer_instance)
  | piBinding row col k => cases row <;> (unfold VmConstraint.holdsVm; infer_instance)

/-- Deciding the ordered hash-site walk, by recursion on the site list (the accumulator is data). -/
instance instDecidableSiteGo (hash : List ℤ → ℤ) (env : VmRowEnv) :
    ∀ (ss : List VmHashSite) (acc : List ℤ), Decidable (siteHoldsAll.go hash env acc ss)
  | [], acc => by
      show Decidable True
      infer_instance
  | s :: ss, acc => by
      have : Decidable (siteHoldsAll.go hash env (acc ++ [hash (s.resolvedInputs env acc)]) ss) :=
        instDecidableSiteGo hash env ss _
      show Decidable (env.loc s.digestCol = hash (s.resolvedInputs env acc)
        ∧ siteHoldsAll.go hash env (acc ++ [hash (s.resolvedInputs env acc)]) ss)
      infer_instance

instance instDecidableSiteHoldsAll (hash : List ℤ → ℤ) (env : VmRowEnv) (ss : List VmHashSite) :
    Decidable (siteHoldsAll hash env ss) := instDecidableSiteGo hash env ss []

instance instDecidableRangeHolds (env : VmRowEnv) (r : VmRange) : Decidable (r.holds env) := by
  unfold VmRange.holds; infer_instance

/-- "Is this pair a genuine collision?" is DECIDABLE, so the wide extractor below may branch on it and
remain a TOTAL computable function with no `Classical.choice` in the walk. -/
instance instDecidableIsSpongeColl (h : List ℤ → ℤ) (p : List ℤ × List ℤ) :
    Decidable (IsSpongeColl h p) := by
  unfold IsSpongeColl; infer_instance

/-- **The deployed row denotation is DECIDABLE.** So "this row is accepted by the effect's circuit"
can sit inside a security game's counted win relation without a classical choice. -/
instance instDecidableSatisfiedVm (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) :
    Decidable (satisfiedVm hash d env isFirst isLast) := by
  unfold satisfiedVm; infer_instance

/-! ## §1 — the two deployed EffectVM commitments, as `SpongeCarrier`s.

Each supplies exactly what the shared spine asks: a TOTAL extractor and its UNCONDITIONAL correctness.
No injectivity, no collision-resistance, no floor — those all live in the `Eff` parameter now. -/

/-- **THE GROUP-4 TRACE DOES NOT BLOW UP ITS INPUT.** Every branch returns either the freshly built
four-slot outer list (`8` felts) or one of the inner block pairs, so the pair it hands back is bounded
by the two inputs' block sizes plus a constant `8`. In the fall-through branch the guards have already
forced `A₁ = A₂`, which is what makes that branch's `(A₁, A₁)` output honestly bounded. -/
theorem group4Find_len_le (h : List ℤ → ℤ) (A₁ B₁ C₁ : List ℤ) (d₁ : ℤ)
    (A₂ B₂ C₂ : List ℤ) (d₂ : ℤ) :
    (group4Find h A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂).1.length
      + (group4Find h A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂).2.length
      ≤ (A₁.length + B₁.length + C₁.length) + (A₂.length + B₂.length + C₂.length) + 8 := by
  unfold group4Find
  split_ifs with h0 h1 h2 h3
  · simp only [List.length_cons, List.length_nil]; omega
  · simp only; omega
  · simp only; omega
  · simp only; omega
  · push_neg at h1
    subst h1
    simp only
    omega

/-- The payload the NARROW deployed commitment binds: the three absorbed GROUP-4 blocks and the
fourth outer slot (the record digest). -/
abbrev G4Val : Type := (List ℤ × List ℤ × List ℤ) × ℤ

/-- **`group4Carrier` — the deployed 13-column `state_commit`, as a `SpongeCarrier`.** `enc` IS
`EffectVmEmitTransferSound.commitOf` re-presented over the block decomposition; `find` IS the deployed
GROUP-4 peel `Poseidon2Binding.group4Find`, and `find_spec` is its UNCONDITIONAL correctness. -/
def group4Carrier : SpongeCarrier where
  Ctx := Unit
  Val := G4Val
  valDecEq := inferInstance
  enc := fun h _ v => h [h v.1.1, h v.1.2.1, h v.1.2.2, v.2]
  find := fun h _ a b => group4Find h a.1.1 a.1.2.1 a.1.2.2 a.2 b.1.1 b.1.2.1 b.1.2.2 b.2
  find_spec := by
    rintro h _ ⟨⟨A₁, B₁, C₁⟩, d₁⟩ ⟨⟨A₂, B₂, C₂⟩, d₂⟩ hne henc
    rcases group4Find_spec h A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂ henc with ⟨hA, hB, hC, hd⟩ | hcoll
    · exact absurd (by rw [hA, hB, hC, hd]) hne
    · exact hcoll
  size := fun _ v => v.1.1.length + v.1.2.1.length + v.1.2.2.length + 1
  outCo := 1
  outBo := 8
  find_len_le := by
    rintro h _ ⟨⟨A₁, B₁, C₁⟩, d₁⟩ ⟨⟨A₂, B₂, C₂⟩, d₂⟩
    have := group4Find_len_le h A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂
    show (group4Find h A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂).1.length
        + (group4Find h A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂).2.length
      ≤ 1 * ((A₁.length + B₁.length + C₁.length + 1)
              + (A₂.length + B₂.length + C₂.length + 1)) + 8
    omega

/-- The payload the WIDE deployed commitment binds: the three absorbed GROUP-4 blocks and the WHOLE
side-table sub-block behind the fourth slot. Carrying `SysRoots` (not just its digest) is what makes
ONE carrier cover BOTH of the wide commitment's collision legs. -/
abbrev WideVal : Type := (List ℤ × List ℤ × List ℤ) × SysRoots

/-- The wide extractor: take the GROUP-4 peel's pair when that pair genuinely collides, otherwise the
two ordered side-table root lists. Decidable branch, so this is a TOTAL computable function with no
`Classical.choice` in the walk. -/
def wideFind (h : List ℤ → ℤ) (a b : WideVal) : List ℤ × List ℤ :=
  if IsSpongeColl h (group4Find h a.1.1 a.1.2.1 a.1.2.2 (h (rootList a.2))
                                 b.1.1 b.1.2.1 b.1.2.2 (h (rootList b.2)))
  then group4Find h a.1.1 a.1.2.1 a.1.2.2 (h (rootList a.2))
                    b.1.1 b.1.2.1 b.1.2.2 (h (rootList b.2))
  else (rootList a.2, rootList b.2)

theorem rootList_length_eight (sr : SysRoots) : (rootList sr).length = 8 :=
  List.length_ofFn

/-- **`wideStateCarrier` — the deployed `system_roots`-absorbing `state_commit`, as a
`SpongeCarrier`.** `enc` IS `EffectVmFullStateRunnable.wideCommitOf` with the fourth slot expanded to
the roots sponge (`systemRootsDigest_eq_hash_rootList`), so the payload is the WHOLE 17-field bound
content: twelve absorbed state columns AND the eight side-table roots. -/
def wideStateCarrier : SpongeCarrier where
  Ctx := Unit
  Val := WideVal
  valDecEq := inferInstance
  enc := fun h _ v => h [h v.1.1, h v.1.2.1, h v.1.2.2, h (rootList v.2)]
  find := fun h _ a b => wideFind h a b
  find_spec := by
    intro h _ a b hne henc
    show IsSpongeColl h (wideFind h a b)
    unfold wideFind
    split_ifs with hg
    · exact hg
    · rcases group4Find_spec h a.1.1 a.1.2.1 a.1.2.2 (h (rootList a.2))
          b.1.1 b.1.2.1 b.1.2.2 (h (rootList b.2)) henc with ⟨hA, hB, hC, hd⟩ | hcoll
      · -- the blocks agree, so the payloads differ in the SIDE-TABLE sub-block.
        have hsr : a.2 ≠ b.2 := by
          intro hs
          apply hne
          obtain ⟨⟨A₁, B₁, C₁⟩, s₁⟩ := a
          obtain ⟨⟨A₂, B₂, C₂⟩, s₂⟩ := b
          simp only at hA hB hC hs
          rw [hA, hB, hC, hs]
        exact ⟨fun hlist => hsr (List.ofFn_inj.mp hlist), hd⟩
      · exact absurd hcoll hg
  size := fun _ v => v.1.1.length + v.1.2.1.length + v.1.2.2.length + (rootList v.2).length
  outCo := 1
  outBo := 8
  find_len_le := by
    intro h _ a b
    have hr₁ : (rootList a.2).length = 8 := rootList_length_eight a.2
    have hr₂ : (rootList b.2).length = 8 := rootList_length_eight b.2
    show (wideFind h a b).1.length + (wideFind h a b).2.length
      ≤ 1 * ((a.1.1.length + a.1.2.1.length + a.1.2.2.length + (rootList a.2).length)
              + (b.1.1.length + b.1.2.1.length + b.1.2.2.length + (rootList b.2).length)) + 8
    unfold wideFind
    split_ifs with hg
    · have := group4Find_len_le h a.1.1 a.1.2.1 a.1.2.2 (h (rootList a.2))
        b.1.1 b.1.2.1 b.1.2.2 (h (rootList b.2))
      omega
    · show (rootList a.2).length + (rootList b.2).length ≤ _
      omega

/-! ## §2 — the NARROW per-effect ROW game, and its lift into the carrier game. -/

/-- The per-effect data a NARROW (13-column) runnable descriptor supplies to ride this reduction: its
hash sites ARE the deployed GROUP-4 sites. That is the whole obligation. -/
structure NarrowRowSpec where
  /-- The effect's emitted EffectVM descriptor. -/
  descriptor : EffectVmDescriptor
  /-- Its hash sites ARE the deployed narrow GROUP-4 sites. -/
  usesTransferSites : descriptor.hashSites = transferHashSites

/-- **THE NARROW ROW FORGERY GAME, AT ONE EFFECT'S DESCRIPTOR.** The adversary is handed a uniformly
sampled domain-separation tag and WINS iff it outputs two rows that are BOTH ACCEPTED by the deployed
circuit `E.descriptor`, publish the SAME after-`state_commit`, and yet DISAGREE on the absorbed
after-state block. A win is a ghost post-state accepted by the circuit the prover runs. -/
def narrowRowBreakGame (D : SpongeKeyed) (E : NarrowRowSpec) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => VmRowEnv × VmRowEnv
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    satisfiedVm (D.hashAt t) E.descriptor c.1 true true
      ∧ satisfiedVm (D.hashAt t) E.descriptor c.2 true true
      ∧ c.1.loc (saCol state.STATE_COMMIT) = c.2.loc (saCol state.STATE_COMMIT)
      ∧ absorbedCols c.1 ≠ absorbedCols c.2
  winsDec := fun _ t c => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT.** -/
theorem narrowRowBreakGame_wins_iff (D : SpongeKeyed) (E : NarrowRowSpec) (l : ℕ) (t : D.Tag)
    (c : VmRowEnv × VmRowEnv) :
    (narrowRowBreakGame D E).wins l t c ↔
      (satisfiedVm (D.hashAt t) E.descriptor c.1 true true
        ∧ satisfiedVm (D.hashAt t) E.descriptor c.2 true true
        ∧ c.1.loc (saCol state.STATE_COMMIT) = c.2.loc (saCol state.STATE_COMMIT)
        ∧ absorbedCols c.1 ≠ absorbedCols c.2) :=
  Iff.rfl

/-- Read a row's narrow GROUP-4 payload off its absorbed columns. -/
def narrowPayload (e : VmRowEnv) : G4Val :=
  ((transferBlockA e, transferBlockB e, transferBlockC e),
   e.loc (auxCol aux_off.STATE_RECORD_DIGEST))

/-- **THE LIFT, AS A MAP OF ADVERSARIES.** A row-level forger IS a `group4Carrier` equivocator: read
the two rows' payloads off their columns. -/
def narrowRowToCarrier (D : SpongeKeyed) (E : NarrowRowSpec)
    (A : Adversary (narrowRowBreakGame D E)) : Adversary (carrierBreakGame D group4Carrier) where
  run := fun l t => ((), narrowPayload (A.run l t).1, narrowPayload (A.run l t).2)

/-- **⚑ WIN-PRESERVATION.** A row forgery IS a commitment equivocation: satisfaction gives the
deployed hash sites, so each published `state_commit` IS `commitOf` of that row's payload; the shared
commit column then equates the two encodings, and the absorbed-column disagreement makes the payloads
distinct. -/
theorem narrowRow_wins_imp (D : SpongeKeyed) (E : NarrowRowSpec)
    (A : Adversary (narrowRowBreakGame D E)) (l : ℕ) (t : D.Tag)
    (hwin : (narrowRowBreakGame D E).wins l t (A.run l t)) :
    (carrierBreakGame D group4Carrier).wins l t ((narrowRowToCarrier D E A).run l t) := by
  obtain ⟨hsat₁, hsat₂, hcommit, hne⟩ := hwin
  have hs₁ : siteHoldsAll (D.hashAt t) (A.run l t).1 transferHashSites :=
    E.usesTransferSites ▸ hsat₁.2.1
  have hs₂ : siteHoldsAll (D.hashAt t) (A.run l t).2 transferHashSites :=
    E.usesTransferSites ▸ hsat₂.2.1
  refine ⟨?_, ?_⟩
  · -- the payloads DIFFER: `absorbedCols` is exactly the payload flattened.
    intro hpay
    apply hne
    have hA : transferBlockA (A.run l t).1 = transferBlockA (A.run l t).2 :=
      congrArg (fun v => v.1.1) hpay
    have hB : transferBlockB (A.run l t).1 = transferBlockB (A.run l t).2 :=
      congrArg (fun v => v.1.2.1) hpay
    have hC : transferBlockC (A.run l t).1 = transferBlockC (A.run l t).2 :=
      congrArg (fun v => v.1.2.2) hpay
    have hd : (A.run l t).1.loc (auxCol aux_off.STATE_RECORD_DIGEST)
        = (A.run l t).2.loc (auxCol aux_off.STATE_RECORD_DIGEST) :=
      congrArg (fun v => v.2) hpay
    show transferBlockA (A.run l t).1 ++ transferBlockB (A.run l t).1
          ++ transferBlockC (A.run l t).1
          ++ [(A.run l t).1.loc (auxCol aux_off.STATE_RECORD_DIGEST)]
        = transferBlockA (A.run l t).2 ++ transferBlockB (A.run l t).2
          ++ transferBlockC (A.run l t).2
          ++ [(A.run l t).2.loc (auxCol aux_off.STATE_RECORD_DIGEST)]
    rw [hA, hB, hC, hd]
  · -- the two commitments AGREE: each is `commitOf` of its own payload (`enc` IS `commitOf`).
    have h₁ := commit_eq_commitOf (D.hashAt t) (A.run l t).1 hs₁
    have h₂ := commit_eq_commitOf (D.hashAt t) (A.run l t).2 hs₂
    exact h₁.symm.trans (hcommit.trans h₂)

/-- **THE ADVANTAGE INEQUALITY for the narrow lift — UNCONDITIONAL, over ALL adversaries.** -/
theorem narrowRow_adv_le (D : SpongeKeyed) (E : NarrowRowSpec)
    (A : Adversary (narrowRowBreakGame D E)) (l : ℕ) :
    gameAdv (narrowRowBreakGame D E) A l
      ≤ gameAdv (carrierBreakGame D group4Carrier) (narrowRowToCarrier D E A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact narrowRow_wins_imp D E A l t ht

/-- **⚑ THE REDUCED NARROW ROW BINDING — the headline that replaces the `_binds_block_or_collides` /
`_binds_state_or_collides` disjunctions.** Under the DEPLOYED sponge's collision floor at the class
`Eff`, a forger producing two SATISFYING rows of the effect's circuit that publish one commitment
while disagreeing on an absorbed state column has NEGLIGIBLE advantage. -/
theorem narrowRow_binds_advantage_bound (D : SpongeKeyed) (E : NarrowRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (narrowRowBreakGame D E))
    (hEff : Eff (carrierBreakToFinder D group4Carrier (narrowRowToCarrier D E A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (narrowRowBreakGame D E) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (narrowRowBreakGame D E) A l).1)
    (narrowRow_adv_le D E A)
    (carrier_binds_advantage_bound D group4Carrier Eff (narrowRowToCarrier D E A) hEff hCR)

/-! ## §3 — the WIDE per-effect ROW game (all 17 fields), and its lift. -/

/-- The per-effect data a WIDE (`system_roots`-absorbing) runnable descriptor supplies: its hash sites
ARE the wide sites. -/
structure WideRowSpec where
  /-- The effect's WIDE emitted descriptor. -/
  descriptor : EffectVmDescriptor
  /-- Its hash sites ARE the `system_roots`-absorbing wide sites. -/
  usesWideSites : descriptor.hashSites = wideHashSites

/-- **THE WIDE FULL-STATE ROW FORGERY GAME, AT ONE EFFECT'S WIDE DESCRIPTOR.** A win is two rows BOTH
ACCEPTED by the deployed wide circuit, each pinning its after-`state_commit` to the published
`NEW_COMMIT`, each carrying the genuine `systemRootsDigest` of its own side-table sub-block, publishing
the SAME `NEW_COMMIT` — and yet DISAGREEING on the absorbed state block or on some side-table root.

The win relation is EXACTLY the hypotheses of
`EffectVmFullStateRunnable.runnable_full_commit_binds_or_collides` plus its NEGATED conclusion: the
game IS "the whole-state anti-ghost fails at this effect's circuit". -/
def wideRowBreakGame (D : SpongeKeyed) (E : WideRowSpec) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    satisfiedVm (D.hashAt t) E.descriptor c.1.1 true true
      ∧ satisfiedVm (D.hashAt t) E.descriptor c.2.1 true true
      ∧ c.1.1.loc (saCol state.STATE_COMMIT) = c.1.1.pub pi.NEW_COMMIT
      ∧ c.2.1.loc (saCol state.STATE_COMMIT) = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.pub pi.NEW_COMMIT = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.1.2
      ∧ c.2.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.2.2
      ∧ ¬ (baseAbsorbedCols c.1.1 = baseAbsorbedCols c.2.1
            ∧ ∀ i : Fin N_SYSTEM_ROOTS, c.1.2 i = c.2.2 i)
  winsDec := fun _ t c => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT.** -/
theorem wideRowBreakGame_wins_iff (D : SpongeKeyed) (E : WideRowSpec) (l : ℕ) (t : D.Tag)
    (c : (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)) :
    (wideRowBreakGame D E).wins l t c ↔
      (satisfiedVm (D.hashAt t) E.descriptor c.1.1 true true
        ∧ satisfiedVm (D.hashAt t) E.descriptor c.2.1 true true
        ∧ c.1.1.loc (saCol state.STATE_COMMIT) = c.1.1.pub pi.NEW_COMMIT
        ∧ c.2.1.loc (saCol state.STATE_COMMIT) = c.2.1.pub pi.NEW_COMMIT
        ∧ c.1.1.pub pi.NEW_COMMIT = c.2.1.pub pi.NEW_COMMIT
        ∧ c.1.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.1.2
        ∧ c.2.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.2.2
        ∧ ¬ (baseAbsorbedCols c.1.1 = baseAbsorbedCols c.2.1
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, c.1.2 i = c.2.2 i)) :=
  Iff.rfl

/-- Read a wide row's payload: its three absorbed GROUP-4 blocks and its side-table sub-block. -/
def widePayload (c : VmRowEnv × SysRoots) : WideVal :=
  ((wideBlockA c.1, wideBlockB c.1, wideBlockC c.1), c.2)

/-- **THE WIDE LIFT, AS A MAP OF ADVERSARIES.** -/
def wideRowToCarrier (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRowBreakGame D E)) : Adversary (carrierBreakGame D wideStateCarrier) where
  run := fun l t => ((), widePayload (A.run l t).1, widePayload (A.run l t).2)

/-- **⚑ WIN-PRESERVATION for the wide lift.** Satisfaction gives the wide hash sites, so each
published `state_commit` IS `wideCommitOf` of that row's blocks and carrier; the carrier IS the roots
sponge, so the encoding is the carrier's `enc` at the row's payload. The two commit pins plus the
shared `NEW_COMMIT` equate them, and the 17-field disagreement makes the payloads distinct. -/
theorem wideRow_wins_imp (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRowBreakGame D E)) (l : ℕ) (t : D.Tag)
    (hwin : (wideRowBreakGame D E).wins l t (A.run l t)) :
    (carrierBreakGame D wideStateCarrier).wins l t ((wideRowToCarrier D E A).run l t) := by
  obtain ⟨hsat₁, hsat₂, hpin₁, hpin₂, hpub, hc₁, hc₂, hne⟩ := hwin
  have hs₁ : siteHoldsAll (D.hashAt t) (A.run l t).1.1 wideHashSites :=
    E.usesWideSites ▸ hsat₁.2.1
  have hs₂ : siteHoldsAll (D.hashAt t) (A.run l t).2.1 wideHashSites :=
    E.usesWideSites ▸ hsat₂.2.1
  have hcommit : (A.run l t).1.1.loc (saCol state.STATE_COMMIT)
      = (A.run l t).2.1.loc (saCol state.STATE_COMMIT) := by
    rw [hpin₁, hpin₂, hpub]
  refine ⟨?_, ?_⟩
  · -- the payloads DIFFER.
    intro hpay
    apply hne
    have hA : wideBlockA (A.run l t).1.1 = wideBlockA (A.run l t).2.1 :=
      congrArg (fun v => v.1.1) hpay
    have hB : wideBlockB (A.run l t).1.1 = wideBlockB (A.run l t).2.1 :=
      congrArg (fun v => v.1.2.1) hpay
    have hC : wideBlockC (A.run l t).1.1 = wideBlockC (A.run l t).2.1 :=
      congrArg (fun v => v.1.2.2) hpay
    have hsr : (A.run l t).1.2 = (A.run l t).2.2 := congrArg (fun v => v.2) hpay
    refine ⟨?_, fun i => by rw [hsr]⟩
    show wideBlockA (A.run l t).1.1 ++ wideBlockB (A.run l t).1.1 ++ wideBlockC (A.run l t).1.1
        = wideBlockA (A.run l t).2.1 ++ wideBlockB (A.run l t).2.1 ++ wideBlockC (A.run l t).2.1
    rw [hA, hB, hC]
  · -- the two commitments AGREE.
    have h₁ := wide_commit_eq (D.hashAt t) (A.run l t).1.1 hs₁
    have h₂ := wide_commit_eq (D.hashAt t) (A.run l t).2.1 hs₂
    have hr₁ : (A.run l t).1.1.loc sysRootsDigestCol = (D.hashAt t) (rootList (A.run l t).1.2) := by
      rw [hc₁, systemRootsDigest_eq_hash_rootList]
    have hr₂ : (A.run l t).2.1.loc sysRootsDigestCol = (D.hashAt t) (rootList (A.run l t).2.2) := by
      rw [hc₂, systemRootsDigest_eq_hash_rootList]
    show (D.hashAt t) [ (D.hashAt t) (wideBlockA (A.run l t).1.1),
        (D.hashAt t) (wideBlockB (A.run l t).1.1),
        (D.hashAt t) (wideBlockC (A.run l t).1.1),
        (D.hashAt t) (rootList (A.run l t).1.2) ]
      = (D.hashAt t) [ (D.hashAt t) (wideBlockA (A.run l t).2.1),
        (D.hashAt t) (wideBlockB (A.run l t).2.1),
        (D.hashAt t) (wideBlockC (A.run l t).2.1),
        (D.hashAt t) (rootList (A.run l t).2.2) ]
    rw [← hr₁, ← hr₂]
    exact h₁.symm.trans (hcommit.trans h₂)

/-- **THE ADVANTAGE INEQUALITY for the wide lift — UNCONDITIONAL, over ALL adversaries.** -/
theorem wideRow_adv_le (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRowBreakGame D E)) (l : ℕ) :
    gameAdv (wideRowBreakGame D E) A l
      ≤ gameAdv (carrierBreakGame D wideStateCarrier) (wideRowToCarrier D E A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact wideRow_wins_imp D E A l t ht

/-- **⚑ THE REDUCED WIDE FULL-STATE BINDING — the headline that replaces
`_runnable_binds_full_state_or_collides`.** Under the DEPLOYED sponge's collision floor at the class
`Eff`, a forger of the effect's whole 17-field runnable commitment has NEGLIGIBLE advantage. -/
theorem wideRow_binds_advantage_bound (D : SpongeKeyed) (E : WideRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRowBreakGame D E))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier (wideRowToCarrier D E A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRowBreakGame D E) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (wideRowBreakGame D E) A l).1)
    (wideRow_adv_le D E A)
    (carrier_binds_advantage_bound D wideStateCarrier Eff (wideRowToCarrier D E A) hEff hCR)

/-! ## §4 — the TAMPER sub-games: the `_rejects_*_tamper` teeth, as reductions.

A TAMPER is a forgery whose disagreement is LOCALIZED — at an absorbed state-block column (a forged
balance, a tampered field, a forged `cap_root`), or at a named side-table root index (a dropped
escrow, an omitted nullifier, a reordered queue). Each keeps its own game so the exported tooth keeps
its content, and maps into the full-state game by the identity reshaping. -/

/-- **THE STATE-BLOCK TAMPER GAME.** -/
def wideStateTamperGame (D : SpongeKeyed) (E : WideRowSpec) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    satisfiedVm (D.hashAt t) E.descriptor c.1.1 true true
      ∧ satisfiedVm (D.hashAt t) E.descriptor c.2.1 true true
      ∧ c.1.1.loc (saCol state.STATE_COMMIT) = c.1.1.pub pi.NEW_COMMIT
      ∧ c.2.1.loc (saCol state.STATE_COMMIT) = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.pub pi.NEW_COMMIT = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.1.2
      ∧ c.2.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.2.2
      ∧ baseAbsorbedCols c.1.1 ≠ baseAbsorbedCols c.2.1
  winsDec := fun _ t c => inferInstance

/-- **THE SIDE-TABLE-ROOT TAMPER GAME.** -/
def wideRootTamperGame (D : SpongeKeyed) (E : WideRowSpec) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    satisfiedVm (D.hashAt t) E.descriptor c.1.1 true true
      ∧ satisfiedVm (D.hashAt t) E.descriptor c.2.1 true true
      ∧ c.1.1.loc (saCol state.STATE_COMMIT) = c.1.1.pub pi.NEW_COMMIT
      ∧ c.2.1.loc (saCol state.STATE_COMMIT) = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.pub pi.NEW_COMMIT = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.1.2
      ∧ c.2.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.2.2
      ∧ ∃ i : Fin N_SYSTEM_ROOTS, c.1.2 i ≠ c.2.2 i
  winsDec := fun _ t c => inferInstance

/-- A state-block tamper IS a full-state forgery (the identity reshaping). -/
def stateTamperToWide (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideStateTamperGame D E)) : Adversary (wideRowBreakGame D E) where
  run := fun l t => A.run l t

/-- A side-table-root tamper IS a full-state forgery (the identity reshaping). -/
def rootTamperToWide (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRootTamperGame D E)) : Adversary (wideRowBreakGame D E) where
  run := fun l t => A.run l t

theorem stateTamper_wins_imp (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideStateTamperGame D E)) (l : ℕ) (t : D.Tag)
    (hwin : (wideStateTamperGame D E).wins l t (A.run l t)) :
    (wideRowBreakGame D E).wins l t ((stateTamperToWide D E A).run l t) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, htamper⟩ := hwin
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, fun h => htamper h.1⟩

theorem rootTamper_wins_imp (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRootTamperGame D E)) (l : ℕ) (t : D.Tag)
    (hwin : (wideRootTamperGame D E).wins l t (A.run l t)) :
    (wideRowBreakGame D E).wins l t ((rootTamperToWide D E A).run l t) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, ⟨i, hi⟩⟩ := hwin
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, fun h => hi (h.2 i)⟩

theorem stateTamper_adv_le (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideStateTamperGame D E)) (l : ℕ) :
    gameAdv (wideStateTamperGame D E) A l
      ≤ gameAdv (wideRowBreakGame D E) (stateTamperToWide D E A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact stateTamper_wins_imp D E A l t ht

theorem rootTamper_adv_le (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRootTamperGame D E)) (l : ℕ) :
    gameAdv (wideRootTamperGame D E) A l
      ≤ gameAdv (wideRowBreakGame D E) (rootTamperToWide D E A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact rootTamper_wins_imp D E A l t ht

/-- **⚑ THE REDUCED STATE-BLOCK TAMPER TOOTH — replaces `_rejects_state_tamper_or_collides`.** An
efficient adversary cannot keep the published `NEW_COMMIT` while tampering an absorbed state-block
column of the effect's wide row, except with negligible probability. -/
theorem wide_state_tamper_advantage_bound (D : SpongeKeyed) (E : WideRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideStateTamperGame D E))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D E (stateTamperToWide D E A))))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideStateTamperGame D E) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (wideStateTamperGame D E) A l).1)
    (stateTamper_adv_le D E A)
    (wideRow_binds_advantage_bound D E Eff (stateTamperToWide D E A) hEff hCR)

/-- **⚑ THE REDUCED SIDE-TABLE-ROOT TAMPER TOOTH — replaces `_rejects_root_tamper_or_collides`.** An
efficient adversary cannot keep the published `NEW_COMMIT` while tampering a side-table root, except
with negligible probability. -/
theorem wide_root_tamper_advantage_bound (D : SpongeKeyed) (E : WideRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRootTamperGame D E))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D E (rootTamperToWide D E A))))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRootTamperGame D E) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (wideRootTamperGame D E) A l).1)
    (rootTamper_adv_le D E A)
    (wideRow_binds_advantage_bound D E Eff (rootTamperToWide D E A) hEff hCR)

/-! ## §5 — ⚑ THE DISCHARGED HEADLINES, ON THE PROVED KEYED-ROM FLOOR.

The four `IsPolyTime` discharges that stood here (`narrowRow_binds_from_polyTime`,
`wideRow_binds_from_polyTime`, `wide_state_tamper_from_polyTime`, `wide_root_tamper_from_polyTime`)
carried `HashCRHardQuant (spongeFamily D) (IsPolyTime …)` — a floor
`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` PROVES FALSE at the
deployed sponge, and no `Eff` repairs the fixed-hash game (`Crypto.RomBindingReduction`'s header).
They are DELETED. The successors land the COMMITMENT layer on a SAMPLED oracle, where
`KeyedRomFloor.keyedRom_hard` (the birthday bound) is a THEOREM.

⚑ THE MODELLING STEP, STATED (not smuggled), the `Exec.SystemRootsBindingReduction` §7 discipline:

  * the sampled `H : Tag × Msg → Fin (2 ^ l)` replaces the fixed public sponge; there is NO `l` at
    which `Fin (2 ^ l)` is the deployed ~31-bit felt (birthday ≈ `2^15.5`, the felt-width wound);
  * the message domain is the TRUNCATED deployed absorb schedule, domain-separated by constructor
    inside ONE family: the three GROUP-4 state blocks (four BabyBear-range felts each — the deployed
    `wideBlockA/B/C` width, a `rfl` fact), the eight-root side-table sub-block, and the OUTER
    four-slot absorb whose entries are the inner digests (at the ideal width those are not felts —
    the SAME felt-width residual, carried visibly in the type);
  * the two-level nest `h [h A, h B, h C, h roots]` is genuinely re-absorbed: the oracle appears
    INSIDE the win relation, which is what neither single carrier could say.

⚑ WHAT THE ROM LAYER DOES NOT CARRY: the per-effect CIRCUIT-satisfaction content (`satisfiedVm` at
`E.descriptor`) is inherently about the fixed deployed hash and stays where it is honest — in §2–§4's
`_advantage_bound` forms, `hEff` in the open. The ROM successors price the COMMITMENT equivocation
those forms reduce to, which is exactly the leg the deleted discharges claimed and could not have. -/

section RomSuccessor

open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction
open Dregg2.Crypto.RomCarrierSites
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.ConcreteSecurity (PolyBounded)

/-- A truncated GROUP-4 state block: four BabyBear-range felts (the deployed `wideBlock*` width). -/
abbrev StateBlock4 : Type := Fin 4 → Fin babyBearP

/-- The truncated side-table sub-block: eight BabyBear-range roots. -/
abbrev RootsBlock8 : Type := Fin 8 → Fin babyBearP

/-- **THE ORACLE MESSAGE DOMAIN** — the deployed wide absorb schedule, domain-separated by
constructor: `inl` a state block (an inner absorb), `inr (inl)` the roots sub-block (the fourth
inner absorb), `inr (inr)` the OUTER four-slot list of inner digests. -/
abbrev WideRomMsg (l : ℕ) : Type :=
  StateBlock4 ⊕ RootsBlock8 ⊕ (Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l))

/-- **THE EFFECTVM ROW KEYED ROM FAMILY** — keyed by the DEPLOYED tag space. -/
def wideRomFamily (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) : KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty WideRomMsg
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨Sum.inl (fun _ => ⟨0, babyBearP_pos⟩)⟩)

theorem wideRomFamily_card_R (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (l : ℕ) :
    letI := (wideRomFamily D tagDec).rFin l
    Fintype.card ((wideRomFamily D tagDec).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- The truncated WIDE payload — the three state blocks and the whole side-table sub-block: the
17-field bound content, exactly `WideVal`'s shape at the truncated widths. -/
abbrev WideRomVal : Type := (StateBlock4 × StateBlock4 × StateBlock4) × RootsBlock8

/-- **THE INNER CARRIER** — binds ONE inner absorb (a state block or the roots sub-block). The
embedding is by constructor, injective on the nose. -/
def wideInnerCarrier (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) :
    RomCarrier (wideRomFamily D tagDec) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => StateBlock4 ⊕ RootsBlock8)
    (fun _ => inferInstance)
    (fun _ _ v => Sum.elim Sum.inl (fun r => Sum.inr (Sum.inl r)) v)
    (fun _ _ a b h => by
      cases a with
      | inl x =>
          cases b with
          | inl y => rw [Sum.inl_injective h]
          | inr y => exact absurd h Sum.inl_ne_inr
      | inr x =>
          cases b with
          | inl y => exact absurd h Sum.inr_ne_inl
          | inr y => rw [Sum.inl_injective (Sum.inr_injective h)])

/-- **THE OUTER CARRIER** — binds the four-slot outer absorb (the list of inner digests). -/
def wideOuterCarrier (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) :
    RomCarrier (wideRomFamily D tagDec) :=
  taggedCarrier _ (fun _ => Unit)
    (fun l => Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l))
    (fun _ => inferInstance)
    (fun _ _ v => Sum.inr (Sum.inr v))
    (fun _ _ a b h => Sum.inr_injective (Sum.inr_injective h))

/-- **THE DEPLOYED NESTED COMMIT AT THE SAMPLED ORACLE** — `H (t, outer (H(t,A), H(t,B), H(t,C),
H(t,roots)))`: the ROM restatement of `wideStateCarrier.enc = h [h A, h B, h C, h (rootList sr)]`,
with the inner digests genuinely re-absorbed by the outer query. -/
def wideRomCommit (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (l : ℕ)
    (H : (wideRomFamily D tagDec).toRomFamily.D l → (wideRomFamily D tagDec).toRomFamily.R l)
    (t : D.Tag) (v : WideRomVal) : (wideRomFamily D tagDec).toRomFamily.R l :=
  H (t, Sum.inr (Sum.inr
    (H (t, Sum.inl v.1.1), H (t, Sum.inl v.1.2.1), H (t, Sum.inl v.1.2.2),
     H (t, Sum.inr (Sum.inl v.2)))))

/-- **THE WIDE FULL-STATE ROM FORGERY** — two DISTINCT truncated 17-field payloads whose NESTED
deployed commitments agree at the sampled oracle. The ROM restatement of `wideRowBreakGame`'s
commitment content (the `satisfiedVm` legs are fixed-hash content, §-header). -/
def effectVmWideRomForgery (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) :
    RomForgery (wideRomFamily D tagDec) where
  Ans := fun _ => D.Tag × WideRomVal × WideRomVal
  wins := fun l H a =>
    a.2.1 ≠ a.2.2 ∧ wideRomCommit D tagDec l H a.1 a.2.1 = wideRomCommit D tagDec l H a.1 a.2.2
  winsDec := fun l _ _ => by
    letI := ((wideRomFamily D tagDec).toRomFamily).rDec l
    exact instDecidableAnd

/-- The wide ROM forgery game. -/
abbrev wideRomBreakGame (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) : Game :=
  (effectVmWideRomForgery D tagDec).game

/-- **THE INNER-LEG EXTRACTION** — a pure post-map of the forger's program: select the FIRST
component at which the two payloads disagree (state block A, B, C, then the roots sub-block). No
queries are added; whether the selected pair actually collides is decided by the sampled oracle in
the union bound's case split, not by the extractor. -/
def wideInnerSelect (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (l : ℕ)
    (a : (effectVmWideRomForgery D tagDec).Ans l) :
    (wideInnerCarrier D tagDec).Ctx l
      × (wideInnerCarrier D tagDec).Val l × (wideInnerCarrier D tagDec).Val l :=
  let v := a.2.1
  let w := a.2.2
  if v.1.1 ≠ w.1.1 then ((a.1, ()), Sum.inl v.1.1, Sum.inl w.1.1)
  else if v.1.2.1 ≠ w.1.2.1 then ((a.1, ()), Sum.inl v.1.2.1, Sum.inl w.1.2.1)
  else if v.1.2.2 ≠ w.1.2.2 then ((a.1, ()), Sum.inl v.1.2.2, Sum.inl w.1.2.2)
  else ((a.1, ()), Sum.inr v.2, Sum.inr w.2)

/-- **THE OUTER-LEG EXTRACTION** — run the forger, then RE-QUERY the eight inner points and answer
with the two outer four-slot tuples: `bindComp` with an eight-query continuation. -/
def wideOuterComp (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (M : ∀ l, OracleComp ((wideRomFamily D tagDec).toRomFamily.D l)
      ((wideRomFamily D tagDec).toRomFamily.R l) ((effectVmWideRomForgery D tagDec).Ans l)) :
    Dregg2.Crypto.RomBindingReduction.RomCarrierComp (wideRomFamily D tagDec)
      (wideOuterCarrier D tagDec) :=
  fun l => OracleComp.bindComp (M l) (fun a =>
    OracleComp.query (a.1, Sum.inl a.2.1.1.1) (fun d₁ =>
    OracleComp.query (a.1, Sum.inl a.2.1.1.2.1) (fun d₂ =>
    OracleComp.query (a.1, Sum.inl a.2.1.1.2.2) (fun d₃ =>
    OracleComp.query (a.1, Sum.inr (Sum.inl a.2.1.2)) (fun d₄ =>
    OracleComp.query (a.1, Sum.inl a.2.2.1.1) (fun e₁ =>
    OracleComp.query (a.1, Sum.inl a.2.2.1.2.1) (fun e₂ =>
    OracleComp.query (a.1, Sum.inl a.2.2.1.2.2) (fun e₃ =>
    OracleComp.query (a.1, Sum.inr (Sum.inl a.2.2.2)) (fun e₄ =>
    OracleComp.pure ((a.1, ()), (d₁, d₂, d₃, d₄), (e₁, e₂, e₃, e₄)))))))))))

/-- **⚑⚑ THE WIDE FULL-STATE BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the
deleted `wideRow_binds_from_polyTime`: a query-bounded forger that equivocates the whole 17-field
nested runnable commitment has NEGLIGIBLE advantage. The chain peel is the union bound over the ONE
sampled oracle: outer four-slot tuples differ → an outer-carrier win (the extractor re-queries the
eight inner points, budget `Q + 8`); tuples agree → the first differing component is an inner
collision (a `mapOut` post-map, budget `Q`). Each leg dies by the birthday floor. NO floor
hypothesis. -/
theorem wideRow_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (wideRomBreakGame D tagDec))
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomForgery D tagDec) Q A) :
    Negl (gameAdv (wideRomBreakGame D tagDec) A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  refine chained_rom_binds (effectVmWideRomForgery D tagDec)
    (wideInnerCarrier D tagDec) (wideOuterCarrier D tagDec)
    Q (fun l => Q l + 2 + 2 + 2 + 2) hQ
    (polyBounded_sq_add_two _ (polyBounded_sq_add_two _
      (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ hQ))))
    (wideRomFamily_card_R D tagDec) A
    (romCarrierAdv _ _ (fun l => OracleComp.mapOut (wideInnerSelect D tagDec l) (M l)))
    (romCarrierAdv _ _ (wideOuterComp D tagDec M))
    ?_
    ⟨fun l => OracleComp.mapOut (wideInnerSelect D tagDec l) (M l),
      fun l => OracleComp.mapOut_queryBounded _ (hM l), fun _ _ => rfl⟩
    ⟨wideOuterComp D tagDec M,
      fun l => (OracleComp.bindComp_queryBounded (hM l)
        (fun a => QueryBounded.query 7 _ _ (fun _ => QueryBounded.query 6 _ _
          (fun _ => QueryBounded.query 5 _ _ (fun _ => QueryBounded.query 4 _ _
          (fun _ => QueryBounded.query 3 _ _ (fun _ => QueryBounded.query 2 _ _
          (fun _ => QueryBounded.query 1 _ _ (fun _ => QueryBounded.query 0 _ _
          (fun _ => QueryBounded.pure 0 _)))))))))).mono
        (by show Q l + 8 ≤ Q l + 2 + 2 + 2 + 2; omega),
      fun _ _ => rfl⟩
  intro l H hwin
  have hArun : A.run l H = (M l).eval H := hrun l H
  set a := A.run l H with ha
  obtain ⟨hne, heq⟩ := hwin
  have hB₁run : (romCarrierAdv _ _
      (fun l => OracleComp.mapOut (wideInnerSelect D tagDec l) (M l))).run l H
      = wideInnerSelect D tagDec l a := by
    show (OracleComp.mapOut (wideInnerSelect D tagDec l) (M l)).eval H = _
    erw [OracleComp.mapOut_eval, ← hArun]
  have hB₂run : (romCarrierAdv _ _ (wideOuterComp D tagDec M)).run l H
      = ((a.1, ()),
          (H (a.1, Sum.inl a.2.1.1.1), H (a.1, Sum.inl a.2.1.1.2.1),
           H (a.1, Sum.inl a.2.1.1.2.2), H (a.1, Sum.inr (Sum.inl a.2.1.2))),
          (H (a.1, Sum.inl a.2.2.1.1), H (a.1, Sum.inl a.2.2.1.2.1),
           H (a.1, Sum.inl a.2.2.1.2.2), H (a.1, Sum.inr (Sum.inl a.2.2.2)))) := by
    show (wideOuterComp D tagDec M l).eval H = _
    unfold wideOuterComp
    erw [OracleComp.bindComp_eval, ← hArun]
    rfl
  by_cases hT :
      ((H (a.1, Sum.inl a.2.1.1.1), H (a.1, Sum.inl a.2.1.1.2.1),
        H (a.1, Sum.inl a.2.1.1.2.2), H (a.1, Sum.inr (Sum.inl a.2.1.2)))
        : Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l))
      = (H (a.1, Sum.inl a.2.2.1.1), H (a.1, Sum.inl a.2.2.1.2.1),
         H (a.1, Sum.inl a.2.2.1.2.2), H (a.1, Sum.inr (Sum.inl a.2.2.2)))
  · -- the outer tuples AGREE: every inner digest pair collides; the first differing
    -- component is a genuine inner-carrier equivocation.
    refine Or.inl ?_
    rw [hB₁run]
    have h1 : H (a.1, Sum.inl a.2.1.1.1) = H (a.1, Sum.inl a.2.2.1.1) :=
      congrArg (fun p => p.1) hT
    have h2 : H (a.1, Sum.inl a.2.1.1.2.1) = H (a.1, Sum.inl a.2.2.1.2.1) :=
      congrArg (fun p => p.2.1) hT
    have h3 : H (a.1, Sum.inl a.2.1.1.2.2) = H (a.1, Sum.inl a.2.2.1.2.2) :=
      congrArg (fun p => p.2.2.1) hT
    have h4 : H (a.1, Sum.inr (Sum.inl a.2.1.2)) = H (a.1, Sum.inr (Sum.inl a.2.2.2)) :=
      congrArg (fun p => p.2.2.2) hT
    unfold wideInnerSelect
    by_cases hA1 : a.2.1.1.1 ≠ a.2.2.1.1
    · rw [if_pos hA1]
      exact ⟨fun hc => hA1 (Sum.inl_injective hc), h1⟩
    · rw [if_neg hA1]
      by_cases hB1 : a.2.1.1.2.1 ≠ a.2.2.1.2.1
      · rw [if_pos hB1]
        exact ⟨fun hc => hB1 (Sum.inl_injective hc), h2⟩
      · rw [if_neg hB1]
        by_cases hC1 : a.2.1.1.2.2 ≠ a.2.2.1.2.2
        · rw [if_pos hC1]
          exact ⟨fun hc => hC1 (Sum.inl_injective hc), h3⟩
        · rw [if_neg hC1]
          push_neg at hA1 hB1 hC1
          have hroots : a.2.1.2 ≠ a.2.2.2 := by
            intro hr
            apply hne
            exact Prod.ext (Prod.ext hA1 (Prod.ext hB1 hC1)) hr
          exact ⟨fun hc => hroots (Sum.inr_injective hc), h4⟩
  · -- the outer tuples DIFFER: the two outer messages are distinct with one digest —
    -- an outer-carrier equivocation, witnessed by the re-queried tuples.
    refine Or.inr ?_
    rw [hB₂run]
    exact ⟨hT, heq⟩

/-! ### The tamper teeth — the LOCALIZED disagreements, as corollaries of the full-state bound. -/

/-- **THE STATE-BLOCK ROM TAMPER** — the disagreement localized to an absorbed state block. -/
def effectVmWideRomStateTamper (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) :
    RomForgery (wideRomFamily D tagDec) where
  Ans := fun _ => D.Tag × WideRomVal × WideRomVal
  wins := fun l H a =>
    a.2.1.1 ≠ a.2.2.1
      ∧ wideRomCommit D tagDec l H a.1 a.2.1 = wideRomCommit D tagDec l H a.1 a.2.2
  winsDec := fun l _ _ => by
    letI := ((wideRomFamily D tagDec).toRomFamily).rDec l
    exact instDecidableAnd

/-- **THE SIDE-TABLE-ROOT ROM TAMPER** — the disagreement localized to the roots sub-block. -/
def effectVmWideRomRootTamper (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) :
    RomForgery (wideRomFamily D tagDec) where
  Ans := fun _ => D.Tag × WideRomVal × WideRomVal
  wins := fun l H a =>
    a.2.1.2 ≠ a.2.2.2
      ∧ wideRomCommit D tagDec l H a.1 a.2.1 = wideRomCommit D tagDec l H a.1 a.2.2
  winsDec := fun l _ _ => by
    letI := ((wideRomFamily D tagDec).toRomFamily).rDec l
    exact instDecidableAnd

/-- **⚑ THE STATE-BLOCK TAMPER TOOTH, DISCHARGED** — successor of the deleted
`wide_state_tamper_from_polyTime`: a query-bounded adversary cannot keep the published nested
commitment while tampering an absorbed state block, except with negligible probability. -/
theorem wide_state_tamper_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmWideRomStateTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomStateTamper D tagDec) Q A) :
    Negl (gameAdv (effectVmWideRomStateTamper D tagDec).game A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  have hgen : Negl (gameAdv (wideRomBreakGame D tagDec)
      (⟨A.run⟩ : Adversary (wideRomBreakGame D tagDec))) :=
    wideRow_binds_rom D tagDec Q hQ
      (⟨A.run⟩ : Adversary (wideRomBreakGame D tagDec)) ⟨M, hM, hrun⟩
  refine negl_of_le
    (fun l => (gameAdv_mem_unit (effectVmWideRomStateTamper D tagDec).game A l).1)
    (fun l => ?_) hgen
  refine @winProb_le_of_imp _
    (((effectVmWideRomStateTamper D tagDec).game).instFin l) _ _ (fun H hH => ?_)
  replace hH := (Adversary.hit_eq_true _ _ _).mp hH
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  obtain ⟨hne, heq⟩ := hH
  exact ⟨fun hc => hne (congrArg Prod.fst hc), heq⟩

/-- **⚑ THE SIDE-TABLE-ROOT TAMPER TOOTH, DISCHARGED** — successor of the deleted
`wide_root_tamper_from_polyTime`. -/
theorem wide_root_tamper_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmWideRomRootTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomRootTamper D tagDec) Q A) :
    Negl (gameAdv (effectVmWideRomRootTamper D tagDec).game A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  have hgen : Negl (gameAdv (wideRomBreakGame D tagDec)
      (⟨A.run⟩ : Adversary (wideRomBreakGame D tagDec))) :=
    wideRow_binds_rom D tagDec Q hQ
      (⟨A.run⟩ : Adversary (wideRomBreakGame D tagDec)) ⟨M, hM, hrun⟩
  refine negl_of_le
    (fun l => (gameAdv_mem_unit (effectVmWideRomRootTamper D tagDec).game A l).1)
    (fun l => ?_) hgen
  refine @winProb_le_of_imp _
    (((effectVmWideRomRootTamper D tagDec).game).instFin l) _ _ (fun H hH => ?_)
  replace hH := (Adversary.hit_eq_true _ _ _).mp hH
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  obtain ⟨hne, heq⟩ := hH
  exact ⟨fun hc => hne (congrArg Prod.snd hc), heq⟩

/-! ### The NARROW commitment, at the sampled oracle. -/

/-- The narrow outer absorb: three inner digests plus the record-digest felt (the deployed
`[h A, h B, h C, d]` fourth slot is a PAYLOAD felt, not an inner hash). Sharing the wide family
would confuse the two outer shapes, so the narrow chain gets its own family. -/
abbrev NarrowRomMsg (l : ℕ) : Type :=
  StateBlock4 ⊕ ((Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l)) × Fin babyBearP)

/-- The narrow EffectVM ROM family. -/
def narrowRomFamily (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) : KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty NarrowRomMsg
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨Sum.inl (fun _ => ⟨0, babyBearP_pos⟩)⟩)

theorem narrowRomFamily_card_R (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (l : ℕ) :
    letI := (narrowRomFamily D tagDec).rFin l
    Fintype.card ((narrowRomFamily D tagDec).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- The truncated NARROW payload — three state blocks and the record-digest felt (`G4Val`'s shape
at the truncated widths). -/
abbrev NarrowRomVal : Type := (StateBlock4 × StateBlock4 × StateBlock4) × Fin babyBearP

/-- The narrow inner carrier — binds one absorbed state block. -/
def narrowInnerCarrier (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) :
    RomCarrier (narrowRomFamily D tagDec) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => StateBlock4)
    (fun _ => inferInstance) (fun _ _ v => Sum.inl v)
    (fun _ _ _ _ h => Sum.inl_injective h)

/-- The narrow outer carrier — binds the outer absorb (three inner digests + the record felt). -/
def narrowOuterCarrier (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) :
    RomCarrier (narrowRomFamily D tagDec) :=
  taggedCarrier _ (fun _ => Unit)
    (fun l => (Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l)) × Fin babyBearP)
    (fun _ => inferInstance) (fun _ _ v => Sum.inr v)
    (fun _ _ _ _ h => Sum.inr_injective h)

/-- The deployed narrow nested commit at the sampled oracle — the ROM restatement of
`group4Carrier.enc = h [h A, h B, h C, d]`. -/
def narrowRomCommit (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (l : ℕ)
    (H : (narrowRomFamily D tagDec).toRomFamily.D l → (narrowRomFamily D tagDec).toRomFamily.R l)
    (t : D.Tag) (v : NarrowRomVal) : (narrowRomFamily D tagDec).toRomFamily.R l :=
  H (t, Sum.inr ((H (t, Sum.inl v.1.1), H (t, Sum.inl v.1.2.1), H (t, Sum.inl v.1.2.2)), v.2))

/-- **THE NARROW ROM FORGERY** — two DISTINCT truncated GROUP-4 payloads, one nested commitment. -/
def effectVmNarrowRomForgery (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) :
    RomForgery (narrowRomFamily D tagDec) where
  Ans := fun _ => D.Tag × NarrowRomVal × NarrowRomVal
  wins := fun l H a =>
    a.2.1 ≠ a.2.2
      ∧ narrowRomCommit D tagDec l H a.1 a.2.1 = narrowRomCommit D tagDec l H a.1 a.2.2
  winsDec := fun l _ _ => by
    letI := ((narrowRomFamily D tagDec).toRomFamily).rDec l
    exact instDecidableAnd

/-- The narrow inner-leg selection — the first differing state block (pure post-map). If all three
agree the payloads differ only at the record felt, which the OUTER leg then catches (the felt sits
in the outer message). The fallback answer is the (equal) A-blocks — never a win, harmlessly. -/
def narrowInnerSelect (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (l : ℕ)
    (a : (effectVmNarrowRomForgery D tagDec).Ans l) :
    (narrowInnerCarrier D tagDec).Ctx l
      × (narrowInnerCarrier D tagDec).Val l × (narrowInnerCarrier D tagDec).Val l :=
  let v := a.2.1
  let w := a.2.2
  if v.1.1 ≠ w.1.1 then ((a.1, ()), v.1.1, w.1.1)
  else if v.1.2.1 ≠ w.1.2.1 then ((a.1, ()), v.1.2.1, w.1.2.1)
  else ((a.1, ()), v.1.2.2, w.1.2.2)

/-- The narrow outer-leg extraction — re-query the six inner points, answer with the two outer
messages (`bindComp`, budget `Q + 6`). -/
def narrowOuterComp (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (M : ∀ l, OracleComp ((narrowRomFamily D tagDec).toRomFamily.D l)
      ((narrowRomFamily D tagDec).toRomFamily.R l)
      ((effectVmNarrowRomForgery D tagDec).Ans l)) :
    Dregg2.Crypto.RomBindingReduction.RomCarrierComp (narrowRomFamily D tagDec)
      (narrowOuterCarrier D tagDec) :=
  fun l => OracleComp.bindComp (M l) (fun a =>
    OracleComp.query (a.1, Sum.inl a.2.1.1.1) (fun d₁ =>
    OracleComp.query (a.1, Sum.inl a.2.1.1.2.1) (fun d₂ =>
    OracleComp.query (a.1, Sum.inl a.2.1.1.2.2) (fun d₃ =>
    OracleComp.query (a.1, Sum.inl a.2.2.1.1) (fun e₁ =>
    OracleComp.query (a.1, Sum.inl a.2.2.1.2.1) (fun e₂ =>
    OracleComp.query (a.1, Sum.inl a.2.2.1.2.2) (fun e₃ =>
    OracleComp.pure ((a.1, ()), ((d₁, d₂, d₃), a.2.1.2), ((e₁, e₂, e₃), a.2.2.2)))))))))

/-- **⚑⚑ THE NARROW ROW BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the deleted
`narrowRow_binds_from_polyTime`: a query-bounded forger of the deployed 13-column nested
`state_commit` has NEGLIGIBLE advantage. Outer messages differ (which covers a record-felt-only
disagreement, since the felt sits in the outer absorb) → outer-carrier win, budget `Q + 6`; outer
messages agree → the first differing state block is an inner collision, budget `Q`. NO floor
hypothesis. -/
theorem narrowRow_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmNarrowRomForgery D tagDec).game)
    (hA : RomForgeryEff (narrowRomFamily D tagDec) (effectVmNarrowRomForgery D tagDec) Q A) :
    Negl (gameAdv (effectVmNarrowRomForgery D tagDec).game A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  refine chained_rom_binds (effectVmNarrowRomForgery D tagDec)
    (narrowInnerCarrier D tagDec) (narrowOuterCarrier D tagDec)
    Q (fun l => Q l + 2 + 2 + 2) hQ
    (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ hQ)))
    (narrowRomFamily_card_R D tagDec) A
    (romCarrierAdv _ _ (fun l => OracleComp.mapOut (narrowInnerSelect D tagDec l) (M l)))
    (romCarrierAdv _ _ (narrowOuterComp D tagDec M))
    ?_
    ⟨fun l => OracleComp.mapOut (narrowInnerSelect D tagDec l) (M l),
      fun l => OracleComp.mapOut_queryBounded _ (hM l), fun _ _ => rfl⟩
    ⟨narrowOuterComp D tagDec M,
      fun l => (OracleComp.bindComp_queryBounded (hM l)
        (fun a => QueryBounded.query 5 _ _ (fun _ => QueryBounded.query 4 _ _
          (fun _ => QueryBounded.query 3 _ _ (fun _ => QueryBounded.query 2 _ _
          (fun _ => QueryBounded.query 1 _ _ (fun _ => QueryBounded.query 0 _ _
          (fun _ => QueryBounded.pure 0 _)))))))).mono
        (by show Q l + 6 ≤ Q l + 2 + 2 + 2; omega),
      fun _ _ => rfl⟩
  intro l H hwin
  have hArun : A.run l H = (M l).eval H := hrun l H
  set a := A.run l H with ha
  obtain ⟨hne, heq⟩ := hwin
  have hB₁run : (romCarrierAdv _ _
      (fun l => OracleComp.mapOut (narrowInnerSelect D tagDec l) (M l))).run l H
      = narrowInnerSelect D tagDec l a := by
    show (OracleComp.mapOut (narrowInnerSelect D tagDec l) (M l)).eval H = _
    erw [OracleComp.mapOut_eval, ← hArun]
  have hB₂run : (romCarrierAdv _ _ (narrowOuterComp D tagDec M)).run l H
      = ((a.1, ()),
          ((H (a.1, Sum.inl a.2.1.1.1), H (a.1, Sum.inl a.2.1.1.2.1),
            H (a.1, Sum.inl a.2.1.1.2.2)), a.2.1.2),
          ((H (a.1, Sum.inl a.2.2.1.1), H (a.1, Sum.inl a.2.2.1.2.1),
            H (a.1, Sum.inl a.2.2.1.2.2)), a.2.2.2)) := by
    show (narrowOuterComp D tagDec M l).eval H = _
    unfold narrowOuterComp
    erw [OracleComp.bindComp_eval, ← hArun]
    rfl
  by_cases hT :
      (((H (a.1, Sum.inl a.2.1.1.1), H (a.1, Sum.inl a.2.1.1.2.1),
         H (a.1, Sum.inl a.2.1.1.2.2)), a.2.1.2)
        : (Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l)) × Fin babyBearP)
      = ((H (a.1, Sum.inl a.2.2.1.1), H (a.1, Sum.inl a.2.2.1.2.1),
          H (a.1, Sum.inl a.2.2.1.2.2)), a.2.2.2)
  · -- the outer messages AGREE: all three inner digests collide and the record felts are
    -- equal, so some state block differs — an inner-carrier equivocation.
    refine Or.inl ?_
    rw [hB₁run]
    have h1 : H (a.1, Sum.inl a.2.1.1.1) = H (a.1, Sum.inl a.2.2.1.1) :=
      congrArg (fun p => p.1.1) hT
    have h2 : H (a.1, Sum.inl a.2.1.1.2.1) = H (a.1, Sum.inl a.2.2.1.2.1) :=
      congrArg (fun p => p.1.2.1) hT
    have h3 : H (a.1, Sum.inl a.2.1.1.2.2) = H (a.1, Sum.inl a.2.2.1.2.2) :=
      congrArg (fun p => p.1.2.2) hT
    have hd : a.2.1.2 = a.2.2.2 := congrArg (fun p => p.2) hT
    unfold narrowInnerSelect
    by_cases hA1 : a.2.1.1.1 ≠ a.2.2.1.1
    · rw [if_pos hA1]
      exact ⟨hA1, h1⟩
    · rw [if_neg hA1]
      by_cases hB1 : a.2.1.1.2.1 ≠ a.2.2.1.2.1
      · rw [if_pos hB1]
        exact ⟨hB1, h2⟩
      · rw [if_neg hB1]
        push_neg at hA1 hB1
        have hC1 : a.2.1.1.2.2 ≠ a.2.2.1.2.2 := by
          intro hc
          apply hne
          exact Prod.ext (Prod.ext hA1 (Prod.ext hB1 hc)) hd
        exact ⟨hC1, h3⟩
  · -- the outer messages DIFFER — an outer-carrier equivocation.
    refine Or.inr ?_
    rw [hB₂run]
    exact ⟨hT, heq⟩

/-! ### Non-vacuity teeth at this site. -/

/-- **(TOOTH — the wide ROM class is INHABITED with POSITIVE advantage, and DEFANGED.)** The
`0`-query constant answerer on two distinct payloads is in `RomForgeryEff` at every budget; at the
constant oracle both nested commitments collapse, so it WINS there (positive advantage); and
`wideRow_binds_rom` applies to it — NEGLIGIBLE advantage. The exact `IsPolyTime`-refuting shape,
admitted and defanged. -/
theorem wideRom_constAnswer_defanged (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (t₀ : D.Tag) (v w : WideRomVal) (hvw : v ≠ w) :
    ∃ A, RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomForgery D tagDec) Q A
      ∧ Negl (gameAdv (wideRomBreakGame D tagDec) A)
      ∧ ∀ l, 0 < gameAdv (wideRomBreakGame D tagDec) A l := by
  refine ⟨⟨fun _ _ => (t₀, v, w)⟩,
    ⟨fun _ => OracleComp.pure (t₀, v, w), fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩,
    wideRow_binds_rom D tagDec Q hQ _
      ⟨fun _ => OracleComp.pure (t₀, v, w), fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩,
    fun l => ?_⟩
  letI := ((wideRomFamily D tagDec).toRomFamily).rNe l
  obtain ⟨r₀⟩ := ((wideRomFamily D tagDec).toRomFamily).rNe l
  refine @winProb_pos_of_witness _ ((wideRomBreakGame D tagDec).instFin l) _ (fun _ => r₀) ?_
  refine (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ l _).mpr ⟨hvw, rfl⟩

/-- **(TOOTH — a non-negligible wide forger is OUTSIDE the class.)** The refutation strategy that
killed the `IsPolyTime` floor cannot produce a member of this one. -/
theorem wideRom_nonNegl_forger_excluded (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (wideRomBreakGame D tagDec))
    (hnn : ¬ Negl (gameAdv (wideRomBreakGame D tagDec) A)) :
    ¬ RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomForgery D tagDec) Q A :=
  fun hA => hnn (wideRow_binds_rom D tagDec Q hQ A hA)

end RomSuccessor

/-! ## §6 — the floor, PRICED at both poles, plus the canary and the positive pole.

Re-exported from `SpongeCarrierReduction` §5, where both poles are PROVED, so a reader of any
per-effect site can price its instantiation exactly without leaving the row layer. -/

/-- **⚑ THE ⊤ POLE — the floor is FALSE at the REAL BabyBear parameters** (the honest price of `hEff`).
A sponge whose output is a genuine BabyBear felt has finite range while `List ℤ` is infinite, so a
collision exists at every tag and the floor at the UNRESTRICTED class is FALSE. What the reduction buys
is NOT a floor the deployed sponge satisfies at ⊤ — no such floor exists — it is that the residual is
ONE named class with both poles proved, in place of a disjunction whose right branch is unconditionally
available at deployed parameters. -/
theorem rowCommitFloor_top_false_babyBear (D : SpongeKeyed)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ HashCRHardQuant (spongeFamily D) (fun _ => True) :=
  carrierFloor_top_false_babyBear D hb

/-- **THE ⊥ POLE — vacuous.** Recorded so the floor's satisfiability cannot be mistaken for evidence. -/
theorem rowCommitFloor_bot_vacuous (D : SpongeKeyed) :
    HashCRHardQuant (spongeFamily D) (fun _ => False) :=
  carrierFloor_bot_vacuous D

/-- **(TOOTH — the class §5 instantiates at is NOT EMPTY.)** Together with
`CostAdversary.bruteForce_not_polyTime` (the ⊤-collapse witness is PROVED excluded) this pins the
instantiated floor STRICTLY between the two poles. -/
theorem rowCommitFloor_isPolyTime_inhabited (D : SpongeKeyed) :
    IsPolyTime (spongeAnsSize D)
      (Dregg2.Crypto.CostAdversary.idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  carrierFloor_isPolyTime_inhabited D

/-- **(CANARY — the keystone does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: try to conclude the wide row forger's negligibility from the collision floor applied at some
OTHER finder `B`, not the one EXTRACTED from it. It does not go through — only `wideRow_adv_le` and
`carrier_adv_le` connect the extracted finder to the row game. This tooth REDS if a future edit
reconnects them. -/
example (D : SpongeKeyed) (E : WideRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRowBreakGame D E))
    (B : Adversary (hashGame (spongeFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (spongeFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (wideRowBreakGame D E) A) := hCR B hB)
  trivial

/-- **(CANARY — the narrow keystone likewise.)** -/
example (D : SpongeKeyed) (E : NarrowRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (narrowRowBreakGame D E))
    (B : Adversary (hashGame (spongeFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (spongeFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (narrowRowBreakGame D E) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one: with the floor at the EXTRACTED finder, the wide row binding fires. -/
theorem the_reduced_wideRow_bound_fires (D : SpongeKeyed) (E : WideRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRowBreakGame D E))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier (wideRowToCarrier D E A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRowBreakGame D E) A) :=
  wideRow_binds_advantage_bound D E Eff A hEff hCR

/-! ## §7 — axiom-hygiene tripwires (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms group4Find_len_le
#assert_axioms narrowRowBreakGame_wins_iff
#assert_axioms narrowRow_wins_imp
#assert_axioms narrowRow_adv_le
#assert_axioms narrowRow_binds_advantage_bound
#assert_axioms narrowRow_binds_rom
#assert_axioms wideRowBreakGame_wins_iff
#assert_axioms wideRow_wins_imp
#assert_axioms wideRow_adv_le
#assert_axioms wideRow_binds_advantage_bound
#assert_axioms wideRow_binds_rom
#assert_axioms stateTamper_wins_imp
#assert_axioms rootTamper_wins_imp
#assert_axioms stateTamper_adv_le
#assert_axioms rootTamper_adv_le
#assert_axioms wide_state_tamper_advantage_bound
#assert_axioms wide_root_tamper_advantage_bound
#assert_axioms wide_state_tamper_rom
#assert_axioms wide_root_tamper_rom
#assert_axioms wideRom_constAnswer_defanged
#assert_axioms wideRom_nonNegl_forger_excluded
#assert_axioms rowCommitFloor_top_false_babyBear
#assert_axioms rowCommitFloor_bot_vacuous
#assert_axioms rowCommitFloor_isPolyTime_inhabited
#assert_axioms the_reduced_wideRow_bound_fires

end Dregg2.Circuit.Emit.EffectVmRowCommitReduction
