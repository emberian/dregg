/-
# `Dregg2.Circuit.Emit.EffectVmKeyedStateCommit` — the per-effect state-commit binding, CLOSED on the
keyed, query-counted random-oracle floor (the floor that is PROVED, not the one that is refuted).

## What this is, and what fraud it undoes

A 07-22 swarm DELETED the per-effect commitment keystones (`…_commit_binds_block_or_collides` /
`…_commit_binds_state_or_collides`, 29 theorems across 16 emission files) and pointed their docstrings
at `Dregg2.Circuit.Emit.EffectVmCommitReduction` — a module that was imported by NOTHING, had NO olean,
and was NEVER ELABORATED, whose reductions moreover discharged efficiency at
`Eff := CostAdversary.IsPolyTime`, a floor `sysRoots_floor_polyTime_false_babyBear` PROVES FALSE at
deployed BabyBear parameters. Net effect: the per-effect anti-ghost bindings had NO machine-checked
statement anywhere in the built tree. That module is deleted; the extraction disjunctions are restored
in their files; and THIS module is the honest closure of the collision branch, on the keyed floor
(`Dregg2.Crypto.KeyedRomFloor` / `Dregg2.Crypto.RomBindingReduction`) — the floor whose hardness is a
THEOREM (the birthday bound), with the forger an ORACLE PROGRAM and no false hypothesis anywhere.

## ⚑ THE MODELLING STEP, SAID OUT LOUD (do not read past this)

`keyedRom_hard` requires a λ-GROWING digest space (`|R l| = 2^l`). The deployed sponge digest is a
FIXED 31-bit BabyBear felt; there is no `l` with `|BabyBear| = 2^l`. So this module's game families
are the STANDARD RANDOM-ORACLE IDEALIZATION of the GROUP-4 state-commit surface at an asymptotic
digest width — `vmSpongeFamily` samples `H : Unit × Block l → Fin (2^l)` uniformly, and the deployed
`hash : List ℤ → ℤ` slot of the emitted machinery is filled by `modelHash l H`. This is a MODELLING
step, taken deliberately and labelled — NOT a derivation about deployed Poseidon2. What survives at
the deployed hash without any idealization is the per-effect EXTRACTION disjunction
(`…_or_collides`, restored in each emission file): commit agreement forces absorbed-state agreement
OR hands back the concrete colliding pair. What THIS module adds is the probabilistic closure of that
collision branch — in the model where "collision" is an event over a SAMPLED oracle rather than a
pigeonhole certainty — for every QUERY-BOUNDED forger.

Also honest and explicit: the deployed `boundaryLastPins` step (`PI[NEW_COMMIT]` pins the commit
COLUMN mod `p = 2013265921`) does NOT transport into the λ-wide model — a `[0, p)` canonicality
hypothesis on a `2^l`-wide digest cell is UNSATISFIABLE for `l ≥ 31` on a colliding-with-reality
oracle output, and stating it would smuggle vacuity. So the model game's shared-commit hypothesis is
the commit COLUMN equality (the §7 block shape); the mod-`p` pin from the public input to the column
is deployed-side content and lives in the restored `…Descriptor_commit_binds_state_or_collides`.

## The shape (the honest successor of the deleted `…_from_polyTime` shape)

  * **The forger is an ORACLE PROGRAM** (`BreakComp`): per parameter, a `QueryBounded` tree over the
    tag-separated domain returning TWO ROWS (`VmRowEnv × VmRowEnv`). It learns the sponge only by
    querying it; the oracle is sampled after the tree is fixed.
  * **The win relation is the per-effect break**: both rows satisfy the effect's GROUP-4 hash sites
    (in the model), share the commit column, and DISAGREE on the absorbed 13-column state.
  * **The extractor is a PURE post-map** (`stateColl`): it peels the H4-of-H4 chain by comparing the
    INTER digest COLUMNS of the two rows (which `siteHoldsAll` pins to the genuine digests), so it
    needs NO oracle access of its own — `OracleComp.mapOut` applies and the query budget is
    PRESERVED (`breakFinder_in_romEff`), which is what replaces the `poly_time` answer-size discharge.
  * **The floor is PROVED**: `narrowStateCommit_binds` concludes from `keyedRom_hard` — the birthday
    bound — with no `IsPolyTime`, no `Poseidon2SpongeCR`, no named-carrier hypothesis.
  * **Both poles hold**: the win is SATISFIABLE (`breakWin_satisfiable` — a genuine equivocating row
    pair under a colliding oracle, so the closure is not `Negl` of an empty event), the class is
    inhabited (`probeComp_in_eff`), the extractor FIRES on the witness (`breakWitness_extracts`), and
    the unrestricted-adversary escape dies (`vmSponge_choiceAdv_excluded`,
    `narrowStateCommit_forger_excluded`).

`winsDec` on the break game is `Classical.propDecidable`: the win event's decidability is not
load-bearing (the probability is a finite count and every consumer is `noncomputable` already); no
statement below depends on how the instance decides.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Crypto.RomBindingReduction

namespace Dregg2.Circuit.Emit.EffectVmKeyedStateCommit

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (site0 site1 site2 site3 transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols transferBlockA transferBlockB transferBlockC)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary Hard gameAdv gameAdv_mem_unit choiceAdv)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomQueryFloor (RomFamily romCollisionGame RomComp romAdv RomEff)
open Dregg2.Crypto.KeyedRomFloor
  (KeyedRomFamily keyedRomGame KeyedRomEff keyedRom_hard keyedChoiceAdv_excluded)
open Dregg2.Crypto.RomBindingReduction

set_option autoImplicit false

/-! ## §1 — the idealized keyed family of the GROUP-4 absorb surface (THE MODELLING STEP). -/

/-- The λ-bit digest space of the idealization. (Deployed: a FIXED 31-bit BabyBear felt — see the
header; this family is the labelled random-oracle idealization, not the deployed hash.) -/
abbrev Digest (l : ℕ) : Type := Fin (2 ^ l)

instance (l : ℕ) : Nonempty (Digest l) := ⟨⟨0, Nat.two_pow_pos l⟩⟩

/-- An arity-4 absorb block over λ-bit words, plus the junk point (`none`) that every out-of-shape
absorb list maps to. The GROUP-4 surface only ever absorbs arity-4 blocks (`site0`–`site3`), so the
junk point is where `modelHash` sends lists the surface never produces. -/
abbrev Block (l : ℕ) : Type := Option (Fin 4 → Digest l)

/-- **THE IDEALIZED KEYED FAMILY of the GROUP-4 state-commit surface.** The tag space is trivial
(`Unit`): the deployed surface runs ONE untagged H4 sponge at all four sites, so no domain-separation
claim is made or smuggled. The domain is the arity-4 block (plus junk); the range is the λ-bit digest,
which is what `keyedRom_hard` requires (`|R l| = 2^l`). -/
def vmSpongeFamily : KeyedRomFamily where
  Key := fun _ => Unit
  D := Block
  R := Digest
  keyFin := fun _ => inferInstance
  keyDec := fun _ => inferInstance
  keyNe := fun _ => inferInstance
  dFin := fun _ => inferInstance
  dDec := fun _ => inferInstance
  dNe := fun _ => inferInstance
  rFin := fun _ => inferInstance
  rDec := fun _ => inferInstance
  rNe := fun _ => inferInstance

/-- The digest space has the λ-growing cardinality the keyed floor requires. -/
theorem vmSponge_hw :
    ∀ l, letI := vmSpongeFamily.rFin l; Fintype.card (vmSpongeFamily.R l) = 2 ^ l := by
  intro l
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  exact Fintype.card_fin _

/-- **The family COMPRESSES at every parameter** — strictly more tagged blocks than digests
(`2^{4l} + 1 > 2^l`), so the pigeonhole canaries (`choiceAdv` exclusion) have their hypothesis. -/
theorem vmSponge_compressing :
    ∀ l, letI := (vmSpongeFamily.toRomFamily).dFin l; letI := (vmSpongeFamily.toRomFamily).rFin l;
      Fintype.card (vmSpongeFamily.toRomFamily.R l)
        < Fintype.card (vmSpongeFamily.toRomFamily.D l) := by
  intro l
  show Fintype.card (Fin (2 ^ l)) < Fintype.card (Unit × Option (Fin 4 → Fin (2 ^ l)))
  rw [Fintype.card_prod, Fintype.card_unit, Fintype.card_option, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]
  have h1 : 2 ^ l ≤ (2 ^ l) ^ 4 := Nat.le_self_pow (by norm_num) _
  omega

/-! ## §2 — shaping and packing: the finite truncation of the absorb lists. -/

/-- An absorb list the model represents faithfully: arity 4, every entry a canonical λ-bit word.
(The deployed canonicality envelope `[0, p)` lands inside `[0, 2^l)` for every `l ≥ 31`.) -/
def Shaped (l : ℕ) (xs : List ℤ) : Prop :=
  xs.length = 4 ∧ ∀ x ∈ xs, 0 ≤ x ∧ x < ((2 ^ l : ℕ) : ℤ)

instance (l : ℕ) (xs : List ℤ) : Decidable (Shaped l xs) := by
  unfold Shaped; infer_instance

/-- `getD` at an in-bounds index is the indexed element. -/
theorem getD_eq_of_lt {xs : List ℤ} {i : Nat} (h : i < xs.length) : xs.getD i 0 = xs[i] := by
  simp [List.getD, List.getElem?_eq_getElem h]

/-- Pack an absorb list into the model domain: in-shape lists pack injectively to `some`; everything
else is the junk point. -/
def packBlock (l : ℕ) (xs : List ℤ) : Block l :=
  if h : Shaped l xs then
    some (fun i => ⟨(xs.getD (i : ℕ) 0).toNat, by
      obtain ⟨hlen, hmem⟩ := h
      have hi : (i : ℕ) < xs.length := by rw [hlen]; exact i.isLt
      have hin : xs.getD (i : ℕ) 0 ∈ xs := by
        rw [getD_eq_of_lt hi]
        exact List.getElem_mem hi
      have hb := hmem _ hin
      omega⟩)
  else none

/-- **Packing is injective on in-shape lists** — the layout fact the extraction rests on: two
DIFFERENT in-shape absorb lists occupy two DIFFERENT points of the model domain. -/
theorem packBlock_inj {l : ℕ} {xs ys : List ℤ} (hx : Shaped l xs) (hy : Shaped l ys)
    (h : packBlock l xs = packBlock l ys) : xs = ys := by
  unfold packBlock at h
  rw [dif_pos hx, dif_pos hy] at h
  have hf := Option.some.inj h
  have hlen : xs.length = ys.length := by rw [hx.1, hy.1]
  refine List.ext_getElem hlen (fun i h1 h2 => ?_)
  have hi4 : i < 4 := hx.1 ▸ h1
  have hfi := congrFun hf ⟨i, hi4⟩
  simp only [Fin.mk.injEq] at hfi
  have hgx : xs.getD i 0 = xs[i] := getD_eq_of_lt h1
  have hgy : ys.getD i 0 = ys[i] := getD_eq_of_lt h2
  rw [hgx, hgy] at hfi
  have hbx := hx.2 _ (List.getElem_mem h1)
  have hby := hy.2 _ (List.getElem_mem h2)
  omega

/-- **THE MODEL HASH** — the sampled oracle in the deployed `hash : List ℤ → ℤ` slot. All the emitted
machinery (`siteHoldsAll`, `satisfiedVm`, the extraction lemmas) is abstract in `hash`, so it applies
to `modelHash l H` verbatim; that is what lets the model game reuse the deployed definitions instead
of a re-authored mirror. -/
def modelHash (l : ℕ) (H : (Unit × Block l) → Digest l) : List ℤ → ℤ :=
  fun xs => ((H ((), packBlock l xs)).val : ℤ)

theorem modelHash_nonneg (l : ℕ) (H : (Unit × Block l) → Digest l) (xs : List ℤ) :
    0 ≤ modelHash l H xs :=
  Int.natCast_nonneg _

theorem modelHash_lt (l : ℕ) (H : (Unit × Block l) → Digest l) (xs : List ℤ) :
    modelHash l H xs < ((2 ^ l : ℕ) : ℤ) := by
  unfold modelHash
  exact_mod_cast (H ((), packBlock l xs)).isLt

/-- Equal model digests at two lists ARE an equal-oracle-output fact at the packed points. -/
theorem modelHash_agree {l : ℕ} {H : (Unit × Block l) → Digest l} {xs ys : List ℤ}
    (h : modelHash l H xs = modelHash l H ys) :
    H ((), packBlock l xs) = H ((), packBlock l ys) := by
  unfold modelHash at h
  exact Fin.val_injective (by exact_mod_cast h)

/-! ## §3 — the GROUP-4 site equations, read off the columns. -/

/-- The outer (site-3) absorb list, read off the columns: the three INTER digests and the record
digest. Under `siteHoldsAll` these columns carry the genuine digests, which is what makes the
chain-peeling extractor PURE in the two rows (no oracle access needed). -/
def outerCols (env : VmRowEnv) : List ℤ :=
  [ env.loc (auxCol aux_off.STATE_INTER1), env.loc (auxCol aux_off.STATE_INTER2)
  , env.loc (auxCol aux_off.STATE_INTER3), env.loc (auxCol aux_off.STATE_RECORD_DIGEST) ]

/-- The four GROUP-4 site equations, unfolded from the ordered site walk (the shape
`transferHash_binds` walks, kept here with the INTER columns explicit). -/
theorem siteHolds_unfold (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env transferHashSites) :
    env.loc (auxCol aux_off.STATE_INTER1) = hash (transferBlockA env)
    ∧ env.loc (auxCol aux_off.STATE_INTER2) = hash (transferBlockB env)
    ∧ env.loc (auxCol aux_off.STATE_INTER3) = hash (transferBlockC env)
    ∧ env.loc (saCol state.STATE_COMMIT) = hash (outerCols env) := by
  unfold siteHoldsAll transferHashSites at h
  simp only [siteHoldsAll.go, site0, site1, site2, site3, VmHashSite.resolvedInputs,
    HashInput.resolve, List.map_cons, List.map_nil, List.getD, List.nil_append,
    List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at h
  obtain ⟨h0, h1, h2, h3, _⟩ := h
  refine ⟨h0, h1, h2, ?_⟩
  have houter : outerCols env
      = [ hash (transferBlockA env), hash (transferBlockB env), hash (transferBlockC env)
        , env.loc (auxCol aux_off.STATE_RECORD_DIGEST) ] := by
    unfold outerCols
    rw [h0, h1, h2]
    rfl
  rw [houter]
  exact h3

/-- Equal outer lists mean equal INTER digest columns and equal record digests, entrywise. -/
theorem outerCols_inj_parts {e₁ e₂ : VmRowEnv} (h : outerCols e₁ = outerCols e₂) :
    e₁.loc (auxCol aux_off.STATE_INTER1) = e₂.loc (auxCol aux_off.STATE_INTER1)
    ∧ e₁.loc (auxCol aux_off.STATE_INTER2) = e₂.loc (auxCol aux_off.STATE_INTER2)
    ∧ e₁.loc (auxCol aux_off.STATE_INTER3) = e₂.loc (auxCol aux_off.STATE_INTER3)
    ∧ e₁.loc (auxCol aux_off.STATE_RECORD_DIGEST) = e₂.loc (auxCol aux_off.STATE_RECORD_DIGEST) := by
  simp only [outerCols, List.cons.injEq, and_true] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- The 13 absorbed columns are exactly the three blocks plus the record digest — the concatenation
the peel cases split along. -/
theorem absorbedCols_eq_blocks (env : VmRowEnv) :
    absorbedCols env
      = transferBlockA env ++ transferBlockB env ++ transferBlockC env
        ++ [env.loc (auxCol aux_off.STATE_RECORD_DIGEST)] := rfl

/-- The in-shape envelope of a row's absorbed surface at width `l`: the three blocks are in-shape and
the record digest is a canonical λ-bit word. (The INTER digest columns need no hypothesis — under the
model sites they carry oracle outputs, in-range by construction.) -/
def AbsorbedShaped (l : ℕ) (env : VmRowEnv) : Prop :=
  Shaped l (transferBlockA env) ∧ Shaped l (transferBlockB env) ∧ Shaped l (transferBlockC env)
  ∧ (0 ≤ env.loc (auxCol aux_off.STATE_RECORD_DIGEST)
     ∧ env.loc (auxCol aux_off.STATE_RECORD_DIGEST) < ((2 ^ l : ℕ) : ℤ))

/-- Under the model sites, the outer absorb list is in-shape: the INTER columns are oracle outputs
(in-range by construction), the record digest by hypothesis. -/
theorem outerCols_shaped (l : ℕ) (H : (Unit × Block l) → Digest l) (env : VmRowEnv)
    (hs : siteHoldsAll (modelHash l H) env transferHashSites)
    (hrd : 0 ≤ env.loc (auxCol aux_off.STATE_RECORD_DIGEST)
           ∧ env.loc (auxCol aux_off.STATE_RECORD_DIGEST) < ((2 ^ l : ℕ) : ℤ)) :
    Shaped l (outerCols env) := by
  obtain ⟨h0, h1, h2, _⟩ := siteHolds_unfold _ env hs
  refine ⟨rfl, fun x hx => ?_⟩
  simp only [outerCols, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [h0]; exact ⟨modelHash_nonneg _ _ _, modelHash_lt _ _ _⟩
  · rw [h1]; exact ⟨modelHash_nonneg _ _ _, modelHash_lt _ _ _⟩
  · rw [h2]; exact ⟨modelHash_nonneg _ _ _, modelHash_lt _ _ _⟩
  · exact hrd

/-! ## §4 — THE EXTRACTOR: a pure chain peel over the two rows. -/

/-- **THE COLLISION EXTRACTOR — PURE in the two rows.** Peels the H4-of-H4 chain by comparing lists
of COLUMNS: if the outer absorb lists differ (while the commits agree) the outer site collides; else
the INTER digests agree, and the first differing inner block collides at its site. Because it reads
only columns, it is a `mapOut` post-map — no oracle queries of its own. -/
def stateColl (l : ℕ) (e₁ e₂ : VmRowEnv) : (Unit × Block l) × (Unit × Block l) :=
  if outerCols e₁ ≠ outerCols e₂ then
    (((), packBlock l (outerCols e₁)), ((), packBlock l (outerCols e₂)))
  else if transferBlockA e₁ ≠ transferBlockA e₂ then
    (((), packBlock l (transferBlockA e₁)), ((), packBlock l (transferBlockA e₂)))
  else if transferBlockB e₁ ≠ transferBlockB e₂ then
    (((), packBlock l (transferBlockB e₁)), ((), packBlock l (transferBlockB e₂)))
  else
    (((), packBlock l (transferBlockC e₁)), ((), packBlock l (transferBlockC e₂)))

/-- **⚑ WIN-PRESERVATION (the peel is correct).** Two rows satisfying the model GROUP-4 sites,
in-shape, agreeing on the commit COLUMN but disagreeing on the absorbed 13-column state, hand the
extractor a GENUINE collision of the sampled oracle. -/
theorem stateColl_wins (l : ℕ) (H : (keyedRomGame vmSpongeFamily).Inst l) (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll (modelHash l H) e₁ transferHashSites)
    (hs₂ : siteHoldsAll (modelHash l H) e₂ transferHashSites)
    (ha₁ : AbsorbedShaped l e₁) (ha₂ : AbsorbedShaped l e₂)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (keyedRomGame vmSpongeFamily).wins l H (stateColl l e₁ e₂) := by
  obtain ⟨h10, h11, h12, h13⟩ := siteHolds_unfold _ e₁ hs₁
  obtain ⟨h20, h21, h22, h23⟩ := siteHolds_unfold _ e₂ hs₂
  unfold stateColl
  split_ifs with hOuter hA hB
  · -- outer lists differ: the outer site collides (commit columns agree).
    have hsh₁ := outerCols_shaped l H e₁ hs₁ ha₁.2.2.2
    have hsh₂ := outerCols_shaped l H e₂ hs₂ ha₂.2.2.2
    refine ⟨fun hp => hOuter ?_, ?_⟩
    · exact packBlock_inj hsh₁ hsh₂ (congrArg Prod.snd hp)
    · have hmh : modelHash l H (outerCols e₁) = modelHash l H (outerCols e₂) := by
        rw [← h13, ← h23]; exact hcommit
      exact modelHash_agree hmh
  · -- block A differs at equal INTER1 digests: site 0 collides.
    rw [not_not] at hOuter
    have hOuter' := outerCols_inj_parts hOuter
    refine ⟨fun hp => hA ?_, ?_⟩
    · exact packBlock_inj ha₁.1 ha₂.1 (congrArg Prod.snd hp)
    · have hmh : modelHash l H (transferBlockA e₁) = modelHash l H (transferBlockA e₂) := by
        rw [← h10, ← h20]; exact hOuter'.1
      exact modelHash_agree hmh
  · -- block B differs at equal INTER2 digests: site 1 collides.
    rw [not_not] at hOuter
    have hOuter' := outerCols_inj_parts hOuter
    refine ⟨fun hp => hB ?_, ?_⟩
    · exact packBlock_inj ha₁.2.1 ha₂.2.1 (congrArg Prod.snd hp)
    · have hmh : modelHash l H (transferBlockB e₁) = modelHash l H (transferBlockB e₂) := by
        rw [← h11, ← h21]; exact hOuter'.2.1
      exact modelHash_agree hmh
  · -- blocks A, B and the outer list agree, so block C MUST differ: site 2 collides.
    rw [not_not] at hOuter hA hB
    have hOuter' := outerCols_inj_parts hOuter
    have hC : transferBlockC e₁ ≠ transferBlockC e₂ := by
      intro hCeq
      apply hne
      rw [absorbedCols_eq_blocks, absorbedCols_eq_blocks, hA, hB, hCeq, hOuter'.2.2.2]
    refine ⟨fun hp => hC ?_, ?_⟩
    · exact packBlock_inj ha₁.2.2.1 ha₂.2.2.1 (congrArg Prod.snd hp)
    · have hmh : modelHash l H (transferBlockC e₁) = modelHash l H (transferBlockC e₂) := by
        rw [← h12, ← h22]; exact hOuter'.2.2.1
      exact modelHash_agree hmh

/-! ## §5 — the per-effect break game and the query-bounded forger class. -/

/-- **THE PER-EFFECT STATE-COMMIT BREAK GAME.** Parameterized by the EFFECT'S hash-site list (every
narrow effect names its own — `cellDestroyHashSites`, `exerciseHashSites`, … — all definitionally the
GROUP-4 `transferHashSites`). The instance is the sampled oracle; the adversary outputs TWO ROWS and
wins iff both satisfy the effect's sites in the model, are in-shape, share the commit column, and
DISAGREE on the absorbed 13-column state — the ghost-state equivocation the deleted keystones were
about. `winsDec` is classical (see header). -/
noncomputable def narrowBreakGame (sites : List VmHashSite) : Game where
  Inst := fun l => (keyedRomGame vmSpongeFamily).Inst l
  Ans := fun _ => VmRowEnv × VmRowEnv
  instFin := (keyedRomGame vmSpongeFamily).instFin
  instNe := (keyedRomGame vmSpongeFamily).instNe
  wins := fun l H p =>
    siteHoldsAll (modelHash l H) p.1 sites ∧ siteHoldsAll (modelHash l H) p.2 sites
    ∧ AbsorbedShaped l p.1 ∧ AbsorbedShaped l p.2
    ∧ p.1.loc (saCol state.STATE_COMMIT) = p.2.loc (saCol state.STATE_COMMIT)
    ∧ absorbedCols p.1 ≠ absorbedCols p.2
  winsDec := fun _ _ _ => Classical.propDecidable _

/-- A row-pair forger, as an oracle program: one query tree per parameter over the tag-separated
domain, returning two rows. -/
abbrev BreakComp : Type :=
  ∀ l, OracleComp (Unit × Block l) (Digest l) (VmRowEnv × VmRowEnv)

/-- The ordinary adversary a break query tree induces. -/
def breakAdv (sites : List VmHashSite) (M : BreakComp) : Adversary (narrowBreakGame sites) where
  run := fun l H => (M l).eval H

/-- **THE QUERY-BOUNDED FORGER CLASS** — the fixed `Eff` at the per-effect layer: the forger factors
through a `Q`-query tree. The honest successor of the `IsPolyTime` discharge. -/
def NarrowBreakEff (sites : List VmHashSite) (Q : ℕ → ℕ) :
    Adversary (narrowBreakGame sites) → Prop := fun A =>
  ∃ M : BreakComp, (∀ l, QueryBounded (Q l) (M l)) ∧
    ∀ l (H : (narrowBreakGame sites).Inst l), A.run l H = (M l).eval H

/-! ## §6 — the reduction. -/

/-- The extracted collision finder: run the forger, peel its two rows. -/
def breakFinder (sites : List VmHashSite) (A : Adversary (narrowBreakGame sites)) :
    Adversary (keyedRomGame vmSpongeFamily) where
  run := fun l H => stateColl l (A.run l H).1 (A.run l H).2

/-- Every oracle the forger beats, the extracted finder beats at the collision game. -/
theorem break_wins_imp (sites : List VmHashSite) (hsites : sites = transferHashSites)
    (A : Adversary (narrowBreakGame sites)) (l : ℕ) (H : (narrowBreakGame sites).Inst l)
    (hwin : (narrowBreakGame sites).wins l H (A.run l H)) :
    (keyedRomGame vmSpongeFamily).wins l H ((breakFinder sites A).run l H) := by
  subst hsites
  obtain ⟨hs₁, hs₂, ha₁, ha₂, hc, hne⟩ := hwin
  exact stateColl_wins l H _ _ hs₁ hs₂ ha₁ ha₂ hc hne

/-- **THE ADVANTAGE INEQUALITY** — unconditional, over ALL adversaries; the class enters only when
the floor is applied. -/
theorem break_adv_le (sites : List VmHashSite) (hsites : sites = transferHashSites)
    (A : Adversary (narrowBreakGame sites)) (l : ℕ) :
    gameAdv (narrowBreakGame sites) A l
      ≤ gameAdv (keyedRomGame vmSpongeFamily) (breakFinder sites A) l := by
  refine @winProb_le_of_imp _ ((narrowBreakGame sites).instFin l) _ _ (fun H hH => ?_)
  replace hH := (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mp hH
  refine (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mpr ?_
  exact break_wins_imp sites hsites A l H hH

/-- **THE EFFICIENCY DISCHARGE, PRESERVING THE QUERY BOUND**: the peel is a `mapOut` post-map, so a
`Q`-query forger yields a `Q`-query collision finder. -/
theorem breakFinder_in_romEff (sites : List VmHashSite) (Q : ℕ → ℕ)
    (A : Adversary (narrowBreakGame sites)) (hA : NarrowBreakEff sites Q A) :
    RomEff vmSpongeFamily.toRomFamily Q (breakFinder sites A) := by
  obtain ⟨M, hMQ, hrun⟩ := hA
  refine ⟨fun l => OracleComp.mapOut (fun p => stateColl l p.1 p.2) (M l),
    fun l => OracleComp.mapOut_queryBounded _ (hMQ l), ?_⟩
  intro l H
  show stateColl l (A.run l H).1 (A.run l H).2 = _
  erw [OracleComp.mapOut_eval, hrun l H]
  rfl

/-- **⚑⚑ THE KEYSTONE — the per-effect state-commit binding, CLOSED on the PROVED floor.** In the
random-oracle idealization of the GROUP-4 surface (the labelled modelling step, see header), every
query-bounded row-pair forger against an effect's absorb surface equivocates the commit column with
NEGLIGIBLE probability. From `keyedRom_hard` (the birthday bound) — no `IsPolyTime`, no
`Poseidon2SpongeCR`, no named-carrier hypothesis, and the counterexample class is excluded below. -/
theorem narrowStateCommit_binds (sites : List VmHashSite) (hsites : sites = transferHashSites)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (narrowBreakGame sites)) (hA : NarrowBreakEff sites Q A) :
    Negl (gameAdv (narrowBreakGame sites) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (narrowBreakGame sites) A l).1)
    (break_adv_le sites hsites A)
    (keyedRom_hard vmSpongeFamily Q hQ vmSponge_hw (breakFinder sites A)
      (breakFinder_in_romEff sites Q A hA))

/-! ## §7 — ⚑ the counterexample dies. -/

/-- **A NON-NEGLIGIBLE FORGER IS OUTSIDE THE CLASS** — the `shortCollAdv` shape (a `Classical.choice`
answerer winning with probability 1, which REFUTES the `IsPolyTime` floor) cannot be a member of the
query-bounded class at this layer. -/
theorem narrowStateCommit_forger_excluded (sites : List VmHashSite)
    (hsites : sites = transferHashSites)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (narrowBreakGame sites))
    (hnn : ¬ Negl (gameAdv (narrowBreakGame sites) A)) :
    ¬ NarrowBreakEff sites Q A :=
  fun hA => hnn (narrowStateCommit_binds sites hsites Q hQ A hA)

/-- **The full-oracle `Classical.choice` collision answerer is excluded from the keyed class** at this
family (the compression canary firing on `vmSpongeFamily`). -/
theorem vmSponge_choiceAdv_excluded (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    ¬ KeyedRomEff vmSpongeFamily Q
        (choiceAdv (keyedRomGame vmSpongeFamily) (fun _ => ⟨(((), none), ((), none))⟩)) :=
  keyedChoiceAdv_excluded vmSpongeFamily Q hQ vmSponge_hw vmSponge_compressing _

/-! ## §8 — NON-VACUITY: the win is satisfiable, the class is inhabited, the peel fires. -/

/-- The all-zero row: every column, next-cell and public input `0`. -/
def zeroRowEnv : VmRowEnv where
  loc := fun _ => 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- The tampered row: the all-zero row with the post-`bal_lo` cell minted to `1` — a ghost-state
equivocation candidate (all digest columns untouched). -/
def mintedRowEnv : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 1 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- The constant-zero oracle — an instance at which the two rows genuinely equivocate. -/
def zeroOracle (l : ℕ) : (narrowBreakGame transferHashSites).Inst l := fun _ => ⟨0, Nat.two_pow_pos l⟩

/-- No aux column is the minted `bal_lo` cell (`auxCol i = 90 + i` vs `saCol BALANCE_LO = 76`). -/
theorem auxCol_ne_minted (i : Nat) : auxCol i ≠ saCol state.BALANCE_LO := by
  simp only [auxCol, saCol, AUX_BASE, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE,
    NUM_EFFECTS, NUM_PARAMS, STATE_SIZE, state.BALANCE_LO]
  omega

/-- A non-`BALANCE_LO` after-state cell is not the minted cell. -/
theorem saCol_ne_minted {off : Nat} (hoff : off ≠ state.BALANCE_LO) :
    saCol off ≠ saCol state.BALANCE_LO := by
  simp only [saCol, state.BALANCE_LO] at *
  omega

/-- The minted row is the zero row away from the minted cell. -/
theorem mintedRowEnv_loc_ne {v : Nat} (hv : v ≠ saCol state.BALANCE_LO) :
    mintedRowEnv.loc v = 0 := by
  show (if v = saCol state.BALANCE_LO then (1 : ℤ) else 0) = 0
  exact if_neg hv

theorem mintedRowEnv_loc_minted : mintedRowEnv.loc (saCol state.BALANCE_LO) = 1 := by
  show (if saCol state.BALANCE_LO = saCol state.BALANCE_LO then (1 : ℤ) else 0) = 1
  exact if_pos rfl

/-- **THE WIN IS SATISFIABLE** (`l ≥ 1`): under the constant-zero oracle the zero row and the minted
row BOTH satisfy the GROUP-4 sites, are in-shape, share the commit column, and disagree on the
absorbed state. So `narrowStateCommit_binds` bounds a NON-EMPTY event — `Negl` of something real, not
of an unsatisfiable conjunction. -/
theorem breakWin_satisfiable (l : ℕ) (hl : 1 ≤ l) :
    (narrowBreakGame transferHashSites).wins l (zeroOracle l) (zeroRowEnv, mintedRowEnv) := by
  have hzero : ∀ xs, modelHash l (zeroOracle l) xs = 0 := fun _ => rfl
  have hpos : (0 : ℤ) < ((2 ^ l : ℕ) : ℤ) := by
    have := Nat.two_pow_pos l
    omega
  have hone : (1 : ℤ) < ((2 ^ l : ℕ) : ℤ) := by
    have h2 : 2 ^ 1 ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
    have h2' : (2 : ℕ) ≤ 2 ^ l := by simpa using h2
    omega
  have hsz : Shaped l [(0 : ℤ), 0, 0, 0] := by
    refine ⟨rfl, fun x hx => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst hx
    exact ⟨le_refl 0, hpos⟩
  have hsm : Shaped l [(1 : ℤ), 0, 0, 0] := by
    refine ⟨rfl, fun x hx => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨by norm_num, hone⟩
    all_goals exact ⟨le_refl 0, hpos⟩
  have hzA : transferBlockA zeroRowEnv = [0, 0, 0, 0] := rfl
  have hzB : transferBlockB zeroRowEnv = [0, 0, 0, 0] := rfl
  have hzC : transferBlockC zeroRowEnv = [0, 0, 0, 0] := rfl
  have hmA : transferBlockA mintedRowEnv = [1, 0, 0, 0] := by
    show [mintedRowEnv.loc (saCol state.BALANCE_LO), mintedRowEnv.loc (saCol state.BALANCE_HI),
          mintedRowEnv.loc (saCol state.NONCE), mintedRowEnv.loc (saCol (state.FIELD_BASE + 0))]
        = [1, 0, 0, 0]
    rw [mintedRowEnv_loc_minted,
      mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.BALANCE_HI, state.BALANCE_LO])),
      mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.NONCE, state.BALANCE_LO])),
      mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.FIELD_BASE, state.BALANCE_LO]))]
  have hmB : transferBlockB mintedRowEnv = [0, 0, 0, 0] := by
    show [mintedRowEnv.loc (saCol (state.FIELD_BASE + 1)), mintedRowEnv.loc (saCol (state.FIELD_BASE + 2)),
          mintedRowEnv.loc (saCol (state.FIELD_BASE + 3)), mintedRowEnv.loc (saCol (state.FIELD_BASE + 4))]
        = [0, 0, 0, 0]
    rw [mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.FIELD_BASE, state.BALANCE_LO])),
      mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.FIELD_BASE, state.BALANCE_LO])),
      mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.FIELD_BASE, state.BALANCE_LO])),
      mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.FIELD_BASE, state.BALANCE_LO]))]
  have hmC : transferBlockC mintedRowEnv = [0, 0, 0, 0] := by
    show [mintedRowEnv.loc (saCol (state.FIELD_BASE + 5)), mintedRowEnv.loc (saCol (state.FIELD_BASE + 6)),
          mintedRowEnv.loc (saCol (state.FIELD_BASE + 7)), mintedRowEnv.loc (saCol state.CAP_ROOT)]
        = [0, 0, 0, 0]
    rw [mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.FIELD_BASE, state.BALANCE_LO])),
      mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.FIELD_BASE, state.BALANCE_LO])),
      mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.FIELD_BASE, state.BALANCE_LO])),
      mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.CAP_ROOT, state.BALANCE_LO]))]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the zero row satisfies the sites under the constant-zero oracle.
    unfold siteHoldsAll transferHashSites
    simp only [siteHoldsAll.go, site0, site1, site2, site3, VmHashSite.resolvedInputs,
      HashInput.resolve, List.map_cons, List.map_nil, List.getD, hzero]
    exact ⟨rfl, rfl, rfl, rfl, trivial⟩
  · -- the minted row satisfies the sites: no digest column is the minted cell.
    unfold siteHoldsAll transferHashSites
    simp only [siteHoldsAll.go, site0, site1, site2, site3, VmHashSite.resolvedInputs,
      HashInput.resolve, List.map_cons, List.map_nil, List.getD, hzero]
    exact ⟨mintedRowEnv_loc_ne (auxCol_ne_minted _), mintedRowEnv_loc_ne (auxCol_ne_minted _),
      mintedRowEnv_loc_ne (auxCol_ne_minted _),
      mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.STATE_COMMIT, state.BALANCE_LO])),
      trivial⟩
  · exact ⟨hzA ▸ hsz, hzB ▸ hsz, hzC ▸ hsz, le_refl 0, hpos⟩
  · exact ⟨hmA ▸ hsm, hmB ▸ hsz, hmC ▸ hsz,
      (mintedRowEnv_loc_ne (auxCol_ne_minted _)).ge,
      by rw [mintedRowEnv_loc_ne (auxCol_ne_minted _)]; exact hpos⟩
  · -- shared commit column: both `0`.
    rw [mintedRowEnv_loc_ne (saCol_ne_minted (by norm_num [state.STATE_COMMIT, state.BALANCE_LO]))]
    rfl
  · -- the absorbed states differ at the minted cell.
    intro h
    rw [absorbedCols_eq_blocks, absorbedCols_eq_blocks, hzA, hmA] at h
    simp only [List.cons_append, List.cons.injEq] at h
    exact absurd h.1 (by norm_num)

/-- **THE PEEL FIRES on the witness**: the extractor hands back a genuine collision of the sampled
oracle at the equivocating pair — the reduction is witnessed end-to-end, not just type-correct. -/
theorem breakWitness_extracts (l : ℕ) (hl : 1 ≤ l) :
    (keyedRomGame vmSpongeFamily).wins l (zeroOracle l) (stateColl l zeroRowEnv mintedRowEnv) := by
  obtain ⟨hs₁, hs₂, ha₁, ha₂, hc, hne⟩ := breakWin_satisfiable l hl
  exact stateColl_wins l (zeroOracle l) _ _ hs₁ hs₂ ha₁ ha₂ hc hne

/-- A one-query member of the forger class — the class is INHABITED (and by something that genuinely
touches its oracle, unlike the 0-query `fixedPairComp` shape the vacuity bar forbids as a witness). -/
def probeComp : BreakComp :=
  fun _ => .query ((), none) (fun _ => .pure (zeroRowEnv, mintedRowEnv))

theorem probeComp_in_eff (sites : List VmHashSite) (Q : ℕ → ℕ) (hQ : ∀ l, 1 ≤ Q l) :
    NarrowBreakEff sites Q (breakAdv sites probeComp) := by
  refine ⟨probeComp, fun l => ?_, fun _ _ => rfl⟩
  exact (Dregg2.Crypto.RomOracle.QueryBounded.query 0 _ _
    (fun _ => Dregg2.Crypto.RomOracle.QueryBounded.pure 0 _)).mono (hQ l)

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  vmSponge_hw,
  vmSponge_compressing,
  packBlock_inj,
  siteHolds_unfold,
  outerCols_shaped,
  stateColl_wins,
  break_wins_imp,
  break_adv_le,
  breakFinder_in_romEff,
  narrowStateCommit_binds,
  narrowStateCommit_forger_excluded,
  vmSponge_choiceAdv_excluded,
  breakWin_satisfiable,
  breakWitness_extracts,
  probeComp_in_eff
]

end Dregg2.Circuit.Emit.EffectVmKeyedStateCommit
