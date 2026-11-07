/-
# `Dregg2.Circuit.CorrelatedAgreement.DecimLiftDischarge` — ⚑ THE `DecimLift` HYPOTHESIS
DISCHARGED at the landed setup tower: the §5 interface theorem's decimation-lift weld is now a
THEOREM at the deployed 5-layer arity-8 schedule, and `ud_tower_far_survival` holds there with
one fewer hypothesis.

**What was carried (verbatim from `Interface.lean:653-658`).** `DecimLift` was named as "the
RS fold-geometry weld … TRUE for the deployed phase decomposition; its deployed-instance proof
is the setup-TOWER engineering `FriChainStepIdx`'s header names as missing (no welded
`FriSetupK` tower in-tree). Named, not faked." That justification is now STALE: the tower
LANDED (`FriSetupTower.towerS`, five welded arity-8 layers `2^19 → … → 2^4`, `tower_link`,
committed green). This file cashes the IOU.

**Why the tower discharges it (the exact comparison).** `DecimLift nn V m dec` demands: at
every layer `i`, if the `m` decimations `dec i w` agree SIMULTANEOUSLY with codewords
`g j ∈ V (i+1)` on all but `e` points of the folded domain, then `w` is `(m·e)`-close to
`V i`. At `dec := Cj` (the `FriFoldArity` components — the decimation whose moment-curve IS
the deployed fold: `towerFold_is_Fold` below is `rfl`) the three ingredients are exactly what
the tower landed:
  * `self_decomp` (`FriFoldArity:115`): `w x = Σ_j p(x)^j · Cⱼw(q x)` — off the disagreement
    fibers, `w` IS the reassembly of the `g j`;
  * `unfold_closed` (proved at every layer by `towerLayer`): `reassemble G g ∈ C` — the
    reassembled word is a LAYER-`i` codeword, the closeness witness;
  * `tower_link`: `(towerS i).C' = (towerS (i+1)).C` — so "`g j` in the NEXT layer's domain
    code" (the shape `DecimLift` states) IS "`g j` in THIS layer's folded code" (the shape
    `unfold_closed` consumes);
  * `pullback_card_le` (`FriFoldArity:161`): each bad fiber has `m` points — the `m·e`.
The generic engine is `setup_decimLift` (any `FriSetupK`); `decimLift_of_tower` instantiates
it down the welded family. Above the tower (layers ≥ 5) the instance `towerV` is `∅`, which
makes those layers' lift VACUOUS by construction — stated loudly: `DecimLift`'s STATEMENT is
untouched (no weakening); the finite-depth tower simply has nothing above layer 5, a
5-round chain never folds there, and `towerFar`/`towerE` never read `V` above layer 5.

**What lands.**
  1. `curveUDParam_exact` — the `r = 0` m-term UD correlated agreement over ANY linear code
     (the exact m-point Vandermonde solve), generalizing `Interface.curveUDParam_pair_exact`
     from `m = 2` to every `m`. This is the CA corner that lets the fire discharge `hCA`
     honestly at the `d = 0` radius schedule; the positive-radius CA remains the L1–L6 target.
  2. `setup_decimLift` — the generic lift over any `FriSetupK` (the BBHR18 reassembly weld).
  3. `decimLift_of_tower` — **`DecimLift twSz towerV 8 towerDec`, PROVEN** (the discharge).
  4. `ud_tower_far_survival_discharged` — the §5 interface theorem AT the tower instance with
     the `DecimLift` hypothesis REMOVED (`hlift` is now supplied by theorem 3). Remaining
     hypotheses: the radius schedule, the per-layer CA (the L1–L6 deliverable), initial
     farness — exactly the ones that SHOULD remain.
  5. `discharged_tower_fire` — **the strengthened corollary FIRES with EVERY hypothesis
     discharged** at the real tower: `m = 8`, five welded layers at the `2^19` production
     domain, the proven-far degree-`2^16` monomial `farWord`, radius schedule `d = 0`, CA
     from `curveUDParam_exact` — bound `5·(8−1)·(0+1)/|BabyBear| = 35/|BabyBear| < 2^-25`,
     reproducing `tower_chain_far_survival`'s number through the CA interface route (the two
     caps agree: `(m−1)(0+1) = 7 = n−1`). Contrast `Interface.tower_fire`, which fired at
     `m = 1` over RS(4,1)/ZMod 5.
  6. ⚑ 2026-07-24 — **the prover is QUANTIFIED**:
     `ud_tower_far_survival_discharged_strategy` is the same statement for an ARBITRARY
     `S : Strategy BabyBear (Σ i, Fin (twSz i) → BabyBear)` committing `w0` at round 0, gated
     only on the path-local `FoldConsistentAlong`; theorem 4 is now its honest instance
     (`honest_foldConsistentAlong` discharges the gate for free — nothing is lost), and
     `discharged_tower_fire_strategy` fires it at the real five-layer tower with a prover
     PROVEN not equal to `honestStrategy` (`towerOffpathS_ne_honest`), same `35/|BabyBear|`.
     `FriChainStepIdx.consistencyFreeSurvival_false` refutes the un-gated form outright.
     NOT proved here or anywhere in-tree: the other branch of the dichotomy — that a
     fold-INCONSISTENT prover is caught by the query phase.

**Honest scope.** The fire's CA instances are at radius 0 (exact agreement — the Vandermonde
corner, genuinely proven); the positive-radius `CorrelatedAgreementCurveUDParam` at the
deployed shaved radii is NOT claimed and remains the explicit hypothesis of the general
corollary (the L1–L6 target). This is a ROM/FS statement about honest-fold word evolution —
NOT prover soundness against the deployed verifier; the FRI floor posture is untouched.
Lean-authored throughout; there is no Rust AIR here and there must not be. ADDITIVE: no
existing theorem is edited.

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no new axiom, no
`native_decide`.
-/
import Dregg2.Circuit.CorrelatedAgreement.Interface
import Dregg2.Circuit.FriSetupTower
import Dregg2.Tactics

namespace Dregg2.Circuit.CorrelatedAgreement.DecimLiftDischarge

open Dregg2.Circuit.CorrelatedAgreement
open Dregg2.Circuit.FriFoldArity
  (FriSetupK FriGeomK Cj reassemble self_decomp pullback_card_le mulVec_eq Fold)
open Dregg2.Circuit.FriSetupTower
  (towerS twSz tower_link farWord farWord_far monoW monoW_mem wchain)
open Dregg2.Circuit.FriChainStepIdx (sigFar sigFold)
open Dregg2.Circuit.FriAdversaryObject
  (Strategy honestStrategy fsChain FoldConsistentAlong honest_foldConsistentAlong
   foldConsistentAlong_zero foldConsistentAlong_succ foldConsistentAlong_of_agree_honest)
open Dregg2.Crypto.ProbCrypto (winProb)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open scoped BigOperators Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ## §1 — the `r = 0` m-term UD correlated agreement, PROVEN over any linear code.

The exact m-point Vandermonde solve: `m` distinct challenges whose power-curve combinations
are EXACTLY codewords pin every row into the code. Generalizes
`Interface.curveUDParam_pair_exact` (its `m = 2`) to every `m` — the CA corner the `d = 0`
radius schedule consumes. The positive-radius Prop is NOT touched here (L1–L6's job). -/

section ExactCA

variable {F : Type*} [Field F] [DecidableEq F]

/-- **`r = 0` m-term UD correlated agreement over any submodule code** — the exact
Vandermonde solve. More than `(m−1)·(0+1) = m−1` good challenges means `m` DISTINCT ones;
`m` exact fold equations invert (challenge Vandermonde), so every row `u j` is a linear
combination of codewords, and the simultaneous agreement is TOTAL. -/
theorem curveUDParam_exact (n m : ℕ) (C : Submodule F (Fin n → F)) :
    CorrelatedAgreementCurveUDParam F n (↑C : Set (Fin n → F)) 0 m := by
  intro u Good hGood hcard
  have hcard' : m - 1 < Good.card := by simpa using hcard
  have hm : m ≤ Good.card := by omega
  have hcards : Fintype.card (Fin m) ≤ Fintype.card Good := by
    simpa [Fintype.card_fin, Fintype.card_coe] using hm
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcards
  set α : Fin m → F := fun i => ((e i : F)) with hαdef
  have hαinj : Function.Injective α := fun a b hab => e.injective (Subtype.ext hab)
  have hmem : ∀ i, α i ∈ Good := fun i => (e i).2
  have hv : ∀ i : Fin m, ∃ v, v ∈ C ∧ (fun x => ∑ j : Fin m, α i ^ (j : ℕ) * u j x) = v := by
    intro i
    obtain ⟨v, hvC, hd⟩ := hGood (α i) (hmem i)
    exact ⟨v, hvC, hammingDist_eq_zero.mp (Nat.le_zero.mp hd)⟩
  choose v hvC hveq using hv
  set A : Matrix (Fin m) (Fin m) F := Matrix.vandermonde α with hA
  have hAdet : IsUnit A.det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hαinj)
  have hkey : ∀ j, u j = ∑ i, A⁻¹ j i • v i := by
    intro j
    funext x
    have hcol : A *ᵥ (fun j' => u j' x) = fun i => v i x := by
      funext i
      rw [mulVec_eq]
      have hrow : (∑ j', A i j' * u j' x) = ∑ j' : Fin m, α i ^ (j' : ℕ) * u j' x :=
        Finset.sum_congr rfl fun j' _ => by rw [hA, Matrix.vandermonde_apply]
      rw [hrow]
      exact congrFun (hveq i) x
    have hsolve : (fun j' => u j' x) = A⁻¹ *ᵥ (fun i => v i x) := by
      rw [← hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAdet, Matrix.one_mulVec]
    have hjx := congrFun hsolve j
    rw [mulVec_eq] at hjx
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hjx
  refine ⟨u, fun j => ?_, ?_⟩
  · rw [hkey j]
    exact Submodule.sum_mem _ fun i _ => C.smul_mem _ (hvC i)
  · have huniv : (Finset.univ.filter fun x : Fin n => ∀ j, u j x = u j x) = Finset.univ := by
      simp
    rw [huniv, Finset.card_univ, Fintype.card_fin]
    omega

end ExactCA

/-! ## §2 — the generic decimation-lift engine: any `FriSetupK` satisfies the lift.

THE comparison, made a theorem: `DecimLift`'s demand at `dec := Cj` is exactly
`self_decomp` (the word IS the reassembly of its components) + `unfold_closed` (the
reassembled codeword-tuple is a domain codeword) + `pullback_card_le` (each bad fiber has
`n` points). Nothing beyond what the tower's layers landed. -/

section Engine

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {n : ℕ}

/-- **The decimation lift at any `FriSetupK`** (the BBHR18 reassembly weld): if the `n`
components of `w` agree simultaneously with folded codewords `g j` off `e` points of the
folded domain, then `w` is `(n·e)`-close to the domain code — witness `reassemble G g`,
which `unfold_closed` puts in `C` and `self_decomp` makes agree with `w` over every
agreement fiber. -/
theorem setup_decimLift (S : FriSetupK F ι κ n) (w : ι → F) (g : Fin n → κ → F)
    (hg : ∀ j, g j ∈ S.C') (e : ℕ)
    (hagree : Fintype.card κ - e ≤
      (Finset.univ.filter fun y => ∀ j, Cj S.geom j w y = g j y).card) :
    closeN (↑S.C : Set (ι → F)) (n * e) w := by
  set Ag : Finset κ := Finset.univ.filter (fun y => ∀ j, Cj S.geom j w y = g j y) with hAg
  refine ⟨reassemble S.geom g, S.unfold_closed g hg, ?_⟩
  have hpt : ∀ x : ι, S.geom.q x ∈ Ag → w x = reassemble S.geom g x := by
    intro x hx
    rw [self_decomp S.geom w x]
    show (∑ j : Fin n, (S.geom.p x) ^ (j : ℕ) * Cj S.geom j w (S.geom.q x))
        = ∑ j : Fin n, (S.geom.p x) ^ (j : ℕ) * g j (S.geom.q x)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(Finset.mem_filter.mp hx).2 j]
  have hsub : (Finset.univ.filter fun x : ι => w x ≠ reassemble S.geom g x)
      ⊆ Finset.univ.filter fun x : ι => S.geom.q x ∈ Agᶜ := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, Finset.mem_compl.mpr fun hmem => hx.2 (hpt x hmem)⟩
  have hAgc : Agᶜ.card ≤ e := by
    have h1 : Ag.card ≤ Fintype.card κ := by
      simpa using Finset.card_le_univ Ag
    rw [Finset.card_compl]
    omega
  calc hammingDist w (reassemble S.geom g)
      = (Finset.univ.filter fun x : ι => w x ≠ reassemble S.geom g x).card :=
        hammingDist_eq_card_filter _ _
    _ ≤ (Finset.univ.filter fun x : ι => S.geom.q x ∈ Agᶜ).card := Finset.card_le_card hsub
    _ ≤ n * Agᶜ.card := pullback_card_le S.geom Agᶜ
    _ ≤ n * e := Nat.mul_le_mul_left _ hAgc

end Engine

/-! ## §3 — the tower instance: the interface's `(nn, V, m, dec)` AT the landed tower. -/

section TowerInstance

open Dregg2.Circuit.CorrelatedAgreement.Interface

/-- The layer code schedule at the tower: layers 0–4 the domain codes of the five welded
setups, layer 5 the terminal folded code (`(towerS 4).C'` — definitionally
`rsCode (2^4) 2 (wchain 6)`, the code `FriSetupTower.farT 5` reads), `∅` above the tower
(the finite-depth truncation: an arity-8 setup needs `|ι| ≥ 8`, so there IS no layer 6). -/
noncomputable def towerV : ∀ i, Set (Fin (twSz i) → BabyBear)
  | 0 => ↑(towerS 0 (by omega)).C
  | 1 => ↑(towerS 1 (by omega)).C
  | 2 => ↑(towerS 2 (by omega)).C
  | 3 => ↑(towerS 3 (by omega)).C
  | 4 => ↑(towerS 4 (by omega)).C
  | 5 => ↑(towerS 4 (by omega)).C'
  | _ + 6 => ∅

/-- The decimation family: the `FriFoldArity` components `Cj` at each welded layer — the
decimation whose power-curve combination IS the deployed fold (`towerFold_is_Fold`).
Zero above the tower (never consumed: `towerV` is `∅` there). -/
noncomputable def towerDec :
    ∀ i, (Fin (twSz i) → BabyBear) → Fin 8 → (Fin (twSz (i + 1)) → BabyBear)
  | 0 => fun w j => Cj (towerS 0 (by omega)).geom j w
  | 1 => fun w j => Cj (towerS 1 (by omega)).geom j w
  | 2 => fun w j => Cj (towerS 2 (by omega)).geom j w
  | 3 => fun w j => Cj (towerS 3 (by omega)).geom j w
  | 4 => fun w j => Cj (towerS 4 (by omega)).geom j w
  | _ + 5 => fun _ _ _ => 0

/-- **The interface fold IS the deployed tower fold** — at every real layer,
`towerFold twSz 8 towerDec` is definitionally `FriFoldArity.Fold` at that layer's geometry
(the moment curve of the `Cj` decimations, `FriArityTransfer`'s shape). So the corollary
below prices the REAL fold chain, not a stand-in. -/
theorem towerFold_is_Fold (i : ℕ) (h : i < 5) (w : Fin (twSz i) → BabyBear) (α : BabyBear) :
    towerFold twSz 8 towerDec i w α = Fold (towerS i h).geom α w := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | n + 5 => exact absurd h (by omega)

/-- **⚑ THE DISCHARGE — `DecimLift` HOLDS at the landed tower.** Layers 0–3 route the
codeword hypothesis through `tower_link` (`V (i+1)` is the next DOMAIN code = this layer's
FOLDED code) into `setup_decimLift`; layer 4 feeds the terminal `C'` directly; layers ≥ 5
are vacuous (`towerV = ∅` above the finite tower — no codeword tuple exists to lift). The
hypothesis `Interface.ud_tower_far_survival` carried by NAME is now a THEOREM here. -/
theorem decimLift_of_tower : DecimLift twSz towerV 8 towerDec := by
  intro i w g hg e hagree
  match i with
  | 0 =>
      have h0 : (0 : ℕ) < 5 := by omega
      have h1 : (1 : ℕ) < 5 := by omega
      have hg' : ∀ j, g j ∈ (towerS 0 h0).C' := by
        intro j
        have hj : g j ∈ ((towerS 1 h1).C : Set (Fin (twSz 1) → BabyBear)) := hg j
        rw [← tower_link 0 h0 h1] at hj
        exact hj
      exact setup_decimLift (towerS 0 h0) w g hg' e (by simp only [towerDec, Fintype.card_fin] at hagree ⊢; exact hagree)
  | 1 =>
      have h0 : (1 : ℕ) < 5 := by omega
      have h1 : (2 : ℕ) < 5 := by omega
      have hg' : ∀ j, g j ∈ (towerS 1 h0).C' := by
        intro j
        have hj : g j ∈ ((towerS 2 h1).C : Set (Fin (twSz 2) → BabyBear)) := hg j
        rw [← tower_link 1 h0 h1] at hj
        exact hj
      exact setup_decimLift (towerS 1 h0) w g hg' e (by simp only [towerDec, Fintype.card_fin] at hagree ⊢; exact hagree)
  | 2 =>
      have h0 : (2 : ℕ) < 5 := by omega
      have h1 : (3 : ℕ) < 5 := by omega
      have hg' : ∀ j, g j ∈ (towerS 2 h0).C' := by
        intro j
        have hj : g j ∈ ((towerS 3 h1).C : Set (Fin (twSz 3) → BabyBear)) := hg j
        rw [← tower_link 2 h0 h1] at hj
        exact hj
      exact setup_decimLift (towerS 2 h0) w g hg' e (by simp only [towerDec, Fintype.card_fin] at hagree ⊢; exact hagree)
  | 3 =>
      have h0 : (3 : ℕ) < 5 := by omega
      have h1 : (4 : ℕ) < 5 := by omega
      have hg' : ∀ j, g j ∈ (towerS 3 h0).C' := by
        intro j
        have hj : g j ∈ ((towerS 4 h1).C : Set (Fin (twSz 4) → BabyBear)) := hg j
        rw [← tower_link 3 h0 h1] at hj
        exact hj
      exact setup_decimLift (towerS 3 h0) w g hg' e (by simp only [towerDec, Fintype.card_fin] at hagree ⊢; exact hagree)
  | 4 =>
      have h0 : (4 : ℕ) < 5 := by omega
      have hg' : ∀ j, g j ∈ (towerS 4 h0).C' := fun j => hg j
      exact setup_decimLift (towerS 4 h0) w g hg' e (by simp only [towerDec, Fintype.card_fin] at hagree ⊢; exact hagree)
  | 5 => exact absurd (hg 0) (Set.notMem_empty _)
  | m + 6 => exact absurd (hg 0) (Set.notMem_empty _)

/-- **The lift's hypothesis is INHABITED at the tower** (the discharge is not vacuous at
the real layers): at layer 0 the honest degree-`2^3` codeword's own components satisfy the
agreement hypothesis TOTALLY (`e = 0`) — `foldC_mem` puts each component in the folded
code, which through `tower_link` IS layer 1's domain code `towerV 1` — and the lift lands
the word `0`-close to the layer-0 code, as it must. -/
theorem decimLift_of_tower_fires :
    closeN (towerV 0) (8 * 0) (monoW (twSz 0) (2 ^ 3) (wchain 1)) := by
  have h0 : (0 : ℕ) < 5 := by omega
  have h1 : (1 : ℕ) < 5 := by omega
  have hwC : monoW (twSz 0) (2 ^ 3) (wchain 1) ∈ (towerS 0 h0).C :=
    monoW_mem (wchain 1) (by norm_num)
  refine decimLift_of_tower 0 (monoW (twSz 0) (2 ^ 3) (wchain 1))
    (fun j => Cj (towerS 0 h0).geom j (monoW (twSz 0) (2 ^ 3) (wchain 1))) ?_ 0 ?_
  · intro j
    have hmem := (towerS 0 h0).foldC_mem _ hwC j
    rw [tower_link 0 h0 h1] at hmem
    exact hmem
  · refine le_trans (Nat.sub_le _ _) ?_
    calc twSz (0 + 1) = (Finset.univ : Finset (Fin (twSz (0 + 1)))).card := by
          rw [Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card fun y _ =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ y, fun j => rfl⟩

/-- **⚑⚑ THE STRENGTHENED COROLLARY AT AN ARBITRARY PROVER STRATEGY.** `DecimLift` removed by
`decimLift_of_tower` AND the prover quantified: `S` is any adaptive strategy over layer-tagged
words that commits `w0` at round 0, gated only on the path-local `FoldConsistentAlong`. This
is the deepest probabilistic statement of the ladder in its strategy-generic form at the REAL
five-layer arity-8 tower. `ud_tower_far_survival_discharged` is its honest instance. -/
theorem ud_tower_far_survival_discharged_strategy
    (rr : ℕ → ℕ) (hsched : ∀ i, 8 * rr (i + 1) ≤ rr i)
    (hCA : ∀ i, i < 5 →
      CorrelatedAgreementCurveUDParam BabyBear (twSz (i + 1)) (towerV (i + 1)) (rr (i + 1)) 8)
    (S : Strategy BabyBear (Σ i, (Fin (twSz i) → BabyBear)))
    (w0 : Fin (twSz 0) → BabyBear) (hstart : S [] = ⟨0, w0⟩)
    (hfar0 : ¬ closeN (towerV 0) (rr 0) w0)
    (rounds : ℕ) {bad : (towerD 5 twSz BabyBear → BabyBear) → Bool}
    (hbad : ∀ H : towerD 5 twSz BabyBear → BabyBear, bad H = true →
      FoldConsistentAlong (towerEnc 5 twSz) S (sigFold (towerFold twSz 8 towerDec)) H rounds []
        ∧ ¬ sigFar (towerFar 5 twSz towerV rr)
            (S (fsChain (towerEnc 5 twSz) S H rounds []))) :
    winProb bad
      ≤ ((rounds : ℝ) * (((8 - 1) * (rr 1 + 1) : ℕ) : ℝ)) / (Fintype.card BabyBear : ℝ) :=
  ud_tower_far_survival_strategy 5 twSz towerV rr 8 towerDec (by norm_num) hsched
    decimLift_of_tower hCA S w0 hstart hfar0 rounds hbad

/-- **⚑ THE STRENGTHENED COROLLARY — `ud_tower_far_survival` at the tower, `DecimLift`
REMOVED.** Same conclusion as the §5 interface theorem, at `(L, nn, V, m, dec) :=
(5, twSz, towerV, 8, towerDec)`; the lift weld is supplied by `decimLift_of_tower`. What
remains hypothetical is exactly what SHOULD remain: the radius schedule, the per-layer
UD-regime CA (the L1–L6 deliverable), and the initial farness.

⚑ 2026-07-24: now the honest instance of `ud_tower_far_survival_discharged_strategy` —
statement unchanged; `honest_foldConsistentAlong` discharges the fold-consistency gate for
free, which is the precise sense in which quantifying the prover lost nothing. -/
theorem ud_tower_far_survival_discharged
    (rr : ℕ → ℕ) (hsched : ∀ i, 8 * rr (i + 1) ≤ rr i)
    (hCA : ∀ i, i < 5 →
      CorrelatedAgreementCurveUDParam BabyBear (twSz (i + 1)) (towerV (i + 1)) (rr (i + 1)) 8)
    (w0 : Fin (twSz 0) → BabyBear) (hfar0 : ¬ closeN (towerV 0) (rr 0) w0)
    (rounds : ℕ) {bad : (towerD 5 twSz BabyBear → BabyBear) → Bool}
    (hbad : ∀ H : towerD 5 twSz BabyBear → BabyBear, bad H = true →
      ¬ sigFar (towerFar 5 twSz towerV rr)
          (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, w0⟩
            (fsChain (towerEnc 5 twSz)
              (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, w0⟩) H rounds []))) :
    winProb bad
      ≤ ((rounds : ℝ) * (((8 - 1) * (rr 1 + 1) : ℕ) : ℝ)) / (Fintype.card BabyBear : ℝ) :=
  ud_tower_far_survival_discharged_strategy rr hsched hCA
    (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, w0⟩) w0 rfl hfar0 rounds
    (fun H hH =>
      ⟨honest_foldConsistentAlong (towerEnc 5 twSz) (sigFold (towerFold twSz 8 towerDec))
        ⟨0, w0⟩ H rounds [], hbad H hH⟩)

end TowerInstance

/-! ## §4 — ⚑ NON-VACUITY: the discharged corollary FIRES with EVERY hypothesis met.

`m = 8`, the five welded layers at the real `2^19` production domain, the proven-far
degree-`2^16` monomial, radius schedule `d = 0`, CA from the exact Vandermonde corner
(`curveUDParam_exact`). Bound `5·7/|BabyBear| = 35/|BabyBear|` — the SAME number
`tower_chain_far_survival` proved through `goodδ_card_lt`, now reproduced through the CA
interface with its lift weld PROVEN: the CA cap `(m−1)(0+1) = 7` and the reconstruction cap
`n−1 = 7` agree at the degenerate radius, as they must. -/

section Fire

open Dregg2.Circuit.CorrelatedAgreement.Interface

/-- The per-layer CA at the `d = 0` schedule, DISCHARGED at every real layer by the exact
Vandermonde solve (layers 1–4: domain codes; layer 5: the terminal folded code). -/
theorem hCA_zero : ∀ i, i < 5 →
    CorrelatedAgreementCurveUDParam BabyBear (twSz (i + 1)) (towerV (i + 1)) 0 8 := by
  intro i hi
  interval_cases i
  · exact curveUDParam_exact (twSz 1) 8 (towerS 1 (by omega)).C
  · exact curveUDParam_exact (twSz 2) 8 (towerS 2 (by omega)).C
  · exact curveUDParam_exact (twSz 3) 8 (towerS 3 (by omega)).C
  · exact curveUDParam_exact (twSz 4) 8 (towerS 4 (by omega)).C
  · exact curveUDParam_exact (twSz 5) 8 (towerS 4 (by omega)).C'

/-- The tower's proven-far word is far in the interface vocabulary at radius 0. -/
theorem farWord_far_zero : ¬ closeN (towerV 0) 0 farWord := by
  rintro ⟨v, hv, hd⟩
  have heq : farWord = v := hammingDist_eq_zero.mp (Nat.le_zero.mp hd)
  refine farWord_far ?_
  rw [heq]
  exact hv

open Classical in
/-- **⚑ THE FIRE — the DecimLift-discharged corollary runs END-TO-END at the deployed
tower.** Five FS rounds of the arity-8 fold from the proven-far `farWord` at the real
`2^19` top domain: the probability that farness dies across the five welded layers is at
most `35/|BabyBear|` — with the lift weld, the per-layer CA, the schedule, and the initial
farness ALL theorems (zero named hypotheses left). -/
theorem discharged_tower_fire :
    winProb (fun H : towerD 5 twSz BabyBear → BabyBear =>
        decide (¬ sigFar (towerFar 5 twSz towerV (fun _ => 0))
          (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩
            (fsChain (towerEnc 5 twSz)
              (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩)
              H 5 []))))
      ≤ (35 : ℝ) / (Fintype.card BabyBear : ℝ) := by
  refine le_trans
    (ud_tower_far_survival_discharged (fun _ => 0) (fun _ => by norm_num) hCA_zero
      farWord farWord_far_zero 5
      (bad := fun H => decide (¬ sigFar (towerFar 5 twSz towerV (fun _ => 0))
        (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩
          (fsChain (towerEnc 5 twSz)
            (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩)
            H 5 []))))
      (fun H hH => of_decide_eq_true hH))
    (le_of_eq (by norm_num))

/-- The fired bound is genuinely nontrivial: `35/|BabyBear| < 1` (indeed `< 2^-25`). -/
theorem discharged_fire_lt_one : (35 : ℝ) / (Fintype.card BabyBear : ℝ) < 1 :=
  Dregg2.Circuit.FriSetupTower.tower_bound_lt_one

/-! ### §4.1 — the STRATEGY-generic corollary fires at a prover that is NOT the honest one.

Firing the generalization only at `honestStrategy` would leave open the suspicion that
`FoldConsistentAlong` is a disguised way of saying "S = honestStrategy". It is not: the gate is
PATH-LOCAL, so a prover is free to behave arbitrarily off the 5-round path the oracle walks. -/

/-- A prover at the REAL five-layer tower that agrees with the honest fold on every prefix of
length ≤ 5 — the entire 5-round FS path — and commits the layer-0 word again beyond it, where
the honest prover would sit at layer ≥ 6. -/
noncomputable def towerOffpathS : Strategy BabyBear (Σ i, (Fin (twSz i) → BabyBear)) :=
  fun cs =>
    if cs.length ≤ 5 then
      honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩ cs
    else ⟨0, farWord⟩

/-- It commits the proven-far `farWord` at round 0. -/
theorem towerOffpathS_start : towerOffpathS [] = ⟨0, farWord⟩ := rfl

/-- **It really is a different strategy**: at a 6-challenge prefix the honest prover is at layer
6 and `towerOffpathS` is at layer 0. -/
theorem towerOffpathS_ne_honest :
    towerOffpathS ≠ honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩ := by
  intro h
  have hfst : (towerOffpathS [0, 0, 0, 0, 0, 0]).1
      = (honestStrategy (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩
          [(0 : BabyBear), 0, 0, 0, 0, 0]).1 :=
    congrArg Sigma.fst (congrFun h [0, 0, 0, 0, 0, 0])
  rw [Dregg2.Circuit.FriChainStepIdx.honest_sig_layer] at hfst
  simp [towerOffpathS] at hfst

/-- …and it IS fold-consistent along the whole 5-round path, under every oracle: it agrees with
the honest fold everywhere the run looks (`foldConsistentAlong_of_agree_honest`). -/
theorem towerOffpathS_consistent (H : towerD 5 twSz BabyBear → BabyBear) :
    FoldConsistentAlong (towerEnc 5 twSz) towerOffpathS
      (sigFold (towerFold twSz 8 towerDec)) H 5 [] := by
  refine foldConsistentAlong_of_agree_honest (towerEnc 5 twSz)
    (sigFold (towerFold twSz 8 towerDec)) ⟨0, farWord⟩ towerOffpathS H 5 [] (fun ds hds => ?_)
  simp only [List.length_nil, Nat.add_zero] at hds
  simp only [towerOffpathS, if_pos hds]

open Classical in
/-- **⚑⚑ THE STRATEGY-GENERIC FIRE AT THE DEPLOYED TOWER.** Five FS rounds of the arity-8 fold
from the proven-far `farWord` at the real `2^19` top domain, run by a prover that
`towerOffpathS_ne_honest` proves is NOT the honest one: the probability that farness dies across
the five welded layers is still at most `35/|BabyBear|`. Same number as `discharged_tower_fire`,
now with the prover quantified rather than fixed — every hypothesis discharged (lift weld,
per-layer CA, schedule, initial farness, fold-consistency). -/
theorem discharged_tower_fire_strategy :
    winProb (fun H : towerD 5 twSz BabyBear → BabyBear =>
        decide (¬ sigFar (towerFar 5 twSz towerV (fun _ => 0))
          (towerOffpathS (fsChain (towerEnc 5 twSz) towerOffpathS H 5 []))))
      ≤ (35 : ℝ) / (Fintype.card BabyBear : ℝ) := by
  refine le_trans
    (ud_tower_far_survival_discharged_strategy (fun _ => 0) (fun _ => by norm_num) hCA_zero
      towerOffpathS farWord towerOffpathS_start farWord_far_zero 5
      (bad := fun H => decide (¬ sigFar (towerFar 5 twSz towerV (fun _ => 0))
        (towerOffpathS (fsChain (towerEnc 5 twSz) towerOffpathS H 5 []))))
      (fun H hH => ⟨towerOffpathS_consistent H, of_decide_eq_true hH⟩))
    (le_of_eq (by norm_num))

end Fire

/-! ## §5 — kernel-clean keystones. -/

#assert_all_clean [
  curveUDParam_exact,
  setup_decimLift,
  towerFold_is_Fold,
  decimLift_of_tower,
  decimLift_of_tower_fires,
  ud_tower_far_survival_discharged_strategy,
  ud_tower_far_survival_discharged,
  hCA_zero,
  farWord_far_zero,
  discharged_tower_fire,
  discharged_fire_lt_one,
  towerOffpathS_ne_honest,
  towerOffpathS_consistent,
  discharged_tower_fire_strategy
]

end Dregg2.Circuit.CorrelatedAgreement.DecimLiftDischarge
