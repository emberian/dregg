/-
# `Dregg2.Circuit.FriChainStepIdx` — ladder rung L2: the INDEXED per-layer fold chain, and the
chain-far-survival probability bound (the corollary `FriAdversaryObject` deferred), PROVEN.

`FriAdversaryObject` (§3) landed the fold chain at a FIXED word type `C`: `ChainStep far goodSet
fold` (deliberately a `def`, `:172`), `honest_chain_far` (`:196`, the proven easy half), and a
module-header deferral (`:38-47`): the `winProb` corollary was NOT landed because
`FriVerifierCompose`'s import closure was red. The deployed FRI fold is NOT fixed-`C`: it SHRINKS
the domain each round (arity `2^maxLogArity = 8`, `|L_{i+1}| = |L_i|/8`), so the word TYPE and the
radius change per layer — a per-layer SCHEDULE. This file is the generalization plus the priced
corollary, all proven against green-at-HEAD imports:

  * **§1 the hit bound, re-derived.** `hitWin`/`hit_cond`/`hit_bound` are re-derived here verbatim
    from the green `RomCounting` substrate because at authoring time their home,
    `FriVerifierCompose` (`:160/:190/:294`), was UNIMPORTABLE: its closure reached
    `RecursiveSoundFromNodes → AggAirSound → SpongeForgeReduction.lean`, which failed axiom
    hygiene (`forge_floor_top_false_babyBear` depended on `sorryAx` — the unpropagated
    effFloor-regrounding rename). THAT BREAK IS FIXED (2026-07-23, E1): `SpongeForgeReduction` now
    imports `DomainSeparatedCREffRegrounded` and the whole `FriVerifierCompose` closure rebuilds
    green from source, all tripwires passing. ⚠ DUPLICATION DEBT, on purpose and flagged — and now
    ACTIONABLE: the closure is green again, so exactly ONE copy must survive (delete this §1 and
    import, or re-point Compose here). Nothing else here is copied.
  * **§2-§3 the deferred corollary, landed** (`chain_far_survival`): for ANY strategy-shaped
    honest-fold word evolution from a far `w0`, ANY boolean event that implies "the terminal word
    is not far" has `winProb ≤ n·b/|R|` (`n` rounds, `b`-capped bad sets). The proof is exactly
    the shape the deferral named: `fsRun_queryBounded` + `hit_cond` + `honest_chain_far`, glued by
    `hitWin_fsRun_true_iff` (the hit event on the FS tree IS the failure of `AvoidsBad`).
  * **§3, 2026-07-24 — ⚑ THE PROVER IS NOW QUANTIFIED.** Until this landing every survival
    theorem in the tree instantiated `S := honestStrategy fold w0`: the randomness was genuine
    (uniform `H`) but the PROVER was not adversarial, so what was proved was "the HONEST fold
    chain from a far word keeps it far except w.p. `n·b/|R|`". `chain_far_survival_strategy`
    (and its indexed form `chain_far_survival_idx_strategy`, §4) states the SAME bound for an
    ARBITRARY `S : Strategy R C`, gated on the path-local `FoldConsistentAlong`
    (`FriAdversaryObject`) — the branch of the L2 dichotomy the verifier's fold-consistency spot
    checks force. `chain_far_survival_strategy_gated` is the `bad && decide (consistent)` reading.
    The honest statements are now literal INSTANCES (`honest_foldConsistentAlong` discharges the
    gate for free), so nothing is lost; §6.1 fires the generalized bound at a prover PROVEN not
    equal to the honest one (`offpathS_ne_honest`, bound `7/|BabyBear|`), so nothing is
    disguised. **§3.1 is the canary**: `consistencyFreeSurvival_false` REFUTES the same statement
    with the gate deleted — a prover that COMMITS A CODEWORD at round 1 escapes farness with
    probability exactly 1 (`codewordCommit_escape_prob_one`) against an identity fold and empty
    bad sets, i.e. against a claimed bound of 0. What is still NOT proved anywhere in-tree is the
    other branch (that a fold-INCONSISTENT prover is caught by the query phase); that is the
    query-phase dichotomy, priced separately and not by this file.
    ⚑ One hypothesis is DELIBERATELY different from the landed `honest_chain_far`: the cover is
    FAR-CONDITIONAL (`far w → goodSet w ⊆ E (enc w cs)`), proven sufficient by
    `honest_chain_far_of_farCover`. The unconditional cover the landed theorem demands is
    UNINSTANTIABLE at the deployed RS shape — a MEMBER word's good set is ALL of `F`
    (`fold_complete`), so any unconditional cover forces `b ≥ |F|` and the bound degenerates to
    `≥ n`. That refutation is PROVEN in §7 (`unconditional_cover_trivial_at_deployed`), not prose.
  * **§4 the INDEXED chain** (`ChainStepIdx`): per-layer word types `W i`, per-layer radius
    schedule `far i`, per-layer good sets, `fold i : W i → R → W (i+1)`. The reduction to the
    landed machinery is a THEOREM, not a re-proof: `chainStepIdx_iff_sigma` packages the layer
    index into `Σ i, W i` and is exactly `ChainStep` there; `honest_sig_layer`/`terminal_layer`
    pin the honest evolution to layer = round count. `chain_far_survival_idx` is the composed
    survival bound over the schedule.
  * **§5 the distance-graded cap** (`goodδ_card_lt`, NEW over `FriFoldArity`): a word that is not
    `n²·d`-close to `C` has FEWER THAN `n` challenges folding it `d`-close to `C'` — the
    contrapositive of `fold_close_of_arity_challenges` in cardinality form, generalizing
    `good_challenge_card_lt` (its `d = 0` case). This is the per-layer `b` a real schedule
    consumes; it is a PROVEN cap, which is what separates a legitimate by-definition `goodδ` from
    the vacuity trap (§7).
  * **§6 the instance FIRES**: at the deployed-arity BabyBear setup `friSetupK8` (arity 8,
    `|L| = 16 → |κ| = 2`), a genuine `ChainStepIdx` instance (far word `f0`, cap `b = 7` from
    `goodδ_card_lt`) runs through `chain_far_survival_idx` end-to-end:
    `Pr[the FS-derived challenge folds the far f0 INTO the code] ≤ 7/|BabyBear|` — and the bound
    is genuinely `< 1` (`k8_bound_lt_one`), unlike anything the vacuous route can produce.
  * **§7 the falsifiers** (the acceptance bar: refute the un-generalized / vacuous forms):
      - `fixed_radius_collapse_refuted` — a family where `ChainStepIdx` HOLDS but collapsing the
        schedule to one layer's radius is FALSE at the first fold: the schedule is load-bearing.
      - `goodSet_by_definition_is_free` + `goodSet_by_definition_no_content` — THE VACUITY TRAP,
        exhibited and priced: defining `goodSet w := {r | ¬ far (fold w r)}` makes `ChainStep`
        true for EVERY fold (zero content), and at a farness-destroying fold that set is ALL of
        `R`, so the survival hypotheses force `b ≥ |R|` and the "bound" is `≥ 1`. A by-definition
        good set is admissible ONLY with an externally-PROVEN cap (§5); it can never supply one.
      - `unconditional_cover_trivial_at_deployed` — the landed fixed-`C` `honest_chain_far`'s
        unconditional-cover hypothesis forces `b ≥ |BabyBear|` at the deployed shape (via
        `fHon8_goodδ_univ`): the un-generalized form yields NO nontrivial deployed bound.

## ⚑ Reported precisely: what the tree does NOT yet provide for the DEPLOYED multi-layer schedule

  * **~~No welded setup TOWER~~ — STALE as of 2026-07-25: `Dregg2/Circuit/FriSetupTower.lean` LANDED it**
    (five welded arity-8 layers at the `2^19` production domain, `tower_link` proving
    `(towerS i).C' = (towerS (i+1)).C` across the real schedule, `chainStepIdx_tower`). What remains is
    NOT the tower but its RADIUS: every landed schedule runs at `d = 0`, so the margin in
    `goodδ_card_lt` is zero and `ChainStepGap` has no positive-radius instance. Original text follows.
  * **No welded setup TOWER.** A deployed `L`-layer instance of `ChainStepIdx` needs a family
    `S : Fin L → FriSetupK` with `(S i).C' = (S (i+1)).C` (the folded code of layer `i` IS the
    domain code of layer `i+1`, transported along `κ_i ≃ ι_{i+1}`). `FriFoldArity` provides ONE
    setup (`friSetupK8`, `|ι| = 16, |κ| = 2`) and its §4 instance cannot even take a second
    arity-8 step (`|κ| = 2 < 8`). §6 therefore fires at ONE layer; the multi-layer firing waits
    on the tower (and on realistic domain sizes — cf. `FriPositiveRadiusPayment`'s finding that
    `friSetupK8`'s positive-radius farness is uninhabited at `|L| = 16`).
  * **No vocabulary weld to the ledger.** `FriLedgerSound.ledger_perFold_soundness`'s `goodCount`
    cap lives in the `Φ`/`H`-polynomial vocabulary (`good_card_le_of_phase_injective`), not the
    `FriSetupK`/`closeN` vocabulary `goodδ_card_lt` lives in; identifying the two good sets (so
    the per-layer `b` can be read off the exported ledger) is real work not done here or anywhere
    in-tree. The per-layer `b` this file consumes is `goodδ_card_lt`'s `n − 1`.
  * `hit_cond` prices a UNIFORM per-point cap `b`; a per-layer `Σ bᵢ` refinement would need a
    schedule-indexed hit bound (same induction, indexed budget) — not needed while `b = n − 1`
    is layer-uniform at fixed arity.

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`. Imports green at HEAD (verified by `lake build` before authoring):
`FriAdversaryObject`, `FriFoldArity`, `RomCounting` (+`ProbCrypto`), `Tactics`.
-/
import Dregg2.Circuit.FriAdversaryObject
import Dregg2.Circuit.FriFoldArity
import Dregg2.Crypto.RomCounting
import Dregg2.Tactics
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.FriChainStepIdx

open Dregg2.Crypto.RomOracle
open Dregg2.Circuit.FriAdversaryObject
open Dregg2.Crypto.RomCounting
  (cyl mem_cyl cyl_empty cyl_nonempty condProb condProb_nonneg condProb_le_one condProb_congr
   condProb_le_of_imp condProb_eq_zero condProb_cyl_empty condProb_split condProb_fresh_eq)
open Dregg2.Crypto.ProbCrypto (winProb winProb_le_of_imp winProb_top)
open Dregg2.Circuit.FriSoundness (closeN closeN_zero_iff_mem disagree)
open Dregg2.Circuit.FriFoldArity
  (FriSetupK Fold fold_close_of_arity_challenges friSetupK8 f0 f0_not_mem fHon8
   fHon8_fold_complete)
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)

/-! ## §1 — the hit bound, re-derived on the green substrate.

⚠ DUPLICATION DEBT (deliberate, tracked in the module header): `hitWin`, `hit_cond`, `hit_bound`
restate `FriVerifierCompose:160/:190/:294` verbatim, because at authoring time that module's
import closure failed (`SpongeForgeReduction.forge_floor_top_false_babyBear` depended on
`sorryAx`). The closure is REPAIRED and green (2026-07-23) — deleting one copy is now actionable. -/

/-- **THE HIT EVENT** (= `FriVerifierCompose.hitWin`). `hitWin E M H` = SOME query along `M`'s run
against `H` receives an answer in that point's target set `E d`. -/
def hitWin {D R A : Type} [DecidableEq R] (E : D → Finset R) :
    OracleComp D R A → (D → R) → Bool
  | .pure _,    _ => false
  | .query d k, H => decide (H d ∈ E d) || hitWin E (k (H d)) H

theorem hitWin_pure {D R A : Type} [DecidableEq R] (E : D → Finset R) (a : A) (H : D → R) :
    hitWin E (OracleComp.pure a : OracleComp D R A) H = false := rfl

theorem hitWin_query {D R A : Type} [DecidableEq R] (E : D → Finset R) (d : D)
    (k : R → OracleComp D R A) (H : D → R) :
    hitWin E (OracleComp.query d k) H = (decide (H d ∈ E d) || hitWin E (k (H d)) H) := rfl

section HitBound

variable {D R A : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]

/-- **The conditional hit bound** (= `FriVerifierCompose.hit_cond`; see the §1 debt note). A
`Q`-query adversary, run against an oracle already pinned on `S` to non-hit values, receives an
answer in its point's target set at SOME query with probability `≤ Q·b/|R|`, `b` capping every
target set. Induction on the query tree: a repeat query is answered by the conditioning (a
non-hit, costs zero); a fresh query splits on its answer (`condProb_split`), at most `b` of the
`|R|` slices are hits at full price `≤ 1`, and the rest extend the invariant for the IH. -/
theorem hit_cond {Q b : ℕ} {M : OracleComp D R A} (hM : QueryBounded Q M)
    (E : D → Finset R) (hE : ∀ d, (E d).card ≤ b) :
    ∀ (S : Finset D) (σ : D → R), (∀ d ∈ S, σ d ∉ E d) →
      condProb (cyl S σ) (hitWin E M) ≤ ((Q : ℝ) * (b : ℝ)) / (Fintype.card R : ℝ) := by
  have hRpos : (0 : ℝ) < (Fintype.card R : ℝ) := by exact_mod_cast Fintype.card_pos
  induction hM with
  | pure n a =>
      intro S σ _
      refine le_trans (le_of_eq (condProb_eq_zero (fun H _ => by rw [hitWin_pure]))) ?_
      positivity
  | query n d k _hk ih =>
      intro S σ hσ
      by_cases hd : d ∈ S
      · -- REPEAT: the conditioning already answered `d`, to a non-hit. Costs nothing.
        have hcongr : condProb (cyl S σ) (hitWin E (OracleComp.query d k))
            = condProb (cyl S σ) (hitWin E (k (σ d))) := by
          refine condProb_congr (fun H hH => ?_)
          have hpin : H d = σ d := (mem_cyl.1 hH) d hd
          rw [hitWin_query, hpin]
          have hno : decide (σ d ∈ E d) = false := by
            simp only [decide_eq_false_iff_not]; exact hσ d hd
          rw [hno, Bool.false_or]
        rw [hcongr]
        refine (ih (σ d) S σ hσ).trans ?_
        rw [div_le_div_iff_of_pos_right hRpos]
        have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
        push_cast
        nlinarith
      · -- FRESH: split on the answer — the law of total probability over the prefix.
        rw [condProb_split S σ d hd]
        set B : ℝ := ((n : ℝ) * (b : ℝ)) / (Fintype.card R : ℝ) with hB
        have hBnn : 0 ≤ B := by rw [hB]; positivity
        have hterm : ∀ r : R,
            condProb (cyl (insert d S) (Function.update σ d r)) (hitWin E (OracleComp.query d k))
              = condProb (cyl (insert d S) (Function.update σ d r))
                  (fun H => decide (r ∈ E d) || hitWin E (k r) H) := by
          intro r
          refine condProb_congr (fun H hH => ?_)
          have hpin : H d = r := by
            have := (mem_cyl.1 hH) d (Finset.mem_insert_self d S)
            simpa using this
          rw [hitWin_query, hpin]
        have hgood : ∀ r ∈ Finset.univ \ E d,
            condProb (cyl (insert d S) (Function.update σ d r)) (hitWin E (OracleComp.query d k))
              ≤ B := by
          intro r hr
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hr
          rw [hterm r]
          have hdec : decide (r ∈ E d) = false := by
            simp only [decide_eq_false_iff_not]; exact hr
          rw [condProb_congr (win' := hitWin E (k r)) (fun H _ => by rw [hdec, Bool.false_or])]
          refine ih r (insert d S) (Function.update σ d r) ?_
          intro e he
          rcases Finset.mem_insert.1 he with rfl | he'
          · rw [Function.update_self]; exact hr
          · have hne : e ≠ d := fun h => hd (h ▸ he')
            rw [Function.update_of_ne hne]
            exact hσ e he'
        have hsub : E d ⊆ (Finset.univ : Finset R) := Finset.subset_univ _
        have hsplit : (∑ r : R,
              condProb (cyl (insert d S) (Function.update σ d r)) (hitWin E (OracleComp.query d k)))
            = (∑ r ∈ Finset.univ \ E d,
                condProb (cyl (insert d S) (Function.update σ d r)) (hitWin E (OracleComp.query d k)))
              + (∑ r ∈ E d,
                condProb (cyl (insert d S) (Function.update σ d r)) (hitWin E (OracleComp.query d k)))
            := (Finset.sum_sdiff hsub).symm
        have hbad : (∑ r ∈ E d,
              condProb (cyl (insert d S) (Function.update σ d r)) (hitWin E (OracleComp.query d k)))
            ≤ (b : ℝ) := by
          refine (Finset.sum_le_card_nsmul _ _ 1 (fun r _ => condProb_le_one _ _)).trans ?_
          rw [nsmul_eq_mul, mul_one]
          exact_mod_cast hE d
        have hgoodsum : (∑ r ∈ Finset.univ \ E d,
              condProb (cyl (insert d S) (Function.update σ d r)) (hitWin E (OracleComp.query d k)))
            ≤ (Fintype.card R : ℝ) * B := by
          refine (Finset.sum_le_card_nsmul _ _ B hgood).trans ?_
          rw [nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ hBnn
          have hc : (Finset.univ \ E d).card ≤ Fintype.card R := by
            simpa using Finset.card_le_card (Finset.subset_univ (Finset.univ \ E d))
          exact_mod_cast hc
        have hRB : (Fintype.card R : ℝ) * B = (n : ℝ) * (b : ℝ) := by
          rw [hB, mul_comm, div_mul_cancel₀ _ (ne_of_gt hRpos)]
        rw [hsplit, div_le_iff₀ hRpos]
        have hnum : (∑ r ∈ Finset.univ \ E d,
              condProb (cyl (insert d S) (Function.update σ d r)) (hitWin E (OracleComp.query d k)))
            + (∑ r ∈ E d,
              condProb (cyl (insert d S) (Function.update σ d r)) (hitWin E (OracleComp.query d k)))
            ≤ (n : ℝ) * (b : ℝ) + (b : ℝ) := add_le_add (hgoodsum.trans (le_of_eq hRB)) hbad
        refine hnum.trans ?_
        rw [div_mul_cancel₀ _ (ne_of_gt hRpos)]
        push_cast
        ring_nf
        nlinarith [Nat.cast_nonneg (α := ℝ) b]

/-- **The unconditional hit bound** (= `FriVerifierCompose.hit_bound`): at the empty conditioning,
a `Q`-query adversary ever draws an answer in its point's target set with probability
`≤ Q·b/|R|`. -/
theorem hit_bound {Q b : ℕ} (M : OracleComp D R A) (hM : QueryBounded Q M)
    (E : D → Finset R) (hE : ∀ d, (E d).card ≤ b) :
    winProb (hitWin E M) ≤ ((Q : ℝ) * (b : ℝ)) / (Fintype.card R : ℝ) := by
  have h := hit_cond hM E hE ∅ (fun _ => Classical.arbitrary R) (by simp)
  rw [condProb_cyl_empty] at h
  exact h

end HitBound

/-! ## §2 — the glue: on the FS tree, the hit event IS the failure of `AvoidsBad`. -/

/-- **The hit event on `fsRun` is exactly `¬ AvoidsBad`.** The FS transform queries one point per
round, and `AvoidsBad` demands each round's answer avoid that point's bad set — so `hitWin` fires
iff some round violates it. This is the two-line bridge the `FriAdversaryObject` header promised
(`AvoidsBad` "is the complement, specialized to `fsRun`, of `hitWin`"), now a theorem. -/
theorem hitWin_fsRun_true_iff {R C D : Type} [DecidableEq R] (enc : C → List R → D)
    (S : Strategy R C) (E : D → Finset R) (H : D → R) :
    ∀ (n : ℕ) (cs : List R),
      hitWin E (fsRun enc S n cs) H = true ↔ ¬ AvoidsBad enc S E H n cs := by
  intro n
  induction n with
  | zero =>
      intro cs
      simp [fsRun, AvoidsBad, hitWin]
  | succ n ih =>
      intro cs
      simp only [fsRun, AvoidsBad, hitWin_query, Bool.or_eq_true, decide_eq_true_eq,
        ih (H (enc (S cs) cs) :: cs)]
      tauto

/-! ## §3 — ⚑ the deferred corollary, landed: chain-far survival is priced. -/

/-- **Chain farness under a FAR-CONDITIONAL cover** — the landed `honest_chain_far`
(`FriAdversaryObject:196`) with its one over-strong hypothesis weakened: the cover
`goodSet w ⊆ E (enc w cs)` is demanded only at FAR `w`. Same induction (the chain only ever
stands on far words). This weakening is NOT cosmetic: §7's
`unconditional_cover_trivial_at_deployed` proves the unconditional form forces `b ≥ |F|` at the
deployed RS shape (a MEMBER word's good set is everything), i.e. the landed hypothesis shape
admits no nontrivial deployed bound.

⚑ 2026-07-24: now an INSTANCE of `FriAdversaryObject.chain_far_strategy_of_farCover` at
`S := honestStrategy fold w0`, whose fold-consistency is unconditional
(`honest_foldConsistentAlong`). Statement unchanged; the duplicated induction is gone. -/
theorem honest_chain_far_of_farCover {R C D : Type} {far : C → Prop} {goodSet : C → Finset R}
    {fold : C → R → C} (hstep : ChainStep far goodSet fold)
    (enc : C → List R → D) (E : D → Finset R) (w0 : C)
    (hcover : ∀ (w : C) (cs : List R), far w → goodSet w ⊆ E (enc w cs))
    (H : D → R) :
    ∀ (n : ℕ) (cs : List R),
      far (honestStrategy fold w0 cs) →
      AvoidsBad enc (honestStrategy fold w0) E H n cs →
      far (honestStrategy fold w0 (fsChain enc (honestStrategy fold w0) H n cs)) :=
  fun n cs hfar havoid =>
    chain_far_strategy_of_farCover hstep enc E (honestStrategy fold w0) hcover H n cs hfar havoid
      (honest_foldConsistentAlong enc fold w0 H n cs)

/-- **⚑⚑ CHAIN-FAR SURVIVAL AT AN ARBITRARY PROVER STRATEGY, PRICED.** The deepest probabilistic
object of the FRI ladder, no longer restricted to the honest prover. `S : Strategy R C` is ANY
adaptive strategy (challenge history ↦ next commitment); the only thing asked of it is the
PATH-LOCAL `FoldConsistentAlong` (each round's commitment is the fold of the previous one along
the path the oracle walks — what the verifier's fold-consistency spot checks force, on pain of
being caught). Then any boolean event implying "`S` was fold-consistent along the path AND the
terminal commitment is NOT far" has probability at most `n·b/|R|`.

Same recipe as before — `fsRun_queryBounded` + `hit_bound` + `chain_far_strategy_of_farCover`,
glued by `hitWin_fsRun_true_iff` — but the randomness is now genuinely quantified over a prover
STRATEGY rather than over the honest fold of a fixed `w0`. `chain_far_survival` is the honest
instance (nothing lost); `consistencyFreeSurvival_false` (§3.1) shows the gate cannot be dropped;
`k8_chain_far_survival_offpath` (§6) fires it at the deployed arity-8 shape with a strategy
PROVEN not equal to `honestStrategy`. -/
theorem chain_far_survival_strategy {D R C : Type}
    [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]
    {far : C → Prop} {goodSet : C → Finset R} {fold : C → R → C}
    (hstep : ChainStep far goodSet fold)
    (enc : C → List R → D) (E : D → Finset R) {b : ℕ} (hE : ∀ d, (E d).card ≤ b)
    (S : Strategy R C) (hcover : ∀ (w : C) (cs : List R), far w → goodSet w ⊆ E (enc w cs))
    (hfar0 : far (S [])) (n : ℕ) {bad : (D → R) → Bool}
    (hbad : ∀ H : D → R, bad H = true →
      FoldConsistentAlong enc S fold H n [] ∧ ¬ far (S (fsChain enc S H n []))) :
    winProb bad ≤ ((n : ℝ) * (b : ℝ)) / (Fintype.card R : ℝ) := by
  have himp : ∀ H : D → R, bad H = true → hitWin E (fsRun enc S n []) H = true := by
    intro H hH
    obtain ⟨hcons, hnotfar⟩ := hbad H hH
    by_contra hnot
    have havoid : AvoidsBad enc S E H n [] := by
      by_contra hav
      exact hnot ((hitWin_fsRun_true_iff enc S E H n []).mpr hav)
    exact hnotfar (chain_far_strategy_of_farCover hstep enc E S hcover H n [] hfar0 havoid hcons)
  exact (winProb_le_of_imp himp).trans (hit_bound _ (fsRun_queryBounded enc S n []) E hE)

open Classical in
/-- The **GATED-EVENT reading** of `chain_far_survival_strategy`: for an arbitrary strategy, the
event "`bad` fires AND the strategy was fold-consistent along the walked path" is priced at
`n·b/|R|`. This is the form a soundness assembly consumes — the other branch of the dichotomy
("`S` was fold-inconsistent somewhere along the path") is the branch the verifier's spot checks
catch, and is priced separately by the query phase. -/
theorem chain_far_survival_strategy_gated {D R C : Type}
    [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]
    {far : C → Prop} {goodSet : C → Finset R} {fold : C → R → C}
    (hstep : ChainStep far goodSet fold)
    (enc : C → List R → D) (E : D → Finset R) {b : ℕ} (hE : ∀ d, (E d).card ≤ b)
    (S : Strategy R C) (hcover : ∀ (w : C) (cs : List R), far w → goodSet w ⊆ E (enc w cs))
    (hfar0 : far (S [])) (n : ℕ) {bad : (D → R) → Bool}
    (hbad : ∀ H : D → R, bad H = true → ¬ far (S (fsChain enc S H n []))) :
    winProb (fun H : D → R => bad H && decide (FoldConsistentAlong enc S fold H n []))
      ≤ ((n : ℝ) * (b : ℝ)) / (Fintype.card R : ℝ) := by
  refine chain_far_survival_strategy hstep enc E hE S hcover hfar0 n ?_
  intro H hH
  rw [Bool.and_eq_true] at hH
  exact ⟨of_decide_eq_true hH.2, hbad H hH.1⟩

/-- **⚑ CHAIN-FAR SURVIVAL, PRICED** — the corollary `FriAdversaryObject:38-47` deferred. Under a
`ChainStep` instance with `b`-capped, far-conditionally-covered bad sets, ANY boolean event that
implies "the terminal word of the `n`-round honest-fold FS chain from the far `w0` is NOT far"
has probability at most `n·b/|R|` over the random oracle. Proof = the deferral's recipe:
`fsRun_queryBounded` (the FS chain is an `n`-query tree) + `hit_cond`/`hit_bound` (the hit event
is priced) + `honest_chain_far_of_farCover` (no hit ⟹ far survives), glued by
`hitWin_fsRun_true_iff`. Stated against an abstract `bad` so no decidability of `far` is needed;
`chain_far_survival_prob` reads it as the direct event.

⚑ 2026-07-24: now the HONEST INSTANCE of `chain_far_survival_strategy` — statement unchanged, and
the fold-consistency gate discharges to nothing because `honest_foldConsistentAlong` holds
unconditionally. That is the precise sense in which the strategy-generic bound loses nothing. -/
theorem chain_far_survival {D R C : Type}
    [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]
    {far : C → Prop} {goodSet : C → Finset R} {fold : C → R → C}
    (hstep : ChainStep far goodSet fold)
    (enc : C → List R → D) (E : D → Finset R) {b : ℕ} (hE : ∀ d, (E d).card ≤ b)
    (w0 : C) (hcover : ∀ (w : C) (cs : List R), far w → goodSet w ⊆ E (enc w cs))
    (hfar0 : far w0) (n : ℕ) {bad : (D → R) → Bool}
    (hbad : ∀ H : D → R, bad H = true →
      ¬ far (honestStrategy fold w0 (fsChain enc (honestStrategy fold w0) H n []))) :
    winProb bad ≤ ((n : ℝ) * (b : ℝ)) / (Fintype.card R : ℝ) :=
  chain_far_survival_strategy hstep enc E hE (honestStrategy fold w0) hcover
    (by simpa using hfar0) n
    (fun H hH => ⟨honest_foldConsistentAlong enc fold w0 H n [], hbad H hH⟩)

open Classical in
/-- The direct-event reading: `Pr[the terminal word is not far] ≤ n·b/|R|` (classical
decidability of the farness event). -/
theorem chain_far_survival_prob {D R C : Type}
    [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]
    {far : C → Prop} {goodSet : C → Finset R} {fold : C → R → C}
    (hstep : ChainStep far goodSet fold)
    (enc : C → List R → D) (E : D → Finset R) {b : ℕ} (hE : ∀ d, (E d).card ≤ b)
    (w0 : C) (hcover : ∀ (w : C) (cs : List R), far w → goodSet w ⊆ E (enc w cs))
    (hfar0 : far w0) (n : ℕ) :
    winProb (fun H : D → R =>
        decide (¬ far (honestStrategy fold w0 (fsChain enc (honestStrategy fold w0) H n []))))
      ≤ ((n : ℝ) * (b : ℝ)) / (Fintype.card R : ℝ) :=
  chain_far_survival hstep enc E hE w0 hcover hfar0 n
    (fun _H h => of_decide_eq_true h)

/-! ## §3.1 — ⚑ THE CANARY: without fold-consistency the strategy-generic bound is FALSE.

The whole content of the generalization is that the gate `FoldConsistentAlong` is the ONLY thing
`chain_far_survival_strategy` asks of an arbitrary prover — so it had better be load-bearing.
It is, and this is the witness: a prover that simply COMMITS A CODEWORD at round 1 escapes
farness with probability EXACTLY 1, against a fold that preserves farness perfectly (the
identity) and EMPTY bad sets (`b = 0`, so the claimed bound is `0`). Every other hypothesis of
`chain_far_survival` — `ChainStep`, the cap, the cover, initial farness — is satisfied. The
strategy is excluded by exactly one thing: it is fold-INCONSISTENT at round 1
(`codewordCommit_not_foldConsistent`). -/

section Canary

/-- Canary farness: `0` is the only far word. -/
def canaryFar : ℕ → Prop := fun w => w = 0

/-- The canary's fold is the IDENTITY — the most farness-preserving fold there is: EVERY
challenge keeps a far word far, so the honest chain never loses farness at all. -/
def canaryFold : ℕ → Bool → ℕ := fun w _ => w

/-- Empty good sets. -/
def canaryGood : ℕ → Finset Bool := fun _ => ∅

/-- One query point (the canary needs no transcript structure). -/
def canaryEnc : ℕ → List Bool → Unit := fun _ _ => ()

/-- Empty bad sets: the cap is `b = 0`, so the survival bound being claimed is `n·0/2 = 0`. -/
def canaryE : Unit → Finset Bool := fun _ => ∅

/-- **THE CHEATING STRATEGY — COMMIT A CODEWORD AT ROUND 1.** At round 0 it shows the far word
(`0`); from round 1 on it shows a NON-far word (a "codeword") no matter what challenge the oracle
drew. Nothing in the `Strategy` type forbids this — which is the point: `Strategy R C` is
`List R → C` and nothing ties `S cs` to a fold of `S cs.tail`. -/
def codewordCommit : Strategy Bool ℕ := fun cs => cs.length

/-- The canary's `ChainStep` holds — and not vacuously: the identity fold preserves farness at
EVERY challenge, so this is the strongest possible per-round obligation. -/
theorem canary_chainStep : ChainStep canaryFar canaryGood canaryFold :=
  fun _w _r hfar _ => hfar

/-- The canary's cap: `b = 0`. -/
theorem canaryE_card : ∀ d, (canaryE d).card ≤ 0 := by
  intro d
  simp [canaryE]

/-- The canary's (far-conditional, hence also unconditional) cover. -/
theorem canary_cover : ∀ (w : ℕ) (cs : List Bool),
    canaryFar w → canaryGood w ⊆ canaryE (canaryEnc w cs) := by
  intro w cs _
  simp [canaryGood, canaryE]

/-- The cheating prover starts FAR: its round-0 commitment is the far word. -/
theorem codewordCommit_far0 : canaryFar (codewordCommit []) := rfl

/-- **The escape**: after one FS round the cheating prover's commitment is NOT far, for EVERY
oracle. No randomness saves the bound — the escape is deterministic. -/
theorem codewordCommit_escapes (H : Unit → Bool) :
    ¬ canaryFar (codewordCommit (fsChain canaryEnc codewordCommit H 1 [])) := by
  simp [fsChain, canaryEnc, canaryFar, codewordCommit]

open Classical in
/-- **Probability EXACTLY 1** — the cheating prover leaves farness with certainty, against a
claimed bound of `1·0/|Bool| = 0`. -/
theorem codewordCommit_escape_prob_one :
    winProb (fun H : Unit → Bool =>
        decide (¬ canaryFar (codewordCommit (fsChain canaryEnc codewordCommit H 1 [])))) = 1 := by
  have hfun : (fun H : Unit → Bool =>
      decide (¬ canaryFar (codewordCommit (fsChain canaryEnc codewordCommit H 1 []))))
      = (fun _ : Unit → Bool => true) :=
    funext fun H => decide_eq_true (codewordCommit_escapes H)
  rw [hfun, winProb_top]

/-- **⚑ AND IT IS EXACTLY FOLD-CONSISTENCY THAT EXCLUDES IT.** The cheating strategy fails
`FoldConsistentAlong` at the very first round, under every oracle: it commits `1` where the fold
of its own round-0 commitment is `0`. So `chain_far_survival_strategy` does not apply to it — the
gate is not decoration, it is the whole difference between a true theorem and a false one. -/
theorem codewordCommit_not_foldConsistent (H : Unit → Bool) :
    ¬ FoldConsistentAlong canaryEnc codewordCommit canaryFold H 1 [] := by
  intro hc
  rw [foldConsistentAlong_succ] at hc
  have h1 := hc.1
  simp [codewordCommit, canaryFold, canaryEnc] at h1

/-- **The consistency-FREE survival statement**, monomorphic at `(D, R, C) = (Unit, Bool, ℕ)`:
`chain_far_survival_strategy` with the `FoldConsistentAlong` gate DELETED. Written out as a
`Prop` so that it can be refuted as a theorem rather than argued in prose. -/
def ConsistencyFreeSurvival : Prop :=
  ∀ (far : ℕ → Prop) (goodSet : ℕ → Finset Bool) (fold : ℕ → Bool → ℕ),
    ChainStep far goodSet fold →
    ∀ (enc : ℕ → List Bool → Unit) (E : Unit → Finset Bool) (b : ℕ),
      (∀ d, (E d).card ≤ b) →
      ∀ S : Strategy Bool ℕ,
        (∀ (w : ℕ) (cs : List Bool), far w → goodSet w ⊆ E (enc w cs)) →
        far (S []) →
        ∀ (n : ℕ) (bad : (Unit → Bool) → Bool),
          (∀ H : Unit → Bool, bad H = true → ¬ far (S (fsChain enc S H n []))) →
          winProb bad ≤ ((n : ℝ) * (b : ℝ)) / (Fintype.card Bool : ℝ)

open Classical in
/-- **THE OTHER SIDE OF THE CANARY, AT THE SAME INSTANCE.** Turn the gate back ON and the very
same codeword-committing prover satisfies the bound — and the theorem that supplies it is the
GENERAL `chain_far_survival_strategy_gated`, not a special case. Gate off: probability 1 against
a bound of 0 (`consistencyFreeSurvival_false`). Gate on: `≤ 0`. One instance, both signs: that is
what "load-bearing" means. -/
theorem codewordCommit_gated_bound :
    winProb (fun H : Unit → Bool =>
        true && decide (FoldConsistentAlong canaryEnc codewordCommit canaryFold H 1 []))
      ≤ ((1 : ℕ) : ℝ) * ((0 : ℕ) : ℝ) / (Fintype.card Bool : ℝ) := by
  exact chain_far_survival_strategy_gated canary_chainStep canaryEnc canaryE canaryE_card
    codewordCommit canary_cover codewordCommit_far0 1
    (bad := fun _ => true) (fun H _ => codewordCommit_escapes H)

/-- **⚑⚑ THE CANARY, AS A REFUTATION.** The consistency-free survival statement is FALSE. The
witness is the codeword-committing prover: `ChainStep` holds (identity fold), the cap is `b = 0`,
the cover holds, the prover starts far — and it leaves farness with probability `1 > 0`. So
`FoldConsistentAlong` is LOAD-BEARING in `chain_far_survival_strategy`, and the tree's deepest
probabilistic object was, before this generalization, silently assuming it away by fixing
`S := honestStrategy fold w0` (for which the gate is free, `honest_foldConsistentAlong`). -/
theorem consistencyFreeSurvival_false : ¬ ConsistencyFreeSurvival := by
  intro h
  have hb := h canaryFar canaryGood canaryFold canary_chainStep canaryEnc canaryE 0
    canaryE_card codewordCommit canary_cover codewordCommit_far0 1 (fun _ => true)
    (fun H _ => codewordCommit_escapes H)
  rw [winProb_top] at hb
  norm_num [Fintype.card_bool] at hb

end Canary

/-! ## §4 — ⚑ the INDEXED per-layer chain: the form the deployed shrinking-domain fold needs. -/

section Indexed

variable {R D : Type} {W : ℕ → Type}

/-- **`ChainStepIdx` — the per-LAYER distance-preservation obligation.** Generalizes the fixed-`C`
`ChainStep` (`FriAdversaryObject:172`) to the deployed shape: the word TYPE changes per layer
(`W i`, the shrinking evaluation domain — arity 8 divides `|L|` by 8 each round), the radius
schedule changes per layer (`far i`, e.g. `¬ closeN Cᵢ (dᵢ)` with `dᵢ = n²·dᵢ₊₁` at the
unique-decoding radius — see `goodδ_card_lt`), and the good sets are per-layer. An instance at
layer `i` says: an `i`-far word folded at a challenge outside its layer-`i` good set is
`(i+1)`-far. -/
def ChainStepIdx (far : ∀ i, W i → Prop) (good : ∀ i, W i → Finset R)
    (fold : ∀ i, W i → R → W (i + 1)) : Prop :=
  ∀ (i : ℕ) (w : W i) (r : R), far i w → r ∉ good i w → far (i + 1) (fold i w r)

/-- The layer-tagged word: fold at the tagged layer, land at the next. -/
def sigFold (fold : ∀ i, W i → R → W (i + 1)) : (Σ i, W i) → R → Σ i, W i :=
  fun w r => ⟨w.1 + 1, fold w.1 w.2 r⟩

/-- Farness at the tagged layer. -/
def sigFar (far : ∀ i, W i → Prop) : (Σ i, W i) → Prop := fun w => far w.1 w.2

/-- The good set at the tagged layer. -/
def sigGood (good : ∀ i, W i → Finset R) : (Σ i, W i) → Finset R := fun w => good w.1 w.2

/-- **The generalization is a THEOREM, not a re-proof**: `ChainStepIdx` is exactly `ChainStep` on
the layer-tagged carrier `Σ i, W i`. Everything the landed §3 machinery proves about `ChainStep`
transfers along this equivalence — which is how `chain_far_survival_idx` below is one line. (What
canNOT be recovered is the schedule-FREE fixed-radius reading; §7's
`fixed_radius_collapse_refuted` refutes it.) -/
theorem chainStepIdx_iff_sigma {far : ∀ i, W i → Prop} {good : ∀ i, W i → Finset R}
    {fold : ∀ i, W i → R → W (i + 1)} :
    ChainStepIdx far good fold ↔ ChainStep (sigFar far) (sigGood good) (sigFold fold) := by
  constructor
  · rintro h ⟨i, w⟩ r hf hg
    exact h i w r hf hg
  · intro h i w r hf hg
    exact h ⟨i, w⟩ r hf hg

/-- The honest layer-tagged evolution tracks the round count: after `cs` challenges the word sits
at layer `cs.length`. -/
theorem honest_sig_layer (fold : ∀ i, W i → R → W (i + 1)) (w0 : W 0) :
    ∀ cs : List R, (honestStrategy (sigFold fold) ⟨0, w0⟩ cs).1 = cs.length := by
  intro cs
  induction cs with
  | nil => rfl
  | cons r cs ih =>
      rw [honestStrategy_cons, List.length_cons]
      show (honestStrategy (sigFold fold) ⟨0, w0⟩ cs).1 + 1 = cs.length + 1
      rw [ih]

/-- The terminal word of the `n`-round FS chain sits at layer `n` (`honest_sig_layer` +
`fsChain_length`). -/
theorem terminal_layer {D R : Type} {W : ℕ → Type} (fold : ∀ i, W i → R → W (i + 1))
    (enc : (Σ i, W i) → List R → D) (w0 : W 0) (H : D → R) (n : ℕ) :
    (honestStrategy (sigFold fold) ⟨0, w0⟩
        (fsChain enc (honestStrategy (sigFold fold) ⟨0, w0⟩) H n [])).1 = n := by
  rw [honest_sig_layer, fsChain_length]
  simp

/-- **⚑⚑ the COMPOSED survival bound over the schedule, AT AN ARBITRARY PROVER STRATEGY.** The
multi-layer form of `chain_far_survival_strategy`: `S : Strategy R (Σ i, W i)` is any adaptive
prover over layer-tagged commitments, gated only on path-local fold-consistency. One line through
`chainStepIdx_iff_sigma`. `chain_far_survival_idx` is the honest instance. -/
theorem chain_far_survival_idx_strategy {D R : Type} {W : ℕ → Type}
    [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]
    {far : ∀ i, W i → Prop} {good : ∀ i, W i → Finset R} {fold : ∀ i, W i → R → W (i + 1)}
    (hidx : ChainStepIdx far good fold)
    (enc : (Σ i, W i) → List R → D) (E : D → Finset R) {b : ℕ}
    (hE : ∀ d, (E d).card ≤ b) (S : Strategy R (Σ i, W i))
    (hcover : ∀ (i : ℕ) (w : W i) (cs : List R), far i w → good i w ⊆ E (enc ⟨i, w⟩ cs))
    (hfar0 : sigFar far (S [])) (n : ℕ) {bad : (D → R) → Bool}
    (hbad : ∀ H : D → R, bad H = true →
      FoldConsistentAlong enc S (sigFold fold) H n [] ∧
        ¬ sigFar far (S (fsChain enc S H n []))) :
    winProb bad ≤ ((n : ℝ) * (b : ℝ)) / (Fintype.card R : ℝ) :=
  chain_far_survival_strategy (chainStepIdx_iff_sigma.mp hidx) enc E hE S
    (fun w cs hf => by cases w with | mk i wi => exact hcover i wi cs hf)
    hfar0 n hbad

/-- **⚑ the COMPOSED survival bound over the schedule** — (iii) of the rung: a `ChainStepIdx`
instance with per-layer far-conditionally-covered, `b`-capped good sets prices the whole
multi-layer fold chain: any event implying "the layer-`n` terminal word is not `n`-far" has
probability `≤ n·b/|R|`. One line through `chainStepIdx_iff_sigma` + `chain_far_survival` — the
indexed form genuinely RIDES the landed fixed-`C` machinery rather than duplicating it.

⚑ 2026-07-24: now the honest instance of `chain_far_survival_idx_strategy`. -/
theorem chain_far_survival_idx {D R : Type} {W : ℕ → Type}
    [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]
    {far : ∀ i, W i → Prop} {good : ∀ i, W i → Finset R} {fold : ∀ i, W i → R → W (i + 1)}
    (hidx : ChainStepIdx far good fold)
    (enc : (Σ i, W i) → List R → D) (E : D → Finset R) {b : ℕ}
    (hE : ∀ d, (E d).card ≤ b) (w0 : W 0)
    (hcover : ∀ (i : ℕ) (w : W i) (cs : List R), far i w → good i w ⊆ E (enc ⟨i, w⟩ cs))
    (hfar0 : far 0 w0) (n : ℕ) {bad : (D → R) → Bool}
    (hbad : ∀ H : D → R, bad H = true →
      ¬ sigFar far (honestStrategy (sigFold fold) ⟨0, w0⟩
          (fsChain enc (honestStrategy (sigFold fold) ⟨0, w0⟩) H n []))) :
    winProb bad ≤ ((n : ℝ) * (b : ℝ)) / (Fintype.card R : ℝ) :=
  chain_far_survival_idx_strategy hidx enc E hE
    (honestStrategy (sigFold fold) ⟨0, w0⟩) hcover hfar0 n
    (fun H hH =>
      ⟨honest_foldConsistentAlong enc (sigFold fold) ⟨0, w0⟩ H n [], hbad H hH⟩)

end Indexed

/-! ## §5 — the distance-graded good-set cap: the per-layer `b`, PROVEN (new over `FriFoldArity`). -/

section UD

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {n : ℕ} (S : FriSetupK F ι κ n)

open Classical in
/-- The `d`-graded good-challenge set of `f`: challenges folding `f` to something `d`-close to the
folded code. By-definition — which is admissible ONLY because `goodδ_card_lt` PROVES its cap for
far words (contrast §7's cap-less trap). At `d = 0` it is `FriFoldArity`'s good set. -/
noncomputable def goodδ (d : ℕ) (f : ι → F) : Finset F :=
  Finset.univ.filter fun α => closeN S.C' d (Fold S.geom α f)

theorem mem_goodδ {d : ℕ} {f : ι → F} {α : F} :
    α ∈ goodδ S d f ↔ closeN S.C' d (Fold S.geom α f) := by
  simp [goodδ]

/-- **⚑ THE DISTANCE-GRADED CAP** — the per-layer `b` of the unique-decoding radius schedule. A
word that is NOT `n²·d`-close to `C` has FEWER THAN `n` challenges folding it `d`-close to `C'`:
the cardinality contrapositive of `fold_close_of_arity_challenges`, generalizing
`FriFoldArity.good_challenge_card_lt` from `d = 0` to every `d`. This is what makes the schedule
`farᵢ = ¬ closeN Cᵢ (n²·dᵢ₊₁)` a real radius LADDER: each layer's good set is capped at `n − 1`
regardless of `d`, so the survival bound stays `rounds·(n−1)/|F|` all the way down. -/
theorem goodδ_card_lt {d : ℕ} {f : ι → F} (hf : ¬ closeN S.C (n ^ 2 * d) f) :
    (goodδ S d f).card < n := by
  by_contra hle
  rw [not_lt] at hle
  have hcard : Fintype.card (Fin n) ≤ Fintype.card (goodδ S d f) := by
    simpa [Fintype.card_fin, Fintype.card_coe] using hle
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine hf (fold_close_of_arity_challenges S (α := fun i => (e i : F)) ?_ ?_)
  · intro a b hab
    exact e.injective (Subtype.ext hab)
  · intro i
    exact (mem_goodδ S).1 (e i).2

end UD

/-! ## §6 — the instance FIRES at the deployed arity: `friSetupK8`, far word `f0`, cap `7`.

One layer only — the honest report of why is in the module header (no welded setup TOWER exists
in-tree; `friSetupK8`'s folded domain `|κ| = 2` cannot take a second arity-8 step). -/

section K8

instance : NeZero babyBearP := ⟨by norm_num⟩

/-- The layer carriers at `friSetupK8`: the domain words, the folded words, then trivial. -/
def W8 : ℕ → Type
  | 0 => Fin 16 → BabyBear
  | 1 => Fin 2 → BabyBear
  | _ + 2 => PUnit

/-- The radius schedule at `d = 0`: layer 0 = not a domain codeword, layer 1 = not a folded
codeword, then trivially satisfied. -/
def far8 : ∀ i, W8 i → Prop
  | 0 => fun f => f ∉ friSetupK8.C
  | 1 => fun g => g ∉ friSetupK8.C'
  | _ + 2 => fun _ => True

/-- The per-layer good sets: the `d = 0` graded set at layer 0, empty afterwards. -/
noncomputable def good8 : ∀ i, W8 i → Finset BabyBear
  | 0 => fun f => goodδ friSetupK8 0 f
  | 1 => fun _ => ∅
  | _ + 2 => fun _ => ∅

/-- The per-layer fold: the deployed arity-8 `Fold` at layer 0, trivial afterwards. -/
noncomputable def fold8 : ∀ i, W8 i → BabyBear → W8 (i + 1)
  | 0 => fun f r => Fold friSetupK8.geom r f
  | 1 => fun _ _ => PUnit.unit
  | _ + 2 => fun _ _ => PUnit.unit

/-- The query-point encoding: layer-0 words are the point; later layers collapse. (The deployed
`enc` is a Merkle cap; injectivity-on-far-words is all a cover needs, and here it is literal.) -/
def enc8 : (Σ i, W8 i) → List BabyBear → Option (Fin 16 → BabyBear) :=
  fun w _ => match w with
    | ⟨0, f⟩ => some f
    | ⟨1, _⟩ => none
    | ⟨_ + 2, _⟩ => none

open Classical in
/-- The bad-set cover: the graded good set at far layer-0 words, empty elsewhere. -/
noncomputable def E8 : Option (Fin 16 → BabyBear) → Finset BabyBear
  | some f => if f ∈ friSetupK8.C then ∅ else goodδ friSetupK8 0 f
  | none => ∅

/-- **A genuine `ChainStepIdx` instance at the deployed arity-8 setup.** The layer-0 step is real
content: a non-codeword folded at a challenge outside its (capped, §5) good set folds OUTSIDE the
folded code. -/
theorem chainStepIdx8 : ChainStepIdx far8 good8 fold8 := by
  intro i w r hfar hr
  cases i with
  | zero =>
      intro hmem
      exact hr ((mem_goodδ friSetupK8).mpr (closeN_zero_iff_mem.mpr hmem))
  | succ j =>
      cases j with
      | zero => trivial
      | succ k => trivial

/-- The cover cap: every point's bad set has at most `7 = n − 1` elements — `goodδ_card_lt` at
the far branch (this is the PROVEN external cap the §7 trap cannot supply). -/
theorem E8_card_le : ∀ d, (E8 d).card ≤ 7 := by
  intro d
  cases d with
  | none => simp [E8]
  | some f =>
      simp only [E8]
      split_ifs with hf
      · simp
      · have hlt : (goodδ friSetupK8 0 f).card < 8 :=
          goodδ_card_lt friSetupK8 (d := 0) (fun h => hf (closeN_zero_iff_mem.mp h))
        omega

/-- The far-conditional cover: at far layer-0 words the cover is the good set itself; later
layers' good sets are empty. -/
theorem E8_cover : ∀ (i : ℕ) (w : W8 i) (cs : List BabyBear),
    far8 i w → good8 i w ⊆ E8 (enc8 ⟨i, w⟩ cs) := by
  intro i w cs hfar
  cases i with
  | zero =>
      show goodδ friSetupK8 0 w ⊆ E8 (some w)
      have hf : w ∉ friSetupK8.C := hfar
      simp only [E8]
      split_ifs with h
      · exact absurd h hf
      · exact subset_rfl
  | succ j =>
      cases j with
      | zero => exact Finset.empty_subset _
      | succ k => exact Finset.empty_subset _

open Classical in
/-- **⚑ NON-VACUITY — the composed theorem FIRES on the deployed shape.** At `friSetupK8` from the
PROVEN far word `f0` (`f0_not_mem`), one FS round: the probability that the derived challenge
folds `f0` INTO the folded code is at most `7/|BabyBear|`. Every hypothesis of
`chain_far_survival_idx` is discharged concretely (`chainStepIdx8`, `E8_card_le`, `E8_cover`,
`f0_not_mem`) — the bound is the theorem's, not an axiom's. -/
theorem k8_chain_far_survival :
    winProb (fun H : Option (Fin 16 → BabyBear) → BabyBear =>
        decide (Fold friSetupK8.geom (H (some f0)) f0 ∈ friSetupK8.C'))
      ≤ (7 : ℝ) / (Fintype.card BabyBear : ℝ) := by
  refine le_trans
    (chain_far_survival_idx (W := W8) chainStepIdx8 enc8 E8 E8_card_le f0 E8_cover
      f0_not_mem 1 ?_)
    (le_of_eq (by norm_num))
  intro H hH hfar
  exact hfar (of_decide_eq_true hH)

/-- The fired bound is GENUINELY nontrivial: `7/|BabyBear| < 1` (indeed `< 2⁻²⁷`; contrast the §7
trap, whose "bound" is provably `≥ 1`). -/
theorem k8_bound_lt_one : (7 : ℝ) / (Fintype.card BabyBear : ℝ) < 1 := by
  rw [ZMod.card]
  norm_num

/-! ### §6.1 — the STRATEGY-generic bound fires at a prover that is NOT the honest one.

`k8_chain_far_survival` fires the honest instance. The generalization is only worth something if
it also fires at a strategy the honest one cannot express — otherwise `FoldConsistentAlong`
would just be a disguised way of saying "S = honestStrategy". It is not: fold-consistency is
PATH-LOCAL, so a prover is free to behave arbitrarily off the walked path. -/

/-- **A NON-HONEST, path-consistent prover at the deployed arity-8 shape.** On prefixes of length
≤ 1 — the entire 1-round FS path — it commits what the honest fold commits; on longer prefixes,
where the honest prover would sit at layer ≥ 2, it commits the layer-0 word again. Nothing in
`Strategy` forbids that, and nothing in `FoldConsistentAlong` at `n = 1` sees it. -/
noncomputable def offpathS : Strategy BabyBear (Σ i, W8 i) :=
  fun cs => if cs.length ≤ 1 then honestStrategy (sigFold fold8) ⟨0, f0⟩ cs else ⟨0, f0⟩

/-- **It really is a different strategy**: at a 2-challenge prefix the honest prover is at layer
2 (`honest_sig_layer`) and `offpathS` is at layer 0. So the strategy-generic theorem is NOT the
honest theorem in disguise. -/
theorem offpathS_ne_honest : offpathS ≠ honestStrategy (sigFold fold8) ⟨0, f0⟩ := by
  intro h
  have hfst : (offpathS [0, 0]).1
      = (honestStrategy (sigFold fold8) ⟨0, f0⟩ [(0 : BabyBear), 0]).1 :=
    congrArg Sigma.fst (congrFun h [0, 0])
  have h2 : (offpathS [0, 0]).1 = 2 := hfst.trans (honest_sig_layer fold8 f0 _)
  simp [offpathS] at h2

/-- `offpathS` IS fold-consistent along the 1-round path (it agrees with the honest fold there),
under every oracle — so the gate admits it. -/
theorem offpathS_consistent (H : Option (Fin 16 → BabyBear) → BabyBear) :
    FoldConsistentAlong enc8 offpathS (sigFold fold8) H 1 [] := by
  rw [foldConsistentAlong_succ]
  refine ⟨?_, foldConsistentAlong_zero _ _ _ _ _⟩
  simp [offpathS]

open Classical in
/-- **⚑ NON-VACUITY OF THE GENERALIZATION — the strategy-generic bound fires at a NON-honest
prover, at the deployed arity-8 shape, with a nontrivial bound.** Same conclusion and same
`7/|BabyBear|` as `k8_chain_far_survival`, but obtained for `offpathS`, which
`offpathS_ne_honest` proves is not the honest strategy. The randomness is genuine (uniform `H`)
and the prover is now quantified, not fixed. -/
theorem k8_chain_far_survival_offpath :
    winProb (fun H : Option (Fin 16 → BabyBear) → BabyBear =>
        decide (Fold friSetupK8.geom (H (some f0)) f0 ∈ friSetupK8.C'))
      ≤ (7 : ℝ) / (Fintype.card BabyBear : ℝ) := by
  refine le_trans
    (chain_far_survival_idx_strategy (W := W8) chainStepIdx8 enc8 E8 E8_card_le offpathS
      E8_cover f0_not_mem 1 ?_)
    (le_of_eq (by norm_num))
  intro H hH
  refine ⟨offpathS_consistent H, ?_⟩
  intro hfar
  exact hfar (of_decide_eq_true hH)

end K8

/-! ## §7 — the falsifiers: the un-generalized and the vacuous forms REFUTED. -/

section Falsifiers

/-- A staircase family: at layer `i` the word must READ `i`. Every layer's radius is its own. -/
theorem stair_chainStepIdx :
    ChainStepIdx (W := fun _ => ℕ) (R := Bool)
      (fun i w => w = i) (fun _ _ => (∅ : Finset Bool)) (fun _ w _ => w + 1) := by
  intro i w r hw _
  simpa using hw

/-- **FALSIFIER — the fixed-radius collapse is FALSE.** Take the staircase family (where
`ChainStepIdx` HOLDS, `stair_chainStepIdx`) and collapse the schedule to layer 0's radius for
every layer — the un-generalized fixed-`C` reading, one `far` for all rounds. The very first fold
refutes it: `far 0` holds, the good set is empty, and the folded word fails `far`. The per-layer
schedule is LOAD-BEARING; the deployed shrinking-domain fold cannot be priced by reusing one
layer's radius. (What survives of the fixed-`C` machinery is the `Σ i, W i` packaging —
`chainStepIdx_iff_sigma` — where the "radius" internalizes the layer.) -/
theorem fixed_radius_collapse_refuted :
    ¬ ChainStep (R := Bool) (fun w : ℕ => w = 0) (fun _ => (∅ : Finset Bool))
        (fun w _ => w + 1) := by
  intro h
  have h1 : (0 : ℕ) + 1 = 0 := h 0 true rfl (by simp)
  omega

open Classical in
/-- **THE VACUITY TRAP, exhibited.** Define the good set to be WHATEVER makes the step true —
`goodSet w := {r | ¬ far (fold w r)}` — and `ChainStep` holds for EVERY `far` and EVERY `fold`,
including folds that destroy farness outright. A `ChainStep` obtained this way carries ZERO
per-fold content; `goodSet_by_definition_no_content` prices the consequence. -/
theorem goodSet_by_definition_is_free {R C : Type} [Fintype R] (far : C → Prop)
    (fold : C → R → C) :
    ChainStep far (fun w => Finset.univ.filter fun r => ¬ far (fold w r)) fold := by
  intro w r hfar hr
  by_contra hbad
  exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hbad⟩)

/-- At the farness-destroying fold (`far = (· = 0)`, `fold = (· + 1)`) the by-definition good set
is ALL of `R`: no fold result is ever far, so every challenge is "good". -/
theorem goodSet_by_definition_is_univ (w : ℕ) :
    (Finset.univ.filter fun _r : Bool => ¬ ((w + 1 : ℕ) = 0)) = (Finset.univ : Finset Bool) := by
  simp

/-- **FALSIFIER — the vacuous form yields NO probability content.** For the trap instance, any
`(E, b)` satisfying `chain_far_survival`'s cover + cap hypotheses (even only far-conditionally)
is forced to `b ≥ |R|`, so for every `n ≥ 1` the "bound" `n·b/|R|` is `≥ 1` — trivially true of
any probability. A goodSet defined to make the theorem true can never beat the trivial bound; the
content of a survival bound is exactly an EXTERNALLY-PROVEN cap (`goodδ_card_lt`, whose §6
instance yields `7/|BabyBear| < 1`, `k8_bound_lt_one`). -/
theorem goodSet_by_definition_no_content {D : Type} (enc : ℕ → List Bool → D)
    (E : D → Finset Bool) (b : ℕ)
    (hcover : ∀ (w : ℕ) (cs : List Bool), w = 0 →
      (Finset.univ.filter fun _r : Bool => ¬ ((w + 1 : ℕ) = 0)) ⊆ E (enc w cs))
    (hE : ∀ d, (E d).card ≤ b) :
    2 ≤ b ∧ ∀ n : ℕ, 1 ≤ n → (1 : ℝ) ≤ ((n : ℝ) * (b : ℝ)) / (Fintype.card Bool : ℝ) := by
  have h2 : 2 ≤ b := by
    have hsub := hcover 0 [] rfl
    rw [goodSet_by_definition_is_univ] at hsub
    have hcards := (Finset.card_le_card hsub).trans (hE (enc 0 []))
    simpa using hcards
  refine ⟨h2, fun n hn => ?_⟩
  have hnb : (2 : ℝ) ≤ (n : ℝ) * (b : ℝ) := by
    have : 1 * 2 ≤ n * b := Nat.mul_le_mul hn h2
    exact_mod_cast by simpa using this
  rw [Fintype.card_bool]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (2 : ℕ))]
  simpa using hnb

/-- At the deployed shape a MEMBER word's good set is EVERYTHING: every challenge folds a
codeword into the folded code (`fold_complete`), witnessed at `fHon8`. -/
theorem fHon8_goodδ_univ : goodδ friSetupK8 0 fHon8 = Finset.univ := by
  ext α
  simp only [mem_goodδ, Finset.mem_univ, iff_true]
  exact closeN_zero_iff_mem.mpr (fHon8_fold_complete α)

/-- **FALSIFIER — the landed UNCONDITIONAL cover is trivial at the deployed shape.** The landed
`honest_chain_far` (`FriAdversaryObject:196`) demands `goodSet w ⊆ E (enc w cs)` for ALL `w`. At
`friSetupK8` the member word `fHon8` has good set = ALL of `BabyBear` (`fHon8_goodδ_univ`), so
any unconditional cover forces the cap `b ≥ |BabyBear|` — and the survival bound `n·b/|R| ≥ n`
says nothing. This is why §3 weakened the cover to far-conditional: with it, §6 gets `b = 7`. -/
theorem unconditional_cover_trivial_at_deployed {D : Type}
    (enc : (Fin 16 → BabyBear) → List BabyBear → D) (E : D → Finset BabyBear) (b : ℕ)
    (hcover : ∀ (w : Fin 16 → BabyBear) (cs : List BabyBear),
      goodδ friSetupK8 0 w ⊆ E (enc w cs))
    (hE : ∀ d, (E d).card ≤ b) :
    Fintype.card BabyBear ≤ b := by
  have hsub := hcover fHon8 []
  rw [fHon8_goodδ_univ] at hsub
  have := (Finset.card_le_card hsub).trans (hE (enc fHon8 []))
  simpa using this

end Falsifiers

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  hit_cond,
  hit_bound,
  hitWin_fsRun_true_iff,
  honest_chain_far_of_farCover,
  chain_far_survival_strategy,
  chain_far_survival_strategy_gated,
  chain_far_survival,
  chain_far_survival_prob,
  canary_chainStep,
  codewordCommit_escapes,
  codewordCommit_escape_prob_one,
  codewordCommit_not_foldConsistent,
  codewordCommit_gated_bound,
  consistencyFreeSurvival_false,
  chainStepIdx_iff_sigma,
  honest_sig_layer,
  terminal_layer,
  chain_far_survival_idx_strategy,
  chain_far_survival_idx,
  goodδ_card_lt,
  chainStepIdx8,
  E8_card_le,
  k8_chain_far_survival,
  k8_bound_lt_one,
  offpathS_ne_honest,
  offpathS_consistent,
  k8_chain_far_survival_offpath,
  stair_chainStepIdx,
  fixed_radius_collapse_refuted,
  goodSet_by_definition_is_free,
  goodSet_by_definition_no_content,
  fHon8_goodδ_univ,
  unconditional_cover_trivial_at_deployed
]

end Dregg2.Circuit.FriChainStepIdx
