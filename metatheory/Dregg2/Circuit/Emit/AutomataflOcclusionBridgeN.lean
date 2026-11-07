/-
# Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN — the OCCLUSION BRIDGE off `Satisfied2`, ARBITRARY n.

`AutomataflOcclusionBridge` discharges the hypotheses of `AutomataflOcclusionGeneric`'s
`occ_eq_occluded_vert/horiz` from `Satisfied2 automataflResolveDesc` — but only at the frozen `NN = 2`,
where a rook line has no strictly-interior cell and both sides are constantly `false`. Every extraction
there leaned on the `{0,1}` coordinate split (`coord01_of_sat`, the 2-selector `oneHot_of_sat`, the
`hk2 : k = 0 ∨ k = 1` case analyses) that does not survive `n > 2`.

This file redoes the SAT-side extraction n-GENERICALLY, off `Satisfied2 (automataflResolveDescN n)`,
using the `AutomataflCoord` foundation (`oneHotN_of_sat`, `coordN_of_sat`, `dot_oneHot`,
`headToExpr_eval`, the `evalH_*` combinators) as the replacements for the 2-selector primitives, and
the `AutomataflOcclusionGeneric` PURE math (`segVal_eq`, `msum_ge_one_iff`, `occ_eq_occluded_*`,
`mem_interior_*`) unchanged. The line reads, endpoint one-hots, passable mask, seg/msum thresholds are
all extracted from the emitted `NGen.*Head` gates at ARBITRARY `n`.

The board-size window `hwin : COORD_RBITS n` no-wrap and `hsq : (n−1)^2 ≤ 511` (the 9-bit forced_ge0
range) are EXPLICIT hypotheses, discharged at any realistic board size; at `n = 2/3/11` they hold.

## Axiom hygiene
`#assert_axioms` subset `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`, no
assumed arithmetization hypothesis (the board-size windows are explicit board-arithmetic inequalities).
-/
import Dregg2.Circuit.Emit.AutomataflResolveRefine
import Dregg2.Circuit.Emit.AutomataflCoord
import Dregg2.Circuit.Emit.AutomataflOcclusionGeneric
import Dregg2.Circuit.Emit.AutomataflResolveMembership

namespace Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN

open Dregg2.Circuit.Emit.AutomataflResolveEmit
open Dregg2.Circuit.Emit.AutomataflResolveMembership
open Dregg2.Circuit.Emit.AutomataflCoord
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Circuit.Emit.AutomataflStepRefine
  (Canon canon_zero canon_one canon_two canon_three eq_of_modEq_canon eq_of_modEq_small
   eq_of_modEq_win bin_of_gate StepCanon canon_loc codeToParticle)
open Dregg2.Circuit.Emit.AutomataflResolveRefine (forcedGe0_wide sq1d_pure)
open Dregg2.Games.Automatafl (Board Coord Particle Move occluded interior)

set_option autoImplicit false
set_option maxHeartbeats 4000000

section
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace}

/-! ## §A — n-generic boolean/small-window gate primitives, off an ARBITRARY descriptor `d`.

These are the direct ports of `AutomataflResolveRefine`'s NN=2 extractors, keyed on `ngate`/`ngateH`
(the descriptor-generic single-row extraction from `AutomataflCoord`) instead of the `rgate` bound to
the frozen descriptor. The `evalH`-`rfl` shapes are structure-only, so they hold at symbolic `n`. -/

/-- **The 9-bit `forced_ge0` extractor, off `d`.** `ib = [val ≥ 1]` for `val` in a small window. -/
theorem ge0_9N_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (val ib bit0 : Nat)
    (hib : cg (gBin ib) ∈ d.constraints)
    (hbit : ∀ k, k < 9 → cg (gBin (bit0 + k)) ∈ d.constraints)
    (hrecomp : cgH ((List.range 9).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
                 (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib)) ∈ d.constraints)
    (hlo : -999 ≤ (envAt t i).loc val) (hhi : (envAt t i).loc val ≤ 999) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 → 1 ≤ (envAt t i).loc val)
      ∧ ((envAt t i).loc ib = 0 → (envAt t i).loc val ≤ 0) := by
  set e := envAt t i with he
  have hibB : e.loc ib = 0 ∨ e.loc ib = 1 :=
    bin_of_gate (ngate hsat i hi hib) (canon_loc hc i _)
  have B : ∀ k : Nat, k < 9 → (0 ≤ e.loc (bit0 + k) ∧ e.loc (bit0 + k) ≤ 1) := by
    intro k hk
    have hb : e.loc (bit0 + k) = 0 ∨ e.loc (bit0 + k) = 1 :=
      bin_of_gate (ngate hsat i hi (hbit k hk)) (canon_loc hc i _)
    rcases hb with h | h <;> omega
  have h0 := B 0 (by norm_num)
  have h1 := B 1 (by norm_num)
  have h2 := B 2 (by norm_num)
  have h3 := B 3 (by norm_num)
  have h4 := B 4 (by norm_num)
  have h5 := B 5 (by norm_num)
  have h6 := B 6 (by norm_num)
  have h7 := B 7 (by norm_num)
  have h8 := B 8 (by norm_num)
  set S : ℤ := e.loc (bit0 + 0) + 2 * e.loc (bit0 + 1) + 4 * e.loc (bit0 + 2)
    + 8 * e.loc (bit0 + 3) + 16 * e.loc (bit0 + 4) + 32 * e.loc (bit0 + 5)
    + 64 * e.loc (bit0 + 6) + 128 * e.loc (bit0 + 7) + 256 * e.loc (bit0 + 8) with hS
  have hS0 : 0 ≤ S := by rw [hS]; omega
  have hS1 : S ≤ 511 := by rw [hS]; omega
  have hg := ngateH hsat i hi hrecomp
  have hE : (headToExpr ((List.range 9).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
        (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))).eval e.loc
      = 2 * (e.loc ib * e.loc val) + (-2) * e.loc ib + e.loc ib + (-1) * e.loc val
        + (-1) * e.loc (bit0 + 0) + (-2) * e.loc (bit0 + 1) + (-4) * e.loc (bit0 + 2)
        + (-8) * e.loc (bit0 + 3) + (-16) * e.loc (bit0 + 4) + (-32) * e.loc (bit0 + 5)
        + (-64) * e.loc (bit0 + 6) + (-128) * e.loc (bit0 + 7)
        + (-256) * e.loc (bit0 + 8) := by canon_head_eval [headToExpr, forcedGe0Term]
  rw [hE] at hg
  have hmod : (2 * e.loc ib * (e.loc val - 1) + e.loc ib - (e.loc val - 1) - 1)
      ≡ S [ZMOD 2013265921] := by
    refine (gate_modEq_iff ?_).mp hg
    rw [hS]; ring
  obtain ⟨hp, hn⟩ := forcedGe0_wide hibB hS0 hS1 hmod (by omega) (by omega)
  exact ⟨hibB, fun h => by have := hp h; omega, fun h => by have := hn h; omega⟩

/-- **The `eq == 1 − neq` pin, off `d`.** -/
theorem eqPinN_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (eqCol neqCol : Nat)
    (hpin : cgH (((Head.lin 1 eqCol).addLin 1 neqCol).addConst (-1)) ∈ d.constraints)
    (hneq : (envAt t i).loc neqCol = 0 ∨ (envAt t i).loc neqCol = 1) :
    (envAt t i).loc eqCol = 1 - (envAt t i).loc neqCol := by
  set e := envAt t i with he
  have hg := ngateH hsat i hi hpin
  have hE : (headToExpr (((Head.lin 1 eqCol).addLin 1 neqCol).addConst (-1))).eval e.loc
      = e.loc eqCol + e.loc neqCol + (-1) := by canon_head_eval [headToExpr]
  rw [hE] at hg
  have hmod := (gate_modEq_iff (x := e.loc eqCol + e.loc neqCol + -1)
    (a := e.loc eqCol) (b := 1 - e.loc neqCol) (by ring)).mp hg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ hmod
  rcases hneq with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩

/-- **The `iv`-gated selection `out = g·s₀ + (1−g)·s₁`, off `d`** — for BOOLEAN `g, s₀, s₁`. -/
theorem gatedSelN_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (out g s0 s1 : Nat)
    (hgate : cgH ((((Head.lin 1 out).addProd (-1) [g, s0]).addLin (-1) s1).addProd 1 [g, s1])
               ∈ d.constraints)
    (hgb : (envAt t i).loc g = 0 ∨ (envAt t i).loc g = 1)
    (h0b : (envAt t i).loc s0 = 0 ∨ (envAt t i).loc s0 = 1)
    (h1b : (envAt t i).loc s1 = 0 ∨ (envAt t i).loc s1 = 1) :
    (envAt t i).loc out
      = (envAt t i).loc g * (envAt t i).loc s0
        + (1 - (envAt t i).loc g) * (envAt t i).loc s1 := by
  set e := envAt t i with he
  have hgt := ngateH hsat i hi hgate
  have hE : (headToExpr ((((Head.lin 1 out).addProd (-1) [g, s0]).addLin (-1) s1).addProd 1
        [g, s1])).eval e.loc
      = e.loc out + (-1) * (e.loc g * e.loc s0) + (-1) * e.loc s1
        + e.loc g * e.loc s1 := by canon_head_eval [headToExpr]
  rw [hE] at hgt
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hgt)
  rcases hgb with a | a <;> rcases h0b with b1 | b1 <;> rcases h1b with c | c <;>
    rw [a, b1, c] <;> exact ⟨by norm_num, by norm_num⟩

/-! ## §B — The novel fold-value lemmas: `evalH` of the `n`-wide occlusion heads.

`lineHead` / `segHead` / `msumHead` fold over `List.range n` (symbolic), so their `headToExpr` does
NOT reduce by `rfl`. These compute their clean `evalH` semantic value via the `AutomataflCoord`
`evalH_*` combinator laws (mirroring `evalH_autoPinHead`), so the extraction can proceed at any `n`. -/

/-- Pushing a per-element negation out of a list sum. -/
theorem neg_sum (L : List Nat) (f : Nat → ℤ) :
    (L.map (fun x => -(f x))).sum = -((L.map f).sum) := by
  induction L with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- `evalH` of the emitted `lineHead`: the two gated scans, uncollapsed. -/
theorem evalH_lineHead (a : Nat → ℤ) (n b o k : Nat) :
    evalH (NGen.lineHead n b o k) a
      = a (NGen.cLine n o k)
        + ((List.range n).map (fun x =>
            (-1) * (a (NGen.cIv n o) * a (NGen.cSelCol n b x) * a (NGen.old n (k * n + x))))).sum
        + ((List.range n).map (fun y =>
            (-1) * (a (NGen.cSelRow n b y) * a (NGen.old n (y * n + k)))
            + a (NGen.cIv n o) * a (NGen.cSelRow n b y) * a (NGen.old n (y * n + k)))).sum := by
  have hstep_outer : ∀ (h : Head) (y : Nat),
      evalH ((h.addProd (-1) [NGen.cSelRow n b y, NGen.old n (y * n + k)]).addProd 1
              [NGen.cIv n o, NGen.cSelRow n b y, NGen.old n (y * n + k)]) a
        = evalH h a + ((-1) * (a (NGen.cSelRow n b y) * a (NGen.old n (y * n + k)))
            + a (NGen.cIv n o) * a (NGen.cSelRow n b y) * a (NGen.old n (y * n + k))) := by
    intro h y
    rw [evalH_addProd, evalH_addProd]
    simp only [varsVal, one_mul, List.foldl_cons, List.foldl_nil]
    ring
  have hstep_inner : ∀ (h : Head) (x : Nat),
      evalH (h.addProd (-1) [NGen.cIv n o, NGen.cSelCol n b x, NGen.old n (k * n + x)]) a
        = evalH h a + (-1) * (a (NGen.cIv n o) * a (NGen.cSelCol n b x) * a (NGen.old n (k * n + x))) := by
    intro h x
    rw [evalH_addProd]
    simp only [varsVal, one_mul, List.foldl_cons, List.foldl_nil]
  rw [NGen.lineHead]
  rw [evalH_foldl_step a _ (List.range n) _ _ hstep_outer]
  rw [evalH_foldl_step a (Head.lin 1 (NGen.cLine n o k)) (List.range n) _ _ hstep_inner]
  rw [evalH_lin, one_mul]

/-- `evalH` of the emitted `segHead`: `cSeg[k]` minus the strictly-between double fold `segVal`. -/
theorem evalH_segHead (a : Nat → ℤ) (n o k : Nat) :
    evalH (NGen.segHead n o k) a
      = a (NGen.cSeg n o k)
        - segVal (fun j => a (NGen.cEfrom n o j)) (fun j => a (NGen.cEto n o j)) n k := by
  have hstep_inner : ∀ (j1 : Nat) (h : Head) (j2 : Nat),
      evalH ((h.addProd (-1) [NGen.cEfrom n o j1, NGen.cEto n o j2]).addProd (-1)
              [NGen.cEto n o j1, NGen.cEfrom n o j2]) a
        = evalH h a + (-(a (NGen.cEfrom n o j1) * a (NGen.cEto n o j2)
            + a (NGen.cEto n o j1) * a (NGen.cEfrom n o j2))) := by
    intro j1 h j2
    rw [evalH_addProd, evalH_addProd]
    simp only [varsVal, one_mul, List.foldl_cons, List.foldl_nil]
    ring
  have hstep_outer : ∀ (h : Head) (j1 : Nat),
      evalH (((List.range n).filter (fun j2 => k < j2)).foldl (fun h2 j2 =>
              (h2.addProd (-1) [NGen.cEfrom n o j1, NGen.cEto n o j2]).addProd (-1)
                [NGen.cEto n o j1, NGen.cEfrom n o j2]) h) a
        = evalH h a
          + (-(((List.range n).filter (fun j2 => decide (k < j2))).map (fun j2 =>
              a (NGen.cEfrom n o j1) * a (NGen.cEto n o j2)
              + a (NGen.cEto n o j1) * a (NGen.cEfrom n o j2))).sum) := by
    intro h j1
    rw [evalH_foldl_step a h _ _ _ (hstep_inner j1)]
    congr 1
    exact neg_sum _ _
  have hseg_eq : segVal (fun j => a (NGen.cEfrom n o j)) (fun j => a (NGen.cEto n o j)) n k
      = ((List.range k).map (fun j1 =>
          (((List.range n).filter (fun j2 => decide (k < j2))).map (fun j2 =>
            a (NGen.cEfrom n o j1) * a (NGen.cEto n o j2)
            + a (NGen.cEto n o j1) * a (NGen.cEfrom n o j2))).sum)).sum := rfl
  rw [NGen.segHead]
  rw [evalH_foldl_step a (Head.lin 1 (NGen.cSeg n o k)) (List.range k) _ _ hstep_outer]
  rw [evalH_lin, one_mul, hseg_eq,
    neg_sum (List.range k) (fun j1 => (((List.range n).filter (fun j2 => decide (k < j2))).map
      (fun j2 => a (NGen.cEfrom n o j1) * a (NGen.cEto n o j2)
        + a (NGen.cEto n o j1) * a (NGen.cEfrom n o j2))).sum)]
  ring

/-- `evalH` of the emitted `msumHead`: `cMsum` minus the masked interior sum `msumVal`. -/
theorem evalH_msumHead (a : Nat → ℤ) (n o : Nat) :
    evalH (NGen.msumHead n o) a
      = a (NGen.cMsum n o)
        - msumVal (fun k => a (NGen.cSeg n o k)) (fun k => a (NGen.cOsrc n o k))
            (fun k => a (NGen.cLine n o k)) n := by
  have hstep : ∀ (h : Head) (k : Nat),
      evalH ((h.addProd (-1) [NGen.cSeg n o k, NGen.cLine n o k]).addProd 1
              [NGen.cSeg n o k, NGen.cOsrc n o k, NGen.cLine n o k]) a
        = evalH h a + (-(a (NGen.cSeg n o k) * a (NGen.cLine n o k)
            - a (NGen.cSeg n o k) * a (NGen.cOsrc n o k) * a (NGen.cLine n o k))) := by
    intro h k
    rw [evalH_addProd, evalH_addProd]
    simp only [varsVal, one_mul, List.foldl_cons, List.foldl_nil]
    ring
  have hmsum_eq : msumVal (fun k => a (NGen.cSeg n o k)) (fun k => a (NGen.cOsrc n o k))
        (fun k => a (NGen.cLine n o k)) n
      = ((List.range n).map (fun k => a (NGen.cSeg n o k) * a (NGen.cLine n o k)
          - a (NGen.cSeg n o k) * a (NGen.cOsrc n o k) * a (NGen.cLine n o k))).sum := rfl
  rw [NGen.msumHead]
  rw [evalH_foldl_step a (Head.lin 1 (NGen.cMsum n o)) (List.range n) _ _ hstep]
  rw [evalH_lin, one_mul, hmsum_eq,
    neg_sum (List.range n) (fun k => a (NGen.cSeg n o k) * a (NGen.cLine n o k)
      - a (NGen.cSeg n o k) * a (NGen.cOsrc n o k) * a (NGen.cLine n o k))]
  ring

/-- `evalH` of the emitted INCLUSIVE `msumInclHead`: `cMsumIncl[w]` minus the exclusive `cMsum[o]`
minus the destination endpoint fold `Σ_k eto[k]·((1 − osrc[k])·line[k])` — the exclusive masked sum
plus the one extra endpoint term, UNCOLLAPSED (the `eto` one-hot collapses it later, in the
`blockedB` bridge). The `blockedB`-analog of `evalH_msumHead`; the fold body matches `msumInclVal`'s
endpoint summand exactly, so the gate pins `cMsumIncl` to `msumInclVal`. -/
theorem evalH_msumInclHead (a : Nat → ℤ) (n w o : Nat) :
    evalH (NGen.msumInclHead n w o) a
      = a (NGen.cMsumIncl n w) - a (NGen.cMsum n o)
        - ((List.range n).map (fun k =>
            a (NGen.cEto n o k) * ((1 - a (NGen.cOsrc n o k)) * a (NGen.cLine n o k)))).sum := by
  have hstep : ∀ (h : Head) (k : Nat),
      evalH ((h.addProd (-1) [NGen.cEto n o k, NGen.cLine n o k]).addProd 1
              [NGen.cEto n o k, NGen.cOsrc n o k, NGen.cLine n o k]) a
        = evalH h a
          + (-(a (NGen.cEto n o k) * ((1 - a (NGen.cOsrc n o k)) * a (NGen.cLine n o k)))) := by
    intro h k
    rw [evalH_addProd, evalH_addProd]
    simp only [varsVal, List.foldl_cons, List.foldl_nil]
    ring
  rw [NGen.msumInclHead]
  rw [evalH_foldl_step a ((Head.lin 1 (NGen.cMsumIncl n w)).addLin (-1) (NGen.cMsum n o))
      (List.range n) _ _ hstep]
  rw [evalH_addLin, evalH_lin,
    neg_sum (List.range n) (fun k =>
      a (NGen.cEto n o k) * ((1 - a (NGen.cOsrc n o k)) * a (NGen.cLine n o k)))]
  ring

/-! ## §C — `validateOcclusion` family-membership navigators (inline; swarm-safe: my own file).

`validateOcclusion n b o ob` is the left-associative 13-way append P0..P12. `g ∈ Fᵢ → g ∈ spine` is
`(12 − i)` `mem_append_left`s then one `mem_append_right` (none for P0). Combinator navigation inside
each family reuses `AutomataflResolveMembership`'s `mem_oneHot*`/`mem_eqScalar*`. -/

theorem voN_iv_fam {g : VmConstraint2} (n b o ob : Nat)
    (h : g ∈ eqScalarConstraints (NGen.cFx n b) (NGen.cTx n b) (NGen.cIvDsq n o) (NGen.cIvNeq n o)
          (NGen.ivNeqBit n o 0) (NGen.cIv n o)) :
    g ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion, NGen.isVerticalConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (h))))))))))))

theorem voN_line {g : VmConstraint2} (n b o ob k : Nat) (hk : k < n)
    (hg : g = cgH (NGen.lineHead n b o k)) : g ∈ NGen.validateOcclusion n b o ob := by
  subst hg; rw [NGen.validateOcclusion]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ((List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))))))))))))

theorem voN_ety_fam {g : VmConstraint2} (n b o ob : Nat)
    (h : g ∈ oneHotAtCol ((List.range n).map (NGen.cEty n o)) (NGen.cTy n b)) :
    g ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (h)))))))))))

theorem voN_etx_fam {g : VmConstraint2} (n b o ob : Nat)
    (h : g ∈ oneHotAtCol ((List.range n).map (NGen.cEtx n o)) (NGen.cTx n b)) :
    g ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (h))))))))))

theorem voN_efrom {g : VmConstraint2} (n b o ob j : Nat) (hj : j < n)
    (hg : g = cgH (NGen.efromHead n b o j)) : g ∈ NGen.validateOcclusion n b o ob := by
  subst hg; rw [NGen.validateOcclusion]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ((List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))))))))

theorem voN_eto {g : VmConstraint2} (n b o ob j : Nat) (hj : j < n)
    (hg : g = cgH (NGen.etoHead n o j)) : g ∈ NGen.validateOcclusion n b o ob := by
  subst hg; rw [NGen.validateOcclusion]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ((List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))))))))

theorem voN_eqx_fam {g : VmConstraint2} (n b o ob : Nat)
    (h : g ∈ eqScalarConstraints (NGen.cFx n ob) (NGen.cFx n b) (NGen.cEqxDsq n o) (NGen.cEqxNeq n o)
          (NGen.eqxBit n o 0) (NGen.cEqx n o)) :
    g ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (h))))))

theorem voN_eqy_fam {g : VmConstraint2} (n b o ob : Nat)
    (h : g ∈ eqScalarConstraints (NGen.cFy n ob) (NGen.cFy n b) (NGen.cEqyDsq n o) (NGen.cEqyNeq n o)
          (NGen.eqyBit n o 0) (NGen.cEqy n o)) :
    g ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (h)))))

theorem voN_og {g : VmConstraint2} (n b o ob : Nat) (hg : g = cgH (NGen.ogHead n o)) :
    g ∈ NGen.validateOcclusion n b o ob := by
  subst hg; rw [NGen.validateOcclusion]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ((List.mem_singleton.mpr rfl)))))

theorem voN_osrc_fam {g : VmConstraint2} (n b o ob : Nat)
    (h : g ∈ oneHotGatedConstraints ((List.range n).map (NGen.cOsrc n o)) (NGen.cOg n o)
          ((((Head.zero.addProd 1 [NGen.cIv n o, NGen.cFy n ob]).addLin 1 (NGen.cFx n ob)).addProd (-1)
            [NGen.cIv n o, NGen.cFx n ob]))) :
    g ∈ NGen.validateOcclusion n b o ob := by
  rw [NGen.validateOcclusion]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (h)))

theorem vmN_srcRow_fam {g : VmConstraint2} (n b : Nat)
    (h : g ∈ oneHotAtCol (NGen.selRowCols n b) (NGen.cFy n b)) : g ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (h)))

theorem vmN_srcCol_fam {g : VmConstraint2} (n b : Nat)
    (h : g ∈ oneHotAtCol (NGen.selColCols n b) (NGen.cFx n b)) : g ∈ NGen.validateMove n b := by
  rw [NGen.validateMove]
  exact List.mem_append_left _ (List.mem_append_right _ (h))

/-! ### CHUNK-2 additive — the INCLUSIVE-occlusion family `inclOcclusionOne` navigators. The block is
`[ cgH (msumInclHead w o) ] ++ forcedGe0Constraints ((lin 1 cMsumIncl[w]) − 1) cOccIncl[w] occInclBit`
(a `forced_ge0` at the default `RBITS = 9`). These locate the msum head and the three `forced_ge0`
gates, generically in `n w o`. -/

/-- The inclusive masked-sum definition head. -/
theorem voI_msumInclHead (n w o : Nat) :
    cgH (NGen.msumInclHead n w o) ∈ NGen.inclOcclusionOne n w o := by
  rw [NGen.inclOcclusionOne]
  exact List.mem_append_left _ (List.mem_singleton.mpr rfl)

/-- The `cOccIncl` boolean of the inclusive `forced_ge0`. -/
theorem voI_occIncl_ib (n w o : Nat) :
    cg (gBin (NGen.cOccIncl n w)) ∈ NGen.inclOcclusionOne n w o := by
  rw [NGen.inclOcclusionOne]
  exact List.mem_append_right _ (mem_forcedGe0N_ib _ (NGen.cOccIncl n w) (NGen.occInclBit n w 0) RBITS)

/-- The k-th range bit of the inclusive `forced_ge0`. -/
theorem voI_occIncl_bit (n w o k : Nat) (hk : k < RBITS) :
    cg (gBin (NGen.occInclBit n w 0 + k)) ∈ NGen.inclOcclusionOne n w o := by
  rw [NGen.inclOcclusionOne]
  exact List.mem_append_right _
    (mem_forcedGe0N_bit _ (NGen.cOccIncl n w) (NGen.occInclBit n w 0) RBITS k hk)

/-- The recomposition head of the inclusive `forced_ge0`. -/
theorem voI_occIncl_head (n w o : Nat) :
    cgH ((List.range RBITS).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (NGen.occInclBit n w 0 + k))
        (forcedGe0Term ((Head.lin 1 (NGen.cMsumIncl n w)).addConst (-1)) (NGen.cOccIncl n w)))
      ∈ NGen.inclOcclusionOne n w o := by
  rw [NGen.inclOcclusionOne]
  exact List.mem_append_right _
    (mem_forcedGe0N_head ((Head.lin 1 (NGen.cMsumIncl n w)).addConst (-1)) (NGen.cOccIncl n w)
      (NGen.occInclBit n w 0) RBITS)

/-- Lift an `inclOcclusionOne w o` membership to the descriptor, at either piece index `w < 2`
(`o = occBase n w`), via `mem_resolve_of_mem_inclOcclusion` over the 2-way `inclOcclusionConstraints`
append. This is the inclusive twin of the capstone's `occLift`; chunk 3 supplies it to
`occ_iff_blocked_of_sat`'s `hincl`. -/
theorem inclLiftN (n w o : Nat) (hw : w < 2) (ho : o = NGen.occBase n w) {g : VmConstraint2}
    (h : g ∈ NGen.inclOcclusionOne n w o) : g ∈ (automataflResolveDescN n).constraints := by
  apply mem_resolve_of_mem_inclOcclusion
  rw [NGen.inclOcclusionConstraints]
  subst ho; interval_cases w
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ h

end

/-! ## §D — the occlusion extractions, off `Satisfied2 (automataflResolveDescN n)`. -/

section OccN
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- Every OLD board cell of a satisfying, canonical Leg-R trace lies in the particle alphabet. -/
theorem oldAlphabetN (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ∀ c, c < NGen.KK n → ((envAt t i).loc (NGen.old n c) = 0 ∨ (envAt t i).loc (NGen.old n c) = 1
      ∨ (envAt t i).loc (NGen.old n c) = 2 ∨ (envAt t i).loc (NGen.old n c) = 3) := by
  intro c hcK
  exact AutomataflStepRefine.mem4_of_gate
    (ngate hsat i hi (mem_resolve_of_mem_boardRange (br_old n c hcK))) (canon_loc hc i _)

/-- Board cell bounds `0 ≤ old c ≤ 3` from the alphabet. -/
theorem oldBoundN (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (c : Nat) (hcK : c < NGen.KK n) :
    0 ≤ (envAt t i).loc (NGen.old n c) ∧ (envAt t i).loc (NGen.old n c) ≤ 3 := by
  rcases oldAlphabetN n hsat hc i hi c hcK with h | h | h | h <;> rw [h] <;> constructor <;> norm_num

/-- The `oneHotAtCol` read, packaged: forces the selector values into a `OneHotAt` at the pinned
index and the index into `[0, n)`. -/
theorem readOneHotN (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (sel : Nat → Nat) (idxCol : Nat)
    (hmem : ∀ {g : VmConstraint2}, g ∈ oneHotAtCol ((List.range n).map sel) idxCol
              → g ∈ (automataflResolveDescN n).constraints) :
    ∃ af : Nat, af < n ∧ (envAt t i).loc idxCol = (af : ℤ)
      ∧ OneHotAt (fun j => (envAt t i).loc (sel j)) n af :=
  oneHotN_of_sat hsat hc i hi n hn sel idxCol
    (fun j hj => hmem (mem_oneHotAtCol_sel _ _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
    (hmem (mem_oneHotAtCol_sumHead _ _))
    (hmem (mem_oneHotAtCol_idxHead _ _))

/-! ### §D.1 — the `eq_scalar` extractor at ARBITRARY coordinates (replaces `sq1d_pure`/`{0,1}`). -/

/-- A witnessed squared-distance column over two `[0,n)` coordinates is exactly the integer squared
distance — the n-generic `sq1d_pure` (the window `(a−c)² < p` is a board-arithmetic fact). -/
theorem sqDistN_pure {d a c : ℤ} (hd : Canon d) (ha0 : 0 ≤ a) (hc0 : 0 ≤ c)
    (hbnd : (a - c) * (a - c) < 2013265921)
    (h : d + (-1) * (a * a) + 2 * (a * c) + (-1) * (c * c) ≡ 0 [ZMOD 2013265921]) :
    d = (a - c) * (a - c) := by
  have hval : Canon ((a - c) * (a - c)) := ⟨mul_self_nonneg _, hbnd⟩
  exact eq_of_modEq_canon hd hval ((gate_modEq_iff (by ring)).mp h)

/-- **`eq_scalar` at arbitrary coordinates.** `eq ∈ {0,1}` and `eq = 1 ↔ a = c`, for `a, c ∈ [0, n)`
under the board-size square window `(n−1)² ≤ 511`. -/
theorem eqScalarN_of_sat (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsq : ((n : ℤ) - 1) * ((n : ℤ) - 1) ≤ 511)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (acol ccol dsq neq bit0 eq : Nat)
    (hmem : ∀ {g : VmConstraint2}, g ∈ eqScalarConstraints acol ccol dsq neq bit0 eq
              → g ∈ (automataflResolveDescN n).constraints)
    (av cv : Nat) (hav : (envAt t i).loc acol = (av : ℤ)) (hcv : (envAt t i).loc ccol = (cv : ℤ))
    (havN : av < n) (hcvN : cv < n) :
    ((envAt t i).loc eq = 0 ∨ (envAt t i).loc eq = 1)
      ∧ ((envAt t i).loc eq = 1 ↔ av = cv) := by
  set e := envAt t i with he
  have hsqb : ((av : ℤ) - (cv : ℤ)) * ((av : ℤ) - (cv : ℤ)) ≤ 511 := by
    have h1 : (av : ℤ) ≤ (n : ℤ) - 1 := by have : av + 1 ≤ n := havN; push_cast; omega
    have h2 : (cv : ℤ) ≤ (n : ℤ) - 1 := by have : cv + 1 ≤ n := hcvN; push_cast; omega
    have h3 : (0 : ℤ) ≤ (av : ℤ) := by positivity
    have h4 : (0 : ℤ) ≤ (cv : ℤ) := by positivity
    nlinarith [hsq]
  have hdsq : e.loc dsq = ((av : ℤ) - (cv : ℤ)) * ((av : ℤ) - (cv : ℤ)) := by
    have hg := ngateH hsat i hi (hmem (mem_eqScalar_dsqHead acol ccol dsq neq bit0 eq))
    have hE : (headToExpr ((((Head.lin 1 dsq).addProd (-1) [acol, acol]).addProd 2 [acol, ccol]).addProd
          (-1) [ccol, ccol])).eval e.loc
        = e.loc dsq + (-1) * (e.loc acol * e.loc acol) + 2 * (e.loc acol * e.loc ccol)
          + (-1) * (e.loc ccol * e.loc ccol) := by canon_head_eval [headToExpr]
    rw [hE] at hg
    rw [hav, hcv] at hg
    exact sqDistN_pure (canon_loc hc i _) (by positivity) (by positivity) (by linarith [hsqb]) hg
  have hbnd : -999 ≤ e.loc dsq ∧ e.loc dsq ≤ 999 := by
    rw [hdsq]; constructor
    · linarith [mul_self_nonneg ((av : ℤ) - (cv : ℤ))]
    · linarith [hsqb]
  obtain ⟨hnb, hn1, hn0⟩ := ge0_9N_of_sat hsat hc i hi dsq neq bit0
    (hmem (mem_eqScalar_neqIb acol ccol dsq neq bit0 eq))
    (fun k hk => hmem (mem_eqScalar_neqBit acol ccol dsq neq bit0 eq k (by simpa [RBITS] using hk)))
    (hmem (mem_eqScalar_neqHead acol ccol dsq neq bit0 eq)) hbnd.1 hbnd.2
  have heq : e.loc eq = 1 - e.loc neq :=
    eqPinN_of_sat hsat hc i hi eq neq (hmem (mem_eqScalar_eqHead acol ccol dsq neq bit0 eq)) hnb
  refine ⟨by rcases hnb with h | h <;> rw [heq, h] <;> norm_num, ?_⟩
  constructor
  · intro h1
    have hn0' : e.loc neq = 0 := by rw [heq] at h1; omega
    have := hn0 hn0'; rw [hdsq] at this
    by_contra hne
    have hpos : (0 : ℤ) < ((av : ℤ) - (cv : ℤ)) * ((av : ℤ) - (cv : ℤ)) :=
      mul_self_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
    linarith
  · intro heqac
    have hz : e.loc dsq = 0 := by rw [hdsq, heqac]; ring
    have hneq0 : e.loc neq = 0 := by
      rcases hnb with h | h
      · exact h
      · exact absurd (hn1 h) (by rw [hz]; norm_num)
    rw [heq, hneq0]; norm_num

/-- **`iv` at arbitrary coordinates.** The witnessed direction bit is `[fx = tx]` — the eq_scalar
over the move's own coordinate columns, at any board size. -/
theorem ivN_of_sat (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsq : ((n : ℤ) - 1) * ((n : ℤ) - 1) ≤ 511)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (fx tx : Nat) (hfx : (envAt t i).loc (NGen.cFx n b) = (fx : ℤ))
    (htx : (envAt t i).loc (NGen.cTx n b) = (tx : ℤ)) (hfxN : fx < n) (htxN : tx < n) :
    ((envAt t i).loc (NGen.cIv n o) = 0 ∨ (envAt t i).loc (NGen.cIv n o) = 1)
      ∧ ((envAt t i).loc (NGen.cIv n o) = 1 ↔ fx = tx) :=
  eqScalarN_of_sat n hn hsq hsat hc i hi (NGen.cFx n b) (NGen.cTx n b) (NGen.cIvDsq n o)
    (NGen.cIvNeq n o) (NGen.ivNeqBit n o 0) (NGen.cIv n o) (fun h => hlift (voN_iv_fam n b o ob h))
    fx tx hfx htx hfxN htxN

/-! ### §D.2 — the along-axis one-hots `efrom` / `eto`, and the `og` passable gate. -/

/-- **`efrom` IS the along-axis source one-hot** (row one-hot at `fy` on the vertical branch, column
one-hot at `fx` on the horizontal branch), off the two `validate_move` source one-hots. -/
theorem efrom_oneHotN (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (fx fy : Nat)
    (hrowOH : OneHotAt (fun j => (envAt t i).loc (NGen.cSelRow n b j)) n fy)
    (hcolOH : OneHotAt (fun j => (envAt t i).loc (NGen.cSelCol n b j)) n fx)
    (hivb : (envAt t i).loc (NGen.cIv n o) = 0 ∨ (envAt t i).loc (NGen.cIv n o) = 1) :
    ((envAt t i).loc (NGen.cIv n o) = 1 →
        OneHotAt (fun j => (envAt t i).loc (NGen.cEfrom n o j)) n fy)
      ∧ ((envAt t i).loc (NGen.cIv n o) = 0 →
        OneHotAt (fun j => (envAt t i).loc (NGen.cEfrom n o j)) n fx) := by
  have hR : ∀ j, j < n → (envAt t i).loc (NGen.cSelRow n b j) = if j = fy then (1 : ℤ) else 0 :=
    fun j hj => hrowOH.2 j hj
  have hCol : ∀ j, j < n → (envAt t i).loc (NGen.cSelCol n b j) = if j = fx then (1 : ℤ) else 0 :=
    fun j hj => hcolOH.2 j hj
  have hrb : ∀ j, j < n → (envAt t i).loc (NGen.cSelRow n b j) = 0
      ∨ (envAt t i).loc (NGen.cSelRow n b j) = 1 := by
    intro j hj; rw [hR j hj]; by_cases h : j = fy <;> simp [h]
  have hcb : ∀ j, j < n → (envAt t i).loc (NGen.cSelCol n b j) = 0
      ∨ (envAt t i).loc (NGen.cSelCol n b j) = 1 := by
    intro j hj; rw [hCol j hj]; by_cases h : j = fx <;> simp [h]
  have hsel : ∀ j, j < n → (envAt t i).loc (NGen.cEfrom n o j)
      = (envAt t i).loc (NGen.cIv n o) * (envAt t i).loc (NGen.cSelRow n b j)
        + (1 - (envAt t i).loc (NGen.cIv n o)) * (envAt t i).loc (NGen.cSelCol n b j) := fun j hj =>
    gatedSelN_of_sat hsat hc i hi (NGen.cEfrom n o j) (NGen.cIv n o) (NGen.cSelRow n b j)
      (NGen.cSelCol n b j) (hlift (voN_efrom n b o ob j hj rfl)) hivb (hrb j hj) (hcb j hj)
  refine ⟨fun hiv => ⟨hrowOH.1, fun j hj => ?_⟩, fun hiv => ⟨hcolOH.1, fun j hj => ?_⟩⟩
  · show (envAt t i).loc (NGen.cEfrom n o j) = if j = fy then (1 : ℤ) else 0
    rw [hsel j hj, hiv, hR j hj]; ring
  · show (envAt t i).loc (NGen.cEfrom n o j) = if j = fx then (1 : ℤ) else 0
    rw [hsel j hj, hiv, hCol j hj]; ring

/-- **`eto` IS the along-axis destination one-hot** (at `ty` vertical, `tx` horizontal), off the two
unconditionally-pinned endpoint one-hots `ety`/`etx`. -/
theorem eto_oneHotN (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (tx ty : Nat)
    (hetyOH : OneHotAt (fun j => (envAt t i).loc (NGen.cEty n o j)) n ty)
    (hetxOH : OneHotAt (fun j => (envAt t i).loc (NGen.cEtx n o j)) n tx)
    (hivb : (envAt t i).loc (NGen.cIv n o) = 0 ∨ (envAt t i).loc (NGen.cIv n o) = 1) :
    ((envAt t i).loc (NGen.cIv n o) = 1 →
        OneHotAt (fun j => (envAt t i).loc (NGen.cEto n o j)) n ty)
      ∧ ((envAt t i).loc (NGen.cIv n o) = 0 →
        OneHotAt (fun j => (envAt t i).loc (NGen.cEto n o j)) n tx) := by
  have hY : ∀ j, j < n → (envAt t i).loc (NGen.cEty n o j) = if j = ty then (1 : ℤ) else 0 :=
    fun j hj => hetyOH.2 j hj
  have hX : ∀ j, j < n → (envAt t i).loc (NGen.cEtx n o j) = if j = tx then (1 : ℤ) else 0 :=
    fun j hj => hetxOH.2 j hj
  have hyb : ∀ j, j < n → (envAt t i).loc (NGen.cEty n o j) = 0
      ∨ (envAt t i).loc (NGen.cEty n o j) = 1 := by
    intro j hj; rw [hY j hj]; by_cases h : j = ty <;> simp [h]
  have hxb : ∀ j, j < n → (envAt t i).loc (NGen.cEtx n o j) = 0
      ∨ (envAt t i).loc (NGen.cEtx n o j) = 1 := by
    intro j hj; rw [hX j hj]; by_cases h : j = tx <;> simp [h]
  have hsel : ∀ j, j < n → (envAt t i).loc (NGen.cEto n o j)
      = (envAt t i).loc (NGen.cIv n o) * (envAt t i).loc (NGen.cEty n o j)
        + (1 - (envAt t i).loc (NGen.cIv n o)) * (envAt t i).loc (NGen.cEtx n o j) := fun j hj =>
    gatedSelN_of_sat hsat hc i hi (NGen.cEto n o j) (NGen.cIv n o) (NGen.cEty n o j)
      (NGen.cEtx n o j) (hlift (voN_eto n b o ob j hj rfl)) hivb (hyb j hj) (hxb j hj)
  refine ⟨fun hiv => ⟨hetyOH.1, fun j hj => ?_⟩, fun hiv => ⟨hetxOH.1, fun j hj => ?_⟩⟩
  · show (envAt t i).loc (NGen.cEto n o j) = if j = ty then (1 : ℤ) else 0
    rw [hsel j hj, hiv, hY j hj]; ring
  · show (envAt t i).loc (NGen.cEto n o j) = if j = tx then (1 : ℤ) else 0
    rw [hsel j hj, hiv, hX j hj]; ring

/-- **`og` passable gate.** Boolean, and on the vertical branch it is `[fxOb = fx]`, on the horizontal
`[fyOb = fy]` — `iv`-gated between the two emitted `eq_scalar`s. -/
theorem ogN_of_sat (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsq : ((n : ℤ) - 1) * ((n : ℤ) - 1) ≤ 511)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (fx fy fxOb fyOb : Nat)
    (hfx : (envAt t i).loc (NGen.cFx n b) = (fx : ℤ)) (hfy : (envAt t i).loc (NGen.cFy n b) = (fy : ℤ))
    (hfxOb : (envAt t i).loc (NGen.cFx n ob) = (fxOb : ℤ))
    (hfyOb : (envAt t i).loc (NGen.cFy n ob) = (fyOb : ℤ))
    (hfxN : fx < n) (hfyN : fy < n) (hfxObN : fxOb < n) (hfyObN : fyOb < n)
    (hivb : (envAt t i).loc (NGen.cIv n o) = 0 ∨ (envAt t i).loc (NGen.cIv n o) = 1) :
    ((envAt t i).loc (NGen.cOg n o) = 0 ∨ (envAt t i).loc (NGen.cOg n o) = 1)
      ∧ ((envAt t i).loc (NGen.cIv n o) = 1 →
          ((envAt t i).loc (NGen.cOg n o) = 1 ↔ fxOb = fx))
      ∧ ((envAt t i).loc (NGen.cIv n o) = 0 →
          ((envAt t i).loc (NGen.cOg n o) = 1 ↔ fyOb = fy)) := by
  set e := envAt t i with he
  obtain ⟨heqxB, heqxM⟩ := eqScalarN_of_sat n hn hsq hsat hc i hi (NGen.cFx n ob) (NGen.cFx n b)
    (NGen.cEqxDsq n o) (NGen.cEqxNeq n o) (NGen.eqxBit n o 0) (NGen.cEqx n o)
    (fun h => hlift (voN_eqx_fam n b o ob h)) fxOb fx hfxOb hfx hfxObN hfxN
  obtain ⟨heqyB, heqyM⟩ := eqScalarN_of_sat n hn hsq hsat hc i hi (NGen.cFy n ob) (NGen.cFy n b)
    (NGen.cEqyDsq n o) (NGen.cEqyNeq n o) (NGen.eqyBit n o 0) (NGen.cEqy n o)
    (fun h => hlift (voN_eqy_fam n b o ob h)) fyOb fy hfyOb hfy hfyObN hfyN
  have hog : e.loc (NGen.cOg n o)
      = e.loc (NGen.cIv n o) * e.loc (NGen.cEqx n o)
        + (1 - e.loc (NGen.cIv n o)) * e.loc (NGen.cEqy n o) :=
    gatedSelN_of_sat hsat hc i hi (NGen.cOg n o) (NGen.cIv n o) (NGen.cEqx n o) (NGen.cEqy n o)
      (hlift (voN_og n b o ob rfl)) hivb heqxB heqyB
  refine ⟨?_, ?_, ?_⟩
  · rcases hivb with h | h <;> rcases heqxB with x | x <;> rcases heqyB with y | y <;>
      rw [hog, h, x, y] <;> norm_num
  · intro hiv; rw [hog, hiv]; simp only [one_mul, sub_self, zero_mul, add_zero]; exact heqxM
  · intro hiv; rw [hog, hiv]; simp only [zero_mul, sub_zero, one_mul, zero_add]; exact heqyM

/-! ### §D.3 — the decoders, and the line reads (the OTHER place `NN = 2` dodged by vacuity). -/

/-- A board column in the emitted alphabet decodes to VACUUM exactly when the felt is `0`. -/
theorem vacuum_iff_zeroN {z : ℤ} (hz : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3) :
    (codeToParticle z).isVacuum = true ↔ z = 0 := by
  rcases hz with h | h | h | h <;> subst h <;> simp [codeToParticle, Particle.isVacuum]

theorem idxLtN (k x n : Nat) (hk : k < n) (hx : x < n) : k * n + x < n * n := by
  have h3 : (k + 1) * n ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  have h2 : (k + 1) * n = k * n + n := by ring
  omega

/-- Decode a satisfying Leg-R row's OLD-board columns into the reference `Board` at size `n`. -/
def boardDecodeOldN (n : Nat) (e : VmRowEnv) : Board where
  size          := n
  automaton     := ⟨(e.loc (NGen.AX_C n)).toNat, (e.loc (NGen.AY_C n)).toNat⟩
  cells         := fun c => codeToParticle (e.loc (NGen.old n (c.y * n + c.x)))
  useColumnRule := true

/-- A negated one-hot·payload sum collapses (contracts the one-hot). `f` is the caller's summand,
matched to `-(v x · p x)`; this keeps the internal `v x · p x` beta-clean while `f` matches the gate. -/
theorem sum_neg_dot {v : Nat → ℤ} {n i : Nat} (hv : OneHotAt v n i) (p f : Nat → ℤ)
    (hf : ∀ x, f x = -(v x * p x)) :
    ((List.range n).map f).sum = -(p i) := by
  have hmap : (List.range n).map f = (List.range n).map (fun x => -(v x * p x)) :=
    List.map_congr_left (fun x _ => hf x)
  have e2 : ((List.range n).map (fun x => -(v x * p x))).sum
      = -(((List.range n).map (fun x => v x * p x)).sum) := neg_sum _ _
  have e3 : ((List.range n).map (fun x => v x * p x)).sum = p i := dot_oneHot hv p
  rw [hmap, e2, e3]

/-- Decode a move's witnessed coordinate columns into the reference `Move`. -/
def moveDecodeN (n : Nat) (e : VmRowEnv) (which : Nat) : Move :=
  Move.mk 0
    ⟨(e.loc (NGen.cFx n (NGen.mvBase n which))).toNat, (e.loc (NGen.cFy n (NGen.mvBase n which))).toNat⟩
    ⟨(e.loc (NGen.cTx n (NGen.mvBase n which))).toNat, (e.loc (NGen.cTy n (NGen.mvBase n which))).toNat⟩

/-- **`line` reads the move's column on the vertical branch.** `line k` is the felt of `(fx, k)`. -/
theorem lineVertValN (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob k : Nat) (hk : k < n)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (fx : Nat) (hfxN : fx < n)
    (hcolOH : OneHotAt (fun x => (envAt t i).loc (NGen.cSelCol n b x)) n fx)
    (halph : ∀ c, c < NGen.KK n → 0 ≤ (envAt t i).loc (NGen.old n c) ∧ (envAt t i).loc (NGen.old n c) ≤ 3)
    (hiv : (envAt t i).loc (NGen.cIv n o) = 1) :
    (envAt t i).loc (NGen.cLine n o k) = (envAt t i).loc (NGen.old n (k * n + fx)) := by
  have hg := ngateH hsat i hi (hlift (voN_line n b o ob k hk rfl))
  rw [headToExpr_eval, evalH_lineHead, hiv] at hg
  have hS2 : ((List.range n).map (fun y =>
      (-1) * ((envAt t i).loc (NGen.cSelRow n b y) * (envAt t i).loc (NGen.old n (y * n + k)))
      + (1 : ℤ) * (envAt t i).loc (NGen.cSelRow n b y) * (envAt t i).loc (NGen.old n (y * n + k)))).sum
      = 0 := by
    rw [show (fun y => (-1) * ((envAt t i).loc (NGen.cSelRow n b y) * (envAt t i).loc (NGen.old n (y * n + k)))
        + (1 : ℤ) * (envAt t i).loc (NGen.cSelRow n b y) * (envAt t i).loc (NGen.old n (y * n + k)))
        = (fun _ => (0 : ℤ)) from by funext y; ring]
    simp
  have hS1 : ((List.range n).map (fun x =>
      (-1) * ((1 : ℤ) * (envAt t i).loc (NGen.cSelCol n b x) * (envAt t i).loc (NGen.old n (k * n + x))))).sum
      = -((envAt t i).loc (NGen.old n (k * n + fx))) :=
    sum_neg_dot hcolOH (fun x => (envAt t i).loc (NGen.old n (k * n + x)))
      (fun x => (-1) * ((1 : ℤ) * (envAt t i).loc (NGen.cSelCol n b x) * (envAt t i).loc (NGen.old n (k * n + x))))
      (fun x => by ring)
  rw [hS1, hS2] at hg
  have hbnd := halph (k * n + fx) (by simpa [NGen.KK] using idxLtN k fx n hk hfxN)
  exact eq_of_modEq_canon (canon_loc hc i _) ⟨hbnd.1, by linarith [hbnd.2]⟩
    ((gate_modEq_iff (by ring)).mp hg)

/-- **`line` reads the move's row on the horizontal branch.** `line k` is the felt of `(k, fy)`. -/
theorem lineHorizValN (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob k : Nat) (hk : k < n)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (fy : Nat) (hfyN : fy < n)
    (hrowOH : OneHotAt (fun y => (envAt t i).loc (NGen.cSelRow n b y)) n fy)
    (halph : ∀ c, c < NGen.KK n → 0 ≤ (envAt t i).loc (NGen.old n c) ∧ (envAt t i).loc (NGen.old n c) ≤ 3)
    (hiv : (envAt t i).loc (NGen.cIv n o) = 0) :
    (envAt t i).loc (NGen.cLine n o k) = (envAt t i).loc (NGen.old n (fy * n + k)) := by
  have hg := ngateH hsat i hi (hlift (voN_line n b o ob k hk rfl))
  rw [headToExpr_eval, evalH_lineHead, hiv] at hg
  have hS1 : ((List.range n).map (fun x =>
      (-1) * ((0 : ℤ) * (envAt t i).loc (NGen.cSelCol n b x) * (envAt t i).loc (NGen.old n (k * n + x))))).sum
      = 0 := by
    rw [show (fun x => (-1) * ((0 : ℤ) * (envAt t i).loc (NGen.cSelCol n b x) * (envAt t i).loc (NGen.old n (k * n + x))))
        = (fun _ => (0 : ℤ)) from by funext x; ring]
    simp
  have hS2 : ((List.range n).map (fun y =>
      (-1) * ((envAt t i).loc (NGen.cSelRow n b y) * (envAt t i).loc (NGen.old n (y * n + k)))
      + (0 : ℤ) * (envAt t i).loc (NGen.cSelRow n b y) * (envAt t i).loc (NGen.old n (y * n + k)))).sum
      = -((envAt t i).loc (NGen.old n (fy * n + k))) :=
    sum_neg_dot hrowOH (fun y => (envAt t i).loc (NGen.old n (y * n + k)))
      (fun y => (-1) * ((envAt t i).loc (NGen.cSelRow n b y) * (envAt t i).loc (NGen.old n (y * n + k)))
        + (0 : ℤ) * (envAt t i).loc (NGen.cSelRow n b y) * (envAt t i).loc (NGen.old n (y * n + k)))
      (fun y => by ring)
  rw [hS1, hS2] at hg
  have hbnd := halph (fy * n + k) (by simpa [NGen.KK] using idxLtN fy k n hfyN hk)
  exact eq_of_modEq_canon (canon_loc hc i _) ⟨hbnd.1, by linarith [hbnd.2]⟩
    ((gate_modEq_iff (by ring)).mp hg)

/-- **`line` columns carry particle codes** `0 ≤ line k ≤ 3`, on either branch. -/
theorem lineRangeN (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (fx fy : Nat) (hfxN : fx < n) (hfyN : fy < n)
    (hcolOH : OneHotAt (fun x => (envAt t i).loc (NGen.cSelCol n b x)) n fx)
    (hrowOH : OneHotAt (fun y => (envAt t i).loc (NGen.cSelRow n b y)) n fy)
    (halph : ∀ c, c < NGen.KK n → 0 ≤ (envAt t i).loc (NGen.old n c) ∧ (envAt t i).loc (NGen.old n c) ≤ 3)
    (hivb : (envAt t i).loc (NGen.cIv n o) = 0 ∨ (envAt t i).loc (NGen.cIv n o) = 1) :
    ∀ k, k < n → 0 ≤ (envAt t i).loc (NGen.cLine n o k) ∧ (envAt t i).loc (NGen.cLine n o k) ≤ 3 := by
  intro k hk
  rcases hivb with h | h
  · rw [lineHorizValN n hsat hc i hi b o ob k hk hlift fy hfyN hrowOH halph h]
    exact halph (fy * n + k) (by simpa [NGen.KK] using idxLtN fy k n hfyN hk)
  · rw [lineVertValN n hsat hc i hi b o ob k hk hlift fx hfxN hcolOH halph h]
    exact halph (k * n + fx) (by simpa [NGen.KK] using idxLtN k fx n hk hfxN)

/-- **`LineReadsVert`, DISCHARGED n-generically.** On the vertical branch `line k` is `0` iff the
board cell `(fx, k)` on the move's own column is vacuum. -/
theorem lineReadsVertN (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (fx : Nat) (hfxN : fx < n)
    (hcolOH : OneHotAt (fun x => (envAt t i).loc (NGen.cSelCol n b x)) n fx)
    (halph4 : ∀ c, c < NGen.KK n → ((envAt t i).loc (NGen.old n c) = 0 ∨ (envAt t i).loc (NGen.old n c) = 1
      ∨ (envAt t i).loc (NGen.old n c) = 2 ∨ (envAt t i).loc (NGen.old n c) = 3))
    (hiv : (envAt t i).loc (NGen.cIv n o) = 1) :
    LineReadsVert (fun k => (envAt t i).loc (NGen.cLine n o k)) (boardDecodeOldN n (envAt t i)) fx n := by
  have halph : ∀ c, c < NGen.KK n → 0 ≤ (envAt t i).loc (NGen.old n c) ∧ (envAt t i).loc (NGen.old n c) ≤ 3 := by
    intro c hcK; rcases halph4 c hcK with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  intro k hk
  have hidx : k * n + fx < NGen.KK n := by simpa [NGen.KK] using idxLtN k fx n hk hfxN
  show (envAt t i).loc (NGen.cLine n o k) = 0 ↔ _
  rw [lineVertValN n hsat hc i hi b o ob k hk hlift fx hfxN hcolOH halph hiv]
  have hcell : (boardDecodeOldN n (envAt t i)).cellAt ⟨fx, k⟩
      = codeToParticle ((envAt t i).loc (NGen.old n (k * n + fx))) := by
    simp only [Board.cellAt, boardDecodeOldN]; exact if_pos (⟨hfxN, hk⟩ : fx < n ∧ k < n)
  rw [hcell]
  exact (vacuum_iff_zeroN (halph4 _ hidx)).symm

/-- **`LineReadsHoriz`, DISCHARGED n-generically.** The row-scan mirror: `line k` is the felt of
`(k, fy)`. -/
theorem lineReadsHorizN (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (fy : Nat) (hfyN : fy < n)
    (hrowOH : OneHotAt (fun y => (envAt t i).loc (NGen.cSelRow n b y)) n fy)
    (halph4 : ∀ c, c < NGen.KK n → ((envAt t i).loc (NGen.old n c) = 0 ∨ (envAt t i).loc (NGen.old n c) = 1
      ∨ (envAt t i).loc (NGen.old n c) = 2 ∨ (envAt t i).loc (NGen.old n c) = 3))
    (hiv : (envAt t i).loc (NGen.cIv n o) = 0) :
    LineReadsHoriz (fun k => (envAt t i).loc (NGen.cLine n o k)) (boardDecodeOldN n (envAt t i)) fy n := by
  have halph : ∀ c, c < NGen.KK n → 0 ≤ (envAt t i).loc (NGen.old n c) ∧ (envAt t i).loc (NGen.old n c) ≤ 3 := by
    intro c hcK; rcases halph4 c hcK with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  intro k hk
  have hidx : fy * n + k < NGen.KK n := by simpa [NGen.KK] using idxLtN fy k n hfyN hk
  show (envAt t i).loc (NGen.cLine n o k) = 0 ↔ _
  rw [lineHorizValN n hsat hc i hi b o ob k hk hlift fy hfyN hrowOH halph hiv]
  have hcell : (boardDecodeOldN n (envAt t i)).cellAt ⟨k, fy⟩
      = codeToParticle ((envAt t i).loc (NGen.old n (fy * n + k))) := by
    simp only [Board.cellAt, boardDecodeOldN]; exact if_pos (⟨hk, hfyN⟩ : k < n ∧ fy < n)
  rw [hcell]
  exact (vacuum_iff_zeroN (halph4 _ hidx)).symm

/-! ### §D.4 — the seg mask, the masked sum, and the `occ` threshold column. -/

/-- A sum over `[0,n)` of terms each in `[0,3]` lies in `[0, 3n]`. -/
theorem sum_map_bound (n : Nat) (g : Nat → ℤ) (h : ∀ k, k < n → 0 ≤ g k ∧ g k ≤ 3) :
    0 ≤ ((List.range n).map g).sum ∧ ((List.range n).map g).sum ≤ 3 * (n : ℤ) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      obtain ⟨h0, h1⟩ := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
      obtain ⟨hm0, hm1⟩ := h m (Nat.lt_succ_self m)
      push_cast
      constructor <;> linarith

/-- `msumVal` respects pointwise-on-`[0,n)` equality of its `seg` argument. -/
theorem msumVal_congr {seg seg' osrc line : Nat → ℤ} {n : Nat} (h : ∀ k, k < n → seg k = seg' k) :
    msumVal seg osrc line n = msumVal seg' osrc line n := by
  unfold msumVal
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  have hh : seg k = seg' k := h k (List.mem_range.mp hk)
  simp only [hh]

/-- `msumVal` with boolean `seg`/`osrc` and `line ∈ [0,3]` lies in `[0, 3n]`. -/
theorem msumVal_boundN {seg osrc line : Nat → ℤ} {n : Nat}
    (hseg : ∀ k, k < n → seg k = 0 ∨ seg k = 1)
    (hosrc : ∀ k, k < n → osrc k = 0 ∨ osrc k = 1)
    (hline : ∀ k, k < n → 0 ≤ line k ∧ line k ≤ 3) :
    0 ≤ msumVal seg osrc line n ∧ msumVal seg osrc line n ≤ 3 * (n : ℤ) := by
  unfold msumVal
  refine sum_map_bound n (fun k => seg k * line k - seg k * osrc k * line k) (fun k hk => ?_)
  show 0 ≤ seg k * line k - seg k * osrc k * line k
    ∧ seg k * line k - seg k * osrc k * line k ≤ 3
  obtain ⟨hl0, hl3⟩ := hline k hk
  rcases hseg k hk with hs | hs <;> rcases hosrc k hk with ho | ho <;> rw [hs, ho] <;>
    constructor <;> nlinarith [hl0, hl3]

/-- **`cSeg[k]` IS `segVal`.** Under `efrom`/`eto` one-hots the emitted seg column equals the
strictly-between mask value (which is `0/1`). -/
theorem segN_of_sat (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (o k : Nat)
    (hseg : cgH (NGen.segHead n o k) ∈ (automataflResolveDescN n).constraints)
    {af at_ : Nat}
    (hf : OneHotAt (fun j => (envAt t i).loc (NGen.cEfrom n o j)) n af)
    (ht : OneHotAt (fun j => (envAt t i).loc (NGen.cEto n o j)) n at_) :
    (envAt t i).loc (NGen.cSeg n o k)
      = segVal (fun j => (envAt t i).loc (NGen.cEfrom n o j))
          (fun j => (envAt t i).loc (NGen.cEto n o j)) n k := by
  have hg := ngateH hsat i hi hseg
  rw [headToExpr_eval, evalH_segHead] at hg
  have hcanon : Canon (segVal (fun j => (envAt t i).loc (NGen.cEfrom n o j))
      (fun j => (envAt t i).loc (NGen.cEto n o j)) n k) := by
    rw [segVal_eq hf ht k]; split
    · exact canon_one
    · exact canon_zero
  exact eq_of_modEq_canon (canon_loc hc i _) hcanon ((gate_modEq_iff (by ring)).mp hg)

/-- **`occ` column = the masked-sum threshold, n-generically.** The emitted `cOcc` bit is `1` exactly
when `1 ≤ msumVal (segVal efrom eto n) osrc line n` — the generic occlusion predicate's arithmetic
side, off the emitted `seg`/`msum`/`occ` gates, with the seg mask contracted from the one-hots. -/
theorem occ_col_iff_msumValN (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (hwin : 3 * (n : ℤ) ≤ 999)
    {af at_ : Nat}
    (hf : OneHotAt (fun j => (envAt t i).loc (NGen.cEfrom n o j)) n af)
    (ht : OneHotAt (fun j => (envAt t i).loc (NGen.cEto n o j)) n at_)
    (hosrc : ∀ k, k < n → (envAt t i).loc (NGen.cOsrc n o k) = 0
      ∨ (envAt t i).loc (NGen.cOsrc n o k) = 1)
    (hlineRange : ∀ k, k < n → 0 ≤ (envAt t i).loc (NGen.cLine n o k)
      ∧ (envAt t i).loc (NGen.cLine n o k) ≤ 3) :
    ((envAt t i).loc (NGen.cOcc n o) = 1)
      ↔ 1 ≤ msumVal (segVal (fun j => (envAt t i).loc (NGen.cEfrom n o j))
              (fun j => (envAt t i).loc (NGen.cEto n o j)) n)
            (fun k => (envAt t i).loc (NGen.cOsrc n o k))
            (fun k => (envAt t i).loc (NGen.cLine n o k)) n := by
  have hsegEq : ∀ k, k < n → (envAt t i).loc (NGen.cSeg n o k)
      = segVal (fun j => (envAt t i).loc (NGen.cEfrom n o j))
          (fun j => (envAt t i).loc (NGen.cEto n o j)) n k := fun k hk =>
    segN_of_sat n hsat hc i hi o k (hlift (vo_seg n b o ob k hk)) hf ht
  have hsegBool : ∀ k, k < n → (envAt t i).loc (NGen.cSeg n o k) = 0
      ∨ (envAt t i).loc (NGen.cSeg n o k) = 1 := by
    intro k hk; rw [hsegEq k hk, segVal_eq hf ht k]; split
    · right; rfl
    · left; rfl
  -- msumVal over cSeg columns equals msumVal over segVal (pointwise on [0,n))
  have hmsumCongr : msumVal (fun k => (envAt t i).loc (NGen.cSeg n o k))
        (fun k => (envAt t i).loc (NGen.cOsrc n o k))
        (fun k => (envAt t i).loc (NGen.cLine n o k)) n
      = msumVal (segVal (fun j => (envAt t i).loc (NGen.cEfrom n o j))
          (fun j => (envAt t i).loc (NGen.cEto n o j)) n)
          (fun k => (envAt t i).loc (NGen.cOsrc n o k))
          (fun k => (envAt t i).loc (NGen.cLine n o k)) n :=
    msumVal_congr hsegEq
  -- cMsum = msumVal(cSeg, cOsrc, cLine) = msumVal(segVal, cOsrc, cLine)
  have hbndM := msumVal_boundN hsegBool hosrc hlineRange
  have hmsumEq : (envAt t i).loc (NGen.cMsum n o)
      = msumVal (fun k => (envAt t i).loc (NGen.cSeg n o k))
          (fun k => (envAt t i).loc (NGen.cOsrc n o k))
          (fun k => (envAt t i).loc (NGen.cLine n o k)) n := by
    have hg := ngateH hsat i hi (hlift (vo_msum n b o ob))
    rw [headToExpr_eval, evalH_msumHead] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) ⟨hbndM.1, by linarith [hbndM.2, hwin]⟩
      ((gate_modEq_iff (by ring)).mp hg)
  have hcMsum : (envAt t i).loc (NGen.cMsum n o)
      = msumVal (segVal (fun j => (envAt t i).loc (NGen.cEfrom n o j))
          (fun j => (envAt t i).loc (NGen.cEto n o j)) n)
          (fun k => (envAt t i).loc (NGen.cOsrc n o k))
          (fun k => (envAt t i).loc (NGen.cLine n o k)) n := by rw [hmsumEq, hmsumCongr]
  have hMbnd : 0 ≤ msumVal (segVal (fun j => (envAt t i).loc (NGen.cEfrom n o j))
          (fun j => (envAt t i).loc (NGen.cEto n o j)) n)
          (fun k => (envAt t i).loc (NGen.cOsrc n o k))
          (fun k => (envAt t i).loc (NGen.cLine n o k)) n
      ∧ msumVal (segVal (fun j => (envAt t i).loc (NGen.cEfrom n o j))
          (fun j => (envAt t i).loc (NGen.cEto n o j)) n)
          (fun k => (envAt t i).loc (NGen.cOsrc n o k))
          (fun k => (envAt t i).loc (NGen.cLine n o k)) n ≤ 3 * (n : ℤ) := by
    rw [← hmsumCongr]; exact hbndM
  obtain ⟨hoccB, hocc1, hocc0⟩ := ge0_9N_of_sat hsat hc i hi (NGen.cMsum n o) (NGen.cOcc n o)
    (NGen.occBit n o 0) (hlift (vo_occ_ib n b o ob))
    (fun k hk => hlift (vo_occ_bit n b o ob k (by simpa [RBITS] using hk)))
    (hlift (vo_occ_head n b o ob)) (by rw [hcMsum]; linarith [hMbnd.1])
    (by rw [hcMsum]; linarith [hMbnd.2, hwin])
  constructor
  · intro h; have := hocc1 h; rw [hcMsum] at this; exact this
  · intro h
    rcases hoccB with h0 | h1
    · exfalso; have := hocc0 h0; rw [hcMsum] at this; linarith
    · exact h1

/-- **The exclusive masked sum, extracted.** `cMsum[o] = msumVal (segVal efrom eto) osrc line n` — the
interior double-fold value, off the emitted `seg`/`msum` gates. Factored out of `occ_col_iff_msumValN`
(ADDITIVE, does not touch it) so the INCLUSIVE column can reuse it. -/
theorem cMsum_eq_msumValN (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (hwin : 3 * (n : ℤ) ≤ 999)
    {af at_ : Nat}
    (hf : OneHotAt (fun j => (envAt t i).loc (NGen.cEfrom n o j)) n af)
    (ht : OneHotAt (fun j => (envAt t i).loc (NGen.cEto n o j)) n at_)
    (hosrc : ∀ k, k < n → (envAt t i).loc (NGen.cOsrc n o k) = 0
      ∨ (envAt t i).loc (NGen.cOsrc n o k) = 1)
    (hlineRange : ∀ k, k < n → 0 ≤ (envAt t i).loc (NGen.cLine n o k)
      ∧ (envAt t i).loc (NGen.cLine n o k) ≤ 3) :
    (envAt t i).loc (NGen.cMsum n o)
      = msumVal (segVal (fun j => (envAt t i).loc (NGen.cEfrom n o j))
          (fun j => (envAt t i).loc (NGen.cEto n o j)) n)
          (fun k => (envAt t i).loc (NGen.cOsrc n o k))
          (fun k => (envAt t i).loc (NGen.cLine n o k)) n := by
  have hsegEq : ∀ k, k < n → (envAt t i).loc (NGen.cSeg n o k)
      = segVal (fun j => (envAt t i).loc (NGen.cEfrom n o j))
          (fun j => (envAt t i).loc (NGen.cEto n o j)) n k := fun k hk =>
    segN_of_sat n hsat hc i hi o k (hlift (vo_seg n b o ob k hk)) hf ht
  have hsegBool : ∀ k, k < n → (envAt t i).loc (NGen.cSeg n o k) = 0
      ∨ (envAt t i).loc (NGen.cSeg n o k) = 1 := by
    intro k hk; rw [hsegEq k hk, segVal_eq hf ht k]; split
    · right; rfl
    · left; rfl
  have hmsumCongr : msumVal (fun k => (envAt t i).loc (NGen.cSeg n o k))
        (fun k => (envAt t i).loc (NGen.cOsrc n o k))
        (fun k => (envAt t i).loc (NGen.cLine n o k)) n
      = msumVal (segVal (fun j => (envAt t i).loc (NGen.cEfrom n o j))
          (fun j => (envAt t i).loc (NGen.cEto n o j)) n)
          (fun k => (envAt t i).loc (NGen.cOsrc n o k))
          (fun k => (envAt t i).loc (NGen.cLine n o k)) n :=
    msumVal_congr hsegEq
  have hbndM := msumVal_boundN hsegBool hosrc hlineRange
  have hmsumEq : (envAt t i).loc (NGen.cMsum n o)
      = msumVal (fun k => (envAt t i).loc (NGen.cSeg n o k))
          (fun k => (envAt t i).loc (NGen.cOsrc n o k))
          (fun k => (envAt t i).loc (NGen.cLine n o k)) n := by
    have hg := ngateH hsat i hi (hlift (vo_msum n b o ob))
    rw [headToExpr_eval, evalH_msumHead] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) ⟨hbndM.1, by linarith [hbndM.2, hwin]⟩
      ((gate_modEq_iff (by ring)).mp hg)
  rw [hmsumEq, hmsumCongr]

/-- **`occIncl` column = the INCLUSIVE masked-sum threshold, n-generically.** The emitted `cOccIncl`
bit is `1` exactly when `1 ≤ msumInclVal (segVal efrom eto) osrc line n` — the strict interior sum
PLUS the destination endpoint term. The `blockedB`-analog of `occ_col_iff_msumValN`: the `cMsumIncl`
gate pins the column to `cMsum[o] + Σ_k eto·((1−osrc)·line)`, and `cOccIncl = [cMsumIncl ≥ 1]` is read
off the new `inclOcclusion` `forced_ge0`. Window `3n+3 ≤ 999` (the endpoint term adds ≤ 3 to the
`[0, 3n]` interior, so `cMsumIncl ∈ [0, 3n+3]` fits the 9-bit `forced_ge0`; `n ≤ 332`, ≫ 11). -/
theorem occ_col_iff_msumInclValN (n : Nat)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob w : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (hincl : ∀ {g : VmConstraint2}, g ∈ NGen.inclOcclusionOne n w o
              → g ∈ (automataflResolveDescN n).constraints)
    (hwinI : 3 * (n : ℤ) + 3 ≤ 999)
    {af at_ : Nat}
    (hf : OneHotAt (fun j => (envAt t i).loc (NGen.cEfrom n o j)) n af)
    (ht : OneHotAt (fun j => (envAt t i).loc (NGen.cEto n o j)) n at_)
    (hosrc : ∀ k, k < n → (envAt t i).loc (NGen.cOsrc n o k) = 0
      ∨ (envAt t i).loc (NGen.cOsrc n o k) = 1)
    (hlineRange : ∀ k, k < n → 0 ≤ (envAt t i).loc (NGen.cLine n o k)
      ∧ (envAt t i).loc (NGen.cLine n o k) ≤ 3) :
    ((envAt t i).loc (NGen.cOccIncl n w) = 1)
      ↔ 1 ≤ msumInclVal (fun j => (envAt t i).loc (NGen.cEfrom n o j))
              (fun j => (envAt t i).loc (NGen.cEto n o j))
              (fun k => (envAt t i).loc (NGen.cOsrc n o k))
              (fun k => (envAt t i).loc (NGen.cLine n o k)) n := by
  set e := envAt t i with he
  -- the interior masked sum
  have hcMsum : e.loc (NGen.cMsum n o)
      = msumVal (segVal (fun j => e.loc (NGen.cEfrom n o j))
          (fun j => e.loc (NGen.cEto n o j)) n)
          (fun k => e.loc (NGen.cOsrc n o k))
          (fun k => e.loc (NGen.cLine n o k)) n :=
    cMsum_eq_msumValN n hsat hc i hi b o ob hlift (by linarith) hf ht hosrc hlineRange
  -- the endpoint fold, collapsed by the eto one-hot
  have hcollapse : ((List.range n).map (fun k =>
        e.loc (NGen.cEto n o k) * ((1 - e.loc (NGen.cOsrc n o k)) * e.loc (NGen.cLine n o k)))).sum
      = (1 - e.loc (NGen.cOsrc n o at_)) * e.loc (NGen.cLine n o at_) := endpoint_collapse ht
  have hatN : at_ < n := ht.1
  -- msumInclVal collapses to interior + single endpoint term
  have hIncl_eq : msumInclVal (fun j => e.loc (NGen.cEfrom n o j)) (fun j => e.loc (NGen.cEto n o j))
        (fun k => e.loc (NGen.cOsrc n o k)) (fun k => e.loc (NGen.cLine n o k)) n
      = msumVal (segVal (fun j => e.loc (NGen.cEfrom n o j)) (fun j => e.loc (NGen.cEto n o j)) n)
          (fun k => e.loc (NGen.cOsrc n o k)) (fun k => e.loc (NGen.cLine n o k)) n
        + (1 - e.loc (NGen.cOsrc n o at_)) * e.loc (NGen.cLine n o at_) := by
    unfold msumInclVal; rw [hcollapse]
  -- interior in [0,3n], endpoint in [0,3]
  have hsegBool : ∀ k, k < n → segVal (fun j => e.loc (NGen.cEfrom n o j))
        (fun j => e.loc (NGen.cEto n o j)) n k = 0
      ∨ segVal (fun j => e.loc (NGen.cEfrom n o j)) (fun j => e.loc (NGen.cEto n o j)) n k = 1 := by
    intro k hk; rw [segVal_eq hf ht k]; split
    · right; rfl
    · left; rfl
  have hbndInt := msumVal_boundN hsegBool hosrc hlineRange
  have hendBnd : 0 ≤ (1 - e.loc (NGen.cOsrc n o at_)) * e.loc (NGen.cLine n o at_)
      ∧ (1 - e.loc (NGen.cOsrc n o at_)) * e.loc (NGen.cLine n o at_) ≤ 3 := by
    obtain ⟨hl0, hl3⟩ := hlineRange at_ hatN
    rcases hosrc at_ hatN with h0 | h1
    · rw [h0]; constructor <;> nlinarith [hl0, hl3]
    · rw [h1]; constructor <;> nlinarith [hl0, hl3]
  have hInclBnd : 0 ≤ msumInclVal (fun j => e.loc (NGen.cEfrom n o j)) (fun j => e.loc (NGen.cEto n o j))
        (fun k => e.loc (NGen.cOsrc n o k)) (fun k => e.loc (NGen.cLine n o k)) n
      ∧ msumInclVal (fun j => e.loc (NGen.cEfrom n o j)) (fun j => e.loc (NGen.cEto n o j))
          (fun k => e.loc (NGen.cOsrc n o k)) (fun k => e.loc (NGen.cLine n o k)) n ≤ 3 * (n : ℤ) + 3 := by
    rw [hIncl_eq]
    exact ⟨by linarith [hbndInt.1, hendBnd.1], by linarith [hbndInt.2, hendBnd.2]⟩
  -- the cMsumIncl gate pins the column to msumInclVal
  have hcMsumIncl : e.loc (NGen.cMsumIncl n w)
      = msumInclVal (fun j => e.loc (NGen.cEfrom n o j)) (fun j => e.loc (NGen.cEto n o j))
          (fun k => e.loc (NGen.cOsrc n o k)) (fun k => e.loc (NGen.cLine n o k)) n := by
    have hg := ngateH hsat i hi (hincl (voI_msumInclHead n w o))
    rw [headToExpr_eval, evalH_msumInclHead, hcMsum, hcollapse] at hg
    rw [hIncl_eq]
    refine eq_of_modEq_canon (canon_loc hc i _)
      ⟨by linarith [hbndInt.1, hendBnd.1], by linarith [hbndInt.2, hendBnd.2, hwinI]⟩
      ((gate_modEq_iff (by ring)).mp hg)
  obtain ⟨hoccB, hocc1, hocc0⟩ := ge0_9N_of_sat hsat hc i hi (NGen.cMsumIncl n w) (NGen.cOccIncl n w)
    (NGen.occInclBit n w 0) (hincl (voI_occIncl_ib n w o))
    (fun k hk => hincl (voI_occIncl_bit n w o k (by simpa [RBITS] using hk)))
    (hincl (voI_occIncl_head n w o)) (by rw [hcMsumIncl]; linarith [hInclBnd.1])
    (by rw [hcMsumIncl]; linarith [hInclBnd.2, hwinI])
  constructor
  · intro h; have := hocc1 h; rw [hcMsumIncl] at this; exact this
  · intro h
    rcases hoccB with h0 | h1
    · exfalso; have := hocc0 h0; rw [hcMsumIncl] at this; linarith
    · exact h1

/-! ### §D.5 — `OsrcIsOtherSource`, the LAST occlusion bridge hypothesis, DISCHARGED n-generically.

The emitted `oneHotGatedConstraints ((range n).map osrc) og idx` makes `osrc` an `og`-scaled one-hot at
the other move's along-index `og·(iv·fyOb + fxOb − iv·fxOb)`. On the vertical branch (`iv = 1`) that
index is `fyOb`; on the horizontal (`iv = 0`) it is `fxOb`. So for a strictly-interior `k` the mask
`osrc k = 1` exactly when the other source (`⟨fxOb, fyOb⟩`) shares this move's line at along-index `k`,
which — the source endpoint being excluded from the interior — is `srcs.contains` at that cell. This
is the n-generic twin of `AutomataflOcclusionBridge.osrcMeansVert/Horiz_of_sat` (`NN = 2`), with the
2-selector `osrc_arith` replaced by the gated one-hot read below. -/

/-- The `og`-gated `osrc` one-hot, extracted at ARBITRARY `n`: every `osrc j` boolean, `Σⱼ osrc j =
og`, and the RAW weighted-index congruence `Σⱼ j·osrc j ≡ og·(iv·fyOb + fxOb − iv·fxOb) [ZMOD p]`
(specialised per branch by the caller before recovering the ℤ one-hot). The n-generic replacement for
the `NN = 2` `osrc_arith` (which enumerated the two selectors). -/
theorem osrc_arithN (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints) :
    (∀ j, j < n → (envAt t i).loc (NGen.cOsrc n o j) = 0 ∨ (envAt t i).loc (NGen.cOsrc n o j) = 1)
      ∧ ((List.range n).map (fun j => (envAt t i).loc (NGen.cOsrc n o j))).sum
          = (envAt t i).loc (NGen.cOg n o)
      ∧ ((List.range n).map (fun j : Nat => (j : ℤ) * (envAt t i).loc (NGen.cOsrc n o j))).sum
          ≡ (envAt t i).loc (NGen.cOg n o)
              * ((envAt t i).loc (NGen.cIv n o) * (envAt t i).loc (NGen.cFy n ob)
                 + (envAt t i).loc (NGen.cFx n ob)
                 - (envAt t i).loc (NGen.cIv n o) * (envAt t i).loc (NGen.cFx n ob))
            [ZMOD 2013265921] := by
  set e := envAt t i with he
  have hbool : ∀ j, j < n → e.loc (NGen.cOsrc n o j) = 0 ∨ e.loc (NGen.cOsrc n o j) = 1 := by
    intro j hj
    exact bin_of_gate (ngate hsat i hi (hlift (voN_osrc_fam n b o ob
      (mem_oneHotGated_sel _ _ _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))))
      (canon_loc hc i _)
  have hsum : ((List.range n).map (fun j => e.loc (NGen.cOsrc n o j))).sum = e.loc (NGen.cOg n o) := by
    have hg := ngateH hsat i hi (hlift (voN_osrc_fam n b o ob (mem_oneHotGated_sumHead _ _ _)))
    rw [headToExpr_eval, evalH_foldl_addLin, evalH_lin, List.map_map] at hg
    have hEq : ((-1) * e.loc (NGen.cOg n o)
        + ((List.range n).map (fun j => e.loc (NGen.cOsrc n o j))).sum) ≡ 0 [ZMOD 2013265921] := by
      simpa [Function.comp_def, he] using hg
    have hmod : ((List.range n).map (fun j => e.loc (NGen.cOsrc n o j))).sum
        ≡ e.loc (NGen.cOg n o) [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hEq
    obtain ⟨hlo, hhi⟩ := sum_bool_bounds hbool
    exact eq_of_modEq_canon ⟨hlo, lt_of_le_of_lt hhi hn⟩ (canon_loc hc i _) hmod
  refine ⟨hbool, hsum, ?_⟩
  have hg := ngateH hsat i hi (hlift (voN_osrc_fam n b o ob
    (mem_oneHotGated_idxHead ((List.range n).map (NGen.cOsrc n o)) (NGen.cOg n o)
      (((Head.zero.addProd 1 [NGen.cIv n o, NGen.cFy n ob]).addLin 1 (NGen.cFx n ob)).addProd (-1)
        [NGen.cIv n o, NGen.cFx n ob]))))
  rw [headToExpr_eval] at hg
  refine (gate_modEq_iff
    (a := ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j))).sum)
    (b := e.loc (NGen.cOg n o)
      * (e.loc (NGen.cIv n o) * e.loc (NGen.cFy n ob) + e.loc (NGen.cFx n ob)
         - e.loc (NGen.cIv n o) * e.loc (NGen.cFx n ob))) ?_).mp hg
  show evalH (((((((List.range n).map (NGen.cOsrc n o)).zipIdx.foldl
        (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).addProd (-1)
          [NGen.cOg n o, NGen.cIv n o, NGen.cFy n ob]).addProd (-1)
          [NGen.cOg n o, NGen.cFx n ob]).addProd 1
          [NGen.cOg n o, NGen.cIv n o, NGen.cFx n ob]).addProd 0 [NGen.cOg n o]) e.loc
      = _
  rw [evalH_addProd, evalH_addProd, evalH_addProd, evalH_addProd, evalH_foldl_addLin_pairs,
    evalH_zero, sum_zipIdx_sel]
  simp only [varsVal, List.foldl_cons, List.foldl_nil]
  ring

/-- **`OsrcIsOtherSourceVert`, DISCHARGED at ARBITRARY `n`.** On the vertical branch the gated mask
marks exactly the strictly-interior along-indices `k` at which `⟨fx, k⟩` is a source in
`srcs = [⟨fx,fy⟩, ⟨fxOb,fyOb⟩]` — the endpoint `⟨fx,fy⟩` excluded from the interior, the other source
`⟨fxOb,fyOb⟩` marked exactly when the `og`-gate fires (`fxOb = fx`) at its own row `fyOb`. -/
theorem osrcMeansVertN (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsq : ((n : ℤ) - 1) * ((n : ℤ) - 1) ≤ 511)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (fx fy ty fxOb fyOb : Nat)
    (hfx : (envAt t i).loc (NGen.cFx n b) = (fx : ℤ)) (hfy : (envAt t i).loc (NGen.cFy n b) = (fy : ℤ))
    (hfxOb : (envAt t i).loc (NGen.cFx n ob) = (fxOb : ℤ))
    (hfyOb : (envAt t i).loc (NGen.cFy n ob) = (fyOb : ℤ))
    (hfxN : fx < n) (hfyN : fy < n) (hfxObN : fxOb < n) (hfyObN : fyOb < n)
    (hivb : (envAt t i).loc (NGen.cIv n o) = 0 ∨ (envAt t i).loc (NGen.cIv n o) = 1)
    (hiv : (envAt t i).loc (NGen.cIv n o) = 1) :
    OsrcIsOtherSourceVert (fun k => (envAt t i).loc (NGen.cOsrc n o k))
      [⟨fx, fy⟩, ⟨fxOb, fyOb⟩] fx n fy ty := by
  set e := envAt t i with he
  obtain ⟨hbool, hsum, hwsum⟩ := osrc_arithN n hn hsat hc i hi b o ob hlift
  rw [← he] at hbool hsum hwsum
  obtain ⟨hogb, hogV, _⟩ := ogN_of_sat n hn hsq hsat hc i hi b o ob hlift fx fy fxOb fyOb
    hfx hfy hfxOb hfyOb hfxN hfyN hfxObN hfyObN hivb
  rw [← he] at hogb hogV
  -- specialise the weighted-sum congruence to iv = 1: Σⱼ j·osrc j ≡ og·fyOb
  have hwv : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j))).sum
      ≡ e.loc (NGen.cOg n o) * (fyOb : ℤ) [ZMOD 2013265921] := by
    have heq : e.loc (NGen.cOg n o)
        * (e.loc (NGen.cIv n o) * e.loc (NGen.cFy n ob) + e.loc (NGen.cFx n ob)
           - e.loc (NGen.cIv n o) * e.loc (NGen.cFx n ob))
        = e.loc (NGen.cOg n o) * (fyOb : ℤ) := by rw [hiv, hfyOb, hfxOb]; ring
    exact heq ▸ hwsum
  intro k hk hbet
  have hfy_ne_k : fy ≠ k := by rintro rfl; unfold Between at hbet; omega
  have hmem : (List.contains [(⟨fx, fy⟩ : Coord), ⟨fxOb, fyOb⟩] (⟨fx, k⟩ : Coord) = true)
      ↔ (fxOb = fx ∧ fyOb = k) := by
    rw [List.contains_eq_mem, decide_eq_true_iff, List.mem_cons, List.mem_singleton]
    simp only [Coord.mk.injEq]
    constructor
    · rintro (⟨_, h⟩ | ⟨h1, h2⟩)
      · exact absurd h.symm hfy_ne_k
      · exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩; right; exact ⟨h1.symm, h2.symm⟩
  show (e.loc (NGen.cOsrc n o k) = 1) ↔ _
  rw [hmem]
  by_cases hog1 : e.loc (NGen.cOg n o) = 1
  · -- og = 1: fxOb = fx, and osrc is the one-hot at fyOb
    have hfxeq : fxOb = fx := (hogV hiv).mp hog1
    have hsum1 : ((List.range n).map (fun j => e.loc (NGen.cOsrc n o j))).sum = 1 := by
      rw [hsum, hog1]
    obtain ⟨af, hone⟩ := oneHot_exists hbool hsum1
    have hafeq : (af : ℤ) = (fyOb : ℤ) := by
      have hdot : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j))).sum = (af : ℤ) := by
        have hcomm : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j)))
            = (List.range n).map (fun j : Nat => (fun j => e.loc (NGen.cOsrc n o j)) j * (j : ℤ)) := by
          apply List.map_congr_left; intro j _; ring
        rw [hcomm, dot_oneHot hone (fun j => (j : ℤ))]
      have hcong : (af : ℤ) ≡ (fyOb : ℤ) [ZMOD 2013265921] := by
        have := hwv; rw [hdot, hog1, one_mul] at this; exact this
      exact eq_of_modEq_canon ⟨by positivity, lt_trans (by exact_mod_cast hone.1) hn⟩
        ⟨by positivity, lt_trans (by exact_mod_cast hfyObN) hn⟩ hcong
    have hafN : af = fyOb := by exact_mod_cast hafeq
    have hok : e.loc (NGen.cOsrc n o k) = if k = fyOb then (1 : ℤ) else 0 := hafN ▸ hone.2 k hk
    rw [hok]
    constructor
    · intro h; by_cases hkeq : k = fyOb
      · exact ⟨hfxeq, hkeq.symm⟩
      · rw [if_neg hkeq] at h; norm_num at h
    · rintro ⟨_, h2⟩; rw [if_pos h2.symm]
  · -- og = 0: osrc ≡ 0 and fxOb ≠ fx
    have hog0 : e.loc (NGen.cOg n o) = 0 := by
      rcases hogb with h | h
      · exact h
      · exact absurd h hog1
    have hall : ∀ j, j < n → e.loc (NGen.cOsrc n o j) = 0 :=
      allZero_of_sum_zero hbool (by rw [hsum, hog0])
    have hfxne : fxOb ≠ fx := fun h => hog1 ((hogV hiv).mpr h)
    rw [hall k hk]
    constructor
    · intro h; norm_num at h
    · rintro ⟨h1, _⟩; exact absurd h1 hfxne

/-- **`OsrcIsOtherSourceHoriz`, DISCHARGED at ARBITRARY `n`.** The row-scan mirror: the gated mask
marks the interior along-indices `k` (an `x`-coordinate) at which `⟨k, fy⟩` is a source. -/
theorem osrcMeansHorizN (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsq : ((n : ℤ) - 1) * ((n : ℤ) - 1) ≤ 511)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (fx fy tx fxOb fyOb : Nat)
    (hfx : (envAt t i).loc (NGen.cFx n b) = (fx : ℤ)) (hfy : (envAt t i).loc (NGen.cFy n b) = (fy : ℤ))
    (hfxOb : (envAt t i).loc (NGen.cFx n ob) = (fxOb : ℤ))
    (hfyOb : (envAt t i).loc (NGen.cFy n ob) = (fyOb : ℤ))
    (hfxN : fx < n) (hfyN : fy < n) (hfxObN : fxOb < n) (hfyObN : fyOb < n)
    (hivb : (envAt t i).loc (NGen.cIv n o) = 0 ∨ (envAt t i).loc (NGen.cIv n o) = 1)
    (hiv : (envAt t i).loc (NGen.cIv n o) = 0) :
    OsrcIsOtherSourceHoriz (fun k => (envAt t i).loc (NGen.cOsrc n o k))
      [⟨fx, fy⟩, ⟨fxOb, fyOb⟩] fy n fx tx := by
  set e := envAt t i with he
  obtain ⟨hbool, hsum, hwsum⟩ := osrc_arithN n hn hsat hc i hi b o ob hlift
  rw [← he] at hbool hsum hwsum
  obtain ⟨hogb, _, hogH⟩ := ogN_of_sat n hn hsq hsat hc i hi b o ob hlift fx fy fxOb fyOb
    hfx hfy hfxOb hfyOb hfxN hfyN hfxObN hfyObN hivb
  rw [← he] at hogb hogH
  -- specialise the weighted-sum congruence to iv = 0: Σⱼ j·osrc j ≡ og·fxOb
  have hwv : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j))).sum
      ≡ e.loc (NGen.cOg n o) * (fxOb : ℤ) [ZMOD 2013265921] := by
    have heq : e.loc (NGen.cOg n o)
        * (e.loc (NGen.cIv n o) * e.loc (NGen.cFy n ob) + e.loc (NGen.cFx n ob)
           - e.loc (NGen.cIv n o) * e.loc (NGen.cFx n ob))
        = e.loc (NGen.cOg n o) * (fxOb : ℤ) := by rw [hiv, hfxOb]; ring
    exact heq ▸ hwsum
  intro k hk hbet
  have hfx_ne_k : fx ≠ k := by rintro rfl; unfold Between at hbet; omega
  have hmem : (List.contains [(⟨fx, fy⟩ : Coord), ⟨fxOb, fyOb⟩] (⟨k, fy⟩ : Coord) = true)
      ↔ (fxOb = k ∧ fyOb = fy) := by
    rw [List.contains_eq_mem, decide_eq_true_iff, List.mem_cons, List.mem_singleton]
    simp only [Coord.mk.injEq]
    constructor
    · rintro (⟨h, _⟩ | ⟨h1, h2⟩)
      · exact absurd h.symm hfx_ne_k
      · exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩; right; exact ⟨h1.symm, h2.symm⟩
  show (e.loc (NGen.cOsrc n o k) = 1) ↔ _
  rw [hmem]
  by_cases hog1 : e.loc (NGen.cOg n o) = 1
  · have hfyeq : fyOb = fy := (hogH hiv).mp hog1
    have hsum1 : ((List.range n).map (fun j => e.loc (NGen.cOsrc n o j))).sum = 1 := by
      rw [hsum, hog1]
    obtain ⟨af, hone⟩ := oneHot_exists hbool hsum1
    have hafeq : (af : ℤ) = (fxOb : ℤ) := by
      have hdot : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j))).sum = (af : ℤ) := by
        have hcomm : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j)))
            = (List.range n).map (fun j : Nat => (fun j => e.loc (NGen.cOsrc n o j)) j * (j : ℤ)) := by
          apply List.map_congr_left; intro j _; ring
        rw [hcomm, dot_oneHot hone (fun j => (j : ℤ))]
      have hcong : (af : ℤ) ≡ (fxOb : ℤ) [ZMOD 2013265921] := by
        have := hwv; rw [hdot, hog1, one_mul] at this; exact this
      exact eq_of_modEq_canon ⟨by positivity, lt_trans (by exact_mod_cast hone.1) hn⟩
        ⟨by positivity, lt_trans (by exact_mod_cast hfxObN) hn⟩ hcong
    have hafN : af = fxOb := by exact_mod_cast hafeq
    have hok : e.loc (NGen.cOsrc n o k) = if k = fxOb then (1 : ℤ) else 0 := hafN ▸ hone.2 k hk
    rw [hok]
    constructor
    · intro h; by_cases hkeq : k = fxOb
      · exact ⟨hkeq.symm, hfyeq⟩
      · rw [if_neg hkeq] at h; norm_num at h
    · rintro ⟨h1, _⟩; rw [if_pos h1.symm]
  · have hog0 : e.loc (NGen.cOg n o) = 0 := by
      rcases hogb with h | h
      · exact h
      · exact absurd h hog1
    have hall : ∀ j, j < n → e.loc (NGen.cOsrc n o j) = 0 :=
      allZero_of_sum_zero hbool (by rw [hsum, hog0])
    have hfyne : fyOb ≠ fy := fun h => hog1 ((hogH hiv).mpr h)
    rw [hall k hk]
    constructor
    · intro h; norm_num at h
    · rintro ⟨_, h2⟩; exact absurd h2 hfyne

/-! ### CHUNK-2 additive — the INCLUSIVE other-source masks (`OsrcIsOtherSourceVert/HorizIncl`).

The `blockedB` twins of `osrcMeansVert/HorizN`: the SAME `og`-gated one-hot read, extended from the
strict interior `Between af at_ k` to `Between af at_ k ∨ k = at_` (the destination endpoint). The
one-hot argument is untouched — the ONLY new content is the `k = at_` case, which needs the along-axis
distinctness (`fy ≠ ty` vertical / `fx ≠ tx` horizontal): the move's OWN source cannot sit on the
destination (`frm ≠ to`), so at `k = at_` the mask `osrc[at_] = 1` iff the OTHER source is there — the
`blockedB` mover-exemption. `ms` is the (abstract) move list and `hms` characterises its source
membership by the two decoded froms (the caller supplies it from `moveDecodeN`). -/

/-- **`OsrcIsOtherSourceVertIncl`, DISCHARGED at ARBITRARY `n`.** -/
theorem osrcMeansVertInclN (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsq : ((n : ℤ) - 1) * ((n : ℤ) - 1) ≤ 511)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (fx fy ty fxOb fyOb : Nat)
    (hfx : (envAt t i).loc (NGen.cFx n b) = (fx : ℤ)) (hfy : (envAt t i).loc (NGen.cFy n b) = (fy : ℤ))
    (hfxOb : (envAt t i).loc (NGen.cFx n ob) = (fxOb : ℤ))
    (hfyOb : (envAt t i).loc (NGen.cFy n ob) = (fyOb : ℤ))
    (hfxN : fx < n) (hfyN : fy < n) (hfxObN : fxOb < n) (hfyObN : fyOb < n)
    (hivb : (envAt t i).loc (NGen.cIv n o) = 0 ∨ (envAt t i).loc (NGen.cIv n o) = 1)
    (hiv : (envAt t i).loc (NGen.cIv n o) = 1)
    (hfyty : fy ≠ ty) (ms : List Move)
    (hms : ∀ c : Coord, ((ms.any (fun m' => m'.frm == c)) = true)
             ↔ ((⟨fx, fy⟩ : Coord) = c ∨ (⟨fxOb, fyOb⟩ : Coord) = c)) :
    OsrcIsOtherSourceVertIncl (fun k => (envAt t i).loc (NGen.cOsrc n o k)) ms fx n fy ty := by
  set e := envAt t i with he
  obtain ⟨hbool, hsum, hwsum⟩ := osrc_arithN n hn hsat hc i hi b o ob hlift
  rw [← he] at hbool hsum hwsum
  obtain ⟨hogb, hogV, _⟩ := ogN_of_sat n hn hsq hsat hc i hi b o ob hlift fx fy fxOb fyOb
    hfx hfy hfxOb hfyOb hfxN hfyN hfxObN hfyObN hivb
  rw [← he] at hogb hogV
  have hwv : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j))).sum
      ≡ e.loc (NGen.cOg n o) * (fyOb : ℤ) [ZMOD 2013265921] := by
    have heq : e.loc (NGen.cOg n o)
        * (e.loc (NGen.cIv n o) * e.loc (NGen.cFy n ob) + e.loc (NGen.cFx n ob)
           - e.loc (NGen.cIv n o) * e.loc (NGen.cFx n ob))
        = e.loc (NGen.cOg n o) * (fyOb : ℤ) := by rw [hiv, hfyOb, hfxOb]; ring
    exact heq ▸ hwsum
  intro k hk hbetOr
  have hfy_ne_k : fy ≠ k := by
    intro h
    rcases hbetOr with hbet | hkeq
    · rw [h] at hbet; unfold Between at hbet; omega
    · exact hfyty (h.trans hkeq)
  -- the RAW one-hot characterisation (mirrors `osrcMeansVertN`)
  have hraw : (e.loc (NGen.cOsrc n o k) = 1) ↔ (fxOb = fx ∧ fyOb = k) := by
    by_cases hog1 : e.loc (NGen.cOg n o) = 1
    · have hfxeq : fxOb = fx := (hogV hiv).mp hog1
      have hsum1 : ((List.range n).map (fun j => e.loc (NGen.cOsrc n o j))).sum = 1 := by
        rw [hsum, hog1]
      obtain ⟨af, hone⟩ := oneHot_exists hbool hsum1
      have hafeq : (af : ℤ) = (fyOb : ℤ) := by
        have hdot : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j))).sum = (af : ℤ) := by
          have hcomm : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j)))
              = (List.range n).map (fun j : Nat => (fun j => e.loc (NGen.cOsrc n o j)) j * (j : ℤ)) := by
            apply List.map_congr_left; intro j _; ring
          rw [hcomm, dot_oneHot hone (fun j => (j : ℤ))]
        have hcong : (af : ℤ) ≡ (fyOb : ℤ) [ZMOD 2013265921] := by
          have := hwv; rw [hdot, hog1, one_mul] at this; exact this
        exact eq_of_modEq_canon ⟨by positivity, lt_trans (by exact_mod_cast hone.1) hn⟩
          ⟨by positivity, lt_trans (by exact_mod_cast hfyObN) hn⟩ hcong
      have hafN : af = fyOb := by exact_mod_cast hafeq
      have hok : e.loc (NGen.cOsrc n o k) = if k = fyOb then (1 : ℤ) else 0 := hafN ▸ hone.2 k hk
      rw [hok]
      constructor
      · intro h; by_cases hkeq : k = fyOb
        · exact ⟨hfxeq, hkeq.symm⟩
        · rw [if_neg hkeq] at h; norm_num at h
      · rintro ⟨_, h2⟩; rw [if_pos h2.symm]
    · have hog0 : e.loc (NGen.cOg n o) = 0 := by
        rcases hogb with h | h
        · exact h
        · exact absurd h hog1
      have hall : ∀ j, j < n → e.loc (NGen.cOsrc n o j) = 0 :=
        allZero_of_sum_zero hbool (by rw [hsum, hog0])
      have hfxne : fxOb ≠ fx := fun h => hog1 ((hogV hiv).mpr h)
      rw [hall k hk]
      constructor
      · intro h; norm_num at h
      · rintro ⟨h1, _⟩; exact absurd h1 hfxne
  -- bridge the raw characterisation to the `ms.any` source-membership form
  show (e.loc (NGen.cOsrc n o k) = 1) ↔ ((ms.any (fun m' => m'.frm == (⟨fx, k⟩ : Coord))) = true)
  rw [hraw, hms ⟨fx, k⟩]
  constructor
  · rintro ⟨h1, h2⟩; right; rw [Coord.mk.injEq]; exact ⟨h1, h2⟩
  · rintro (h | h)
    · rw [Coord.mk.injEq] at h; exact absurd h.2 hfy_ne_k
    · rw [Coord.mk.injEq] at h; exact h

/-- **`OsrcIsOtherSourceHorizIncl`, DISCHARGED at ARBITRARY `n`.** The row-scan mirror. -/
theorem osrcMeansHorizInclN (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsq : ((n : ℤ) - 1) * ((n : ℤ) - 1) ≤ 511)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b o ob : Nat)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.validateOcclusion n b o ob
              → g ∈ (automataflResolveDescN n).constraints)
    (fx fy tx fxOb fyOb : Nat)
    (hfx : (envAt t i).loc (NGen.cFx n b) = (fx : ℤ)) (hfy : (envAt t i).loc (NGen.cFy n b) = (fy : ℤ))
    (hfxOb : (envAt t i).loc (NGen.cFx n ob) = (fxOb : ℤ))
    (hfyOb : (envAt t i).loc (NGen.cFy n ob) = (fyOb : ℤ))
    (hfxN : fx < n) (hfyN : fy < n) (hfxObN : fxOb < n) (hfyObN : fyOb < n)
    (hivb : (envAt t i).loc (NGen.cIv n o) = 0 ∨ (envAt t i).loc (NGen.cIv n o) = 1)
    (hiv : (envAt t i).loc (NGen.cIv n o) = 0)
    (hfxtx : fx ≠ tx) (ms : List Move)
    (hms : ∀ c : Coord, ((ms.any (fun m' => m'.frm == c)) = true)
             ↔ ((⟨fx, fy⟩ : Coord) = c ∨ (⟨fxOb, fyOb⟩ : Coord) = c)) :
    OsrcIsOtherSourceHorizIncl (fun k => (envAt t i).loc (NGen.cOsrc n o k)) ms fy n fx tx := by
  set e := envAt t i with he
  obtain ⟨hbool, hsum, hwsum⟩ := osrc_arithN n hn hsat hc i hi b o ob hlift
  rw [← he] at hbool hsum hwsum
  obtain ⟨hogb, _, hogH⟩ := ogN_of_sat n hn hsq hsat hc i hi b o ob hlift fx fy fxOb fyOb
    hfx hfy hfxOb hfyOb hfxN hfyN hfxObN hfyObN hivb
  rw [← he] at hogb hogH
  have hwv : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j))).sum
      ≡ e.loc (NGen.cOg n o) * (fxOb : ℤ) [ZMOD 2013265921] := by
    have heq : e.loc (NGen.cOg n o)
        * (e.loc (NGen.cIv n o) * e.loc (NGen.cFy n ob) + e.loc (NGen.cFx n ob)
           - e.loc (NGen.cIv n o) * e.loc (NGen.cFx n ob))
        = e.loc (NGen.cOg n o) * (fxOb : ℤ) := by rw [hiv, hfxOb]; ring
    exact heq ▸ hwsum
  intro k hk hbetOr
  have hfx_ne_k : fx ≠ k := by
    intro h
    rcases hbetOr with hbet | hkeq
    · rw [h] at hbet; unfold Between at hbet; omega
    · exact hfxtx (h.trans hkeq)
  have hraw : (e.loc (NGen.cOsrc n o k) = 1) ↔ (fxOb = k ∧ fyOb = fy) := by
    by_cases hog1 : e.loc (NGen.cOg n o) = 1
    · have hfyeq : fyOb = fy := (hogH hiv).mp hog1
      have hsum1 : ((List.range n).map (fun j => e.loc (NGen.cOsrc n o j))).sum = 1 := by
        rw [hsum, hog1]
      obtain ⟨af, hone⟩ := oneHot_exists hbool hsum1
      have hafeq : (af : ℤ) = (fxOb : ℤ) := by
        have hdot : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j))).sum = (af : ℤ) := by
          have hcomm : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (NGen.cOsrc n o j)))
              = (List.range n).map (fun j : Nat => (fun j => e.loc (NGen.cOsrc n o j)) j * (j : ℤ)) := by
            apply List.map_congr_left; intro j _; ring
          rw [hcomm, dot_oneHot hone (fun j => (j : ℤ))]
        have hcong : (af : ℤ) ≡ (fxOb : ℤ) [ZMOD 2013265921] := by
          have := hwv; rw [hdot, hog1, one_mul] at this; exact this
        exact eq_of_modEq_canon ⟨by positivity, lt_trans (by exact_mod_cast hone.1) hn⟩
          ⟨by positivity, lt_trans (by exact_mod_cast hfxObN) hn⟩ hcong
      have hafN : af = fxOb := by exact_mod_cast hafeq
      have hok : e.loc (NGen.cOsrc n o k) = if k = fxOb then (1 : ℤ) else 0 := hafN ▸ hone.2 k hk
      rw [hok]
      constructor
      · intro h; by_cases hkeq : k = fxOb
        · exact ⟨hkeq.symm, hfyeq⟩
        · rw [if_neg hkeq] at h; norm_num at h
      · rintro ⟨h1, _⟩; rw [if_pos h1.symm]
    · have hog0 : e.loc (NGen.cOg n o) = 0 := by
        rcases hogb with h | h
        · exact h
        · exact absurd h hog1
      have hall : ∀ j, j < n → e.loc (NGen.cOsrc n o j) = 0 :=
        allZero_of_sum_zero hbool (by rw [hsum, hog0])
      have hfyne : fyOb ≠ fy := fun h => hog1 ((hogH hiv).mpr h)
      rw [hall k hk]
      constructor
      · intro h; norm_num at h
      · rintro ⟨_, h2⟩; exact absurd h2 hfyne
  show (e.loc (NGen.cOsrc n o k) = 1) ↔ ((ms.any (fun m' => m'.frm == (⟨k, fy⟩ : Coord))) = true)
  rw [hraw, hms ⟨k, fy⟩]
  constructor
  · rintro ⟨h1, h2⟩; right; rw [Coord.mk.injEq]; exact ⟨h1, h2⟩
  · rintro (h | h)
    · rw [Coord.mk.injEq] at h; exact absurd h.1 hfx_ne_k
    · rw [Coord.mk.injEq] at h; exact h

/-! ### §D.6 — `occ_iff_occluded_of_sat`, ASSEMBLED at ARBITRARY `n`.

The whole occlusion bridge, composed: the emitted threshold bit `cOcc` equals the reference
`Automatafl.occluded` of the decoded board, sources and move, off `Satisfied2 (automataflResolveDescN
n)` at ANY board size. Every hypothesis of the generic `occ_eq_occluded_vert/horiz` is now a
`Satisfied2`-discharged n-generic fact (`efrom_oneHotN`, `eto_oneHotN`, `lineReadsVertN/HorizN`,
`lineRangeN`, `occ_col_iff_msumValN`, `osrcMeansVertN/HorizN`). NON-VACUOUS at `n = 3`: the interior
of a 3-line genuinely holds a cell the occlusion sum inspects. This is the n-generic twin of
`AutomataflOcclusionBridge.occ_iff_occluded_of_sat`, which was frozen at `NN = 2` (both sides `false`).

The membership lifts are taken as hypotheses (the caller supplies them from the descriptor's
`validateOcclusion`/`validateMove` navigators); the board-size windows are explicit board arithmetic. -/
theorem occ_iff_occluded_of_sat (n which : Nat) (hn : (n : ℤ) < 2013265921)
    (hsq : ((n : ℤ) - 1) * ((n : ℤ) - 1) ≤ 511) (hwin : 3 * (n : ℤ) ≤ 999)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hlift : ∀ {g : VmConstraint2},
        g ∈ NGen.validateOcclusion n (NGen.mvBase n which) (NGen.occBase n which)
              (NGen.mvBase n (1 - which))
          → g ∈ (automataflResolveDescN n).constraints)
    (hmv : ∀ {g : VmConstraint2}, g ∈ NGen.validateMove n (NGen.mvBase n which)
            → g ∈ (automataflResolveDescN n).constraints)
    (hmvo : ∀ {g : VmConstraint2}, g ∈ NGen.validateMove n (NGen.mvBase n (1 - which))
            → g ∈ (automataflResolveDescN n).constraints) :
    ((envAt t i).loc (NGen.cOcc n (NGen.occBase n which)) = 1)
      ↔ occluded (boardDecodeOldN n (envAt t i))
          [(moveDecodeN n (envAt t i) which).frm, (moveDecodeN n (envAt t i) (1 - which)).frm]
          (moveDecodeN n (envAt t i) which) = true := by
  set e := envAt t i with he
  set b := NGen.mvBase n which with hb
  set o := NGen.occBase n which with ho
  set ob := NGen.mvBase n (1 - which) with hob
  -- source row/column one-hots (move under test)
  obtain ⟨afy, hafyN, hfyE, hrowOH⟩ :=
    readOneHotN n hn hsat hc i hi (NGen.cSelRow n b) (NGen.cFy n b)
      (fun h => hmv (vmN_srcRow_fam n b h))
  obtain ⟨afx, hafxN, hfxE, hcolOH⟩ :=
    readOneHotN n hn hsat hc i hi (NGen.cSelCol n b) (NGen.cFx n b)
      (fun h => hmv (vmN_srcCol_fam n b h))
  -- destination endpoint one-hots (ety at ty, etx at tx)
  obtain ⟨aty, hatyN, htyE, hetyOH⟩ :=
    readOneHotN n hn hsat hc i hi (NGen.cEty n o) (NGen.cTy n b)
      (fun h => hlift (voN_ety_fam n b o ob h))
  obtain ⟨atx, hatxN, htxE, hetxOH⟩ :=
    readOneHotN n hn hsat hc i hi (NGen.cEtx n o) (NGen.cTx n b)
      (fun h => hlift (voN_etx_fam n b o ob h))
  -- the OTHER move's source coordinates
  obtain ⟨fyOb, hfyObN, hfyObE, _⟩ :=
    readOneHotN n hn hsat hc i hi (NGen.cSelRow n ob) (NGen.cFy n ob)
      (fun h => hmvo (vmN_srcRow_fam n ob h))
  obtain ⟨fxOb, hfxObN, hfxObE, _⟩ :=
    readOneHotN n hn hsat hc i hi (NGen.cSelCol n ob) (NGen.cFx n ob)
      (fun h => hmvo (vmN_srcCol_fam n ob h))
  -- the witnessed direction bit and its geometric meaning
  obtain ⟨hivb, hivM⟩ := ivN_of_sat n hn hsq hsat hc i hi b o ob hlift afx atx hfxE htxE hafxN hatxN
  -- shared: osrc booleanity, line range, alphabets
  obtain ⟨hosrcB, _, _⟩ := osrc_arithN n hn hsat hc i hi b o ob hlift
  have halph4 : ∀ c, c < NGen.KK n → ((e.loc (NGen.old n c) = 0 ∨ e.loc (NGen.old n c) = 1
      ∨ e.loc (NGen.old n c) = 2 ∨ e.loc (NGen.old n c) = 3)) := oldAlphabetN n hsat hc i hi
  have halph : ∀ c, c < NGen.KK n → 0 ≤ e.loc (NGen.old n c) ∧ e.loc (NGen.old n c) ≤ 3 :=
    fun c hcK => oldBoundN n hsat hc i hi c hcK
  have hlineRange := lineRangeN n hsat hc i hi b o ob hlift afx afy hafxN hafyN hcolOH hrowOH halph hivb
  -- toNat facts and the decoded move / other source
  have hfxNat : (e.loc (NGen.cFx n b)).toNat = afx := by rw [hfxE]; simp
  have hfyNat : (e.loc (NGen.cFy n b)).toNat = afy := by rw [hfyE]; simp
  have htxNat : (e.loc (NGen.cTx n b)).toNat = atx := by rw [htxE]; simp
  have htyNat : (e.loc (NGen.cTy n b)).toNat = aty := by rw [htyE]; simp
  have hmwhich : moveDecodeN n e which = Move.mk 0 ⟨afx, afy⟩ ⟨atx, aty⟩ := by
    simp only [moveDecodeN, ← hb]; rw [hfxNat, hfyNat, htxNat, htyNat]
  have hotherfrm : (moveDecodeN n e (1 - which)).frm = (⟨fxOb, fyOb⟩ : Coord) := by
    simp only [moveDecodeN, ← hob]
    rw [show (e.loc (NGen.cFx n ob)).toNat = fxOb by rw [hfxObE]; simp,
      show (e.loc (NGen.cFy n ob)).toNat = fyOb by rw [hfyObE]; simp]
  rw [hmwhich, hotherfrm]
  by_cases hivv : e.loc (NGen.cIv n o) = 1
  · -- VERTICAL branch (afx = atx)
    have hvert : afx = atx := hivM.mp hivv
    have hfoh := (efrom_oneHotN n hsat hc i hi b o ob hlift afx afy hrowOH hcolOH hivb).1 hivv
    have htoh := (eto_oneHotN n hsat hc i hi b o ob hlift atx aty hetyOH hetxOH hivb).1 hivv
    have hlineRead := lineReadsVertN n hsat hc i hi b o ob hlift afx hafxN hcolOH halph4 hivv
    have hosrcMeans := osrcMeansVertN n hn hsq hsat hc i hi b o ob hlift afx afy aty fxOb fyOb
      hfxE hfyE hfxObE hfyObE hafxN hafyN hfxObN hfyObN hivb hivv
    rw [occ_col_iff_msumValN n hsat hc i hi b o ob hlift hwin hfoh htoh hosrcB hlineRange]
    exact occ_eq_occluded_vert (m := Move.mk 0 ⟨afx, afy⟩ ⟨atx, aty⟩)
      (b := boardDecodeOldN n e) (srcs := [⟨afx, afy⟩, ⟨fxOb, fyOb⟩])
      hvert hafyN hatyN hfoh htoh hosrcB hlineRange hlineRead hosrcMeans
  · -- HORIZONTAL branch (afx ≠ atx)
    have hiv0 : e.loc (NGen.cIv n o) = 0 := by rcases hivb with h | h; exact h; exact absurd h hivv
    have hhoriz : afx ≠ atx := by
      intro h; rw [hivM.mpr h] at hiv0; exact absurd hiv0 (by norm_num)
    have hfoh := (efrom_oneHotN n hsat hc i hi b o ob hlift afx afy hrowOH hcolOH hivb).2 hiv0
    have htoh := (eto_oneHotN n hsat hc i hi b o ob hlift atx aty hetyOH hetxOH hivb).2 hiv0
    have hlineRead := lineReadsHorizN n hsat hc i hi b o ob hlift afy hafyN hrowOH halph4 hiv0
    have hosrcMeans := osrcMeansHorizN n hn hsq hsat hc i hi b o ob hlift afx afy atx fxOb fyOb
      hfxE hfyE hfxObE hfyObE hafxN hafyN hfxObN hfyObN hivb hiv0
    rw [occ_col_iff_msumValN n hsat hc i hi b o ob hlift hwin hfoh htoh hosrcB hlineRange]
    exact occ_eq_occluded_horiz (m := Move.mk 0 ⟨afx, afy⟩ ⟨atx, aty⟩)
      (b := boardDecodeOldN n e) (srcs := [⟨afx, afy⟩, ⟨fxOb, fyOb⟩])
      hhoriz hafxN hatxN hfoh htoh hosrcB hlineRange hlineRead hosrcMeans

/-! ### §D.7 — `occ_iff_blocked_of_sat`, the INCLUSIVE capstone, ASSEMBLED at ARBITRARY `n` (CHUNK 2).

The `blockedB` twin of `occ_iff_occluded_of_sat`: the emitted INCLUSIVE threshold bit `cOccIncl`
equals the reference `AutomataflRules.blockedB` of the decoded board / move list / move, off
`Satisfied2 (automataflResolveDescN n)`, UNCONDITIONALLY, at ANY board size. It composes exactly like
the exclusive capstone — the same `efrom_oneHotN`/`eto_oneHotN`/`lineReadsVertN/HorizN`/`lineRangeN`
extractions — but off the NEW inclusive column (`occ_col_iff_msumInclValN`) and the strengthened
other-source masks (`osrcMeansVertInclN/HorizInclN`), and it lands on `AutomataflOcclusionGeneric.
occ_eq_blockedB_vert/horiz`. The move list `ms = [moveDecodeN which, moveDecodeN (1−which)]` is the two
resolving moves; `blockedB` reads it only through `.frm`. NON-VACUOUS at `n = 3`: a piece ON the
DESTINATION now fires `cOccIncl = blockedB = true`, where the exclusive `cOcc`/`occluded` MISS it
(§5b.4). ADDITIVE — leaves the exclusive `occ_iff_occluded_of_sat` untouched.

`hincl` lifts the new `inclOcclusionOne` gates (chunk 3 supplies it from `inclLiftN`); `hvalid` is the
move's reference `MoveValid` (the caller already extracts it via `validMoveN_of_sat`) — its `frm ≠ to`
and rook-alignment give the along-axis distinctness the destination endpoint case needs. -/
theorem occ_iff_blocked_of_sat (n which : Nat) (hn : (n : ℤ) < 2013265921)
    (hsq : ((n : ℤ) - 1) * ((n : ℤ) - 1) ≤ 511) (hwinI : 3 * (n : ℤ) + 3 ≤ 999)
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hlift : ∀ {g : VmConstraint2},
        g ∈ NGen.validateOcclusion n (NGen.mvBase n which) (NGen.occBase n which)
              (NGen.mvBase n (1 - which))
          → g ∈ (automataflResolveDescN n).constraints)
    (hincl : ∀ {g : VmConstraint2},
        g ∈ NGen.inclOcclusionOne n which (NGen.occBase n which)
          → g ∈ (automataflResolveDescN n).constraints)
    (hmv : ∀ {g : VmConstraint2}, g ∈ NGen.validateMove n (NGen.mvBase n which)
            → g ∈ (automataflResolveDescN n).constraints)
    (hmvo : ∀ {g : VmConstraint2}, g ∈ NGen.validateMove n (NGen.mvBase n (1 - which))
            → g ∈ (automataflResolveDescN n).constraints)
    (hvalid : Dregg2.Games.Automatafl.MoveValid (boardDecodeOldN n (envAt t i))
                (moveDecodeN n (envAt t i) which)) :
    ((envAt t i).loc (NGen.cOccIncl n which) = 1)
      ↔ Dregg2.Games.AutomataflRules.blockedB (boardDecodeOldN n (envAt t i))
          [moveDecodeN n (envAt t i) which, moveDecodeN n (envAt t i) (1 - which)]
          (moveDecodeN n (envAt t i) which) = true := by
  set e := envAt t i with he
  set b := NGen.mvBase n which with hb
  set o := NGen.occBase n which with ho
  set ob := NGen.mvBase n (1 - which) with hob
  obtain ⟨afy, hafyN, hfyE, hrowOH⟩ :=
    readOneHotN n hn hsat hc i hi (NGen.cSelRow n b) (NGen.cFy n b)
      (fun h => hmv (vmN_srcRow_fam n b h))
  obtain ⟨afx, hafxN, hfxE, hcolOH⟩ :=
    readOneHotN n hn hsat hc i hi (NGen.cSelCol n b) (NGen.cFx n b)
      (fun h => hmv (vmN_srcCol_fam n b h))
  obtain ⟨aty, hatyN, htyE, hetyOH⟩ :=
    readOneHotN n hn hsat hc i hi (NGen.cEty n o) (NGen.cTy n b)
      (fun h => hlift (voN_ety_fam n b o ob h))
  obtain ⟨atx, hatxN, htxE, hetxOH⟩ :=
    readOneHotN n hn hsat hc i hi (NGen.cEtx n o) (NGen.cTx n b)
      (fun h => hlift (voN_etx_fam n b o ob h))
  obtain ⟨fyOb, hfyObN, hfyObE, _⟩ :=
    readOneHotN n hn hsat hc i hi (NGen.cSelRow n ob) (NGen.cFy n ob)
      (fun h => hmvo (vmN_srcRow_fam n ob h))
  obtain ⟨fxOb, hfxObN, hfxObE, _⟩ :=
    readOneHotN n hn hsat hc i hi (NGen.cSelCol n ob) (NGen.cFx n ob)
      (fun h => hmvo (vmN_srcCol_fam n ob h))
  obtain ⟨hivb, hivM⟩ := ivN_of_sat n hn hsq hsat hc i hi b o ob hlift afx atx hfxE htxE hafxN hatxN
  obtain ⟨hosrcB, _, _⟩ := osrc_arithN n hn hsat hc i hi b o ob hlift
  have halph4 : ∀ c, c < NGen.KK n → ((e.loc (NGen.old n c) = 0 ∨ e.loc (NGen.old n c) = 1
      ∨ e.loc (NGen.old n c) = 2 ∨ e.loc (NGen.old n c) = 3)) := oldAlphabetN n hsat hc i hi
  have halph : ∀ c, c < NGen.KK n → 0 ≤ e.loc (NGen.old n c) ∧ e.loc (NGen.old n c) ≤ 3 :=
    fun c hcK => oldBoundN n hsat hc i hi c hcK
  have hlineRange := lineRangeN n hsat hc i hi b o ob hlift afx afy hafxN hafyN hcolOH hrowOH halph hivb
  have hfxNat : (e.loc (NGen.cFx n b)).toNat = afx := by rw [hfxE]; simp
  have hfyNat : (e.loc (NGen.cFy n b)).toNat = afy := by rw [hfyE]; simp
  have htxNat : (e.loc (NGen.cTx n b)).toNat = atx := by rw [htxE]; simp
  have htyNat : (e.loc (NGen.cTy n b)).toNat = aty := by rw [htyE]; simp
  have hmwhich : moveDecodeN n e which = Move.mk 0 ⟨afx, afy⟩ ⟨atx, aty⟩ := by
    simp only [moveDecodeN, ← hb]; rw [hfxNat, hfyNat, htxNat, htyNat]
  have hotherfrm : (moveDecodeN n e (1 - which)).frm = (⟨fxOb, fyOb⟩ : Coord) := by
    simp only [moveDecodeN, ← hob]
    rw [show (e.loc (NGen.cFx n ob)).toNat = fxOb by rw [hfxObE]; simp,
      show (e.loc (NGen.cFy n ob)).toNat = fyOb by rw [hfyObE]; simp]
  -- move distinctness + rook alignment (from the reference `MoveValid`)
  obtain ⟨hne, hrook, -⟩ := hvalid
  have hfrmC : (moveDecodeN n e which).frm = (⟨afx, afy⟩ : Coord) := by rw [hmwhich]
  have htoC : (moveDecodeN n e which).to = (⟨atx, aty⟩ : Coord) := by rw [hmwhich]
  -- the (post-`hmwhich`) two-move source-membership characterisation for `blockedB`
  have hms : ∀ c : Coord,
      (([Move.mk 0 ⟨afx, afy⟩ ⟨atx, aty⟩, moveDecodeN n e (1 - which)].any
          (fun m' => m'.frm == c)) = true)
        ↔ ((⟨afx, afy⟩ : Coord) = c ∨ (⟨fxOb, fyOb⟩ : Coord) = c) := by
    intro c
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq, hotherfrm]
  rw [hmwhich]
  by_cases hivv : e.loc (NGen.cIv n o) = 1
  · -- VERTICAL branch (afx = atx): the destination endpoint case needs `afy ≠ aty`
    have hvert : afx = atx := hivM.mp hivv
    have hfyty : afy ≠ aty := by intro h; apply hne; rw [hfrmC, htoC, hvert, h]
    have hfoh := (efrom_oneHotN n hsat hc i hi b o ob hlift afx afy hrowOH hcolOH hivb).1 hivv
    have htoh := (eto_oneHotN n hsat hc i hi b o ob hlift atx aty hetyOH hetxOH hivb).1 hivv
    have hlineRead := lineReadsVertN n hsat hc i hi b o ob hlift afx hafxN hcolOH halph4 hivv
    have hosrcMeans := osrcMeansVertInclN n hn hsq hsat hc i hi b o ob hlift afx afy aty fxOb fyOb
      hfxE hfyE hfxObE hfyObE hafxN hafyN hfxObN hfyObN hivb hivv hfyty
      [Move.mk 0 ⟨afx, afy⟩ ⟨atx, aty⟩, moveDecodeN n e (1 - which)] hms
    rw [occ_col_iff_msumInclValN n hsat hc i hi b o ob which hlift hincl hwinI hfoh htoh hosrcB
      hlineRange]
    exact occ_eq_blockedB_vert (m := Move.mk 0 ⟨afx, afy⟩ ⟨atx, aty⟩)
      (b := boardDecodeOldN n e) (ms := [Move.mk 0 ⟨afx, afy⟩ ⟨atx, aty⟩, moveDecodeN n e (1 - which)])
      hvert hafyN hatyN hfoh htoh hosrcB hlineRange hlineRead hosrcMeans
  · -- HORIZONTAL branch (afx ≠ atx): rook alignment gives `afy = aty`
    have hiv0 : e.loc (NGen.cIv n o) = 0 := by rcases hivb with h | h; exact h; exact absurd h hivv
    have hhoriz : afx ≠ atx := by
      intro h; rw [hivM.mpr h] at hiv0; exact absurd hiv0 (by norm_num)
    have hrow : afy = aty := by
      have hr := hrook; rw [hfrmC, htoC] at hr
      rcases hr with h | h
      · exact absurd h hhoriz
      · exact h
    have hfoh := (efrom_oneHotN n hsat hc i hi b o ob hlift afx afy hrowOH hcolOH hivb).2 hiv0
    have htoh := (eto_oneHotN n hsat hc i hi b o ob hlift atx aty hetyOH hetxOH hivb).2 hiv0
    have hlineRead := lineReadsHorizN n hsat hc i hi b o ob hlift afy hafyN hrowOH halph4 hiv0
    have hosrcMeans := osrcMeansHorizInclN n hn hsq hsat hc i hi b o ob hlift afx afy atx fxOb fyOb
      hfxE hfyE hfxObE hfyObE hafxN hafyN hfxObN hfyObN hivb hiv0 hhoriz
      [Move.mk 0 ⟨afx, afy⟩ ⟨atx, aty⟩, moveDecodeN n e (1 - which)] hms
    rw [occ_col_iff_msumInclValN n hsat hc i hi b o ob which hlift hincl hwinI hfoh htoh hosrcB
      hlineRange]
    exact occ_eq_blockedB_horiz (m := Move.mk 0 ⟨afx, afy⟩ ⟨atx, aty⟩)
      (b := boardDecodeOldN n e) (ms := [Move.mk 0 ⟨afx, afy⟩ ⟨atx, aty⟩, moveDecodeN n e (1 - which)])
      hhoriz hrow hafxN hatxN hfoh htoh hosrcB hlineRange hlineRead hosrcMeans

/-! ## §E — Axiom hygiene for the discharged (n-generic) bridge hypotheses. -/

#assert_axioms evalH_lineHead
#assert_axioms evalH_segHead
#assert_axioms evalH_msumHead
#assert_axioms ge0_9N_of_sat
#assert_axioms eqScalarN_of_sat
#assert_axioms ivN_of_sat
#assert_axioms efrom_oneHotN
#assert_axioms eto_oneHotN
#assert_axioms ogN_of_sat
#assert_axioms lineReadsVertN
#assert_axioms lineReadsHorizN
#assert_axioms lineRangeN
#assert_axioms segN_of_sat
#assert_axioms occ_col_iff_msumValN
#assert_axioms osrc_arithN
#assert_axioms osrcMeansVertN
#assert_axioms osrcMeansHorizN
#assert_axioms occ_iff_occluded_of_sat
#assert_axioms evalH_msumInclHead
#assert_axioms cMsum_eq_msumValN
#assert_axioms occ_col_iff_msumInclValN
#assert_axioms osrcMeansVertInclN
#assert_axioms osrcMeansHorizInclN
#assert_axioms inclLiftN
#assert_axioms occ_iff_blocked_of_sat

end OccN

end Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN
