/-
# Dregg2.Circuit.Emit.AutomataflCoord — the n-GENERIC COORDINATE / ONE-HOT FOUNDATION.

## Why this file exists

The automatafl refinement capstones (`AutomataflResolveRefine`, `AutomataflStepRefine`) stay `NN = 2`
because their coordinate reasoning is `{0,1}`-specific: `coord01_of_sat` / `interval_cases` /
`sqdist_pure` / the 4-way auto-cell split, and `oneHot_of_sat` is 2-SELECTOR-specific (it collapses
`(1 − c, c)`). To reach `n > 2` those need n-generic replacements.

This file supplies them, off the EMITTER's own fold structure (mirroring
`AutomataflOcclusionGeneric`'s `segVal`/`msumVal` pattern), so nothing is a re-authored model:

  * **§1 — the `evalH` bridge.** `AutomataflResolveEmit.headToExpr` lowers a `Head` to a gate
    `EmittedExpr` by FILTERING zero-coeff terms and folding `.add`. At `n = 2` every consumer got the
    closed eval by `rfl` (the fold reduces on numerals); at general `n` the fold does NOT reduce, so
    we prove ONCE that `(headToExpr h).eval a` equals the clean semantic sum `evalH h a`, and give the
    incremental `evalH_*` combinator laws. Every downstream reads `evalH`, never the AST.

  * **§2 — the one-hot collapse.** `dot_oneHot`: a satisfied `OneHotAt` (the shared
    `AutomataflOcclusionGeneric.OneHotAt`) dotted with any payload collapses to the payload at the
    selected index, n-generically. `oneHot_exists`: booleans over `[0,n)` summing to `1` ARE a one-hot.

  * **§3 — `oneHotN_of_sat`.** The read primitive: a satisfied n-wide `Builder::one_hot`
    (`oneHotAtCol`) forces its selector VALUES into a genuine `OneHotAt` at the pinned index, and the
    index into `[0,n)`. Generalises `oneHot_of_sat`. Used by the auto pin, source read, target read.

  * **§4 — `coordN_of_sat`.** `decompose_coord_le` at `COORD_RBITS n` forces the decoded coordinate
    into `[0, n)` with NO wrap, via the lower-edge recomposition and the wider-window upper edge —
    under the labelled no-wrap window `2^(COORD_RBITS n) ≤ p` (true for every realistic board size).

  * **§5 — `autoPinN_of_sat`.** DEMONSTRATES the foundation: the witnessed auto `(AX, AY)` is in
    `[0, n)` and `old[AY·n+AX] = AUTO`, at ARBITRARY `n`, off `Satisfied2 (automataflResolveDescN n)`.
    NON-VACUOUS at `n = 3` (a `#guard` rejecting a wrong auto cell on a 3×3 board).

## Axiom hygiene

`#assert_axioms` subset `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`, no
assumed arithmetization hypothesis (the no-wrap window in §4 is an EXPLICIT, discharged-at-call
inequality on the board size, not an assumed circuit fact).
-/
import Dregg2.Circuit.Emit.AutomataflResolveEmit
import Dregg2.Circuit.Emit.AutomataflOcclusionGeneric
import Dregg2.Circuit.Emit.AutomataflResolveMembership
import Dregg2.Circuit.Emit.AutomataflStepRefine

namespace Dregg2.Circuit.Emit.AutomataflCoord

open Dregg2.Circuit.Emit.AutomataflResolveEmit
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric (OneHotAt sum_oneHot sum_map_ite)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Circuit.Emit.AutomataflStepRefine
  (Canon canon_zero canon_one canon_two canon_three eq_of_modEq_canon eq_of_modEq_small
   bin_of_gate StepCanon canon_loc)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## §1 — The `evalH` bridge: `(headToExpr h).eval a = evalH h a`. -/

/-- The product `∏_{c ∈ cols} a c` (empty product `1`), matching `AutomataflResolveEmit.varsProd`'s
left-fold shape so its evaluation is definitional, not a `List.prod` port. -/
def varsVal (a : Nat → ℤ) : List Nat → ℤ
  | []        => 1
  | co :: rest => rest.foldl (fun acc v => acc * a v) (a co)

/-- The value of one `(coeff, cols)` term. -/
def termVal (a : Nat → ℤ) (t : ℤ × List Nat) : ℤ := t.1 * varsVal a t.2

/-- The clean semantic value of a `Head`: `Σ termⱼ + const`, over ALL terms (zero-coeff included —
they contribute `0`, so this matches the filtered `headToExpr`). -/
def evalH (h : Head) (a : Nat → ℤ) : ℤ := (h.terms.map (termVal a)).sum + h.const

/-- A `.mul`-fold over `.var`s evaluates to the corresponding `*`-fold. -/
theorem foldl_mul_eval (a : Nat → ℤ) (rest : List Nat) (e : EmittedExpr) :
    (rest.foldl (fun acc v => .mul acc (.var v)) e).eval a
      = rest.foldl (fun acc v => acc * a v) (e.eval a) := by
  induction rest generalizing e with
  | nil => rfl
  | cons c cs ih => simpa [EmittedExpr.eval] using ih (.mul e (.var c))

theorem varsProd_eval (a : Nat → ℤ) (cols : List Nat) :
    (varsProd cols).eval a = varsVal a cols := by
  cases cols with
  | nil => rfl
  | cons co rest =>
      show (rest.foldl (fun acc v => EmittedExpr.mul acc (.var v)) (.var co)).eval a
        = varsVal a (co :: rest)
      rw [foldl_mul_eval]
      rfl

/-- ⚑ RE-PROVED FOR THE CANONICAL RENDERER (2026-08-06). The `coeff == 1` case split is gone: the
coefficient is always written, so there is one arm, not two. -/
theorem termToExpr_eval (a : Nat → ℤ) (t : ℤ × List Nat) :
    (termToExpr t).eval a = termVal a t := by
  obtain ⟨coeff, cols⟩ := t
  cases cols with
  | nil => simp [termToExpr, Dregg2.Circuit.GateExpr.gTermToExpr, termVal, varsVal,
      EmittedExpr.eval]
  | cons co rest =>
      show (EmittedExpr.mul (.const coeff) (varsProd (co :: rest))).eval a
        = termVal a (coeff, co :: rest)
      simp only [EmittedExpr.eval, varsProd_eval, termVal]

/-- A `.add`-fold evaluates to `init + Σ` of the tail's evals. -/
theorem foldl_add_eval (a : Nat → ℤ) (l : List EmittedExpr) (e : EmittedExpr) :
    (l.foldl (fun acc x => .add acc x) e).eval a = e.eval a + (l.map (fun x => x.eval a)).sum := by
  induction l generalizing e with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih (.add e x)]
      simp only [EmittedExpr.eval, List.map_cons, List.sum_cons]
      ring

/-- The list of component `EmittedExpr`s `headToExpr` folds — ⚑ EVERY term plus a possible constant,
factored out so the fold is over a list I control (dodging matcher-identity `rw` pain). The zero-coeff
FILTER is gone with the flag day: the canonical renderer keeps a zero-coefficient term and elides only
a zero head-CONSTANT, which is exactly the rule `AirNormalForm` §1 states. -/
def headExprs (h : Head) : List EmittedExpr :=
  h.terms.map termToExpr ++ (if h.const = 0 then [] else [.const h.const])

/-- `headToExpr`'s `.add`-fold, over an explicit list. -/
def foldExprs : List EmittedExpr → EmittedExpr :=
  Dregg2.Circuit.GateExpr.gFoldExprs Dregg2.Circuit.GateExpr.toEmitted

/-- `headToExpr` IS `foldExprs ∘ headExprs`, definitionally. -/
theorem headToExpr_eq_foldExprs (h : Head) : headToExpr h = foldExprs (headExprs h) := rfl

theorem foldExprs_eval (a : Nat → ℤ) (ts : List EmittedExpr) :
    (foldExprs ts).eval a = (ts.map (fun x => x.eval a)).sum := by
  cases ts with
  | nil => show (EmittedExpr.const 0).eval a = _; simp [EmittedExpr.eval]
  | cons e rest =>
      show (rest.foldl (fun acc x => EmittedExpr.add acc x) e).eval a = _
      rw [foldl_add_eval]; simp [List.map_cons, List.sum_cons]

/-- Filtering zero-coeff terms preserves the term-sum (dropped terms have value `0`). -/
theorem sum_filter_termVal (a : Nat → ℤ) (L : List (ℤ × List Nat)) :
    ((L.filter (fun t => t.1 != 0)).map (termVal a)).sum = (L.map (termVal a)).sum := by
  induction L with
  | nil => rfl
  | cons t ts ih =>
      rw [List.filter_cons]
      by_cases h : t.1 = 0
      · have hb : (t.1 != 0) = false := by simp [h]
        rw [hb]
        simp only [Bool.false_eq_true, if_false, ih, List.map_cons, List.sum_cons, termVal, h,
          zero_mul, zero_add]
      · have hb : (t.1 != 0) = true := by simp [h]
        rw [hb]
        simp only [if_true, List.map_cons, List.sum_cons, ih]

/-- The term sublist evaluates (mapped, summed) to the term-sum. ⚑ No filter step any more — the
canonical renderer emits every term, so this is a plain `map` congruence. -/
theorem headExprs_termPart_sum (a : Nat → ℤ) (h : Head) :
    ((h.terms.map termToExpr).map (fun x => x.eval a)).sum = (h.terms.map (termVal a)).sum := by
  rw [List.map_map]
  exact congrArg List.sum (List.map_congr_left (fun t _ => termToExpr_eval a t))

/-- **THE BRIDGE.** The lowered gate evaluates to the clean semantic sum. -/
theorem headToExpr_eval (a : Nat → ℤ) (h : Head) :
    (headToExpr h).eval a = evalH h a := by
  rw [headToExpr_eq_foldExprs, foldExprs_eval, headExprs, List.map_append, List.sum_append,
    headExprs_termPart_sum]
  by_cases hconst : h.const = 0
  · rw [if_pos hconst, evalH, hconst]; simp
  · rw [if_neg hconst]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EmittedExpr.eval, add_zero]
    rw [evalH]

/-! ## §1.5 — Incremental `evalH` combinator laws (compute any built head, no AST unfolding). -/

theorem evalH_zero (a : Nat → ℤ) : evalH Head.zero a = 0 := by simp [evalH, Head.zero]
theorem evalH_c (a : Nat → ℤ) (k : ℤ) : evalH (Head.c k) a = k := by simp [evalH, Head.c]
theorem evalH_lin (a : Nat → ℤ) (c : ℤ) (col : Nat) : evalH (Head.lin c col) a = c * a col := by
  simp [evalH, Head.lin, termVal, varsVal]

theorem evalH_addLin (a : Nat → ℤ) (h : Head) (c : ℤ) (col : Nat) :
    evalH (h.addLin c col) a = evalH h a + c * a col := by
  simp only [evalH, Dregg2.Circuit.GateExpr.GHead.addLin, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, termVal, varsVal, List.foldl_nil, add_zero]
  ring

theorem evalH_addProd (a : Nat → ℤ) (h : Head) (c : ℤ) (cols : List Nat) :
    evalH (h.addProd c cols) a = evalH h a + c * varsVal a cols := by
  simp only [evalH, Dregg2.Circuit.GateExpr.GHead.addProd, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, termVal, add_zero]
  ring

theorem evalH_addConst (a : Nat → ℤ) (h : Head) (k : ℤ) :
    evalH (h.addConst k) a = evalH h a + k := by
  simp only [evalH, Dregg2.Circuit.GateExpr.GHead.addConst]; ring

theorem evalH_append (a : Nat → ℤ) (h o : Head) :
    evalH (h.append o) a = evalH h a + evalH o a := by
  simp only [evalH, Dregg2.Circuit.GateExpr.GHead.append, List.map_append, List.sum_append]; ring

theorem sum_map_mul_left {α : Type _} (k : ℤ) (l : List α) (f : α → ℤ) :
    (l.map (fun x => k * f x)).sum = k * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem evalH_scale (a : Nat → ℤ) (h : Head) (k : ℤ) : evalH (h.scale k) a = k * evalH h a := by
  simp only [evalH, Dregg2.Circuit.GateExpr.GHead.scale, List.map_map]
  have : (h.terms.map ((termVal a) ∘ (fun t => (t.1 * k, t.2))))
      = h.terms.map (fun t => k * termVal a t) := by
    apply List.map_congr_left; intro t _; simp only [Function.comp, termVal]; ring
  rw [this, sum_map_mul_left]; ring

/-- The `Σ`-fold sum head (`Builder::one_hot`'s `Σ selⱼ`): evaluates to `init + Σ_{s∈sels} a s`. -/
theorem evalH_foldl_addLin (a : Nat → ℤ) (init : Head) (sels : List Nat) :
    evalH (sels.foldl (fun acc s => acc.addLin 1 s) init) a
      = evalH init a + (sels.map a).sum := by
  induction sels generalizing init with
  | nil => simp
  | cons s ss ih =>
      rw [List.foldl_cons, ih, evalH_addLin]
      simp only [List.map_cons, List.sum_cons]; ring

/-- A `foldl` whose every step adds a fixed `delta y` accumulates `Σ delta`. The general shape the
NESTED `autoPinHead` dot-product fold is built from (`addProd` inner, sum-of-deltas outer). -/
theorem evalH_foldl_step (a : Nat → ℤ) (init : Head) (ys : List Nat) (step : Head → Nat → Head)
    (delta : Nat → ℤ) (hstep : ∀ h y, evalH (step h y) a = evalH h a + delta y) :
    evalH (ys.foldl step init) a = evalH init a + (ys.map delta).sum := by
  induction ys generalizing init with
  | nil => simp
  | cons y ys ih =>
      rw [List.foldl_cons, ih, hstep]
      simp only [List.map_cons, List.sum_cons]; ring

/-- The `Σ j·selⱼ`-fold index head, over a `(col, idx)` pair list (`Builder::one_hot`'s `zipIdx`). -/
theorem evalH_foldl_addLin_pairs (a : Nat → ℤ) (init : Head) (L : List (Nat × Nat)) :
    evalH (L.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) init) a
      = evalH init a + (L.map (fun p => (p.2 : ℤ) * a p.1)).sum := by
  induction L generalizing init with
  | nil => simp
  | cons p ps ih =>
      rw [List.foldl_cons, ih, evalH_addLin]
      simp only [List.map_cons, List.sum_cons]; ring

/-! ## §2 — The one-hot collapse (pure, n-generic; mirrors `AutomataflOcclusionGeneric.sum_oneHot`).

`OneHotAt v n i` (the SHARED occlusion definition: `i < n ∧ ∀ j < n, v j = if j = i then 1 else 0`)
dotted with any payload picks out the payload at the selected index. This is the collapse the auto
pin / source read / target read all perform. -/

/-- Summing `v j · payload j` over a duplicate-free in-range index list, `v` a one-hot at `i`. -/
theorem sum_map_mul_ite (l : List Nat) (hnd : l.Nodup) (i : Nat) (payload : Nat → ℤ) :
    (l.map (fun j => (if j = i then (1 : ℤ) else 0) * payload j)).sum
      = if i ∈ l then payload i else 0 := by
  induction l with
  | nil => simp
  | cons b rest ih =>
      rw [List.nodup_cons] at hnd
      obtain ⟨hb, hrest⟩ := hnd
      rw [List.map_cons, List.sum_cons, ih hrest]
      by_cases h : b = i
      · subst h
        rw [if_pos rfl, if_neg hb, if_pos (List.mem_cons_self ..)]; ring
      · rw [if_neg h]
        by_cases hm : i ∈ rest
        · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm)]; ring
        · rw [if_neg hm, if_neg (by simp only [List.mem_cons, not_or]
                                    exact ⟨fun hc => h hc.symm, hm⟩)]; ring

/-- **THE READ PRIMITIVE (pure).** A one-hot at `i` dotted with `payload` over `[0, n)` collapses to
`payload i`. -/
theorem dot_oneHot {v : Nat → ℤ} {n i : Nat} (hv : OneHotAt v n i) (payload : Nat → ℤ) :
    ((List.range n).map (fun j => v j * payload j)).sum = payload i := by
  have hmap : (List.range n).map (fun j => v j * payload j)
      = (List.range n).map (fun j => (if j = i then (1 : ℤ) else 0) * payload j) := by
    apply List.map_congr_left; intro j hj; rw [hv.2 j (List.mem_range.mp hj)]
  rw [hmap, sum_map_mul_ite _ List.nodup_range i payload, if_pos (List.mem_range.mpr hv.1)]

/-- **THE 2D READ (pure).** Two one-hots (row at `ay`, column at `ax`) collapse a masked board
double-sum `Σ_y Σ_x rv[y]·cv[x]·cell[y][x]` to the single selected cell `cell[ay][ax]`. This is the
collapse the AUTO pin / source read / target read all perform, at arbitrary `n`. -/
theorem dot_oneHot2 {rv cv : Nat → ℤ} {n ay ax : Nat}
    (hr : OneHotAt rv n ay) (hcv : OneHotAt cv n ax) (cell : Nat → Nat → ℤ) :
    ((List.range n).map (fun y =>
        ((List.range n).map (fun x => rv y * cv x * cell y x)).sum)).sum = cell ay ax := by
  have hinner : ∀ y, ((List.range n).map (fun x => rv y * cv x * cell y x)).sum = rv y * cell y ax := by
    intro y
    have hcong : ((List.range n).map (fun x => rv y * cv x * cell y x))
        = ((List.range n).map (fun x => cv x * (rv y * cell y x))) := by
      apply List.map_congr_left; intro x _; ring
    rw [hcong, dot_oneHot hcv (fun x => rv y * cell y x)]
  rw [show ((List.range n).map (fun y => ((List.range n).map (fun x => rv y * cv x * cell y x)).sum))
        = ((List.range n).map (fun y => rv y * cell y ax)) from by
      apply List.map_congr_left; intro y _; exact hinner y,
    dot_oneHot hr (fun y => cell y ax)]

/-! ## §3a — Booleans over `[0,n)` summing to `1` ARE a one-hot (pure, n-generic). -/

/-- `((range n).map sel).zipIdx` is the index-tagged list `[(sel 0, 0), …, (sel (n−1), n−1)]`. -/
theorem zipIdx_range_map (n : Nat) (sel : Nat → Nat) :
    ((List.range n).map sel).zipIdx = (List.range n).map (fun j => (sel j, j)) := by
  rw [List.zipIdx_map]
  have hr : (List.range n).zipIdx = (List.range n).map (fun j => (j, j)) := by
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_zipIdx, List.getElem?_map, Nat.zero_add]
    rcases Nat.lt_or_ge j n with h | h
    · simp [h]
    · simp [Nat.not_lt.mpr h]
  rw [hr, List.map_map]
  rfl

/-- The `Σ j·selⱼ` fold's value, resolved to `Σ_{j<n} j·a(sel j)`. -/
theorem sum_zipIdx_sel (n : Nat) (sel : Nat → Nat) (a : Nat → ℤ) :
    ((((List.range n).map sel).zipIdx).map (fun p => (p.2 : ℤ) * a p.1)).sum
      = ((List.range n).map (fun j : Nat => (j : ℤ) * a (sel j))).sum := by
  rw [zipIdx_range_map, List.map_map]
  apply congrArg
  apply List.map_congr_left
  intro j _
  rfl

/-- A sum of `n` booleans lies in `[0, n]`. -/
theorem sum_bool_bounds {b : Nat → ℤ} {n : Nat} (hb : ∀ j, j < n → b j = 0 ∨ b j = 1) :
    0 ≤ ((List.range n).map b).sum ∧ ((List.range n).map b).sum ≤ (n : ℤ) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      obtain ⟨h0, h1⟩ := ih (fun j hj => hb j (Nat.lt_succ_of_lt hj))
      rcases hb m (Nat.lt_succ_self m) with h | h <;> rw [h] <;> push_cast <;>
        constructor <;> omega

/-- A sum of `n` booleans that vanishes forces every one to `0`. -/
theorem allZero_of_sum_zero {b : Nat → ℤ} {n : Nat}
    (hb : ∀ j, j < n → b j = 0 ∨ b j = 1)
    (hsum : ((List.range n).map b).sum = 0) : ∀ j, j < n → b j = 0 := by
  intro j hj
  rcases hb j hj with h | h
  · exact h
  · exfalso
    have hmem : b j ∈ (List.range n).map b := List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have hnn : ∀ x ∈ (List.range n).map b, 0 ≤ x := by
      intro x hx; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      have : ∀ z : ℤ, z = 0 ∨ z = 1 → 0 ≤ z := by rintro z (rfl | rfl) <;> norm_num
      exact this _ (hb k (List.mem_range.mp hk))
    have hle := List.single_le_sum hnn (b j) hmem
    rw [hsum, h] at hle; norm_num at hle

/-- **Booleans over `[0,n)` summing to `1` ARE a `OneHotAt`.** -/
theorem oneHot_exists {b : Nat → ℤ} : ∀ {n : Nat},
    (∀ j, j < n → b j = 0 ∨ b j = 1) →
    ((List.range n).map b).sum = 1 →
    ∃ af, OneHotAt b n af := by
  intro n
  induction n with
  | zero => intro _ hsum; simp at hsum
  | succ m ih =>
      intro hb hsum
      rw [List.range_succ, List.map_append, List.sum_append] at hsum
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum
      rcases hb m (Nat.lt_succ_self m) with hbm | hbm
      · rw [hbm, add_zero] at hsum
        obtain ⟨af, haf, hone⟩ := ih (fun j hj => hb j (Nat.lt_succ_of_lt hj)) hsum
        refine ⟨af, Nat.lt_succ_of_lt haf, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjm | hjm
        · exact hone j hjm
        · subst hjm; rw [hbm, if_neg (by omega)]
      · have hz : ((List.range m).map b).sum = 0 := by rw [hbm] at hsum; omega
        have hall := allZero_of_sum_zero (fun j hj => hb j (Nat.lt_succ_of_lt hj)) hz
        refine ⟨m, Nat.lt_succ_self m, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjm | hjm
        · rw [hall j hjm, if_neg (by omega)]
        · subst hjm; rw [hbm, if_pos rfl]

/-- General coefficient-and-column `addLin` fold (the `range_nonneg` recomposition shape). -/
theorem evalH_foldl_addLinF (a : Nat → ℤ) (init : Head) (ks : List Nat)
    (coeff : Nat → ℤ) (colf : Nat → Nat) :
    evalH (ks.foldl (fun acc k => acc.addLin (coeff k) (colf k)) init) a
      = evalH init a + (ks.map (fun k => coeff k * a (colf k))).sum := by
  induction ks generalizing init with
  | nil => simp
  | cons k ks ih =>
      rw [List.foldl_cons, ih, evalH_addLin]
      simp only [List.map_cons, List.sum_cons]; ring

/-- A `Σ 2^k·bit` recomposition value lies in `[0, 2^rbits − 1]` when the bits are boolean. -/
theorem bitSum_bounds (b : Nat → ℤ) (bit0 rbits : Nat)
    (hb : ∀ k, k < rbits → b (bit0 + k) = 0 ∨ b (bit0 + k) = 1) :
    0 ≤ ((List.range rbits).map (fun k => (2 ^ k : ℤ) * b (bit0 + k))).sum
      ∧ ((List.range rbits).map (fun k => (2 ^ k : ℤ) * b (bit0 + k))).sum ≤ 2 ^ rbits - 1 := by
  induction rbits with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      obtain ⟨h0, h1⟩ := ih (fun k hk => hb k (Nat.lt_succ_of_lt hk))
      have hpow : (2 : ℤ) ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
      have h2m : (0 : ℤ) ≤ 2 ^ m := by positivity
      rcases hb m (Nat.lt_succ_self m) with h | h <;> rw [h]
      · constructor <;> nlinarith
      · constructor <;> nlinarith

/-! ## §3b — `oneHotN_of_sat`: the descriptor-generic n-wide one-hot read primitive.

Off ANY `Satisfied2 hash d …` and the three emitted `Builder::one_hot` gate families (each selector
boolean, `Σ selⱼ == 1`, `Σ j·selⱼ == idxCol`) over `sel = fun j => sel j`, `j ∈ [0,n)`: the selector
VALUES form a genuine `OneHotAt` at the pinned index, and `idxCol ∈ [0, n)`. This is the n-generic
replacement for `AutomataflResolveRefine.oneHot_of_sat` (which collapsed the 2-selector `(1−c, c)`),
and it is what the auto pin, source read and target read all consume. -/

section OfSat
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace}

/-- Descriptor-generic single-row gate extraction (the `AutomataflResolveRefine.rgate` twin, off an
ARBITRARY descriptor `d`): a per-row gate forces its body to vanish mod `p` on a non-last row. -/
theorem ngate (hsat : Satisfied2 hash d minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {g : EmittedExpr} (hg : cg g ∈ d.constraints) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hg
  have hlf : (i + 1 == t.rows.length) = false := by
    have h : i + 1 ≠ t.rows.length := by omega
    simpa using h
  simpa only [cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- `Head` form of `ngate`. -/
theorem ngateH (hsat : Satisfied2 hash d minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {h : Head} (hg : cgH h ∈ d.constraints) :
    (headToExpr h).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] :=
  ngate hsat i hi hg

/-- **`oneHotN_of_sat` — the n-generic one-hot read primitive.** -/
theorem oneHotN_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (n : Nat) (hn : (n : ℤ) < 2013265921) (sel : Nat → Nat) (idxCol : Nat)
    (hbool : ∀ j, j < n → cg (gBin (sel j)) ∈ d.constraints)
    (hsumG : cgH (((List.range n).map sel).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1)))
               ∈ d.constraints)
    (hidxG : cgH (((((List.range n).map sel).zipIdx.foldl
                    (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero)).append
                    ((Head.lin 1 idxCol).scale (-1))) ∈ d.constraints) :
    ∃ af : Nat, af < n ∧ (envAt t i).loc idxCol = (af : ℤ)
      ∧ OneHotAt (fun j => (envAt t i).loc (sel j)) n af := by
  set e := envAt t i with he
  -- (a) every selector value is boolean
  have hb : ∀ j, j < n → e.loc (sel j) = 0 ∨ e.loc (sel j) = 1 := by
    intro j hj
    exact bin_of_gate (ngate hsat i hi (hbool j hj)) (canon_loc hc i _)
  -- (b) Σ selⱼ = 1 over ℤ (the no-wrap window `n < p` makes the field congruence an equality)
  have hSsum : ((List.range n).map (fun j => e.loc (sel j))).sum = 1 := by
    have hg := ngateH hsat i hi hsumG
    rw [headToExpr_eval, evalH_foldl_addLin, evalH_c, List.map_map] at hg
    have hEq : (-1 + ((List.range n).map ((fun j => e.loc (sel j)))).sum)
        ≡ 0 [ZMOD 2013265921] := by
      simpa [Function.comp_def, he] using hg
    have hmod : ((List.range n).map (fun j => e.loc (sel j))).sum ≡ 1 [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hEq
    obtain ⟨hlo, hhi⟩ := sum_bool_bounds hb
    exact eq_of_modEq_canon ⟨hlo, by exact lt_of_le_of_lt hhi hn⟩ canon_one hmod
  -- (c) the values ARE a one-hot at some `af`
  obtain ⟨af, hone⟩ := oneHot_exists hb hSsum
  -- (d) the index pin forces `idxCol = af`
  have hidx : e.loc idxCol = (af : ℤ) := by
    have hg := ngateH hsat i hi hidxG
    rw [headToExpr_eval, evalH_append, evalH_foldl_addLin_pairs, evalH_zero, evalH_scale,
      evalH_lin, sum_zipIdx_sel] at hg
    -- hg : (0 + Σ_{j<n} j·(sel j)val) + (-1)*(1 * idxColval) ≡ 0
    have hT : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (sel j))).sum = (af : ℤ) := by
      have hcomm : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (sel j)))
          = (List.range n).map (fun j => (fun j => e.loc (sel j)) j * (j : ℤ)) := by
        apply List.map_congr_left; intro j _; ring
      rw [hcomm, dot_oneHot hone (fun j => (j : ℤ))]
    rw [hT] at hg
    have hmod : (af : ℤ) ≡ e.loc idxCol [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hg
    have hafcanon : Canon (af : ℤ) :=
      ⟨by positivity, by exact lt_of_le_of_lt (by exact_mod_cast Nat.le_of_lt hone.1) hn⟩
    exact (eq_of_modEq_canon hafcanon (canon_loc hc i _) hmod).symm
  exact ⟨af, hone.1, hidx, hone⟩

/-! ## §4 — `coordN_of_sat`: `decompose_coord_le` forces the coordinate into `[0, n)`, NO wrap.

Both `range_nonneg` edges are read off `Satisfied2`: the lower edge recomposes `col = Σ 2^k b_k ≥ 0`
and the upper edge recomposes `(n−1) − col = Σ 2^k b'_k ≥ 0`. Combining them (`Slo + Shi = n − 1`,
each nonnegative, their sum below `p` by the no-wrap window `2^(rbits+1) ≤ p`) pins
`0 ≤ col ≤ n − 1`. This is the n-generic replacement for `coord01_of_sat` (the `{0,1}` edge). -/

/-- **`coordN_of_sat`.** Under the no-wrap window (`hwin`, discharged trivially at any real board
size) the decoded coordinate is a genuine board index in `[0, n)`. -/
theorem coordN_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (n rbits col loBit0 hiBit0 : Nat) (hn1 : 1 ≤ n) (hn : (n : ℤ) < 2013265921)
    (hwin : (2 : ℤ) ^ (rbits + 1) ≤ 2013265921)
    (hlobit : ∀ k, k < rbits → cg (gBin (loBit0 + k)) ∈ d.constraints)
    (hlohead : cgH ((List.range rbits).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (loBit0 + k))
                 (Head.lin 1 col)) ∈ d.constraints)
    (hhibit : ∀ k, k < rbits → cg (gBin (hiBit0 + k)) ∈ d.constraints)
    (hhihead : cgH ((List.range rbits).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (hiBit0 + k))
                 ((Head.c ((n : ℤ) - 1)).addLin (-1) col)) ∈ d.constraints) :
    ∃ v : Nat, v < n ∧ (envAt t i).loc col = (v : ℤ) := by
  set e := envAt t i with he
  -- window facts
  have hpow_split : (2 : ℤ) ^ (rbits + 1) = 2 ^ rbits + 2 ^ rbits := by rw [pow_succ]; ring
  have hpow_le : (2 : ℤ) ^ rbits ≤ 2013265921 := by
    have : (0 : ℤ) ≤ 2 ^ rbits := by positivity
    nlinarith [hwin, hpow_split]
  -- lower edge: col ≡ Σ 2^k b_k =: Slo, and 0 ≤ Slo ≤ 2^rbits − 1
  set Slo := ((List.range rbits).map (fun k => (2 ^ k : ℤ) * e.loc (loBit0 + k))).sum with hSlo
  have hlob : ∀ k, k < rbits → e.loc (loBit0 + k) = 0 ∨ e.loc (loBit0 + k) = 1 := fun k hk =>
    bin_of_gate (ngate hsat i hi (hlobit k hk)) (canon_loc hc i _)
  obtain ⟨hSlo0, hSlo1⟩ := bitSum_bounds (fun c => e.loc c) loBit0 rbits hlob
  have hcolSlo : e.loc col = Slo := by
    have hg := ngateH hsat i hi hlohead
    rw [headToExpr_eval, evalH_foldl_addLinF, evalH_lin] at hg
    have : (1 * e.loc col + ((List.range rbits).map
            (fun k => -((2 : ℤ) ^ k) * e.loc (loBit0 + k))).sum) ≡ 0 [ZMOD 2013265921] := hg
    have hneg : ((List.range rbits).map (fun k => -((2 : ℤ) ^ k) * e.loc (loBit0 + k))).sum = -Slo := by
      rw [hSlo, show (fun k => -((2 : ℤ) ^ k) * e.loc (loBit0 + k))
          = (fun k => (-1 : ℤ) * ((2 : ℤ) ^ k * e.loc (loBit0 + k))) from by funext k; ring,
        sum_map_mul_left]
      ring
    rw [hneg] at this
    have hmod : e.loc col ≡ Slo [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp this
    refine eq_of_modEq_canon (canon_loc hc i _) ⟨hSlo0, ?_⟩ hmod
    calc Slo ≤ 2 ^ rbits - 1 := hSlo1
      _ < 2013265921 := by linarith [hpow_le]
  -- upper edge: (n−1) − col ≡ Σ 2^k b'_k =: Shi
  set Shi := ((List.range rbits).map (fun k => (2 ^ k : ℤ) * e.loc (hiBit0 + k))).sum with hShi
  have hhib : ∀ k, k < rbits → e.loc (hiBit0 + k) = 0 ∨ e.loc (hiBit0 + k) = 1 := fun k hk =>
    bin_of_gate (ngate hsat i hi (hhibit k hk)) (canon_loc hc i _)
  obtain ⟨hShi0, hShi1⟩ := bitSum_bounds (fun c => e.loc c) hiBit0 rbits hhib
  have hsumEq : Slo + Shi = (n : ℤ) - 1 := by
    have hg := ngateH hsat i hi hhihead
    rw [headToExpr_eval, evalH_foldl_addLinF, evalH_addLin, evalH_c] at hg
    have hneg : ((List.range rbits).map (fun k => -((2 : ℤ) ^ k) * e.loc (hiBit0 + k))).sum = -Shi := by
      rw [hShi, show (fun k => -((2 : ℤ) ^ k) * e.loc (hiBit0 + k))
          = (fun k => (-1 : ℤ) * ((2 : ℤ) ^ k * e.loc (hiBit0 + k))) from by funext k; ring,
        sum_map_mul_left]
      ring
    rw [hneg, hcolSlo] at hg
    -- hg : ((n-1) + (-1)*Slo) + (-Shi) ≡ 0
    have hmod : ((n : ℤ) - 1) ≡ (Slo + Shi) [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hg
    have heq : (n : ℤ) - 1 = Slo + Shi := by
      refine eq_of_modEq_canon ⟨by linarith [hn1], by linarith [hn]⟩ ⟨by linarith, ?_⟩ hmod
      have hle : Slo + Shi ≤ (2 ^ rbits - 1) + (2 ^ rbits - 1) := by linarith [hSlo1, hShi1]
      calc Slo + Shi ≤ (2 ^ rbits - 1) + (2 ^ rbits - 1) := hle
        _ = 2 ^ (rbits + 1) - 2 := by rw [hpow_split]; ring
        _ < 2013265921 := by linarith [hwin]
    exact heq.symm
  -- assemble: 0 ≤ col = Slo ≤ n − 1
  have hcol0 : 0 ≤ e.loc col := by rw [hcolSlo]; exact hSlo0
  have hcolLt : e.loc col ≤ (n : ℤ) - 1 := by rw [hcolSlo]; linarith [hShi0, hsumEq]
  refine ⟨(e.loc col).toNat, ?_, ?_⟩
  · have : (e.loc col).toNat ≤ n - 1 := by omega
    omega
  · rw [Int.toNat_of_nonneg hcol0]

/-! ## §5 — `autoPinN_of_sat`: DEMONSTRATE the foundation at ARBITRARY `n`.

Off `Satisfied2 (automataflResolveDescN n)`: the auto row/column one-hots (`oneHotN_of_sat`, twice)
pin `(AX, AY)` into `[0, n)`, and the emitted AUTO-pin dot product (`dot_oneHot2`) collapses
`Σ_y Σ_x selRow[y]·selCol[x]·old[y·n+x]` to the single selected cell, forced to `AUTO_CODE`. This is
the n-generic twin of `AutomataflResolveRefine.autoPinR_of_sat` (whose 4-way `rcases` over a 2×2 board
this replaces). NON-VACUOUS at `n = 3` — see §6. -/

open Dregg2.Circuit.Emit.AutomataflResolveMembership

/-- The AUTO-pin head evaluates to `−AUTO_CODE + Σ_y Σ_x selRow[y]·selCol[x]·old[y·n+x]`. -/
theorem evalH_autoPinHead (a : Nat → ℤ) (n : Nat) :
    evalH (NGen.autoPinHead n) a
      = -AUTO_CODE + ((List.range n).map (fun y => ((List.range n).map (fun x =>
          a (NGen.selAutoRow n y) * a (NGen.selAutoCol n x) * a (NGen.old n (y * n + x)))).sum)).sum := by
  have hstep_outer : ∀ (h : Head) (y : Nat),
      evalH ((List.range n).foldl (fun h2 x =>
          h2.addProd 1 [NGen.selAutoRow n y, NGen.selAutoCol n x, NGen.old n (y * n + x)]) h) a
        = evalH h a + ((List.range n).map (fun x =>
            a (NGen.selAutoRow n y) * a (NGen.selAutoCol n x) * a (NGen.old n (y * n + x)))).sum := by
    intro h y
    refine evalH_foldl_step a h (List.range n) _
      (fun x => a (NGen.selAutoRow n y) * a (NGen.selAutoCol n x) * a (NGen.old n (y * n + x))) ?_
    intro h2 x
    rw [evalH_addProd]
    simp only [varsVal, one_mul, List.foldl_cons, List.foldl_nil]
  rw [NGen.autoPinHead,
    evalH_foldl_step a (Head.c (-AUTO_CODE)) (List.range n) _ _ hstep_outer, evalH_c]

/-- **`autoPinN_of_sat`.** The witnessed auto `(AX, AY)` is in `[0, n)` and the OLD board holds
`AUTO_CODE` there — at ARBITRARY `n`, off `Satisfied2 (automataflResolveDescN n)`. -/
theorem autoPinN_of_sat (n : Nat) (hn : (n : ℤ) < 2013265921)
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : VmTrace} (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ∃ X Y : Nat, X < n ∧ Y < n
      ∧ (envAt t i).loc (NGen.AX_C n) = (X : ℤ) ∧ (envAt t i).loc (NGen.AY_C n) = (Y : ℤ)
      ∧ (envAt t i).loc (NGen.old n (Y * n + X)) = AUTO_CODE := by
  set e := envAt t i with he
  -- auto ROW one-hot @ AY_C, auto COLUMN one-hot @ AX_C
  obtain ⟨ay, hayLt, hayEq, hrow⟩ :=
    oneHotN_of_sat hsat hc i hi n hn (NGen.selAutoRow n) (NGen.AY_C n)
      (fun j hj => mem_resolve_of_mem_autoRead (ar_selRowBit n j hj))
      (mem_resolve_of_mem_autoRead (ar_selRowSum n))
      (mem_resolve_of_mem_autoRead (ar_selRowIdx n))
  obtain ⟨ax, haxLt, haxEq, hcol⟩ :=
    oneHotN_of_sat hsat hc i hi n hn (NGen.selAutoCol n) (NGen.AX_C n)
      (fun j hj => mem_resolve_of_mem_autoRead (ar_selColBit n j hj))
      (mem_resolve_of_mem_autoRead (ar_selColSum n))
      (mem_resolve_of_mem_autoRead (ar_selColIdx n))
  rw [← he] at hayEq haxEq
  -- the AUTO pin: the collapse pins the selected cell to AUTO_CODE
  have hg := ngateH hsat i hi (mem_resolve_of_mem_autoRead (ar_autoPin n))
  rw [headToExpr_eval, evalH_autoPinHead] at hg
  rw [dot_oneHot2 hrow hcol (fun y x => e.loc (NGen.old n (y * n + x)))] at hg
  -- hg : -AUTO_CODE + e.loc (old n (ay*n+ax)) ≡ 0
  have hmod : e.loc (NGen.old n (ay * n + ax)) ≡ AUTO_CODE [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hg
  have hcell : e.loc (NGen.old n (ay * n + ax)) = AUTO_CODE :=
    eq_of_modEq_canon (canon_loc hc i _) canon_three hmod
  exact ⟨ax, ay, haxLt, hayLt, haxEq, hayEq, hcell⟩

end OfSat

/-! ## §6 — NON-VACUITY at `n = 3`: the collapse SELECTS the `(ay, ax)` cell, and the pin is a
genuine two-sided constraint on it — content a 2×2 board's `autoPinR_of_sat` `rcases` cannot express
(there is no `(ay, ax) = (1, 2)`). Mirrors `AutomataflOcclusionGeneric`'s `decide` witnesses. -/

theorem oneHotAt3_1 : OneHotAt (fun j => if j = 1 then (1 : ℤ) else 0) 3 1 :=
  AutomataflOcclusionGeneric.oneHotAt_ite 3 1 (by decide)
theorem oneHotAt3_2 : OneHotAt (fun j => if j = 2 then (1 : ℤ) else 0) 3 2 :=
  AutomataflOcclusionGeneric.oneHotAt_ite 3 2 (by decide)

/-- **CORRECT auto cell ACCEPTED.** With the row one-hot at `ay = 1`, the column one-hot at `ax = 2`,
and the OLD board carrying `AUTO_CODE` at `(1, 2)`, the AUTO-pin dot product collapses to `AUTO_CODE`
— so `−AUTO_CODE + collapse = 0`, the pin gate is satisfied. -/
theorem autoPin_n3_accepts_correct :
    -AUTO_CODE + ((List.range 3).map (fun y => ((List.range 3).map (fun x =>
        (if y = 1 then (1 : ℤ) else 0) * (if x = 2 then (1 : ℤ) else 0)
          * (if y = 1 ∧ x = 2 then AUTO_CODE else 0))).sum)).sum = 0 := by
  rw [dot_oneHot2 oneHotAt3_1 oneHotAt3_2 (fun y x => if y = 1 ∧ x = 2 then AUTO_CODE else 0)]
  norm_num [AUTO_CODE]

/-- **WRONG auto cell REJECTED.** The SAME one-hots, but a board whose `(1, 2)` cell is vacuum (the
automaton is elsewhere): the collapse is `0`, so `−AUTO_CODE + collapse = −AUTO_CODE ≠ 0` — the pin
gate is UNSATISFIED, the wrong auto cell refused. This is the non-vacuity a 2-line lacks. -/
theorem autoPin_n3_rejects_wrong :
    -AUTO_CODE + ((List.range 3).map (fun y => ((List.range 3).map (fun x =>
        (if y = 1 then (1 : ℤ) else 0) * (if x = 2 then (1 : ℤ) else 0)
          * (if y = 0 ∧ x = 0 then AUTO_CODE else 0))).sum)).sum ≠ 0 := by
  rw [dot_oneHot2 oneHotAt3_1 oneHotAt3_2 (fun y x => if y = 0 ∧ x = 0 then AUTO_CODE else 0)]
  norm_num [AUTO_CODE]

/-! ## §6.5 — `coordN_of_sat` APPLIES to the STEP descriptor: the auto coordinate decodes into
`[0, n)` at `n = 3` and `n = 11` — the PAYOFF of the `AutomataflStepEmit.NGen` gadget migration.

The step coordinate decompose is now the `COORD_RBITS n`-bit `rangeNonnegConstraints` form (mirroring
the RESOLVE emitter), NOT the old frozen 2-bit-per-edge gadget. The old gadget pinned the auto
coordinate to `col ∈ {0,1} ∩ {n−2, n−1}` — `[0,2)` at `n = 2` (correct), `{1}` at `n = 3` (only a
centre auto), and `∅` at `n ≥ 4` (so `automataflStepDescN n` was UNSATISFIABLE for EVERY board). Here
the SAME generic `coordN_of_sat` that serves the resolve descriptor applies VERBATIM to the STEP
descriptor's `AX`/`AY` decompose families: the four `range_nonneg` gate hypotheses are discharged by
the STEP §2.5 membership (`decomp_loBit`/`decomp_loHead`/`decomp_hiBit`/`decomp_hiHead`), and the
coordinate is forced into the FULL `[0, n)`. The `cg`/`gBin` gate hypotheses match across the two
emitters' vocabularies definitionally (they carry no `Head`), and the `cgH` recomposition heads match
by concrete reduction at each fixed `n`. Concrete `n = 3` (auto ∈ {0,1,2}, not the old {1}) and the
deployed `n = 11` (auto ∈ [0,11), not the old ∅) WITNESS that the `n ≥ 4` unsatisfiability is CLOSED. -/

section StepCoordDecode
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

open Dregg2.Circuit.Emit.AutomataflStepEmit (automataflStepDescN)
open Dregg2.Circuit.Emit.AutomataflStepEmit.NGen (AX AY axLoBit axHiBit ayLoBit ayHiBit)
open Dregg2.Circuit.Emit.AutomataflStepRefine
  (mem_fe_decompAX mem_fe_decompAY decomp_loBit decomp_loHead decomp_hiBit decomp_hiHead)

/-- **`coordStep_n3_of_sat`.** On a satisfying, canonical `automataflStepDescN 3` trace the witnessed
auto `AX`/`AY` are genuine 3×3-board indices in `[0, 3)`, via `coordN_of_sat` on the STEP descriptor's
`COORD_RBITS 3 = 2`-bit decompose. NON-VACUOUS: the old 2-bit gadget forced `AX = 1` (centre only);
this admits `AX ∈ {0,1,2}`. -/
theorem coordStep_n3_of_sat
    (hsat : Satisfied2 hash (automataflStepDescN 3) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (∃ vx : Nat, vx < 3 ∧ (envAt t i).loc (AX 3) = (vx : ℤ))
      ∧ (∃ vy : Nat, vy < 3 ∧ (envAt t i).loc (AY 3) = (vy : ℤ)) :=
  ⟨coordN_of_sat hsat hc i hi 3 (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.COORD_RBITS 3)
      (AX 3) (axLoBit 3) (axHiBit 3) (by decide) (by decide) (by decide)
      (fun _ hk => mem_fe_decompAX (decomp_loBit hk)) (mem_fe_decompAX decomp_loHead)
      (fun _ hk => mem_fe_decompAX (decomp_hiBit hk)) (mem_fe_decompAX decomp_hiHead),
   coordN_of_sat hsat hc i hi 3 (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.COORD_RBITS 3)
      (AY 3) (ayLoBit 3) (ayHiBit 3) (by decide) (by decide) (by decide)
      (fun _ hk => mem_fe_decompAY (decomp_loBit hk)) (mem_fe_decompAY decomp_loHead)
      (fun _ hk => mem_fe_decompAY (decomp_hiBit hk)) (mem_fe_decompAY decomp_hiHead)⟩

/-- **`coordStep_n11_of_sat`.** The same at the deployed `n = 11`: `AX`/`AY ∈ [0, 11)`, via the
`COORD_RBITS 11 = 4`-bit decompose. At `n ≥ 4` the old 2-bit gadget was UNSATISFIABLE
(`{0,1} ∩ {9,10} = ∅`); this shows the migrated descriptor admits a genuine full-range auto
coordinate on the 11×11 board. -/
theorem coordStep_n11_of_sat
    (hsat : Satisfied2 hash (automataflStepDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (∃ vx : Nat, vx < 11 ∧ (envAt t i).loc (AX 11) = (vx : ℤ))
      ∧ (∃ vy : Nat, vy < 11 ∧ (envAt t i).loc (AY 11) = (vy : ℤ)) :=
  ⟨coordN_of_sat hsat hc i hi 11 (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.COORD_RBITS 11)
      (AX 11) (axLoBit 11) (axHiBit 11) (by decide) (by decide) (by decide)
      (fun _ hk => mem_fe_decompAX (decomp_loBit hk)) (mem_fe_decompAX decomp_loHead)
      (fun _ hk => mem_fe_decompAX (decomp_hiBit hk)) (mem_fe_decompAX decomp_hiHead),
   coordN_of_sat hsat hc i hi 11 (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.COORD_RBITS 11)
      (AY 11) (ayLoBit 11) (ayHiBit 11) (by decide) (by decide) (by decide)
      (fun _ hk => mem_fe_decompAY (decomp_loBit hk)) (mem_fe_decompAY decomp_loHead)
      (fun _ hk => mem_fe_decompAY (decomp_hiBit hk)) (mem_fe_decompAY decomp_hiHead)⟩

end StepCoordDecode

/-! ## §7 — Axiom pins. -/

#assert_axioms headToExpr_eval
#assert_axioms dot_oneHot
#assert_axioms dot_oneHot2
#assert_axioms oneHot_exists
#assert_axioms oneHotN_of_sat
#assert_axioms coordN_of_sat
#assert_axioms autoPinN_of_sat
#assert_axioms autoPin_n3_accepts_correct
#assert_axioms autoPin_n3_rejects_wrong
#assert_axioms coordStep_n3_of_sat
#assert_axioms coordStep_n11_of_sat

end Dregg2.Circuit.Emit.AutomataflCoord
