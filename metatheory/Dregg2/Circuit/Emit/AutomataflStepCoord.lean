/-
# Dregg2.Circuit.Emit.AutomataflStepCoord — the STEP-side n-GENERIC COORDINATE / ONE-HOT FOUNDATION.

## Why this file exists (the exact crux it removes)

`AutomataflCoord` built the n-generic coordinate/one-hot foundation for the RESOLVE emitter. Its
`evalH` / `headToExpr_eval` are typed on `AutomataflResolveEmit.Head` — a DISTINCT inductive type from
`AutomataflStepEmit.Head`, even though the two are structurally identical (same fields, same
combinators, same `headToExpr` lowering). So every STEP-side consumer that tried
`rw [headToExpr_eval]` on a STEP gate FAILED: the rewrite's LHS pattern is
`AutomataflResolveEmit.headToExpr _`, and the goal carries `AutomataflStepEmit.headToExpr _`.

At CONCRETE `n` this was survivable — `AutomataflCoord` §6.5 (`coordStep_n3_of_sat` /
`coordStep_n11_of_sat`) applies the RESOLVE-typed `coordN_of_sat` to the STEP descriptor because at a
fixed numeral both sides reduce to the same `EmittedExpr` and the elaborator closes the gap by
`whnf`. At SYMBOLIC `n` nothing reduces, so the Leg-A capstone chain (`oneHotStepN_of_sat` →
ray-of-sat wiring → `decideAxis` → `chooseOffset` → `astep`) was pinned at concrete board sizes.

This file mirrors `AutomataflCoord` §1–§1.5 and §3–§5 for `AutomataflStepEmit.Head`, so the STEP side
has its OWN bridge and the `rw` succeeds SYMBOLICALLY:

  * **§1 — `headToExpr_evalStep`.** `(AutomataflStepEmit.headToExpr h).eval a = evalHStep h a`, the
    clean semantic sum, at arbitrary `n`. Plus the incremental `evalHStep_*` combinator laws
    (`addLin`/`addProd`/`addConst`/`scale`/`append`/the three fold shapes).

  * **§2 — `oneHotStepN_of_sat` (∀ n).** The step one-hot read primitive: a satisfied n-wide
    `Builder::one_hot` over the STEP descriptor forces its selector VALUES into a genuine `OneHotAt`
    and pins the index into `[0, n)`. The ∀-n mirror of `AutomataflCoord.oneHotN_of_sat`.
    NOTE a REAL structural difference from RESOLVE, handled here: the STEP emitter's index gate folds
    over `List.range sels.length` reading `sels[j]!` (a `getElem!`), where RESOLVE folds over
    `sels.zipIdx`. §2's `evalHStep_foldl_idxBang` + `getElem!_range_map` absorb it; the resulting
    value is the same `Σ_{j<n} j·selⱼ`.

  * **§3 — `coordNStep_of_sat` / `coordStepN_of_sat` (∀ n).** The `decompose_coord_le` no-wrap decode,
    STEP-typed, and its application to `automataflStepDescN n`'s `AX`/`AY` at ARBITRARY `n` —
    replacing the concrete `coordStep_n3_of_sat` / `coordStep_n11_of_sat` pair.

  * **§4 — `autoPinStepN_of_sat` (∀ n).** Off `Satisfied2 (automataflStepDescN n)`: the witnessed auto
    `(AX, AY)` is in `[0, n)` and `old[AY·n+AX] = AUTO`, at ARBITRARY `n`.

  * **§5 — non-vacuity at `n = 3`** (the collapse SELECTS the cell; a wrong auto cell is REFUSED).

## Scope honesty

Nothing here asserts the step capstone. This is the FOUNDATION the ray-of-sat wiring / `decideAxis` /
`chooseOffset` / `astep` chain stands on; those remain the named residual (see
`AutomataflStepCapstone` §3). The `[0, n)` decode carries an EXPLICIT no-wrap window inequality on the
board size (`2^(COORD_RBITS n + 1) ≤ p`), discharged at each call — not an assumed circuit fact.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `native_decide`, no assumed
arithmetization hypothesis. NEW file; imports read-only save the `Dregg2.lean` root add.
-/
import Dregg2.Circuit.Emit.AutomataflCoord

namespace Dregg2.Circuit.Emit.AutomataflStepCoord

open Dregg2.Circuit.Emit.AutomataflStepEmit
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric (OneHotAt)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Circuit.Emit.AutomataflStepRefine
  (Canon canon_zero canon_one canon_two canon_three eq_of_modEq_canon bin_of_gate StepCanon canon_loc
   mem_fe_oneHotRow mem_fe_oneHotCol mem_fe_autoPin mem_fe_decompAX mem_fe_decompAY
   oneHot_bool oneHot_sigma oneHot_index decomp_loBit decomp_loHead decomp_hiBit decomp_hiHead)
open Dregg2.Circuit.Emit.AutomataflCoord
  (varsVal termVal foldl_mul_eval foldl_add_eval sum_filter_termVal sum_map_mul_left sum_bool_bounds
   oneHot_exists dot_oneHot dot_oneHot2 bitSum_bounds)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## §1 — The STEP `evalH` bridge: `(AutomataflStepEmit.headToExpr h).eval a = evalHStep h a`.

`varsVal` / `termVal` are PURE (`ℤ`-valued, no `Head` in sight) so they are REUSED from
`AutomataflCoord` verbatim — only the `Head`-typed layer is duplicated, and only because the two
emitters carry two distinct `Head` types. -/

/-- The clean semantic value of a STEP `Head`: `Σ termⱼ + const`, over ALL terms (zero-coeff included
— they contribute `0`, matching the filtered `headToExpr`). -/
def evalHStep (h : Head) (a : Nat → ℤ) : ℤ := (h.terms.map (termVal a)).sum + h.const

theorem varsProdStep_eval (a : Nat → ℤ) (cols : List Nat) :
    (varsProd cols).eval a = varsVal a cols := by
  cases cols with
  | nil => rfl
  | cons co rest =>
      show (rest.foldl (fun acc v => EmittedExpr.mul acc (.var v)) (.var co)).eval a
        = varsVal a (co :: rest)
      rw [foldl_mul_eval]
      rfl

/-- ⚑ RE-PROVED FOR THE CANONICAL RENDERER (2026-08-06): one arm, not two. -/
theorem termToExprStep_eval (a : Nat → ℤ) (t : ℤ × List Nat) :
    (termToExpr t).eval a = termVal a t := by
  obtain ⟨coeff, cols⟩ := t
  cases cols with
  | nil => simp [termToExpr, Dregg2.Circuit.GateExpr.gTermToExpr, AutomataflCoord.termVal,
      AutomataflCoord.varsVal, EmittedExpr.eval]
  | cons co rest =>
      show (EmittedExpr.mul (.const coeff) (varsProd (co :: rest))).eval a
        = termVal a (coeff, co :: rest)
      simp only [EmittedExpr.eval, varsProdStep_eval, AutomataflCoord.termVal]

/-- The list of component `EmittedExpr`s the STEP `headToExpr` folds. ⚑ EVERY term plus a possible
constant — the zero-coeff filter went with the flag day of 2026-08-06. -/
def headExprsStep (h : Head) : List EmittedExpr :=
  h.terms.map termToExpr ++ (if h.const = 0 then [] else [.const h.const])

/-- The STEP `headToExpr`'s `.add`-fold, over an explicit list. -/
def foldExprsStep : List EmittedExpr → EmittedExpr :=
  Dregg2.Circuit.GateExpr.gFoldExprs Dregg2.Circuit.GateExpr.toEmitted

theorem headToExprStep_eq_foldExprs (h : Head) : headToExpr h = foldExprsStep (headExprsStep h) := rfl

theorem foldExprsStep_eval (a : Nat → ℤ) (ts : List EmittedExpr) :
    (foldExprsStep ts).eval a = (ts.map (fun x => x.eval a)).sum := by
  cases ts with
  | nil => show (EmittedExpr.const 0).eval a = _; simp [EmittedExpr.eval]
  | cons e rest =>
      show (rest.foldl (fun acc x => EmittedExpr.add acc x) e).eval a = _
      rw [foldl_add_eval]; simp [List.map_cons, List.sum_cons]

theorem headExprsStep_termPart_sum (a : Nat → ℤ) (h : Head) :
    ((h.terms.map termToExpr).map (fun x => x.eval a)).sum = (h.terms.map (termVal a)).sum := by
  rw [List.map_map]
  exact congrArg List.sum (List.map_congr_left (fun t _ => termToExprStep_eval a t))

/-- **THE STEP BRIDGE.** The lowered STEP gate evaluates to the clean semantic sum, at ARBITRARY `n`.
This is the exact rewrite `oneHotStepN_of_sat` needs and `AutomataflCoord.headToExpr_eval` (typed on
`AutomataflResolveEmit.Head`) could not supply. -/
theorem headToExpr_evalStep (a : Nat → ℤ) (h : Head) :
    (headToExpr h).eval a = evalHStep h a := by
  rw [headToExprStep_eq_foldExprs, foldExprsStep_eval, headExprsStep, List.map_append,
    List.sum_append, headExprsStep_termPart_sum]
  by_cases hconst : h.const = 0
  · rw [if_pos hconst, evalHStep, hconst]; simp
  · rw [if_neg hconst]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EmittedExpr.eval, add_zero]
    rw [evalHStep]

/-! ## §1.5 — Incremental `evalHStep` combinator laws (compute any built STEP head, no AST unfolding). -/

theorem evalHStep_zero (a : Nat → ℤ) : evalHStep Head.zero a = 0 := by simp [evalHStep, Head.zero]
theorem evalHStep_c (a : Nat → ℤ) (k : ℤ) : evalHStep (Head.c k) a = k := by simp [evalHStep, Head.c]
theorem evalHStep_lin (a : Nat → ℤ) (c : ℤ) (col : Nat) : evalHStep (Head.lin c col) a = c * a col := by
  simp [evalHStep, Head.lin, AutomataflCoord.termVal, AutomataflCoord.varsVal]

theorem evalHStep_addLin (a : Nat → ℤ) (h : Head) (c : ℤ) (col : Nat) :
    evalHStep (h.addLin c col) a = evalHStep h a + c * a col := by
  simp only [evalHStep, Dregg2.Circuit.GateExpr.GHead.addLin, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, AutomataflCoord.termVal, AutomataflCoord.varsVal, List.foldl_nil,
    add_zero]
  ring

theorem evalHStep_addProd (a : Nat → ℤ) (h : Head) (c : ℤ) (cols : List Nat) :
    evalHStep (h.addProd c cols) a = evalHStep h a + c * varsVal a cols := by
  simp only [evalHStep, Dregg2.Circuit.GateExpr.GHead.addProd, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, AutomataflCoord.termVal, add_zero]
  ring

theorem evalHStep_addConst (a : Nat → ℤ) (h : Head) (k : ℤ) :
    evalHStep (h.addConst k) a = evalHStep h a + k := by
  simp only [evalHStep, Dregg2.Circuit.GateExpr.GHead.addConst]; ring

theorem evalHStep_append (a : Nat → ℤ) (h o : Head) :
    evalHStep (h.append o) a = evalHStep h a + evalHStep o a := by
  simp only [evalHStep, Dregg2.Circuit.GateExpr.GHead.append, List.map_append, List.sum_append]; ring

theorem evalHStep_scale (a : Nat → ℤ) (h : Head) (k : ℤ) :
    evalHStep (h.scale k) a = k * evalHStep h a := by
  simp only [evalHStep, Dregg2.Circuit.GateExpr.GHead.scale, List.map_map]
  have : (h.terms.map ((termVal a) ∘ (fun t => (t.1 * k, t.2))))
      = h.terms.map (fun t => k * termVal a t) := by
    apply List.map_congr_left; intro t _; simp only [Function.comp, AutomataflCoord.termVal]; ring
  rw [this, sum_map_mul_left]; ring

/-- The `Σ`-fold sum head (`Builder::one_hot`'s `Σ selⱼ`). NOTE the STEP emitter's binder name/order
(`fun h co => h.addLin 1 co`) — same shape, own lemma. -/
theorem evalHStep_foldl_addLin (a : Nat → ℤ) (init : Head) (sels : List Nat) :
    evalHStep (sels.foldl (fun h co => h.addLin 1 co) init) a
      = evalHStep init a + (sels.map a).sum := by
  induction sels generalizing init with
  | nil => simp
  | cons s ss ih =>
      rw [List.foldl_cons, ih, evalHStep_addLin]
      simp only [List.map_cons, List.sum_cons]; ring

/-- General coefficient-and-column `addLin` fold (the `range_nonneg` recomposition shape). -/
theorem evalHStep_foldl_addLinF (a : Nat → ℤ) (init : Head) (ks : List Nat)
    (coeff : Nat → ℤ) (colf : Nat → Nat) :
    evalHStep (ks.foldl (fun acc k => acc.addLin (coeff k) (colf k)) init) a
      = evalHStep init a + (ks.map (fun k => coeff k * a (colf k))).sum := by
  induction ks generalizing init with
  | nil => simp
  | cons k ks ih =>
      rw [List.foldl_cons, ih, evalHStep_addLin]
      simp only [List.map_cons, List.sum_cons]; ring

/-- A `foldl` whose every step adds a fixed `delta y` accumulates `Σ delta` — the general shape the
NESTED `autoPinHead` dot-product fold is built from. -/
theorem evalHStep_foldl_step (a : Nat → ℤ) (init : Head) (ys : List Nat) (step : Head → Nat → Head)
    (delta : Nat → ℤ) (hstep : ∀ h y, evalHStep (step h y) a = evalHStep h a + delta y) :
    evalHStep (ys.foldl step init) a = evalHStep init a + (ys.map delta).sum := by
  induction ys generalizing init with
  | nil => simp
  | cons y ys ih =>
      rw [List.foldl_cons, ih, hstep]
      simp only [List.map_cons, List.sum_cons]; ring

/-- **THE STRUCTURAL DIFFERENCE FROM RESOLVE, ABSORBED.** `AutomataflStepEmit.oneHotConstraints`'s
index gate folds `Σ j·sels[j]!` over `List.range sels.length` (a `getElem!` read), where
`AutomataflResolveEmit` folds over `sels.zipIdx`. This is the fold-value law for the STEP shape. -/
theorem evalHStep_foldl_idxBang (a : Nat → ℤ) (init : Head) (L : List Nat) (sels : List Nat) :
    evalHStep (L.foldl (fun h (j : Nat) => h.addLin (j : ℤ) (sels[j]!)) init) a
      = evalHStep init a + (L.map (fun (j : Nat) => (j : ℤ) * a (sels[j]!))).sum := by
  induction L generalizing init with
  | nil => simp
  | cons j js ih =>
      rw [List.foldl_cons, ih, evalHStep_addLin]
      simp only [List.map_cons, List.sum_cons]; ring

/-- `((range n).map f)[j]! = f j` for an in-range `j` — the `getElem!` discharge. -/
theorem getElem!_range_map (n : Nat) (f : Nat → Nat) {j : Nat} (hj : j < n) :
    ((List.range n).map f)[j]! = f j := by
  rw [List.getElem!_eq_getElem?_getD]
  simp [hj]

/-! ## §2 — `oneHotStepN_of_sat`: the STEP n-wide one-hot read primitive, ∀ n.

Descriptor-generic (any `d` carrying the three emitted `Builder::one_hot` gate families over
`sel j`, `j ∈ [0,n)`). Because the bridge is now `headToExpr_evalStep`, the rewrites go through
SYMBOLICALLY in `n` — the concrete-`n` `whnf` crutch is gone. -/

section OfSat
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace}

/-- Descriptor-generic single-row gate extraction, STEP vocabulary (`AutomataflStepEmit.cg`). -/
theorem sgate (hsat : Satisfied2 hash d minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {g : EmittedExpr} (hg : cg g ∈ d.constraints) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hg
  have hlf : (i + 1 == t.rows.length) = false := by
    have h : i + 1 ≠ t.rows.length := by omega
    simpa using h
  simpa only [cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- `Head` form of `sgate`. -/
theorem sgateH (hsat : Satisfied2 hash d minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {h : Head} (hg : cgH h ∈ d.constraints) :
    (headToExpr h).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] :=
  sgate hsat i hi hg

/-- **`oneHotStepN_of_sat` — the ∀-n STEP one-hot read primitive.** The three gate hypotheses are
LITERALLY what `AutomataflStepRefine.oneHot_bool` / `oneHot_sigma` / `oneHot_index` produce at
`sels := (List.range n).map sel`, `idxHead := Head.lin 1 idxCol`. -/
theorem oneHotStepN_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (n : Nat) (hn : (n : ℤ) < 2013265921) (sel : Nat → Nat) (idxCol : Nat)
    (hbool : ∀ j, j < n → cg (gBin (sel j)) ∈ d.constraints)
    (hsumG : cgH (((List.range n).map sel).foldl (fun h co => h.addLin 1 co) (Head.c (-1)))
               ∈ d.constraints)
    (hidxG : cgH (((List.range ((List.range n).map sel).length).foldl
                    (fun h (j : Nat) => h.addLin (j : ℤ) (((List.range n).map sel)[j]!)) Head.zero).append
                    ((Head.lin 1 idxCol).scale (-1))) ∈ d.constraints) :
    ∃ af : Nat, af < n ∧ (envAt t i).loc idxCol = (af : ℤ)
      ∧ OneHotAt (fun j => (envAt t i).loc (sel j)) n af := by
  set e := envAt t i with he
  -- (a) every selector value is boolean
  have hb : ∀ j, j < n → e.loc (sel j) = 0 ∨ e.loc (sel j) = 1 := by
    intro j hj
    exact bin_of_gate (sgate hsat i hi (hbool j hj)) (canon_loc hc i _)
  -- (b) Σ selⱼ = 1 over ℤ (the no-wrap window `n < p` makes the field congruence an equality)
  have hSsum : ((List.range n).map (fun j => e.loc (sel j))).sum = 1 := by
    have hg := sgateH hsat i hi hsumG
    rw [headToExpr_evalStep, evalHStep_foldl_addLin, evalHStep_c, List.map_map] at hg
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
    have hg := sgateH hsat i hi hidxG
    rw [headToExpr_evalStep, evalHStep_append, evalHStep_foldl_idxBang, evalHStep_zero,
      evalHStep_scale, evalHStep_lin] at hg
    simp only [List.length_map, List.length_range] at hg
    -- the `getElem!` reads resolve to `sel j` on `[0, n)`
    have hcong : ((List.range n).map (fun (j : Nat) => (j : ℤ) * e.loc (((List.range n).map sel)[j]!)))
        = (List.range n).map (fun j : Nat => (j : ℤ) * e.loc (sel j)) := by
      apply List.map_congr_left; intro j hj
      rw [getElem!_range_map n sel (List.mem_range.mp hj)]
    rw [hcong] at hg
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

/-! ## §3 — `coordNStep_of_sat`: the STEP `decompose_coord_le` no-wrap decode, ∀ n. -/

/-- **`coordNStep_of_sat`.** Under the explicit no-wrap window `hwin` the decoded coordinate is a
genuine board index in `[0, n)`. STEP-typed mirror of `AutomataflCoord.coordN_of_sat`. -/
theorem coordNStep_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
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
  have hpow_split : (2 : ℤ) ^ (rbits + 1) = 2 ^ rbits + 2 ^ rbits := by rw [pow_succ]; ring
  have hpow_le : (2 : ℤ) ^ rbits ≤ 2013265921 := by
    have : (0 : ℤ) ≤ 2 ^ rbits := by positivity
    nlinarith [hwin, hpow_split]
  set Slo := ((List.range rbits).map (fun k => (2 ^ k : ℤ) * e.loc (loBit0 + k))).sum with hSlo
  have hlob : ∀ k, k < rbits → e.loc (loBit0 + k) = 0 ∨ e.loc (loBit0 + k) = 1 := fun k hk =>
    bin_of_gate (sgate hsat i hi (hlobit k hk)) (canon_loc hc i _)
  obtain ⟨hSlo0, hSlo1⟩ := bitSum_bounds (fun c => e.loc c) loBit0 rbits hlob
  have hcolSlo : e.loc col = Slo := by
    have hg := sgateH hsat i hi hlohead
    rw [headToExpr_evalStep, evalHStep_foldl_addLinF, evalHStep_lin] at hg
    have hstep : (1 * e.loc col + ((List.range rbits).map
            (fun k => -((2 : ℤ) ^ k) * e.loc (loBit0 + k))).sum) ≡ 0 [ZMOD 2013265921] := hg
    have hneg : ((List.range rbits).map (fun k => -((2 : ℤ) ^ k) * e.loc (loBit0 + k))).sum = -Slo := by
      rw [hSlo, show (fun k => -((2 : ℤ) ^ k) * e.loc (loBit0 + k))
          = (fun k => (-1 : ℤ) * ((2 : ℤ) ^ k * e.loc (loBit0 + k))) from by funext k; ring,
        sum_map_mul_left]
      ring
    rw [hneg] at hstep
    have hmod : e.loc col ≡ Slo [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hstep
    refine eq_of_modEq_canon (canon_loc hc i _) ⟨hSlo0, ?_⟩ hmod
    calc Slo ≤ 2 ^ rbits - 1 := hSlo1
      _ < 2013265921 := by linarith [hpow_le]
  set Shi := ((List.range rbits).map (fun k => (2 ^ k : ℤ) * e.loc (hiBit0 + k))).sum with hShi
  have hhib : ∀ k, k < rbits → e.loc (hiBit0 + k) = 0 ∨ e.loc (hiBit0 + k) = 1 := fun k hk =>
    bin_of_gate (sgate hsat i hi (hhibit k hk)) (canon_loc hc i _)
  obtain ⟨hShi0, hShi1⟩ := bitSum_bounds (fun c => e.loc c) hiBit0 rbits hhib
  have hsumEq : Slo + Shi = (n : ℤ) - 1 := by
    have hg := sgateH hsat i hi hhihead
    rw [headToExpr_evalStep, evalHStep_foldl_addLinF, evalHStep_addLin, evalHStep_c] at hg
    have hneg : ((List.range rbits).map (fun k => -((2 : ℤ) ^ k) * e.loc (hiBit0 + k))).sum = -Shi := by
      rw [hShi, show (fun k => -((2 : ℤ) ^ k) * e.loc (hiBit0 + k))
          = (fun k => (-1 : ℤ) * ((2 : ℤ) ^ k * e.loc (hiBit0 + k))) from by funext k; ring,
        sum_map_mul_left]
      ring
    rw [hneg, hcolSlo] at hg
    have hmod : ((n : ℤ) - 1) ≡ (Slo + Shi) [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hg
    have heq : (n : ℤ) - 1 = Slo + Shi := by
      refine eq_of_modEq_canon ⟨by linarith [hn1], by linarith [hn]⟩ ⟨by linarith, ?_⟩ hmod
      have hle : Slo + Shi ≤ (2 ^ rbits - 1) + (2 ^ rbits - 1) := by linarith [hSlo1, hShi1]
      calc Slo + Shi ≤ (2 ^ rbits - 1) + (2 ^ rbits - 1) := hle
        _ = 2 ^ (rbits + 1) - 2 := by rw [hpow_split]; ring
        _ < 2013265921 := by linarith [hwin]
    exact heq.symm
  have hcol0 : 0 ≤ e.loc col := by rw [hcolSlo]; exact hSlo0
  have hcolLt : e.loc col ≤ (n : ℤ) - 1 := by rw [hcolSlo]; linarith [hShi0, hsumEq]
  refine ⟨(e.loc col).toNat, ?_, ?_⟩
  · have : (e.loc col).toNat ≤ n - 1 := by omega
    omega
  · rw [Int.toNat_of_nonneg hcol0]

end OfSat

/-! ## §3.5 — `coordStepN_of_sat`: `AX`/`AY ∈ [0, n)` off `Satisfied2 (automataflStepDescN n)`, ∀ n.

This REPLACES the concrete `AutomataflCoord.coordStep_n3_of_sat` / `coordStep_n11_of_sat` pair (which
only typechecked because at a fixed numeral the RESOLVE-typed `coordN_of_sat`'s `cgH` reduced to the
STEP gate). The no-wrap window is an EXPLICIT hypothesis on the board size, discharged by `decide` at
any concrete `n` (`n = 3`: `COORD_RBITS 3 = 2`, `2^3 ≤ p`; `n = 11`: `COORD_RBITS 11 = 4`, `2^5 ≤ p`). -/

section StepCoordN
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

open Dregg2.Circuit.Emit.AutomataflStepEmit.NGen (AX AY axLoBit axHiBit ayLoBit ayHiBit COORD_RBITS)

/-- **`coordStepN_of_sat` — ∀ n.** On a satisfying, canonical `automataflStepDescN n` trace the
witnessed auto `AX`/`AY` are genuine `n × n`-board indices in `[0, n)`. -/
theorem coordStepN_of_sat (n : Nat) (hn1 : 1 ≤ n) (hn : (n : ℤ) < 2013265921)
    (hwin : (2 : ℤ) ^ (COORD_RBITS n + 1) ≤ 2013265921)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (∃ vx : Nat, vx < n ∧ (envAt t i).loc (AX n) = (vx : ℤ))
      ∧ (∃ vy : Nat, vy < n ∧ (envAt t i).loc (AY n) = (vy : ℤ)) :=
  ⟨coordNStep_of_sat hsat hc i hi n (COORD_RBITS n) (AX n) (axLoBit n) (axHiBit n) hn1 hn hwin
      (fun _ hk => mem_fe_decompAX (decomp_loBit hk)) (mem_fe_decompAX decomp_loHead)
      (fun _ hk => mem_fe_decompAX (decomp_hiBit hk)) (mem_fe_decompAX decomp_hiHead),
   coordNStep_of_sat hsat hc i hi n (COORD_RBITS n) (AY n) (ayLoBit n) (ayHiBit n) hn1 hn hwin
      (fun _ hk => mem_fe_decompAY (decomp_loBit hk)) (mem_fe_decompAY decomp_loHead)
      (fun _ hk => mem_fe_decompAY (decomp_hiBit hk)) (mem_fe_decompAY decomp_hiHead)⟩

/-! ## §4 — `autoPinStepN_of_sat`: the AUTO pin at ARBITRARY `n`, off the STEP descriptor. -/

/-- The STEP AUTO-pin head evaluates to `−AUTO + Σ_y Σ_x selRow[y]·selCol[x]·old[y·n+x]`. -/
theorem evalHStep_autoPinHead (a : Nat → ℤ) (n : Nat) :
    evalHStep (NGen.autoPinHead n) a
      = -AUTO + ((List.range n).map (fun y => ((List.range n).map (fun x =>
          a (NGen.selRow n y) * a (NGen.selCol n x) * a (NGen.old n (y * n + x)))).sum)).sum := by
  have hstep_outer : ∀ (h : Head) (y : Nat),
      evalHStep ((List.range n).foldl (fun h2 x =>
          h2.addProd 1 [NGen.selRow n y, NGen.selCol n x, NGen.old n (y * n + x)]) h) a
        = evalHStep h a + ((List.range n).map (fun x =>
            a (NGen.selRow n y) * a (NGen.selCol n x) * a (NGen.old n (y * n + x)))).sum := by
    intro h y
    refine evalHStep_foldl_step a h (List.range n) _
      (fun x => a (NGen.selRow n y) * a (NGen.selCol n x) * a (NGen.old n (y * n + x))) ?_
    intro h2 x
    rw [evalHStep_addProd]
    simp only [AutomataflCoord.varsVal, one_mul, List.foldl_cons, List.foldl_nil]
  rw [NGen.autoPinHead,
    evalHStep_foldl_step a (Head.c (-AUTO)) (List.range n) _ _ hstep_outer, evalHStep_c]

/-- **`autoPinStepN_of_sat` — ∀ n.** The witnessed auto `(AX, AY)` is in `[0, n)` and the OLD board
holds `AUTO` there, at ARBITRARY `n`, off `Satisfied2 (automataflStepDescN n)`. The ∀-n twin of
`AutomataflStepRefine.autoPin_of_sat` (whose four-way `rcases` over a 2×2 board this replaces). -/
theorem autoPinStepN_of_sat (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ∃ X Y : Nat, X < n ∧ Y < n
      ∧ (envAt t i).loc (AX n) = (X : ℤ) ∧ (envAt t i).loc (AY n) = (Y : ℤ)
      ∧ (envAt t i).loc (NGen.old n (Y * n + X)) = AUTO := by
  set e := envAt t i with he
  obtain ⟨ay, hayLt, hayEq, hrow⟩ :=
    oneHotStepN_of_sat hsat hc i hi n hn (NGen.selRow n) (AY n)
      (fun j hj => mem_fe_oneHotRow
        (oneHot_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
      (mem_fe_oneHotRow oneHot_sigma)
      (mem_fe_oneHotRow oneHot_index)
  obtain ⟨ax, haxLt, haxEq, hcol⟩ :=
    oneHotStepN_of_sat hsat hc i hi n hn (NGen.selCol n) (AX n)
      (fun j hj => mem_fe_oneHotCol
        (oneHot_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
      (mem_fe_oneHotCol oneHot_sigma)
      (mem_fe_oneHotCol oneHot_index)
  rw [← he] at hayEq haxEq
  have hg := sgateH hsat i hi (mem_fe_autoPin (n := n))
  rw [headToExpr_evalStep, evalHStep_autoPinHead] at hg
  rw [dot_oneHot2 hrow hcol (fun y x => e.loc (NGen.old n (y * n + x)))] at hg
  have hmod : e.loc (NGen.old n (ay * n + ax)) ≡ AUTO [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hg
  have hcell : e.loc (NGen.old n (ay * n + ax)) = AUTO :=
    eq_of_modEq_canon (canon_loc hc i _) canon_three hmod
  exact ⟨ax, ay, haxLt, hayLt, haxEq, hayEq, hcell⟩

end StepCoordN

/-! ## §4.5 — `dot_oneHotStep`: the step-side name for the one-hot collapse.

`dot_oneHot` / `dot_oneHot2` are PURE (`OneHotAt` + a payload; no `Head`, no emitter), so unlike the
`evalH` bridge they need no duplication — the STEP side consumes the SAME theorem. Named here so the
step lane has a stable handle. -/

theorem dot_oneHotStep {v : Nat → ℤ} {n i : Nat} (hv : OneHotAt v n i) (payload : Nat → ℤ) :
    ((List.range n).map (fun j => v j * payload j)).sum = payload i := dot_oneHot hv payload

theorem dot_oneHotStep2 {rv cv : Nat → ℤ} {n ay ax : Nat}
    (hr : OneHotAt rv n ay) (hcv : OneHotAt cv n ax) (cell : Nat → Nat → ℤ) :
    ((List.range n).map (fun y =>
        ((List.range n).map (fun x => rv y * cv x * cell y x)).sum)).sum = cell ay ax :=
  dot_oneHot2 hr hcv cell

/-! ## §5 — NON-VACUITY at `n = 3`: the STEP window discharges, and the pin is TWO-SIDED.

`coordStepN_of_sat`'s no-wrap window is a REAL side condition, not decoration: it discharges at the
board sizes we deploy. And the AUTO pin genuinely BITES — with the same one-hots, a board whose
selected cell is vacuum FAILS the gate. -/

/-- The `n = 3` no-wrap window discharges (`COORD_RBITS 3 = 2`). -/
theorem stepWindow_n3 : (2 : ℤ) ^ (NGen.COORD_RBITS 3 + 1) ≤ 2013265921 := by decide

/-- The deployed `n = 11` no-wrap window discharges (`COORD_RBITS 11 = 4`). -/
theorem stepWindow_n11 : (2 : ℤ) ^ (NGen.COORD_RBITS 11 + 1) ≤ 2013265921 := by decide

/-- **CORRECT auto cell ACCEPTED** at `n = 3`: the collapse yields `AUTO`, so `−AUTO + collapse = 0`. -/
theorem autoPinStep_n3_accepts_correct :
    -AUTO + ((List.range 3).map (fun y => ((List.range 3).map (fun x =>
        (if y = 1 then (1 : ℤ) else 0) * (if x = 2 then (1 : ℤ) else 0)
          * (if y = 1 ∧ x = 2 then AUTO else 0))).sum)).sum = 0 := by
  rw [dot_oneHotStep2 AutomataflCoord.oneHotAt3_1 AutomataflCoord.oneHotAt3_2
    (fun y x => if y = 1 ∧ x = 2 then AUTO else 0)]
  norm_num [AUTO]

/-- **WRONG auto cell REJECTED** at `n = 3`: the same one-hots over a board whose `(1,2)` cell is
vacuum collapse to `0`, so the pin gate is `−AUTO ≠ 0` — the wrong auto cell is refused. -/
theorem autoPinStep_n3_rejects_wrong :
    -AUTO + ((List.range 3).map (fun y => ((List.range 3).map (fun x =>
        (if y = 1 then (1 : ℤ) else 0) * (if x = 2 then (1 : ℤ) else 0)
          * (if y = 0 ∧ x = 0 then AUTO else 0))).sum)).sum ≠ 0 := by
  rw [dot_oneHotStep2 AutomataflCoord.oneHotAt3_1 AutomataflCoord.oneHotAt3_2
    (fun y x => if y = 0 ∧ x = 0 then AUTO else 0)]
  norm_num [AUTO]

/-! ## §5.5 — The ∀-n results INSTANTIATE (the window is dischargeable, the hypotheses are not
unreachable), and the RAY-family heads now COMPUTE symbolically — the concrete unblock for the
ray-of-sat wiring lane. -/

section Instantiations
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- `coordStepN_of_sat` at `n = 3` — the ∀-n theorem SUBSUMES the old concrete `coordStep_n3_of_sat`,
window and all. -/
theorem coordStep_n3 (hsat : Satisfied2 hash (automataflStepDescN 3) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (∃ vx : Nat, vx < 3 ∧ (envAt t i).loc (NGen.AX 3) = (vx : ℤ))
      ∧ (∃ vy : Nat, vy < 3 ∧ (envAt t i).loc (NGen.AY 3) = (vy : ℤ)) :=
  coordStepN_of_sat 3 (by norm_num) (by norm_num) stepWindow_n3 hsat hc i hi

/-- `coordStepN_of_sat` at the deployed `n = 11` — SUBSUMES the old concrete `coordStep_n11_of_sat`. -/
theorem coordStep_n11 (hsat : Satisfied2 hash (automataflStepDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (∃ vx : Nat, vx < 11 ∧ (envAt t i).loc (NGen.AX 11) = (vx : ℤ))
      ∧ (∃ vy : Nat, vy < 11 ∧ (envAt t i).loc (NGen.AY 11) = (vy : ℤ)) :=
  coordStepN_of_sat 11 (by norm_num) (by norm_num) stepWindow_n11 hsat hc i hi

/-- `autoPinStepN_of_sat` at the deployed `n = 11`. -/
theorem autoPinStep_n11 (hsat : Satisfied2 hash (automataflStepDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ∃ X Y : Nat, X < 11 ∧ Y < 11
      ∧ (envAt t i).loc (NGen.AX 11) = (X : ℤ) ∧ (envAt t i).loc (NGen.AY 11) = (Y : ℤ)
      ∧ (envAt t i).loc (NGen.old 11 (Y * 11 + X)) = AUTO :=
  autoPinStepN_of_sat 11 (by norm_num) hsat hc i hi

end Instantiations

/-- **THE RAY UNBLOCK, DEMONSTRATED (1).** The ray's hit one-hot `Σ hit_kk == 1` head — a
`List.range' 1 n` fold, i.e. a genuine RAY-family head at SYMBOLIC `n` — now evaluates to its clean
semantic sum. Before the step bridge this `rw` could not even fire. -/
theorem evalHStep_rayHitSum (a : Nat → ℤ) (n d : Nat) :
    evalHStep ((List.range' 1 n).foldl (fun h (kk : Nat) => h.addLin 1 (NGen.rHit n d kk))
        (Head.c (-1))) a
      = -1 + ((List.range' 1 n).map (fun kk => a (NGen.rHit n d kk))).sum := by
  rw [evalHStep_foldl_addLinF a (Head.c (-1)) (List.range' 1 n) (fun _ => 1)
    (fun kk => NGen.rHit n d kk), evalHStep_c]
  simp

/-- **THE RAY UNBLOCK, DEMONSTRATED (2).** The ray's `dist = Σ kk·hit_kk` head, symbolically in `n`. -/
theorem evalHStep_rayDist (a : Nat → ℤ) (n d : Nat) :
    evalHStep ((List.range' 1 n).foldl (fun h (kk : Nat) => h.addLin (kk : ℤ) (NGen.rHit n d kk))
        (Head.lin (-1) (NGen.rDist n d))) a
      = -a (NGen.rDist n d) + ((List.range' 1 n).map (fun (kk : Nat) => (kk : ℤ) * a (NGen.rHit n d kk))).sum := by
  rw [evalHStep_foldl_addLinF a (Head.lin (-1) (NGen.rDist n d)) (List.range' 1 n)
    (fun kk => (kk : ℤ)) (fun kk => NGen.rHit n d kk), evalHStep_lin]
  ring

/-- **THE RAY UNBLOCK, DEMONSTRATED (3).** The ray's `what = Σ hit_kk·rc_kk` head — a PRODUCT fold —
symbolically in `n`. -/
theorem evalHStep_rayWhat (a : Nat → ℤ) (n d : Nat) :
    evalHStep ((List.range' 1 n).foldl
        (fun h (kk : Nat) => h.addProd 1 [NGen.rHit n d kk, NGen.rRc n d kk])
        (Head.lin (-1) (NGen.rWhat n d))) a
      = -a (NGen.rWhat n d)
        + ((List.range' 1 n).map (fun kk => a (NGen.rHit n d kk) * a (NGen.rRc n d kk))).sum := by
  rw [evalHStep_foldl_step a (Head.lin (-1) (NGen.rWhat n d)) (List.range' 1 n) _
      (fun kk => a (NGen.rHit n d kk) * a (NGen.rRc n d kk))
      (by intro h kk; rw [evalHStep_addProd]
          simp only [AutomataflCoord.varsVal, one_mul, List.foldl_cons, List.foldl_nil]),
    evalHStep_lin]
  ring

/-! ## §6 — Axiom pins. -/

#assert_axioms headToExpr_evalStep
#assert_axioms evalHStep_foldl_idxBang
#assert_axioms getElem!_range_map
#assert_axioms oneHotStepN_of_sat
#assert_axioms coordNStep_of_sat
#assert_axioms coordStepN_of_sat
#assert_axioms autoPinStepN_of_sat
#assert_axioms autoPinStep_n3_accepts_correct
#assert_axioms autoPinStep_n3_rejects_wrong
#assert_axioms coordStep_n3
#assert_axioms coordStep_n11
#assert_axioms autoPinStep_n11
#assert_axioms evalHStep_rayHitSum
#assert_axioms evalHStep_rayDist
#assert_axioms evalHStep_rayWhat

end Dregg2.Circuit.Emit.AutomataflStepCoord
