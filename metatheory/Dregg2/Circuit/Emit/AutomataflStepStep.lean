/-
# LEG (5) at ARBITRARY board size `n`: the gated row×column target read, the step guards, the
board-update fold, and the automaton-step CAPSTONE.

`AutomataflStepRefine`'s leg-5 chain (`tread_of_sat`, `seltarg_of_sat`, `autosel_of_sat`,
`boardupd_of_sat`, `cell_of_data`) writes the `read_rowcol_gated` target read and the board-update
fold as explicit 2×2 SELECTOR SUMS — every selector a numeral, every `.eval = <sum> from rfl`.
At arbitrary `n` both are `n`-wide folds. This file lands:

* §1 — the `evalHStep` closed forms for `idxGatedHead` and `readRowcolHead` (the two heads the
  `n = 2` chain only ever evaluated by `rfl` at numerals), plus the `varsVal` cons law.
* §2 — the step block's SEGMENT MEMBERSHIP for the read/update one-hots and the read dot-product.
* §3 — **THE n-WIDE GATED ONE-HOT / ROW×COLUMN DOT-PRODUCT PRIMITIVE**
  (`oneHotGatedStepN_of_sat`, `rowcolReadN_of_sat`): a `one_hot_gated` family forces its selectors
  to `0` when the gate is `0`, and to a genuine `OneHotAt` at the (mod-`p`) pinned index when the
  gate is `1`; the gated read then collapses the double sum to the single selected cell.
* §4 — `tibN_of_sat` (the four edge guards + their product), `treadN_of_sat` /
  `tcellTargetN_of_sat` (the target read IS `old[(ay+oy)·n + (ax+ox)]`), `targVacN_of_sat`,
  `movedN_of_sat` / `movedIffGuardN_of_sat` (`m = offnz·tib·targ_vac` IS the reference guard).
* §5 — `boardupdN_of_sat` (the per-cell update equality at symbolic `c`) and `cellN_of_data`
  (the decoded three-way `stepTo` match, `n`-generic — the `n = 2` `selv` enumeration is gone).
* §6 — **THE CAPSTONE** `astep_sat_imp_automatonStepN`, cell-wise over `range n × range n`,
  instantiated at `n = 3` and the deployed `n = 11`.

CEILINGS (stated, not papered over): the composition consumes `automatonOffset_of_satN`, which
carries the `n ≤ 99` SCORE_ATT radix ceiling (defect #9) and the `SMALL_RBITS = 5` decide-axis
satisfiability ceiling documented in `AutomataflStepBackend`. Everything in §1–§5 that does not
touch the offset SEMANTICS is free of both.
-/
import Dregg2.Circuit.Emit.AutomataflStepChoose
import Dregg2.Games.AutomataflRules

namespace Dregg2.Circuit.Emit.AutomataflStepStep

open Dregg2.Circuit.Emit.AutomataflStepEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Circuit.Emit.AutomataflStepRefine
open Dregg2.Circuit.Emit.AutomataflStepCoord
open Dregg2.Circuit.Emit.AutomataflStepBackend
open Dregg2.Circuit.Emit.AutomataflStepChoose
open Dregg2.Circuit.Emit.AutomataflStepCapstone (boardDecodeN)
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric (OneHotAt)
open Dregg2.Circuit.Emit.AutomataflCoord
  (varsVal termVal sum_map_mul_left dot_oneHot dot_oneHot2 oneHot_exists sum_bool_bounds)
open Dregg2.Games.Automatafl (Board Coord Particle automatonStep stepTo automatonOffset)

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §1 — the two head closed forms the `n = 2` chain never needed. -/

/-- `varsVal` is multiplicative in its head column — the law that turns the `gate :: t.2` prefix
`idxGatedHead` puts on every term into a clean `a gate * …` factor. -/
theorem varsVal_cons (a : Nat → ℤ) (co : Nat) (rest : List Nat) :
    varsVal a (co :: rest) = a co * varsVal a rest := by
  cases rest with
  | nil => simp [varsVal]
  | cons c2 r2 =>
      show r2.foldl (fun acc v => acc * a v) (a co * a c2)
        = a co * r2.foldl (fun acc v => acc * a v) (a c2)
      have key : ∀ (L : List Nat) (k x : ℤ),
          L.foldl (fun acc v => acc * a v) (k * x) = k * L.foldl (fun acc v => acc * a v) x := by
        intro L
        induction L with
        | nil => intro k x; rfl
        | cons c L ih => intro k x; simp only [List.foldl_cons]; rw [mul_assoc, ih]
      exact key r2 (a co) (a c2)

theorem varsVal_triple (a : Nat → ℤ) (x y z : Nat) : varsVal a [x, y, z] = a x * a y * a z := by
  rw [varsVal_cons, varsVal_cons, varsVal_cons]; simp [varsVal]; ring

theorem varsVal_quad (a : Nat → ℤ) (w x y z : Nat) :
    varsVal a [w, x, y, z] = a w * a x * a y * a z := by
  rw [varsVal_cons, varsVal_cons, varsVal_cons, varsVal_cons]; simp [varsVal]; ring

/-- `evalHStep_foldl_step` at an ARBITRARY element type (the `idxGatedHead` fold runs over
`List (ℤ × List Nat)`, not `List Nat`). -/
theorem evalHStep_foldlG {α : Type} (a : Nat → ℤ) (init : Head) (ys : List α)
    (step : Head → α → Head) (delta : α → ℤ)
    (hstep : ∀ h y, evalHStep (step h y) a = evalHStep h a + delta y) :
    evalHStep (ys.foldl step init) a = evalHStep init a + (ys.map delta).sum := by
  induction ys generalizing init with
  | nil => simp
  | cons y ys ih =>
      rw [List.foldl_cons, ih, hstep]
      simp only [List.map_cons, List.sum_cons]; ring

/-- **The `one_hot_gated` index-gate closed form, ANY index head.** `Σ j·sel_j − gate·⟦idxHead⟧`.
The `n = 2` chain could only get this by `rfl` at explicit numerals. -/
theorem evalHStep_idxGatedHead (a : Nat → ℤ) (sels : List Nat) (gate : Nat) (ih : Head) :
    evalHStep (idxGatedHead sels gate ih) a
      = ((List.range sels.length).map (fun (j : Nat) => (j : ℤ) * a (sels[j]!))).sum
        - a gate * evalHStep ih a := by
  unfold idxGatedHead
  rw [evalHStep_addProd,
    evalHStep_foldlG a _ ih.terms _ (fun t => -t.1 * (a gate * varsVal a t.2)) (by
      intro h y; rw [evalHStep_addProd, varsVal_cons]),
    evalHStep_foldl_idxBang, evalHStep_zero, varsVal_cons]
  have hsum : (ih.terms.map (fun t => -t.1 * (a gate * varsVal a t.2))).sum
      = -(a gate) * (ih.terms.map (termVal a)).sum := by
    rw [show (fun (t : ℤ × List Nat) => -t.1 * (a gate * varsVal a t.2))
        = (fun t => (-(a gate)) * termVal a t) from by funext t; simp [termVal]; ring,
      sum_map_mul_left]
  rw [hsum, evalHStep]
  simp [varsVal]
  ring

/-- **The `read_rowcol_gated` dot-product closed form.** `value − Σ_y Σ_x selRow[y]·selCol[x]·board[y·n+x]`,
as a TOTAL `List.range n × List.range n` double sum the one-hot collapse can eat. -/
theorem evalHStep_readRowcolHead (a : Nat → ℤ) (selRow selCol board : List Nat) (n value : Nat) :
    evalHStep (readRowcolHead selRow selCol board n value) a
      = a value - ((List.range n).map (fun (y : Nat) =>
          ((List.range n).map (fun (x : Nat) =>
            a (selRow[y]!) * a (selCol[x]!) * a (board[y * n + x]!))).sum)).sum := by
  have hinner : ∀ (h : Head) (y : Nat),
      evalHStep ((List.range n).foldl (fun (h2 : Head) (x : Nat) =>
          h2.addProd (-1) [selRow[y]!, selCol[x]!, board[y * n + x]!]) h) a
        = evalHStep h a + ((List.range n).map (fun (x : Nat) =>
            -(a (selRow[y]!) * a (selCol[x]!) * a (board[y * n + x]!)))).sum := by
    intro h y
    refine evalHStep_foldlG a h (List.range n) _ _ ?_
    intro h2 x
    rw [evalHStep_addProd, varsVal_triple]; ring
  rw [readRowcolHead, evalHStep_foldlG a (Head.lin 1 value) (List.range n) _ _ hinner,
    evalHStep_lin]
  have hneg : ∀ (y : Nat), ((List.range n).map (fun (x : Nat) =>
        -(a (selRow[y]!) * a (selCol[x]!) * a (board[y * n + x]!)))).sum
      = -(((List.range n).map (fun (x : Nat) =>
        a (selRow[y]!) * a (selCol[x]!) * a (board[y * n + x]!))).sum) := by
    intro y
    rw [show (fun (x : Nat) => -(a (selRow[y]!) * a (selCol[x]!) * a (board[y * n + x]!)))
        = (fun x => (-1 : ℤ) * (a (selRow[y]!) * a (selCol[x]!) * a (board[y * n + x]!)))
        from by funext x; ring, sum_map_mul_left]
    ring
  rw [show ((List.range n).map (fun (y : Nat) => ((List.range n).map (fun (x : Nat) =>
        -(a (selRow[y]!) * a (selCol[x]!) * a (board[y * n + x]!)))).sum))
      = ((List.range n).map (fun (y : Nat) => (-1 : ℤ) * ((List.range n).map (fun (x : Nat) =>
        a (selRow[y]!) * a (selCol[x]!) * a (board[y * n + x]!))).sum))
      from by apply List.map_congr_left; intro y _; rw [hneg y]; ring,
    sum_map_mul_left]
  ring

/-! ## §2 — segment membership: the step's two gated one-hots and the gated read. -/

/-- Membership inside a `one_hot_gated` block: the per-selector boolean gate. -/
theorem oneHotG_bool {sels : List Nat} {gate : Nat} {ih : Head} {co : Nat} (hco : co ∈ sels) :
    cg (gBin co) ∈ oneHotGatedConstraints sels gate ih := by
  unfold oneHotGatedConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨co, hco, rfl⟩))

/-- Membership inside a `one_hot_gated` block: `Σ sel == gate`. -/
theorem oneHotG_sigma {sels : List Nat} {gate : Nat} {ih : Head} :
    cgH (sels.foldl (fun h co => h.addLin 1 co) (Head.lin (-1) gate))
      ∈ oneHotGatedConstraints sels gate ih := by
  unfold oneHotGatedConstraints
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

/-- Membership inside a `one_hot_gated` block: the gated index pin. -/
theorem oneHotG_index {sels : List Nat} {gate : Nat} {ih : Head} :
    cgH (idxGatedHead sels gate ih) ∈ oneHotGatedConstraints sels gate ih := by
  unfold oneHotGatedConstraints
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

section StepMem
variable (n : Nat)

/-- The step's `read_rowcol_gated` block (`tib`-gated target read), inside `stepConstraints n`. -/
theorem mem_st_read {x : VmConstraint2}
    (h : x ∈ readRowcolGatedConstraints
          ((List.range n).map (fun j => NGen.A_STEP_BASE n + 26 + j))
          ((List.range n).map (fun j => NGen.A_STEP_BASE n + 26 + n + j))
          (NGen.A_STEP_BASE n + 24)
          ((Head.lin 1 (NGen.AX n)).addLin 1 (NGen.A_CHOOSE_BASE n + 55))
          ((Head.lin 1 (NGen.AY n)).addLin 1 (NGen.A_CHOOSE_BASE n + 56))
          ((List.range (NGen.KK n)).map (NGen.old n)) n (NGen.A_STEP_BASE n + 25)) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step; unfold NGen.stepConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_append_right _ h

/-- The `[tcell ≥ 1]` range gadget block (`nz`), inside `stepConstraints n`. -/
theorem mem_st_nz {x : VmConstraint2}
    (h : x ∈ forcedGe0Constraints (NGen.A_STEP_BASE n + 26 + 2 * n)
          ((Head.lin 1 (NGen.A_STEP_BASE n + 25)).addConst (-1))
          (bitsFrom (NGen.A_STEP_BASE n + 26 + 2 * n + 1) SMALL_RBITS)) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step; unfold NGen.stepConstraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ h

/-- The `sel_target` UPDATE row one-hot (gated by the move mask `m`), inside `stepConstraints n`. -/
theorem mem_st_updRow {x : VmConstraint2}
    (h : x ∈ oneHotGatedConstraints
          ((List.range n).map (fun j => NGen.A_STEP_BASE n + 35 + 2 * n + j))
          (NGen.A_STEP_BASE n + 34 + 2 * n)
          ((Head.lin 1 (NGen.AY n)).addLin 1 (NGen.A_CHOOSE_BASE n + 56))) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step; unfold NGen.stepConstraints
  apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_append_right _ h

/-- The `sel_target` UPDATE column one-hot (gated by `m`), inside `stepConstraints n`. -/
theorem mem_st_updCol {x : VmConstraint2}
    (h : x ∈ oneHotGatedConstraints
          ((List.range n).map (fun j => NGen.A_STEP_BASE n + 35 + 3 * n + j))
          (NGen.A_STEP_BASE n + 34 + 2 * n)
          ((Head.lin 1 (NGen.AX n)).addLin 1 (NGen.A_CHOOSE_BASE n + 55))) :
    x ∈ (automataflStepDescN n).constraints := by
  apply mem_be_step; unfold NGen.stepConstraints
  apply List.mem_append_left
  exact List.mem_append_right _ h

end StepMem

/-! ## §3 — THE n-WIDE GATED ONE-HOT / ROW×COLUMN DOT-PRODUCT PRIMITIVE.

This is the object the `n = 2` chain wrote out as explicit 2×2 selector sums (`selv`). Descriptor-
and column-generic, arbitrary `n`, MOD-AWARE in the index (the step's index heads are `ax + ox` with
`ox = p − 1`, a large field value). -/

section Primitive
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace}

/-- **`oneHotGatedStepN_of_sat` — the `∀ n` GATED one-hot.** A satisfied `Builder::one_hot_gated`
family forces its selectors to be identically `0` when the gate is `0`, and to be a genuine
`OneHotAt` at an index congruent to the pinned head when the gate is `1`. The three gate hypotheses
are LITERALLY what `oneHotG_bool` / `oneHotG_sigma` / `oneHotG_index` produce. -/
theorem oneHotGatedStepN_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (n : Nat) (hn : (n : ℤ) < 2013265921) (sel : Nat → Nat) (gate : Nat) (ih : Head)
    (hgb : (envAt t i).loc gate = 0 ∨ (envAt t i).loc gate = 1)
    (hbool : ∀ j, j < n → cg (gBin (sel j)) ∈ d.constraints)
    (hsumG : cgH (((List.range n).map sel).foldl (fun h co => h.addLin 1 co) (Head.lin (-1) gate))
               ∈ d.constraints)
    (hidxG : cgH (idxGatedHead ((List.range n).map sel) gate ih) ∈ d.constraints) :
    ((envAt t i).loc gate = 0 → ∀ j, j < n → (envAt t i).loc (sel j) = 0)
    ∧ ((envAt t i).loc gate = 1 → ∃ af : Nat, af < n
        ∧ ((af : ℤ) ≡ evalHStep ih (envAt t i).loc [ZMOD 2013265921])
        ∧ OneHotAt (fun j => (envAt t i).loc (sel j)) n af) := by
  set e := envAt t i with he
  have hb : ∀ j, j < n → e.loc (sel j) = 0 ∨ e.loc (sel j) = 1 := fun j hj =>
    bin_of_gate (sgate hsat i hi (hbool j hj)) (canon_loc hc i _)
  -- Σ selⱼ = gate over ℤ (the window `n < p` turns the field congruence into an equality)
  have hSsum : ((List.range n).map (fun j => e.loc (sel j))).sum = e.loc gate := by
    have hg := sgateH hsat i hi hsumG
    rw [headToExpr_evalStep, evalHStep_foldl_addLin, evalHStep_lin, List.map_map] at hg
    have hEq : (-1 * e.loc gate + ((List.range n).map ((fun j => e.loc (sel j)))).sum)
        ≡ 0 [ZMOD 2013265921] := by rw [← he] at hg; simpa [Function.comp_def] using hg
    have hmod : ((List.range n).map (fun j => e.loc (sel j))).sum ≡ e.loc gate [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hEq
    obtain ⟨hlo, hhi⟩ := sum_bool_bounds hb
    exact eq_of_modEq_canon ⟨hlo, lt_of_le_of_lt hhi hn⟩
      (by rcases hgb with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩) hmod
  refine ⟨?_, ?_⟩
  · -- gate = 0: every selector is 0 (nonneg booleans summing to 0)
    intro hg0 j hj
    rw [hg0] at hSsum
    have hnn : ∀ k, k < n → 0 ≤ e.loc (sel k) := by
      intro k hk; rcases hb k hk with h | h <;> rw [h] <;> norm_num
    by_contra hne
    have hj1 : e.loc (sel j) = 1 := (hb j hj).resolve_left hne
    have hmem : (1 : ℤ) ≤ ((List.range n).map (fun k => e.loc (sel k))).sum := by
      have : ((List.range n).map (fun k => e.loc (sel k))).sum
          = ((List.range n).map (fun k => if k = j then (1 : ℤ) else 0)).sum
            + ((List.range n).map (fun k => e.loc (sel k) - (if k = j then (1 : ℤ) else 0))).sum := by
        rw [← List.sum_map_add]; apply congrArg; apply List.map_congr_left; intro k _; ring
      rw [this]
      have h1 : ((List.range n).map (fun k => if k = j then (1 : ℤ) else 0)).sum = 1 := by
        have := AutomataflCoord.sum_map_mul_ite (List.range n) List.nodup_range j (fun _ => (1 : ℤ))
        simpa [List.mem_range.mpr hj] using this
      have h2 : 0 ≤ ((List.range n).map
          (fun k => e.loc (sel k) - (if k = j then (1 : ℤ) else 0))).sum := by
        apply List.sum_nonneg; intro z hz
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
        by_cases hkj : k = j
        · subst hkj; simp [hj1]
        · simp only [hkj, if_false, sub_zero]; exact hnn k (List.mem_range.mp hk)
      omega
    omega
  · -- gate = 1: a genuine one-hot, index congruent to the pinned head
    intro hg1
    rw [hg1] at hSsum
    obtain ⟨af, hone⟩ := oneHot_exists hb hSsum
    refine ⟨af, hone.1, ?_, hone⟩
    have hg := sgateH hsat i hi hidxG
    rw [headToExpr_evalStep, evalHStep_idxGatedHead] at hg
    simp only [List.length_map, List.length_range] at hg
    have hcong : ((List.range n).map
          (fun (j : Nat) => (j : ℤ) * e.loc (((List.range n).map sel)[j]!)))
        = (List.range n).map (fun j : Nat => (j : ℤ) * e.loc (sel j)) := by
      apply List.map_congr_left; intro j hj
      rw [getElem!_range_map n sel (List.mem_range.mp hj)]
    rw [hcong] at hg
    have hT : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (sel j))).sum = (af : ℤ) := by
      rw [show ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (sel j)))
          = (List.range n).map (fun j => (fun j => e.loc (sel j)) j * (j : ℤ))
          from by apply List.map_congr_left; intro j _; ring,
        dot_oneHot hone (fun j => (j : ℤ))]
    rw [hT, hg1, one_mul] at hg
    exact (gate_modEq_iff (by ring)).mp hg

end Primitive

/-! ## §4 — the STEP guards at arbitrary `n`: `tib`, the gated read, `targ_vac`, `m`. -/

section StepN
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`tibN_of_sat` — the target-in-bounds flag at ARBITRARY `n`.** The four `forced_ge0` edge
gadgets decide the four edges of `(ax+ox, ay+oy)` MOD `p` (`ox = p−1 ≡ −1` is a large felt, which is
exactly why `ge0RN_mod_of_sat` and not `ge0N_of_sat`), and `tib` is their product. -/
theorem tibN_of_sat (n : Nat) (hn1 : 1 ≤ n) (hn : (n : ℤ) < 2013265921)
    (hwin : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921) (hnsm : (n : ℤ) ≤ 1000000)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc (NGen.A_STEP_BASE n + 24) = 0
      ∨ (envAt t i).loc (NGen.A_STEP_BASE n + 24) = 1)
    ∧ ((envAt t i).loc (NGen.A_STEP_BASE n + 24) = 1 ↔
        (0 ≤ (envAt t i).loc (NGen.AX n)
              + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55))
          ∧ (envAt t i).loc (NGen.AX n)
              + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55)) ≤ (n : ℤ) - 1
          ∧ 0 ≤ (envAt t i).loc (NGen.AY n)
              + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))
          ∧ (envAt t i).loc (NGen.AY n)
              + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56)) ≤ (n : ℤ) - 1)) := by
  set e := envAt t i with he
  set S := NGen.A_STEP_BASE n with hS
  set OX := NGen.A_CHOOSE_BASE n + 55 with hOX
  set OY := NGen.A_CHOOSE_BASE n + 56 with hOY
  obtain ⟨⟨vx, hvxLt, hvxEq⟩, ⟨vy, hvyLt, hvyEq⟩⟩ := coordStepN_of_sat n hn1 hn hwin hsat hc i hi
  rw [← he] at hvxEq hvyEq
  obtain ⟨hoxtri, hoytri⟩ := offsetN_of_sat hsat hc i hi
  rw [← he, ← hOX] at hoxtri; rw [← he, ← hOY] at hoytri
  have hoxm := decodeOff_modEq hoxtri
  have hoym := decodeOff_modEq hoytri
  have hoxv := decodeOff_val hoxtri
  have hoyv := decodeOff_val hoytri
  have hvxB : (0 : ℤ) ≤ e.loc (NGen.AX n) ∧ e.loc (NGen.AX n) ≤ (n : ℤ) - 1 := by
    rw [hvxEq]; exact ⟨by positivity, by exact_mod_cast Nat.le_sub_one_of_lt hvxLt⟩
  have hvyB : (0 : ℤ) ≤ e.loc (NGen.AY n) ∧ e.loc (NGen.AY n) ≤ (n : ℤ) - 1 := by
    rw [hvyEq]; exact ⟨by positivity, by exact_mod_cast Nat.le_sub_one_of_lt hvyLt⟩
  have hR : (2 : ℤ) ^ SMALL_RBITS ≤ 100000000 := by norm_num [SMALL_RBITS]
  -- the four edge guards
  have e1 := ge0RN_mod_of_sat hsat hc i hi S (S + 1) SMALL_RBITS
    ((Head.lin 1 (NGen.AX n)).addLin 1 OX) (e.loc (NGen.AX n) + e.loc OX)
    (e.loc (NGen.AX n) + decodeOff (e.loc OX)) hR
    (mem_st_txlo n (mem_ge0_ib _ _ _))
    (fun k hk => mem_st_txlo n (mem_ge0_bit _ _ _ (mem_bitsFrom (S + 1) SMALL_RBITS k hk)))
    (by have h := mem_ge0_head S ((Head.lin 1 (NGen.AX n)).addLin 1 OX)
          (bitsFrom (S + 1) SMALL_RBITS)
        rw [bitsFrom_length] at h; exact mem_st_txlo n h)
    (by rw [evalHStep_addLin, evalHStep_lin]; ring)
    (Int.ModEq.add_left _ hoxm) (by rcases hoxv with h | h | h <;> rw [h] <;> omega)
    (by rcases hoxv with h | h | h <;> rw [h] <;> omega)
  have e2 := ge0RN_mod_of_sat hsat hc i hi (S + 6) (S + 7) SMALL_RBITS
    (((Head.c ((n : ℤ) - 1)).addLin (-1) (NGen.AX n)).addLin (-1) OX)
    (((n : ℤ) - 1) - e.loc (NGen.AX n) - e.loc OX)
    (((n : ℤ) - 1) - e.loc (NGen.AX n) - decodeOff (e.loc OX)) hR
    (mem_st_txhi n (mem_ge0_ib _ _ _))
    (fun k hk => mem_st_txhi n (mem_ge0_bit _ _ _ (mem_bitsFrom (S + 7) SMALL_RBITS k hk)))
    (by have h := mem_ge0_head (S + 6)
          (((Head.c ((n : ℤ) - 1)).addLin (-1) (NGen.AX n)).addLin (-1) OX)
          (bitsFrom (S + 7) SMALL_RBITS)
        rw [bitsFrom_length] at h; exact mem_st_txhi n h)
    (by rw [evalHStep_addLin, evalHStep_addLin, evalHStep_c]; ring)
    (Int.ModEq.sub_left _ hoxm) (by rcases hoxv with h | h | h <;> rw [h] <;> omega)
    (by rcases hoxv with h | h | h <;> rw [h] <;> omega)
  have e3 := ge0RN_mod_of_sat hsat hc i hi (S + 12) (S + 13) SMALL_RBITS
    ((Head.lin 1 (NGen.AY n)).addLin 1 OY) (e.loc (NGen.AY n) + e.loc OY)
    (e.loc (NGen.AY n) + decodeOff (e.loc OY)) hR
    (mem_st_tylo n (mem_ge0_ib _ _ _))
    (fun k hk => mem_st_tylo n (mem_ge0_bit _ _ _ (mem_bitsFrom (S + 13) SMALL_RBITS k hk)))
    (by have h := mem_ge0_head (S + 12) ((Head.lin 1 (NGen.AY n)).addLin 1 OY)
          (bitsFrom (S + 13) SMALL_RBITS)
        rw [bitsFrom_length] at h; exact mem_st_tylo n h)
    (by rw [evalHStep_addLin, evalHStep_lin]; ring)
    (Int.ModEq.add_left _ hoym) (by rcases hoyv with h | h | h <;> rw [h] <;> omega)
    (by rcases hoyv with h | h | h <;> rw [h] <;> omega)
  have e4 := ge0RN_mod_of_sat hsat hc i hi (S + 18) (S + 19) SMALL_RBITS
    (((Head.c ((n : ℤ) - 1)).addLin (-1) (NGen.AY n)).addLin (-1) OY)
    (((n : ℤ) - 1) - e.loc (NGen.AY n) - e.loc OY)
    (((n : ℤ) - 1) - e.loc (NGen.AY n) - decodeOff (e.loc OY)) hR
    (mem_st_tyhi n (mem_ge0_ib _ _ _))
    (fun k hk => mem_st_tyhi n (mem_ge0_bit _ _ _ (mem_bitsFrom (S + 19) SMALL_RBITS k hk)))
    (by have h := mem_ge0_head (S + 18)
          (((Head.c ((n : ℤ) - 1)).addLin (-1) (NGen.AY n)).addLin (-1) OY)
          (bitsFrom (S + 19) SMALL_RBITS)
        rw [bitsFrom_length] at h; exact mem_st_tyhi n h)
    (by rw [evalHStep_addLin, evalHStep_addLin, evalHStep_c]; ring)
    (Int.ModEq.sub_left _ hoym) (by rcases hoyv with h | h | h <;> rw [h] <;> omega)
    (by rcases hoyv with h | h | h <;> rw [h] <;> omega)
  -- tib = the product of the four edge bits
  have hg := sgateH hsat i hi (mem_st_tib n)
  rw [headToExpr_evalStep, evalHStep_addProd, evalHStep_lin, varsVal_quad] at hg
  have hprodC : Canon (e.loc S * e.loc (S + 6) * e.loc (S + 12) * e.loc (S + 18)) := by
    rcases e1.1 with h | h <;> rcases e2.1 with h1 | h1 <;> rcases e3.1 with h2 | h2 <;>
      rcases e4.1 with h3 | h3 <;> rw [h, h1, h2, h3] <;> exact ⟨by norm_num, by norm_num⟩
  have htib : e.loc (S + 24) = e.loc S * e.loc (S + 6) * e.loc (S + 12) * e.loc (S + 18) :=
    eq_of_modEq_canon (canon_loc hc i _) hprodC ((gate_modEq_iff (by ring)).mp hg)
  refine ⟨?_, ?_⟩
  · rw [htib]
    rcases e1.1 with h | h <;> rcases e2.1 with h1 | h1 <;> rcases e3.1 with h2 | h2 <;>
      rcases e4.1 with h3 | h3 <;> rw [h, h1, h2, h3] <;> norm_num
  · rw [htib]
    constructor
    · intro hp
      have hall : e.loc S = 1 ∧ e.loc (S + 6) = 1 ∧ e.loc (S + 12) = 1 ∧ e.loc (S + 18) = 1 := by
        rcases e1.1 with h | h <;> rcases e2.1 with h1 | h1 <;> rcases e3.1 with h2 | h2 <;>
          rcases e4.1 with h3 | h3 <;> rw [h, h1, h2, h3] at hp <;>
          first | exact ⟨h, h1, h2, h3⟩ | (exfalso; revert hp; norm_num)
      have g1 := e1.2.1 hall.1
      have g2 := e2.2.1 hall.2.1
      have g3 := e3.2.1 hall.2.2.1
      have g4 := e4.2.1 hall.2.2.2
      exact ⟨g1, by omega, g3, by omega⟩
    · rintro ⟨c1, c2, c3, c4⟩
      have h1 : e.loc S = 1 := by
        rcases e1.1 with h | h
        · have := e1.2.2 h; omega
        · exact h
      have h2 : e.loc (S + 6) = 1 := by
        rcases e2.1 with h | h
        · have := e2.2.2 h; omega
        · exact h
      have h3 : e.loc (S + 12) = 1 := by
        rcases e3.1 with h | h
        · have := e3.2.2 h; omega
        · exact h
      have h4 : e.loc (S + 18) = 1 := by
        rcases e4.1 with h | h
        · have := e4.2.2 h; omega
        · exact h
      rw [h1, h2, h3, h4]; norm_num

/-- The `getElem!` reads inside a `readRowcolHead` double sum resolve to the column functions. -/
theorem readSum_resolve (a : Nat → ℤ) (n : Nat) (fr fc : Nat → Nat) :
    ((List.range n).map (fun (y : Nat) => ((List.range n).map (fun (x : Nat) =>
        a (((List.range n).map fr)[y]!) * a (((List.range n).map fc)[x]!)
          * a (((List.range (NGen.KK n)).map (NGen.old n))[y * n + x]!))).sum)).sum
      = ((List.range n).map (fun (y : Nat) => ((List.range n).map (fun (x : Nat) =>
        a (fr y) * a (fc x) * a (NGen.old n (y * n + x)))).sum)).sum := by
  apply congrArg; apply List.map_congr_left; intro y hy
  have hyn : y < n := List.mem_range.mp hy
  apply congrArg; apply List.map_congr_left; intro x hx
  have hxn : x < n := List.mem_range.mp hx
  have hcell : y * n + x < NGen.KK n := by
    have : y * n + x < y * n + n := by omega
    calc y * n + x < y * n + n := this
      _ = (y + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n (by omega)
      _ = NGen.KK n := rfl
  rw [getElem!_range_map n fr hyn, getElem!_range_map n fc hxn,
    getElem!_range_map (NGen.KK n) (NGen.old n) hcell]

/-- **`treadN_of_sat` — THE n-WIDE GATED TARGET READ.** When `tib = 0` the gated read is `0`; when
`tib = 1` it IS the OLD board cell at the target `(ax+ox, ay+oy)`. This is the lemma the `n = 2`
chain (`tread_of_sat` + `tcell_target_of_sat`) wrote as an explicit 2×2 selector sum. -/
theorem treadN_of_sat (n : Nat) (hn1 : 1 ≤ n) (hn : (n : ℤ) < 2013265921)
    (hwin : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921) (hnsm : (n : ℤ) ≤ 1000000)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc (NGen.A_STEP_BASE n + 24) = 0
        → (envAt t i).loc (NGen.A_STEP_BASE n + 25) = 0)
    ∧ ((envAt t i).loc (NGen.A_STEP_BASE n + 24) = 1
        → (envAt t i).loc (NGen.A_STEP_BASE n + 25)
            = (envAt t i).loc (NGen.old n
                (((envAt t i).loc (NGen.AY n)
                    + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))).toNat * n
                  + ((envAt t i).loc (NGen.AX n)
                    + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55))).toNat))) := by
  set e := envAt t i with he
  set S := NGen.A_STEP_BASE n with hS
  set OX := NGen.A_CHOOSE_BASE n + 55 with hOX
  set OY := NGen.A_CHOOSE_BASE n + 56 with hOY
  obtain ⟨htibB, htibIff⟩ := tibN_of_sat n hn1 hn hwin hnsm hsat hc i hi
  rw [← he, ← hS] at htibB
  rw [← he, ← hS, ← hOX, ← hOY] at htibIff
  -- the two gated one-hots
  have hrow := oneHotGatedStepN_of_sat hsat hc i hi n hn (fun j => S + 26 + j) (S + 24)
    ((Head.lin 1 (NGen.AY n)).addLin 1 OY) htibB
    (fun j hj => mem_st_read n (List.mem_append_left _ (List.mem_append_left _
      (oneHotG_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))))
    (mem_st_read n (List.mem_append_left _ (List.mem_append_left _ oneHotG_sigma)))
    (mem_st_read n (List.mem_append_left _ (List.mem_append_left _ oneHotG_index)))
  have hcol := oneHotGatedStepN_of_sat hsat hc i hi n hn (fun j => S + 26 + n + j) (S + 24)
    ((Head.lin 1 (NGen.AX n)).addLin 1 OX) htibB
    (fun j hj => mem_st_read n (List.mem_append_left _ (List.mem_append_right _
      (oneHotG_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))))
    (mem_st_read n (List.mem_append_left _ (List.mem_append_right _ oneHotG_sigma)))
    (mem_st_read n (List.mem_append_left _ (List.mem_append_right _ oneHotG_index)))
  -- the dot-product gate
  have hg := sgateH hsat i hi (mem_st_read n (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
  rw [headToExpr_evalStep, evalHStep_readRowcolHead,
    readSum_resolve e.loc n (fun j => S + 26 + j) (fun j => S + 26 + n + j)] at hg
  refine ⟨?_, ?_⟩
  · -- tib = 0: every selector vanishes, so the read is 0
    intro h0
    have hr0 := hrow.1 h0
    have hzero : ((List.range n).map (fun (y : Nat) => ((List.range n).map (fun (x : Nat) =>
          e.loc (S + 26 + y) * e.loc (S + 26 + n + x) * e.loc (NGen.old n (y * n + x)))).sum)).sum
        = 0 := by
      have : ((List.range n).map (fun (y : Nat) => ((List.range n).map (fun (x : Nat) =>
            e.loc (S + 26 + y) * e.loc (S + 26 + n + x) * e.loc (NGen.old n (y * n + x)))).sum))
          = (List.range n).map (fun _ => (0 : ℤ)) := by
        apply List.map_congr_left; intro y hy
        have hy0 : e.loc (S + 26 + y) = 0 := hr0 y (List.mem_range.mp hy)
        rw [show ((List.range n).map (fun (x : Nat) =>
              e.loc (S + 26 + y) * e.loc (S + 26 + n + x) * e.loc (NGen.old n (y * n + x))))
            = (List.range n).map (fun _ => (0 : ℤ))
            from by apply List.map_congr_left; intro x _; rw [hy0]; ring]
        simp
      rw [this]; simp
    rw [hzero, sub_zero] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero hg
  · -- tib = 1: both one-hots are pinned to the target coordinate
    intro h1
    obtain ⟨ay0, hay0Lt, hay0Cong, hay0One⟩ := hrow.2 h1
    obtain ⟨ax0, hax0Lt, hax0Cong, hax0One⟩ := hcol.2 h1
    obtain ⟨b1, b2, b3, b4⟩ := htibIff.mp h1
    rw [evalHStep_addLin, evalHStep_lin] at hay0Cong hax0Cong
    obtain ⟨hoxtri, hoytri⟩ := offsetN_of_sat hsat hc i hi
    rw [← he, ← hOX] at hoxtri; rw [← he, ← hOY] at hoytri
    have hoxm := decodeOff_modEq hoxtri
    have hoym := decodeOff_modEq hoytri
    -- the pinned indices are the (small) target coordinates
    have hayEq : (ay0 : ℤ) = e.loc (NGen.AY n) + decodeOff (e.loc OY) := by
      refine eq_of_modEq_wide ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ?_
      refine hay0Cong.trans ?_
      have : (1 * e.loc (NGen.AY n) + 1 * e.loc OY) = e.loc (NGen.AY n) + e.loc OY := by ring
      rw [this]; exact Int.ModEq.add_left _ hoym
    have haxEq : (ax0 : ℤ) = e.loc (NGen.AX n) + decodeOff (e.loc OX) := by
      refine eq_of_modEq_wide ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ?_
      refine hax0Cong.trans ?_
      have : (1 * e.loc (NGen.AX n) + 1 * e.loc OX) = e.loc (NGen.AX n) + e.loc OX := by ring
      rw [this]; exact Int.ModEq.add_left _ hoxm
    have hayNat : ay0 = (e.loc (NGen.AY n) + decodeOff (e.loc OY)).toNat := by omega
    have haxNat : ax0 = (e.loc (NGen.AX n) + decodeOff (e.loc OX)).toNat := by omega
    rw [dot_oneHot2 hay0One hax0One
      (fun y x => e.loc (NGen.old n (y * n + x)))] at hg
    have := eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (a := e.loc (S + 25))
        (b := e.loc (NGen.old n (ay0 * n + ax0))) (by ring)).mp hg)
    rw [this, hayNat, haxNat]

/-- **The gated target read is a genuine particle felt at ARBITRARY `n`** — out of bounds it is `0`,
in bounds it is an OLD board cell and the descriptor's own `boardRangeConstraints` range-check it. -/
theorem tcellValidN_of_sat (n : Nat) (hn1 : 1 ≤ n) (hn : (n : ℤ) < 2013265921)
    (hwin : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921) (hnsm : (n : ℤ) ≤ 1000000)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (NGen.A_STEP_BASE n + 25) = 0 ∨ (envAt t i).loc (NGen.A_STEP_BASE n + 25) = 1
    ∨ (envAt t i).loc (NGen.A_STEP_BASE n + 25) = 2
    ∨ (envAt t i).loc (NGen.A_STEP_BASE n + 25) = 3 := by
  obtain ⟨htibB, htibIff⟩ := tibN_of_sat n hn1 hn hwin hnsm hsat hc i hi
  obtain ⟨hz, hr⟩ := treadN_of_sat n hn1 hn hwin hnsm hsat hc i hi
  rcases htibB with h0 | h1
  · exact Or.inl (hz h0)
  · obtain ⟨b1, b2, b3, b4⟩ := htibIff.mp h1
    rw [hr h1]
    refine boardvalidN_of_sat hsat hc i hi _ ?_
    have hxb : ((envAt t i).loc (NGen.AX n)
        + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55))).toNat < n := by omega
    have hyb : ((envAt t i).loc (NGen.AY n)
        + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))).toNat < n := by omega
    show _ < n * n
    have hy1 : ((envAt t i).loc (NGen.AY n)
        + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))).toNat + 1 ≤ n := by omega
    have h1 := Nat.mul_le_mul_right n hy1
    have h2 : (((envAt t i).loc (NGen.AY n)
          + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))).toNat + 1) * n
        = ((envAt t i).loc (NGen.AY n)
          + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))).toNat * n + n := by ring
    omega

/-- **`targVacN_of_sat` — the target-vacant flag at ARBITRARY `n`.** `nz` is the `[tcell ≥ 1]` range
bit and `targ_vac = 1 − nz`; the alphabet check comes off the descriptor, so `targ_vac = 1` IFF the
target cell is VACUUM. -/
theorem targVacN_of_sat (n : Nat) (hn1 : 1 ≤ n) (hn : (n : ℤ) < 2013265921)
    (hwin : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921) (hnsm : (n : ℤ) ≤ 1000000)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc (NGen.A_STEP_BASE n + 32 + 2 * n) = 0
      ∨ (envAt t i).loc (NGen.A_STEP_BASE n + 32 + 2 * n) = 1)
    ∧ ((envAt t i).loc (NGen.A_STEP_BASE n + 32 + 2 * n) = 1
        ↔ (envAt t i).loc (NGen.A_STEP_BASE n + 25) = 0) := by
  set e := envAt t i with he
  set S := NGen.A_STEP_BASE n with hS
  have htcv := tcellValidN_of_sat n hn1 hn hwin hnsm hsat hc i hi
  rw [← he, ← hS] at htcv
  have hnz := ge0RN_of_sat hsat hc i hi (S + 26 + 2 * n) (S + 26 + 2 * n + 1) SMALL_RBITS
    ((Head.lin 1 (S + 25)).addConst (-1)) (e.loc (S + 25) - 1)
    (by norm_num [SMALL_RBITS])
    (mem_st_nz n (mem_ge0_ib _ _ _))
    (fun k hk => mem_st_nz n (mem_ge0_bit _ _ _
      (mem_bitsFrom (S + 26 + 2 * n + 1) SMALL_RBITS k hk)))
    (by have h := mem_ge0_head (S + 26 + 2 * n) ((Head.lin 1 (S + 25)).addConst (-1))
          (bitsFrom (S + 26 + 2 * n + 1) SMALL_RBITS)
        rw [bitsFrom_length] at h; exact mem_st_nz n h)
    (by rw [evalHStep_addConst, evalHStep_lin]; ring)
    (by rcases htcv with h | h | h | h <;> rw [h] <;> norm_num)
    (by rcases htcv with h | h | h | h <;> rw [h] <;> norm_num)
  -- targ_vac = 1 − nz
  have hg := sgateH hsat i hi (mem_st_targVac n)
  rw [headToExpr_evalStep, evalHStep_addConst, evalHStep_addLin, evalHStep_lin] at hg
  have htv : e.loc (S + 32 + 2 * n) = 1 - e.loc (S + 26 + 2 * n) := by
    refine eq_of_modEq_canon (canon_loc hc i _)
      (by rcases hnz.1 with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩) ?_
    exact (gate_modEq_iff (a := e.loc (S + 32 + 2 * n))
      (b := 1 - e.loc (S + 26 + 2 * n)) (by ring)).mp hg
  refine ⟨by rw [htv]; rcases hnz.1 with h | h <;> rw [h] <;> norm_num, ?_⟩
  rw [htv]
  constructor
  · intro hv
    have hnz0 : e.loc (S + 26 + 2 * n) = 0 := by omega
    have := hnz.2.2 hnz0; omega
  · intro h0
    have hz : e.loc (S + 26 + 2 * n) = 0 := by
      rcases hnz.1 with h | h
      · exact h
      · have := hnz.2.1 h; omega
    omega

/-- **`movedN_of_sat` — the move mask is the product of its three factors, at ARBITRARY `n`.** -/
theorem movedN_of_sat (n : Nat)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hoffB : (envAt t i).loc (NGen.A_STEP_BASE n + 33 + 2 * n) = 0
      ∨ (envAt t i).loc (NGen.A_STEP_BASE n + 33 + 2 * n) = 1)
    (htibB : (envAt t i).loc (NGen.A_STEP_BASE n + 24) = 0
      ∨ (envAt t i).loc (NGen.A_STEP_BASE n + 24) = 1)
    (htvB : (envAt t i).loc (NGen.A_STEP_BASE n + 32 + 2 * n) = 0
      ∨ (envAt t i).loc (NGen.A_STEP_BASE n + 32 + 2 * n) = 1) :
    (envAt t i).loc (NGen.A_STEP_BASE n + 34 + 2 * n)
      = (envAt t i).loc (NGen.A_STEP_BASE n + 33 + 2 * n)
        * (envAt t i).loc (NGen.A_STEP_BASE n + 24)
        * (envAt t i).loc (NGen.A_STEP_BASE n + 32 + 2 * n) := by
  have hg := sgateH hsat i hi (mem_st_moved n)
  rw [headToExpr_evalStep, evalHStep_addProd, evalHStep_lin, varsVal_triple] at hg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
  rcases hoffB with h | h <;> rcases htibB with h1 | h1 <;> rcases htvB with h2 | h2 <;>
    rw [h, h1, h2] <;> exact ⟨by norm_num, by norm_num⟩

/-- **`movedPartsN_of_sat`** — `m ∈ {0,1}` and `m = 1` exactly when all three factors fire. Carries
the `n ≤ 99` ceiling because `offnz ∈ {0,1}` is a consequence of the OFFSET SEMANTICS
(`offCardN_of_sat`), not of the `offnz = ox² + oy²` gate alone. -/
theorem movedPartsN_of_sat (n : Nat) (hn1 : 1 ≤ n) (hn : (n : ℤ) < 2013265921)
    (hn99 : (n : ℤ) ≤ 99) (hwin : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc (NGen.A_STEP_BASE n + 34 + 2 * n) = 0
      ∨ (envAt t i).loc (NGen.A_STEP_BASE n + 34 + 2 * n) = 1)
    ∧ ((envAt t i).loc (NGen.A_STEP_BASE n + 34 + 2 * n) = 1
        ↔ ((envAt t i).loc (NGen.A_STEP_BASE n + 33 + 2 * n) = 1
            ∧ (envAt t i).loc (NGen.A_STEP_BASE n + 24) = 1
            ∧ (envAt t i).loc (NGen.A_STEP_BASE n + 32 + 2 * n) = 1)) := by
  have hnsm : (n : ℤ) ≤ 1000000 := by omega
  obtain ⟨htibB, _⟩ := tibN_of_sat n hn1 hn hwin hnsm hsat hc i hi
  obtain ⟨htvB, _⟩ := targVacN_of_sat n hn1 hn hwin hnsm hsat hc i hi
  have hoffnz := offnzN_of_sat hsat hc i hi
  have hcard := offCardN_of_sat n hn hn99 hsat hc i hi
  have hoffB : (envAt t i).loc (NGen.A_STEP_BASE n + 33 + 2 * n) = 0
      ∨ (envAt t i).loc (NGen.A_STEP_BASE n + 33 + 2 * n) = 1 := by
    rw [hoffnz]
    rcases hcard with h | h | h | h | h <;>
      (simp only [Prod.mk.injEq] at h; obtain ⟨hx, hy⟩ := h; rw [hx, hy]; norm_num)
  have hm := movedN_of_sat n hsat hc i hi hoffB htibB htvB
  refine ⟨?_, ?_⟩
  · rw [hm]; rcases hoffB with h | h <;> rcases htibB with h1 | h1 <;> rcases htvB with h2 | h2 <;>
      rw [h, h1, h2] <;> norm_num
  · rw [hm]; constructor
    · intro hp
      rcases hoffB with h | h <;> rcases htibB with h1 | h1 <;> rcases htvB with h2 | h2 <;>
        rw [h, h1, h2] at hp ⊢ <;> first | exact ⟨rfl, rfl, rfl⟩ | (exfalso; revert hp; norm_num)
    · rintro ⟨h1, h2, h3⟩; rw [h1, h2, h3]; norm_num

/-- **`movedIffGuardN_of_sat` — the move mask IS the reference guard, at ARBITRARY `n`.** `m = 1`
exactly when `automatonStep`'s own `if` fires on the DECODED board: the target is in bounds on both
axes, the offset is nonzero, and the target cell is VACUUM. -/
theorem movedIffGuardN_of_sat (n : Nat) (hn1 : 1 ≤ n) (hn : (n : ℤ) < 2013265921)
    (hn99 : (n : ℤ) ≤ 99) (hwin : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc (NGen.A_STEP_BASE n + 34 + 2 * n) = 1) ↔
      (0 ≤ ((boardDecodeN n (envAt t i)).automaton.x : ℤ)
            + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55))
        ∧ ((boardDecodeN n (envAt t i)).automaton.x : ℤ)
            + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55))
            < ((boardDecodeN n (envAt t i)).size : ℤ)
        ∧ 0 ≤ ((boardDecodeN n (envAt t i)).automaton.y : ℤ)
            + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))
        ∧ ((boardDecodeN n (envAt t i)).automaton.y : ℤ)
            + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))
            < ((boardDecodeN n (envAt t i)).size : ℤ)
        ∧ (decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55)) ≠ 0
            ∨ decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56)) ≠ 0)
        ∧ (boardDecodeN n (envAt t i)).cellAt
            ⟨(((boardDecodeN n (envAt t i)).automaton.x : ℤ)
                + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55))).toNat,
              (((boardDecodeN n (envAt t i)).automaton.y : ℤ)
                + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))).toNat⟩
            = Particle.vacuum) := by
  have hnsm : (n : ℤ) ≤ 1000000 := by omega
  set e := envAt t i with he
  obtain ⟨⟨vx, hvxLt, hvxEq⟩, ⟨vy, hvyLt, hvyEq⟩⟩ := coordStepN_of_sat n hn1 hn hwin hsat hc i hi
  rw [← he] at hvxEq hvyEq
  have hbx : ((boardDecodeN n e).automaton.x : ℤ) = e.loc (NGen.AX n) := by
    show ((e.loc (NGen.AX n)).toNat : ℤ) = e.loc (NGen.AX n)
    rw [hvxEq]; simp
  have hby : ((boardDecodeN n e).automaton.y : ℤ) = e.loc (NGen.AY n) := by
    show ((e.loc (NGen.AY n)).toNat : ℤ) = e.loc (NGen.AY n)
    rw [hvyEq]; simp
  have hsz : ((boardDecodeN n e).size : ℤ) = (n : ℤ) := rfl
  rw [hbx, hby, hsz]
  obtain ⟨_, hmiff⟩ := movedPartsN_of_sat n hn1 hn hn99 hwin hsat hc i hi
  obtain ⟨_, htibIff⟩ := tibN_of_sat n hn1 hn hwin hnsm hsat hc i hi
  obtain ⟨_, htvIff⟩ := targVacN_of_sat n hn1 hn hwin hnsm hsat hc i hi
  obtain ⟨_, htread⟩ := treadN_of_sat n hn1 hn hwin hnsm hsat hc i hi
  have hoffnz := offnzN_of_sat hsat hc i hi
  have hcard := offCardN_of_sat n hn hn99 hsat hc i hi
  rw [← he] at hmiff htibIff htvIff htread hoffnz hcard
  -- the offset-nonzero factor
  have hnziff : e.loc (NGen.A_STEP_BASE n + 33 + 2 * n) = 1 ↔
      (decodeOff (e.loc (NGen.A_CHOOSE_BASE n + 55)) ≠ 0
        ∨ decodeOff (e.loc (NGen.A_CHOOSE_BASE n + 56)) ≠ 0) := by
    rw [hoffnz]
    rcases hcard with h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨hx, hy⟩ := h <;> rw [hx, hy] <;> norm_num
  -- the target-vacuum factor, under the in-bounds factor
  have hvaciff : e.loc (NGen.A_STEP_BASE n + 24) = 1 →
      (e.loc (NGen.A_STEP_BASE n + 32 + 2 * n) = 1 ↔
        (boardDecodeN n e).cellAt
          ⟨(e.loc (NGen.AX n) + decodeOff (e.loc (NGen.A_CHOOSE_BASE n + 55))).toNat,
            (e.loc (NGen.AY n) + decodeOff (e.loc (NGen.A_CHOOSE_BASE n + 56))).toNat⟩
          = Particle.vacuum) := by
    intro htib
    obtain ⟨b1, b2, b3, b4⟩ := htibIff.mp htib
    have hcell : (boardDecodeN n e).cellAt
        ⟨(e.loc (NGen.AX n) + decodeOff (e.loc (NGen.A_CHOOSE_BASE n + 55))).toNat,
          (e.loc (NGen.AY n) + decodeOff (e.loc (NGen.A_CHOOSE_BASE n + 56))).toNat⟩
        = codeToParticle (e.loc (NGen.A_STEP_BASE n + 25)) := by
      rw [htread htib]
      unfold Dregg2.Games.Automatafl.Board.cellAt
      split
      · rfl
      · next hbad =>
          exfalso; apply hbad
          refine ⟨?_, ?_⟩
          · show (e.loc (NGen.AX n)
              + decodeOff (e.loc (NGen.A_CHOOSE_BASE n + 55))).toNat < n
            omega
          · show (e.loc (NGen.AY n)
              + decodeOff (e.loc (NGen.A_CHOOSE_BASE n + 56))).toNat < n
            omega
    rw [hcell, htvIff]
    have htcv := tcellValidN_of_sat n hn1 hn hwin hnsm hsat hc i hi
    rw [← he] at htcv
    rcases htcv with h | h | h | h <;> rw [h] <;> simp [codeToParticle]
  rw [hmiff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨b1, b2, b3, b4⟩ := htibIff.mp h2
    exact ⟨b1, by omega, b3, by omega, hnziff.mp h1, (hvaciff h2).mp h3⟩
  · rintro ⟨g1, g2, g3, g4, g5, g6⟩
    have h2 : e.loc (NGen.A_STEP_BASE n + 24) = 1 :=
      htibIff.mpr ⟨g1, by omega, g3, by omega⟩
    exact ⟨hnziff.mpr g5, h2, (hvaciff h2).mpr g6⟩

/-! ## §5 — the `sel_target` UPDATE one-hots, the auto one-hots, and the board-update fold. -/

/-- **`selTargN_of_sat` — the `m`-gated `sel_target` UPDATE one-hots at ARBITRARY `n`.** With
`m = 0` every selector vanishes (the board is frozen); with `m = 1` they single-hot exactly the
target cell `(ax+ox, ay+oy)`. -/
theorem selTargN_of_sat (n : Nat) (hn1 : 1 ≤ n) (hn : (n : ℤ) < 2013265921)
    (hn99 : (n : ℤ) ≤ 99) (hwin : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc (NGen.A_STEP_BASE n + 34 + 2 * n) = 0 → ∀ j, j < n →
        (envAt t i).loc (NGen.A_STEP_BASE n + 35 + 2 * n + j) = 0
        ∧ (envAt t i).loc (NGen.A_STEP_BASE n + 35 + 3 * n + j) = 0)
    ∧ ((envAt t i).loc (NGen.A_STEP_BASE n + 34 + 2 * n) = 1 →
        OneHotAt (fun j => (envAt t i).loc (NGen.A_STEP_BASE n + 35 + 2 * n + j)) n
            (((envAt t i).loc (NGen.AY n)
              + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))).toNat)
        ∧ OneHotAt (fun j => (envAt t i).loc (NGen.A_STEP_BASE n + 35 + 3 * n + j)) n
            (((envAt t i).loc (NGen.AX n)
              + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55))).toNat)) := by
  have hnsm : (n : ℤ) ≤ 1000000 := by omega
  set e := envAt t i with he
  set S := NGen.A_STEP_BASE n with hS
  set OX := NGen.A_CHOOSE_BASE n + 55 with hOX
  set OY := NGen.A_CHOOSE_BASE n + 56 with hOY
  obtain ⟨hmB, hmIff⟩ := movedPartsN_of_sat n hn1 hn hn99 hwin hsat hc i hi
  rw [← he, ← hS] at hmB hmIff
  have hrow := oneHotGatedStepN_of_sat hsat hc i hi n hn (fun j => S + 35 + 2 * n + j)
    (S + 34 + 2 * n) ((Head.lin 1 (NGen.AY n)).addLin 1 OY) hmB
    (fun j hj => mem_st_updRow n (oneHotG_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
    (mem_st_updRow n oneHotG_sigma) (mem_st_updRow n oneHotG_index)
  have hcol := oneHotGatedStepN_of_sat hsat hc i hi n hn (fun j => S + 35 + 3 * n + j)
    (S + 34 + 2 * n) ((Head.lin 1 (NGen.AX n)).addLin 1 OX) hmB
    (fun j hj => mem_st_updCol n (oneHotG_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
    (mem_st_updCol n oneHotG_sigma) (mem_st_updCol n oneHotG_index)
  refine ⟨fun h0 j hj => ⟨hrow.1 h0 j hj, hcol.1 h0 j hj⟩, ?_⟩
  intro h1
  obtain ⟨ay0, hay0Lt, hay0Cong, hay0One⟩ := hrow.2 h1
  obtain ⟨ax0, hax0Lt, hax0Cong, hax0One⟩ := hcol.2 h1
  obtain ⟨_, htib1, _⟩ := hmIff.mp h1
  obtain ⟨_, htibIff⟩ := tibN_of_sat n hn1 hn hwin hnsm hsat hc i hi
  rw [← he, ← hS, ← hOX, ← hOY] at htibIff
  obtain ⟨b1, b2, b3, b4⟩ := htibIff.mp htib1
  rw [evalHStep_addLin, evalHStep_lin] at hay0Cong hax0Cong
  obtain ⟨hoxtri, hoytri⟩ := offsetN_of_sat hsat hc i hi
  rw [← he, ← hOX] at hoxtri; rw [← he, ← hOY] at hoytri
  have hoxm := decodeOff_modEq hoxtri
  have hoym := decodeOff_modEq hoytri
  have hayEq : (ay0 : ℤ) = e.loc (NGen.AY n) + decodeOff (e.loc OY) := by
    refine eq_of_modEq_wide ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ?_
    refine hay0Cong.trans ?_
    rw [show (1 * e.loc (NGen.AY n) + 1 * e.loc OY) = e.loc (NGen.AY n) + e.loc OY from by ring]
    exact Int.ModEq.add_left _ hoym
  have haxEq : (ax0 : ℤ) = e.loc (NGen.AX n) + decodeOff (e.loc OX) := by
    refine eq_of_modEq_wide ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ?_
    refine hax0Cong.trans ?_
    rw [show (1 * e.loc (NGen.AX n) + 1 * e.loc OX) = e.loc (NGen.AX n) + e.loc OX from by ring]
    exact Int.ModEq.add_left _ hoxm
  rw [show ((e.loc (NGen.AY n) + decodeOff (e.loc OY)).toNat) = ay0 from by omega,
    show ((e.loc (NGen.AX n) + decodeOff (e.loc OX)).toNat) = ax0 from by omega]
  exact ⟨hay0One, hax0One⟩

/-- **`autoSelN_of_sat` — the FRONT-END auto one-hots are pinned to the decoded auto cell.** -/
theorem autoSelN_of_sat (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    OneHotAt (fun j => (envAt t i).loc (NGen.selRow n j)) n ((envAt t i).loc (NGen.AY n)).toNat
    ∧ OneHotAt (fun j => (envAt t i).loc (NGen.selCol n j)) n ((envAt t i).loc (NGen.AX n)).toNat := by
  obtain ⟨ay, hayLt, hayEq, hrow⟩ :=
    oneHotStepN_of_sat hsat hc i hi n hn (NGen.selRow n) (NGen.AY n)
      (fun j hj => mem_fe_oneHotRow (oneHot_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
      (mem_fe_oneHotRow oneHot_sigma) (mem_fe_oneHotRow oneHot_index)
  obtain ⟨ax, haxLt, haxEq, hcol⟩ :=
    oneHotStepN_of_sat hsat hc i hi n hn (NGen.selCol n) (NGen.AX n)
      (fun j hj => mem_fe_oneHotCol (oneHot_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
      (mem_fe_oneHotCol oneHot_sigma) (mem_fe_oneHotCol oneHot_index)
  rw [hayEq, haxEq]
  simpa using ⟨hrow, hcol⟩

/-- **`boardupdN_of_sat` — the per-cell board-update equality at SYMBOLIC `c`, ARBITRARY `n`.**
`new[c] ≡ old[c] + AUTO·A − A·old[c] − B·old[c]` with `A` the `m`-gated target-selector product and
`B` the `m`-gated auto-selector product for that cell. The `n = 2` twin is the four-way
`boardupd_of_sat`. -/
theorem boardupdN_of_sat (n : Nat) (hn1 : 1 ≤ n) (c : Nat) (hcK : c < NGen.KK n)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (NGen.new n c)
      ≡ (envAt t i).loc (NGen.old n c)
        + 3 * ((envAt t i).loc (NGen.A_STEP_BASE n + 34 + 2 * n)
              * (envAt t i).loc (NGen.A_STEP_BASE n + 35 + 2 * n + c / n)
              * (envAt t i).loc (NGen.A_STEP_BASE n + 35 + 3 * n + c % n))
        - (envAt t i).loc (NGen.A_STEP_BASE n + 34 + 2 * n)
              * (envAt t i).loc (NGen.A_STEP_BASE n + 35 + 2 * n + c / n)
              * (envAt t i).loc (NGen.A_STEP_BASE n + 35 + 3 * n + c % n)
              * (envAt t i).loc (NGen.old n c)
        - (envAt t i).loc (NGen.A_STEP_BASE n + 34 + 2 * n)
              * (envAt t i).loc (NGen.selRow n (c / n))
              * (envAt t i).loc (NGen.selCol n (c % n))
              * (envAt t i).loc (NGen.old n c) [ZMOD 2013265921] := by
  have hnn : 0 < n := hn1
  have hdiv : c / n < n := by
    have : c < n * n := hcK
    exact Nat.div_lt_of_lt_mul (by omega)
  have hmod : c % n < n := Nat.mod_lt _ hnn
  have hg := sgateH hsat i hi (mem_step_update n c hcK)
  rw [getElem!_range_map n (fun j => NGen.A_STEP_BASE n + 35 + 2 * n + j) hdiv,
    getElem!_range_map n (fun j => NGen.A_STEP_BASE n + 35 + 3 * n + j) hmod] at hg
  rw [headToExpr_evalStep, evalHStep_addProd, evalHStep_addProd, evalHStep_addProd,
    evalHStep_addLin, evalHStep_lin, varsVal_triple, varsVal_quad, varsVal_quad] at hg
  exact (gate_modEq_iff (by simp only [AUTO]; ring)).mp hg

/-! ## §6 — THE CAPSTONE at ARBITRARY `n`. -/

/-- **LEG A, CLOSED AT ARBITRARY `n` — the capstone.** On a satisfying, canonical trace of
`automataflStepDescN n`, the emitted NEW board columns ARE the reference automaton step applied to
the decoded OLD board: the size is preserved, the automaton sits on the witnessed target exactly
when the move mask fires, and EVERY in-bounds cell of the decoded NEW board equals the corresponding
cell of `automatonStep (boardDecodeN n …)`. UNCONDITIONAL in the board-alphabet envelope (the
descriptor's own `boardRangeConstraints` supply it); the `n ≤ 99` hypothesis is the SCORE_ATT radix
ceiling inherited from `automatonOffset_of_satN` (defect #9), and `hwin` is the coordinate no-wrap
window. -/
theorem astep_sat_imp_automatonStepN (n : Nat) (hn1 : 1 ≤ n) (hn : (n : ℤ) < 2013265921)
    (hn99 : (n : ℤ) ≤ 99) (hwin : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (automatonStep (boardDecodeN n (envAt t i))).size = n
    ∧ (automatonStep (boardDecodeN n (envAt t i))).automaton
        = (if (envAt t i).loc (NGen.A_STEP_BASE n + 34 + 2 * n) = 1
            then (⟨((envAt t i).loc (NGen.AX n)
                    + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 55))).toNat,
                   ((envAt t i).loc (NGen.AY n)
                    + decodeOff ((envAt t i).loc (NGen.A_CHOOSE_BASE n + 56))).toNat⟩ : Coord)
            else ⟨((envAt t i).loc (NGen.AX n)).toNat, ((envAt t i).loc (NGen.AY n)).toNat⟩)
    ∧ (∀ x y : Nat, x < n → y < n →
        codeToParticle ((envAt t i).loc (NGen.new n (y * n + x)))
          = (automatonStep (boardDecodeN n (envAt t i))).cellAt ⟨x, y⟩) := by
  have hnsm : (n : ℤ) ≤ 1000000 := by omega
  set e := envAt t i with he
  set S := NGen.A_STEP_BASE n with hS
  set OX := NGen.A_CHOOSE_BASE n + 55 with hOX
  set OY := NGen.A_CHOOSE_BASE n + 56 with hOY
  obtain ⟨⟨vx, hvxLt, hvxEq⟩, ⟨vy, hvyLt, hvyEq⟩⟩ := coordStepN_of_sat n hn1 hn hwin hsat hc i hi
  rw [← he] at hvxEq hvyEq
  have hbx : ((boardDecodeN n e).automaton.x : ℤ) = e.loc (NGen.AX n) := by
    show ((e.loc (NGen.AX n)).toNat : ℤ) = e.loc (NGen.AX n)
    rw [hvxEq]; simp
  have hby : ((boardDecodeN n e).automaton.y : ℤ) = e.loc (NGen.AY n) := by
    show ((e.loc (NGen.AY n)).toNat : ℤ) = e.loc (NGen.AY n)
    rw [hvyEq]; simp
  obtain ⟨hmB, hmIff⟩ := movedPartsN_of_sat n hn1 hn hn99 hwin hsat hc i hi
  rw [← he, ← hS] at hmB hmIff
  have hguard := movedIffGuardN_of_sat n hn1 hn hn99 hwin hsat hc i hi
  rw [← he, ← hS, ← hOX, ← hOY] at hguard
  -- the reference step, with its guard discharged against the move mask
  have hstep : automatonStep (boardDecodeN n e)
      = if e.loc (S + 34 + 2 * n) = 1
        then stepTo (boardDecodeN n e)
              ⟨(e.loc (NGen.AX n) + decodeOff (e.loc OX)).toNat,
               (e.loc (NGen.AY n) + decodeOff (e.loc OY)).toNat⟩
        else boardDecodeN n e := by
    have hoff : automatonOffset (boardDecodeN n e)
        = (decodeOff (e.loc OX), decodeOff (e.loc OY)) := by
      rw [he, hOX, hOY]; exact automatonOffset_of_satN n hn hn99 hsat hc i hi
    simp only [automatonStep, hoff]
    by_cases hm : e.loc (S + 34 + 2 * n) = 1
    · rw [if_pos hm, if_pos (hguard.mp hm), hbx, hby]
    · rw [if_neg hm, if_neg (fun hg => hm (hguard.mpr hg))]
  -- the per-cell decode
  refine ⟨by rw [Dregg2.Games.Automatafl.automatonStep_size]; rfl, ?_, ?_⟩
  · rw [hstep]
    by_cases hm : e.loc (S + 34 + 2 * n) = 1
    · rw [if_pos hm, if_pos hm]; rfl
    · rw [if_neg hm, if_neg hm]
      show (⟨(e.loc (NGen.AX n)).toNat, (e.loc (NGen.AY n)).toNat⟩ : Coord) = _
      rfl
  · intro x y hx hy
    have hcK : y * n + x < NGen.KK n := by
      have hy1 : y + 1 ≤ n := by omega
      have h1 := Nat.mul_le_mul_right n hy1
      have h2 : (y + 1) * n = y * n + n := by ring
      show _ < n * n
      omega
    have hupd := boardupdN_of_sat n hn1 (y * n + x) hcK hsat hc i hi
    rw [← he, ← hS] at hupd
    have hcomm : y * n + x = x + n * y := by ring
    have hdiv : (y * n + x) / n = y := by
      rw [hcomm, Nat.add_mul_div_left _ _ (show 0 < n by omega), Nat.div_eq_of_lt hx,
        Nat.zero_add]
    have hmodn : (y * n + x) % n = x := by
      rw [hcomm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    rw [hdiv, hmodn] at hupd
    obtain ⟨hasR, hasC⟩ := autoSelN_of_sat n hn hsat hc i hi
    rw [← he] at hasR hasC
    have hold := boardvalidN_of_sat hsat hc i hi (y * n + x) hcK
    rw [← he] at hold
    -- the two selector products
    set A := e.loc (S + 34 + 2 * n) * e.loc (S + 35 + 2 * n + y) * e.loc (S + 35 + 3 * n + x)
      with hA
    set B := e.loc (S + 34 + 2 * n) * e.loc (NGen.selRow n y) * e.loc (NGen.selCol n x) with hB
    have hcellOld : (boardDecodeN n e).cellAt ⟨x, y⟩
        = codeToParticle (e.loc (NGen.old n (y * n + x))) := by
      unfold Dregg2.Games.Automatafl.Board.cellAt
      rw [if_pos ⟨hx, hy⟩]; rfl
    by_cases hm : e.loc (S + 34 + 2 * n) = 1
    · -- the automaton MOVED
      obtain ⟨hsel1, hsel2⟩ := (selTargN_of_sat n hn1 hn hn99 hwin hsat hc i hi).2 hm
      rw [← he, ← hS, ← hOY] at hsel1
      rw [← he, ← hS, ← hOX] at hsel2
      set TX := (e.loc (NGen.AX n) + decodeOff (e.loc OX)).toNat with hTX
      set TY := (e.loc (NGen.AY n) + decodeOff (e.loc OY)).toNat with hTY
      have hselR : e.loc (S + 35 + 2 * n + y) = if y = TY then 1 else 0 := hsel1.2 y hy
      have hselC : e.loc (S + 35 + 3 * n + x) = if x = TX then 1 else 0 := hsel2.2 x hx
      have hautoR : e.loc (NGen.selRow n y)
          = if y = (e.loc (NGen.AY n)).toNat then 1 else 0 := hasR.2 y hy
      have hautoC : e.loc (NGen.selCol n x)
          = if x = (e.loc (NGen.AX n)).toNat then 1 else 0 := hasC.2 x hx
      have hAv : A = if (⟨x, y⟩ : Coord) = ⟨TX, TY⟩ then 1 else 0 := by
        rw [hA, hm, one_mul, hselR, hselC]
        by_cases hxy : (⟨x, y⟩ : Coord) = ⟨TX, TY⟩
        · have hx' : x = TX := congrArg Coord.x hxy
          have hy' : y = TY := congrArg Coord.y hxy
          rw [if_pos hxy, if_pos hy', if_pos hx']; norm_num
        · rw [if_neg hxy]
          by_cases hy' : y = TY
          · have hx' : x ≠ TX := by
              intro hxx; exact hxy (by rw [Coord.mk.injEq]; exact ⟨hxx, hy'⟩)
            rw [if_neg hx']; ring
          · rw [if_neg hy']; ring
      have hBv : B = if (⟨x, y⟩ : Coord)
            = ⟨(e.loc (NGen.AX n)).toNat, (e.loc (NGen.AY n)).toNat⟩ then 1 else 0 := by
        rw [hB, hm, one_mul, hautoR, hautoC]
        by_cases hxy : (⟨x, y⟩ : Coord) = ⟨(e.loc (NGen.AX n)).toNat, (e.loc (NGen.AY n)).toNat⟩
        · have hx' : x = (e.loc (NGen.AX n)).toNat := congrArg Coord.x hxy
          have hy' : y = (e.loc (NGen.AY n)).toNat := congrArg Coord.y hxy
          rw [if_pos hxy, if_pos hy', if_pos hx']; norm_num
        · rw [if_neg hxy]
          by_cases hy' : y = (e.loc (NGen.AY n)).toNat
          · have hx' : x ≠ (e.loc (NGen.AX n)).toNat := by
              intro hxx; exact hxy (by rw [Coord.mk.injEq]; exact ⟨hxx, hy'⟩)
            rw [if_neg hx']; ring
          · rw [if_neg hy']; ring
      -- target ≠ auto (the move is a NONZERO cardinal offset)
      have hne : (⟨TX, TY⟩ : Coord) ≠ ⟨(e.loc (NGen.AX n)).toNat, (e.loc (NGen.AY n)).toNat⟩ := by
        obtain ⟨hoff1, htib1, _⟩ := hmIff.mp hm
        have hoffnz := offnzN_of_sat hsat hc i hi
        rw [← he, ← hS, ← hOX, ← hOY] at hoffnz
        obtain ⟨_, htibIff⟩ := tibN_of_sat n hn1 hn hwin hnsm hsat hc i hi
        rw [← he, ← hS, ← hOX, ← hOY] at htibIff
        obtain ⟨b1, b2, b3, b4⟩ := htibIff.mp htib1
        have hnz : decodeOff (e.loc OX) ≠ 0 ∨ decodeOff (e.loc OY) ≠ 0 := by
          rw [hoffnz] at hoff1
          by_contra hcon
          push_neg at hcon
          obtain ⟨c1, c2⟩ := hcon
          rw [c1, c2] at hoff1
          norm_num at hoff1
        have hax0 : (0 : ℤ) ≤ e.loc (NGen.AX n) := by rw [hvxEq]; omega
        have hay0 : (0 : ℤ) ≤ e.loc (NGen.AY n) := by rw [hvyEq]; omega
        intro hEq
        have h1 : TX = (e.loc (NGen.AX n)).toNat := congrArg Coord.x hEq
        have h2 : TY = (e.loc (NGen.AY n)).toNat := congrArg Coord.y hEq
        rcases hnz with h | h <;> omega
      have hAB : A = 1 → B = 0 := by
        intro hA1
        rw [hAv] at hA1
        have hxy : (⟨x, y⟩ : Coord) = ⟨TX, TY⟩ := by
          by_contra hcon; rw [if_neg hcon] at hA1; norm_num at hA1
        rw [hBv, if_neg (by rw [hxy]; exact hne)]
      have hA01 : A = 0 ∨ A = 1 := by
        rw [hAv]; by_cases hxy : (⟨x, y⟩ : Coord) = ⟨TX, TY⟩
        · right; rw [if_pos hxy]
        · left; rw [if_neg hxy]
      have hB01 : B = 0 ∨ B = 1 := by
        rw [hBv]
        by_cases hxy : (⟨x, y⟩ : Coord) = ⟨(e.loc (NGen.AX n)).toNat, (e.loc (NGen.AY n)).toNat⟩
        · right; rw [if_pos hxy]
        · left; rw [if_neg hxy]
      have hcell := cell_update_pure hold hA01 hB01 hAB (canon_loc hc i _)
        hupd
      rw [hcell, hstep, if_pos hm]
      unfold Dregg2.Games.Automatafl.Board.cellAt
      rw [if_pos (show x < (stepTo (boardDecodeN n e) ⟨TX, TY⟩).size
          ∧ y < (stepTo (boardDecodeN n e) ⟨TX, TY⟩).size from ⟨hx, hy⟩)]
      show _ = (if (⟨x, y⟩ : Coord) = ⟨TX, TY⟩ then Particle.automaton
        else if (⟨x, y⟩ : Coord) = (boardDecodeN n e).automaton then Particle.vacuum
        else (boardDecodeN n e).cells ⟨x, y⟩)
      have hauto : (boardDecodeN n e).automaton
          = ⟨(e.loc (NGen.AX n)).toNat, (e.loc (NGen.AY n)).toNat⟩ := rfl
      rw [hauto]
      by_cases h1 : (⟨x, y⟩ : Coord) = ⟨TX, TY⟩
      · rw [if_pos (show A = 1 from by rw [hAv, if_pos h1]), if_pos h1]
      · rw [if_neg (show ¬ A = 1 from by rw [hAv, if_neg h1]; norm_num), if_neg h1]
        by_cases h2 : (⟨x, y⟩ : Coord) = ⟨(e.loc (NGen.AX n)).toNat, (e.loc (NGen.AY n)).toNat⟩
        · rw [if_pos (show B = 1 from by rw [hBv, if_pos h2]), if_pos h2]
        · rw [if_neg (show ¬ B = 1 from by rw [hBv, if_neg h2]; norm_num), if_neg h2]
          rfl
    · -- the automaton did NOT move: every selector vanishes and the board is unchanged
      have hm0 : e.loc (S + 34 + 2 * n) = 0 := hmB.resolve_right hm
      have hA0 : A = 0 := by rw [hA, hm0]; ring
      have hB0 : B = 0 := by rw [hB, hm0]; ring
      have hcell := cell_update_pure hold (Or.inl hA0) (Or.inl hB0)
        (by intro h1; rw [hA0] at h1; norm_num at h1) (canon_loc hc i _)
        hupd
      rw [hcell, if_neg (by rw [hA0]; norm_num), if_neg (by rw [hB0]; norm_num), hstep,
        if_neg hm, hcellOld]

/-! ### §6b — LEG A re-pointed onto the VALIDATED spec (`AutomataflRules.automatonStepCfg .column`).

The migration re-targets the tower from the OLD `Automatafl.automatonStep` to the rules-faithful
`AutomataflRules.automatonStepCfg`. For the DEPLOYED default (`.column`) tie-break this is a pure
rewrite: `boardDecodeN` fixes `useColumnRule = true` (`rfl`), so
`AutomataflRules.automatonStepCfg_column_eq` makes the new step defeq-equal to the old one and the
capstone transports verbatim. NO descriptor is re-emitted; `automatafl-step.json` is untouched.
(A `.row`/`.freeze` game would need `StepChoose`'s `.eq`-tie branch re-emitted — a Phase-4 item.) -/
theorem astep_sat_imp_automatonStepCfgN (n : Nat) (hn1 : 1 ≤ n) (hn : (n : ℤ) < 2013265921)
    (hn99 : (n : ℤ) ≤ 99) (hwin : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (Dregg2.Games.AutomataflRules.automatonStepCfg ⟨.column⟩
        (boardDecodeN n (envAt t i))).size = n
    ∧ (∀ x y : Nat, x < n → y < n →
        codeToParticle ((envAt t i).loc (NGen.new n (y * n + x)))
          = (Dregg2.Games.AutomataflRules.automatonStepCfg ⟨.column⟩
              (boardDecodeN n (envAt t i))).cellAt ⟨x, y⟩) := by
  have hbridge : Dregg2.Games.AutomataflRules.automatonStepCfg ⟨.column⟩
        (boardDecodeN n (envAt t i))
      = automatonStep (boardDecodeN n (envAt t i)) :=
    Dregg2.Games.AutomataflRules.automatonStepCfg_column_eq ⟨.column⟩
      (boardDecodeN n (envAt t i)) rfl rfl
  rw [hbridge]
  have h := astep_sat_imp_automatonStepN n hn1 hn hn99 hwin hsat hc i hi
  exact ⟨h.1, h.2.2⟩

end StepN

/-! ## §7 — non-vacuous instantiation: `n = 3` and the DEPLOYED `n = 11`. -/

section Instances
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The capstone at `n = 3` (a genuine 3×3 board: nine cells, four 3-step rays). -/
theorem astep_sat_imp_automatonStep_n3
    (hsat : Satisfied2 hash (automataflStepDescN 3) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (automatonStep (boardDecodeN 3 (envAt t i))).size = 3
    ∧ (∀ x y : Nat, x < 3 → y < 3 →
        codeToParticle ((envAt t i).loc (NGen.new 3 (y * 3 + x)))
          = (automatonStep (boardDecodeN 3 (envAt t i))).cellAt ⟨x, y⟩) :=
  let h := astep_sat_imp_automatonStepN 3 (by norm_num) (by norm_num) (by norm_num)
    (by decide) hsat hc i hi
  ⟨h.1, h.2.2⟩

/-- The capstone at the DEPLOYED `n = 11`. -/
theorem astep_sat_imp_automatonStep_n11
    (hsat : Satisfied2 hash (automataflStepDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (automatonStep (boardDecodeN 11 (envAt t i))).size = 11
    ∧ (∀ x y : Nat, x < 11 → y < 11 →
        codeToParticle ((envAt t i).loc (NGen.new 11 (y * 11 + x)))
          = (automatonStep (boardDecodeN 11 (envAt t i))).cellAt ⟨x, y⟩) :=
  let h := astep_sat_imp_automatonStepN 11 (by norm_num) (by norm_num) (by norm_num)
    (by decide) hsat hc i hi
  ⟨h.1, h.2.2⟩

end Instances

/-! ## §7b — NON-VACUITY: the two `n`-wide families this file reasons about genuinely BITE at
`n = 3` (where the `n = 2` `#guard`s cannot reach — a 3-wide row×column read has 9 cells and the
one-hot has a third slot the 2×2 form never had). -/

/-- The `n = 3` gated target-read dot-product body. -/
def treadExprN3 : EmittedExpr :=
  headToExpr (readRowcolHead
    ((List.range 3).map (fun j => NGen.A_STEP_BASE 3 + 26 + j))
    ((List.range 3).map (fun j => NGen.A_STEP_BASE 3 + 26 + 3 + j))
    ((List.range (NGen.KK 3)).map (NGen.old 3)) 3 (NGen.A_STEP_BASE 3 + 25))

/-- Row one-hot at `y = 1`, column one-hot at `x = 2`, `old[1·3+2] = ATT = 2`, `tcell = 2`. -/
def treadGoodN3 : Assignment := fun c =>
  if c = NGen.A_STEP_BASE 3 + 26 + 1 then 1
  else if c = NGen.A_STEP_BASE 3 + 26 + 3 + 2 then 1
  else if c = NGen.old 3 5 then 2
  else if c = NGen.A_STEP_BASE 3 + 25 then 2 else 0

/-- Same one-hots and board, but the witness claims the target cell read `0` (VACUUM) — the value a
forger wants, since `targ_vac` would then fire and the automaton would step onto an OCCUPIED cell. -/
def treadForgeN3 : Assignment := fun c =>
  if c = NGen.A_STEP_BASE 3 + 26 + 1 then 1
  else if c = NGen.A_STEP_BASE 3 + 26 + 3 + 2 then 1
  else if c = NGen.old 3 5 then 2 else 0

#guard treadExprN3.eval treadGoodN3 == 0     -- the honest read of the 3×3 board: accepted
#guard treadExprN3.eval treadForgeN3 != 0    -- "the occupied target read vacuum": REJECTED

/-- The `n = 3` board-update gate for cell `c = 4` (`x = y = 1`). -/
def buCellExprN3 : EmittedExpr :=
  headToExpr (((((Head.lin 1 (NGen.new 3 4)).addLin (-1) (NGen.old 3 4)).addProd (-AUTO)
      [NGen.A_STEP_BASE 3 + 34 + 6, NGen.A_STEP_BASE 3 + 35 + 6 + 1,
       NGen.A_STEP_BASE 3 + 35 + 9 + 1]).addProd 1
      [NGen.A_STEP_BASE 3 + 34 + 6, NGen.A_STEP_BASE 3 + 35 + 6 + 1,
       NGen.A_STEP_BASE 3 + 35 + 9 + 1, NGen.old 3 4]).addProd 1
      [NGen.A_STEP_BASE 3 + 34 + 6, NGen.selRow 3 1, NGen.selCol 3 1, NGen.old 3 4])

/-- `m = 1`, the target one-hot on cell 4, the AUTO elsewhere, `old[4] = 0`, `new[4] = AUTO`. -/
def buGoodN3 : Assignment := fun c =>
  if c = NGen.A_STEP_BASE 3 + 34 + 6 ∨ c = NGen.A_STEP_BASE 3 + 35 + 6 + 1
      ∨ c = NGen.A_STEP_BASE 3 + 35 + 9 + 1 then 1
  else if c = NGen.new 3 4 then 3 else 0

/-- The same move, but the witness leaves `new[4] = 0` — the automaton did NOT appear. -/
def buForgeN3 : Assignment := fun c =>
  if c = NGen.A_STEP_BASE 3 + 34 + 6 ∨ c = NGen.A_STEP_BASE 3 + 35 + 6 + 1
      ∨ c = NGen.A_STEP_BASE 3 + 35 + 9 + 1 then 1 else 0

#guard buCellExprN3.eval buGoodN3 == 0    -- automaton lands on the vacated 3×3 target: accepted
#guard buCellExprN3.eval buForgeN3 != 0   -- step happened but new[4] = 0: REJECTED

/-- The `n = 3` gated INDEX pin of the target-read row one-hot (`Σ j·sel_j − tib·(ay+oy)`). -/
def treadIdxExprN3 : EmittedExpr :=
  headToExpr (idxGatedHead ((List.range 3).map (fun j => NGen.A_STEP_BASE 3 + 26 + j))
    (NGen.A_STEP_BASE 3 + 24)
    ((Head.lin 1 (NGen.AY 3)).addLin 1 (NGen.A_CHOOSE_BASE 3 + 56)))

/-- `tib = 1`, `ay = 1`, `oy = +1`, and the row selector hot at `j = 2`: consistent. -/
def treadIdxGoodN3 : Assignment := fun c =>
  if c = NGen.A_STEP_BASE 3 + 24 then 1
  else if c = NGen.AY 3 then 1
  else if c = NGen.A_CHOOSE_BASE 3 + 56 then 1
  else if c = NGen.A_STEP_BASE 3 + 26 + 2 then 1 else 0

/-- Same target coordinate, but the selector is hot at `j = 1` (it reads the automaton's OWN row
instead of the row it is stepping into): the index pin REFUSES it. -/
def treadIdxForgeN3 : Assignment := fun c =>
  if c = NGen.A_STEP_BASE 3 + 24 then 1
  else if c = NGen.AY 3 then 1
  else if c = NGen.A_CHOOSE_BASE 3 + 56 then 1
  else if c = NGen.A_STEP_BASE 3 + 26 + 1 then 1 else 0

#guard treadIdxExprN3.eval treadIdxGoodN3 == 0    -- the one-hot sits on the target row: accepted
#guard treadIdxExprN3.eval treadIdxForgeN3 != 0   -- one-hot on the WRONG row: REJECTED

/-! ## §8 — axiom pins. -/

#assert_axioms evalHStep_idxGatedHead
#assert_axioms evalHStep_readRowcolHead
#assert_axioms oneHotGatedStepN_of_sat
#assert_axioms tibN_of_sat
#assert_axioms treadN_of_sat
#assert_axioms tcellValidN_of_sat
#assert_axioms targVacN_of_sat
#assert_axioms movedN_of_sat
#assert_axioms movedPartsN_of_sat
#assert_axioms movedIffGuardN_of_sat
#assert_axioms selTargN_of_sat
#assert_axioms autoSelN_of_sat
#assert_axioms boardupdN_of_sat
#assert_axioms astep_sat_imp_automatonStepN
#assert_axioms astep_sat_imp_automatonStepCfgN
#assert_axioms astep_sat_imp_automatonStep_n3
#assert_axioms astep_sat_imp_automatonStep_n11

end Dregg2.Circuit.Emit.AutomataflStepStep
