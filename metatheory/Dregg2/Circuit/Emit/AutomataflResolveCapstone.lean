/-
# Dregg2.Circuit.Emit.AutomataflResolveCapstone — LEG R'S CAPSTONE AT ARBITRARY BOARD SIZE `n`.

`AutomataflResolveRefine` once closed a Leg R capstone (`resolve_sat_imp_resolveMid`) at the frozen
`NN = 2`, over the SUPERSEDED `mid` columns; it is RETIRED (see that file's §D.6b). §D.7/§D.8 of
that file landed the adjudication core and every coordinate extraction at arbitrary `n`;
`AutomataflOcclusionBridgeN` landed `occ_iff_occluded_of_sat` at arbitrary `n`. This file is the
COMPOSITION, and its live product is `resolveFactsN_of_sat` — the per-row fact bundle the LIVE
capstone `AutomataflResolveMovesCapstone.resolve_sat_imp_roundBoardN` consumes.

What is here:

  * **§1 — `oneHotHeadN_of_sat`**: the `n`-generic one-hot read primitive pinned to an arbitrary index
    HEAD (the destination one-hots are pinned to `destHead`, an interpolation, not a bare column).
  * **§2 — the INDICATOR GLUE at arbitrary `n`**: `srcIndN_of_sat` / `dstIndN_of_sat`, the row×column
    one-hot products read as the `Coord` indicators of the source and of the `ft`-selected landing.
  * **§3 — `ResolveFactsN` / `resolveFactsN_of_sat`**: every semantic fact the assembly needs, derived
    from a satisfying canonical row of `automataflResolveDescN n`. The occlusion conjuncts are REAL here
    (`carry = surv ∧ nz ∧ ¬occ`, `ft` carries `¬occ` of the other piece), bridged to the reference
    `Automatafl.occluded` by `AutomataflOcclusionBridgeN.occ_iff_occluded_of_sat`.
  * (§4 — `writeCellN_of_sat`, the per-cell rewrite gate over the SUPERSEDED `mid` columns, is
    DELETED. It read the OLD `carryCol` / `wDstRow`/`wDstCol` and wrote `NGen.mid`; the LIVE board
    rewrite is `AutomataflResolveMovesCapstone`'s V4 surface over `cWBoardV4` / `cMidV4`.)
  * **§5 — the OCCLUSION-AWARE caterpillar**: `nextOf_pairN` states the `m = 2` move graph
    UNCONDITIONALLY (each edge gated by its own `occluded`), and `chainDest_aN` / `chainDest_bN` resolve
    the chain at ARBITRARY coordinates, threading the not-occluded facts the carries supply.
  * **§6 — the OCCLUDED-STAYER WOUND**: why `resolve_sat_imp_resolveMid` is NOT restated at `n > 2`.
    It is not a plumbing gap — the emitted descriptor and the reference DISAGREE at `n ≥ 3` when a
    non-vacuum OCCLUDED source stays put and the other, carrying piece lands on it. `stayer_keeps_cell`
    is the reference side, `writeCell_forces_other` the circuit side, and `occludedStayer_witness_n3`
    exhibits the class at `n = 3` by `decide`. The capstone is therefore NOT stated here; it needs a
    descriptor (or reference) FIX, not more assembly.

Board-size windows (`BoardWindow`) are EXPLICIT board arithmetic, not assumed arithmetization: they are
the no-wrap conditions of the coordinate decode and the fixed 9-bit `forced_ge0` ranges. They hold at
`n = 2`, `n = 3` and `n = 11`. NON-VACUOUS at `n = 3`, where occlusion genuinely bites (a 3-line has an
interior cell, so `occluded` can be `true` and the carry/`ft` conjuncts are live).

## Axiom hygiene
`#assert_axioms` subset `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`.
-/
import Dregg2.Circuit.Emit.AutomataflResolveRefine
import Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN
import Dregg2.Games.Automatafl

namespace Dregg2.Circuit.Emit.AutomataflResolveCapstone

open Dregg2.Circuit.Emit.AutomataflResolveEmit
open Dregg2.Circuit.Emit.AutomataflResolveMembership
open Dregg2.Circuit.Emit.AutomataflCoord
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric (OneHotAt)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)
open Dregg2.Circuit.Emit.AutomataflStepRefine
open Dregg2.Circuit.Emit.AutomataflResolveRefine
open Dregg2.Games.Automatafl (Board Coord Particle Move MoveValid moveValidB conflictResolve
  applyMoves occluded interior nextOf followChain resolveMid applyMoves_size
  applyMoves_cell_TT applyMoves_cell_TF applyMoves_cell_FT applyMoves_cell_FF)

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! ## §1 — the one-hot read primitive pinned to an arbitrary index HEAD.

`AutomataflCoord.oneHotN_of_sat` pins the one-hot's index to a bare COLUMN (`Head.lin 1 idxCol`). The
`write_mid` DESTINATION one-hots are pinned to `destHead own other ft = own + ft·(other − own)`, an
interpolation head. This is the same argument with the pin generalised; the canonicity of the pinned
VALUE (which the bare-column version got from `canon_loc`) becomes an explicit hypothesis, discharged
at the call site from the coordinate windows. -/

section OneHotHead
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace}

/-- **`oneHotHeadN_of_sat`.** A satisfied `n`-wide `Builder::one_hot` whose index is an arbitrary
`Head` forces its selector VALUES into a genuine `OneHotAt`, at the index the head evaluates to. -/
theorem oneHotHeadN_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (n : Nat) (hn : (n : ℤ) < 2013265921) (sel : Nat → Nat) (idx : Head)
    (hcanon : Canon (evalH idx (envAt t i).loc))
    (hbool : ∀ j, j < n → cg (gBin (sel j)) ∈ d.constraints)
    (hsumG : cgH (((List.range n).map sel).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1)))
               ∈ d.constraints)
    (hidxG : cgH (((((List.range n).map sel).zipIdx.foldl
                    (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero)).append
                    (idx.scale (-1))) ∈ d.constraints) :
    ∃ af : Nat, af < n ∧ evalH idx (envAt t i).loc = (af : ℤ)
      ∧ OneHotAt (fun j => (envAt t i).loc (sel j)) n af := by
  set e := envAt t i with he
  have hb : ∀ j, j < n → e.loc (sel j) = 0 ∨ e.loc (sel j) = 1 := by
    intro j hj
    exact bin_of_gate (ngate hsat i hi (hbool j hj)) (canon_loc hc i _)
  have hSsum : ((List.range n).map (fun j => e.loc (sel j))).sum = 1 := by
    have hg := ngateH hsat i hi hsumG
    rw [headToExpr_eval, evalH_foldl_addLin, evalH_c, List.map_map] at hg
    have hEq : (-1 + ((List.range n).map ((fun j => e.loc (sel j)))).sum)
        ≡ 0 [ZMOD 2013265921] := by
      rw [← he] at hg
      simpa [Function.comp_def] using hg
    have hmod : ((List.range n).map (fun j => e.loc (sel j))).sum ≡ 1 [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hEq
    obtain ⟨hlo, hhi⟩ := sum_bool_bounds hb
    exact eq_of_modEq_canon ⟨hlo, by exact lt_of_le_of_lt hhi hn⟩ canon_one hmod
  obtain ⟨af, hone⟩ := oneHot_exists hb hSsum
  have hidx : evalH idx e.loc = (af : ℤ) := by
    have hg := ngateH hsat i hi hidxG
    rw [headToExpr_eval, evalH_append, evalH_foldl_addLin_pairs, evalH_zero, evalH_scale,
      sum_zipIdx_sel] at hg
    have hT : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (sel j))).sum = (af : ℤ) := by
      have hcomm : ((List.range n).map (fun j : Nat => (j : ℤ) * e.loc (sel j)))
          = (List.range n).map (fun j => (fun j => e.loc (sel j)) j * (j : ℤ)) := by
        apply List.map_congr_left; intro j _; ring
      rw [hcomm, dot_oneHot hone (fun j => (j : ℤ))]
    rw [hT] at hg
    have hmod : (af : ℤ) ≡ evalH idx e.loc [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hg
    have hafcanon : Canon (af : ℤ) :=
      ⟨by positivity, by exact lt_of_le_of_lt (by exact_mod_cast Nat.le_of_lt hone.1) hn⟩
    exact (eq_of_modEq_canon hafcanon hcanon hmod).symm
  exact ⟨af, hone.1, hidx, hone⟩

end OneHotHead

/-! ## §2 — THE INDICATOR GLUE at arbitrary `n`.

The `write_mid` cell gate multiplies a row selector by a column selector; the product IS the `Coord`
indicator of the pinned point. At `NN = 2` this was `oneHotPair_indicator` over the four literal
cells; here it is the one-hot definition applied at `(x, y)`, for any `x, y < n`. -/

section Indicators
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {n : Nat}

/-- Two one-hots' product is the indicator of the pinned pair, at every in-range cell. -/
theorem oneHot_pair_ind {rv cv : Nat → ℤ} {ay ax : Nat}
    (hr : OneHotAt rv n ay) (hcv : OneHotAt cv n ax) (x y : Nat) (hx : x < n) (hy : y < n) :
    rv y * cv x = if (⟨x, y⟩ : Coord) = (⟨ax, ay⟩ : Coord) then 1 else 0 := by
  rw [hr.2 y hy, hcv.2 x hx]
  by_cases hxx : x = ax
  · by_cases hyy : y = ay
    · subst hxx; subst hyy; simp
    · rw [if_neg hyy, if_neg (by simp [hyy] : ¬ ((⟨x, y⟩ : Coord) = (⟨ax, ay⟩ : Coord)))]
      ring
  · rw [if_neg hxx, if_neg (by simp [hxx] : ¬ ((⟨x, y⟩ : Coord) = (⟨ax, ay⟩ : Coord)))]
    ring

/-- **`srcIndN_of_sat`.** The source row×column one-hot product IS the indicator of the move's own
source square, at every cell of the `n × n` board. -/
theorem srcIndN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hn : (n : ℤ) < 2013265921) :
    ∀ x y : Nat, x < n → y < n →
      (envAt t i).loc (NGen.wSrcRow n which y) * (envAt t i).loc (NGen.wSrcCol n which x)
        = if (⟨x, y⟩ : Coord)
             = (Dregg2.Circuit.Emit.AutomataflResolveRefine.moveDecodeN n (envAt t i) which).frm
          then 1 else 0 := by
  obtain ⟨ay, hayLt, hfyEq, hrow⟩ :=
    oneHotN_of_sat hsat hc i hi n hn (NGen.wSrcRow n which)
      (NGen.cFy n (NGen.mvBase n which))
      (fun j hj => mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint
        (we_srcRow_sel n which j hw hj)))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcRow_sum n which hw)))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcRow_idx n which hw)))
  obtain ⟨ax, haxLt, hfxEq, hcol⟩ :=
    oneHotN_of_sat hsat hc i hi n hn (NGen.wSrcCol n which)
      (NGen.cFx n (NGen.mvBase n which))
      (fun j hj => mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint
        (we_srcCol_sel n which j hw hj)))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcCol_sum n which hw)))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_srcCol_idx n which hw)))
  intro x y hx hy
  have hfrm : (Dregg2.Circuit.Emit.AutomataflResolveRefine.moveDecodeN n (envAt t i) which).frm
      = (⟨ax, ay⟩ : Coord) := by
    simp only [Dregg2.Circuit.Emit.AutomataflResolveRefine.moveDecodeN, hfxEq, hfyEq,
      Int.toNat_natCast]
  rw [hfrm]
  exact oneHot_pair_ind hrow hcol x y hx hy

/-- The interpolation head's VALUE: the piece's own coordinate, moved to the other piece's when the
flow-through bit is set. -/
theorem evalH_destHead (a : Nat → ℤ) (own other ft : Nat) :
    evalH (destHead own other ft) a = a own + a ft * a other - a ft * a own := by
  simp only [destHead, evalH_addProd, evalH_lin, varsVal, List.foldl_cons, List.foldl_nil]
  ring

/-- On a boolean `ft` the interpolation is a SELECTION. -/
theorem destHead_select (a : Nat → ℤ) (own other ft : Nat) (hft : a ft = 0 ∨ a ft = 1) :
    evalH (destHead own other ft) a = if a ft = 1 then a other else a own := by
  rw [evalH_destHead]
  rcases hft with h | h <;> rw [h] <;> norm_num

/-- **`dstIndN_of_sat`.** The destination row×column one-hot product IS the indicator of the square
the `ft` bit selects — the piece's own `to` when `ft = 0`, the OTHER piece's `to` when `ft = 1` —
at every cell of the `n × n` board. This is the `n`-generic twin of `dstIndicator_of_sat`. -/
theorem dstIndN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hn : (n : ℤ) < 2013265921)
    (hft : (envAt t i).loc (if which == 0 then NGen.cFtA n else NGen.cFtB n) = 0
        ∨ (envAt t i).loc (if which == 0 then NGen.cFtA n else NGen.cFtB n) = 1)
    (hx0 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which)) < (n : ℤ))
    (hy0 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which)) < (n : ℤ))
    (hx1 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which))) < (n : ℤ))
    (hy1 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which))) < (n : ℤ)) :
    ∀ x y : Nat, x < n → y < n →
      (envAt t i).loc (NGen.wDstRow n which y) * (envAt t i).loc (NGen.wDstCol n which x)
        = if (⟨x, y⟩ : Coord)
             = (if (envAt t i).loc (if which == 0 then NGen.cFtA n else NGen.cFtB n) = 1
                then (Dregg2.Circuit.Emit.AutomataflResolveRefine.moveDecodeN n (envAt t i)
                        (1 - which)).to
                else (Dregg2.Circuit.Emit.AutomataflResolveRefine.moveDecodeN n (envAt t i)
                        which).to)
          then 1 else 0 := by
  set e := envAt t i with he
  set ftc := (if which == 0 then NGen.cFtA n else NGen.cFtB n) with hftc
  have hcanonRow : Canon (evalH (destHead (NGen.cTy n (NGen.mvBase n which))
      (NGen.cTy n (NGen.mvBase n (1 - which))) ftc) e.loc) := by
    rw [destHead_select _ _ _ _ hft]
    by_cases h : e.loc ftc = 1
    · rw [if_pos h]; exact ⟨hy1.1, lt_trans hy1.2 hn⟩
    · rw [if_neg h]; exact ⟨hy0.1, lt_trans hy0.2 hn⟩
  have hcanonCol : Canon (evalH (destHead (NGen.cTx n (NGen.mvBase n which))
      (NGen.cTx n (NGen.mvBase n (1 - which))) ftc) e.loc) := by
    rw [destHead_select _ _ _ _ hft]
    by_cases h : e.loc ftc = 1
    · rw [if_pos h]; exact ⟨hx1.1, lt_trans hx1.2 hn⟩
    · rw [if_neg h]; exact ⟨hx0.1, lt_trans hx0.2 hn⟩
  obtain ⟨ar, harLt, harEq, hrow⟩ :=
    oneHotHeadN_of_sat hsat hc i hi n hn (NGen.wDstRow n which)
      (destHead (NGen.cTy n (NGen.mvBase n which)) (NGen.cTy n (NGen.mvBase n (1 - which))) ftc)
      hcanonRow
      (fun j hj => mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint
        (we_dstRow_sel n which j hw hj)))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstRow_sum n which hw)))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstRow_idx n which hw)))
  obtain ⟨ac, hacLt, hacEq, hcol⟩ :=
    oneHotHeadN_of_sat hsat hc i hi n hn (NGen.wDstCol n which)
      (destHead (NGen.cTx n (NGen.mvBase n which)) (NGen.cTx n (NGen.mvBase n (1 - which))) ftc)
      hcanonCol
      (fun j hj => mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint
        (we_dstCol_sel n which j hw hj)))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstCol_sum n which hw)))
      (mem_resolve_of_mem_writeMid (mem_writeMid_of_writeEndpoint (we_dstCol_idx n which hw)))
  rw [destHead_select _ _ _ _ hft] at harEq hacEq
  have hpt : (if e.loc ftc = 1
        then (Dregg2.Circuit.Emit.AutomataflResolveRefine.moveDecodeN n e (1 - which)).to
        else (Dregg2.Circuit.Emit.AutomataflResolveRefine.moveDecodeN n e which).to)
      = (⟨ac, ar⟩ : Coord) := by
    by_cases h : e.loc ftc = 1
    · rw [if_pos h] at harEq hacEq ⊢
      simp only [Dregg2.Circuit.Emit.AutomataflResolveRefine.moveDecodeN, harEq, hacEq,
        Int.toNat_natCast]
    · rw [if_neg h] at harEq hacEq ⊢
      simp only [Dregg2.Circuit.Emit.AutomataflResolveRefine.moveDecodeN, harEq, hacEq,
        Int.toNat_natCast]
  intro x y hx hy
  rw [hpt]
  exact oneHot_pair_ind hrow hcol x y hx hy

end Indicators

/-! ## §3 — the BOARD-SIZE WINDOW, and the derived per-row semantic facts at arbitrary `n`.

Every window here is EXPLICIT board arithmetic — the no-wrap conditions of the coordinate decode and
of the FIXED 9-bit `forced_ge0` ranges the emitter uses for the squared-distance sites. None of them
is an assumed arithmetization hypothesis: they are inequalities about `n`, decidable at any concrete
board size, and they hold at `n = 2`, `n = 3` and `n = 11`. -/

/-- The board-size window Leg R's `n`-generic extraction needs. -/
structure BoardWindow (n : Nat) : Prop where
  /-- The board is non-degenerate. -/
  pos    : 1 ≤ n
  /-- Board indices do not wrap the field. -/
  lt_p   : (n : ℤ) < 2013265921
  /-- The 9-bit `forced_ge0` range of the 1-D squared distance (`(n−1)² ≤ 511`). -/
  sq511  : ((n : ℤ) - 1) * ((n : ℤ) - 1) ≤ 511
  /-- The occlusion masked-sum window (`3n ≤ 999`, the `msum` bound over `[0,3]` line felts). -/
  msum   : 3 * (n : ℤ) ≤ 999
  /-- The 9-bit `forced_ge0` range of the 2-D squared distance (`2(n−1)² ≤ 999`). -/
  sq999  : 2 * ((n : ℤ) - 1) * ((n : ℤ) - 1) ≤ 999
  /-- The rook-alignment / squared-distance no-wrap window. -/
  sqM    : ((n : ℤ) - 1) * ((n : ℤ) - 1) ≤ 1000000
  /-- The coordinate decode's no-wrap window. -/
  rbits  : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921

/-- The window at the deployed sizes. NON-VACUOUS: `n = 3` is the first size at which a rook line
has a strictly-interior cell, so occlusion genuinely bites there. -/
theorem boardWindow_two : BoardWindow 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h : NGen.COORD_RBITS 2 = 1 := by decide
  rw [h]; norm_num
theorem boardWindow_three : BoardWindow 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h : NGen.COORD_RBITS 3 = 2 := by decide
  rw [h]; norm_num
theorem boardWindow_eleven : BoardWindow 11 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h : NGen.COORD_RBITS 11 = 4 := by decide
  rw [h]; norm_num

section Facts
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {n : Nat}

/-- `validate_move` membership at either piece index. -/
theorem mvLift (n which : Nat) (hw : which < 2) {g : VmConstraint2}
    (h : g ∈ NGen.validateMove n (NGen.mvBase n which)) :
    g ∈ (automataflResolveDescN n).constraints := by
  interval_cases which
  · exact mem_resolve_of_mem_validateMove0 h
  · exact mem_resolve_of_mem_validateMove1 h

/-- `validate_occlusion` membership at either piece index. -/
theorem occLift (n which : Nat) (hw : which < 2) {g : VmConstraint2}
    (h : g ∈ NGen.validateOcclusion n (NGen.mvBase n which) (NGen.occBase n which)
           (NGen.mvBase n (1 - which))) :
    g ∈ (automataflResolveDescN n).constraints := by
  interval_cases which
  · exact mem_resolve_of_mem_validateOcclusion0 h
  · exact mem_resolve_of_mem_validateOcclusion1 h

/-- `occluded` depends on the passable-source list only through MEMBERSHIP, so the two pieces'
source lists (which the occlusion block emits in each move's own order) agree. -/
theorem occluded_swap (b : Board) (p q : Coord) (m : Move) :
    occluded b [p, q] m = occluded b [q, p] m := by
  simp only [occluded, List.contains_cons, List.contains_nil, Bool.or_false]
  congr 1
  funext c
  by_cases h1 : c = p <;> by_cases h2 : c = q <;> simp [h1, h2]

/-- The four coordinate columns of one move, all decoded into `[0, n)` — off the reference
`MoveValid` (whose in-bounds clause is a `toNat` statement) plus row canonicity (which supplies the
missing non-negativity, so the `toNat` bound IS the integer bound). -/
theorem moveCoordBounds (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : BoardWindow n)
    (which : Nat) (hw : which < 2) :
    (0 ≤ (envAt t i).loc (NGen.cFx n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cFx n (NGen.mvBase n which)) < (n : ℤ))
    ∧ (0 ≤ (envAt t i).loc (NGen.cFy n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cFy n (NGen.mvBase n which)) < (n : ℤ))
    ∧ (0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which)) < (n : ℤ))
    ∧ (0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which)) < (n : ℤ)) := by
  obtain ⟨-, -, ⟨hfx, hfy⟩, ⟨htx, hty⟩, -, -, -, -⟩ :=
    validMoveN_of_sat hsat hc i hi which ((n : ℤ) - 1) W.pos W.lt_p rfl W.sqM W.rbits
      (mvLift n which hw)
  have c1 := (canon_loc hc i (NGen.cFx n (NGen.mvBase n which))).1
  have c2 := (canon_loc hc i (NGen.cFy n (NGen.mvBase n which))).1
  have c3 := (canon_loc hc i (NGen.cTx n (NGen.mvBase n which))).1
  have c4 := (canon_loc hc i (NGen.cTy n (NGen.mvBase n which))).1
  simp only [Dregg2.Circuit.Emit.AutomataflResolveRefine.moveDecodeN,
    Dregg2.Circuit.Emit.AutomataflResolveRefine.boardDecodeOldN] at hfx hfy htx hty
  refine ⟨⟨c1, ?_⟩, ⟨c2, ?_⟩, ⟨c3, ?_⟩, ⟨c4, ?_⟩⟩ <;> omega

/-- `Int.toNat` is injective on the non-negatives, so a decoded `Coord` equality IS the pair of
column equalities — the `n`-generic replacement for `toNat_inj01`. -/
theorem toNat_injN {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a.toNat = b.toNat) ↔ a = b := by
  omega

/-- **THE DERIVED PER-ROW FACTS, AT ARBITRARY `n`.** The `n`-generic twin of `ResolveFacts`: every
field is a THEOREM about `automataflResolveDescN n` (see `resolveFactsN_of_sat`). The carry and
flow-through fields carry the REFERENCE occlusion predicate — at `n ≥ 3` those conjuncts are live,
where at `NN = 2` they were vacuously discharged. -/
structure ResolveFactsN (n : Nat) (e : VmRowEnv) : Prop where
  validA : MoveValid (boardDecodeOldN n e) (moveDecodeN n e 0)
  validB : MoveValid (boardDecodeOldN n e) (moveDecodeN n e 1)
  alphaOld : ∀ c, c < NGen.KK n →
    (e.loc (NGen.old n c) = 0 ∨ e.loc (NGen.old n c) = 1 ∨ e.loc (NGen.old n c) = 2
      ∨ e.loc (NGen.old n c) = 3)
  alphaMid : ∀ c, c < NGen.KK n →
    (e.loc (NGen.mid n c) = 0 ∨ e.loc (NGen.mid n c) = 1 ∨ e.loc (NGen.mid n c) = 2
      ∨ e.loc (NGen.mid n c) = 3)
  paVal : (boardDecodeOldN n e).cellAt (moveDecodeN n e 0).frm
    = codeToParticle (e.loc (NGen.particleCol n 0))
  pbVal : (boardDecodeOldN n e).cellAt (moveDecodeN n e 1).frm
    = codeToParticle (e.loc (NGen.particleCol n 1))
  paAlpha : e.loc (NGen.particleCol n 0) = 0 ∨ e.loc (NGen.particleCol n 0) = 1
    ∨ e.loc (NGen.particleCol n 0) = 2 ∨ e.loc (NGen.particleCol n 0) = 3
  pbAlpha : e.loc (NGen.particleCol n 1) = 0 ∨ e.loc (NGen.particleCol n 1) = 1
    ∨ e.loc (NGen.particleCol n 1) = 2 ∨ e.loc (NGen.particleCol n 1) = 3
  survB : e.loc (NGen.cSurv n) = 0 ∨ e.loc (NGen.cSurv n) = 1
  anzB : e.loc (NGen.cAnz n) = 0 ∨ e.loc (NGen.cAnz n) = 1
  bnzB : e.loc (NGen.cBnz n) = 0 ∨ e.loc (NGen.cBnz n) = 1
  anzIff : e.loc (NGen.cAnz n) = 1 ↔
    ((boardDecodeOldN n e).cellAt (moveDecodeN n e 0).frm).isVacuum = false
  bnzIff : e.loc (NGen.cBnz n) = 1 ↔
    ((boardDecodeOldN n e).cellAt (moveDecodeN n e 1).frm).isVacuum = false
  survIff : e.loc (NGen.cSurv n) = 1 ↔
    ¬ (((moveDecodeN n e 0).frm = (moveDecodeN n e 1).frm
          ∧ (moveDecodeN n e 0).to ≠ (moveDecodeN n e 1).to)
       ∨ ((moveDecodeN n e 0).to = (moveDecodeN n e 1).to
          ∧ (moveDecodeN n e 0).frm ≠ (moveDecodeN n e 1).frm
          ∧ ((boardDecodeOldN n e).cellAt (moveDecodeN n e 0).frm).isVacuum = false
          ∧ ((boardDecodeOldN n e).cellAt (moveDecodeN n e 1).frm).isVacuum = false))
  carryAB : e.loc (NGen.cCarryA n) = 0 ∨ e.loc (NGen.cCarryA n) = 1
  carryBB : e.loc (NGen.cCarryB n) = 0 ∨ e.loc (NGen.cCarryB n) = 1
  carryAIff : e.loc (NGen.cCarryA n) = 1 ↔
    (e.loc (NGen.cSurv n) = 1 ∧ e.loc (NGen.cAnz n) = 1
      ∧ occluded (boardDecodeOldN n e)
          [(moveDecodeN n e 0).frm, (moveDecodeN n e 1).frm] (moveDecodeN n e 0) = false)
  carryBIff : e.loc (NGen.cCarryB n) = 1 ↔
    (e.loc (NGen.cSurv n) = 1 ∧ e.loc (NGen.cBnz n) = 1
      ∧ occluded (boardDecodeOldN n e)
          [(moveDecodeN n e 0).frm, (moveDecodeN n e 1).frm] (moveDecodeN n e 1) = false)
  ftAB : e.loc (NGen.cFtA n) = 0 ∨ e.loc (NGen.cFtA n) = 1
  ftBB : e.loc (NGen.cFtB n) = 0 ∨ e.loc (NGen.cFtB n) = 1
  ftAIff : e.loc (NGen.cFtA n) = 1 ↔
    ((moveDecodeN n e 0).to = (moveDecodeN n e 1).frm ∧ e.loc (NGen.cBnz n) = 0
      ∧ e.loc (NGen.cSurv n) = 1
      ∧ occluded (boardDecodeOldN n e)
          [(moveDecodeN n e 0).frm, (moveDecodeN n e 1).frm] (moveDecodeN n e 1) = false
      ∧ (moveDecodeN n e 1).to ≠ (moveDecodeN n e 0).frm)
  ftBIff : e.loc (NGen.cFtB n) = 1 ↔
    ((moveDecodeN n e 1).to = (moveDecodeN n e 0).frm ∧ e.loc (NGen.cAnz n) = 0
      ∧ e.loc (NGen.cSurv n) = 1
      ∧ occluded (boardDecodeOldN n e)
          [(moveDecodeN n e 0).frm, (moveDecodeN n e 1).frm] (moveDecodeN n e 0) = false
      ∧ (moveDecodeN n e 0).to ≠ (moveDecodeN n e 1).frm)
  srcIndA : ∀ x y : Nat, x < n → y < n →
    e.loc (NGen.wSrcRow n 0 y) * e.loc (NGen.wSrcCol n 0 x)
      = if (⟨x, y⟩ : Coord) = (moveDecodeN n e 0).frm then 1 else 0
  srcIndB : ∀ x y : Nat, x < n → y < n →
    e.loc (NGen.wSrcRow n 1 y) * e.loc (NGen.wSrcCol n 1 x)
      = if (⟨x, y⟩ : Coord) = (moveDecodeN n e 1).frm then 1 else 0
  dstIndA : ∀ x y : Nat, x < n → y < n →
    e.loc (NGen.wDstRow n 0 y) * e.loc (NGen.wDstCol n 0 x)
      = if (⟨x, y⟩ : Coord)
           = (if e.loc (NGen.cFtA n) = 1 then (moveDecodeN n e 1).to else (moveDecodeN n e 0).to)
        then 1 else 0
  dstIndB : ∀ x y : Nat, x < n → y < n →
    e.loc (NGen.wDstRow n 1 y) * e.loc (NGen.wDstCol n 1 x)
      = if (⟨x, y⟩ : Coord)
           = (if e.loc (NGen.cFtB n) = 1 then (moveDecodeN n e 0).to else (moveDecodeN n e 1).to)
        then 1 else 0

/-- The occlusion bridge's board/move decodes ARE this file's (both are the same structure literal;
the two files carry their own copy of the definition). -/
theorem bdN_eq (m : Nat) (e : VmRowEnv) :
    Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.boardDecodeOldN m e = boardDecodeOldN m e := rfl
theorem mdN_eq (m : Nat) (e : VmRowEnv) (w : Nat) :
    Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.moveDecodeN m e w = moveDecodeN m e w := rfl

/-- The `fork` and `collide` columns are BOOLEAN — the piece of the selection block
`selectionN_of_sat` computes internally but does not export, and which the `surv` translation needs
to turn "not `1`" into "`0`". -/
theorem forkCollideBoolN (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hff : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1)
    (htt : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1)
    (hanz : (envAt t i).loc (NGen.cAnz n) = 0 ∨ (envAt t i).loc (NGen.cAnz n) = 1)
    (hbnz : (envAt t i).loc (NGen.cBnz n) = 0 ∨ (envAt t i).loc (NGen.cBnz n) = 1) :
    ((envAt t i).loc (NGen.cFork n) = 0 ∨ (envAt t i).loc (NGen.cFork n) = 1)
      ∧ ((envAt t i).loc (NGen.cCollide n) = 0 ∨ (envAt t i).loc (NGen.cCollide n) = 1) := by
  set e := envAt t i with he
  have hforkv : e.loc (NGen.cFork n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 0))
        - e.loc (NGen.cEqBit n (NGen.eqBase n 0)) * e.loc (NGen.cEqBit n (NGen.eqBase n 1)) := by
    have hg := rgateHN hsat i hi
      (h := ((Head.lin 1 (NGen.cFork n)).addLin (-1) (NGen.cEqBit n (NGen.eqBase n 0))).addProd 1
              [NGen.cEqBit n (NGen.eqBase n 0), NGen.cEqBit n (NGen.eqBase n 1)])
      (mem_selection_idx n 0 (show (0:Nat) < 6 by decide))
    have hE : (headToExpr (((Head.lin 1 (NGen.cFork n)).addLin (-1)
          (NGen.cEqBit n (NGen.eqBase n 0))).addProd 1
          [NGen.cEqBit n (NGen.eqBase n 0), NGen.cEqBit n (NGen.eqBase n 1)])).eval e.loc
        = e.loc (NGen.cFork n) + (-1) * e.loc (NGen.cEqBit n (NGen.eqBase n 0))
          + e.loc (NGen.cEqBit n (NGen.eqBase n 0)) * e.loc (NGen.cEqBit n (NGen.eqBase n 1)) := by canon_head_eval [headToExpr]
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rcases htt with b | b <;> rw [a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hnff : e.loc (NGen.cNeqFf n) = 1 - e.loc (NGen.cEqBit n (NGen.eqBase n 0)) :=
    notBitN_of_sat hsat hc i hi (NGen.cNeqFf n) (NGen.cEqBit n (NGen.eqBase n 0))
      (mem_selection_idx n 1 (show (1:Nat) < 6 by decide)) hff
  have hnffB : e.loc (NGen.cNeqFf n) = 0 ∨ e.loc (NGen.cNeqFf n) = 1 := by
    rcases hff with a | a <;> rw [hnff, a] <;> norm_num
  have hcol1 : e.loc (NGen.cCol1 n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 1)) * e.loc (NGen.cNeqFf n) :=
    prodN_of_sat hsat hc i hi (NGen.cCol1 n) (NGen.cEqBit n (NGen.eqBase n 1)) (NGen.cNeqFf n)
      (mem_selection_idx n 2 (show (2:Nat) < 6 by decide)) htt hnffB
  have hcol1B : e.loc (NGen.cCol1 n) = 0 ∨ e.loc (NGen.cCol1 n) = 1 := by
    rcases htt with a | a <;> rcases hnffB with b | b <;> rw [hcol1, a, b] <;> norm_num
  have hcol2 : e.loc (NGen.cCol2 n) = e.loc (NGen.cCol1 n) * e.loc (NGen.cAnz n) :=
    prodN_of_sat hsat hc i hi (NGen.cCol2 n) (NGen.cCol1 n) (NGen.cAnz n)
      (mem_selection_idx n 3 (show (3:Nat) < 6 by decide)) hcol1B hanz
  have hcol2B : e.loc (NGen.cCol2 n) = 0 ∨ e.loc (NGen.cCol2 n) = 1 := by
    rcases hcol1B with a | a <;> rcases hanz with b | b <;> rw [hcol2, a, b] <;> norm_num
  have hcollv : e.loc (NGen.cCollide n) = e.loc (NGen.cCol2 n) * e.loc (NGen.cBnz n) :=
    prodN_of_sat hsat hc i hi (NGen.cCollide n) (NGen.cCol2 n) (NGen.cBnz n)
      (mem_selection_idx n 4 (show (4:Nat) < 6 by decide)) hcol2B hbnz
  refine ⟨?_, ?_⟩
  · rcases hff with a | a <;> rcases htt with b | b <;> rw [hforkv, a, b] <;> norm_num
  · rcases hcol2B with a | a <;> rcases hbnz with b | b <;> rw [hcollv, a, b] <;> norm_num

/-- **`resolveFactsN_of_sat` — EVERY FACT THE ASSEMBLY NEEDS, AT ARBITRARY `n`.** Off a satisfying,
canonical row of the emitted `automataflResolveDescN n`, under the explicit board-size window. The
occlusion conjuncts are the REFERENCE `Automatafl.occluded`, routed through the `n`-generic bridge. -/
theorem resolveFactsN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : BoardWindow n) :
    ResolveFactsN n (envAt t i) := by
  -- the eight coordinate columns, decoded into `[0, n)`
  obtain ⟨hfxa, hfya, htxa, htya⟩ := moveCoordBounds hsat hc i hi W 0 (by norm_num)
  obtain ⟨hfxb, hfyb, htxb, htyb⟩ := moveCoordBounds hsat hc i hi W 1 (by norm_num)
  have hM : ∀ z : ℤ, 0 ≤ z ∧ z < (n : ℤ) → 0 ≤ z ∧ z ≤ (n : ℤ) - 1 := by
    rintro z ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  -- the four pattern bits
  obtain ⟨hffB, hffI⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cFx n (NGen.mvBase n 0))
    (NGen.cFy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 0) ((n : ℤ) - 1) (by have := W.sq999; linarith)
    (hM _ hfxa) (hM _ hfya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))))
  obtain ⟨httB, httI⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cTx n (NGen.mvBase n 1)) (NGen.cTy n (NGen.mvBase n 1))
    (NGen.eqBase n 1) ((n : ℤ) - 1) (by have := W.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ htxb) (hM _ htyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))))
  obtain ⟨habB, habI⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 2) ((n : ℤ) - 1) (by have := W.sq999; linarith)
    (hM _ htxa) (hM _ htya) (hM _ hfxb) (hM _ hfyb)
    (fun h => mem_resolve_of_mem_patternBit
      (List.mem_append_left _ (List.mem_append_right _ h)))
  obtain ⟨hbaB, hbaI⟩ := eqCoordsN_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 1))
    (NGen.cTy n (NGen.mvBase n 1)) (NGen.cFx n (NGen.mvBase n 0)) (NGen.cFy n (NGen.mvBase n 0))
    (NGen.eqBase n 3) ((n : ℤ) - 1) (by have := W.sq999; linarith)
    (hM _ htxb) (hM _ htyb) (hM _ hfxa) (hM _ hfya)
    (fun h => mem_resolve_of_mem_patternBit (List.mem_append_right _ h))
  -- the two non-vacuum bits
  obtain ⟨hanzB, hanzI⟩ := srcNonVacN_of_sat hsat hc i hi 0 (NGen.cAnz n) (NGen.anzBit n 0) W.lt_p
    (mvLift n 0 (by norm_num))
    (mem_resolve_of_mem_srcNonVac (List.mem_append_left _ (mem_forcedGe0N_ib _ _ _ _)))
    (fun k hk => mem_resolve_of_mem_srcNonVac
      (List.mem_append_left _ (mem_forcedGe0N_bit _ _ _ _ k hk)))
    (mem_resolve_of_mem_srcNonVac (List.mem_append_left _ (mem_forcedGe0N_head _ _ _ _)))
  obtain ⟨hbnzB, hbnzI⟩ := srcNonVacN_of_sat hsat hc i hi 1 (NGen.cBnz n) (NGen.bnzBit n 0) W.lt_p
    (mvLift n 1 (by norm_num))
    (mem_resolve_of_mem_srcNonVac (List.mem_append_right _ (mem_forcedGe0N_ib _ _ _ _)))
    (fun k hk => mem_resolve_of_mem_srcNonVac
      (List.mem_append_right _ (mem_forcedGe0N_bit _ _ _ _ k hk)))
    (mem_resolve_of_mem_srcNonVac (List.mem_append_right _ (mem_forcedGe0N_head _ _ _ _)))
  -- the occlusion bits: boolean, and EXACTLY the reference `occluded`
  have hoccaB : (envAt t i).loc (NGen.cOcc n (NGen.occBase n 0)) = 0
      ∨ (envAt t i).loc (NGen.cOcc n (NGen.occBase n 0)) = 1 :=
    bin_of_gate (rgateN hsat i hi (occLift n 0 (by norm_num) (vo_occ_ib n _ _ _)))
      (canon_loc hc i _)
  have hoccbB : (envAt t i).loc (NGen.cOcc n (NGen.occBase n 1)) = 0
      ∨ (envAt t i).loc (NGen.cOcc n (NGen.occBase n 1)) = 1 :=
    bin_of_gate (rgateN hsat i hi (occLift n 1 (by norm_num) (vo_occ_ib n _ _ _)))
      (canon_loc hc i _)
  have hoccaI : (envAt t i).loc (NGen.cOcc n (NGen.occBase n 0)) = 1
      ↔ occluded (boardDecodeOldN n (envAt t i)) [(moveDecodeN n (envAt t i) 0).frm, (moveDecodeN n (envAt t i) 1).frm]
          (moveDecodeN n (envAt t i) 0) = true := by
    have h := Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.occ_iff_occluded_of_sat n 0 W.lt_p
      W.sq511 W.msum hsat hc i hi (occLift n 0 (by norm_num)) (mvLift n 0 (by norm_num))
      (mvLift n 1 (by norm_num))
    simpa [bdN_eq, mdN_eq] using h
  have hoccbI : (envAt t i).loc (NGen.cOcc n (NGen.occBase n 1)) = 1
      ↔ occluded (boardDecodeOldN n (envAt t i)) [(moveDecodeN n (envAt t i) 0).frm, (moveDecodeN n (envAt t i) 1).frm]
          (moveDecodeN n (envAt t i) 1) = true := by
    have h := Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.occ_iff_occluded_of_sat n 1 W.lt_p
      W.sq511 W.msum hsat hc i hi (occLift n 1 (by norm_num)) (mvLift n 1 (by norm_num))
      (mvLift n 0 (by norm_num))
    rw [occluded_swap] at h
    simpa [bdN_eq, mdN_eq] using h
  -- the selection truth table, the carries and the flow-through bits
  obtain ⟨hforkI, hcollI, hsurvB, hsurvI⟩ :=
    selectionN_of_sat hsat hc i hi hffB httB hanzB hbnzB
  obtain ⟨hforkB, hcollB⟩ := forkCollideBoolN hsat hc i hi hffB httB hanzB hbnzB
  obtain ⟨hcaB, hcaI⟩ := carryAN_of_sat hsat hc i hi hsurvB hanzB hoccaB
  obtain ⟨hcbB, hcbI⟩ := carryBN_of_sat hsat hc i hi hsurvB hbnzB hoccbB
  obtain ⟨hftaB, hftaI⟩ := ftAN_of_sat hsat hc i hi habB hbnzB hoccbB hbaB hsurvB
  obtain ⟨hftbB, hftbI⟩ := ftBN_of_sat hsat hc i hi hbaB hanzB hoccaB habB hsurvB
  -- the `Coord`-level readings of the four pattern bits
  have hffC : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1
      ↔ (moveDecodeN n (envAt t i) 0).frm = (moveDecodeN n (envAt t i) 1).frm := by
    rw [hffI]
    simp only [moveDecodeN, Coord.mk.injEq]
    rw [toNat_injN hfxa.1 hfxb.1, toNat_injN hfya.1 hfyb.1]
  have httC : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1
      ↔ (moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).to := by
    rw [httI]
    simp only [moveDecodeN, Coord.mk.injEq]
    rw [toNat_injN htxa.1 htxb.1, toNat_injN htya.1 htyb.1]
  have habC : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1
      ↔ (moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).frm := by
    rw [habI]
    simp only [moveDecodeN, Coord.mk.injEq]
    rw [toNat_injN htxa.1 hfxb.1, toNat_injN htya.1 hfyb.1]
  have hbaC : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1
      ↔ (moveDecodeN n (envAt t i) 1).to = (moveDecodeN n (envAt t i) 0).frm := by
    rw [hbaI]
    simp only [moveDecodeN, Coord.mk.injEq]
    rw [toNat_injN htxb.1 hfxa.1, toNat_injN htyb.1 hfya.1]
  -- the witnessed source particle IS the OLD board cell there
  have hsrc : ∀ which : Nat, which < 2 →
      (boardDecodeOldN n (envAt t i)).cellAt (moveDecodeN n (envAt t i) which).frm
          = codeToParticle ((envAt t i).loc (NGen.cFp n (NGen.mvBase n which)))
        ∧ ((envAt t i).loc (NGen.cFp n (NGen.mvBase n which)) = 0
            ∨ (envAt t i).loc (NGen.cFp n (NGen.mvBase n which)) = 1
            ∨ (envAt t i).loc (NGen.cFp n (NGen.mvBase n which)) = 2
            ∨ (envAt t i).loc (NGen.cFp n (NGen.mvBase n which)) = 3) := by
    intro which hw
    obtain ⟨X, Y, hX, hY, hfxE, hfyE, hfp⟩ :=
      sourceReadN_of_sat hsat hc i hi (NGen.mvBase n which) W.lt_p (mvLift n which hw)
    have hXY : Y * n + X < NGen.KK n := by
      simp only [NGen.KK]
      have hle : (Y + 1) * n ≤ n * n := Nat.mul_le_mul_right n (by omega : Y + 1 ≤ n)
      have hexp : (Y + 1) * n = Y * n + n := by ring
      omega
    have halpha : (envAt t i).loc (NGen.old n (Y * n + X)) = 0 ∨ (envAt t i).loc (NGen.old n (Y * n + X)) = 1
        ∨ (envAt t i).loc (NGen.old n (Y * n + X)) = 2 ∨ (envAt t i).loc (NGen.old n (Y * n + X)) = 3 :=
      AutomataflStepRefine.mem4_of_gate
        (rgateN hsat i hi (mem_resolve_of_mem_boardRange (br_old n (Y * n + X) hXY)))
        (canon_loc hc i _)
    refine ⟨?_, by rw [hfp]; exact halpha⟩
    have hfrm : (moveDecodeN n (envAt t i) which).frm = (⟨X, Y⟩ : Coord) := by
      simp only [moveDecodeN, hfxE, hfyE, Int.toNat_natCast]
    rw [hfrm, hfp]
    simp only [boardDecodeOldN, Board.cellAt]
    exact if_pos (⟨hX, hY⟩ : X < n ∧ Y < n)
  obtain ⟨hpaV, hpaA⟩ := hsrc 0 (by norm_num)
  obtain ⟨hpbV, hpbA⟩ := hsrc 1 (by norm_num)
  refine
    { validA := validMoveN_of_sat hsat hc i hi 0 ((n : ℤ) - 1) W.pos W.lt_p rfl W.sqM W.rbits
        (mvLift n 0 (by norm_num))
      validB := validMoveN_of_sat hsat hc i hi 1 ((n : ℤ) - 1) W.pos W.lt_p rfl W.sqM W.rbits
        (mvLift n 1 (by norm_num))
      alphaOld := fun c hcK =>
        AutomataflStepRefine.mem4_of_gate
          (rgateN hsat i hi (mem_resolve_of_mem_boardRange (br_old n c hcK))) (canon_loc hc i _)
      alphaMid := fun c hcK =>
        AutomataflStepRefine.mem4_of_gate
          (rgateN hsat i hi (mem_resolve_of_mem_boardRange (br_mid n c hcK))) (canon_loc hc i _)
      paVal := hpaV
      pbVal := hpbV
      paAlpha := hpaA
      pbAlpha := hpbA
      survB := hsurvB
      anzB := hanzB
      bnzB := hbnzB
      anzIff := hanzI
      bnzIff := hbnzI
      carryAB := hcaB
      carryBB := hcbB
      ftAB := hftaB
      ftBB := hftbB
      survIff := ?_
      carryAIff := ?_
      carryBIff := ?_
      ftAIff := ?_
      ftBIff := ?_
      srcIndA := srcIndN_of_sat hsat hc i hi 0 (by norm_num) W.lt_p
      srcIndB := srcIndN_of_sat hsat hc i hi 1 (by norm_num) W.lt_p
      dstIndA := dstIndN_of_sat hsat hc i hi 0 (by norm_num) W.lt_p hftaB htxa htya htxb htyb
      dstIndB := dstIndN_of_sat hsat hc i hi 1 (by norm_num) W.lt_p hftbB htxb htyb htxa htya }
  · -- survIff
    rw [hsurvI]
    constructor
    · rintro ⟨hf0, hc0⟩ hPQ
      rcases hPQ with h | h
      · have httz : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 0 := by
          rcases httB with hz | ho
          · exact hz
          · exact absurd (httC.mp ho) h.2
        have : (envAt t i).loc (NGen.cFork n) = 1 := hforkI.mpr ⟨hffC.mpr h.1, httz⟩
        omega
      · have hffz : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 0 := by
          rcases hffB with hz | ho
          · exact hz
          · exact absurd (hffC.mp ho) h.2.1
        have : (envAt t i).loc (NGen.cCollide n) = 1 :=
          hcollI.mpr ⟨httC.mpr h.1, hffz, hanzI.mpr h.2.2.1, hbnzI.mpr h.2.2.2⟩
        omega
    · intro hno
      refine ⟨?_, ?_⟩
      · rcases hforkB with hz | ho
        · exact hz
        · obtain ⟨h1, h2⟩ := hforkI.mp ho
          refine absurd (Or.inl ⟨hffC.mp h1, ?_⟩) hno
          intro hEq
          have := httC.mpr hEq
          omega
      · rcases hcollB with hz | ho
        · exact hz
        · obtain ⟨h1, h2, h3, h4⟩ := hcollI.mp ho
          refine absurd (Or.inr ⟨httC.mp h1, ?_, hanzI.mp h3, hbnzI.mp h4⟩) hno
          intro hEq
          have := hffC.mpr hEq
          omega
  · rw [hcaI]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      cases hoccc : occluded (boardDecodeOldN n (envAt t i))
          [(moveDecodeN n (envAt t i) 0).frm, (moveDecodeN n (envAt t i) 1).frm] (moveDecodeN n (envAt t i) 0)
      · rfl
      · rw [hoccaI.mpr hoccc] at h3; exact absurd h3 (by norm_num)
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rcases hoccaB with hz | ho
      · exact hz
      · rw [hoccaI.mp ho] at h3; exact absurd h3 (by norm_num)
  · rw [hcbI]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      cases hoccc : occluded (boardDecodeOldN n (envAt t i))
          [(moveDecodeN n (envAt t i) 0).frm, (moveDecodeN n (envAt t i) 1).frm] (moveDecodeN n (envAt t i) 1)
      · rfl
      · rw [hoccbI.mpr hoccc] at h3; exact absurd h3 (by norm_num)
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rcases hoccbB with hz | ho
      · exact hz
      · rw [hoccbI.mp ho] at h3; exact absurd h3 (by norm_num)
  · rw [hftaI]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨habC.mp h1, h2, h3, ?_, fun hEq => by have := hbaC.mpr hEq; omega⟩
      cases hoccc : occluded (boardDecodeOldN n (envAt t i))
          [(moveDecodeN n (envAt t i) 0).frm, (moveDecodeN n (envAt t i) 1).frm] (moveDecodeN n (envAt t i) 1)
      · rfl
      · rw [hoccbI.mpr hoccc] at h4; exact absurd h4 (by norm_num)
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨habC.mpr h1, h2, h3, ?_, ?_⟩
      · rcases hoccbB with hz | ho
        · exact hz
        · rw [hoccbI.mp ho] at h4; exact absurd h4 (by norm_num)
      · rcases hbaB with hz | ho
        · exact hz
        · exact absurd (hbaC.mp ho) h5
  · rw [hftbI]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨hbaC.mp h1, h2, h3, ?_, fun hEq => by have := habC.mpr hEq; omega⟩
      cases hoccc : occluded (boardDecodeOldN n (envAt t i))
          [(moveDecodeN n (envAt t i) 0).frm, (moveDecodeN n (envAt t i) 1).frm] (moveDecodeN n (envAt t i) 0)
      · rfl
      · rw [hoccaI.mpr hoccc] at h4; exact absurd h4 (by norm_num)
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨hbaC.mpr h1, h2, h3, ?_, ?_⟩
      · rcases hoccaB with hz | ho
        · exact hz
        · rw [hoccaI.mp ho] at h4; exact absurd h4 (by norm_num)
      · rcases habB with hz | ho
        · exact hz
        · exact absurd (habC.mp ho) h5

end Facts

/-! ## §5 — THE OCCLUSION-AWARE CATERPILLAR, AT COORDINATES `< n`.

At `NN = 2` the move graph was unconditional in the board: `occluded_false_n2` says a 2-line has no
strictly-interior cell, so no move is ever occluded and `nextOf_pair` could drop the check. At `n ≥ 3`
occlusion BITES, and each edge of the two-entry lookup exists only if ITS OWN move is not occluded.
`nextOf_pairN` states that unconditionally; the chain lemmas then thread the not-occluded facts the
carry (`surv ∧ nz ∧ ¬occ`) and the flow-through bit (`… ∧ ¬occ_other`) supply. -/

section Caterpillar

/-! The `m = 2` move graph and the occlusion-aware caterpillar are PURE REFERENCE SEMANTICS — no
descriptor, no trace — so they live with the reference, in `Dregg2.Games.Automatafl` §8d, next to the
conservation theorem that consumes them. They are re-exported here under their original names so
Leg R's assembly (and the `#assert_axioms` block below) reads unchanged. -/

export Dregg2.Games.Automatafl (nextOf_pairN chainDest_aN chainDest_bN)

end Caterpillar

/-! ## §6 — THE OCCLUDED-STAYER SEAM: why the capstone is NOT restated at `n ≥ 3`, and WHICH SIDE
IS NOW WRONG.

Assembling §1–§5 into `resolve_sat_imp_resolveMid` at arbitrary `n` FAILS, and not for want of
plumbing: at `n ≥ 3` the emitted descriptor and the reference DISAGREE on one configuration class,
which `NN = 2` could not express because occlusion never fires there.

THE CLASS.  Piece A's source is NON-VACUUM and its move is OCCLUDED, so A STAYS on its square,
keeping its particle and NOT vacating.  Piece B carries (`surv ∧ bnz ∧ ¬occ_b`) and its move TARGETS
`ma.frm`.  Then:

  * the REFERENCE (since defect #8's fix) has B's move FAIL TO EXECUTE — `followChain` sees that
    `ma.frm` is a carrying source with no edge out of it, so B stays on `mb.frm` and BOTH particles
    survive.  This is the author's rule: "designating a move to an occupied square is fine, it just
    fails to execute, it doesn't generate a conflict and shouldn't."
  * the EMITTED gate still places B's particle on `ma.frm` — `carry_a = 0` erases every A term from
    the cell polynomial and the surviving `carry_b · dst_b · particle_b` term forces
    `mid[ma.frm] = p_b` (`writeCell_forces_other`) — while `mid[mb.frm]` is written vacuum.  **The
    DESCRIPTOR destroys A's particle** (it overwrites the stayer) and, before the fix, so did the
    reference (it dropped B's instead: `journeys.find?` scanned in source order).

`occludedStayer_witness_n3` exhibits the configuration at `n = 3` with `p_a ≠ p_b`, computed by
`decide` on the reference semantics — so the class is NOT empty, and the disagreement is real.

WHAT THIS MEANS NOW.  The wound has MOVED SIDES.  It used to be a reference bug AND a descriptor
bug; the reference half is fixed (`Dregg2.Games.Automatafl.followChain`, defect #8) and is now
covered by a conservation theorem (`applyMoves_conserves_pieces`, with `buggy_refutes_conservation`
showing the pre-fix chain violates it).  `resolve_sat_imp_resolveMid` is therefore still NOT
restatable at arbitrary `n` — it is false on this class — but the FIX IS OWED BY THE DESCRIPTOR, not
by the reference:

  * `carry_b` must be forced to 0 (equivalently `dest_b := frm_b`) whenever B's landing square holds
    a NON-CARRYING piece — the emitted gate needs a "landing square is occupied by a non-mover" bit,
    computed from the OLD board's cell at the landing square and the other piece's carry bit, and
    ANDed into `carry`;
  * that same bit closes defect #8's LABELLED RESIDUAL on the reference side (a target held by a
    piece that never proposed a move), which is why the conservation theorem still carries the
    `hland` hypothesis.

At `NN = 2` the descriptor and the fixed reference STILL AGREE — the stay branch of `chainDest_a` is
empty at every call site of the frozen assembly (see the three `hmid` discharges in
`AutomataflResolveRefine` §C) — so `resolve_sat_imp_resolveMid` at `NN = 2` is UNCHANGED and no
golden was re-pinned.  Everything else this file lands — the indicator glue, the facts, the per-cell
gate and the occlusion-aware caterpillar — is the assembly that closes the moment the descriptor
grows that bit. -/

section Wound

/-- `occluded` reads only a move's endpoints, so two moves with the same endpoints are occluded
together. (This is what rules the mixed case out when both pieces share a source.) -/
theorem occluded_congr (bd : Board) (srcs : List Coord) (m m' : Move)
    (hf : m.frm = m'.frm) (ht : m.to = m'.to) :
    occluded bd srcs m = occluded bd srcs m' := by
  simp only [occluded, hf, ht]

/-- **THE REFERENCE SIDE OF THE WOUND.** An occluded piece STAYS on its square and keeps its
particle — even when the other piece lands there, because its journey is found first. -/
theorem stayer_keeps_cell (bd : Board) (ma mb : Move)
    (hx : ma.frm.x < bd.size) (hy : ma.frm.y < bd.size)
    (hne : ma.frm ≠ mb.frm)
    (hoa : occluded bd [ma.frm, mb.frm] ma = true)
    (hva : (bd.cellAt ma.frm).isVacuum = false) (hvb : (bd.cellAt mb.frm).isVacuum = false) :
    (applyMoves bd [ma, mb]).cellAt ma.frm = bd.cellAt ma.frm := by
  have hnext : nextOf bd [ma, mb] [ma.frm, mb.frm] ma.frm = none := by
    rw [nextOf_pairN, if_neg (by rintro ⟨-, q⟩; rw [hoa] at q; exact Bool.noConfusion q),
      if_neg (by rintro ⟨q, -⟩; exact hne q)]
  have hchain : followChain (nextOf bd [ma, mb] [ma.frm, mb.frm]) [ma.frm, mb.frm] ma.frm [] 3
      = ma.frm := by
    rw [followChain, hnext]
  rw [applyMoves_cell_TT bd ma mb ma.frm hx hy hva hvb, hchain, if_pos rfl]

/-- **THE CIRCUIT SIDE OF THE WOUND.** With `carry_a = 0` (the occluded piece contributes nothing)
and B landing on the cell, the emitted cell gate FORCES the other piece's particle there. This is
`cellAlgebra` at the indicator pattern `(A, B, C, D) = (0, 0, 0, 1)`. -/
theorem writeCell_forces_other {oldc midc pa pb : ℤ}
    (hold : 0 ≤ oldc ∧ oldc ≤ 3) (hmid : 0 ≤ midc ∧ midc ≤ 3)
    (hpa : 0 ≤ pa ∧ pa ≤ 3) (hpb : 0 ≤ pb ∧ pb ≤ 3)
    (hmod : midc ≡ (1 - 0 - 0 - 0 - 1 + 0 * 1 + 0 * 0 + 0 * 0 + 0 * 1) * oldc
              + 0 * pa + 1 * pb - 0 * 1 * pb [ZMOD 2013265921]) :
    midc = pb := by
  have hmidC : Canon midc := ⟨hmid.1, by have := hmid.2; omega⟩
  have h := cellAlgebra (A := 0) (B := 0) (C := 0) (D := 1) (oldc := oldc) (midc := midc)
    (pa := pa) (pb := pb) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
    (by norm_num) (by norm_num) hold hmidC hpa hpb hmod
  simpa using h

/-- The 3×3 witness board: A carries an attractor at `(0,0)` and wants `(0,2)`, but `(0,1)` holds a
non-source attractor, so A is OCCLUDED and stays. B carries a repulsor at `(1,0)` and lands exactly
on `(0,0)`. -/
def woundBoard : Board :=
  Dregg2.Games.Automatafl.mkBoard 3
    [(⟨0, 0⟩, Particle.attractor), (⟨1, 0⟩, Particle.repulsor), (⟨0, 1⟩, Particle.attractor)]
    ⟨2, 2⟩
def woundA : Move := Move.mk 0 ⟨0, 0⟩ ⟨0, 2⟩
def woundB : Move := Move.mk 1 ⟨1, 0⟩ ⟨0, 0⟩

/-- **THE CLASS IS NOT EMPTY, AT `n = 3`.** Both moves are valid, A is occluded and B is not, B lands
on A's source, and the REFERENCE keeps A's attractor there — while the emitted gate is forced (by
`writeCell_forces_other`) to write B's repulsor. Every clause `decide`d on the reference semantics. -/
theorem occludedStayer_witness_n3 :
    MoveValid woundBoard woundA ∧ MoveValid woundBoard woundB
      ∧ occluded woundBoard [woundA.frm, woundB.frm] woundA = true
      ∧ occluded woundBoard [woundA.frm, woundB.frm] woundB = false
      ∧ woundB.to = woundA.frm
      ∧ conflictResolve woundBoard [woundA, woundB] = [woundA, woundB]
      ∧ ¬ ((woundA.frm = woundB.frm ∧ woundA.to ≠ woundB.to)
            ∨ (woundA.to = woundB.to ∧ woundA.frm ≠ woundB.frm
               ∧ (woundBoard.cellAt woundA.frm).isVacuum = false
               ∧ (woundBoard.cellAt woundB.frm).isVacuum = false))
      ∧ (woundBoard.cellAt woundA.frm).isVacuum = false
      ∧ (woundBoard.cellAt woundB.frm).isVacuum = false
      ∧ (resolveMid woundBoard [woundA, woundB]).cellAt woundA.frm = Particle.attractor
      ∧ woundBoard.cellAt woundB.frm = Particle.repulsor
      ∧ Particle.attractor ≠ Particle.repulsor := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

end Wound

/-! ## §7 — Axiom hygiene. Every exported theorem, kernel-clean. -/

#assert_axioms oneHotHeadN_of_sat
#assert_axioms oneHot_pair_ind
#assert_axioms srcIndN_of_sat
#assert_axioms dstIndN_of_sat
#assert_axioms boardWindow_three
#assert_axioms occluded_swap
#assert_axioms moveCoordBounds
#assert_axioms forkCollideBoolN
#assert_axioms resolveFactsN_of_sat
#assert_axioms nextOf_pairN
#assert_axioms chainDest_aN
#assert_axioms chainDest_bN
#assert_axioms occluded_congr
#assert_axioms stayer_keeps_cell
#assert_axioms writeCell_forces_other
#assert_axioms occludedStayer_witness_n3

end Dregg2.Circuit.Emit.AutomataflResolveCapstone
