/-
# `AutomataflCommitRefine` — the SEAM-DISCHARGE bridge off `automataflCommitDesc n`

Step 2 of the n-generic board-commitment rebuild, and the mechanism that KILLS the whole-turn seam
residual. `AutomataflCommit.lean` (Step 1) emitted the base-4 pack family and proved the PURE-Lean
`pack_injective` / `pack_injective_modp` / `packBoard_injective`. Those live on abstract cell columns;
they say NOTHING yet about what a satisfying witness of the emitted descriptor actually publishes.

This file closes that gap over the EMITTED object `automataflCommitDesc n` (LEAN-AUTHORED AIR — the
pack gates, the alphabet range gates, and the packed-felt PI bindings are all `VmConstraint2` emitted
in `AutomataflCommit`; Rust only calls the emit path). It lands two theorems, both keyed on the
deployed acceptance predicate `Satisfied2`, in the exact extraction style of
`AutomataflStepRefine`/`AutomataflResolveRefine` (gate ⇐ `Satisfied2`, `.piBinding` ⇐ `Satisfied2`,
canonicality via `StepCanon`):

  (1) **`pack_pi_of_sat` — THE PACKED TRANSPORT.** On a satisfying, canonical trace, the committed
      public input `t.pub (16 + j)` is congruent mod `p` to `packBoard`'s `j`-th felt of the board
      DECODED off the cell columns. Derived from the emitted `packBoardConstraints` gate (the linear
      pack `packed_j − Σ 4^i·cell = 0`), the emitted `commitBoardConstraints` `.piBinding`
      (`packed_j = PI[16+j]`), and the emitted `boardRangeCells` alphabet gates (which make the
      `{0,1,2,3}` decode a THEOREM, not an assumption). The `mod-p`/no-wrap collapse rides
      `AutomataflCommit.packCell_nonneg`.

  (2) **`seam_of_equal_pis` — THE SEAM-DISCHARGE LEMMA.** Two satisfying, canonical witnesses whose
      committed PIs are EQUAL (`t_R.pub(16+j) = t_A.pub(16+j)` — exactly what the fold-level connect
      enforces when Leg R publishes the mid-commitment and Leg A consumes the old-commitment) have
      cell-wise-agreeing decoded boards. Proof: `pack_pi_of_sat` both sides ⇒ the two packed felt
      tuples agree mod `p` ⇒ `AutomataflCommit.pack_injective_modp` ⇒ cell-wise agreement.
      UNCONDITIONAL, PURE Lean, NO crypto floor — this is the reusable lemma that turns the
      whole-turn seam HYPOTHESIS into a discharged consequence of the fold PI-equality once the
      Leg R/A descriptors adopt this commitment (the coupled `descN` refactor; NOT done here).

Nothing is a vacuous `P → P`; the forge canary (`forge_rejected` + the `#guard`s) shows the transport
gate BITES. ADDITIVE: does not touch the capstones or the Step/Resolve descriptors.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Membership into the fold-generated
constraint list is discharged by `List.mem_map`/`List.mem_append_*` on the `n`-generic families
(no `decide` over a variable-length list), so the proofs are n-generic.
-/
import Dregg2.Circuit.Emit.AutomataflCommit
import Dregg2.Circuit.Emit.AutomataflStepRefine

namespace Dregg2.Circuit.Emit.AutomataflCommitRefine

open Dregg2.Circuit.Emit.AutomataflCommit
open Dregg2.Circuit.Emit.AutomataflStepRefine (Canon eq_of_modEq_canon StepCanon canon_loc codeToParticle)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Games.Automatafl (Board Coord Particle)
open Dregg2.Circuit (Assignment)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §0 — Pure list/eval glue for the emitted linear gate. -/

/-- The reference linear combination `Σ (coeff · loc[col])` of a gate's term list. -/
def linComb (terms : List (ℤ × Nat)) (a : Assignment) : ℤ :=
  (terms.map (fun t => t.1 * a t.2)).sum

/-- `sumExpr` (the left-folded gate sum) evaluates to the list-sum of the pieces. -/
theorem foldl_add_eval (a : Assignment) :
    ∀ (rest : List EmittedExpr) (init : EmittedExpr),
      (rest.foldl (fun acc x => .add acc x) init).eval a
        = init.eval a + (rest.map (fun e => e.eval a)).sum := by
  intro rest
  induction rest with
  | nil => intro init; simp
  | cons x xs ih =>
    intro init
    simp only [List.foldl_cons]
    rw [ih (.add init x)]
    simp only [EmittedExpr.eval, List.map_cons, List.sum_cons]
    ring

theorem sumExpr_eval (a : Assignment) (es : List EmittedExpr) :
    (sumExpr es).eval a = (es.map (fun e => e.eval a)).sum := by
  cases es with
  | nil => show (EmittedExpr.const 0).eval a = _; simp [EmittedExpr.eval]
  | cons e rest =>
    show (rest.foldl (fun acc x => EmittedExpr.add acc x) e).eval a = _
    rw [foldl_add_eval a rest e]
    simp only [List.map_cons, List.sum_cons]

/-- Each emitted `varTerm (c, col)` evaluates to `c · loc[col]`. ⚑ RE-PROVED for the canonical
renderer (2026-08-06): the coefficient is always written, so there is no `coeff == 1` case split. -/
theorem varTerm_eval (a : Assignment) (t : ℤ × Nat) : (varTerm t).eval a = t.1 * a t.2 := by
  obtain ⟨c, col⟩ := t
  show (EmittedExpr.mul (.const c) (.var col)).eval a = c * a col
  simp only [EmittedExpr.eval]

/-- The emitted gate body `sumExpr (terms.map varTerm)` evaluates to the reference `linComb`. -/
theorem sumExpr_varTerm_eval (a : Assignment) (terms : List (ℤ × Nat)) :
    (sumExpr (terms.map varTerm)).eval a = linComb terms a := by
  rw [sumExpr_eval]
  simp only [List.map_map, linComb]
  apply congrArg
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  exact varTerm_eval a t

/-- Dropping zero-coefficient terms (the `linGate` filter) does not change the linear combination. -/
theorem linComb_filter (a : Assignment) (terms : List (ℤ × Nat)) :
    linComb (terms.filter (fun t => t.1 != 0)) a = linComb terms a := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    rw [List.filter_cons]
    simp only [linComb] at ih
    by_cases h : (t.1 != 0) = true
    · rw [if_pos h]
      simp only [linComb, List.map_cons, List.sum_cons, ih]
    · rw [if_neg h]
      have h0 : t.1 = 0 := by simpa [bne_iff_ne] using h
      simp only [linComb, List.map_cons, List.sum_cons, ih, h0, zero_mul, zero_add]

/-- `linGate terms 0` is `.base (.gate (sumExpr (terms.map varTerm)))`. ⚑ The zero-coefficient FILTER
is gone with the flag day: the canonical renderer keeps every term and elides only a zero head
constant, so the term list here is the head's own. -/
theorem linGate_zero (terms : List (ℤ × Nat)) :
    linGate terms 0 = .base (.gate (sumExpr (terms.map varTerm))) := by
  simp only [linGate, Dregg2.Circuit.GateExpr.gHeadToExpr, Dregg2.Circuit.GateExpr.gHeadExprs,
    List.map_map, if_true, List.append_nil, sumExpr, Function.comp_def]
  rfl

/-- `prodGate terms 0` is the degree-`k` twin of `linGate_zero`. -/
theorem prodGate_zero (terms : List (ℤ × List Nat)) :
    prodGate terms 0 = .base (.gate (sumExpr (terms.map prodTerm))) := by
  simp only [prodGate, Dregg2.Circuit.GateExpr.gHeadToExpr, Dregg2.Circuit.GateExpr.gHeadExprs,
    if_true, List.append_nil, sumExpr, prodTerm]

/-- THE DEGREE-2 MASK-PIN BODY, evaluated. The gate `nax − ax − m·ox == 0` emitted by
`newAutoCoordCommitConstraints` has body `sumExpr [var nax, (−1)·var ax, (−1)·(var m · var ox)]`;
this computes its value as `loc nax − (loc ax + loc m · loc ox)`, the `gate_modEq_iff` shape. -/
theorem maskPinBody_eval (a : Assignment) (naxCol axCol mCol oxCol : Nat) :
    (sumExpr (([(1, [naxCol]), (-1, [axCol]), (-1, [mCol, oxCol])] : List (ℤ × List Nat)).map
        prodTerm)).eval a
      = a naxCol - (a axCol + a mCol * a oxCol) := by
  -- The coefficient list is CLOSED (`1, -1, -1`), so the map/fold all reduce; what is left is the
  -- literal emitted body, whose columns are the only variables. ⚑ The leading `1 · nax` term now
  -- renders `mul(const 1, var nax)` where the elided renderer wrote it bare.
  show (EmittedExpr.add (.add (.mul (.const 1) (.var naxCol)) (.mul (.const (-1)) (.var axCol)))
      (.mul (.const (-1)) (.mul (.var mCol) (.var oxCol)))).eval a
    = a naxCol - (a axCol + a mCol * a oxCol)
  simp only [EmittedExpr.eval]
  ring

/-- Signed base-4 negation glue. -/
theorem sum_map_neg {α : Type*} (l : List α) (g : α → ℤ) :
    (l.map (fun x => -(g x))).sum = -(l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- `filterMap (if P then some (g,h) else none)` mapped+summed = the `if…else 0` map+sum. -/
theorem sum_map_filterMap_if {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P]
    (g : α → ℤ) (h : α → Nat) (a : Assignment) :
    (((l.filterMap (fun x => if P x then some (g x, h x) else none)).map
        (fun t => t.1 * a t.2)).sum)
      = (l.map (fun x => if P x then g x * a (h x) else 0)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hp : P x
    · simp only [List.filterMap_cons, if_pos hp, List.map_cons, List.sum_cons, ih]
    · simp only [List.filterMap_cons, if_neg hp, List.map_cons, List.sum_cons, ih, zero_add]

/-- `horner4` of a length-15 `range`-map is the explicit weighted sum `Σ_{i<15} 4^i · f i`. The
felt width `CELLS_PER_FELT = 15` is concrete, so this closes by unfolding + `ring`. -/
theorem horner4_range15 (f : Nat → ℤ) :
    horner4 ((List.range 15).map f)
      = ((List.range 15).map (fun i => (4:ℤ) ^ i * f i)).sum := by
  show horner4 (([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] : List Nat).map f)
    = (([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] : List Nat).map (fun i => (4:ℤ) ^ i * f i)).sum
  simp only [List.map_cons, List.map_nil, horner4_cons, horner4_nil, List.sum_cons, List.sum_nil,
             pow_succ, pow_zero]
  ring

/-! ## §1 — The decoded board and the alphabet decode. -/

/-- Decode a row's cell columns AT AN ARBITRARY BASE into the reference `Board`: cell `(x,y)` is the
felt-decode of `loc[cellCol (y·n + x)]`. The `automaton` field is irrelevant to the pack (`boardCode`
reads only `cellAt`, which reads only `size`/`cells`), so it is a placeholder — a host descriptor
identifies its own decoded board with this one and supplies the coordinate separately. -/
def boardDecodeCommitAt (n : Nat) (cellCol : Nat → Nat) (e : VmRowEnv) : Board where
  size          := n
  automaton     := ⟨0, 0⟩
  cells         := fun c => codeToParticle (e.loc (cellCol (c.y * n + c.x)))
  useColumnRule := true

/-- Decode a row's cell columns `[0, n²)` into the reference `Board`: cell `(x,y)` is the felt-decode
of `loc[y·n + x]` (the working `n²`-cell representation `PACK_CELL c = c`). -/
def boardDecodeCommit (n : Nat) (e : VmRowEnv) : Board := boardDecodeCommitAt n PACK_CELL e

/-- `particleCode ∘ codeToParticle = id` on the alphabet `{0,1,2,3}` (the exact inverse the pack
needs to read the circuit cell back off the decoded board). -/
theorem particleCode_codeToParticle {z : ℤ} (h : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3) :
    particleCode (codeToParticle z) = z := by
  rcases h with h | h | h | h <;> subst h <;> decide

/-- **The circuit cell IS the decoded board cell** (on the alphabet). For an in-bounds index the
board-code of `boardDecodeCommit` is exactly the circuit column value; padding indices are `0`. This
is where the `boardRangeCells` alphabet gate pays off: `hmem` is supplied by `cell_mem_of_sat`. -/
theorem boardCode_decode_eqAt (n : Nat) (cellCol : Nat → Nat) (e : VmRowEnv) (idx : Nat)
    (hmem : idx < n * n → (e.loc (cellCol idx) = 0 ∨ e.loc (cellCol idx) = 1
      ∨ e.loc (cellCol idx) = 2 ∨ e.loc (cellCol idx) = 3)) :
    boardCode (boardDecodeCommitAt n cellCol e) n idx
      = if idx < n * n then e.loc (cellCol idx) else 0 := by
  unfold boardCode
  by_cases hlt : idx < n * n
  · rw [if_pos hlt, if_pos hlt]
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hlt
      · exact h
    have hxlt : idx % n < n := Nat.mod_lt _ hn
    have hylt : idx / n < n := Nat.div_lt_of_lt_mul hlt
    have hidx : (idx / n) * n + idx % n = idx := by rw [Nat.mul_comm]; exact Nat.div_add_mod idx n
    have hcell : (boardDecodeCommitAt n cellCol e).cellAt ⟨idx % n, idx / n⟩
        = codeToParticle (e.loc (cellCol idx)) := by
      simp only [Board.cellAt, boardDecodeCommitAt, hxlt, hylt, and_self, ↓reduceIte, hidx]
    rw [hcell, particleCode_codeToParticle (hmem hlt)]
  · rw [if_neg hlt, if_neg hlt]

/-- The `PACK_CELL c = c` instance (the standalone layout). -/
theorem boardCode_decode_eq (n : Nat) (e : VmRowEnv) (idx : Nat)
    (hmem : idx < n * n → (e.loc idx = 0 ∨ e.loc idx = 1 ∨ e.loc idx = 2 ∨ e.loc idx = 3)) :
    boardCode (boardDecodeCommit n e) n idx = if idx < n * n then e.loc idx else 0 :=
  boardCode_decode_eqAt n PACK_CELL e idx hmem

/-! ## §2 — Single-row gate / `.piBinding` extraction off `Satisfied2 (automataflCommitDesc n)`. -/

section Extract
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {n : Nat}

/-- A per-row `.gate` of the commitment descriptor vanishes mod `p` on a NON-LAST row. -/
theorem commit_gate (hsat : Satisfied2 hash (automataflCommitDesc n) minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {body : EmittedExpr}
    (hg : (.base (.gate body) : VmConstraint2) ∈ (automataflCommitDesc n).constraints) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hg
  have hlf : (i + 1 == t.rows.length) = false := by
    have : i + 1 ≠ t.rows.length := by omega
    simpa using this
  simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- **The alphabet gate DERIVES `{0,1,2,3}`.** A `boardRangeCells` member gate on a canonical trace
forces the in-bounds cell into the two-bit alphabet — so `pack_injective`'s precondition is a theorem
of the descriptor, not an assumption. Mirrors `mem3_of_gate` with one factor wider. -/
theorem cell_mem_of_sat (hsat : Satisfied2 hash (automataflCommitDesc n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (idx : Nat) (hidx : idx < n * n) :
    (envAt t 0).loc idx = 0 ∨ (envAt t 0).loc idx = 1 ∨ (envAt t 0).loc idx = 2
      ∨ (envAt t 0).loc idx = 3 := by
  have hmem : (.base (.gate (memberExpr (PACK_CELL idx) [0, 1, 2, 3])) : VmConstraint2)
      ∈ (automataflCommitDesc n).constraints := by
    show _ ∈ boardRangeCells n ++ packBoardConstraints n ++ commitBoardConstraints n
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨idx, List.mem_range.mpr hidx, rfl⟩
  have hg := commit_gate hsat 0 (by omega) hmem
  have e : (memberExpr (PACK_CELL idx) [0, 1, 2, 3]).eval (envAt t 0).loc
      = (envAt t 0).loc idx * ((envAt t 0).loc idx + -1) * ((envAt t 0).loc idx + -2)
        * ((envAt t 0).loc idx + -3) := rfl
  rw [e] at hg
  have hd : (2013265921 : ℤ) ∣
      ((((envAt t 0).loc idx + -0) * ((envAt t 0).loc idx + -1)) * ((envAt t 0).loc idx + -2))
        * ((envAt t 0).loc idx + -3) :=
    Int.modEq_zero_iff_dvd.mp (by simpa using hg)
  obtain ⟨hc0, hc1⟩ := canon_loc hc 0 idx
  rcases pPrimeInt.dvd_mul.mp hd with h1 | h1
  · rcases pPrimeInt.dvd_mul.mp h1 with h2 | h2
    · rcases pPrimeInt.dvd_mul.mp h2 with h3 | h3
      · obtain ⟨k, hk⟩ := h3; left; omega
      · obtain ⟨k, hk⟩ := h3; right; left; omega
    · obtain ⟨k, hk⟩ := h2; right; right; left; omega
  · obtain ⟨k, hk⟩ := h1; right; right; right; omega

/-- The emitted pack gate `packed_j − Σ 4^i·cell = 0` forces `linComb (packTerms n j) loc ≡ 0`. -/
theorem pack_gate_of_sat (hsat : Satisfied2 hash (automataflCommitDesc n) minit mfin maddrs t)
    (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    linComb (packTerms n j) (envAt t 0).loc ≡ 0 [ZMOD 2013265921] := by
  have hmem : (linGate (packTerms n j) 0) ∈ (automataflCommitDesc n).constraints := by
    show _ ∈ boardRangeCells n ++ packBoardConstraints n ++ commitBoardConstraints n
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  rw [linGate_zero] at hmem
  have hg := commit_gate hsat 0 (by omega) hmem
  rwa [sumExpr_varTerm_eval] at hg

/-- The emitted `commitBoardConstraints` `.piBinding` forces `packed_j ≡ PI[16+j]` on the first row. -/
theorem commit_pi_of_sat (hsat : Satisfied2 hash (automataflCommitDesc n) minit mfin maddrs t)
    (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    (envAt t 0).loc (PACK_FELT n j) ≡ (envAt t 0).pub (COMMIT_PI_BASE + j) [ZMOD 2013265921] := by
  have hmem : (.base (.piBinding VmRow.first (PACK_FELT n j) (COMMIT_PI_BASE + j)) : VmConstraint2)
      ∈ (automataflCommitDesc n).constraints := by
    show _ ∈ boardRangeCells n ++ packBoardConstraints n ++ commitBoardConstraints n
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  have hrc := hsat.rowConstraints 0 (by omega) _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hrc
  exact hrc rfl

end Extract

/-! ## §3 — The two per-felt integer identities that bridge the gate to `packCell`. -/

/-- The circuit-side weighted cell sum for felt `j` at an arbitrary cell base (the `if idx<n²`
padding mirrors `boardCode`). -/
def packCircSumAt (n j : Nat) (cellCol : Nat → Nat) (a : Assignment) : ℤ :=
  ((List.range 15).map (fun i =>
    if 15 * j + i < n * n then (4:ℤ) ^ i * a (cellCol (15 * j + i)) else 0)).sum

/-- The circuit-side weighted cell sum for felt `j` (the `if idx<n²` padding mirrors `boardCode`). -/
def packCircSum (n j : Nat) (a : Assignment) : ℤ := packCircSumAt n j PACK_CELL a

/-- **L1.** The emitted pack gate value `= loc[felt_j] − packCircSum`, at any cell/felt base. -/
theorem linComb_packTermsAt (n j : Nat) (cellCol feltCol : Nat → Nat) (a : Assignment) :
    linComb (packTermsAt n j cellCol feltCol) a = a (feltCol j) - packCircSumAt n j cellCol a := by
  have h1 : (((List.range 15).filterMap (fun i =>
        if 15 * j + i < n * n then some (-(4:ℤ) ^ i, cellCol (15 * j + i)) else none)).map
        (fun t => t.1 * a t.2)).sum = -(packCircSumAt n j cellCol a) := by
    rw [sum_map_filterMap_if (List.range 15) (fun i => 15 * j + i < n * n)
      (fun i => -(4:ℤ) ^ i) (fun i => cellCol (15 * j + i)) a]
    rw [show (fun i => if 15 * j + i < n * n
              then (-(4:ℤ) ^ i) * a (cellCol (15 * j + i)) else 0)
          = (fun i => -(if 15 * j + i < n * n
              then (4:ℤ) ^ i * a (cellCol (15 * j + i)) else 0)) from ?_]
    · rw [sum_map_neg]; rfl
    · funext i; split_ifs <;> ring
  simp only [linComb, packTermsAt, List.map_cons, List.sum_cons, one_mul]
  rw [h1]; ring

/-- **L1**, standalone-layout instance. -/
theorem linComb_packTerms (n j : Nat) (a : Assignment) :
    linComb (packTerms n j) a = a (PACK_FELT n j) - packCircSum n j a :=
  linComb_packTermsAt n j PACK_CELL (PACK_FELT n) a

/-- **L2.** `packCell` of the decoded board `= packCircSum` (needs the alphabet membership), at any
cell base. -/
theorem packCell_boardCode_eqAt (n j : Nat) (cellCol : Nat → Nat) (e : VmRowEnv)
    (hcells : ∀ idx, idx < n * n →
      (e.loc (cellCol idx) = 0 ∨ e.loc (cellCol idx) = 1 ∨ e.loc (cellCol idx) = 2
        ∨ e.loc (cellCol idx) = 3)) :
    packCell (boardCode (boardDecodeCommitAt n cellCol e) n) j = packCircSumAt n j cellCol e.loc := by
  unfold packCell
  rw [horner4_range15 (fun i => boardCode (boardDecodeCommitAt n cellCol e) n (15 * j + i))]
  simp only [packCircSumAt]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  rw [boardCode_decode_eqAt n cellCol e (15 * j + i) (fun hh => hcells (15 * j + i) hh)]
  split_ifs <;> ring

/-- **L2**, standalone-layout instance. -/
theorem packCell_boardCode_eq (n j : Nat) (e : VmRowEnv)
    (hcells : ∀ idx, idx < n * n →
      (e.loc idx = 0 ∨ e.loc idx = 1 ∨ e.loc idx = 2 ∨ e.loc idx = 3)) :
    packCell (boardCode (boardDecodeCommit n e) n) j = packCircSum n j e.loc :=
  packCell_boardCode_eqAt n j PACK_CELL e hcells

/-! ## §4 — (1) THE PACKED TRANSPORT and (2) THE SEAM-DISCHARGE LEMMA. -/

section Transport
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {n : Nat}

/-! ### §4.0 — THE HOST-DESCRIPTOR FORMS. Everything below takes the descriptor `D` as a variable
and the three commitment ingredients (alphabet, pack gate, `.piBinding`) as MEMBERSHIP hypotheses,
so Leg A and Leg R instantiate them against their OWN emitted constraint lists — no re-derivation,
no second copy of the base-4 argument. -/

section Host
variable {D : EffectVmDescriptor2}

/-- A per-row `.gate` of ANY descriptor vanishes mod `p` on a NON-LAST row. -/
theorem gate_of_mem (hsat : Satisfied2 hash D minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {body : EmittedExpr}
    (hg : (.base (.gate body) : VmConstraint2) ∈ D.constraints) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hg
  have hlf : (i + 1 == t.rows.length) = false := by
    have : i + 1 ≠ t.rows.length := by omega
    simpa using this
  simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- A `.piBinding VmRow.first` of ANY descriptor forces `loc[col] ≡ pub[pi]` on the first row. -/
theorem piFirst_of_mem (hsat : Satisfied2 hash D minit mfin maddrs t)
    (hlen : 1 < t.rows.length) (col pi : Nat)
    (hg : (.base (.piBinding VmRow.first col pi) : VmConstraint2) ∈ D.constraints) :
    (envAt t 0).loc col ≡ t.pub pi [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints 0 (by omega) _ hg
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hrc
  exact hrc rfl

/-- **`pack_pi_of_mem` — THE PACKED TRANSPORT, host form.** For any descriptor that emits the
re-pointed pack gate for felt `j` and the matching `.piBinding`, and whose board columns at `cellCol`
are alphabet-constrained, the published `PI[piBase+j]` IS (mod `p`) the `j`-th packed felt of the
board decoded off those very columns. NO hash, NO permutation-soundness hypothesis: the whole
commitment is one degree-1 gate plus a boundary binding. -/
theorem pack_pi_of_mem (hsat : Satisfied2 hash D minit mfin maddrs t)
    (hlen : 1 < t.rows.length) (cellCol feltCol : Nat → Nat) (piBase j : Nat)
    (halpha : ∀ idx, idx < n * n →
      ((envAt t 0).loc (cellCol idx) = 0 ∨ (envAt t 0).loc (cellCol idx) = 1
        ∨ (envAt t 0).loc (cellCol idx) = 2 ∨ (envAt t 0).loc (cellCol idx) = 3))
    (hpack : linGate (packTermsAt n j cellCol feltCol) 0 ∈ D.constraints)
    (hpi : (.base (.piBinding VmRow.first (feltCol j) (piBase + j)) : VmConstraint2)
      ∈ D.constraints) :
    t.pub (piBase + j)
      ≡ packCell (boardCode (boardDecodeCommitAt n cellCol (envAt t 0)) n) j [ZMOD 2013265921] := by
  rw [linGate_zero] at hpack
  have hgate : linComb (packTermsAt n j cellCol feltCol) (envAt t 0).loc ≡ 0 [ZMOD 2013265921] := by
    have hg := gate_of_mem hsat 0 (by omega) hpack
    rwa [sumExpr_varTerm_eval] at hg
  rw [linComb_packTermsAt, ← packCell_boardCode_eqAt n j cellCol (envAt t 0) halpha] at hgate
  have hfelt : (envAt t 0).loc (feltCol j)
      ≡ packCell (boardCode (boardDecodeCommitAt n cellCol (envAt t 0)) n) j [ZMOD 2013265921] :=
    (gate_modEq_iff rfl).mp hgate
  exact ((piFirst_of_mem hsat hlen (feltCol j) (piBase + j) hpi).symm).trans hfelt

/-- **`maskPin_gate_of_mem` — the DEGREE-2 mask-pin transport, host form.** A gate
`naxCol − axCol − mCol·oxCol == 0` in ANY descriptor forces
`loc[naxCol] ≡ loc[axCol] + loc[mCol]·loc[oxCol]` on the first row. This is the engine of the
NEW-automaton-coordinate transport: on a moved step (`m = 1`) it reads `ax + ox`, on a BLOCKED step
(`m = 0`) it reads `ax` — matching the reference `automatonStep` on BOTH branches, which the degree-1
`nax = ax + ox` pin did not. -/
theorem maskPin_gate_of_mem (hsat : Satisfied2 hash D minit mfin maddrs t)
    (hlen : 1 < t.rows.length) (naxCol axCol mCol oxCol : Nat)
    (hg : prodGate [(1, [naxCol]), (-1, [axCol]), (-1, [mCol, oxCol])] 0 ∈ D.constraints) :
    (envAt t 0).loc naxCol
      ≡ (envAt t 0).loc axCol + (envAt t 0).loc mCol * (envAt t 0).loc oxCol
        [ZMOD 2013265921] := by
  rw [prodGate_zero] at hg
  have hgate := gate_of_mem hsat 0 (by omega) hg
  exact (gate_modEq_iff (maskPinBody_eval (envAt t 0).loc naxCol axCol mCol oxCol)).mp hgate

end Host

/-- **`pack_pi_of_sat` — (1) THE PACKED TRANSPORT.** On a satisfying, canonical trace the committed
public input `PI[16+j]` equals (mod `p`) the `j`-th packed felt of the board decoded off the cell
columns. Every ingredient is extracted from the emitted `automataflCommitDesc n` — the pack gate, the
`.piBinding`, and the alphabet gates — none assumed. -/
theorem pack_pi_of_sat (hsat : Satisfied2 hash (automataflCommitDesc n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    t.pub (COMMIT_PI_BASE + j)
      ≡ packCell (boardCode (boardDecodeCommit n (envAt t 0)) n) j [ZMOD 2013265921] := by
  have hcells : ∀ idx, idx < n * n →
      ((envAt t 0).loc idx = 0 ∨ (envAt t 0).loc idx = 1 ∨ (envAt t 0).loc idx = 2
        ∨ (envAt t 0).loc idx = 3) :=
    fun idx hidx => cell_mem_of_sat hsat hc hlen idx hidx
  have hgate : linComb (packTerms n j) (envAt t 0).loc ≡ 0 [ZMOD 2013265921] :=
    pack_gate_of_sat hsat hlen j hj
  rw [linComb_packTerms, ← packCell_boardCode_eq n j (envAt t 0) hcells] at hgate
  have hfelt : (envAt t 0).loc (PACK_FELT n j)
      ≡ packCell (boardCode (boardDecodeCommit n (envAt t 0)) n) j [ZMOD 2013265921] :=
    (gate_modEq_iff rfl).mp hgate
  have hpi := commit_pi_of_sat hsat hlen j hj
  exact (hpi.symm).trans hfelt

/-- **`forge_rejected` — the transport BITES.** No satisfying, canonical witness can publish a
committed PI that is NOT the genuine packed board felt: the pack gate + `.piBinding` force
`PI[16+j] ≡ packCell(…) [ZMOD p]`, so a non-congruent (forged) PI is refused. The contrapositive of
`pack_pi_of_sat`. -/
theorem forge_rejected (hsat : Satisfied2 hash (automataflCommitDesc n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n)
    (hforge : ¬ (t.pub (COMMIT_PI_BASE + j)
      ≡ packCell (boardCode (boardDecodeCommit n (envAt t 0)) n) j [ZMOD 2013265921])) :
    False :=
  hforge (pack_pi_of_sat hsat hc hlen j hj)

end Transport

/-- **`seam_of_equal_pis` — (2) THE SEAM-DISCHARGE LEMMA (unconditional, pure Lean, no crypto).**
Two satisfying, canonical witnesses of `automataflCommitDesc n` whose committed PIs agree publish
cell-wise-agreeing decoded boards. This is the reusable object: once Leg R and Leg A adopt this
commitment, the fold's PI-equality (`t_R.pub(16+j) = t_A.pub(16+j)`) DISCHARGES the whole-turn seam
"the two decoded boards agree cell-wise" as a theorem — via `pack_pi_of_sat` on both sides feeding
`AutomataflCommit.pack_injective_modp`. -/
theorem seam_of_pack_congr {n : Nat} (b1 b2 : Board) (v1 v2 : Nat → ℤ)
    (h1 : ∀ j, j < feltCount n → v1 j ≡ packCell (boardCode b1 n) j [ZMOD 2013265921])
    (h2 : ∀ j, j < feltCount n → v2 j ≡ packCell (boardCode b2 n) j [ZMOD 2013265921])
    (heq : ∀ j, j < feltCount n → v1 j = v2 j) :
    ∀ x y : Nat, x < n → y < n → b1.cellAt ⟨x, y⟩ = b2.cellAt ⟨x, y⟩ := by
  have hcodes : ∀ i, i < 15 * feltCount n → boardCode b1 n i = boardCode b2 n i := by
    refine pack_injective_modp (boardCode b1 n) (boardCode b2 n) (feltCount n)
      (fun i _ => boardCode_mem _ n i) (fun i _ => boardCode_mem _ n i) ?_
    intro j hj
    exact ((h1 j hj).symm.trans ((heq j hj) ▸ h2 j hj))
  intro x y hx hy
  have hlt : y * n + x < n * n :=
    calc y * n + x < y * n + n := by omega
      _ = (y + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  have hidx : y * n + x < 15 * feltCount n := lt_of_lt_of_le hlt (sq_le_feltCount n)
  have hcc := hcodes (y * n + x) hidx
  rw [boardCode_inbounds _ n x y hx hy, boardCode_inbounds _ n x y hx hy] at hcc
  exact particleCode_inj hcc

/-- The standalone-descriptor instance of the seam discharge. -/
theorem seam_of_equal_pis {hash : List ℤ → ℤ} {n : Nat}
    {minitR : ℤ → ℤ} {mfinR : ℤ → ℤ × Nat} {maddrsR : List ℤ} {tR : VmTrace}
    {minitA : ℤ → ℤ} {mfinA : ℤ → ℤ × Nat} {maddrsA : List ℤ} {tA : VmTrace}
    (hsatR : Satisfied2 hash (automataflCommitDesc n) minitR mfinR maddrsR tR)
    (hcR : StepCanon tR) (hlenR : 1 < tR.rows.length)
    (hsatA : Satisfied2 hash (automataflCommitDesc n) minitA mfinA maddrsA tA)
    (hcA : StepCanon tA) (hlenA : 1 < tA.rows.length)
    (hpi : ∀ j, j < feltCount n →
      tR.pub (COMMIT_PI_BASE + j) = tA.pub (COMMIT_PI_BASE + j)) :
    ∀ x y : Nat, x < n → y < n →
      (boardDecodeCommit n (envAt tR 0)).cellAt ⟨x, y⟩
        = (boardDecodeCommit n (envAt tA 0)).cellAt ⟨x, y⟩ :=
  seam_of_pack_congr (n := n) _ _
    (fun j => tR.pub (COMMIT_PI_BASE + j)) (fun j => tA.pub (COMMIT_PI_BASE + j))
    (fun j hj => pack_pi_of_sat hsatR hcR hlenR j hj)
    (fun j hj => pack_pi_of_sat hsatA hcA hlenA j hj)
    (fun j hj => hpi j hj)

/-! ## §5 — Non-vacuity: the transport gate is REAL and two-sided (`#guard`). -/

/-- Concrete `n = 2` genuine row: cells `[REP,ATT,AUTO,VAC] = [1,2,3,0]` at columns `0..3`, the packed
felt at column `PACK_FELT 2 0 = 4` set to the genuine pack `1 + 4·2 + 16·3 + 64·0 = 57`. -/
def demoLoc2 : Assignment := fun c =>
  if c = 0 then 1 else if c = 1 then 2 else if c = 2 then 3 else if c = 4 then 57 else 0
/-- Same row, but the committed felt is FORGED to `99 ≠ 57`. -/
def demoLoc2Forge : Assignment := fun c =>
  if c = 0 then 1 else if c = 1 then 2 else if c = 2 then 3 else if c = 4 then 99 else 0
/-- Env carrying the genuine row (nxt/pub unused by the pack gate). -/
def demoEnv2 : VmRowEnv := ⟨demoLoc2, demoLoc2, demoLoc2, fun _ => 0⟩

-- The emitted pack gate on the GENUINE row vanishes (the transport is satisfiable) …
#guard (sumExpr (((packTerms 2 0).filter (fun t => t.1 != 0)).map varTerm)).eval demoLoc2 = 0
-- … and on the FORGED committed felt it does NOT (the transport gate BITES).
#guard (sumExpr (((packTerms 2 0).filter (fun t => t.1 != 0)).map varTerm)).eval demoLoc2Forge ≠ 0
-- The gate value IS the reference linear combination on both rows.
#guard linComb (packTerms 2 0) demoLoc2 = 0
#guard linComb (packTerms 2 0) demoLoc2Forge = 42
-- The genuine committed felt (57) IS the packed board felt the transport targets; the forge (99) is not.
#guard packCell (boardCode (boardDecodeCommit 2 demoEnv2) 2) 0 = 57
#guard packCell (boardCode (boardDecodeCommit 2 demoEnv2) 2) 0 ≠ 99
#guard packCircSum 2 0 demoLoc2 = 57
-- The decoded board reads the genuine cells back.
#guard (boardDecodeCommit 2 demoEnv2).cellAt ⟨0, 0⟩ = Particle.repulsor
#guard (boardDecodeCommit 2 demoEnv2).cellAt ⟨1, 0⟩ = Particle.attractor
#guard (boardDecodeCommit 2 demoEnv2).cellAt ⟨0, 1⟩ = Particle.automaton

/-! ## §6 — LEG A: the packed commitment transported off `automataflStepDescN n`.

The Leg-A descriptor adopted this commitment (`AutomataflStepEmit.commitBoardsConstraints`), so its
published PIs are now packed board felts and NOT `MerkleHash8` digests. Everything below is
`n`-GENERIC: the three ingredients (alphabet gate, pack gate, `.piBinding`) are all folds over
`List.range`, so membership is `mem_map`/`mem_range`/`mem_append`, never `decide` over a fixed list.

WHAT WAS DROPPED WITH THE MERKLE LEG: the old `oldRoot_pi_of_sat` / `newRoot_pi_of_sat` took a
`ChipTableSoundN permOut (t.tf .poseidon2)` hypothesis — a wide-soundness ASSUMPTION about the
prover-supplied Poseidon2 chip table. These take none. -/

section LegA
open Dregg2.Circuit.Emit.AutomataflStepEmit
open Dregg2.Circuit.Emit.AutomataflStepRefine
  (mem_fe_boardRange mem_constraintsN_of_commit boardRange_old boardRange_new mem4_of_gate)

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace} {n : Nat}

/-- The OLD board cells of a satisfying Leg-A trace are in the particle alphabet — off the emitted
`NGen.boardRangeConstraints`, `n`-generically. -/
theorem astepN_oldAlpha (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (c : Nat) (hcK : c < n * n) :
    ((envAt t 0).loc (NGen.old n c) = 0 ∨ (envAt t 0).loc (NGen.old n c) = 1
      ∨ (envAt t 0).loc (NGen.old n c) = 2 ∨ (envAt t 0).loc (NGen.old n c) = 3) :=
  mem4_of_gate (gate_of_mem hsat 0 (by omega) (mem_fe_boardRange (boardRange_old hcK)))
    (canon_loc hc 0 _)

/-- The CLAIMED NEW board cells likewise. -/
theorem astepN_newAlpha (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (c : Nat) (hcK : c < n * n) :
    ((envAt t 0).loc (NGen.new n c) = 0 ∨ (envAt t 0).loc (NGen.new n c) = 1
      ∨ (envAt t 0).loc (NGen.new n c) = 2 ∨ (envAt t 0).loc (NGen.new n c) = 3) :=
  mem4_of_gate (gate_of_mem hsat 0 (by omega) (mem_fe_boardRange (boardRange_new hcK)))
    (canon_loc hc 0 _)

/-- The OLD pack gate is a member of the emitted list. -/
theorem astepN_oldPack_mem (j : Nat) (hj : j < feltCount n) :
    linGate (packTermsAt n j (NGen.old n) (packOldFelt n)) 0
      ∈ (automataflStepDescN n).constraints := by
  refine mem_constraintsN_of_commit ?_
  unfold commitBoardsConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))))

/-- The NEW pack gate is a member of the emitted list. -/
theorem astepN_newPack_mem (j : Nat) (hj : j < feltCount n) :
    linGate (packTermsAt n j (NGen.new n) (packNewFelt n)) 0
      ∈ (automataflStepDescN n).constraints := by
  refine mem_constraintsN_of_commit ?_
  unfold commitBoardsConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))))

/-- The OLD packed-felt `.piBinding` is a member of the emitted list. -/
theorem astepN_oldPi_mem (j : Nat) (hj : j < feltCount n) :
    (.base (.piBinding VmRow.first (packOldFelt n j) (16 + j)) : VmConstraint2)
      ∈ (automataflStepDescN n).constraints := by
  refine mem_constraintsN_of_commit ?_
  unfold commitBoardsConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))))

/-- The NEW packed-felt `.piBinding` is a member of the emitted list. -/
theorem astepN_newPi_mem (j : Nat) (hj : j < feltCount n) :
    (.base (.piBinding VmRow.first (packNewFelt n j) (16 + feltCount n + j)) : VmConstraint2)
      ∈ (automataflStepDescN n).constraints := by
  refine mem_constraintsN_of_commit ?_
  unfold commitBoardsConstraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))

/-- The OLD automaton-coordinate `.piBinding`s are members of the emitted list. The NEW-automaton
family is appended AFTER the old-auto pair, so each reaches the old pair through one extra
`mem_append_left`. -/
theorem astepN_autoX_mem :
    (.base (.piBinding VmRow.first (NGen.AX n) (AUTO_PI_BASE n)) : VmConstraint2)
      ∈ (automataflStepDescN n).constraints := by
  refine mem_constraintsN_of_commit ?_
  unfold commitBoardsConstraints
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl)))

theorem astepN_autoY_mem :
    (.base (.piBinding VmRow.first (NGen.AY n) (AUTO_PI_BASE n + 1)) : VmConstraint2)
      ∈ (automataflStepDescN n).constraints := by
  refine mem_constraintsN_of_commit ?_
  unfold commitBoardsConstraints
  exact List.mem_append_left _
    (List.mem_append_right _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

/-- The NEW-automaton pin GATES are members of the emitted list (the appended new-auto family, last).
`nax − ax − m·ox == 0` is element 0, `nay − ay − m·oy == 0` element 1. -/
theorem astepN_newAutoX_pin_mem :
    prodGate [(1, [NAXcol n]), (-1, [NGen.AX n]), (-1, [maskCol n, offXCol n])] 0
      ∈ (automataflStepDescN n).constraints := by
  refine mem_constraintsN_of_commit ?_
  unfold commitBoardsConstraints
  exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))

theorem astepN_newAutoY_pin_mem :
    prodGate [(1, [NAYcol n]), (-1, [NGen.AY n]), (-1, [maskCol n, offYCol n])] 0
      ∈ (automataflStepDescN n).constraints := by
  refine mem_constraintsN_of_commit ?_
  unfold commitBoardsConstraints
  exact List.mem_append_right _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))

/-- The NEW-automaton-coordinate `.piBinding`s (`nax → PI[AUTO_PI_BASE+2]`, `nay → PI[+3]`) are
members of the emitted list — elements 2 and 3 of the appended new-auto family. -/
theorem astepN_newAutoX_pi_mem :
    (.base (.piBinding VmRow.first (NAXcol n) (AUTO_PI_BASE n + 2)) : VmConstraint2)
      ∈ (automataflStepDescN n).constraints := by
  refine mem_constraintsN_of_commit ?_
  unfold commitBoardsConstraints
  exact List.mem_append_right _
    (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))

theorem astepN_newAutoY_pi_mem :
    (.base (.piBinding VmRow.first (NAYcol n) (AUTO_PI_BASE n + 3)) : VmConstraint2)
      ∈ (automataflStepDescN n).constraints := by
  refine mem_constraintsN_of_commit ?_
  unfold commitBoardsConstraints
  exact List.mem_append_right _
    (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
      (List.mem_singleton.mpr rfl)))))))

/-- **`astep_oldPack_pi_of_sat` — LEG A's OLD-board commitment transport.** `PI[16+j]` IS the `j`-th
packed felt of the board decoded off Leg A's `old` columns. No hash, no chip-soundness hypothesis. -/
theorem astep_oldPack_pi_of_sat (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    t.pub (16 + j)
      ≡ packCell (boardCode (boardDecodeCommitAt n (NGen.old n) (envAt t 0)) n) j
        [ZMOD 2013265921] :=
  pack_pi_of_mem hsat hlen (NGen.old n) (packOldFelt n) 16 j
    (fun idx hidx => astepN_oldAlpha hsat hc hlen idx hidx)
    (astepN_oldPack_mem j hj) (astepN_oldPi_mem j hj)

/-- **`astep_newPack_pi_of_sat` — LEG A's NEW-board commitment transport.** `PI[16+fc+j]` IS the
`j`-th packed felt of the board decoded off Leg A's `new` columns. -/
theorem astep_newPack_pi_of_sat (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    t.pub (16 + feltCount n + j)
      ≡ packCell (boardCode (boardDecodeCommitAt n (NGen.new n) (envAt t 0)) n) j
        [ZMOD 2013265921] :=
  pack_pi_of_mem hsat hlen (NGen.new n) (packNewFelt n) (16 + feltCount n) j
    (fun idx hidx => astepN_newAlpha hsat hc hlen idx hidx)
    (astepN_newPack_mem j hj) (astepN_newPi_mem j hj)

/-- The published automaton coordinate IS the witnessed `(AX, AY)` (canonical, so equality on ℤ). -/
theorem astep_autoX_pi_of_sat (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hlen : 1 < t.rows.length) :
    (envAt t 0).loc (NGen.AX n) ≡ t.pub (AUTO_PI_BASE n) [ZMOD 2013265921] :=
  piFirst_of_mem hsat hlen _ _ astepN_autoX_mem

theorem astep_autoY_pi_of_sat (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hlen : 1 < t.rows.length) :
    (envAt t 0).loc (NGen.AY n) ≡ t.pub (AUTO_PI_BASE n + 1) [ZMOD 2013265921] :=
  piFirst_of_mem hsat hlen _ _ astepN_autoY_mem

/-! ### The NEW automaton coordinate `(ax + m·ox, ay + m·oy)` — the fold's `auto_out`.

Mirror of `astep_autoX_pi_of_sat` / `astep_autoY_pi_of_sat` for the appended NEW-auto PIs, plus the
DEGREE-2 mask-pin fact `nax = ax + m·ox`. The `m` factor makes the pinned column agree with the
reference `automatonStep` on BOTH branches — `ax + ox` when the mask fires, `ax` when the step is
BLOCKED. The full-semantics statement (`PI = (automatonStepCfg …).automaton.x`) is
`AutomataflTurnCapstone.astep_newAuto_pi_of_sat`, which needs the step capstone and so lives one
level up; what THIS file exports is the column-level fact the capstone consumes. -/

/-- The NEW-auto x `.piBinding` transport: `loc(nax) ≡ PI[AUTO_PI_BASE+2]`. -/
theorem astep_newAutoX_pi_of_sat
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hlen : 1 < t.rows.length) :
    (envAt t 0).loc (NAXcol n) ≡ t.pub (AUTO_PI_BASE n + 2) [ZMOD 2013265921] :=
  piFirst_of_mem hsat hlen _ _ astepN_newAutoX_pi_mem

/-- The NEW-auto y `.piBinding` transport: `loc(nay) ≡ PI[AUTO_PI_BASE+3]`. -/
theorem astep_newAutoY_pi_of_sat
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hlen : 1 < t.rows.length) :
    (envAt t 0).loc (NAYcol n) ≡ t.pub (AUTO_PI_BASE n + 3) [ZMOD 2013265921] :=
  piFirst_of_mem hsat hlen _ _ astepN_newAutoY_pi_mem

/-- **`astep_newAuto_pin_of_sat` — LEG A's NEW-automaton-coordinate transport, at the COLUMN level.**
The published `PI[AUTO_PI_BASE+2]`/`[+3]` ARE (mod `p`) the MASK-GATED applied-offset coordinate
`(ax + m·ox, ay + m·oy)` read off Leg A's OWN auto (`AX`/`AY`), chosen-offset (`offXCol`/`offYCol`)
and move-mask (`maskCol`) columns — the value the fold OUT window exposes as `auto_out`. Engine: the
degree-2 pin gate `nax − ax − m·ox == 0` (`maskPin_gate_of_mem`) plus the boundary `.piBinding`. NO
hash, NO chip-soundness. `AutomataflTurnCapstone.astep_newAuto_pi_of_sat` upgrades this to the FULL
`automatonStepCfg` semantics by discharging `m` against the reference guard. -/
theorem astep_newAuto_pin_of_sat
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hlen : 1 < t.rows.length) :
    t.pub (AUTO_PI_BASE n + 2)
        ≡ (envAt t 0).loc (NGen.AX n)
          + (envAt t 0).loc (maskCol n) * (envAt t 0).loc (offXCol n) [ZMOD 2013265921]
    ∧ t.pub (AUTO_PI_BASE n + 3)
        ≡ (envAt t 0).loc (NGen.AY n)
          + (envAt t 0).loc (maskCol n) * (envAt t 0).loc (offYCol n) [ZMOD 2013265921] :=
  ⟨(astep_newAutoX_pi_of_sat hsat hlen).symm.trans
      (maskPin_gate_of_mem hsat hlen _ _ _ _ astepN_newAutoX_pin_mem),
   (astep_newAutoY_pi_of_sat hsat hlen).symm.trans
      (maskPin_gate_of_mem hsat hlen _ _ _ _ astepN_newAutoY_pin_mem)⟩

/-- **`astep_forge_rejected`** — the Leg-A transport BITES: a satisfying canonical witness CANNOT
publish an OLD-board commitment that is not the genuine pack of its own cells. -/
theorem astep_forge_rejected (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n)
    (hforge : ¬ (t.pub (16 + j)
      ≡ packCell (boardCode (boardDecodeCommitAt n (NGen.old n) (envAt t 0)) n) j
        [ZMOD 2013265921])) : False :=
  hforge (astep_oldPack_pi_of_sat hsat hc hlen j hj)

/-- Leg A's own `boardDecode` and the commitment decode at the `old` base are THE SAME BOARD on
every in-bounds cell (they read the same columns through the same alphabet decode). -/
theorem astep_boardDecode_cellAt (e : VmRowEnv) (x y : Nat) (hx : x < NN) (hy : y < NN) :
    (Dregg2.Circuit.Emit.AutomataflStepRefine.boardDecode e).cellAt ⟨x, y⟩
      = (boardDecodeCommitAt NN (NGen.old NN) e).cellAt ⟨x, y⟩ := by
  simp only [Board.cellAt, Dregg2.Circuit.Emit.AutomataflStepRefine.boardDecode,
    boardDecodeCommitAt, NGen.old, AutomataflStepEmit.old, hx, hy, and_self, ↓reduceIte]

end LegA

/-! ## §7 — Axiom hygiene. -/

#assert_axioms sumExpr_varTerm_eval
#assert_axioms linComb_filter
#assert_axioms horner4_range15
#assert_axioms boardCode_decode_eq
#assert_axioms cell_mem_of_sat
#assert_axioms pack_gate_of_sat
#assert_axioms commit_pi_of_sat
#assert_axioms linComb_packTerms
#assert_axioms packCell_boardCode_eq
#assert_axioms pack_pi_of_sat
#assert_axioms forge_rejected
#assert_axioms seam_of_pack_congr
#assert_axioms seam_of_equal_pis
-- the host-descriptor forms + the LEG A instances
#assert_axioms gate_of_mem
#assert_axioms piFirst_of_mem
#assert_axioms pack_pi_of_mem
#assert_axioms maskPinBody_eval
#assert_axioms maskPin_gate_of_mem
#assert_axioms astepN_oldAlpha
#assert_axioms astepN_newAlpha
#assert_axioms astep_oldPack_pi_of_sat
#assert_axioms astep_newPack_pi_of_sat
#assert_axioms astep_autoX_pi_of_sat
#assert_axioms astep_autoY_pi_of_sat
#assert_axioms astep_newAutoX_pi_of_sat
#assert_axioms astep_newAutoY_pi_of_sat
#assert_axioms astep_newAuto_pin_of_sat
#assert_axioms astep_forge_rejected
#assert_axioms astep_boardDecode_cellAt

end Dregg2.Circuit.Emit.AutomataflCommitRefine
