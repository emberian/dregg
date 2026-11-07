/-
# `Dregg2.Crypto.MlDsaHintCodec` — the FIPS 204 hint-codec round-trip `HintBitUnpack ∘ HintBitPack = id`,
∀ well-formed hints, `#assert_axioms`-clean.

This closes the ONE named residual of `CodecRoundTrip.sigDecode_sigEncode` (its `hhint` hypothesis): the
`hintDecode (hintEncode hs) 0 = some hs` round-trip. It is pure `Array`/`Nat`/`List` bookkeeping over the
per-poly set-bit-index + cumulative-boundary layout (FIPS 204 Algorithm 20/21) — NO crypto, NO hardness.

## Method
`hintEncode`'s inner loop writes, for poly `i`, its set-bit indices (increasing) at the consecutive slots
`[W i, W (i+1))` where `W i` is the cumulative weight, and the boundary byte `ω+i = W (i+1)`; the tail stays
zero. We characterise those bytes exactly (`encOuter_spec`), then run `hintDecode` over that description
(`decOuter_spec`): every fail-closed check passes (boundaries non-decreasing ≤ ω; set-bits strictly
increasing since they are a filtered strictly-increasing range; padding zero), and each reconstructed poly is
`zeroPoly` with `1`s at exactly the set-bit indices, i.e. `hs[i]` (given `{0,1}` coeffs + size 256).

The hypotheses are witnessed satisfiable-and-firing on a GENUINE `fips204` crate hint (`native_decide`, in the
witness lemma only — never inside a ∀-body).
-/
import Dregg2.Crypto.VerifyCoreEqSpec

set_option maxRecDepth 8000

namespace Dregg2.Crypto.MlDsaHintCodec

open Dregg2.Crypto.MlDsaCodec
open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly)
open Dregg2.Crypto.VerifyCoreEqSpec (arrayExtAll size_mkEmpty getElem!_push_lt getElem!_push_eq)

/-! ## Set-bit index list of a polynomial (increasing order). -/

/-- The set-bit indices `< n` of `p`, in increasing order. -/
def sbAux (p : Poly) (n : Nat) : List Nat :=
  (List.range' 0 n 1).filter (fun j => decide (p[j]! ≠ 0))

/-- Poly weight: number of set (`≠ 0`) coefficients among the first 256. -/
def pw (p : Poly) : Nat := (sbAux p 256).length

theorem sbAux_zero (p : Poly) : sbAux p 0 = [] := rfl

theorem sbAux_succ (p : Poly) (n : Nat) :
    sbAux p (n + 1) = sbAux p n ++ (if p[n]! ≠ 0 then [n] else []) := by
  unfold sbAux
  rw [List.range'_1_concat, List.filter_append]
  simp only [Nat.zero_add, List.filter_cons, List.filter_nil, decide_eq_true_eq]

theorem sbAux_len_succ (p : Poly) (n : Nat) :
    (sbAux p (n + 1)).length = (sbAux p n).length + (if p[n]! ≠ 0 then 1 else 0) := by
  rw [sbAux_succ]; rw [List.length_append]; split <;> simp

theorem sbAux_len_mono (p : Poly) {a b : Nat} (h : a ≤ b) :
    (sbAux p a).length ≤ (sbAux p b).length := by
  induction b with
  | zero => have h0 : a = 0 := Nat.le_zero.mp h; subst h0; exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Nat.le_refl _
    · rw [sbAux_len_succ]; have := ih (by omega); omega

theorem sbAux_mem (p : Poly) (n j : Nat) : j ∈ sbAux p n ↔ (j < n ∧ p[j]! ≠ 0) := by
  unfold sbAux
  simp only [List.mem_filter, List.mem_range', decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨hj, hp⟩; exact ⟨⟨j, by omega, by omega⟩, hp⟩

/-- The set-bit list is strictly increasing. -/
theorem sbAux_sorted (p : Poly) (n : Nat) : (sbAux p n).Pairwise (· < ·) := by
  unfold sbAux
  apply List.Pairwise.filter
  exact @List.pairwise_lt_range' 0 n 1 (by omega)

/-! ## Applying a set-bit list to a base polynomial. -/

/-- Set all indices in `l` to `1` in `base`. -/
def appSB (l : List Nat) (base : Poly) : Poly := l.foldl (fun p k => p.set! k 1) base

theorem appSB_size (l : List Nat) (base : Poly) : (appSB l base).size = base.size := by
  induction l generalizing base with
  | nil => rfl
  | cons a t ih =>
    show (appSB t (base.set! a 1)).size = base.size
    rw [ih (base.set! a 1), Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem getElem!_set!_ne' {β} [Inhabited β] (arr : Array β) (i : Nat) (v : β) (j : Nat) (h : i ≠ j) :
    (arr.set! i v)[j]! = arr[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_ne h]

theorem getElem!_set!_self' {β} [Inhabited β] (arr : Array β) (i : Nat) (v : β) (h : i < arr.size) :
    (arr.set! i v)[i]! = v := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_self_of_lt h, Option.getD_some]

theorem getElem!_append_right {β} [Inhabited β] (a b : Array β) (i : Nat)
    (h : a.size ≤ i) (h2 : i < a.size + b.size) : (a ++ b)[i]! = b[i - a.size]! := by
  have hb : i - a.size < b.size := by omega
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append_right h]

/-- Reading `appSB l base` at `j < base.size`: it is `1` iff `j ∈ l`, else `base[j]!`. -/
theorem appSB_get (l : List Nat) (j : Nat) : ∀ (base : Poly), j < base.size →
    (appSB l base)[j]! = if j ∈ l then 1 else base[j]! := by
  induction l with
  | nil => intro base hj; simp [appSB]
  | cons a t ih =>
    intro base hj
    show (appSB t (base.set! a 1))[j]! = if j ∈ a :: t then 1 else base[j]!
    rw [ih (base.set! a 1) (by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hj)]
    by_cases hjt : j ∈ t
    · simp [hjt, List.mem_cons]
    · by_cases hja : a = j
      · subst hja
        rw [getElem!_set!_self' _ _ _ hj]
        simp [List.mem_cons]
      · rw [getElem!_set!_ne' _ _ _ _ hja]
        simp [hjt, List.mem_cons, Ne.symm hja]

/-- On a size-256 `{0,1}` poly, applying its own set-bit list to `zeroPoly` recovers it. -/
theorem appSB_sbAux_eq (p : Poly) (hsz : p.size = 256)
    (hbit : ∀ j, j < 256 → p[j]! = 0 ∨ p[j]! = 1) :
    appSB (sbAux p 256) zeroPoly = p := by
  apply arrayExtAll
  · rw [appSB_size]; simp [zeroPoly, hsz]
  · intro j hj
    rw [appSB_size] at hj
    have hj256 : j < 256 := by simpa only [zeroPoly, Array.size_replicate] using hj
    have hjz : j < zeroPoly.size := by simp only [zeroPoly, Array.size_replicate]; omega
    have hz : zeroPoly[j]! = 0 := by
      simp only [zeroPoly, Array.getElem!_eq_getD]; simp [Array.getD, hj256]
    rw [appSB_get _ _ _ hjz, hz]
    by_cases hm : j ∈ sbAux p 256
    · rw [if_pos hm]
      have hp := ((sbAux_mem p 256 j).mp hm).2
      rcases hbit j hj256 with h | h
      · exact absurd h hp
      · exact h.symm
    · rw [if_neg hm]
      have hp0 : p[j]! = 0 := by
        by_contra hne
        exact hm ((sbAux_mem p 256 j).mpr ⟨hj256, hne⟩)
      exact hp0.symm

/-! ## Cumulative weight and the encode do-loop, as explicit `List.foldl`. -/

/-- Cumulative set-bit weight of polys `0 .. m-1`. -/
def cw (hs : Array Poly) : Nat → Nat
  | 0 => 0
  | (m + 1) => cw hs m + pw (hs[m]!)

theorem cw_le_of_le (hs : Array Poly) {a b : Nat} (h : a ≤ b) : cw hs a ≤ cw hs b := by
  induction b with
  | zero => have : a = 0 := Nat.le_zero.mp h; subst this; exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Nat.le_refl _
    · have := ih (by omega); simp only [cw]; omega

/-- The encode inner-loop body (do-notation `MProd ⟨index, y⟩` state). -/
def encStep (p : Poly) (s : MProd Nat (Array UInt8)) (j : Nat) : MProd Nat (Array UInt8) :=
  if p[j]! ≠ 0 then ⟨s.1 + 1, s.2.set! s.1 (UInt8.ofNat j)⟩ else s

/-- The encode outer-loop body: run the inner loop over poly `i`, then write the boundary byte `ω+i`. -/
def encOuterStep (hs : Array Poly) (st : MProd Nat (Array UInt8)) (i : Nat) : MProd Nat (Array UInt8) :=
  let inner := List.foldl (encStep (hs[i]!)) st (List.range' 0 256 1)
  ⟨inner.1, inner.2.set! (omega + i) (UInt8.ofNat inner.1)⟩

/-- `hintEncode` as an explicit `List.foldl` (its `.snd` array). -/
def candEnc (hs : Array Poly) : Array UInt8 :=
  (List.foldl (encOuterStep hs) ⟨0, Array.replicate (omega + paramK) 0⟩ (List.range' 0 paramK 1)).2

private theorem ite_pure_yield {X : Type} {c : Prop} [Decidable c] (a b : X) :
    (if c then pure (ForInStep.yield a) else pure (ForInStep.yield b))
      = (pure (ForInStep.yield (if c then a else b)) : Id (ForInStep X)) := by
  split <;> rfl

/-- The v4.35 `do`-notation inner encode step: the loop state is the `Prod` `(y, index)` in
declaration order (it was the `MProd ⟨index, y⟩` `encStep` is stated over). -/
private def encStepP (p : Poly) (b : Array UInt8 × Nat) (j : Nat) : Array UInt8 × Nat :=
  if p[j]! ≠ 0 then (b.1.set! b.2 (UInt8.ofNat j), b.2 + 1) else (b.1, b.2)

private theorem encStepP_fold (p : Poly) (st : MProd Nat (Array UInt8)) (l : List Nat) :
    List.foldl (encStepP p) (st.2, st.1) l
      = ((List.foldl (encStep p) st l).2, (List.foldl (encStep p) st l).1) :=
  List.foldl_hom (fun s : MProd Nat (Array UInt8) => ((s.2, s.1) : Array UInt8 × Nat))
    (fun s j => by unfold encStep encStepP; split <;> rfl)

/-- The v4.35 outer encode step over the `Prod` state. -/
private def encOuterStepP (hs : Array Poly) (b : Array UInt8 × Nat) (i : Nat) : Array UInt8 × Nat :=
  ((List.foldl (encStepP (hs[i]!)) (b.1, b.2) (List.range' 0 256 1)).1.set! (omega + i)
      (UInt8.ofNat (List.foldl (encStepP (hs[i]!)) (b.1, b.2) (List.range' 0 256 1)).2),
    (List.foldl (encStepP (hs[i]!)) (b.1, b.2) (List.range' 0 256 1)).2)

private theorem encOuterStepP_fold (hs : Array Poly) (st : MProd Nat (Array UInt8)) (l : List Nat) :
    List.foldl (encOuterStepP hs) (st.2, st.1) l
      = ((List.foldl (encOuterStep hs) st l).2, (List.foldl (encOuterStep hs) st l).1) :=
  List.foldl_hom (fun s : MProd Nat (Array UInt8) => ((s.2, s.1) : Array UInt8 × Nat))
    (fun s i => by
      show encOuterStepP hs (s.2, s.1) i = ((encOuterStep hs s i).2, (encOuterStep hs s i).1)
      unfold encOuterStepP encOuterStep
      rw [encStepP_fold])

theorem encUnfold (hs : Array Poly) : hintEncode hs = candEnc hs := by
  unfold hintEncode candEnc
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    bind_pure_comp, map_pure,
    ite_pure_yield, List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
  exact congrArg Prod.fst
    (encOuterStepP_fold hs ⟨0, Array.replicate (omega + paramK) 0⟩ (List.range' 0 paramK 1))

theorem list_get!_append_left {α} [Inhabited α] {l1 l2 : List α} {i : Nat} (h : i < l1.length) :
    (l1 ++ l2)[i]! = l1[i]! := by simp only [getElem!_def, List.getElem?_append_left h]

theorem list_get!_append_right_len {α} [Inhabited α] (l : List α) (x : α) :
    (l ++ [x])[l.length]! = x := by
  simp only [getElem!_def, List.getElem?_append_right (Nat.le_refl _)]; simp

/-- **Encode inner-loop characterisation.** Starting from `⟨idx0, y0⟩`, folding `encStep p` over the first
`n` coefficients writes `p`'s set-bit indices (increasing) at consecutive slots `idx0, idx0+1, …`, leaving
all other slots untouched. -/
theorem encInner_spec (p : Poly) (y0 : Array UInt8) (idx0 : Nat) (hbound : idx0 + pw p ≤ y0.size) :
    ∀ (n : Nat), n ≤ 256 →
      let r := List.foldl (encStep p) ⟨idx0, y0⟩ (List.range' 0 n 1)
      r.1 = idx0 + (sbAux p n).length
      ∧ r.2.size = y0.size
      ∧ (∀ k, k < idx0 → r.2[k]! = y0[k]!)
      ∧ (∀ k, idx0 + (sbAux p n).length ≤ k → r.2[k]! = y0[k]!)
      ∧ (∀ rr, rr < (sbAux p n).length → r.2[idx0 + rr]! = UInt8.ofNat ((sbAux p n)[rr]!)) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [List.range'_zero, sbAux_zero]
    · simp [List.range'_zero]
    · intro k _; simp [List.range'_zero]
    · intro k _; simp [List.range'_zero]
    · intro rr hrr; simp [sbAux_zero] at hrr
  | succ k ih =>
    intro hk
    obtain ⟨IH1, IH2, IH3, IH4, IH5⟩ := ih (by omega)
    rw [show List.range' 0 (k + 1) 1 = List.range' 0 k 1 ++ [k] from by
          rw [List.range'_1_concat, Nat.zero_add], List.foldl_concat]
    set P := List.foldl (encStep p) ⟨idx0, y0⟩ (List.range' 0 k 1) with hP
    have hLmono : (sbAux p (k + 1)).length ≤ pw p := sbAux_len_mono p (by omega)
    by_cases hpk : p[k]! ≠ 0
    · -- coefficient k is a set bit
      have hsucc : sbAux p (k + 1) = sbAux p k ++ [k] := by rw [sbAux_succ]; simp [hpk]
      have hlensucc : (sbAux p (k + 1)).length = (sbAux p k).length + 1 := by
        rw [hsucc, List.length_append]; simp
      have hstep : encStep p P k = ⟨P.1 + 1, P.2.set! P.1 (UInt8.ofNat k)⟩ := by
        simp only [encStep, if_pos hpk]
      have hP1 : P.1 = idx0 + (sbAux p k).length := IH1
      have hP2sz : P.2.size = y0.size := IH2
      have hP1lt : P.1 < P.2.size := by
        rw [hP1, hP2sz]; have := hlensucc ▸ hLmono; omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show (encStep p P k).1 = _
        rw [hstep]; simp only; rw [hP1, hlensucc]; omega
      · show (encStep p P k).2.size = _
        rw [hstep]; simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hP2sz
      · intro k' hk'
        show (encStep p P k).2[k']! = _
        rw [hstep]; simp only
        rw [getElem!_set!_ne' _ _ _ _ (by rw [hP1]; omega), IH3 k' hk']
      · intro k' hk'
        show (encStep p P k).2[k']! = _
        rw [hstep]; simp only
        rw [getElem!_set!_ne' _ _ _ _ (by rw [hP1, hlensucc] at *; omega),
          IH4 k' (by rw [hlensucc] at hk'; omega)]
      · intro rr hrr
        show (encStep p P k).2[idx0 + rr]! = _
        rw [hstep]; simp only
        rw [hlensucc] at hrr
        rcases Nat.lt_succ_iff_lt_or_eq.mp hrr with hlt | heq
        · rw [getElem!_set!_ne' _ _ _ _ (by rw [hP1]; omega), IH5 rr hlt, hsucc,
            list_get!_append_left hlt]
        · subst heq
          rw [show idx0 + (sbAux p k).length = P.1 from by rw [hP1],
            getElem!_set!_self' _ _ _ hP1lt, hsucc, list_get!_append_right_len]
    · -- coefficient k is not a set bit: state unchanged
      have hsucc : sbAux p (k + 1) = sbAux p k := by rw [sbAux_succ]; simp [hpk]
      have hstep : encStep p P k = P := by simp only [encStep, if_neg hpk]
      rw [hstep, hsucc]
      exact ⟨IH1, IH2, IH3, IH4, IH5⟩

theorem replicate_get! {α} [Inhabited α] (n t : Nat) (v : α) (h : t < n) :
    (Array.replicate n v)[t]! = v := by
  rw [getElem!_pos _ _ (by simpa using h), Array.getElem_replicate]

/-- **Encode outer-loop characterisation.** After encoding the first `m` polys, the byte array has the set-bit
indices of poly `i` at slots `[cw i, cw (i+1))`, the boundary byte `ω+i = cw (i+1)`, and zeros elsewhere in
the still-unwritten data `[cw m, ω)` and boundary `[ω+m, ω+k)` regions. -/
theorem encOuter_spec (hs : Array Poly) (hsz : hs.size = paramK) (hwt : cw hs paramK ≤ omega) :
    ∀ (m : Nat), m ≤ paramK →
      let r := List.foldl (encOuterStep hs) ⟨0, Array.replicate (omega + paramK) 0⟩ (List.range' 0 m 1)
      r.1 = cw hs m
      ∧ r.2.size = omega + paramK
      ∧ (∀ i, i < m → r.2[omega + i]! = UInt8.ofNat (cw hs (i + 1)))
      ∧ (∀ i, i < m → ∀ rr, rr < pw (hs[i]!) →
          r.2[cw hs i + rr]! = UInt8.ofNat ((sbAux (hs[i]!) 256)[rr]!))
      ∧ (∀ t, cw hs m ≤ t → t < omega → r.2[t]! = 0)
      ∧ (∀ t, omega + m ≤ t → t < omega + paramK → r.2[t]! = 0) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨rfl, by simp, ?_, ?_, ?_, ?_⟩
    · intro i hi; omega
    · intro i hi; omega
    · intro t _ ht; exact replicate_get! _ _ _ (by omega)
    · intro t _ ht; exact replicate_get! _ _ _ ht
  | succ m ih =>
    intro hk
    obtain ⟨IH1, IH2, IH3, IH4, IH5, IH6⟩ := ih (by omega)
    rw [show List.range' 0 (m + 1) 1 = List.range' 0 m 1 ++ [m] from by
          rw [List.range'_1_concat, Nat.zero_add], List.foldl_concat]
    set P := List.foldl (encOuterStep hs) ⟨0, Array.replicate (omega + paramK) 0⟩ (List.range' 0 m 1)
      with hPdef
    -- inner-loop result Q for poly m
    set Q := List.foldl (encStep (hs[m]!)) P (List.range' 0 256 1) with hQdef
    have hstepeq : encOuterStep hs P m = ⟨Q.1, Q.2.set! (omega + m) (UInt8.ofNat Q.1)⟩ := rfl
    have hcw1 : cw hs (m + 1) = cw hs m + pw (hs[m]!) := rfl
    have hcwle : cw hs (m + 1) ≤ omega := le_trans (cw_le_of_le hs hk) hwt
    have hcwm : cw hs m ≤ omega := le_trans (cw_le_of_le hs (by omega)) hwt
    -- apply the inner-loop spec
    have hbound : P.1 + pw (hs[m]!) ≤ P.2.size := by
      rw [IH1, IH2]; rw [← hcw1] at *; omega
    have hspec := encInner_spec (hs[m]!) P.2 P.1 hbound 256 (Nat.le_refl _)
    rw [show (⟨P.1, P.2⟩ : MProd Nat (Array UInt8)) = P from rfl, ← hQdef] at hspec
    obtain ⟨Q1, Q2, Q3, Q4, Q5⟩ := hspec
    have hpweq : (sbAux (hs[m]!) 256).length = pw (hs[m]!) := rfl
    rw [hpweq] at Q1 Q4 Q5
    -- rewrite Q1..Q5 into cw-form
    rw [IH1] at Q3 Q4 Q5
    have hQ1 : Q.1 = cw hs (m + 1) := by rw [Q1, IH1]; exact hcw1.symm
    have hQ2 : Q.2.size = omega + paramK := by rw [Q2, IH2]
    have hQ4' : ∀ t, cw hs (m + 1) ≤ t → Q.2[t]! = P.2[t]! := by
      intro t ht; exact Q4 t (by rw [← hcw1] at *; omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (encOuterStep hs P m).1 = _
      rw [hstepeq]; exact hQ1
    · show (encOuterStep hs P m).2.size = _
      rw [hstepeq]; simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hQ2
    · -- boundary bytes
      intro i hi
      show (encOuterStep hs P m).2[omega + i]! = _
      rw [hstepeq]; simp only
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · rw [getElem!_set!_ne' _ _ _ _ (by omega), hQ4' _ (by omega), IH3 i hlt]
      · subst heq
        rw [getElem!_set!_self' _ _ _ (by rw [hQ2]; omega), hQ1]
    · -- data bytes
      intro i hi rr hrr
      show (encOuterStep hs P m).2[cw hs i + rr]! = _
      rw [hstepeq]; simp only
      have hcwi : cw hs i + rr < cw hs (i + 1) := by
        have hci : cw hs (i + 1) = cw hs i + pw (hs[i]!) := rfl
        rw [hci]; omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · have hbnd : cw hs i + rr < cw hs m := lt_of_lt_of_le hcwi (cw_le_of_le hs (by omega))
        rw [getElem!_set!_ne' _ _ _ _ (by omega), Q3 _ hbnd, IH4 i hlt rr hrr]
      · subst heq
        rw [getElem!_set!_ne' _ _ _ _ (by omega), Q5 rr hrr]
    · -- untouched data region [cw (m+1), ω)
      intro t ht htω
      show (encOuterStep hs P m).2[t]! = _
      rw [hstepeq]; simp only
      rw [getElem!_set!_ne' _ _ _ _ (by omega), hQ4' t ht, IH5 t (by rw [hcw1] at ht; omega) htω]
    · -- untouched boundary region [ω+(m+1), ω+k)
      intro t ht htk
      show (encOuterStep hs P m).2[t]! = _
      rw [hstepeq]; simp only
      rw [getElem!_set!_ne' _ _ _ _ (by omega), hQ4' t (by omega), IH6 t (by omega) htk]

/-- **Byte characterisation of `hintEncode hs`.** -/
theorem encBytes (hs : Array Poly) (hsz : hs.size = paramK) (hwt : cw hs paramK ≤ omega) :
    (hintEncode hs).size = omega + paramK
    ∧ (∀ i, i < paramK → (hintEncode hs)[omega + i]! = UInt8.ofNat (cw hs (i + 1)))
    ∧ (∀ i, i < paramK → ∀ rr, rr < pw (hs[i]!) →
        (hintEncode hs)[cw hs i + rr]! = UInt8.ofNat ((sbAux (hs[i]!) 256)[rr]!))
    ∧ (∀ t, cw hs paramK ≤ t → t < omega → (hintEncode hs)[t]! = 0) := by
  obtain ⟨R1, R2, R3, R4, R5, _⟩ := encOuter_spec hs hsz hwt paramK (Nat.le_refl _)
  rw [encUnfold]
  exact ⟨R2, R3, R4, R5⟩

/-! ## The decode do-loop, as explicit `List.foldl`. -/

/-- Decode inner-loop body (do-notation `MProd ⟨ok, p, prevIdx⟩` state). -/
def decInStep (b : Array UInt8) (hoff start : Nat) (s : MProd Bool (MProd Poly Nat)) (pos : Nat) :
    MProd Bool (MProd Poly Nat) :=
  if (decide (pos > start) && decide ((b[hoff + pos]!).toNat ≤ s.2.2)) then
    ⟨false, s.2.1.set! (b[hoff + pos]!).toNat 1, (b[hoff + pos]!).toNat⟩
  else ⟨s.1, s.2.1.set! (b[hoff + pos]!).toNat 1, (b[hoff + pos]!).toNat⟩

/-- Decode inner loop over `[start, bound)` starting from ok-flag `ok0`. -/
def decInFold (b : Array UInt8) (hoff start bound : Nat) (ok0 : Bool) : MProd Bool (MProd Poly Nat) :=
  List.foldl (decInStep b hoff start) ⟨ok0, zeroPoly, 0⟩ (List.range' start (bound - start) 1)

/-- Decode outer-loop body (do-notation `MProd ⟨index, ok, polys⟩` state). -/
def decOutStep (b : Array UInt8) (hoff : Nat) (st : MProd Nat (MProd Bool (Array Poly))) (i : Nat) :
    MProd Nat (MProd Bool (Array Poly)) :=
  let bound := (b[hoff + omega + i]!).toNat
  if (decide (bound < st.1) || decide (bound > omega)) then
    let inner := decInFold b hoff st.1 bound false
    ⟨bound, inner.1, st.2.2.push inner.2.1⟩
  else
    let inner := decInFold b hoff st.1 bound st.2.1
    ⟨bound, inner.1, st.2.2.push inner.2.1⟩

/-- Decode trailing-padding fold: `ok` becomes false on any nonzero byte in `[index, ω)`. -/
def decPadOk (b : Array UInt8) (hoff : Nat) (r : MProd Nat (MProd Bool (Array Poly))) : Bool :=
  List.foldl (fun ok pos => if (b[hoff + pos]!).toNat ≠ 0 then false else ok) r.2.1
    (List.range' r.1 (omega - r.1) 1)

/-- `hintDecode` as explicit `List.foldl`s. -/
def candDec (b : Array UInt8) (hoff : Nat) : Option (Array Poly) :=
  let r := List.foldl (decOutStep b hoff) ⟨0, true, Array.mkEmpty paramK⟩ (List.range' 0 paramK 1)
  if decPadOk b hoff r then some r.2.2 else none

/-- `candDec` with its internal `let` zeta-reduced (for rewriting). -/
theorem candDec_eq (b : Array UInt8) (hoff : Nat) :
    candDec b hoff =
      (if decPadOk b hoff
            (List.foldl (decOutStep b hoff) ⟨0, true, Array.mkEmpty paramK⟩ (List.range' 0 paramK 1))
        then some (List.foldl (decOutStep b hoff) ⟨0, true, Array.mkEmpty paramK⟩
            (List.range' 0 paramK 1)).2.2
        else none) := rfl

/-! The v4.35 `do`-notation decode state is a `Prod` in declaration order: `(ok, p, prevIdx)` for the
inner loop and `(index, ok, polys)` for the outer one, the same component order as the `MProd`s the
steps above are stated over. These are the `Prod` steps and their fold bridges. -/

private def decInStepP (b : Array UInt8) (hoff start : Nat) (s : Bool × Poly × Nat) (pos : Nat) :
    Bool × Poly × Nat :=
  if (decide (pos > start) && decide ((b[hoff + pos]!).toNat ≤ s.2.2)) then
    (false, s.2.1.set! (b[hoff + pos]!).toNat 1, (b[hoff + pos]!).toNat)
  else (s.1, s.2.1.set! (b[hoff + pos]!).toNat 1, (b[hoff + pos]!).toNat)

private theorem decInStepP_fold (b : Array UInt8) (hoff start : Nat) (s : MProd Bool (MProd Poly Nat))
    (l : List Nat) :
    List.foldl (decInStepP b hoff start) (s.1, s.2.1, s.2.2) l
      = ((List.foldl (decInStep b hoff start) s l).1, (List.foldl (decInStep b hoff start) s l).2.1,
          (List.foldl (decInStep b hoff start) s l).2.2) :=
  List.foldl_hom (fun s : MProd Bool (MProd Poly Nat) => ((s.1, s.2.1, s.2.2) : Bool × Poly × Nat))
    (fun s j => by unfold decInStep decInStepP; split <;> rfl)

private def decInFoldP (b : Array UInt8) (hoff start bound : Nat) (ok0 : Bool) : Bool × Poly × Nat :=
  List.foldl (decInStepP b hoff start) (ok0, zeroPoly, 0) (List.range' start (bound - start) 1)

private theorem decInFoldP_eq (b : Array UInt8) (hoff start bound : Nat) (ok0 : Bool) :
    decInFoldP b hoff start bound ok0
      = ((decInFold b hoff start bound ok0).1, (decInFold b hoff start bound ok0).2.1,
          (decInFold b hoff start bound ok0).2.2) :=
  decInStepP_fold b hoff start ⟨ok0, zeroPoly, 0⟩ _

private def decOutStepP (b : Array UInt8) (hoff : Nat) (st : Nat × Bool × Array Poly) (i : Nat) :
    Nat × Bool × Array Poly :=
  let bound := (b[hoff + omega + i]!).toNat
  if (decide (bound < st.1) || decide (bound > omega)) then
    let inner := decInFoldP b hoff st.1 bound false
    (bound, inner.1, st.2.2.push inner.2.1)
  else
    let inner := decInFoldP b hoff st.1 bound st.2.1
    (bound, inner.1, st.2.2.push inner.2.1)

private theorem decOutStepP_fold (b : Array UInt8) (hoff : Nat) (st : MProd Nat (MProd Bool (Array Poly)))
    (l : List Nat) :
    List.foldl (decOutStepP b hoff) (st.1, st.2.1, st.2.2) l
      = ((List.foldl (decOutStep b hoff) st l).1, (List.foldl (decOutStep b hoff) st l).2.1,
          (List.foldl (decOutStep b hoff) st l).2.2) :=
  List.foldl_hom
    (fun s : MProd Nat (MProd Bool (Array Poly)) => ((s.1, s.2.1, s.2.2) : Nat × Bool × Array Poly))
    (fun s i => by
      show decOutStepP b hoff (s.1, s.2.1, s.2.2) i
        = ((decOutStep b hoff s i).1, (decOutStep b hoff s i).2.1, (decOutStep b hoff s i).2.2)
      unfold decOutStepP decOutStep
      by_cases h : (decide ((b[hoff + omega + i]!).toNat < s.1)
          || decide ((b[hoff + omega + i]!).toNat > omega)) = true
      · simp only [h, ↓reduceIte, decInFoldP_eq]
      · simp only [h, Bool.false_eq_true, ↓reduceIte, decInFoldP_eq])

theorem decUnfold (b : Array UInt8) (hoff : Nat) : hintDecode b hoff = candDec b hoff := by
  unfold hintDecode
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    pure_bind, bind_pure_comp, map_pure,
    ite_pure_yield, List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
  have hR := decOutStepP_fold b hoff ⟨0, true, Array.mkEmpty paramK⟩ (List.range' 0 paramK 1)
  rw [candDec_eq, show List.foldl (decOutStep b hoff) ⟨0, true, Array.mkEmpty paramK⟩
      (List.range' 0 paramK 1)
    = ⟨(List.foldl (decOutStepP b hoff) (0, true, Array.mkEmpty paramK) (List.range' 0 paramK 1)).1,
        (List.foldl (decOutStepP b hoff) (0, true, Array.mkEmpty paramK) (List.range' 0 paramK 1)).2.1,
        (List.foldl (decOutStepP b hoff) (0, true, Array.mkEmpty paramK) (List.range' 0 paramK 1)).2.2⟩
    from by rw [hR]]
  unfold decPadOk decOutStepP decInFoldP decInStepP
  dsimp only
  rfl

/-- **Decode inner-loop characterisation.** If the bytes read over `[start, start+n)` are strictly
increasing (consecutively), the inner fold sets exactly those indices, and never trips the strict-increase
fail-closed check (so `ok` is preserved). -/
theorem decInner_spec (b : Array UInt8) (hoff start : Nat) :
    ∀ (n : Nat),
      (∀ r, r + 1 < n → (b[hoff + (start + r)]!).toNat < (b[hoff + (start + (r + 1))]!).toNat) →
      ∀ (base : Poly) (ok0 : Bool) (prev0 : Nat),
        let R := List.foldl (decInStep b hoff start) ⟨ok0, base, prev0⟩ (List.range' start n 1)
        R.1 = ok0
        ∧ R.2.1 = appSB ((List.range' 0 n 1).map (fun r => (b[hoff + (start + r)]!).toNat)) base
        ∧ R.2.2 = (if n = 0 then prev0 else (b[hoff + (start + (n - 1))]!).toNat) := by
  intro n
  induction n with
  | zero =>
    intro _ base ok0 prev0
    refine ⟨?_, ?_, ?_⟩ <;> simp [appSB, List.range'_zero]
  | succ k ih =>
    intro hsort base ok0 prev0
    obtain ⟨IH1, IH2, IH3⟩ := ih (fun r hr => hsort r (by omega)) base ok0 prev0
    rw [show List.range' start (k + 1) 1 = List.range' start k 1 ++ [start + k] from by
          rw [List.range'_1_concat], List.foldl_concat]
    set P := List.foldl (decInStep b hoff start) ⟨ok0, base, prev0⟩ (List.range' start k 1) with hPdef
    have hstep : decInStep b hoff start P (start + k)
        = ⟨P.1, P.2.1.set! (b[hoff + (start + k)]!).toNat 1, (b[hoff + (start + k)]!).toNat⟩ := by
      unfold decInStep
      rw [if_neg ?_]
      rintro hcond
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hcond
      obtain ⟨hgt, hle⟩ := hcond
      have hk1 : 0 < k := by omega
      rw [IH3, if_neg (by omega)] at hle
      have hcancel : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk1
      have := hsort (k - 1) (by omega)
      rw [hcancel] at this
      omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hstep]; exact IH1
    · rw [hstep]
      show (P.2.1.set! (b[hoff + (start + k)]!).toNat 1) = _
      rw [IH2, List.range'_1_concat, List.map_append]
      simp only [Nat.zero_add, List.map_cons, List.map_nil, appSB, List.foldl_concat]
    · rw [hstep]
      simp only [Nat.add_one_sub_one]
      rw [if_neg (by omega)]

/-! ## List helpers for the decode reconstruction. -/

theorem pairwise_lt_getElem! (L : List Nat) (h : L.Pairwise (· < ·)) (r : Nat)
    (hr : r + 1 < L.length) : L[r]! < L[r + 1]! := by
  rw [List.pairwise_iff_getElem] at h
  have hlt := h r (r + 1) (by omega) hr (by omega)
  rwa [getElem!_pos L r (by omega), getElem!_pos L (r + 1) hr]

theorem map_getElem!_range' (L : List Nat) :
    (List.range' 0 L.length 1).map (fun r => L[r]!) = L := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    rw [List.getElem_map, List.getElem_range']
    simp only [Nat.zero_add, Nat.one_mul]
    exact getElem!_pos L k h2

/-- **Decode outer-loop characterisation** on bytes matching the encode layout. Every fail-closed check
passes (`ok` stays true) and poly `i` is reconstructed as `hs[i]!`. -/
theorem decOuter_spec (hs : Array Poly) (b : Array UInt8) (hoff : Nat)
    (hwt : cw hs paramK ≤ omega)
    (hszAll : ∀ i, i < paramK → (hs[i]!).size = 256)
    (hbitAll : ∀ i, i < paramK → ∀ j, j < 256 → (hs[i]!)[j]! = 0 ∨ (hs[i]!)[j]! = 1)
    (HB : ∀ i, i < paramK → (b[hoff + omega + i]!).toNat = cw hs (i + 1))
    (HD : ∀ i, i < paramK → ∀ rr, rr < pw (hs[i]!) →
        (b[hoff + (cw hs i + rr)]!).toNat = (sbAux (hs[i]!) 256)[rr]!) :
    ∀ (m : Nat), m ≤ paramK →
      let r := List.foldl (decOutStep b hoff) ⟨0, true, Array.mkEmpty paramK⟩ (List.range' 0 m 1)
      r.1 = cw hs m
      ∧ r.2.1 = true
      ∧ r.2.2.size = m
      ∧ (∀ i, i < m → r.2.2[i]! = hs[i]!) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨rfl, rfl, size_mkEmpty paramK, ?_⟩
    intro i hi; omega
  | succ m ih =>
    intro hk
    obtain ⟨IH1, IH2, IH3, IH4⟩ := ih (by omega)
    rw [show List.range' 0 (m + 1) 1 = List.range' 0 m 1 ++ [m] from by
          rw [List.range'_1_concat, Nat.zero_add], List.foldl_concat]
    set P := List.foldl (decOutStep b hoff) ⟨0, true, Array.mkEmpty paramK⟩ (List.range' 0 m 1)
      with hPdef
    have hcw1 : cw hs (m + 1) = cw hs m + pw (hs[m]!) := rfl
    have hcwle : cw hs (m + 1) ≤ omega := le_trans (cw_le_of_le hs hk) hwt
    have hbound_eq : (b[hoff + omega + m]!).toNat = cw hs (m + 1) := HB m (by omega)
    have hcond : (decide (cw hs (m + 1) < P.1) || decide (cw hs (m + 1) > omega)) = false := by
      rw [IH1, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not,
        not_lt, not_lt]
      exact ⟨cw_le_of_le hs (by omega), hcwle⟩
    have hsub : cw hs (m + 1) - cw hs m = pw (hs[m]!) := by rw [hcw1]; omega
    -- the inner fold (decInner over poly m's window), and its equality to the else-branch decInFold
    have hsorted : ∀ r, r + 1 < pw (hs[m]!) →
        (b[hoff + (cw hs m + r)]!).toNat < (b[hoff + (cw hs m + (r + 1))]!).toNat := by
      intro r hr
      rw [HD m (by omega) r (by omega), HD m (by omega) (r + 1) (by omega)]
      exact pairwise_lt_getElem! (sbAux (hs[m]!) 256) (sbAux_sorted _ _) r (by
        rw [show (sbAux (hs[m]!) 256).length = pw (hs[m]!) from rfl]; omega)
    obtain ⟨I1, I2, _⟩ := decInner_spec b hoff (cw hs m) (pw (hs[m]!)) hsorted zeroPoly P.2.1 0
    set F := List.foldl (decInStep b hoff (cw hs m)) ⟨P.2.1, zeroPoly, 0⟩
      (List.range' (cw hs m) (pw (hs[m]!)) 1) with hFdef
    have hdecfold : decInFold b hoff P.1 (cw hs (m + 1)) P.2.1 = F := by
      rw [hFdef]; unfold decInFold; rw [IH1, hsub]
    have hstepeq : decOutStep b hoff P m = ⟨cw hs (m + 1), F.1, P.2.2.push F.2.1⟩ := by
      unfold decOutStep
      simp only [hbound_eq, hcond, Bool.false_eq_true, if_false]
      rw [hdecfold]
    -- reconstruction of poly m
    have hmapeq : (List.range' 0 (pw (hs[m]!)) 1).map (fun r => (b[hoff + (cw hs m + r)]!).toNat)
        = sbAux (hs[m]!) 256 := by
      rw [show pw (hs[m]!) = (sbAux (hs[m]!) 256).length from rfl,
        List.map_congr_left (g := fun r => (sbAux (hs[m]!) 256)[r]!) ?_]
      · exact map_getElem!_range' _
      · intro r hr
        rw [List.mem_range'] at hr
        exact HD m (by omega) r (by
          rw [show pw (hs[m]!) = (sbAux (hs[m]!) 256).length from rfl]; omega)
    have hrecon : F.2.1 = hs[m]! := by
      rw [I2, hmapeq, appSB_sbAux_eq (hs[m]!) (hszAll m (by omega)) (hbitAll m (by omega))]
    have hokF : F.1 = true := by rw [I1, IH2]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hstepeq]
    · rw [hstepeq]; exact hokF
    · rw [hstepeq]; simp only [Array.size_push]; rw [IH3]
    · intro i hi
      rw [hstepeq]
      simp only
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · rw [getElem!_push_lt _ _ _ (by rw [IH3]; omega), IH4 i hlt]
      · subst heq
        have hpe : (P.2.2.push F.2.1)[i]! = F.2.1 := by rw [← IH3]; exact getElem!_push_eq _ _
        rw [hpe, hrecon]

/-! ## Assembly: `hintDecode (hintEncode hs) 0 = some hs`. -/

theorem toNat_ofNat_lt (n : Nat) (h : n < 256) : (UInt8.ofNat n).toNat = n :=
  UInt8.toNat_ofNat_of_lt' h

theorem sbAux_getElem_lt (p : Poly) (rr : Nat) (h : rr < (sbAux p 256).length) :
    (sbAux p 256)[rr]! < 256 := by
  have hmem : (sbAux p 256)[rr]! ∈ sbAux p 256 := by
    rw [getElem!_pos (sbAux p 256) rr h]; exact List.getElem_mem h
  exact ((sbAux_mem p 256 _).mp hmem).1

/-- The trailing-padding fold over all-zero bytes leaves `ok` unchanged. -/
theorem padFold_zero (b : Array UInt8) (hoff start : Nat) :
    ∀ (len : Nat) (ok0 : Bool),
      (∀ pos, start ≤ pos → pos < start + len → (b[hoff + pos]!).toNat = 0) →
      List.foldl (fun ok pos => if (b[hoff + pos]!).toNat ≠ 0 then false else ok) ok0
        (List.range' start len 1) = ok0 := by
  intro len
  induction len with
  | zero => intro ok0 _; rfl
  | succ k ih =>
    intro ok0 hz
    rw [show List.range' start (k + 1) 1 = List.range' start k 1 ++ [start + k] from by
          rw [List.range'_1_concat], List.foldl_concat,
        ih ok0 (fun pos h1 h2 => hz pos h1 (by omega)), hz (start + k) (by omega) (by omega)]
    simp

/-! ## `hintWeight hs = cw hs paramK` (so the primary target can use the FIPS `hintWeight` hypothesis). -/

/-- The set-bit counting inner loop equals the set-bit-list length. -/
theorem countFold_eq (p : Poly) : ∀ (n w0 : Nat),
    List.foldl (fun w j => if p[j]! ≠ 0 then w + 1 else w) w0 (List.range' 0 n 1)
      = w0 + (sbAux p n).length := by
  intro n
  induction n with
  | zero => intro w0; simp [sbAux_zero]
  | succ k ih =>
    intro w0
    rw [show List.range' 0 (k + 1) 1 = List.range' 0 k 1 ++ [k] from by
          rw [List.range'_1_concat, Nat.zero_add], List.foldl_concat, ih w0, sbAux_len_succ]
    split_ifs <;> omega

/-- `hintWeight` as a `List.foldl` over `hs.toList` (nested count loop). -/
theorem hintWeight_unfold (hs : Array Poly) :
    hintWeight hs = List.foldl (fun w p =>
      List.foldl (fun w j => if p[j]! ≠ 0 then w + 1 else w) w (List.range' 0 256 1)) 0 hs.toList := by
  unfold hintWeight
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    ite_pure_yield, List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_one_sub_one, Nat.div_one, ← Array.forIn_toList]
  rfl

theorem foldl_toList_take (hs : Array Poly) : ∀ m, m ≤ hs.size →
    List.foldl (fun w p => w + pw p) 0 (hs.toList.take m) = cw hs m := by
  intro m
  induction m with
  | zero => intro _; simp [cw]
  | succ k ih =>
    intro hk
    have hlen : k < hs.toList.length := by rw [Array.length_toList]; omega
    rw [List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some, List.foldl_append,
      ih (by omega), List.foldl_cons, List.foldl_nil, Array.getElem_toList,
      ← getElem!_pos hs k (by omega)]
    rfl

theorem hintWeight_eq_cw (hs : Array Poly) : hintWeight hs = cw hs hs.size := by
  rw [hintWeight_unfold]
  have hbody : (fun w (p : Poly) =>
        List.foldl (fun w j => if p[j]! ≠ 0 then w + 1 else w) w (List.range' 0 256 1))
      = (fun w p => w + pw p) := by
    funext w p; rw [countFold_eq]; rfl
  rw [hbody, ← foldl_toList_take hs hs.size (Nat.le_refl _),
    show hs.toList.take hs.size = hs.toList from by
      conv_rhs => rw [← List.take_length (l := hs.toList)]
      rw [Array.length_toList]]

/-- **Decode core**, parametric in the byte array and offset: any window whose bytes match the encode
layout of `hs` decodes back to `hs`. -/
theorem hintDecode_core (hs : Array Poly) (b : Array UInt8) (hoff : Nat)
    (hsz : hs.size = paramK)
    (hpsz : ∀ i, i < paramK → (hs[i]!).size = 256)
    (hbit : ∀ i, i < paramK → ∀ j, j < 256 → (hs[i]!)[j]! = 0 ∨ (hs[i]!)[j]! = 1)
    (hwt : cw hs paramK ≤ omega)
    (HB : ∀ i, i < paramK → (b[hoff + omega + i]!).toNat = cw hs (i + 1))
    (HD : ∀ i, i < paramK → ∀ rr, rr < pw (hs[i]!) →
        (b[hoff + (cw hs i + rr)]!).toNat = (sbAux (hs[i]!) 256)[rr]!)
    (Hpad : ∀ t, cw hs paramK ≤ t → t < omega → (b[hoff + t]!).toNat = 0) :
    hintDecode b hoff = some hs := by
  rw [decUnfold, candDec_eq]
  obtain ⟨R1, R2, R3, R4⟩ :=
    decOuter_spec hs b hoff hwt hpsz hbit HB HD paramK (Nat.le_refl _)
  set r := List.foldl (decOutStep b hoff) ⟨0, true, Array.mkEmpty paramK⟩
    (List.range' 0 paramK 1) with hr
  have hpadok : decPadOk b hoff r = true := by
    unfold decPadOk
    rw [R1, R2]
    exact padFold_zero b hoff (cw hs paramK) (omega - cw hs paramK) true (fun pos h1 h2 => by
      rw [Hpad pos h1 (by omega)])
  have hpolys : r.2.2 = hs := by
    apply arrayExtAll
    · rw [R3, hsz]
    · intro j hj; rw [R3] at hj; exact R4 j hj
  rw [hpadok, if_pos rfl, hpolys]

/-- The three byte facts (`HB`/`HD`/`Hpad`) hold for `hintEncode hs` read at offset `pre.size` of any
`pre ++ hintEncode hs`, given `pre.size = hoff`. Extracted so both `hintDecode_hintEncode` (pre = `#[]`,
hoff = 0) and `hintDecode_append` share the arithmetic. -/
theorem encBytes_shifted (pre : Array UInt8) (hs : Array Poly) (hsz : hs.size = paramK)
    (hwt : cw hs paramK ≤ omega) :
    (∀ i, i < paramK → ((pre ++ hintEncode hs)[pre.size + omega + i]!).toNat = cw hs (i + 1))
    ∧ (∀ i, i < paramK → ∀ rr, rr < pw (hs[i]!) →
        ((pre ++ hintEncode hs)[pre.size + (cw hs i + rr)]!).toNat = (sbAux (hs[i]!) 256)[rr]!)
    ∧ (∀ t, cw hs paramK ≤ t → t < omega → ((pre ++ hintEncode hs)[pre.size + t]!).toNat = 0) := by
  obtain ⟨hesize, hbound, hdata, hpad⟩ := encBytes hs hsz hwt
  have hread : ∀ t, t < omega + paramK →
      (pre ++ hintEncode hs)[pre.size + t]! = (hintEncode hs)[t]! := by
    intro t ht
    rw [getElem!_append_right pre (hintEncode hs) (pre.size + t) (by omega) (by rw [hesize]; omega)]
    congr 1; omega
  have hcw_lt : ∀ i, i < paramK → cw hs (i + 1) < 256 := by
    intro i hi; have := le_trans (cw_le_of_le hs (show i + 1 ≤ paramK by omega)) hwt
    have : omega = 55 := rfl; omega
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [show pre.size + omega + i = pre.size + (omega + i) from by omega,
      hread _ (by omega), hbound i hi]
    exact toNat_ofNat_lt _ (hcw_lt i hi)
  · intro i hi rr hrr
    have hcwrr : cw hs i + rr < omega := by
      have h1 : cw hs i + rr < cw hs (i + 1) := by
        have : cw hs (i + 1) = cw hs i + pw (hs[i]!) := rfl; rw [this]; omega
      have := le_trans (cw_le_of_le hs (show i + 1 ≤ paramK by omega)) hwt; omega
    rw [hread _ (by have : omega = 55 := rfl; have : paramK = 6 := rfl; omega), hdata i hi rr hrr]
    exact toNat_ofNat_lt _ (sbAux_getElem_lt _ _ hrr)
  · intro t ht htω
    rw [hread _ (by have : paramK = 6 := rfl; omega), hpad t ht htω]; rfl

/-- The FIPS 204 hint round-trip in cumulative-weight form (`hwt : cw hs paramK ≤ ω`); `cw hs paramK` is the
cumulative set-bit weight `= hintWeight hs` (`hintWeight_eq_cw`). The `hintWeight` form is
`hintDecode_hintEncode` below. -/
theorem hintDecode_hintEncode_cw (hs : Array Poly)
    (hsz : hs.size = paramK)
    (hpsz : ∀ i, i < paramK → (hs[i]!).size = 256)
    (hbit : ∀ i, i < paramK → ∀ j, j < 256 → (hs[i]!)[j]! = 0 ∨ (hs[i]!)[j]! = 1)
    (hwt : cw hs paramK ≤ omega) :
    hintDecode (hintEncode hs) 0 = some hs := by
  obtain ⟨_, hbound, hdata, hpad⟩ := encBytes hs hsz hwt
  refine hintDecode_core hs (hintEncode hs) 0 hsz hpsz hbit hwt ?_ ?_ ?_
  · intro i hi; rw [Nat.zero_add, hbound i hi]
    exact toNat_ofNat_lt _ (by
      have := le_trans (cw_le_of_le hs (show i + 1 ≤ paramK by omega)) hwt
      have : omega = 55 := rfl; omega)
  · intro i hi rr hrr; rw [Nat.zero_add, hdata i hi rr hrr]
    exact toNat_ofNat_lt _ (sbAux_getElem_lt _ _ hrr)
  · intro t ht htω; rw [Nat.zero_add, hpad t ht htω]; rfl

/-- **PRIMARY TARGET.** The FIPS 204 hint-codec round-trip `HintBitUnpack (HintBitPack hs) = hs` for any
`k = 6` size-256 `{0,1}`-polynomial hint whose total set-bit weight `hintWeight hs ≤ ω`. Pure
`Array`/`Nat`/`List` bookkeeping — NO crypto, NO hardness. -/
theorem hintDecode_hintEncode (hs : Array Poly)
    (hsz : hs.size = paramK)
    (hpsz : ∀ i, i < paramK → (hs[i]!).size = 256)
    (hbit : ∀ i, i < paramK → ∀ j, j < 256 → (hs[i]!)[j]! = 0 ∨ (hs[i]!)[j]! = 1)
    (hwt : hintWeight hs ≤ omega) :
    hintDecode (hintEncode hs) 0 = some hs := by
  refine hintDecode_hintEncode_cw hs hsz hpsz hbit ?_
  rw [← hsz, ← hintWeight_eq_cw]; exact hwt

/-- **SECONDARY TARGET (the shape `sigDecode_sigEncode` needs).** Decoding the hint region of a signature
`pre ++ hintEncode hs` at offset `pre.size` recovers `hs`. -/
theorem hintDecode_append (pre : Array UInt8) (hs : Array Poly)
    (hsz : hs.size = paramK)
    (hpsz : ∀ i, i < paramK → (hs[i]!).size = 256)
    (hbit : ∀ i, i < paramK → ∀ j, j < 256 → (hs[i]!)[j]! = 0 ∨ (hs[i]!)[j]! = 1)
    (hwt : cw hs paramK ≤ omega) :
    hintDecode (pre ++ hintEncode hs) pre.size = some hs := by
  obtain ⟨HB, HD, Hpad⟩ := encBytes_shifted pre hs hsz hwt
  exact hintDecode_core hs (pre ++ hintEncode hs) pre.size hsz hpsz hbit hwt HB HD Hpad

/-! ## Non-vacuity: the hypotheses are satisfiable and the ∀-theorem fires on a GENUINE `fips204` hint. -/

/-- The `k = 6` `{0,1}`-polynomial hint decoded from the real crate signature satisfies every hypothesis of
`hintDecode_hintEncode` (`native_decide`, on concrete data — never inside a ∀-body). -/
theorem real_hint_wf :
    (sigDecode realSig.toList).2.2.size = paramK
    ∧ (∀ i, i < paramK → ((sigDecode realSig.toList).2.2[i]!).size = 256)
    ∧ (∀ i, i < paramK → ∀ j, j < 256 →
        ((sigDecode realSig.toList).2.2[i]!)[j]! = 0 ∨ ((sigDecode realSig.toList).2.2[i]!)[j]! = 1)
    ∧ cw (sigDecode realSig.toList).2.2 paramK ≤ omega := by native_decide

/-- **Non-vacuity witness**: `hintDecode_hintEncode` FIRES on the genuine crate hint — encode then decode is
the identity on the real `k = 6` hint, so the ∀-theorem is not vacuous. -/
theorem hintDecode_hintEncode_witness :
    hintDecode (hintEncode (sigDecode realSig.toList).2.2) 0 = some (sigDecode realSig.toList).2.2 := by
  native_decide

/-- **Non-vacuity witness** for the offset/append form (real hint appended after a `3248`-byte prefix). -/
theorem hintDecode_append_witness :
    hintDecode ((sigDecode realSig.toList).1.toArray ++ hintEncode (sigDecode realSig.toList).2.2)
        (sigDecode realSig.toList).1.toArray.size = some (sigDecode realSig.toList).2.2 := by
  native_decide

#assert_axioms hintDecode_hintEncode
#assert_axioms hintDecode_hintEncode_cw
#assert_axioms hintDecode_append
#assert_axioms hintDecode_core
#assert_axioms hintWeight_eq_cw
#assert_axioms encOuter_spec
#assert_axioms decOuter_spec

end Dregg2.Crypto.MlDsaHintCodec
