/-
Ct.Inclusion — RFC 6962 inclusion (audit) proofs, section 2.1.1.

An inclusion proof (audit path) for the leaf at index `i` in a size-`n` tree is
the list of sibling subtree heads encountered on the root-to-leaf descent.  A
monitor holding only the signed tree head `mth HS xs` and the claimed leaf can
recompute the head from the leaf hash and the path; if it matches, the leaf is
committed by that head.

  * `auditPath`     — the honest prover: emits the sibling heads, root-first.
  * `rootFromPath`  — the verifier core: recomputes the head from a leaf hash,
                      index, size, and path (or `none` on a malformed path).
  * `verifyInclusion` — the `Bool` verifier: recompute and compare.

Wire-order note: RFC 6962 serializes the audit path leaf-to-root; we build and
consume it root-to-leaf (a `List.reverse` away).  The recomputation is
order-internal, so the theorems are unaffected.

Theorem (1), inclusion soundness, is `verifyInclusion_iff`: against the real
head, a leaf verifies *iff* it is the genuine `i`-th appended leaf.  The
`←` direction (`inclusion_complete`) is pure recomputation; the `→` direction
(`inclusion_sound`, stated for an *arbitrary* — possibly adversarial — path)
is where collision resistance is spent: peeling `hnode_inj`/`hleaf_inj` forces
the claimed leaf to equal the real one.
-/
import Ct.Basic
import Ct.Split
import Ct.Tree

namespace Ct

variable {Leaf H : Type}

/-- Honest inclusion-proof generator: the sibling heads on the descent to leaf
`i`, emitted root-first. -/
def auditPath (HS : HashScheme Leaf H) : List Leaf → Nat → List H
  | xs, i =>
    if h : 2 ≤ xs.length then
      if i < split xs.length then
        mth HS (xs.drop (split xs.length)) :: auditPath HS (xs.take (split xs.length)) i
      else
        mth HS (xs.take (split xs.length)) :: auditPath HS (xs.drop (split xs.length)) (i - split xs.length)
    else []
termination_by xs _ => xs.length
decreasing_by
  · simp only [List.length_take]
    exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (split_lt h)
  · simp only [List.length_drop]
    exact Nat.sub_lt (by omega) (split_pos h)

/-- Verifier core: recompute the tree head from a leaf hash, its index, the tree
size, and an audit path.  Returns `none` on a malformed (wrong-length) path. -/
def rootFromPath (HS : HashScheme Leaf H) (lh : H) : Nat → Nat → List H → Option H
  | i, n, path =>
    if n ≤ 1 then
      match path with
      | [] => some lh
      | _ :: _ => none
    else
      match path with
      | [] => none
      | sib :: rest =>
        if i < split n then
          (rootFromPath HS lh i (split n) rest).map (fun L => HS.hnode L sib)
        else
          (rootFromPath HS lh (i - split n) (n - split n) rest).map (fun R => HS.hnode sib R)
termination_by _ n _ => n
decreasing_by
  · exact split_lt (by omega)
  · exact Nat.sub_lt (by omega) (split_pos (by omega))

/-- `Bool` inclusion verifier: recompute the head and compare to the expected
head (the signed tree head). -/
def verifyInclusion (HS : HashScheme Leaf H) [DecidableEq H]
    (leafHash : H) (i n : Nat) (path : List H) (root : H) : Bool :=
  match rootFromPath HS leafHash i n path with
  | some r => decide (r = root)
  | none => false

/-! ### One-step unfolding lemmas -/

theorem auditPath_le1 (HS : HashScheme Leaf H) {xs : List Leaf}
    (h : xs.length ≤ 1) (i : Nat) : auditPath HS xs i = [] := by
  rw [auditPath]; simp only [dif_neg (by omega : ¬ 2 ≤ xs.length)]

theorem auditPath_ge2 (HS : HashScheme Leaf H) {xs : List Leaf}
    (h : 2 ≤ xs.length) (i : Nat) :
    auditPath HS xs i =
      (if i < split xs.length then
         mth HS (xs.drop (split xs.length)) :: auditPath HS (xs.take (split xs.length)) i
       else
         mth HS (xs.take (split xs.length)) :: auditPath HS (xs.drop (split xs.length)) (i - split xs.length)) := by
  rw [auditPath]; simp only [dif_pos h]

theorem rootFromPath_le1 (HS : HashScheme Leaf H) (lh : H) {n : Nat} (i : Nat)
    (h : n ≤ 1) (path : List H) :
    rootFromPath HS lh i n path = (match path with | [] => some lh | _ :: _ => none) := by
  rw [rootFromPath.eq_def]; simp only [if_pos h]

theorem rootFromPath_ge2 (HS : HashScheme Leaf H) (lh : H) {n : Nat} (i : Nat)
    (h : 2 ≤ n) (path : List H) :
    rootFromPath HS lh i n path =
      (match path with
       | [] => none
       | sib :: rest =>
         if i < split n then
           (rootFromPath HS lh i (split n) rest).map (fun L => HS.hnode L sib)
         else
           (rootFromPath HS lh (i - split n) (n - split n) rest).map (fun R => HS.hnode sib R)) := by
  rw [rootFromPath.eq_def]; simp only [if_neg (by omega : ¬ n ≤ 1)]

/-! ### Property (1): inclusion soundness -/

/-- Completeness (`←` of theorem 1): the honest audit path for the genuine
`i`-th leaf recomputes the real head.  Pure recomputation — collision
resistance is not needed. -/
theorem inclusion_complete (HS : HashScheme Leaf H) :
    ∀ (n : Nat) (xs : List Leaf) (i : Nat) (y : Leaf),
      xs.length = n → xs[i]? = some y →
      rootFromPath HS (HS.hleaf y) i xs.length (auditPath HS xs i) = some (mth HS xs) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs i y hn hy
    rcases xs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hy
    · -- singleton [a]
      rcases i with _ | i'
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
        subst hy
        rw [auditPath_le1 HS (by simp) 0]
        rw [rootFromPath_le1 HS (HS.hleaf a) 0 (by simp) []]
        simp [mth_single]
      · simp at hy
    · -- length ≥ 2
      revert hn hy
      generalize hxs : a :: b :: rest = xs
      intro hn hy
      have h2 : 2 ≤ xs.length := by rw [← hxs]; simp
      have hklt : split xs.length < xs.length := split_lt h2
      have hkpos : 1 ≤ split xs.length := split_pos h2
      rw [auditPath_ge2 HS h2 i, mth_split HS h2]
      by_cases hik : i < split xs.length
      · -- descend into the left subtree
        simp only [if_pos hik]
        rw [rootFromPath_ge2 HS _ i h2]
        simp only [if_pos hik]
        have htlen : (xs.take (split xs.length)).length = split xs.length := by
          rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hklt)
        have hyt : (xs.take (split xs.length))[i]? = some y := by
          rw [List.getElem?_take_of_lt hik]; exact hy
        have hrec := ih (xs.take (split xs.length)).length (by rw [htlen]; omega)
          (xs.take (split xs.length)) i y rfl hyt
        rw [htlen] at hrec
        rw [hrec]; simp
      · -- descend into the right subtree
        simp only [if_neg hik]
        rw [rootFromPath_ge2 HS _ i h2]
        simp only [if_neg hik]
        have hile : split xs.length ≤ i := Nat.le_of_not_lt hik
        have hdlen : (xs.drop (split xs.length)).length = xs.length - split xs.length :=
          List.length_drop _ _
        have hyd : (xs.drop (split xs.length))[i - split xs.length]? = some y := by
          rw [List.getElem?_drop, Nat.add_sub_cancel' hile]; exact hy
        have hrec := ih (xs.drop (split xs.length)).length (by rw [hdlen]; omega)
          (xs.drop (split xs.length)) (i - split xs.length) y rfl hyd
        rw [hdlen] at hrec
        rw [hrec]; simp

/-- Soundness (`→` of theorem 1), stated for an **arbitrary** — possibly
adversarial — audit path: if *any* path recomputes the real head for a claimed
leaf hash `hleaf y`, then `y` is the genuine `i`-th appended leaf.  This is the
security core; it spends `hnode_inj` (peeling each interior node) and
`hleaf_inj` (at the leaf). -/
theorem inclusion_sound (HS : HashScheme Leaf H) :
    ∀ (n : Nat) (xs : List Leaf) (i : Nat) (y : Leaf) (path : List H),
      xs.length = n → i < n →
      rootFromPath HS (HS.hleaf y) i n path = some (mth HS xs) →
      xs[i]? = some y := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs i y path hn hi hroot
    rcases xs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp only [List.length_nil] at hn; omega
    · -- singleton [a]
      have hn1 : n = 1 := by simp at hn; omega
      have hi0 : i = 0 := by omega
      subst hi0
      rw [rootFromPath_le1 HS (HS.hleaf y) 0 (by omega) path, mth_single] at hroot
      cases path with
      | nil =>
        simp only [Option.some.injEq] at hroot
        have hya := HS.hleaf_inj hroot
        subst hya; simp
      | cons c cs => simp at hroot
    · -- length ≥ 2
      revert hn hi hroot
      generalize hxs : a :: b :: rest = xs
      intro hi hn hroot
      subst hn
      have h2 : 2 ≤ xs.length := by rw [← hxs]; simp
      have hklt : split xs.length < xs.length := split_lt h2
      have hkpos : 1 ≤ split xs.length := split_pos h2
      rw [mth_split HS h2, rootFromPath_ge2 HS _ i h2] at hroot
      cases path with
      | nil => simp at hroot
      | cons sib rest' =>
        by_cases hik : i < split xs.length
        · -- left subtree
          simp only [if_pos hik] at hroot
          cases hr : rootFromPath HS (HS.hleaf y) i (split xs.length) rest' with
          | none => rw [hr] at hroot; simp at hroot
          | some L =>
            rw [hr] at hroot
            simp only [Option.map_some', Option.some.injEq] at hroot
            obtain ⟨hL, _hsib⟩ := HS.hnode_inj hroot
            have htlen : (xs.take (split xs.length)).length = split xs.length := by
              rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hklt)
            rw [hL] at hr
            have hgot := ih (split xs.length) hklt
              (xs.take (split xs.length)) i y rest' htlen hik hr
            rw [← List.getElem?_take_of_lt hik]; exact hgot
        · -- right subtree
          simp only [if_neg hik] at hroot
          cases hr : rootFromPath HS (HS.hleaf y) (i - split xs.length) (xs.length - split xs.length) rest' with
          | none => rw [hr] at hroot; simp at hroot
          | some R =>
            rw [hr] at hroot
            simp only [Option.map_some', Option.some.injEq] at hroot
            obtain ⟨_hsib, hR⟩ := HS.hnode_inj hroot
            have hile : split xs.length ≤ i := Nat.le_of_not_lt hik
            have hdlen : (xs.drop (split xs.length)).length = xs.length - split xs.length :=
              List.length_drop _ _
            rw [hR] at hr
            have hgot := ih (xs.length - split xs.length) (by omega)
              (xs.drop (split xs.length)) (i - split xs.length) y rest' hdlen (by omega) hr
            have hidx : (xs.drop (split xs.length))[i - split xs.length]? = xs[i]? := by
              rw [List.getElem?_drop, Nat.add_sub_cancel' hile]
            rw [← hidx]; exact hgot

/-- **Theorem (1): inclusion-proof soundness.**  Against the real tree head, the
honest audit path for index `i` verifies a claimed leaf `y` *iff* `y` is the
genuine `i`-th appended leaf. -/
theorem inclusion_iff (HS : HashScheme Leaf H) [DecidableEq H]
    {xs : List Leaf} {i : Nat} {y : Leaf} (hi : i < xs.length) :
    verifyInclusion HS (HS.hleaf y) i xs.length (auditPath HS xs i) (mth HS xs) = true
      ↔ xs[i]? = some y := by
  constructor
  · intro hv
    unfold verifyInclusion at hv
    cases hr : rootFromPath HS (HS.hleaf y) i xs.length (auditPath HS xs i) with
    | none => rw [hr] at hv; simp at hv
    | some r =>
      rw [hr] at hv
      simp only [decide_eq_true_eq] at hv
      exact inclusion_sound HS xs.length xs i y (auditPath HS xs i) rfl hi (by rw [hr, hv])
  · intro hy
    have hc := inclusion_complete HS xs.length xs i y rfl hy
    unfold verifyInclusion
    rw [hc]; simp

/-! ### Property (4): verification is total -/

/-- Inclusion verification is a total, decidable predicate. -/
theorem verifyInclusion_total (HS : HashScheme Leaf H) [DecidableEq H]
    (leafHash : H) (i n : Nat) (path : List H) (root : H) :
    verifyInclusion HS leafHash i n path root = true
      ∨ verifyInclusion HS leafHash i n path root = false := by
  cases verifyInclusion HS leafHash i n path root <;> simp

end Ct
