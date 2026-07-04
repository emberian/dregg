/-
Ct.Tree — the RFC 6962 Merkle tree head (section 2.1).

`mth HS xs` is the Merkle Tree Hash of the leaf list `xs`:

  MTH([])       = hempty
  MTH([x])      = hleaf x
  MTH(xs)       = hnode (MTH (xs.take k)) (MTH (xs.drop k)),   k = split |xs|,  |xs| ≥ 2.

`xs` is the *log*: the leaves in append order.  `mth HS xs` is the **tree head**
(signed tree head, once signed) — a single digest committing to the whole list.

`head_deterministic` and `head_stable_under_append` record property (3): the head
is a function of the leaf list, and the head of the size-`m` prefix is unchanged
by later appends — the log only ever grows to the right.
-/
import Ct.Basic
import Ct.Split

namespace Ct

variable {Leaf H : Type}

/-- RFC 6962 Merkle Tree Hash (the tree head) of a leaf list. -/
def mth (HS : HashScheme Leaf H) : List Leaf → H
  | [] => HS.hempty
  | [x] => HS.hleaf x
  | a :: b :: rest =>
    HS.hnode
      (mth HS ((a :: b :: rest).take (split (a :: b :: rest).length)))
      (mth HS ((a :: b :: rest).drop (split (a :: b :: rest).length)))
termination_by l => l.length
decreasing_by
  · simp only [List.length_take]
    exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _)
      (split_lt (by simp only [List.length_cons]; omega))
  · simp only [List.length_drop]
    exact Nat.sub_lt (by simp only [List.length_cons]; omega)
      (split_pos (by simp only [List.length_cons]; omega))

@[simp] theorem mth_nil (HS : HashScheme Leaf H) : mth HS [] = HS.hempty := by
  rw [mth]

@[simp] theorem mth_single (HS : HashScheme Leaf H) (x : Leaf) :
    mth HS [x] = HS.hleaf x := by
  rw [mth]

/-- One-step RFC 6962 unfolding of the tree head for `|xs| ≥ 2`. -/
theorem mth_split (HS : HashScheme Leaf H) {xs : List Leaf} (h : 2 ≤ xs.length) :
    mth HS xs
      = HS.hnode (mth HS (xs.take (split xs.length)))
                 (mth HS (xs.drop (split xs.length))) := by
  match xs, h with
  | a :: b :: rest, _ => simp only [mth]

/-! ### Property (3): determinism -/

/-- The tree head is a function of the leaf list. -/
theorem head_deterministic (HS : HashScheme Leaf H) {xs ys : List Leaf}
    (h : xs = ys) : mth HS xs = mth HS ys := by rw [h]

/-- The head of the size-`m` prefix is unchanged by later appends: the log only
grows to the right, and past heads are stable. -/
theorem head_stable_under_append (HS : HashScheme Leaf H) {m : Nat}
    {xs ys : List Leaf} (h : m ≤ xs.length) :
    mth HS ((xs ++ ys).take m) = mth HS (xs.take m) := by
  rw [List.take_append_of_le_length h]

end Ct
