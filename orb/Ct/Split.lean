/-
Ct.Split — the RFC 6962 split point.

RFC 6962 section 2.1 splits an `n`-leaf tree (`n ≥ 2`) into a left subtree of
size `k` and a right subtree of size `n - k`, where `k` is the largest power of
two strictly less than `n`.  We compute `k = split n` via `highBit (n - 1)`,
where `highBit j` is the largest power of two `≤ j` (obtained by halving — no
bit-twiddling).

The three properties that drive every downstream recursion and proof:

  * `split_lt`  — `split n < n`         (both subtrees are strictly smaller: termination);
  * `split_pos` — `1 ≤ split n`         (the right subtree is nonempty: termination);
  * `split_stable` — `split n < m ≤ n → split m = split n`.

`split_stable` is the arithmetic heart of the consistency proof: it says the
old tree's left subtree (of size `split n`) is *the same complete subtree* in
both the size-`m` and size-`n` trees, which is exactly why appended history
cannot rewrite the prefix.
-/

namespace Ct

/-- Largest power of two `≤ k`, for `k ≥ 1`; `highBit 0 = 0`.  Defined by
halving, so it is manifestly a power of two on `k ≥ 1`. -/
def highBit (k : Nat) : Nat :=
  if k < 2 then k else 2 * highBit (k / 2)
termination_by k
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- RFC 6962 split point: the largest power of two strictly less than `n`
(meaningful for `n ≥ 2`). -/
def split (n : Nat) : Nat := highBit (n - 1)

theorem highBit_le (k : Nat) : highBit k ≤ k := by
  induction k using highBit.induct with
  | case1 k h => rw [highBit]; simp [h]
  | case2 k h ih =>
    rw [highBit]
    simp only [if_neg h]
    omega

theorem highBit_pos {k : Nat} (h : 1 ≤ k) : 1 ≤ highBit k := by
  induction k using highBit.induct with
  | case1 k hk => rw [highBit]; simp only [if_pos hk]; omega
  | case2 k hk ih =>
    rw [highBit]
    simp only [if_neg hk]
    have : 1 ≤ highBit (k / 2) := ih (by omega)
    omega

/-- The largest bit is unchanged on the interval `[highBit a, a]`. -/
theorem highBit_stable {a b : Nat} (hlo : highBit a ≤ b) (hhi : b ≤ a) :
    highBit b = highBit a := by
  induction a using highBit.induct generalizing b with
  | case1 a ha =>
    -- a < 2 : highBit a = a, so hlo : a ≤ b, hhi : b ≤ a, hence b = a
    have hba : highBit a = a := by rw [highBit]; simp [ha]
    rw [hba] at hlo
    have hb : b = a := by omega
    subst hb
    rfl
  | case2 a ha ih =>
    -- a ≥ 2
    have hpos : 1 ≤ highBit (a / 2) := highBit_pos (by omega)
    have ha2 : highBit a = 2 * highBit (a / 2) := by rw [highBit]; simp [ha]
    -- highBit a ≥ 2, so b ≥ 2
    have hbnlt : ¬ b < 2 := by omega
    have hbeq : highBit b = 2 * highBit (b / 2) := by rw [highBit]; simp [hbnlt]
    -- reduce to a/2, b/2 via the induction hypothesis
    have hlo' : highBit (a / 2) ≤ b / 2 := by
      have : 2 * highBit (a / 2) ≤ b := by omega
      omega
    have hhi' : b / 2 ≤ a / 2 := by omega
    have := ih hlo' hhi'
    rw [hbeq, ha2, this]

theorem split_lt {n : Nat} (h : 2 ≤ n) : split n < n := by
  have := highBit_le (n - 1)
  unfold split
  omega

theorem split_pos {n : Nat} (h : 2 ≤ n) : 1 ≤ split n := by
  have := highBit_pos (k := n - 1) (by omega)
  unfold split
  omega

/-- `split_stable`, phrased on tree sizes: when the old boundary `m` sits to the
right of the split of `n`, the split of `m` coincides with the split of `n`. -/
theorem split_stable {m n : Nat} (hk : split n < m) (hmn : m ≤ n) :
    split m = split n := by
  unfold split
  -- highBit (m-1) = highBit (n-1) from highBit_stable on a = n-1, b = m-1
  have hlo : highBit (n - 1) ≤ m - 1 := by
    have : split n < m := hk
    unfold split at this
    omega
  have hhi : m - 1 ≤ n - 1 := by omega
  exact highBit_stable hlo hhi

end Ct
