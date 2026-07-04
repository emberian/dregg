/-
Ct.Consistency — RFC 6962 consistency proofs, section 2.1.2.

A consistency proof between an old size `m` and a new size `n` (`m ≤ n`) lets a
monitor that previously accepted the head `mth HS (xs.take m)` check that the
current head `mth HS xs` extends it *without rewriting history*: the size-`m`
tree is exactly the size-`m` prefix of the size-`n` tree.  This is the property
Certificate Transparency exists to give.

  * `consProof`         — the honest prover (subtree heads on the m→n frontier).
  * `consRec`           — the verifier core: from the proof and `(m, n)` it
                          recomputes *both* the old and the new head.
  * `verifyConsistency` — the `Bool` verifier: recompute, compare to the two
                          supplied heads, and require the proof fully consumed.

Encoding note: RFC 6962 omits the old head from the proof when the old tree is
a complete subtree (the `start`-flag optimization), reusing the externally
supplied `old_root` as the recomputation seed.  We instead transmit that shared
subtree head explicitly.  The two encodings are information-equivalent — RFC's
proof is ours with the redundant old head removed, which the verifier already
holds — and the append-only guarantee is identical.

Theorem (2), append-only/consistency, is `consistency_iff`: the honest proof
against the real new head verifies *iff* the claimed old head is the genuine
size-`m` prefix head.  Soundness (`consRec_sound`) is where collision resistance
is spent; the crux is `oldRoot_split` + `split_stable` — the old tree's complete
left subtree is *the same node* in both trees.
-/
import Ct.Basic
import Ct.Split
import Ct.Tree

namespace Ct

variable {Leaf H : Type}

/-! ### The append-only crux -/

/-- When the old boundary `m` lies strictly right of `split n`, the size-`m`
tree splits at the *same* node as the size-`n` tree (`split_stable`): its left
subtree is the shared complete subtree `xs.take (split n)`, and its right part
is the `m - split n` prefix of `xs.drop (split n)`. -/
theorem oldRoot_split (HS : HashScheme Leaf H) {xs : List Leaf} {m : Nat}
    (h2 : 2 ≤ xs.length) (hlt : split xs.length < m) (hmn : m ≤ xs.length) :
    HS.hnode (mth HS (xs.take (split xs.length)))
             (mth HS ((xs.drop (split xs.length)).take (m - split xs.length)))
      = mth HS (xs.take m) := by
  have hstab : split m = split xs.length := split_stable hlt hmn
  have hkpos : 1 ≤ split xs.length := split_pos h2
  have hml : (xs.take m).length = m := by rw [List.length_take]; omega
  have hm2 : 2 ≤ (xs.take m).length := by rw [hml]; omega
  have e1 : xs.take (split xs.length) = (xs.take m).take (split xs.length) := by
    rw [List.take_take]; congr 1; omega
  have e2 : (xs.drop (split xs.length)).take (m - split xs.length)
      = (xs.take m).drop (split xs.length) :=
    (List.drop_take m (split xs.length) xs).symm
  rw [mth_split HS hm2, hml, hstab, e1, e2]

/-! ### The honest prover -/

/-- Honest consistency-proof generator between old size `m` and the tree `xs`
(`n = xs.length`), emitted root-first. -/
def consProof (HS : HashScheme Leaf H) (m : Nat) : List Leaf → List H
  | xs =>
    if h2 : 2 ≤ xs.length then
      if m = xs.length then [mth HS xs]
      else if m ≤ split xs.length then
        mth HS (xs.drop (split xs.length)) :: consProof HS m (xs.take (split xs.length))
      else
        mth HS (xs.take (split xs.length))
          :: consProof HS (m - split xs.length) (xs.drop (split xs.length))
    else
      if m = xs.length then [mth HS xs] else []
termination_by xs => xs.length
decreasing_by
  · simp only [List.length_take]
    exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (split_lt h2)
  · simp only [List.length_drop]
    exact Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) (split_lt h2)) (split_pos h2)

theorem consProof_eq_len (HS : HashScheme Leaf H) (m : Nat) {xs : List Leaf}
    (h : m = xs.length) : consProof HS m xs = [mth HS xs] := by
  rw [consProof]
  by_cases h2 : 2 ≤ xs.length
  · simp only [dif_pos h2, if_pos h]
  · simp only [dif_neg h2, if_pos h]

theorem consProof_le (HS : HashScheme Leaf H) (m : Nat) {xs : List Leaf}
    (hne : m ≠ xs.length) (h2 : 2 ≤ xs.length) (hle : m ≤ split xs.length) :
    consProof HS m xs
      = mth HS (xs.drop (split xs.length)) :: consProof HS m (xs.take (split xs.length)) := by
  rw [consProof]; simp only [dif_pos h2, if_neg hne, if_pos hle]

theorem consProof_gt (HS : HashScheme Leaf H) (m : Nat) {xs : List Leaf}
    (hne : m ≠ xs.length) (h2 : 2 ≤ xs.length) (hgt : ¬ m ≤ split xs.length) :
    consProof HS m xs
      = mth HS (xs.take (split xs.length))
          :: consProof HS (m - split xs.length) (xs.drop (split xs.length)) := by
  rw [consProof]; simp only [dif_pos h2, if_neg hne, if_neg hgt]

/-! ### The verifier core -/

/-- Verifier core: from the proof and the sizes `(m, n)`, recompute both the old
head and the new head, returning them with the unconsumed proof suffix (or
`none` on a malformed proof). -/
def consRec (HS : HashScheme Leaf H) (m n : Nat) (proof : List H) :
    Option ((H × H) × List H) :=
  if h2 : 2 ≤ n then
    if m = n then
      match proof with
      | R :: rest => some ((R, R), rest)
      | [] => none
    else if m ≤ split n then
      match proof with
      | nR :: rest0 =>
        match consRec HS m (split n) rest0 with
        | some ((oL, nL), rest1) => some ((oL, HS.hnode nL nR), rest1)
        | none => none
      | [] => none
    else
      match proof with
      | L :: rest0 =>
        match consRec HS (m - split n) (n - split n) rest0 with
        | some ((oR, nR), rest1) => some ((HS.hnode L oR, HS.hnode L nR), rest1)
        | none => none
      | [] => none
  else
    if m = n then
      match proof with
      | R :: rest => some ((R, R), rest)
      | [] => none
    else none
termination_by n
decreasing_by
  · exact split_lt h2
  · exact Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) (split_lt h2)) (split_pos h2)

theorem consRec_eq_cons (HS : HashScheme Leaf H) (m n : Nat) (h : m = n)
    (R : H) (rest : List H) : consRec HS m n (R :: rest) = some ((R, R), rest) := by
  rw [consRec.eq_def]
  by_cases h2 : 2 ≤ n
  · simp only [dif_pos h2, if_pos h]
  · simp only [dif_neg h2, if_pos h]

theorem consRec_eq_nil (HS : HashScheme Leaf H) (m n : Nat) (h : m = n) :
    consRec HS m n [] = none := by
  rw [consRec.eq_def]
  by_cases h2 : 2 ≤ n
  · simp only [dif_pos h2, if_pos h]
  · simp only [dif_neg h2, if_pos h]

theorem consRec_le_cons (HS : HashScheme Leaf H) (m n : Nat) (hne : m ≠ n)
    (h2 : 2 ≤ n) (hle : m ≤ split n) (nR : H) (rest0 : List H) :
    consRec HS m n (nR :: rest0) =
      (match consRec HS m (split n) rest0 with
       | some ((oL, nL), rest1) => some ((oL, HS.hnode nL nR), rest1)
       | none => none) := by
  rw [consRec.eq_def]; simp only [dif_pos h2, if_neg hne, if_pos hle]

theorem consRec_le_nil (HS : HashScheme Leaf H) (m n : Nat) (hne : m ≠ n)
    (h2 : 2 ≤ n) (hle : m ≤ split n) : consRec HS m n [] = none := by
  rw [consRec.eq_def]; simp only [dif_pos h2, if_neg hne, if_pos hle]

theorem consRec_gt_cons (HS : HashScheme Leaf H) (m n : Nat) (hne : m ≠ n)
    (h2 : 2 ≤ n) (hgt : ¬ m ≤ split n) (L : H) (rest0 : List H) :
    consRec HS m n (L :: rest0) =
      (match consRec HS (m - split n) (n - split n) rest0 with
       | some ((oR, nR), rest1) => some ((HS.hnode L oR, HS.hnode L nR), rest1)
       | none => none) := by
  rw [consRec.eq_def]; simp only [dif_pos h2, if_neg hne, if_neg hgt]

theorem consRec_gt_nil (HS : HashScheme Leaf H) (m n : Nat) (hne : m ≠ n)
    (h2 : 2 ≤ n) (hgt : ¬ m ≤ split n) : consRec HS m n [] = none := by
  rw [consRec.eq_def]; simp only [dif_pos h2, if_neg hne, if_neg hgt]

/-! ### Property (2): completeness -/

/-- Completeness core: `consRec` applied to the honest proof recomputes the
genuine old head `mth (xs.take m)` and new head `mth xs`, consuming the proof
exactly. -/
theorem consProof_complete (HS : HashScheme Leaf H) :
    ∀ (n : Nat) (xs : List Leaf) (m : Nat),
      xs.length = n → 1 ≤ m → m ≤ n →
      consRec HS m n (consProof HS m xs) = some ((mth HS (xs.take m), mth HS xs), []) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs m hn hm1 hmn
    subst hn
    by_cases hmeqn : m = xs.length
    · rw [consProof_eq_len HS m hmeqn, consRec_eq_cons HS m xs.length hmeqn,
          List.take_of_length_le (by omega)]
    · have hxlen2 : 2 ≤ xs.length := by omega
      by_cases hle : m ≤ split xs.length
      · rw [consProof_le HS m hmeqn hxlen2 hle,
            consRec_le_cons HS m xs.length hmeqn hxlen2 hle]
        have htlen : (xs.take (split xs.length)).length = split xs.length := by
          rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt (split_lt hxlen2))
        have hrec := ih (split xs.length) (split_lt hxlen2) (xs.take (split xs.length)) m
          htlen hm1 (by rw [htlen] at *; exact hle)
        have htk : (xs.take (split xs.length)).take m = xs.take m := by
          rw [List.take_take]; congr 1; omega
        simp only [hrec, htk, ← mth_split HS hxlen2]
      · rw [consProof_gt HS m hmeqn hxlen2 hle,
            consRec_gt_cons HS m xs.length hmeqn hxlen2 hle]
        have hkpos : 1 ≤ split xs.length := split_pos hxlen2
        have hgt' : split xs.length < m := by omega
        have hdlen : (xs.drop (split xs.length)).length = xs.length - split xs.length :=
          List.length_drop _ _
        have hrec := ih (xs.length - split xs.length) (by omega)
          (xs.drop (split xs.length)) (m - split xs.length) hdlen (by omega) (by omega)
        simp only [hrec, oldRoot_split HS hxlen2 hgt' hmn, ← mth_split HS hxlen2]

/-! ### Property (2): soundness (append-only) -/

/-- Soundness core, stated for an **arbitrary** proof: if `consRec` recomputes a
new head equal to the real head `mth xs`, then the recomputed old head is forced
to be the genuine size-`m` prefix head.  History cannot be rewritten.  Spends
`hnode_inj` at each level and `oldRoot_split`/`split_stable` at the frontier. -/
theorem consRec_sound (HS : HashScheme Leaf H) :
    ∀ (n : Nat) (xs : List Leaf) (m : Nat) (proof : List H) (o nw : H) (rest : List H),
      xs.length = n → 1 ≤ m → m ≤ n →
      consRec HS m n proof = some ((o, nw), rest) →
      nw = mth HS xs →
      o = mth HS (xs.take m) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs m proof o nw rest hn hm1 hmn hcons hnw
    subst hn
    by_cases hmeqn : m = xs.length
    · cases proof with
      | nil => rw [consRec_eq_nil HS m xs.length hmeqn] at hcons; simp at hcons
      | cons R rest' =>
        rw [consRec_eq_cons HS m xs.length hmeqn] at hcons
        simp only [Option.some.injEq, Prod.mk.injEq] at hcons
        obtain ⟨⟨hRo, hRnw⟩, _⟩ := hcons
        rw [List.take_of_length_le (by omega), ← hRo, hRnw]; exact hnw
    · have hxlen2 : 2 ≤ xs.length := by omega
      have hxs_split : mth HS xs
          = HS.hnode (mth HS (xs.take (split xs.length))) (mth HS (xs.drop (split xs.length))) :=
        mth_split HS hxlen2
      by_cases hle : m ≤ split xs.length
      · cases proof with
        | nil => rw [consRec_le_nil HS m xs.length hmeqn hxlen2 hle] at hcons; simp at hcons
        | cons nR rest0 =>
          rw [consRec_le_cons HS m xs.length hmeqn hxlen2 hle nR rest0] at hcons
          cases hcr : consRec HS m (split xs.length) rest0 with
          | none => rw [hcr] at hcons; simp at hcons
          | some val =>
            obtain ⟨⟨oL, nL⟩, rest1⟩ := val
            rw [hcr] at hcons
            simp only [Option.some.injEq, Prod.mk.injEq] at hcons
            obtain ⟨⟨hoL, hnwv⟩, _⟩ := hcons
            rw [hnw, hxs_split] at hnwv
            obtain ⟨hnL, _hnR⟩ := HS.hnode_inj hnwv
            have htlen : (xs.take (split xs.length)).length = split xs.length := by
              rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt (split_lt hxlen2))
            have hget := ih (split xs.length) (split_lt hxlen2) (xs.take (split xs.length)) m
              rest0 oL nL rest1 htlen hm1 hle hcr hnL
            have htk : (xs.take (split xs.length)).take m = xs.take m := by
              rw [List.take_take]; congr 1; omega
            rw [← hoL, hget, htk]
      · cases proof with
        | nil => rw [consRec_gt_nil HS m xs.length hmeqn hxlen2 hle] at hcons; simp at hcons
        | cons L rest0 =>
          rw [consRec_gt_cons HS m xs.length hmeqn hxlen2 hle L rest0] at hcons
          cases hcr : consRec HS (m - split xs.length) (xs.length - split xs.length) rest0 with
          | none => rw [hcr] at hcons; simp at hcons
          | some val =>
            obtain ⟨⟨oR, nR⟩, rest1⟩ := val
            rw [hcr] at hcons
            simp only [Option.some.injEq, Prod.mk.injEq] at hcons
            obtain ⟨⟨hoo, hnwv⟩, _⟩ := hcons
            rw [hnw, hxs_split] at hnwv
            obtain ⟨hL, hnR⟩ := HS.hnode_inj hnwv
            have hkpos : 1 ≤ split xs.length := split_pos hxlen2
            have hgt' : split xs.length < m := by omega
            have hdlen : (xs.drop (split xs.length)).length = xs.length - split xs.length :=
              List.length_drop _ _
            have hget := ih (xs.length - split xs.length) (by omega)
              (xs.drop (split xs.length)) (m - split xs.length) rest0 oR nR rest1
              hdlen (by omega) (by omega) hcr hnR
            rw [← hoo, hL, hget, oldRoot_split HS hxlen2 hgt' hmn]

/-! ### The `Bool` verifier and Theorem (2) -/

/-- `Bool` consistency verifier: recompute both heads from the proof, compare to
the supplied old/new heads, and require the proof fully consumed. -/
def verifyConsistency (HS : HashScheme Leaf H) [DecidableEq H]
    (m n : Nat) (oldRoot newRoot : H) (proof : List H) : Bool :=
  if m = 0 then false
  else if n < m then false
  else if m = n then proof.isEmpty && decide (oldRoot = newRoot)
  else
    match consRec HS m n proof with
    | some ((o, nw), rest) => rest.isEmpty && decide (o = oldRoot) && decide (nw = newRoot)
    | none => false

/-- The honest top-level proof: empty when `m = n` (the old head equals the new
head, nothing to prove), otherwise the `consProof` frontier. -/
def consistencyProof (HS : HashScheme Leaf H) (m : Nat) (xs : List Leaf) : List H :=
  if m = xs.length then [] else consProof HS m xs

/-- Completeness (`←` of theorem 2): the honest proof against the genuine old and
new heads verifies. -/
theorem consistency_complete (HS : HashScheme Leaf H) [DecidableEq H]
    {xs : List Leaf} {m : Nat} (hm1 : 1 ≤ m) (hmn : m ≤ xs.length) :
    verifyConsistency HS m xs.length (mth HS (xs.take m)) (mth HS xs)
        (consistencyProof HS m xs) = true := by
  by_cases hmeqn : m = xs.length
  · have hproof : consistencyProof HS m xs = [] := by
      unfold consistencyProof; simp [hmeqn]
    rw [hproof]
    unfold verifyConsistency
    rw [if_neg (by omega : ¬ m = 0), if_neg (by omega : ¬ xs.length < m), if_pos hmeqn,
        List.take_of_length_le (by omega)]
    simp
  · have hproof : consistencyProof HS m xs = consProof HS m xs := by
      unfold consistencyProof; simp [hmeqn]
    rw [hproof]
    unfold verifyConsistency
    rw [if_neg (by omega : ¬ m = 0), if_neg (by omega : ¬ xs.length < m), if_neg hmeqn,
        consProof_complete HS xs.length xs m rfl hm1 hmn]
    simp

/-- Soundness (`→` of theorem 2): any accepted proof against the real new head
forces the claimed old head to be the genuine size-`m` prefix head. -/
theorem consistency_sound (HS : HashScheme Leaf H) [DecidableEq H]
    {n : Nat} {xs : List Leaf} {m : Nat} {oldRoot : H} {proof : List H}
    (hn : xs.length = n) (hm1 : 1 ≤ m)
    (hv : verifyConsistency HS m n oldRoot (mth HS xs) proof = true) :
    oldRoot = mth HS (xs.take m) := by
  subst hn
  unfold verifyConsistency at hv
  rw [if_neg (by omega : ¬ m = 0)] at hv
  by_cases hnm : xs.length < m
  · rw [if_pos hnm] at hv; simp at hv
  · rw [if_neg hnm] at hv
    by_cases hmeqn : m = xs.length
    · rw [if_pos hmeqn] at hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨_, hor⟩ := hv
      rw [hor, List.take_of_length_le (by omega)]
    · rw [if_neg hmeqn] at hv
      cases hcr : consRec HS m xs.length proof with
      | none => rw [hcr] at hv; simp at hv
      | some val =>
        obtain ⟨⟨o, nw⟩, rest⟩ := val
        rw [hcr] at hv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨⟨_, ho⟩, hnwv⟩ := hv
        have := consRec_sound HS xs.length xs m proof o nw rest rfl hm1 (by omega) hcr hnwv
        rw [← ho, this]

/-- **Theorem (2): append-only / consistency.**  Against the real size-`n` head,
the honest consistency proof verifies *iff* the claimed old head is the genuine
head of the size-`m` prefix `xs.take m` — i.e. the log never rewrites history. -/
theorem consistency_iff (HS : HashScheme Leaf H) [DecidableEq H]
    {xs : List Leaf} {m : Nat} {oldRoot : H} (hm1 : 1 ≤ m) (hmn : m ≤ xs.length) :
    verifyConsistency HS m xs.length oldRoot (mth HS xs) (consistencyProof HS m xs) = true
      ↔ oldRoot = mth HS (xs.take m) := by
  constructor
  · intro hv
    exact consistency_sound HS rfl hm1 hv
  · intro hold
    rw [hold]
    exact consistency_complete HS hm1 hmn

/-! ### Property (4): verification is total -/

/-- Consistency verification is a total, decidable predicate. -/
theorem verifyConsistency_total (HS : HashScheme Leaf H) [DecidableEq H]
    (m n : Nat) (oldRoot newRoot : H) (proof : List H) :
    verifyConsistency HS m n oldRoot newRoot proof = true
      ∨ verifyConsistency HS m n oldRoot newRoot proof = false := by
  cases verifyConsistency HS m n oldRoot newRoot proof <;> simp

end Ct
