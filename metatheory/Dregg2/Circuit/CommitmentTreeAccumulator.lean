/-
# Dregg2.Circuit.CommitmentTreeAccumulator — the DEPLOYED append-only 4-ary Poseidon2
  note-commitment accumulator, AUTHORED IN LEAN (architectural law #1).

## What object this is (and why the existing Lean note model is NOT it)

`commit/src/poseidon2_tree.rs` (`Poseidon2MerkleTree::{append, root, from_leaves}`) is the
position-indexed, append-only, fan-out-4 Poseidon2 Merkle tree the note-commitment set lives in.
Its root is a genuine 4-ary tree over `hash_4_to_1`, with EMPTY_LEAF-padded slots and an
empty-subtree shortcut. That Rust is DEBT (law #1: AIR/accumulator logic is authored in Lean; Rust
only calls into the Lean-emitted object). This module is the faithful Lean author of that object.

The prior Lean "note model" (`RotatedKernelRefinementNotes.noteListRoot`) is a `listDigest` over a
`List Nat` — a ONE-SHOT sponge of the whole list, NOT a position-indexed 4-ary tree. It binds the
kernel `commitments : List Nat` datum (the right thing at the KERNEL layer), but it is a DIFFERENT
object than the deployed accumulator: no positions, no fan-out-4 internal nodes, no EMPTY_LEAF
padding, no incremental append. This module models the DEPLOYED tree exactly.

## The hash floor is CARRIED and REDUCED, never assumed as an axiom

The node compression is the opaque `H : List ℤ → ℤ` (the `gStep`/`listDigest` convention — a 4-element
list into one felt), the Lean stand-in for `hash_4_to_1`. Binding is REDUCED to `H`-collision-resistance
two ways:

  * `root_binds_of_injective` — the `ListCommit`-style reduction to the `compressNInjective H` carrier
    (⚠ that carrier is the ⊤/realizable form, documented FALSE at deployed BabyBear parameters in
    `StateCommit`/`Spike.CommitTreeRegrounded`; kept for the clean reduction, priced there);
  * `root_distinct_extracts_collision` — the HONEST form that assumes NO floor: two leaf sequences that
    DIFFER inside the tree's capacity yet share a root EXHIBIT a genuine `H`-collision (`∃ l ≠ l', H l =
    H l'`). This is the counting-core-consumable reduction (`CommitTreeRegrounded.exists_collision_*`
    shape) — it is honest even where injectivity is false, because it produces a collision rather than
    presupposing none.

## Properties proved

  * `emptyHash_correct` — the DEPLOYED empty-subtree shortcut is SOUND: a node whose whole subtree is
    beyond the populated leaves equals the precomputed `emptyHash` for its level (this is the equality
    between `poseidon2_tree.rs`'s optimized `compute_node_at_level` and this pure recursion).
  * `root_binds_of_injective` / `root_distinct_extracts_collision` — root binds the padded leaf
    sequence (reduced to the `H` floor, per above).
  * `nodeAt_congr` + `append_offpath_unchanged` — the INCREMENTAL-APPEND lemma: appending at position
    `p = leaves.length` changes the root only along the single root-to-leaf path whose windows contain
    `p`; every off-path node is unchanged.
  * `append_length` — append is GENUINELY ADDITIVE (length grows by one, never idempotent). Exactly-once
    is NOT claimed here: dedup/no-double-insert is the finalization/nullifier layer's job
    (`Exec.NullifierAccumulator`), tracked separately.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.ListCommit

namespace Dregg2.Circuit.CommitmentTreeAccumulator

open Dregg2.Circuit.StateCommit (compressNInjective)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the deployed tree's data: EMPTY_LEAF sentinel, padded leaf lookup, node/root. -/

/-- **`EMPTY_LEAF`** — the domain-separated empty-slot sentinel, `= 0x0DEAD1EF` exactly as
`poseidon2_tree.rs::EMPTY_LEAF = BabyBear(0x0DEAD1EF)`. A fixed non-zero constant so an empty slot is
distinguishable from a legitimate zero-valued leaf. -/
def EMPTY_LEAF : ℤ := 233492975  -- 0x0DEAD1EF

/-- **`leafAt leaves i`** — the leaf at position `i`, or `EMPTY_LEAF` out of bounds. The Lean image of
Rust `get_leaf` (`if i < len then leaves[i] else EMPTY_LEAF`). -/
def leafAt (leaves : List ℤ) (i : Nat) : ℤ := (leaves[i]?).getD EMPTY_LEAF

/-- **`emptyHash H level`** — the precomputed hash of an all-empty subtree of height `level` (Rust
`EMPTY_HASHES`): level 0 is `EMPTY_LEAF`, level `k+1` hashes four copies of level `k`. -/
def emptyHash (H : List ℤ → ℤ) : Nat → ℤ
  | 0 => EMPTY_LEAF
  | level+1 => H [emptyHash H level, emptyHash H level, emptyHash H level, emptyHash H level]

/-- **`nodeAt H leaves level index`** — the value of the node at (`level`, `index`), the PURE 4-ary
recursion (no empty-subtree shortcut): a level-0 node is the padded leaf; a level-`k+1` node is `H` of
its four children at level `k` (indices `4·index .. 4·index+3`). This is Rust
`compute_node_at_level` WITHOUT the `first_leaf >= len` optimization; `emptyHash_correct` proves the
optimization equals this. -/
def nodeAt (H : List ℤ → ℤ) (leaves : List ℤ) : Nat → Nat → ℤ
  | 0, index => leafAt leaves index
  | level+1, index =>
      H [ nodeAt H leaves level (4*index),
          nodeAt H leaves level (4*index+1),
          nodeAt H leaves level (4*index+2),
          nodeAt H leaves level (4*index+3) ]

/-- **`root H depth leaves`** — the tree root: the node at the apex (`level = depth`, `index = 0`). The
Lean image of Rust `Poseidon2MerkleTree::root` (= `compute_node_at_level(depth, 0)`). -/
def root (H : List ℤ → ℤ) (depth : Nat) (leaves : List ℤ) : ℤ := nodeAt H leaves depth 0

/-- **`append leaves cm`** — append a commitment at the next position (`= leaves.length`). Genuinely
additive; the Lean image of Rust `append` (`position = len; leaves.push(leaf)`). -/
def append (leaves : List ℤ) (cm : ℤ) : List ℤ := leaves ++ [cm]

/-! ## §1 — the padded-leaf lookup lemmas (the append/out-of-bounds algebra). -/

/-- Out of bounds reads the sentinel. -/
theorem leafAt_oob (leaves : List ℤ) (i : Nat) (h : leaves.length ≤ i) :
    leafAt leaves i = EMPTY_LEAF := by
  unfold leafAt
  rw [List.getElem?_eq_none h]
  rfl

/-- The slot AT the current length is empty (this is what append fills). -/
theorem leafAt_len_empty (leaves : List ℤ) : leafAt leaves leaves.length = EMPTY_LEAF :=
  leafAt_oob leaves leaves.length (le_refl _)

/-- Append leaves the in-range leaves untouched. -/
theorem append_leafAt_lt (leaves : List ℤ) (cm : ℤ) (i : Nat) (h : i < leaves.length) :
    leafAt (append leaves cm) i = leafAt leaves i := by
  unfold leafAt append
  rw [List.getElem?_append_left h]

/-- Append fills exactly position `leaves.length` with `cm`. -/
theorem append_leafAt_len (leaves : List ℤ) (cm : ℤ) :
    leafAt (append leaves cm) leaves.length = cm := by
  unfold leafAt append
  rw [List.getElem?_append_right (le_refl _)]
  simp

/-- Append changes NO position other than `leaves.length` (above it stays sentinel both sides). -/
theorem append_leafAt_gt (leaves : List ℤ) (cm : ℤ) (i : Nat) (h : leaves.length < i) :
    leafAt (append leaves cm) i = leafAt leaves i := by
  rw [leafAt_oob leaves i (le_of_lt h),
      leafAt_oob (append leaves cm) i (by simp [append]; omega)]

/-- **`append_length`** — append is GENUINELY ADDITIVE: the length grows by exactly one, so append is
never idempotent. (Exactly-once insertion is the finalization/nullifier layer's job, not the
accumulator's — see `Exec.NullifierAccumulator`.) -/
theorem append_length (leaves : List ℤ) (cm : ℤ) : (append leaves cm).length = leaves.length + 1 := by
  simp [append]

/-! ## §2 — window arithmetic (the 4-ary subtree covered by a node). -/

/-- `4^(level+1) = 4 * 4^level`. -/
private theorem four_pow_succ (level : Nat) : (4:Nat)^(level+1) = 4 * 4^level := by
  rw [pow_succ]; ring

/-- A child `m < 4` of node `index` covers a subrange of node `index`'s window (`4^(level+1)` wide). -/
private theorem window_child_subset (index m p i : Nat) (hm : m < 4)
    (hlo : (4*index+m)*p ≤ i) (hhi : i < (4*index+m+1)*p) :
    index*(4*p) ≤ i ∧ i < (index+1)*(4*p) := by
  refine ⟨?_, ?_⟩
  · calc index*(4*p) = (4*index)*p := by ring
      _ ≤ (4*index+m)*p := Nat.mul_le_mul_right _ (by omega)
      _ ≤ i := hlo
  · calc i < (4*index+m+1)*p := hhi
      _ ≤ (4*index+4)*p := Nat.mul_le_mul_right _ (by omega)
      _ = (index+1)*(4*p) := by ring

/-! ## §3 — the empty-subtree shortcut is SOUND (faithfulness to the deployed optimization). -/

/-- **`emptyHash_correct` — the DEPLOYED empty-subtree shortcut equals the pure recursion.** If the
first leaf under node (`level`, `index`) is at or beyond the populated leaves (`len ≤ index·4^level`,
Rust's `first_leaf >= self.leaves.len()`), the node's value is `emptyHash H level`. So Rust's
`compute_node_at_level` optimization computes exactly this pure recursion — the two agree by
construction. -/
theorem emptyHash_correct (H : List ℤ → ℤ) (leaves : List ℤ) :
    ∀ level index, leaves.length ≤ index * 4^level → nodeAt H leaves level index = emptyHash H level := by
  intro level
  induction level with
  | zero =>
    intro index h
    simp only [pow_zero, mul_one] at h
    simp only [nodeAt, emptyHash]
    exact leafAt_oob leaves index h
  | succ level ih =>
    intro index h
    rw [four_pow_succ] at h
    simp only [nodeAt, emptyHash]
    have hb : leaves.length ≤ 4 * index * 4^level := by
      calc leaves.length ≤ index * (4 * 4^level) := h
        _ = 4 * index * 4^level := by ring
    have e0 : nodeAt H leaves level (4*index) = emptyHash H level := ih (4*index) hb
    have e1 : nodeAt H leaves level (4*index+1) = emptyHash H level :=
      ih (4*index+1) (le_trans hb (by gcongr; omega))
    have e2 : nodeAt H leaves level (4*index+2) = emptyHash H level :=
      ih (4*index+2) (le_trans hb (by gcongr; omega))
    have e3 : nodeAt H leaves level (4*index+3) = emptyHash H level :=
      ih (4*index+3) (le_trans hb (by gcongr; omega))
    rw [e0, e1, e2, e3]

/-- **`root_empty`** — the empty accumulator's root is the all-empty tree hash `emptyHash H depth`
(deterministic; the Rust `empty_tree_has_deterministic_root` fact). -/
theorem root_empty (H : List ℤ → ℤ) (depth : Nat) : root H depth [] = emptyHash H depth := by
  unfold root
  exact emptyHash_correct H [] depth 0 (by simp)

/-! ## §4 — the node-compression splitting lemma from the carried floor. -/

/-- Four-child injectivity from `compressNInjective`: equal node hashes force equal children. -/
theorem hash4_inj (H : List ℤ → ℤ) (hN : compressNInjective H)
    (a b c d a' b' c' d' : ℤ) (h : H [a,b,c,d] = H [a',b',c',d']) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hl : [a,b,c,d] = [a',b',c',d'] := hN _ _ h
  simp only [List.cons.injEq, and_true] at hl
  exact ⟨hl.1, hl.2.1, hl.2.2.1, hl.2.2.2⟩

/-! ## §5 — BINDING: the root binds the padded leaf sequence.

Two forms of the reduction to the `H` floor: the injective carrier (clean, but the ⊤/realizable form)
and the honest collision-EXTRACTION (assumes no floor). -/

/-- **`nodeAt_binds_all` — equal nodes force equal padded leaves across the node's whole window.** From
`compressNInjective H`, `nodeAt xs = nodeAt ys` at (`level`,`index`) forces `leafAt xs = leafAt ys` at
every position `index·4^level + j` for `j < 4^level`. Induction on level; `hash4_inj` splits each level
and the window arithmetic routes each `j` to its child. -/
theorem nodeAt_binds_all (H : List ℤ → ℤ) (hN : compressNInjective H) (xs ys : List ℤ) :
    ∀ level index, nodeAt H xs level index = nodeAt H ys level index →
      ∀ j, j < 4^level → leafAt xs (index*4^level + j) = leafAt ys (index*4^level + j) := by
  intro level
  induction level with
  | zero =>
    intro index heq j hj
    simp only [pow_zero, Nat.lt_one_iff] at hj
    subst hj
    simpa only [nodeAt, pow_zero, mul_one, Nat.add_zero] using heq
  | succ level ih =>
    intro index heq j hj
    simp only [nodeAt] at heq
    obtain ⟨c0, c1, c2, c3⟩ := hash4_inj H hN _ _ _ _ _ _ _ _ heq
    have hp : 0 < (4:Nat)^level := pow_pos (by norm_num) level
    -- decompose j = m * p + r,  m = j / p < 4,  r = j % p < p
    set p := (4:Nat)^level with hpdef
    have hm : j / p < 4 := by
      rw [Nat.div_lt_iff_lt_mul hp, ← four_pow_succ]; exact hj
    have hr : j % p < p := Nat.mod_lt j hp
    -- pick the child m = j/p
    have key : ∀ m, m < 4 → nodeAt H xs level (4*index+m) = nodeAt H ys level (4*index+m) := by
      intro m hmlt
      have hm4 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
      rcases hm4 with rfl|rfl|rfl|rfl
      · exact c0
      · exact c1
      · exact c2
      · exact c3
    have hchild := ih (4*index + j/p) (key (j/p) hm) (j % p) hr
    -- rewrite the child index expression to the parent-relative position
    have hidx : (4*index + j/p)*p + j%p = index*4^(level+1) + j := by
      have hdm : (j/p)*p + j%p = j := by rw [mul_comm]; exact Nat.div_add_mod j p
      have hfp : index*4^(level+1) = 4*index*p := by rw [four_pow_succ, ← hpdef]; ring
      rw [add_mul, hfp]; omega
    rw [hidx] at hchild
    exact hchild

/-- **`root_binds_of_injective` — the root binds the padded leaf function (injective-carrier form).**
Equal roots at `depth` force `leafAt xs = leafAt ys` on the whole capacity `[0, 4^depth)`. The
`ListCommit`-style reduction to the `compressNInjective H` carrier. ⚠ that carrier is the ⊤/realizable
form (FALSE at deployed BabyBear params — `StateCommit`/`CommitTreeRegrounded`); the honest form is
`root_distinct_extracts_collision`. -/
theorem root_binds_of_injective (H : List ℤ → ℤ) (hN : compressNInjective H) (xs ys : List ℤ)
    (depth : Nat) (h : root H depth xs = root H depth ys) :
    ∀ j, j < 4^depth → leafAt xs j = leafAt ys j := by
  intro j hj
  have := nodeAt_binds_all H hN xs ys depth 0 h j hj
  simpa using this

/-- **`nodeAt_distinct_extracts` — a distinguishing leaf under equal nodes EXHIBITS an `H`-collision.**
If two trees agree at node (`level`,`index`) yet their padded leaves differ somewhere in that node's
window, then `H` has a genuine collision (`∃ l ≠ l', H l = H l'`). Assumes NO floor — it PRODUCES the
collision. Induction on level: at each level either the two child-lists already collide (done), or they
are equal and the difference descends into a child. -/
theorem nodeAt_distinct_extracts (H : List ℤ → ℤ) (xs ys : List ℤ) :
    ∀ level index, nodeAt H xs level index = nodeAt H ys level index →
      (∃ j, j < 4^level ∧ leafAt xs (index*4^level + j) ≠ leafAt ys (index*4^level + j)) →
      ∃ l l' : List ℤ, l ≠ l' ∧ H l = H l' := by
  intro level
  induction level with
  | zero =>
    intro index heq hdiff
    obtain ⟨j, hj, hne⟩ := hdiff
    simp only [pow_zero, Nat.lt_one_iff] at hj
    subst hj
    simp only [nodeAt, pow_zero, mul_one, Nat.add_zero] at heq hne
    exact absurd heq hne
  | succ level ih =>
    intro index heq hdiff
    simp only [nodeAt] at heq
    set p := (4:Nat)^level with hpdef
    by_cases hlists :
        ([nodeAt H xs level (4*index), nodeAt H xs level (4*index+1),
          nodeAt H xs level (4*index+2), nodeAt H xs level (4*index+3)] : List ℤ) =
        [nodeAt H ys level (4*index), nodeAt H ys level (4*index+1),
          nodeAt H ys level (4*index+2), nodeAt H ys level (4*index+3)]
    · -- the child-lists are equal: descend into the child holding the difference.
      simp only [List.cons.injEq, and_true] at hlists
      obtain ⟨hc0, hc1, hc2, hc3⟩ := hlists
      obtain ⟨j, hj, hne⟩ := hdiff
      have hp : 0 < p := pow_pos (by norm_num) level
      have hm : j / p < 4 := by
        rw [Nat.div_lt_iff_lt_mul hp, hpdef, ← four_pow_succ]; exact hj
      have hr : j % p < p := Nat.mod_lt j hp
      have key : ∀ m, m < 4 → nodeAt H xs level (4*index+m) = nodeAt H ys level (4*index+m) := by
        intro m hmlt
        have hm4 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
        rcases hm4 with rfl|rfl|rfl|rfl
        · exact hc0
        · exact hc1
        · exact hc2
        · exact hc3
      have hchildeq := key (j/p) hm
      have hidx : (4*index + j/p)*p + j%p = index*4^(level+1) + j := by
        have hdm : (j/p)*p + j%p = j := by rw [mul_comm]; exact Nat.div_add_mod j p
        have hfp : index*4^(level+1) = 4*index*p := by rw [four_pow_succ, ← hpdef]; ring
        rw [add_mul, hfp]; omega
      refine ih (4*index + j/p) hchildeq ⟨j % p, hr, ?_⟩
      rw [hidx]
      exact hne
    · -- the child-lists differ but hash equal: a genuine collision, exhibited.
      exact ⟨_, _, hlists, heq⟩

/-- **`root_distinct_extracts_collision` — THE HONEST BINDING (no floor assumed).** If two leaf
sequences differ somewhere inside the tree's capacity `[0, 4^depth)` yet publish the SAME root, then a
genuine `H`-collision exists. This is what a forged accumulator root must clear: not an assumed
injectivity, but the production of a `hash_4_to_1` collision. Honest even where injectivity is false
(the `CommitTreeRegrounded.exists_collision_*` posture). -/
theorem root_distinct_extracts_collision (H : List ℤ → ℤ) (xs ys : List ℤ) (depth : Nat)
    (hroot : root H depth xs = root H depth ys)
    (hdiff : ∃ j, j < 4^depth ∧ leafAt xs j ≠ leafAt ys j) :
    ∃ l l' : List ℤ, l ≠ l' ∧ H l = H l' := by
  obtain ⟨j, hj, hne⟩ := hdiff
  refine nodeAt_distinct_extracts H xs ys depth 0 hroot ⟨j, hj, ?_⟩
  simpa using hne

/-! ## §6 — the INCREMENTAL-APPEND lemma: append touches only one root-to-leaf path. -/

/-- **`nodeAt_congr` — node locality.** A node's value depends only on the leaves in its window: if
`xs` and `ys` agree on `[index·4^level, (index+1)·4^level)` then their nodes are equal. (The
completeness dual of `nodeAt_binds_all`; no floor needed.) -/
theorem nodeAt_congr (H : List ℤ → ℤ) (xs ys : List ℤ) :
    ∀ level index,
      (∀ i, index*4^level ≤ i → i < (index+1)*4^level → leafAt xs i = leafAt ys i) →
      nodeAt H xs level index = nodeAt H ys level index := by
  intro level
  induction level with
  | zero =>
    intro index hcong
    simp only [nodeAt]
    exact hcong index (by simp) (by simp)
  | succ level ih =>
    intro index hcong
    simp only [nodeAt]
    rw [four_pow_succ] at hcong
    have hchild : ∀ m, m < 4 → nodeAt H xs level (4*index+m) = nodeAt H ys level (4*index+m) := by
      intro m hm
      refine ih (4*index+m) (fun i hlo hhi => ?_)
      obtain ⟨hlo', hhi'⟩ := window_child_subset index m (4^level) i hm hlo hhi
      exact hcong i hlo' hhi'
    have g0 := hchild 0 (by norm_num)
    have g1 := hchild 1 (by norm_num)
    have g2 := hchild 2 (by norm_num)
    have g3 := hchild 3 (by norm_num)
    simp only [Nat.add_zero] at g0
    rw [g0, g1, g2, g3]

/-- **`append_offpath_unchanged` — THE INCREMENTAL-APPEND LEMMA.** A node whose window does NOT contain
the append position `p = leaves.length` is UNCHANGED by the append. Hence `append` recomputes the root
only along the single root-to-leaf path whose windows contain `p`; every off-path subtree root is
reused (exactly the incremental structure `poseidon2_tree.rs` relies on when it invalidates only the
cached root). -/
theorem append_offpath_unchanged (H : List ℤ → ℤ) (leaves : List ℤ) (cm : ℤ) (level index : Nat)
    (hoff : ¬ (index*4^level ≤ leaves.length ∧ leaves.length < (index+1)*4^level)) :
    nodeAt H (append leaves cm) level index = nodeAt H leaves level index := by
  refine nodeAt_congr H (append leaves cm) leaves level index (fun i hlo hhi => ?_)
  rcases lt_trichotomy i leaves.length with hlt | heq | hgt
  · exact append_leafAt_lt leaves cm i hlt
  · exact absurd ⟨heq ▸ hlo, heq ▸ hhi⟩ hoff
  · exact append_leafAt_gt leaves cm i hgt

/-! ## §7 — NON-VACUITY: a concrete injective toy hash, golden roots, anti-ghost teeth.

`cNC` is a positional Horner sponge (NOT `List.sum` — order- and position-sensitive), the same shape
`ListCommit`/`RotatedKernelRefinementNotes` use for their non-vacuity carriers. The golden roots pin
the tree's SHAPE (fan-out-4 + position indexing + EMPTY_LEAF padding) so a Rust differential over the
SAME toy reproduces these exact integers (see `commit/tests/`), and so a `root := 0` / `List.sum` stub
would fail every guard below. -/

private def cNC : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

-- The empty accumulator's root is the all-empty-tree hash (deterministic), and equals the pure
-- recursion via the shortcut (`emptyHash_correct` / `root_empty`, here DECIDED on the toy).
#guard decide (root cNC 2 [] = emptyHash cNC 2)

-- GOLDEN roots (fan-out-4, depth 2 = 16-leaf capacity). Pinned so a Rust reference over the same toy
-- reproduces them: the cross-language structural cross-check of the tree shape.
#guard decide (root cNC 2 [] = (237497732899559001643131668920985294316773284 : ℤ))
#guard decide (root cNC 2 [1, 2, 3] = (4000322497796412683283128774162397315672067 : ℤ))
#guard decide (root cNC 2 [1, 2, 3, 4] = (4000322497796412449788056331119080794361850 : ℤ))
#guard decide (root cNC 1 [5] = (4000286494870454427409134 : ℤ))

-- DETERMINISM (Rust `append_is_deterministic`): identical sequences ⇒ identical roots.
#guard decide (root cNC 2 [1, 2, 3] = root cNC 2 [1, 2, 3])

-- APPEND CHANGES THE ROOT (Rust `append_changes_root`): the accumulator is genuinely additive.
#guard decide (root cNC 2 [1, 2, 3] = root cNC 2 (append [1, 2, 3] 4)) == false

-- ANTI-GHOST: a positional MOVE (2 and 3 swapped) changes the root — positions are bound, not just the
-- multiset (a `List.sum` stub would collapse this).
#guard decide (root cNC 2 [1, 2, 3] = root cNC 2 [1, 3, 2]) == false

-- NON-IDEMPOTENCE: appending the SAME commitment twice grows the length by two and changes the root
-- again — exactly-once is NOT the accumulator's job (it is the finalization/nullifier layer's).
#guard decide ((append (append [1] 2) 2).length = 3)
#guard decide (root cNC 2 (append [1] 2) = root cNC 2 (append (append [1] 2) 2)) == false

-- EMPTY_LEAF sentinel is the exact deployed constant (`0x0DEAD1EF`).
#guard decide (EMPTY_LEAF = (233492975 : ℤ))

/-! ### A tiny toy (fits `u64`) for a NUMERIC Rust↔Lean structural cross-check.

Depth 1, `M = 7`, `EMPTY = 3`, so the golden fits a machine word — mirrored byte-for-byte in the Rust
differential test, giving an actual cross-language equality on the tree SHAPE (independent of Poseidon2,
which is opaque here). -/

private def cTiny : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 7 + x) (xs.length : ℤ)
private def EMPTY_TINY : ℤ := 3
private def rootTiny (leaves : List ℤ) : ℤ :=
  -- inline depth-1 root with the tiny sentinel: cTiny of the four padded leaves.
  cTiny [ leaves.getD 0 EMPTY_TINY, leaves.getD 1 EMPTY_TINY,
          leaves.getD 2 EMPTY_TINY, leaves.getD 3 EMPTY_TINY ]

-- rootTiny [5] = cTiny [5,3,3,3] = ((((4)*7+5)*7+3)*7+3)*7+3 = 11490 (mirrored in Rust).
#guard decide (rootTiny [5] = (11490 : ℤ))
#guard decide (rootTiny [] = (10804 : ℤ))          -- all-empty depth-1 (padding-only)
#guard decide (rootTiny [1, 2] = (10069 : ℤ))       -- partial fill: positions 2,3 padded
#guard decide (rootTiny [1, 2] = rootTiny [2, 1]) == false  -- position-sensitive (not a multiset)

/-! ## §8 — axiom-hygiene tripwires. -/

#assert_axioms leafAt_oob
#assert_axioms append_leafAt_lt
#assert_axioms append_leafAt_len
#assert_axioms append_leafAt_gt
#assert_axioms append_length
#assert_axioms emptyHash_correct
#assert_axioms root_empty
#assert_axioms hash4_inj
#assert_axioms nodeAt_binds_all
#assert_axioms root_binds_of_injective
#assert_axioms nodeAt_distinct_extracts
#assert_axioms root_distinct_extracts_collision
#assert_axioms nodeAt_congr
#assert_axioms append_offpath_unchanged

end Dregg2.Circuit.CommitmentTreeAccumulator
