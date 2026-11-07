/-
# Dregg2.Circuit.MapMerkleRoot — the DEPLOYED depth-16 binary-Merkle map root (the faithful map-op commitment).

## What this closes (deliverable 2 — the last real denotation gap)

`DescriptorIR2.opensTo`/`writesTo` (the `MapOp.holdsAt` legs for nullifiers / cells / commitments)
denoted a FLAT SPONGE `Dregg2.Substrate.Heap.root hash h = hash (h.map leafOf)` — a single sponge over
the sorted leaf list. The DEPLOYED map-op (`circuit/src/heap_root.rs`, `circuit/src/descriptor_ir2.rs`
`Ir2Air::MapOps`) commits a **depth-`d` BINARY MERKLE** root instead:

    leaf = hash[addr, value]                       -- ⚠ the PRE-IMT leaf (see below)
    node = hash[left, right]                       -- arity-2 `hash_fact(l, [r])` (the `mix` fold)
    root = the perfect binary fold of the (padded) sorted leaf-digest list, depth `HEAP_TREE_DEPTH = 16`

⚠ ARITY NOTE (gap-#5 IMT, 2026-07): the DEPLOYED `HeapLeaf::digest`/`digest8` is now the LINKED
arity-3 `hash[addr, value, next_addr]` (`IndexedMerkleTree.imtLeafHash`). The FAITHFUL 8-felt §5b
section below models exactly that (`linkHeap` + the arity-3 `heapLeafDigest8`). The SCALAR §2-§5
model in THIS section still folds the historical arity-2 `leafOf` — it is the lane-0/1-felt
DENOTATION layer (`DescriptorIR2.opensTo`/`writesTo`), a NAMED residue of the IMT cutover: its
`writesTo` describes the pre-IMT leaf function, pending the denotation rewire onto `ImtLeaf`.

This module models EXACTLY that binary fold (`mapNode`/`foldLevel`/`perfectRoot`) and proves it
INJECTIVE on the padded leaf-digest vector under the single named Poseidon2-CR floor
(`mapNode_injective` — the `hash[l,r]` 2-to-1 node CR — composed up the depth-`d` perfect tree by
`perfectRoot_injective`). `DescriptorIR2` re-defines `opensTo`/`writesTo` over THIS root (dropping the
flat-sponge `Heap.root`), so `MapOp.holdsAt` — a leg of the deployed `Satisfied2` — denotes the genuine
depth-16 binary-Merkle opening, and the anti-ghost `opensTo_functional`/`writesTo_functional` re-prove
against `perfectRoot_injective` (the binary-tree analog of `Heap.root_injective`), NOT the sponge.

## The model (faithful to `heap_root.rs`)

The deployed `CanonicalHeapTree` pads the sorted leaf list to `2^d` positions with the MIN/MAX
sentinels, then folds bottom-up by `hash_fact(l, [r])`. We model the COMMITMENT of a sorted heap as
`mapRoot hash h := perfectRoot hash d (padDigests d (h.map (leafOf hash)))`: the leaf digests of the
sorted entries, padded to `2^d` with a fixed sentinel digest, folded up the perfect tree. The sorted
discipline (`SortedKeys`) keeps the entry list canonical, so the heap MEANING (`Heap.get`) is unchanged
— only the COMMITMENT FUNCTION moves from the flat sponge to the binary fold. The named CR floor is the
SAME `Poseidon2SpongeCR`, now used at the 2-to-1 node (`mapNode`) and the leaf (`leafOf`).

## ⚑ The exported §5b binding is a REDUCTION on the keyed-ROM floor (07-24)

The §5b `…_binds_or_collides` forms are DEMOTED to exact-Prop skeletons: a bare
`binds ∨ Coll8 (extracted pair)` quantifies over SOLUTIONS, and at deployed BabyBear parameters a
chip collision EXISTS by pigeonhole (`VacuitySweepTeeth.compress8CR_false_babyBear`), so each
disjunction is satisfiable through the collides branch with `binds` never holding.  Cryptographic
hardness quantifies over EFFICIENT ADVERSARIES.  The exported binding of the depth-`d` heap tree
is §RomSuccessor's `heapTreeRoot_binds_rom`: the whole-tree equivocation is a first-class
`RomForgery` at a SAMPLED role-keyed oracle, the extractor RE-WALKS both trees as an oracle
program (`heapFindComp`, `2^(d+2) − 2` queries, additive accounting), and the floor is
`KeyedRomFloor.keyedRom_hard` — the birthday bound, a THEOREM.  The skeletons are RETAINED (not
deleted) because `Deos.DocSubstrateSound` still consumes them one layer up (its two composition
theorems are the next repoint site of this class); the reduction consumes NONE of them.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Crypto
enters ONLY as the named `Poseidon2SpongeCR` floor (at the node + leaf), the SAME floor the whole
commitment tower carries — and, in §RomSuccessor, as the PROVED keyed-ROM floor.
-/
import Dregg2.Substrate.Heap
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.DeployedHeapTree
import Dregg2.Crypto.RomCarrierSites

namespace Dregg2.Circuit.MapMerkleRoot

open Dregg2.Substrate
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR SpongeColl)
open Dregg2.Crypto.SpongeCarrierReduction (IsSpongeColl)
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)

set_option autoImplicit false

/-- The deployed map-tree depth (`heap_root.rs::HEAP_TREE_DEPTH = 16`). The model is generic in `d`;
the deployment instance pins `d = 16`. -/
def HEAP_TREE_DEPTH : Nat := 16

/-! ## §1 — the 2-to-1 binary node (`hash[left, right]`, arity-2 — the deployed `hash_fact(l,[r])`). -/

/-- **`mapNode hash l r`** — the internal node digest, the arity-2 hash over `[left, right]`.
BYTE-IDENTICAL to `heap_root.rs`'s `hash_fact(cur, &[sib])` / `hash_fact(sib, &[cur])` fold node (a
length-2 absorb, NO domain marker — distinct from the cap node's `[FACT_MARK, l, r]`). -/
def mapNode (hash : List ℤ → ℤ) (l r : ℤ) : ℤ := hash [l, r]

/-! ⚑ **`mapNode_injective` IS GONE (2026-07-28).** It peeled the node with `Poseidon2SpongeCR`, which
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE at deployed BabyBear, so it said
nothing where the system stands; and its only consumer was `foldLevel_injective`, also gone. The node
peel now lives in §3b's `foldLevel_binds_or_collides`, which does the same case split and RETURNS the
colliding `[l, r]` pair instead of assuming it away. Nothing is kept in parallel. -/

/-! ## §2 — the perfect-tree fold (a level pairs adjacent digests; `perfectRoot` folds `d` levels). -/

/-- **`foldLevel hash xs`** — one Merkle level: pair adjacent digests by `mapNode`. On a list of even
length `2n` this returns the `n` parent digests, matching `heap_root.rs`'s `chunks(2)` step. -/
def foldLevel (hash : List ℤ → ℤ) : List ℤ → List ℤ
  | [] => []
  | [x] => [x]                                   -- (unreached at even lengths; carry the orphan)
  | l :: r :: rest => mapNode hash l r :: foldLevel hash rest

/-- **`perfectRoot hash d xs`** — fold `d` levels and take the head: the perfect binary-tree root of
the `2^d` leaf digests `xs`. At `d = 0` the root is the single leaf (`xs.headD 0`). -/
def perfectRoot (hash : List ℤ → ℤ) : Nat → List ℤ → ℤ
  | 0,     xs => xs.headD 0
  | d + 1, xs => perfectRoot hash d (foldLevel hash xs)

/-! ## §3 — injectivity of one level, then of the whole fold (the binary `root_injective` analog). -/

/-- One fold level HALVES an even-length list: `(foldLevel hash xs).length = n` when
`xs.length = 2 * n`, matching `heap_root.rs`'s `chunks(2)` step. Inducts on the half-length `n`. -/
theorem foldLevel_length_half (hash : List ℤ → ℤ) :
    ∀ (n : Nat) (xs : List ℤ), xs.length = 2 * n → (foldLevel hash xs).length = n := by
  intro n
  induction n with
  | zero =>
    intro xs hn
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; simp [foldLevel]
  | succ m ih =>
    intro xs hn
    match xs, hn with
    | l :: r :: rest, hn =>
      simp only [List.length_cons] at hn
      have hrest : rest.length = 2 * m := by omega
      simp only [foldLevel, List.length_cons, ih rest hrest]

/-! ### §3-take — ⚑ **THE FOLD IS BLIND ABOVE `2 ^ d`, and that is the ROOT CAUSE of the
over-capacity equivocation.**

Everything the padding lane found downstream — `padTo`'s saturating `Nat` subtraction, `padTo8`'s,
`padVec`'s — is a *symptom*. The disease is here: `perfectRoot hash d` is `d` LOCAL pairings
followed by `headD`, and position `0` after `d` levels descends from positions `0 .. 2^d - 1` and
from NOTHING else. So the fold does not merely tolerate an over-long vector — it CANNOT SEE past
`2 ^ d`, for every hash, with no assumption of any kind.

Stated once, here, rather than re-discovered per padded wrapper. Two consequences, both used:

  * it is the exact reason **truncation is not a repair** for an over-capacity commitment. A
    `take (2 ^ d)` normalisation would change no root the fold ever produces (`perfectRoot_eq_take`
    says it is already the identity on roots), so it buys width honesty and NOTHING else — the two
    over-capacity vectors still meet. Only refusing the input closes it.
  * it upgrades the padding lane's `d = 0` witness to a theorem at EVERY depth, the DEPLOYED
    `MAP_TREE_DEPTH = 16` included (`perfectRoot_over_capacity_collides`). -/

/-- One fold level commutes with truncation: the first `n` parents are exactly the parents of the
first `2 * n` children. Pure combinatorics — the pairing is LOCAL. -/
theorem foldLevel_take (hash : List ℤ → ℤ) :
    ∀ (n : Nat) (xs : List ℤ), foldLevel hash (xs.take (2 * n)) = (foldLevel hash xs).take n := by
  intro n
  induction n with
  | zero => intro xs; simp [foldLevel]
  | succ m ih =>
    intro xs
    match xs with
    | [] => simp [foldLevel]
    | [x] =>
      have h2 : 2 * (m + 1) = m + m + 2 := by ring
      simp [foldLevel, h2]
    | l :: r :: rest =>
      have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [h2, List.take_succ_cons, List.take_succ_cons]
      show mapNode hash l r :: foldLevel hash (rest.take (2 * m))
        = (mapNode hash l r :: foldLevel hash rest).take (m + 1)
      rw [List.take_succ_cons, ih rest]

/-- **★ THE PERFECT FOLD READS ONLY THE FIRST `2 ^ d` LEAVES.** No length hypothesis, no hash
hypothesis: whatever is at position `2 ^ d` or beyond contributes to the root NOTHING, at any
depth. -/
theorem perfectRoot_eq_take (hash : List ℤ → ℤ) :
    ∀ (d : Nat) (xs : List ℤ), perfectRoot hash d xs = perfectRoot hash d (xs.take (2 ^ d)) := by
  intro d
  induction d with
  | zero =>
    intro xs
    cases xs with
    | nil => rfl
    | cons x t => rfl
  | succ d ih =>
    intro xs
    show perfectRoot hash d (foldLevel hash xs)
      = perfectRoot hash d (foldLevel hash (xs.take (2 ^ (d + 1))))
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    rw [hp, foldLevel_take hash (2 ^ d) xs, ← ih (foldLevel hash xs)]

/-- **★★ ABOVE CAPACITY THE FOLD IS NOT BINDING — AT EVERY DEPTH, FOR EVERY HASH, FLOOR-FREE.** Any
two vectors sharing their first `2 ^ d` entries publish ONE root. This is not a collision (nothing
about `hash` is used), not a padding ghost, and no injectivity hypothesis excludes it; it is simply
what `perfectRoot_eq_take` says. `perfectRoot_binds_or_collides` carries `xs.length = 2 ^ d`
precisely to stay out of here, and the padded wrappers' occupancy obligations exist to keep every
caller out of here too. -/
theorem perfectRoot_over_capacity_collides (hash : List ℤ → ℤ) (d : Nat) (xs ys : List ℤ)
    (h : xs.take (2 ^ d) = ys.take (2 ^ d)) : perfectRoot hash d xs = perfectRoot hash d ys := by
  rw [perfectRoot_eq_take hash d xs, perfectRoot_eq_take hash d ys, h]

/-- The equivocation is INHABITED at every depth, and the witnesses are as close as two lists can
be: a full tree, and the same tree with ONE extra leaf that the fold cannot see. ⚠ This is the
statement `over_capacity_roots_collide` was the `d = 0` shadow of. -/
theorem perfectRoot_over_capacity_collides_witness (hash : List ℤ → ℤ) (d : Nat) (xs : List ℤ)
    (hlen : xs.length = 2 ^ d) (x : ℤ) :
    perfectRoot hash d (xs ++ [x]) = perfectRoot hash d xs ∧ xs ++ [x] ≠ xs := by
  refine ⟨perfectRoot_over_capacity_collides hash d _ _ ?_, ?_⟩
  · rw [← hlen, List.take_left, List.take_length]
  · intro hc
    have := congrArg List.length hc
    simp at this

/-! ⚑ **`foldLevel_injective` IS GONE (2026-07-28), and so is the CR-peeled `perfectRoot_injective`
induction.** Both consumed `Poseidon2SpongeCR` — PROVED FALSE at deployed BabyBear — and the level
induction is reproduced VERBATIM in §3b (`foldLevel_binds_or_collides` /
`perfectRoot_binds_or_collides`) with the hypothesis removed and the colliding pair RETURNED.
`perfectRoot_injective` KEEPS ITS NAME below §3b, now riding the extractor. -/

/-! ## §3b — THE SAME FOLD, FLOOR-FREE: a TOTAL collision EXTRACTOR over the ℤ node levels.

`perfectRoot_injective` used to peel the `d` levels with `Poseidon2SpongeCR`, which
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE for every BabyBear-bounded sponge.
So at deployed parameters it said nothing. This section restates the SAME induction with the floor
REMOVED: where the old proof fed an equal-digest pair to the (false) injectivity, this one RETURNS
that pair. The 8-felt half of this file already worked this way (`foldLevel8Find`/`perfectRoot8Find`,
§5b); the ℤ half did not, and every widened map-root consumer routes through it.

⚑ **2026-07-28 — THE NARROW CONE FOLLOWED.** This section used to end "`perfectRoot_injective` is
deliberately LEFT STANDING and still carries the floor … the narrow cone can follow without a second
extractor being written." It has: `perfectRoot_injective` is re-proved from
`perfectRoot_binds_or_collides` at the end of this section, `mapRoot_injective` from `§4`'s
`mapRoot_binds_or_collides`, and the three `opensToMerkle`/`writesToMerkle` anti-ghost teeth from
`§5`'s `OpenColl`/`WriteColl`. No second extractor was written; every one of them resolves to the
pair `perfectRootFind`/`Heap.mapLeafFind` already returned. -/

/-- **`foldLevelFind xs ys`** — scan two digest vectors pairwise and RETURN the first adjacent pair
whose `mapNode` PREIMAGES differ. Decidable throughout (list equality on `ℤ`), total, and
INDEPENDENT of the hash: the extractor is combinatorics, the hash only makes the returned pair a
collision. -/
def foldLevelFind : List ℤ → List ℤ → List ℤ × List ℤ
  | l :: r :: rest, l' :: r' :: rest' =>
      if ([l, r] : List ℤ) = [l', r'] then foldLevelFind rest rest' else ([l, r], [l', r'])
  | _, _ => ([], [])

/-- **THE EXTRACTOR DOES NOT BLOW UP ITS INPUT** — every branch returns two lists of at most two
felts, whatever the level width. The cost model's output-growth obligation, PROVED. -/
theorem foldLevelFind_len_le :
    ∀ xs ys : List ℤ, (foldLevelFind xs ys).1.length + (foldLevelFind xs ys).2.length ≤ 4
  | [], _ => by simp [foldLevelFind]
  | [_], _ => by simp [foldLevelFind]
  | _ :: _ :: _, [] => by simp [foldLevelFind]
  | _ :: _ :: _, [_] => by simp [foldLevelFind]
  | l :: r :: rest, l' :: r' :: rest' => by
      by_cases hp : ([l, r] : List ℤ) = [l', r']
      · rw [foldLevelFind, if_pos hp]; exact foldLevelFind_len_le rest rest'
      · rw [foldLevelFind, if_neg hp]; simp

/-- On EQUAL vectors the extractor bottoms out at the empty pair — so the residual it guards is
DISCHARGEABLE with no hypothesis at all on an honest (non-equivocating) opening. -/
theorem foldLevelFind_self : ∀ xs : List ℤ, foldLevelFind xs xs = ([], [])
  | [] => rfl
  | [_] => rfl
  | l :: r :: rest => by rw [foldLevelFind, if_pos rfl]; exact foldLevelFind_self rest

/-- **ONE MERKLE LEVEL, FLOOR-FREE.** Two equal-length vectors with the same folded level are EITHER
EQUAL, OR `foldLevelFind` names two DISTINCT node preimages on which the deployed sponge genuinely
collides. No hypothesis on `hash`. -/
theorem foldLevel_binds_or_collides (hash : List ℤ → ℤ) :
    ∀ (n : Nat) {xs ys : List ℤ}, xs.length = 2 * n → ys.length = 2 * n →
      foldLevel hash xs = foldLevel hash ys →
      xs = ys ∨ IsSpongeColl hash (foldLevelFind xs ys) := by
  intro n
  induction n with
  | zero =>
    intro xs ys hx hy _
    have hxe : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hye : ys = [] := List.length_eq_zero_iff.mp (by omega)
    exact Or.inl (by rw [hxe, hye])
  | succ m ih =>
    intro xs ys hx hy hfold
    match xs, hx, ys, hy with
    | l :: r :: rest, hx, l' :: r' :: rest', hy =>
      simp only [foldLevel, List.cons.injEq] at hfold
      obtain ⟨hnode, hrest⟩ := hfold
      simp only [List.length_cons] at hx hy
      have hxlen : rest.length = 2 * m := by omega
      have hylen : rest'.length = 2 * m := by omega
      by_cases hpre : ([l, r] : List ℤ) = [l', r']
      · have hl : l = l' := by simpa using (List.cons.inj hpre).1
        have hr : r = r' := by
          have h2 := (List.cons.inj hpre).2
          simpa using (List.cons.inj h2).1
        rcases ih hxlen hylen hrest with hrec | hc
        · exact Or.inl (by rw [hl, hr, hrec])
        · refine Or.inr ?_
          show IsSpongeColl hash (foldLevelFind (l :: r :: rest) (l' :: r' :: rest'))
          rw [foldLevelFind, if_pos hpre]
          exact hc
      · refine Or.inr ?_
        show IsSpongeColl hash (foldLevelFind (l :: r :: rest) (l' :: r' :: rest'))
        rw [foldLevelFind, if_neg hpre]
        exact ⟨hpre, hnode⟩

/-- **`perfectRootFind hash d xs ys`** — descend the `d` levels and name the ONE pair the peel
actually equivocates on: the deepest level whose folds still agree supplies a colliding node pair,
otherwise the recursion carries the deeper level's pair up. -/
def perfectRootFind (hash : List ℤ → ℤ) : Nat → List ℤ → List ℤ → List ℤ × List ℤ
  | 0,     _,  _  => ([], [])
  | d + 1, xs, ys =>
      if foldLevel hash xs = foldLevel hash ys then foldLevelFind xs ys
      else perfectRootFind hash d (foldLevel hash xs) (foldLevel hash ys)

/-- The root extractor inherits the level extractor's output bound. -/
theorem perfectRootFind_len_le (hash : List ℤ → ℤ) :
    ∀ (d : Nat) (xs ys : List ℤ),
      (perfectRootFind hash d xs ys).1.length + (perfectRootFind hash d xs ys).2.length ≤ 4 := by
  intro d
  induction d with
  | zero => intro xs ys; simp [perfectRootFind]
  | succ d ih =>
    intro xs ys
    by_cases hEq : foldLevel hash xs = foldLevel hash ys
    · rw [perfectRootFind, if_pos hEq]; exact foldLevelFind_len_le xs ys
    · rw [perfectRootFind, if_neg hEq]; exact ih _ _

/-- On an EQUAL pair of leaf-digest vectors the root extractor bottoms out at the empty pair. The
DISCHARGEABLE pole: the honest prover, who commits ONE vector, pays nothing. -/
theorem perfectRootFind_self (hash : List ℤ → ℤ) :
    ∀ (d : Nat) (xs : List ℤ), perfectRootFind hash d xs xs = ([], []) := by
  intro d
  induction d with
  | zero => intro xs; rfl
  | succ d _ =>
    intro xs
    rw [perfectRootFind, if_pos rfl]
    exact foldLevelFind_self xs

/-- **★ THE BINARY-MERKLE ROOT BINDS THE LEAF-DIGEST VECTOR, FLOOR-FREE** (the honest replacement of
`perfectRoot_injective`). Two length-`2^d` leaf-digest vectors with EQUAL perfect-tree roots are
EITHER EQUAL, OR the deployed sponge genuinely collides at the ONE pair `perfectRootFind` returns.
NO hypothesis on `hash`: unlike the theorem it replaces, this holds of the deployed 1-felt Poseidon2
sponge. -/
theorem perfectRoot_binds_or_collides (hash : List ℤ → ℤ) :
    ∀ (d : Nat) {xs ys : List ℤ}, xs.length = 2 ^ d → ys.length = 2 ^ d →
      perfectRoot hash d xs = perfectRoot hash d ys →
      xs = ys ∨ IsSpongeColl hash (perfectRootFind hash d xs ys) := by
  intro d
  induction d with
  | zero =>
    intro xs ys hx hy hroot
    rw [pow_zero] at hx hy
    match xs, ys, hx, hy with
    | [x], [y], _, _ =>
      simp only [perfectRoot, List.headD_cons] at hroot
      exact Or.inl (by rw [hroot])
  | succ d ih =>
    intro xs ys hx hy hroot
    simp only [perfectRoot] at hroot
    have hxlen : xs.length = 2 ^ d + 2 ^ d := by rw [hx]; ring
    have hylen : ys.length = 2 ^ d + 2 ^ d := by rw [hy]; ring
    have hfl_x : (foldLevel hash xs).length = 2 ^ d :=
      foldLevel_length_half hash (2 ^ d) xs (by omega)
    have hfl_y : (foldLevel hash ys).length = 2 ^ d :=
      foldLevel_length_half hash (2 ^ d) ys (by omega)
    by_cases hEq : foldLevel hash xs = foldLevel hash ys
    · rcases foldLevel_binds_or_collides hash (2 ^ d) (xs := xs) (ys := ys)
        (by omega) (by omega) hEq with hxy | hc
      · exact Or.inl hxy
      · refine Or.inr ?_
        show IsSpongeColl hash (perfectRootFind hash (d + 1) xs ys)
        rw [perfectRootFind, if_pos hEq]
        exact hc
    · rcases ih hfl_x hfl_y hroot with hfold | hc
      · exact absurd hfold hEq
      · refine Or.inr ?_
        show IsSpongeColl hash (perfectRootFind hash (d + 1) xs ys)
        rw [perfectRootFind, if_neg hEq]
        exact hc

/-! ### §3b teeth — the residual is REFUTABLE, DISCHARGEABLE, and a genuine REFUTATION of the floor.

Three poles, because a side condition that can never fail is `True` in disguise and one that can
never be discharged is a broken keystone rather than a repaired one. -/

/-- **REFUTABLE.** At the constant sponge the extractor really does hand back a colliding pair, so
`¬ IsSpongeColl hash (perfectRootFind …)` is not free. -/
theorem perfectRootColl_refutable :
    IsSpongeColl (fun _ => 0) (perfectRootFind (fun _ => (0 : ℤ)) 1 [1, 2] [3, 4]) := by
  refine ⟨?_, rfl⟩
  decide

/-- **DISCHARGEABLE.** The honest prover — who commits ONE leaf-digest vector — discharges the
residual for EVERY hash, with no cryptographic assumption whatsoever. -/
theorem perfectRootColl_dischargeable (hash : List ℤ → ℤ) (d : Nat) (xs : List ℤ) :
    ¬ IsSpongeColl hash (perfectRootFind hash d xs xs) := by
  rw [perfectRootFind_self hash d xs]
  exact fun hc => hc.1 rfl

/-- **A REFUTATION, NOT A NEW FLOOR.** Exhibiting the residual REFUTES `Poseidon2SpongeCR` outright,
so the port is a strict WEAKENING of the premise it replaces — stated contrapositively, assuming no
floor content, so the ratchet reads it as the tooth it is. -/
theorem perfectRootColl_refutes_poseidon2CR {hash : List ℤ → ℤ} {d : Nat} {xs ys : List ℤ}
    (hc : IsSpongeColl hash (perfectRootFind hash d xs ys)) : ¬ Poseidon2SpongeCR hash :=
  fun hCR => hc.1 (hCR _ _ hc.2)

/-- **⚑ `perfectRoot_injective`, PORTED OFF THE REFUTED FLOOR (2026-07-28) — same name, same
conclusion, a hypothesis the deployed sponge can actually satisfy.** It used to assume
`Poseidon2SpongeCR hash` and peel the `d` levels with it; that premise is FALSE at deployed BabyBear
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so the theorem was VACUOUS exactly where the
prover runs — and so, at 2^d leaf digests into one bounded field, was its CONCLUSION.

It now assumes the DECIDABLE per-instance residual at the ONE pair `perfectRootFind` hands back for
these two vectors. Strictly weaker than the floor (`perfectRootColl_refutes_poseidon2CR`),
dischargeable by anyone who can evaluate the sponge on two ≤2-felt lists
(`perfectRootColl_dischargeable`), and — unlike the floor — SATISFIABLE at deployed parameters.

⚠ ARGUMENT ORDER MOVED: the old form was `perfectRoot_injective hash hCR d hx hy hroot`; the residual
depends on `d`, `xs`, `ys`, so it cannot sit where `hCR` did. -/
theorem perfectRoot_injective (hash : List ℤ → ℤ) (d : Nat) {xs ys : List ℤ}
    (hx : xs.length = 2 ^ d) (hy : ys.length = 2 ^ d)
    (hno : ¬ IsSpongeColl hash (perfectRootFind hash d xs ys))
    (hroot : perfectRoot hash d xs = perfectRoot hash d ys) : xs = ys :=
  (perfectRoot_binds_or_collides hash d hx hy hroot).resolve_right hno

#assert_axioms perfectRoot_injective
#assert_axioms foldLevelFind_len_le
#assert_axioms foldLevelFind_self
#assert_axioms foldLevel_binds_or_collides
#assert_axioms perfectRootFind_len_le
#assert_axioms perfectRootFind_self
#assert_axioms perfectRoot_binds_or_collides
#assert_axioms perfectRootColl_refutable
#assert_axioms perfectRootColl_dischargeable
#assert_axioms perfectRootColl_refutes_poseidon2CR

/-! ## §4 — `mapRoot`: the ARITY-2 map COMMITMENT (the binary fold of the sorted heap's leaf digests).

⚠ This section was titled "the deployed map COMMITMENT". It is not: since 2026-07-12 the deployed tree
folds ARITY-3 IMT leaves over a sparse padded vector — see `mapRoot`'s doc-comment below for the full
correction and the pointer to `MapPaddedDenotation.padImtRoot`.

The sorted heap (`Heap.FeltHeap`, the abstract map MEANING) is committed by folding its leaf-digest list
through the depth-`d` perfect binary tree. The heap MEANING
(`Heap.get`/`Heap.SortedKeys`) is UNCHANGED; only the COMMITMENT FUNCTION moves from the flat sponge
(`Heap.root hash h = hash (h.map leafOf)`) to this binary fold. The deployment pins every heap as the
fixed-depth `2^d`-leaf padded vector; the `RootedAt` relation below carries that `length = 2^d`
discipline so the root BINDS the heap (`mapRoot_injective`). -/

/-- **`mapRoot hash d h`** — the depth-`d` binary-Merkle root of the sorted heap `h`: the perfect-tree
fold of its leaf-digest list `h.map (Heap.leafOf hash)`.

⚠ **THIS DOC-COMMENT CLAIMED "BYTE-IDENTICAL to `heap_root.rs`'s `CanonicalHeapTree::root` (arity-2
`leafOf` leaves…)" AND THAT IS FALSE AT HEAD.** It was true when written and stopped being true on
2026-07-12 (`919b2b0b8d`): `CanonicalHeapTree` became an INDEXED Merkle tree whose leaf is
`hash[addr, value, next_addr]` (`HeapLeaf::preimage`, `HEAP_LEAF_ARITY = 3`, arity 2 → 3 with the
successor pointer inside the digest) over a SPARSE zero-padded `2^d` vector with ONE stored sentinel
(`HEAP_SENTINEL_LEAVES = 1`). Under the CR floor an arity-3 IMT root is NEVER an arity-2 `mapRoot`
(`MapReconcileImtRepoint.imtRoot_ne_mapRoot`), so this is not a drifted constant — it is a DIFFERENT
COMMITMENT over the same logical map. A byte-identity claim to a Rust object is exactly the kind of
claim that must be re-read when that object moves.

`mapRoot` itself is unchanged and still correct as the arity-2 model fold; the DEPLOYED commitment is
`MapPaddedDenotation.padImtRoot sent` (schema `padImtSchema sent`, teeth `padImtTeeth sent`), and the
NODE fold `mapNode` is still shared. Everything below is about `mapRoot`; nothing below should be quoted
as being about `heap_root`. -/
def mapRoot (hash : List ℤ → ℤ) (d : Nat) (h : Heap.FeltHeap) : ℤ :=
  perfectRoot hash d (h.map (Heap.leafOf hash))

/-! ### §4a — THE MAP-ROOT EXTRACTOR and the floor-free binding.

⚑ These two lived in `MapPaddedDenotation` §4c (added there to feed `narrowTeeth`) while
`mapRoot_injective` — one level UP, in this file — still peeled the tree with the refuted floor. That
is the shape the ⚑07-28 sweep was looking for: the cure existed, downstream of the wound, and the
wound was never rewired onto it. They are MOVED here, at the definition of `mapRoot`, and
`MapPaddedDenotation` now `open`s them. Same statements, same proofs, one home. -/

/-- **THE MAP-ROOT EXTRACTOR** — the SINGLE named pair the whole arity-2 heap-root peel hands back.
Run the perfect-tree descent over the two leaf-digest vectors; if it found a genuine collision that
is the answer, otherwise the descent has already forced the two DIGEST VECTORS equal, so the
collision (if any) is at the LEAF absorb and `Heap.mapLeafFind` supplies the pair. Total, decidable,
and independent of anything assumed about `hash`. -/
def mapRootFind (hash : List ℤ → ℤ) (d : Nat) (h₁ h₂ : Heap.FeltHeap) : List ℤ × List ℤ :=
  if SpongeColl hash (perfectRootFind hash d (h₁.map (Heap.leafOf hash))
                                               (h₂.map (Heap.leafOf hash)))
  then perfectRootFind hash d (h₁.map (Heap.leafOf hash)) (h₂.map (Heap.leafOf hash))
  else Heap.mapLeafFind hash h₁ h₂

/-- **`MapRootSpongeColl hash d h₁ h₂` — THE MAP ROOT'S PER-INSTANCE RESIDUAL.** The pair `mapRootFind`
RETURNS on this heap equivocation is a genuine collision of the deployed sponge.

Deliberately NOT `∃ xs ys, xs ≠ ys ∧ hash xs = hash ys` (unconditionally TRUE by pigeonhole at
deployed BabyBear, hence no more content than `True`) and deliberately NOT `∀ p q, ¬ …` (the refuted
floor wearing a disjunction). It is the collision AT THE ONE PAIR IN PLAY, and it is DECIDABLE. -/
def MapRootSpongeColl (hash : List ℤ → ℤ) (d : Nat) (h₁ h₂ : Heap.FeltHeap) : Prop :=
  SpongeColl hash (mapRootFind hash d h₁ h₂)

/-- **★ THE ARITY-2 MAP ROOT BINDS THE WHOLE HEAP, FLOOR-FREE.** Two depth-`d` `2^d`-leaf heaps
publishing the same binary root are EITHER the same heap, OR the deployed sponge genuinely collides
at the ONE pair `mapRootFind` returns. NO hypothesis on `hash`: unlike `mapRoot_injective`'s old
form, this holds of the deployed 1-felt Poseidon2 sponge. -/
theorem mapRoot_binds_or_collides (hash : List ℤ → ℤ) (d : Nat) {h₁ h₂ : Heap.FeltHeap}
    (hl₁ : h₁.length = 2 ^ d) (hl₂ : h₂.length = 2 ^ d)
    (heq : mapRoot hash d h₁ = mapRoot hash d h₂) :
    h₁ = h₂ ∨ MapRootSpongeColl hash d h₁ h₂ := by
  by_cases hif : SpongeColl hash (perfectRootFind hash d (h₁.map (Heap.leafOf hash))
                                                           (h₂.map (Heap.leafOf hash)))
  · refine Or.inr ?_
    show SpongeColl hash (mapRootFind hash d h₁ h₂)
    rw [mapRootFind, if_pos hif]
    exact hif
  · rcases perfectRoot_binds_or_collides hash d (by rw [List.length_map]; exact hl₁)
      (by rw [List.length_map]; exact hl₂) heq with hmap | hc
    · by_cases hne : h₁ = h₂
      · exact Or.inl hne
      · refine Or.inr ?_
        show SpongeColl hash (mapRootFind hash d h₁ h₂)
        rw [mapRootFind, if_neg hif]
        exact Heap.mapLeafFind_spec hash h₁ h₂ hne hmap
    · exact absurd hc hif

/-! ### §4a teeth — the residual is DISCHARGEABLE, REFUTABLE, and a REFUTATION of the floor. -/

/-- **DISCHARGEABLE.** An honest prover commits ONE heap and pays nothing, for EVERY hash, with no
cryptographic assumption whatsoever. Both extractor branches bottom out: the tree descent at the
empty pair (`perfectRootFind_self`), the leaf scan at an equal pair (`Heap.mapLeafFind_self_eq`). -/
theorem mapRootSpongeColl_dischargeable (hash : List ℤ → ℤ) (d : Nat) (h : Heap.FeltHeap) :
    ¬ MapRootSpongeColl hash d h h := by
  have hself : ¬ SpongeColl hash (perfectRootFind hash d (h.map (Heap.leafOf hash))
                                                           (h.map (Heap.leafOf hash))) := by
    rw [perfectRootFind_self hash d]
    exact fun hc => hc.1 rfl
  show ¬ SpongeColl hash (mapRootFind hash d h h)
  rw [mapRootFind, if_neg hself]
  exact fun hc => hc.1 (Heap.mapLeafFind_self_eq hash h)

/-- **REFUTABLE.** At the constant sponge two genuinely different one-leaf heaps publish the same
root and the extractor really does hand back a colliding pair, so `¬ MapRootSpongeColl` is not free. -/
theorem mapRootSpongeColl_refutable :
    MapRootSpongeColl (fun _ => (0 : ℤ)) 0 [(0, 0)] [(0, 1)] := by
  rcases mapRoot_binds_or_collides (fun _ => (0 : ℤ)) 0 (h₁ := [(0, 0)]) (h₂ := [(0, 1)])
    rfl rfl rfl with hne | hc
  · exact absurd hne (by decide)
  · exact hc

/-- **A REFUTATION, NOT A NEW FLOOR.** Exhibiting the residual REFUTES `Poseidon2SpongeCR` outright,
so the port is a strict WEAKENING of the premise it replaces — stated contrapositively, assuming no
floor content, so the ratchet reads it as the tooth it is. -/
theorem mapRootSpongeColl_refutes_poseidon2CR {hash : List ℤ → ℤ} {d : Nat} {h₁ h₂ : Heap.FeltHeap}
    (hc : MapRootSpongeColl hash d h₁ h₂) : ¬ Poseidon2SpongeCR hash :=
  fun hCR => hc.1 (hCR _ _ hc.2)

/-- **⚑ `mapRoot_injective`, PORTED OFF THE REFUTED FLOOR (2026-07-28) — the anti-ghost the DEPLOYED
map-op denotation terminates in.** It assumed `Poseidon2SpongeCR hash`, PROVED FALSE at deployed
BabyBear (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so `DescriptorIR2.opensTo_functional`
/ `writesTo_functional` — the deployed map-op anti-ghost — bottomed out, at their final step, in a
VACUOUS theorem. Its CONCLUSION was empty there too: `2 ^ 16` entries of `ℤ × ℤ` into one BabyBear
felt collide by the same pigeonhole that refutes the premise.

It now assumes the DECIDABLE per-instance residual at the ONE pair `mapRootFind` hands back for these
two heaps. Strictly weaker than the floor (`mapRootSpongeColl_refutes_poseidon2CR`), dischargeable
(`mapRootSpongeColl_dischargeable`), refutable (`mapRootSpongeColl_refutable`), and SATISFIABLE at deployed
parameters where the floor is not.

⚑ HONEST PRICE, stated at the resolution the deployment actually has: this is a ONE-FELT commitment
(`mapNode hash [l, r] : ℤ`, `Heap.leafOf hash [a, v] : ℤ`), so the residual costs a collision search
on a single BabyBear felt — **≈2^15.5 queries, which is a BREAK**, not a security level. The 8-felt
twin (`§5b`'s `mapRoot8` / `MapRootSpongeColl` at `Digest8`) is the ~2^123.5 object. Porting the floor off
does not make the arity-2 model safe; it makes the price VISIBLE instead of assumed away.

⚠ ARGUMENT ORDER MOVED: the old form was `mapRoot_injective hash hCR d hlen₁ hlen₂ h`. -/
theorem mapRoot_injective (hash : List ℤ → ℤ) (d : Nat)
    {h₁ h₂ : Heap.FeltHeap} (hlen₁ : h₁.length = 2 ^ d) (hlen₂ : h₂.length = 2 ^ d)
    (hno : ¬ MapRootSpongeColl hash d h₁ h₂)
    (h : mapRoot hash d h₁ = mapRoot hash d h₂) : h₁ = h₂ :=
  (mapRoot_binds_or_collides hash d hlen₁ hlen₂ h).resolve_right hno

/-! ## §5 — the faithful map OPENING (`opensToMerkle`/`writesToMerkle`) + the re-proved anti-ghost.

The binary-Merkle replacement for `DescriptorIR2.opensTo`/`writesTo`: a depth-`d` `2^d`-leaf sorted heap
behind the binary root reads / writes the abstract map. The `_functional` anti-ghost rides
`§4a`'s `mapRoot_binds_or_collides` — the floor-free binding — NOT the sponge `root_injective` and no
longer any CR floor at all. -/

/-- **`opensToMerkle hash d r k o`** — some depth-`d` `2^d`-leaf sorted heap behind the BINARY-MERKLE
root `r` reads `o` at `k`. The faithful replacement of `DescriptorIR2.opensTo` over the deployed tree. -/
def opensToMerkle (hash : List ℤ → ℤ) (d : Nat) (r k : ℤ) (o : Option ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ h.length = 2 ^ d ∧ mapRoot hash d h = r ∧ Heap.get h k = o

/-- **`writesToMerkle hash d r k v r'`** — some depth-`d` `2^d`-leaf sorted heap behind binary root `r`
produces root `r'` under the sorted insert-or-update of `(k, v)`, with the post-heap still `2^d`-leaf. -/
def writesToMerkle (hash : List ℤ → ℤ) (d : Nat) (r k v r' : ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ h.length = 2 ^ d
    ∧ (Heap.set h k v).length = 2 ^ d
    ∧ mapRoot hash d h = r ∧ r' = mapRoot hash d (Heap.set h k v)

/-! ### §5a — THE OPENING-LEVEL RESIDUAL, at the heaps the two openings ACTUALLY SUPPLY.

⚑ The three teeth below quantify over OPENINGS, not over heaps: `opensToMerkle` hides its witness
behind an `∃`. That is why they could not simply inherit `§4a`'s per-instance residual, and it is
also why no `∀ h₁ h₂, ¬ MapRootSpongeColl …` side condition would do — at a fixed root the set of heaps
with that root is INFINITE, so a `∀`-shaped residual is refuted by exactly the pigeonhole that
refutes the floor. (`MapPaddedDenotation`'s schema-level teeth took the other road: they expose the
witness heaps as arguments. `opensToMerkleS_functional_of_good` then needs `Good hash`, which at
`narrowTeeth` is `Function.Injective hash` — **definitionally `Poseidon2SpongeCR hash`**, i.e. the
same refuted floor under another name. So that road does not reach the deployed statement either.)

What does reach it: NAME the two heaps. `Exists.choose` is canonical here — proof irrelevance makes
`h.choose` a function of the PROPOSITION `opensToMerkle hash d r k o`, not of the proof term — so
`OpenColl` is the collision at the ONE pair `mapRootFind` returns for the two heaps these two
openings supply, and nothing wider. -/

/-- The heap an opening supplies (canonical by proof irrelevance). -/
noncomputable def openHeap {hash : List ℤ → ℤ} {d : Nat} {r k : ℤ} {o : Option ℤ}
    (h : opensToMerkle hash d r k o) : Heap.FeltHeap := h.choose

/-- The heap a write supplies (canonical by proof irrelevance). -/
noncomputable def writeHeap {hash : List ℤ → ℤ} {d : Nat} {r k v r' : ℤ}
    (h : writesToMerkle hash d r k v r') : Heap.FeltHeap := h.choose

/-- **`OpenColl` — the per-instance residual of the OPENING anti-ghost.** The sponge genuinely
collides at the pair `mapRootFind` returns for the two heaps THESE TWO OPENINGS supply. -/
def OpenColl (hash : List ℤ → ℤ) (d : Nat) {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkle hash d r k o₁) (h₂ : opensToMerkle hash d r k o₂) : Prop :=
  MapRootSpongeColl hash d (openHeap h₁) (openHeap h₂)

/-- **`WriteColl` — the per-instance residual of the WRITE anti-ghost.** -/
def WriteColl (hash : List ℤ → ℤ) (d : Nat) {r k v r₁ r₂ : ℤ}
    (h₁ : writesToMerkle hash d r k v r₁) (h₂ : writesToMerkle hash d r k v r₂) : Prop :=
  MapRootSpongeColl hash d (writeHeap h₁) (writeHeap h₂)

/-- **★ BINARY-MERKLE OPENINGS BIND THE READ, FLOOR-FREE.** Two openings of the same root at the same
key EITHER agree, OR the sponge collides at the named pair. NO hypothesis on `hash`. -/
theorem opensToMerkle_binds_or_collides (hash : List ℤ → ℤ) (d : Nat) {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkle hash d r k o₁) (h₂ : opensToMerkle hash d r k o₂) :
    o₁ = o₂ ∨ OpenColl hash d h₁ h₂ := by
  obtain ⟨_, hl₁, hr₁, hg₁⟩ := h₁.choose_spec
  obtain ⟨_, hl₂, hr₂, hg₂⟩ := h₂.choose_spec
  rcases mapRoot_binds_or_collides hash d hl₁ hl₂ (hr₁.trans hr₂.symm) with hm | hc
  · exact Or.inl (by rw [← hg₁, ← hg₂, hm])
  · exact Or.inr hc

/-- **★ BINARY-MERKLE WRITES BIND THE NEW ROOT, FLOOR-FREE.** -/
theorem writesToMerkle_binds_or_collides (hash : List ℤ → ℤ) (d : Nat) {r k v r₁ r₂ : ℤ}
    (h₁ : writesToMerkle hash d r k v r₁) (h₂ : writesToMerkle hash d r k v r₂) :
    r₁ = r₂ ∨ WriteColl hash d h₁ h₂ := by
  obtain ⟨_, hl₁, _, hr₁, he₁⟩ := h₁.choose_spec
  obtain ⟨_, hl₂, _, hr₂, he₂⟩ := h₂.choose_spec
  rcases mapRoot_binds_or_collides hash d hl₁ hl₂ (hr₁.trans hr₂.symm) with hm | hc
  · exact Or.inl (by rw [he₁, he₂, hm])
  · exact Or.inr hc

/-- **DISCHARGEABLE.** One and the same opening never equivocates with itself — for EVERY hash. -/
theorem openColl_dischargeable (hash : List ℤ → ℤ) (d : Nat) {r k : ℤ} {o : Option ℤ}
    (h : opensToMerkle hash d r k o) : ¬ OpenColl hash d h h :=
  mapRootSpongeColl_dischargeable hash d (openHeap h)

/-- **DISCHARGEABLE.** -/
theorem writeColl_dischargeable (hash : List ℤ → ℤ) (d : Nat) {r k v r' : ℤ}
    (h : writesToMerkle hash d r k v r') : ¬ WriteColl hash d h h :=
  mapRootSpongeColl_dischargeable hash d (writeHeap h)

/-- **REFUTABLE.** At the constant sponge one root opens at one key to TWO different values, so
`¬ OpenColl` is not free: the residual is genuinely reachable at the deployed shape of hash. -/
theorem openColl_refutable :
    ∃ (h₁ : opensToMerkle (fun _ => (0 : ℤ)) 0 0 0 (some 0))
      (h₂ : opensToMerkle (fun _ => (0 : ℤ)) 0 0 0 (some 1)),
      OpenColl (fun _ => (0 : ℤ)) 0 h₁ h₂ := by
  have h₁ : opensToMerkle (fun _ => (0 : ℤ)) 0 0 0 (some 0) :=
    ⟨[(0, 0)], by simp [Heap.SortedKeys, Heap.keys], rfl, rfl, rfl⟩
  have h₂ : opensToMerkle (fun _ => (0 : ℤ)) 0 0 0 (some 1) :=
    ⟨[(0, 1)], by simp [Heap.SortedKeys, Heap.keys], rfl, rfl, rfl⟩
  refine ⟨h₁, h₂, ?_⟩
  rcases opensToMerkle_binds_or_collides (fun _ => (0 : ℤ)) 0 h₁ h₂ with hv | hc
  · exact absurd hv (by decide)
  · exact hc

/-- **A REFUTATION, NOT A NEW FLOOR.** -/
theorem openColl_refutes_poseidon2CR {hash : List ℤ → ℤ} {d : Nat} {r k : ℤ} {o₁ o₂ : Option ℤ}
    {h₁ : opensToMerkle hash d r k o₁} {h₂ : opensToMerkle hash d r k o₂}
    (hc : OpenColl hash d h₁ h₂) : ¬ Poseidon2SpongeCR hash :=
  mapRootSpongeColl_refutes_poseidon2CR hc

/-- **A REFUTATION, NOT A NEW FLOOR.** -/
theorem writeColl_refutes_poseidon2CR {hash : List ℤ → ℤ} {d : Nat} {r k v r₁ r₂ : ℤ}
    {h₁ : writesToMerkle hash d r k v r₁} {h₂ : writesToMerkle hash d r k v r₂}
    (hc : WriteColl hash d h₁ h₂) : ¬ Poseidon2SpongeCR hash :=
  mapRootSpongeColl_refutes_poseidon2CR hc

/-- **⚑ Binary-Merkle openings are FUNCTIONAL — PORTED OFF THE REFUTED FLOOR (2026-07-28).** The
binary root + key determine the read, up to the per-instance residual at the two heaps the openings
supply. It used to assume `Poseidon2SpongeCR hash`, false at deployed BabyBear, so this — the
last peel of `DescriptorIR2.opensTo_functional`, the DEPLOYED map-op anti-ghost — was VACUOUS at the
prover's own parameters, and its conclusion was false there besides. -/
theorem opensToMerkle_functional (hash : List ℤ → ℤ) (d : Nat)
    {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkle hash d r k o₁) (h₂ : opensToMerkle hash d r k o₂)
    (hno : ¬ OpenColl hash d h₁ h₂) : o₁ = o₂ :=
  (opensToMerkle_binds_or_collides hash d h₁ h₂).resolve_right hno

/-- Membership and non-membership at the same binary root/key EXCLUDE each other (the nullifier / cap
non-membership tooth, over the deployed tree), up to the same named residual. -/
theorem opensToMerkle_some_excludes_none (hash : List ℤ → ℤ) (d : Nat)
    {r k v : ℤ} (h₁ : opensToMerkle hash d r k (some v)) (h₂ : opensToMerkle hash d r k none)
    (hno : ¬ OpenColl hash d h₁ h₂) : False := by
  have := opensToMerkle_functional hash d h₁ h₂ hno
  simp at this

/-- **⚑ Binary-Merkle writes are FUNCTIONAL — PORTED OFF THE REFUTED FLOOR (2026-07-28).** Binary root
+ key + value determine the new root: the map-op row's `new_root` column cannot be forged, up to the
per-instance residual at the two heaps the writes supply. -/
theorem writesToMerkle_functional (hash : List ℤ → ℤ) (d : Nat)
    {r k v r₁ r₂ : ℤ}
    (h₁ : writesToMerkle hash d r k v r₁) (h₂ : writesToMerkle hash d r k v r₂)
    (hno : ¬ WriteColl hash d h₁ h₂) : r₁ = r₂ :=
  (writesToMerkle_binds_or_collides hash d h₁ h₂).resolve_right hno

/-! ## §5b — THE FAITHFUL 8-felt map denotation (Phase H-HEAP-8): the perfect-tree fold + opening over
`node8` (`Digest8`), the exact twin of §2–§5 but at the deployed ~124-bit width. The historical §2–§5
folded a SINGLE felt per node (`mapNode hash : ℤ → ℤ → ℤ`, ~2^31, below the FRI/STARK ~124-bit floor); the
GENTIAN tooth exhibits a colliding-lane-0 heap pair. This section commits the FULL 8-felt root: nodes ride
`Heap8Scheme.heapNodeOf8` (arity-16 `node8` chip) and leaves `heapLeafDigest8` (`DeployedHeapTree`), NOT
the 1-felt sponge. `MapOp.holdsAt`'s deployed denotation moves onto `opensToMerkle8` / `writesToMerkle8`.

⚑ **BINDING IS EXTRACTED AS DATA, NOT ASSUMED (2026-07-20).** This cascade used to be discharged from
`heapNodeOf8_injective` / `heapLeafDigest8_injective`, which rode the `Heap8Scheme.chip8CR` FIELD —
`Compress8CR chipAbsorb8`, which the deployed chip REFUTES (`VacuitySweepTeeth.compress8CR_false_babyBear`)
and which therefore made `Heap8Scheme` uninhabitable and this whole section VACUOUS. The field is deleted;
every equality below is now a DISJUNCTION `binding ∨ Coll8 chipAbsorb8 (the pair a TOTAL extractor
returned)`. The extractors mirror the proofs exactly: `foldLevel8Find` scans one Merkle level pairwise,
`perfectRoot8Find` descends the levels, `mapLeaf8Find` scans the leaf vector, and `mapRoot8Find` resolves
the two possible collision sites (node vs leaf) into ONE named pair. §5b.S recovers every deleted
statement as the injective special case, so no strength was lost. -/

section Faithful8
open Dregg2.Circuit.DeployedHeapTree.Heap8Scheme (heapLeafDigest8 heapNodeOf8
  heapLeafColl8Find heapNodeColl8Find
  heapLeafDigest8_binds_or_collides heapNodeOf8_binds_or_collides)
open Dregg2.Circuit.DeployedCapTree (Coll8 Compress8CR)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (coll8_refutable_of_injective)

variable (S8 : Heap8Scheme)

/-- The all-zero `Digest8` (off-the-end default for `headD`; never semantically load-bearing on a
length-`2^d` vector). -/
def zeroDigest8 : Digest8 := fun _ => 0

/-- **`foldLevel8 S8 xs`** — one 8-felt Merkle level: pair adjacent `Digest8`s by `heapNodeOf8`. The
`node8` twin of `foldLevel`. -/
def foldLevel8 : List Digest8 → List Digest8
  | [] => []
  | [x] => [x]
  | l :: r :: rest => heapNodeOf8 S8 l r :: foldLevel8 rest

/-- **`perfectRoot8 S8 d xs`** — fold `d` 8-felt levels and take the head: the perfect binary-tree
`node8` root of the `2^d` leaf digests. At `d = 0` the root is the single leaf. -/
def perfectRoot8 : Nat → List Digest8 → Digest8
  | 0,     xs => xs.headD (zeroDigest8)
  | d + 1, xs => perfectRoot8 d (foldLevel8 S8 xs)

/-- One 8-felt fold level HALVES an even-length list (the `node8` twin of `foldLevel_length_half`). -/
theorem foldLevel8_length_half :
    ∀ (n : Nat) (xs : List Digest8), xs.length = 2 * n → (foldLevel8 S8 xs).length = n := by
  intro n
  induction n with
  | zero =>
    intro xs hn
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; simp [foldLevel8]
  | succ m ih =>
    intro xs hn
    match xs, hn with
    | l :: r :: rest, hn =>
      simp only [List.length_cons] at hn
      have hrest : rest.length = 2 * m := by omega
      simp only [foldLevel8, List.length_cons, ih rest hrest]

/-- **The one-level EXTRACTOR** — scan two Merkle levels pairwise and return the first pair of arity-16
`node8` input blocks that is a GENUINE chip collision; if the scan runs out, return the trivially
non-colliding `([], [])` (the spec's terminal cases deliver equality outright and never read it). A
TOTAL function — no `Classical.choice` in the walk. -/
def foldLevel8Find : List Digest8 → List Digest8 → List ℤ × List ℤ
  | l :: r :: rest, l' :: r' :: rest' =>
      if Coll8 S8.chipAbsorb8 (heapNodeColl8Find l r l' r')
      then heapNodeColl8Find l r l' r'
      else foldLevel8Find rest rest'
  | _, _ => ([], [])

/-- **One 8-felt fold level BINDS its input, UNCONDITIONAL** (replaces `foldLevel8_injective`). Equal
folds of equal-length levels EITHER force the levels equal, OR the scan lands on a pair of arity-16
`node8` blocks that genuinely collide, handed back by name. Peels each pair by
`heapNodeOf8_binds_or_collides` — the same peel as before, with the failure branch producing a WITNESS
instead of consuming an injectivity hypothesis the deployed chip refutes. -/
theorem foldLevel8_binds_or_collides :
    ∀ (n : Nat) {xs ys : List Digest8}, xs.length = 2 * n → ys.length = 2 * n →
      foldLevel8 S8 xs = foldLevel8 S8 ys →
      xs = ys ∨ Coll8 S8.chipAbsorb8 (foldLevel8Find S8 xs ys) := by
  intro n
  induction n with
  | zero =>
    intro xs ys hx hy _
    have hxe : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hye : ys = [] := List.length_eq_zero_iff.mp (by omega)
    exact Or.inl (by rw [hxe, hye])
  | succ m ih =>
    intro xs ys hx hy hfold
    match xs, hx, ys, hy with
    | l :: r :: rest, hx, l' :: r' :: rest', hy =>
      simp only [foldLevel8, List.cons.injEq] at hfold
      obtain ⟨hnode, hrest⟩ := hfold
      by_cases hif : Coll8 S8.chipAbsorb8 (heapNodeColl8Find l r l' r')
      · refine Or.inr ?_
        show Coll8 S8.chipAbsorb8 (foldLevel8Find S8 (l :: r :: rest) (l' :: r' :: rest'))
        rw [foldLevel8Find, if_pos hif]
        exact hif
      · rcases heapNodeOf8_binds_or_collides S8 hnode with ⟨hl, hr⟩ | hc
        · simp only [List.length_cons] at hx hy
          have hxlen : rest.length = 2 * m := by omega
          have hylen : rest'.length = 2 * m := by omega
          rcases ih hxlen hylen hrest with htail | hct
          · exact Or.inl (by rw [hl, hr, htail])
          · refine Or.inr ?_
            show Coll8 S8.chipAbsorb8 (foldLevel8Find S8 (l :: r :: rest) (l' :: r' :: rest'))
            rw [foldLevel8Find, if_neg hif]
            exact hct
        · exact absurd hc hif

/-- **The perfect-tree EXTRACTOR** — descend the `d` fold levels; if the deeper walk found a genuine
collision that is the answer, otherwise the deeper levels have already been forced equal and the
collision (if any) is at THIS level, so hand back what the one-level scan returns. TOTAL. -/
def perfectRoot8Find : Nat → List Digest8 → List Digest8 → List ℤ × List ℤ
  | 0,     _,  _  => ([], [])
  | d + 1, xs, ys =>
      if Coll8 S8.chipAbsorb8 (perfectRoot8Find d (foldLevel8 S8 xs) (foldLevel8 S8 ys))
      then perfectRoot8Find d (foldLevel8 S8 xs) (foldLevel8 S8 ys)
      else foldLevel8Find S8 xs ys

/-- **The 8-felt binary-Merkle root BINDS the whole leaf-digest vector, UNCONDITIONAL** (replaces
`perfectRoot8_injective`). Two length-`2^d` `Digest8` lists with EQUAL `node8` roots are EITHER EQUAL,
OR the descent lands on a level whose two arity-16 `node8` blocks genuinely collide. The ~124-bit
statement: a prover cannot republish the same 8-felt root over a different leaf vector without
exhibiting a real collision at the NAMED pair this extractor returns. -/
theorem perfectRoot8_binds_or_collides :
    ∀ (d : Nat) {xs ys : List Digest8}, xs.length = 2 ^ d → ys.length = 2 ^ d →
      perfectRoot8 S8 d xs = perfectRoot8 S8 d ys →
      xs = ys ∨ Coll8 S8.chipAbsorb8 (perfectRoot8Find S8 d xs ys) := by
  intro d
  induction d with
  | zero =>
    intro xs ys hx hy hroot
    rw [pow_zero] at hx hy
    match xs, ys, hx, hy with
    | [x], [y], _, _ =>
      simp only [perfectRoot8, List.headD_cons] at hroot
      exact Or.inl (by rw [hroot])
  | succ d ih =>
    intro xs ys hx hy hroot
    simp only [perfectRoot8] at hroot
    have hfl_x : (foldLevel8 S8 xs).length = 2 ^ d := foldLevel8_length_half S8 (2 ^ d) xs (by omega)
    have hfl_y : (foldLevel8 S8 ys).length = 2 ^ d := foldLevel8_length_half S8 (2 ^ d) ys (by omega)
    by_cases hif : Coll8 S8.chipAbsorb8
        (perfectRoot8Find S8 d (foldLevel8 S8 xs) (foldLevel8 S8 ys))
    · refine Or.inr ?_
      show Coll8 S8.chipAbsorb8 (perfectRoot8Find S8 (d + 1) xs ys)
      rw [perfectRoot8Find, if_pos hif]
      exact hif
    · rcases ih hfl_x hfl_y hroot with hfold | hc
      · rcases foldLevel8_binds_or_collides S8 (2 ^ d) (by omega) (by omega) hfold with hxy | hcl
        · exact Or.inl hxy
        · refine Or.inr ?_
          show Coll8 S8.chipAbsorb8 (perfectRoot8Find S8 (d + 1) xs ys)
          rw [perfectRoot8Find, if_neg hif]
          exact hcl
      · exact absurd hc hif

/-- **The leaf-vector EXTRACTOR** — scan two LINKED leaf lists in step and return the first pair of
arity-3 IMT blocks that is a GENUINE chip collision; `([], [])` (never a collision) if the scan runs
out. TOTAL. -/
def mapLeaf8Find : List (ℤ × ℤ × ℤ) → List (ℤ × ℤ × ℤ) → List ℤ × List ℤ
  | e₁ :: t₁, e₂ :: t₂ =>
      if Coll8 S8.chipAbsorb8 (heapLeafColl8Find e₁ e₂)
      then heapLeafColl8Find e₁ e₂
      else mapLeaf8Find t₁ t₂
  | _, _ => ([], [])

/-- **The `heapLeafDigest8` map BINDS the LINKED leaf list, UNCONDITIONAL** (replaces
`map_leaf8_injective`). Equal 8-felt leaf-digest lists EITHER force the linked entry lists equal — addr,
value, AND the sorted-chain pointer, so the chain cannot be relinked under a fixed digest vector — OR
the scan returns a genuinely colliding pair of arity-3 IMT blocks. -/
theorem map_leaf8_binds_or_collides :
    ∀ (l₁ l₂ : List (ℤ × ℤ × ℤ)),
      l₁.map (heapLeafDigest8 S8) = l₂.map (heapLeafDigest8 S8) →
      l₁ = l₂ ∨ Coll8 S8.chipAbsorb8 (mapLeaf8Find S8 l₁ l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; cases l₂ with
    | nil => exact Or.inl rfl
    | cons hd t => simp at h
  | cons hd₁ t₁ ih =>
    intro l₂ h
    cases l₂ with
    | nil => simp at h
    | cons hd₂ t₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hleaf, htail⟩ := h
      by_cases hif : Coll8 S8.chipAbsorb8 (heapLeafColl8Find hd₁ hd₂)
      · refine Or.inr ?_
        show Coll8 S8.chipAbsorb8 (mapLeaf8Find S8 (hd₁ :: t₁) (hd₂ :: t₂))
        rw [mapLeaf8Find, if_pos hif]
        exact hif
      · rcases heapLeafDigest8_binds_or_collides S8 hleaf with hhd | hc
        · rcases ih t₂ htail with htl | hct
          · exact Or.inl (by rw [hhd, htl])
          · refine Or.inr ?_
            show Coll8 S8.chipAbsorb8 (mapLeaf8Find S8 (hd₁ :: t₁) (hd₂ :: t₂))
            rw [mapLeaf8Find, if_neg hif]
            exact hct
        · exact absurd hc hif

/-- The deployed TERMINAL pointer (`circuit/src/dsl/revocation.rs::SENTINEL_MAX = p − 1 =
2013265920`): the largest linked leaf points at it (the sorted chain's end). -/
def SENTINEL_MAX8 : ℤ := 2013265920

/-- **`linkHeap h`** — the gap-#5 IMT LINKING of a sorted pair-heap: each `(addr, value)` entry gains
the POINTER to its successor's `addr` (the last leaf → `SENTINEL_MAX8`). The model twin of
`heap_root.rs::relink_next_addrs` — the deployed commitment hashes LINKED `(addr, value, next)`
leaves (`HeapLeaf::digest8`, arity 3), while the map MEANING (`Heap.get`/`Heap.set`) stays the pair
list. -/
def linkHeap : Heap.FeltHeap → List (ℤ × ℤ × ℤ)
  | [] => []
  | (a, v) :: rest => (a, v, (rest.head?.map Prod.fst).getD SENTINEL_MAX8) :: linkHeap rest

/-- Dropping the pointers recovers the pair-heap: `linkHeap` loses nothing. -/
theorem linkHeap_unlink : ∀ h : Heap.FeltHeap,
    (linkHeap h).map (fun t => (t.1, t.2.1)) = h := by
  intro h
  induction h with
  | nil => rfl
  | cons hd rest ih => cases hd with
    | mk a v => simp only [linkHeap, List.map_cons, ih]

/-- `linkHeap` is INJECTIVE (unlink is a retraction). -/
theorem linkHeap_injective {h₁ h₂ : Heap.FeltHeap} (h : linkHeap h₁ = linkHeap h₂) : h₁ = h₂ := by
  have := congrArg (List.map (fun t : ℤ × ℤ × ℤ => (t.1, t.2.1))) h
  rwa [linkHeap_unlink, linkHeap_unlink] at this

/-- `linkHeap` preserves length. -/
theorem linkHeap_length : ∀ h : Heap.FeltHeap, (linkHeap h).length = h.length := by
  intro h
  induction h with
  | nil => rfl
  | cons hd rest ih => cases hd with
    | mk a v => simp only [linkHeap, List.length_cons, ih]

/-- **`mapRoot8 S8 d h`** — the depth-`d` 8-felt binary-Merkle root of the sorted heap `h`: LINK the
pointers (`linkHeap` — `relink_next_addrs`), digest each linked leaf (arity-3 `heapLeafDigest8` —
`HeapLeaf::digest8`), fold the perfect `node8` tree.

⚠ **THIS DOC-COMMENT SAID "BYTE-IDENTICAL to `heap_root.rs`'s `CanonicalHeapTree8::root` over the
padded sorted vector" AND THAT NAMED NOTHING.** There is no `CanonicalHeapTree8::root`; the deployed
method is `CanonicalHeapTree8::root8` (`circuit/src/heap_root.rs:1054`). And the "over the padded
sorted vector" clause described a padding this definition does not perform — `mapRoot8` is the DENSE
form and requires `h.length = 2 ^ d`, while the deployed builder prepends ONE MIN sentinel
(`min_sentinel_leaf`, `:307`) and ZERO-pads a sparse prefix. The LEAF and NODE shapes here are right;
the OCCUPANCY is not.

★ **The padded, sentinel-headed object — the one `CanonicalHeapTree8::root8` and
`circuit/src/whole_image_fold.rs::whole_boundary_fold` actually compute — is
`WholeImageFoldRealization.padImtRoot8` / `wholeBoundaryFold8`**, with the binding
`padImtRoot8_binds_or_ghost_or_collides`. `mapRoot8` remains correct as the DENSE 8-felt fold and is
the conservativity anchor the padded one extends (`padTo8_dense`). -/
def mapRoot8 (d : Nat) (h : Heap.FeltHeap) : Digest8 :=
  perfectRoot8 S8 d ((linkHeap h).map (heapLeafDigest8 S8))

/-- **THE HEAP-ROOT EXTRACTOR** — the SINGLE named pair the whole 8-felt heap-root peel hands back. Run
the perfect-tree descent over the two leaf-digest vectors; if it found a genuine collision that is the
answer, otherwise the descent has already forced the two DIGEST VECTORS equal, so the collision (if any)
is at the leaf absorb and the leaf-vector scan supplies the pair. -/
def mapRoot8Find (d : Nat) (h₁ h₂ : Heap.FeltHeap) : List ℤ × List ℤ :=
  if Coll8 S8.chipAbsorb8
      (perfectRoot8Find S8 d ((linkHeap h₁).map (heapLeafDigest8 S8))
                             ((linkHeap h₂).map (heapLeafDigest8 S8)))
  then perfectRoot8Find S8 d ((linkHeap h₁).map (heapLeafDigest8 S8))
                             ((linkHeap h₂).map (heapLeafDigest8 S8))
  else mapLeaf8Find S8 (linkHeap h₁) (linkHeap h₂)

/-- **`MapRootColl S8 d h₁ h₂`** — the pair `mapRoot8Find` RETURNS on this heap equivocation is a genuine
collision of the deployed arity-16 chip. The ONE named disjunct every 8-felt heap-root consumer carries
in place of the deleted `chip8CR` floor.

Deliberately NOT `∃ a b, chip collides`: at deployed BabyBear parameters that existence claim is
UNCONDITIONALLY TRUE by pigeonhole (`VacuitySweepTeeth.compress8CR_false_babyBear` proves precisely it),
so a disjunct of that shape would carry no more content than `True`. This one is about the SPECIFIC pair
a total extractor hands back, and it is REFUTABLE (`mapRootColl_refutable_of_injective`). -/
def MapRootColl (d : Nat) (h₁ h₂ : Heap.FeltHeap) : Prop :=
  Coll8 S8.chipAbsorb8 (mapRoot8Find S8 d h₁ h₂)

/-- **EXACT-PROP SKELETON — ⚑ NOT THE HEADLINE BINDING ANY MORE (see §RomSuccessor's
`heapTreeRoot_binds_rom`).** At deployed parameters a chip collision EXISTS by pigeonhole, so this
disjunction is satisfiable through the collides branch; the exported binding is the keyed-ROM
reduction.  Retained because `Deos.DocSubstrateSound` consumes it (the next repoint site).

(Replaces `mapRoot8_injective`.) Two
depth-`d` `2^d`-leaf heaps publishing the SAME 8-felt root are EITHER the same heap, OR the deployed chip
genuinely collides at the two blocks `mapRoot8Find` hands back.

This is what the 8-felt migration actually buys, stated honestly: the colliding-lane-0 heap pair the
GENTIAN tooth exhibits (`circuit/tests/heap_root_gentian_weld.rs`) is excluded UNLESS the adversary
produces a full ~124-bit collision at a NAMED pair of chip input blocks. The old form asserted the
exclusion outright while resting on a premise the deployed chip refutes. -/
theorem mapRoot8_binds_or_collides (d : Nat) {h₁ h₂ : Heap.FeltHeap}
    (hlen₁ : h₁.length = 2 ^ d) (hlen₂ : h₂.length = 2 ^ d)
    (h : mapRoot8 S8 d h₁ = mapRoot8 S8 d h₂) : h₁ = h₂ ∨ MapRootColl S8 d h₁ h₂ := by
  by_cases hif : Coll8 S8.chipAbsorb8
      (perfectRoot8Find S8 d ((linkHeap h₁).map (heapLeafDigest8 S8))
                             ((linkHeap h₂).map (heapLeafDigest8 S8)))
  · refine Or.inr ?_
    show Coll8 S8.chipAbsorb8 (mapRoot8Find S8 d h₁ h₂)
    rw [mapRoot8Find, if_pos hif]
    exact hif
  · rcases perfectRoot8_binds_or_collides S8 d
        (by rw [List.length_map, linkHeap_length, hlen₁])
        (by rw [List.length_map, linkHeap_length, hlen₂]) h with hmap | hc
    · rcases map_leaf8_binds_or_collides S8 _ _ hmap with hlink | hcl
      · exact Or.inl (linkHeap_injective hlink)
      · refine Or.inr ?_
        show Coll8 S8.chipAbsorb8 (mapRoot8Find S8 d h₁ h₂)
        rw [mapRoot8Find, if_neg hif]
        exact hcl
    · exact absurd hc hif

/-- **`opensToMerkle8 S8 d r k o`** — some depth-`d` `2^d`-leaf sorted heap behind the 8-felt binary root
`r` reads `o` at `k`. The faithful `node8` replacement of `opensToMerkle`. -/
def opensToMerkle8 (d : Nat) (r : Digest8) (k : ℤ) (o : Option ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ h.length = 2 ^ d ∧ mapRoot8 S8 d h = r ∧ Heap.get h k = o

/-- **`writesToMerkle8 S8 d r k v r'`** — some depth-`d` `2^d`-leaf sorted heap behind 8-felt root `r`
produces root `r'` under the sorted insert-or-update of `(k, v)` (post-heap still `2^d`-leaf). -/
def writesToMerkle8 (d : Nat) (r : Digest8) (k v : ℤ) (r' : Digest8) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ h.length = 2 ^ d
    ∧ (Heap.set h k v).length = 2 ^ d
    ∧ mapRoot8 S8 d h = r ∧ r' = mapRoot8 S8 d (Heap.set h k v)

/-! ### §5b.E — the OPENING-LEVEL consumers, over EXPLICIT witness heaps.

`opensToMerkle8` / `writesToMerkle8` hide their heap behind an existential, so the pair a collision
extractor returns is a function of the WITNESSES, not of the statement's visible parameters. Restating
the conclusion as `… ∨ ∃ collision` would be exactly the free pass this repair exists to avoid
(pigeonhole makes it unconditionally true). So the honest form takes the two witness heaps EXPLICITLY
and names `MapRootColl S8 d m₁ m₂` — the specific pair, extracted from the specific witnesses. The
existential-level statements survive as the injective special cases in §5b.S. -/

/-- **8-felt openings are FUNCTIONAL, UNCONDITIONAL** (replaces `opensToMerkle8_functional`; the
anti-ghost over the `node8` tree). Two witness heaps behind the SAME 8-felt root read the SAME value at
a key — OR the deployed chip genuinely collides at the named pair. -/
theorem opensToMerkle8_functional_or_collides (d : Nat) {r : Digest8} {k : ℤ} {o₁ o₂ : Option ℤ}
    {m₁ m₂ : Heap.FeltHeap}
    (hl₁ : m₁.length = 2 ^ d) (hr₁ : mapRoot8 S8 d m₁ = r) (hg₁ : Heap.get m₁ k = o₁)
    (hl₂ : m₂.length = 2 ^ d) (hr₂ : mapRoot8 S8 d m₂ = r) (hg₂ : Heap.get m₂ k = o₂) :
    o₁ = o₂ ∨ MapRootColl S8 d m₁ m₂ := by
  rcases mapRoot8_binds_or_collides S8 d hl₁ hl₂ (hr₁.trans hr₂.symm) with hm | hc
  · exact Or.inl (by rw [← hg₁, ← hg₂, hm])
  · exact Or.inr hc

/-- **Membership and non-membership at the same 8-felt root/key EXCLUDE each other, UNCONDITIONAL** (the
`node8` nullifier / non-membership tooth; replaces `opensToMerkle8_some_excludes_none`). A prover
showing both must exhibit the named chip collision. -/
theorem opensToMerkle8_some_excludes_none_or_collides (d : Nat) {r : Digest8} {k v : ℤ}
    {m₁ m₂ : Heap.FeltHeap}
    (hl₁ : m₁.length = 2 ^ d) (hr₁ : mapRoot8 S8 d m₁ = r) (hg₁ : Heap.get m₁ k = some v)
    (hl₂ : m₂.length = 2 ^ d) (hr₂ : mapRoot8 S8 d m₂ = r) (hg₂ : Heap.get m₂ k = none) :
    MapRootColl S8 d m₁ m₂ := by
  rcases opensToMerkle8_functional_or_collides S8 d hl₁ hr₁ hg₁ hl₂ hr₂ hg₂ with heq | hc
  · simp at heq
  · exact hc

/-- **8-felt writes are FUNCTIONAL, UNCONDITIONAL** (replaces `writesToMerkle8_functional`). The 8-felt
root + key + value determine the new root — the map-op row's `new_root` GROUP cannot be forged — unless
the deployed chip genuinely collides at the named pair. -/
theorem writesToMerkle8_functional_or_collides (d : Nat) {r : Digest8} {k v : ℤ} {r₁ r₂ : Digest8}
    {m₁ m₂ : Heap.FeltHeap}
    (hl₁ : m₁.length = 2 ^ d) (hr₁ : mapRoot8 S8 d m₁ = r) (he₁ : r₁ = mapRoot8 S8 d (Heap.set m₁ k v))
    (hl₂ : m₂.length = 2 ^ d) (hr₂ : mapRoot8 S8 d m₂ = r) (he₂ : r₂ = mapRoot8 S8 d (Heap.set m₂ k v)) :
    r₁ = r₂ ∨ MapRootColl S8 d m₁ m₂ := by
  rcases mapRoot8_binds_or_collides S8 d hl₁ hl₂ (hr₁.trans hr₂.symm) with hm | hc
  · exact Or.inl (by rw [he₁, he₂, hm])
  · exact Or.inr hc

/-! ### §5b.S — THE STRENGTH RELATION, both directions (no strength lost; no free pass gained).

The `…_of_injective` bridges assume exactly the injectivity the deleted `Heap8Scheme.chip8CR` field
asserted, and EVERY deleted statement — including the existential-level `opensToMerkle8_functional`,
`opensToMerkle8_some_excludes_none` and `writesToMerkle8_functional` — falls straight out. They are
precisely the injective special case of the new disjunctions. And `mapRootColl_refutable_of_injective`
shows the collision disjunct is REFUTABLE, so it is not a free pass: at an injective chip the binding
half has to do the work.

These are STANDALONE bridges, deliberately NOT hypotheses on any deployed keystone: `Compress8CR` is
FALSE at deployed BabyBear parameters, so a keystone carrying it would be right back where this repair
started. -/

/-- **(CANARY — the collision disjunct is REFUTABLE.)** At an injective chip `MapRootColl` is empty. -/
theorem mapRootColl_refutable_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (d : Nat) (h₁ h₂ : Heap.FeltHeap) : ¬ MapRootColl S8 d h₁ h₂ :=
  coll8_refutable_of_injective hCR _

/-- **NO STRENGTH LOST — the deleted `mapRoot8_injective` is the injective special case.** -/
theorem mapRoot8_injective_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (d : Nat) {h₁ h₂ : Heap.FeltHeap}
    (hlen₁ : h₁.length = 2 ^ d) (hlen₂ : h₂.length = 2 ^ d)
    (h : mapRoot8 S8 d h₁ = mapRoot8 S8 d h₂) : h₁ = h₂ := by
  rcases mapRoot8_binds_or_collides S8 d hlen₁ hlen₂ h with hm | hc
  · exact hm
  · exact absurd hc (mapRootColl_refutable_of_injective S8 hCR _ _ _)

/-- **NO STRENGTH LOST — the deleted existential-level `opensToMerkle8_functional`, recovered verbatim
at an injective chip.** -/
theorem opensToMerkle8_functional_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (d : Nat) {r : Digest8} {k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkle8 S8 d r k o₁) (h₂ : opensToMerkle8 S8 d r k o₂) : o₁ = o₂ := by
  obtain ⟨m₁, _, hl₁, hr₁, hg₁⟩ := h₁
  obtain ⟨m₂, _, hl₂, hr₂, hg₂⟩ := h₂
  rcases opensToMerkle8_functional_or_collides S8 d hl₁ hr₁ hg₁ hl₂ hr₂ hg₂ with ho | hc
  · exact ho
  · exact absurd hc (mapRootColl_refutable_of_injective S8 hCR _ _ _)

/-- **NO STRENGTH LOST — the deleted `opensToMerkle8_some_excludes_none`.** -/
theorem opensToMerkle8_some_excludes_none_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (d : Nat) {r : Digest8} {k v : ℤ}
    (h₁ : opensToMerkle8 S8 d r k (some v)) (h₂ : opensToMerkle8 S8 d r k none) : False := by
  have := opensToMerkle8_functional_of_injective S8 hCR d h₁ h₂
  simp at this

/-- **NO STRENGTH LOST — the deleted `writesToMerkle8_functional`.** -/
theorem writesToMerkle8_functional_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (d : Nat) {r : Digest8} {k v : ℤ} {r₁ r₂ : Digest8}
    (h₁ : writesToMerkle8 S8 d r k v r₁) (h₂ : writesToMerkle8 S8 d r k v r₂) : r₁ = r₂ := by
  obtain ⟨m₁, _, hl₁, _, hr₁, he₁⟩ := h₁
  obtain ⟨m₂, _, hl₂, _, hr₂, he₂⟩ := h₂
  rcases writesToMerkle8_functional_or_collides S8 d hl₁ hr₁ he₁ hl₂ hr₂ he₂ with hr | hc
  · exact hr
  · exact absurd hc (mapRootColl_refutable_of_injective S8 hCR _ _ _)

end Faithful8

/-! ## ⚑ §RomSuccessor — the depth-`d` tree binding, DISCHARGED on the PROVED keyed-ROM floor.

⚑ **THE MODELLING STEP, STATED (not smuggled)**, the `RomCarrierSites` discipline:

  * the sampled `H : Role × Msg → Fin (2 ^ l)` idealises the deployed arity-16 `node8` chip at an
    ASYMPTOTIC digest width — there is NO `l` at which `Fin (2 ^ l)` is the deployed 8-felt
    (~124-bit) digest;
  * the message domain is the TRUNCATED deployed absorb schedule: the linked arity-3 IMT leaf
    block `(addr, value, next)` at BabyBear range (`HeapLeaf::digest8`), and the two-child node
    block (a pair of digests — `heap_root.rs`'s `hash_fact(l, [r])` fold node), domain-separated
    by the ROLE key where the deployed chip separates by absorb arity (3 vs 16 felts);
  * the tree SHAPE is the deployed one: the bottom-up adjacent-pair fold of `perfectRoot8` IS the
    top-down contiguous-halves recursion `romFold` (level-`k` node `j` covers leaves
    `j·2^k … (j+1)·2^k − 1` in both presentations).

The forger equivocates the WHOLE `2^d`-leaf tree; the extractor RE-WALKS both trees as an oracle
program (`heapFindComp` — the ROM successor of the total extractor `mapRoot8Find`), paying
`2^(d+2) − 2` queries with ADDITIVE accounting, and names the shallowest layer at which the two
trees' absorbed blocks differ.  Every case is a win of ONE carrier at the sampled oracle;
`romCarrier_binds` (hence `keyedRom_hard`, the birthday bound) kills it.  What this section does
NOT carry: the ℤ-heap range bridge (`linkHeap` payloads are in-range felts on every deployed
heap) stays at the fixed-hash layer above — the ROM payload is the truncated linked-leaf
schedule itself. -/

section RomSuccessor

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction
open Dregg2.Crypto.RomCarrierSites

/-- The two deployed absorb roles: the arity-3 linked leaf and the arity-16 two-child node. -/
abbrev HeapRole : Type := Fin 2

/-- The leaf role (`HeapLeaf::digest8`'s absorb). -/
def heapLeafRole : HeapRole := 0
/-- The node role (`hash_fact(l, [r])`'s absorb). -/
def heapNodeRole : HeapRole := 1

/-- The truncated linked IMT leaf block: `(addr, value, next_addr)`, three BabyBear-range felts. -/
abbrev HeapLeafBlock : Type := Fin babyBearP × Fin babyBearP × Fin babyBearP

/-- **THE ORACLE MESSAGE DOMAIN** — a linked leaf block or a two-child node block. -/
abbrev HeapRomMsg (l : ℕ) : Type := HeapLeafBlock ⊕ (Fin (2 ^ l) × Fin (2 ^ l))

/-- **THE HEAP-TREE KEYED ROM FAMILY** — keyed by the two deployed roles. -/
def heapRomFamily : KeyedRomFamily :=
  flatFamily HeapRole inferInstance inferInstance ⟨0⟩ HeapRomMsg
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨Sum.inl (⟨0, babyBearP_pos⟩, ⟨0, babyBearP_pos⟩, ⟨0, babyBearP_pos⟩)⟩)

/-- The family's width obligation, closed by construction. -/
theorem heapRomFamily_card_R (l : ℕ) :
    letI := heapRomFamily.rFin l
    Fintype.card (heapRomFamily.R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **THE TREE CARRIER** — the identity carrier over the tree's own message shape, role in the
context: every tree layer's equivocation is a win of THIS carrier at its role. -/
def heapRomCarrier : RomCarrier heapRomFamily :=
  taggedCarrier _ (fun _ => Unit) (fun l => HeapRomMsg l)
    (fun _ => inferInstance)
    (fun _ _ v => v)
    (fun _ _ _ _ h => h)

/-- The left-half embedding of leaf positions (level split, contiguous halves). -/
def finL (n : ℕ) (i : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) :=
  ⟨i.val, by have h := i.isLt; rw [pow_succ]; omega⟩

/-- The right-half embedding of leaf positions. -/
def finR (n : ℕ) (i : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) :=
  ⟨2 ^ n + i.val, by have h := i.isLt; rw [pow_succ]; omega⟩

/-- A `2^(n+1)`-vector is determined by its two contiguous halves. -/
theorem halves_ext {n : ℕ} {α : Type} {u v : Fin (2 ^ (n + 1)) → α}
    (hL : (fun i => u (finL n i)) = (fun i => v (finL n i)))
    (hR : (fun i => u (finR n i)) = (fun i => v (finR n i))) : u = v := by
  funext i
  by_cases h : i.val < 2 ^ n
  · have hi : finL n ⟨i.val, h⟩ = i := Fin.val_injective rfl
    have := congrFun hL ⟨i.val, h⟩
    simpa [hi] using this
  · have hle : 2 ^ n ≤ i.val := Nat.le_of_not_lt h
    have hlt : i.val - 2 ^ n < 2 ^ n := by
      have h2 : i.val < 2 ^ (n + 1) := i.isLt
      have h3 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      omega
    have hi : finR n ⟨i.val - 2 ^ n, hlt⟩ = i := by
      apply Fin.val_injective
      show 2 ^ n + (i.val - 2 ^ n) = i.val
      omega
    have := congrFun hR ⟨i.val - 2 ^ n, hlt⟩
    simpa [hi] using this

/-- **THE PERFECT-TREE FOLD AT THE SAMPLED ORACLE** — contiguous-halves recursion; the deployed
`perfectRoot8` tree shape (`foldLevel8`'s bottom-up adjacent pairing folds exactly this tree). -/
def romFold (l : ℕ) (H : HeapRole × HeapRomMsg l → Fin (2 ^ l)) :
    (n : ℕ) → (Fin (2 ^ n) → Fin (2 ^ l)) → Fin (2 ^ l)
  | 0, v => v ⟨0, by positivity⟩
  | n + 1, v =>
      H (heapNodeRole, Sum.inr
        (romFold l H n (fun i => v (finL n i)), romFold l H n (fun i => v (finR n i))))

/-- **THE DEPLOYED HEAP ROOT AT THE SAMPLED ORACLE** — digest each linked leaf block at the leaf
role, fold the perfect node tree.  The ROM restatement of `mapRoot8`. -/
def romHeapRoot (l : ℕ) (H : HeapRole × HeapRomMsg l → Fin (2 ^ l)) (d : ℕ)
    (b : Fin (2 ^ d) → HeapLeafBlock) : Fin (2 ^ l) :=
  romFold l H d (fun i => H (heapLeafRole, Sum.inl (b i)))

/-- **THE TREE-WALK SELECTION (pure)** — the ROM successor of the total extractor `mapRoot8Find`:
descend from the root, at each level naming the shallowest absorbed-block disagreement.  Pure —
`heapFindComp` below pays its queries. -/
def heapFindSpec (l : ℕ) (H : HeapRole × HeapRomMsg l → Fin (2 ^ l)) :
    (n : ℕ) → (bu bv : Fin (2 ^ n) → HeapLeafBlock) →
      (HeapRole × Unit) × HeapRomMsg l × HeapRomMsg l
  | 0, bu, bv =>
      ((heapLeafRole, ()), Sum.inl (bu ⟨0, by positivity⟩), Sum.inl (bv ⟨0, by positivity⟩))
  | n + 1, bu, bv =>
      if ((romHeapRoot l H n (fun i => bu (finL n i)), romHeapRoot l H n (fun i => bu (finR n i)))
          : Fin (2 ^ l) × Fin (2 ^ l))
        ≠ (romHeapRoot l H n (fun i => bv (finL n i)), romHeapRoot l H n (fun i => bv (finR n i)))
      then ((heapNodeRole, ()),
        Sum.inr (romHeapRoot l H n (fun i => bu (finL n i)),
                 romHeapRoot l H n (fun i => bu (finR n i))),
        Sum.inr (romHeapRoot l H n (fun i => bv (finL n i)),
                 romHeapRoot l H n (fun i => bv (finR n i))))
      else if (fun i => bu (finL n i)) ≠ (fun i => bv (finL n i))
      then heapFindSpec l H n (fun i => bu (finL n i)) (fun i => bv (finL n i))
      else heapFindSpec l H n (fun i => bu (finR n i)) (fun i => bv (finR n i))

/-- **⚑ THE WALK WINS** — two DISTINCT leaf-block vectors with ONE tree root at the sampled
oracle: whatever the selection names is a genuine carrier equivocation.  The win-preservation
core, by induction on the depth: the root absorbs differ (a node-role win through the shared
root), or they agree and a half with differing blocks recurses through its shared sub-root, until
a single differing leaf block wins at the leaf role through its shared leaf digest. -/
theorem heapFindSpec_wins (l : ℕ) (H : HeapRole × HeapRomMsg l → Fin (2 ^ l)) :
    ∀ (n : ℕ) (bu bv : Fin (2 ^ n) → HeapLeafBlock), bu ≠ bv →
      romHeapRoot l H n bu = romHeapRoot l H n bv →
      (romCarrierGame heapRomFamily heapRomCarrier).wins l H (heapFindSpec l H n bu bv) := by
  intro n
  induction n with
  | zero =>
      intro bu bv hne hroot
      have hb : bu ⟨0, by positivity⟩ ≠ bv ⟨0, by positivity⟩ := by
        intro hc
        apply hne
        funext i
        have h1 : (2 : ℕ) ^ 0 = 1 := pow_zero 2
        have hi : i = ⟨0, by positivity⟩ := by
          apply Fin.val_injective
          have := i.isLt
          omega
        rw [hi]
        exact hc
      exact ⟨fun hc => hb (Sum.inl_injective hc), hroot⟩
  | succ n ih =>
      intro bu bv hne hroot
      unfold heapFindSpec
      split_ifs with hT hL
      · -- the two root absorbs DIFFER under the shared root digest.
        exact ⟨fun hc => hT (Sum.inr_injective hc), hroot⟩
      · -- left halves differ under the shared left sub-root.
        exact ih _ _ hL (congrArg Prod.fst (not_not.mp hT))
      · -- left halves agree, so the right halves must differ, under the shared right sub-root.
        have hR : (fun i => bu (finR n i)) ≠ (fun i => bv (finR n i)) := by
          intro hc
          exact hne (halves_ext (not_not.mp hL) hc)
        exact ih _ _ hR (congrArg Prod.snd (not_not.mp hT))

/-- **THE WALK, AS AN ORACLE PROGRAM** — re-derive every leaf digest and node digest of BOTH
trees by querying the sampled oracle (`2^(n+2) − 2` queries), returning the two roots and the
selection.  This is what prices the extraction: the walk is not free, and its cost is counted. -/
def heapFindComp (l : ℕ) :
    (n : ℕ) → (bu bv : Fin (2 ^ n) → HeapLeafBlock) →
      OracleComp (heapRomFamily.toRomFamily.D l) (heapRomFamily.toRomFamily.R l)
        (Fin (2 ^ l) × Fin (2 ^ l) × ((HeapRole × Unit) × HeapRomMsg l × HeapRomMsg l))
  | 0, bu, bv =>
      OracleComp.query (heapLeafRole, Sum.inl (bu ⟨0, by positivity⟩)) (fun du =>
      OracleComp.query (heapLeafRole, Sum.inl (bv ⟨0, by positivity⟩)) (fun dv =>
      OracleComp.pure (du, dv,
        ((heapLeafRole, ()),
         Sum.inl (bu ⟨0, by positivity⟩), Sum.inl (bv ⟨0, by positivity⟩)))))
  | n + 1, bu, bv =>
      OracleComp.bindComp
        (heapFindComp l n (fun i => bu (finL n i)) (fun i => bv (finL n i))) (fun pL =>
      OracleComp.bindComp
        (heapFindComp l n (fun i => bu (finR n i)) (fun i => bv (finR n i))) (fun pR =>
      OracleComp.query (heapNodeRole, Sum.inr (pL.1, pR.1)) (fun ru =>
      OracleComp.query (heapNodeRole, Sum.inr (pL.2.1, pR.2.1)) (fun rv =>
      OracleComp.pure (ru, rv,
        if ((pL.1, pR.1) : Fin (2 ^ l) × Fin (2 ^ l)) ≠ (pL.2.1, pR.2.1)
        then ((heapNodeRole, ()), Sum.inr (pL.1, pR.1), Sum.inr (pL.2.1, pR.2.1))
        else if (fun i => bu (finL n i)) ≠ (fun i => bv (finL n i))
        then pL.2.2 else pR.2.2)))))

/-- The program computes exactly the two tree roots and the pure selection. -/
theorem heapFindComp_eval (l : ℕ) (H : heapRomFamily.toRomFamily.D l → heapRomFamily.toRomFamily.R l) :
    ∀ (n : ℕ) (bu bv : Fin (2 ^ n) → HeapLeafBlock),
      (heapFindComp l n bu bv).eval H
        = (romHeapRoot l H n bu, romHeapRoot l H n bv, heapFindSpec l H n bu bv) := by
  intro n
  induction n with
  | zero => intro bu bv; rfl
  | succ n ih =>
      intro bu bv
      show (OracleComp.bindComp _ _).eval H = _
      simp only [OracleComp.bindComp_eval]
      rw [ih, ih]
      rfl

/-- The walk's query budget: `2^(n+2) − 2` — two full trees, one query per absorb. -/
theorem heapFindComp_queryBounded (l : ℕ) :
    ∀ (n : ℕ) (bu bv : Fin (2 ^ n) → HeapLeafBlock),
      QueryBounded (2 ^ (n + 2) - 2) (heapFindComp l n bu bv) := by
  intro n
  induction n with
  | zero =>
      intro bu bv
      exact QueryBounded.query 1 _ _ (fun _ => QueryBounded.query 0 _ _
        (fun _ => QueryBounded.pure 0 _))
  | succ n ih =>
      intro bu bv
      refine (OracleComp.bindComp_queryBounded (ih _ _) (fun pL =>
        OracleComp.bindComp_queryBounded (ih _ _) (fun pR =>
          QueryBounded.query 1 _ _ (fun _ => QueryBounded.query 0 _ _
            (fun _ => QueryBounded.pure 0 _))))).mono ?_
      have h1 : (2 : ℕ) ^ (n + 1 + 2) = 2 * 2 ^ (n + 2) := by rw [pow_succ]; ring
      have h2 : (2 : ℕ) ≤ 2 ^ (n + 2) := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- A `Q + c` budget stays polynomial, for ANY constant `c` — the accounting fact a depth-`d`
tree walk needs (`polyBounded_sq_add_two` generalized off the `+2` special case). -/
theorem polyBounded_sq_add_const (c : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    PolyBounded (fun l => (((Q l + c : ℕ) : ℝ) * ((Q l + c : ℕ) : ℝ) + 1)) := by
  obtain ⟨e, C, h⟩ := hQ
  refine ⟨e, (2 * ((c : ℝ) + 1) ^ 2 + 1) * C, ?_⟩
  filter_upwards [h] with n hn
  have hq : (0 : ℝ) ≤ (Q n : ℝ) := Nat.cast_nonneg _
  have hc : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have h1 : |((Q n : ℝ) * (Q n : ℝ) + 1)| = (Q n : ℝ) * (Q n : ℝ) + 1 :=
    abs_of_nonneg (by positivity)
  have h2 : |(((Q n + c : ℕ) : ℝ) * ((Q n + c : ℕ) : ℝ) + 1)|
      = ((Q n : ℝ) + c) * ((Q n : ℝ) + c) + 1 := by
    push_cast
    exact abs_of_nonneg (by positivity)
  rw [h2]
  rw [h1] at hn
  have hkey : ((Q n : ℝ) + c) * ((Q n : ℝ) + c) + 1
      ≤ (2 * ((c : ℝ) + 1) ^ 2 + 1) * ((Q n : ℝ) * (Q n : ℝ) + 1) := by
    nlinarith [sq_nonneg ((Q n : ℝ) - c), sq_nonneg (Q n : ℝ), hq, hc,
      mul_nonneg (mul_nonneg hc hc) (sq_nonneg (Q n : ℝ)),
      mul_nonneg hc (sq_nonneg (Q n : ℝ))]
  have hmul : (2 * ((c : ℝ) + 1) ^ 2 + 1) * ((Q n : ℝ) * (Q n : ℝ) + 1)
      ≤ (2 * ((c : ℝ) + 1) ^ 2 + 1) * (C * (n : ℝ) ^ e) :=
    mul_le_mul_of_nonneg_left hn (by positivity)
  calc ((Q n : ℝ) + c) * ((Q n : ℝ) + c) + 1
      ≤ (2 * ((c : ℝ) + 1) ^ 2 + 1) * ((Q n : ℝ) * (Q n : ℝ) + 1) := hkey
    _ ≤ (2 * ((c : ℝ) + 1) ^ 2 + 1) * (C * (n : ℝ) ^ e) := hmul
    _ = (2 * ((c : ℝ) + 1) ^ 2 + 1) * C * (n : ℝ) ^ e := by ring

/-- **THE WHOLE-TREE ROM FORGERY** — two DISTINCT `2^d`-leaf linked-block vectors whose tree
roots agree at the sampled oracle.  The ROM restatement of the `mapRoot8` equivocation. -/
def heapRomForgery (d : ℕ) : RomForgery heapRomFamily where
  Ans := fun _ => (Fin (2 ^ d) → HeapLeafBlock) × (Fin (2 ^ d) → HeapLeafBlock)
  wins := fun l H p => p.1 ≠ p.2 ∧ romHeapRoot l H d p.1 = romHeapRoot l H d p.2
  winsDec := fun _ _ _ => instDecidableAnd

/-- The whole-tree break game at depth `d` (deployed `d = HEAP_TREE_DEPTH = 16`). -/
abbrev heapRomBreakGame (d : ℕ) : Game := (heapRomForgery d).game

/-- **THE EXTRACTOR, AS AN ORACLE PROGRAM** — run the forger, then hand its two leaf-block
vectors to the priced tree walk and keep the selection (`mapOut` drops the recomputed roots
without adding queries). -/
def heapExtractComp (d : ℕ)
    (M : ∀ l, OracleComp (heapRomFamily.toRomFamily.D l) (heapRomFamily.toRomFamily.R l)
      ((heapRomForgery d).Ans l)) :
    RomCarrierComp heapRomFamily heapRomCarrier :=
  fun l => OracleComp.bindComp (M l)
    (fun a => OracleComp.mapOut (fun r => r.2.2) (heapFindComp l d a.1 a.2))

/-- **⚑⚑ THE DEPTH-`d` TREE BINDING, DISCHARGED ON THE PROVED FLOOR** — the exported successor of
the demoted `mapRoot8_binds_or_collides` / `perfectRoot8_binds_or_collides` /
`foldLevel8_binds_or_collides` / `map_leaf8_binds_or_collides` skeletons: every query-bounded
forger that equivocates the depth-`d` heap tree between two DISTINCT leaf-block vectors has
NEGLIGIBLE advantage.  The extractor is the priced tree walk (`Q + 2^(d+2)` queries, additive);
the floor is `keyedRom_hard` (the birthday bound).  NO floor hypothesis, NO escape branch. -/
theorem heapTreeRoot_binds_rom (d : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (heapRomBreakGame d))
    (hA : RomForgeryEff heapRomFamily (heapRomForgery d) Q A) :
    Negl (gameAdv (heapRomBreakGame d) A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  refine negl_of_le (fun l => (gameAdv_mem_unit (heapRomBreakGame d) A l).1)
    (fun l => ?_)
    (romCarrier_binds heapRomFamily heapRomCarrier (fun l => Q l + 2 ^ (d + 2))
      (polyBounded_sq_add_const (2 ^ (d + 2)) Q hQ)
      heapRomFamily_card_R
      (romCarrierAdv _ _ (heapExtractComp d M))
      ⟨heapExtractComp d M,
        fun l => (OracleComp.bindComp_queryBounded (hM l)
          (fun a => OracleComp.mapOut_queryBounded _
            (heapFindComp_queryBounded l d a.1 a.2))).mono
          (by
            show Q l + (2 ^ (d + 2) - 2) ≤ Q l + 2 ^ (d + 2)
            have h2 : (2 : ℕ) ≤ 2 ^ (d + 2) := by
              calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
              _ ≤ 2 ^ (d + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega),
        fun _ _ => rfl⟩)
  refine @winProb_le_of_imp _ ((heapRomBreakGame d).instFin l) _ _ (fun H hH => ?_)
  replace hH := (Adversary.hit_eq_true _ _ _).mp hH
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  obtain ⟨hne, hroot⟩ := hH
  have hBrun : (romCarrierAdv _ _ (heapExtractComp d M)).run l H
      = heapFindSpec l H d (A.run l H).1 (A.run l H).2 := by
    show (heapExtractComp d M l).eval H = _
    unfold heapExtractComp
    rw [OracleComp.bindComp_eval, ← hrun l H, OracleComp.mapOut_eval, heapFindComp_eval]
  rw [hBrun]
  exact heapFindSpec_wins l H d (A.run l H).1 (A.run l H).2 hne hroot

/-- The tree root at a CONSTANT oracle is that constant — every absorb answers it. -/
theorem romHeapRoot_const (l : ℕ) (r : Fin (2 ^ l)) (d : ℕ) (b : Fin (2 ^ d) → HeapLeafBlock) :
    romHeapRoot l (fun _ => r) d b = r := by
  cases d with
  | zero => rfl
  | succ n => rfl

/-- **(TOOTH — the game is WINNABLE and the admitted refuter-shape is DEFANGED.)** The `0`-query
constant answerer with two DISTINCT fixed leaf-block vectors is IN the class, WINS at the
constant oracle (both roots are the constant), and is NEGLIGIBLE by the bound — the pigeonhole
strategy that made the demoted disjunctions free passes dies at the sampled oracle. -/
theorem heapRom_constAnswer_defanged (d : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (v w : Fin (2 ^ d) → HeapLeafBlock) (hvw : v ≠ w) :
    (RomForgeryEff heapRomFamily (heapRomForgery d) Q
        ⟨fun l _ => ((v, w) : (heapRomForgery d).Ans l)⟩)
      ∧ (∀ l, 0 < gameAdv (heapRomBreakGame d) ⟨fun l _ => ((v, w) : (heapRomForgery d).Ans l)⟩ l)
      ∧ Negl (gameAdv (heapRomBreakGame d) ⟨fun l _ => ((v, w) : (heapRomForgery d).Ans l)⟩) := by
  have hmem : RomForgeryEff heapRomFamily (heapRomForgery d) Q
      ⟨fun l _ => ((v, w) : (heapRomForgery d).Ans l)⟩ :=
    ⟨fun l => OracleComp.pure (v, w), fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩
  refine ⟨hmem, fun l => ?_, heapTreeRoot_binds_rom d Q hQ _ hmem⟩
  refine @winProb_pos_of_witness _ ((heapRomBreakGame d).instFin l) _
    (fun _ => ⟨0, by positivity⟩) ?_
  refine (Adversary.hit_eq_true _ l _).mpr ⟨hvw, ?_⟩
  exact (romHeapRoot_const l _ d _).trans (romHeapRoot_const l _ d _).symm

/-- **(TOOTH — a non-negligible tree equivocator is OUTSIDE the class.)** -/
theorem heapRom_nonNegl_forger_excluded (d : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (heapRomBreakGame d))
    (hnn : ¬ Negl (gameAdv (heapRomBreakGame d) A)) :
    ¬ RomForgeryEff heapRomFamily (heapRomForgery d) Q A :=
  fun hA => hnn (heapTreeRoot_binds_rom d Q hQ A hA)

end RomSuccessor

/-! ## §6 — Axiom hygiene. -/

#assert_axioms foldLevel_length_half
#assert_axioms mapRootFind
#assert_axioms mapRoot_binds_or_collides
#assert_axioms mapRootSpongeColl_dischargeable
#assert_axioms mapRootSpongeColl_refutable
#assert_axioms mapRootSpongeColl_refutes_poseidon2CR
#assert_axioms mapRoot_injective
#assert_axioms opensToMerkle_binds_or_collides
#assert_axioms writesToMerkle_binds_or_collides
#assert_axioms openColl_dischargeable
#assert_axioms writeColl_dischargeable
#assert_axioms openColl_refutable
#assert_axioms openColl_refutes_poseidon2CR
#assert_axioms writeColl_refutes_poseidon2CR
#assert_axioms opensToMerkle_functional
#assert_axioms opensToMerkle_some_excludes_none
#assert_axioms writesToMerkle_functional
-- §5b — the faithful 8-felt (`node8`) denotation, axiom-clean. Crypto no longer enters as an ASSUMED
-- carrier at all: the `Heap8Scheme.chip8CR` field is deleted (it is false at deployed BabyBear
-- parameters), and every statement below carries its collision site as EXTRACTED DATA instead.
#assert_axioms foldLevel8_binds_or_collides
#assert_axioms perfectRoot8_binds_or_collides
#assert_axioms map_leaf8_binds_or_collides
#assert_axioms mapRoot8_binds_or_collides
#assert_axioms opensToMerkle8_functional_or_collides
#assert_axioms opensToMerkle8_some_excludes_none_or_collides
#assert_axioms writesToMerkle8_functional_or_collides
-- §5b.S — the strength relation: every deleted statement recovered as the injective special case, plus
-- the refutability canary that keeps the collision disjunct from being a free pass.
#assert_axioms mapRootColl_refutable_of_injective
#assert_axioms mapRoot8_injective_of_injective
#assert_axioms opensToMerkle8_functional_of_injective
#assert_axioms opensToMerkle8_some_excludes_none_of_injective
#assert_axioms writesToMerkle8_functional_of_injective
-- §RomSuccessor — the EXPORTED binding: the depth-`d` tree equivocation as a reduction on the
-- PROVED keyed-ROM floor, with the tree walk priced as an oracle program.
#assert_axioms halves_ext
#assert_axioms heapRomFamily_card_R
#assert_axioms heapFindSpec_wins
#assert_axioms heapFindComp_eval
#assert_axioms heapFindComp_queryBounded
#assert_axioms polyBounded_sq_add_const
#assert_axioms heapTreeRoot_binds_rom
#assert_axioms heapRom_constAnswer_defanged
#assert_axioms heapRom_nonNegl_forger_excluded

end Dregg2.Circuit.MapMerkleRoot
