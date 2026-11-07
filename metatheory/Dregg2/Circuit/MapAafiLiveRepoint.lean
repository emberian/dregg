/-
# `Dregg2.Circuit.MapAafiLiveRepoint` — the `.aafiInsert` arm REPOINTED: the arm that SHIPS, given
  non-vacuous laws at the deployed leaf shape, plus the ELEVENTH impossibility that fixes exactly
  what the post side can and cannot say.

`MapInsertImtRepoint` §8 found that `MapOpsColumnLayout.ReconcileGatesAt`'s `.write`, `.insert` and
`.aafiInsert` arms are **the same body**, so `reconcileGates_insert_forces_key_present` was never
about `.insert` — and that the two literal op = 3 MapOps are ORPHANS while `.aafiInsert` is what the
prover runs. This file repoints THAT arm, and lands the positive result the `.insert` arm could not
have: the deployed AAFI gate is genuinely STRONG, so its post side IS forced — just not into any
shape a `MapLeafSchema` can express.

## PREMISES, RE-VERIFIED AT HEAD (all four confirmed; SIX citations corrected, one list extended)

* `ReconcileGatesAt`'s `.write` / `.insert` / `.aafiInsert` arms are the same body, character for
  character, at `MapOpsColumnLayout.lean:840-856` (the finding cited `:825-842`; the file moved).
* `insert_witness_aafi` is `heap_root.rs:1157` — NOT `:1077-1156`, which is the tail of
  `update_witness8` plus the doc block. Its present-key refusal IS at `:1167-1169` as cited
  (`if self.position_of(key).is_some() { return None }`), and `:1188-1189`'s pointer-bracket refusal
  is a second, independent freshness guard. `insert_witness`'s twin refusal is `:1092-1094`; the
  `MapInsertImtRepoint` header's `:1091-1093` is one line off.
* `Ir2Air::MapOps` is `descriptor_ir2.rs:3253-3563`, not `:3232-3541`. `rw_sel = not_insert + s` and
  `not_insert3 = not_insert + 2s` ARE at `:3298-3299` as cited, and `s·(op−4) = 0` at `:3288` pins
  `s = 0` off op = 4. ⚠ The free-slot `ZERO8` pin is `:3514-3516`, **NOT** `:3493-3495` — those lines
  are inside gate (c)'s PATH1 loop. The five op = 4 gates are (a) `:3371-3378` + `:3402-3405`,
  (b) `:3436-3475`, (c) `:3477-3508`, (d1) `:3510-3534`, (d2) `:3536-3557`.
* **`.aafiInsert` SHIPS, and the reach is one effect WIDER than the brief said.** `"op":"aafi_insert"`
  appears on eight descriptors in each of three committed registries — `noteSpend`, **`noteCreate`**,
  `revoke`, `createCell`, `factory`, `spawn`, `spawnCapOpen`, `spawnWriteCapOpen`. The brief's list
  omitted `noteCreate` / `commitmentsInsertOp`. Histogram over all seven registry TSVs:
  `aafi_insert` 24 rows, `absent` 24, `write` 4, **`insert` 0.** The orphanhood of `insertWriteOp` /
  `insertWriteOpRot` is confirmed twice: no `.mapOp` wiring in the Lean, no `"op":"insert"` row in any
  emitted descriptor.
* The generic prover-side fill `descriptor_ir2.rs:5265-5271` calls `insert_witness_aafi` for EVERY
  `MapKind::AafiInsert` row, from `build_traces` → `prove_vm_descriptor2_inner`, so all eight deployed
  descriptors run the present-key refusal on every prove. `next_free_index` is `sorted_leaves.len()`
  and is never re-compacted (`:1006`, `:1204`, and `:1212`'s own `debug_assert_eq!`), so the honest
  free slot is exactly the first padding cell — which §1 handles as an EQUALITY and §5 generalizes to
  every free slot the AIR actually admits.

## THE THREE RESULTS

### 1. THE REPOINT, AND THE POST SIDE IS FORCED IN FULL (§3, §4, §6)

`MapKindImtGates.aafiImtGates_force_absence_or_resid` consumes gates (a) and (b) only and stops at
the PRE side. `AafiLayoutAt` / `aafiImtGates_force_layout_or_resid` extract all five. An accepting
op = 4 row forces the post-root column to be the fold of a vector that is the committed pre-vector
with **exactly two cells changed**: position `p1` (the low leaf — its ADDRESS and VALUE untouched, its
POINTER moved `lowNext → key`) and position `p2`, which is FORCED to have held the padding constant
(`h.length ≤ p2 < 2 ^ dep`, DERIVED from gate (d1)'s pinned `ZERO8`, not assumed).

⚑ THE CONTRAST THAT MAKES THIS THE PAYOFF. `MapInsertImtRepoint.insertPair_erases_the_rest_of_the_map`
exhibits an accepting `.absent` + op = 3 pair whose post-root commits a map with the OTHER ENTRY
DELETED, because neither row relates the pre-root to the post-root. `aafiLayout_admits_no_erasure`
proves the live arm cannot do that: every cell other than `p1` and `p2` is *literally* the
pre-commitment's cell. The map-preservation nobody checks for op = 3 **is checked** for op = 4.

### 2. ⚑ THE ELEVENTH APPROACH, AND IT WORKS: A LAYOUT-LEVEL DENOTATION (§5)

Ten of the last eleven obvious approaches on this epoch were proved impossible. The eleventh — "give
the denotation an ORDER coordinate", which §12.4 of the design doc named without taking — works, and
what it buys is not a consolation prize:

> `aafiImtRow_forces_insertsUpToLayout_of_good` — an accepting deployed AAFI row forces
> `AafiInsertsUpToLayout`: there is an admissible sparse pre-map `h` behind the pre-root at which the
> row's key is ABSENT, and the post-root is the fold of a list that is a **`List.Perm` of the padded
> commitment vector of `Heap.set h key value`**.

Freshness AND total map preservation, at the deployed padded arity-3 leaf, floor-free. The engine is
`chain_relink_snoc_perm`: the deployed physical layout — pre-chain, low leaf relinked, new leaf
appended at the free slot — IS the relinked chain of the correctly-inserted map, permuted. So
`heap_root.rs:1139-1141`'s *"a distinct commitment lineage from the sorted-compacted `root8` (same
leaf SET, different positions)"* becomes a theorem with the "same leaf SET" half PROVED and the
"different positions" half localized to one `List.Perm`.

### 3. ⚑⚑ THE ELEVENTH IMPOSSIBILITY — the post-root is not a commitment AT ALL (§7)

The eighth impossibility (`no_schema_commits_the_append_order_layout`) refuted a UNIFORM law: *for
every chain and every permuted layout…*. This refutes the post side at ONE deployed row, for EVERY
key and EVERY value:

> `aafi_interior_post_admits_no_opening` — the post-root an accepting op = 4 row produces over the
> pre-map `[(1,7),(9,3)]` at fresh key `5` satisfies `¬ opensToMerkleS (padImtSchema 100) … k o` for
> **every** `k` and **every** `o`. It is the `commit` of no admissible heap whatsoever, because the
> append-order address list is `[1, 9, 5]` and every `imtChainOf`'s is strictly increasing.

Consequence: `insertsFreshS` — `MapInsertImtRepoint`'s honest limit for the op = 3 pairing — is NOT
available at the AAFI post side either (`aafi_post_cannot_be_insertsFreshS`), because its second
conjunct is an `opensToMerkleS`. **§5's layout statement is not a weakened convenience; it is the only
shape the deployed AAFI post-condition has.** `aafi_interior_row_at_depth2` is a REAL accepting row
(every path obligation `rfl`) so the refutation bites on gate data, not on a hypothetical root.

## THE WIDE TWIN (§9)

`MapOpWideKeyWeld.demoInsertGateW_accepts` ran `MapOpKind.insert` at `keyLo`, which `demoHeapW`
ALREADY HOLDS — the wide twin of the narrow `toy_insert_gates` blind spot. It is RENAMED
`demoValueUpdateGateW_accepts` in place, with `demoValueUpdateGateW_key_is_already_committed`
promoted from prose to a theorem beside it. ⚑ A fresh-key twin at the wide shape does not exist and
CANNOT be written, and the obstruction is FLOOR-FREE: `wide_insert_never_grows_the_map` — the
denotation both write-shaped wide arms conclude (`writesToMerkleW`) has `h.length = 2 ^ dep` on BOTH
sides of the write, so every witness has its key already committed, at every `LaneEnc` and every
depth. That impossibility is the deliverable.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free; no `native_decide`; no
`decide` over any depth-16 object — every depth-16 exhibit reuses `MapKindImtGates`'s symbolic
`leftPadPath` / `slot1Path` recursions and NAMES its roots as the schema's own `commit`.
**NO FLOOR CARRIER**: `Poseidon2SpongeCR` and `Compress8CR` appear in no type and no `def` body here;
every law is the `_or_resid` / `_of_good` pair at `MapGood = Function.Injective ∧ PadFree3`, which is
`padImtTeeth`'s own `Good` field, and all three residuals are at SPECIFIC named witnesses.
Lean-only; no Rust, descriptor, emit or JSON byte touched.
-/
import Dregg2.Circuit.MapInsertImtRepoint
import Dregg2.Circuit.MapOpWideKeyWeld

namespace Dregg2.Circuit.MapAafiLiveRepoint

open Dregg2.Substrate
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (MapOp MapOpKind MAP_TREE_DEPTH EffectVmDescriptor2 VmTrace
  VmConstraint2 mapOpsOf envAt)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.MapMerkleRoot (mapNode perfectRoot mapRoot perfectRoot_binds_or_collides)
open Dregg2.Circuit.MapDenotationSchema (MapLeafSchema imtChainOf opensToMerkleS writesToMerkleS
  imtSchema_chain_imtSorted)
open Dregg2.Circuit.MapPaddedDenotation (padDigest padTo padTo_length padTo_dense
  padImtRoot PadFree3 padImtSchema padImtTeeth imtChainOf_length
  imtToHeap_imtChainOf oddSponge oddSponge_injective oddSponge_padFree3)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted imtAddrs imtLeafHash imtToHeap
  imtAbsent_excludes keys_imtToHeap)
open Dregg2.Circuit.MapOpsColumnLayout (pathPos pathRecompute pathCollFind
  pathRecompute_binds_updates ReconcileGatesAt mem_mapOpsOf set_append_right' map_set')
open Dregg2.Crypto.SpongeCarrierReduction (IsSpongeColl)
open Dregg2.Circuit.Poseidon2Binding (spongeColl_refutable_of_injective)
open Dregg2.Circuit.MapKindImtGates
-- `fits_of_pow_le` — capacity from a CHEAPER exponent; the only way §7's symbolic-depth exhibit can
-- carry `appendOrderRoot`'s occupancy obligation without ever evaluating `2 ^ dep`.
open Dregg2.Circuit.DeployedMapDenotation (fits_of_pow_le)
open Dregg2.Circuit.MapInsertImtRepoint (padTo_getElem?_lt insertsFreshS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — PADDING ALGEBRA FOR THE FREE SLOT: overwriting a padding cell IS appending.

Gate (d1) pins the free slot to the padding constant, so the AAFI append writes into the padding.
These three lemmas turn "cell `p2` of the padded vector was replaced" into "one entry joined the live
prefix": an EQUALITY when `p2` is the FIRST free slot (which is what `next_free_index` always is), and
a `List.Perm` at every other free slot, which is all the AIR actually forces. -/

/-- Overwriting one cell of a padding run has the same multiset as prepending the new value to a run
one shorter. This is the whole `List.Perm` content of "append order is not sorted order". -/
theorem set_append_at_head (A : List ℤ) (i : Nat) (hi : A.length = i) (a y : ℤ) (T : List ℤ) :
    (A ++ a :: T).set i y = A ++ y :: T := by
  subst hi
  induction A with
  | nil => rfl
  | cons b t ih => simpa using ih

theorem set_replicate_perm (n j : Nat) (a y : ℤ) (hj : j < n) :
    (((List.replicate n a).set j y)).Perm (y :: List.replicate (n - 1) a) := by
  have hsplit : List.replicate n a
      = List.replicate j a ++ (a :: List.replicate (n - 1 - j) a) := by
    have harith : j + 1 + (n - 1 - j) = n := by omega
    rw [← harith, List.replicate_add, List.replicate_add]
    simp
  have hset : (List.replicate n a).set j y
      = List.replicate j a ++ (y :: List.replicate (n - 1 - j) a) := by
    conv_lhs => rw [hsplit]
    exact set_append_at_head (List.replicate j a) j (by simp) a y (List.replicate (n - 1 - j) a)
  rw [hset]
  refine List.perm_middle.trans ?_
  have hadd : j + (n - 1 - j) = n - 1 := by omega
  rw [← List.replicate_add, hadd]

/-- **The free slot is the append slot, EXACTLY, when it is the FIRST free slot** — the honest
producer's case (`free_index = next_free_index = sorted_leaves.len()`). -/
theorem padTo_set_at_length (d : Nat) (M : List ℤ) (y : ℤ) (hlt : M.length < 2 ^ d) :
    (padTo d M).set M.length y = padTo d (M ++ [y]) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ d - M.length = m + 1 := ⟨2 ^ d - M.length - 1, by omega⟩
  have e1 : padTo d M = M ++ (padDigest :: List.replicate m padDigest) := by
    rw [padTo, hm, List.replicate_succ]
  have e2 : padTo d (M ++ [y]) = M ++ (y :: List.replicate m padDigest) := by
    rw [padTo, show (M ++ [y]).length = M.length + 1 from by simp,
      show 2 ^ d - (M.length + 1) = m from by omega]
    simp
  rw [e1, e2]
  exact set_append_at_head M M.length rfl padDigest y (List.replicate m padDigest)

/-- **And a PERMUTATION at any other free slot** — which is all gate (d1) forces, since the AIR pins
the slot's DIGEST to `ZERO8` and never pins its INDEX to `next_free_index`. -/
theorem padTo_set_pad_perm (d : Nat) (M : List ℤ) (p : Nat) (y : ℤ)
    (hM : M.length ≤ p) (hp : p < 2 ^ d)
    (fM : M.length ≤ 2 ^ d) (fA : (M ++ [y]).length ≤ 2 ^ d) :
    (((padTo d M fM).set p y)).Perm (padTo d (M ++ [y]) fA) := by
  obtain ⟨j, hpj⟩ : ∃ j, p = M.length + j := ⟨p - M.length, by omega⟩
  subst hpj
  have hj : j < 2 ^ d - M.length := by omega
  have htgt : padTo d (M ++ [y]) fA
      = M ++ (y :: List.replicate (2 ^ d - M.length - 1) padDigest) := by
    rw [padTo, show (M ++ [y]).length = M.length + 1 from by simp,
      show 2 ^ d - (M.length + 1) = 2 ^ d - M.length - 1 from by omega]
    simp
  have hsrc : (padTo d M fM).set (M.length + j) y
      = M ++ (List.replicate (2 ^ d - M.length) padDigest).set j y := by
    rw [padTo, set_append_right']
  rw [hsrc, htgt]
  exact List.Perm.append_left M (set_replicate_perm _ _ padDigest y hj)

/-- Padding a permutation is a permutation of the paddings (equal lengths ⇒ equal padding runs). -/
theorem padTo_perm_of_perm (d : Nat) {P Q : List ℤ} (hpq : P.Perm Q)
    (fP : P.length ≤ 2 ^ d) (fQ : Q.length ≤ 2 ^ d) :
    ((padTo d P fP)).Perm (padTo d Q fQ) := by
  have hl : P.length = Q.length := hpq.length_eq
  simp only [padTo, hl]
  exact hpq.append_right _

/-! ## §2 — ⚑ THE ENGINE: THE DEPLOYED PHYSICAL LAYOUT **IS** THE INSERTED MAP'S CHAIN, PERMUTED.

`heap_root.rs::insert_witness_aafi` (`:1210-1213`) builds `append_order_after` as *the sorted vector
with position `low_position` overwritten by the pointer-updated low leaf, then the new leaf pushed*,
and `:1139-1141` calls the result *"a distinct commitment lineage from the sorted-compacted `root8`
(same leaf SET, different positions)"*. That sentence has two halves. The first is a theorem now. -/

theorem heap_set_cons_gt (k' v' key value : ℤ) (rest : Heap.FeltHeap) (hlt : k' < key) :
    Heap.set ((k', v') :: rest) key value = (k', v') :: Heap.set rest key value := by
  simp only [Heap.set]
  rw [if_neg (by omega : ¬ (key < k')), if_neg (by omega : ¬ (key = k'))]

theorem heap_set_cons_lt (k' v' key value : ℤ) (rest : Heap.FeltHeap) (hlt : key < k') :
    Heap.set ((k', v') :: rest) key value = (key, value) :: (k', v') :: rest := by
  simp only [Heap.set]
  rw [if_pos hlt]

/-- **★★ THE AAFI LAYOUT IS THE INSERTED MAP, PERMUTED.** Take the deployed pre-chain, relink the low
leaf's POINTER to the fresh key, append the new leaf: the result is a `List.Perm` of the relinked
chain of `Heap.set h key value`. Every hypothesis is one the deployed gate (a) + (b) pair FORCES —
the low leaf sits at position `p` of the committed heap, and the key is strictly inside its pointer
gap. Nothing about the hash, nothing about the depth. -/
theorem chain_relink_snoc_perm (sent : ℤ) :
    ∀ (h : Heap.FeltHeap) (p : Nat) (key value lowAddr lowValue : ℤ),
      Heap.SortedKeys h → h[p]? = some (lowAddr, lowValue) →
      lowAddr < key → key < (h[p + 1]?).elim sent Prod.fst →
      (((imtChainOf sent h).set p (⟨lowAddr, lowValue, key⟩ : ImtLeaf)
        ++ [(⟨key, value, (h[p + 1]?).elim sent Prod.fst⟩ : ImtLeaf)])).Perm
          (imtChainOf sent (Heap.set h key value)) := by
  intro h
  induction h with
  | nil => intro p key value lowAddr lowValue _ hp; simp at hp
  | cons e rest ih =>
    intro p key value lowAddr lowValue hs hp hlk hkn
    obtain ⟨k', v'⟩ := e
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      cases rest with
      | nil =>
        -- The low leaf is the LAST entry: its pointer gap is `lowAddr → sent`.
        simp only [List.getElem?_cons_succ, List.getElem?_nil, Option.elim] at hkn ⊢
        rw [heap_set_cons_gt _ _ key value [] hlk]
        exact List.Perm.refl _
      | cons e' t =>
        obtain ⟨a, b⟩ := e'
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.elim] at hkn ⊢
        rw [heap_set_cons_gt _ _ key value ((a, b) :: t) hlk,
          heap_set_cons_lt a b key value t hkn]
        exact List.Perm.cons _ (List.perm_append_singleton _ _)
    | succ q =>
      simp only [List.getElem?_cons_succ] at hp hkn
      -- The low leaf is in the TAIL, so the head key is below it, hence below `key`.
      have hmem : lowAddr ∈ Heap.keys rest :=
        List.mem_map.mpr ⟨(lowAddr, lowValue), List.mem_of_getElem? hp, rfl⟩
      have hk'low : k' < lowAddr := Heap.sortedKeys_head_lt hs lowAddr hmem
      have hk'key : k' < key := lt_trans hk'low hlk
      have hst : Heap.SortedKeys rest := Heap.sortedKeys_tail hs
      cases rest with
      | nil => simp at hp
      | cons e' t =>
        obtain ⟨a, b⟩ := e'
        have hakey : a < key := by
          have hcons : lowAddr ∈ a :: Heap.keys t := by rwa [Heap.keys_cons] at hmem
          rcases List.mem_cons.mp hcons with heq | hmt
          · rw [← heq]; exact hlk
          · exact lt_trans (Heap.sortedKeys_head_lt hst lowAddr hmt) hlk
        have hihq := ih q key value lowAddr lowValue hst hp hlk hkn
        rw [heap_set_cons_gt k' v' key value ((a, b) :: t) hk'key]
        have hhead : imtChainOf sent ((k', v') :: Heap.set ((a, b) :: t) key value)
            = (⟨k', v', a⟩ : ImtLeaf) :: imtChainOf sent (Heap.set ((a, b) :: t) key value) := by
          rw [heap_set_cons_gt a b key value t hakey]
          rfl
        rw [hhead]
        exact List.Perm.cons _ hihq

/-! ## §3 — THE DEPLOYED AAFI POST SIDE, FORCED IN FULL.

The AIR writes five gates and the landed pre-side law reads two. This section reads all five. -/

/-- The post digest vector a deployed AAFI row produces: the committed pre-vector with the low leaf's
cell relinked and the free slot filled. Everything the gates leave free is a PARAMETER. -/
noncomputable def aafiPostVec (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat) (h : Heap.FeltHeap)
    (hFits : h.length ≤ 2 ^ dep) (p1 p2 : Nat) (key value lowAddr lowValue lowNext : ℤ) :
    List ℤ :=
  (((padVec sent hash dep h hFits).set p1 (imtLeafHash hash ⟨lowAddr, lowValue, key⟩)).set p2
    (imtLeafHash hash ⟨key, value, lowNext⟩))

/-- **`AafiLayoutAt`** — what the five deployed op = 4 gates FORCE about the row's post-root, stated
positionally. ⚑ `h.length ≤ p2` — the free slot being a PADDING cell — is DERIVED from gate (d1)'s
pinned `ZERO8`, never assumed. -/
def AafiLayoutAt (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat) (h : Heap.FeltHeap)
    (hFits : h.length ≤ 2 ^ dep)
    (p1 p2 : Nat) (key value lowAddr lowValue lowNext newRoot : ℤ) : Prop :=
  p1 < h.length ∧ h.length ≤ p2 ∧ p2 < 2 ^ dep ∧ p1 ≠ p2 ∧
  h[p1]? = some (lowAddr, lowValue) ∧
  lowNext = (h[p1 + 1]?).elim sent Prod.fst ∧
  Heap.get h key = none ∧
  newRoot = perfectRoot hash dep
    (aafiPostVec sent hash dep h hFits p1 p2 key value lowAddr lowValue lowNext)

/-- **`AafiLayoutResid`** — the THREE named, per-row, refutable residuals of the two-path extraction.
The first is `MapKindImtGates`'s `OpenResid` at gate (a)'s leaf verbatim. The second is the
`pathCollFind` event for PATH2 against the low-updated vector. The third is
`imtLeafHash hash l = padDigest` at the leaf the TOTAL extractor `chainAt` names for `p2` — the event
that would let a LIVE cell masquerade as the free slot. No hypothesis on `hash` anywhere. -/
def AafiLayoutResid (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat) (h : Heap.FeltHeap)
    (hFits : h.length ≤ 2 ^ dep)
    (steps1 steps2 : List (Bool × ℤ)) (key lowAddr lowValue lowNext : ℤ) : Prop :=
  OpenResid sent hash dep h hFits steps1 ⟨lowAddr, lowValue, lowNext⟩
  ∨ IsSpongeColl hash (pathCollFind hash steps2
      ((padVec sent hash dep h hFits).set (pathPos steps1)
        (imtLeafHash hash ⟨lowAddr, lowValue, key⟩))
      padDigest)
  ∨ imtLeafHash hash (chainAt sent h (pathPos steps2)) = padDigest

/-- ANTI-LAUNDERING: at a good hash all three residuals are REFUTED, so `Resid := True` is
unbuildable and the disjunction below is informative. -/
theorem aafiLayoutResid_refuted {hash : List ℤ → ℤ} (hgood : MapGood hash) (sent : ℤ) (dep : Nat)
    (h : Heap.FeltHeap) (hFits : h.length ≤ 2 ^ dep)
    (steps1 steps2 : List (Bool × ℤ)) (key lowAddr lowValue lowNext : ℤ) :
    ¬ AafiLayoutResid sent hash dep h hFits steps1 steps2 key lowAddr lowValue lowNext := by
  rintro (hres | ⟨hne, he⟩ | hpad)
  · exact openResid_refuted hgood sent dep h hFits steps1 _ hres
  · exact hne (hgood.1 he)
  · exact hgood.2 _ hpad

/-- **★★ THE DEPLOYED AAFI POST SIDE IS FORCED, floor-free.** The proof is the two-path composition:
gate (a)'s update clause turns gate (c) into a NAMED vector for `R1`, then gate (d1) binds `p2` into
THAT vector as a padding cell, so gate (d2) names the post-root. -/
theorem aafiImtGates_force_layout_or_resid (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    {oldRoot newRoot R1 key value lowAddr lowValue lowNext : ℤ}
    {h : Heap.FeltHeap} {steps1 steps2 : List (Bool × ℤ)}
    (hok : (padImtSchema sent).HeapOk h) (hsz : (padImtSchema sent).SizeOk dep h)
    (hcommit : padImtRoot sent hash dep h hsz = oldRoot)
    (hg : AafiImtGatesOn hash dep steps1 steps2 oldRoot newRoot R1 key value lowAddr lowValue
      lowNext) :
    AafiLayoutAt sent hash dep h hsz (pathPos steps1) (pathPos steps2) key value lowAddr lowValue
        lowNext newRoot
    ∨ AafiLayoutResid sent hash dep h hsz steps1 steps2 key lowAddr lowValue lowNext := by
  obtain ⟨hsl1, hsl2, hpne, hpa, hlk, hkn, hpc, hpd1, hpd2⟩ := hg
  have hsz' : h.length ≤ 2 ^ dep := hsz
  rcases padOpen_binds_or_resid sent hash dep hsz hsl1 (by rw [hpa, ← hcommit]) with
    ⟨hlt1, hchain, hentry, hptr, hupd⟩ | hres
  · -- (c): the low-update fold NAMES `R1` as the one-cell update of the committed pre-vector.
    have hR1 : R1 = perfectRoot hash dep
        ((padVec sent hash dep h hsz).set (pathPos steps1)
          (imtLeafHash hash ⟨lowAddr, lowValue, key⟩)) := by
      rw [← hpc]; exact hupd ⟨lowAddr, lowValue, key⟩
    have hV1len : ((padVec sent hash dep h hsz).set (pathPos steps1)
        (imtLeafHash hash ⟨lowAddr, lowValue, key⟩)).length = 2 ^ dep := by
      rw [List.length_set]; exact padVec_length hsz
    by_cases hc2 : IsSpongeColl hash (pathCollFind hash steps2
        ((padVec sent hash dep h hsz).set (pathPos steps1)
          (imtLeafHash hash ⟨lowAddr, lowValue, key⟩)) padDigest)
    · exact Or.inr (Or.inr (Or.inl hc2))
    · -- (d1): PATH2 binds `p2` in that vector; (d2) then NAMES the post-root.
      obtain ⟨hbind2, hupd2⟩ := pathRecompute_binds_updates hash steps2
        ((padVec sent hash dep h hsz).set (pathPos steps1)
          (imtLeafHash hash ⟨lowAddr, lowValue, key⟩)) padDigest
        (by rw [hV1len, hsl2]) (by rw [hsl2, hpd1, hR1]) hc2
      have hpost : newRoot = perfectRoot hash dep
          (aafiPostVec sent hash dep h hsz (pathPos steps1) (pathPos steps2) key value lowAddr
            lowValue lowNext) := by
        rw [← hpd2]
        unfold aafiPostVec
        have := hupd2 (imtLeafHash hash ⟨key, value, lowNext⟩)
        rwa [hsl2] at this
      have hp2lt : pathPos steps2 < 2 ^ dep := by
        rw [← hV1len]
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hbind2
        simp at hbind2
      by_cases hlt2 : pathPos steps2 < h.length
      · -- A LIVE cell reading the padding constant is residual 3, not a free slot.
        refine Or.inr (Or.inr (Or.inr ?_))
        have hVeq : (padVec sent hash dep h hsz)[pathPos steps2]? = some padDigest := by
          rw [← hbind2, List.getElem?_set_ne hpne]
        have hL : ((imtChainOf sent h).map (imtLeafHash hash)).length = h.length := by
          rw [List.length_map, imtChainOf_length]
        have hlive : ((imtChainOf sent h).map (imtLeafHash hash))[pathPos steps2]?
            = some padDigest := by
          rw [← padTo_getElem?_lt dep ((imtChainOf sent h).map (imtLeafHash hash)) _
            (pathPos steps2) (by rw [hL]; exact hlt2)]
          exact hVeq
        rw [List.getElem?_map] at hlive
        cases hcc : (imtChainOf sent h)[pathPos steps2]? with
        | none => rw [hcc] at hlive; simp at hlive
        | some l =>
          rw [hcc] at hlive
          simp only [Option.map_some, Option.some.injEq] at hlive
          simpa [chainAt, hcc] using hlive
      · -- The honest branch: every conjunct of `AafiLayoutAt` is in hand.
        have habs : Heap.get h key = none := by
          have hmem : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf) ∈ imtChainOf sent h :=
            List.mem_of_getElem? hchain
          have hs : ImtSorted (imtChainOf sent h) := imtSchema_chain_imtSorted sent h hok
          have hnotin : key ∉ imtAddrs (imtChainOf sent h) :=
            imtAbsent_excludes hs ⟨⟨lowAddr, lowValue, lowNext⟩, hmem, hlk, hkn⟩
          have hkeys : Heap.keys h = imtAddrs (imtChainOf sent h) := by
            rw [← keys_imtToHeap (imtChainOf sent h), imtToHeap_imtChainOf sent h]
          rw [Heap.get_eq_none_iff, hkeys]; exact hnotin
        exact Or.inl ⟨hlt1, by omega, hp2lt, hpne, hentry, hptr, habs, hpost⟩
  · exact Or.inr (Or.inl hres)

/-- **★ THE POST SIDE AT A GOOD HASH** — the whole layout, with the committed pre-map named. -/
theorem aafiImtRow_forces_layout_of_good {hash : List ℤ → ℤ} (hgood : MapGood hash)
    (sent : ℤ) (dep : Nat) {oldRoot newRoot R1 key value lowAddr lowValue lowNext : ℤ}
    (hr : AafiImtRowAt sent hash dep oldRoot newRoot R1 key value lowAddr lowValue lowNext) :
    ∃ (h : Heap.FeltHeap) (p1 p2 : Nat),
      (padImtSchema sent).HeapOk h ∧ ∃ hsz : (padImtSchema sent).SizeOk dep h,
      padImtRoot sent hash dep h hsz = oldRoot ∧ lowAddr < key ∧ key < lowNext ∧
      AafiLayoutAt sent hash dep h hsz p1 p2 key value lowAddr lowValue lowNext newRoot := by
  obtain ⟨h, steps1, steps2, hok, hsz, hcommit, hg⟩ := hr
  have hbr := hg
  obtain ⟨-, -, -, -, hlk, hkn, -, -, -⟩ := hbr
  rcases aafiImtGates_force_layout_or_resid sent hash dep hok hsz hcommit hg with hlay | hbad
  · exact ⟨h, pathPos steps1, pathPos steps2, hok, hsz, hcommit, hlk, hkn, hlay⟩
  · exact absurd hbad (aafiLayoutResid_refuted hgood sent dep h hsz steps1 steps2 _ _ _ _)


/-! ## §4 — ⚑ THE PAYOFF: THE LIVE ARM ADMITS **NO ERASURE**, and its post-root MOVES. -/

/-- **★★ EVERY OTHER CELL SURVIVES.** Off the low-leaf position and the free slot, the post
commitment's digest vector is *literally* the pre commitment's. Nothing a prover can do to an
accepting op = 4 row touches another entry — which is exactly what
`MapInsertImtRepoint.insertPair_erases_the_rest_of_the_map` shows the op = 3 pairing CAN do. -/
theorem aafiLayout_admits_no_erasure (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (h : Heap.FeltHeap) (hFits : h.length ≤ 2 ^ dep) (p1 p2 : Nat)
    (key value lowAddr lowValue lowNext : ℤ) :
    ∀ i : Nat, i ≠ p1 → i ≠ p2 →
      (aafiPostVec sent hash dep h hFits p1 p2 key value lowAddr lowValue lowNext)[i]?
        = (padVec sent hash dep h hFits)[i]? := by
  intro i hi1 hi2
  rw [aafiPostVec, List.getElem?_set_ne (fun hc => hi2 hc.symm),
    List.getElem?_set_ne (fun hc => hi1 hc.symm)]

/-- **★ THE LOW LEAF KEEPS ITS ENTRY.** The one live cell the row rewrites carries the SAME address
and the SAME value; only the successor POINTER moves, `lowNext → key`. That is `relink_next_addrs`,
and it is why the erasure clause above is the whole story rather than half of it. -/
theorem aafiLayout_low_cell_keeps_addr_and_value (key lowAddr lowValue lowNext : ℤ) :
    (⟨lowAddr, lowValue, key⟩ : ImtLeaf).addr = (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf).addr
    ∧ (⟨lowAddr, lowValue, key⟩ : ImtLeaf).value
        = (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf).value :=
  ⟨rfl, rfl⟩

/-- **★ THE FREE SLOT REALLY WAS EMPTY.** `h.length ≤ p2`, which the gate FORCES, means the cell the
append overwrites held `heap_root.rs`'s padding constant under the pre-root — so the live prefix
GREW and nothing was displaced. -/
theorem aafiLayout_free_slot_was_padding (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    {h : Heap.FeltHeap} {p2 : Nat} (hsz : h.length ≤ 2 ^ dep) (hge : h.length ≤ p2)
    (hlt : p2 < 2 ^ dep) : (padVec sent hash dep h hsz)[p2]? = some padDigest := by
  have hL : ((imtChainOf sent h).map (imtLeafHash hash)).length = h.length := by
    rw [List.length_map, imtChainOf_length]
  rw [padVec, padTo, List.getElem?_append_right (by rw [hL]; exact hge), hL]
  have hlen : (List.replicate (2 ^ dep - h.length) padDigest).length = 2 ^ dep - h.length := by
    simp
  rw [List.getElem?_eq_getElem (by rw [hlen]; omega)]
  simp

/-- **★★ THE POST-ROOT MOVES — the FROZEN-ROOT forgery is refused.** An accepting op = 4 row cannot
republish its own pre-root as its post-root: the two vectors differ at `p2`, where the pre-vector
holds the padding constant and the post-vector holds a live arity-3 leaf digest, which `PadFree3`
separates. An accumulator insert that leaves the accumulator alone has no accepting row. -/
theorem aafiLayout_post_root_moves {hash : List ℤ → ℤ} (hgood : MapGood hash) (sent : ℤ) (dep : Nat)
    {h : Heap.FeltHeap} {p1 p2 : Nat} {key value lowAddr lowValue lowNext oldRoot newRoot : ℤ}
    (hsz : h.length ≤ 2 ^ dep) (hcommit : padImtRoot sent hash dep h hsz = oldRoot)
    (hlay : AafiLayoutAt sent hash dep h hsz p1 p2 key value lowAddr lowValue lowNext newRoot) :
    newRoot ≠ oldRoot := by
  obtain ⟨hlt1, hge2, hlt2, hpne, hentry, hptr, habs, hroot⟩ := hlay
  intro he
  have hvpre : (padVec sent hash dep h hsz).length = 2 ^ dep := padVec_length hsz
  have hvpost : (aafiPostVec sent hash dep h hsz p1 p2 key value lowAddr lowValue lowNext).length
      = 2 ^ dep := by
    rw [aafiPostVec, List.length_set, List.length_set]; exact hvpre
  have heq : perfectRoot hash dep
      (aafiPostVec sent hash dep h hsz p1 p2 key value lowAddr lowValue lowNext)
      = perfectRoot hash dep (padVec sent hash dep h hsz) := by
    rw [← hroot, he, ← hcommit, padImtRoot_eq_padVec]
  rcases perfectRoot_binds_or_collides hash dep hvpost hvpre heq with hveq | hcol
  · have hp2b : p2 < ((padVec sent hash dep h hsz).set p1
        (imtLeafHash hash ⟨lowAddr, lowValue, key⟩)).length := by
      rw [List.length_set, hvpre]; exact hlt2
    have h1 : (aafiPostVec sent hash dep h hsz p1 p2 key value lowAddr lowValue lowNext)[p2]?
        = some (imtLeafHash hash ⟨key, value, lowNext⟩) := by
      rw [aafiPostVec, List.getElem?_set_self hp2b]
    have h2 : (padVec sent hash dep h hsz)[p2]? = some padDigest :=
      aafiLayout_free_slot_was_padding sent hash dep hsz hge2 hlt2
    rw [hveq, h2] at h1
    exact hgood.2 _ (Option.some.inj h1).symm
  · exact spongeColl_refutable_of_injective hash hgood.1 _ hcol

/-! ## §5 — ⚑⚑ THE ELEVENTH APPROACH: A LAYOUT-LEVEL DENOTATION, AND IT IS THE FULL STATEMENT. -/

/-- **`AafiInsertsUpToLayout`** — the deployed `.aafiInsert` DENOTATION. Some admissible sparse map
`h` sits behind the pre-root, the row's key is ABSENT from it, and the post-root is the fold of a
`List.Perm` of the padded commitment vector of `Heap.set h key value`.

⚠ THE PERMUTATION IS NOT SLACK, IT IS THE DEPLOYED LINEAGE. `heap_root.rs` folds append order and the
schema commits sorted order; §7 proves no `opensToMerkleS` statement holds at the post-root at all.
So this is the STRONGEST shape the deployed post-condition has, not a weakened one. -/
def AafiInsertsUpToLayout (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (oldRoot newRoot key value : ℤ) : Prop :=
  ∃ h : Heap.FeltHeap,
    (padImtSchema sent).HeapOk h ∧ ∃ hsz : (padImtSchema sent).SizeOk dep h,
    padImtRoot sent hash dep h hsz = oldRoot ∧
    Heap.get h key = none ∧
    ∃ (hsz' : (Heap.set h key value).length ≤ 2 ^ dep) (V : List ℤ),
      V.Perm (padVec sent hash dep (Heap.set h key value) hsz')
      ∧ perfectRoot hash dep V = newRoot

/-- The layout vector IS a permutation of the correct post-map's commitment vector: §2's chain
permutation, carried through the sparse occupancy by §1's padding algebra. -/
theorem aafiPostVec_perm_of_layout (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    {h : Heap.FeltHeap} {p1 p2 : Nat} {key value lowAddr lowValue lowNext newRoot : ℤ}
    (hok : (padImtSchema sent).HeapOk h) (hsz : (padImtSchema sent).SizeOk dep h)
    (hlk : lowAddr < key) (hkn : key < lowNext)
    (hlay : AafiLayoutAt sent hash dep h hsz p1 p2 key value lowAddr lowValue lowNext newRoot)
    (hsz2 : (Heap.set h key value).length ≤ 2 ^ dep) :
    ((aafiPostVec sent hash dep h hsz p1 p2 key value lowAddr lowValue lowNext)).Perm
      (padVec sent hash dep (Heap.set h key value) hsz2) := by
  obtain ⟨hlt1, hge2, hlt2, hpne, hentry, hptr, habs, hroot⟩ := hlay
  have hsz' : h.length ≤ 2 ^ dep := hsz
  have hclen : (imtChainOf sent h).length = h.length := imtChainOf_length sent h
  have hLlen : ((imtChainOf sent h).map (imtLeafHash hash)).length = h.length := by
    rw [List.length_map, hclen]
  -- Step 1: the `p1` set moves inside the padding, and inside the `map`.
  have hMlen0 : (((imtChainOf sent h).set p1 (⟨lowAddr, lowValue, key⟩ : ImtLeaf)).map
      (imtLeafHash hash)).length ≤ 2 ^ dep := by
    rw [List.length_map, List.length_set, hclen]; exact hsz'
  have hSetMap : ((imtChainOf sent h).set p1 (⟨lowAddr, lowValue, key⟩ : ImtLeaf)).map
      (imtLeafHash hash)
      = ((imtChainOf sent h).map (imtLeafHash hash)).set p1
          (imtLeafHash hash ⟨lowAddr, lowValue, key⟩) :=
    map_set' (imtLeafHash hash) (imtChainOf sent h) p1 _
  have hSetFits : (((imtChainOf sent h).map (imtLeafHash hash)).set p1
      (imtLeafHash hash ⟨lowAddr, lowValue, key⟩)).length ≤ 2 ^ dep := by
    rw [List.length_set, hLlen]; exact hsz'
  have h1 : (padVec sent hash dep h hsz).set p1 (imtLeafHash hash ⟨lowAddr, lowValue, key⟩)
      = padTo dep (((imtChainOf sent h).set p1 (⟨lowAddr, lowValue, key⟩ : ImtLeaf)).map
          (imtLeafHash hash)) hMlen0 := by
    rw [padTo_congr hSetMap hMlen0 hSetFits]
    exact (padTo_set dep _ p1 _ (by rw [hLlen]; exact hlt1)).symm
  -- Step 2: the `p2` set past the live prefix is an APPEND, up to `List.Perm`.
  have hMlen : (((imtChainOf sent h).set p1 (⟨lowAddr, lowValue, key⟩ : ImtLeaf)).map
      (imtLeafHash hash)).length = h.length := by
    rw [List.length_map, List.length_set, hclen]
  have hApp : ((((imtChainOf sent h).set p1 (⟨lowAddr, lowValue, key⟩ : ImtLeaf)).map
      (imtLeafHash hash)) ++ [imtLeafHash hash ⟨key, value, lowNext⟩]).length ≤ 2 ^ dep := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
      List.length_set]
    rw [hclen]; omega
  have h2 := padTo_set_pad_perm dep
    (((imtChainOf sent h).set p1 (⟨lowAddr, lowValue, key⟩ : ImtLeaf)).map (imtLeafHash hash))
    p2 (imtLeafHash hash ⟨key, value, lowNext⟩) (by rw [hMlen]; exact hge2) hlt2 hMlen0 hApp
  -- Step 3: the appended layout is the inserted map's chain, permuted (§2).
  have hkn' : key < (h[p1 + 1]?).elim sent Prod.fst := by rw [← hptr]; exact hkn
  have hchainperm : ((((imtChainOf sent h).set p1 (⟨lowAddr, lowValue, key⟩ : ImtLeaf))
      ++ [(⟨key, value, lowNext⟩ : ImtLeaf)])).Perm
        (imtChainOf sent (Heap.set h key value)) := by
    have hp := chain_relink_snoc_perm sent h p1 key value lowAddr lowValue hok.1 hentry hlk hkn'
    rwa [← hptr] at hp
  have h3 : ((((imtChainOf sent h).set p1 (⟨lowAddr, lowValue, key⟩ : ImtLeaf)).map
      (imtLeafHash hash)) ++ [imtLeafHash hash ⟨key, value, lowNext⟩]).Perm
        ((imtChainOf sent (Heap.set h key value)).map (imtLeafHash hash)) := by
    simpa using hchainperm.map (imtLeafHash hash)
  have hgoal : aafiPostVec sent hash dep h hsz p1 p2 key value lowAddr lowValue lowNext
      = (padTo dep (((imtChainOf sent h).set p1 (⟨lowAddr, lowValue, key⟩ : ImtLeaf)).map
          (imtLeafHash hash)) hMlen0).set p2 (imtLeafHash hash ⟨key, value, lowNext⟩) := by
    unfold aafiPostVec
    rw [h1]
  have hPostFits : ((imtChainOf sent (Heap.set h key value)).map (imtLeafHash hash)).length
      ≤ 2 ^ dep := by
    rw [List.length_map, imtChainOf_length]; exact hsz2
  rw [hgoal]
  exact h2.trans (padTo_perm_of_perm dep h3 hApp hPostFits)

/-- **★★ THE LIVE-ARM LAW.** An accepting deployed AAFI row forces the layout denotation: absence
before, and a post-root that commits the correctly-inserted map up to leaf PLACEMENT. Floor-free —
`MapGood` is `padImtTeeth`'s own `Good` field. -/
theorem aafiImtRow_forces_insertsUpToLayout_of_good {hash : List ℤ → ℤ} (hgood : MapGood hash)
    (sent : ℤ) (dep : Nat) {oldRoot newRoot R1 key value lowAddr lowValue lowNext : ℤ}
    (hr : AafiImtRowAt sent hash dep oldRoot newRoot R1 key value lowAddr lowValue lowNext) :
    AafiInsertsUpToLayout sent hash dep oldRoot newRoot key value := by
  obtain ⟨h, p1, p2, hok, hsz, hcommit, hlk, hkn, hlay⟩ :=
    aafiImtRow_forces_layout_of_good hgood sent dep hr
  -- ⚑ THE POST HEAP FITS, and the OBLIGATION IS WHERE THE FACT COMES FROM. `Heap.set` at an
  -- ABSENT key GROWS by one, so `h.length ≤ 2 ^ dep` alone would NOT do — a full tree admits no
  -- insert. The gate's own `h.length ≤ p2 < 2 ^ dep` is what makes room, and before `padVec` took
  -- the obligation nothing in this file had to notice that.
  have hsz2 : (Heap.set h key value).length ≤ 2 ^ dep := by
    have habs : Heap.get h key = none := hlay.2.2.2.2.2.2.1
    have hnk : key ∉ Heap.keys h := (Heap.get_eq_none_iff h key).mp habs
    rw [Heap.length_set_fresh h key value hnk]
    have hge2 : h.length ≤ p2 := hlay.2.1
    have hlt2 : p2 < 2 ^ dep := hlay.2.2.1
    omega
  refine ⟨h, hok, hsz, hcommit, hlay.2.2.2.2.2.2.1, hsz2, _,
    aafiPostVec_perm_of_layout sent hash dep hok hsz hlk hkn hlay hsz2, ?_⟩
  exact hlay.2.2.2.2.2.2.2.symm

/-- **★ AND THE PRE SIDE COMES ALONG UNCHANGED** — the double-spend tooth `MapKindImtGates` landed,
restated as the first half of the live-arm denotation so a consumer reads one object. -/
theorem aafiImtRow_forces_both_sides_of_good {hash : List ℤ → ℤ} (hgood : MapGood hash)
    (sent : ℤ) (dep : Nat) {oldRoot newRoot R1 key value lowAddr lowValue lowNext : ℤ}
    (hr : AafiImtRowAt sent hash dep oldRoot newRoot R1 key value lowAddr lowValue lowNext) :
    opensToMerkleS (padImtSchema sent) hash dep oldRoot key none
      ∧ AafiInsertsUpToLayout sent hash dep oldRoot newRoot key value :=
  ⟨aafiImtRow_forces_absence_of_good hgood sent dep hr,
    aafiImtRow_forces_insertsUpToLayout_of_good hgood sent dep hr⟩

/-! ## §6 — THE REPOINTED `.aafiInsert` DISPATCH.

The live arm is judged by the shape that ships. Every other kind is left EXACTLY as it was, so this
composes additively with `MapReconcileImtRepoint`'s `.absent` repoint and
`MapInsertImtRepoint`'s `.insert` repoint. -/

/-- **`AafiRowImtAt`** — the deployed op = 4 acceptance AT THE ROW'S COLUMNS. `MAP_R1`,
`MAP_LOW_ADDR`, `MAP_LOW_VALUE` and `MAP_NEXT` are real deployed columns that `MapOp` has no fields
for, so they ride existentially, exactly as `ReconcileGatesAt`'s `vOld` does. ⚠ `MAP_NEXT` is ONE
column, shared by gate (a)'s low leaf and gate (d2)'s appended leaf — which is why `lowNext` occurs
twice in `AafiImtGatesOn` rather than as two variables. -/
def AafiRowImtAt (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat) (a : Assignment) (m : MapOp) : Prop :=
  ∃ R1 lowAddr lowValue lowNext : ℤ,
    AafiImtRowAt sent hash dep ((m.root 0).eval a) ((m.newRoot 0).eval a) R1
      (m.key.eval a) (m.value.eval a) lowAddr lowValue lowNext

/-- **`ReconcileGatesImtAafiAt`** — `ReconcileGatesAt` with the `.aafiInsert` dispatch REPOINTED,
written as two guarded arms so the dispatch is visible in the statement. -/
def ReconcileGatesImtAafiAt (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (a : Assignment) (m : MapOp) : Prop :=
  (m.op = MapOpKind.aafiInsert → AafiRowImtAt sent hash dep a m) ∧
  (m.op ≠ MapOpKind.aafiInsert → ReconcileGatesAt hash dep a m)

theorem reconcileGatesImtAafi_aafi (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (a : Assignment) (m : MapOp) (hop : m.op = MapOpKind.aafiInsert) :
    ReconcileGatesImtAafiAt sent hash dep a m ↔ AafiRowImtAt sent hash dep a m :=
  ⟨fun h => h.1 hop, fun h => ⟨fun _ => h, fun hne => absurd hop hne⟩⟩

theorem reconcileGatesImtAafi_of_ne_aafi (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (a : Assignment) (m : MapOp) (hop : m.op ≠ MapOpKind.aafiInsert) :
    ReconcileGatesImtAafiAt sent hash dep a m ↔ ReconcileGatesAt hash dep a m :=
  ⟨fun h => h.2 hop, fun h => ⟨fun hins => absurd hins hop, fun _ => h⟩⟩

/-- **The per-trace REPOINTED model** — the drop-in twin of `MapOpsColumnLayout.MapReconcileModelOk`
and of `MapInsertImtRepoint.MapInsertReconcileModelOk`, at the same deployed depth. -/
def MapAafiReconcileModelOk (sent : ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (t : VmTrace) : Prop :=
  ∀ i < t.rows.length, ∀ m ∈ mapOpsOf d,
    m.guard.eval (envAt t i).loc = 1 →
      ReconcileGatesImtAafiAt sent hash MAP_TREE_DEPTH (envAt t i).loc m

/-- **`MapOpImtAafiHoldsAt`** — the repointed `.aafiInsert` DENOTATION: on a fired AAFI row the key
was absent under the pre-root, and the post-root commits the inserted map up to leaf placement.
⚑ There is deliberately no `writesToMerkleS` conjunct and no `insertsFreshS` conjunct: §7 proves
BOTH are unavailable at the deployed post-root, at every schema and at a concrete accepting row. -/
def MapOpImtAafiHoldsAt (sent : ℤ) (hash : List ℤ → ℤ) (env : VmRowEnv) (m : MapOp) : Prop :=
  m.op = MapOpKind.aafiInsert → m.guard.eval env.loc = 1 →
    opensToMerkleS (padImtSchema sent) hash MAP_TREE_DEPTH ((m.root 0).eval env.loc)
        (m.key.eval env.loc) none
    ∧ AafiInsertsUpToLayout sent hash MAP_TREE_DEPTH ((m.root 0).eval env.loc)
        ((m.newRoot 0).eval env.loc) (m.key.eval env.loc) (m.value.eval env.loc)

/-- **★ THE REPOINTED PER-ROW LAW.** -/
theorem aafiRowImt_forces_denotation {hash : List ℤ → ℤ} (hgood : MapGood hash)
    (sent : ℤ) (dep : Nat) (a : Assignment) (m : MapOp) (hg : AafiRowImtAt sent hash dep a m) :
    opensToMerkleS (padImtSchema sent) hash dep ((m.root 0).eval a) (m.key.eval a) none
      ∧ AafiInsertsUpToLayout sent hash dep ((m.root 0).eval a) ((m.newRoot 0).eval a)
          (m.key.eval a) (m.value.eval a) := by
  obtain ⟨R1, lowAddr, lowValue, lowNext, hr⟩ := hg
  exact aafiImtRow_forces_both_sides_of_good hgood sent dep hr

/-- **★ THE REPOINTED `.mapOp` ARM (∀ d), for the LIVE leg.** The twin of
`MapInsertImtRepoint.mapOpsArmImtInsert_of_modeler` on the arm that actually ships — and, like it, it
carries NO floor in its type. -/
theorem mapOpsArmImtAafi_of_modeler {hash : List ℤ → ℤ} (hgood : MapGood hash) (sent : ℤ)
    (d : EffectVmDescriptor2) (t : VmTrace) (hok : MapAafiReconcileModelOk sent hash d t) :
    ∀ i < t.rows.length, ∀ m : MapOp, VmConstraint2.mapOp m ∈ d.constraints →
      MapOpImtAafiHoldsAt sent hash (envAt t i) m := by
  intro i hi m hm hop hguard
  have hmem : m ∈ mapOpsOf d := mem_mapOpsOf.mpr hm
  exact aafiRowImt_forces_denotation hgood sent MAP_TREE_DEPTH (envAt t i).loc m
    ((hok i hi m hmem hguard).1 hop)

/-! ## §7 — ⚑⚑ THE ELEVENTH IMPOSSIBILITY: THE DEPLOYED AAFI POST-ROOT IS NOT A COMMITMENT AT ALL.

`no_schema_commits_the_append_order_layout` refuted a UNIFORM law. This is sharper and lands where a
consumer stands: at ONE deployed row's post-root, `opensToMerkleS` is FALSE for EVERY key and EVERY
value, so `insertsFreshS` — the honest limit `MapInsertImtRepoint` found for the op = 3 pairing — is
also unavailable here. The reason is one line: `imtChainOf` is address-SORTED and the append-order
layout of an INTERIOR insert is not. -/

section Interior

def intSent : ℤ := 100
def intHeap : Heap.FeltHeap := [(1, 7), (9, 3)]

/-- The deployed AAFI post-LAYOUT for inserting `5` into `[(1,7),(9,3)]`: the low leaf relinked
`9 → 5` in place, and the new leaf pushed at `next_free_index = 2`. Append order, `free_index` last —
`insert_witness_aafi:1210-1213` verbatim. -/
def intPhys : List ImtLeaf := [⟨1, 7, 5⟩, ⟨9, 3, 100⟩, ⟨5, 2, 9⟩]

theorem intPhys_addrs : imtAddrs intPhys = [(1 : ℤ), 9, 5] := rfl

theorem intHeap_ok : (padImtSchema intSent).HeapOk intHeap := by
  refine ⟨by simp [Heap.SortedKeys, Heap.keys, intHeap], ?_⟩
  intro x hx
  simp only [intHeap, Heap.keys, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl <;> norm_num [intSent]

theorem intHeap_sz (dep : Nat) (hdep : 2 ≤ dep) : (padImtSchema intSent).SizeOk dep intHeap := by
  show (intHeap.length : Nat) ≤ 2 ^ dep
  have h4 : (4 : Nat) ≤ 2 ^ dep := by
    calc (4 : Nat) = 2 ^ 2 := rfl
      _ ≤ 2 ^ dep := Nat.pow_le_pow_right (by norm_num) hdep
  show (2 : Nat) ≤ 2 ^ dep
  omega

/-- **★ THE APPEND-ORDER LAYOUT IS THE RELINKED CHAIN OF NO ADMISSIBLE HEAP.** `imtChainOf`'s
addresses are `Heap.keys`, which `HeapOk` makes strictly increasing; `intPhys`'s are `[1, 9, 5]`. No
hash, no depth, no floor. -/
theorem intPhys_is_no_relinked_chain (h' : Heap.FeltHeap)
    (hok : (padImtSchema intSent).HeapOk h') : intPhys ≠ imtChainOf intSent h' := by
  intro he
  have hkeys : Heap.keys h' = imtAddrs (imtChainOf intSent h') := by
    rw [← keys_imtToHeap (imtChainOf intSent h'), imtToHeap_imtChainOf intSent h']
  rw [← he, intPhys_addrs] at hkeys
  have hs : (Heap.keys h').Pairwise (· < ·) := hok.1
  rw [hkeys] at hs
  have h95 := (List.pairwise_cons.mp ((List.pairwise_cons.mp hs).2)).1 5 (by simp)
  omega

/-- The physical layout fits, from the section's own `2 ≤ dep` — `heap_fits` cannot reach
`3 ≤ 2 ^ dep` at a SYMBOLIC exponent, and `fits_of_pow_le` is the bridge. -/
theorem intPhys_fits {dep : Nat} (hdep : 2 ≤ dep) : intPhys.length ≤ 2 ^ dep :=
  fits_of_pow_le hdep (by decide)

/-- The post-root an accepting op = 4 row over `intHeap` at fresh key `5` produces. -/
noncomputable def intPostRoot (dep : Nat) (hdep : 2 ≤ dep) : ℤ :=
  appendOrderRoot oddSponge dep intPhys (intPhys_fits hdep)

/-- **⚑⚑ THE ELEVENTH IMPOSSIBILITY.** The deployed AAFI post-root of an INTERIOR insert opens
NOTHING: it is the `padImtSchema` commitment of no admissible heap, so `opensToMerkleS` is false at
it for every key and every option. (Anti-floor content: the conclusion is `False`.) -/
theorem aafi_interior_post_admits_no_opening (dep : Nat) (hdep : 2 ≤ dep) (k : ℤ) (o : Option ℤ) :
    ¬ opensToMerkleS (padImtSchema intSent) oddSponge dep (intPostRoot dep hdep) k o := by
  rintro ⟨h', hok, hsz, hcommit, -⟩
  have h4 : (4 : Nat) ≤ 2 ^ dep := fits_of_pow_le hdep (by decide)
  have hsz' : h'.length ≤ 2 ^ dep := hsz
  have hcl : (imtChainOf intSent h').length ≤ 2 ^ dep := by rw [imtChainOf_length]; exact hsz'
  have hpl : (intPhys).length ≤ 2 ^ dep := intPhys_fits hdep
  have he : appendOrderRoot oddSponge dep intPhys hpl
      = appendOrderRoot oddSponge dep (imtChainOf intSent h') hcl := by
    rw [← padImtRoot_eq_appendOrderRoot intSent oddSponge dep h' hsz']
    exact (hcommit.trans rfl).symm
  exact intPhys_is_no_relinked_chain h' hok
    (appendOrderRoot_binds mapGood_inhabited dep hpl hcl he)

/-! ### §7b — the SAME, on a REAL accepting row, so the refutation bites gate data.

At `dep = 2` the four-leaf commitment holds three live cells and the two deployed paths are explicit
cons-lists whose every obligation is `rfl`. ⚠ LABELLED: this exhibit is at depth 2, not at
`MAP_TREE_DEPTH`; §8's depth-16 exhibit is the MAXIMUM-key row, where append order and sorted order
coincide, which is precisely why an INTERIOR one is needed to see the impossibility at all. -/

noncomputable def iy0' : ℤ := imtLeafHash oddSponge ⟨1, 7, 5⟩
noncomputable def iy1 : ℤ := imtLeafHash oddSponge ⟨9, 3, 100⟩
noncomputable def iy2 : ℤ := imtLeafHash oddSponge ⟨5, 2, 9⟩

/-- Position 0's depth-2 membership path: level-0 sibling is cell 1, level-1 sibling is the
all-padding right subtree. -/
noncomputable def iPath1 : List (Bool × ℤ) :=
  [(false, mapNode oddSponge padDigest padDigest), (false, iy1)]

/-- Position 2's depth-2 membership path: level-0 sibling is the padding cell 3, level-1 sibling is
the node over cells 0 and 1 — read UNDER `R1`, i.e. with the low leaf already relinked. -/
noncomputable def iPath2 : List (Bool × ℤ) :=
  [(true, mapNode oddSponge iy0' iy1), (false, padDigest)]

noncomputable def iR1 : ℤ :=
  mapNode oddSponge (mapNode oddSponge iy0' iy1) (mapNode oddSponge padDigest padDigest)

theorem iNewRoot_eq : mapNode oddSponge (mapNode oddSponge iy0' iy1) (mapNode oddSponge iy2 padDigest)
    = intPostRoot 2 (le_refl 2) := rfl

/-- **★★ A REAL ACCEPTING DEPLOYED AAFI ROW AT AN INTERIOR KEY.** All five gates, every path
obligation `rfl`, over the sparse `2^2`-leaf commitment of `[(1,7),(9,3)]` at fresh key `5`. -/
theorem aafi_interior_row_at_depth2 :
    AafiImtRowAt intSent oddSponge 2 (padImtRoot intSent oddSponge 2 intHeap)
      (intPostRoot 2 (le_refl 2)) iR1 5 2 1 7 9 :=
  ⟨intHeap, iPath1, iPath2, intHeap_ok, intHeap_sz 2 (le_refl 2), rfl,
    rfl, rfl, by decide, rfl, by norm_num, by norm_num, rfl, rfl, rfl⟩

/-- **⚑⚑ AND ITS POST-ROOT ADMITS NO OPENING.** So the AAFI post side is not `insertsFreshS`, not
`writesToMerkleS`, and not any `opensToMerkleS`-shaped statement — on an accepting row. -/
theorem aafi_interior_row_post_admits_no_opening (k : ℤ) (o : Option ℤ) :
    ¬ opensToMerkleS (padImtSchema intSent) oddSponge 2 (intPostRoot 2 (le_refl 2)) k o :=
  aafi_interior_post_admits_no_opening 2 (le_refl 2) k o

/-- **⚑⚑ `insertsFreshS` IS REFUTED AT THE AAFI POST SIDE.** `MapInsertImtRepoint` found
`insertsFreshS` to be the honest denotation of the op = 3 pairing. It is NOT available on the live
arm, because its second conjunct is an `opensToMerkleS` at the post-root. (Conclusion `False`.) -/
theorem aafi_post_cannot_be_insertsFreshS :
    ¬ (∀ (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
        (oldRoot newRoot R1 key value lowAddr lowValue lowNext : ℤ),
        MapGood hash →
        AafiImtRowAt sent hash dep oldRoot newRoot R1 key value lowAddr lowValue lowNext →
        insertsFreshS (padImtSchema sent) hash dep oldRoot key value newRoot) := by
  intro hbad
  exact aafi_interior_row_post_admits_no_opening 5 (some 2)
    (hbad intSent oddSponge 2 _ (intPostRoot 2 (le_refl 2)) iR1 5 2 1 7 9 mapGood_inhabited
      aafi_interior_row_at_depth2).2

/-- **★ AND THE LAYOUT DENOTATION DOES HOLD ON THAT SAME ROW** — the discrimination that makes §5 a
statement rather than a retreat: the interior row satisfies `AafiInsertsUpToLayout` while satisfying
no `opensToMerkleS` at its post-root. -/
theorem aafi_interior_row_satisfies_the_layout_denotation :
    AafiInsertsUpToLayout intSent oddSponge 2 (padImtRoot intSent oddSponge 2 intHeap)
      (intPostRoot 2 (le_refl 2)) 5 2 :=
  aafiImtRow_forces_insertsUpToLayout_of_good mapGood_inhabited intSent 2
    aafi_interior_row_at_depth2

end Interior

/-! ## §8 — NON-VACUITY AT `MAP_TREE_DEPTH = 16` OVER A SPARSE TREE.

Reuse, do not rebuild: `MapKindImtGates.bite_aafi_row` is the deployed AAFI row over a `2^16`-leaf
commitment holding ONE live leaf, its paths the symbolic `leftPadPath` / `slot1Path` recursions whose
siblings are `heap_root.rs`'s `EMPTY_SUBTREE_ROOTS`, every root NAMED as the schema's own `commit`.
Nothing is enumerated and no `2^16` object is constructed. -/

/-- **★★ THE LIVE-ARM LAW FIRES AT THE DEPLOYED DEPTH.** -/
theorem bite_aafi_layout_fires :
    AafiInsertsUpToLayout biteSent oddSponge MAP_TREE_DEPTH biteRoot aafiNewRoot 5 2 :=
  aafiImtRow_forces_insertsUpToLayout_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH
    bite_aafi_row

/-- **★★ BOTH SIDES, on one deployed row at depth 16.** -/
theorem bite_aafi_both_sides_fire :
    opensToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 5 none
      ∧ AafiInsertsUpToLayout biteSent oddSponge MAP_TREE_DEPTH biteRoot aafiNewRoot 5 2 :=
  aafiImtRow_forces_both_sides_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH bite_aafi_row

/-- **★★ THE TOOTH — the FROZEN-ROOT forgery is refused at depth 16.** No accepting deployed AAFI
row over this pre-root can republish it as its post-root. -/
theorem bite_aafi_post_root_moves : aafiNewRoot ≠ biteRoot := by
  obtain ⟨h, p1, p2, hok, hsz, hcommit, hlk, hkn, hlay⟩ :=
    aafiImtRow_forces_layout_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH bite_aafi_row
  exact aafiLayout_post_root_moves mapGood_inhabited biteSent MAP_TREE_DEPTH hsz hcommit hlay

/-- **★ THE SECOND TOOTH, at depth 16 and through the NEW law**: the deployed AAFI row cannot claim
its key was already committed. (`MapKindImtGates.bite_aafi_present_key_refused` is the pre-side twin;
this one runs through the layout extraction, so it bites even on a row whose post-root is honest.) -/
theorem bite_aafi_key_is_absent_before :
    Heap.get biteHeap (5 : ℤ) = none := by decide

/-! ### §8b — the model-level exhibit: one descriptor, one trace, one fired `.aafiInsert` row. -/

section ModelExhibit

/-- An `.aafiInsert`-op row vehicle on wires 0/1/2/3, the `MapInsertImtRepoint.insRow` wiring. -/
def aafiOp : MapOp :=
  { guard := .const 1, root := fun _ => .var 0, key := .var 1, value := .var 2
  , newRoot := fun _ => .var 3, op := .aafiInsert }

def aafiRow (r k v r' : ℤ) : Assignment := fun c =>
  if c = 0 then r else if c = 1 then k else if c = 2 then v else if c = 3 then r' else 0

theorem aafiRow_root (r k v r' : ℤ) : (aafiOp.root 0).eval (aafiRow r k v r') = r := rfl
theorem aafiRow_key (r k v r' : ℤ) : aafiOp.key.eval (aafiRow r k v r') = k := rfl
theorem aafiRow_value (r k v r' : ℤ) : aafiOp.value.eval (aafiRow r k v r') = v := rfl
theorem aafiRow_newRoot (r k v r' : ℤ) : (aafiOp.newRoot 0).eval (aafiRow r k v r') = r' := rfl
theorem aafiOp_op : aafiOp.op = MapOpKind.aafiInsert := rfl

def dAafi : EffectVmDescriptor2 :=
  { name := "map-aafi-insert-fresh-key"
  , traceWidth := 4
  , piCount := 0
  , tables := []
  , constraints := [VmConstraint2.mapOp aafiOp]
  , hashSites := []
  , ranges := [] }

theorem dAafi_mapOps : mapOpsOf dAafi = [aafiOp] := rfl

theorem mem_dAafi {m : MapOp} (h : m ∈ mapOpsOf dAafi) : m = aafiOp := by
  rw [dAafi_mapOps] at h
  simpa using h

def traceAafi (r k v r' : ℤ) : VmTrace :=
  { rows := [aafiRow r k v r'], pub := fun _ => 0, tf := fun _ => [] }

theorem traceAafi_rows_length (r k v r' : ℤ) : (traceAafi r k v r').rows.length = 1 := rfl
theorem traceAafi_loc (r k v r' : ℤ) :
    (envAt (traceAafi r k v r') 0).loc = aafiRow r k v r' := rfl

/-- **★ THE REPOINTED PREMISE HOLDS on the deployed depth-16 AAFI row.** -/
theorem bite_aafi_model_holds :
    MapAafiReconcileModelOk biteSent oddSponge dAafi (traceAafi biteRoot 5 2 aafiNewRoot) := by
  intro i hi m hm hguard
  have hi0 : i = 0 := by rw [traceAafi_rows_length] at hi; omega
  subst hi0
  rw [mem_dAafi hm, traceAafi_loc]
  refine ⟨fun _ => ⟨aafiR1, 1, 7, biteSent, ?_⟩, fun hne => absurd rfl hne⟩
  rw [aafiRow_root, aafiRow_newRoot, aafiRow_key, aafiRow_value]
  exact bite_aafi_row

/-- **★ AND THE REPOINTED DENOTATION IS DELIVERED THROUGH THE ARM**, not by hand. -/
theorem bite_aafi_denotation_holds :
    MapOpImtAafiHoldsAt biteSent oddSponge (envAt (traceAafi biteRoot 5 2 aafiNewRoot) 0) aafiOp :=
  mapOpsArmImtAafi_of_modeler mapGood_inhabited biteSent dAafi
    (traceAafi biteRoot 5 2 aafiNewRoot) bite_aafi_model_holds 0
    (by rw [traceAafi_rows_length]; omega) aafiOp (List.mem_singleton_self _)

end ModelExhibit

/-! ## §9 — THE WIDE TWIN: the blind spot, and the impossibility that IS the fix.

`MapOpWideKeyWeld.demoInsertGateW_accepts` ran `MapOpKind.insert` at `keyLo`, which `demoHeapW`
ALREADY HOLDS. It is RENAMED `demoValueUpdateGateW_accepts` in that file, with
`demoValueUpdateGateW_key_is_already_committed` promoted from prose to a theorem beside it.

⚑ A fresh-key twin at the wide shape does not exist and CANNOT be written. Below is why, FLOOR-FREE:
the denotation both write-shaped wide arms conclude has `h.length = 2 ^ dep` on the pre-heap AND on
the written heap, and `Heap.length_set_fresh` grows by exactly one. So the DENSE extraction premise —
not any hash property — forbids growth, at every `LaneEnc` and every depth. That impossibility is the
deliverable; there is nothing to add a witness for. -/

section WideTwin

open Dregg2.Circuit.MapOpWideKeyGate (LaneEnc mapRootW writesToMerkleW)
open Dregg2.Circuit.MapOpWideKeyWeld (writesToMerkleW_forces_present)

variable {K : Type} [LinearOrder K]

/-- **⚑ THE WIDE WRITE-SHAPED DENOTATION NEVER GROWS THE MAP** — hence no accepting wide `.insert` /
`.aafiInsert` row can be at a fresh key, at ANY `LaneEnc` and ANY depth. Floor-free: the obstruction
is the DENSE occupancy in the extraction premise, and `Heap.length_set_fresh` alone. -/
theorem wide_insert_never_grows_the_map (hash : List ℤ → ℤ) (E : LaneEnc K) (dep : Nat)
    {r : ℤ} {k : K} {v r' : ℤ} (hw : writesToMerkleW hash E dep r k v r') :
    ∃ h : List (K × ℤ), E.HeapOk h ∧ h.length = 2 ^ dep ∧ mapRootW hash E dep h = r
      ∧ k ∈ Heap.keys h ∧ (Heap.set h k v).length = h.length := by
  obtain ⟨h, hok, hlen, hroot, hk, hr'⟩ := writesToMerkleW_forces_present hash E dep hw
  exact ⟨h, hok, hlen, hroot, hk,
    Heap.length_set_mem h k v (E.heapOk_sorted h hok) hk⟩

/-- **⚑ AND THE OBSTRUCTION, STATED AS THE IMPOSSIBILITY.** There is no wide write-shaped witness at
a fresh key — the hypothesis and the conclusion are jointly unsatisfiable, for every encoding and
every depth. (Anti-floor content: the conclusion is `False`.) -/
theorem wide_insert_unsat_at_fresh_key (hash : List ℤ → ℤ) (E : LaneEnc K) (dep : Nat)
    {r : ℤ} {k : K} {v r' : ℤ} (h : List (K × ℤ))
    (hw : writesToMerkleW hash E dep r k v r')
    (hfresh : ∀ h' : List (K × ℤ), E.HeapOk h' → h'.length = 2 ^ dep →
      mapRootW hash E dep h' = r → k ∉ Heap.keys h') : False := by
  obtain ⟨h', hok, hlen, hroot, hk, -⟩ := wide_insert_never_grows_the_map hash E dep hw
  exact hfresh h' hok hlen hroot hk

end WideTwin

/-! ## §10 — ⚑ THE FLOOR-RATCHET ENTRIES, ADJUDICATED — and the premise this lane was handed is a
CATEGORY ERROR that has to be corrected before any of them can be read.

The brief (and `MapInsertImtRepoint` §9:885) says *"NINE of these are registered keystones in
`Dregg2/Verify/FloorRatchetBaseline.lean`, so the vacuity is load-bearing in the assurance case."*
Three things about that sentence are wrong, and the third one matters most.

**(i) `FloorRatchetBaseline` IS NOT A KEYSTONE REGISTRY.** Its own header (`:1-14`) says what it is:
*"Every name here is a declaration whose type takes a hypothesis this tree PROVES FALSE at deployed
BabyBear parameters, so the declaration is VACUOUS. They are grandfathered because they cannot all be
ported at once — this file is the RATCHET, and its only healthy direction is SHORTER."* Registration
is a recorded ADMISSION of vacuity, not a load-bearing claim. Structurally it is twelve flat
`Array String` literals of declaration names (`c0`..`c10` + `manual`), concatenated at `:2282-2283`;
there is no keystone field, no satisfiability witness, no teeth.

**(ii) THE KEYSTONE MECHANISM IS A DIFFERENT INSTRUMENT, AND NONE OF THESE NAMES IS IN IT.**
`Dregg2/Verify/KeystoneLint.lean`'s `@[load_bearing_keystone satisfiable := … teeth := …]` +
`#keystone_audit` is the instrument that demands a non-vacuity witness and a discriminating
counter-instance. Zero `@[load_bearing_keystone]` attributes exist on any §9 name, and none appears
in `metatheory/docs/KEYSTONE-LEDGER.md`.

**(iii) ⚑ THE REAL FINDING IS WORSE THAN THE ONE CLAIMED: NO LIVE GATE SEES THIS VACUITY AT ALL.**
The ten entries below are baselined because they carry the REFUTED `Poseidon2SpongeCR` floor — a
different axis entirely. Their PREMISE vacuity (the hypothesis is false on every deployed row) is
invisible to the floor ratchet, invisible to `#keystone_audit`, and invisible to
`check-floor-baseline-preflight.sh`. The vacuity is not "load-bearing in the assurance case"; it is
UNDETECTED, which is the sharper problem.

**⚠ AND THE PRESCRIBED REMEDY WOULD TURN THE GATE RED.** The brief says such an entry *"should be
removed from the baseline"*. It must NOT be, while the declaration still carries the floor:
`FloorRatchet.check` (`:524-530`) errors on any carrier NOT in the baseline, and reports a baseline
name that is no longer a carrier as harmless SLACK. Deleting a live carrier's line is a build ERROR,
not a cleanup. The only legal way off the baseline is to make the declaration stop carrying the
floor — i.e. to port it to the `_or_resid` idiom, which is what this file and `MapKindImtGates` do
for the narrow shape.

### The line numbers, corrected

Of the nine cited baseline lines, **one** (`:941`) lands on a name §9 discusses. `:945` and `:973`
are the `.read` legs — the ones §9 itself calls SOUND; `:984`/`:988` are group-B names; `:985` is
`noLeafColl_of_CR`; `:2042`/`:2046` are in `FinInjectivityCollapse` and `Freshness`, unrelated
modules. The cited set is consistent with an off-by-one against `{940, 944, 972, 983, 984, 987}`
after one baseline line was deleted, but even then two entries are group B and two are unrelated.
The real count is **TEN, not nine**, and here they are with their true lines.

### The ten, adjudicated

| baseline | declaration | verdict |
|---|---|---|
| `:940` | `MapOpWideKeyRowBoundary.demoRow_insert_then_absent_unsat` | **RESTATE.** Its accepting-row input is the mislabeled `demoInsertGateW_accepts`, renamed here; the theorem is TRUE and non-vacuous *as a statement about a VALUE UPDATE*, which is what its input actually is. Its name over-claims. Keep, rename its subject, keep the baseline line (still a floor carrier). |
| `:941` | `…demoRow_insert_then_absent_unsat_via_abstract` | **RESTATE**, same reason, same input. |
| `:944` | `…gates_force_holdsKindW_insert_row` | **STAYS VACUOUS on deployed rows** — `.insert` rows do not exist in any emitted descriptor (`"op":"insert"` = 0 across all seven registries), so its hypothesis is unsatisfiable *at deployment* for a second, independent reason. Not removable from the baseline (live floor carrier). The honest fix is DELETION of the arm, which is a deployed-side scope call, not this lane's. |
| `:965` | `MapOpWideKeyWeld.demoInsert_then_absent_unsat` | **RESTATE** (value-update subject, as `:940`). |
| `:966` | `…demoInsert_then_absent_unsat_via_abstract` | **RESTATE**, same. |
| `:972` | `…gates_force_holdsKindW_insert` | **STAYS VACUOUS**, as `:944`. |
| `:2066` | `MapOpWideKeyRowBoundary.gates_insertW_absentW_jointly_unsat_row` | **STAYS VACUOUS on `.insert`**; but note its `.aafiInsert` TWIN (`:2065`) is the live one, and §9 of this file adjudicates that separately. |
| `:2068` | `…gates_jointly_unsat_via_abstract_row'` | **STAYS VACUOUS**, as `:2066`. |
| `:2070` | `MapOpWideKeyWeld.gates_insertW_absentW_jointly_unsat` | **STAYS VACUOUS**, as `:2066`. |
| `:2072` | `…gates_jointly_unsat_via_abstract'` | **STAYS VACUOUS**, as `:2066`. |

Three group-A names §9 lists are **correctly ABSENT** from the baseline, and this is not an omission:
`MapOpWideKeyGate.insertW_absentW_jointly_unsat'`, `MapOpWideKey.insertW_sound` and
`.insertW_then_absentW_unsat` quantify over an abstract `Opens` with no floor binder, so they are not
floor carriers at all. They are still PREMISE-vacuous at deployment via their instantiations, and
nothing records that.

### The A′ set — the LIVE arm — is what this file repairs

`gates_force_holdsKindW_aafiInsert` (`MapOpWideKeyWeld:313`), its `_row` twin (`:340` of
`MapOpWideKeyRowBoundary`, baselined at `:942`), `gates_aafiInsertW_absentW_jointly_unsat` (`:348`),
`gates_jointly_unsat_via_abstract` (`:361`), `gates_aafiInsertW_absentW_jointly_unsat_row` (`:387`,
baselined `:2065`), `gates_jointly_unsat_via_abstract_row` (`:409`), `MapOpWideKeyGate`'s
`insertW_absentW_jointly_unsat` (`:921`) and `MapOpWideKey.aafiInsertW_sound` (`:419`): these are the
ones whose rows are EMITTED, and every one of them routes the `.aafiInsert` kind through
`ReconcileGatesAtW`'s write-shaped body, whose hypothesis is false on every honest deployed AAFI row.

**VERDICT: RESTATE, and the narrow replacement is landed here.** `MapOpImtAafiHoldsAt` /
`mapOpsArmImtAafi_of_modeler` / `aafiImtRow_forces_both_sides_of_good` are the deployed-shape
substitutes at the narrow key: same arm, same rows, true premise, floor-free, both sides forced.
⚠ NAMED RESIDUAL, not closed here: the WIDE-key (`Digest8Key`) versions of these do not exist. The
wide analogue of `padOpen_binds_or_resid` — an arity-3 padded opening extractor at 8-felt lanes with
named residuals instead of `Poseidon2SpongeCR` — is the missing piece, and it is the same piece the
whole wide file needs to leave the baseline. Naming it is not closing it. -/

/-! ## §11 — AXIOM HYGIENE. -/

#assert_axioms set_append_at_head
#assert_axioms set_replicate_perm
#assert_axioms padTo_set_at_length
#assert_axioms padTo_set_pad_perm
#assert_axioms padTo_perm_of_perm
#assert_axioms heap_set_cons_gt
#assert_axioms heap_set_cons_lt
#assert_axioms chain_relink_snoc_perm
#assert_axioms aafiLayoutResid_refuted
#assert_axioms aafiImtGates_force_layout_or_resid
#assert_axioms aafiImtRow_forces_layout_of_good
#assert_axioms aafiLayout_admits_no_erasure
#assert_axioms aafiLayout_low_cell_keeps_addr_and_value
#assert_axioms aafiLayout_free_slot_was_padding
#assert_axioms aafiLayout_post_root_moves
#assert_axioms aafiPostVec_perm_of_layout
#assert_axioms aafiImtRow_forces_insertsUpToLayout_of_good
#assert_axioms aafiImtRow_forces_both_sides_of_good
#assert_axioms reconcileGatesImtAafi_aafi
#assert_axioms reconcileGatesImtAafi_of_ne_aafi
#assert_axioms aafiRowImt_forces_denotation
#assert_axioms mapOpsArmImtAafi_of_modeler
#assert_axioms intHeap_ok
#assert_axioms intPhys_is_no_relinked_chain
#assert_axioms aafi_interior_post_admits_no_opening
#assert_axioms aafi_interior_row_at_depth2
#assert_axioms aafi_interior_row_post_admits_no_opening
#assert_axioms aafi_post_cannot_be_insertsFreshS
#assert_axioms aafi_interior_row_satisfies_the_layout_denotation
#assert_axioms bite_aafi_layout_fires
#assert_axioms bite_aafi_both_sides_fire
#assert_axioms bite_aafi_post_root_moves
#assert_axioms bite_aafi_key_is_absent_before
#assert_axioms bite_aafi_model_holds
#assert_axioms bite_aafi_denotation_holds
#assert_axioms wide_insert_never_grows_the_map
#assert_axioms wide_insert_unsat_at_fresh_key

end Dregg2.Circuit.MapAafiLiveRepoint
