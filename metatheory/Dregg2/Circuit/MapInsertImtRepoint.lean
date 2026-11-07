/-
# `Dregg2.Circuit.MapInsertImtRepoint` — the `.insert` arm REPOINTED onto the deployed shape, and
  the TWO limits repointing runs into on this arm (both proved, neither named-and-left).

`MapKindImtGates` (stage 2 proper) found the `.absent` disease on a SECOND host: the arity-2
`.insert` model demands an OLD-leaf path to the PRE-root, which BINDS the row's key into the
committed pre-heap (`reconcileGates_insert_forces_key_present`), while the deployed builder
`heap_root.rs::insert_witness` REFUSES an insert whose key is already present (`:1091-1093`,
`if self.position_of(key).is_some() { return None }`). So on every honest deployed insert row the
model's hypothesis is FALSE (`reconcileGates_insert_unsat_at_fresh_key`). This file does for
`.insert` what `MapAbsentImtGate` → `MapReconcileImtRepoint` did for `.absent`: model the shipped
arm 1:1, make it the PRIMARY dispatch, keep the arity-2 arm available, and state the limit plainly.

## THE DEPLOYED `.insert` (op = 3), read in `circuit/src/descriptor_ir2.rs` (`Ir2Air::MapOps`)

`not_insert = 1 − 6⁻¹·op·(op−1)` is `0` at op = 3 (`:3277-3278`), and `s` (the committed AAFI
selector) is pinned to `0` off op = 4 (`:3288`), so `rw_sel = not_insert + s = 0` and
`not_insert3 = not_insert + 2s = 0` (`:3298-3299`). Consequence, in the AIR's own comment: *"insert
opens the NEW leaf against the NEW root (no old leaf at a fresh key)"* (`:3385-3386`). **There is no
old-leaf absorb, no PATH1 fold to `MAP_ROOT`, and therefore no constraint on the pre-root at all.**
The enum says what is supposed to make up the difference: *"Freshness must be established
separately, e.g. by a paired `MapKind::Absent` opening against the same pre-root"* (`:540-542`).

## THE THREE RESULTS

### 1. THE REPOINT EXISTS, IS PRIMARY, AND THE TWO SHAPES ARE INCOMPARABLE (§3, §5)

`ReconcileGatesImtInsertAt` dispatches `.insert` to the deployed op = 3 body
(`MapKindImtGates.InsertImtRowAt` at the row's own columns) and leaves every other kind at
`ReconcileGatesAt`, verbatim — the same two-guarded-arms shape `MapReconcileImtRepoint` used for
`.absent`. `MapInsertReconcileModelOk` is the drop-in per-trace twin of `MapReconcileModelOk`, and
`mapOpsArmImtInsert_of_modeler` delivers the repointed per-row denotation for every declared map op.

⚑ INCOMPARABLE, both directions concrete, exactly as `.absent`'s turned out to be — and here by TWO
independent mechanisms on the deployed side:
  * on the honest deployed row (`MAP_TREE_DEPTH = 16`, sparse tree, FRESH key `5`) the OLD model is
    FALSE **(A) by the COMMITMENT** — its `∃ h, mapRoot hash 16 h = root` cannot hold at a padded
    arity-3 pre-root (`insert_old_model_false_deployed_commitment`) — and **(B) by the FRESH KEY**,
    in the counterfactual arity-2 world at the same depth, over the epoch's own `spineC` spine
    (`insert_old_model_false_fresh_key_at_depth`); the REPOINTED model HOLDS on that row;
  * on the epoch's own toy `.insert` row the OLD model holds and the repointed one is EMPTY, because
    that row's post-root column is a `mapRoot` and never a `padImtRoot`.
`insert_models_are_incomparable` bundles it. Neither refines the other; the deployed one is the one
that describes the shipped table.

⚑ THE ARITY WALL, FLOOR-FREE AND PADDED. `MapReconcileImtRepoint.imtRoot_ne_mapRoot` needed the
refuted `Poseidon2SpongeCR` and was stated at the UNPADDED commitment — its residual #1. Here
`padImtRoot_ne_mapRoot_of_good` proves the same separation at the DEPLOYED PADDED commitment from
`Function.Injective` + `PadFree2` alone, with the sparse (`≤`) occupancy on the IMT side. No floor.

### 2. ⚑⚑ `.insert` HAS NO SOUND STANDALONE DENOTATION — AND THE PAIRING DOES NOT RESCUE IT (§6)

`MapKindImtGates.insertImtGates_cannot_force_the_write_denotation` already refuted the standalone
opener. The obvious next move — and the one the DEPLOYMENT ITSELF names — is the pairing: an
`.absent` row against the same pre-root establishes freshness. So model the pairing and ask.

`InsertPairRowAt` is that composition as a FIRST-CLASS OBJECT: a deployed `Ir2Air::MapAbsent` row at
the padded commitment (§2, which also closes `MapReconcileImtRepoint`'s residual #1 on the gate law)
plus a deployed op = 3 row. What it FORCES is `insertsFreshS` — *the key was absent before and is
present at the written value after* (`insertPair_forces_insertsFresh_of_good`). What it does NOT
force is the write denotation, and that is REFUTED, not unproved:

> ⚑⚑ `insertPair_cannot_force_the_write_denotation` / `insertPair_erases_the_rest_of_the_map` — at
> `MAP_TREE_DEPTH = 16`, an accepting `.absent`+`.insert` PAIR over the pre-root of `[(1,7)]` sits
> beside a post-root committing `[(5,2)]`: key `5` is genuinely fresh, key `5` genuinely lands, and
> **key `1` has been ERASED**. `writesToMerkleS` is FALSE on that pair.

So the answer to "is `.insert` sound only in composition?" is **no — it is not sound in the named
composition either.** The pairing buys FRESHNESS; nothing in it buys PRESERVATION of the rest of the
map, because neither row constrains the pre-root and the post-root TOGETHER. `insertsFreshS` is
what the pair denotes, it is strictly weaker than `writesToMerkleS`
(`insertPair_is_strictly_weaker_than_the_write_denotation` exhibits one pair in both and one pair in
only the weak one), and it is the object a consumer of op = 3 rows may actually assume today.

### 3. ⚑⚑ THE TENTH IMPOSSIBILITY — no SINGLE-PATH row can denote an interior sorted insert (§7)

Nine obvious approaches on this epoch were proved impossible; this is the tenth, and it forecloses
the natural repair rather than leaving it to be tried. The natural repair for §6 is to add the
AAFI-style gate (d1) to op = 3: *"the slot was EMPTY under the pre-root"*, folding the padding
constant up the SAME sibling path. Any such gate set — indeed ANY gate set that reuses the one
deployed `MAP_SIB0`/`MAP_DIR0` path — changes **exactly one cell** of the committed digest vector
(`padOpen_binds_or_resid`'s update clause is literally `(padVec …).set (pathPos steps) …`). But
`heap_root.rs::insert_witness` splices the fresh leaf into its SORTED position and RE-COMPACTS, so
at an interior key the post-vector differs from the pre-vector in the inserted cell, in every
shifted cell, AND in the predecessor's POINTER.

> `interior_sorted_insert_moves_more_than_one_cell` — inserting `5` into `[(1,7),(9,3)]` moves
> positions `0` and `1` (and `2`); one `List.set` cannot do it, at any depth ≥ 2.
> `singlePath_postRoot_is_not_the_sorted_insert` lifts that to ROOTS: the post-root a one-path row
> can produce is NEVER the sorted-insert commitment there.

Hence op = 3 cannot be repaired into soundness on its own shape at all: **the two-path AAFI op is
not an optimisation of `.insert`, it is the only shape in which a fresh-key insert is expressible.**
That is a deployed-side conclusion, and it is the same verdict `heap_root.rs` reached in prose
(*"no shared pre-image binds the shifted suffix"*, `descriptor_ir2.rs:545-547`) — now a theorem.

## ⚠ THE EPOCH'S OWN `.insert` EXHIBIT WAS A VALUE UPDATE, AND IS RENAMED

`MapOpsColumnLayout.toy_insert_gates` wrote key `20` into `toyHeap`, which HOLDS key `20` — a value
update wearing an insert's name, and the only `.insert` non-vacuity the epoch had. It is now
`toy_insert_op_value_update_gates` / `_fires`, with `toy_insert_op_key_is_already_committed` as a
THEOREM rather than a `#guard`. A fresh-key witness for it does not exist and cannot be written:
that is `reconcileGates_insert_unsat_at_fresh_key`. The REAL insert exhibit is §4's, at the deployed
depth on the deployed shape, and it is the first fresh-key `.insert` witness this epoch has had.

## BLAST RADIUS — what rested on the arity-2 `.insert` model (§8 lists it in full)

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free; no `native_decide`; no
`decide` on any object containing the depth-16 spine — every depth-16 exhibit NAMES its root and
builds its path by the symbolic `leftPadPath` / `slot1Path` / `spineC` recursions of the modules it
reuses. **NO FLOOR CARRIER**: `Poseidon2SpongeCR` and `Compress8CR` appear in no type and no `def`
body here; every law is `MapKindImtGates`'s `_or_resid` / `_of_good` pair at
`MapGood = Function.Injective ∧ PadFree3`, which is `padImtTeeth`'s own `Good` field. NEW file;
every import read-only; no deployed descriptor / emit / JSON / Rust byte touched.
-/
import Dregg2.Circuit.MapKindImtGates

namespace Dregg2.Circuit.MapInsertImtRepoint

open Dregg2.Substrate
open Dregg2.Circuit (Assignment)
-- ⚠ SELECTIVE, not wholesale: `DescriptorIR2` also declares a `padTo`, and opening both namespaces
-- makes every `padTo` in this file ambiguous.
open Dregg2.Circuit.DescriptorIR2 (MapOp MapOpKind MAP_TREE_DEPTH EffectVmDescriptor2 VmTrace
  VmConstraint2 mapOpsOf envAt)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.MapMerkleRoot (mapNode perfectRoot mapRoot perfectRoot_binds_or_collides
  mapRootFind mapRoot_binds_or_collides)
open Dregg2.Circuit.MapDenotationSchema (MapLeafSchema imtChainOf opensToMerkleS writesToMerkleS
  imtSchema_chain_imtSorted)
open Dregg2.Circuit.MapPaddedDenotation (padDigest padTo padTo_length
  padImtRoot PadFree2 PadFree3 padImtSchema padImtTeeth imtChainOf_length imtToHeap_imtChainOf
  oddSponge oddSponge_injective oddSponge_padFree2 oddSponge_padFree3
  opensToMerkleS_functional_of_good opensToMerkleS_some_excludes_none_of_good)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted imtAddrs imtLeafHash imtToHeap
  imtAbsent_excludes keys_imtToHeap)
open Dregg2.Circuit.MapOpsColumnLayout (pathPos pathRecompute ReconcileGatesAt MapReconcileModelOk
  mem_mapOpsOf toyInsertOp toyInsertEnv toyHeap toyGrown toy_insert_op_value_update_gates
  pathRecompute_binds_updates noPathColl_of_CR noLeafColl_of_CR leafOf_injective)
open Dregg2.Circuit.Poseidon2Binding (spongeColl_refutable_of_injective)
open Dregg2.Circuit.MapReconcileImtRepoint (depSpine depKey depSpine_addr_lt depHeap_length)
open Dregg2.Circuit.MapKindImtGates
-- `fits_of_pow_le` — capacity from a CHEAPER exponent; the only way §7's symbolic-depth exhibit can
-- carry `padVec`/`padImtRoot`'s occupancy obligation without ever evaluating `2 ^ dep`.
open Dregg2.Circuit.DeployedMapDenotation (fits_of_pow_le)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — THE ARITY WALL AT THE DEPLOYED PADDED COMMITMENT, FLOOR-FREE.

`MapReconcileImtRepoint.imtRoot_ne_mapRoot` separates the arity-3 IMT root from the arity-2 `mapRoot`
under the REFUTED `Poseidon2SpongeCR` floor and at the UNPADDED commitment (its named residual #1:
*"every statement here is at the unpadded commitment form"*). Both limitations go here: the
separation holds at `padImtRoot` — the deployed sparse, zero-padded, arity-3 fold — from
`Function.Injective` + `PadFree2` alone. Those are two fields of `padImtTeeth`'s idealisation, not a
new hash property, and `oddSponge` inhabits both. -/

/-- Reading a LIVE cell of a padded vector is reading the prefix — the one-liner the position-0
comparison below and §7's shift argument both run on. -/
theorem padTo_getElem?_lt (d : Nat) (L : List ℤ) (hFits : L.length ≤ 2 ^ d) (i : Nat)
    (hi : i < L.length) : (padTo d L hFits)[i]? = L[i]? := by
  rw [padTo, List.getElem?_append_left hi]

/-- **★ THE DEPLOYED PADDED ARITY-3 COMMITMENT IS NEVER AN ARITY-2 `mapRoot`** — at any depth, for
any admissible sparse IMT heap and any DENSE arity-2 heap, with NO floor. Position `0` of a dense
arity-2 vector is a live `Heap.leafOf` digest; position `0` of the padded arity-3 vector is either a
live `imtLeafHash` digest (whose preimage has length 3, not 2) or the padding constant (excluded by
`PadFree2` on the other side). -/
theorem padImtRoot_ne_mapRoot_of_good {hash : List ℤ → ℤ}
    (hinj : Function.Injective hash) (hpf : PadFree2 hash)
    (sent : ℤ) (dep : Nat) {h₁ h₂ : Heap.FeltHeap}
    (hz₁ : h₁.length ≤ 2 ^ dep) (hz₂ : h₂.length = 2 ^ dep) :
    padImtRoot sent hash dep h₁ ≠ mapRoot hash dep h₂ := by
  intro he
  have hv₁ : (padTo dep ((imtChainOf sent h₁).map (imtLeafHash hash))).length = 2 ^ dep :=
    padTo_length (by rw [List.length_map, imtChainOf_length]; exact hz₁)
  have hv₂ : (h₂.map (Heap.leafOf hash)).length = 2 ^ dep := by rw [List.length_map]; exact hz₂
  rcases perfectRoot_binds_or_collides hash dep hv₁ hv₂ he with hveq | hcol
  · -- The two committed vectors coincide; compare position 0, which is LIVE on the arity-2 side.
    have hpos : 0 < h₂.length := by rw [hz₂]; exact Nat.two_pow_pos dep
    obtain ⟨e, rest, hh⟩ : ∃ e rest, h₂ = e :: rest := by
      cases h₂ with
      | nil => simp at hpos
      | cons a b => exact ⟨a, b, rfl⟩
    have h0 : (padTo dep ((imtChainOf sent h₁).map (imtLeafHash hash)))[0]?
        = some (Heap.leafOf hash e) := by
      rw [hveq, hh]; rfl
    rcases padTo_getElem? dep ((imtChainOf sent h₁).map (imtLeafHash hash)) 0
      (Heap.leafOf hash e) h0 with ⟨hlt, hcell⟩ | hpad
    · rw [List.getElem?_map] at hcell
      cases hc : (imtChainOf sent h₁)[0]? with
      | none => rw [hc] at hcell; simp at hcell
      | some l =>
        rw [hc] at hcell
        simp only [Option.map_some, Option.some.injEq, imtLeafHash, Heap.leafOf] at hcell
        have hlists : ([l.addr, l.value, l.nextAddr] : List ℤ) = [e.1, e.2] := hinj hcell
        have := congrArg List.length hlists
        simp at this
    · exact hpf e hpad
  · exact spongeColl_refutable_of_injective hash hinj _ hcol

/-! ## §2 — THE DEPLOYED `.absent` GATE AT THE **PADDED** COMMITMENT.

`MapAbsentImtGate.AbsentImtGatesAt` models the deployed `Ir2Air::MapAbsent` table (one arity-3
low-leaf opening whose digest BINDS the pointer, the bracket `lo_addr < key < low_next`, and
`MA_NEW_ROOT = MA_ROOT`) — but at the UNPADDED commitment, and under `Poseidon2SpongeCR`. §6 needs
the `.absent` row and the `.insert` row to speak about the SAME committed object, which is the
deployed sparse padded tree, so the arm is restated here at `padImtSchema` in `MapKindImtGates`'s
floor-free idiom. That closes `MapReconcileImtRepoint`'s residual #1 for the gate law: the deployed
`.absent` soundness now holds at the commitment `CanonicalHeapTree8::new` actually builds.

⚠ What is NOT closed by that: the residual also covered the WALL theorems and the apex wiring, which
are untouched here. -/

/-- **`AbsentImtGatesOn`** — the deployed `Ir2Air::MapAbsent` acceptance for ONE row, at the padded
arity-3 commitment. The path is `MA_LO_SIB0`/`MA_LO_DIR0`, the leaf is `HeapLeaf::digest8`, the
bracket is `MA_CMP_LO0`/`MA_CMP_HI0` over the canonical lifts, and `newRoot = oldRoot` is the lane
equality the absent table (unlike `MapOps`) really does write. -/
def AbsentImtGatesOn (hash : List ℤ → ℤ) (dep : Nat) (steps : List (Bool × ℤ))
    (oldRoot newRoot key lowAddr lowValue lowNext : ℤ) : Prop :=
  steps.length = dep ∧
  pathRecompute hash (imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩) steps = oldRoot ∧
  lowAddr < key ∧ key < lowNext ∧
  newRoot = oldRoot

/-- The `.absent` row: the gates plus the committed sparse heap behind the pre-root, in the same
knowledge-extraction slot `ReconcileGatesAt`'s `∃ h` occupies. -/
def AbsentImtRowAt (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (oldRoot newRoot key lowAddr lowValue lowNext : ℤ) : Prop :=
  ∃ (h : Heap.FeltHeap) (steps : List (Bool × ℤ)),
    (padImtSchema sent).HeapOk h ∧ ∃ hsz : (padImtSchema sent).SizeOk dep h,
    padImtRoot sent hash dep h hsz = oldRoot ∧
    AbsentImtGatesOn hash dep steps oldRoot newRoot key lowAddr lowValue lowNext

/-- **★ THE `.absent` LAW AT THE DEPLOYED PADDED COMMITMENT, floor-free.** An accepting deployed
absent row FORCES the key off the committed map and the post-root column to equal the pre-root.
⚠ `ImtSorted` on the pre-chain is DERIVED from the schema's own `HeapOk` (`imtSchema_chain_imtSorted`)
rather than assumed — the same saving `MapKindImtGates`'s `.aafiInsert` arm makes and
`MapAbsentImtGate`'s unpadded law does not. -/
theorem absentImtGates_force_absence_or_resid (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    {oldRoot newRoot key lowAddr lowValue lowNext : ℤ}
    {h : Heap.FeltHeap} {steps : List (Bool × ℤ)}
    (hok : (padImtSchema sent).HeapOk h) (hsz : (padImtSchema sent).SizeOk dep h)
    (hcommit : padImtRoot sent hash dep h hsz = oldRoot)
    (hg : AbsentImtGatesOn hash dep steps oldRoot newRoot key lowAddr lowValue lowNext) :
    (Heap.get h key = none
      ∧ opensToMerkleS (padImtSchema sent) hash dep oldRoot key none
      ∧ newRoot = oldRoot)
    ∨ OpenResid sent hash dep h hsz steps ⟨lowAddr, lowValue, lowNext⟩ := by
  obtain ⟨hsl, hpa, hlk, hkn, hnr⟩ := hg
  rcases padOpen_binds_or_resid sent hash dep hsz hsl (by rw [hpa, ← hcommit]) with
    ⟨_, hchain, _, _, _⟩ | hres
  · have hmem : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf) ∈ imtChainOf sent h :=
      List.mem_of_getElem? hchain
    have hs : ImtSorted (imtChainOf sent h) := imtSchema_chain_imtSorted sent h hok
    have hnotin : key ∉ imtAddrs (imtChainOf sent h) :=
      imtAbsent_excludes hs ⟨⟨lowAddr, lowValue, lowNext⟩, hmem, hlk, hkn⟩
    have hkeys : Heap.keys h = imtAddrs (imtChainOf sent h) := by
      rw [← keys_imtToHeap (imtChainOf sent h), imtToHeap_imtChainOf sent h]
    have hnone : Heap.get h key = none := by
      rw [Heap.get_eq_none_iff, hkeys]; exact hnotin
    exact Or.inl ⟨hnone, ⟨h, hok, hsz, hcommit, hnone⟩, hnr⟩
  · exact Or.inr hres

/-- **★ `.absent` at a good hash: the deployed padded gates ⇒ the absence denotation.** -/
theorem absentImtRow_forces_absence_of_good {hash : List ℤ → ℤ} (hgood : MapGood hash)
    (sent : ℤ) (dep : Nat) {oldRoot newRoot key lowAddr lowValue lowNext : ℤ}
    (hr : AbsentImtRowAt sent hash dep oldRoot newRoot key lowAddr lowValue lowNext) :
    opensToMerkleS (padImtSchema sent) hash dep oldRoot key none ∧ newRoot = oldRoot := by
  obtain ⟨h, steps, hok, hsz, hcommit, hg⟩ := hr
  rcases absentImtGates_force_absence_or_resid sent hash dep hok hsz hcommit hg with hres | hbad
  · exact ⟨hres.2.1, hres.2.2⟩
  · exact absurd hbad (openResid_refuted hgood sent dep h hsz steps _)

/-! ## §3 — THE REPOINTED `.insert` DISPATCH.

The `.insert` arm is judged by the shape that ships. The committed POST-heap rides in the SAME
knowledge-extraction slot `ReconcileGatesAt`'s `∃ h, Heap.SortedKeys h` occupies — same species, no
new floor. Every other kind is left EXACTLY as it was, so this composes additively with
`MapReconcileImtRepoint`'s `.absent` repoint and the arity-2 arm stays available for the future model
in which the AIR really does fold a chain to the pre-root. -/

/-- **`InsertRowImtAt`** — the deployed op = 3 acceptance AT THE ROW'S COLUMNS. `MAP_NEXT` is a real
deployed column but `MapOp` has no field for it, so it rides existentially, exactly as
`ReconcileGatesAt`'s `vOld` does. ⚑ Note the absent parameter: the row's PRE-root column
(`m.root 0`) does not appear, because the AIR does not constrain it. -/
def InsertRowImtAt (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat) (a : Assignment) (m : MapOp) : Prop :=
  ∃ next : ℤ,
    InsertImtRowAt sent hash dep ((m.newRoot 0).eval a) (m.key.eval a) (m.value.eval a) next

/-- **`ReconcileGatesImtInsertAt`** — `ReconcileGatesAt` with the `.insert` dispatch REPOINTED,
written as two guarded arms so the dispatch is visible in the statement. -/
def ReconcileGatesImtInsertAt (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (a : Assignment) (m : MapOp) : Prop :=
  (m.op = MapOpKind.insert → InsertRowImtAt sent hash dep a m) ∧
  (m.op ≠ MapOpKind.insert → ReconcileGatesAt hash dep a m)

theorem reconcileGatesImtInsert_insert (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (a : Assignment) (m : MapOp) (hop : m.op = MapOpKind.insert) :
    ReconcileGatesImtInsertAt sent hash dep a m ↔ InsertRowImtAt sent hash dep a m :=
  ⟨fun h => h.1 hop, fun h => ⟨fun _ => h, fun hne => absurd hop hne⟩⟩

theorem reconcileGatesImtInsert_of_ne_insert (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (a : Assignment) (m : MapOp) (hop : m.op ≠ MapOpKind.insert) :
    ReconcileGatesImtInsertAt sent hash dep a m ↔ ReconcileGatesAt hash dep a m :=
  ⟨fun h => h.2 hop, fun h => ⟨fun hins => absurd hins hop, fun _ => h⟩⟩

/-- **The per-trace REPOINTED model** — the drop-in twin of `MapOpsColumnLayout.MapReconcileModelOk`
at the same deployed depth. -/
def MapInsertReconcileModelOk (sent : ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (t : VmTrace) : Prop :=
  ∀ i < t.rows.length, ∀ m ∈ mapOpsOf d,
    m.guard.eval (envAt t i).loc = 1 →
      ReconcileGatesImtInsertAt sent hash MAP_TREE_DEPTH (envAt t i).loc m

/-- **`MapOpImtInsertHoldsAt`** — the repointed `.insert` DENOTATION: on a fired insert row the
committed POST-tree opens the row's key to the row's value. ⚑ This is ALL of it. There is
deliberately no pre-root conjunct: §6 proves none is available, with or without the paired
`.absent` row. -/
def MapOpImtInsertHoldsAt (sent : ℤ) (hash : List ℤ → ℤ) (env : VmRowEnv) (m : MapOp) : Prop :=
  m.op = MapOpKind.insert → m.guard.eval env.loc = 1 →
    opensToMerkleS (padImtSchema sent) hash MAP_TREE_DEPTH ((m.newRoot 0).eval env.loc)
      (m.key.eval env.loc) (some (m.value.eval env.loc))

/-- **★ THE REPOINTED PER-ROW LAW.** An accepting DEPLOYED insert row forces the post-root column to
be a genuine padded commitment opening the key to the value. -/
theorem insertRowImt_forces_post_opening {hash : List ℤ → ℤ} (hgood : MapGood hash)
    (sent : ℤ) (dep : Nat) (a : Assignment) (m : MapOp)
    (hg : InsertRowImtAt sent hash dep a m) :
    opensToMerkleS (padImtSchema sent) hash dep ((m.newRoot 0).eval a) (m.key.eval a)
      (some (m.value.eval a)) := by
  obtain ⟨next, hr⟩ := hg
  exact insertImtRow_post_opens_of_good hgood sent dep hr

/-- **★ THE REPOINTED `.mapOp` ARM (∀ d), for the `.insert` leg.** The repointed model plus the
`MapGood` bridge force the repointed per-row denotation for every declared map op. The twin of
`MapReconcileImtRepoint.mapOpsArmImt_of_modeler` on the second repointed arm — and, unlike it, it
carries NO floor in its type. -/
theorem mapOpsArmImtInsert_of_modeler {hash : List ℤ → ℤ} (hgood : MapGood hash) (sent : ℤ)
    (d : EffectVmDescriptor2) (t : VmTrace) (hok : MapInsertReconcileModelOk sent hash d t) :
    ∀ i < t.rows.length, ∀ m : MapOp, VmConstraint2.mapOp m ∈ d.constraints →
      MapOpImtInsertHoldsAt sent hash (envAt t i) m := by
  intro i hi m hm hop hguard
  have hmem : m ∈ mapOpsOf d := mem_mapOpsOf.mpr hm
  exact insertRowImt_forces_post_opening hgood sent MAP_TREE_DEPTH (envAt t i).loc m
    ((hok i hi m hmem hguard).1 hop)

/-! ## §4 — THE ROW VEHICLE AND THE FIRST FRESH-KEY `.insert` EXHIBIT, AT `MAP_TREE_DEPTH = 16`.

The epoch has never had one. `MapOpsColumnLayout.toy_insert_op_value_update_gates` (renamed this
session) writes key `20` into a heap that HOLDS key `20`; at the arity-2 model no fresh-key witness
exists at all (`reconcileGates_insert_unsat_at_fresh_key`). Here is the real thing, on the deployed
shape at the deployed depth over the SPARSE occupancy `CanonicalHeapTree8::new` builds: one live
leaf `(1,7)` in a `2^16`-leaf commitment, key `5` FRESH, appended at the first padding slot.

Everything is reused rather than rebuilt: `MapKindImtGates`'s `biteHeap` / `biteSteps`
(`leftPadPath`) / `aafiSteps2` (`slot1Path`) / `aafiNewRoot`. No `2^16` object is ever constructed;
every root is NAMED as the schema's own `commit`. -/

section Exhibit

/-- The insert-row vehicle: pre-root, key, value, post-root on wires 0/1/2/3 — the epoch's
`toyInsertOp` wiring, with the post-root column INDEPENDENT of the pre-root column (which is exactly
the freedom op = 3 leaves in the table). -/
def insRow (r k v r' : ℤ) : Assignment := fun c =>
  if c = 0 then r else if c = 1 then k else if c = 2 then v else if c = 3 then r' else 0

theorem insRow_root (r k v r' : ℤ) : (toyInsertOp.root 0).eval (insRow r k v r') = r := rfl
theorem insRow_key (r k v r' : ℤ) : toyInsertOp.key.eval (insRow r k v r') = k := rfl
theorem insRow_value (r k v r' : ℤ) : toyInsertOp.value.eval (insRow r k v r') = v := rfl
theorem insRow_newRoot (r k v r' : ℤ) : (toyInsertOp.newRoot 0).eval (insRow r k v r') = r' := rfl
theorem insRow_guard (r k v r' : ℤ) : toyInsertOp.guard.eval (insRow r k v r') = 1 := rfl
theorem toyInsertOp_op : toyInsertOp.op = MapOpKind.insert := rfl

/-- The post-heap of the honest fresh insert: `[(1,7)]` with `(5,2)` spliced in. -/
theorem bite_set52 : Heap.set biteHeap 5 2 = [(1, 7), (5, 2)] := by
  norm_num [biteHeap, Heap.set]

theorem biteGrown_ok : (padImtSchema biteSent).HeapOk [(1, 7), (5, 2)] := by
  refine ⟨by simp [Heap.SortedKeys, Heap.keys], ?_⟩
  intro x hx
  simp only [Heap.keys, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl <;> norm_num [biteSent]

theorem biteGrown_sz : (padImtSchema biteSent).SizeOk MAP_TREE_DEPTH [(1, 7), (5, 2)] := by
  show ([(1, 7), (5, 2)] : Heap.FeltHeap).length ≤ 2 ^ MAP_TREE_DEPTH
  show 2 ≤ 2 ^ MAP_TREE_DEPTH
  exact two_le_two_pow_depth

/-- **★★ THE FIRST FRESH-KEY `.insert` WITNESS ON THE DEPLOYED SHAPE, AT `MAP_TREE_DEPTH = 16`.**
Key `5` is genuinely absent from the pre-map `[(1,7)]`; the new leaf `⟨5, 2, 100⟩` opens at the
first padding position against the post-root, which IS the padded commitment of the grown map. This
is the row `heap_root.rs::insert_witness` emits, and the arity-2 model has no witness for it. -/
theorem bite_fresh_insert_row :
    InsertImtRowAt biteSent oddSponge MAP_TREE_DEPTH aafiNewRoot 5 2 biteSent :=
  ⟨[(1, 7), (5, 2)], aafiSteps2, biteGrown_ok, biteGrown_sz, rfl,
    aafi_steps2_length, by rw [aafi_steps2_recompute, aafiNewRoot_eq]⟩

/-- The key really is FRESH — the property the epoch's exhibit lacked, stated rather than assumed. -/
theorem bite_fresh_insert_key_is_fresh :
    (5 : ℤ) ∉ Heap.keys biteHeap ∧ (Heap.set biteHeap 5 2).length = biteHeap.length + 1 := by
  have hfresh : (5 : ℤ) ∉ Heap.keys biteHeap := by decide
  exact ⟨hfresh, Heap.length_set_fresh biteHeap 5 2 hfresh⟩

/-- **★ THE REPOINTED LAW FIRES on the fresh-key row.** -/
theorem bite_fresh_insert_post_opens :
    opensToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH aafiNewRoot 5 (some 2) :=
  insertImtRow_post_opens_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH bite_fresh_insert_row

/-- **★★ THE TOOTH — a FORGED post value is REFUSED.** No accepting deployed insert row, for ANY
claimed pointer, can claim that this post-root holds `5 ↦ 9`. -/
theorem bite_fresh_insert_forged_value_refused (next : ℤ) :
    ¬ InsertImtRowAt biteSent oddSponge MAP_TREE_DEPTH aafiNewRoot 5 9 next := by
  intro hr
  have h9 := insertImtRow_post_opens_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH hr
  have hEq := opensToMerkleS_functional_of_good (padImtTeeth biteSent)
    ⟨oddSponge_injective, oddSponge_padFree3⟩ MAP_TREE_DEPTH h9 bite_fresh_insert_post_opens
  simp at hEq

/-! ### §4b — the same row at MODEL level: one descriptor, one trace, one fired `.insert` row. -/

/-- The one-row descriptor carrying a single fired `.insert` map op. -/
def dInsert : EffectVmDescriptor2 :=
  { name := "map-insert-fresh-key"
  , traceWidth := 4
  , piCount := 0
  , tables := []
  , constraints := [VmConstraint2.mapOp toyInsertOp]
  , hashSites := []
  , ranges := [] }

theorem dInsert_mapOps : mapOpsOf dInsert = [toyInsertOp] := rfl

theorem mem_dInsert {m : MapOp} (h : m ∈ mapOpsOf dInsert) : m = toyInsertOp := by
  rw [dInsert_mapOps] at h
  simpa using h

def traceIns (r k v r' : ℤ) : VmTrace :=
  { rows := [insRow r k v r'], pub := fun _ => 0, tf := fun _ => [] }

theorem traceIns_rows_length (r k v r' : ℤ) : (traceIns r k v r').rows.length = 1 := rfl
theorem traceIns_loc (r k v r' : ℤ) : (envAt (traceIns r k v r') 0).loc = insRow r k v r' := rfl

/-- **★ THE REPOINTED PREMISE HOLDS on the fresh-key deployed row, at the DEPLOYED depth.** -/
theorem bite_fresh_insert_model_holds :
    MapInsertReconcileModelOk biteSent oddSponge dInsert (traceIns biteRoot 5 2 aafiNewRoot) := by
  intro i hi m hm hguard
  have hi0 : i = 0 := by rw [traceIns_rows_length] at hi; omega
  subst hi0
  rw [mem_dInsert hm, traceIns_loc]
  refine ⟨fun _ => ⟨biteSent, ?_⟩, fun hne => absurd rfl hne⟩
  rw [insRow_newRoot, insRow_key, insRow_value]
  exact bite_fresh_insert_row

/-- **★ AND THE REPOINTED DENOTATION IS DELIVERED ON THAT ROW**, through the repointed arm rather
than by hand. -/
theorem bite_fresh_insert_denotation_holds :
    MapOpImtInsertHoldsAt biteSent oddSponge
      (envAt (traceIns biteRoot 5 2 aafiNewRoot) 0) toyInsertOp :=
  mapOpsArmImtInsert_of_modeler mapGood_inhabited biteSent dInsert
    (traceIns biteRoot 5 2 aafiNewRoot) bite_fresh_insert_model_holds 0
    (by rw [traceIns_rows_length]; omega) toyInsertOp (List.mem_singleton_self _)

end Exhibit

/-! ## §5 — ⚑ THE TWO MODELS ARE INCOMPARABLE, both directions concrete.

Exactly the verdict the `.absent` repoint reached, on the second arm — and the deployed side is
refuted by TWO independent mechanisms, as it was there. -/

section Incomparable

/-- **★ MECHANISM A — THE COMMITMENT.** On the honest deployed row the OLD model has no witness at
all: its extraction premise demands `mapRoot hash 16 h = MAP_ROOT` and the deployed pre-root column
is the padded arity-3 commitment, which §1 proves is never an arity-2 `mapRoot`. Note what this does
NOT need: no assumption about the key, the map's contents, or even the op kind. -/
theorem insert_old_model_false_deployed_commitment (k v r' : ℤ) :
    ¬ ReconcileGatesAt oddSponge MAP_TREE_DEPTH (insRow biteRoot k v r') toyInsertOp := by
  rintro ⟨h, -, hlen, hroot, -⟩
  refine padImtRoot_ne_mapRoot_of_good oddSponge_injective oddSponge_padFree2 biteSent
    MAP_TREE_DEPTH (h₁ := biteHeap) (h₂ := h) biteHeap_sz hlen ?_
  exact (hroot.trans (insRow_root biteRoot k v r')).symm

/-- **★ MECHANISM B — THE FRESH KEY**, in the COUNTERFACTUAL arity-2 world, at the DEPLOYED depth.
Even where the arity-2 commitment is the one in play, the model's `.insert` arm demands an old-leaf
path to the pre-root, hence the key ALREADY COMMITTED — and the deployed builder refuses exactly
those rows. Stated over the epoch's own `spineC` spine at `MAP_TREE_DEPTH`, whose terminal gap holds
every fresh key: nothing is enumerated. -/
theorem insert_old_model_false_fresh_key_at_depth (v r' : ℤ) :
    ¬ ReconcileGatesAt oddSponge MAP_TREE_DEPTH
        (insRow (mapRoot oddSponge MAP_TREE_DEPTH (imtToHeap depSpine)) depKey v r') toyInsertOp := by
  refine reconcileGates_insert_unsat_at_fresh_key oddSponge oddSponge_injective MAP_TREE_DEPTH
    _ toyInsertOp toyInsertOp_op (imtToHeap depSpine) depHeap_length ?_ ?_
  · rw [insRow_root]
  · rw [insRow_key, keys_imtToHeap]
    intro hx
    exact absurd (depSpine_addr_lt depKey hx) (lt_irrefl depKey)

/-- **★ THE REPOINTED MODEL HOLDS on that same deployed row.** -/
theorem insert_repointed_model_holds_deployed :
    ReconcileGatesImtInsertAt biteSent oddSponge MAP_TREE_DEPTH
      (insRow biteRoot 5 2 aafiNewRoot) toyInsertOp := by
  refine ⟨fun _ => ⟨biteSent, ?_⟩, fun hne => absurd rfl hne⟩
  rw [insRow_newRoot, insRow_key, insRow_value]
  exact bite_fresh_insert_row

/-- **★ THE OTHER DIRECTION — the epoch's own toy `.insert` row has NO repointed body.** That row's
post-root column is `mapRoot oddSponge 2 toyGrown`, an arity-2 commitment; the repointed body
demands a padded arity-3 one. So the arity-2 arm is not a special case of the deployed arm either. -/
theorem toy_insert_row_has_no_repointed_body (sent : ℤ) :
    ¬ ReconcileGatesImtInsertAt sent oddSponge 2 (toyInsertEnv oddSponge) toyInsertOp := by
  intro hg
  obtain ⟨next, h', steps, -, hsz, hcommit, -⟩ := hg.1 rfl
  refine padImtRoot_ne_mapRoot_of_good oddSponge_injective oddSponge_padFree2 sent 2
    (h₁ := h') (h₂ := toyGrown) hsz rfl ?_
  exact hcommit

/-- **★★ THE TWO `.insert` MODELS ARE INCOMPARABLE.** On the deployed fresh-key row at
`MAP_TREE_DEPTH = 16` the old model is EMPTY (two mechanisms) and the repointed one HOLDS; on the
epoch's own toy row the old model HOLDS and the repointed one is EMPTY. Neither refines the other;
the deployed one is the one that describes the shipped table. -/
theorem insert_models_are_incomparable :
    (¬ ReconcileGatesAt oddSponge MAP_TREE_DEPTH (insRow biteRoot 5 2 aafiNewRoot) toyInsertOp
      ∧ ¬ ReconcileGatesAt oddSponge MAP_TREE_DEPTH
          (insRow (mapRoot oddSponge MAP_TREE_DEPTH (imtToHeap depSpine)) depKey 2 aafiNewRoot)
          toyInsertOp
      ∧ ReconcileGatesImtInsertAt biteSent oddSponge MAP_TREE_DEPTH
          (insRow biteRoot 5 2 aafiNewRoot) toyInsertOp)
    ∧ (ReconcileGatesAt oddSponge 2 (toyInsertEnv oddSponge) toyInsertOp
      ∧ ¬ ReconcileGatesImtInsertAt biteSent oddSponge 2 (toyInsertEnv oddSponge) toyInsertOp) :=
  ⟨⟨insert_old_model_false_deployed_commitment 5 2 aafiNewRoot,
    insert_old_model_false_fresh_key_at_depth 2 aafiNewRoot,
    insert_repointed_model_holds_deployed⟩,
   toy_insert_op_value_update_gates oddSponge, toy_insert_row_has_no_repointed_body biteSent⟩

end Incomparable

/-! ## §6 — ⚑⚑ THE HONEST LIMIT: THE PAIRING IS A FIRST-CLASS OBJECT, AND IT IS **NOT ENOUGH**.

`descriptor_ir2.rs:540-542` names the deployed fix in prose: *"Freshness must be established
separately, e.g. by a paired `MapKind::Absent` opening against the same pre-root."* Model that
composition and ask what it forces. It forces FRESHNESS-THEN-PRESENCE. It does NOT force the write
denotation — and that is a REFUTATION at the deployed depth, not a gap.

The reason is structural and survives any amount of Lean: the `.absent` row constrains the PRE-root
only, the op = 3 row constrains the POST-root only, and NOTHING relates them. A prover may therefore
answer an honest freshness check about one map and then commit an entirely different map. -/

/-- **`insertsFreshS`** — what the deployed `.absent` + `.insert` PAIR actually denotes: the key was
ABSENT under the pre-root and is PRESENT at the written value under the post-root. This is the
composition object, named. It is strictly weaker than `writesToMerkleS`, which additionally says the
post-map is the pre-map with exactly that one entry changed. -/
def insertsFreshS (S : MapLeafSchema) (hash : List ℤ → ℤ) (dep : Nat) (r k v r' : ℤ) : Prop :=
  opensToMerkleS S hash dep r k none ∧ opensToMerkleS S hash dep r' k (some v)

/-- **`InsertPairRowAt`** — the pairing the deployment names, as ONE object: a deployed
`Ir2Air::MapAbsent` row against the pre-root (root-preserving, per that table's lane equality) and a
deployed op = 3 row against the post-root, at the SAME padded commitment. ⚠ NOTE WHAT IS MISSING AND
IS ALSO MISSING FROM THE DEPLOYMENT: nothing here — and nothing in the AIR — checks that the two rows
are on the same turn, in the same order, or present at all. -/
def InsertPairRowAt (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (oldRoot newRoot key value : ℤ) : Prop :=
  (∃ lowAddr lowValue lowNext : ℤ,
      AbsentImtRowAt sent hash dep oldRoot oldRoot key lowAddr lowValue lowNext)
  ∧ (∃ next : ℤ, InsertImtRowAt sent hash dep newRoot key value next)

/-- **★ WHAT THE PAIRING DOES FORCE.** The composition denotation, derived from the two deployed
gate sets — freshness from the absent row, landing from the insert row. -/
theorem insertPair_forces_insertsFresh_of_good {hash : List ℤ → ℤ} (hgood : MapGood hash)
    (sent : ℤ) (dep : Nat) {oldRoot newRoot key value : ℤ}
    (hp : InsertPairRowAt sent hash dep oldRoot newRoot key value) :
    insertsFreshS (padImtSchema sent) hash dep oldRoot key value newRoot := by
  obtain ⟨⟨lowAddr, lowValue, lowNext, hab⟩, next, hins⟩ := hp
  exact ⟨(absentImtRow_forces_absence_of_good hgood sent dep hab).1,
    insertImtRow_post_opens_of_good hgood sent dep hins⟩

section Erasure

/-- The post-root of the ERASING pair: the padded commitment of a map holding ONLY `(5,2)`. -/
noncomputable def eraseRoot : ℤ := padImtRoot biteSent oddSponge MAP_TREE_DEPTH [(5, 2)]

theorem erase_ok : (padImtSchema biteSent).HeapOk [(5, 2)] :=
  heapOk_singleton (by norm_num [biteSent])

theorem erase_sz : (padImtSchema biteSent).SizeOk MAP_TREE_DEPTH [(5, 2)] := by
  show ([(5, 2)] : Heap.FeltHeap).length ≤ 2 ^ MAP_TREE_DEPTH
  show 1 ≤ 2 ^ MAP_TREE_DEPTH
  exact Nat.one_le_pow _ 2 (by norm_num)

/-- The ABSENT half: key `5` sits in the terminal pointer gap `1 → 100` of the one-leaf pre-tree. -/
theorem erase_absent_row :
    AbsentImtRowAt biteSent oddSponge MAP_TREE_DEPTH biteRoot biteRoot 5 1 7 biteSent :=
  ⟨biteHeap, biteSteps, biteHeap_ok, biteHeap_sz, rfl,
    bite_steps_length, bite_path_leaf 1 7 biteSent, by norm_num, by norm_num [biteSent], rfl⟩

/-- The INSERT half: the same key `5` lands — in a tree that has forgotten key `1`. -/
theorem erase_insert_row :
    InsertImtRowAt biteSent oddSponge MAP_TREE_DEPTH eraseRoot 5 2 biteSent :=
  ⟨[(5, 2)], biteSteps, erase_ok, erase_sz, rfl,
    bite_steps_length, bite_path_leaf 5 2 biteSent⟩

theorem erase_ne : ([(5, 2)] : Heap.FeltHeap) ≠ Heap.set biteHeap 5 2 := by
  rw [bite_set52]
  simp

theorem erase_set_ok : (padImtSchema biteSent).HeapOk (Heap.set biteHeap 5 2) := by
  rw [bite_set52]; exact biteGrown_ok

theorem erase_set_sz : (padImtSchema biteSent).SizeOk MAP_TREE_DEPTH (Heap.set biteHeap 5 2) := by
  rw [bite_set52]; exact biteGrown_sz

/-- **⚑⚑ THE PAIRING ACCEPTS AN ERASURE, AT `MAP_TREE_DEPTH = 16`.** The `.absent` row honestly
certifies that key `5` is fresh under the pre-root of `[(1,7)]`; the op = 3 row honestly lands
`5 ↦ 2` under a post-root — and that post-root commits `[(5,2)]`, in which key `1` **no longer
exists**. Both deployed gate sets accept, the composition denotation holds, and the write denotation
is FALSE. This is what "the pre-root is unconstrained" costs, spelled out on a turn. -/
theorem insertPair_erases_the_rest_of_the_map :
    InsertPairRowAt biteSent oddSponge MAP_TREE_DEPTH biteRoot eraseRoot 5 2
    ∧ insertsFreshS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 5 2 eraseRoot
    ∧ ¬ writesToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 5 2 eraseRoot
    ∧ Heap.get biteHeap 1 = some 7
    ∧ Heap.get ([(5, 2)] : Heap.FeltHeap) 1 = none := by
  have hpair : InsertPairRowAt biteSent oddSponge MAP_TREE_DEPTH biteRoot eraseRoot 5 2 :=
    ⟨⟨1, 7, biteSent, erase_absent_row⟩, biteSent, erase_insert_row⟩
  refine ⟨hpair,
    insertPair_forces_insertsFresh_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH hpair,
    ?_, by decide, by decide⟩
  exact write_denotation_false_of_wrong_preroot mapGood_inhabited biteSent MAP_TREE_DEPTH
    biteHeap_ok biteHeap_sz erase_ok erase_sz erase_set_ok erase_set_sz erase_ne

/-- **⚑⚑ THE PAIRED `.insert` IS NOT SOUND EITHER.** No law of the shape *"an accepting deployed
`.absent` + `.insert` pair forces the write denotation"* exists — the composition the DEPLOYMENT
names is refuted at the deployed depth, at a hash that is injective AND pad-free. (Anti-floor
content: the conclusion is `False`.) -/
theorem insertPair_cannot_force_the_write_denotation :
    ¬ (∀ (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat) (oldRoot newRoot key value : ℤ),
        MapGood hash →
        InsertPairRowAt sent hash dep oldRoot newRoot key value →
        writesToMerkleS (padImtSchema sent) hash dep oldRoot key value newRoot) := by
  intro hbad
  obtain ⟨hpair, -, hno, -, -⟩ := insertPair_erases_the_rest_of_the_map
  exact hno (hbad biteSent oddSponge MAP_TREE_DEPTH biteRoot eraseRoot 5 2 mapGood_inhabited hpair)

/-- **★ AND THE COMPOSITION IS GENUINELY WEAKER, NOT MERELY DIFFERENT** — one pair of roots lies in
both `insertsFreshS` and `writesToMerkleS` (the honest AAFI growth row, `bite_aafi_grows`), another
lies in `insertsFreshS` alone (the erasure). So `insertsFreshS` is the true denotational content of
the deployed pairing, and the gap between it and `writesToMerkleS` is exactly the map-preservation
nobody checks. -/
theorem insertPair_is_strictly_weaker_than_the_write_denotation :
    (insertsFreshS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 5 2 aafiNewRoot
      ∧ writesToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 5 2 aafiNewRoot)
    ∧ (insertsFreshS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 5 2 eraseRoot
      ∧ ¬ writesToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 5 2 eraseRoot) := by
  obtain ⟨-, hfresh, hno, -, -⟩ := insertPair_erases_the_rest_of_the_map
  refine ⟨⟨⟨bite_aafi_absence_fires, bite_fresh_insert_post_opens⟩, bite_aafi_grows.1⟩,
    hfresh, hno⟩

end Erasure

/-! ## §7 — ⚑⚑ THE TENTH IMPOSSIBILITY: A SINGLE-PATH ROW CANNOT DENOTE AN INTERIOR SORTED INSERT.

§6 leaves an obvious repair on the table: add to op = 3 the AAFI-style gate (d1) — *"the free slot
was EMPTY under the pre-root"* — folding `padDigest` up the SAME `MAP_SIB0`/`MAP_DIR0` path that
already carries the new leaf. That would relate the pre-root to the post-root, so it looks like it
closes the erasure. It does not, and the obstruction is structural, not cryptographic.

Any gate set built on the ONE deployed sibling path produces a post-vector of the form
`(padVec … pre).set p x` — that is literally `padOpen_binds_or_resid`'s update clause. But
`heap_root.rs::insert_witness` (`:1087-1121`) splices the fresh leaf into its SORTED position and
rebuilds a COMPACTED tree, so at an interior key the post-vector differs from the pre-vector in the
predecessor's POINTER, in the new cell, and in every shifted cell — three positions, not one.

Consequence: **op = 3 cannot be repaired into soundness on its own shape.** The two-path AAFI op is
not an optimisation of `.insert`; it is the only shape in which a fresh-key insert is expressible at
stable positions. `descriptor_ir2.rs:545-547` reached the same verdict in prose (*"no shared
pre-image binds the shifted suffix"*); this is that sentence as a theorem. -/

section Shift

/-- The interior-insert witness: a two-leaf map, and the fresh key `5` landing BETWEEN them. -/
def shiftHeap : Heap.FeltHeap := [(1, 7), (9, 3)]

theorem shiftHeap_set : Heap.set shiftHeap 5 2 = [(1, 7), (5, 2), (9, 3)] := by
  norm_num [shiftHeap, Heap.set]

/-- The PRE digest vector's live prefix: note the predecessor points at `9`. -/
noncomputable def shiftPre : List ℤ :=
  [imtLeafHash oddSponge ⟨1, 7, 9⟩, imtLeafHash oddSponge ⟨9, 3, 100⟩]

/-- The POST digest vector's live prefix: the predecessor now points at `5`, the new leaf is at
position `1`, and the old position-1 leaf has SHIFTED to position `2`. -/
noncomputable def shiftPost : List ℤ :=
  [imtLeafHash oddSponge ⟨1, 7, 5⟩, imtLeafHash oddSponge ⟨5, 2, 9⟩,
   imtLeafHash oddSponge ⟨9, 3, 100⟩]

theorem shiftPre_length : shiftPre.length = 2 := rfl
theorem shiftPost_length : shiftPost.length = 3 := rfl

/-- ⚠ **THE OCCUPANCIES OF §7, NAMED, AND OFF `hdep` RATHER THAN OFF `heap_fits`.** At a SYMBOLIC
`dep` the discharger cannot reach `2 ≤ 2 ^ dep` — there is nothing for `omega` to do with `2 ^ dep`
and nothing for the kernel to evaluate — and the bound is a CONSEQUENCE of this section's own
`2 ≤ dep` rather than a fact that is absent. `fits_of_pow_le` is the bridge: capacity from a CHEAPER
exponent, so the exhibit never evaluates a power. -/
theorem shiftHeap_fits {dep : Nat} (hdep : 2 ≤ dep) : shiftHeap.length ≤ 2 ^ dep :=
  fits_of_pow_le hdep (by decide)
theorem shiftSet_fits {dep : Nat} (hdep : 2 ≤ dep) :
    (Heap.set shiftHeap 5 2).length ≤ 2 ^ dep := by
  rw [shiftHeap_set]; exact fits_of_pow_le hdep (by decide)
theorem shiftPre_fits {dep : Nat} (hdep : 2 ≤ dep) : shiftPre.length ≤ 2 ^ dep :=
  fits_of_pow_le hdep (by rw [shiftPre_length]; decide)
theorem shiftPost_fits {dep : Nat} (hdep : 2 ≤ dep) : shiftPost.length ≤ 2 ^ dep :=
  fits_of_pow_le hdep (by rw [shiftPost_length]; decide)

theorem shift_pre_vec {dep : Nat} (hdep : 2 ≤ dep) :
    padVec 100 oddSponge dep shiftHeap (shiftHeap_fits hdep)
      = padTo dep shiftPre (shiftPre_fits hdep) := rfl

theorem shift_post_vec {dep : Nat} (hdep : 2 ≤ dep) :
    padVec 100 oddSponge dep (Heap.set shiftHeap 5 2) (shiftSet_fits hdep)
      = padTo dep shiftPost (shiftPost_fits hdep) := by
  have hmap : (imtChainOf 100 (Heap.set shiftHeap 5 2)).map (imtLeafHash oddSponge) = shiftPost := by
    rw [shiftHeap_set]; rfl
  show padTo dep ((imtChainOf 100 (Heap.set shiftHeap 5 2)).map (imtLeafHash oddSponge)) _ = _
  exact padTo_congr hmap _ _

/-- Position `0` moved: the PREDECESSOR'S POINTER went `9 → 5`. Distinct arity-3 preimages, so
distinct digests at an injective hash. -/
theorem shift_pos0_ne :
    imtLeafHash oddSponge ⟨1, 7, 5⟩ ≠ imtLeafHash oddSponge ⟨1, 7, 9⟩ := by
  intro hc
  simp only [imtLeafHash] at hc
  have hl := oddSponge_injective hc
  simp at hl

/-- Position `1` moved: the new entry took the slot the old position-1 leaf held. -/
theorem shift_pos1_ne :
    imtLeafHash oddSponge ⟨5, 2, 9⟩ ≠ imtLeafHash oddSponge ⟨9, 3, 100⟩ := by
  intro hc
  simp only [imtLeafHash] at hc
  have hl := oddSponge_injective hc
  simp at hl

/-- **★★ THE SORTED SPLICE MOVES MORE THAN ONE CELL.** Inserting `5` into `[(1,7),(9,3)]` changes
position `0` (the predecessor's pointer `9 → 5`) AND position `1` (the entry itself) — so the
post-vector is NOT any one-cell update of the pre-vector, at any depth ≥ 2. -/
theorem interior_sorted_insert_moves_more_than_one_cell (dep : Nat) (hdep : 2 ≤ dep) :
    ∀ (p : Nat) (x : ℤ),
      padVec 100 oddSponge dep (Heap.set shiftHeap 5 2) (shiftSet_fits hdep)
        ≠ (padVec 100 oddSponge dep shiftHeap (shiftHeap_fits hdep)).set p x := by
  intro p x he
  rw [shift_pre_vec hdep, shift_post_vec hdep] at he
  have hpre0 : (padTo dep shiftPre (shiftPre_fits hdep))[0]?
      = some (imtLeafHash oddSponge ⟨1, 7, 9⟩) := by
    rw [padTo_getElem?_lt dep shiftPre _ 0 (by rw [shiftPre_length]; omega)]; rfl
  have hpre1 : (padTo dep shiftPre (shiftPre_fits hdep))[1]?
      = some (imtLeafHash oddSponge ⟨9, 3, 100⟩) := by
    rw [padTo_getElem?_lt dep shiftPre _ 1 (by rw [shiftPre_length]; omega)]; rfl
  have hpost0 : (padTo dep shiftPost (shiftPost_fits hdep))[0]?
      = some (imtLeafHash oddSponge ⟨1, 7, 5⟩) := by
    rw [padTo_getElem?_lt dep shiftPost _ 0 (by rw [shiftPost_length]; omega)]; rfl
  have hpost1 : (padTo dep shiftPost (shiftPost_fits hdep))[1]?
      = some (imtLeafHash oddSponge ⟨5, 2, 9⟩) := by
    rw [padTo_getElem?_lt dep shiftPost _ 1 (by rw [shiftPost_length]; omega)]; rfl
  have hp0 : p = 0 := by
    by_contra hne
    have h := congrArg (fun L => L[0]?) he
    rw [List.getElem?_set_ne (fun hc => hne hc)] at h
    rw [hpost0, hpre0] at h
    exact shift_pos0_ne (Option.some.inj h)
  have hp1 : p = 1 := by
    by_contra hne
    have h := congrArg (fun L => L[1]?) he
    rw [List.getElem?_set_ne (fun hc => hne hc)] at h
    rw [hpost1, hpre1] at h
    exact shift_pos1_ne (Option.some.inj h)
  omega

/-- **⚑⚑ THE TENTH IMPOSSIBILITY, AT THE ROOT.** Whatever a one-path op = 3 row folds — the new
leaf, an empty-slot witness, any repair that reuses `MAP_SIB0`/`MAP_DIR0` — the post-root it can
produce is `perfectRoot` of a ONE-CELL update of the committed pre-vector, and that is NEVER the
sorted-insert commitment at an interior key. No amount of extra gates on the single deployed path
fixes op = 3; the shape has to change (which is what the two-path AAFI op is). -/
theorem singlePath_postRoot_is_not_the_sorted_insert (dep : Nat) (hdep : 2 ≤ dep)
    (p : Nat) (x : ℤ) :
    perfectRoot oddSponge dep ((padVec 100 oddSponge dep shiftHeap (shiftHeap_fits hdep)).set p x)
      ≠ padImtRoot 100 oddSponge dep (Heap.set shiftHeap 5 2) (shiftSet_fits hdep) := by
  intro he
  have hlPre : (padVec 100 oddSponge dep shiftHeap (shiftHeap_fits hdep)).length = 2 ^ dep :=
    padVec_length (shiftHeap_fits hdep)
  have hlSet : ((padVec 100 oddSponge dep shiftHeap (shiftHeap_fits hdep)).set p x).length
      = 2 ^ dep := by
    rw [List.length_set]; exact hlPre
  have hlPost : (padVec 100 oddSponge dep (Heap.set shiftHeap 5 2) (shiftSet_fits hdep)).length
      = 2 ^ dep := padVec_length (shiftSet_fits hdep)
  have he' : perfectRoot oddSponge dep
        ((padVec 100 oddSponge dep shiftHeap (shiftHeap_fits hdep)).set p x)
      = perfectRoot oddSponge dep
        (padVec 100 oddSponge dep (Heap.set shiftHeap 5 2) (shiftSet_fits hdep)) := he
  rcases perfectRoot_binds_or_collides oddSponge dep hlSet hlPost he' with hveq | hcol
  · exact interior_sorted_insert_moves_more_than_one_cell dep hdep p x hveq.symm
  · exact spongeColl_refutable_of_injective oddSponge oddSponge_injective _ hcol

end Shift

/-! ## §8 — ⚑⚑ THE THIRD HOST, AND IT IS THE LIVE ONE: `.aafiInsert`.

Read `MapOpsColumnLayout.ReconcileGatesAt` at lines 825-842. The `.write`, `.insert` AND
`.aafiInsert` arms are **the same body, character for character** — one shared path, an old leaf at
`(key, vOld)` folding to the PRE-root, a new leaf folding to the post-root. So
`reconcileGates_insert_forces_key_present` was never about `.insert`: it is about that body, and the
body sits on three arms.

Which arm does the prover actually run? Not `.insert`. The two literal `op := .insert` MapOps in the
emit tree — `EffectVmEmitRotationV3.insertWriteOp` (`:1445`) and `insertWriteOpRot` (`:1925`) — are
**ORPHANS**: no descriptor's `constraints` list contains `.mapOp insertWriteOp` or
`.mapOp insertWriteOpRot` anywhere in the tree. ⚠ THIS CORRECTS `MapAbsentImtGate`'s header
(`:71-73`), which says *"the two surviving op=3 `.insert`s (`insertWriteOp`, `insertWriteOpRot`)
write only `cap_root`"* — they write nothing, because nothing declares them.

What IS wired is `.aafiInsert`: `nullifierInsertOp` (`:2387-2393`, in `noteSpendV3.constraints` at
`:2437`), `commitmentsInsertOp` (`:2648`), `revokedInsertOp` (`:2748`), `cellsInsertOp` (`:2875`).
And every one of those rows has a FRESH key by construction — `heap_root.rs::insert_witness_aafi`
returns `None` when the key is already present (guard at `:1167`, documented at `:1154-1155`),
which is the whole point of the double-spend bracket. So the model's hypothesis is FALSE on every AAFI row the prover emits, for the
same reason and by the same proof.

⚑ **The `.insert` finding's practical weight is therefore on `.aafiInsert`**: it is not a dormant
arm's defect, it is the accumulator arm — nullifiers, commitments, revocations, cells — running on a
premise no honest trace satisfies. -/

/-- The arity-2 model's `.aafiInsert` arm FORCES the row's key into the committed pre-heap — the
same proof as the `.insert` one, because it is the same body. -/
theorem reconcileGates_aafi_forces_key_present (hash : List ℤ → ℤ)
    (hinj : Function.Injective hash) (dep : Nat) (a : Assignment) (m : MapOp)
    (hop : m.op = MapOpKind.aafiInsert) (hg : ReconcileGatesAt hash dep a m) :
    ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ h.length = 2 ^ dep ∧
      mapRoot hash dep h = (m.root 0).eval a ∧ m.key.eval a ∈ Heap.keys h := by
  obtain ⟨h, hs, hlen, hroot, hgates⟩ := hg
  rw [hop] at hgates
  obtain ⟨steps, vOld, hsl, hpOld, _⟩ := hgates
  have hbind := (pathRecompute_binds_updates hash steps (h.map (Heap.leafOf hash))
    (Heap.leafOf hash (m.key.eval a, vOld))
    (by rw [List.length_map, hlen, hsl]) (by rw [hsl]; exact hpOld.trans hroot.symm)
    (noPathColl_of_CR hinj)).1
  simp only [List.getElem?_map] at hbind
  cases he : h[pathPos steps]? with
  | none => rw [he] at hbind; simp at hbind
  | some e =>
    rw [he] at hbind
    simp only [Option.map_some, Option.some.injEq] at hbind
    obtain rfl := leafOf_injective hash (noLeafColl_of_CR hinj) hbind
    exact ⟨h, hs, hlen, hroot, List.mem_map.mpr ⟨_, List.mem_of_getElem? he, rfl⟩⟩

/-- **★★ THE ARITY-2 MODEL HAS NO WITNESS ON A DEPLOYED AAFI INSERT ROW.** `insert_witness_aafi`
refuses a key that is already present, so every emitted `nullifierInsertOp` / `commitmentsInsertOp` /
`revokedInsertOp` / `cellsInsertOp` row carries a FRESH key — and at a fresh key the model's premise
is FALSE. This is `reconcileGates_insert_unsat_at_fresh_key` on the arm that actually ships. -/
theorem reconcileGates_aafi_unsat_at_fresh_key (hash : List ℤ → ℤ)
    (hinj : Function.Injective hash) (dep : Nat) (a : Assignment) (m : MapOp)
    (hop : m.op = MapOpKind.aafiInsert) (h : Heap.FeltHeap) (hlen : h.length = 2 ^ dep)
    (hroot : mapRoot hash dep h = (m.root 0).eval a) (hfresh : m.key.eval a ∉ Heap.keys h) :
    ¬ ReconcileGatesAt hash dep a m := by
  intro hg
  obtain ⟨h', _, hlen', hroot', hmem⟩ :=
    reconcileGates_aafi_forces_key_present hash hinj dep a m hop hg
  have hhh : h' = h :=
    (mapRoot_binds_or_collides hash dep hlen' hlen (hroot'.trans hroot.symm)).resolve_right
      (spongeColl_refutable_of_injective hash hinj _)
  rw [hhh] at hmem
  exact hfresh hmem

/-- **★ THE LIVE ARM IS EMPTY AT THE DEPLOYED DEPTH**, over the epoch's own `spineC` spine: the
deployed AAFI row whose key sits in the terminal gap above every committed address — the ordinary
path for a fresh nullifier — has NO arity-2 gate data. Nothing is enumerated. -/
theorem aafi_old_model_false_fresh_key_at_depth (mA : MapOp) (hop : mA.op = MapOpKind.aafiInsert)
    (hr : (mA.root 0).eval (insRow (mapRoot oddSponge MAP_TREE_DEPTH (imtToHeap depSpine)) depKey 2 0)
        = mapRoot oddSponge MAP_TREE_DEPTH (imtToHeap depSpine))
    (hk : mA.key.eval (insRow (mapRoot oddSponge MAP_TREE_DEPTH (imtToHeap depSpine)) depKey 2 0)
        = depKey) :
    ¬ ReconcileGatesAt oddSponge MAP_TREE_DEPTH
        (insRow (mapRoot oddSponge MAP_TREE_DEPTH (imtToHeap depSpine)) depKey 2 0) mA := by
  refine reconcileGates_aafi_unsat_at_fresh_key oddSponge oddSponge_injective MAP_TREE_DEPTH
    _ mA hop (imtToHeap depSpine) depHeap_length hr.symm ?_
  rw [hk, keys_imtToHeap]
  intro hx
  exact absurd (depSpine_addr_lt depKey hx) (lt_irrefl depKey)

/-! ## §9 — THE BLAST RADIUS: what rested on the arity-2 `.insert` model.

Everything below has the write-shaped arity-2 body (`.write` / `.insert` / `.aafiInsert` — §8: one
body, three arms) as a HYPOTHESIS at a FRESH key, so on every honest deployed insert / AAFI row that
hypothesis is FALSE and the statement is vacuous exactly where the prover operates. This is the same
list `MapAbsentImtGate`'s §5 produced for `.absent`; it is what tells the next lane what to trust.

**(A) SPECIALIZED to `MapOpKind.insert` — fully vacuous on deployed rows.**
`MapOpWideKeyWeld.gates_force_holdsKindW_insert` (`:305`), `.gates_insertW_absentW_jointly_unsat`
(`:339`), `.gates_jointly_unsat_via_abstract'` (`:370`), `.demoInsert_then_absent_unsat` (`:473`),
`.demoInsert_then_absent_unsat_via_abstract` (`:481`);
`MapOpWideKeyRowBoundary.gates_force_holdsKindW_insert_row` (`:333`),
`.gates_insertW_absentW_jointly_unsat_row` (`:376`), `.gates_jointly_unsat_via_abstract_row'`
(`:399`), `.demoRow_insert_then_absent_unsat` (`:762`), `.…_via_abstract` (`:774`);
`MapOpWideKeyGate.insertW_absentW_jointly_unsat'` (`:928`); `MapOpWideKey.insertW_sound` (`:409`),
`.insertW_then_absentW_unsat` (`:432`).
⚠ **CORRECTED 2026-07-26 (`MapAafiLiveRepoint` §10).** This paragraph read *"NINE of these are
registered keystones in `Dregg2/Verify/FloorRatchetBaseline.lean` (`:941`, `:942`, `:945`, `:973`,
`:984`, `:985`, `:988`, `:2042`, `:2046`) — so the vacuity is load-bearing in the assurance case"*.
Three things were wrong. (i) `FloorRatchetBaseline` is NOT a keystone registry: its header says every
name there *"is a declaration whose type takes a hypothesis this tree PROVES FALSE at deployed
BabyBear parameters, so the declaration is VACUOUS"* — registration is a recorded ADMISSION, not a
claim. (ii) The keystone instrument is `Verify/KeystoneLint`'s `@[load_bearing_keystone]` +
`#keystone_audit`, and ZERO of these names carry it. (iii) The line numbers: one of the nine
(`:941`) lands on a name this list discusses, `:945`/`:973` are the `.read` legs this list itself
calls SOUND, `:984`/`:988` are group B, `:2042`/`:2046` are in unrelated modules. The real count is
**TEN**, at `:940`, `:941`, `:944`, `:965`, `:966`, `:972`, `:2066`, `:2068`, `:2070`, `:2072`, and
each is adjudicated by name in `MapAafiLiveRepoint` §10. ⚑ The corrected finding is SHARPER, not
softer: the premise vacuity is invisible to the floor ratchet (which sees only the refuted
`Poseidon2SpongeCR`), invisible to `#keystone_audit`, and invisible to the preflight — it is
UNDETECTED, not load-bearing. And a baseline line for a LIVE carrier must not be deleted:
`FloorRatchet.check` errors on any carrier absent from the baseline.

**(A′) THE SAME, on the LIVE `.aafiInsert` arm (§8).** `MapOpWideKeyWeld.gates_force_holdsKindW_aafiInsert`
(`:313`), `.gates_aafiInsertW_absentW_jointly_unsat` (`:348`), `.gates_jointly_unsat_via_abstract`
(`:361`); `MapOpWideKeyRowBoundary.gates_force_holdsKindW_aafiInsert_row` (`:340`),
`.gates_aafiInsertW_absentW_jointly_unsat_row` (`:387`), `.gates_jointly_unsat_via_abstract_row`
(`:409`); `MapOpWideKeyGate.insertW_absentW_jointly_unsat` (`:921`); `MapOpWideKey.aafiInsertW_sound`
(`:419`). ⚠ These are the ones that BITE: their rows are emitted.
(`MapOpsColumnLayout.AafiGatesAt` / `MapOpWideKeyGate.AafiGatesAtW` / `aafiInsert_forces_imtInsert`
are a SEPARATE two-path model and are NOT affected.)

**(B) GENERIC over all five kinds — sound on `.read`/`.absent`, vacuous on the write-shaped legs.**
`MapOpsColumnLayout.reconcileGates_force_opening` (`:847`), `.mapOp_holds_of_mapReconcile` (`:900`),
`.MapReconcileModelOk` (`:912`), `.mapOpsArm_of_modeler` (`:922`),
`.hbus_of_busModels_and_mapModel` (`:937`), `.airAccept_forces_satisfied2_of_modelers` (`:974`);
`MapOpWideKeyGate.reconcileGatesW_force_openingW` (`:557`), `.mapOpW_gates_force_holds` (`:658`),
and the two `Iff.rfl` transports `.narrow_gates_is_instance` (`:635`) / `.narrow_holdsAt_is_instance`
(`:625`) that land the defect on BOTH models at once;
`MapOpWideKeyRowBoundary.mapOpW_gatesCanon_force_holdsCanon` (`:349`);
`DescriptorIR2.MapOp.holdsAt` (`:577`) and `MapDenotationSchema.MapOp.holdsAtS` (`:196`);
`DecideMapMerkle.mapDecMerkle` (`:128`) and its `_sound` / `_complete` / `_faithful` /
`decideSatisfied2'_iff_Satisfied2` / `instDecidableSatisfied2'` (`:149`, `:200`, `:269`, `:290`,
`:302`) — note `decWritesTo` decides `h.length = 2^16 ∧ (Heap.set h k v).length = 2^16`, which a
FRESH key makes unsatisfiable outright;
`AlgoStarkSoundFanoutMemory.MapReconcileFamily` (`:119`), `.memoryLegs_of_mapShape` (`:218`),
`.algoStarkSound_of_mapShape` (`:266`), `.…_noOodShape` (`:581`), and the per-effect apexes
`algoStarkSound_noteSpend` / `_noteCreate` / `_createCell` / `_createCellFromFactory` / `_spawn` /
`_spawnWrite` (`:388`, `:405`, `:422`, `:439`, `:456`, `:474`) — each fires an `.aafiInsert` row.
⚠ `algoStarkSound_refusal` (`:491`) and `_heapWrite` (`:509`) are CLEAN: their map ops are `.write`
at keys the row's own gate holds present.
`MapReconcileImtRepoint.ReconcileGatesImtAt` (`:256`) and `.mapOpsArmImt_of_modeler` (`:349`) inherit
it too — that repoint fixed `.absent` ONLY, and routes every other kind to the broken arm (`:265`).

**(C) EXHIBITS that instantiate a write-shaped row and were read as insert evidence.**
`MapOpsColumnLayout.toy_insert_op_value_update_gates` / `_fires` / `toy_frozen_insert_bites` (renamed
and restated this session) — key `20`, which `toyHeap` HOLDS.
⚑ AND THE WIDE TWIN HAS THE SAME BLIND SPOT, unflagged until now:
`MapOpWideKeyWeld.demoInsertGateW_accepts` (`:454`) ran `MapOpKind.insert` over
`demoHeapW = [(keyLo,1),(keyHi,2)] → demoHeapW2 = [(keyLo,5),(keyHi,2)]` — `keyLo` is ALREADY in the
heap and the two heaps have the SAME length. It is a value update at the wide key, and it is what
feeds `demoRow_insert_then_absent_unsat` (a floor-ratchet baseline entry, not a keystone — see the
correction above). ⚑ FIXED 2026-07-26: RENAMED `demoValueUpdateGateW_accepts`, with
`demoValueUpdateGateW_key_is_already_committed` promoted to a theorem beside it, and
`MapAafiLiveRepoint.wide_insert_never_grows_the_map` proves FLOOR-FREE that a fresh-key twin cannot
be written at any `LaneEnc` or depth. The `.insert` teeth have never been exercised on an insert, at
either key width, and at the wide width they never can be.

⚠ NOT in the blast radius, and this is the point of the repoint: `insertImtRow_post_opens_of_good`,
`MapOpImtInsertHoldsAt`, §4's fresh-key exhibits and §6's composition are stated over the deployed
shape and hold on exactly the rows the prover emits. -/

/-! ## §10 — AXIOM HYGIENE. -/

#assert_axioms padTo_getElem?_lt
#assert_axioms padImtRoot_ne_mapRoot_of_good
#assert_axioms absentImtGates_force_absence_or_resid
#assert_axioms absentImtRow_forces_absence_of_good
#assert_axioms reconcileGatesImtInsert_insert
#assert_axioms reconcileGatesImtInsert_of_ne_insert
#assert_axioms insertRowImt_forces_post_opening
#assert_axioms mapOpsArmImtInsert_of_modeler
#assert_axioms bite_fresh_insert_row
#assert_axioms bite_fresh_insert_key_is_fresh
#assert_axioms bite_fresh_insert_post_opens
#assert_axioms bite_fresh_insert_forged_value_refused
#assert_axioms bite_fresh_insert_model_holds
#assert_axioms bite_fresh_insert_denotation_holds
#assert_axioms insert_old_model_false_deployed_commitment
#assert_axioms insert_old_model_false_fresh_key_at_depth
#assert_axioms insert_repointed_model_holds_deployed
#assert_axioms toy_insert_row_has_no_repointed_body
#assert_axioms insert_models_are_incomparable
#assert_axioms insertPair_forces_insertsFresh_of_good
#assert_axioms insertPair_erases_the_rest_of_the_map
#assert_axioms insertPair_cannot_force_the_write_denotation
#assert_axioms insertPair_is_strictly_weaker_than_the_write_denotation
#assert_axioms interior_sorted_insert_moves_more_than_one_cell
#assert_axioms singlePath_postRoot_is_not_the_sorted_insert
#assert_axioms reconcileGates_aafi_forces_key_present
#assert_axioms reconcileGates_aafi_unsat_at_fresh_key
#assert_axioms aafi_old_model_false_fresh_key_at_depth

end Dregg2.Circuit.MapInsertImtRepoint
