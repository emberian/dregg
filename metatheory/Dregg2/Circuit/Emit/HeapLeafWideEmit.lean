/-
# Dregg2.Circuit.Emit.HeapLeafWideEmit — the WIDE heap leaf (felt-width #4/#10 LEAF SCHEMA),
Lean-authored AIR, additive.

## What this is (say the substrate out loud)

This is **Lean-authored AIR schema work**: the note-nullifier sorted tree's leaf widened so its
SORT KEY fields are full 8-felt digests. The deployed IMT leaf absorbs
`[addr, value, nextAddr]` with `addr`/`nextAddr` a SINGLE felt each
(`DeployedHeapTree.Heap8Scheme.heapLeafDigest8`, arity 3; emit sites
`EffectVmEmitHeapRoot.siteHeapAddr`/`siteHeapLeaf`, 1-felt addr) — so the KEY the pointer bracket
sorts on is ~31-bit, 2^15.5-collidable, while the tree's NODES are already the faithful 8-felt
`node8`. THIS file widens the leaf: `addr : Digest8` and `nextAddr : Digest8` (8 felts each),
leaf arity 3 → **17** (`addr8 ‖ value ‖ nextAddr8`), folded with the EXISTING
`Heap8Scheme.chipAbsorb8` carrier — the SAME single chip (`descriptor_ir2::chip_absorb_all_lanes`)
that serves `heapNodeOf8` (arity 16) and the narrow leaf (arity 3). No new hash is invented; the
input lists are length-disjoint (17 ∉ {3, 16}), so the chip's per-row `(arity, padded inputs)`
seeding separates the three domains for free, and the cross-domain theorems below make that
separation UNCONDITIONAL (a wide leaf equal to a node or to a narrow leaf IS a named chip
collision).

## Scope — what this lane does and does NOT do

  * **DONE HERE**: the widened leaf schema + digest (`heapLeafWideDigest8`), its absorb-block
    contract byte-pinned (`heapLeafWideDesc` + the marker-leaf pin), binding extracted as data
    (`…_binds_or_collides`, the §H.X discipline), the wide GENTIAN close through the DEPLOYED
    `node8` spine (`wideOpen8_binds_leaf_or_collides`), and the IMT pointer bracket
    `low.addr <_lex k <_lex low.nextAddr` at the LEX order with the exclusion keystone
    instantiated over the WIDE key (`wideBracket_excludes`), plus anti-masquerade teeth.
  * **DEFERRED (not this lane)**: the Rust `heap_root.rs`/`trace_rotated.rs` witness widening;
    the sorted-tree membership AIR wiring that instantiates the byte-pinned lex-compare block
    (`LexCompare8Emit.lexLt8Descriptor`) per bracket compare (that wiring is the follow-up
    LexCompare8Emit's own header names); and decisively the **ember-gated kernel flip**
    (`Dregg2/Exec/NullifierAccumulator.lean:12-23` — landing the wide roots into
    `RecordKernelState` extends the rest-hash/frame apex, a VK-epoch commitment change; NOT
    touched, NOT in scope, do not fire piecemeal).

## The soundness story (what transfers, what is new, what is named honestly)

The soundness side of #4/#10 transferred FREE: `Digest8KeySpike` machine-confirmed
`sorted_gap_excludes` at `Digest8Key := Lex (Fin 8 → ℤ)` and instantiated the deployed IMT
keystones (`imtAbsent_excludes_digest8` / `imtInsert_preserves_digest8` — the exclusion over the
wide key). The field-faithful in-circuit comparison is `LexCompare8Emit.lexLt8_refines`
(byte-pinned, boundary-canaried). THIS file supplies the remaining piece — the leaf schema whose
`addr`/`nextAddr` ARE genuine 8-felt keys — and states the bracket in EXACTLY the vocabulary both
of those close over: `toLex a < toLex b` on `Fin 8 → ℤ` (see `wideBracket_is_two_gadget_props` —
each bracket conjunct IS the RHS of `lexLt8_refines`, so the gadget instantiates per compare with
zero glue).

⚑ Honest local-tree note (the LexCompare8Emit precedent, repeated): `Digest8KeySpike.olean` and
`IndexedMerkleTree`'s import closure (`MapOpsColumnLayout.olean`) are absent from the local build
tree, so the key type is named STRUCTURALLY here — `Lex (Fin 8 → ℤ)`, the literal definition of
the spike's `Digest8Key` abbrev — and the exclusion keystone instantiated in-file is the deployed
`LinearOrder`-generic `NonMembership.sorted_gap_excludes` (the same generic object
`imtAbsent_excludes_digest8` instantiates at the IMT chain; the spike's §2 route). Nothing here
is a twin: `WideHeapLeaf` widens the SAME triple shape `heapLeafDigest8` absorbs, and the
exclusion is the SAME deployed lemma at the wide key.

## Anti-masquerade (the teeth this widening exists for)

Two leaves whose `addr` COLLIDE on lane 0 but differ in lanes 1..7:
  * are conflated by the NARROW schema at EVERY scheme (`narrow_schema_conflates` — the 1-felt
    leaf literally cannot state the difference; this is the disease, proved, not just named);
  * are DISTINCT wide keys (`twins_distinct_keys`), their difference is BRACKET-VISIBLE
    (`twinB_bracketed` — the lane-7-only twin lands strictly inside the pointer gap), the
    exclusion FIRES over the wide key (`lane0Twin_excluded`), and their wide DIGESTS differ at
    the deployed-shaped chip (the `#guard` pair) — equal wide digests would BE a named 17-block
    chip collision (`wide_twins_bind_or_collide`).

Heap safety: literal lists and small integers only; no `native_decide`; `decide` only on
`Fin 8`/small-ℤ literals. Axiom hygiene: `#assert_axioms ⊆ {propext, Classical.choice,
Quot.sound}` on every theorem below.
-/
import Dregg2.Circuit.DeployedHeapTree
import Dregg2.Crypto.NonMembership
import Dregg2.Crypto.RomCarrierSites
import Mathlib.Order.PiLex

namespace Dregg2.Circuit.Emit.HeapLeafWideEmit

open Dregg2.Circuit.DeployedCapTree (Digest8 Coll8 Compress8CR BABYBEAR_P)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8 pack8_inj coll8_refutable_of_injective)
open Dregg2.Circuit.DeployedHeapTree
open Dregg2.Crypto.NonMembership (Sorted Adjacent sorted_gap_excludes)

set_option autoImplicit false

/-! ## §1 — the WIDE leaf schema: `addr8 ‖ value ‖ nextAddr8`, arity 17. -/

/-- **The WIDE heap leaf** — the felt-width #4/#10 leaf schema: `(addr, value, nextAddr)` with
`addr` and `nextAddr` FULL 8-felt digests (the sort keys of the note-nullifier sorted tree) and
`value` a felt. The widened twin of the narrow triple `ℤ × ℤ × ℤ` that
`Heap8Scheme.heapLeafDigest8` absorbs today — the SAME shape, keys widened 1 felt → 8. -/
abbrev WideHeapLeaf : Type := Digest8 × ℤ × Digest8

/-- **The arity-17 absorb block** `addr8 ‖ value ‖ nextAddr8` — offsets 0..7 the addr lanes
(lane 0 most significant, the `LexCompare8Emit` limb convention), offset 8 the value, offsets
9..16 the nextAddr lanes. Written as the explicit 17-element literal so the schema IS the
definition (the narrow `heapLeafDigest8` absorbs its literal `[e.1, e.2.1, e.2.2]` the same
way). -/
def wideLeafBlock (e : WideHeapLeaf) : List ℤ :=
  [ e.1 0, e.1 1, e.1 2, e.1 3, e.1 4, e.1 5, e.1 6, e.1 7
  , e.2.1
  , e.2.2 0, e.2.2 1, e.2.2 2, e.2.2 3, e.2.2 4, e.2.2 5, e.2.2 6, e.2.2 7 ]

/-- Leaf arity 17 — length-disjoint from BOTH existing domains of the shared chip (narrow leaf 3,
`node8` 16), so the per-row `(arity, padded inputs)` seeding separates the wide leaf for free. -/
theorem wideLeafBlock_length (e : WideHeapLeaf) : (wideLeafBlock e).length = 17 := rfl

/-- The wide block is injective in the whole leaf — all 8 addr lanes, the value, AND all 8
pointer lanes. Pure list/product plumbing, no crypto (the widened `heapLeafBlock_inj`). -/
theorem wideLeafBlock_inj {e₁ e₂ : WideHeapLeaf} (h : wideLeafBlock e₁ = wideLeafBlock e₂) :
    e₁ = e₂ := by
  simp only [wideLeafBlock, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hv, n0, n1, n2, n3, n4, n5, n6, n7⟩ := h
  refine Prod.ext ?_ (Prod.ext hv ?_)
  · funext i; fin_cases i <;> assumption
  · funext i; fin_cases i <;> assumption

/-! ### §1.d — the schema contract, byte-pinned (`heapLeafWideDesc`).

There is deliberately NO standalone `EffectVmDescriptor2` here: the wide leaf is an absorb
SCHEMA riding the shared chip, and the gates that consume it (the splice `MapOp` + the per-bracket
`lexLt8` blocks) are the deferred sorted-tree wiring. What Rust's widened
`heap_root.rs::HeapLeaf::digest8` must byte-match is the absorb ORDER and OFFSETS — pinned twice:
the decodable schema record (repr-pinned) and the marker-leaf block value (order-pinned: any
offset swap or off-by-one flips the guard). -/

/-- The wide heap-leaf absorb-schema record — the decodable contract for the Rust witness
widening (name, arity, and the `[addrLo, addrHi) / valueOff / [nextLo, nextHi)` offsets). -/
structure WideLeafSchema where
  name     : String
  arity    : Nat
  addrLo   : Nat
  addrHi   : Nat
  valueOff : Nat
  nextLo   : Nat
  nextHi   : Nat
  deriving Repr, DecidableEq

/-- **`heapLeafWideDesc`** — THE wide heap-leaf schema descriptor. -/
def heapLeafWideDesc : WideLeafSchema :=
  { name := "dregg-heap-leaf-wide-digest8-v1"
  , arity := 17, addrLo := 0, addrHi := 8, valueOff := 8, nextLo := 9, nextHi := 17 }

/-- The descriptor's arity is the block's length, for EVERY leaf — the pin is a name FOR the
block, not a free-floating string. -/
theorem desc_arity_faithful (e : WideHeapLeaf) :
    (wideLeafBlock e).length = heapLeafWideDesc.arity := rfl

/-- Offset faithfulness: the descriptor's offsets read back the leaf's own fields. -/
theorem desc_addr_lane0_faithful (e : WideHeapLeaf) :
    (wideLeafBlock e)[heapLeafWideDesc.addrLo]? = some (e.1 0) := rfl
theorem desc_value_faithful (e : WideHeapLeaf) :
    (wideLeafBlock e)[heapLeafWideDesc.valueOff]? = some e.2.1 := rfl
theorem desc_next_lane0_faithful (e : WideHeapLeaf) :
    (wideLeafBlock e)[heapLeafWideDesc.nextLo]? = some (e.2.2 0) := rfl
theorem desc_last_lane_faithful (e : WideHeapLeaf) :
    (wideLeafBlock e)[16]? = some (e.2.2 7) := rfl

/-- The marker leaf: every lane carries a distinct sentinel, so the block pin below detects any
reorder/off-by-one in the absorb schema. -/
def markerLeaf : WideHeapLeaf :=
  (fun i => (100 : ℤ) + i.val, 999, fun i => (200 : ℤ) + i.val)

-- **The absorb-order byte-pin**: `addr8 ‖ value ‖ nextAddr8`, exactly.
#guard wideLeafBlock markerLeaf ==
  [100, 101, 102, 103, 104, 105, 106, 107, 999, 200, 201, 202, 203, 204, 205, 206, 207]

-- **The schema-record byte-pin** (`#eval reprStr heapLeafWideDesc` → pasted → guarded).
#guard reprStr heapLeafWideDesc ==
  "{ name := \"dregg-heap-leaf-wide-digest8-v1\",\n  arity := 17,\n  addrLo := 0,\n  addrHi := 8,\n  valueOff := 8,\n  nextLo := 9,\n  nextHi := 17 }"

/-! ## §2 — the WIDE leaf digest on the SHARED chip, binding extracted as data (§H.X style). -/

/-- **`heapLeafWideDigest8 S8 e`** — the wide 8-felt heap-leaf digest: the SINGLE 8-output chip
absorb over the 17-felt block `addr8 ‖ value ‖ nextAddr8`. The SAME `chipAbsorb8` carrier as
`heapNodeOf8` (arity 16) and the narrow `heapLeafDigest8` (arity 3) — one heap hash everywhere,
REUSED, not invented; 17 ∉ {3, 16} keeps the domains separated (§2-cross below makes that a
theorem, not a remark). -/
def heapLeafWideDigest8 (S8 : Heap8Scheme) (e : WideHeapLeaf) : Digest8 :=
  S8.chipAbsorb8 (wideLeafBlock e)

/-- The wide-leaf extractor: the two arity-17 blocks the chip absorbed. -/
def wideLeafColl8Find (e₁ e₂ : WideHeapLeaf) : List ℤ × List ℤ :=
  (wideLeafBlock e₁, wideLeafBlock e₂)

/-- **EXACT-PROP SKELETON — ⚑ NOT THE HEADLINE BINDING (see §RomSuccessor's
`wideLeaf_binds_rom`).** At deployed parameters a chip collision EXISTS by pigeonhole
(`compress8CR_false_babyBear`), so this disjunction is satisfiable through the collides branch;
the exported binding is the keyed-ROM reduction.  Retained because `wideOpen8_binds_leaf_or_collides`
and the `_of_injective` strength bridge derive from it.

(The widened `heapLeafDigest8_binds_or_collides`.)
Equal wide digests EITHER force the whole widened triple equal — all 8 addr lanes, the value,
AND all 8 pointer lanes, so a prover can neither vary a lane-1..7 key limb nor relink the sorted
chain while keeping the leaf — OR the two arity-17 blocks ARE a genuine chip collision, handed
back by name. -/
theorem heapLeafWide_binds_or_collides (S8 : Heap8Scheme) {e₁ e₂ : WideHeapLeaf}
    (h : heapLeafWideDigest8 S8 e₁ = heapLeafWideDigest8 S8 e₂) :
    e₁ = e₂ ∨ Coll8 S8.chipAbsorb8 (wideLeafColl8Find e₁ e₂) := by
  by_cases he : e₁ = e₂
  · exact Or.inl he
  · exact Or.inr ⟨fun hf => he (wideLeafBlock_inj hf), h⟩

/-- **(CANARY.)** The collision disjunct is REFUTABLE at an injective chip — the disjunction
carries strictly more than `True` (the §H.S discipline). -/
theorem wideLeafColl_refutable_of_injective (S8 : Heap8Scheme)
    (hCR : Compress8CR S8.chipAbsorb8) (e₁ e₂ : WideHeapLeaf) :
    ¬ Coll8 S8.chipAbsorb8 (wideLeafColl8Find e₁ e₂) :=
  coll8_refutable_of_injective hCR _

/-- **NO STRENGTH LOST** — at an injective chip the wide digest is injective outright. -/
theorem heapLeafWide_injective_of_injective (S8 : Heap8Scheme)
    (hCR : Compress8CR S8.chipAbsorb8) {e₁ e₂ : WideHeapLeaf}
    (h : heapLeafWideDigest8 S8 e₁ = heapLeafWideDigest8 S8 e₂) : e₁ = e₂ := by
  rcases heapLeafWide_binds_or_collides S8 h with he | hc
  · exact he
  · exact absurd hc (coll8_refutable_of_injective hCR _)

/-! ### §2-cross — domain separation as THEOREMS (the shared chip cannot be masqueraded
across arities). -/

/-- A wide leaf whose digest equals a NARROW leaf's digest IS a named chip collision — the
arity-17 and arity-3 blocks can never be the same list. The wide leaf cannot silently pose as
(or be posed by) the deployed 1-felt-key leaf it lands beside. -/
theorem wideLeaf_narrow_cross_collides (S8 : Heap8Scheme) (ew : WideHeapLeaf) (en : ℤ × ℤ × ℤ)
    (h : heapLeafWideDigest8 S8 ew = Heap8Scheme.heapLeafDigest8 S8 en) :
    Coll8 S8.chipAbsorb8 (wideLeafBlock ew, [en.1, en.2.1, en.2.2]) := by
  refine ⟨fun hf => ?_, h⟩
  have hlen := congrArg List.length hf
  simp [wideLeafBlock] at hlen

/-- A wide leaf whose digest equals a `node8` image IS a named chip collision (17 ≠ 16) — the
widened leaf folds UNDER the existing node without ever being confusable WITH one. -/
theorem wideLeaf_node8_cross_collides (S8 : Heap8Scheme) (ew : WideHeapLeaf) (l r : Digest8)
    (h : heapLeafWideDigest8 S8 ew = Heap8Scheme.heapNodeOf8 S8 l r) :
    Coll8 S8.chipAbsorb8 (wideLeafBlock ew, pack8 l r) := by
  refine ⟨fun hf => ?_, h⟩
  have hlen := congrArg List.length hf
  simp [wideLeafBlock, pack8] at hlen

/-! ### §2-spine — the wide leaf FOLDS into the DEPLOYED `node8` spine (reuse, then teeth). -/

/-- The wide leaf digest is a `Digest8`, so the DEPLOYED membership walk applies VERBATIM — no
new tree, no new recursion; `recomposeUp8` is already the generic `recomposeG` at `node8`. -/
theorem wideLeaf_folds_into_deployed_spine (S8 : Heap8Scheme) (e : WideHeapLeaf)
    (path : List (CapMerkleGeneric.StepG Digest8)) :
    Heap8Scheme.recomposeUp8 S8 (heapLeafWideDigest8 S8 e) path
      = CapMerkleGeneric.recomposeG (Heap8Scheme.heapNodeOf8 S8)
          (heapLeafWideDigest8 S8 e) path := rfl

/-- The wide-open extractor: the spine walk's colliding pair if it found one, else the two
arity-17 leaf blocks (the widened `heapOpen8Find`). -/
def wideOpen8Find (S8 : Heap8Scheme) (e₁ e₂ : WideHeapLeaf)
    (path : List (CapMerkleGeneric.StepG Digest8)) : List ℤ × List ℤ :=
  if Coll8 S8.chipAbsorb8
      (Heap8Scheme.recomposeUp8Find S8
        (heapLeafWideDigest8 S8 e₁) (heapLeafWideDigest8 S8 e₂) path)
  then Heap8Scheme.recomposeUp8Find S8
        (heapLeafWideDigest8 S8 e₁) (heapLeafWideDigest8 S8 e₂) path
  else wideLeafColl8Find e₁ e₂

/-- **EXACT-PROP SKELETON — ⚑ NOT THE HEADLINE (its ROM successor is the ONE site of this file
still to repoint).** The path-opening successor composes the §RomSuccessor leaf carrier with
`Crypto.RomMerkleOpening.merkleOpenRom_binds` (two leaves, ONE shared sibling path — the
same-context transpose shape): leaf digests differ ⇒ a `merkleOpenForgery` win at accumulator
level (extractor pays two extra leaf queries), leaf digests agree ⇒ a leaf-carrier win; the union
bound closes both from the proved floor.  Stated here so the successor is a composition of LANDED
kit, not new machinery; until it lands this skeleton remains the deterministic residue.

(The widened `heapOpen8_binds_leaf_or_collides`, riding the SAME deployed spine keystone.) Two WIDE leaves
opening the SAME 8-felt root along the SAME committed path are EITHER the same leaf — all 8 addr
lanes, the value, AND the full 8-felt sorted-chain pointer — OR the deployed chip genuinely
collides at the pair `wideOpen8Find` hands back. A prover cannot keep the published root while
relinking the chain or nudging a lane-1..7 key limb UNLESS it produces a full ~124-bit collision
at a NAMED pair of blocks. -/
theorem wideOpen8_binds_leaf_or_collides (S8 : Heap8Scheme)
    (path : List (CapMerkleGeneric.StepG Digest8)) {e₁ e₂ : WideHeapLeaf}
    (h : Heap8Scheme.recomposeUp8 S8 (heapLeafWideDigest8 S8 e₁) path
       = Heap8Scheme.recomposeUp8 S8 (heapLeafWideDigest8 S8 e₂) path) :
    e₁ = e₂ ∨ Coll8 S8.chipAbsorb8 (wideOpen8Find S8 e₁ e₂ path) := by
  by_cases hif : Coll8 S8.chipAbsorb8
      (Heap8Scheme.recomposeUp8Find S8
        (heapLeafWideDigest8 S8 e₁) (heapLeafWideDigest8 S8 e₂) path)
  · refine Or.inr ?_
    show Coll8 S8.chipAbsorb8 (wideOpen8Find S8 e₁ e₂ path)
    rw [wideOpen8Find, if_pos hif]
    exact hif
  · rcases Heap8Scheme.recomposeUp8_binds_or_collides S8 path h with hdig | hc
    · rcases heapLeafWide_binds_or_collides S8 hdig with he | hec
      · exact Or.inl he
      · refine Or.inr ?_
        show Coll8 S8.chipAbsorb8 (wideOpen8Find S8 e₁ e₂ path)
        rw [wideOpen8Find, if_neg hif]
        exact hec
    · exact absurd hc hif

/-! ## §3 — the KEY view and the pointer bracket at the LEX order.

The sort key is the addr under `Lex (Fin 8 → ℤ)` — STRUCTURALLY the spike's
`Digest8Key := Lex (Fin 8 → ℤ)` (its olean absent locally; the LexCompare8Emit precedent), felt 0
most significant, the exact order `lexLt8_refines` lands in. The bare product order on
`Fin 8 → ℤ` is not linear (the spike's `product_order_incomparable`), so the bracket MUST run
under `Lex` — the synonym is load-bearing. -/

/-- The wide leaf's 8-felt SORT KEY: its `addr` under the lex order. -/
def wideAddrKey (e : WideHeapLeaf) : Lex (Fin 8 → ℤ) := toLex e.1

/-- The wide leaf's 8-felt POINTER key: its `nextAddr` under the lex order. -/
def wideNextKey (e : WideHeapLeaf) : Lex (Fin 8 → ℤ) := toLex e.2.2

/-- **The IMT pointer bracket over the WIDE leaf**: `low.addr <_lex k <_lex low.nextAddr`. The
subjects are the leaf's OWN 8-felt fields — bound into the leaf digest across all 17 felts
(`heapLeafWide_binds_or_collides`), so the bracket's keys are exactly what the committed leaf
carries, not a 1-felt shadow of it. -/
def WideBracket (low : WideHeapLeaf) (k : Lex (Fin 8 → ℤ)) : Prop :=
  wideAddrKey low < k ∧ k < wideNextKey low

/-- **The gadget seam, definitional.** Each bracket conjunct IS the proposition
`toLex a < toLex b` on raw `Fin 8 → ℤ` keys — the exact RHS of
`LexCompare8Emit.lexLt8_refines` — so the byte-pinned in-circuit compare instantiates each
conjunct with zero glue when the sorted-tree AIR wiring lands (one `lexLt8` block per compare,
key columns wired to the leaf's addr/nextAddr lanes at the §1.d offsets). -/
theorem wideBracket_is_two_gadget_props (low : WideHeapLeaf) (k : Fin 8 → ℤ) :
    WideBracket low (toLex k) ↔ (toLex low.1 < toLex k ∧ toLex k < toLex low.2.2) :=
  Iff.rfl

/-! The former `wideKeys_bound_or_collide` — "the bracket keys survive the digest, or the named
17-block collision" — is DELETED (zero consumers): its escape branch is unconditionally available
at deployed parameters.  The exported key-binding claim is §RomSuccessor's
`wideKeysTamper_binds_rom`: a query-bounded adversary cannot keep the wide digest while moving
the SORT KEY, the value, or the POINTER key, except with negligible probability at the sampled
oracle. -/

/-- **⚑ THE EXCLUSION OVER THE WIDE KEY** — the deployed `LinearOrder`-generic keystone
`NonMembership.sorted_gap_excludes` instantiated at `Lex (Fin 8 → ℤ)` with the bracketing
neighbors read off the WIDE leaf's own fields: a key strictly inside `low`'s pointer gap is NOT
in the sorted key list. This is the same instantiation `Digest8KeySpike.
imtAbsent_excludes_digest8` performs at the deployed IMT chain (`ImtLeaf (K := Digest8Key) V` —
the exclusion now over the wide key); that module's olean is absent locally, so the loadable
deployed generic is instantiated here directly — same lemma family, zero new bracketing math. -/
theorem wideBracket_excludes (leaves : List (Lex (Fin 8 → ℤ))) (low : WideHeapLeaf)
    (k : Lex (Fin 8 → ℤ)) (hsorted : Sorted leaves)
    (hadj : Adjacent leaves (wideAddrKey low) (wideNextKey low))
    (hbr : WideBracket low k) : k ∉ leaves :=
  sorted_gap_excludes leaves (wideAddrKey low) (wideNextKey low) k hsorted hadj hbr.1 hbr.2

/-! ## §4 — ANTI-MASQUERADE TEETH: lane-0 collision, lanes-1..7 difference.

`addrTwinA`/`addrTwinB` collide on lane 0 (both `0`) and differ ONLY at lane 7 — the LEAST
significant limb, the harshest anti-lane-0 witness (any lane 1..7 works the same way; lane 7
also exercises the full prefix walk of the lex order). `nextHiKey` differs at lane 0, so the
demo bracket's two compares are decided at DIFFERENT limbs (7 and 0) — genuinely lexicographic,
not a lane-0 disguise. -/

/-- `(0,0,0,0,0,0,0,0)` — the bracketing leaf's addr. -/
def addrTwinA : Digest8 := fun _ => 0

/-- `(0,0,0,0,0,0,0,1)` — lane-0 COLLIDES with `addrTwinA`, differs ONLY at lane 7. -/
def addrTwinB : Digest8 := fun i => if i = 7 then 1 else 0

/-- `(1,0,0,0,0,0,0,0)` — the pointer target, greater at lane 0. -/
def nextHiKey : Digest8 := fun i => if i = 0 then 1 else 0

/-- The lane-0 collision, on the nose: the narrow schema's ENTIRE view of the two keys. -/
theorem twins_collide_on_lane0 : addrTwinA 0 = addrTwinB 0 := rfl

/-- The twins genuinely differ (at lane 7) — as raw digests. -/
theorem twins_differ_lane7 : addrTwinA ≠ addrTwinB := by
  intro h
  have h7 := congrFun h 7
  simp [addrTwinA, addrTwinB] at h7

/-- `addrTwinA <_lex addrTwinB`, decided at lane 7 (all earlier limbs equal — the lex witness
walks the full equal prefix). The lane-1..7 difference IS bracket-visible. -/
theorem twinA_lt_twinB : toLex addrTwinA < toLex addrTwinB := by
  refine ⟨7, fun j hj => ?_, ?_⟩
  · show addrTwinA j = if j = 7 then 1 else 0
    rw [if_neg (Fin.ne_of_lt hj)]
    rfl
  · show addrTwinA 7 < if (7 : Fin 8) = 7 then 1 else 0
    simp [addrTwinA]

/-- `addrTwinB <_lex nextHiKey`, decided at lane 0 (the most-significant limb dominates the
lane-7 `1`). -/
theorem twinB_lt_nextHi : toLex addrTwinB < toLex nextHiKey := by
  refine ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), ?_⟩
  show (if (0 : Fin 8) = 7 then (1 : ℤ) else 0) < if (0 : Fin 8) = 0 then 1 else 0
  decide

/-- `addrTwinA <_lex nextHiKey` — the demo chain's own sortedness. -/
theorem twinA_lt_nextHi : toLex addrTwinA < toLex nextHiKey := by
  refine ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), ?_⟩
  show addrTwinA 0 < if (0 : Fin 8) = 0 then (1 : ℤ) else 0
  simp [addrTwinA]

/-- The demo WIDE leaf: addr `addrTwinA`, pointer `nextHiKey` — the sorted-chain leaf whose gap
the twin key lands in. -/
def demoWideLeaf : WideHeapLeaf := (addrTwinA, 22, nextHiKey)

/-- The SAME value and pointer with the lane-7-twin addr — the leaf the narrow schema cannot
tell apart from `demoWideLeaf`. -/
def demoWideLeafB : WideHeapLeaf := (addrTwinB, 22, nextHiKey)

/-- **★ DISTINCT KEYS.** The lane-0-colliding twins are DISTINCT wide sort keys — NOT conflated
by the wide bracket's order. -/
theorem twins_distinct_keys : wideAddrKey demoWideLeaf ≠ wideAddrKey demoWideLeafB :=
  ne_of_lt twinA_lt_twinB

/-- **★ BRACKET-VISIBLE.** The twin key lands STRICTLY INSIDE `demoWideLeaf`'s pointer gap —
the lane-7 difference is seen by the bracket itself (compares decided at lanes 7 and 0). -/
theorem twinB_bracketed : WideBracket demoWideLeaf (wideAddrKey demoWideLeafB) :=
  ⟨twinA_lt_twinB, twinB_lt_nextHi⟩

/-- The committed sorted wide-key list `[addrTwinA, nextHiKey]` (as lex keys). -/
def demoLeaves : List (Lex (Fin 8 → ℤ)) := [toLex addrTwinA, toLex nextHiKey]

theorem demoLeaves_sorted : Sorted demoLeaves := by
  simp only [demoLeaves, Sorted, List.pairwise_cons, List.mem_singleton, List.not_mem_nil,
    false_implies, implies_true]
  exact ⟨fun a' ha' => by rw [ha']; exact twinA_lt_nextHi, trivial, List.Pairwise.nil⟩

theorem demo_adjacent : Adjacent demoLeaves (wideAddrKey demoWideLeaf) (wideNextKey demoWideLeaf) :=
  ⟨[], [], rfl⟩

/-- **★ THE EXCLUSION FIRES OVER THE WIDE KEY.** The lane-0-colliding twin is excluded from the
committed list by `demoWideLeaf`'s OWN pointer bracket — a real multi-felt bracket (decided at
lanes 7 and 0), the keystone consuming `twinB_bracketed` directly. -/
theorem lane0Twin_excluded : wideAddrKey demoWideLeafB ∉ demoLeaves :=
  wideBracket_excludes demoLeaves demoWideLeaf (wideAddrKey demoWideLeafB)
    demoLeaves_sorted demo_adjacent twinB_bracketed

/-- **DISCRIMINATION TOOTH** — the exclusion is not vacuous about everything: the genuine
member key IS in the list. -/
theorem demo_member : wideAddrKey demoWideLeaf ∈ demoLeaves := by
  simp [demoLeaves, wideAddrKey, demoWideLeaf]

/-! ### §4.n — the NARROW schema's conflation, proved (the disease this file closes). -/

/-- **⚑ THE CONFLATION, AT EVERY SCHEME.** Project the twins to their lane-0 felts (the narrow
schema's whole key) and the narrow leaf digests are EQUAL — definitionally, for ANY chip. The
1-felt schema does not merely risk colliding the twins; it cannot STATE their difference. -/
theorem narrow_schema_conflates (S8 : Heap8Scheme) (v n : ℤ) :
    Heap8Scheme.heapLeafDigest8 S8 (addrTwinA 0, v, n)
      = Heap8Scheme.heapLeafDigest8 S8 (addrTwinB 0, v, n) := rfl

/-- **⚑ THE WIDE SCHEMA DOES NOT.** Equal wide digests for the twins would BE a chip collision
at the two named arity-17 blocks — the schema separates them; only a genuine ~124-bit collision
could re-conflate them. (Below, the `#guard`s show the deployed-shaped chip in fact separates
them.) -/
theorem wide_twins_bind_or_collide (S8 : Heap8Scheme)
    (h : heapLeafWideDigest8 S8 demoWideLeaf = heapLeafWideDigest8 S8 demoWideLeafB) :
    Coll8 S8.chipAbsorb8 (wideLeafColl8Find demoWideLeaf demoWideLeafB) := by
  rcases heapLeafWide_binds_or_collides S8 h with he | hc
  · exact absurd (congrArg Prod.fst he) twins_differ_lane7
  · exact hc

/-! ### §4.g — the teeth COMPUTE at the deployed inhabitant (§H.D-guard style; no
`native_decide`). -/

-- The wide digest is a genuine 8-lane vector, every lane inside the BabyBear range.
#guard (List.ofFn (heapLeafWideDigest8 deployedHeap8Scheme demoWideLeaf)).length == 8
#guard (List.ofFn (heapLeafWideDigest8 deployedHeap8Scheme demoWideLeaf)).all
    (fun x => 0 ≤ x && x < BABYBEAR_P)

-- ★ ANTI-MASQUERADE AT THE DIGEST: the lane-0-colliding, lane-7-differing twins get DIFFERENT
-- wide digests at the deployed-shaped chip…
#guard (List.ofFn (heapLeafWideDigest8 deployedHeap8Scheme demoWideLeaf))
    != (List.ofFn (heapLeafWideDigest8 deployedHeap8Scheme demoWideLeafB))

-- …while the narrow schema hands both the SAME digest (their lane-0 projections coincide) —
-- the conflation of `narrow_schema_conflates`, computed.
#guard (List.ofFn (Heap8Scheme.heapLeafDigest8 deployedHeap8Scheme (addrTwinA 0, 22, nextHiKey 0)))
    == (List.ofFn (Heap8Scheme.heapLeafDigest8 deployedHeap8Scheme (addrTwinB 0, 22, nextHiKey 0)))

-- The widened POINTER binds: a lane-3-only bump in `nextAddr` alone moves the wide digest (the
-- 8-felt chain link is genuinely IN the digest).
#guard (List.ofFn (heapLeafWideDigest8 deployedHeap8Scheme demoWideLeaf))
    != (List.ofFn (heapLeafWideDigest8 deployedHeap8Scheme
          (addrTwinA, 22, fun i => if i = 0 then 1 else if i = 3 then 5 else 0)))

-- The value still binds too.
#guard (List.ofFn (heapLeafWideDigest8 deployedHeap8Scheme demoWideLeaf))
    != (List.ofFn (heapLeafWideDigest8 deployedHeap8Scheme (addrTwinA, 99, nextHiKey)))

/-! ## ⚑ §RomSuccessor — the wide-leaf binding, DISCHARGED on the PROVED keyed-ROM floor.

⚑ THE MODELLING STEP, STATED: the sampled `H : Unit × WideLeafT → Fin (2 ^ l)` idealises the
deployed 17-felt chip absorb at asymptotic width over the TRUNCATED wide-leaf triple
`addr8 ‖ value ‖ nextAddr8` (BabyBear-range lanes — the deployed felt discipline); the arity-17
length separation from the narrow-leaf/node domains is carried here by this site's own family.
The flat single-absorb shape needs NO chain machinery: the extractor is the identity carrier's
own, and `romCarrier_binds` (the birthday floor) closes it at the forger's own budget. -/

section RomSuccessor

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction
open Dregg2.Crypto.RomCarrierSites

/-- The truncated wide heap leaf: 8 addr lanes, the value, 8 pointer lanes — every limb a
BabyBear-range felt (the deployed `wideLeafBlock` shape at genuine felt width). -/
abbrev WideLeafT : Type :=
  (Fin 8 → Fin babyBearP) × Fin babyBearP × (Fin 8 → Fin babyBearP)

/-- **THE WIDE-LEAF KEYED ROM FAMILY** — this site's own arity-17 absorb domain. -/
def wideLeafRomFamily : KeyedRomFamily :=
  flatFamily Unit inferInstance inferInstance ⟨()⟩ (fun _ => WideLeafT)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨(fun _ => ⟨0, babyBearP_pos⟩, ⟨0, babyBearP_pos⟩, fun _ => ⟨0, babyBearP_pos⟩)⟩)

/-- The family's width obligation, closed by construction. -/
theorem wideLeafRomFamily_card_R (l : ℕ) :
    letI := wideLeafRomFamily.rFin l
    Fintype.card (wideLeafRomFamily.R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **THE WIDE-LEAF CARRIER** — the identity carrier: one commitment = one absorb of the whole
truncated triple (the `wideLeafBlock_inj` layout fact is the identity embedding's injectivity). -/
def wideLeafRomCarrier : RomCarrier wideLeafRomFamily :=
  taggedCarrier _ (fun _ => Unit) (fun _ => WideLeafT)
    (fun _ => inferInstance)
    (fun _ _ v => v)
    (fun _ _ _ _ h => h)

/-- **⚑⚑ THE WIDE-LEAF BINDING, DISCHARGED ON THE PROVED FLOOR** — the exported successor of the
demoted `heapLeafWide_binds_or_collides` skeleton: every query-bounded forger that equivocates
one wide-leaf digest between two DISTINCT truncated triples — any addr lane, the value, or any
pointer lane — has NEGLIGIBLE advantage.  NO floor hypothesis, NO escape branch. -/
theorem wideLeaf_binds_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame wideLeafRomFamily wideLeafRomCarrier))
    (hA : RomCarrierEff wideLeafRomFamily wideLeafRomCarrier Q A) :
    Negl (gameAdv (romCarrierGame wideLeafRomFamily wideLeafRomCarrier) A) :=
  romCarrier_binds wideLeafRomFamily wideLeafRomCarrier Q hQ wideLeafRomFamily_card_R A hA

/-- **THE KEY/VALUE/POINTER TAMPER FORGERY** — the successor shape of the deleted
`wideKeys_bound_or_collide`: the adversary wins iff its two triples differ in the SORT KEY
(addr), the value, or the POINTER key (nextAddr), yet carry ONE wide digest at the sampled
oracle. -/
def wideKeysTamper : RomForgery wideLeafRomFamily where
  Ans := fun _ => WideLeafT × WideLeafT
  wins := fun _ H p =>
    (p.1.1 ≠ p.2.1 ∨ p.1.2.1 ≠ p.2.2.1 ∨ p.1.2.2 ≠ p.2.2.2)
      ∧ H ((), p.1) = H ((), p.2)
  winsDec := fun l _ _ => by
    letI := (wideLeafRomFamily.toRomFamily).rDec l
    exact instDecidableAnd

/-- The tamper extractor — a pure output reshaping into the carrier triple (budget preserved). -/
def wideKeysExtract
    (M : ∀ l, OracleComp (wideLeafRomFamily.toRomFamily.D l) (wideLeafRomFamily.toRomFamily.R l)
      (wideKeysTamper.Ans l)) :
    RomCarrierComp wideLeafRomFamily wideLeafRomCarrier :=
  fun l => OracleComp.mapOut (fun p => (((), ()), p.1, p.2)) (M l)

/-- **⚑ THE KEY BINDING, DISCHARGED** — a query-bounded adversary cannot keep the wide digest
while moving the sort key, the value, or the pointer key, except with negligible probability:
the bracket's subjects (`wideAddrKey`/`wideNextKey`) are pinned by the commitment at full
width, on the PROVED floor. -/
theorem wideKeysTamper_binds_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary wideKeysTamper.game)
    (hA : RomForgeryEff wideLeafRomFamily wideKeysTamper Q A) :
    Negl (gameAdv wideKeysTamper.game A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  refine negl_of_le (fun l => (gameAdv_mem_unit wideKeysTamper.game A l).1)
    (fun l => ?_)
    (romCarrier_binds wideLeafRomFamily wideLeafRomCarrier Q hQ wideLeafRomFamily_card_R
      (romCarrierAdv _ _ (wideKeysExtract M))
      ⟨wideKeysExtract M, fun l => OracleComp.mapOut_queryBounded _ (hM l), fun _ _ => rfl⟩)
  refine @winProb_le_of_imp _ (wideKeysTamper.game.instFin l) _ _ (fun H hH => ?_)
  replace hH := (Adversary.hit_eq_true _ _ _).mp hH
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  obtain ⟨hproj, heq⟩ := hH
  have hBrun : (romCarrierAdv _ _ (wideKeysExtract M)).run l H
      = (((), ()), (A.run l H).1, (A.run l H).2) := by
    show (wideKeysExtract M l).eval H = _
    unfold wideKeysExtract
    erw [OracleComp.mapOut_eval, hrun l H]
    rfl
  rw [hBrun]
  refine ⟨fun hc => ?_, heq⟩
  rcases hproj with h | h | h
  · exact h (congrArg Prod.fst hc)
  · exact h (congrArg (fun v : WideLeafT => v.2.1) hc)
  · exact h (congrArg (fun v : WideLeafT => v.2.2) hc)

/-- The truncated lane-0-colliding twins: all-zero addr vs lane-7-one addr, same value, same
pointer — `demoWideLeaf`/`demoWideLeafB` at genuine felt width. -/
def demoWideLeafT : WideLeafT :=
  (fun _ => ⟨0, babyBearP_pos⟩, ⟨22, by norm_num [Dregg2.Crypto.RomCarrierSites.babyBearP]⟩,
   fun i => if i = 0 then ⟨1, one_lt_babyBearP⟩ else ⟨0, babyBearP_pos⟩)

/-- The lane-7 twin. -/
def demoWideLeafBT : WideLeafT :=
  (fun i => if i = 7 then ⟨1, one_lt_babyBearP⟩ else ⟨0, babyBearP_pos⟩,
   ⟨22, by norm_num [Dregg2.Crypto.RomCarrierSites.babyBearP]⟩,
   fun i => if i = 0 then ⟨1, one_lt_babyBearP⟩ else ⟨0, babyBearP_pos⟩)

/-- The truncated twins genuinely differ (lane 7) — the wide schema STATES their difference. -/
theorem demoWideLeafT_ne : demoWideLeafT ≠ demoWideLeafBT := by
  intro h
  have h7 := congrFun (congrArg Prod.fst h) 7
  simp [demoWideLeafT, demoWideLeafBT] at h7

/-- **(TOOTH — the twins' conflation is a WIN, and the admitted refuter-shape is DEFANGED.)**
The `0`-query constant answerer emitting the twins is IN the class, WINS at the constant oracle
(the anti-masquerade content of `wide_twins_bind_or_collide`, at the sampled oracle: conflating
the lane-0-colliding twins IS an equivocation), and is NEGLIGIBLE by the bound. -/
theorem wideTwins_defanged (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    RomCarrierEff wideLeafRomFamily wideLeafRomCarrier Q
        (romCarrierAdv _ _ (constTripleComp _ _ (fun _ => ((), ()))
          (fun _ => demoWideLeafT) (fun _ => demoWideLeafBT)))
      ∧ (∀ l, 0 < gameAdv (romCarrierGame wideLeafRomFamily wideLeafRomCarrier)
          (romCarrierAdv _ _ (constTripleComp _ _ (fun _ => ((), ()))
            (fun _ => demoWideLeafT) (fun _ => demoWideLeafBT))) l)
      ∧ Negl (gameAdv (romCarrierGame wideLeafRomFamily wideLeafRomCarrier)
          (romCarrierAdv _ _ (constTripleComp _ _ (fun _ => ((), ()))
            (fun _ => demoWideLeafT) (fun _ => demoWideLeafBT)))) :=
  ⟨constTriple_in_eff _ _ _ _ _ Q,
    fun l => constTriple_gameAdv_pos _ _ _ _ _ l demoWideLeafT_ne,
    constTriple_binds _ _ _ _ _ Q hQ wideLeafRomFamily_card_R⟩

/-- **(TOOTH — a non-negligible wide-leaf equivocator is OUTSIDE the class.)** -/
theorem wideLeaf_nonNegl_forger_excluded (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame wideLeafRomFamily wideLeafRomCarrier))
    (hnn : ¬ Negl (gameAdv (romCarrierGame wideLeafRomFamily wideLeafRomCarrier) A)) :
    ¬ RomCarrierEff wideLeafRomFamily wideLeafRomCarrier Q A :=
  romCarrier_choiceForger_excluded _ _ Q hQ wideLeafRomFamily_card_R A hnn

end RomSuccessor

/-! ## §5 — axiom hygiene: every theorem rests on the kernel triple only. -/

#assert_axioms wideLeafBlock_inj
#assert_axioms desc_arity_faithful
#assert_axioms desc_addr_lane0_faithful
#assert_axioms desc_value_faithful
#assert_axioms desc_next_lane0_faithful
#assert_axioms desc_last_lane_faithful
#assert_axioms heapLeafWide_binds_or_collides
#assert_axioms wideLeafColl_refutable_of_injective
#assert_axioms heapLeafWide_injective_of_injective
#assert_axioms wideLeaf_narrow_cross_collides
#assert_axioms wideLeaf_node8_cross_collides
#assert_axioms wideLeaf_folds_into_deployed_spine
#assert_axioms wideOpen8_binds_leaf_or_collides
#assert_axioms wideBracket_is_two_gadget_props
#assert_axioms wideBracket_excludes
#assert_axioms twins_collide_on_lane0
#assert_axioms twins_differ_lane7
#assert_axioms twinA_lt_twinB
#assert_axioms twinB_lt_nextHi
#assert_axioms twinA_lt_nextHi
#assert_axioms twins_distinct_keys
#assert_axioms twinB_bracketed
#assert_axioms demoLeaves_sorted
#assert_axioms demo_adjacent
#assert_axioms lane0Twin_excluded
#assert_axioms demo_member
#assert_axioms narrow_schema_conflates
#assert_axioms wide_twins_bind_or_collide
-- §RomSuccessor — the EXPORTED wide-leaf binding on the PROVED keyed-ROM floor.
#assert_axioms wideLeafRomFamily_card_R
#assert_axioms wideLeaf_binds_rom
#assert_axioms wideKeysTamper_binds_rom
#assert_axioms demoWideLeafT_ne
#assert_axioms wideTwins_defanged
#assert_axioms wideLeaf_nonNegl_forger_excluded

end Dregg2.Circuit.Emit.HeapLeafWideEmit
