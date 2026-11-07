/-
# Dregg2.Circuit.MapOpWideKey — the WIDE-KEY map-op IR node (`MapOpW`), and the weld that makes
  the felt-width **kind-D** class widenable producer-side.

## The root cause this file addresses

`Dregg2/Circuit/DescriptorIR2.lean:301-313` types a `MapOp` with 8-felt `root` / `newRoot` groups
but a **scalar `key : EmittedExpr`**. That one line is why every kind-D felt-width site (wound
`docs/WOUND-felt-width-boundaries-2026-07-19.md` #5 / #9 / #11 / #20) is un-widenable *producer
side*: the producer physically cannot hand 8 felts to a 1-felt column. This file authors the
widened IR node **beside** the deployed one — `MapOpW` with `key : Fin 8 → EmittedExpr` — and
proves the soundness of its `.absent` / `.insert` legs by COMPOSING the already-landed Wide8
machinery, plus the one weld nothing had yet: the emitted lex-8 compare gadget bolted to the
widened pointer-bracket keystone.

## What was already proven (COMPOSED here, never re-derived)

  * `Crypto/Digest8KeySpike.lean` — `Digest8Key := Lex (Fin 8 → ℤ)` with its `LinearOrder`;
    `sorted_gap_excludes_digest8`, `imtAbsent_excludes_digest8`, `imtInsert_preserves_digest8`.
  * `Circuit/SortedTreeNonMembershipWide8.lean` — the `[LinearOrder K]`-generic non-membership
    wrapper (`SpineCommitsW`/`keysOfW`/`GapOpenW`/`nonMembership_soundW`) at `K := Digest8Key`,
    plus the `proj0` security delta.
  * `Circuit/SortedTreeInsertWide8.lean` — the insert side (`sortedInsertW`/`update_soundW`/
    `insert_then_no_nonmembershipW`) and the insert/exclude duality.
  * `Circuit/Emit/LexCompare8Emit.lean` — `lexLt8Descriptor` + `lexLt8_refines`: the EMITTED AIR
    block deciding `toLex a < toLex b` over canonical 8-felt keys, as a proven iff.

## What is genuinely NEW here

  1. **`MapOpW`** — the widened IR node, and `MapOpW.narrow` : the DEPLOYED `MapOp` is EXACTLY its
     lane-0 projection (`narrow_key_is_lane0`, `rfl`). So the widening is a conservative extension,
     not a parallel universe, and the wire cost is a theorem (`rowAt` 19 → 26 felts, leaf arity
     3 → 17).
  2. **The weld** `absentBracket_of_lexBlocks` — two satisfied `lexLt8` blocks (`low.addr < k` and
     `k < low.next`, both at the FULL 8-felt lex order) plus a committed low leaf FORCE
     `k ∉ imtAddrs c`. This is the first place the emitted compare gadget and the widened
     bracketing keystone touch; it is what a widened `MapKind::Absent` AIR row means. Its
     completeness twin `absentBracket_realizable` says an honest bracket ADMITS those blocks (the
     gate is not a DoS).
  3. **The wide IMT leaf** `imtLeafHash8` (arity 17 = 8 addr ‖ value ‖ 8 next) with
     `imtLeafHash8_binds_or_collides` — FLOOR-FREE, up to a named collision at the two
     ABSORBED 17-felt preimages — and `imtLeafHash8_injective` cut over to that per-instance
     side condition (⛑ 2026-07-26; it USED to carry `Poseidon2SpongeCR`, which is PROVED FALSE
     at deployed BabyBear parameters and therefore made the statement vacuous there), and the
     anti-launder tooth `narrowLeaf_conflates` / `wideLeaf_separates`: pre-folding the 8-felt
     address to lane 0 and THEN hashing still conflates two distinct keys (the
     `finalSqueezeOnly_still_conflates` shape, at the map leaf).
  4. **Wound #20's prose argument, machine-checked in BOTH directions.**
     `narrow_only_over_revokes`: a same-projection-keyed `.absent` op can only OVER-include, so a
     lane-0 collision is NOT a soundness break — the wound's claim, now a theorem, not a paragraph.
     `narrowAbsent_unprovable`: and yet the SAME collision makes the honest, genuinely-fresh key
     PERMANENTLY unprovable at the narrow key — the availability break, also a theorem.
     `wideAbsent_provable`: at the wide key the same query goes through. `dosDelta_site20`
     packages the three.

## Honest scope (residuals, NOT closed here)

  * The `Opens` predicate is left ABSTRACT (same discipline as the Wide8 wrappers): the realizing
    widened chip row — an arity-17 leaf absorb + two `lexLt8` blocks per bracket — is the Rust
    re-emit, and it is a **VK epoch**. Nothing deployed is touched by this file.
  * The map-op VALUE stays one felt. Value widening is a separate named residual (#4/#10).
  * `MapOpW` is not registered in any descriptor, not emitted, and has no JSON face: adding one
    is the cutover commit, deliberately not here.
  * The `.write` leg (an in-place value update at an EXISTING key, keyed by `heap_addr(coll,key)`)
    is not part of the kind-D class and is intentionally `True` in the widened denotation.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Crypto enters ONLY as the named
`Poseidon2SpongeCR` floor. NEW file; every import read-only; no `sorry`/`admit`/`native_decide`.
Heap safety: all concrete objects are literal 8-element lists / 1-3-element chains.
-/
import Dregg2.Circuit.SortedTreeInsertWide8
import Dregg2.Circuit.MapOpsColumnLayout
import Dregg2.Circuit.Emit.LexCompare8Emit
import Dregg2.Tactics

namespace Dregg2.Circuit.MapOpWideKey

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2 (MapOp MapOpKind)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto.SpongeCarrierReduction (IsSpongeColl)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.LexCompare8Emit (lexBlockHolds lexTf lexLt8_refines)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted ImtAbsent imtAddrs)
open Dregg2.Crypto.NonMembership (Sorted)
open Dregg2.Crypto.Digest8KeySpike (Digest8Key keyLo keyE keyHi spikeLeaves spikeLeaves_sorted
  keyLo_lt_keyE keyE_lt_keyHi spike_member spike_excluded imtAbsent_excludes_digest8)
open Dregg2.Circuit.SortedTreeNonMembershipWide8 (keyOfW SpineCommitsW keysOfW keysOfW_eq_spine
  GapOpenW nonMembership_soundW proj0 demoOpens demoOpens_spine demo_excludes keyLo_present
  lowfelt_collision)
open Dregg2.Circuit.SortedTreeInsertWide8 (sortedInsertW update_soundW insert_then_no_nonmembershipW)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — `Digest8Key` plumbing: lane extensionality and the lane list. -/

/-- Two 8-felt lex keys agreeing lane-by-lane are equal (`Lex` is a type synonym, so this is
`funext` under the `ofLex` identity). -/
theorem digest8_ext {a b : Digest8Key} (h : ∀ i : Fin 8, ofLex a i = ofLex b i) : a = b := by
  show ofLex a = ofLex b
  funext i
  exact h i

/-- **`keyLanes k`** — the 8 felts of a key as the list a chip ABSORB consumes, most-significant
lane first. Written as a literal 8-cons list (not `List.ofFn`) so the injectivity below decomposes
by `List.cons.injEq` alone, and so the arity is visible in the term. -/
def keyLanes (k : Digest8Key) : List ℤ :=
  [ofLex k 0, ofLex k 1, ofLex k 2, ofLex k 3, ofLex k 4, ofLex k 5, ofLex k 6, ofLex k 7]

theorem keyLanes_length (k : Digest8Key) : (keyLanes k).length = 8 := rfl

/-- The lane list DETERMINES the key: absorbing all 8 lanes loses nothing. -/
theorem keyLanes_inj {a b : Digest8Key} (h : keyLanes a = keyLanes b) : a = b := by
  simp only [keyLanes, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine digest8_ext ?_
  intro i
  fin_cases i <;> assumption

/-! ## §1 — `MapOpW`: the widened IR node, and the deployed node as its lane-0 projection. -/

/-- **`MapOpW`** — a boundary reconciliation `(root, key, value, op) → new_root` whose KEY is an
8-felt digest group, not one felt. The faithful widening of `DescriptorIR2.MapOp`: `root` /
`newRoot` are unchanged (they were already 8-felt groups); only `key` grows from
`EmittedExpr` to `Fin 8 → EmittedExpr`. The map-op VALUE stays one felt (named residual). -/
structure MapOpW where
  /-- Selector guard (active iff it evaluates to 1). -/
  guard   : EmittedExpr
  /-- The pre-root as an 8-felt digest group (unchanged from the deployed `MapOp`). -/
  root    : Fin 8 → EmittedExpr
  /-- **THE WIDENING** — the map key as an 8-felt digest group (lane 0 most significant). The
  deployed `MapOp.key : EmittedExpr` is lane 0 of this (`narrow_key_is_lane0`). -/
  key     : Fin 8 → EmittedExpr
  /-- The read/written value (still one felt — value widening is a separate site). -/
  value   : EmittedExpr
  /-- The post-root as an 8-felt digest group (unchanged from the deployed `MapOp`). -/
  newRoot : Fin 8 → EmittedExpr
  /-- Reconciliation kind (the SAME `MapOpKind` — the widening changes no wire op code). -/
  op      : MapOpKind

/-- **`MapOpW.keyAt`** — the row's key, read as a full 8-felt lex key. -/
def MapOpW.keyAt (m : MapOpW) (a : Assignment) : Digest8Key :=
  toLex (fun i : Fin 8 => (m.key i).eval a)

/-- Read the widened key off any assignment whose columns carry the key's lanes. -/
theorem MapOpW.keyAt_eq (m : MapOpW) (a : Assignment) (k : Digest8Key)
    (h : ∀ i : Fin 8, (m.key i).eval a = ofLex k i) : m.keyAt a = k := by
  show toLex (fun i : Fin 8 => (m.key i).eval a) = k
  have hf : (fun i : Fin 8 => (m.key i).eval a) = ofLex k := funext h
  rw [hf]
  rfl

/-- **`MapOpW.narrow`** — the DEPLOYED node: the widened one with its key projected to lane 0.
Everything else is carried through verbatim. -/
def MapOpW.narrow (m : MapOpW) : MapOp :=
  { guard := m.guard, root := m.root, key := m.key 0, value := m.value
  , newRoot := m.newRoot, op := m.op }

/-- **The deployed key IS lane 0 of the widened key.** So `MapOpW` is a conservative extension of
the deployed IR node — the whole kind-D class is "read the other seven lanes", not a new object.
This is the one `rfl` that licenses calling the widening a repair rather than a rewrite. -/
theorem narrow_key_is_lane0 (m : MapOpW) (a : Assignment) :
    (m.narrow).key.eval a = proj0 (m.keyAt a) := rfl

/-- The narrow node's guard / value / op / root groups are byte-identical to the wide node's. -/
theorem narrow_carries_through (m : MapOpW) :
    (m.narrow).guard = m.guard ∧ (m.narrow).value = m.value ∧ (m.narrow).op = m.op ∧
    (m.narrow).root = m.root ∧ (m.narrow).newRoot = m.newRoot :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### §1b — THE EMBEDDING: every deployed narrow map-op lifts, ORDER-PRESERVINGLY.

This is the epoch-shape fact. The kind-D sites (digest keys) are only SOME of the 32 committed
map-op-bearing descriptors; the rest key on a derived heap ADDRESS (`heap_root.rs::heap_addr` =
`hash[coll, key]`) and do not need widening. But the map-ops table is ONE shared LogUp bus, so
either everything widens or a second table forks. The embedding below says everything CAN widen
for free: pin lanes 1..7 to `0`, and because lane 0 is the MOST-significant limb, the lex order on
embedded keys IS the ℤ order — so every sorted-tree invariant a narrow op relies on survives the
lift verbatim. No dual AIR, no key-space migration: a re-emit at a wider tuple. -/

/-- The lane vector of the canonical narrow embedding: the felt in lane 0, zeros elsewhere. -/
def e1 (k : ℤ) : Fin 8 → ℤ := fun i => if i = 0 then k else 0

/-- **`embed1 k`** — a deployed 1-felt map key as an 8-felt key. Lane 0 carries the felt (it is the
MOST-significant limb), lanes 1..7 are zero. -/
def embed1 (k : ℤ) : Digest8Key := toLex (e1 k)

/-- **★ THE EMBEDDING IS ORDER-PRESERVING (both directions).** `embed1 a < embed1 b` at the 8-limb
lex order IFF `a < b` at ℤ. So a narrow sorted tree, lifted lane-0-wise into the widened key space,
is sorted by the SAME order it already was — every `Sorted`/`ImtSorted`/gap-bracket fact about a
deployed narrow tree transports across the lift with no re-proof. This is why the widening is a
flag day and not a migration. -/
theorem embed1_lt (a b : ℤ) : embed1 a < embed1 b ↔ a < b := by
  constructor
  · rintro ⟨i, hpre, hlt⟩
    have hlt' : e1 a i < e1 b i := hlt
    by_cases h0 : i = 0
    · subst h0
      simpa [e1] using hlt'
    · exfalso
      simp only [e1, if_neg h0] at hlt'
      exact absurd hlt' (lt_irrefl 0)
  · intro h
    exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), show e1 a 0 < e1 b 0 by simpa [e1] using h⟩

/-- The deployed narrow key is recovered by the lane-0 projection: the lift is lossless. -/
theorem proj0_embed1 (k : ℤ) : proj0 (embed1 k) = k := by
  simp [proj0, embed1, e1]

/-- …hence the embedding is injective: distinct deployed keys stay distinct after the lift. -/
theorem embed1_injective : Function.Injective embed1 := by
  intro a b h
  rw [← proj0_embed1 a, ← proj0_embed1 b, h]

/-- **`MapOpW.ofNarrow`** — lift a DEPLOYED map-op into the widened node by pinning lanes 1..7 to
the constant `0`. This is the mechanical re-emit every non-kind-D map op takes in the epoch. -/
def MapOpW.ofNarrow (m : MapOp) : MapOpW :=
  { guard := m.guard, root := m.root, key := fun i => if i = 0 then m.key else .const 0
  , value := m.value, newRoot := m.newRoot, op := m.op }

/-- The lift reads exactly the embedded deployed key. -/
theorem ofNarrow_keyAt (m : MapOp) (a : Assignment) :
    (MapOpW.ofNarrow m).keyAt a = embed1 (m.key.eval a) := by
  refine MapOpW.keyAt_eq _ _ _ ?_
  intro i
  show (if i = 0 then m.key else EmittedExpr.const 0).eval a = e1 (m.key.eval a) i
  by_cases h : i = 0
  · simp [h, e1]
  · simp [h, e1, EmittedExpr.eval]

/-- **★ THE ROUND TRIP.** Projecting the lift recovers the DEPLOYED node byte-for-byte — the
widening is a conservative extension of the whole committed map-op family, not just of one site. -/
theorem narrow_ofNarrow (m : MapOp) : (MapOpW.ofNarrow m).narrow = m := by
  cases m
  simp [MapOpW.ofNarrow, MapOpW.narrow]

/-! ### §1c — the WIRE COST of the widening, as arithmetic on the deployed constants. -/

/-- The DEPLOYED map-log receive tuple width: `[root8 (8), key, value, op, new_root8 (8)]`
(`circuit/src/descriptor_ir2.rs::MAP_LOG_WIDTH = 2·CHIP_OUT_LANES + 3 = 19`). -/
def MAP_LOG_WIDTH_NARROW : Nat := 19

/-- The WIDENED map-log receive tuple width: the key becomes an 8-lane group. -/
def MAP_LOG_WIDTH_WIDE : Nat := 26

/-- The deployed IMT leaf absorb arity, `hash[addr, value, next_addr]`
(`heap_root.rs::HeapLeaf::digest8`, `map_leaf_input_cols`). -/
def MAP_LEAF_ARITY_NARROW : Nat := 3

/-- The widened IMT leaf absorb arity: `hash[addr8 (8), value, next_addr8 (8)]`. -/
def MAP_LEAF_ARITY_WIDE : Nat := 17

/-- The widened map-log row of a `MapOpW`: `[root8, key8, value, op, new_root8]`. The deployed
`MapOp.rowAt` scalar face is its lane-0 shadow. -/
def MapOpW.rowAt (m : MapOpW) (a : Assignment) : List ℤ :=
  (List.ofFn fun i : Fin 8 => (m.root i).eval a)
    ++ (List.ofFn fun i : Fin 8 => (m.key i).eval a)
    ++ [m.value.eval a, m.op.code]
    ++ (List.ofFn fun i : Fin 8 => (m.newRoot i).eval a)

theorem MapOpW.rowAt_length (m : MapOpW) (a : Assignment) :
    (m.rowAt a).length = MAP_LOG_WIDTH_WIDE := by
  simp [MapOpW.rowAt, MAP_LOG_WIDTH_WIDE]

-- The bus cost of the widening: +7 felts per map-op row, +14 per leaf absorb.
#guard MAP_LOG_WIDTH_WIDE - MAP_LOG_WIDTH_NARROW == 7
#guard MAP_LEAF_ARITY_WIDE - MAP_LEAF_ARITY_NARROW == 14

/-! ## §2 — The WIDE IMT LEAF: arity 17, injective under the named CR floor, and the anti-launder.

The deployed leaf is `hash[addr, value, next_addr]` at 3 felts (`aafiLeafHash`,
`IndexedMerkleTree.imtLeafHash`). Widening the key widens BOTH the address and the pointer — the
pointer IS the absence bracket, so a wide addr with a narrow pointer would re-open the 31-bit
waist on the high side of every gap. -/

/-- **`imtLeafHash8`** — the arity-17 widened IMT leaf digest `hash[addr8 ‖ value ‖ next8]`. All 8
address lanes and all 8 pointer lanes are absorbed; nothing is pre-folded. -/
def imtLeafHash8 (hash : List ℤ → ℤ) (addr : Digest8Key) (value : ℤ) (next : Digest8Key) : ℤ :=
  hash (keyLanes addr ++ value :: keyLanes next)

/-- **`imtLeafPre8 addr value next`** — the arity-17 leaf's sponge PREIMAGE, named so the
per-instance collision event below is stated at exactly the list the widened digest absorbs
(`imtLeafHash8 hash a v n = hash (imtLeafPre8 a v n)`, `rfl`). -/
def imtLeafPre8 (addr : Digest8Key) (value : ℤ) (next : Digest8Key) : List ℤ :=
  keyLanes addr ++ value :: keyLanes next

theorem imtLeafHash8_eq_pre (hash : List ℤ → ℤ) (addr : Digest8Key) (value : ℤ)
    (next : Digest8Key) : imtLeafHash8 hash addr value next = hash (imtLeafPre8 addr value next) :=
  rfl

/-- The arity-17 preimage DETERMINES all three fields: 8 address lanes, the value, 8 pointer lanes,
recovered by list decomposition alone. No hash hypothesis. -/
theorem imtLeafPre8_inj {a₁ a₂ n₁ n₂ : Digest8Key} {v₁ v₂ : ℤ}
    (h : imtLeafPre8 a₁ v₁ n₁ = imtLeafPre8 a₂ v₂ n₂) : a₁ = a₂ ∧ v₁ = v₂ ∧ n₁ = n₂ := by
  simp only [imtLeafPre8, keyLanes, List.cons_append, List.nil_append, List.cons.injEq,
    and_true] at h
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, hv, q0, q1, q2, q3, q4, q5, q6, q7⟩ := h
  refine ⟨digest8_ext ?_, hv, digest8_ext ?_⟩
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption

/-- **THE HYPOTHESIS-FREE WIDENED-LEAF BINDING.** Equal arity-17 leaf digests force equal
`(addr8, value, next8)` triples OR name a genuine collision of the deployed sponge at the two
ABSORBED preimages. NO floor — the `IndexedMerkleTree.imtLeafHash_binds_or_collides` idiom at the
widened leaf. -/
theorem imtLeafHash8_binds_or_collides (hash : List ℤ → ℤ)
    {a₁ a₂ n₁ n₂ : Digest8Key} {v₁ v₂ : ℤ}
    (h : imtLeafHash8 hash a₁ v₁ n₁ = imtLeafHash8 hash a₂ v₂ n₂) :
    (a₁ = a₂ ∧ v₁ = v₂ ∧ n₁ = n₂)
      ∨ IsSpongeColl hash (imtLeafPre8 a₁ v₁ n₁, imtLeafPre8 a₂ v₂ n₂) := by
  by_cases hpre : imtLeafPre8 a₁ v₁ n₁ = imtLeafPre8 a₂ v₂ n₂
  · exact Or.inl (imtLeafPre8_inj hpre)
  · exact Or.inr ⟨hpre, h⟩

/-- The widened leaf binds all three fields — address, value AND pointer.
⛑ CUT OVER: the refuted `Poseidon2SpongeCR hash` premise is replaced by the per-instance,
refutable side condition at the two NAMED preimages — which the old premise IMPLIES
(`fun hc => hc.1 (hCR _ _ hc.2)`, inlined at the one remaining `hCR`-carrying call site rather than
named, so the cutover mints NO new floor carrier) — exactly as
`IndexedMerkleTree.imtLeafHash_injective` was cut over on
2026-07-25. `Poseidon2SpongeCR` is PROVED FALSE at deployed BabyBear parameters, so the old
statement said nothing about the shipping system; this one is a statement at the deployed sponge. -/
theorem imtLeafHash8_injective (hash : List ℤ → ℤ)
    {a₁ a₂ n₁ n₂ : Digest8Key} {v₁ v₂ : ℤ}
    (hno : ¬ IsSpongeColl hash (imtLeafPre8 a₁ v₁ n₁, imtLeafPre8 a₂ v₂ n₂))
    (h : imtLeafHash8 hash a₁ v₁ n₁ = imtLeafHash8 hash a₂ v₂ n₂) :
    a₁ = a₂ ∧ v₁ = v₂ ∧ n₁ = n₂ :=
  (imtLeafHash8_binds_or_collides hash h).resolve_right hno

/-- **The ANTI-LAUNDER leaf** — the "widen it by hashing the narrow felt" move: fold the 8-felt
address to lane 0 FIRST, then absorb. The wide-looking output is a function of a ~31-bit input. -/
def narrowLeafHash (hash : List ℤ → ℤ) (addr : Digest8Key) (value : ℤ) (next : Digest8Key) : ℤ :=
  hash [proj0 addr, value, proj0 next]

/-- **★ ANTI-LAUNDER TOOTH (`finalSqueezeOnly_still_conflates`, at the map leaf).** The lane-0
pre-fold CONFLATES the distinct keys `keyE` and `keyLo` (they collide on lane 0 — `keyE`'s
difference lives at felt 7): the same leaf digest, for EVERY hash, with no CR hypothesis at all.
Squeezing the address before the absorb is not a widening. -/
theorem narrowLeaf_conflates (hash : List ℤ → ℤ) (value : ℤ) (next : Digest8Key) :
    narrowLeafHash hash keyE value next = narrowLeafHash hash keyLo value next ∧ keyE ≠ keyLo := by
  refine ⟨?_, lowfelt_collision.2⟩
  simp only [narrowLeafHash, lowfelt_collision.1]

/-- **★ THE FIX IS SOUND.** The arity-17 leaf SEPARATES the same pair — the lanes the projection
discards are exactly what the absorb now carries.
⛑ CUT OVER off `Poseidon2SpongeCR`: the premise is now the per-instance non-collision at the TWO
NAMED preimages this row actually absorbs, which the refuted floor implies
(`noWideLeafColl_of_CR`). Unlike the floor, it is satisfiable at deployed BabyBear parameters. -/
theorem wideLeaf_separates (hash : List ℤ → ℤ) (value : ℤ) (next : Digest8Key)
    (hno : ¬ IsSpongeColl hash (imtLeafPre8 keyE value next, imtLeafPre8 keyLo value next)) :
    imtLeafHash8 hash keyE value next ≠ imtLeafHash8 hash keyLo value next := by
  intro h
  exact lowfelt_collision.2 (imtLeafHash8_injective hash hno h).1

/-! ## §3 — THE WELD: the emitted lex-8 compare gadget bolted to the widened pointer bracket.

This is the piece nothing had. `LexCompare8Emit.lexLt8_refines` decides `toLex a < toLex b` in the
AIR; `Digest8KeySpike.imtAbsent_excludes_digest8` turns a pointer bracket at the 8-felt key into
absence. A widened `MapKind::Absent` row is EXACTLY: open the low leaf (arity-17), then run the
two blocks. Soundness of that row is the composition below. -/

/-- The deployed canonicality envelope on a key's 8 cells (`0 ≤ cell < p`) — the same range-check
discipline `lexLt8_refines` consumes. -/
def KeyCanon (k : Fin 8 → ℤ) : Prop := ∀ i : Fin 8, 0 ≤ k i ∧ k i < 2013265921

/-- **`absentBracket_of_lexBlocks` — THE WELD (soundness).** Two satisfied `lexLt8` blocks (one
for `low.addr < k`, one for `k < low.next`, both over the FULL 8 lanes) plus a committed low leaf
in the sorted chain FORCE the queried key ABSENT from the whole committed key spine. Nothing is
assumed about the compare: it is the emitted block's own refinement. This is what a widened
`.absent` map-op row means. -/
theorem absentBracket_of_lexBlocks
    (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ)
    (hcLow : KeyCanon lowAddr) (hcK : KeyCanon kk) (hcNext : KeyCanon lowNext)
    (hLoA : ∀ i : Fin 8, envLo.loc i.val = lowAddr i)
    (hLoB : ∀ i : Fin 8, envLo.loc (8 + i.val) = kk i)
    (hLoBlk : lexBlockHolds lexTf envLo)
    (hHiA : ∀ i : Fin 8, envHi.loc i.val = kk i)
    (hHiB : ∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i)
    (hHiBlk : lexBlockHolds lexTf envHi)
    (c : List (ImtLeaf Digest8Key ℤ)) (hs : ImtSorted c) (val : ℤ)
    (hmem : (⟨toLex lowAddr, val, toLex lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c) :
    toLex kk ∉ imtAddrs c := by
  have hlo : toLex lowAddr < toLex kk :=
    (lexLt8_refines lowAddr kk hcLow hcK).mp ⟨envLo, hLoA, hLoB, hLoBlk⟩
  have hhi : toLex kk < toLex lowNext :=
    (lexLt8_refines kk lowNext hcK hcNext).mp ⟨envHi, hHiA, hHiB, hHiBlk⟩
  exact imtAbsent_excludes_digest8 hs ⟨_, hmem, hlo, hhi⟩

/-- **`absentBracket_realizable` — THE WELD (completeness / anti-DoS).** An HONEST 8-felt bracket
`low.addr < k < low.next` ADMITS both `lexLt8` witness rows: the widened gate is satisfiable
exactly when the bracket is real, so widening the key does not brick honest provers. -/
theorem absentBracket_realizable
    (lowAddr kk lowNext : Fin 8 → ℤ)
    (hcLow : KeyCanon lowAddr) (hcK : KeyCanon kk) (hcNext : KeyCanon lowNext)
    (hlo : toLex lowAddr < toLex kk) (hhi : toLex kk < toLex lowNext) :
    (∃ envLo : VmRowEnv, (∀ i : Fin 8, envLo.loc i.val = lowAddr i)
        ∧ (∀ i : Fin 8, envLo.loc (8 + i.val) = kk i) ∧ lexBlockHolds lexTf envLo)
    ∧ (∃ envHi : VmRowEnv, (∀ i : Fin 8, envHi.loc i.val = kk i)
        ∧ (∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i) ∧ lexBlockHolds lexTf envHi) :=
  ⟨(lexLt8_refines lowAddr kk hcLow hcK).mpr hlo,
   (lexLt8_refines kk lowNext hcK hcNext).mpr hhi⟩

/-! ## §4 — The widened per-kind denotation, and its soundness by composition.

`Opens : Root → Digest8Key × ℤ → Prop` is the ABSTRACT leaf-at-root opening (the widened chip row
is the Rust re-emit; leaving it abstract is the same discipline `SortedTreeNonMembershipWide8`
uses). Every leg below is `nonMembership_soundW` / `update_soundW` INSTANTIATED — zero re-proved
tree combinatorics. -/

section Denotation

variable {Root : Type*}

/-- **`HoldsKindW`** — what one widened map-op row MEANS, per kind, at the full 8-felt key.
`.write` (an in-place value update at an EXISTING key, keyed by the derived `heap_addr`) is NOT in
the kind-D class and is deliberately trivial here. -/
def HoldsKindW (Opens : Root → Digest8Key × ℤ → Prop) (pre post : Root)
    (k : Digest8Key) (v : ℤ) : MapOpKind → Prop
  | .read       => Opens pre (k, v) ∧ post = pre
  | .absent     => k ∉ keysOfW Opens pre ∧ post = pre
  | .write      => True
  | .insert     => ∀ y, y ∈ keysOfW Opens post ↔ (y = k ∨ y ∈ keysOfW Opens pre)
  | .aafiInsert => ∀ y, y ∈ keysOfW Opens post ↔ (y = k ∨ y ∈ keysOfW Opens pre)

/-- **`MapOpW.HoldsW`** — the guarded row denotation: when the selector fires, the row's widened
key means what its kind says. -/
def MapOpW.HoldsW (m : MapOpW) (Opens : Root → Digest8Key × ℤ → Prop) (pre post : Root)
    (a : Assignment) : Prop :=
  m.guard.eval a = 1 → HoldsKindW Opens pre post (m.keyAt a) (m.value.eval a) m.op

/-- Lift a per-kind fact to the guarded row denotation. -/
theorem holdsW_of_kind {m : MapOpW} {Opens : Root → Digest8Key × ℤ → Prop} {pre post : Root}
    {a : Assignment} {kk : MapOpKind} (hop : m.op = kk)
    (h : HoldsKindW Opens pre post (m.keyAt a) (m.value.eval a) kk) :
    m.HoldsW Opens pre post a := fun _ => hop ▸ h

/-- **The `.absent` leg, SOUND at 8 felts.** A covering-gap open valid against the committed
spine proves the widened key absent — `nonMembership_soundW` at `K := Digest8Key`, verbatim. -/
theorem absentW_sound (Opens : Root → Digest8Key × ℤ → Prop) (pre : Root)
    (k : Digest8Key) (v : ℤ) (spine : List Digest8Key)
    (hc : SpineCommitsW Opens pre spine)
    (g : GapOpenW Opens pre k) (hv : g.coversSpine spine) :
    HoldsKindW Opens pre pre k v MapOpKind.absent :=
  ⟨nonMembership_soundW Opens pre k spine hc g hv, rfl⟩

/-- **The `.insert` / `.aafiInsert` leg, SOUND at 8 felts.** A fresh-key insert grows the
committed key set by EXACTLY the widened key — `update_soundW` at `K := Digest8Key`, verbatim. -/
theorem insertW_sound (Opens : Root → Digest8Key × ℤ → Prop) (pre post : Root)
    (k : Digest8Key) (v : ℤ) (spine : List Digest8Key)
    (hold : SpineCommitsW Opens pre spine)
    (hfresh : k ∉ keysOfW Opens pre)
    (hnew : SpineCommitsW Opens post (sortedInsertW k spine)) :
    HoldsKindW Opens pre post k v MapOpKind.insert :=
  update_soundW Opens pre post k spine hold hfresh hnew

/-- The AAFI (append-at-free-index) leg has the SAME scalar denotation as `.insert` — the
two-path append-order forcing is the physical `AafiGatesAt` law, orthogonal to key width. -/
theorem aafiInsertW_sound (Opens : Root → Digest8Key × ℤ → Prop) (pre post : Root)
    (k : Digest8Key) (v : ℤ) (spine : List Digest8Key)
    (hold : SpineCommitsW Opens pre spine)
    (hfresh : k ∉ keysOfW Opens pre)
    (hnew : SpineCommitsW Opens post (sortedInsertW k spine)) :
    HoldsKindW Opens pre post k v MapOpKind.aafiInsert :=
  update_soundW Opens pre post k spine hold hfresh hnew

/-- **THE INSERT/OPEN DUALITY at the widened key — the reason the two sides must move TOGETHER.**
After a widened insert of `k`, ANY widened `.absent` open for `k` against the new root is
contradictory. Read the other way: widening only ONE side leaves the `.absent` op keyed at a
different width from the set it opens against, and the op becomes unopenable rather than safer —
which is exactly why kind D rides ONE epoch. -/
theorem insertW_then_absentW_unsat (Opens : Root → Digest8Key × ℤ → Prop) (pre post : Root)
    (k : Digest8Key) (spine : List Digest8Key)
    (hold : SpineCommitsW Opens pre spine)
    (hfresh : k ∉ keysOfW Opens pre)
    (hnew : SpineCommitsW Opens post (sortedInsertW k spine))
    (g : GapOpenW Opens post k) (hv : g.coversSpine (sortedInsertW k spine)) : False :=
  insert_then_no_nonmembershipW Opens pre post k spine hold hfresh hnew g hv

/-! ### §4b — the NARROW projection of a widened set: the deployed lane-0 keying. -/

/-- **`projOpens`** — the deployed narrow view of a widened opening: a leaf opens at the FELT `n`
iff some 8-felt key projecting to `n` opens. This is exactly what a 1-felt `MapOp.key` can see. -/
def projOpens (Opens : Root → Digest8Key × ℤ → Prop) : Root → ℤ × ℤ → Prop :=
  fun r e => ∃ k : Digest8Key, proj0 k = e.1 ∧ Opens r (k, e.2)

/-- The narrow committed key set is the lane-0 IMAGE of the wide one. -/
theorem mem_keysOfW_projOpens (Opens : Root → Digest8Key × ℤ → Prop) (root : Root) (n : ℤ) :
    n ∈ keysOfW (projOpens Opens) root ↔ ∃ k ∈ keysOfW Opens root, proj0 k = n := by
  constructor
  · rintro ⟨e, he, k, hpk, hop⟩
    exact ⟨k, ⟨(k, e.2), rfl, hop⟩, by rw [hpk]; exact he⟩
  · rintro ⟨k, ⟨⟨e1, e2⟩, he, hop⟩, hpk⟩
    simp only [keyOfW] at he
    subst he
    exact ⟨(n, e2), rfl, e1, hpk, hop⟩

/-- **★ WOUND #20's SOUNDNESS ARGUMENT, MACHINE-CHECKED.** A projection is a function, so a key
genuinely present in the wide set is present in the narrow one too: a lane-0 collision can only
ADD to the narrow set's preimage. A same-projection-keyed `.absent` op therefore OVER-includes,
never UNDER-includes — the narrow width buys an attacker NOTHING on the soundness side. (The
soundness shape is the OPPOSITE polarity: a `.present`/membership-AUTHORIZES op.) -/
theorem narrow_only_over_revokes (Opens : Root → Digest8Key × ℤ → Prop) (root : Root)
    (k : Digest8Key) (hk : k ∈ keysOfW Opens root) :
    proj0 k ∈ keysOfW (projOpens Opens) root :=
  (mem_keysOfW_projOpens Opens root (proj0 k)).mpr ⟨k, hk, rfl⟩

end Denotation

/-! ## §5 — WOUND #20, both directions, on a concrete committed set.

The committed tree is the spike's `[keyLo, keyHi]`. `keyE` is a genuinely FRESH key that COLLIDES
with the present `keyLo` on lane 0 (`keyE` differs at felt 7 — the limb the deployed projection
discards). This is the ~2^31-offline-grind shape of #20 in miniature: one attacker-ground key
lands in the grow-only set's lane-0 image and poisons a DISTINCT, honest key forever. -/

/-- The lane-0 image of the committed set CONTAINS `proj0 keyE` — via the colliding PRESENT
neighbour `keyLo`, even though `keyE` itself was never inserted. The poisoning, as a fact. -/
theorem narrowKeys_poisoned : proj0 keyE ∈ keysOfW (projOpens demoOpens) () :=
  (mem_keysOfW_projOpens demoOpens () (proj0 keyE)).mpr
    ⟨keyLo, keyLo_present, lowfelt_collision.1.symm⟩

/-- **★ THE AVAILABILITY BREAK (#20), MACHINE-CHECKED.** At the DEPLOYED narrow key there is NO
covering-gap witness for the honest, genuinely-fresh `keyE` — refuted for EVERY spine and EVERY
gap shape, not one. The `.absent` op keyed at lane 0 can never be satisfied for it again: the
spend is permanently unprovable. That is the wound's "~2^31 offline hashes ⇒ permanent DoS on
every undelegated `NoteSpend`", stated as a theorem instead of a paragraph. -/
theorem narrowAbsent_unprovable (spine : List ℤ)
    (hc : SpineCommitsW (projOpens demoOpens) () spine)
    (g : GapOpenW (projOpens demoOpens) () (proj0 keyE))
    (hv : g.coversSpine spine) : False :=
  nonMembership_soundW (projOpens demoOpens) () (proj0 keyE) spine hc g hv narrowKeys_poisoned

/-- **★ THE WIDENED KEY SURVIVES.** Against the SAME committed set, the full 8-felt key EXCLUDES
`keyE` — the `keyLo < keyE` bracket is decided at felt 7, the limb the projection discards. The
honest spend is provable again. -/
theorem wideAbsent_provable : keyE ∉ keysOfW demoOpens () := demo_excludes

/-- **★ `dosDelta_site20` — the three-part verdict on wound #20, in one statement.**

  (1) SOUNDNESS is untouched by the width: a genuinely-present key stays present under the
      projection, so the narrow `.absent` op can only OVER-revoke (`narrow_only_over_revokes`).
  (2) AVAILABILITY is broken by the width: the honest fresh `keyE` admits NO narrow gap witness,
      for any spine and any gap shape (`narrowAbsent_unprovable`).
  (3) The WIDENED key repairs exactly (2), leaving (1) intact (`wideAbsent_provable`), and the
      collision is a REAL distinct-key hit, not equality.

This is the priced shape of every kind-D `.absent` site: HIGH availability, NONE soundness. -/
theorem dosDelta_site20 :
    (∀ k : Digest8Key, k ∈ keysOfW demoOpens () → proj0 k ∈ keysOfW (projOpens demoOpens) ())
    ∧ (∀ (spine : List ℤ), SpineCommitsW (projOpens demoOpens) () spine →
        ∀ g : GapOpenW (projOpens demoOpens) () (proj0 keyE), g.coversSpine spine → False)
    ∧ keyE ∉ keysOfW demoOpens ()
    ∧ proj0 keyE = proj0 keyLo ∧ keyE ≠ keyLo :=
  ⟨fun k hk => narrow_only_over_revokes demoOpens () k hk,
   fun spine hc g hv => narrowAbsent_unprovable spine hc g hv,
   wideAbsent_provable, lowfelt_collision.1, lowfelt_collision.2⟩

/-! ## §6 — NON-VACUITY: a concrete widened node whose 8 key columns really carry `keyE`. -/

/-- A widened `.absent` node wired like the deployed `spendAncestorFreshOp`, except its key is the
8-column group `0..7` instead of one param column; the root group rides column 8. -/
def demoAncestorOpW : MapOpW :=
  { guard   := .const 1
  , root    := fun _ => .var 8
  , key     := fun i => .var i.val
  , value   := .const 0
  , newRoot := fun _ => .var 8
  , op      := .absent }

/-- A row assignment carrying `keyE`'s eight lanes in columns `0..7`. -/
def envKeyE : Assignment := fun c => if h : c < 8 then ofLex keyE ⟨c, h⟩ else 0

/-- **★ The widened node READS a real 8-felt key** — `keyAt` on this row is exactly `keyE`, the
key whose distinguishing limb is felt 7. -/
theorem demoAncestorOpW_keyAt : demoAncestorOpW.keyAt envKeyE = keyE := by
  refine MapOpW.keyAt_eq _ _ _ ?_
  intro i
  show envKeyE i.val = ofLex keyE i
  simp only [envKeyE, dif_pos i.isLt]

/-- **★ …and its DEPLOYED lane-0 projection reads the colliding felt** — the same felt `keyLo`
projects to. One node, two readings: the wide one separates, the narrow one conflates. -/
theorem demoAncestorOpW_narrow_collides :
    (demoAncestorOpW.narrow).key.eval envKeyE = proj0 keyLo := by
  rw [narrow_key_is_lane0, demoAncestorOpW_keyAt]
  exact lowfelt_collision.1

/-- **★ The widened node's `.absent` denotation HOLDS on this row** (against the committed spike
tree) — the gate is live, not vacuous. -/
theorem demoAncestorOpW_holds :
    demoAncestorOpW.HoldsW demoOpens () () envKeyE := by
  refine holdsW_of_kind rfl ?_
  rw [demoAncestorOpW_keyAt]
  exact ⟨demo_excludes, rfl⟩

/-! ## §7 — axiom hygiene: every keystone rests on the kernel triple only. -/

#assert_axioms digest8_ext
#assert_axioms keyLanes_inj
#assert_axioms narrow_key_is_lane0
#assert_axioms embed1_lt
#assert_axioms proj0_embed1
#assert_axioms embed1_injective
#assert_axioms ofNarrow_keyAt
#assert_axioms narrow_ofNarrow
#assert_axioms MapOpW.rowAt_length
#assert_axioms imtLeafPre8_inj
#assert_axioms imtLeafHash8_binds_or_collides
#assert_axioms imtLeafHash8_injective
#assert_axioms narrowLeaf_conflates
#assert_axioms wideLeaf_separates
#assert_axioms absentBracket_of_lexBlocks
#assert_axioms absentBracket_realizable
#assert_axioms absentW_sound
#assert_axioms insertW_sound
#assert_axioms aafiInsertW_sound
#assert_axioms insertW_then_absentW_unsat
#assert_axioms mem_keysOfW_projOpens
#assert_axioms narrow_only_over_revokes
#assert_axioms narrowKeys_poisoned
#assert_axioms narrowAbsent_unprovable
#assert_axioms wideAbsent_provable
#assert_axioms dosDelta_site20
#assert_axioms demoAncestorOpW_keyAt
#assert_axioms demoAncestorOpW_narrow_collides
#assert_axioms demoAncestorOpW_holds

end Dregg2.Circuit.MapOpWideKey
