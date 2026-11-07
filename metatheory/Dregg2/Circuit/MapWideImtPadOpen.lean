/-
# `Dregg2.Circuit.MapWideImtPadOpen` — THE WIDE ANALOGUE OF `padOpen_binds_or_resid`:
  the arity-3 PADDED IMT opening at **8-felt lanes**, floor-free, with NAMED residuals.

`MapAafiLiveRepoint` §10 closed with the one thing it could not close:

> ⚠ NAMED RESIDUAL, not closed here: the WIDE-key (`Digest8Key`) versions of these do not exist.
> The wide analogue of `padOpen_binds_or_resid` — an arity-3 padded opening extractor at 8-felt
> lanes with named residuals instead of `Poseidon2SpongeCR` — is the missing piece, and it is the
> same piece the whole wide file needs to leave the baseline.

This is that piece. `Poseidon2SpongeCR` and `Compress8CR` are PROVED FALSE at deployed BabyBear
parameters, so every wide theorem carrying one is VACUOUSLY TRUE at deployment. The narrow side
escaped in `MapPaddedDenotation` / `MapKindImtGates`: an **unconditional** binding half plus
**named, refutable residuals over SPECIFIC witnesses**, with a clearly-labelled strength bridge at
an injective idealisation. Ported here to the 8-felt lanes.

## THE WIDE FILE'S FLOOR SURFACE, MEASURED (`FloorRatchetBaseline`, HEAD)

Ninety-five grandfathered declarations across the wide-key family carry the refuted
`Poseidon2SpongeCR` — `MapOpWideKeyWeld` 33, `MapOpWideKeyRowBoundary` 28, `MapOpWideKeyGate` 21,
`MapAbsentImtGateWide` 11, `MapOpWideKey` 2 — and `Poseidon2SpongeCR` is the ONLY floor any of them
names. Every one of the 95 routes its crypto through exactly three objects: the arity-9 map-tree
leaf (`leafOfW`), the arity-17 IMT leaf (`imtLeafHash8Of`), and `perfectRoot`. All three are cured
below, so the port is a change of citation, not of proof.

## WHAT IS COMPOSED, NOT RE-DERIVED

The **node layer does not widen** — `perfectRoot` folds a vector of ℤ digests whatever the key
width is. So the entire `_or_collides` spine arrives for free at 8 felts:
`MapMerkleRoot.foldLevel_binds_or_collides` / `perfectRoot_binds_or_collides` (⚑ MOVED there
2026-07-28 from `MapPaddedDenotation`, which carried a verbatim duplicate), the padding algebra (`padTo`, `PadHit`,
`append_replicate_eq_or_hit`, `padTo_eq_or_hit`, `padTo_getElem?`, `padTo_set`, `padTo_snoc_pad`),
the floor-free path law `MapOpsColumnLayout.pathRecompute_binds_updates_or_collides` with its
`pathCollFind` extractor, and the symbolic sparse paths `leftPadPath` / `slot1Path`. Nothing in
that list is restated.

What is genuinely NEW is the **lane-encoded IMT leaf and its relink**: `imtLeafHashE E`, the
arity-`2·E.width + 1` absorb `E.enc addr ‖ value ‖ E.enc next`, and `imtChainOfE`, the relink at an
arbitrary key type. Both are pinned to the landed objects by `rfl`:

  * `imtLeafHashE hash narrowEnc = imtLeafHash hash` — the DEPLOYED arity-3 leaf;
  * `imtLeafHashE hash wideEnc = imtLeafHash8Of hash` — the landed arity-**17** wide leaf, whose
    17 = `2 · 8 + 1` is a `rfl` theorem here (`imtLeafPreE_wide_arity`).

So this is one law at two encodings, and the kernel certifies both ends.

## THE RESIDUALS ARE OVER SPECIFIC NAMED WITNESSES

`OpenResidE` has the same three disjuncts the narrow `OpenResid` has, at the wide leaf:

  1. `IsSpongeColl hash (pathCollFind hash steps (padVecE …) (imtLeafHashE hash E l))` — a genuine
     collision at the pair the TOTAL path extractor returns for THIS path and THIS committed vector;
  2. `IsSpongeColl hash (imtLeafPreE E (chainAtE sent h (pathPos steps)), imtLeafPreE E l)` — a
     genuine collision at the arity-17 leaf pair the TOTAL `chainAtE` extractor names;
  3. `imtLeafHashE hash E l = padDigest` — the opened digest IS `heap_root.rs`'s padding constant.

⚠ None of these is `∃ a b, a ≠ b ∧ hash a = hash b`, which is simply TRUE at deployed parameters
and is a free pass. Each names the PARTICULAR pair a total function of committed data returns.
`ImtLaneTeeth` (§5) is `MapPaddedDenotation.MapLeafTeeth` at a lane encoding, carrying the same two
anti-laundering fields — `resid_refuted` (the residual vanishes at a hash-level `Good`) and
`good_inhabited` (`Good` is non-empty) — so `Resid := True` and `Resid := (h₁ ≠ h₂)` are
unbuildable.

## ⚑⚑ THE TWELFTH IMPOSSIBILITY — WIDENING THE KEY DOES NOT KILL THE PADDING GHOST

Eleven obvious approaches on this epoch have been proved impossible. Here is the twelfth, and it is
the one a reader of the wide epoch would most naturally assume away. `MapPaddedDenotation`'s header
prices the padding ghost at "~2^31 at this 1-felt commitment, ~2^124 at the deployed 8-felt tree",
which invites the reading that the kind-D widening buys the ghost away. It does not, and §8 proves
it: the widening moves the **key** from 1 felt to 8; the padding constant lives in the **digest**,
which is one felt at every key width. `padded_imt8_injectivity_is_refuted` refutes padded
injectivity at `wideEnc` at the DEPLOYED depth, at a hash that IS injective, on heaps that satisfy
`wideEnc.HeapOk` — i.e. sorted AND canonically keyed, the L3 closure included.
`wide_hardenings_do_not_kill_the_ghost` packages the verdict: all three of the epoch's hardenings
(8-felt keys, canonical committed heaps, an injective sponge) hold simultaneously and the ghost
survives. Only a domain-separated padding constant reaches it, exactly as the narrow finding said.

## NON-VACUITY AT `MAP_TREE_DEPTH = 16`, OVER A SPARSE TREE (§7)

A `2^16`-leaf wide commitment holding ONE live leaf, every other cell `EMPTY_SUBTREE_ROOTS` — the
occupancy `CanonicalHeapTree::new` actually produces, and the one the DENSE wide laws
(`c.length = 2 ^ dep`, `MapAbsentImtGateWide`'s named residual #1) have no witness for at all. Both
polarities on both deployed-shaped wide arms: the `.absent` row (24 emitted rows across the seven
committed registries) and the AAFI row (24 emitted rows, the arm that SHIPS). Every root is NAMED
as the padded commitment and never evaluated; every path is the symbolic `leftPadPath` / `slot1Path`
recursion; nothing is enumerated and no `decide` touches a depth-16 object.

## Floors
**NONE, and none assumed.** `Poseidon2SpongeCR` appears in no type and no `Prop`-def body in this
file. The binding halves take no hypothesis on `hash` at all. The `_of_good` bridges ride
`MapGoodE E hash := Function.Injective hash ∧ PadFreeE E hash`, which is `padImtLaneTeeth`'s own
`Good` FIELD (`mapGoodE_is_teeth_good`, `Iff.rfl`) — the same discipline, and the same labelling,
`MapKindImtGates.MapGood` carries: ⚠ the bridge is at an injective idealisation, so only the
`_or_resid` halves are statements about the deployed sponge.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free; no `native_decide`; no
`decide` on any object containing the depth-16 spine. NEW file; every import read-only; no deployed
descriptor / emit / JSON / Rust byte touched.
-/
import Dregg2.Circuit.MapKindImtGates
import Dregg2.Circuit.MapAbsentImtGateWide

namespace Dregg2.Circuit.MapWideImtPadOpen

open Dregg2.Substrate
open Dregg2.Crypto.SpongeCarrierReduction (IsSpongeColl)
open Dregg2.Circuit.Poseidon2Binding (SpongeColl)
open Dregg2.Circuit.MapMerkleRoot (mapNode foldLevel perfectRoot perfectRootFind
  perfectRoot_binds_or_collides)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted ImtAbsent imtAddrs imtAbsent_excludes)
open Dregg2.Circuit.MapPaddedDenotation (padDigest padTo padTo_length padTo_dense PadHit
  padTo_eq_or_hit emptySubtreeRoot
  perfectRoot_all_padding oddSponge oddSponge_injective oddSponge_ne_pad)
open Dregg2.Circuit.MapKindImtGates (padTo_set padTo_getElem? padTo_succ_split padTo_snoc_pad
  padTo_congr
  leftPadPath leftPadPath_length leftPadPath_pos leftPadPath_recompute
  slot1Path slot1Path_length slot1Path_pos slot1Path_recompute)
open Dregg2.Circuit.MapOpsColumnLayout (pathPos pathRecompute pathCollFind
  pathRecompute_binds_updates_or_collides)
open Dregg2.Circuit.MapOpWideKeyGate (LaneEnc narrowEnc wideEnc CanonHeapW imtLeafHash8Of
  imtLeafInput8 keyLo_canon keyHi_canon keyE_canon)
open Dregg2.Circuit.MapOpWideKeyWeld (imtToHeapW keys_imtToHeapW)
open Dregg2.Crypto.Digest8KeySpike (Digest8Key keyLo keyE keyHi keyLo_lt_keyE keyE_lt_keyHi
  keyLo_lt_keyHi)
open Dregg2.Circuit.DescriptorIR2 (MAP_TREE_DEPTH)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## §1 — THE LANE-ENCODED IMT LEAF: one absorb, two deployed instances.

`IndexedMerkleTree.imtLeafHash` absorbs `[addr, value, nextAddr]` — arity 3 because the key
contributes ONE felt. `MapOpWideKeyGate.imtLeafHash8Of` absorbs `addr8 ‖ value ‖ next8` — arity 17
because it contributes EIGHT. Both are `imtLeafHashE` at a `LaneEnc`, and both come back by `rfl`.
The pointer widens with the address, never separately: `halfWideLeaf_forges_absence_of_present`
already proves a wide address with a projected pointer forges a non-membership. -/

section Lane

variable {K : Type} [LinearOrder K]

/-- **`imtLeafPreE E l`** — the IMT leaf's sponge PREIMAGE at key width `E`:
`E.enc addr ‖ value ‖ E.enc nextAddr`, arity `2 · E.width + 1`. Named so every per-instance
collision event below is stated at exactly the list the deployed digest absorbs. -/
def imtLeafPreE (E : LaneEnc K) (l : ImtLeaf K ℤ) : List ℤ :=
  E.enc l.addr ++ l.value :: E.enc l.nextAddr

/-- **`imtLeafHashE hash E l`** — the IMT leaf digest at key width `E`. -/
def imtLeafHashE (hash : List ℤ → ℤ) (E : LaneEnc K) (l : ImtLeaf K ℤ) : ℤ :=
  hash (imtLeafPreE E l)

theorem imtLeafPreE_length (E : LaneEnc K) (l : ImtLeaf K ℤ) :
    (imtLeafPreE E l).length = 2 * E.width + 1 := by
  simp only [imtLeafPreE, List.length_append, List.length_cons, E.enc_length]
  omega

/-- **★ CONSERVATIVE EXTENSION (deployed narrow leaf).** The DEPLOYED arity-3 IMT leaf IS the
`narrowEnc` instance — the kernel, not the eye, certifies that the widening changed no deployed
meaning at the leaf. -/
theorem imtLeafHashE_narrow (hash : List ℤ → ℤ) :
    imtLeafHashE hash narrowEnc = Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash := rfl

/-- **★ CONSERVATIVE EXTENSION (landed wide leaf).** The landed arity-17 wide IMT leaf
(`MapOpWideKeyGate.imtLeafHash8Of`, the one every wide `.absent` / AAFI law is stated over) IS the
`wideEnc` instance. This is the weld that makes every law below a statement about the wide file's
own object rather than a lookalike. -/
theorem imtLeafHashE_wide (hash : List ℤ → ℤ) :
    imtLeafHashE hash wideEnc = imtLeafHash8Of hash := rfl

/-- The wide absorb arity is **17**, as arithmetic on the encoding's own width — `2 · 8 + 1`. -/
theorem imtLeafPreE_wide_arity (l : ImtLeaf Digest8Key ℤ) :
    (imtLeafPreE wideEnc l).length = 17 := imtLeafPreE_length wideEnc l

/-- The lane preimage DETERMINES the leaf: the address lanes, the value and the pointer lanes are
each recovered, because `E.enc` is fixed-width and injective. -/
theorem imtLeafPreE_inj (E : LaneEnc K) {l₁ l₂ : ImtLeaf K ℤ}
    (h : imtLeafPreE E l₁ = imtLeafPreE E l₂) : l₁ = l₂ := by
  obtain ⟨a₁, v₁, n₁⟩ := l₁
  obtain ⟨a₂, v₂, n₂⟩ := l₂
  simp only [imtLeafPreE] at h
  have hlen : (E.enc a₁).length = (E.enc a₂).length := by rw [E.enc_length, E.enc_length]
  obtain ⟨ha, hrest⟩ := List.append_inj h hlen
  simp only [List.cons.injEq] at hrest
  obtain ⟨hv, hn⟩ := hrest
  rw [E.enc_inj ha, hv, E.enc_inj hn]

/-- **★ THE LANE-ENCODED IMT LEAF BINDS — UNCONDITIONALLY.** Equal leaf digests force equal leaves
OR name a genuine collision of the deployed sponge at the two ABSORBED preimages. No floor, at
either width. This is the cured `imtLeafHash8Of_injective`. -/
theorem imtLeafHashE_binds_or_collides (hash : List ℤ → ℤ) (E : LaneEnc K)
    {l₁ l₂ : ImtLeaf K ℤ} (h : imtLeafHashE hash E l₁ = imtLeafHashE hash E l₂) :
    l₁ = l₂ ∨ IsSpongeColl hash (imtLeafPreE E l₁, imtLeafPreE E l₂) := by
  by_cases hpre : imtLeafPreE E l₁ = imtLeafPreE E l₂
  · exact Or.inl (imtLeafPreE_inj E hpre)
  · exact Or.inr ⟨hpre, h⟩

/-! ## §2 — THE RELINK AT AN ARBITRARY KEY TYPE (`relink_next_addrs`, widened). -/

/-- **`imtChainOfE sent h`** — `heap_root.rs::relink_next_addrs` at key type `K`: every entry's
pointer is its sorted SUCCESSOR's address, the terminal one the sentinel. -/
def imtChainOfE (sent : K) : List (K × ℤ) → List (ImtLeaf K ℤ)
  | [] => []
  | [e] => [⟨e.1, e.2, sent⟩]
  | e :: e' :: rest => ⟨e.1, e.2, e'.1⟩ :: imtChainOfE sent (e' :: rest)

/-- The cons equation, with the pointer NAMED (the landed narrow `imtChainOf_cons` hides it behind
an existential, which is enough for length but not for the conservativity below). -/
theorem imtChainOfE_cons (sent : K) (e : K × ℤ) (rest : List (K × ℤ)) :
    imtChainOfE sent (e :: rest)
      = (⟨e.1, e.2, (rest.head?).elim sent Prod.fst⟩ : ImtLeaf K ℤ) :: imtChainOfE sent rest := by
  cases rest with
  | nil => rfl
  | cons e' rest' => rfl

theorem imtChainOfE_length (sent : K) :
    ∀ h : List (K × ℤ), (imtChainOfE sent h).length = h.length := by
  intro h
  induction h with
  | nil => rfl
  | cons e rest ih => rw [imtChainOfE_cons, List.length_cons, List.length_cons, ih]

/-- **The relink is a RETRACTION** — dropping the pointers recovers the heap, at any key width. -/
theorem imtToHeapW_imtChainOfE (sent : K) :
    ∀ h : List (K × ℤ), imtToHeapW (imtChainOfE sent h) = h := by
  intro h
  induction h with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨a, v⟩ := e
    rw [imtChainOfE_cons]
    show (a, v) :: imtToHeapW (imtChainOfE sent rest) = (a, v) :: rest
    rw [ih]

theorem imtChainOfE_injective (sent : K) {h₁ h₂ : List (K × ℤ)}
    (h : imtChainOfE sent h₁ = imtChainOfE sent h₂) : h₁ = h₂ := by
  have hc := congrArg imtToHeapW h
  rwa [imtToHeapW_imtChainOfE, imtToHeapW_imtChainOfE] at hc

theorem keys_imtChainOfE (sent : K) (h : List (K × ℤ)) :
    imtAddrs (imtChainOfE sent h) = Heap.keys h := by
  rw [← keys_imtToHeapW (imtChainOfE sent h), imtToHeapW_imtChainOfE]

/-- **The relink, POSITIONALLY.** Leaf `i` carries `h`'s entry at `i` and the pointer to `h`'s
SUCCESSOR address (the terminal one to `sent`). `imtChainOf_getElem?` at any key width. -/
theorem imtChainOfE_getElem? (sent : K) :
    ∀ (h : List (K × ℤ)) (i : Nat),
      (imtChainOfE sent h)[i]? =
        (h[i]?).map (fun e => (⟨e.1, e.2, (h[i + 1]?).elim sent Prod.fst⟩ : ImtLeaf K ℤ)) := by
  intro h
  induction h with
  | nil => intro i; simp [imtChainOfE]
  | cons e rest ih =>
    intro i
    cases i with
    | zero =>
      cases rest with
      | nil => rfl
      | cons e' rest' => rfl
    | succ j =>
      rw [imtChainOfE_cons]
      show (imtChainOfE sent rest)[j]?
        = (rest[j]?).map (fun x => (⟨x.1, x.2, (rest[j + 1]?).elim sent Prod.fst⟩ : ImtLeaf K ℤ))
      exact ih j

/-- **★ CONSERVATIVE EXTENSION (the relink).** At `K := ℤ` this IS the deployed
`MapDenotationSchema.imtChainOf`. -/
theorem imtChainOfE_narrow (sent : ℤ) :
    ∀ h : Heap.FeltHeap,
      imtChainOfE sent h = Dregg2.Circuit.MapDenotationSchema.imtChainOf sent h := by
  intro h
  induction h with
  | nil => rfl
  | cons e rest ih =>
    rw [imtChainOfE_cons, ih]
    cases rest with
    | nil => rfl
    | cons e' rest' => rfl

/-- **AN ADMISSIBLE HEAP RELINKS TO A WELL-LINKED SORTED CHAIN**, at any key width — the sentinel
bound is what makes the TERMINAL pointer respect `ImtSorted`, exactly as in the narrow
`imtSchema_chain_imtSorted`. -/
theorem chainE_imtSorted (sent : K) :
    ∀ h : List (K × ℤ), Heap.SortedKeys h → (∀ x ∈ Heap.keys h, x < sent) →
      ImtSorted (imtChainOfE sent h) := by
  intro h
  induction h with
  | nil => intro _ _; trivial
  | cons e rest ih =>
    cases rest with
    | nil =>
      intro _ hb
      show e.1 < sent
      exact hb e.1 (by simp [Heap.keys])
    | cons e' rest' =>
      intro hs hb
      have hpw := hs
      rw [Heap.SortedKeys, Heap.keys, List.map_cons, List.map_cons, List.pairwise_cons] at hpw
      have hlt : e.1 < e'.1 := hpw.1 e'.1 (by simp)
      have hstail : Heap.SortedKeys (e' :: rest') := by
        have h2 := hs
        rw [Heap.SortedKeys, Heap.keys, List.map_cons, List.pairwise_cons] at h2
        exact h2.2
      have hbtail : ∀ x ∈ Heap.keys (e' :: rest'), x < sent := by
        intro x hx
        exact hb x (by rw [Heap.keys, List.map_cons] at hx ⊢; exact List.mem_cons_of_mem _ hx)
      cases rest' with
      | nil =>
        show ImtSorted [(⟨e.1, e.2, e'.1⟩ : ImtLeaf K ℤ), (⟨e'.1, e'.2, sent⟩ : ImtLeaf K ℤ)]
        exact ⟨hlt, rfl, hbtail e'.1 (by simp [Heap.keys])⟩
      | cons e'' rest'' =>
        show ImtSorted ((⟨e.1, e.2, e'.1⟩ : ImtLeaf K ℤ)
          :: (⟨e'.1, e'.2, e''.1⟩ : ImtLeaf K ℤ) :: imtChainOfE sent (e'' :: rest''))
        exact ⟨hlt, rfl, ih hstail hbtail⟩

/-! ## §3 — THE PADDED LANE-ENCODED COMMITMENT, and its floor-free binding. -/

/-- **`padVecE E sent hash dep h`** — the digest vector the deployed prover folds at key width `E`:
relink, digest at arity `2 · E.width + 1`, zero-pad to `2 ^ dep`.

⚑ **IT TAKES THE OBLIGATION, and the decision is the SAME one `DeployedMapDenotation.padTo` §3-cap
took — REFUSAL, not truncation — for reasons that are if anything sharper at 8-felt lanes:**

1. **The deployed WIDE builder refuses.** `circuit/src/heap_root.rs:1015-1019`
   (`compute_canonical_heap_root_8`) and `:1149-1153` (`CanonicalHeapTree8::new`) carry the same
   release-active `assert!(leaves.len() <= capacity)` as the 1-felt `CanonicalHeapTree::new` at
   `:560`, whose own comment is "*Fail loudly rather than silently truncate*". A truncating
   `padVecE` would model the exact input the deployed wide builder was written to reject.
2. **Nothing below this refuses the residue.** Below `padVecE` sits `perfectRoot`, which returns ONE
   FELT and carries no length, no arity tag and no refusal — so there is no downstream `Prop` that a
   dropped leaf could ever contradict. This is the discriminator `DescriptorIR2.padTo` fails and
   this one meets: there `chipRow`'s UNTRUNCATED arity tag is checked by
   `over_rate_arity_always_refused`, so truncation is total-correctness with a downstream refusal;
   here truncation is data loss into an admitted, indistinguishable root.
3. **Widening the key does not weaken any of that.** The node layer never widens
   (`perfectRoot_binds_or_collides` is shared verbatim), so `over_capacity_roots_collide` — a
   collision with NO length and NO hash hypothesis — transports to every `LaneEnc` unchanged. It is
   the same defect at `wideEnc` that it is at `narrowEnc`, and §6's twelfth impossibility already
   showed that hardening the KEY buys nothing against a defect in the padding.

`hFits` is a `Prop` the body does not read, so no committed felt moves and every `rfl` below still
closes; an over-capacity site FAILS TO ELABORATE. -/
def padVecE (E : LaneEnc K) (sent : K) (hash : List ℤ → ℤ) (dep : Nat)
    (h : List (K × ℤ)) (hFits : h.length ≤ 2 ^ dep := by heap_fits) : List ℤ :=
  padTo dep ((imtChainOfE sent h).map (imtLeafHashE hash E))
    (by rw [List.length_map, imtChainOfE_length]; exact hFits)

/-- **`padImtRootE E sent hash dep h`** — ⚑ THE DEPLOYED MAP COMMITMENT AT KEY WIDTH `E`. -/
def padImtRootE (E : LaneEnc K) (sent : K) (hash : List ℤ → ℤ) (dep : Nat)
    (h : List (K × ℤ)) (hFits : h.length ≤ 2 ^ dep := by heap_fits) : ℤ :=
  perfectRoot hash dep (padVecE E sent hash dep h hFits)

theorem padImtRootE_unfold (E : LaneEnc K) (sent : K) (hash : List ℤ → ℤ) (dep : Nat)
    (h : List (K × ℤ)) (hFits : h.length ≤ 2 ^ dep) :
    padImtRootE E sent hash dep h hFits
      = perfectRoot hash dep (padTo dep ((imtChainOfE sent h).map (imtLeafHashE hash E))
          (by rw [List.length_map, imtChainOfE_length]; exact hFits)) := rfl

theorem padVecE_length {E : LaneEnc K} {sent : K} {hash : List ℤ → ℤ} {dep : Nat}
    {h : List (K × ℤ)} (hl : h.length ≤ 2 ^ dep) :
    (padVecE E sent hash dep h hl).length = 2 ^ dep :=
  padTo_length (by rw [List.length_map, imtChainOfE_length]; exact hl)

/-- **★ CONSERVATIVE EXTENSION (the commitment).** At `narrowEnc` this IS the deployed
`MapPaddedDenotation.padImtRoot` — the object stage 2b's teeth are built from.

⚠ The two `padTo` obligations differ as TERMS (each is the rewrite its own caller supplied) and are
equal only by proof irrelevance, so this is proved through the BODY — `padTo`'s occupancy argument is
a `Prop` the body never reads, hence unfolding it discharges the dependency instead of asking the
unifier to see through it. A `rw` at the root would hit `motive is not type correct`, which is a
FORMULATION and never a heartbeat budget. -/
theorem padImtRootE_narrow (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat) (h : Heap.FeltHeap)
    (hFits : h.length ≤ 2 ^ dep) :
    padImtRootE narrowEnc sent hash dep h hFits
      = Dregg2.Circuit.MapPaddedDenotation.padImtRoot sent hash dep h hFits := by
  have hL : (imtChainOfE sent h).map (imtLeafHashE hash narrowEnc)
      = (Dregg2.Circuit.MapDenotationSchema.imtChainOf sent h).map
          (Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash) := by
    rw [imtChainOfE_narrow sent h, imtLeafHashE_narrow hash]
  show perfectRoot hash dep (padTo dep _ _) = perfectRoot hash dep (padTo dep _ _)
  simp only [padTo, hL]

/-- **`PadGhostE E sent hash h`** — a LIVE lane-encoded IMT leaf digest of `h` equals the padding
constant. ⚠ A decidable property of the vector the prover COMMITTED, deliberately not an
existential over the hash's domain (which pigeonhole makes free at deployed parameters). -/
def PadGhostE (E : LaneEnc K) (sent : K) (hash : List ℤ → ℤ) (h : List (K × ℤ)) : Prop :=
  PadHit ((imtChainOfE sent h).map (imtLeafHashE hash E))

/-- The hash-level side condition that kills the ghost: the padding constant has NO lane-encoded
IMT leaf preimage. `heap_root.rs` does not check it; it is the named repair. -/
def PadFreeE (E : LaneEnc K) (hash : List ℤ → ℤ) : Prop :=
  ∀ l : ImtLeaf K ℤ, imtLeafHashE hash E l ≠ padDigest

theorem padGhostE_refuted {E : LaneEnc K} {hash : List ℤ → ℤ} (hpf : PadFreeE E hash) (sent : K)
    (h : List (K × ℤ)) : ¬ PadGhostE E sent hash h := by
  intro hmem
  rw [PadGhostE, PadHit, List.mem_map] at hmem
  obtain ⟨l, _, hl⟩ := hmem
  exact hpf l hl

/-- `oddSponge` is injective and never lands on the padding constant, at EVERY key width — so
`PadFreeE` is satisfiable and every `good_inhabited` below is real. -/
theorem padFreeE_oddSponge (E : LaneEnc K) : PadFreeE E oddSponge := fun _ => oddSponge_ne_pad _

/-- The lane-encoded leaf-list extractor: walk to the first differing leaf and hand back the two
ABSORBED preimages. TOTAL, and it branches on a `List ℤ` equality, so no `DecidableEq K` is
needed — which matters at `Digest8Key`, whose order is classical. -/
def imtLeafFindE (E : LaneEnc K) :
    List (ImtLeaf K ℤ) → List (ImtLeaf K ℤ) → List ℤ × List ℤ
  | l :: ls, l' :: ls' =>
      if imtLeafPreE E l = imtLeafPreE E l' then imtLeafFindE E ls ls'
      else (imtLeafPreE E l, imtLeafPreE E l')
  | _, _ => ([], [])

theorem imtLeafFindE_spec (E : LaneEnc K) (hash : List ℤ → ℤ) :
    ∀ (c₁ c₂ : List (ImtLeaf K ℤ)), c₁ ≠ c₂ →
      c₁.map (imtLeafHashE hash E) = c₂.map (imtLeafHashE hash E) →
      SpongeColl hash (imtLeafFindE E c₁ c₂) := by
  intro c₁
  induction c₁ with
  | nil =>
    intro c₂ hne hmap
    cases c₂ with
    | nil => exact absurd rfl hne
    | cons l' ls' => simp at hmap
  | cons l ls ih =>
    intro c₂ hne hmap
    cases c₂ with
    | nil => simp at hmap
    | cons l' ls' =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hleaf, htail⟩ := hmap
      by_cases hll : imtLeafPreE E l = imtLeafPreE E l'
      · have hleq : l = l' := imtLeafPreE_inj E hll
        subst hleq
        have htne : ls ≠ ls' := fun hc => hne (by rw [hc])
        rw [imtLeafFindE, if_pos hll]
        exact ih ls' htne htail
      · rw [imtLeafFindE, if_neg hll]
        exact ⟨hll, hleaf⟩

/-- The padded lane-encoded root extractor: the node descent if it collides, else the leaf scan.
TOTAL — and it stays total across the capacity obligation the way `DeployedMapDenotation`'s narrow
`padImtRootFind` does: the extractor takes NO obligation and branches on the occupancy `dif`,
returning `([], [])` off the domain the commitment is defined on. The residual it names is only ever
read under a hypothesis that both heaps fit, so nothing downstream ever sees the off-domain arm. -/
def padImtRootFindE (E : LaneEnc K) (sent : K) (hash : List ℤ → ℤ) (d : Nat)
    (h₁ h₂ : List (K × ℤ)) : List ℤ × List ℤ :=
  if hz : h₁.length ≤ 2 ^ d ∧ h₂.length ≤ 2 ^ d then
    (if SpongeColl hash (perfectRootFind hash d (padVecE E sent hash d h₁ hz.1)
                                                (padVecE E sent hash d h₂ hz.2))
     then perfectRootFind hash d (padVecE E sent hash d h₁ hz.1) (padVecE E sent hash d h₂ hz.2)
     else imtLeafFindE E (imtChainOfE sent h₁) (imtChainOfE sent h₂))
  else ([], [])

/-- **★★ THE PADDED LANE-ENCODED ROOT BINDS THE HEAP — UNCONDITIONALLY, up to TWO named
residuals.** The wide twin of `MapPaddedDenotation.padImtRoot_binds_or_ghost_or_collides`: relaxed
(sparse) occupancy, zero padding, no floor at the node and none at the leaf, at EVERY key width. -/
theorem padImtRootE_binds_or_ghost_or_collides (E : LaneEnc K) (sent : K) (hash : List ℤ → ℤ)
    (d : Nat) {h₁ h₂ : List (K × ℤ)} (hl₁ : h₁.length ≤ 2 ^ d) (hl₂ : h₂.length ≤ 2 ^ d)
    (heq : padImtRootE E sent hash d h₁ hl₁ = padImtRootE E sent hash d h₂ hl₂) :
    h₁ = h₂ ∨ PadGhostE E sent hash h₁ ∨ PadGhostE E sent hash h₂
      ∨ SpongeColl hash (padImtRootFindE E sent hash d h₁ h₂) := by
  have hz : h₁.length ≤ 2 ^ d ∧ h₂.length ≤ 2 ^ d := ⟨hl₁, hl₂⟩
  by_cases hif : SpongeColl hash (perfectRootFind hash d (padVecE E sent hash d h₁ hl₁)
                                                         (padVecE E sent hash d h₂ hl₂))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [padImtRootFindE, dif_pos hz, if_pos hif]
    exact hif
  · rcases perfectRoot_binds_or_collides hash d (padVecE_length hl₁) (padVecE_length hl₂) heq with
      hpad | hc
    · rcases padTo_eq_or_hit d hpad with hL | hh₁ | hh₂
      · by_cases hne : h₁ = h₂
        · exact Or.inl hne
        · refine Or.inr (Or.inr (Or.inr ?_))
          rw [padImtRootFindE, dif_pos hz, if_neg hif]
          exact imtLeafFindE_spec E hash _ _
            (fun hcc => hne (imtChainOfE_injective sent hcc)) hL
      · exact Or.inr (Or.inl hh₁)
      · exact Or.inr (Or.inr (Or.inl hh₂))
    · exact absurd hc hif

/-! ## §4 — ★★ THE WIDE ANALOGUE OF `padOpen_binds_or_resid`.

This is the residual `MapAafiLiveRepoint` §10 named. Every wide arm law below runs through it. It
takes **no hypothesis on `hash`** — the binding half is unconditional at the deployed sponge — and
everything the refuted floor used to buy is instead NAMED, per-row and refutable. -/

/-- The TOTAL extractor naming the chain leaf a path position points at (off the end it returns the
sentinel-shaped leaf; the spec's live branch never reads that value). Totality is what lets the leaf
residual be stated at a NAMED pair instead of a proof-local binder. -/
def chainAtE (sent : K) (h : List (K × ℤ)) (p : Nat) : ImtLeaf K ℤ :=
  ((imtChainOfE sent h)[p]?).getD ⟨sent, 0, sent⟩

/-- **`OpenResidE`** — the NAMED residual of ONE lane-encoded padded opening. All three disjuncts
are properties of data the row and the commitment actually hold; none quantifies over the hash's
domain, and none is the free-pass shape `∃ a b, a ≠ b ∧ hash a = hash b`. -/
def OpenResidE (E : LaneEnc K) (sent : K) (hash : List ℤ → ℤ) (dep : Nat) (h : List (K × ℤ))
    (hFits : h.length ≤ 2 ^ dep) (steps : List (Bool × ℤ)) (l : ImtLeaf K ℤ) : Prop :=
  IsSpongeColl hash
    (pathCollFind hash steps (padVecE E sent hash dep h hFits) (imtLeafHashE hash E l))
  ∨ IsSpongeColl hash (imtLeafPreE E (chainAtE sent h (pathPos steps)), imtLeafPreE E l)
  ∨ imtLeafHashE hash E l = padDigest

/-- **`MapGoodE E hash`** — the hash-level idealisation at which every residual vanishes. It is
`padImtLaneTeeth`'s own `Good` FIELD (§5), so this file introduces no new hash property. -/
def MapGoodE (E : LaneEnc K) (hash : List ℤ → ℤ) : Prop :=
  Function.Injective hash ∧ PadFreeE E hash

/-- ANTI-LAUNDERING: good hashes EXIST, so `openResidE_refuted` is not discharged by an empty
premise. -/
theorem mapGoodE_inhabited (E : LaneEnc K) : MapGoodE E oddSponge :=
  ⟨oddSponge_injective, padFreeE_oddSponge E⟩

/-- ANTI-LAUNDERING: at a good hash the residual is REFUTED, so `Resid := True` is unbuildable and
the disjunctions below are informative. -/
theorem openResidE_refuted {E : LaneEnc K} {hash : List ℤ → ℤ} (hgood : MapGoodE E hash)
    (sent : K) (dep : Nat) (h : List (K × ℤ)) (hFits : h.length ≤ 2 ^ dep)
    (steps : List (Bool × ℤ)) (l : ImtLeaf K ℤ) :
    ¬ OpenResidE E sent hash dep h hFits steps l := by
  rintro (⟨hne, he⟩ | ⟨hne, he⟩ | hpad)
  · exact hne (hgood.1 he)
  · exact hne (hgood.1 he)
  · exact hgood.2 l hpad

/-- **★★ THE LANE-ENCODED PADDED OPENING BINDS — UNCONDITIONALLY, up to the three named
residuals.** A path recomputing a lane-encoded IMT leaf digest to the padded root of a SPARSE
committed heap (i) BINDS the leaf into the relinked chain at the path's position, (ii) decodes it to
the heap entry there, (iii) pins its pointer to the successor address the relink assigns, and
(iv) FORCES THE UPDATE — the same siblings recompute any replacement leaf to the genuinely updated
padded root. No floor, at any key width.

At `E := wideEnc` this is the arity-3 padded opening at 8-felt lanes — the missing piece. -/
theorem padOpenE_binds_or_resid (E : LaneEnc K) (sent : K) (hash : List ℤ → ℤ) (dep : Nat)
    {h : List (K × ℤ)} {steps : List (Bool × ℤ)} {l : ImtLeaf K ℤ}
    (hlen : h.length ≤ 2 ^ dep) (hsl : steps.length = dep)
    (hpath : pathRecompute hash (imtLeafHashE hash E l) steps = padImtRootE E sent hash dep h) :
    (pathPos steps < h.length
      ∧ (imtChainOfE sent h)[pathPos steps]? = some l
      ∧ h[pathPos steps]? = some (l.addr, l.value)
      ∧ l.nextAddr = (h[pathPos steps + 1]?).elim sent Prod.fst
      ∧ ∀ l' : ImtLeaf K ℤ, pathRecompute hash (imtLeafHashE hash E l') steps
          = perfectRoot hash dep ((padVecE E sent hash dep h).set (pathPos steps)
              (imtLeafHashE hash E l')))
    ∨ OpenResidE E sent hash dep h hlen steps l := by
  by_cases hc1 : IsSpongeColl hash
      (pathCollFind hash steps (padVecE E sent hash dep h) (imtLeafHashE hash E l))
  · exact Or.inr (Or.inl hc1)
  · have hvl : (padVecE E sent hash dep h).length = 2 ^ steps.length := by
      rw [hsl]; exact padVecE_length hlen
    have hroot : pathRecompute hash (imtLeafHashE hash E l) steps
        = perfectRoot hash steps.length (padVecE E sent hash dep h) := by rw [hsl]; exact hpath
    rcases pathRecompute_binds_updates_or_collides hash steps (padVecE E sent hash dep h)
      (imtLeafHashE hash E l) hvl hroot with ⟨hmem, hupd⟩ | hcol
    · rcases padTo_getElem? dep ((imtChainOfE sent h).map (imtLeafHashE hash E)) (pathPos steps)
        (imtLeafHashE hash E l) hmem with ⟨hlt, hcell⟩ | hpad
      · rw [List.length_map, imtChainOfE_length] at hlt
        rw [List.getElem?_map] at hcell
        cases he : (imtChainOfE sent h)[pathPos steps]? with
        | none => rw [he] at hcell; simp at hcell
        | some l₀ =>
          rw [he] at hcell
          simp only [Option.map_some, Option.some.injEq] at hcell
          have hca : chainAtE sent h (pathPos steps) = l₀ := by rw [chainAtE, he]; rfl
          rcases imtLeafHashE_binds_or_collides hash E hcell with heq | hcol2
          · subst heq
            have hdec : ∃ e : K × ℤ, h[pathPos steps]? = some e
                ∧ l₀ = (⟨e.1, e.2, (h[pathPos steps + 1]?).elim sent Prod.fst⟩
                        : ImtLeaf K ℤ) := by
              have he' := he
              rw [imtChainOfE_getElem? sent h (pathPos steps)] at he'
              cases hh : h[pathPos steps]? with
              | none => rw [hh] at he'; simp at he'
              | some e =>
                rw [hh] at he'
                simp only [Option.map_some, Option.some.injEq] at he'
                exact ⟨e, rfl, he'.symm⟩
            obtain ⟨e, hh, hl₀⟩ := hdec
            refine Or.inl ⟨hlt, rfl, ?_, ?_, ?_⟩
            · rw [hh, hl₀]
            · rw [hl₀]
            · intro l'
              have := hupd (imtLeafHashE hash E l')
              rwa [hsl] at this
          · exact Or.inr (Or.inr (Or.inl (by rw [hca]; exact hcol2)))
      · exact Or.inr (Or.inr (Or.inr hpad))
    · exact absurd hcol hc1

end Lane

/-! ## §5 — THE SCHEMA-LEVEL TEETH AT A LANE ENCODING.

`MapPaddedDenotation.MapLeafTeeth` is `Heap.FeltHeap`-pinned. This is the same bundle at key type
`K`, carrying the SAME two anti-laundering fields, and the three anti-ghost theorems are proved ONCE
over it. Every instance inherits them; a `Resid := True` or `Resid := (h₁ ≠ h₂)` bundle cannot be
built, because `resid_refuted` would force a good hash to identify all heaps and `good_inhabited`
says good hashes exist. -/

/-- **`ImtLaneTeeth E sent`** — the anti-ghost teeth of the padded lane-encoded commitment, as a
bundle an instance must EARN. -/
structure ImtLaneTeeth (K : Type) [LinearOrder K] (E : LaneEnc K) (sent : K) where
  /-- The NAMED, per-commitment residual of this encoding's binding. -/
  Resid : (List ℤ → ℤ) → Nat → List (K × ℤ) → List (K × ℤ) → Prop
  /-- ★ THE BINDING, with NO hypothesis on `hash`.

  ⚠ **The two occupancy facts are NAMED BINDERS, not bare arrows, and that is load-bearing.** Since
  `padImtRootE` took its capacity obligation (§3) the commitment is a function OF the occupancy
  proof, so it has to be applied to one — and an `autoParam` elaborating inside this field cannot see
  a hypothesis introduced by `→`: `h₁.length ≤ 2 ^ d → …` puts the fact in the TYPE and out of the
  tactic's reach, which reads as "the bound is missing" when it is merely anonymous. -/
  binds : ∀ (hash : List ℤ → ℤ) (d : Nat) (h₁ h₂ : List (K × ℤ))
      (hz₁ : h₁.length ≤ 2 ^ d) (hz₂ : h₂.length ≤ 2 ^ d),
      padImtRootE E sent hash d h₁ hz₁ = padImtRootE E sent hash d h₂ hz₂ →
        h₁ = h₂ ∨ Resid hash d h₁ h₂
  /-- The hash-level property at which the residual is empty. -/
  Good : (List ℤ → ℤ) → Prop
  /-- ★ ANTI-LAUNDERING #1 — at a GOOD hash the residual is REFUTED. -/
  resid_refuted : ∀ hash, Good hash → ∀ d h₁ h₂, ¬ Resid hash d h₁ h₂
  /-- ★ ANTI-LAUNDERING #2 — GOOD hashes EXIST, so #1 is not vacuous. -/
  good_inhabited : ∃ hash, Good hash

section Teeth

variable {K : Type} [LinearOrder K] {E : LaneEnc K} {sent : K}

/-- **`opensToMerkleE`** — the padded lane-encoded opening: some ADMISSIBLE sparse heap, committed
by the padded depth-`dep` root, reads `o` at `k`. `E.HeapOk` is the landed admissibility (at
`wideEnc`: sorted AND canonically keyed — the L3 closure), plus the sentinel bound the relink
needs. -/
def opensToMerkleE (E : LaneEnc K) (sent : K) (hash : List ℤ → ℤ) (dep : Nat) (r : ℤ) (k : K)
    (o : Option ℤ) : Prop :=
  ∃ m : List (K × ℤ), E.HeapOk m ∧ (∀ x ∈ Heap.keys m, x < sent) ∧ ∃ hz : m.length ≤ 2 ^ dep,
    padImtRootE E sent hash dep m hz = r ∧ Heap.get m k = o

/-- **★ TOOTH 1/3 — OPENINGS ARE FUNCTIONAL, up to the named residual.** Stated over EXPLICIT
witness heaps: the residual is a function of the WITNESSES, so hiding them behind the existential
and writing `… ∨ ∃ residual` would be the free pass this idiom exists to avoid. -/
theorem opensToMerkleE_functional_or_resid (T : ImtLaneTeeth K E sent)
    (hash : List ℤ → ℤ) (d : Nat) {r : ℤ} {k : K} {o₁ o₂ : Option ℤ} {m₁ m₂ : List (K × ℤ)}
    (hz₁ : m₁.length ≤ 2 ^ d) (hr₁ : padImtRootE E sent hash d m₁ hz₁ = r)
      (hg₁ : Heap.get m₁ k = o₁)
    (hz₂ : m₂.length ≤ 2 ^ d) (hr₂ : padImtRootE E sent hash d m₂ hz₂ = r)
      (hg₂ : Heap.get m₂ k = o₂) :
    o₁ = o₂ ∨ T.Resid hash d m₁ m₂ := by
  rcases T.binds hash d m₁ m₂ hz₁ hz₂ (hr₁.trans hr₂.symm) with hm | hc
  · exact Or.inl (by rw [← hg₁, ← hg₂, hm])
  · exact Or.inr hc

/-- **★ TOOTH 2/3 — MEMBERSHIP EXCLUDES NON-MEMBERSHIP.** The tooth that stops a prover claiming
ABSENCE of a key the committed wide tree PRESENTS: the double-spend tooth at 8 felts. -/
theorem opensToMerkleE_some_excludes_none_or_resid (T : ImtLaneTeeth K E sent)
    (hash : List ℤ → ℤ) (d : Nat) {r : ℤ} {k : K} {v : ℤ} {m₁ m₂ : List (K × ℤ)}
    (hz₁ : m₁.length ≤ 2 ^ d) (hr₁ : padImtRootE E sent hash d m₁ hz₁ = r)
      (hg₁ : Heap.get m₁ k = some v)
    (hz₂ : m₂.length ≤ 2 ^ d) (hr₂ : padImtRootE E sent hash d m₂ hz₂ = r)
      (hg₂ : Heap.get m₂ k = none) :
    T.Resid hash d m₁ m₂ := by
  rcases opensToMerkleE_functional_or_resid T hash d hz₁ hr₁ hg₁ hz₂ hr₂ hg₂ with he | hc
  · simp at he
  · exact hc

/-- **`opensToMerkle_functional` at the lane-encoded padded instance**, at a GOOD hash. -/
theorem opensToMerkleE_functional_of_good (T : ImtLaneTeeth K E sent) {hash : List ℤ → ℤ}
    (hgood : T.Good hash) (d : Nat) {r : ℤ} {k : K} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkleE E sent hash d r k o₁) (h₂ : opensToMerkleE E sent hash d r k o₂) :
    o₁ = o₂ := by
  obtain ⟨m₁, _, _, hz₁, hr₁, hg₁⟩ := h₁
  obtain ⟨m₂, _, _, hz₂, hr₂, hg₂⟩ := h₂
  rcases opensToMerkleE_functional_or_resid T hash d hz₁ hr₁ hg₁ hz₂ hr₂ hg₂ with ho | hc
  · exact ho
  · exact absurd hc (T.resid_refuted hash hgood d m₁ m₂)

/-- **`opensToMerkle_some_excludes_none` at the lane-encoded padded instance**, at a GOOD hash. -/
theorem opensToMerkleE_some_excludes_none_of_good (T : ImtLaneTeeth K E sent) {hash : List ℤ → ℤ}
    (hgood : T.Good hash) (d : Nat) {r : ℤ} {k : K} {v : ℤ}
    (h₁ : opensToMerkleE E sent hash d r k (some v))
    (h₂ : opensToMerkleE E sent hash d r k none) : False := by
  have := opensToMerkleE_functional_of_good T hgood d h₁ h₂
  simp at this

end Teeth

/-- **★★ TEETH FOR THE PADDED LANE-ENCODED INSTANCE.** The wide-key twin of stage 2b's
`padImtTeeth`: the padded, arity-`2·width+1`, deployed-shape instance ARRIVES WITH its anti-ghost
theorems instead of assuming them, at every key width including 8 felts. -/
def padImtLaneTeeth {K : Type} [LinearOrder K] (E : LaneEnc K) (sent : K) :
    ImtLaneTeeth K E sent where
  Resid := fun hash d h₁ h₂ =>
    PadGhostE E sent hash h₁ ∨ PadGhostE E sent hash h₂
      ∨ SpongeColl hash (padImtRootFindE E sent hash d h₁ h₂)
  binds := fun hash d _ _ hz₁ hz₂ he =>
    padImtRootE_binds_or_ghost_or_collides E sent hash d hz₁ hz₂ he
  Good := MapGoodE E
  resid_refuted := by
    intro hash hgood d h₁ h₂
    rintro (hg | hg | ⟨hne, he⟩)
    · exact padGhostE_refuted hgood.2 sent h₁ hg
    · exact padGhostE_refuted hgood.2 sent h₂ hg
    · exact hne (hgood.1 he)
  good_inhabited := ⟨oddSponge, mapGoodE_inhabited E⟩

/-- The strength bridge is the teeth bundle's own `Good` field, definitionally — not a fresh
assumption wearing a new name. -/
theorem mapGoodE_is_teeth_good {K : Type} [LinearOrder K] (E : LaneEnc K) (sent : K)
    (hash : List ℤ → ℤ) : MapGoodE E hash ↔ (padImtLaneTeeth E sent).Good hash := Iff.rfl

/-! ## §6 — THE TWO DEPLOYED-SHAPED WIDE ARMS, at the PADDED commitment.

`MapAbsentImtGateWide`'s named residual #1 was "no padding": every law there is stated at
`c.length = 2 ^ dep` with the chain IS the committed vector, which is not the tree
`CanonicalHeapTree::new` builds. These are the same two arms at the SPARSE padded commitment, and
floor-free. The gate bodies are the landed ones with the committed-vector premise replaced by the
padded root of an admissible sparse WIDE heap; the digest-vector layer is untouched. -/

section WideArms

/-- The DEPLOYED wide commitment: `padImtRootE` at `wideEnc`. -/
noncomputable def padImtRoot8 (sent : Digest8Key) (hash : List ℤ → ℤ) (dep : Nat)
    (h : List (Digest8Key × ℤ)) (hFits : h.length ≤ 2 ^ dep := by heap_fits) : ℤ :=
  padImtRootE wideEnc sent hash dep h hFits

/-- The DEPLOYED wide residual, at the arity-17 leaf. -/
noncomputable def OpenResid8 (sent : Digest8Key) (hash : List ℤ → ℤ) (dep : Nat)
    (h : List (Digest8Key × ℤ)) (hFits : h.length ≤ 2 ^ dep) (steps : List (Bool × ℤ))
    (l : ImtLeaf Digest8Key ℤ) : Prop :=
  OpenResidE wideEnc sent hash dep h hFits steps l

/-- **`HeapOk8 sent h`** — the admissible committed WIDE heap: `wideEnc.HeapOk` (sorted AND
canonically keyed — the L3 closure, carried as a definition exactly where `Heap.SortedKeys` already
sat) plus the terminal-sentinel bound the relink needs to be `ImtSorted`. -/
def HeapOk8 (sent : Digest8Key) (h : List (Digest8Key × ℤ)) : Prop :=
  wideEnc.HeapOk h ∧ ∀ x ∈ Heap.keys h, x < sent

/-- **★★ THE WIDE PADDED OPENING LAW — the residual, closed.** `padOpenE_binds_or_resid` at
`wideEnc`: arity-**17** leaf (`imtLeafHash8Of`, the landed wide object by `imtLeafHashE_wide`),
8-felt lex-ordered keys, the deployed sparse zero-padded occupancy, NO hypothesis on `hash`. -/
theorem padOpen8_binds_or_resid (sent : Digest8Key) (hash : List ℤ → ℤ) (dep : Nat)
    {h : List (Digest8Key × ℤ)} {steps : List (Bool × ℤ)} {l : ImtLeaf Digest8Key ℤ}
    (hlen : h.length ≤ 2 ^ dep) (hsl : steps.length = dep)
    (hpath : pathRecompute hash (imtLeafHash8Of hash l) steps = padImtRoot8 sent hash dep h) :
    (pathPos steps < h.length
      ∧ (imtChainOfE sent h)[pathPos steps]? = some l
      ∧ h[pathPos steps]? = some (l.addr, l.value)
      ∧ l.nextAddr = (h[pathPos steps + 1]?).elim sent Prod.fst
      ∧ ∀ l' : ImtLeaf Digest8Key ℤ, pathRecompute hash (imtLeafHash8Of hash l') steps
          = perfectRoot hash dep ((padVecE wideEnc sent hash dep h).set (pathPos steps)
              (imtLeafHash8Of hash l')))
    ∨ OpenResid8 sent hash dep h hlen steps l :=
  padOpenE_binds_or_resid wideEnc sent hash dep hlen hsl hpath

/-- The bracket at the arity-17 low leaf excludes the queried key from the whole committed WIDE
key spine — the pointer-bracket keystone at 8 felts, over the RELINKED chain of a sparse heap. -/
theorem bracket8_excludes (sent : Digest8Key) {h : List (Digest8Key × ℤ)}
    (hok : HeapOk8 sent h) {p : Nat} {l : ImtLeaf Digest8Key ℤ} {k : Digest8Key}
    (hp : (imtChainOfE sent h)[p]? = some l) (hlo : l.addr < k) (hhi : k < l.nextAddr) :
    k ∉ Heap.keys h := by
  have hs : ImtSorted (imtChainOfE sent h) :=
    chainE_imtSorted sent h (wideEnc.heapOk_sorted h hok.1) hok.2
  have hnot : k ∉ imtAddrs (imtChainOfE sent h) :=
    imtAbsent_excludes hs ⟨l, List.mem_of_getElem? hp, hlo, hhi⟩
  rwa [keys_imtChainOfE] at hnot

/-! ### §6a — the deployed wide `.absent` row (op = 2; **24 emitted rows**), PADDED. -/

/-- **`AbsentImtPadGatesAtW`** — `MapAbsentImtGateWide.AbsentImtGatesAtW` at the SPARSE padded
commitment: one low-leaf open at the arity-17 IMT leaf, the POINTER bracket at the full 8-felt lex
order, root preservation. The committed-vector premise is replaced by the padded root of an
ADMISSIBLE sparse wide heap — the tree `CanonicalHeapTree::new` actually builds. -/
def AbsentImtPadGatesAtW (sent : Digest8Key) (hash : List ℤ → ℤ) (dep : Nat)
    (oldRoot newRoot : ℤ) (key lowAddr : Digest8Key) (lowValue : ℤ)
    (lowNext : Digest8Key) : Prop :=
  ∃ (h : List (Digest8Key × ℤ)) (steps : List (Bool × ℤ)),
    HeapOk8 sent h ∧ ∃ hz : h.length ≤ 2 ^ dep,
    padImtRoot8 sent hash dep h hz = oldRoot ∧
    steps.length = dep ∧
    pathRecompute hash (imtLeafHash8Of hash ⟨lowAddr, lowValue, lowNext⟩) steps = oldRoot ∧
    lowAddr < key ∧ key < lowNext ∧
    newRoot = oldRoot

/-- **★ THE WIDE PADDED `.absent` LAW, FLOOR-FREE.** An accepting deployed-shaped wide `.absent`
row over a SPARSE committed tree FORCES the 8-felt key absent from the committed key spine and the
post-root to equal the pre-root — up to the one named residual at THIS row's low leaf. -/
theorem absentImtPadGatesW_force_absence_or_resid (sent : Digest8Key) (hash : List ℤ → ℤ)
    (dep : Nat) {oldRoot newRoot : ℤ} {key lowAddr : Digest8Key} {lowValue : ℤ}
    {lowNext : Digest8Key} {h : List (Digest8Key × ℤ)} {steps : List (Bool × ℤ)}
    (hok : HeapOk8 sent h) (hsz : h.length ≤ 2 ^ dep)
    (hcommit : padImtRoot8 sent hash dep h = oldRoot)
    (hsl : steps.length = dep)
    (hlow : pathRecompute hash (imtLeafHash8Of hash ⟨lowAddr, lowValue, lowNext⟩) steps = oldRoot)
    (hlk : lowAddr < key) (hkn : key < lowNext) (hnr : newRoot = oldRoot) :
    (Heap.get h key = none
      ∧ opensToMerkleE wideEnc sent hash dep oldRoot key none
      ∧ newRoot = oldRoot)
    ∨ OpenResid8 sent hash dep h hsz steps ⟨lowAddr, lowValue, lowNext⟩ := by
  rcases padOpen8_binds_or_resid sent hash dep hsz hsl (by rw [hlow, ← hcommit]) with
    ⟨_, hchain, _, _, _⟩ | hres
  · have hnotin : key ∉ Heap.keys h := bracket8_excludes sent hok hchain hlk hkn
    have hnone : Heap.get h key = none := (Heap.get_eq_none_iff h key).mpr hnotin
    exact Or.inl ⟨hnone, ⟨h, hok.1, hok.2, hsz, hcommit, hnone⟩, hnr⟩
  · exact Or.inr hres

/-- **★ THE SAME LAW AT A GOOD HASH** — the labelled strength bridge. ⚠ `MapGoodE wideEnc` is
`padImtLaneTeeth`'s own `Good` field; the bridge is at an INJECTIVE idealisation, so only the
`_or_resid` half above is a statement about the deployed sponge. -/
theorem absentImtPadRowW_forces_absence_of_good {hash : List ℤ → ℤ}
    (hgood : MapGoodE wideEnc hash) (sent : Digest8Key) (dep : Nat)
    {oldRoot newRoot : ℤ} {key lowAddr : Digest8Key} {lowValue : ℤ} {lowNext : Digest8Key}
    (hg : AbsentImtPadGatesAtW sent hash dep oldRoot newRoot key lowAddr lowValue lowNext) :
    opensToMerkleE wideEnc sent hash dep oldRoot key none ∧ newRoot = oldRoot := by
  obtain ⟨h, steps, hok, hsz, hcommit, hsl, hlow, hlk, hkn, hnr⟩ := hg
  rcases absentImtPadGatesW_force_absence_or_resid sent hash dep hok hsz hcommit hsl hlow
    hlk hkn hnr with hres | hbad
  · exact ⟨hres.2.1, hres.2.2⟩
  · exact absurd hbad (openResidE_refuted hgood sent dep h hsz steps _)

/-! ### §6b — the deployed wide AAFI row (op = 4; **24 emitted rows — the arm that SHIPS**),
PADDED, with the free slot PINNED to the padding constant.

`descriptor_ir2.rs:3514-3516` asserts `s · MAP_FREE_EMPTY[i] = 0` on all eight lanes, pinning the
free slot to `ZERO8` = the padding constant. So the deployed AAFI append lands IN THE PADDING, which
is exactly the occupancy this file models — and the wide gate below pins it, where
`MapOpWideKeyGate.AafiGatesAtW` leaves `freeEmpty` a FREE variable. -/

/-- **`AafiImtPadGatesOnW`** — the deployed op = 4 acceptance for ONE wide row at the PINNED
free-slot digest: (a) low-open at the arity-17 leaf, (b) the 8-felt pointer bracket, (c) PATH1
low-update → `R1`, (d1) PATH2 free slot holds `padDigest` under `R1`, (d2) PATH2 append →
`new_root`. -/
def AafiImtPadGatesOnW (hash : List ℤ → ℤ) (dep : Nat) (steps1 steps2 : List (Bool × ℤ))
    (oldRoot newRoot R1 : ℤ) (key : Digest8Key) (value : ℤ) (lowAddr : Digest8Key)
    (lowValue : ℤ) (lowNext : Digest8Key) : Prop :=
  steps1.length = dep ∧ steps2.length = dep ∧ pathPos steps1 ≠ pathPos steps2 ∧
  pathRecompute hash (imtLeafHash8Of hash ⟨lowAddr, lowValue, lowNext⟩) steps1 = oldRoot ∧
  lowAddr < key ∧ key < lowNext ∧
  pathRecompute hash (imtLeafHash8Of hash ⟨lowAddr, lowValue, key⟩) steps1 = R1 ∧
  pathRecompute hash padDigest steps2 = R1 ∧
  pathRecompute hash (imtLeafHash8Of hash ⟨key, value, lowNext⟩) steps2 = newRoot

/-- The AAFI row: the gates plus the committed sparse WIDE heap behind the PRE-root (which is
`heap_root.rs`'s SORTED `root8`, `insert_witness_aafi:1153`). -/
def AafiImtPadRowAtW (sent : Digest8Key) (hash : List ℤ → ℤ) (dep : Nat)
    (oldRoot newRoot R1 : ℤ) (key : Digest8Key) (value : ℤ) (lowAddr : Digest8Key)
    (lowValue : ℤ) (lowNext : Digest8Key) : Prop :=
  ∃ (h : List (Digest8Key × ℤ)) (steps1 steps2 : List (Bool × ℤ)),
    HeapOk8 sent h ∧ ∃ hz : h.length ≤ 2 ^ dep,
    padImtRoot8 sent hash dep h hz = oldRoot ∧
    AafiImtPadGatesOnW hash dep steps1 steps2 oldRoot newRoot R1 key value lowAddr lowValue lowNext

/-- **★ THE WIDE AAFI OPENER — the double-spend tooth at the DEPLOYED PADDED WIDE commitment,
FLOOR-FREE.** An accepting op = 4 wide row FORCES its 8-felt key ABSENT from the pre-tree: gate (a)
binds the arity-17 low leaf into the relinked chain, gate (b)'s pointer bracket is the `ImtAbsent`
witness, and the chain's `ImtSorted` is DERIVED from admissibility rather than assumed. -/
theorem aafiImtPadGatesW_force_absence_or_resid (sent : Digest8Key) (hash : List ℤ → ℤ) (dep : Nat)
    {oldRoot newRoot R1 : ℤ} {key : Digest8Key} {value : ℤ} {lowAddr : Digest8Key}
    {lowValue : ℤ} {lowNext : Digest8Key}
    {h : List (Digest8Key × ℤ)} {steps1 steps2 : List (Bool × ℤ)}
    (hok : HeapOk8 sent h) (hsz : h.length ≤ 2 ^ dep)
    (hcommit : padImtRoot8 sent hash dep h = oldRoot)
    (hg : AafiImtPadGatesOnW hash dep steps1 steps2 oldRoot newRoot R1 key value lowAddr lowValue
      lowNext) :
    (Heap.get h key = none
      ∧ opensToMerkleE wideEnc sent hash dep oldRoot key none)
    ∨ OpenResid8 sent hash dep h hsz steps1 ⟨lowAddr, lowValue, lowNext⟩ := by
  obtain ⟨hsl1, _, _, hpa, hlk, hkn, _, _, _⟩ := hg
  rcases absentImtPadGatesW_force_absence_or_resid sent hash dep hok hsz hcommit hsl1 hpa
    hlk hkn (rfl : oldRoot = oldRoot) with hres | hbad
  · exact Or.inl ⟨hres.1, hres.2.1⟩
  · exact Or.inr hbad

/-- **★ THE WIDE AAFI ARM AT A GOOD HASH** — the labelled bridge. -/
theorem aafiImtPadRowW_forces_absence_of_good {hash : List ℤ → ℤ}
    (hgood : MapGoodE wideEnc hash) (sent : Digest8Key) (dep : Nat)
    {oldRoot newRoot R1 : ℤ} {key : Digest8Key} {value : ℤ} {lowAddr : Digest8Key}
    {lowValue : ℤ} {lowNext : Digest8Key}
    (hr : AafiImtPadRowAtW sent hash dep oldRoot newRoot R1 key value lowAddr lowValue lowNext) :
    opensToMerkleE wideEnc sent hash dep oldRoot key none := by
  obtain ⟨h, steps1, steps2, hok, hsz, hcommit, hg⟩ := hr
  rcases aafiImtPadGatesW_force_absence_or_resid sent hash dep hok hsz hcommit hg with hres | hbad
  · exact hres.2
  · exact absurd hbad (openResidE_refuted hgood sent dep h hsz steps1 _)

end WideArms

/-! ## §7 — NON-VACUITY, AT `MAP_TREE_DEPTH = 16` OVER A SPARSE WIDE TREE.

A law with no inhabited instance at the deployed depth is the ∃-image mistake this campaign spent
days refuting. Both wide arms get BOTH polarities on the shape `heap_root.rs` actually builds — a
`2^16`-leaf commitment holding ONE live leaf, everything else `EMPTY_SUBTREE_ROOTS`. Nothing here
evaluates a root or a `2^16` object: every root is NAMED as the padded commitment, and every path is
the symbolic `leftPadPath` / `slot1Path` recursion. -/

section Bite8

theorem two_le_two_pow_depth : (2 : Nat) ≤ 2 ^ MAP_TREE_DEPTH := by
  calc (2 : Nat) = 2 ^ 1 := rfl
    _ ≤ 2 ^ MAP_TREE_DEPTH := Nat.pow_le_pow_right (by norm_num) (by decide)

/-- One live leaf fits the deployed depth — the occupancy every one-entry §7 exhibit is indexed by. -/
theorem one_le_two_pow_depth {α : Type} (x : α) : ([x] : List α).length ≤ 2 ^ MAP_TREE_DEPTH :=
  Nat.one_le_pow _ 2 (by norm_num)
/-- …and at a SYMBOLIC depth, for §8's ghost pair. -/
theorem one_le_two_pow_depth' {α : Type} (d : Nat) (x : α) : ([x] : List α).length ≤ 2 ^ d :=
  Nat.one_le_pow _ 2 (by norm_num)

/-- The terminal sentinel of these exhibits, at the 8-felt key. -/
def bite8Sent : Digest8Key := keyHi
/-- ⚑ A SPARSE WIDE tree: ONE live leaf in a `2^16`-leaf commitment. The DENSE wide laws
(`MapAbsentImtGateWide`, stated at `c.length = 2 ^ dep`) have NO witness for such a tree at all. -/
def bite8Heap : List (Digest8Key × ℤ) := [(keyLo, 7)]

theorem bite8Heap_ok : HeapOk8 bite8Sent bite8Heap := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show List.Pairwise (· < ·) [keyLo]
    exact List.Pairwise.cons (by intro b hb; simp at hb) List.Pairwise.nil
  · intro k hk
    have : k ∈ [keyLo] := hk
    rw [List.mem_singleton.mp this]
    exact keyLo_canon
  · intro x hx
    have : x ∈ [keyLo] := hx
    rw [List.mem_singleton.mp this]
    exact keyLo_lt_keyHi

theorem bite8Heap_sz : bite8Heap.length ≤ 2 ^ MAP_TREE_DEPTH := by
  show 1 ≤ 2 ^ MAP_TREE_DEPTH
  exact Nat.one_le_pow _ 2 (by norm_num)

/-- The committed root, NAMED as the padded wide commitment at a NAMED OCCUPANCY PROOF — never
evaluated. ⚠ The occupancy argument is `bite8Heap_sz` and not the `heap_fits` `autoParam`, for the
reason `MapKindImtGates` §8 measured: a root carrying an `autoParam`'s occupancy term has to be
identified with one carrying the term `refine`/`exact` introduced, and with `padImtRoot8` at depth 16
the unifier falls through proof irrelevance to δ — `perfectRoot` over `List.replicate (2^16 - 1)
padDigest`, a `whnf` timeout. Naming the proof hands the denotation the SAME term and every `rfl`
below stays syntactic. -/
noncomputable def bite8Root : ℤ :=
  padImtRoot8 bite8Sent oddSponge MAP_TREE_DEPTH bite8Heap bite8Heap_sz
/-- The deployed membership path of position `0` at depth 16, built symbolically. -/
noncomputable def bite8Steps : List (Bool × ℤ) := leftPadPath oddSponge MAP_TREE_DEPTH

theorem bite8_steps_length : bite8Steps.length = MAP_TREE_DEPTH := leftPadPath_length _ _
theorem bite8_steps_pos : pathPos bite8Steps = 0 := leftPadPath_pos _ _

/-- The one-entry relinked WIDE chain, at the LIST level (cheap `rfl`; nothing folds). -/
theorem bite8_chain_map (a n : Digest8Key) (v : ℤ) :
    (imtChainOfE n [(a, v)]).map (imtLeafHashE oddSponge wideEnc)
      = [imtLeafHash8Of oddSponge ⟨a, v, n⟩] := rfl

/-- The depth-16 leftmost WIDE opening, for ANY arity-17 leaf: the path recomputes to the padded
root of the one-entry wide heap whose terminal pointer is the leaf's. -/
theorem bite8_path_leaf (a n : Digest8Key) (v : ℤ)
    (hz : ([(a, v)] : List (Digest8Key × ℤ)).length ≤ 2 ^ MAP_TREE_DEPTH) :
    pathRecompute oddSponge (imtLeafHash8Of oddSponge ⟨a, v, n⟩) bite8Steps
      = padImtRoot8 n oddSponge MAP_TREE_DEPTH [(a, v)] hz := by
  have hf₀ : ((imtChainOfE n [(a, v)]).map (imtLeafHashE oddSponge wideEnc)).length
      ≤ 2 ^ MAP_TREE_DEPTH := by
    rw [List.length_map, imtChainOfE_length]; exact hz
  have hf₁ : ([imtLeafHash8Of oddSponge ⟨a, v, n⟩] : List ℤ).length ≤ 2 ^ MAP_TREE_DEPTH := by
    show 1 ≤ 2 ^ MAP_TREE_DEPTH
    exact Nat.one_le_pow _ 2 (by norm_num)
  show pathRecompute oddSponge (imtLeafHash8Of oddSponge ⟨a, v, n⟩) bite8Steps
    = perfectRoot oddSponge MAP_TREE_DEPTH
        (padTo MAP_TREE_DEPTH ((imtChainOfE n [(a, v)]).map (imtLeafHashE oddSponge wideEnc)) hf₀)
  rw [padTo_congr (bite8_chain_map a n v) hf₀ hf₁]
  show pathRecompute oddSponge _ (leftPadPath oddSponge MAP_TREE_DEPTH) = _
  exact leftPadPath_recompute _ _ _ hf₁

/-! ### §7a — the wide `.absent` arm FIRES, and its tooth BITES. -/

/-- **★ A REAL ACCEPTING WIDE `.absent` ROW at `MAP_TREE_DEPTH = 16` over a SPARSE tree.** The low
leaf is the single live entry `keyLo`; the queried key is `keyE`, whose bracket `keyLo < keyE` is
decided at felt **7** — the limb the deployed lane-0 projection discards. -/
theorem bite8_absent_row :
    AbsentImtPadGatesAtW bite8Sent oddSponge MAP_TREE_DEPTH bite8Root bite8Root keyE keyLo 7
      bite8Sent :=
  ⟨bite8Heap, bite8Steps, bite8Heap_ok, bite8Heap_sz, rfl, bite8_steps_length,
    bite8_path_leaf keyLo bite8Sent 7 bite8Heap_sz, keyLo_lt_keyE, keyE_lt_keyHi, rfl⟩

/-- **★ THE WIDE `.absent` LAW FIRES** — the row forces a genuine wide non-membership at the padded
sparse commitment, at the deployed depth. -/
theorem bite8_absent_fires :
    opensToMerkleE wideEnc bite8Sent oddSponge MAP_TREE_DEPTH bite8Root keyE none
    ∧ bite8Root = bite8Root :=
  absentImtPadRowW_forces_absence_of_good (mapGoodE_inhabited wideEnc) bite8Sent MAP_TREE_DEPTH
    bite8_absent_row

/-- The sparse wide tree really OPENS at the present key (the discrimination side). -/
theorem bite8_presents :
    opensToMerkleE wideEnc bite8Sent oddSponge MAP_TREE_DEPTH bite8Root keyLo (some 7) :=
  ⟨bite8Heap, bite8Heap_ok.1, bite8Heap_ok.2, bite8Heap_sz, rfl,
    Heap.get_cons_self keyLo 7 []⟩

/-- **★★ THE WIDE `.absent` TOOTH BITES.** No accepting deployed-shaped wide `.absent` row — for
ANY claimed low leaf, ANY claimed pointer and ANY claimed post-root — can prove the PRESENT key
`keyLo` absent from this commitment. A denotation that cannot refuse a ghost refuses nothing. -/
theorem bite8_absent_present_key_refused (newRoot : ℤ) (lowAddr : Digest8Key) (lowValue : ℤ)
    (lowNext : Digest8Key) :
    ¬ AbsentImtPadGatesAtW bite8Sent oddSponge MAP_TREE_DEPTH bite8Root newRoot keyLo lowAddr
        lowValue lowNext := fun hg =>
  opensToMerkleE_some_excludes_none_of_good (padImtLaneTeeth wideEnc bite8Sent)
    (mapGoodE_inhabited wideEnc) MAP_TREE_DEPTH bite8_presents
    (absentImtPadRowW_forces_absence_of_good (mapGoodE_inhabited wideEnc) bite8Sent
      MAP_TREE_DEPTH hg).1

/-! ### §7b — the wide AAFI arm (op = 4, the arm that SHIPS) FIRES into the PADDING. -/

/-- The intermediate root after the low-pointer update: the padded commitment of the SAME one-entry
wide heap with terminal pointer `keyE`. -/
noncomputable def aafi8R1 : ℤ :=
  padImtRoot8 keyE oddSponge MAP_TREE_DEPTH [(keyLo, 7)] bite8Heap_sz
/-- The post-heap's occupancy, NAMED — `aafi8NewRoot` is indexed by it. -/
theorem aafi8Heap_sz : ([(keyLo, 7), (keyE, 2)] : List (Digest8Key × ℤ)).length
    ≤ 2 ^ MAP_TREE_DEPTH := by
  show 1 + 1 ≤ 2 ^ MAP_TREE_DEPTH
  exact two_le_two_pow_depth
noncomputable def aafi8NewRoot : ℤ :=
  padImtRoot8 bite8Sent oddSponge MAP_TREE_DEPTH [(keyLo, 7), (keyE, 2)] aafi8Heap_sz
/-- PATH2 — the free-slot path, at the FIRST PADDING POSITION (`free_index = next_free_index = 1`,
`heap_root.rs:1124`). -/
noncomputable def aafi8Steps2 : List (Bool × ℤ) :=
  slot1Path oddSponge (imtLeafHash8Of oddSponge ⟨keyLo, 7, keyE⟩) MAP_TREE_DEPTH

theorem aafi8_steps2_length : aafi8Steps2.length = MAP_TREE_DEPTH := slot1Path_length _ _ _
theorem aafi8_steps2_pos : pathPos aafi8Steps2 = 1 := slot1Path_pos _ _ _ (by decide)

theorem aafi8_steps2_recompute (x : ℤ) :
    pathRecompute oddSponge x aafi8Steps2
      = perfectRoot oddSponge MAP_TREE_DEPTH
          (padTo MAP_TREE_DEPTH [imtLeafHash8Of oddSponge ⟨keyLo, 7, keyE⟩, x]
            two_le_two_pow_depth) :=
  slot1Path_recompute _ _ MAP_TREE_DEPTH (by decide) x two_le_two_pow_depth

theorem aafi8R1_eq : aafi8R1
    = perfectRoot oddSponge MAP_TREE_DEPTH
        (padTo MAP_TREE_DEPTH [imtLeafHash8Of oddSponge ⟨keyLo, 7, keyE⟩]
          (one_le_two_pow_depth _)) := by
  show padImtRootE wideEnc keyE oddSponge MAP_TREE_DEPTH [(keyLo, 7)]
    (one_le_two_pow_depth (keyLo, (7 : ℤ))) = _
  rw [padImtRootE_unfold,
    padTo_congr (bite8_chain_map keyLo keyE 7) _ (one_le_two_pow_depth _)]

/-- The two-entry relinked WIDE chain, at the LIST level (cheap `rfl`; nothing folds). -/
theorem bite8_chain2 : (imtChainOfE bite8Sent [(keyLo, 7), (keyE, 2)]).map
    (imtLeafHashE oddSponge wideEnc)
      = [imtLeafHash8Of oddSponge ⟨keyLo, 7, keyE⟩,
         imtLeafHash8Of oddSponge ⟨keyE, 2, bite8Sent⟩] := rfl

theorem aafi8NewRoot_eq : aafi8NewRoot
    = perfectRoot oddSponge MAP_TREE_DEPTH (padTo MAP_TREE_DEPTH
        [imtLeafHash8Of oddSponge ⟨keyLo, 7, keyE⟩,
         imtLeafHash8Of oddSponge ⟨keyE, 2, bite8Sent⟩] two_le_two_pow_depth) := by
  show padImtRoot8 bite8Sent oddSponge MAP_TREE_DEPTH [(keyLo, 7), (keyE, 2)] aafi8Heap_sz = _
  rw [padImtRoot8, padImtRootE_unfold, padTo_congr bite8_chain2 _ two_le_two_pow_depth]

theorem cons8_pad_append :
    ([imtLeafHash8Of oddSponge ⟨keyLo, 7, keyE⟩, padDigest] : List ℤ)
      = [imtLeafHash8Of oddSponge ⟨keyLo, 7, keyE⟩] ++ [padDigest] := rfl

/-- **⚑ THE DEPLOYED WIDE AAFI FREE SLOT IS A PADDING CELL.** Gate (d1) pins `MAP_FREE_EMPTY` to
`ZERO8` and opens it at position `1`, which in a one-live-leaf `2^16` commitment holds the padding
constant — so the deployed AAFI append GROWS INTO THE PADDING, at 8-felt keys too. -/
theorem aafi8_free_slot_is_padding
    {f₀ : (([imtLeafHash8Of oddSponge ⟨keyLo, 7, keyE⟩] ++ [padDigest] : List ℤ)).length
      ≤ 2 ^ MAP_TREE_DEPTH}
    {f₁ : ([imtLeafHash8Of oddSponge ⟨keyLo, 7, keyE⟩] : List ℤ).length ≤ 2 ^ MAP_TREE_DEPTH} :
    padTo MAP_TREE_DEPTH ([imtLeafHash8Of oddSponge ⟨keyLo, 7, keyE⟩] ++ [padDigest]) f₀
      = padTo MAP_TREE_DEPTH [imtLeafHash8Of oddSponge ⟨keyLo, 7, keyE⟩] f₁ :=
  padTo_snoc_pad MAP_TREE_DEPTH _
    (by show 1 + 1 ≤ 2 ^ MAP_TREE_DEPTH; exact two_le_two_pow_depth)

/-- **★ A REAL ACCEPTING WIDE AAFI ROW at `MAP_TREE_DEPTH = 16`** — all five gates, over a SPARSE
tree, with the free slot in the padding. Every path obligation closes symbolically. -/
theorem bite8_aafi_row :
    AafiImtPadRowAtW bite8Sent oddSponge MAP_TREE_DEPTH bite8Root aafi8NewRoot aafi8R1 keyE 2
      keyLo 7 bite8Sent := by
  refine ⟨bite8Heap, bite8Steps, aafi8Steps2, bite8Heap_ok, bite8Heap_sz, rfl,
    bite8_steps_length, aafi8_steps2_length, ?_, bite8_path_leaf keyLo bite8Sent 7 bite8Heap_sz,
    keyLo_lt_keyE, keyE_lt_keyHi, bite8_path_leaf keyLo keyE 7 bite8Heap_sz, ?_, ?_⟩
  · rw [bite8_steps_pos, aafi8_steps2_pos]; decide
  · rw [aafi8_steps2_recompute,
      padTo_congr cons8_pad_append two_le_two_pow_depth two_le_two_pow_depth,
      aafi8_free_slot_is_padding, aafi8R1_eq]
  · rw [aafi8_steps2_recompute, aafi8NewRoot_eq]

/-- **★ THE WIDE AAFI LAW FIRES — the double-spend tooth at the deployed padded WIDE commitment.**
An accepting op = 4 wide row forces `keyE` ABSENT from the pre-tree, at the deployed depth. -/
theorem bite8_aafi_absence_fires :
    opensToMerkleE wideEnc bite8Sent oddSponge MAP_TREE_DEPTH bite8Root keyE none :=
  aafiImtPadRowW_forces_absence_of_good (mapGoodE_inhabited wideEnc) bite8Sent MAP_TREE_DEPTH
    bite8_aafi_row

/-- **★★ THE WIDE AAFI TOOTH BITES — a PRESENT key has NO accepting wide AAFI row**, for any
claimed low leaf, any claimed intermediate root and any claimed post-root. -/
theorem bite8_aafi_present_key_refused (newRoot R1 value : ℤ) (lowAddr : Digest8Key)
    (lowValue : ℤ) (lowNext : Digest8Key) :
    ¬ AafiImtPadRowAtW bite8Sent oddSponge MAP_TREE_DEPTH bite8Root newRoot R1 keyLo value
        lowAddr lowValue lowNext := fun hr =>
  opensToMerkleE_some_excludes_none_of_good (padImtLaneTeeth wideEnc bite8Sent)
    (mapGoodE_inhabited wideEnc) MAP_TREE_DEPTH bite8_presents
    (aafiImtPadRowW_forces_absence_of_good (mapGoodE_inhabited wideEnc) bite8Sent MAP_TREE_DEPTH hr)

end Bite8

/-! ## §8 — ⚑⚑ THE TWELFTH IMPOSSIBILITY: WIDENING THE KEY DOES NOT KILL THE PADDING GHOST.

The natural reading of stage 2b's pricing — "~2^31 at this 1-felt commitment, ~2^124 at the deployed
8-felt tree" — is that the kind-D widening buys the padding ghost away. It does not. The widening
moves the KEY from 1 felt to 8; the padding constant is a DIGEST, and the digest is one felt at
every key width. Nor do the epoch's other two hardenings reach it: `wideEnc.HeapOk`'s canonicity
(the L3 closure) is a property of KEYS, and the ghost heaps below are canonically keyed; and
injectivity of the sponge is a property the ghost hash SATISFIES.

So the residual stays exactly what the narrow finding said it was — a FIXED-TARGET PREIMAGE of a
literal constant, repaired only by a DOMAIN-SEPARATED padding digest, which is a deployed-side
change and not a Lean one. -/

section Ghost8

/-- `ghostSpongeAt pre` re-bases `refSponge` so that `pre` lands exactly on the padding constant —
still INJECTIVE, so it satisfies the tower's idealisation, but the padding constant is now in its
leaf-digest image. Stage 2b's witness, reused verbatim at the wide leaf. -/
theorem ghost8_hash_injective (pre : List ℤ) :
    Function.Injective (Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt pre) :=
  Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt_injective pre

/-- The two ghost heaps are both ADMISSIBLE at the WIDE encoding — sorted, canonically keyed (the
L3 closure) and below the sentinel. The hardening does not exclude them. -/
theorem ghost8_heapOk_one : HeapOk8 keyHi [(keyLo, (0 : ℤ))] := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show List.Pairwise (· < ·) [keyLo]
    exact List.Pairwise.cons (by intro b hb; simp at hb) List.Pairwise.nil
  · intro k hk
    have : k ∈ [keyLo] := hk
    rw [List.mem_singleton.mp this]
    exact keyLo_canon
  · intro x hx
    have : x ∈ [keyLo] := hx
    rw [List.mem_singleton.mp this]
    exact keyLo_lt_keyHi

theorem ghost8_heapOk_empty : HeapOk8 keyHi ([] : List (Digest8Key × ℤ)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact List.Pairwise.nil
  · intro k hk; simp [Heap.keys] at hk
  · intro x hx; simp [Heap.keys] at hx

/-- The ghost pair's occupancies, NAMED at a symbolic depth — both roots below are indexed by
these, so nothing in §8 hands `padImtRoot8` an anonymous obligation. -/
theorem ghost8_one_sz (d : Nat) : ([(keyLo, (0 : ℤ))] : List (Digest8Key × ℤ)).length ≤ 2 ^ d :=
  Nat.one_le_pow d 2 (by norm_num)
theorem ghost8_empty_sz (d : Nat) : (([] : List (Digest8Key × ℤ))).length ≤ 2 ^ d := Nat.zero_le _

/-- **⚑⚑ THE GHOST AT THE DEPLOYED WIDE TREE.** At the INJECTIVE hash whose image of the arity-17
low leaf IS the padding constant, the one-entry ADMISSIBLE wide heap `[(keyLo, 0)]` and the EMPTY
one publish the SAME padded arity-17 root at EVERY depth including `MAP_TREE_DEPTH = 16`, while
disagreeing at `keyLo`: one PRESENTS it, the other reports it ABSENT. -/
theorem padded_imt8_ghost (d : Nat) :
    Function.Injective (Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt
        (imtLeafPreE wideEnc ⟨keyLo, 0, keyHi⟩))
    ∧ HeapOk8 keyHi [(keyLo, (0 : ℤ))]
    ∧ HeapOk8 keyHi ([] : List (Digest8Key × ℤ))
    ∧ padImtRoot8 keyHi (Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt
          (imtLeafPreE wideEnc ⟨keyLo, 0, keyHi⟩)) d [(keyLo, (0 : ℤ))] (ghost8_one_sz d)
        = padImtRoot8 keyHi (Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt
            (imtLeafPreE wideEnc ⟨keyLo, 0, keyHi⟩)) d [] (ghost8_empty_sz d)
    ∧ Heap.get [(keyLo, (0 : ℤ))] keyLo = some 0
    ∧ Heap.get ([] : List (Digest8Key × ℤ)) keyLo = none := by
  refine ⟨ghost8_hash_injective _, ghost8_heapOk_one, ghost8_heapOk_empty, ?_,
    Heap.get_cons_self keyLo 0 [], rfl⟩
  have hleaf : imtLeafHashE (Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt
      (imtLeafPreE wideEnc ⟨keyLo, 0, keyHi⟩)) wideEnc
        (⟨keyLo, 0, keyHi⟩ : ImtLeaf Digest8Key ℤ) = padDigest :=
    Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt_hit _
  have hmap : (imtChainOfE keyHi [(keyLo, (0 : ℤ))]).map
      (imtLeafHashE (Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt
        (imtLeafPreE wideEnc ⟨keyLo, 0, keyHi⟩)) wideEnc) = [padDigest] := by
    show [imtLeafHashE (Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt
        (imtLeafPreE wideEnc ⟨keyLo, 0, keyHi⟩)) wideEnc
          (⟨keyLo, 0, keyHi⟩ : ImtLeaf Digest8Key ℤ)] = [padDigest]
    rw [hleaf]
  have hnilmap : (imtChainOfE keyHi ([] : List (Digest8Key × ℤ))).map
      (imtLeafHashE (Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt
        (imtLeafPreE wideEnc ⟨keyLo, 0, keyHi⟩)) wideEnc) = ([] : List ℤ) := rfl
  show perfectRoot _ d (padTo d ((imtChainOfE keyHi [(keyLo, (0 : ℤ))]).map
        (imtLeafHashE _ wideEnc)) _)
    = perfectRoot _ d (padTo d ((imtChainOfE keyHi ([] : List (Digest8Key × ℤ))).map
        (imtLeafHashE _ wideEnc)) _)
  rw [padTo_congr hmap _ (one_le_two_pow_depth' d padDigest),
    padTo_congr hnilmap _ (Nat.zero_le _),
    Dregg2.Circuit.MapPaddedDenotation.padTo_singleton_pad]

/-- **⚑⚑ PADDED INJECTIVITY IS REFUTED AT 8-FELT LANES, AT THE DEPLOYED DEPTH.** There is NO
theorem "the padded arity-17 root is injective on admissible sparse WIDE heaps", not even under the
tower's injectivity idealisation — which is `Poseidon2SpongeCR` definitionally. So the widening
epoch inherits the residual verbatim, and the `_or_resid` idiom above is not optional at 8 felts
either. (Anti-floor content: the conclusion is `False`.) -/
theorem padded_imt8_injectivity_is_refuted :
    ¬ (∀ (hash : List ℤ → ℤ), Function.Injective hash →
        ∀ h₁ h₂ : List (Digest8Key × ℤ), HeapOk8 keyHi h₁ → HeapOk8 keyHi h₂ →
        ∀ (hz₁ : h₁.length ≤ 2 ^ MAP_TREE_DEPTH) (hz₂ : h₂.length ≤ 2 ^ MAP_TREE_DEPTH),
        padImtRoot8 keyHi hash MAP_TREE_DEPTH h₁ hz₁
          = padImtRoot8 keyHi hash MAP_TREE_DEPTH h₂ hz₂ →
        h₁ = h₂) := by
  intro hbad
  obtain ⟨hinj, ho₁, ho₂, hroot, _, _⟩ := padded_imt8_ghost MAP_TREE_DEPTH
  exact absurd (hbad _ hinj _ _ ho₁ ho₂ _ _ hroot) (by simp)

/-- **⚑⚑ THE TWELFTH IMPOSSIBILITY, PACKAGED.** All three of the wide epoch's hardenings hold
SIMULTANEOUSLY on the ghost pair — an 8-felt key space, `wideEnc`-admissible (sorted AND
CANONICALLY KEYED) committed heaps, and a genuinely INJECTIVE sponge — and the padding ghost
survives all three at `MAP_TREE_DEPTH = 16`. Widening the key is not a repair for it; only a
domain-separated padding digest is. -/
theorem wide_hardenings_do_not_kill_the_ghost :
    (∃ hash : List ℤ → ℤ, Function.Injective hash
      ∧ ∃ h₁ h₂ : List (Digest8Key × ℤ),
          HeapOk8 keyHi h₁ ∧ HeapOk8 keyHi h₂
          ∧ ∃ (hz₁ : h₁.length ≤ 2 ^ MAP_TREE_DEPTH) (hz₂ : h₂.length ≤ 2 ^ MAP_TREE_DEPTH),
            padImtRoot8 keyHi hash MAP_TREE_DEPTH h₁ hz₁
              = padImtRoot8 keyHi hash MAP_TREE_DEPTH h₂ hz₂
          ∧ h₁ ≠ h₂
          ∧ Heap.get h₁ keyLo ≠ Heap.get h₂ keyLo)
    ∧ ¬ (∀ (hash : List ℤ → ℤ), Function.Injective hash →
        ∀ h₁ h₂ : List (Digest8Key × ℤ), HeapOk8 keyHi h₁ → HeapOk8 keyHi h₂ →
        ∀ (hz₁ : h₁.length ≤ 2 ^ MAP_TREE_DEPTH) (hz₂ : h₂.length ≤ 2 ^ MAP_TREE_DEPTH),
        padImtRoot8 keyHi hash MAP_TREE_DEPTH h₁ hz₁
          = padImtRoot8 keyHi hash MAP_TREE_DEPTH h₂ hz₂ →
        h₁ = h₂) := by
  obtain ⟨hinj, ho₁, ho₂, hroot, hg₁, hg₂⟩ := padded_imt8_ghost MAP_TREE_DEPTH
  refine ⟨⟨_, hinj, _, _, ho₁, ho₂, _, _, hroot, by simp, ?_⟩,
    padded_imt8_injectivity_is_refuted⟩
  rw [hg₁, hg₂]
  simp

/-- **★ THE GHOST PAIR IS EXACTLY THE NAMED RESIDUAL, not an unnamed escape.** Fed to the wide
teeth, the ghost heaps do not yield `False` — they yield `PadGhostE` at the entry whose arity-17
leaf digest IS the padding constant. The residual is REACHED by the attack it prices. -/
theorem ghost8_pair_is_the_named_resid (d : Nat) :
    (padImtLaneTeeth wideEnc keyHi).Resid
      (Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt
        (imtLeafPreE wideEnc ⟨keyLo, 0, keyHi⟩)) d [(keyLo, (0 : ℤ))] [] := by
  refine Or.inl ?_
  show PadHit ((imtChainOfE keyHi [(keyLo, (0 : ℤ))]).map (imtLeafHashE _ wideEnc))
  have hleaf : imtLeafHashE (Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt
      (imtLeafPreE wideEnc ⟨keyLo, 0, keyHi⟩)) wideEnc
        (⟨keyLo, 0, keyHi⟩ : ImtLeaf Digest8Key ℤ) = padDigest :=
    Dregg2.Circuit.MapPaddedDenotation.ghostSpongeAt_hit _
  show PadHit [imtLeafHashE _ wideEnc (⟨keyLo, 0, keyHi⟩ : ImtLeaf Digest8Key ℤ)]
  rw [hleaf]
  exact Dregg2.Circuit.MapPaddedDenotation.padHit_singleton

end Ghost8

/-! ## §9 — AXIOM HYGIENE. -/

#assert_axioms imtLeafPreE_length
#assert_axioms imtLeafHashE_narrow
#assert_axioms imtLeafHashE_wide
#assert_axioms imtLeafPreE_wide_arity
#assert_axioms imtLeafPreE_inj
#assert_axioms imtLeafHashE_binds_or_collides
#assert_axioms imtChainOfE_cons
#assert_axioms imtChainOfE_length
#assert_axioms imtToHeapW_imtChainOfE
#assert_axioms imtChainOfE_injective
#assert_axioms keys_imtChainOfE
#assert_axioms imtChainOfE_getElem?
#assert_axioms imtChainOfE_narrow
#assert_axioms chainE_imtSorted
#assert_axioms padVecE_length
#assert_axioms padImtRootE_narrow
#assert_axioms padGhostE_refuted
#assert_axioms padFreeE_oddSponge
#assert_axioms imtLeafFindE_spec
#assert_axioms padImtRootE_binds_or_ghost_or_collides
#assert_axioms mapGoodE_inhabited
#assert_axioms openResidE_refuted
#assert_axioms padOpenE_binds_or_resid
#assert_axioms opensToMerkleE_functional_or_resid
#assert_axioms opensToMerkleE_some_excludes_none_or_resid
#assert_axioms opensToMerkleE_functional_of_good
#assert_axioms opensToMerkleE_some_excludes_none_of_good
#assert_axioms mapGoodE_is_teeth_good
#assert_axioms padOpen8_binds_or_resid
#assert_axioms bracket8_excludes
#assert_axioms absentImtPadGatesW_force_absence_or_resid
#assert_axioms absentImtPadRowW_forces_absence_of_good
#assert_axioms aafiImtPadGatesW_force_absence_or_resid
#assert_axioms aafiImtPadRowW_forces_absence_of_good
#assert_axioms bite8Heap_ok
#assert_axioms bite8_path_leaf
#assert_axioms bite8_absent_row
#assert_axioms bite8_absent_fires
#assert_axioms bite8_presents
#assert_axioms bite8_absent_present_key_refused
#assert_axioms bite8_aafi_row
#assert_axioms bite8_aafi_absence_fires
#assert_axioms bite8_aafi_present_key_refused
#assert_axioms padded_imt8_ghost
#assert_axioms padded_imt8_injectivity_is_refuted
#assert_axioms wide_hardenings_do_not_kill_the_ghost
#assert_axioms ghost8_pair_is_the_named_resid

end Dregg2.Circuit.MapWideImtPadOpen
