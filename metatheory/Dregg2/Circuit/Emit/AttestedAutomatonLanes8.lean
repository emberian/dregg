/-
# Dregg2.Circuit.Emit.AttestedAutomatonLanes8 — the weld's DENOTATION, routed through all eight lanes.

`AttestedAutomatonWeld8` carries the attestation root as EIGHT columns, pins all eight to public
inputs and threads all eight by constancy windows — and then records, honestly, that the shared IR
denotation `DescriptorIR2.MapOp.holdsAt` reads `(m.root 0)` ONLY, so the descriptor's per-row
OPENING is still the one-felt scalar `opensTo hash (lane 0)` (~2^15.5 to collide) and lanes 1..7 are
pinned, threaded and CONTENT-UNFORCED. `weld_completion_lanes_free` exhibits that.

This file is the denotation half. It does NOT edit the shared `DescriptorIR2` (every `.mapOp`
consumer in the tree — 43 files — rides `MapOp.holdsAt`; moving it is a whole-tree flag day and is
named below as the follow-up). Instead it defines, for ANY v2 descriptor, the row denotation in
which the `.mapOp` arm opens the FULL 8-felt root group under the 8-felt `node8`/`heapLeafDigest8`
fold (`MapMerkleRoot.opensToMerkle8` / `writesToMerkle8` over a `Heap8Scheme`), the 19-felt map-log
row `[root8, key, value, op, new_root8]` the deployed table actually carries
(`circuit/src/descriptor_ir2.rs`), and the satisfaction structure `Satisfied2Lanes8` that is
`Satisfied2Public` with exactly those two legs swapped. Everything else is `Satisfied2Public`'s
field, verbatim.

## What is proved here

  * **§1 the denotation.** `MapOp.holdsAt8 S8 env m`, `MapOp.rowAt8`, `mapLog8`,
    `VmConstraint2.holdsAt8`, `Satisfied2Lanes8`. A descriptor's meaning under the 8-lane reading.
  * **§2 the witness (the gate).** `weldWit8_satisfies`: the welded descriptor has a real
    `Satisfied2Lanes8` witness at ANY root group that commits the automaton at the 8-felt width
    (`CommitsAutomaton8 S8 R8 d`), and `autoRoot8_opens` constructs one, so
    `weldWit8_satisfies_constructed` needs no hypothesis about any hash. Every non-map leg is
    `AttestedAutomatonWeld8.weldWit_rowConstraints_nonmap` / `weldWit_rowRanges`, reused, not
    re-proved.
  * **§3 extraction.** `lanes8_row_opens`: every row of a Lanes8-satisfying welded trace opens its
    edge `(2·current + symbol ↦ next)` at the row's OWN 8-felt root group. `lanes8_root_public`:
    the row's group is the PUBLIC root group, lane by lane, modulo the BabyBear prime (the window
    gates and public pins are congruences); `lanes8_root_eq_public` upgrades that to equality at
    canonical felt values.
  * **§4 the binding theorem for the full 8-felt digest.**
    `weld8_forged_edge_refused`: a Lanes8-satisfying trace whose public root group commits `d`
    (`CommitsAutomaton8By S8 m R8 d`) and which claims a step `next ≠ d.step s y` must have supplied,
    for that row, a 2^16-leaf heap behind the SAME 8-felt root that reads the forged value — and
    `MapRootColl S8 MAP_TREE_DEPTH m_row m` names the collision of the chip absorb `chipAbsorb8`
    (at a node block of arity 16 or a leaf block of arity 3, whichever `mapRoot8Find` resolves)
    between that heap and the committing one. No `Compress8CR`/`Poseidon2SpongeCR` hypothesis; the collision disjunct is
    the named-pair form `MapMerkleRoot` §5b exports, and `weld_collision_disjunct_refutable` says
    it is refutable, not a pigeonhole free pass. `weld8_accepted_run_is_committed_run` is the
    positive polarity: every accepted row IS an edge of the committed automaton, or the named pair
    collides.
  * **§5 the vacuity falsifier — `weld_completion_lanes_free` FLIPS.** At the toy chip
    `constChip` (every absorb is the zero digest) every 2^16-leaf heap root is `zeroDigest8`, so
    `lanes8_forces_root_at_constChip` forces every row's group to zero and
    `weld_completion_lanes_not_free` refutes "any completion lanes satisfy the welded descriptor"
    under `Satisfied2Lanes8` — while `AttestedAutomatonWeld8.weld_completion_lanes_free` still
    proves it under the scalar `Satisfied2Public`. The two theorems together are the exhibited
    SEPARATION between the lane-0 denotation and this one. (A constant chip is a legitimate
    `Heap8Scheme`: the structure carries no injectivity field, by design — `MapMerkleRoot` §5b.)

## What is NOT claimed (and what codex round 1 added — `docs/automata/codex-synthesis.md` §1)

  * **The occupancy model is the DENSE one.** `opensToMerkle8` demands a `2^16`-leaf sorted heap
    (`MapMerkleRoot` §5b: "`mapRoot8` is the DENSE form"); the deployed builder's root is the
    sentinel-headed, zero-padded `padImtRoot8` (`WholeImageFoldRealization`). For the attested
    automaton the two coincide in content because `autoHeapW d` is TOTAL over the `2^16` keys, but
    `Satisfied2Lanes8` is "the weld under the dense 8-felt model", not "the deployed verifier".
    Re-basing onto `padImtRoot8` is a follow-up that touches `writesToMerkle8` (which also demands
    full-sized post-heaps) and is not attempted here.
  * **The row heaps are existential.** `weld8_forged_edge_refused` names the colliding pair at the
    heap the row's opening supplies, but that heap lives inside `opensToMerkle8`'s existential; an
    EXECUTABLE extractor needs `Satisfied2Lanes8` to carry the heaps as data (explicit `M i` per row).
    Until then the right disjunct of `weld8_accepted_run_is_committed_run` can also be taken by an
    honest row that happens to have a root-colliding sibling heap (change an unqueried value at a
    chip that reduces mod `p`): the OR is true, not exclusive. The content is
    `weld8_forged_edge_refused`: a forged step FORCES the named collision.
  * **Whole-run statements are not here.** The theorems are per row; `d.start`/`d.accepts` are
    pinned by `attB1`/`attB2` on the witness side only. The chaining corollary (an accepted trace
    is `classifyFrom d q w` of its symbol column, or a named collision) is the next theorem.
  * The shared IR's `MapOp.holdsAt` still reads lane 0. The `Satisfied2` family and every
    `AlgoStarkSound*` conclusion in the tree still denote map ops at one felt. The named follow-up:
    replace the `.mapOp` arm of `VmConstraint2.holdsAt` by `MapOp.holdsAt8` and
    `Satisfied2.mapTableFaithful` by `mapLog8`, after which `Satisfied2Lanes8` is definitionally
    `Satisfied2Public` and this file collapses to §3–§5.
  * `Satisfied2Lanes8` is a MODEL of the deployed verifier's acceptance, exactly as
    `Satisfied2Public` is. The deployed Rust map-ops AIR forces all eight lanes of a map op's root
    group already [READ by the routing lane: parse 8+8 `descriptor_ir2.rs:1815-1840`, the 19-felt log
    `:4410-4425`, node8 chip queries on loc 0..7 / 11..18 in `dregg-ir2-map-ops-v1.json`
    interactions 33/34, PI pins `:4103-4109`]; the lane-0 gap was this Lean denotation. BUT the
    deployed v2 assembly refuses `weldDesc` outright as non-graduated (`ranges` carrier non-empty,
    `descriptor_ir2.rs:2315`), so the descriptor is routed by name and NOT served; see the Weld8
    header for the graduation follow-up.
  * `lanes8_root_eq_public` needs `LaneCanonical`: cells in `[0, p)`. Over BabyBear every cell is,
    by type; in this ℤ-valued model it is a hypothesis, and the constructed witness meets it
    whenever its root group does.

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound} on every theorem (§6). NEW file;
imports read-only except `AttestedAutomatonWeld8` (two hash-free lemmas factored out of its
witness proof, nothing deleted). -/
import Dregg2.Circuit.Emit.AttestedAutomatonWeld8

namespace Dregg2.Circuit.Emit.AttestedAutomatonLanes8

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv VmRange siteHoldsAll)
open Dregg2.Crypto
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Substrate
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.MapMerkleRoot
  (mapRoot8 opensToMerkle8 writesToMerkle8 MapRootColl zeroDigest8 perfectRoot8 foldLevel8
   foldLevel8_length_half linkHeap linkHeap_length opensToMerkle8_functional_or_collides)
open Dregg2.Circuit.DeployedHeapTree.Heap8Scheme (heapLeafDigest8 heapNodeOf8)
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa classifyFrom)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
  (CURRENT SYMBOL NEXT PI_INITIAL PI_FINAL envAt_loc envAt_nxt)
open Dregg2.Circuit.Emit.AttestedAutomatonEmit (ASYM ASTATES keyOf)
open Dregg2.Circuit.Emit.AttestedAutomatonWeld8

set_option autoImplicit false

/-! ## §1 — THE 8-LANE DENOTATION of a map op, for any v2 descriptor. -/

/-- The pre-root GROUP a map op evaluates on a row: all eight lanes. -/
def _root_.Dregg2.Circuit.DescriptorIR2.MapOp.rootAt (a : Assignment) (m : MapOp) : Digest8 := fun l => (m.root l).eval a

/-- The post-root GROUP a map op evaluates on a row: all eight lanes. -/
def _root_.Dregg2.Circuit.DescriptorIR2.MapOp.newRootAt (a : Assignment) (m : MapOp) : Digest8 := fun l => (m.newRoot l).eval a

/-- **`MapOp.holdsAt8 S8 env m`** — the map-op's per-row denotation at the DEPLOYED width: when the
guard fires, the evaluated `(root group, key, value, new-root group)` is a genuine opening of the
8-felt `node8` tree per the op kind. The lane-complete twin of `DescriptorIR2.MapOp.holdsAt`, which
reads `(m.root 0)` only. -/
def _root_.Dregg2.Circuit.DescriptorIR2.MapOp.holdsAt8 (S8 : Heap8Scheme) (env : VmRowEnv) (m : MapOp) : Prop :=
  m.guard.eval env.loc = 1 →
    match m.op with
    | .read   => opensToMerkle8 S8 MAP_TREE_DEPTH (m.rootAt env.loc) (m.key.eval env.loc)
                   (some (m.value.eval env.loc))
                 ∧ m.newRootAt env.loc = m.rootAt env.loc
    | .absent => opensToMerkle8 S8 MAP_TREE_DEPTH (m.rootAt env.loc) (m.key.eval env.loc) none
                 ∧ m.newRootAt env.loc = m.rootAt env.loc
    | .write | .insert | .aafiInsert =>
                 writesToMerkle8 S8 MAP_TREE_DEPTH (m.rootAt env.loc) (m.key.eval env.loc)
                   (m.value.eval env.loc) (m.newRootAt env.loc)

/-- The DEPLOYED 19-felt map-ops table row `[root8, key, value, op, new_root8]`
(`circuit/src/descriptor_ir2.rs`), against the model's 5-felt `MapOp.rowAt`. -/
def _root_.Dregg2.Circuit.DescriptorIR2.MapOp.rowAt8 (a : Assignment) (m : MapOp) : List ℤ :=
  List.ofFn (m.rootAt a) ++ [m.key.eval a, m.value.eval a, m.op.code] ++ List.ofFn (m.newRootAt a)

theorem MapOp.rowAt8_length (a : Assignment) (m : MapOp) : (m.rowAt8 a).length = 19 := by
  simp [Dregg2.Circuit.DescriptorIR2.MapOp.rowAt8]

/-- The gathered 19-felt map-ops log, in trace order. -/
def mapLog8 (d : EffectVmDescriptor2) (t : VmTrace) : Table :=
  t.rows.flatMap fun a =>
    (mapOpsOf d).filterMap fun m =>
      if m.guard.eval a = 1 then some (m.rowAt8 a) else none

/-- Per-row meaning of one v2 constraint with the `.mapOp` arm at eight lanes; every other arm is
`VmConstraint2.holdsAt`, verbatim. -/
def _root_.Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt8 (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (tf : TraceFamily)
    (env : VmRowEnv) (isFirst isLast : Bool) : VmConstraint2 → Prop
  | .mapOp m => m.holdsAt8 S8 env
  | c => c.holdsAt hash tf env isFirst isLast

theorem VmConstraint2.holdsAt8_of_not_mapOp (S8 : Heap8Scheme) (hash : List ℤ → ℤ)
    (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool) (c : VmConstraint2)
    (hne : ∀ m, c ≠ .mapOp m) (h : c.holdsAt hash tf env isFirst isLast) :
    c.holdsAt8 S8 hash tf env isFirst isLast := by
  cases c with
  | mapOp m => exact absurd rfl (hne m)
  | _ => exact h

theorem VmConstraint2.holdsAt8_mapOp (S8 : Heap8Scheme) (hash : List ℤ → ℤ)
    (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool) (m : MapOp)
    (h : (VmConstraint2.mapOp m).holdsAt8 S8 hash tf env isFirst isLast) : m.holdsAt8 S8 env := h

/-- **`Satisfied2Lanes8 S8 hash d minit mfin maddrs t`** — `Satisfied2Public` with its two map legs
at the deployed width: the `.mapOp` row arm is `MapOp.holdsAt8`, and the map-ops table carries the
19-felt `mapLog8`. Every other field is `Satisfied2`'s / `Satisfied2Public`'s, verbatim. -/
structure Satisfied2Lanes8 (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) : Prop where
  rowConstraints : ∀ i < t.rows.length, ∀ c ∈ d.constraints,
    c.holdsAt8 S8 hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)
  rowHashes : ∀ i < t.rows.length, siteHoldsAll hash (envAt t i) d.hashSites
  rowRanges : ∀ i < t.rows.length, ∀ r ∈ d.ranges, r.holds (envAt t i)
  memAddrsNodup : maddrs.Nodup
  memClosed : ∀ op ∈ memLog d t, op.addr ∈ maddrs
  memDisciplined : MemoryChecking.Disciplined (memLog d t)
  memBalanced : MemoryChecking.MemCheck minit mfin maddrs (memLog d t)
  memTableFaithful : t.tf .memory = (memLog d t).map opRow
  mapTableFaithful8 : t.tf .mapOps = mapLog8 d t
  publicTablesFaithful : PublicTablesFaithful d t
  publicLookupBalanced : PublicLookupBalanced d t

/-! ## §2 — THE WITNESS: the welded descriptor under the 8-lane denotation. -/

/-- The welded map op (the single `.mapOp` of `weldDesc`), as a `MapOp`. -/
def weldOp : MapOp :=
  { guard   := .const 1
  , root    := weldRootGroup
  , key     := .add (.mul (.const 2) (.var CURRENT)) (.var SYMBOL)
  , value   := .var NEXT
  , newRoot := weldRootGroup
  , op      := .read }

theorem weldTransitionOpen_eq : weldTransitionOpen = .mapOp weldOp := rfl

/-- The 19-felt map row of a welded trace row. -/
def weldMapRow8 (a : Assignment) : List ℤ := weldOp.rowAt8 a

/-- The witness's table family at the deployed width: the 19-felt map-ops log at `.mapOps`, the two
range tables of the graduated weld at their ids, empty elsewhere. -/
def attTf8 (rows : List Assignment) : TraceFamily :=
  fun id => if id = TableId.mapOps then rows.map weldMapRow8
    else if id = WELD_TID_RANGE15 then rangeRows 15
    else if id = WELD_TID_RANGE1 then rangeRows 1 else []

theorem attTf8_faithful (rows : List Assignment) : WeldRangeTablesFaithful (attTf8 rows) :=
  ⟨rfl, rfl⟩

/-- **THE WELDED WITNESS AT THE DEPLOYED WIDTH**: the same rows and public inputs as
`AttestedAutomatonWeld8.weldWit`, with the 19-felt map table. -/
def weldWit8 (d : TableDfa Nat Nat) (R8 : Digest8) (q : Nat) (w : List Nat) : VmTrace :=
  { rows := rowsW d R8 q w
  , pub  := weldPub q (classifyFrom d q w) R8
  , tf   := attTf8 (rowsW d R8 q w) }

theorem weldWit8_rows (d : TableDfa Nat Nat) (R8 : Digest8) (q : Nat) (w : List Nat) :
    (weldWit8 d R8 q w).rows = (weldWit d R8 q w).rows := rfl

/-- The two witnesses see the SAME row environment at every row (rows, public inputs and
challenges agree; only the table family differs). -/
theorem envAt_weldWit8 (d : TableDfa Nat Nat) (R8 : Digest8) (q : Nat) (w : List Nat) (i : Nat) :
    envAt (weldWit8 d R8 q w) i = envAt (weldWit d R8 q w) i := rfl

theorem weld_mapLog8 (name : String) (t : VmTrace) :
    mapLog8 (weldDesc name) t = t.rows.map weldMapRow8 := by
  show t.rows.flatMap _ = _
  simp only [weld_mapOps]
  induction t.rows with
  | nil => rfl
  | cons a rest ih => rw [List.flatMap_cons, ih]; rfl

/-- The welded map op's row denotation at eight lanes, on a row of the welded witness: the row's
group IS `R8`, and `R8` opens the edge. -/
theorem weldOp_holdsAt8 (S8 : Heap8Scheme) (d : TableDfa Nat Nat) (R8 : Digest8)
    (h8 : CommitsAutomaton8 S8 R8 d)
    (hstep : ∀ s y, d.step s y < ASTATES) (q : Nat) (hq : q < ASTATES)
    (w : List Nat) (hsym : ∀ y ∈ w, y < ASYM)
    (i : Nat) (hi : i < (weldWit8 d R8 q w).rows.length) :
    weldOp.holdsAt8 S8 (envAt (weldWit8 d R8 q w) i) := by
  have hi' : i < (rowsW d R8 q w).length := hi
  have hloc : (envAt (weldWit8 d R8 q w) i).loc = (rowsW d R8 q w)[i]'hi' :=
    envAt_loc (t := weldWit d R8 q w) hi
  obtain ⟨s, y, hs, hy, hrow⟩ := rowsW_shape d hstep R8 w q hq hsym i hi'
  show ((1 : ℤ) = 1 → _)
  intro _
  rw [hloc, hrow]
  have hgroup : weldOp.rootAt (asgW s y (d.step s y) R8) = R8 := by
    funext l
    exact asgW_root s y (d.step s y) R8 l
  constructor
  · show opensToMerkle8 S8 MAP_TREE_DEPTH (weldOp.rootAt (asgW s y (d.step s y) R8))
      (2 * Int.ofNat s + Int.ofNat y) (some (Int.ofNat (d.step s y)))
    rw [hgroup]
    have hkey : (2 : ℤ) * Int.ofNat s + Int.ofNat y = ((keyOf s y : Nat) : ℤ) := by
      simp only [keyOf, Int.ofNat_eq_natCast]
      push_cast
      ring
    rw [hkey]
    exact h8 s y hs hy
  · rfl

/-- ⚑ **THE GATE — a real `Satisfied2Lanes8` witness for the welded descriptor**, at ANY root group
that commits the automaton at the 8-felt width. General in the automaton, the start state, the
word, the descriptor name, and in ALL EIGHT lanes. -/
theorem weldWit8_satisfies (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (d : TableDfa Nat Nat)
    (R8 : Digest8) (h8 : CommitsAutomaton8 S8 R8 d)
    (hstep : ∀ s y, d.step s y < ASTATES) (q : Nat) (hq : q < ASTATES)
    (w : List Nat) (hw : w ≠ []) (hsym : ∀ y ∈ w, y < ASYM) (name : String) :
    Satisfied2Lanes8 S8 hash (weldDesc name)
      (fun _ => 0) (fun _ => (0, 0)) [] (weldWit8 d R8 q w) where
  rowConstraints := by
    intro i hi c hc
    by_cases hne : c = weldTransitionOpen
    · subst hne
      exact weldOp_holdsAt8 S8 d R8 h8 hstep q hq w hsym i hi
    · refine VmConstraint2.holdsAt8_of_not_mapOp S8 hash _ _ _ _ c ?_ ?_
      · intro m hm
        subst hm
        -- the only `.mapOp` of `weldDesc` is `weldTransitionOpen`
        simp only [weldDesc, List.mem_cons] at hc
        rcases hc with h | h | h | h | h
        · exact hne h
        · exact VmConstraint2.noConfusion h
        · exact VmConstraint2.noConfusion h
        · exact VmConstraint2.noConfusion h
        · rcases weldTail_classify h with ⟨l, hl | hl⟩ | hl | hl
          · exact VmConstraint2.noConfusion hl
          · exact VmConstraint2.noConfusion hl
          · exact VmConstraint2.noConfusion hl
          · exact VmConstraint2.noConfusion hl
      · rw [envAt_weldWit8]
        exact weldWit_rowConstraints_nonmap hash _ (attTf8_faithful _) d R8 hstep q hq w hw hsym
          name i hi c hc hne
  rowHashes := by intro i _; trivial
  rowRanges := fun _ _ r hr => absurd hr (by rw [weld_ranges]; exact List.not_mem_nil)
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [weld_memLog]; simp
  memDisciplined := by rw [weld_memLog]; trivial
  memBalanced := by rw [weld_memLog]; exact memCheck_nil _ _
  memTableFaithful := by rw [weld_memLog]; rfl
  mapTableFaithful8 := by rw [weld_mapLog8]; rfl
  publicTablesFaithful := by
    intro td htd
    simp only [weldDesc, List.mem_cons, List.not_mem_nil, or_false] at htd
    rcases htd with rfl | rfl | rfl <;> trivial
  publicLookupBalanced := by
    intro td htd
    simp only [weldDesc, List.mem_cons, List.not_mem_nil, or_false] at htd
    rcases htd with rfl | rfl | rfl <;> trivial

/-- ⚑ **THE GATE, FIRED UNCONDITIONALLY**: `autoRoot8 S8 d` commits `d` at eight felts
(`autoRoot8_opens`), so the welded descriptor has a `Satisfied2Lanes8` witness with NO hypothesis
about any chip or hash. -/
theorem weldWit8_satisfies_constructed (S8 : Heap8Scheme) (hash : List ℤ → ℤ)
    (d : TableDfa Nat Nat) (hstep : ∀ s y, d.step s y < ASTATES) (q : Nat) (hq : q < ASTATES)
    (w : List Nat) (hw : w ≠ []) (hsym : ∀ y ∈ w, y < ASYM) (name : String) :
    Satisfied2Lanes8 S8 hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) []
      (weldWit8 d (autoRoot8 S8 d) q w) :=
  weldWit8_satisfies S8 hash d _ (autoRoot8_opens S8 d) hstep q hq w hw hsym name

/-! ## §3 — EXTRACTION: what a Lanes8-satisfying welded trace FORCES, row by row. -/

/-- The row's 8-felt root group, read off the trace. -/
def rowRoot (t : VmTrace) (i : Nat) : Digest8 := fun l => (envAt t i).loc (W8ROOT l)

/-- The PUBLIC 8-felt root group, read off the public inputs. -/
def pubRoot (t : VmTrace) : Digest8 := fun l => t.pub (PI_W8ROOT l)

/-- **Every accepted row opens its edge at the row's OWN 8-felt group.** The `.mapOp` arm of
`Satisfied2Lanes8`, unfolded at the welded op. -/
theorem lanes8_row_opens (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    opensToMerkle8 S8 MAP_TREE_DEPTH (rowRoot t i)
      (2 * (envAt t i).loc CURRENT + (envAt t i).loc SYMBOL) (some ((envAt t i).loc NEXT)) := by
  have hc := h.rowConstraints i hi weldTransitionOpen (weldOpen_mem name)
  have hm : weldOp.holdsAt8 S8 (envAt t i) := hc
  exact (hm rfl).1

/-- **The row group is the PUBLIC group, lane by lane, modulo the BabyBear prime.** Row 0 by the
lane's public pin; row `i + 1` by the lane's constancy window at row `i`. -/
theorem lanes8_root_public (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t) (l : Fin 8) :
    ∀ i, i < t.rows.length → rowRoot t i l ≡ pubRoot t l [ZMOD 2013265921] := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hc := h.rowConstraints 0 hi (weldB3 l) (weldB3_mem name l)
    have hpin : (0 == 0) = true → (envAt t 0).loc (W8ROOT l)
        ≡ (envAt t 0).pub (PI_W8ROOT l) [ZMOD 2013265921] := hc
    exact hpin rfl
  | succ i ih =>
    intro hi
    have hi0 : i < t.rows.length := Nat.lt_of_succ_lt hi
    have hc := h.rowConstraints i hi0 (weldRootConst l) (weldRootConst_mem name l)
    have hwin : WindowConstraint.holdsAt (envAt t i) (i + 1 == t.rows.length)
        ⟨weldRootBody l, true⟩ := hc
    simp only [WindowConstraint.holdsAt, if_true] at hwin
    have hnl : (i + 1 == t.rows.length) = false := by
      have : i + 1 ≠ t.rows.length := Nat.ne_of_lt hi
      simpa using this
    have hb := hwin hnl
    rw [weldRootBody_eq] at hb
    simp only [WindowExpr.eval] at hb
    have hnxt : (envAt t i).nxt (W8ROOT l) = (envAt t (i + 1)).loc (W8ROOT l) := rfl
    rw [hnxt] at hb
    have hdvd := Int.modEq_iff_dvd.mp hb
    have hstep : rowRoot t i l ≡ rowRoot t (i + 1) l [ZMOD 2013265921] := by
      apply Int.modEq_iff_dvd.mpr
      show (2013265921 : ℤ) ∣ (envAt t (i + 1)).loc (W8ROOT l) - (envAt t i).loc (W8ROOT l)
      have h' : (2013265921 : ℤ) ∣ 0 - ((envAt t (i + 1)).loc (W8ROOT l)
          + -1 * (envAt t i).loc (W8ROOT l)) := hdvd
      have heq : (0 : ℤ) - ((envAt t (i + 1)).loc (W8ROOT l) + -1 * (envAt t i).loc (W8ROOT l))
          = -((envAt t (i + 1)).loc (W8ROOT l) - (envAt t i).loc (W8ROOT l)) := by ring
      rw [heq] at h'
      exact (Int.dvd_neg).mp h'
    exact hstep.symm.trans (ih hi0)

/-- ⚑ **The graduated range teeth under the 8-lane denotation**: every accepted row's state is
`< 2^15` and its symbol `< 2`, given faithful range tables (the lookup arm of `holdsAt8` IS
`holdsAt`). This is what lets `hs`/`hy` below be DISCHARGED from the trace rather than assumed. -/
theorem lanes8_row_bounded (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t)
    (htf : WeldRangeTablesFaithful t.tf) (i : Nat) (hi : i < t.rows.length) :
    VmRange.holds (envAt t i) ⟨CURRENT, 15⟩ ∧ VmRange.holds (envAt t i) ⟨SYMBOL, 1⟩ := by
  have h1 : [(EmittedExpr.var CURRENT).eval (envAt t i).loc] ∈ t.tf WELD_TID_RANGE15 :=
    h.rowConstraints i hi weldCurRange (weldCurRange_mem name)
  have h2 : [(EmittedExpr.var SYMBOL).eval (envAt t i).loc] ∈ t.tf WELD_TID_RANGE1 :=
    h.rowConstraints i hi weldSymRange (weldSymRange_mem name)
  rw [htf.1, range_row_mem_iff] at h1
  rw [htf.2, range_row_mem_iff] at h2
  exact ⟨h1, h2⟩

/-- Cells in canonical BabyBear range: every root-lane cell of every row, and every public lane.
Over the deployed field this holds by type; in the ℤ-valued model it is a hypothesis. -/
def LaneCanonical (t : VmTrace) : Prop :=
  (∀ i, i < t.rows.length → ∀ l : Fin 8, 0 ≤ rowRoot t i l ∧ rowRoot t i l < 2013265921)
  ∧ ∀ l : Fin 8, 0 ≤ pubRoot t l ∧ pubRoot t l < 2013265921

/-- The constructed witness is canonical whenever its root group is. -/
theorem weldWit8_laneCanonical (d : TableDfa Nat Nat) (R8 : Digest8)
    (hR : ∀ l, 0 ≤ R8 l ∧ R8 l < 2013265921) (q : Nat) (w : List Nat) :
    LaneCanonical (weldWit8 d R8 q w) := by
  refine ⟨?_, ?_⟩
  · intro i hi l
    have hi' : i < (rowsW d R8 q w).length := hi
    show 0 ≤ (envAt (weldWit8 d R8 q w) i).loc (W8ROOT l)
      ∧ (envAt (weldWit8 d R8 q w) i).loc (W8ROOT l) < 2013265921
    rw [envAt_weldWit8, envAt_loc (t := weldWit d R8 q w) hi]
    show 0 ≤ ((rowsW d R8 q w)[i]'hi') (W8ROOT l) ∧ ((rowsW d R8 q w)[i]'hi') (W8ROOT l) < 2013265921
    rw [rowsW_root d R8 l w q i hi']
    exact hR l
  · intro l
    show 0 ≤ weldPub q (classifyFrom d q w) R8 (PI_W8ROOT l)
      ∧ weldPub q (classifyFrom d q w) R8 (PI_W8ROOT l) < 2013265921
    rw [weldPub_root]
    exact hR l

/-- **At canonical felts the row group EQUALS the public group** (as a `Digest8`). -/
theorem lanes8_root_eq_public (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t) (hcan : LaneCanonical t)
    (i : Nat) (hi : i < t.rows.length) : rowRoot t i = pubRoot t := by
  funext l
  have hmod := lanes8_root_public S8 hash name minit mfin maddrs t h l i hi
  have h1 := hcan.1 i hi l
  have h2 := hcan.2 l
  have e1 : rowRoot t i l % 2013265921 = rowRoot t i l := Int.emod_eq_of_lt h1.1 h1.2
  have e2 : pubRoot t l % 2013265921 = pubRoot t l := Int.emod_eq_of_lt h2.1 h2.2
  calc rowRoot t i l = rowRoot t i l % 2013265921 := e1.symm
    _ = pubRoot t l % 2013265921 := hmod
    _ = pubRoot t l := e2

/-- **Every accepted row opens its edge at the PUBLIC 8-felt root** (canonical felts). -/
theorem lanes8_row_opens_public (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t) (hcan : LaneCanonical t)
    (i : Nat) (hi : i < t.rows.length) :
    opensToMerkle8 S8 MAP_TREE_DEPTH (pubRoot t)
      (2 * (envAt t i).loc CURRENT + (envAt t i).loc SYMBOL) (some ((envAt t i).loc NEXT)) := by
  rw [← lanes8_root_eq_public S8 hash name minit mfin maddrs t h hcan i hi]
  exact lanes8_row_opens S8 hash name minit mfin maddrs t h i hi

/-! ## §4 — ⚑ THE BINDING THEOREM FOR THE FULL 8-FELT DIGEST.

Stated over EXPLICIT witness heaps, as `MapMerkleRoot` §5b.E insists: the collision disjunct names
the pair `mapRoot8Find` returns for the row's heap and the committing heap. It is NOT
`∃ collision` (unconditionally true at BabyBear by pigeonhole) — and `weld_collision_disjunct_refutable`
shows exhibiting it refutes the chip's injectivity outright. -/

/-- **`weld8_forged_edge_refused`** — a Lanes8-accepted trace whose PUBLIC root group commits `d`
cannot claim a step `d` does not have, except by supplying, for that row, a heap behind the same
8-felt root that reads the forged value — and that heap collides with the committing heap at the
named arity-16 chip pair. The 8-felt, denotation-level form of
`AttestedAutomatonWeld8.forged_edge_refused_8`. -/
theorem weld8_forged_edge_refused (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t) (hcan : LaneCanonical t)
    (d : TableDfa Nat Nat) {m : Heap.FeltHeap} (hd : CommitsAutomaton8By S8 m (pubRoot t) d)
    (i : Nat) (hi : i < t.rows.length) (s y : Nat) (hs : s < ASTATES) (hy : y < ASYM)
    (hcur : (envAt t i).loc CURRENT = Int.ofNat s) (hsym : (envAt t i).loc SYMBOL = Int.ofNat y)
    (hbad : (envAt t i).loc NEXT ≠ Int.ofNat (d.step s y)) :
    ∃ mRow : Heap.FeltHeap,
      Heap.SortedKeys mRow ∧ mRow.length = 2 ^ MAP_TREE_DEPTH
        ∧ mapRoot8 S8 MAP_TREE_DEPTH mRow = pubRoot t
        ∧ Heap.get mRow ((keyOf s y : Nat) : ℤ) = some ((envAt t i).loc NEXT)
        ∧ MapRootColl S8 MAP_TREE_DEPTH mRow m := by
  have hopen := lanes8_row_opens_public S8 hash name minit mfin maddrs t h hcan i hi
  rw [hcur, hsym] at hopen
  have hkey : (2 : ℤ) * Int.ofNat s + Int.ofNat y = ((keyOf s y : Nat) : ℤ) := by
    simp only [keyOf, Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [hkey] at hopen
  obtain ⟨mRow, hsort, hlen, hroot, hget⟩ := hopen
  refine ⟨mRow, hsort, hlen, hroot, hget, ?_⟩
  rcases opensToMerkle8_functional_or_collides S8 MAP_TREE_DEPTH hlen hroot hget
      hd.2.1 hd.2.2.1 (hd.2.2.2 s y hs hy) with heq | hc
  · exfalso
    simp only [Option.some.injEq] at heq
    exact hbad (by rw [heq]; rfl)
  · exact hc

/-- **`weld8_accepted_run_is_committed_run`** — the positive polarity: every accepted row's `next`
IS the committed automaton's step, or the row's own heap collides with the committing heap at the
named pair. -/
theorem weld8_accepted_run_is_committed_run (S8 : Heap8Scheme) (hash : List ℤ → ℤ) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t) (hcan : LaneCanonical t)
    (d : TableDfa Nat Nat) {m : Heap.FeltHeap} (hd : CommitsAutomaton8By S8 m (pubRoot t) d)
    (i : Nat) (hi : i < t.rows.length) (s y : Nat) (hs : s < ASTATES) (hy : y < ASYM)
    (hcur : (envAt t i).loc CURRENT = Int.ofNat s) (hsym : (envAt t i).loc SYMBOL = Int.ofNat y) :
    (envAt t i).loc NEXT = Int.ofNat (d.step s y)
      ∨ ∃ mRow : Heap.FeltHeap,
          Heap.SortedKeys mRow ∧ mRow.length = 2 ^ MAP_TREE_DEPTH
            ∧ mapRoot8 S8 MAP_TREE_DEPTH mRow = pubRoot t
            ∧ Heap.get mRow ((keyOf s y : Nat) : ℤ) = some ((envAt t i).loc NEXT)
            ∧ MapRootColl S8 MAP_TREE_DEPTH mRow m := by
  by_cases hbad : (envAt t i).loc NEXT = Int.ofNat (d.step s y)
  · exact Or.inl hbad
  · exact Or.inr (weld8_forged_edge_refused S8 hash name minit mfin maddrs t h hcan d hd i hi
      s y hs hy hcur hsym hbad)

/-! ## §5 — ⚑ THE VACUITY FALSIFIER: `weld_completion_lanes_free` FLIPS under this denotation.

`AttestedAutomatonWeld8.weld_completion_lanes_free` proves that under the scalar `Satisfied2Public`
the seven completion lanes may be ANY felts. Under `Satisfied2Lanes8` that is REFUTED, exhibited at
the toy chip whose every absorb is the zero digest: every 2^16-leaf heap then has root
`zeroDigest8`, so a satisfying trace's group must be zero on every lane, and a completion vector
with a non-zero lane does not satisfy. The pair (`weld_completion_lanes_free`,
`weld_completion_lanes_not_free`) is the exhibited separation. -/

/-- The toy chip: every absorb is the zero digest. A legitimate `Heap8Scheme` (the structure carries
no injectivity field — `MapMerkleRoot` §5b deleted it because BabyBear refutes it). -/
def constChip : Heap8Scheme := { chipAbsorb8 := fun _ => zeroDigest8 }

theorem constChip_node (l r : Digest8) : heapNodeOf8 constChip l r = zeroDigest8 := rfl

/-- One fold level at the constant chip over an EVEN-length list is all-zero. -/
theorem foldLevel8_constChip_zero :
    ∀ (n : Nat) (xs : List Digest8), xs.length = 2 * n →
      ∀ x ∈ foldLevel8 constChip xs, x = zeroDigest8 := by
  intro n
  induction n with
  | zero =>
    intro xs hxs x hx
    have : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hxs)
    subst this
    simp [foldLevel8] at hx
  | succ k ih =>
    intro xs hxs x hx
    match xs, hxs with
    | [], h => simp at h
    | [_], h =>
      simp only [List.length_singleton] at h
      omega
    | l :: r :: rest, h =>
      simp only [foldLevel8, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · exact ih rest (by simp only [List.length_cons] at h; omega) x hx

/-- A fold level at ANY chip keeps a non-empty list non-empty. -/
theorem foldLevel8_ne_nil (S8 : Heap8Scheme) : ∀ xs : List Digest8, xs ≠ [] →
    foldLevel8 S8 xs ≠ []
  | [], h => absurd rfl h
  | [_], _ => by simp [foldLevel8]
  | _ :: _ :: _, _ => by simp [foldLevel8]

/-- A fold level at the constant chip keeps an all-zero list all-zero. -/
theorem foldLevel8_constChip_zero_of_zero : ∀ xs : List Digest8,
    (∀ x ∈ xs, x = zeroDigest8) → ∀ y ∈ foldLevel8 constChip xs, y = zeroDigest8
  | [], _, y, hy => by simp [foldLevel8] at hy
  | [x], hx, y, hy => by
    simp only [foldLevel8, List.mem_singleton] at hy
    subst hy
    exact hx y (List.mem_singleton.mpr rfl)
  | l :: r :: rest, hx, y, hy => by
    simp only [foldLevel8, List.mem_cons] at hy
    rcases hy with rfl | hy
    · rfl
    · exact foldLevel8_constChip_zero_of_zero rest
        (fun z hz => hx z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))) y hy

/-- The perfect-tree root of a non-empty all-zero list at the constant chip is zero, at every depth. -/
theorem perfectRoot8_constChip_zero : ∀ (dep : Nat) (xs : List Digest8), xs ≠ [] →
    (∀ x ∈ xs, x = zeroDigest8) → perfectRoot8 constChip dep xs = zeroDigest8 := by
  intro dep
  induction dep with
  | zero =>
    intro xs hne hz
    match xs, hne with
    | [], h => exact absurd rfl h
    | x :: _, _ => exact hz x (List.mem_cons_self)
  | succ k ih =>
    intro xs hne hz
    show perfectRoot8 constChip k (foldLevel8 constChip xs) = zeroDigest8
    exact ih _ (foldLevel8_ne_nil constChip xs hne) (foldLevel8_constChip_zero_of_zero xs hz)

/-- **At the constant chip every deployed-depth heap root is the zero digest.** -/
theorem mapRoot8_constChip (h : Heap.FeltHeap) (hlen : h.length = 2 ^ MAP_TREE_DEPTH) :
    mapRoot8 constChip MAP_TREE_DEPTH h = zeroDigest8 := by
  have hD : MAP_TREE_DEPTH = 15 + 1 := rfl
  show perfectRoot8 constChip MAP_TREE_DEPTH ((linkHeap h).map (heapLeafDigest8 constChip))
    = zeroDigest8
  rw [hD]
  show perfectRoot8 constChip 15
    (foldLevel8 constChip ((linkHeap h).map (heapLeafDigest8 constChip))) = zeroDigest8
  have hlen' : ((linkHeap h).map (heapLeafDigest8 constChip)).length = 2 * 2 ^ 15 := by
    rw [List.length_map, linkHeap_length, hlen, hD]
    rfl
  apply perfectRoot8_constChip_zero
  · apply foldLevel8_ne_nil
    intro hnil
    have : ((linkHeap h).map (heapLeafDigest8 constChip)).length = 0 := by rw [hnil]; rfl
    rw [hlen'] at this
    omega
  · exact foldLevel8_constChip_zero (2 ^ 15) _ hlen'

/-- **The 8-lane denotation FORCES the group at the toy chip**: every accepted row's group is zero. -/
theorem lanes8_forces_root_at_constChip (hash : List ℤ → ℤ) (name : String)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2Lanes8 constChip hash (weldDesc name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) : rowRoot t i = zeroDigest8 := by
  obtain ⟨mRow, _, hlen, hroot, _⟩ := lanes8_row_opens constChip hash name minit mfin maddrs t h i hi
  rw [← hroot]
  exact mapRoot8_constChip mRow hlen

/-- ⚑ **THE COMPLETION LANES ARE NOT FREE.** The exact negation of the universally-quantified form
of `AttestedAutomatonWeld8.weld_completion_lanes_free`, under `Satisfied2Lanes8`, at the toy chip:
it is FALSE that every completion-lane vector satisfies the welded descriptor. (At the deployed chip
the content is §4; this is the vacuity falsifier, exhibited.) -/
theorem weld_completion_lanes_not_free (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) (r0 : ℤ)
    (q : Nat) (w : List Nat) (hw : w ≠ []) (name : String) :
    ¬ ∀ hi : Fin 8 → ℤ,
      Satisfied2Lanes8 constChip hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) []
        (weldWit8 d (fun l => if l = 0 then r0 else hi l) q w) := by
  intro hall
  have h := hall (fun _ => 1)
  have h0 : 0 < (weldWit8 d (fun l => if l = 0 then r0 else (fun _ : Fin 8 => (1 : ℤ)) l) q w).rows.length := by
    show 0 < (rowsW d _ q w).length
    rw [rowsW_length]
    exact List.length_pos_of_ne_nil hw
  have hz := lanes8_forces_root_at_constChip hash name _ _ _ _ h 0 h0
  have h1 : rowRoot (weldWit8 d (fun l => if l = 0 then r0 else (fun _ : Fin 8 => (1 : ℤ)) l) q w) 0 1
      = 1 := by
    show (envAt (weldWit8 d _ q w) 0).loc (W8ROOT 1) = 1
    rw [envAt_weldWit8, envAt_loc (t := weldWit d _ q w) h0]
    show ((rowsW d (fun l => if l = 0 then r0 else (fun _ : Fin 8 => (1 : ℤ)) l) q w)[0]'h0)
      (W8ROOT 1) = 1
    rw [rowsW_root d _ 1 w q 0 h0]
    rfl
  rw [hz] at h1
  exact absurd h1 (by decide)

/-- At the constant chip the automaton's own 8-felt commitment is the zero digest. -/
theorem autoRoot8_constChip (d : TableDfa Nat Nat) : autoRoot8 constChip d = zeroDigest8 := by
  unfold autoRoot8
  exact mapRoot8_constChip _ (autoHeapW_length d)

/-- ⚑ **THE CHARACTERIZATION AT THE TOY CHIP** (codex round 1 §6): the welded witness satisfies
`Satisfied2Lanes8` at `constChip` EXACTLY when its root group is the zero digest. The `←` half is
the witness, the `→` half is the forcing; together they say the lane-complete denotation is
satisfiable and NOT lane-free, in one sentence. -/
theorem lanes8_constChip_iff (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) (R8 : Digest8)
    (hstep : ∀ s y, d.step s y < ASTATES) (q : Nat) (hq : q < ASTATES)
    (w : List Nat) (hw : w ≠ []) (hsym : ∀ y ∈ w, y < ASYM) (name : String) :
    Satisfied2Lanes8 constChip hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) []
        (weldWit8 d R8 q w)
      ↔ R8 = zeroDigest8 := by
  constructor
  · intro h
    have h0 : 0 < (weldWit8 d R8 q w).rows.length := by
      show 0 < (rowsW d R8 q w).length
      rw [rowsW_length]
      exact List.length_pos_of_ne_nil hw
    have hz := lanes8_forces_root_at_constChip hash name _ _ _ _ h 0 h0
    funext l
    have hl : rowRoot (weldWit8 d R8 q w) 0 l = R8 l := by
      show (envAt (weldWit8 d R8 q w) 0).loc (W8ROOT l) = R8 l
      rw [envAt_weldWit8, envAt_loc (t := weldWit d R8 q w) h0]
      show ((rowsW d R8 q w)[0]'h0) (W8ROOT l) = R8 l
      exact rowsW_root d R8 l w q 0 h0
    rw [← hl, hz]
  · intro hR
    subst hR
    have h8 : CommitsAutomaton8 constChip zeroDigest8 d := by
      have := autoRoot8_opens constChip d
      rwa [autoRoot8_constChip] at this
    exact weldWit8_satisfies constChip hash d zeroDigest8 h8 hstep q hq w hw hsym name

/-! ### §5a — the forgery premises are JOINTLY INHABITED (codex round 1 §5).

`weld8_forged_edge_refused` takes a satisfying trace, canonical lanes, a commitment of `d` at the
public root, and a row whose `next` is NOT `d.step`. At the toy chip every automaton shares the zero
root, so the constant-ZERO automaton is committed at the very root the constant-ONE automaton's run
publishes: the forged edge is real, and the theorem's hypotheses are met by a closed instance. -/

/-- The committed automaton: every step goes to state 0. -/
def forgeD : TableDfa Nat Nat := ⟨fun _ _ => 0, 0, fun _ => True⟩
/-- The automaton the trace actually runs: every step goes to state 1. -/
def forgeE : TableDfa Nat Nat := ⟨fun _ _ => 1, 0, fun _ => True⟩
/-- The one-step run of `forgeE` from state 0 on symbol 0, at the zero root. -/
def forgeT : VmTrace := weldWit8 forgeE zeroDigest8 0 [0]

theorem weld8_forgery_premises_inhabited (hash : List ℤ → ℤ) (name : String) :
    Satisfied2Lanes8 constChip hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) [] forgeT
    ∧ LaneCanonical forgeT
    ∧ CommitsAutomaton8By constChip (autoHeapW forgeD) (pubRoot forgeT) forgeD
    ∧ (envAt forgeT 0).loc CURRENT = Int.ofNat 0
    ∧ (envAt forgeT 0).loc SYMBOL = Int.ofNat 0
    ∧ (envAt forgeT 0).loc NEXT ≠ Int.ofNat (forgeD.step 0 0) := by
  have hpub : pubRoot forgeT = zeroDigest8 := by
    funext l
    show weldPub 0 (classifyFrom forgeE 0 [0]) zeroDigest8 (PI_W8ROOT l) = zeroDigest8 l
    rw [weldPub_root]
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
  · exact (lanes8_constChip_iff hash forgeE zeroDigest8
      (fun _ _ => (by decide : (1 : Nat) < ASTATES)) 0 (by decide) [0]
      (by simp) (fun y hy => by simp at hy; subst hy; decide) name).mpr rfl
  · exact weldWit8_laneCanonical forgeE zeroDigest8
      (fun _ => ⟨(by decide : (0 : ℤ) ≤ 0), (by decide : (0 : ℤ) < 2013265921)⟩) 0 [0]
  · rw [hpub, ← autoRoot8_constChip forgeD]
    exact autoRoot8_commits constChip forgeD
  · show Int.ofNat 1 ≠ Int.ofNat 0
    decide

/-! ## §6 — axiom tripwires. -/

#assert_all_clean [MapOp.rowAt8_length, VmConstraint2.holdsAt8_of_not_mapOp,
  weld_mapLog8, weldOp_holdsAt8, weldWit8_satisfies, weldWit8_satisfies_constructed,
  lanes8_row_opens, lanes8_root_public, weldWit8_laneCanonical, lanes8_root_eq_public,
  lanes8_row_opens_public, weld8_forged_edge_refused, weld8_accepted_run_is_committed_run,
  foldLevel8_constChip_zero, foldLevel8_ne_nil, foldLevel8_constChip_zero_of_zero,
  perfectRoot8_constChip_zero, mapRoot8_constChip, lanes8_forces_root_at_constChip,
  weld_completion_lanes_not_free, autoRoot8_constChip, lanes8_constChip_iff,
  weld8_forgery_premises_inhabited, attTf8_faithful, lanes8_row_bounded]

end Dregg2.Circuit.Emit.AttestedAutomatonLanes8
