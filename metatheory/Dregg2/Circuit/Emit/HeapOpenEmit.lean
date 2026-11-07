/-
# Dregg2.Circuit.Emit.HeapOpenEmit — the LIVE heap-membership open, the SECOND faithful-root after-spine.

The exact twin of `CapOpenEmit.lean` §11/§12 for the `heap_root` (the second faithful 8-felt Merkle root).
Where the cap-open read authenticates a HELD capability's authority (7-field `CapLeaf`, facet/mask gates),
the heap open authenticates a LINKED IMT leaf `(addr, value, nextAddr)` against the committed 8-felt heap
root — no authority machinery, just membership. The keystone `heapOpen_writesTo8` reduces the faithful
8-felt heap-write to TWO `HeapMembershipCore` witnesses sharing a path (before = old leaf against the
BEFORE heap-root group; after = in-place-updated leaf, SAME address, new value, SAME pointer, against the
AFTER heap-root group), FORCING `EffectVmEmitRotationV3.heapWritesTo8` over the FULL ~124-bit root — NEVER
the lane-0 squeeze the heap GENTIAN tooth (`circuit/tests/heap_root_gentian_weld.rs`) refutes.

REUSE: the node-recompose spine is leaf-AGNOSTIC (`DeployedCapOpen.nodeLookup`/`nodeInputs`/`nodeInputs_eval`/
`dir_zero_or_one` over `CapOpenCols`, rides the ONE `node8` chip), so the heap membership reuses it verbatim
and re-instantiates the digest scheme at `Heap8Scheme` (`heapNodeOf8`, `heapLeafDigest8`). The SOLE
heap-specific material is the arity-3 leaf absorb (`heapLeafLookup`, `heapLeafDigest_sound8`) — the heap leaf
is the gap-#5 IMT `(addr, value, nextAddr)` (`heap_root.rs::HeapLeaf::digest8`), not a 7-field `CapLeaf`.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the named WIDE
chip-soundness `ChipTableSoundN (heapPermOut S8)`, inherited from `DeployedHeapTree`/`DeployedCapOpen`.
-/
import Dregg2.Circuit.DeployedCapOpen
import Dregg2.Circuit.DeployedHeapTree
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.CapOpenEmit
import Dregg2.Circuit.Emit.EffectVmEmitHeapRoot

namespace Dregg2.Circuit.Emit.HeapOpenEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv EFFECT_VM_WIDTH VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (Table TraceFamily Lookup VmConstraint2 EffectVmDescriptor2 ChipTableSoundN Satisfied2
   chipLookupTupleN chip_lookup_sound_N CHIP_RATE ChipArityAdmitted)
open Dregg2.Circuit.DeployedCapOpen
  (CapOpenCols DEPTH digestCols digestCols_map curCol nodeInputs nodeLookup nodeInputs_eval
   dirBoolGate dirBoolGate_eq dirBoolVal dir_zero_or_one rootPinGate pathOf8 groupVal)
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.DeployedHeapTree.Heap8Scheme (heapLeafDigest8 heapNodeOf8 recomposeUp8)
open Dregg2.Circuit.CapMerkleGeneric (StepG recomposeG)
open Dregg2.Circuit.Emit.CapOpenEmit
  (capOpenCols nodeLookups dirBoolGates rootPinGates eqGate eqGate_eval
   boolGateCanon_exact diffGate_exact
   CAP_OPEN_SPAN AFTER_SPINE_SPAN AFTER_SPINE_BASE)
open Dregg2.Circuit.Emit.EffectVmEmit (prmCol)
open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (B_SPAN)

set_option autoImplicit false

/-! ## §0 — the heap leaf columns + the arity-3 IMT leaf absorb (the SOLE heap-specific chip lookup).

The heap membership reuses the `CapOpenCols` layout, reading leaf column 0 as the `addr`, leaf column 1
as the `value`, and leaf column 2 as the IMT `nextAddr` POINTER (columns 3..6, and the facet/mask
machinery, are UNUSED — the heap leaf carries no authority). The leaf absorb is arity-3
(`heapLeafDigest8 S8 (addr, value, next) = S8.chipAbsorb8 [addr, value, next]` — the deployed
`HeapLeaf::digest8`, gap-#5 IMT), NOT the cap arity-7 `leafFields`. -/

/-- The LINKED `(addr, value, nextAddr)` heap leaf read off the row's leaf columns 0/1/2. -/
def heapLeafTripleOf (c : CapOpenCols) (env : VmRowEnv) : ℤ × ℤ × ℤ :=
  (env.loc (c.leaf 0), env.loc (c.leaf 1), env.loc (c.leaf 2))

/-- The `(addr, value)` MAP-LEVEL heap leaf pair (leaf cols 0/1) — the projection the sorted-tree
`MembersAt8` consumers (accumulator insert/open) read, where the IMT pointer is existential at the
map level. Equals the first two components of `heapLeafTripleOf`. -/
def heapLeafPairOf (c : CapOpenCols) (env : VmRowEnv) : ℤ × ℤ :=
  (env.loc (c.leaf 0), env.loc (c.leaf 1))

/-- The 3 heap-leaf column EXPRESSIONS `[addr, value, nextAddr]` (the arity-3 chip absorb's input
tuple). -/
def heapLeafInputs (c : CapOpenCols) : List EmittedExpr :=
  [EmittedExpr.var (c.leaf 0), EmittedExpr.var (c.leaf 1), EmittedExpr.var (c.leaf 2)]

/-- The heap leaf inputs evaluate to exactly `[addr, value, nextAddr]` of the decoded triple. -/
theorem heapLeafInputs_eval (c : CapOpenCols) (env : VmRowEnv) :
    (heapLeafInputs c).map (·.eval env.loc)
      = [(heapLeafTripleOf c env).1, (heapLeafTripleOf c env).2.1,
         (heapLeafTripleOf c env).2.2] := by
  simp [heapLeafInputs, heapLeafTripleOf, EmittedExpr.eval]

/-- **`heapPermOut S8`** — the WIDE permutation output the shared `node8` chip realizes for the heap
scheme: the 8 squeezed lanes of `S8.chipAbsorb8` read as a `List ℤ`. `heapPermOut S8 [addr,value,next] =
List.ofFn (heapLeafDigest8 S8 (addr,value,next))` and `heapPermOut S8 (pack8 l r) = List.ofFn
(heapNodeOf8 S8 l r)` — both by `rfl` (`List.ofFn ∘ chipAbsorb8` of the input block). -/
def heapPermOut (S8 : Heap8Scheme) : List ℤ → List ℤ := fun xs => List.ofFn (S8.chipAbsorb8 xs)

/-- The 8-felt heap-leaf chip lookup tuple: absorb the 3 heap-leaf columns, output = the 8 bound
leaf-digest columns (the whole `node8` leaf block). -/
def heapLeafLookup (c : CapOpenCols) : Lookup :=
  { table := .poseidon2, tuple := chipLookupTupleN (heapLeafInputs c) (digestCols c.leafDigest) }

-- REGRESSION TOOTH (gap-#5 IMT arity): the emitted heap-leaf lookup absorbs EXACTLY 3 inputs —
-- the deployed `HeapLeaf::digest8` absorbs `[addr, value, next_addr]` (arity 3). An arity-2 emit
-- (the pre-flip wound) would request a `(2, [addr,value])` chip row the digest8 provide never has,
-- so every honest heap-open-appendix path would go RED. Pinning the arity here catches the drift at
-- emit time, before the producer/descriptor differential. (Inputs read consecutive leaf cols 0/1/2.)
#guard (heapLeafInputs (capOpenCols 100)).length == 3
#guard (heapLeafInputs (capOpenCols 100)) == [EmittedExpr.var ((capOpenCols 100).leaf 0),
  EmittedExpr.var ((capOpenCols 100).leaf 1), EmittedExpr.var ((capOpenCols 100).leaf 2)]

/-! ## §1 — the heap membership core + the node/leaf digest soundness (re-instantiated at `Heap8Scheme`). -/

/-- **`HeapMembershipCore tf c env`** — the four facts the 8-felt heap Merkle fold consumes: the arity-3
leaf absorb, the per-level `node8` absorbs (SHARED with cap — the same `nodeLookup`), direction booleanity,
and the (8-lane) root pin. The heap twin of `DeployedCapOpen.MembershipCore`. -/
structure HeapMembershipCore (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv) : Prop where
  leafHashed : (heapLeafLookup c).holdsAt tf env
  nodeHashed : ∀ lvl < DEPTH, (nodeLookup c lvl).holdsAt tf env
  dirBool    : ∀ lvl < DEPTH, (dirBoolGate c lvl).eval env.loc = 0
  rootPinned : ∀ i : Fin 8, (rootPinGate c i).eval env.loc = 0

/-- **`heapLeafDigest_sound8`** — under a SOUND WIDE chip table, the 8 leaf-digest columns carry the genuine
native-8-felt `heapLeafDigest8 S8 (addr, value, nextAddr)`. The whole 8-felt block is bound, not just
lane-0. The heap twin of `leafDigest_sound8` (arity-3 IMT leaf). -/
theorem heapLeafDigest_sound8 (S8 : Heap8Scheme)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (heapPermOut S8) (tf .poseidon2))
    (hcore : HeapMembershipCore tf c env) :
    groupVal env c.leafDigest = heapLeafDigest8 S8 (heapLeafTripleOf c env) := by
  -- the IMT leaf absorb is 3 lanes: an admitted arity, and the spine is literal for any `c`.
  have hlen : ChipArityAdmitted (heapLeafInputs c).length := of_decide_eq_true (Eq.refl true)
  have hmem : (chipLookupTupleN (heapLeafInputs c) (digestCols c.leafDigest)).map (·.eval env.loc)
      ∈ tf .poseidon2 := by
    have := hcore.leafHashed
    unfold Lookup.holdsAt heapLeafLookup at this
    exact this
  have h := chip_lookup_sound_N (heapPermOut S8) (tf .poseidon2) hChip env.loc (heapLeafInputs c)
    (digestCols c.leafDigest) hlen hmem
  rw [digestCols_map, heapLeafInputs_eval] at h
  -- `heapPermOut S8 [addr,value,next] = List.ofFn (heapLeafDigest8 S8 (addr,value,next))` by `rfl`.
  have hreal : heapPermOut S8 [(heapLeafTripleOf c env).1, (heapLeafTripleOf c env).2.1,
      (heapLeafTripleOf c env).2.2]
      = List.ofFn (heapLeafDigest8 S8 (heapLeafTripleOf c env)) := rfl
  rw [hreal] at h
  exact List.ofFn_inj.mp h

/-- **`heapNode_sound8`** — under a SOUND WIDE chip table, level `lvl`'s 8 node columns carry the genuine
native-8-felt `heapNodeOf8 S8` of the dir-mixed `(cur8, sib8)` pair — one `recomposeUp8` step at full
~124-bit width. Reuses the SHARED `nodeInputs_eval` (the node block is leaf-agnostic). -/
theorem heapNode_sound8 (S8 : Heap8Scheme)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (heapPermOut S8) (tf .poseidon2))
    (hcore : HeapMembershipCore tf c env) (lvl : Nat) (hlvl : lvl < DEPTH) :
    groupVal env (c.node lvl)
      = (if dirBoolVal c env lvl
          then heapNodeOf8 S8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl))
          else heapNodeOf8 S8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl))) := by
  have hlen : ChipArityAdmitted (nodeInputs c lvl).length := of_decide_eq_true (Eq.refl true)
  have hmem : (chipLookupTupleN (nodeInputs c lvl) (digestCols (c.node lvl))).map (·.eval env.loc)
      ∈ tf .poseidon2 := by
    have := hcore.nodeHashed lvl hlvl
    unfold Lookup.holdsAt nodeLookup at this
    exact this
  have h := chip_lookup_sound_N (heapPermOut S8) (tf .poseidon2) hChip env.loc (nodeInputs c lvl)
    (digestCols (c.node lvl)) hlen hmem
  rw [digestCols_map, nodeInputs_eval c env lvl (dir_zero_or_one c env lvl (hcore.dirBool lvl hlvl))] at h
  cases hb : dirBoolVal c env lvl
  · simp only [hb, Bool.false_eq_true, if_false] at h ⊢
    have hreal : heapPermOut S8 (pack8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl)))
        = List.ofFn (heapNodeOf8 S8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl))) := rfl
    rw [hreal] at h
    exact List.ofFn_inj.mp h
  · simp only [hb, if_true] at h ⊢
    have hreal : heapPermOut S8 (pack8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl)))
        = List.ofFn (heapNodeOf8 S8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl))) := rfl
    rw [hreal] at h
    exact List.ofFn_inj.mp h

/-- `recomposeUp8` (heap scheme) distributes over a path append (over the generic `recomposeG` spine). -/
theorem heapRecomposeUp8_append (S8 : Heap8Scheme) (cur : Digest8) (p q : List (StepG Digest8)) :
    recomposeUp8 S8 cur (p ++ q) = recomposeUp8 S8 (recomposeUp8 S8 cur p) q := by
  show recomposeG (heapNodeOf8 S8) cur (p ++ q)
     = recomposeG (heapNodeOf8 S8) (recomposeG (heapNodeOf8 S8) cur p) q
  induction p generalizing cur with
  | nil => rfl
  | cons s rest ih => simp only [List.cons_append, recomposeG]; rw [ih]

/-- Folding `recomposeUp8` over the first `n` levels reproduces `curCol c n` (as a `Digest8`), under the
WIDE chip soundness — the native 8-felt heap fold. The heap twin of `recompose_reaches_cur8`. -/
theorem heapRecompose_reaches_cur8 (S8 : Heap8Scheme)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (heapPermOut S8) (tf .poseidon2))
    (hcore : HeapMembershipCore tf c env) :
    ∀ n, n ≤ DEPTH →
      recomposeUp8 S8 (groupVal env c.leafDigest) (pathOf8 c env n) = groupVal env (curCol c n) := by
  intro n
  induction n with
  | zero => intro _; simp [pathOf8, recomposeUp8, recomposeG, curCol]
  | succ k ih =>
    intro hk
    have hkd : k < DEPTH := Nat.lt_of_succ_le hk
    have hkle : k ≤ DEPTH := Nat.le_of_lt hkd
    have hpath : pathOf8 c env (k + 1)
        = pathOf8 c env k ++ [{ sib := groupVal env (c.sib k), dir := dirBoolVal c env k }] := by
      simp [pathOf8, List.range_succ, List.map_append]
    rw [hpath, heapRecomposeUp8_append, ih hkle]
    simp only [recomposeUp8, recomposeG]
    have hns := heapNode_sound8 S8 tf c env hChip hcore k hkd
    have hcur : curCol c (k + 1) = c.node k := rfl
    rw [hcur]
    cases hb : dirBoolVal c env k
    · simp only [hb, Bool.false_eq_true, if_false] at hns ⊢
      rw [hns]
    · simp only [hb, if_true] at hns ⊢
      rw [hns]

/-! ## §2 — the recompose from a single core + the STEP-A keystone `heapOpen_writesTo8`. -/

/-- **`heapOpen_recompose8`** — the explicit before/after recompose: under a sound WIDE chip table, the leaf's
native-8-felt heap digest recomposes the committed 8-felt heap-root GROUP along the column-read path. The
`heapWritesTo8` assembler instantiates this at BOTH the before and after spine. The heap twin of
`capOpen_recompose8`. -/
theorem heapOpen_recompose8 (S8 : Heap8Scheme)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (heapPermOut S8) (tf .poseidon2))
    (hcore : HeapMembershipCore tf c env) :
    recomposeUp8 S8 (heapLeafDigest8 S8 (heapLeafTripleOf c env)) (pathOf8 c env DEPTH)
      = groupVal env c.capRoot := by
  have hfold := heapRecompose_reaches_cur8 S8 tf c env hChip hcore DEPTH (le_refl _)
  have hleaf := heapLeafDigest_sound8 S8 tf c env hChip hcore
  rw [hleaf] at hfold
  have hcurTop : curCol c DEPTH = c.node (DEPTH - 1) := rfl
  rw [hcurTop] at hfold
  have hroot : groupVal env (c.node (DEPTH - 1)) = groupVal env c.capRoot := by
    funext i
    have hpin := hcore.rootPinned i
    unfold rootPinGate at hpin
    simp only [EmittedExpr.eval] at hpin
    simp only [groupVal]
    linarith
  rw [hfold, hroot]

/-- **`heapOpen_writesTo8` — THE STEP-A KEYSTONE.** Two `HeapMembershipCore` witnesses sharing the sibling
path (before = old leaf membership against the BEFORE heap-root group; after = updated-leaf membership, SAME
address, new value, SAME IMT pointer, against the AFTER heap-root group) FORCE the faithful 8-felt
`heapWritesTo8` over the FULL ~124-bit root — NOT the lane-0 projection. The post root cannot be forged: a
colliding heap tree (different leaves, same lane-0) yields a different `node8` fold top and FAILS ≥1 of the
8 `rootPinGate` lanes of the after core. The pointer weld (`hnext`) is the IMT value-update discipline — a
value update never re-links the sorted chain. Trace-forced: the witnesses come from `Satisfied2`, never
from `henc`'s `SpineCommits`. -/
theorem heapOpen_writesTo8 (S8 : Heap8Scheme)
    (tf : TraceFamily) (cBefore cAfter : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (heapPermOut S8) (tf .poseidon2))
    (hBefore : HeapMembershipCore tf cBefore env)
    (hAfter  : HeapMembershipCore tf cAfter env)
    (hsib : cAfter.sib = cBefore.sib)
    (hdir : cAfter.dir = cBefore.dir)
    (hkey : (heapLeafTripleOf cAfter env).1 = (heapLeafTripleOf cBefore env).1)
    (hnext : (heapLeafTripleOf cAfter env).2.2 = (heapLeafTripleOf cBefore env).2.2) :
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapWritesTo8 S8
        (groupVal env cBefore.capRoot)
        ((heapLeafTripleOf cBefore env).1) ((heapLeafTripleOf cAfter env).2.1)
        (groupVal env cAfter.capRoot) := by
  refine ⟨(heapLeafTripleOf cBefore env).2.1, (heapLeafTripleOf cBefore env).2.2,
    pathOf8 cBefore env DEPTH, ?_, ?_⟩
  · -- before: recomposeUp8 (heapLeafDigest8 (k, oldVal, next)) path = groupVal cBefore.capRoot
    have hrec := heapOpen_recompose8 S8 tf cBefore env hChip hBefore
    -- (heapLeafTripleOf cBefore env) = ((·).1, (·).2.1, (·).2.2) definitionally (Prod eta).
    simpa using hrec
  · -- after: recomposeUp8 (heapLeafDigest8 (k, v, next)) path = groupVal cAfter.capRoot, SAME path
    have hpath : pathOf8 cAfter env DEPTH = pathOf8 cBefore env DEPTH := by
      simp only [pathOf8, dirBoolVal, hsib, hdir]
    have hrec := heapOpen_recompose8 S8 tf cAfter env hChip hAfter
    rw [hpath] at hrec
    -- rewrite the after leaf's addr to the shared key and its pointer to the shared (held) pointer.
    have htriple : heapLeafTripleOf cAfter env
        = ((heapLeafTripleOf cBefore env).1, (heapLeafTripleOf cAfter env).2.1,
           (heapLeafTripleOf cBefore env).2.2) := by
      rw [← hkey, ← hnext]
    rw [htriple] at hrec
    exact hrec

#assert_axioms heapLeafDigest_sound8
#assert_axioms heapNode_sound8
#assert_axioms heapRecompose_reaches_cur8
#assert_axioms heapOpen_recompose8
#assert_axioms heapOpen_writesTo8

/-! ## §3 — the heap-open READ appendix + the before-membership core (`effHeapOpenV3`).

Mirrors `CapOpenEmit.effCapOpenV3` but WITHOUT the authority machinery — a heap leaf
`(addr, value, nextAddr)` carries no facet/tier, so the read appendix is just the arity-3 IMT leaf
absorb, the 16 shared `node8` lookups, the 16 dir-boolean gates, and the 8-lane root pin. A
`Satisfied2` witness rebuilds `HeapMembershipCore` on every active row. -/

/-- **`heapOpenConstraints w`** — the heap-open read constraint list: the arity-3 leaf lookup, the 16
node lookups (SHARED with cap — the same `nodeLookup`), the 16 dir gates, and the 8 root-pin gates. -/
def heapOpenConstraints (w : Nat) : List VmConstraint2 :=
  .lookup (heapLeafLookup (capOpenCols w))
  :: nodeLookups w
  ++ dirBoolGates w
  ++ rootPinGates w

/-- **`effHeapOpenV3 base name`** — the per-effect heap-open descriptor: a rotated base widened by the
heap-open appendix at `base.traceWidth`, carrying `heapOpenConstraints`. -/
def effHeapOpenV3 (base : EffectVmDescriptor2) (name : String) : EffectVmDescriptor2 :=
  { base with
    name        := name
    traceWidth  := base.traceWidth + CAP_OPEN_SPAN
    constraints := base.constraints ++ heapOpenConstraints base.traceWidth }

/-- Every heap-open constraint is a constraint of the descriptor. -/
theorem effHeapOpenV3_constraints_mem (base : EffectVmDescriptor2) (name : String)
    (c : VmConstraint2) (hc : c ∈ heapOpenConstraints base.traceWidth) :
    c ∈ (effHeapOpenV3 base name).constraints :=
  List.mem_append_right _ hc

/-- **`effHeapOpenV3_core`** — a `Satisfied2` of the heap-open descriptor rebuilds `HeapMembershipCore`
on every active (non-last) row (the appendix constraints read no base column). The heap twin of
`effCapOpenV3_satisfiedEff`'s `core` block. Field-faithful: the lookups lift untouched; the gates arrive
`≡ 0 [ZMOD p]` (`holdsVm`) and lift to their ℤ form through cell canonicality — primality (`dirBool`) /
the `(−p, p)` residual collapse (`rootPinned`). -/
theorem effHeapOpenV3_core (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effHeapOpenV3 base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    HeapMembershipCore t.tf (capOpenCols base.traceWidth) (envAt t i) := by
  have hrow := hsat.rowConstraints i hi
  have hmem := effHeapOpenV3_constraints_mem base name
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  refine { leafHashed := ?_, nodeHashed := ?_, dirBool := ?_, rootPinned := ?_ }
  · have hin : VmConstraint2.lookup (heapLeafLookup (capOpenCols base.traceWidth))
        ∈ heapOpenConstraints base.traceWidth := List.mem_cons_self
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have hin : VmConstraint2.lookup (nodeLookup (capOpenCols base.traceWidth) lvl)
        ∈ heapOpenConstraints base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have hin : VmConstraint2.base (.gate (dirBoolGate (capOpenCols base.traceWidth) lvl))
        ∈ heapOpenConstraints base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
    have h := hrow _ (hmem _ hin)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
    have h' : (dirBoolGate (capOpenCols base.traceWidth) lvl).eval
        (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by simpa using h
    simp only [dirBoolGate_eq] at h' ⊢
    simp only [EmittedExpr.eval] at h' ⊢
    exact boolGateCanon_exact (hcells _) h'
  · intro k
    have hin : VmConstraint2.base (.gate (rootPinGate (capOpenCols base.traceWidth) k))
        ∈ heapOpenConstraints base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_right _ ?_
      exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have h := hrow _ (hmem _ hin)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
    have h' : (rootPinGate (capOpenCols base.traceWidth) k).eval
        (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by simpa using h
    unfold rootPinGate at h' ⊢
    simp only [EmittedExpr.eval] at h' ⊢
    exact diffGate_exact (hcells _) (hcells _) h'

/-! ## §4 — the AFTER-spine appendix + the trace-FORCED `effHeapWriteV3_forces_write8` (§12 twin). -/

/-- The after-spine heap column layout. `sib`/`dir` SHARED with the read (`capOpenCols w`); `capRoot` IS
the committed AFTER heap-root block (`heapRootGroupCol (EFFECT_VM_WIDTH + B_SPAN)`). -/
def afterSpineColsH (w : Nat) : CapOpenCols :=
  { leaf       := fun i => AFTER_SPINE_BASE w + i.val
  , leafDigest := fun i => AFTER_SPINE_BASE w + 7 + i.val
  , sib        := (capOpenCols w).sib
  , dir        := (capOpenCols w).dir
  , node       := fun lvl i => AFTER_SPINE_BASE w + 15 + 8 * lvl + i.val
  , capRoot    := fun i => Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapRootGroupCol
                             (EFFECT_VM_WIDTH + B_SPAN) i
  , src        := AFTER_SPINE_BASE w + 15 + 8 * DEPTH
  , effBit     := AFTER_SPINE_BASE w + 16 + 8 * DEPTH
  , bit        := fun i => AFTER_SPINE_BASE w + 17 + 8 * DEPTH + i }

theorem afterSpineColsH_dir (w : Nat) : (afterSpineColsH w).dir = (capOpenCols w).dir := rfl

/-- The after `capRoot` group IS the committed AFTER heap-root block. -/
theorem afterSpineH_capRoot_after (w : Nat) (env : VmRowEnv) :
    groupVal env (afterSpineColsH w).capRoot
      = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterHeapRootCols env := rfl

/-- The 3 narrowed-leaf weld gates: after leaf 0 (addr) = the read's addr; after leaf 1 (value) =
`param[VALUE]` (the written value); after leaf 2 (IMT `nextAddr`) = the read's pointer — a value
update HOLDS the pointer fixed (`heap_root.rs::apply_value_update` never re-links the sorted
chain). -/
def afterLeafWeldsH (w : Nat) : List VmConstraint2 :=
  [ .base (.gate (eqGate ((afterSpineColsH w).leaf 0) ((capOpenCols w).leaf 0)))
  , .base (.gate (eqGate ((afterSpineColsH w).leaf 1)
      (prmCol Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.VALUE)))
  , .base (.gate (eqGate ((afterSpineColsH w).leaf 2) ((capOpenCols w).leaf 2))) ]

/-- The 8 BEFORE heap-root weld gates: the read's appendix `capRoot` group equals the committed BEFORE
heap-root block — so `groupVal env (capOpenCols w).capRoot = beforeHeapRootCols env`. -/
def beforeRootWeldsH (w : Nat) : List VmConstraint2 :=
  (List.finRange 8).map (fun i =>
    VmConstraint2.base (.gate (eqGate ((capOpenCols w).capRoot i)
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapRootGroupCol EFFECT_VM_WIDTH i))))

/-- The key-bind gate: the read leaf's `addr` (leaf 0) equals the committed heap-address column
(`HEAP_ADDR` = the MapOp KEY, `hash[coll,key]`) — so the forced 8-felt write is keyed at the SAME address
the deployed splice `MapOp` uses. -/
def keyBindGateH (w : Nat) : EmittedExpr :=
  eqGate ((capOpenCols w).leaf 0) Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.HEAP_ADDR

/-- The after-spine constraint list (appended past the heap-open appendix): the after-leaf absorb, the 16
after-node absorbs, the 8 after root-pins, the 3 narrowed-leaf welds (addr/value/pointer), the 8 before
heap-root welds, and the key bind. -/
def afterSpineConstraintsH (w : Nat) : List VmConstraint2 :=
  .lookup (heapLeafLookup (afterSpineColsH w))
  :: ((List.range DEPTH).map (fun lvl => VmConstraint2.lookup (nodeLookup (afterSpineColsH w) lvl)))
  ++ ((List.finRange 8).map (fun i => VmConstraint2.base (.gate (rootPinGate (afterSpineColsH w) i))))
  ++ afterLeafWeldsH w
  ++ beforeRootWeldsH w
  ++ [VmConstraint2.base (.gate (keyBindGateH w))]

/-- **`effHeapWriteV3 base name`** — the heap-open read descriptor WIDENED by the after-spine appendix: the
deployed heap-write descriptor a light client checks. Its `Satisfied2` FORCES the faithful 8-felt heap-write
(`effHeapWriteV3_forces_write8`). -/
def effHeapWriteV3 (base : EffectVmDescriptor2) (name : String) : EffectVmDescriptor2 :=
  { (effHeapOpenV3 base name) with
    name        := name
    traceWidth  := (effHeapOpenV3 base name).traceWidth + AFTER_SPINE_SPAN
    constraints := (effHeapOpenV3 base name).constraints ++ afterSpineConstraintsH base.traceWidth }

/-- Every after-spine constraint is a constraint of the write descriptor. -/
theorem effHeapWriteV3_afterMem (base : EffectVmDescriptor2) (name : String)
    (c : VmConstraint2) (hc : c ∈ afterSpineConstraintsH base.traceWidth) :
    c ∈ (effHeapWriteV3 base name).constraints :=
  List.mem_append_right _ hc

/-- A `Satisfied2` of the write descriptor strips (constraint-subset) to a `Satisfied2` of the heap-open
read descriptor `effHeapOpenV3` — the after-spine appendix is all `.lookup`/`.base (.gate …)`, reads no base
column and contributes no map/mem op. -/
theorem effHeapWriteV3_strips_to_heapOpen (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (name : String) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (h : Satisfied2 hash (effHeapWriteV3 base name) minit mfin maddrs t) :
    Satisfied2 hash (effHeapOpenV3 base name) minit mfin maddrs t := by
  have hmapOps : Dregg2.Circuit.DescriptorIR2.mapOpsOf (effHeapWriteV3 base name)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf (effHeapOpenV3 base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, effHeapWriteV3, afterSpineConstraintsH,
      afterLeafWeldsH, beforeRootWeldsH, List.filterMap_append, List.filterMap_map, List.filterMap_cons]
  have hmemOps : Dregg2.Circuit.DescriptorIR2.memOpsOf (effHeapWriteV3 base name)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf (effHeapOpenV3 base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, effHeapWriteV3, afterSpineConstraintsH,
      afterLeafWeldsH, beforeRootWeldsH, List.filterMap_append, List.filterMap_map, List.filterMap_cons]
  have hmemLog : Dregg2.Circuit.DescriptorIR2.memLog (effHeapWriteV3 base name) t
      = Dregg2.Circuit.DescriptorIR2.memLog (effHeapOpenV3 base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.memLog, hmemOps]
  have hmapLog : Dregg2.Circuit.DescriptorIR2.mapLog (effHeapWriteV3 base name) t
      = Dregg2.Circuit.DescriptorIR2.mapLog (effHeapOpenV3 base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.mapLog, hmapOps]
  exact
    { rowConstraints := fun i hi c hc =>
        h.rowConstraints i hi c (by
          show c ∈ (effHeapOpenV3 base name).constraints ++ afterSpineConstraintsH base.traceWidth
          exact List.mem_append_left _ hc)
      rowHashes := h.rowHashes
      rowRanges := h.rowRanges
      memAddrsNodup := h.memAddrsNodup
      memClosed := by have := h.memClosed; rwa [hmemLog] at this
      memDisciplined := by have := h.memDisciplined; rwa [hmemLog] at this
      memBalanced := by have := h.memBalanced; rwa [hmemLog] at this
      memTableFaithful := by have := h.memTableFaithful; rwa [hmemLog] at this
      mapTableFaithful := by have := h.mapTableFaithful; rwa [hmapLog] at this }

/-! ### The heap-open APPENDIX-STRIP-TO-BASE bridge (`effHeapWriteV3_satisfied2_strips_to_base`).

The heap-open READ appendix (`heapOpenConstraints`) is all `.lookup`/`.base (.gate …)` — it surfaces NO
map/mem op — so a `Satisfied2` of `effHeapOpenV3 base name` restricts to a `Satisfied2` of the bare
`base` (the appendix reads no base column and contributes no offline-checking op), exactly as the cap
`effCapOpenV3_satisfied2_strips_to_base` does. Composed with `effHeapWriteV3_strips_to_heapOpen`, this
lets the DEPLOYED after-spine `effHeapWriteV3 heapWriteV3 …` (`= Rfix 56`) strip all the way to the
Class-A splice base `heapWriteV3`, so the base-level `heapWrite_*_sat` rungs lift to the apex descriptor. -/

/-- `effHeapOpenV3` gathers exactly `base`'s map ops (the read appendix is all lookups + base gates). -/
theorem effHeapOpenV3_mapOpsOf (base : EffectVmDescriptor2) (name : String) :
    Dregg2.Circuit.DescriptorIR2.mapOpsOf (effHeapOpenV3 base name)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf base := by
  simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, effHeapOpenV3, heapOpenConstraints,
    Dregg2.Circuit.Emit.CapOpenEmit.nodeLookups, Dregg2.Circuit.Emit.CapOpenEmit.dirBoolGates,
    Dregg2.Circuit.Emit.CapOpenEmit.rootPinGates, List.filterMap_append, List.filterMap_map]

/-- `effHeapOpenV3` gathers exactly `base`'s mem ops. -/
theorem effHeapOpenV3_memOpsOf (base : EffectVmDescriptor2) (name : String) :
    Dregg2.Circuit.DescriptorIR2.memOpsOf (effHeapOpenV3 base name)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf base := by
  simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, effHeapOpenV3, heapOpenConstraints,
    Dregg2.Circuit.Emit.CapOpenEmit.nodeLookups, Dregg2.Circuit.Emit.CapOpenEmit.dirBoolGates,
    Dregg2.Circuit.Emit.CapOpenEmit.rootPinGates, List.filterMap_append, List.filterMap_map]

/-- ...so the gathered memory log is `base`'s, op-for-op. -/
theorem effHeapOpenV3_memLog (base : EffectVmDescriptor2) (name : String) (t : VmTrace) :
    Dregg2.Circuit.DescriptorIR2.memLog (effHeapOpenV3 base name) t
      = Dregg2.Circuit.DescriptorIR2.memLog base t := by
  simp [Dregg2.Circuit.DescriptorIR2.memLog, effHeapOpenV3_memOpsOf]

/-- ...and the gathered map log is `base`'s. -/
theorem effHeapOpenV3_mapLog (base : EffectVmDescriptor2) (name : String) (t : VmTrace) :
    Dregg2.Circuit.DescriptorIR2.mapLog (effHeapOpenV3 base name) t
      = Dregg2.Circuit.DescriptorIR2.mapLog base t := by
  simp [Dregg2.Circuit.DescriptorIR2.mapLog, effHeapOpenV3_mapOpsOf]

/-- **`effHeapOpenV3_satisfied2_strips_to_base`** — a `Satisfied2` of the heap-open-widened descriptor
restricts to a `Satisfied2` of the bare `base` (constraint-subset monotonicity + the appendix
contributing no map/mem op). The heap analog of `effCapOpenV3_satisfied2_strips_to_base`. -/
theorem effHeapOpenV3_satisfied2_strips_to_base (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (name : String) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash (effHeapOpenV3 base name) minit mfin maddrs t) :
    Satisfied2 hash base minit mfin maddrs t :=
  { rowConstraints := fun i hi c hc =>
      h.rowConstraints i hi c (by
        show c ∈ base.constraints ++ heapOpenConstraints base.traceWidth
        exact List.mem_append_left _ hc)
    rowHashes := h.rowHashes
    rowRanges := h.rowRanges
    memAddrsNodup := h.memAddrsNodup
    memClosed := by have := h.memClosed; rwa [effHeapOpenV3_memLog] at this
    memDisciplined := by have := h.memDisciplined; rwa [effHeapOpenV3_memLog] at this
    memBalanced := by have := h.memBalanced; rwa [effHeapOpenV3_memLog] at this
    memTableFaithful := by have := h.memTableFaithful; rwa [effHeapOpenV3_memLog] at this
    mapTableFaithful := by have := h.mapTableFaithful; rwa [effHeapOpenV3_mapLog] at this }

/-- **`effHeapWriteV3_satisfied2_strips_to_base`** — THE FULL APEX BRIDGE: a `Satisfied2` of the DEPLOYED
after-spine heap-write `effHeapWriteV3 base name` (the shape `Rfix 56` returns) restricts to a
`Satisfied2` of the bare `base` (the Class-A splice `heapWriteV3`). Composes the after-spine strip
(`effHeapWriteV3_strips_to_heapOpen`) with the read-appendix strip
(`effHeapOpenV3_satisfied2_strips_to_base`) — both appendices are ADDITIVE (all lookups + base gates,
no map/mem op), so the base-level `heapWrite_*_sat` keystones lift to the apex's deployed descriptor. -/
theorem effHeapWriteV3_satisfied2_strips_to_base (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (name : String) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash (effHeapWriteV3 base name) minit mfin maddrs t) :
    Satisfied2 hash base minit mfin maddrs t :=
  effHeapOpenV3_satisfied2_strips_to_base hash base name minit mfin maddrs t
    (effHeapWriteV3_strips_to_heapOpen hash base name minit mfin maddrs t h)

/-- **`effHeapWriteV3_afterCore`** — the AFTER-spine `HeapMembershipCore`, derived from `Satisfied2` of the
write descriptor. The `dirBool` is reused from the read (the SHARED dir column). Field-faithful: the
root-pin gates arrive `≡ 0 [ZMOD p]` and collapse to ℤ through cell canonicality (`(−p, p)` residual). -/
theorem effHeapWriteV3_afterCore (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effHeapWriteV3 base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (hdir : ∀ lvl < DEPTH,
      (dirBoolGate (capOpenCols base.traceWidth) lvl).eval (envAt t i).loc = 0) :
    HeapMembershipCore t.tf (afterSpineColsH base.traceWidth) (envAt t i) := by
  have hrow := hsat.rowConstraints i hi
  have hmem := effHeapWriteV3_afterMem base name
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  refine { leafHashed := ?_, nodeHashed := ?_, dirBool := ?_, rootPinned := ?_ }
  · have hin : VmConstraint2.lookup (heapLeafLookup (afterSpineColsH base.traceWidth))
        ∈ afterSpineConstraintsH base.traceWidth := List.mem_cons_self
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have hin : VmConstraint2.lookup (nodeLookup (afterSpineColsH base.traceWidth) lvl)
        ∈ afterSpineConstraintsH base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ ?_)))
      exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have := hdir lvl hlvl
    exact this
  · intro k
    have hin : VmConstraint2.base (.gate (rootPinGate (afterSpineColsH base.traceWidth) k))
        ∈ afterSpineConstraintsH base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ ?_)))
      exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have h := hrow _ (hmem _ hin)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
    have h' : (rootPinGate (afterSpineColsH base.traceWidth) k).eval
        (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by simpa using h
    unfold rootPinGate at h' ⊢
    simp only [EmittedExpr.eval] at h' ⊢
    exact diffGate_exact (hcells _) (hcells _) h'

/-- Any after-spine `.base (.gate g)` constraint forces `g.eval ≡ 0 [ZMOD p]` on an active (non-last)
row — the field-faithful consequence (`holdsVm` binds under `when_transition`, reduced by `hlastf`). -/
theorem afterSpineH_gate_forces (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effHeapWriteV3 base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (g : EmittedExpr) (hin : VmConstraint2.base (.gate g) ∈ afterSpineConstraintsH base.traceWidth) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi
  have hmem := effHeapWriteV3_afterMem base name
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have h := hrow _ (hmem _ hin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
  simpa using h

/-- An after-spine COLUMN weld (`eqGate a b`) forces the ℤ equality `loc a = loc b` on an active row,
under cell canonicality: the mod-`p` congruence's residual lies in `(−p, p)` and collapses. -/
theorem afterSpineH_eqGate_forces (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effHeapWriteV3 base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (a b : Nat) (hin : VmConstraint2.base (.gate (eqGate a b)) ∈ afterSpineConstraintsH base.traceWidth) :
    (envAt t i).loc a = (envAt t i).loc b := by
  have h := afterSpineH_gate_forces base name hash minit mfin maddrs t hsat i hi hnotlast _ hin
  unfold eqGate at h
  simp only [EmittedExpr.eval] at h
  have := diffGate_exact (hcells a) (hcells b) h
  linarith

/-- **`effHeapWriteV3_forces_write8` — THE STEP-A DELIVERABLE.** A `Satisfied2` of the write descriptor
TRACE-FORCES the faithful 8-felt heap-write over the FULL committed BEFORE/AFTER heap-root blocks: the read
leaf `(addr, oldVal)` is membership-authenticated against the before block, the updated leaf `(addr, VALUE)`
against the after block, along the SHARED path. Forced from `Satisfied2` via the §11 keystone — NEVER from
`henc`'s `SpineCommits`. -/
theorem effHeapWriteV3_forces_write8 (S8 : Heap8Scheme)
    (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (heapPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effHeapWriteV3 base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapWritesTo8 S8
        (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeHeapRootCols (envAt t i))
        ((envAt t i).loc Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.HEAP_ADDR)
        ((envAt t i).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.VALUE))
        (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterHeapRootCols (envAt t i)) := by
  set e := envAt t i with he
  -- the BEFORE membership core (the heap-open read) + its dirBool.
  have hbeforeSat := effHeapWriteV3_strips_to_heapOpen hash base name minit mfin maddrs t hsat
  have hbeforeCore : HeapMembershipCore t.tf (capOpenCols base.traceWidth) e :=
    effHeapOpenV3_core base name hash minit mfin maddrs t hbeforeSat i hi hnotlast hcells
  -- the AFTER membership core (reusing the read's dirBool over the SHARED dir column).
  have hafterCore : HeapMembershipCore t.tf (afterSpineColsH base.traceWidth) e :=
    effHeapWriteV3_afterCore base name hash minit mfin maddrs t hsat i hi hnotlast hcells
      hbeforeCore.dirBool
  -- weld: after leaf 0 (addr) = read leaf 0.
  have hslot : e.loc ((afterSpineColsH base.traceWidth).leaf 0)
      = e.loc ((capOpenCols base.traceWidth).leaf 0) := by
    have hin : VmConstraint2.base (.gate (eqGate ((afterSpineColsH base.traceWidth).leaf 0)
        ((capOpenCols base.traceWidth).leaf 0))) ∈ afterSpineConstraintsH base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      simp [afterLeafWeldsH]
    exact afterSpineH_eqGate_forces base name hash minit mfin maddrs t hsat i hi hnotlast hcells
      _ _ hin
  -- weld: after leaf 1 (value) = param[VALUE].
  have hvalw : e.loc ((afterSpineColsH base.traceWidth).leaf 1)
      = e.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.VALUE) := by
    have hin : VmConstraint2.base (.gate (eqGate ((afterSpineColsH base.traceWidth).leaf 1)
        (prmCol Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.VALUE)))
        ∈ afterSpineConstraintsH base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      simp [afterLeafWeldsH]
    exact afterSpineH_eqGate_forces base name hash minit mfin maddrs t hsat i hi hnotlast hcells
      _ _ hin
  -- weld: after leaf 2 (IMT nextAddr) = read leaf 2 (the value update HOLDS the pointer).
  have hnextw : e.loc ((afterSpineColsH base.traceWidth).leaf 2)
      = e.loc ((capOpenCols base.traceWidth).leaf 2) := by
    have hin : VmConstraint2.base (.gate (eqGate ((afterSpineColsH base.traceWidth).leaf 2)
        ((capOpenCols base.traceWidth).leaf 2))) ∈ afterSpineConstraintsH base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      simp [afterLeafWeldsH]
    exact afterSpineH_eqGate_forces base name hash minit mfin maddrs t hsat i hi hnotlast hcells
      _ _ hin
  -- key bind: read leaf 0 = HEAP_ADDR.
  have hkeyb : e.loc ((capOpenCols base.traceWidth).leaf 0)
      = e.loc Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.HEAP_ADDR := by
    have hin : VmConstraint2.base (.gate (keyBindGateH base.traceWidth))
        ∈ afterSpineConstraintsH base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_right _ ?_
      simp
    exact afterSpineH_eqGate_forces base name hash minit mfin maddrs t hsat i hi hnotlast hcells
      ((capOpenCols base.traceWidth).leaf 0) Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.HEAP_ADDR hin
  -- before-block heap-root weld: the read's appendix capRoot group IS the committed BEFORE block.
  have hbroot : groupVal e (capOpenCols base.traceWidth).capRoot
      = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeHeapRootCols e := by
    funext k
    have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols base.traceWidth).capRoot k)
        (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapRootGroupCol EFFECT_VM_WIDTH k)))
        ∈ afterSpineConstraintsH base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have := afterSpineH_eqGate_forces base name hash minit mfin maddrs t hsat i hi hnotlast hcells
      _ _ hin
    simpa [groupVal, Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeHeapRootCols] using this
  -- assemble the §11 keystone over the two cores along the SHARED path (+ the held pointer).
  have hkey : (heapLeafTripleOf (afterSpineColsH base.traceWidth) e).1
      = (heapLeafTripleOf (capOpenCols base.traceWidth) e).1 := hslot
  have hnext : (heapLeafTripleOf (afterSpineColsH base.traceWidth) e).2.2
      = (heapLeafTripleOf (capOpenCols base.traceWidth) e).2.2 := hnextw
  have hw := heapOpen_writesTo8 S8 t.tf (capOpenCols base.traceWidth)
    (afterSpineColsH base.traceWidth) e hChip hbeforeCore hafterCore rfl rfl hkey hnext
  rw [hbroot] at hw
  rw [afterSpineH_capRoot_after] at hw
  -- rewrite key (before addr → HEAP_ADDR) and value (after value → param VALUE).
  have hkeyb' : (heapLeafTripleOf (capOpenCols base.traceWidth) e).1
      = e.loc Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.HEAP_ADDR := hkeyb
  have hvalw' : (heapLeafTripleOf (afterSpineColsH base.traceWidth) e).2.1
      = e.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.VALUE) := hvalw
  rw [hkeyb', hvalw'] at hw
  exact hw

#assert_axioms effHeapOpenV3_core
#assert_axioms effHeapWriteV3_afterCore
#assert_axioms effHeapWriteV3_forces_write8

end Dregg2.Circuit.Emit.HeapOpenEmit
