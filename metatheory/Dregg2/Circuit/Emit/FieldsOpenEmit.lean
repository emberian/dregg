/-
# Dregg2.Circuit.Emit.FieldsOpenEmit — the LIVE fields-membership open, the THIRD faithful-root after-spine.

The exact twin of `HeapOpenEmit.lean` §11/§12 for the `fields_root` (the THIRD and LAST faithful 8-felt
Merkle root). Where the heap open authenticates a `(addr, value)` leaf at a RUNTIME address (`HEAP_ADDR`),
the fields open authenticates the RESERVED refusal-audit slot at the CONSTANT key `refusalAuditKeyFelt`
against the committed 8-felt fields root — no authority machinery, just membership. The keystone
`fieldsOpen_writesTo8` reduces the faithful 8-felt fields-write to TWO `FieldsMembershipCore` witnesses
sharing a path (before = old leaf against the BEFORE fields-root group; after = in-place-updated leaf, SAME
address, new value, against the AFTER fields-root group), FORCING
`EffectVmEmitRotationV3.fieldsWritesTo8` over the FULL ~124-bit root — NEVER the lane-0 squeeze the fields
GENTIAN tooth (`circuit/tests/fields_root_gentian_weld.rs`) refutes.

REUSE: the node-recompose spine is leaf-AGNOSTIC (`DeployedCapOpen.nodeLookup`/`nodeInputs`/
`nodeInputs_eval`/`dir_zero_or_one` over `CapOpenCols`, rides the ONE `node8` chip), so the fields
membership reuses it verbatim and re-instantiates the digest scheme at `Fields8Scheme` (`fieldsNodeOf8`,
`fieldsLeafDigest8`). The SOLE fields-specific material is the arity-3 IMT leaf absorb (`fieldsLeafLookup`,
`fieldsLeafDigest_sound8`) — the fields leaf is the gap-#5 IMT `(addr, value, nextAddr)`, not a 7-field
`CapLeaf` — and the CONSTANT-key bind (`constEqGate`, the audit slot is keyed at `refusalAuditKeyFelt`,
not a runtime column).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the named WIDE
chip-soundness `ChipTableSoundN (fieldsPermOut S8)`, inherited from `DeployedFieldsTree`/`DeployedCapOpen`.
-/
import Dregg2.Circuit.DeployedCapOpen
import Dregg2.Circuit.DeployedFieldsTree
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.CapOpenEmit

namespace Dregg2.Circuit.Emit.FieldsOpenEmit

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
open Dregg2.Circuit.DeployedFieldsTree (Fields8Scheme)
open Dregg2.Circuit.DeployedFieldsTree.Fields8Scheme (fieldsLeafDigest8 fieldsNodeOf8 recomposeUp8)
open Dregg2.Circuit.CapMerkleGeneric (StepG recomposeG)
open Dregg2.Circuit.Emit.CapOpenEmit
  (capOpenCols nodeLookups dirBoolGates rootPinGates eqGate eqGate_eval
   boolGateCanon_exact diffGate_exact
   CAP_OPEN_SPAN AFTER_SPINE_SPAN AFTER_SPINE_BASE)
open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (B_SPAN)

set_option autoImplicit false

/-! ## §0 — the fields leaf columns + the arity-3 IMT leaf absorb (the SOLE fields-specific chip lookup). -/

/-- The LINKED `(addr, value, nextAddr)` fields leaf read off the row's leaf columns 0/1/2. -/
def fieldsLeafTripleOf (c : CapOpenCols) (env : VmRowEnv) : ℤ × ℤ × ℤ :=
  (env.loc (c.leaf 0), env.loc (c.leaf 1), env.loc (c.leaf 2))

/-- The 3 fields-leaf column EXPRESSIONS `[addr, value, nextAddr]` (the arity-3 chip absorb's input
tuple). -/
def fieldsLeafInputs (c : CapOpenCols) : List EmittedExpr :=
  [EmittedExpr.var (c.leaf 0), EmittedExpr.var (c.leaf 1), EmittedExpr.var (c.leaf 2)]

/-- The fields leaf inputs evaluate to exactly `[addr, value, nextAddr]` of the decoded triple. -/
theorem fieldsLeafInputs_eval (c : CapOpenCols) (env : VmRowEnv) :
    (fieldsLeafInputs c).map (·.eval env.loc)
      = [(fieldsLeafTripleOf c env).1, (fieldsLeafTripleOf c env).2.1,
         (fieldsLeafTripleOf c env).2.2] := by
  simp [fieldsLeafInputs, fieldsLeafTripleOf, EmittedExpr.eval]

/-- **`fieldsPermOut S8`** — the WIDE permutation output the shared `node8` chip realizes for the fields
scheme: the 8 squeezed lanes of `S8.chipAbsorb8` read as a `List ℤ`. -/
def fieldsPermOut (S8 : Fields8Scheme) : List ℤ → List ℤ := fun xs => List.ofFn (S8.chipAbsorb8 xs)

/-- The 8-felt fields-leaf chip lookup tuple: absorb the 3 fields-leaf columns, output = the 8 bound
leaf-digest columns. -/
def fieldsLeafLookup (c : CapOpenCols) : Lookup :=
  { table := .poseidon2, tuple := chipLookupTupleN (fieldsLeafInputs c) (digestCols c.leafDigest) }

-- REGRESSION TOOTH (gap-#5 IMT arity): the emitted fields-leaf lookup absorbs EXACTLY 3 inputs —
-- the deployed `HeapLeaf::digest8` (the fields tree IS a `CanonicalHeapTree8`) absorbs
-- `[addr, value, next_addr]` (arity 3). An arity-2 emit would request a chip row the digest8 provide
-- never has, reddening the honest refusal fields-write path. Pins the arity at emit time.
#guard (fieldsLeafInputs (capOpenCols 100)).length == 3
#guard (fieldsLeafInputs (capOpenCols 100)) == [EmittedExpr.var ((capOpenCols 100).leaf 0),
  EmittedExpr.var ((capOpenCols 100).leaf 1), EmittedExpr.var ((capOpenCols 100).leaf 2)]

/-- A constant-key equality gate: `col − k = 0`, i.e. the column HOLDS the compile-time constant `k`. The
fields audit slot is keyed at the CONSTANT `refusalAuditKeyFelt`, so its key-bind uses this gate (heap used
the runtime `HEAP_ADDR` column via `eqGate`). -/
def constEqGate (col : Nat) (k : ℤ) : EmittedExpr :=
  .add (.var col) (.mul (.const (-1)) (.const k))

theorem constEqGate_eval (col : Nat) (k : ℤ) (env : VmRowEnv) :
    (constEqGate col k).eval env.loc = 0 ↔ env.loc col = k := by
  simp only [constEqGate, EmittedExpr.eval]; constructor <;> intro h <;> linarith

/-! ## §1 — the fields membership core + the node/leaf digest soundness (re-instantiated at `Fields8Scheme`). -/

/-- **`FieldsMembershipCore tf c env`** — the four facts the 8-felt fields Merkle fold consumes: the
arity-3 leaf absorb, the per-level `node8` absorbs (SHARED with cap — the same `nodeLookup`), direction
booleanity, and the (8-lane) root pin. The fields twin of `DeployedCapOpen.MembershipCore`. -/
structure FieldsMembershipCore (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv) : Prop where
  leafHashed : (fieldsLeafLookup c).holdsAt tf env
  nodeHashed : ∀ lvl < DEPTH, (nodeLookup c lvl).holdsAt tf env
  dirBool    : ∀ lvl < DEPTH, (dirBoolGate c lvl).eval env.loc = 0
  rootPinned : ∀ i : Fin 8, (rootPinGate c i).eval env.loc = 0

/-- **`fieldsLeafDigest_sound8`** — under a SOUND WIDE chip table, the 8 leaf-digest columns carry the
genuine native-8-felt `fieldsLeafDigest8 S8 (addr, value, nextAddr)`. The fields twin of
`heapLeafDigest_sound8` (arity-3 IMT leaf). -/
theorem fieldsLeafDigest_sound8 (S8 : Fields8Scheme)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (tf .poseidon2))
    (hcore : FieldsMembershipCore tf c env) :
    groupVal env c.leafDigest = fieldsLeafDigest8 S8 (fieldsLeafTripleOf c env) := by
  have hlen : ChipArityAdmitted (fieldsLeafInputs c).length := of_decide_eq_true (Eq.refl true)
  have hmem : (chipLookupTupleN (fieldsLeafInputs c) (digestCols c.leafDigest)).map (·.eval env.loc)
      ∈ tf .poseidon2 := by
    have := hcore.leafHashed
    unfold Lookup.holdsAt fieldsLeafLookup at this
    exact this
  have h := chip_lookup_sound_N (fieldsPermOut S8) (tf .poseidon2) hChip env.loc (fieldsLeafInputs c)
    (digestCols c.leafDigest) hlen hmem
  rw [digestCols_map, fieldsLeafInputs_eval] at h
  have hreal : fieldsPermOut S8 [(fieldsLeafTripleOf c env).1, (fieldsLeafTripleOf c env).2.1,
      (fieldsLeafTripleOf c env).2.2]
      = List.ofFn (fieldsLeafDigest8 S8 (fieldsLeafTripleOf c env)) := rfl
  rw [hreal] at h
  exact List.ofFn_inj.mp h

/-- **`fieldsNode_sound8`** — under a SOUND WIDE chip table, level `lvl`'s 8 node columns carry the genuine
native-8-felt `fieldsNodeOf8 S8` of the dir-mixed `(cur8, sib8)` pair. Reuses the SHARED `nodeInputs_eval`. -/
theorem fieldsNode_sound8 (S8 : Fields8Scheme)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (tf .poseidon2))
    (hcore : FieldsMembershipCore tf c env) (lvl : Nat) (hlvl : lvl < DEPTH) :
    groupVal env (c.node lvl)
      = (if dirBoolVal c env lvl
          then fieldsNodeOf8 S8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl))
          else fieldsNodeOf8 S8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl))) := by
  have hlen : ChipArityAdmitted (nodeInputs c lvl).length := of_decide_eq_true (Eq.refl true)
  have hmem : (chipLookupTupleN (nodeInputs c lvl) (digestCols (c.node lvl))).map (·.eval env.loc)
      ∈ tf .poseidon2 := by
    have := hcore.nodeHashed lvl hlvl
    unfold Lookup.holdsAt nodeLookup at this
    exact this
  have h := chip_lookup_sound_N (fieldsPermOut S8) (tf .poseidon2) hChip env.loc (nodeInputs c lvl)
    (digestCols (c.node lvl)) hlen hmem
  rw [digestCols_map, nodeInputs_eval c env lvl (dir_zero_or_one c env lvl (hcore.dirBool lvl hlvl))] at h
  cases hb : dirBoolVal c env lvl
  · simp only [hb, Bool.false_eq_true, if_false] at h ⊢
    have hreal : fieldsPermOut S8 (pack8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl)))
        = List.ofFn (fieldsNodeOf8 S8 (groupVal env (curCol c lvl)) (groupVal env (c.sib lvl))) := rfl
    rw [hreal] at h
    exact List.ofFn_inj.mp h
  · simp only [hb, if_true] at h ⊢
    have hreal : fieldsPermOut S8 (pack8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl)))
        = List.ofFn (fieldsNodeOf8 S8 (groupVal env (c.sib lvl)) (groupVal env (curCol c lvl))) := rfl
    rw [hreal] at h
    exact List.ofFn_inj.mp h

/-- `recomposeUp8` (fields scheme) distributes over a path append (over the generic `recomposeG` spine). -/
theorem fieldsRecomposeUp8_append (S8 : Fields8Scheme) (cur : Digest8) (p q : List (StepG Digest8)) :
    recomposeUp8 S8 cur (p ++ q) = recomposeUp8 S8 (recomposeUp8 S8 cur p) q := by
  show recomposeG (fieldsNodeOf8 S8) cur (p ++ q)
     = recomposeG (fieldsNodeOf8 S8) (recomposeG (fieldsNodeOf8 S8) cur p) q
  induction p generalizing cur with
  | nil => rfl
  | cons s rest ih => simp only [List.cons_append, recomposeG]; rw [ih]

/-- Folding `recomposeUp8` over the first `n` levels reproduces `curCol c n`, under the WIDE chip
soundness — the native 8-felt fields fold. The fields twin of `heapRecompose_reaches_cur8`. -/
theorem fieldsRecompose_reaches_cur8 (S8 : Fields8Scheme)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (tf .poseidon2))
    (hcore : FieldsMembershipCore tf c env) :
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
    rw [hpath, fieldsRecomposeUp8_append, ih hkle]
    simp only [recomposeUp8, recomposeG]
    have hns := fieldsNode_sound8 S8 tf c env hChip hcore k hkd
    have hcur : curCol c (k + 1) = c.node k := rfl
    rw [hcur]
    cases hb : dirBoolVal c env k
    · simp only [hb, Bool.false_eq_true, if_false] at hns ⊢
      rw [hns]
    · simp only [hb, if_true] at hns ⊢
      rw [hns]

/-! ## §2 — the recompose from a single core + the STEP-A keystone `fieldsOpen_writesTo8`. -/

/-- **`fieldsOpen_recompose8`** — the explicit before/after recompose: the leaf's native-8-felt fields
digest recomposes the committed 8-felt fields-root GROUP along the column-read path. -/
theorem fieldsOpen_recompose8 (S8 : Fields8Scheme)
    (tf : TraceFamily) (c : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (tf .poseidon2))
    (hcore : FieldsMembershipCore tf c env) :
    recomposeUp8 S8 (fieldsLeafDigest8 S8 (fieldsLeafTripleOf c env)) (pathOf8 c env DEPTH)
      = groupVal env c.capRoot := by
  have hfold := fieldsRecompose_reaches_cur8 S8 tf c env hChip hcore DEPTH (le_refl _)
  have hleaf := fieldsLeafDigest_sound8 S8 tf c env hChip hcore
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

/-- **`fieldsOpen_writesTo8` — THE STEP-A KEYSTONE.** Two `FieldsMembershipCore` witnesses sharing the
sibling path FORCE the faithful 8-felt `fieldsWritesTo8` over the FULL ~124-bit root — NOT the lane-0
projection. Trace-forced: the witnesses come from `Satisfied2`, never from `henc`'s `SpineCommits`. -/
theorem fieldsOpen_writesTo8 (S8 : Fields8Scheme)
    (tf : TraceFamily) (cBefore cAfter : CapOpenCols) (env : VmRowEnv)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (tf .poseidon2))
    (hBefore : FieldsMembershipCore tf cBefore env)
    (hAfter  : FieldsMembershipCore tf cAfter env)
    (hsib : cAfter.sib = cBefore.sib)
    (hdir : cAfter.dir = cBefore.dir)
    (hkey : (fieldsLeafTripleOf cAfter env).1 = (fieldsLeafTripleOf cBefore env).1)
    (hnext : (fieldsLeafTripleOf cAfter env).2.2 = (fieldsLeafTripleOf cBefore env).2.2) :
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.fieldsWritesTo8 S8
        (groupVal env cBefore.capRoot)
        ((fieldsLeafTripleOf cBefore env).1) ((fieldsLeafTripleOf cAfter env).2.1)
        (groupVal env cAfter.capRoot) := by
  refine ⟨(fieldsLeafTripleOf cBefore env).2.1, (fieldsLeafTripleOf cBefore env).2.2,
    pathOf8 cBefore env DEPTH, ?_, ?_⟩
  · have hrec := fieldsOpen_recompose8 S8 tf cBefore env hChip hBefore
    simpa using hrec
  · have hpath : pathOf8 cAfter env DEPTH = pathOf8 cBefore env DEPTH := by
      simp only [pathOf8, dirBoolVal, hsib, hdir]
    have hrec := fieldsOpen_recompose8 S8 tf cAfter env hChip hAfter
    rw [hpath] at hrec
    have htriple : fieldsLeafTripleOf cAfter env
        = ((fieldsLeafTripleOf cBefore env).1, (fieldsLeafTripleOf cAfter env).2.1,
           (fieldsLeafTripleOf cBefore env).2.2) := by
      rw [← hkey, ← hnext]
    rw [htriple] at hrec
    exact hrec

#assert_axioms fieldsLeafDigest_sound8
#assert_axioms fieldsNode_sound8
#assert_axioms fieldsRecompose_reaches_cur8
#assert_axioms fieldsOpen_recompose8
#assert_axioms fieldsOpen_writesTo8

/-! ## §3 — the fields-open READ appendix + the before-membership core (`effFieldsOpenV3`). -/

/-- **`fieldsOpenConstraints w`** — the fields-open read constraint list: the arity-3 leaf lookup, the 16
node lookups (SHARED with cap — the same `nodeLookup`), the 16 dir gates, and the 8 root-pin gates. -/
def fieldsOpenConstraints (w : Nat) : List VmConstraint2 :=
  .lookup (fieldsLeafLookup (capOpenCols w))
  :: nodeLookups w
  ++ dirBoolGates w
  ++ rootPinGates w

/-- **`effFieldsOpenV3 base name`** — the per-effect fields-open descriptor: a rotated base widened by the
fields-open appendix at `base.traceWidth`, carrying `fieldsOpenConstraints`. -/
def effFieldsOpenV3 (base : EffectVmDescriptor2) (name : String) : EffectVmDescriptor2 :=
  { base with
    name        := name
    traceWidth  := base.traceWidth + CAP_OPEN_SPAN
    constraints := base.constraints ++ fieldsOpenConstraints base.traceWidth }

/-- Every fields-open constraint is a constraint of the descriptor. -/
theorem effFieldsOpenV3_constraints_mem (base : EffectVmDescriptor2) (name : String)
    (c : VmConstraint2) (hc : c ∈ fieldsOpenConstraints base.traceWidth) :
    c ∈ (effFieldsOpenV3 base name).constraints :=
  List.mem_append_right _ hc

/-- **`effFieldsOpenV3_core`** — a `Satisfied2` of the fields-open descriptor rebuilds
`FieldsMembershipCore` on every active (non-last) row. The fields twin of `effHeapOpenV3_core`.
Field-faithful: the lookups lift untouched; the gates arrive `≡ 0 [ZMOD p]` (`holdsVm`) and lift to
their ℤ form through cell canonicality — primality (`dirBool`) / the `(−p, p)` residual collapse
(`rootPinned`). -/
theorem effFieldsOpenV3_core (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effFieldsOpenV3 base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    FieldsMembershipCore t.tf (capOpenCols base.traceWidth) (envAt t i) := by
  have hrow := hsat.rowConstraints i hi
  have hmem := effFieldsOpenV3_constraints_mem base name
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  refine { leafHashed := ?_, nodeHashed := ?_, dirBool := ?_, rootPinned := ?_ }
  · have hin : VmConstraint2.lookup (fieldsLeafLookup (capOpenCols base.traceWidth))
        ∈ fieldsOpenConstraints base.traceWidth := List.mem_cons_self
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have hin : VmConstraint2.lookup (nodeLookup (capOpenCols base.traceWidth) lvl)
        ∈ fieldsOpenConstraints base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have hin : VmConstraint2.base (.gate (dirBoolGate (capOpenCols base.traceWidth) lvl))
        ∈ fieldsOpenConstraints base.traceWidth := by
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
        ∈ fieldsOpenConstraints base.traceWidth := by
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

/-! ## §4 — the AFTER-spine appendix + the trace-FORCED `effFieldsWriteV3_forces_write8` (§12 twin). -/

/-- The after-spine fields column layout. `sib`/`dir` SHARED with the read; `capRoot` IS the committed
AFTER fields-root block (`fieldsRootGroupCol (EFFECT_VM_WIDTH + B_SPAN)`). -/
def afterSpineColsF (w : Nat) : CapOpenCols :=
  { leaf       := fun i => AFTER_SPINE_BASE w + i.val
  , leafDigest := fun i => AFTER_SPINE_BASE w + 7 + i.val
  , sib        := (capOpenCols w).sib
  , dir        := (capOpenCols w).dir
  , node       := fun lvl i => AFTER_SPINE_BASE w + 15 + 8 * lvl + i.val
  , capRoot    := fun i => Dregg2.Circuit.Emit.EffectVmEmitRotationV3.fieldsRootGroupCol
                             (EFFECT_VM_WIDTH + B_SPAN) i
  , src        := AFTER_SPINE_BASE w + 15 + 8 * DEPTH
  , effBit     := AFTER_SPINE_BASE w + 16 + 8 * DEPTH
  , bit        := fun i => AFTER_SPINE_BASE w + 17 + 8 * DEPTH + i }

theorem afterSpineColsF_dir (w : Nat) : (afterSpineColsF w).dir = (capOpenCols w).dir := rfl

/-- The after `capRoot` group IS the committed AFTER fields-root block. -/
theorem afterSpineF_capRoot_after (w : Nat) (env : VmRowEnv) :
    groupVal env (afterSpineColsF w).capRoot
      = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterFieldsRootCols env := rfl

/-- The 3 narrowed-leaf weld gates: after leaf 0 (addr) = the read's addr; after leaf 1 (value) =
`REFUSAL_AUDIT_FELT_COL` (the audit felt the write inserts); after leaf 2 (IMT `nextAddr`) = the read's
pointer (the value update HOLDS the sorted-chain pointer fixed). -/
def afterLeafWeldsF (w : Nat) : List VmConstraint2 :=
  [ .base (.gate (eqGate ((afterSpineColsF w).leaf 0) ((capOpenCols w).leaf 0)))
  , .base (.gate (eqGate ((afterSpineColsF w).leaf 1)
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.REFUSAL_AUDIT_FELT_COL))
  , .base (.gate (eqGate ((afterSpineColsF w).leaf 2) ((capOpenCols w).leaf 2))) ]

/-- The 8 BEFORE fields-root weld gates: the read's appendix `capRoot` group equals the committed BEFORE
fields-root block. -/
def beforeRootWeldsF (w : Nat) : List VmConstraint2 :=
  (List.finRange 8).map (fun i =>
    VmConstraint2.base (.gate (eqGate ((capOpenCols w).capRoot i)
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.fieldsRootGroupCol EFFECT_VM_WIDTH i))))

/-- The CONSTANT-key bind gate: the read leaf's `addr` (leaf 0) equals `refusalAuditKeyFelt` (the reserved
audit slot key). Unlike heap's runtime `HEAP_ADDR`, the fields audit write is keyed at a compile-time
constant. -/
def keyBindGateF (w : Nat) : EmittedExpr :=
  constEqGate ((capOpenCols w).leaf 0) Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalAuditKeyFelt

/-- The after-spine constraint list (appended past the fields-open appendix). -/
def afterSpineConstraintsF (w : Nat) : List VmConstraint2 :=
  .lookup (fieldsLeafLookup (afterSpineColsF w))
  :: ((List.range DEPTH).map (fun lvl => VmConstraint2.lookup (nodeLookup (afterSpineColsF w) lvl)))
  ++ ((List.finRange 8).map (fun i => VmConstraint2.base (.gate (rootPinGate (afterSpineColsF w) i))))
  ++ afterLeafWeldsF w
  ++ beforeRootWeldsF w
  ++ [VmConstraint2.base (.gate (keyBindGateF w))]

/-- **`effFieldsWriteV3 base name`** — the fields-open read descriptor WIDENED by the after-spine appendix:
the deployed fields-write descriptor a light client checks. Its `Satisfied2` FORCES the faithful 8-felt
fields-write (`effFieldsWriteV3_forces_write8`). -/
def effFieldsWriteV3 (base : EffectVmDescriptor2) (name : String) : EffectVmDescriptor2 :=
  { (effFieldsOpenV3 base name) with
    name        := name
    traceWidth  := (effFieldsOpenV3 base name).traceWidth + AFTER_SPINE_SPAN
    constraints := (effFieldsOpenV3 base name).constraints ++ afterSpineConstraintsF base.traceWidth }

/-- Every after-spine constraint is a constraint of the write descriptor. -/
theorem effFieldsWriteV3_afterMem (base : EffectVmDescriptor2) (name : String)
    (c : VmConstraint2) (hc : c ∈ afterSpineConstraintsF base.traceWidth) :
    c ∈ (effFieldsWriteV3 base name).constraints :=
  List.mem_append_right _ hc

/-- A `Satisfied2` of the write descriptor strips (constraint-subset) to a `Satisfied2` of the fields-open
read descriptor `effFieldsOpenV3` — the after-spine appendix is all `.lookup`/`.base (.gate …)`, reads no
base column and contributes no map/mem op. -/
theorem effFieldsWriteV3_strips_to_fieldsOpen (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (name : String) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (h : Satisfied2 hash (effFieldsWriteV3 base name) minit mfin maddrs t) :
    Satisfied2 hash (effFieldsOpenV3 base name) minit mfin maddrs t := by
  have hmapOps : Dregg2.Circuit.DescriptorIR2.mapOpsOf (effFieldsWriteV3 base name)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf (effFieldsOpenV3 base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, effFieldsWriteV3, afterSpineConstraintsF,
      afterLeafWeldsF, beforeRootWeldsF, List.filterMap_append, List.filterMap_map]
  have hmemOps : Dregg2.Circuit.DescriptorIR2.memOpsOf (effFieldsWriteV3 base name)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf (effFieldsOpenV3 base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, effFieldsWriteV3, afterSpineConstraintsF,
      afterLeafWeldsF, beforeRootWeldsF, List.filterMap_append, List.filterMap_map]
  have hmemLog : Dregg2.Circuit.DescriptorIR2.memLog (effFieldsWriteV3 base name) t
      = Dregg2.Circuit.DescriptorIR2.memLog (effFieldsOpenV3 base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.memLog, hmemOps]
  have hmapLog : Dregg2.Circuit.DescriptorIR2.mapLog (effFieldsWriteV3 base name) t
      = Dregg2.Circuit.DescriptorIR2.mapLog (effFieldsOpenV3 base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.mapLog, hmapOps]
  exact
    { rowConstraints := fun i hi c hc =>
        h.rowConstraints i hi c (by
          show c ∈ (effFieldsOpenV3 base name).constraints ++ afterSpineConstraintsF base.traceWidth
          exact List.mem_append_left _ hc)
      rowHashes := h.rowHashes
      rowRanges := h.rowRanges
      memAddrsNodup := h.memAddrsNodup
      memClosed := by have := h.memClosed; rwa [hmemLog] at this
      memDisciplined := by have := h.memDisciplined; rwa [hmemLog] at this
      memBalanced := by have := h.memBalanced; rwa [hmemLog] at this
      memTableFaithful := by have := h.memTableFaithful; rwa [hmemLog] at this
      mapTableFaithful := by have := h.mapTableFaithful; rwa [hmapLog] at this }

/-- `effFieldsOpenV3` gathers exactly `base`'s map ops (the read appendix is all lookups + base gates). -/
theorem effFieldsOpenV3_mapOpsOf (base : EffectVmDescriptor2) (name : String) :
    Dregg2.Circuit.DescriptorIR2.mapOpsOf (effFieldsOpenV3 base name)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf base := by
  simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, effFieldsOpenV3, fieldsOpenConstraints,
    Dregg2.Circuit.Emit.CapOpenEmit.nodeLookups, Dregg2.Circuit.Emit.CapOpenEmit.dirBoolGates,
    Dregg2.Circuit.Emit.CapOpenEmit.rootPinGates, List.filterMap_append, List.filterMap_map]

/-- `effFieldsOpenV3` gathers exactly `base`'s mem ops. -/
theorem effFieldsOpenV3_memOpsOf (base : EffectVmDescriptor2) (name : String) :
    Dregg2.Circuit.DescriptorIR2.memOpsOf (effFieldsOpenV3 base name)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf base := by
  simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, effFieldsOpenV3, fieldsOpenConstraints,
    Dregg2.Circuit.Emit.CapOpenEmit.nodeLookups, Dregg2.Circuit.Emit.CapOpenEmit.dirBoolGates,
    Dregg2.Circuit.Emit.CapOpenEmit.rootPinGates, List.filterMap_append, List.filterMap_map]

/-- ...so the gathered memory log is `base`'s, op-for-op. -/
theorem effFieldsOpenV3_memLog (base : EffectVmDescriptor2) (name : String) (t : VmTrace) :
    Dregg2.Circuit.DescriptorIR2.memLog (effFieldsOpenV3 base name) t
      = Dregg2.Circuit.DescriptorIR2.memLog base t := by
  simp [Dregg2.Circuit.DescriptorIR2.memLog, effFieldsOpenV3_memOpsOf]

/-- ...and the gathered map log is `base`'s. -/
theorem effFieldsOpenV3_mapLog (base : EffectVmDescriptor2) (name : String) (t : VmTrace) :
    Dregg2.Circuit.DescriptorIR2.mapLog (effFieldsOpenV3 base name) t
      = Dregg2.Circuit.DescriptorIR2.mapLog base t := by
  simp [Dregg2.Circuit.DescriptorIR2.mapLog, effFieldsOpenV3_mapOpsOf]

/-- **`effFieldsOpenV3_satisfied2_strips_to_base`** — a `Satisfied2` of the fields-open-widened descriptor
restricts to a `Satisfied2` of the bare `base`. The fields analog of `effHeapOpenV3_satisfied2_strips_to_base`. -/
theorem effFieldsOpenV3_satisfied2_strips_to_base (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (name : String) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash (effFieldsOpenV3 base name) minit mfin maddrs t) :
    Satisfied2 hash base minit mfin maddrs t :=
  { rowConstraints := fun i hi c hc =>
      h.rowConstraints i hi c (by
        show c ∈ base.constraints ++ fieldsOpenConstraints base.traceWidth
        exact List.mem_append_left _ hc)
    rowHashes := h.rowHashes
    rowRanges := h.rowRanges
    memAddrsNodup := h.memAddrsNodup
    memClosed := by have := h.memClosed; rwa [effFieldsOpenV3_memLog] at this
    memDisciplined := by have := h.memDisciplined; rwa [effFieldsOpenV3_memLog] at this
    memBalanced := by have := h.memBalanced; rwa [effFieldsOpenV3_memLog] at this
    memTableFaithful := by have := h.memTableFaithful; rwa [effFieldsOpenV3_memLog] at this
    mapTableFaithful := by have := h.mapTableFaithful; rwa [effFieldsOpenV3_mapLog] at this }

/-- **`effFieldsWriteV3_satisfied2_strips_to_base`** — THE FULL APEX BRIDGE. -/
theorem effFieldsWriteV3_satisfied2_strips_to_base (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (name : String) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash (effFieldsWriteV3 base name) minit mfin maddrs t) :
    Satisfied2 hash base minit mfin maddrs t :=
  effFieldsOpenV3_satisfied2_strips_to_base hash base name minit mfin maddrs t
    (effFieldsWriteV3_strips_to_fieldsOpen hash base name minit mfin maddrs t h)

/-- **`effFieldsWriteV3_afterCore`** — the AFTER-spine `FieldsMembershipCore`, derived from `Satisfied2` of
the write descriptor. The `dirBool` is reused from the read (the SHARED dir column). Field-faithful: the
root-pin gates arrive `≡ 0 [ZMOD p]` and collapse to ℤ through cell canonicality (`(−p, p)` residual). -/
theorem effFieldsWriteV3_afterCore (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effFieldsWriteV3 base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (hdir : ∀ lvl < DEPTH,
      (dirBoolGate (capOpenCols base.traceWidth) lvl).eval (envAt t i).loc = 0) :
    FieldsMembershipCore t.tf (afterSpineColsF base.traceWidth) (envAt t i) := by
  have hrow := hsat.rowConstraints i hi
  have hmem := effFieldsWriteV3_afterMem base name
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  refine { leafHashed := ?_, nodeHashed := ?_, dirBool := ?_, rootPinned := ?_ }
  · have hin : VmConstraint2.lookup (fieldsLeafLookup (afterSpineColsF base.traceWidth))
        ∈ afterSpineConstraintsF base.traceWidth := List.mem_cons_self
    have h := hrow _ (hmem _ hin)
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have hin : VmConstraint2.lookup (nodeLookup (afterSpineColsF base.traceWidth) lvl)
        ∈ afterSpineConstraintsF base.traceWidth := by
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
    have hin : VmConstraint2.base (.gate (rootPinGate (afterSpineColsF base.traceWidth) k))
        ∈ afterSpineConstraintsF base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ ?_)))
      exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have h := hrow _ (hmem _ hin)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
    have h' : (rootPinGate (afterSpineColsF base.traceWidth) k).eval
        (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by simpa using h
    unfold rootPinGate at h' ⊢
    simp only [EmittedExpr.eval] at h' ⊢
    exact diffGate_exact (hcells _) (hcells _) h'

/-- Any after-spine `.base (.gate g)` constraint forces `g.eval ≡ 0 [ZMOD p]` on an active (non-last)
row — the field-faithful consequence (`holdsVm` binds under `when_transition`, reduced by `hlastf`). -/
theorem afterSpineF_gate_forces (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effFieldsWriteV3 base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (g : EmittedExpr) (hin : VmConstraint2.base (.gate g) ∈ afterSpineConstraintsF base.traceWidth) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi
  have hmem := effFieldsWriteV3_afterMem base name
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have h := hrow _ (hmem _ hin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
  simpa using h

/-- An after-spine COLUMN weld (`eqGate a b`) forces the ℤ equality `loc a = loc b` on an active row,
under cell canonicality: the mod-`p` congruence's residual lies in `(−p, p)` and collapses. -/
theorem afterSpineF_eqGate_forces (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effFieldsWriteV3 base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (a b : Nat) (hin : VmConstraint2.base (.gate (eqGate a b)) ∈ afterSpineConstraintsF base.traceWidth) :
    (envAt t i).loc a = (envAt t i).loc b := by
  have h := afterSpineF_gate_forces base name hash minit mfin maddrs t hsat i hi hnotlast _ hin
  unfold eqGate at h
  simp only [EmittedExpr.eval] at h
  have := diffGate_exact (hcells a) (hcells b) h
  linarith

/-- **`effFieldsWriteV3_forces_write8` — THE STEP-A DELIVERABLE.** A `Satisfied2` of the write descriptor
TRACE-FORCES the faithful 8-felt fields-write over the FULL committed BEFORE/AFTER fields-root blocks: the
read leaf `(refusalAuditKeyFelt, oldVal)` is membership-authenticated against the before block, the updated
leaf `(refusalAuditKeyFelt, REFUSAL_AUDIT_FELT_COL)` against the after block, along the SHARED path. Forced
from `Satisfied2` via the §11 keystone — NEVER from `henc`'s `SpineCommits`. -/
theorem effFieldsWriteV3_forces_write8 (S8 : Fields8Scheme)
    (base : EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effFieldsWriteV3 base name) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.fieldsWritesTo8 S8
        (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols (envAt t i))
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalAuditKeyFelt
        ((envAt t i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.REFUSAL_AUDIT_FELT_COL)
        (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterFieldsRootCols (envAt t i)) := by
  set e := envAt t i with he
  have hbeforeSat := effFieldsWriteV3_strips_to_fieldsOpen hash base name minit mfin maddrs t hsat
  have hbeforeCore : FieldsMembershipCore t.tf (capOpenCols base.traceWidth) e :=
    effFieldsOpenV3_core base name hash minit mfin maddrs t hbeforeSat i hi hnotlast hcells
  have hafterCore : FieldsMembershipCore t.tf (afterSpineColsF base.traceWidth) e :=
    effFieldsWriteV3_afterCore base name hash minit mfin maddrs t hsat i hi hnotlast hcells
      hbeforeCore.dirBool
  -- weld: after leaf 0 (addr) = read leaf 0.
  have hslot : e.loc ((afterSpineColsF base.traceWidth).leaf 0)
      = e.loc ((capOpenCols base.traceWidth).leaf 0) := by
    have hin : VmConstraint2.base (.gate (eqGate ((afterSpineColsF base.traceWidth).leaf 0)
        ((capOpenCols base.traceWidth).leaf 0))) ∈ afterSpineConstraintsF base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      simp [afterLeafWeldsF]
    exact afterSpineF_eqGate_forces base name hash minit mfin maddrs t hsat i hi hnotlast hcells
      _ _ hin
  -- weld: after leaf 1 (value) = REFUSAL_AUDIT_FELT_COL.
  have hvalw : e.loc ((afterSpineColsF base.traceWidth).leaf 1)
      = e.loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.REFUSAL_AUDIT_FELT_COL := by
    have hin : VmConstraint2.base (.gate (eqGate ((afterSpineColsF base.traceWidth).leaf 1)
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.REFUSAL_AUDIT_FELT_COL))
        ∈ afterSpineConstraintsF base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      simp [afterLeafWeldsF]
    exact afterSpineF_eqGate_forces base name hash minit mfin maddrs t hsat i hi hnotlast hcells
      _ _ hin
  -- weld: after leaf 2 (IMT nextAddr) = read leaf 2 (the value update HOLDS the pointer).
  have hnextw : e.loc ((afterSpineColsF base.traceWidth).leaf 2)
      = e.loc ((capOpenCols base.traceWidth).leaf 2) := by
    have hin : VmConstraint2.base (.gate (eqGate ((afterSpineColsF base.traceWidth).leaf 2)
        ((capOpenCols base.traceWidth).leaf 2))) ∈ afterSpineConstraintsF base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      simp [afterLeafWeldsF]
    exact afterSpineF_eqGate_forces base name hash minit mfin maddrs t hsat i hi hnotlast hcells
      _ _ hin
  -- key bind: read leaf 0 = refusalAuditKeyFelt (const).
  have hkeyb : e.loc ((capOpenCols base.traceWidth).leaf 0)
      = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalAuditKeyFelt := by
    have hin : VmConstraint2.base (.gate (keyBindGateF base.traceWidth))
        ∈ afterSpineConstraintsF base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_right _ ?_
      simp
    have h := afterSpineF_gate_forces base name hash minit mfin maddrs t hsat i hi hnotlast _ hin
    -- the CONSTANT `refusalAuditKeyFelt = 529176517` is a canonical field element, so the
    -- constant-pin residual lies in `(−p, p)` and collapses to the ℤ equality.
    have hz : (keyBindGateF base.traceWidth).eval e.loc = 0 := by
      unfold keyBindGateF constEqGate at h ⊢
      simp only [EmittedExpr.eval] at h ⊢
      exact diffGate_exact (hcells _)
        ⟨by norm_num [Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalAuditKeyFelt],
         by norm_num [Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalAuditKeyFelt]⟩ h
    exact (constEqGate_eval _ _ e).mp hz
  -- before-block fields-root weld: the read's appendix capRoot group IS the committed BEFORE block.
  have hbroot : groupVal e (capOpenCols base.traceWidth).capRoot
      = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols e := by
    funext k
    have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols base.traceWidth).capRoot k)
        (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.fieldsRootGroupCol EFFECT_VM_WIDTH k)))
        ∈ afterSpineConstraintsF base.traceWidth := by
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have := afterSpineF_eqGate_forces base name hash minit mfin maddrs t hsat i hi hnotlast hcells
      _ _ hin
    simpa [groupVal, Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols] using this
  -- assemble the §11 keystone over the two cores along the SHARED path (+ the held pointer).
  have hkey : (fieldsLeafTripleOf (afterSpineColsF base.traceWidth) e).1
      = (fieldsLeafTripleOf (capOpenCols base.traceWidth) e).1 := hslot
  have hnext : (fieldsLeafTripleOf (afterSpineColsF base.traceWidth) e).2.2
      = (fieldsLeafTripleOf (capOpenCols base.traceWidth) e).2.2 := hnextw
  have hw := fieldsOpen_writesTo8 S8 t.tf (capOpenCols base.traceWidth)
    (afterSpineColsF base.traceWidth) e hChip hbeforeCore hafterCore rfl rfl hkey hnext
  rw [hbroot] at hw
  rw [afterSpineF_capRoot_after] at hw
  have hkeyb' : (fieldsLeafTripleOf (capOpenCols base.traceWidth) e).1
      = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalAuditKeyFelt := hkeyb
  have hvalw' : (fieldsLeafTripleOf (afterSpineColsF base.traceWidth) e).2.1
      = e.loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.REFUSAL_AUDIT_FELT_COL := hvalw
  rw [hkeyb', hvalw'] at hw
  exact hw

#assert_axioms effFieldsOpenV3_core
#assert_axioms effFieldsWriteV3_afterCore
#assert_axioms effFieldsWriteV3_forces_write8

end Dregg2.Circuit.Emit.FieldsOpenEmit
