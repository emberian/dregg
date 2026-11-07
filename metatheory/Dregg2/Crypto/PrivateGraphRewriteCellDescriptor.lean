/-
# Dregg2.Crypto.PrivateGraphRewriteCellDescriptor

The platform custom-cell wrapper for the reusable bounded private graph-rewrite
relation.  `PrivateGraphRewriteDescriptor` keeps its compact 29-PI receipt ABI;
this descriptor prepends the mandatory sixteen-felt cell-state door:

  [cellOldCommit8, cellNewCommit8,
   domain, session, version, shape, index,
   rulesetRoot8, graphOldRoot8, graphNewRoot8].

The platform recursion carrier welds PI 0..16 to the real rotated cell roots and
PI 37..45 (`graphNewRoot8`) to committed post-state fields 0..7.  The latter is
the application-root weld: a light client learns that the semantic graph output
proved here is the graph root the cell actually stored.  History linkage binds
the next receipt's `graphOldRoot8` to this output.

This wrapper copies no semantic equations.  It imports the base relation's
hash/range/gate/boundary lists verbatim and changes only PI placement plus the
two state-root columns.  The theorems below pin the complete ABI and state that
every non-PI base constraint remains literally a wrapper constraint.
-/
import Dregg2.Crypto.PrivateGraphRewriteDescriptor

namespace Dregg2.Crypto.PrivateGraphRewriteCellDescriptor

open Dregg2.Crypto.PrivateGraphRewriteDescriptor
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily Satisfied2 emitVmJson2
   rangeTableDef)

set_option autoImplicit false
set_option maxRecDepth 10000

def CELL_OLD_COMMIT_BASE : Nat := TRACE_WIDTH
def CELL_NEW_COMMIT_BASE : Nat := TRACE_WIDTH + 8
def CELL_TRACE_WIDTH : Nat := TRACE_WIDTH + 16
def CELL_APP_PI_BASE : Nat := 16
def CELL_PI_COUNT : Nat := CELL_APP_PI_BASE + PI_COUNT
def GRAPH_NEW_ROOT_PI_BASE : Nat := CELL_APP_PI_BASE + 21

def CELL_OLD_COMMIT (lane : Nat) : Nat := CELL_OLD_COMMIT_BASE + lane
def CELL_NEW_COMMIT (lane : Nat) : Nat := CELL_NEW_COMMIT_BASE + lane

def statePublicPins : List VmConstraint2 :=
  (List.range 8).map
      (fun lane => .base (.piBinding .first (CELL_OLD_COMMIT lane) lane)) ++
  (List.range 8).map
      (fun lane => .base (.piBinding .first (CELL_NEW_COMMIT lane) (8 + lane)))

def shiftPublicPin : VmConstraint2 → VmConstraint2
  | .base (.piBinding row col pi) =>
      .base (.piBinding row col (CELL_APP_PI_BASE + pi))
  | other => other

/-- The reusable relation's exact PI order, shifted past the state prefix. -/
def corePublicPins : List VmConstraint2 := publicPins.map shiftPublicPin

def cellPublicPins : List VmConstraint2 := statePublicPins ++ corePublicPins

/-- The custom-VK cell door for one hidden semantic graph reduction. -/
def privateGraphRewriteCellDescriptor : EffectVmDescriptor2 :=
  { name := "private-graph-rewrite-cell-4x2::injective-swapnet-poseidon2-v1"
  , traceWidth := CELL_TRACE_WIDTH
  , piCount := CELL_PI_COUNT
  , tables := [rangeTableDef 4]
  , constraints := hashLookups ++ rangeLookups ++
      semanticBodies.map (fun body => .base (.gate body)) ++ cellPublicPins ++
      semanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard privateGraphRewriteCellDescriptor.traceWidth == 326
#guard privateGraphRewriteCellDescriptor.piCount == 45
#guard statePublicPins.length == 16
#guard corePublicPins.length == 29
#guard cellPublicPins.length == 45
#guard GRAPH_NEW_ROOT_PI_BASE == 37
#guard (emitVmJson2 privateGraphRewriteCellDescriptor).contains
  "private-graph-rewrite-cell-4x2::injective-swapnet-poseidon2-v1"
#guard !(emitVmJson2 privateGraphRewriteCellDescriptor).contains "1347571253"

theorem cell_public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ cellPublicPins) :
    pin ∈ privateGraphRewriteCellDescriptor.constraints := by
  simp [privateGraphRewriteCellDescriptor, hpin]

theorem cell_semantic_gate_mem {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    VmConstraint2.base (.gate body) ∈ privateGraphRewriteCellDescriptor.constraints := by
  simp [privateGraphRewriteCellDescriptor, hbody]

theorem cell_hash_lookup_mem {lookup : VmConstraint2} (h : lookup ∈ hashLookups) :
    lookup ∈ privateGraphRewriteCellDescriptor.constraints := by
  simp [privateGraphRewriteCellDescriptor, h]

theorem cell_range_lookup_mem {lookup : VmConstraint2} (h : lookup ∈ rangeLookups) :
    lookup ∈ privateGraphRewriteCellDescriptor.constraints := by
  simp [privateGraphRewriteCellDescriptor, h]

theorem cell_boundary_mem {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    VmConstraint2.base (.boundary .last body) ∈
      privateGraphRewriteCellDescriptor.constraints := by
  simp [privateGraphRewriteCellDescriptor, hbody]

/-- Extract any of the exact 45 public lanes from a satisfying wrapper. -/
theorem cell_public_pin_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateGraphRewriteCellDescriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ cellPublicPins) :
    a col ≡ pis pi [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 (by simp [constTrace]) _ (cell_public_pin_mem hpin)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, constTrace,
    Dregg2.Circuit.DescriptorIR2.envAt] using h

/-- Every base public pin occurs at the same trace column in the wrapper, with
only the canonical sixteen-lane state-prefix offset added to its PI index. -/
theorem base_public_pin_shifted {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ publicPins) :
    VmConstraint2.base (.piBinding .first col (CELL_APP_PI_BASE + pi)) ∈
      corePublicPins := by
  apply List.mem_map.mpr
  exact ⟨VmConstraint2.base (.piBinding .first col pi), hpin, by
    simp [shiftPublicPin]⟩

theorem base_public_pin_cell_mem {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ publicPins) :
    VmConstraint2.base (.piBinding .first col (CELL_APP_PI_BASE + pi)) ∈
      cellPublicPins := by
  exact List.mem_append_right statePublicPins (base_public_pin_shifted hpin)

theorem base_public_pin_shape {pin : VmConstraint2} (hpin : pin ∈ publicPins) :
    ∃ col pi, pin = VmConstraint2.base (.piBinding .first col pi) := by
  simp [publicPins] at hpin
  aesop

theorem hash_lookup_shape {constraint : VmConstraint2}
    (h : constraint ∈ hashLookups) :
    ∃ lookup, constraint = VmConstraint2.lookup lookup := by
  simp [hashLookups, graphCoreLookup, hashLookup] at h
  aesop

theorem range_lookup_shape {constraint : VmConstraint2}
    (h : constraint ∈ rangeLookups) :
    ∃ lookup, constraint = VmConstraint2.lookup lookup := by
  rcases List.mem_map.mp h with ⟨col, _, rfl⟩
  exact ⟨⟨TableId.range, [v col]⟩, rfl⟩

structure CellBindingFacts (a pis : Assignment) : Prop where
  oldCommit : ∀ lane < 8, a (CELL_OLD_COMMIT lane) ≡ pis lane [ZMOD 2013265921]
  newCommit : ∀ lane < 8, a (CELL_NEW_COMMIT lane) ≡ pis (8 + lane) [ZMOD 2013265921]
  domain : a DOMAIN ≡ pis CELL_APP_PI_BASE [ZMOD 2013265921]
  session : a SESSION ≡ pis (CELL_APP_PI_BASE + 1) [ZMOD 2013265921]
  version : a VERSION ≡ pis (CELL_APP_PI_BASE + 2) [ZMOD 2013265921]
  shape : a SHAPE ≡ pis (CELL_APP_PI_BASE + 3) [ZMOD 2013265921]
  index : a INDEX ≡ pis (CELL_APP_PI_BASE + 4) [ZMOD 2013265921]
  rulesetRoot : ∀ lane < 8,
    a (RULESET_ROOT_BASE + lane) ≡ pis (CELL_APP_PI_BASE + 5 + lane) [ZMOD 2013265921]
  graphOldRoot : ∀ lane < 8,
    a (OLD_ROOT_BASE + lane) ≡ pis (CELL_APP_PI_BASE + 13 + lane) [ZMOD 2013265921]
  graphNewRoot : ∀ lane < 8,
    a (NEW_ROOT_BASE + lane) ≡ pis (GRAPH_NEW_ROOT_PI_BASE + lane) [ZMOD 2013265921]

/-- Complete Lean-owned cell/custom-VK ABI theorem. -/
theorem privateGraphRewriteCell_binding_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateGraphRewriteCellDescriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    CellBindingFacts a pis := by
  constructor
  · intro lane hlane
    apply cell_public_pin_sound hsat
    simp [cellPublicPins, statePublicPins, CELL_OLD_COMMIT, hlane]
  · intro lane hlane
    apply cell_public_pin_sound hsat
    simp [cellPublicPins, statePublicPins, CELL_NEW_COMMIT, hlane]
  · apply cell_public_pin_sound hsat
    simpa [CELL_APP_PI_BASE] using
      (base_public_pin_cell_mem (col := DOMAIN) (pi := 0) (by simp [publicPins]))
  · apply cell_public_pin_sound hsat
    simpa [CELL_APP_PI_BASE] using
      (base_public_pin_cell_mem (col := SESSION) (pi := 1) (by simp [publicPins]))
  · apply cell_public_pin_sound hsat
    simpa [CELL_APP_PI_BASE] using
      (base_public_pin_cell_mem (col := VERSION) (pi := 2) (by simp [publicPins]))
  · apply cell_public_pin_sound hsat
    simpa [CELL_APP_PI_BASE] using
      (base_public_pin_cell_mem (col := SHAPE) (pi := 3) (by simp [publicPins]))
  · apply cell_public_pin_sound hsat
    simpa [CELL_APP_PI_BASE] using
      (base_public_pin_cell_mem (col := INDEX) (pi := 4) (by simp [publicPins]))
  · intro lane hlane
    apply cell_public_pin_sound hsat
    convert
      (base_public_pin_cell_mem (col := RULESET_ROOT_BASE + lane) (pi := 5 + lane)
        (by simp [publicPins, hlane])) using 1
    · norm_num [CELL_APP_PI_BASE, ← Nat.add_assoc]
  · intro lane hlane
    apply cell_public_pin_sound hsat
    convert
      (base_public_pin_cell_mem (col := OLD_ROOT_BASE + lane) (pi := 13 + lane)
        (by simp [publicPins, hlane])) using 1
    · norm_num [CELL_APP_PI_BASE, ← Nat.add_assoc]
  · intro lane hlane
    apply cell_public_pin_sound hsat
    convert
      (base_public_pin_cell_mem (col := NEW_ROOT_BASE + lane) (pi := 21 + lane)
        (by simp [publicPins, hlane])) using 1
    · norm_num [GRAPH_NEW_ROOT_PI_BASE, CELL_APP_PI_BASE, ← Nat.add_assoc]

/-- Drop the platform state prefix to recover the reusable 29-PI statement. -/
def cellCorePis (pis : Assignment) : Assignment := fun i => pis (CELL_APP_PI_BASE + i)

/-- Satisfaction of the cell wrapper induces satisfaction of the exact compact
base descriptor.  This is the formal no-second-semantics bridge: the wrapper
adds state-root columns and shifts PI indices, while every graph equation,
lookup, boundary, and table discipline is unchanged. -/
theorem cell_satisfied_to_base_satisfied
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateGraphRewriteCellDescriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a (cellCorePis pis) tf) := by
  -- The two descriptors declare the same memory and map ops and the traces share their rows,
  -- so the logs coincide; stated once and closed by rfl, not re-simplified per leg.
  have hmem : Dregg2.Circuit.DescriptorIR2.memLog privateGraphRewriteDescriptor
      (constTrace a (cellCorePis pis) tf) =
      Dregg2.Circuit.DescriptorIR2.memLog privateGraphRewriteCellDescriptor (constTrace a pis tf) := rfl
  have hmap : Dregg2.Circuit.DescriptorIR2.mapLog privateGraphRewriteDescriptor
      (constTrace a (cellCorePis pis) tf) =
      Dregg2.Circuit.DescriptorIR2.mapLog privateGraphRewriteCellDescriptor (constTrace a pis tf) := rfl
  constructor
  · intro i hi constraint hc
    change constraint ∈ hashLookups ++ (rangeLookups ++
      (semanticBodies.map (fun body => .base (.gate body)) ++ (publicPins ++
      semanticBodies.map (fun body => .base (.boundary .last body))))) at hc
    rcases List.mem_append.mp hc with hhash | hc
    · obtain ⟨lookup, rfl⟩ := hash_lookup_shape hhash
      have h := hsat.rowConstraints i (by simpa [constTrace] using hi) (.lookup lookup)
          (cell_hash_lookup_mem hhash)
      simpa [constTrace, cellCorePis,
        Dregg2.Circuit.DescriptorIR2.envAt, VmConstraint2.holdsAt,
        Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using h
    · rcases List.mem_append.mp hc with hrange | hc
      · obtain ⟨lookup, rfl⟩ := range_lookup_shape hrange
        have h := hsat.rowConstraints i (by simpa [constTrace] using hi) (.lookup lookup)
            (cell_range_lookup_mem hrange)
        simpa [constTrace, cellCorePis,
          Dregg2.Circuit.DescriptorIR2.envAt, VmConstraint2.holdsAt,
          Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using h
      · rcases List.mem_append.mp hc with hgate | hc
        · rcases List.mem_map.mp hgate with ⟨body, hbody, rfl⟩
          have h := hsat.rowConstraints i (by simpa [constTrace] using hi)
            (.base (.gate body)) (cell_semantic_gate_mem hbody)
          simpa [constTrace, cellCorePis,
            Dregg2.Circuit.DescriptorIR2.envAt, VmConstraint2.holdsAt,
            VmConstraint.holdsVm] using h
        · rcases List.mem_append.mp hc with hpin | hboundary
          · obtain ⟨col, pi, rfl⟩ := base_public_pin_shape hpin
            have h := hsat.rowConstraints i (by simpa [constTrace] using hi)
              (.base (.piBinding .first col (CELL_APP_PI_BASE + pi)))
              (cell_public_pin_mem (base_public_pin_cell_mem hpin))
            simpa [constTrace, cellCorePis,
              Dregg2.Circuit.DescriptorIR2.envAt, VmConstraint2.holdsAt,
              VmConstraint.holdsVm] using h
          · rcases List.mem_map.mp hboundary with ⟨body, hbody, rfl⟩
            have h := hsat.rowConstraints i (by simpa [constTrace] using hi)
              (.base (.boundary .last body)) (cell_boundary_mem hbody)
            simpa [constTrace, cellCorePis,
              Dregg2.Circuit.DescriptorIR2.envAt, VmConstraint2.holdsAt,
              VmConstraint.holdsVm] using h
  · intro i hi
    simpa [privateGraphRewriteDescriptor, privateGraphRewriteCellDescriptor,
      constTrace, Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll,
      Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll.go]
      using hsat.rowHashes i (by simpa [constTrace] using hi)
  · intro i hi r hr
    simp [privateGraphRewriteDescriptor] at hr
  · exact hsat.memAddrsNodup
  · rw [hmem]; exact hsat.memClosed
  · rw [hmem]; exact hsat.memDisciplined
  · rw [hmem]; exact hsat.memBalanced
  · rw [hmem]; exact hsat.memTableFaithful
  · rw [hmap]; exact hsat.mapTableFaithful

/-- Structural no-second-semantics theorem: every hash lookup authored by the
base relation is literally enforced by the cell wrapper. -/
theorem base_hash_constraints_preserved :
    ∀ lookup ∈ hashLookups,
      lookup ∈ privateGraphRewriteCellDescriptor.constraints :=
  fun _ h => cell_hash_lookup_mem h

/-- Every range lookup authored by the base relation is literally preserved. -/
theorem base_range_constraints_preserved :
    ∀ lookup ∈ rangeLookups,
      lookup ∈ privateGraphRewriteCellDescriptor.constraints :=
  fun _ h => cell_range_lookup_mem h

/-- Every semantic gate and its final-row boundary copy are literally preserved. -/
theorem base_semantic_constraints_preserved :
    ∀ body ∈ semanticBodies,
      VmConstraint2.base (.gate body) ∈ privateGraphRewriteCellDescriptor.constraints ∧
      VmConstraint2.base (.boundary .last body) ∈
        privateGraphRewriteCellDescriptor.constraints :=
  fun _ h => ⟨cell_semantic_gate_mem h, cell_boundary_mem h⟩

#assert_all_clean [
  Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.cell_public_pin_sound,
  Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.base_public_pin_shifted,
  Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.base_public_pin_cell_mem,
  Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.base_public_pin_shape,
  Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.privateGraphRewriteCell_binding_sound,
  Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.cell_satisfied_to_base_satisfied,
  Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.base_hash_constraints_preserved,
  Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.base_range_constraints_preserved,
  Dregg2.Crypto.PrivateGraphRewriteCellDescriptor.base_semantic_constraints_preserved]

end Dregg2.Crypto.PrivateGraphRewriteCellDescriptor
