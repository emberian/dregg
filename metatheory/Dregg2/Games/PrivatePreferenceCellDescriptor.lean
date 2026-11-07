/-
# Dregg2.Games.PrivatePreferenceCellDescriptor

An additive custom-cell ABI wrapper around the reusable private-preference
relation in `PrivatePreferenceDescriptor`.  The base descriptor remains the
eleven-PI application relation.  This wrapper prepends the platform's canonical
sixteen-felt state door and is the descriptor retained/re-proved by the custom
recursion carrier.

Public inputs are exactly:

`[oldCommit8 || newCommit8 || session || rule || ballotRoot8 || winner]`.

The descriptor proves the imported score/commitment/lowest-index-argmax
relation and pins all 27 public inputs.  The platform custom fold supplies the
two external welds: PI 0..16 to the real rotated cell anchors, and PI 26
(`winner`) to the wide leg's committed post-state winner field.
-/
import Dregg2.Games.PrivatePreferenceDescriptor

namespace Dregg2.Games.PrivatePreferenceCellDescriptor

open Dregg2.Games.PrivatePreferenceDescriptor
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily Satisfied2
    ChipTableSoundN chipLookupTupleN chip_lookup_sound_N emitVmJson2)

set_option autoImplicit false
set_option maxRecDepth 10000

def CELL_OLD_COMMIT_BASE : Nat := TRACE_WIDTH
def CELL_NEW_COMMIT_BASE : Nat := TRACE_WIDTH + DIGEST_WIDTH
def CELL_TRACE_WIDTH : Nat := TRACE_WIDTH + 2 * DIGEST_WIDTH
def CELL_APP_PI_BASE : Nat := 2 * DIGEST_WIDTH

def CELL_OLD_COMMIT (lane : Nat) : Nat := CELL_OLD_COMMIT_BASE + lane
def CELL_NEW_COMMIT (lane : Nat) : Nat := CELL_NEW_COMMIT_BASE + lane

def cellPublicPins : List VmConstraint2 :=
  (List.range DIGEST_WIDTH).map
      (fun lane => .base (.piBinding .first (CELL_OLD_COMMIT lane) lane)) ++
  (List.range DIGEST_WIDTH).map
      (fun lane => .base (.piBinding .first (CELL_NEW_COMMIT lane) (DIGEST_WIDTH + lane))) ++
  [ .base (.piBinding .first SESSION CELL_APP_PI_BASE)
  , .base (.piBinding .first RULE (CELL_APP_PI_BASE + 1)) ] ++
  (List.range DIGEST_WIDTH).map
      (fun lane => .base (.piBinding .first (ROOT lane) (CELL_APP_PI_BASE + 2 + lane))) ++
  [ .base (.piBinding .first WINNER (CELL_APP_PI_BASE + 10)) ]

/-- The custom-VK/cell door for the Lean-owned private-preference relation. -/
def privatePreferenceCellN4K4Descriptor : EffectVmDescriptor2 :=
  { name := "private-preference-cell-n4k4::score2-wide-poseidon2-v1"
  , traceWidth := CELL_TRACE_WIDTH
  , piCount := CELL_APP_PI_BASE + 11
  , tables := []
  , constraints := hashLookups ++
      semanticBodies.map (fun body => .base (.gate body)) ++ cellPublicPins ++
      semanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard privatePreferenceCellN4K4Descriptor.traceWidth == 134
#guard privatePreferenceCellN4K4Descriptor.piCount == 27
#guard cellPublicPins.length == 27
#guard privatePreferenceCellN4K4Descriptor.constraints.length ==
  1 + 2 * semanticBodies.length + 27
#guard (emitVmJson2 privatePreferenceCellN4K4Descriptor).contains
  "private-preference-cell-n4k4::score2-wide-poseidon2-v1"
#guard !(emitVmJson2 privatePreferenceCellN4K4Descriptor).contains "1347571253"

theorem cell_semantic_gate_mem {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    VmConstraint2.base (.gate body) ∈ privatePreferenceCellN4K4Descriptor.constraints := by
  simp [privatePreferenceCellN4K4Descriptor, hbody]

theorem cell_public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ cellPublicPins) :
    pin ∈ privatePreferenceCellN4K4Descriptor.constraints := by
  simp [privatePreferenceCellN4K4Descriptor, hpin]

theorem cell_root_lookup_mem :
    rootLookup ∈ privatePreferenceCellN4K4Descriptor.constraints := by
  simp [privatePreferenceCellN4K4Descriptor, hashLookups]

/-- Exact extraction of any PI pin from the cell-bound descriptor.  In
particular this covers every lane of the canonical `[old8 || new8]` prefix and
PI 26, the winner lane consumed by `AppRootBinding`. -/
theorem cell_public_pin_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privatePreferenceCellN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ cellPublicPins) :
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (cell_public_pin_mem hpin)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

theorem cell_semantic_gate_vanishes
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privatePreferenceCellN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (cell_semantic_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

theorem cell_wide_root_lookup_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privatePreferenceCellN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    rootDigestCols.map a = permOut (rootInputExprs.map (·.eval a)) := by
  have hrow := hsat.rowConstraints 0 (by simp) rootLookup cell_root_lookup_mem
  have hlookup :
      (chipLookupTupleN rootInputExprs rootDigestCols).map (·.eval a) ∈ tf TableId.poseidon2 := by
    simpa [rootLookup, VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using hrow
  exact chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip a
    rootInputExprs rootDigestCols (by decide) hlookup

structure CellBindingFacts (a pis : Assignment) : Prop where
  oldCommit : ∀ lane < DIGEST_WIDTH,
    a (CELL_OLD_COMMIT lane) ≡ pis lane [ZMOD BABYBEAR_MODULUS]
  newCommit : ∀ lane < DIGEST_WIDTH,
    a (CELL_NEW_COMMIT lane) ≡ pis (DIGEST_WIDTH + lane) [ZMOD BABYBEAR_MODULUS]
  session : a SESSION ≡ pis CELL_APP_PI_BASE [ZMOD BABYBEAR_MODULUS]
  rule : a RULE ≡ pis (CELL_APP_PI_BASE + 1) [ZMOD BABYBEAR_MODULUS]
  ballotRoot : ∀ lane < DIGEST_WIDTH,
    a (ROOT lane) ≡ pis (CELL_APP_PI_BASE + 2 + lane) [ZMOD BABYBEAR_MODULUS]
  winner : a WINNER ≡ pis (CELL_APP_PI_BASE + 10) [ZMOD BABYBEAR_MODULUS]

/-- The Lean-owned ABI theorem: a satisfying cell descriptor carries the exact
27-lane public layout used by the custom state/app-root fold. -/
theorem privatePreferenceCellN4K4_binding_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privatePreferenceCellN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    CellBindingFacts a pis := by
  constructor
  · intro lane hlane
    have hlane8 : lane < 8 := by simpa [DIGEST_WIDTH] using hlane
    apply cell_public_pin_sound hsat
    simp [cellPublicPins, CELL_OLD_COMMIT, DIGEST_WIDTH, hlane8]
  · intro lane hlane
    have hlane8 : lane < 8 := by simpa [DIGEST_WIDTH] using hlane
    apply cell_public_pin_sound hsat
    simp [cellPublicPins, CELL_NEW_COMMIT, DIGEST_WIDTH, hlane8]
  · apply cell_public_pin_sound hsat
    simp [cellPublicPins, CELL_APP_PI_BASE, DIGEST_WIDTH]
  · apply cell_public_pin_sound hsat
    simp [cellPublicPins, CELL_APP_PI_BASE, DIGEST_WIDTH]
  · intro lane hlane
    have hlane8 : lane < 8 := by simpa [DIGEST_WIDTH] using hlane
    apply cell_public_pin_sound hsat
    simp [cellPublicPins, CELL_APP_PI_BASE, DIGEST_WIDTH, hlane8]
  · apply cell_public_pin_sound hsat
    simp [cellPublicPins, CELL_APP_PI_BASE, DIGEST_WIDTH]

/-- Drop the platform's 16-felt state prefix from the cell ABI. -/
def cellCorePis (pis : Assignment) : Assignment := fun i => pis (CELL_APP_PI_BASE + i)

/-- A satisfying cell wrapper induces satisfaction of the exact reusable base
descriptor.  This is the formal no-second-semantics bridge: the wrapper differs
only in public-input placement and the appended state-door columns. -/
theorem cell_satisfied_to_base_satisfied
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privatePreferenceCellN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    Satisfied2 hash privatePreferenceN4K4Descriptor ppM0 ppF0 []
      (constTrace a (cellCorePis pis) tf) := by
  -- The two descriptors declare the same (empty) memory and map ops and the traces share
  -- their rows, so the logs coincide; stated once, by unfolding, not re-simplified per leg.
  have hmem : Dregg2.Circuit.DescriptorIR2.memLog privatePreferenceN4K4Descriptor
      (constTrace a (cellCorePis pis) tf) =
      Dregg2.Circuit.DescriptorIR2.memLog privatePreferenceCellN4K4Descriptor
        (constTrace a pis tf) := rfl
  have hmap : Dregg2.Circuit.DescriptorIR2.mapLog privatePreferenceN4K4Descriptor
      (constTrace a (cellCorePis pis) tf) =
      Dregg2.Circuit.DescriptorIR2.mapLog privatePreferenceCellN4K4Descriptor
        (constTrace a pis tf) := rfl
  constructor
  · intro i hi c hc
    change c ∈ hashLookups ++
      (semanticBodies.map (fun body => .base (.gate body)) ++
        (publicPins ++ semanticBodies.map (fun body => .base (.boundary .last body)))) at hc
    rcases List.mem_append.mp hc with hhash | hc
    · have hcEq : c = rootLookup := by simpa [hashLookups] using hhash
      subst c
      have hcell : rootLookup ∈ privatePreferenceCellN4K4Descriptor.constraints := by
        change rootLookup ∈ hashLookups ++
          (semanticBodies.map (fun body => .base (.gate body)) ++
            (cellPublicPins ++ semanticBodies.map (fun body => .base (.boundary .last body))))
        exact List.mem_append_left _ hhash
      have h := hsat.rowConstraints i (by simpa [constTrace] using hi) rootLookup hcell
      simpa [constTrace, Dregg2.Circuit.DescriptorIR2.envAt,
        VmConstraint2.holdsAt, rootLookup,
        Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using h
    · rcases List.mem_append.mp hc with hgate | hc
      · rcases List.mem_map.mp hgate with ⟨body, hbody, rfl⟩
        have hcell : VmConstraint2.base (.gate body) ∈
            privatePreferenceCellN4K4Descriptor.constraints := by
          change VmConstraint2.base (.gate body) ∈ hashLookups ++
            (semanticBodies.map (fun body => .base (.gate body)) ++
              (cellPublicPins ++ semanticBodies.map (fun body => .base (.boundary .last body))))
          exact List.mem_append_right _ (List.mem_append_left _ hgate)
        have h := hsat.rowConstraints i (by simpa [constTrace] using hi)
          (.base (.gate body)) hcell
        simpa [constTrace, Dregg2.Circuit.DescriptorIR2.envAt,
          VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
      · rcases List.mem_append.mp hc with hpin | hbound
        · simp [publicPins, DIGEST_WIDTH, ROOT, List.range_succ] at hpin
          have facts := privatePreferenceCellN4K4_binding_sound hsat
          rcases hpin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · intro hi0
            simp at hi0
            subst i
            simpa [constTrace, cellCorePis, Dregg2.Circuit.DescriptorIR2.envAt,
              VmConstraint2.holdsAt, VmConstraint.holdsVm, CELL_APP_PI_BASE, BABYBEAR_MODULUS, ROOT] using facts.session
          · intro hi0
            simp at hi0
            subst i
            simpa [constTrace, cellCorePis, Dregg2.Circuit.DescriptorIR2.envAt,
              VmConstraint2.holdsAt, VmConstraint.holdsVm, CELL_APP_PI_BASE, BABYBEAR_MODULUS, ROOT] using facts.rule
          · intro hi0
            simp at hi0
            subst i
            simpa [constTrace, cellCorePis, Dregg2.Circuit.DescriptorIR2.envAt,
              VmConstraint2.holdsAt, VmConstraint.holdsVm, CELL_APP_PI_BASE, BABYBEAR_MODULUS, ROOT] using
              facts.ballotRoot 0 (by decide)
          · intro hi0
            simp at hi0
            subst i
            simpa [constTrace, cellCorePis, Dregg2.Circuit.DescriptorIR2.envAt,
              VmConstraint2.holdsAt, VmConstraint.holdsVm, CELL_APP_PI_BASE, BABYBEAR_MODULUS, ROOT] using
              facts.ballotRoot 1 (by decide)
          · intro hi0
            simp at hi0
            subst i
            simpa [constTrace, cellCorePis, Dregg2.Circuit.DescriptorIR2.envAt,
              VmConstraint2.holdsAt, VmConstraint.holdsVm, CELL_APP_PI_BASE, BABYBEAR_MODULUS, ROOT] using
              facts.ballotRoot 2 (by decide)
          · intro hi0
            simp at hi0
            subst i
            simpa [constTrace, cellCorePis, Dregg2.Circuit.DescriptorIR2.envAt,
              VmConstraint2.holdsAt, VmConstraint.holdsVm, CELL_APP_PI_BASE, BABYBEAR_MODULUS, ROOT] using
              facts.ballotRoot 3 (by decide)
          · intro hi0
            simp at hi0
            subst i
            simpa [constTrace, cellCorePis, Dregg2.Circuit.DescriptorIR2.envAt,
              VmConstraint2.holdsAt, VmConstraint.holdsVm, CELL_APP_PI_BASE, BABYBEAR_MODULUS, ROOT] using
              facts.ballotRoot 4 (by decide)
          · intro hi0
            simp at hi0
            subst i
            simpa [constTrace, cellCorePis, Dregg2.Circuit.DescriptorIR2.envAt,
              VmConstraint2.holdsAt, VmConstraint.holdsVm, CELL_APP_PI_BASE, BABYBEAR_MODULUS, ROOT] using
              facts.ballotRoot 5 (by decide)
          · intro hi0
            simp at hi0
            subst i
            simpa [constTrace, cellCorePis, Dregg2.Circuit.DescriptorIR2.envAt,
              VmConstraint2.holdsAt, VmConstraint.holdsVm, CELL_APP_PI_BASE, BABYBEAR_MODULUS, ROOT] using
              facts.ballotRoot 6 (by decide)
          · intro hi0
            simp at hi0
            subst i
            simpa [constTrace, cellCorePis, Dregg2.Circuit.DescriptorIR2.envAt,
              VmConstraint2.holdsAt, VmConstraint.holdsVm, CELL_APP_PI_BASE, BABYBEAR_MODULUS, ROOT] using
              facts.ballotRoot 7 (by decide)
          · intro hi0
            simp at hi0
            subst i
            simpa [constTrace, cellCorePis, Dregg2.Circuit.DescriptorIR2.envAt,
              VmConstraint2.holdsAt, VmConstraint.holdsVm, CELL_APP_PI_BASE, BABYBEAR_MODULUS, ROOT] using facts.winner
        · rcases List.mem_map.mp hbound with ⟨body, hbody, rfl⟩
          have hcell : VmConstraint2.base (.boundary .last body) ∈
              privatePreferenceCellN4K4Descriptor.constraints := by
            change VmConstraint2.base (.boundary .last body) ∈ hashLookups ++
              (semanticBodies.map (fun body => .base (.gate body)) ++
                (cellPublicPins ++ semanticBodies.map
                  (fun body => .base (.boundary .last body))))
            exact List.mem_append_right _
              (List.mem_append_right _ (List.mem_append_right _ hbound))
          have h := hsat.rowConstraints i (by simpa [constTrace] using hi)
            (.base (.boundary .last body)) hcell
          simpa [constTrace, Dregg2.Circuit.DescriptorIR2.envAt,
            VmConstraint2.holdsAt, VmConstraint.holdsVm] using h
  · intro i hi
    simpa [privatePreferenceN4K4Descriptor, privatePreferenceCellN4K4Descriptor,
      constTrace, Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll,
      Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll.go]
      using hsat.rowHashes i (by simpa [constTrace] using hi)
  · intro i hi r hr
    simp [privatePreferenceN4K4Descriptor] at hr
  · exact hsat.memAddrsNodup
  · rw [hmem]; exact hsat.memClosed
  · rw [hmem]; exact hsat.memDisciplined
  · rw [hmem]; exact hsat.memBalanced
  · rw [hmem]; exact hsat.memTableFaithful
  · rw [hmap]; exact hsat.mapTableFaithful

/-- **The cell door carries the closed semantic relation.** Satisfaction of the
27-PI wrapper implies the base descriptor's exact `Accepts` theorem for the
application statement at PI 16..27, while
[`privatePreferenceCellN4K4_binding_sound`] retains the state/app-root facts. -/
theorem privatePreferenceCellN4K4_descriptor_to_accepts
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hcanonPis : CanonicalAssignment (cellCorePis pis))
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash privatePreferenceCellN4K4Descriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    Accepts (permHash8 permOut) (piPublic (cellCorePis pis)) (decodedWitness a) := by
  exact privatePreferenceN4K4_descriptor_to_accepts permOut hcanon hcanonPis hChip
    (cell_satisfied_to_base_satisfied hsat)

#assert_all_clean [
  Dregg2.Games.PrivatePreferenceCellDescriptor.cell_public_pin_sound,
  Dregg2.Games.PrivatePreferenceCellDescriptor.cell_semantic_gate_vanishes,
  Dregg2.Games.PrivatePreferenceCellDescriptor.cell_wide_root_lookup_sound,
  Dregg2.Games.PrivatePreferenceCellDescriptor.privatePreferenceCellN4K4_binding_sound,
  Dregg2.Games.PrivatePreferenceCellDescriptor.cell_satisfied_to_base_satisfied,
  Dregg2.Games.PrivatePreferenceCellDescriptor.privatePreferenceCellN4K4_descriptor_to_accepts]

end Dregg2.Games.PrivatePreferenceCellDescriptor
