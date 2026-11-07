/-
# Dregg2.Circuit.Emit.EffectVmEmitV2 — the FAITHFULNESS RE-ANCHOR onto descriptor IR v2.

`DescriptorIR2` (the EPOCH keystone) supplies the multi-table grammar: chip `Lookup`s for hash
sites, range `Lookup`s for range teeth, `MemOp`s for state accesses, `MapOp`s for boundary map
reconciliations — with `Satisfied2` as the multi-table denotation. THIS module moves the
PER-EFFECT EMISSION onto it:

  * **`graduateV1`** — the generic re-anchor: a v1 `EffectVmDescriptor`'s hash sites become
    Poseidon2-chip lookups (`siteLookup`), its range teeth become range-table lookups, its
    arithmetic/transition/boundary/PI constraints embed as `.base`. The graduated descriptor
    carries NO legacy `hashSites`/`ranges` — the v2 wire is lookup-shaped throughout.
  * **`graduateV1_sound`** — the keystone: a `Satisfied2` witness of the graduated descriptor
    (against a sound chip table + the faithful range table) yields the FULL v1 denotation
    `satisfiedVm` on every row window. So EVERY existing per-effect faithfulness /
    anti-ghost / full-state theorem (all stated against `satisfiedVm`) RE-STATES against v2
    by one composition — the refinement tower's shape is unchanged, only the emission target
    moved. The ordered-hash-site walk survives the move by the `go_of_siteLookups` induction
    (digest-chaining via result columns, the well-formedness `sitesWF` making earlier-site
    references meaningful).
  * **`graduateV1_complete`** + **`graduateV1_faithful`** — the round trip: a v1-satisfying
    row family CONSTRUCTS a satisfying multi-table v2 witness (`v2TraceOf`: the chip table is
    the gathered genuine permutation rows, sound BY CONSTRUCTION; memory/map tables empty).
    Nothing is gained or lost in the re-anchor.
  * **The SWEEP** (§6) — graduated v2 descriptors for the whole graduation cohort (the
    EmitGraduate 16 + attenuate + the 8 setField slots), each `#guard`-checked `graduable`;
    re-anchored corner theorems for the validated TRANSFER reference
    (`transferV2_pins_intent`) and the economic family (`burnV2_full_sound`,
    `mintV2_full_sound`).
  * **NEWLY EXPRESSIBLE I (§7)** — the Attenuate cap-crown phase-B circuit leg
    (`attenuateVmDescriptor2`): held-capability MEMBERSHIP authenticated against the before
    `cap_root` (a `MapOp.read` — under CR the row cannot lie: `opensTo_functional`), the post
    `cap_root` pinned to the GENUINE sorted write (`MapOp.write`), and `granted ⊑ held` as a
    BITWISE-SUBMASK lookup into the custom subset table (`subsetTable`,
    `subsetTable_mem_iff`) — the lattice compare the v1 IR could not express
    (`attenuateV2_non_amp`, `attenuateV2_held_determined`).
  * **NEWLY EXPRESSIBLE II (§8)** — SetField with a DYNAMIC slot index
    (`setFieldDynVmDescriptor2`): the field write is a `MemOp` at address `param[SLOT]` (one
    descriptor, not 8 per-slot circuits), the slot bounded by the degree-8 product gate, and
    the write→read transport carried by the PROVED memory argument with ZERO hashing
    (`setFieldDyn_readback_genuine` via `satisfied2_mem_consistent` = Blum applied).

## Honest boundary notes (do NOT over-read)

  * The custom subset table's CONTENTS are pinned by hypothesis (`t.tf (.custom SUBMASK_TID) =
    subsetTable MASK_BITS`) in the §7 theorems: `TableDef.RowSemantics` has no tag for emitted
    custom-table contents yet, so the wire manifest for custom tables is a small IR follow-up
    (the Rust assembly must generate the subset rows from the declared id). The chip / range
    table pins are the same shape (`ChipTableSound` / `tf .range = rangeRows`) — those are the
    per-table AIR faithfulness obligations the multi-table assembly discharges.
  * `setFieldDynVmDescriptor2` is the POST-FLAG-DAY shape: the 8 user-field cells live in the
    memory table at addresses `0..7` (the witness-generation restructure), not in per-slot
    state columns. The full-state spec triangle for the dynamic form composes with the memory
    argument; the per-slot static descriptors remain valid and graduated in the sweep.
  * `MASK_BITS := 30` matches the deployed effect-mask width; the deployed AIR splits masks
    into `mask_lo`/`mask_hi` limbs (`circuit/tests/effect_vm_attenuate_non_amp.rs`) — the
    two-limb split is a wire-layout choice over the SAME subset relation; the Lean denotation
    states it unsplit.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Crypto enters ONLY
as the named `Poseidon2SpongeCR` (via the imported map-op functionality theorems); memory
consistency is the PROVED `memcheck_sound` import. NEW file;
imports are read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitBurn
import Dregg2.Circuit.Emit.EffectVmEmitMint
import Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
import Dregg2.Circuit.Emit.EffectVmEmitNoteCreate
-- NOT imported: Dregg2.Circuit.Emit.EffectVmEmitBridgeMint — that module does not build in the
-- current shared tree (`Unknown identifier recBalCredit_correct` at its line 315: its Exec-side
-- dependency moved under it mid-epoch; pre-existing, not introduced here). Its graduation is
-- one `graduateV1` line + one `graduable` #guard once its own lane repairs it.
import Dregg2.Circuit.Emit.EffectVmEmitCellSeal
import Dregg2.Circuit.Emit.EffectVmEmitCellDestroy
import Dregg2.Circuit.Emit.EffectVmEmitRefusal
import Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
import Dregg2.Circuit.Emit.EffectVmEmitSetVK
import Dregg2.Circuit.Emit.EffectVmEmitExercise
import Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend
import Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
import Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
import Dregg2.Circuit.Emit.EffectVmEmitIntroduce
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Circuit.Emit.EffectVmEmitRevokeCapability
import Dregg2.Circuit.Emit.EffectVmEmitSetField
import Dregg2.Circuit.Emit.EffectVmEmitEmitEvent

namespace Dregg2.Circuit.Emit.EffectVmEmitV2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — Graduation side conditions (decidable, `#guard`-checkable per descriptor).

`sitesWF`: every `.digest k` input references a STRICTLY EARLIER site (the deterministic
`hash_sites()` order contract — the property that makes the result-column chaining meaningful).
`sitesFit`: every site's input list fits the chip rate. `graduable` bundles them with the
range-bits uniformity (the shared range table is the 30-bit limb table). -/

/-- One input is well-formed at site index `idx`: a `.digest k` reference must be earlier. -/
def siteInputWF (idx : Nat) : HashInput → Bool
  | .digest k => decide (k < idx)
  | _ => true

/-- All sites from index `idx` on reference only digests `<` their own index. -/
def sitesWFAux : Nat → List VmHashSite → Bool
  | _, [] => true
  | idx, s :: ss => s.inputs.all (siteInputWF idx) && sitesWFAux (idx + 1) ss

/-- The whole ordered site list is reference-well-formed. -/
def sitesWF (sites : List VmHashSite) : Bool := sitesWFAux 0 sites

/-- Every site's input tuple is an arity the deployed chip AIR ADMITS.

⚑ **This used to read `s.inputs.length ≤ CHIP_RATE`, and that is the emitter-side face of the
wound `DescriptorIR2`'s arity note describes**: the deployed chip's admission is a degree-7 product
with seven roots, so `≤ CHIP_RATE` passed ten arities at which the graduated lookup has NO
satisfying assignment. The gate a descriptor must clear to graduate is now the chip's actual
budget. -/
def sitesFit (sites : List VmHashSite) : Bool :=
  sites.all fun s => decide (ChipArityAdmitted s.inputs.length)

/-- `sitesFit` unpacked: the per-site admission every graduated chip lookup is CONSTRUCTED with. -/
theorem sitesFit_admitted {sites : List VmHashSite} (h : sitesFit sites = true) :
    ∀ s ∈ sites, ChipArityAdmitted s.inputs.length :=
  fun s hs => of_decide_eq_true (List.all_eq_true.mp h s hs)



/-- A v1 descriptor is GRADUABLE: well-formed site references, chip-rate fit, and every range
tooth at the shared limb width (`BAL_LIMB_BITS = 30` — the whole registry, surveyed). -/
def graduable (d : EffectVmDescriptor) : Bool :=
  sitesWF d.hashSites && sitesFit d.hashSites
    && d.ranges.all (fun r => r.bits == BAL_LIMB_BITS)

/-- Unpack the decidable `graduable` check into the three propositional side conditions. -/
theorem graduable_spec {d : EffectVmDescriptor} (h : graduable d = true) :
    sitesWF d.hashSites = true ∧ sitesFit d.hashSites = true
      ∧ ∀ r ∈ d.ranges, r.bits = BAL_LIMB_BITS := by
  unfold graduable at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun r hr => ?_⟩
  have := List.all_eq_true.mp h3 r hr
  simpa using this

/-- **The graduation-site admission discharger.** `assumption` for the generic keystones that
already carry the family condition; then the emitter's OWN fail-closed gate — `graduable` /
`graduableWide` in the context, or decided outright for a concrete descriptor; then a loud failure.
A v1 descriptor whose hash sites ask the chip for an arity it refuses cannot be graduated: the
graduated descriptor cannot be written down, rather than being written down and proved about
vacuously. -/
macro "graduate_arity" : tactic =>
  `(tactic| first
      | assumption
      | exact sitesFit_admitted (graduable_spec (by assumption)).2.1
      | exact sitesFit_admitted (graduableWide_spec (by assumption)).2.1
      | exact sitesFit_admitted (of_decide_eq_true (Eq.refl true))
      | fail "GRADUATION REFUSED — a v1 hash site of this descriptor absorbs a number of inputs \
              the deployed chip AIR does not admit (CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, \
              16]). Graduating it emits a chip lookup with NO satisfying assignment. PAD the \
              site's input block up to the next admitted arity; do NOT widen the admitted set.")

/-! ## §2 — `graduateV1`: the re-anchored emission.

Hash sites → chip lookups (`siteLookup`, digest chaining via result columns); range teeth →
range-table lookups; the v1 constraint list embeds whole. The graduated descriptor carries NO
legacy `hashSites`/`ranges`: its v2 wire (`emitVmJson2`) is lookup-shaped throughout. -/

/-- The range-table lookup replacing a v1 `VmRange` tooth. -/
def rangeLookup (r : VmRange) : Dregg2.Circuit.DescriptorIR2.Lookup :=
  { table := .range, tuple := [.var r.wire] }

/-- One graduated hash site's chip lookup, carrying its own admission. `attach` is what transports
the family condition `hAdm` into the `mapIdx` lambda, where the bound site would otherwise have no
membership fact and therefore no way to name its arity. `Prop`-erased: the emitted lookup is
byte-identical to the unchecked one. -/
def graduateSiteLookup (sites : List VmHashSite) (width i : Nat)
    (hAdm : ∀ x ∈ sites, ChipArityAdmitted x.inputs.length)
    (s : {x : VmHashSite // x ∈ sites}) : Dregg2.Circuit.DescriptorIR2.Lookup :=
  siteLookup sites s.1 (width + (CHIP_OUT_LANES - 1) * i) (hAdm s.1 s.2)

/-- The graduated chip-lookup family: site `i` at lane base `width + 7·i`. -/
def graduateSiteLookups (sites : List VmHashSite) (width : Nat)
    (hAdm : ∀ x ∈ sites, ChipArityAdmitted x.inputs.length) :
    List Dregg2.Circuit.DescriptorIR2.Lookup :=
  sites.attach.mapIdx (graduateSiteLookup sites width · hAdm)

/-- Membership in the graduated lookup family, in EXACTLY `List.mem_mapIdx`'s shape — so the
admission threading costs no proof restructuring downstream. -/
theorem mem_graduateSiteLookups {sites : List VmHashSite} {width : Nat}
    {hAdm : ∀ x ∈ sites, ChipArityAdmitted x.inputs.length}
    {l : Dregg2.Circuit.DescriptorIR2.Lookup} :
    l ∈ graduateSiteLookups sites width hAdm ↔
      ∃ (j : Nat) (hj : j < sites.length),
        siteLookup sites sites[j] (width + (CHIP_OUT_LANES - 1) * j)
          (hAdm _ (List.getElem_mem hj)) = l := by
  rw [graduateSiteLookups, List.mem_mapIdx]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by simpa using hj, by simp [graduateSiteLookup]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by simpa using hj, by simp [graduateSiteLookup]⟩

/-- The graduated site block as v2 constraints. -/
def graduateSites (sites : List VmHashSite) (width : Nat)
    (hAdm : ∀ x ∈ sites, ChipArityAdmitted x.inputs.length) : List VmConstraint2 :=
  (graduateSiteLookups sites width hAdm).map .lookup

/-- Membership in the graduated site block, in EXACTLY `List.mem_mapIdx`'s shape — so every
`simp only [List.mem_append, List.mem_map, mem_graduateSites]` reproduces the `⟨j, hj, rfl⟩`
pattern the un-admitted `mapIdx` gave. -/
theorem mem_graduateSites {sites : List VmHashSite} {width : Nat}
    {hAdm : ∀ x ∈ sites, ChipArityAdmitted x.inputs.length} {c : VmConstraint2} :
    c ∈ graduateSites sites width hAdm ↔
      ∃ (j : Nat) (hj : j < sites.length),
        VmConstraint2.lookup (siteLookup sites sites[j] (width + (CHIP_OUT_LANES - 1) * j)
          (hAdm _ (List.getElem_mem hj))) = c := by
  rw [graduateSites, List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨j, hj, rfl⟩ := mem_graduateSiteLookups.mp hl
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, mem_graduateSiteLookups.mpr ⟨j, hj, rfl⟩, rfl⟩

/-- **`graduateV1`** — re-anchor a v1 descriptor onto IR v2: constraints embed, every hash site
becomes a chip lookup, every range tooth becomes a range lookup; the five EPOCH tables are
declared; the legacy carriers empty.

⚑ `hAdm` is the CONSTRUCTION obligation the graduation always owed and never took: every hash site
must ask the chip for an admitted arity. It is an `autoParam` discharged by `graduate_arity`, so a
concrete graduable descriptor threads it silently and a descriptor with an inadmissible site FAILS
TO ELABORATE. `Prop`-erased — every emitted byte is unchanged. -/
def graduateV1 (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length := by graduate_arity) :
    EffectVmDescriptor2 :=
  { name        := d.name
  , traceWidth  := d.traceWidth + (CHIP_OUT_LANES - 1) * d.hashSites.length
  , piCount     := d.piCount
  , tables      := v2Tables (d.traceWidth + (CHIP_OUT_LANES - 1) * d.hashSites.length)
  , constraints :=
      d.constraints.map .base
        ++ graduateSites d.hashSites d.traceWidth hAdm
        ++ d.ranges.map (fun r => .lookup (rangeLookup r))
  , hashSites   := []
  , ranges      := [] }

/-- Every graduated constraint is a `.base` or a `.lookup` (no mem/map ops — those are the
NEWLY-EXPRESSIBLE sections' additions, not the v1 re-anchor's). -/
theorem constraints_graduateV1_shapes (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) :
    ∀ c ∈ (graduateV1 d hAdm).constraints,
      (∃ c₀, c = .base c₀) ∨ (∃ l, c = .lookup l) := by
  intro c hc
  unfold graduateV1 at hc
  simp only [List.mem_append, List.mem_map, mem_graduateSites] at hc
  rcases hc with (⟨c₀, _, rfl⟩ | ⟨j, _, rfl⟩) | ⟨r, _, rfl⟩
  · exact Or.inl ⟨c₀, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

/-- A graduated v1 descriptor declares no mem ops. -/
theorem memOpsOf_graduateV1 (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) :
    memOpsOf (graduateV1 d hAdm) = [] := by
  unfold memOpsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  rcases constraints_graduateV1_shapes d hAdm c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩ <;> rfl

/-- A graduated v1 descriptor declares no map ops. -/
theorem mapOpsOf_graduateV1 (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) :
    mapOpsOf (graduateV1 d hAdm) = [] := by
  unfold mapOpsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  rcases constraints_graduateV1_shapes d hAdm c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩ <;> rfl

/-- A graduated v1 descriptor's memory log is empty. -/
theorem memLog_graduateV1 (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) (t : VmTrace) :
    memLog (graduateV1 d hAdm) t = [] := by
  unfold memLog
  rw [memOpsOf_graduateV1 d hAdm]
  simp

/-- A graduated v1 descriptor's map-ops log is empty. -/
theorem mapLog_graduateV1 (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) (t : VmTrace) :
    mapLog (graduateV1 d hAdm) t = [] := by
  unfold mapLog
  rw [mapOpsOf_graduateV1 d hAdm]
  simp

/-! ## §3 — The ordered-site induction: chip lookups ⟹ the v1 hash-site walk.

The v1 denotation `siteHoldsAll` walks the ordered site list with a digest ACCUMULATOR (site `i`
reads digests `[0..i)`); the graduated form is one chip lookup per site, the `.digest k` input
translated to the EARLIER site's result COLUMN. The bridge: as long as the processed prefix's
result columns carry the accumulated digests (the invariant the induction maintains), the
translated tuple evaluates to exactly the resolved inputs — so `chip_lookup_sound` forces each
result column to the genuine digest, re-establishing the invariant one site further. -/

/-- The translated input evaluates to the v1-resolved input, given the prefix invariant. -/
theorem toExpr_eval_eq_resolve (env : VmRowEnv) (all : List VmHashSite) (acc : List ℤ)
    (inp : HashInput)
    (hwf : siteInputWF acc.length inp = true)
    (hacc : ∀ k, k < acc.length → env.loc ((all.getD k default).digestCol) = acc.getD k 0) :
    (HashInput.toExpr all inp).eval env.loc = inp.resolve env acc := by
  cases inp with
  | col c => rfl
  | digest k =>
    have hk : k < acc.length := by simpa [siteInputWF] using hwf
    simpa [HashInput.toExpr, HashInput.resolve, EmittedExpr.eval] using hacc k hk
  | zero => rfl

/-- The translated input TUPLE evaluates to the v1-resolved input list. -/
theorem siteTuple_eval_resolved (env : VmRowEnv) (all : List VmHashSite) (acc : List ℤ)
    (s : VmHashSite)
    (hwfs : s.inputs.all (siteInputWF acc.length) = true)
    (hacc : ∀ k, k < acc.length → env.loc ((all.getD k default).digestCol) = acc.getD k 0) :
    (s.inputs.map (HashInput.toExpr all)).map (·.eval env.loc) = s.resolvedInputs env acc := by
  rw [List.map_map]
  unfold VmHashSite.resolvedInputs
  apply List.map_congr_left
  intro inp hin
  exact toExpr_eval_eq_resolve env all acc inp (List.all_eq_true.mp hwfs inp hin) hacc

/-- The prefix-extension step shared by both inductions: pushing the freshly-established digest
onto the accumulator preserves the result-column invariant. -/
theorem hacc_extend (env : VmRowEnv) (pre ss : List VmHashSite) (s : VmHashSite) (acc : List ℤ)
    (d : ℤ) (all : List VmHashSite)
    (hall : all = pre ++ s :: ss)
    (hlen : acc.length = pre.length)
    (hacc : ∀ k, k < acc.length → env.loc ((all.getD k default).digestCol) = acc.getD k 0)
    (hd : env.loc s.digestCol = d) :
    ∀ k, k < (acc ++ [d]).length →
      env.loc ((all.getD k default).digestCol) = (acc ++ [d]).getD k 0 := by
  intro k hk
  have hk' : k < acc.length + 1 := by simpa using hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk'' | rfl
  · have h2 : (acc ++ [d]).getD k 0 = acc.getD k 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk'']
    rw [h2]
    exact hacc k hk''
  · have h1 : all.getD acc.length default = s := by
      rw [hall, hlen, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (le_refl pre.length)]
      simp
    have h2 : (acc ++ [d]).getD acc.length 0 = d := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl acc.length)]
      simp
    rw [h1, h2]
    exact hd

/-- **The soundness induction.** With the prefix invariant established, the suffix's chip
lookups (against a sound chip table) realize the v1 site walk from the current accumulator. -/
theorem go_of_siteLookups (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSound hash tbl) (env : VmRowEnv) (all : List VmHashSite) (width : Nat)
    (rest : List VmHashSite) :
    ∀ (pre : List VmHashSite) (acc : List ℤ),
      all = pre ++ rest →
      acc.length = pre.length →
      (∀ k, k < acc.length → env.loc ((all.getD k default).digestCol) = acc.getD k 0) →
      sitesWFAux acc.length rest = true →
      (hfit : ∀ s ∈ rest, ChipArityAdmitted s.inputs.length) →
      (∀ i, (h : i < rest.length) →
        (siteLookup all rest[i] (width + (CHIP_OUT_LANES - 1) * (pre.length + i))
          (hfit _ (List.getElem_mem h))).tuple.map (·.eval env.loc) ∈ tbl) →
      siteHoldsAll.go hash env acc rest := by
  induction rest with
  | nil => intro pre acc _ _ _ _ _ _; trivial
  | cons s ss ih =>
    intro pre acc hall hlen hacc hwf hfit hlk
    simp only [sitesWFAux, Bool.and_eq_true] at hwf
    obtain ⟨hwfs, hwfss⟩ := hwf
    -- the head site sits at global index `pre.length` (= `i = 0` of `rest`); its lane base is
    -- `width + 7·pre.length`. The base does NOT enter the conclusion — `chip_lookup_sound`
    -- forces out0 only, lanes ride existentially — so the per-site base is purely positional.
    have hlk0 := hlk 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hlk0
    have hchip := chip_lookup_sound hash tbl hSound env.loc
      (s.inputs.map (HashInput.toExpr all)) s.digestCol
      (siteLaneCols (width + (CHIP_OUT_LANES - 1) * pre.length))
      (by simpa [List.length_map] using hfit s List.mem_cons_self)
      hlk0
    rw [siteTuple_eval_resolved env all acc s hwfs hacc] at hchip
    refine ⟨hchip, ?_⟩
    -- ⚠ the arguments are supplied POSITIONALLY: `hfit` is now a NAMED binder that the lookup
    -- hypothesis DEPENDS on, so `apply` no longer presents the goals in source order.
    refine ih (pre ++ [s]) (acc ++ [hash (s.resolvedInputs env acc)])
      (by rw [hall, List.append_assoc]; rfl)
      (by simp [hlen])
      (hacc_extend env pre ss s acc _ all hall hlen hacc hchip)
      (by simpa using hwfss)
      (fun s' hs' => hfit s' (List.mem_cons_of_mem s hs')) ?_
    -- the tail's site `ss[i]` is at global index `(pre.length+1) + i = pre.length + (i+1)`,
    -- matching `rest[i+1]` of the original list.
    intro i hi
    have := hlk (i + 1) (by simpa using Nat.succ_lt_succ hi)
    simp only [List.getElem_cons_succ] at this
    rw [List.length_append, List.length_singleton]
    have heq : pre.length + 1 + i = pre.length + (i + 1) := by omega
    rw [heq]
    exact this

/-- **`siteLookups_sound`** — the whole ordered family: per-site chip lookups against a sound
chip table ⟹ the full v1 hash-site denotation `siteHoldsAll`. The `i`-th site's lane block sits
at `width + 7·i` (the contiguous append `graduateV1` threads past the v1 trace width). -/
theorem siteLookups_sound (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSound hash tbl) (env : VmRowEnv) (sites : List VmHashSite) (width : Nat)
    (hwf : sitesWF sites = true)
    (hfit : ∀ s ∈ sites, ChipArityAdmitted s.inputs.length)
    (hlk : ∀ i, (h : i < sites.length) →
      (siteLookup sites sites[i] (width + (CHIP_OUT_LANES - 1) * i)
        (hfit _ (List.getElem_mem h))).tuple.map (·.eval env.loc) ∈ tbl) :
    siteHoldsAll hash env sites :=
  go_of_siteLookups hash tbl hSound env sites width sites [] [] rfl rfl
    (fun k hk => absurd hk (by simp)) hwf hfit
    (fun i hi => by simpa using hlk i hi)

/-! ## §4 — `graduateV1_sound`: THE re-anchor keystone.

A `Satisfied2` witness of the graduated descriptor — against a sound chip table and the faithful
range table — yields the FULL v1 denotation `satisfiedVm` on every row window. Every per-effect
faithfulness theorem composes through this. -/

theorem graduateV1_sound (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hgrad : graduable d = true)
    (hsat : Satisfied2 hash (graduateV1 d) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  obtain ⟨hwf, hfit, hbits⟩ := graduable_spec hgrad
  intro i hi
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_, ?_⟩
  · -- the v1 constraints, embedded
    intro c hc
    have hmem : VmConstraint2.base c ∈ (graduateV1 d (sitesFit_admitted hfit)).constraints := by
      unfold graduateV1
      simp only [List.mem_append, List.mem_map, mem_graduateSites]
      exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    exact hrow _ hmem
  · -- the hash sites, via the chip-lookup induction (the `i`-th site's lane base is
    -- `d.traceWidth + 7·i`, the contiguous append `graduateV1` threads)
    refine siteLookups_sound hash (t.tf .poseidon2) hchip (envAt t i) d.hashSites d.traceWidth hwf
      (sitesFit_admitted hfit) ?_
    · intro j hj
      have hmem : VmConstraint2.lookup
          (siteLookup d.hashSites d.hashSites[j]
            (d.traceWidth + (CHIP_OUT_LANES - 1) * j)
            (sitesFit_admitted hfit _ (List.getElem_mem hj)))
          ∈ (graduateV1 d (sitesFit_admitted hfit)).constraints := by
        unfold graduateV1
        simp only [List.mem_append, List.mem_map, mem_graduateSites]
        exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
      exact hrow _ hmem
  · -- the range teeth, via the range-table lookup
    intro r hr
    obtain ⟨w, bits⟩ := r
    have hb : bits = BAL_LIMB_BITS := hbits ⟨w, bits⟩ hr
    subst hb
    have hmem : VmConstraint2.lookup (rangeLookup ⟨w, BAL_LIMB_BITS⟩)
        ∈ (graduateV1 d (sitesFit_admitted hfit)).constraints := by
      unfold graduateV1
      simp only [List.mem_append, List.mem_map, mem_graduateSites]
      exact Or.inr ⟨⟨w, BAL_LIMB_BITS⟩, hr, rfl⟩
    exact lookup_replaces_range BAL_LIMB_BITS t.tf hrange (envAt t i) w (hrow _ hmem)

/-- **`graduateV1_satisfiedVm_of_rowConstraints`** — the `graduateV1_sound` keystone, parametric in JUST
the row-constraint witness (the only `Satisfied2` field it consumes). A descriptor that APPENDS extra
constraints to `graduateV1 d` (e.g. a grow-gate `MapOp`, as `noteSpendV3`/heapWrite's splice do) cannot
build a full `Satisfied2 (graduateV1 d)` (its `mapTableFaithful` mismatches), but it CAN hand over the
row-constraint walk restricted to `graduateV1 d`'s own constraints — which is all the v1 denotation
needs. This lets the addr/leaf hash-site forcing survive an appended `MapOp` row. -/
theorem graduateV1_satisfiedVm_of_rowConstraints (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (t : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hgrad : graduable d = true)
    (hrow : ∀ i, i < t.rows.length → ∀ c ∈ (graduateV1 d).constraints,
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length))
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  obtain ⟨hwf, hfit, hbits⟩ := graduable_spec hgrad
  have hrowi := hrow i hi
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    have hmem : VmConstraint2.base c ∈ (graduateV1 d (sitesFit_admitted hfit)).constraints := by
      unfold graduateV1
      simp only [List.mem_append, List.mem_map, mem_graduateSites]
      exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    exact hrowi _ hmem
  · refine siteLookups_sound hash (t.tf .poseidon2) hchip (envAt t i) d.hashSites d.traceWidth hwf
      (sitesFit_admitted hfit) ?_
    · intro j hj
      have hmem : VmConstraint2.lookup
          (siteLookup d.hashSites d.hashSites[j]
            (d.traceWidth + (CHIP_OUT_LANES - 1) * j)
            (sitesFit_admitted hfit _ (List.getElem_mem hj)))
          ∈ (graduateV1 d (sitesFit_admitted hfit)).constraints := by
        unfold graduateV1
        simp only [List.mem_append, List.mem_map, mem_graduateSites]
        exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
      exact hrowi _ hmem
  · intro r hr
    obtain ⟨w, bits⟩ := r
    have hb : bits = BAL_LIMB_BITS := hbits ⟨w, bits⟩ hr
    subst hb
    have hmem : VmConstraint2.lookup (rangeLookup ⟨w, BAL_LIMB_BITS⟩)
        ∈ (graduateV1 d (sitesFit_admitted hfit)).constraints := by
      unfold graduateV1
      simp only [List.mem_append, List.mem_map, mem_graduateSites]
      exact Or.inr ⟨⟨w, BAL_LIMB_BITS⟩, hr, rfl⟩
    exact lookup_replaces_range BAL_LIMB_BITS t.tf hrange (envAt t i) w (hrowi _ hmem)

/-! ## §4F — `Satisfied2Faithful`: the deployed accept-set with the chip / range soundness as
STRUCTURAL conjuncts (not free levers), plus the COLLAPSE RECIPE.

`graduateV1_sound` carries the chip- and range-table soundness as FREE hypotheses. The deployed
`Ir2Air::Chip` CONSTRAINS every Poseidon2 chip row to a genuine permutation and the range table to
the genuine limb table — so they are NOT free levers; they are STRUCTURAL facts the deployed circuit
forces. `Satisfied2Faithful` folds them INTO the denotation as CONJUNCTS (`chipTableFaithful :
ChipTableSoundN permOut` — the WIDE genuine-permutation chip soundness — and `rangeTableFaithful`).
`satisfied2Faithful_satisfiedVm` is THE COLLAPSE RECIPE: from a faithful witness of a graduated
descriptor, the v1 denotation `satisfiedVm` holds on every row WITHOUT a free `hchip`/`hrange` lever.
Placed here (right after `graduateV1_sound`) so every rotation rung and the apex consume the faithful
object with no upward dependency. -/

/-- A WIDE-sound chip table is legacy-sound for the digest `hash := fun ins => (permOut ins).headD 0`
it exposes at lane 0: the wide row's output block is `permOut ins` (length `CHIP_OUT_LANES`); its head
is the single squeezed digest, the remaining lanes ride existentially — exactly `ChipTableSound`'s
shape. Binding the genuine wide permutation (the deployed `Ir2Air::Chip`) DISCHARGES the legacy chip
soundness the `graduateV1` hash sites need. -/
theorem chipSoundN_implies_chipSound (permOut : List ℤ → List ℤ)
    (hlen : ∀ ins, (permOut ins).length = CHIP_OUT_LANES) (tbl : Table)
    (hN : ChipTableSoundN permOut tbl) :
    ChipTableSound (fun ins => (permOut ins).headD 0) tbl := by
  intro r hr
  obtain ⟨ins, hins, hrow⟩ := hN r hr
  have hl := hlen ins
  cases hpo : permOut ins with
  | nil =>
      rw [hpo] at hl; simp [CHIP_OUT_LANES] at hl
  | cons d lanes =>
      refine ⟨ins, lanes, hins, ?_, ?_⟩
      · have : (d :: lanes).length = CHIP_OUT_LANES := by rw [← hpo]; exact hl
        simp only [List.length_cons] at this
        omega
      · rw [hrow]
        unfold chipRowN chipRow
        simp only [hpo, List.headD_cons]

/-- **`Satisfied2Faithful permOut hash d minit mfin maddrs t`** — the FAITHFUL deployed denotation:
`Satisfied2` PLUS the deployed circuit's own table-faithfulness, carried as STRUCTURE fields. This
binds `t.tf .poseidon2`/`t.tf .range` to the genuine permutation / limb rows IN the structure,
matching the deployed `Ir2Air::Chip` — chip-table-faithful + range-faithful as conjuncts rather than
free `hchip`/`hrange` levers. -/
structure Satisfied2Faithful (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) : Prop extends Satisfied2 hash d minit mfin maddrs t where
  /-- the genuine permutation exposes exactly `CHIP_OUT_LANES` output lanes. -/
  permWidth : ∀ ins, (permOut ins).length = CHIP_OUT_LANES
  /-- the v1 digest IS lane 0 of the genuine permutation (the deployed squeeze). -/
  chipHashIsLane0 : ∀ ins, hash ins = (permOut ins).headD 0
  /-- THE CHIP-TABLE-FAITHFUL CONJUNCT: every chip row is a genuine wide permutation tuple
  (`Ir2Air::Chip`), bound to `t.tf .poseidon2` — not a free lever. -/
  chipTableFaithful : ChipTableSoundN permOut (t.tf .poseidon2)
  /-- THE RANGE-FAITHFUL CONJUNCT: the range table is the genuine limb table (the deployed height). -/
  rangeTableFaithful : t.tf .range = rangeRows BAL_LIMB_BITS

/-- The legacy chip soundness (`ChipTableSound hash`) FOLLOWS from the faithful structure's wide
soundness + the lane-0 digest identity — the `hchip` lever `graduateV1_sound` needs, DISCHARGED from
the structure, not assumed. -/
theorem Satisfied2Faithful.chipSound {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ}
    {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2Faithful permOut hash d minit mfin maddrs t) :
    ChipTableSound hash (t.tf .poseidon2) := by
  have hcs := chipSoundN_implies_chipSound permOut h.permWidth (t.tf .poseidon2) h.chipTableFaithful
  have hfun : (fun ins => (permOut ins).headD 0) = hash := by
    funext ins; exact (h.chipHashIsLane0 ins).symm
  rwa [hfun] at hcs

/-- **`satisfied2Faithful_satisfiedVm` — THE COLLAPSE RECIPE.** From a `Satisfied2Faithful` witness of
the GRADUATED descriptor `graduateV1 d` (and `graduable d`), the v1 denotation `satisfiedVm` holds on
every row window — with NO free `hchip`/`hrange` lever: the structure CARRIES them
(`Satisfied2Faithful.chipSound` discharges `hchip`; `rangeTableFaithful` IS `hrange`). -/
theorem satisfied2Faithful_satisfiedVm (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduable d = true)
    (h : Satisfied2Faithful permOut hash
      (graduateV1 d (sitesFit_admitted (graduable_spec hgrad).2.1)) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  graduateV1_sound hash d minit mfin maddrs t h.chipSound h.rangeTableFaithful hgrad h.toSatisfied2

#assert_axioms chipSoundN_implies_chipSound
#assert_axioms Satisfied2Faithful.chipSound
#assert_axioms satisfied2Faithful_satisfiedVm

/-! ## §5 — Completeness: a v1-satisfying row family BUILDS a satisfying v2 witness.

The chip table is the gathered genuine permutation rows (`chipLogOf`), sound BY CONSTRUCTION
(`chipLogOf_sound` — the mirror induction `go_siteLookups_complete`); the range table is the
faithful limb table; memory/map tables are empty (the graduated v1 face is inert there). So the
re-anchor loses nothing: `graduateV1_faithful` is the round trip. -/

/-- The row environment of a bare row family (what `envAt` reads — trace-family-free). -/
def envOf (rows : List Assignment) (pub : Assignment) (i : Nat)
    (chal : Assignment := fun _ => 0) : VmRowEnv :=
  -- ⚑ `chal` is a trailing parameter (defaulted) so `envOf` and `envAt` stay DEFINITIONALLY equal
  -- on a `v2TraceOf`-built trace, which is what `graduateV1_sound`'s conclusion is stated against.
  -- Defaulting it INSIDE (rather than threading) would have made the two envs different functions
  -- and turned that `rfl` into a false statement about any challenge-bearing trace.
  { loc := rows.getD i zeroAsg, nxt := rows.getD (i + 1) zeroAsg, pub := pub, chal := chal }

/-- The gathered chip rows: every row's every site lookup tuple, evaluated (Phase B-GATE: the
`i`-th site rides the lane base `width + 7·i`, mirroring `graduateV1`'s `mapIdx`). -/
def chipLogOf (sites : List VmHashSite) (width : Nat)
    (hAdm : ∀ s ∈ sites, ChipArityAdmitted s.inputs.length) (rows : List Assignment) : Table :=
  rows.flatMap fun a =>
    (graduateSiteLookups sites width hAdm).map (fun l => l.tuple.map (·.eval a))

/-- **The completeness induction.** Under the same prefix invariant, a v1 site walk makes every
suffix site's lookup tuple evaluate to a GENUINE 17-wide chip row (output block `hash ins ::
lanes`, the lanes carried from the row's lane columns). -/
theorem go_siteLookups_complete (hash : List ℤ → ℤ) (env : VmRowEnv) (all : List VmHashSite)
    (rest : List VmHashSite) :
    ∀ (pre : List VmHashSite) (acc : List ℤ) (base : Nat),
      all = pre ++ rest →
      acc.length = pre.length →
      (∀ k, k < acc.length → env.loc ((all.getD k default).digestCol) = acc.getD k 0) →
      sitesWFAux acc.length rest = true →
      siteHoldsAll.go hash env acc rest →
      ∀ (hfit : ∀ s ∈ rest, ChipArityAdmitted s.inputs.length),
      ∀ s, ∀ hs : s ∈ rest, ∃ (ins lanes : List ℤ), ins.length = s.inputs.length
        ∧ lanes.length = CHIP_OUT_LANES - 1
        ∧ (siteLookup all s base (hfit s hs)).tuple.map (·.eval env.loc)
            = chipRow hash ins lanes := by
  induction rest with
  | nil => intro pre acc base _ _ _ _ _ _ s hs; cases hs
  | cons s ss ih =>
    intro pre acc base hall hlen hacc hwf hgo hfit s' hs'
    simp only [sitesWFAux, Bool.and_eq_true] at hwf
    obtain ⟨hwfs, hwfss⟩ := hwf
    obtain ⟨hd, hgo'⟩ := hgo
    rcases List.mem_cons.mp hs' with rfl | hs''
    · -- the head site: its 17-wide tuple IS a genuine chip row (out0 = hash, lanes = the
      -- evaluated lane columns)
      refine ⟨s'.resolvedInputs env acc, (siteLaneCols base).map env.loc,
        by simp [VmHashSite.resolvedInputs], by simp [siteLaneCols], ?_⟩
      have hev : (chipLookupTuple (s'.inputs.map (HashInput.toExpr all)) s'.digestCol
            (siteLaneCols base) (by simpa [List.length_map] using hfit s' hs')).map (·.eval env.loc)
          = ((s'.inputs.map (HashInput.toExpr all)).length : ℤ)
            :: padTo CHIP_RATE ((s'.inputs.map (HashInput.toExpr all)).map (·.eval env.loc))
            ++ (env.loc s'.digestCol :: (siteLaneCols base).map env.loc) := by
        simp [chipLookupTuple, List.map_cons, List.map_append, map_eval_padToE,
          EmittedExpr.eval, List.map_map, Function.comp_def]
      show (chipLookupTuple (s'.inputs.map (HashInput.toExpr all)) s'.digestCol
          (siteLaneCols base) (by simpa [List.length_map] using hfit s' hs')).map (·.eval env.loc)
          = chipRow hash (s'.resolvedInputs env acc) ((siteLaneCols base).map env.loc)
      rw [hev, siteTuple_eval_resolved env all acc s' hwfs hacc, hd]
      unfold chipRow
      simp [VmHashSite.resolvedInputs, List.length_map]
    · -- a later site: recurse with the extended prefix
      exact ih (pre ++ [s]) (acc ++ [hash (s.resolvedInputs env acc)]) base
        (by rw [hall, List.append_assoc]; rfl)
        (by simp [hlen])
        (hacc_extend env pre ss s acc _ all hall hlen hacc hd)
        (by simpa using hwfss)
        hgo' (fun x hx => hfit x (List.mem_cons_of_mem s hx)) s' hs''

/-- The gathered chip table is SOUND by construction. -/
theorem chipLogOf_sound (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (rows : List Assignment) (pub : Assignment)
    (hgrad : graduable d = true)
    (hsat : ∀ i, i < rows.length →
      satisfiedVm hash d (envOf rows pub i) (i == 0) (i + 1 == rows.length)) :
    ChipTableSound hash
      (chipLogOf d.hashSites d.traceWidth
        (sitesFit_admitted (graduable_spec hgrad).2.1) rows) := by
  obtain ⟨hwf, hfit, _⟩ := graduable_spec hgrad
  intro r hr
  unfold chipLogOf at hr
  rw [List.mem_flatMap] at hr
  obtain ⟨a, ha, hr⟩ := hr
  rw [List.mem_map] at hr
  obtain ⟨l, hl, rfl⟩ := hr
  obtain ⟨j, hj, rfl⟩ := mem_graduateSiteLookups.mp hl
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  have hloc : (envOf rows pub i).loc = rows[i] := by
    simp [envOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hgo : siteHoldsAll hash (envOf rows pub i) d.hashSites := (hsat i hi).2.1
  have hsmem : d.hashSites[j] ∈ d.hashSites := List.getElem_mem hj
  obtain ⟨ins, lanes, hlen, hlanes, heq⟩ := go_siteLookups_complete hash (envOf rows pub i)
    d.hashSites d.hashSites [] [] (d.traceWidth + (CHIP_OUT_LANES - 1) * j)
    rfl rfl (fun k hk => absurd hk (by simp)) hwf hgo
    (sitesFit_admitted hfit) d.hashSites[j] hsmem
  rw [hloc] at heq
  refine ⟨ins, lanes, ?_, hlanes, heq.symm ▸ rfl⟩
  rw [hlen]
  exact sitesFit_admitted hfit d.hashSites[j] hsmem

/-- The constructed trace family: gathered chip rows, the faithful range table, empty
memory/map/custom tables, main unconstrained. -/
def v2TF (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length)
    (rows : List Assignment) : TraceFamily := fun tid =>
  match tid with
  | .poseidon2 => chipLogOf d.hashSites d.traceWidth hAdm rows
  | .range => rangeRows BAL_LIMB_BITS
  | _ => []

/-- The constructed multi-table witness over a v1-satisfying row family. -/
def v2TraceOf (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length)
    (rows : List Assignment) (pub : Assignment) : VmTrace :=
  { rows := rows, pub := pub, tf := v2TF d hAdm rows }

/-- The constructed trace's family, projected (kept as a `rw` target: a bare `rfl` at the
`.range` USE SITE sends the unifier whnf-ing `rangeRows 30` = `List.range 2^30` — the
documented evaluation trap; the projection equation itself is cheap). -/
theorem v2TraceOf_tf (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length)
    (rows : List Assignment) (pub : Assignment) :
    (v2TraceOf d hAdm rows pub).tf = v2TF d hAdm rows := rfl

/-- The constructed family's range table is the faithful limb table. -/
theorem v2TF_range (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) (rows : List Assignment) :
    v2TF d hAdm rows .range = rangeRows BAL_LIMB_BITS := rfl

/-- **`graduateV1_complete`** — a v1-satisfying row family yields a `Satisfied2` witness of the
graduated descriptor, over the constructed tables, with the EMPTY memory boundary. -/
theorem graduateV1_complete (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (rows : List Assignment) (pub : Assignment)
    (hgrad : graduable d = true)
    (hsat : ∀ i, i < rows.length →
      satisfiedVm hash d (envOf rows pub i) (i == 0) (i + 1 == rows.length)) :
    Satisfied2 hash (graduateV1 d (sitesFit_admitted (graduable_spec hgrad).2.1)) (fun _ => 0) (fun _ => ((0 : ℤ), 0)) []
      (v2TraceOf d (sitesFit_admitted (graduable_spec hgrad).2.1) rows pub) := by
  obtain ⟨hwf, hfit, hbits⟩ := graduable_spec hgrad
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    unfold graduateV1 at hc
    simp only [List.mem_append, List.mem_map, mem_graduateSites] at hc
    rcases hc with (⟨c₀, hc₀, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨r, hr, rfl⟩
    · exact (hsat i hi).1 c₀ hc₀
    · -- chip lookup: membership in the gathered table, by construction
      have hi' : i < rows.length := hi
      show (siteLookup d.hashSites d.hashSites[j]
            (d.traceWidth + (CHIP_OUT_LANES - 1) * j)
            (sitesFit_admitted hfit _ (List.getElem_mem hj))).tuple.map
          (·.eval (envAt (v2TraceOf d (sitesFit_admitted hfit) rows pub) i).loc)
        ∈ chipLogOf d.hashSites d.traceWidth (sitesFit_admitted hfit) rows
      have hloc : (envAt (v2TraceOf d (sitesFit_admitted hfit) rows pub) i).loc = rows[i] := by
        simp [v2TraceOf, envAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      rw [hloc]
      unfold chipLogOf
      rw [List.mem_flatMap]
      exact ⟨rows[i], List.getElem_mem hi',
        List.mem_map.mpr ⟨_, mem_graduateSiteLookups.mpr ⟨j, hj, rfl⟩, rfl⟩⟩
    · -- range lookup: completeness of the limb table
      obtain ⟨w, bits⟩ := r
      have hb : bits = BAL_LIMB_BITS := hbits ⟨w, bits⟩ hr
      subst hb
      exact lookup_range_complete BAL_LIMB_BITS (v2TF d (sitesFit_admitted hfit) rows) rfl
        (envAt (v2TraceOf d (sitesFit_admitted (graduable_spec hgrad).2.1) rows pub) i) w ((hsat i hi).2.2 ⟨w, BAL_LIMB_BITS⟩ hr)
  · intro i hi; trivial
  · intro i hi r hr
    have hnil : (graduateV1 d).ranges = [] := rfl
    rw [hnil] at hr
    cases hr
  · intro op hop
    rw [memLog_graduateV1] at hop
    cases hop
  · rw [memLog_graduateV1]
    trivial
  · rw [memLog_graduateV1]
    exact memCheck_nil _ _
  · rw [memLog_graduateV1]
    rfl
  · rw [mapLog_graduateV1]
    rfl

/-- **`graduateV1_faithful` — THE RE-ANCHOR ROUND TRIP.** A row family satisfies the v1
descriptor on every window IFF some multi-table witness over it (sound chip table, faithful
range table) satisfies the graduated v2 descriptor. Nothing gained, nothing lost: the emission
target moved; the semantics did not. -/
theorem graduateV1_faithful (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (rows : List Assignment) (pub : Assignment)
    (hgrad : graduable d = true) :
    (∀ i, i < rows.length →
        satisfiedVm hash d (envOf rows pub i) (i == 0) (i + 1 == rows.length))
      -- ⚑ `t.chal = fun _ => 0` is a CONJUNCT, not a default. A v1 descriptor carries no
      -- `chalGate` (`challengeCount_eq_zero_of_no_chalGate`), so no challenge is readable on
      -- either side and the round trip is about a challenge-free witness — which is the honest
      -- thing to SAY rather than to arrange by picking a default that makes a `rfl` go through.
      ↔ ∃ t : VmTrace, t.rows = rows ∧ t.pub = pub ∧ t.chal = (fun _ => 0)
          ∧ ChipTableSound hash (t.tf .poseidon2)
          ∧ t.tf .range = rangeRows BAL_LIMB_BITS
          ∧ Satisfied2 hash (graduateV1 d (sitesFit_admitted (graduable_spec hgrad).2.1)) (fun _ => 0) (fun _ => ((0 : ℤ), 0)) [] t := by
  constructor
  · intro h
    refine ⟨v2TraceOf d (sitesFit_admitted (graduable_spec hgrad).2.1) rows pub, rfl, rfl, rfl,
      chipLogOf_sound hash d rows pub hgrad h, ?_,
      graduateV1_complete hash d rows pub hgrad h⟩
    rw [v2TraceOf_tf]
    exact v2TF_range d _ rows
  · rintro ⟨t, rfl, rfl, hchal, hchip, hrange, hsat⟩
    have := graduateV1_sound hash d _ _ _ t hchip hrange hgrad hsat
    intro i hi
    have henv : envAt t i = envOf t.rows t.pub i := by
      simp only [envAt, envOf, hchal]
    rw [← henv]
    exact this i hi

/-! ## §6 — THE SWEEP: the graduation cohort, re-anchored.

One v2 descriptor per cohort member (`graduateV1`), each `#guard`-checked `graduable` so
`graduateV1_sound`/`_complete`/`_faithful` apply by `by decide` discharge. The re-anchored
corner theorems are spelled for the validated TRANSFER reference and the economic family; every
other member's existing `satisfiedVm`-shaped theorem composes with `graduateV1_sound`
identically (one application). -/

def transferVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitTransfer.transferVmDescriptor
def burnVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitBurn.burnVmDescriptor
def mintVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitMint.mintVmDescriptor
def noteSpendVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitNoteSpend.noteSpendVmDescriptor
def noteCreateVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitNoteCreate.noteCreateVmDescriptor
def cellSealVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitCellSeal.cellSealVmDescriptor
def cellDestroyVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitCellDestroy.cellDestroyVmDescriptor
def refusalVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitRefusal.refusalVmDescriptor
def setPermsVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitSetPermissions.setPermsVmDescriptor
def setVKVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitSetVK.setVKVmDescriptor
def exerciseVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitExercise.exerciseVmDescriptor
def pipelinedSendVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor
def refreshVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitRefreshDelegation.refreshVmDescriptor
def incrementNonceVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitIncrementNonce.incrementNonceVmDescriptor
def revokeVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitRevokeDelegation.revokeVmDescriptor
def introduceVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitIntroduce.introduceVmDescriptor
def attenuateVmDescriptor2Base : EffectVmDescriptor2 :=
  graduateV1 EffectVmEmitAttenuateA.attenuateVmDescriptor
def setFieldVmDescriptor2 (slot : Fin 8) : EffectVmDescriptor2 :=
  graduateV1 (EffectVmEmitSetField.setFieldVmDescriptor slot)

-- Every cohort member passes the graduation side conditions (so the §4/§5 theorems apply).
#guard graduable EffectVmEmitTransfer.transferVmDescriptor
#guard graduable EffectVmEmitBurn.burnVmDescriptor
#guard graduable EffectVmEmitMint.mintVmDescriptor
#guard graduable EffectVmEmitNoteSpend.noteSpendVmDescriptor
#guard graduable EffectVmEmitNoteCreate.noteCreateVmDescriptor
#guard graduable EffectVmEmitCellSeal.cellSealVmDescriptor
#guard graduable EffectVmEmitCellDestroy.cellDestroyVmDescriptor
#guard graduable EffectVmEmitRefusal.refusalVmDescriptor
#guard graduable EffectVmEmitSetPermissions.setPermsVmDescriptor
#guard graduable EffectVmEmitSetVK.setVKVmDescriptor
#guard graduable EffectVmEmitExercise.exerciseVmDescriptor
#guard graduable EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor
#guard graduable EffectVmEmitRefreshDelegation.refreshVmDescriptor
#guard graduable EffectVmEmitIncrementNonce.incrementNonceVmDescriptor
#guard graduable EffectVmEmitRevokeDelegation.revokeVmDescriptor
#guard graduable EffectVmEmitIntroduce.introduceVmDescriptor
#guard graduable EffectVmEmitAttenuateA.attenuateVmDescriptor
#guard (List.finRange 8).all fun slot =>
  graduable (EffectVmEmitSetField.setFieldVmDescriptor slot)

/-- **The validated reference, re-anchored (FAITHFUL to `when_transition()`/`when_last_row()`).** The
deployed circuit binds the effect gates only on TRANSITION rows (`isLast = false`) and the post-state
commitment only on the LAST row (`isLast = true`); a single `(true,true)` row — the degenerate wrap row
of a one-row trace — binds NEITHER's intent gates. So the faithful v2 re-anchor takes a trace with at
least TWO rows (`htwo`), the transfer effect on the ACTIVE row 0 (a transition row, `0 + 1 < length`),
and reads:
  * `TransferRowIntent (envAt t 0)` — from row 0's gates, where `when_transition()` binds;
  * the published commit `state_commit = NEW_COMMIT` on the LAST row (`envAt t (length-1)`), where the
    `boundaryLastPins` (`.piBinding .last`) fire.
This separates the two facts onto the rows where the deployed circuit genuinely enforces each, rather
than over-pinning both onto one window. -/
theorem transferV2_pins_intent (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (htwo : 2 ≤ t.rows.length)
    (hrow : EffectVmEmitTransfer.IsTransferRow (envAt t 0))
    (hf : Satisfied2Faithful permOut hash transferVmDescriptor2 minit mfin maddrs t) :
    EffectVmEmitTransfer.TransferRowIntent (envAt t 0)
    ∧ (envAt t (t.rows.length - 1)).loc (saCol state.STATE_COMMIT)
        ≡ (envAt t (t.rows.length - 1)).pub pi.NEW_COMMIT [ZMOD 2013265921] := by
  -- Row 0: active transition row (`isLast = false`, since `0 + 1 < length`). Gates ⟹ intent.
  have h0 := satisfied2Faithful_satisfiedVm permOut hash EffectVmEmitTransfer.transferVmDescriptor
    minit mfin maddrs t (by decide) hf 0 (by omega)
  have hf0 : ((0 : Nat) + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne, Nat.zero_add]; omega
  rw [show (0 == 0) = true from rfl, hf0] at h0
  -- Last row: `isLast = true`; the `.piBinding .last` commit pin fires there.
  have hlast := satisfied2Faithful_satisfiedVm permOut hash EffectVmEmitTransfer.transferVmDescriptor
    minit mfin maddrs t (by decide) hf (t.rows.length - 1) (by omega)
  have hfl : ((t.rows.length - 1) + 1 == t.rows.length) = true := by
    simp only [beq_iff_eq]; omega
  rw [hfl] at hlast
  refine ⟨?_, ?_⟩
  · -- intent: gates at the active row (the first flag is immaterial to `.gate`s; `false false` flatten)
    obtain ⟨hcsT, _⟩ := h0
    have hgates' : ∀ c ∈ EffectVmEmitTransfer.transferRowGates, c.holdsVm (envAt t 0) false false := by
      intro c hc
      have hmem : c ∈ EffectVmEmitTransfer.transferVmDescriptor.constraints := by
        unfold EffectVmEmitTransfer.transferVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
      have := hcsT c hmem
      unfold EffectVmEmitTransfer.transferRowGates EffectVmEmitTransfer.gFieldPassAll at hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
        List.mem_range] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
        simpa only [VmConstraint.holdsVm] using this
    exact (EffectVmEmitTransfer.transferVm_faithful (envAt t 0) hrow).mp hgates'
  · -- commit pin: the last-row `.piBinding .last` clause (`when_last_row()`), fires at `false true`
    obtain ⟨hcs, _⟩ := hlast
    have hl : ∀ c ∈ EffectVmEmitTransfer.boundaryLastPins,
        c.holdsVm (envAt t (t.rows.length - 1)) false true := by
      intro c hc
      have hmem : c ∈ EffectVmEmitTransfer.transferVmDescriptor.constraints := by
        unfold EffectVmEmitTransfer.transferVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
      have hh := hcs c hmem
      unfold EffectVmEmitTransfer.boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (EffectVmEmitTransfer.boundaryLast_pins (envAt t (t.rows.length - 1)) hl).1

/-- **The economic family, re-anchored (burn) — FAITHFUL.** Exactly as `transferV2_pins_intent`: the
deployed burn gates bind on the ACTIVE row 0 (`when_transition()`) and the post commitment on the LAST
row (`when_last_row()`), so a faithful re-anchor takes a `≥ 2`-row trace and reads `CellBurnSpec` from
row 0's gates and the published `state_commit = NEW_COMMIT` on the last row. (A one-row trace's sole
`(true,true)` window binds NEITHER's gates — the degenerate wrap row.) `post.commit` is row 0's
decoded after-state column; the commit pin is the LAST row's column, so the two are stated at their own
rows rather than over-identified on a single window. -/
theorem burnV2_full_sound (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (htwo : 2 ≤ t.rows.length)
    (hrow : EffectVmEmitBurn.IsBurnRow (envAt t 0))
    (pre post : EffectVmEmitTransferSound.CellState) (amt : ℤ)
    (henc : EffectVmEmitBurn.RowEncodes (envAt t 0) pre amt post)
    (hf : Satisfied2Faithful permOut hash burnVmDescriptor2 minit mfin maddrs t) :
    EffectVmEmitBurn.CellBurnSpec pre amt post
    ∧ (envAt t (t.rows.length - 1)).loc (saCol state.STATE_COMMIT)
        ≡ (envAt t (t.rows.length - 1)).pub pi.NEW_COMMIT [ZMOD 2013265921] := by
  -- Row 0: active transition row (`isLast = false`). Gates ⟹ `CellBurnSpec`.
  have h0 := satisfied2Faithful_satisfiedVm permOut hash EffectVmEmitBurn.burnVmDescriptor
    minit mfin maddrs t (by decide) hf 0 (by omega)
  have hf0 : ((0 : Nat) + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne, Nat.zero_add]; omega
  rw [show (0 == 0) = true from rfl, hf0] at h0
  -- Last row: `isLast = true`; the boundary commit pin fires there.
  have hlast := satisfied2Faithful_satisfiedVm permOut hash EffectVmEmitBurn.burnVmDescriptor
    minit mfin maddrs t (by decide) hf (t.rows.length - 1) (by omega)
  have hfl : ((t.rows.length - 1) + 1 == t.rows.length) = true := by simp only [beq_iff_eq]; omega
  rw [hfl] at hlast
  refine ⟨?_, ?_⟩
  · obtain ⟨hcsT, _⟩ := h0
    have hgates : ∀ c ∈ EffectVmEmitBurn.burnRowGates, c.holdsVm (envAt t 0) true false := by
      intro c hc; apply hcsT
      unfold EffectVmEmitBurn.burnVmDescriptor; simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have hgates' := EffectVmEmitBurn.burnRowGates_flag_indep (envAt t 0) true hgates
    exact EffectVmEmitBurn.intent_to_cellSpec (envAt t 0) pre post amt henc
      ((EffectVmEmitBurn.burnVm_faithful (envAt t 0) hrow).mp hgates')
  · obtain ⟨hcs, _⟩ := hlast
    have hl : ∀ c ∈ EffectVmEmitTransfer.boundaryLastPins,
        c.holdsVm (envAt t (t.rows.length - 1)) false true := by
      intro c hc
      have hmem : c ∈ EffectVmEmitBurn.burnVmDescriptor.constraints := by
        unfold EffectVmEmitBurn.burnVmDescriptor; simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
      have hh := hcs c hmem
      unfold EffectVmEmitTransfer.boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
    exact (EffectVmEmitTransfer.boundaryLast_pins (envAt t (t.rows.length - 1)) hl).1

/-- **The economic family, re-anchored (mint) — FAITHFUL.** As `burnV2_full_sound`: the mint gates bind
on the ACTIVE row 0 (`when_transition()`), the post commitment on the LAST row (`when_last_row()`).
Carries the `IsMintRow` premise (the active BridgeMint row, `s_bridge_mint = 1`, `s_noop = 0`). A
`≥ 2`-row trace; `CellMintSpec` from row 0's gates, the published `state_commit = NEW_COMMIT` on the
last row. -/
theorem mintV2_full_sound (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (htwo : 2 ≤ t.rows.length)
    (hrow : EffectVmEmitMint.IsMintRow (envAt t 0))
    (pre post : EffectVmEmitTransferSound.CellState) (amt : ℤ)
    (henc : EffectVmEmitMint.RowEncodes (envAt t 0) pre amt post)
    (hf : Satisfied2Faithful permOut hash mintVmDescriptor2 minit mfin maddrs t) :
    EffectVmEmitMint.CellMintSpec pre amt post
    ∧ (envAt t (t.rows.length - 1)).loc (saCol state.STATE_COMMIT)
        ≡ (envAt t (t.rows.length - 1)).pub pi.NEW_COMMIT [ZMOD 2013265921] := by
  have h0 := satisfied2Faithful_satisfiedVm permOut hash EffectVmEmitMint.mintVmDescriptor
    minit mfin maddrs t (by decide) hf 0 (by omega)
  have hf0 : ((0 : Nat) + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne, Nat.zero_add]; omega
  rw [show (0 == 0) = true from rfl, hf0] at h0
  have hlast := satisfied2Faithful_satisfiedVm permOut hash EffectVmEmitMint.mintVmDescriptor
    minit mfin maddrs t (by decide) hf (t.rows.length - 1) (by omega)
  have hfl : ((t.rows.length - 1) + 1 == t.rows.length) = true := by simp only [beq_iff_eq]; omega
  rw [hfl] at hlast
  refine ⟨?_, ?_⟩
  · obtain ⟨hcsT, _⟩ := h0
    have hgates : ∀ c ∈ EffectVmEmitMint.mintRowGates, c.holdsVm (envAt t 0) true false := by
      intro c hc; apply hcsT
      unfold EffectVmEmitMint.mintVmDescriptor; simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have hgates' := EffectVmEmitMint.mintRowGates_flag_indep (envAt t 0) true hgates
    exact EffectVmEmitMint.intent_to_cellSpec (envAt t 0) pre post amt henc
      ((EffectVmEmitMint.mintVm_faithful (envAt t 0) hrow).mp hgates')
  · obtain ⟨hcs, _⟩ := hlast
    have hl : ∀ c ∈ EffectVmEmitTransfer.boundaryLastPins,
        c.holdsVm (envAt t (t.rows.length - 1)) false true := by
      intro c hc
      have hmem : c ∈ EffectVmEmitMint.mintVmDescriptor.constraints := by
        unfold EffectVmEmitMint.mintVmDescriptor; simp only [List.mem_append]
        exact Or.inr hc
      have hh := hcs c hmem
      unfold EffectVmEmitTransfer.boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
    exact (EffectVmEmitTransfer.boundaryLast_pins (envAt t (t.rows.length - 1)) hl).1

/-! ## §7 — NEWLY EXPRESSIBLE I: the Attenuate cap-crown phase-B circuit leg.

The v1 IR could only PIN the post `cap_root` to a witness-supplied parameter (the
`EffectVmEmitAttenuateA` IR GAP: no in-circuit cap-table opening). The v2 `MapOp` IS that
opening: the held capability is READ out of the before cap-map (authenticated — under CR the
row cannot claim a value the root does not hold), the post root is the GENUINE sorted write of
the kept mask, and `granted ⊑ held` is a BITWISE-SUBMASK lookup into the subset table — the
lattice compare that blocked graduation, now a first-class constraint. -/

/-- The held-capability map key parameter column. -/
def CAP_KEY : Nat := 3
/-- The held rights-mask parameter column (authenticated against the before `cap_root`). -/
def HELD_MASK : Nat := 4
/-- The kept (granted) rights-mask parameter column (written to the post `cap_root`). -/
def KEEP_MASK : Nat := 5
/-- The held/anchor MEMBERSHIP-read key parameter column for the INSERT cap-write wrappers
(delegate / introduce / delegateAtten / grantCap). The held-authority read MUST authenticate a key
DISTINCT from the inserted `CAP_KEY`: the read requires the key PRESENT (`opensTo … some`), while a
fresh INSERT requires the inserted key ABSENT (the deployed `insert_witness` refuses an already-present
key). Binding the read and the insert to the SAME `CAP_KEY` is JOINTLY UNSAT on the wire, so the read
opens against this distinct anchor — the existing held leaf the delegator's authority lives at (the
already-present sorted-tree leaf the fresh edge inserts alongside). For REVOKE (a `write`/remove) the
read and write share `CAP_KEY` (both require it present — consistent), so revoke does NOT use this. -/
def ANCHOR_KEY : Nat := 6
/-- The anchor (held) rights-mask parameter column the INSERT wrappers' membership-read authenticates
at `ANCHOR_KEY` (the value the present anchor leaf opens to). Distinct from `HELD_MASK` (param 4), which
the non-amplification submask lookup compares against the conferred `KEEP_MASK`. -/
def ANCHOR_MASK : Nat := 7
/-- The effect-mask width (the deployed mask width; the deployed AIR splits this into
`mask_lo`/`mask_hi` limbs — same relation, two-limb wire layout). -/
def MASK_BITS : Nat := 30
/-- The custom-table id of the subset (submask) table. -/
def SUBMASK_TID : Nat := 0

/-- **The subset table**: rows `[a, b]` with `a &&& b = a` (i.e. `a ⊑ b` in the mask lattice),
both below `2^bits`. The custom-table realization of the lattice compare. -/
def subsetTable (bits : Nat) : Table :=
  (List.range (2 ^ bits)).flatMap fun (b : ℕ) =>
    ((List.range (2 ^ bits)).filter (fun (a : ℕ) => a &&& b == a)).map
      fun (a : ℕ) => [(a : ℤ), (b : ℤ)]

/-- Subset-table membership, characterized: `[x, y]` is a row iff `x`/`y` are mask naturals
with `x ⊑ y` bitwise. -/
theorem subsetTable_mem_iff (bits : Nat) (x y : ℤ) :
    [x, y] ∈ subsetTable bits ↔
      ∃ a b : Nat, a < 2 ^ bits ∧ b < 2 ^ bits ∧ a &&& b = a
        ∧ x = (a : ℤ) ∧ y = (b : ℤ) := by
  unfold subsetTable
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨b, hb, hmem⟩
    rw [List.mem_map] at hmem
    obtain ⟨a, ha, heq⟩ := hmem
    rw [List.mem_filter] at ha
    obtain ⟨ha, hsub⟩ := ha
    rw [List.mem_range] at ha
    rw [List.mem_range] at hb
    injection heq with h1 h2
    injection h2 with h2 _
    exact ⟨a, b, ha, hb, by simpa using hsub, h1.symm, h2.symm⟩
  · rintro ⟨a, b, ha, hb, hsub, rfl, rfl⟩
    refine ⟨b, List.mem_range.mpr hb, ?_⟩
    rw [List.mem_map]
    exact ⟨a, List.mem_filter.mpr ⟨List.mem_range.mpr ha, by simpa using hsub⟩, rfl⟩

-- Non-vacuity (witness TRUE and FALSE): 1 ⊑ 3 is a row; 2 ⋢ 1 is not; the strict pair refutes.
#guard ([1, 3] : List ℤ) ∈ subsetTable 2
#guard ([0, 0] : List ℤ) ∈ subsetTable 2
#guard ¬ (([2, 1] : List ℤ) ∈ subsetTable 2)
#guard ¬ (([3, 1] : List ℤ) ∈ subsetTable 2)

/-- The held-capability MEMBERSHIP read: the before `cap_root` opens at `param[CAP_KEY]` to
`param[HELD_MASK]` (root unchanged — a read). Guarded by the attenuate selector.

**FORGE NOTE (`bd7ba0bf9`) — CLOSED for the deployed wire.** The guard `selA.ATTENUATE = 2` is the
SET_FIELD column, NOT the live attenuate row's `sel.ATTENUATE_CAPABILITY = 48` — so this V2 op NEVER FIRES
on the deployed wire, AND it writes the V1-STATE cap-root (col 65/87, not a rotated-limb commitment input,
no witness-heap bridge). The DEPLOYED `attenuateV3` / `revokeCapabilityV3` no longer ride these ops: they
were rebased onto the ROTATED-limb write ops (`heldReadOpRot` / `keepWriteOpRot` / `removeWriteOpRot`,
descriptor vars 213→264, guarded on the FIRING selectors `48`/`24`) via `v3OfWithCapWrite` over the tick
face — the SAME close the cap-WRITE wrappers got (the post cap-root folds into the rotated `wireCommitR`
commitment, genuinely bound; the forge-detector `cap_write_attenuate_no_silent_forge` /
`cap_write_revoke_cap_no_silent_forge` reject a fabricated post-root). These V2 ops remain ONLY in the
older `attenuateVmDescriptor2` / `revokeCapabilityVmDescriptor2` (not on the V3 registry wire), kept for the
phase-B expressibility theorems. -/
def heldReadOp : MapOp :=
  { guard   := .var EffectVmEmitAttenuateA.selA.ATTENUATE
  , root    := fun _ => .var (sbCol state.CAP_ROOT)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol HELD_MASK)
  , newRoot := fun _ => .var (sbCol state.CAP_ROOT)
  , op      := .read }

/-- The attenuated WRITE: the post `cap_root` is the genuine sorted insert-or-update of
`param[KEEP_MASK]` at the same key. See `heldReadOp`'s FORGE NOTE — this V1-STATE write needs the
rotated-limb rebase + witness-heap threading, not a bare guard re-point. -/
def keepWriteOp : MapOp :=
  { guard   := .var EffectVmEmitAttenuateA.selA.ATTENUATE
  , root    := fun _ => .var (sbCol state.CAP_ROOT)
  , key     := .var (prmCol CAP_KEY)
  , value   := .var (prmCol KEEP_MASK)
  , newRoot := fun _ => .var (saCol state.CAP_ROOT)
  , op      := .write }

/-- The non-amplification lookup: `(keep, held)` must be a subset-table row. (On NoOp pad rows
the parameter columns are zero and `0 ⊑ 0` is a row, so pads pass.) -/
def submaskLookup : Dregg2.Circuit.DescriptorIR2.Lookup :=
  { table := .custom SUBMASK_TID
  , tuple := [.var (prmCol KEEP_MASK), .var (prmCol HELD_MASK)] }

/-- **`attenuateVmDescriptor2`** — the graduated attenuate descriptor PLUS the phase-B circuit
leg: held-membership map-read, attenuated map-write, and the submask lookup. -/
def attenuateVmDescriptor2 : EffectVmDescriptor2 :=
  { graduateV1 EffectVmEmitAttenuateA.attenuateVmDescriptor with
    constraints :=
      (graduateV1 EffectVmEmitAttenuateA.attenuateVmDescriptor).constraints
        ++ [.mapOp heldReadOp, .mapOp keepWriteOp, .lookup submaskLookup] }

/-- **`attenuateV2_non_amp` — cap-crown phase B, the circuit leg.** On an active attenuate row
of a `Satisfied2` witness (subset table faithful): (1) the held capability IS in the before
cap-map — some sorted heap behind `cap_root` carries `(key ↦ held)`; (2) the post `cap_root` is
the GENUINE sorted write of `(key ↦ keep)`; (3) `keep ⊑ held` BITWISE — non-amplification. The
v1 IR could express none of these. -/
theorem attenuateV2_non_amp (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsub : t.tf (.custom SUBMASK_TID) = subsetTable MASK_BITS)
    (hsat : Satisfied2 hash attenuateVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc EffectVmEmitAttenuateA.selA.ATTENUATE = 1) :
    opensTo hash ((envAt t i).loc (sbCol state.CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) (some ((envAt t i).loc (prmCol HELD_MASK)))
    ∧ writesTo hash ((envAt t i).loc (sbCol state.CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) ((envAt t i).loc (prmCol KEEP_MASK))
        ((envAt t i).loc (saCol state.CAP_ROOT))
    ∧ ∃ a b : Nat, (envAt t i).loc (prmCol KEEP_MASK) = (a : ℤ)
        ∧ (envAt t i).loc (prmCol HELD_MASK) = (b : ℤ) ∧ a &&& b = a := by
  have hrowc := hsat.rowConstraints i hi
  have hread := hrowc (.mapOp heldReadOp) (by simp [attenuateVmDescriptor2])
  have hwrite := hrowc (.mapOp keepWriteOp) (by simp [attenuateVmDescriptor2])
  have hlook := hrowc (.lookup submaskLookup) (by simp [attenuateVmDescriptor2])
  have hr := hread hactive
  have hw := hwrite hactive
  refine ⟨hr.1, hw, ?_⟩
  have hlook' : [(envAt t i).loc (prmCol KEEP_MASK), (envAt t i).loc (prmCol HELD_MASK)]
      ∈ t.tf (.custom SUBMASK_TID) := hlook
  rw [hsub] at hlook'
  obtain ⟨a, b, _, _, hab, hx, hy⟩ := (subsetTable_mem_iff MASK_BITS _ _).mp hlook'
  exact ⟨a, b, hx, hy, hab⟩

/-- **The held leaf is DETERMINED (anti-forgery, FORGERY-3 in Lean form).** ANY opening of the same
before-root at the same key agrees with the satisfying row's held mask — a forged held leaf with
inflated rights is excluded by `opensTo_functional`.

⛑ **OFF THE FLOOR, 2026-07-30.** This took `hCR : Poseidon2SpongeCR hash` and discharged the
opening residual from it. That floor is PROVED FALSE at deployed BabyBear
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so the anti-forgery theorem was true and said
nothing. It now takes the PER-INSTANCE residual directly: `hno` is refutable, decidable on committed
data, and dischargeable by an honest prover at zero cost — the two openings on THIS row simply do not
equivocate. Nothing was weakened: `hCR` implied `hno` (that is what the old proof did), so this is
strictly the more general statement. -/
theorem attenuateV2_held_determined (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsub : t.tf (.custom SUBMASK_TID) = subsetTable MASK_BITS)
    (hsat : Satisfied2 hash attenuateVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc EffectVmEmitAttenuateA.selA.ATTENUATE = 1)
    (v : ℤ)
    (hclaim : opensTo hash ((envAt t i).loc (sbCol state.CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) (some v))
    (hno : ¬ OpenColl hash hclaim
      (attenuateV2_non_amp hash minit mfin maddrs t hsub hsat i hi hactive).1) :
    v = (envAt t i).loc (prmCol HELD_MASK) := by
  have := opensTo_functional hash hclaim _ hno
  simpa using this

/-! ## §7.5 — NEWLY EXPRESSIBLE I.b: the RevokeCapability cap-crown circuit leg (sel 24).

The v1 IR could only PIN the post `cap_root` to a witness-supplied parameter (the
`EffectVmEmitRevokeCapability` v1 FACE GAP: no in-circuit cap-table opening). Revoke is SIMPLER
than Attenuate — it does NOT narrow rights, it DELETES a slot — so the v2 leg has only TWO map ops
and NO submask lookup:

  * **`heldReadOp`** (REUSED from §7) — the held capability is READ out of the before cap-map
    (authenticated: under CR the row cannot claim a value the root does not hold,
    `opensTo_functional`), proving the revoked cap WAS HELD. Rejects fabricating a revoke of a
    non-member.
  * **`removeWriteOp`** — the post `cap_root` is the GENUINE sorted WRITE of the ZERO sentinel
    VALUE at the same key (`writesTo old_root key 0 new_root`): the slot's rights are removed (the
    cap confers nothing). `writesTo_functional` pins the post root — a forged `new_cap_root` is
    excluded.

There is NO `granted ⊑ held` submask lookup: revoke is not an attenuation. The non-amplification
content is structural — revoke can ONLY remove authority (the written value is the ZERO sentinel,
strictly below any held mask). Both map ops fire on the abstract cap-graph-row selector
(`selA.ATTENUATE`), the same one the v1 face's gates use; the concrete sel-24-vs-48 mapping is the
Rust registry's job. -/

/-- The revoke WRITE: the post `cap_root` is the genuine sorted write of the ZERO sentinel value at
the held key (the slot's rights removed). Guarded by the cap-graph-row selector. See `heldReadOp`'s
FORGE NOTE — like attenuate, this V1-STATE write (col 65/87) needs the rotated-limb rebase + witness-heap
threading, not a bare guard re-point. Left at the faithfulness name pending that rebase. -/
def removeWriteOp : MapOp :=
  { guard   := .var EffectVmEmitAttenuateA.selA.ATTENUATE
  , root    := fun _ => .var (sbCol state.CAP_ROOT)
  , key     := .var (prmCol CAP_KEY)
  , value   := .const 0
  , newRoot := fun _ => .var (saCol state.CAP_ROOT)
  , op      := .write }

/-- **`revokeCapabilityVmDescriptor2`** — the graduated revoke descriptor PLUS the cap-crown circuit
leg: held-membership map-read (REUSED) + the ZERO-value remove-write. NO submask lookup (revoke
deletes a slot; it does not narrow rights). -/
def revokeCapabilityVmDescriptor2 : EffectVmDescriptor2 :=
  { graduateV1 EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor with
    constraints :=
      (graduateV1 EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor).constraints
        ++ [.mapOp heldReadOp, .mapOp removeWriteOp] }

/-- **`revokeV2_removes` — cap-crown revoke, the circuit leg.** On an active cap-graph row of a
`Satisfied2` witness: (1) the revoked capability IS in the before cap-map — some sorted heap behind
`cap_root` carries `(key ↦ held)`; (2) the post `cap_root` is the GENUINE sorted write of
`(key ↦ 0)` (the slot's rights removed). The v1 IR could express neither. -/
theorem revokeV2_removes (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash revokeCapabilityVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc EffectVmEmitAttenuateA.selA.ATTENUATE = 1) :
    opensTo hash ((envAt t i).loc (sbCol state.CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) (some ((envAt t i).loc (prmCol HELD_MASK)))
    ∧ writesTo hash ((envAt t i).loc (sbCol state.CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) 0
        ((envAt t i).loc (saCol state.CAP_ROOT)) := by
  have hrowc := hsat.rowConstraints i hi
  have hread := hrowc (.mapOp heldReadOp) (by simp [revokeCapabilityVmDescriptor2])
  have hwrite := hrowc (.mapOp removeWriteOp) (by simp [revokeCapabilityVmDescriptor2])
  have hr := hread hactive
  have hw := hwrite hactive
  -- The write op's `value` is the constant 0; its evaluated value is `0`.
  refine ⟨hr.1, ?_⟩
  simpa [removeWriteOp, EmittedExpr.eval] using hw

/-- **The held leaf is DETERMINED (anti-forgery).** Under CR, ANY opening of the same before-root at
the same key agrees with the satisfying row's held value — a forged held leaf is excluded by
`opensTo_functional`. The revoke analogue of `attenuateV2_held_determined`. -/
theorem revokeV2_held_determined (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash revokeCapabilityVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc EffectVmEmitAttenuateA.selA.ATTENUATE = 1)
    (v : ℤ)
    (hclaim : opensTo hash ((envAt t i).loc (sbCol state.CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) (some v))
    (hno : ¬ OpenColl hash hclaim
      (revokeV2_removes hash minit mfin maddrs t hsat i hi hactive).1) :
    v = (envAt t i).loc (prmCol HELD_MASK) := by
  have := opensTo_functional hash hclaim _ hno
  simpa using this

/-- **The post `cap_root` is DETERMINED (anti-forgery).** Under CR, the new root is the unique sorted
write of `(key ↦ 0)` — a forged `new_cap_root` is excluded by `writesTo_functional`. -/
theorem revokeV2_post_determined (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash revokeCapabilityVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc EffectVmEmitAttenuateA.selA.ATTENUATE = 1)
    (r' : ℤ)
    (hclaim : writesTo hash ((envAt t i).loc (sbCol state.CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) 0 r')
    (hno : ¬ WriteColl hash hclaim
      (revokeV2_removes hash minit mfin maddrs t hsat i hi hactive).2) :
    r' = (envAt t i).loc (saCol state.CAP_ROOT) :=
  writesTo_functional hash hclaim _ hno

/-! ## §7.6 — NEWLY EXPRESSIBLE I.c: the Custom cell-program recursive-proof binding (sel 8).

`Custom` (effect selector 8) dispatches a cell program whose domain constraints are proven
EXTERNALLY. The runtime row is a frozen-economic-block + nonce-tick PASSTHROUGH (byte-identical to
emitEvent's shape — `circuit/src/effect_vm/air.rs` Group "Custom"), so the v1 FACE reuses the
emitEvent passthrough/tick batch with the CUSTOM selector. What the v1 IR could NOT express is the
BINDING of the row's `custom_proof_commitment` to the external proof: the v1 AIR only RECORDS the
commitment in the public inputs and TRUSTS it (the Gap-5 hole — "the Effect VM circuit does NOT
verify the external proof"). The v2 `proofBind` IS that binding: the row commits to a VERIFYING
sub-proof of the named recursion engine whose public-input commitment EQUALS the row's commitment
column and whose program VK equals the row's vk column. This is the FOUR-row-local-kinds gap the
task names: none of lookup/mem/map/umem can fold in another STARK proof; `proofBind` does, by the
SAME named-recursion boundary the aggregate prover already carries. -/

/-- The Custom-row `custom_program_vk_hash` parameter column (`param.CUSTOM_VK_HASH_BASE = 0`;
the low felt of the 4-felt program-VK identifier the row binds). -/
def CUSTOM_VK : Nat := 0
/-- The Custom-row `custom_proof_commitment` parameter column (`param.CUSTOM_PROOF_COMMIT_BASE =
4`; the low felt of the 4-felt external-proof commitment the row binds). -/
def CUSTOM_COMMIT : Nat := 4
/-- The Custom effect's selector column (`columns::sel::CUSTOM = 8`). -/
def SEL_CUSTOM : Nat := 8

/-- The Custom v1 FACE: the emitEvent frozen-economic-block + nonce-tick passthrough batch (the
SAME runtime row shape the Custom AIR pins) with the CUSTOM selector (8) instead of emitEvent's
(25). State flows through unchanged; the nonce ticks like any non-NoOp effect. -/
def customV1Face : EffectVmDescriptor :=
  { name        := "dregg-effectvm-custom-v1"
  , traceWidth  := EFFECT_VM_WIDTH
  , piCount     := pi.V1_PI_COUNT
  , constraints := EffectVmEmitEmitEvent.emitTickRowGates
                     ++ EffectVmEmitTransfer.transitionAll
                     ++ EffectVmEmitTransfer.boundaryFirstPins
                     ++ EffectVmEmitTransfer.boundaryLastPins
                     ++ selectorGates SEL_CUSTOM
  , hashSites   := []
  , ranges      := [] }

/-- ⚑ **THE CUSTOM BINDING OP, AT EIGHT LANES** (the 2026-08-05 widening). The deployed objects are
eight felts each — `custom_proof_pi_commitment` is the full `WideHash` squeeze
(`PROOF_BIND_COMMIT_WIDTH = 8`) and `custom_program_vk_hash` is `bytes32_to_8_limbs` — but only the
LOW four of each live in the `param` block. The HIGH four ride member-local TEETH columns, whose
base differs between the un-rotated face and the rotated V3 member, so the op is parameterized by
the two teeth bases rather than duplicated.

Lane order is low limb first: `param[CUSTOM_COMMIT + 0..4]` then `commitHi + 0..4`, and the same
for the VK. That is the order `custom_proof_pi_commitment`'s `to_felts()` produces and the order
the fold's lane-by-lane `connect` walks. -/
def customProofBindAt (commitHi vkHi : Nat) : Dregg2.Circuit.DescriptorIR2.ProofBind :=
  { guard  := .var SEL_CUSTOM
  , commit := (List.range 4).map (fun k => .var (prmCol (CUSTOM_COMMIT + k)))
                ++ (List.range 4).map (fun k => .var (commitHi + k))
  , vk     := (List.range 4).map (fun k => .var (prmCol (CUSTOM_VK + k)))
                ++ (List.range 4).map (fun k => .var (vkHi + k))
    -- ⚑ DECLARED UNPINNED, and this is the honest answer for Custom specifically. The row-local
    -- seam can pin a program and a commitment; Custom can supply NEITHER — it exists to dispatch an
    -- ARBITRARY registered cell program, and its commitment is `custom_proof_pi_commitment` of the
    -- sub-proof's public inputs, computed OFF-ROW. No expression over this row recomputes it; the
    -- binding is the fold's lane-by-lane `connect`. So `proofBindDeclarative customVmDescriptor2 = 1`
    -- and the residual is a COUNTED VALUE in the emitted bytes rather than a `True` nobody could see.
    -- ⚑ What DID change on 2026-08-05 is the WIDTH of what the fold has to connect to: eight
    -- declared lanes, not lane 0 with seven felts unnamed by any constraint.
  , vkPin  := none
  -- ⚑ 2026-08-10: the commit half is the Custom effect's `custom-proof-commitment` PORT,
  -- covered by the fold's lane-by-lane `connect`. The `none` that used to sit here emitted
  -- nothing AND named nothing; the port emits nothing and NAMES the welder.
  , bound  := .port ⟨"custom-proof-commitment", "dregg_circuit_prove::joint_turn_recursive::prove_custom_binding_node"⟩ }

/-- The un-rotated graduated face's commit-teeth base: the HIGH four commitment limbs, appended at
the END of the graduated width (the V2 twin of `EffectVmEmitRotationV3.CUSTOM_COMMIT_TEETH_COL`). -/
def CUSTOM_V2_COMMIT_TEETH_COL : Nat := (graduateV1 customV1Face).traceWidth

/-- The un-rotated face's VK-teeth base: the HIGH four program-VK limbs, past the commit teeth. -/
def CUSTOM_V2_VK_TEETH_COL : Nat := CUSTOM_V2_COMMIT_TEETH_COL + 4

/-- The Custom row's proof-binding op on the UN-ROTATED graduated face. -/
def customProofBind : Dregg2.Circuit.DescriptorIR2.ProofBind :=
  customProofBindAt CUSTOM_V2_COMMIT_TEETH_COL CUSTOM_V2_VK_TEETH_COL

/-- **`customVmDescriptor2`** — the graduated Custom descriptor PLUS the recursive-proof-binding
leg: the runtime passthrough face graduated onto IR-v2, with the `proofBind` op that ties the
row's commitment to a verifying external sub-proof (the accumulator constraint the per-row IR
gained — `DescriptorIR2.ProofBind`).

⚑ **FLAG DAY 2026-08-05 (+8 columns, 188 → 196).** The seam widened from one felt to eight lanes,
so the face carries the HIGH four limbs of the commitment and of the program VK on eight appended
teeth columns. A four-lane artifact no longer loads: `check_descriptor2` refuses a bind below
`PROOF_BIND_MIN_LANES`. -/
def customVmDescriptor2 : EffectVmDescriptor2 :=
  { graduateV1 customV1Face with
    traceWidth  := (graduateV1 customV1Face).traceWidth + 8
    constraints := (graduateV1 customV1Face).constraints ++ [.proofBind customProofBind] }

/-- ⚑ **THE UN-ROTATED CUSTOM SEAM IS AT THE LANE FLOOR** — eight lanes, equal on both halves, no
truncated pin. This is the verdict the Rust admission door applies to the emitted bytes. -/
theorem customProofBind_widthOk : customProofBind.widthOk = true := by decide

/-- The Custom v1 face is graduable (so `graduateV1_sound`/`_complete`/`_faithful` apply to the
passthrough leg). -/
theorem custom_graduable : graduable customV1Face = true := by decide

/-- The graduated Custom base declares no proof-binding ops (every graduated constraint is a
`.base` or a `.lookup`). -/
theorem proofBindsOf_graduateV1 (d : EffectVmDescriptor) (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length) :
    proofBindsOf (graduateV1 d hAdm) = [] := by
  unfold proofBindsOf
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  rcases constraints_graduateV1_shapes d hAdm c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩ <;> rfl

/-- The graduated Custom descriptor declares EXACTLY the one proof-binding op. -/
theorem proofBindsOf_customVmDescriptor2 :
    proofBindsOf customVmDescriptor2 = [customProofBind] := by
  have hbase : proofBindsOf (graduateV1 customV1Face) = [] :=
    proofBindsOf_graduateV1 customV1Face _
  unfold proofBindsOf at hbase ⊢
  show ((graduateV1 customV1Face).constraints ++ [VmConstraint2.proofBind customProofBind]).filterMap
      _ = _
  rw [List.filterMap_append, hbase]
  rfl

/-- **`customV2_binds_proof` — cap-crown analog for Custom, the circuit leg.** On an active Custom
row of a `Satisfied2Custom` witness: the row's `custom_proof_commitment` LANES ARE the public-input
commitment of a VERIFYING external sub-proof, and its `custom_program_vk_hash` LANES are that
proof's program VK. The v1 IR could express NEITHER — it recorded the commitment and trusted it.

⚑ **EIGHT LANES since 2026-08-05.** The equality is of lane VECTORS, so a sub-proof agreeing with
the row on limb 0 and differing above it does not discharge this. -/
theorem customV2_binds_proof (hash : List ℤ → ℤ)
    (E : Dregg2.Circuit.DescriptorIR2.ProofEngine)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2Custom hash E customVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc (SEL_CUSTOM) = 1) :
    E.boundTo (customProofBind.commit.map (·.eval (envAt t i).loc))
      (customProofBind.vk.map (·.eval (envAt t i).loc)) := by
  have hm : customProofBind ∈ proofBindsOf customVmDescriptor2 := by
    rw [proofBindsOf_customVmDescriptor2]; exact List.mem_cons_self
  exact proofBind_bound hash E customVmDescriptor2 hsat hm i hi
    (by exact hactive)

/-- **The bound commitment is DETERMINED (anti-forgery, the Custom anti-ghost).** Under the named
engine binding, the program VK a Custom row attests is FORCED by its `custom_proof_commitment`: a
forged row claiming a commitment that no verifying sub-proof exposes — or claiming the genuine
commitment but a WRONG vk — cannot have a `Satisfied2Custom` witness. The recursion analog of
`attenuateV2_held_determined`. -/
theorem customV2_proof_determined (hash : List ℤ → ℤ)
    (E : Dregg2.Circuit.DescriptorIR2.ProofEngine)
    (hE : Dregg2.Circuit.DescriptorIR2.EngineBinding E)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2Custom hash E customVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc (SEL_CUSTOM) = 1)
    (q : E.Proof) (hq : E.verify q = true)
    (hqc : E.piCommit q = customProofBind.commit.map (·.eval (envAt t i).loc)) :
    E.vkOf q = customProofBind.vk.map (·.eval (envAt t i).loc) := by
  have hm : customProofBind ∈ proofBindsOf customVmDescriptor2 := by
    rw [proofBindsOf_customVmDescriptor2]; exact List.mem_cons_self
  exact proofBind_determined hash E hE customVmDescriptor2 hsat hm i hi
    (by exact hactive) q hq hqc

/-! ## §8 — NEWLY EXPRESSIBLE II: SetField with a DYNAMIC slot index.

ONE descriptor for all 8 slots: the field write is a `MemOp` at address `param[SLOT]` — the
dynamic indexing the v1 column IR could not express (it needed 8 per-slot descriptors). The
write→read transport is carried by the PROVED memory argument (`satisfied2_mem_consistent` =
Blum applied) with ZERO hashing. POST-FLAG-DAY shape: the 8 user-field cells are memory
addresses `0..7`. -/

/-- The dynamic slot-index parameter column. -/
def SLOT : Nat := 1
/-- The written value parameter column (`param.AMOUNT`, the same carrier the static setField
uses). -/
def NEW_VAL : Nat := EffectVmEmitSetField.VALUE
/-- The claimed previous value witness column. -/
def PREV_VAL : Nat := 2
/-- The claimed previous serial witness column. -/
def PREV_SERIAL : Nat := 6
/-- The read-back value column (the memory argument transports the write to it). -/
def READBACK : Nat := 7

/-- The slot expression. -/
def eSlot : EmittedExpr := .var (prmCol SLOT)
/-- `slot - c` as an expression. -/
def slotMinus (c : ℤ) : EmittedExpr := .add eSlot (.const (-c))

/-- The slot-range gate body: `∏_{j<8} (slot - j)` — the degree-8 product vanishing exactly on
`{0..7}`. (On pad rows the zeroed slot column makes the first factor vanish.) -/
def gSlotRange : EmittedExpr :=
  .mul (.mul (.mul (slotMinus 0) (slotMinus 1)) (.mul (slotMinus 2) (slotMinus 3)))
       (.mul (.mul (slotMinus 4) (slotMinus 5)) (.mul (slotMinus 6) (slotMinus 7)))

/-- The slot-range gate's denotation, FIELD-FAITHFUL. The gate body is now `∏_{j<8}(slot - j) ≡ 0
[ZMOD p]` (`VmConstraint.holdsVm` pins the degree-8 product only mod `p`). Under the DEPLOYED
range-check canonicality of the slot column (`0 ≤ slot < p`, the same invariant the negative teeth
consume), a prime `p` dividing the product divides exactly one factor `slot - j`, and canonicality
collapses `p ∣ (slot - j)` to the EXACT integer `slot = j`. So the conclusion keeps its teeth — the
dynamic memory index is a genuine natural `< 8`, not merely `≡` a residue that could escape the field
block by a multiple of `p`. -/
theorem gSlotRange_holds_iff (env : VmRowEnv) (isFirst : Bool)
    (hcanon : 0 ≤ env.loc (prmCol SLOT) ∧ env.loc (prmCol SLOT) < 2013265921) :
    (VmConstraint.gate gSlotRange).holdsVm env isFirst false ↔
      ∃ j : Nat, j < 8 ∧ env.loc (prmCol SLOT) = (j : ℤ) := by
  obtain ⟨hlo, hhi⟩ := hcanon
  simp only [VmConstraint.holdsVm, gSlotRange, slotMinus, eSlot, EmittedExpr.eval]
  constructor
  · intro h
    rw [Int.modEq_zero_iff_dvd] at h
    rcases EffectVmEmitTransfer.pPrimeInt.dvd_mul.mp h with h | h
    · rcases EffectVmEmitTransfer.pPrimeInt.dvd_mul.mp h with h | h
      · rcases EffectVmEmitTransfer.pPrimeInt.dvd_mul.mp h with h | h
        · obtain ⟨k, hk⟩ := h; exact ⟨0, by norm_num, by omega⟩
        · obtain ⟨k, hk⟩ := h; exact ⟨1, by norm_num, by omega⟩
      · rcases EffectVmEmitTransfer.pPrimeInt.dvd_mul.mp h with h | h
        · obtain ⟨k, hk⟩ := h; exact ⟨2, by norm_num, by omega⟩
        · obtain ⟨k, hk⟩ := h; exact ⟨3, by norm_num, by omega⟩
    · rcases EffectVmEmitTransfer.pPrimeInt.dvd_mul.mp h with h | h
      · rcases EffectVmEmitTransfer.pPrimeInt.dvd_mul.mp h with h | h
        · obtain ⟨k, hk⟩ := h; exact ⟨4, by norm_num, by omega⟩
        · obtain ⟨k, hk⟩ := h; exact ⟨5, by norm_num, by omega⟩
      · rcases EffectVmEmitTransfer.pPrimeInt.dvd_mul.mp h with h | h
        · obtain ⟨k, hk⟩ := h; exact ⟨6, by norm_num, by omega⟩
        · obtain ⟨k, hk⟩ := h; exact ⟨7, by norm_num, by omega⟩
  · rintro ⟨j, hj, hs⟩
    rw [Int.modEq_zero_iff_dvd, hs]
    interval_cases j <;> norm_num

/-- The DYNAMIC field write: a memory-table write at address `param[SLOT]`. -/
def fieldWriteOp : MemOp :=
  { guard      := .var EffectVmEmitSetField.SEL_SET_FIELD
  , addr       := .var (prmCol SLOT)
  , value      := .var (prmCol NEW_VAL)
  , prevValue  := .var (prmCol PREV_VAL)
  , prevSerial := .var (prmCol PREV_SERIAL)
  , kind       := .write }

/-- The read-back: a memory-table read at the SAME dynamic address. Its claimed prev tuple is
the write's `(value, serial 1)`; the read discipline ties `value = prevValue`, both riding the
`READBACK` column. -/
def fieldReadbackOp : MemOp :=
  { guard      := .var EffectVmEmitSetField.SEL_SET_FIELD
  , addr       := .var (prmCol SLOT)
  , value      := .var (prmCol READBACK)
  , prevValue  := .var (prmCol READBACK)
  , prevSerial := .const 1
  , kind       := .read }

/-- **`setFieldDynVmDescriptor2`** — ONE setField descriptor for all 8 slots: selector binding,
slot-range gate, the dynamic write, the read-back. -/
def setFieldDynVmDescriptor2 : EffectVmDescriptor2 :=
  { name        := "dregg-effectvm-setfield-dyn-v2"
  , traceWidth  := EFFECT_VM_WIDTH
  , piCount     := pi.V1_PI_COUNT
  , tables      := v2Tables EFFECT_VM_WIDTH
  , constraints :=
      [ .base (.gate gSlotRange)
      , .base (selectorGate EffectVmEmitSetField.SEL_SET_FIELD)
      , .memOp fieldWriteOp
      , .memOp fieldReadbackOp ]
  , hashSites   := []
  , ranges      := [] }

/-- The gathered memory log of a one-row active setField-dyn trace: exactly the dynamic write
followed by the read-back. -/
theorem setFieldDyn_memLog (t : VmTrace) (hone : t.rows.length = 1)
    (hactive : (envAt t 0).loc EffectVmEmitSetField.SEL_SET_FIELD = 1) :
    memLog setFieldDynVmDescriptor2 t =
      [ ⟨.write, (envAt t 0).loc (prmCol SLOT), (envAt t 0).loc (prmCol NEW_VAL),
          (envAt t 0).loc (prmCol PREV_VAL), ((envAt t 0).loc (prmCol PREV_SERIAL)).toNat⟩
      , ⟨.read, (envAt t 0).loc (prmCol SLOT), (envAt t 0).loc (prmCol READBACK),
          (envAt t 0).loc (prmCol READBACK), 1⟩ ] := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hone
  have henv : (envAt t 0).loc = a := by
    simp [envAt, ha]
  rw [henv] at hactive
  unfold memLog memOpsOf setFieldDynVmDescriptor2
  rw [ha]
  simp [MemOp.opAt?, fieldWriteOp, fieldReadbackOp, EmittedExpr.eval, hactive, henv]

/-- **The dynamic write→read transport — Blum applied, zero hashing.** On a satisfying one-row
active trace, the read-back column carries EXACTLY the written value: the memory argument
(`satisfied2_mem_consistent` = the proved `memcheck_sound`) transports the dynamic write to the
dynamic read with no authenticated structure at all. -/
theorem setFieldDyn_readback_genuine (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hone : t.rows.length = 1)
    (hactive : (envAt t 0).loc EffectVmEmitSetField.SEL_SET_FIELD = 1)
    (hsat : Satisfied2 hash setFieldDynVmDescriptor2 minit mfin maddrs t) :
    (envAt t 0).loc (prmCol READBACK) = (envAt t 0).loc (prmCol NEW_VAL) := by
  have hcons := satisfied2_mem_consistent hash _ minit mfin maddrs t hsat
  rw [setFieldDyn_memLog t hone hactive] at hcons
  obtain ⟨_, hr, _⟩ := hcons
  have := hr rfl
  simpa [MemoryChecking.step] using this

/-- The slot is genuinely bounded on every ACTIVE row of a satisfying trace (the dynamic index
cannot escape the field block). The bound is the `gSlotRange` degree-8 product GATE, which runs
under the deployed `builder.when_transition()` — so it binds on every transition row (`isLast =
false`, i.e. `i + 1 ≠ t.rows.length`) and is vacuous on the wrap/last row; the active effect row of
any real trace is a transition row. -/
theorem setFieldDyn_slot_bounded (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash setFieldDynVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length)
    (hcanon : 0 ≤ (envAt t i).loc (prmCol SLOT) ∧ (envAt t i).loc (prmCol SLOT) < 2013265921) :
    ∃ j : Nat, j < 8 ∧ (envAt t i).loc (prmCol SLOT) = (j : ℤ) := by
  have hmem : VmConstraint2.base (.gate gSlotRange) ∈ setFieldDynVmDescriptor2.constraints := by
    simp [setFieldDynVmDescriptor2]
  have h := hsat.rowConstraints i hi _ hmem
  have hf : (i + 1 == t.rows.length) = false := by simp only [beq_eq_false_iff_ne]; exact hnl
  rw [hf] at h
  exact (gSlotRange_holds_iff (envAt t i) (i == 0) hcanon).mp h

/-! ## §9 — The v2 registry + wire/shape tripwires. -/

/-- The graduated v2 registry (the wire strings are `emitVmJson2` of each; the regeneration
executable wires this list). -/
def v2Registry : List (String × EffectVmDescriptor2) :=
  [ ("transferVmDescriptor2", transferVmDescriptor2)
  , ("burnVmDescriptor2", burnVmDescriptor2)
  , ("mintVmDescriptor2", mintVmDescriptor2)
  , ("noteSpendVmDescriptor2", noteSpendVmDescriptor2)
  , ("noteCreateVmDescriptor2", noteCreateVmDescriptor2)
  , ("cellSealVmDescriptor2", cellSealVmDescriptor2)
  , ("cellDestroyVmDescriptor2", cellDestroyVmDescriptor2)
  , ("refusalVmDescriptor2", refusalVmDescriptor2)
  , ("setPermsVmDescriptor2", setPermsVmDescriptor2)
  , ("setVKVmDescriptor2", setVKVmDescriptor2)
  , ("exerciseVmDescriptor2", exerciseVmDescriptor2)
  , ("pipelinedSendVmDescriptor2", pipelinedSendVmDescriptor2)
  , ("refreshVmDescriptor2", refreshVmDescriptor2)
  , ("incrementNonceVmDescriptor2", incrementNonceVmDescriptor2)
  , ("revokeVmDescriptor2", revokeVmDescriptor2)
  , ("introduceVmDescriptor2", introduceVmDescriptor2)
  , ("attenuateVmDescriptor2", attenuateVmDescriptor2)
  , ("revokeCapabilityVmDescriptor2", revokeCapabilityVmDescriptor2)
  , ("customVmDescriptor2", customVmDescriptor2)
  , ("setFieldDynVmDescriptor2", setFieldDynVmDescriptor2) ]
  ++ (List.finRange 8).map fun slot =>
      (s!"setFieldVmDescriptor2-{slot.val}", setFieldVmDescriptor2 slot)

#guard v2Registry.length == 28

-- The graduated transfer: 36 embedded v1 constraints + 4 chip lookups + 2 range lookups; the
-- five EPOCH tables declared; NO legacy carriers (graduation means graduation).
#guard transferVmDescriptor2.constraints.length == 36 + 4 + 2
#guard transferVmDescriptor2.tables.length == 5
#guard transferVmDescriptor2.hashSites.length == 0
#guard transferVmDescriptor2.ranges.length == 0
#guard transferVmDescriptor2.name == "dregg-effectvm-transfer-v1"
-- The enriched attenuate carries exactly the 3 phase-B constraints past its graduated base.
#guard attenuateVmDescriptor2.constraints.length
        == attenuateVmDescriptor2Base.constraints.length + 3
-- The enriched revoke carries exactly the 2 cap-crown constraints (held-read + remove-write, NO
-- submask) past its graduated base.
#guard revokeCapabilityVmDescriptor2.constraints.length
        == (graduateV1 EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor).constraints.length + 2
-- The revoke v1 face is graduable (so `graduateV1_sound`/`_complete`/`_faithful` apply).
#guard graduable EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor
-- The revoke descriptor declares exactly the 2 map ops (held-read + remove-write), no submask.
#guard (mapOpsOf revokeCapabilityVmDescriptor2).length == 2
-- The Custom v1 face is graduable, and the graduated descriptor carries EXACTLY one proof-binding
-- op past its passthrough base (no mem/map/umem ops — Custom's only NEWLY-EXPRESSIBLE content is
-- the recursive-proof binding).
#guard graduable customV1Face
#guard (proofBindsOf customVmDescriptor2).length == 1
#guard (memOpsOf customVmDescriptor2).length == 0
#guard (mapOpsOf customVmDescriptor2).length == 0
#guard customVmDescriptor2.name == "dregg-effectvm-custom-v1"
-- The dyn setField is mem-op shaped: 2 mem ops, no map ops.
#guard (memOpsOf setFieldDynVmDescriptor2).length == 2
#guard (mapOpsOf setFieldDynVmDescriptor2).length == 0
-- Every registry entry is a well-formed, populated descriptor (named, non-empty constraints,
-- non-zero width). This is the cheap STRUCTURAL smoke test — it replaces a former
-- `emitVmJson2 d |>.startsWith "{\"name\":\""` prefix check that serialized all 39 registry
-- descriptors to full JSON at elaboration time (~9 s of the file's ~13 s; measured). `emitVmJson2`
-- correctness itself is covered EXACTLY and per-family by the `#guard emitVmJson2 <desc> == "…"`
-- byte-pins in each `*Emit.lean`, so re-serializing the whole registry here was redundant compute.
#guard v2Registry.all fun (_, d) => !d.name.isEmpty && !d.constraints.isEmpty && d.traceWidth != 0

#assert_axioms graduable_spec
#assert_axioms constraints_graduateV1_shapes
#assert_axioms memOpsOf_graduateV1
#assert_axioms mapOpsOf_graduateV1
#assert_axioms memLog_graduateV1
#assert_axioms mapLog_graduateV1
#assert_axioms toExpr_eval_eq_resolve
#assert_axioms siteTuple_eval_resolved
#assert_axioms hacc_extend
#assert_axioms go_of_siteLookups
#assert_axioms siteLookups_sound
#assert_axioms graduateV1_sound
#assert_axioms go_siteLookups_complete
#assert_axioms chipLogOf_sound
#assert_axioms graduateV1_complete
#assert_axioms graduateV1_faithful
#assert_axioms transferV2_pins_intent
#assert_axioms burnV2_full_sound
#assert_axioms mintV2_full_sound
#assert_axioms subsetTable_mem_iff
#assert_axioms attenuateV2_non_amp
#assert_axioms attenuateV2_held_determined
#assert_axioms revokeV2_removes
#assert_axioms revokeV2_held_determined
#assert_axioms revokeV2_post_determined
#assert_axioms custom_graduable
#assert_axioms proofBindsOf_graduateV1
#assert_axioms proofBindsOf_customVmDescriptor2
#assert_axioms customV2_binds_proof
#assert_axioms customV2_proof_determined
#assert_axioms gSlotRange_holds_iff
#assert_axioms setFieldDyn_memLog
#assert_axioms setFieldDyn_readback_genuine
#assert_axioms setFieldDyn_slot_bounded

/-! ## §10 — THE MULTI-WIDTH GRADUATION (`graduableWide`): 15-bit borrow-limb range teeth reach
the graduation/rotation tower.

`graduable` demands EVERY range tooth at the shared `BAL_LIMB_BITS = 30` width, and `graduateV1`
lowers every tooth into the ONE 30-bit table — correct for the surveyed registry, but it LOCKS OUT
the §11.7 hardened availability descriptors (`EffectVmEmitTransfer.transferVmDescriptorAvail`):
their borrow-weld limbs are 15-BIT teeth (`transferAvailRanges`), and lowering a 15-bit tooth into
the 30-bit table would only bound the limb `< 2^30` — DEFEATING the borrow proof, whose residuals
must stay `< 2^16 < p` (`transferAvail_derives_availability`). This section is the multi-width
enabler, PURELY ADDITIVE beside the single-width path:

  * `WIDE_RANGE_WIDTHS` — the allowed widths `{15, BAL_LIMB_BITS}`;
  * `rangeTidW` — the width-indexed table id (`BAL_LIMB_BITS` stays the shared `.range`; 15 rides
    a width-tagged custom id) + `rangeLookupW`, the WIDTH-PRESERVING lowering;
  * `graduableWide` — the relaxed decidable side condition (every tooth at an ALLOWED width;
    `graduable ⟹ graduableWide`, `graduableWide_of_graduable`);
  * `graduateV1Wide` — the multi-width graduation: identical to `graduateV1` except each range
    tooth lowers into ITS OWN width's table (a 15-bit limb is bounded `< 2^15` EXACTLY);
  * `graduateV1Wide_sound` / `Satisfied2FaithfulWide` / `satisfied2FaithfulWide_satisfiedVm` —
    the soundness collapse mirroring §4/§4F, per-width table pins in place of the single pin.

Deployment note (do NOT over-read): the deployed `Ir2Air` assembly realizes the `.range` pin
today; the 15-bit pin (`t.tf (rangeTidW 15) = rangeRows 15`) is the table the availability-weld
assembly must realize (the Rust weld's `RangeSpec { bits: 15 }` teeth, `transfer_avail_weld.rs`) —
part of the SAME ember-gated registry/VK regen that routes the hardened descriptor. -/

/-- The allowed multi-width range widths: 15 = the borrow-weld limb width (`transferAvailRanges` —
residuals stay `< 2^16 < p`), `BAL_LIMB_BITS` = 30 = the shared balance-limb width. -/
def WIDE_RANGE_WIDTHS : List Nat := [15, BAL_LIMB_BITS]

/-- The width-tagged custom-table id base for non-`BAL_LIMB_BITS` range widths (offset past the
allocated custom ids: SUBMASK 0, UMEM 1, umem-boundary 2). Width `b` rides `.custom (64 + b)` —
e.g. the 15-bit table is `.custom 79` (wire id 84). -/
def RANGE_W_TID_BASE : Nat := 64

/-- The width-indexed range-table id: the shared 30-bit table stays `.range` (so the single-width
world embeds unchanged); every other allowed width rides its width-tagged custom id. -/
def rangeTidW (bits : Nat) : TableId :=
  if bits = BAL_LIMB_BITS then .range else .custom (RANGE_W_TID_BASE + bits)

theorem rangeTidW_bal : rangeTidW BAL_LIMB_BITS = .range := rfl

/-- The per-width table pins subsume the legacy single pin (`rangeTidW BAL_LIMB_BITS = .range`). -/
theorem rangeTablesWide_range {tf : TraceFamily}
    (h : ∀ b ∈ WIDE_RANGE_WIDTHS, tf (rangeTidW b) = rangeRows b) :
    tf .range = rangeRows BAL_LIMB_BITS := by
  have hb : BAL_LIMB_BITS ∈ WIDE_RANGE_WIDTHS := by simp [WIDE_RANGE_WIDTHS]
  simpa [rangeTidW_bal] using h BAL_LIMB_BITS hb

/-- The width-preserving range lowering: a `bits`-wide tooth looks up ITS OWN width's table. -/
def rangeLookupW (r : VmRange) : Dregg2.Circuit.DescriptorIR2.Lookup :=
  { table := rangeTidW r.bits, tuple := [.var r.wire] }

/-- A v1 descriptor is WIDE-GRADUABLE: well-formed site references, chip-rate fit, and every
range tooth at an ALLOWED width (15-bit borrow limbs admitted beside the 30-bit balance limbs). -/
def graduableWide (d : EffectVmDescriptor) : Bool :=
  sitesWF d.hashSites && sitesFit d.hashSites
    && d.ranges.all (fun r => decide (r.bits ∈ WIDE_RANGE_WIDTHS))

/-- Unpack the decidable `graduableWide` check into the three propositional side conditions. -/
theorem graduableWide_spec {d : EffectVmDescriptor} (h : graduableWide d = true) :
    sitesWF d.hashSites = true ∧ sitesFit d.hashSites = true
      ∧ ∀ r ∈ d.ranges, r.bits ∈ WIDE_RANGE_WIDTHS := by
  unfold graduableWide at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun r hr => ?_⟩
  have := List.all_eq_true.mp h3 r hr
  exact of_decide_eq_true this

/-- The single-width gate implies the wide gate (30 is an allowed width). -/
theorem graduableWide_of_graduable {d : EffectVmDescriptor} (h : graduable d = true) :
    graduableWide d = true := by
  obtain ⟨h1, h2, h3⟩ := graduable_spec h
  unfold graduableWide
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨h1, h2⟩, fun r hr => ?_⟩
  simp [h3 r hr, WIDE_RANGE_WIDTHS]

/-- **`graduateV1Wide`** — the multi-width re-anchor: `graduateV1` verbatim except each range tooth
lowers via `rangeLookupW` into its OWN width's table. The width-tagged range tables join the
declared table family. -/
def graduateV1Wide (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ d.hashSites, ChipArityAdmitted s.inputs.length := by graduate_arity) :
    EffectVmDescriptor2 :=
  { name        := d.name
  , traceWidth  := d.traceWidth + (CHIP_OUT_LANES - 1) * d.hashSites.length
  , piCount     := d.piCount
  , tables      :=
      v2Tables (d.traceWidth + (CHIP_OUT_LANES - 1) * d.hashSites.length)
        ++ (WIDE_RANGE_WIDTHS.filter (fun b => !(b == BAL_LIMB_BITS))).map
             (fun b => ⟨rangeTidW b, "range_w" ++ toString b, 1, .rangeLimb b⟩)
  , constraints :=
      d.constraints.map .base
        ++ graduateSites d.hashSites d.traceWidth hAdm
        ++ d.ranges.map (fun r => .lookup (rangeLookupW r))
  , hashSites   := []
  , ranges      := [] }

/-- **A width-preserving range lookup REPLACES a v1 `VmRange` tooth at ITS OWN width.** Against
the faithful `bits`-wide table, looking up `[col w]` enforces exactly `VmRange.holds ⟨w, bits⟩` —
the wire lies in `[0, 2^bits)`. The 15-bit instance is the borrow-proof enabler. -/
theorem lookup_replaces_rangeW (bits : Nat) (tf : TraceFamily)
    (hr : tf (rangeTidW bits) = rangeRows bits) (env : VmRowEnv) (w : Nat)
    (h : Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt tf env ⟨rangeTidW bits, [.var w]⟩) :
    VmRange.holds env ⟨w, bits⟩ := by
  unfold Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt at h
  rw [hr] at h
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval] at h
  exact (range_row_mem_iff _ bits).mp h

/-- **`graduateV1Wide_sound`** — the multi-width re-anchor keystone, mirroring `graduateV1_sound`:
a `Satisfied2` witness of the wide graduation, against a sound chip table + the per-width faithful
range tables, yields the FULL v1 denotation `satisfiedVm` (15-bit teeth bounded `< 2^15` EXACTLY)
on every row window. -/
theorem graduateV1Wide_sound (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrangeW : ∀ b ∈ WIDE_RANGE_WIDTHS, t.tf (rangeTidW b) = rangeRows b)
    (hgrad : graduableWide d = true)
    (hsat : Satisfied2 hash
      (graduateV1Wide d (sitesFit_admitted (graduableWide_spec hgrad).2.1)) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  obtain ⟨hwf, hfit, hbits⟩ := graduableWide_spec hgrad
  intro i hi
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_, ?_⟩
  · -- the v1 constraints, embedded
    intro c hc
    have hmem : VmConstraint2.base c ∈ (graduateV1Wide d (sitesFit_admitted hfit)).constraints := by
      unfold graduateV1Wide
      simp only [List.mem_append, List.mem_map, mem_graduateSites]
      exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    exact hrow _ hmem
  · -- the hash sites, via the chip-lookup induction (verbatim `graduateV1_sound`)
    refine siteLookups_sound hash (t.tf .poseidon2) hchip (envAt t i) d.hashSites d.traceWidth hwf
      (sitesFit_admitted hfit) ?_
    · intro j hj
      have hmem : VmConstraint2.lookup
          (siteLookup d.hashSites d.hashSites[j]
            (d.traceWidth + (CHIP_OUT_LANES - 1) * j)
            (sitesFit_admitted hfit _ (List.getElem_mem hj)))
          ∈ (graduateV1Wide d (sitesFit_admitted hfit)).constraints := by
        unfold graduateV1Wide
        simp only [List.mem_append, List.mem_map, mem_graduateSites]
        exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
      exact hrow _ hmem
  · -- the range teeth, each via ITS OWN width's table
    intro r hr
    have hb : r.bits ∈ WIDE_RANGE_WIDTHS := hbits r hr
    have hmem : VmConstraint2.lookup (rangeLookupW r)
        ∈ (graduateV1Wide d (sitesFit_admitted hfit)).constraints := by
      unfold graduateV1Wide
      simp only [List.mem_append, List.mem_map, mem_graduateSites]
      exact Or.inr ⟨r, hr, rfl⟩
    exact lookup_replaces_rangeW r.bits t.tf (hrangeW r.bits hb) (envAt t i) r.wire (hrow _ hmem)

/-- **`Satisfied2FaithfulWide`** — the §4F faithful deployed denotation with the PER-WIDTH range
pins in place of the single `.range` pin: `Satisfied2` + the wide chip soundness + every allowed
width's table bound to its genuine limb rows. -/
structure Satisfied2FaithfulWide (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) : Prop extends Satisfied2 hash d minit mfin maddrs t where
  /-- the genuine permutation exposes exactly `CHIP_OUT_LANES` output lanes. -/
  permWidth : ∀ ins, (permOut ins).length = CHIP_OUT_LANES
  /-- the v1 digest IS lane 0 of the genuine permutation (the deployed squeeze). -/
  chipHashIsLane0 : ∀ ins, hash ins = (permOut ins).headD 0
  /-- THE CHIP-TABLE-FAITHFUL CONJUNCT (`Ir2Air::Chip`), bound to `t.tf .poseidon2`. -/
  chipTableFaithful : ChipTableSoundN permOut (t.tf .poseidon2)
  /-- THE PER-WIDTH RANGE-FAITHFUL CONJUNCT: every allowed width's table is its genuine limb
  table (subsumes the single `.range` pin at `b = BAL_LIMB_BITS`). -/
  rangeTablesWideFaithful : ∀ b ∈ WIDE_RANGE_WIDTHS, t.tf (rangeTidW b) = rangeRows b

/-- The wide faithful object PROJECTS to the single-width faithful object (the `.range` pin is
the `b = BAL_LIMB_BITS` instance). -/
theorem Satisfied2FaithfulWide.toFaithful {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ}
    {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2FaithfulWide permOut hash d minit mfin maddrs t) :
    Satisfied2Faithful permOut hash d minit mfin maddrs t :=
  { h.toSatisfied2 with
    permWidth := h.permWidth
    chipHashIsLane0 := h.chipHashIsLane0
    chipTableFaithful := h.chipTableFaithful
    rangeTableFaithful := rangeTablesWide_range h.rangeTablesWideFaithful }

/-- The legacy chip soundness, discharged from the wide faithful structure (not assumed). -/
theorem Satisfied2FaithfulWide.chipSound {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ}
    {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2FaithfulWide permOut hash d minit mfin maddrs t) :
    ChipTableSound hash (t.tf .poseidon2) :=
  h.toFaithful.chipSound

/-- **`satisfied2FaithfulWide_satisfiedVm` — THE WIDE COLLAPSE RECIPE.** From a wide-faithful
witness of the wide graduation `graduateV1Wide d` (and `graduableWide d`), the v1 denotation
`satisfiedVm` holds on every row window — no free `hchip`/`hrange` lever, and the 15-bit teeth
return at their genuine width. -/
theorem satisfied2FaithfulWide_satisfiedVm (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduableWide d = true)
    (h : Satisfied2FaithfulWide permOut hash
      (graduateV1Wide d (sitesFit_admitted (graduableWide_spec hgrad).2.1)) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  graduateV1Wide_sound hash d minit mfin maddrs t h.chipSound h.rangeTablesWideFaithful hgrad
    h.toSatisfied2

-- The wide gate ADMITS the hardened availability descriptor the single-width gate REFUSES —
-- exactly the lock-out `graduableWide` exists to lift.
#guard graduableWide EffectVmEmitTransfer.transferVmDescriptorAvail
#guard !(graduable EffectVmEmitTransfer.transferVmDescriptorAvail)
-- The bare transfer is graduable BOTH ways (the single-width world embeds).
#guard graduableWide EffectVmEmitTransfer.transferVmDescriptor
-- The 15-bit table bounds a 15-bit limb EXACTLY (the borrow-proof enabler): 2^15−1 ∈, 2^15 ∉ —
-- lowering into the 30-bit table would have admitted 2^15 (`range_row_mem_iff`: `2^15 < 2^30`)
-- and killed the borrow proof. (No `rangeRows 30` #guard — evaluating it materializes a 2^30-element
-- list, the documented `.range` whnf trap.)
#guard ([32767] : List ℤ) ∈ rangeRows 15
#guard ¬ (([32768] : List ℤ) ∈ rangeRows 15)

#assert_axioms graduableWide_spec
#assert_axioms graduableWide_of_graduable
#assert_axioms rangeTablesWide_range
#assert_axioms lookup_replaces_rangeW
#assert_axioms graduateV1Wide_sound
#assert_axioms Satisfied2FaithfulWide.toFaithful
#assert_axioms Satisfied2FaithfulWide.chipSound
#assert_axioms satisfied2FaithfulWide_satisfiedVm

end Dregg2.Circuit.Emit.EffectVmEmitV2
