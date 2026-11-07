/-
# Dregg2.Circuit.Emit.CapRemoveEmit — the REMOVE-shaped CAP-tree keystone, the assurance core for the
cap-key-SET-SHRINKING cap-write (`revokeDelegation`).

## Why this file exists (the inverse of the insert break)

`CapInsertEmit.lean` handles the fresh-key SPLICE (delegate/introduce/delegateAtten grow the cap
key-set). `revokeDelegation` is the INVERSE: it DELETES an existing cap key from the sorted cap-tree
(`cap_root.rs::CanonicalCapTree::remove_witness`) — the key is PRESENT in BEFORE, is dropped, and the
tree REBUILDS with the pred/succ now adjacent. Like the insert, there is NO shared before/after path
(the splice reorders siblings), so the UPDATE-at-key `writesTo8` shape (attenuate's in-place narrow)
does NOT fit it either.

This file builds the CORRECT remove-shaped keystone — the mirror of `CapInsertEmit`. The honest model
of the sorted cap remove:
  (a) MEMBERSHIP of the removed cap `leaf` in BEFORE — `MembersAt8 beforeRoot leaf` (the `remove_witness`
      recompose path reaching the BEFORE cap-root8), TRACE-FORCED off the reused `effCapOpenV3`
      membership read welded to the committed BEFORE cap-root group (exactly the cap-open READ that
      revokeDelegation must exhibit to authorize the revocation);
  (b) NON-MEMBERSHIP of the removed key in AFTER — the key is GONE: the pred/succ bracket now covers it
      (`GapOpen.inner` over the REBUILT after cap-tree) ⟹ `keyOf leaf ∉ keysOf afterRoot`
      (`SortedTreeNonMembership.nonMembership_sound`);
  (c) the ROOT RECOMPUTE tying BEFORE→AFTER — the cap key set shrinks by EXACTLY the removed key
      (`CapTreeUpdate.capRemove_sound` over `sortedRemove`).

## The deliverables
  * `capRemoves8` (§A) — the faithful arity-7 cap REMOVE relation (the inverse of `capInserts8`):
    present in BEFORE, gone in AFTER, set-shrinks-by-exactly-key; its faithful consequences.
  * `capRemove_writesTo8` (§B) — THE KEYSTONE: the BEFORE cap-membership + the AFTER non-membership
    bracket + the two spine bindings FORCE `capRemoves8` over the FULL committed 8-felt BEFORE/AFTER
    cap-root groups — NEVER lane-0. The inverse of `capInsert_writesTo8`.
  * `effCapRemoveV3` (§C) — the DEPLOYED remove-shaped cap descriptor: the reused `effCapOpenV3`
    membership read welded to the committed BEFORE cap-root group. `effCapRemoveV3_forces_write8`
    TRACE-FORCES the honest remove (a) is forced; (b)+(c) ride the realizable carriers).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the Poseidon2-CR floor enters only through
the `Cap8Scheme` arity-16 `node8` carrier already in play, and the realizable spine↔root binding
`SpineCommits` is a HYPOTHESIS, never an axiom; never a fabricated shared path; never lane-0.
-/
import Dregg2.Circuit.SortedTreeNonMembership
import Dregg2.Circuit.CapTreeUpdate
import Dregg2.Circuit.Emit.CapOpenEmit

namespace Dregg2.Circuit.Emit.CapRemoveEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv EFFECT_VM_WIDTH VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (TraceFamily VmConstraint2 EffectVmDescriptor2 ChipTableSoundN Satisfied2 VmTrace envAt)
open Dregg2.Circuit.DeployedCapTree (CapLeaf Cap8Scheme Digest8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (MembersAt8)
open Dregg2.Circuit.DeployedCapOpen
  (CapOpenCols leafOf groupVal capPermOut SatisfiedEff capOpenEff_membership
   MembershipCore membershipCore_opens SpineCore capOpen_recomposeFrom8
   DEPTH pathOf8 nodeLookup rootPinGate dirBoolGate)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (recomposeUp8 capLeafDigest8)
open Dregg2.Circuit.Emit.CapOpenEmit
  (capOpenCols eqGate eqGate_eval effCapOpenV3 effCapOpenV3_satisfiedEff
   effCapOpenV3_membershipCore diffGate_exact
   beforeCapRootWelds effCapRemoveV3
   afterSpineCols afterSpineCols_dir afterSpine_capRoot_after AFTER_SPINE_SPAN
   zeroPinGate tombstoneZeroPins removeTombstoneConstraints removeSpineConstraints)
open Dregg2.Circuit.SortedTreeNonMembership
  (SpineCommits keysOf GapOpen keyOf nonMembership_sound)
open Dregg2.Circuit.CapTreeUpdate (sortedRemove capRemove_sound)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (capRootGroupCol B_SPAN)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §A — the faithful arity-7 cap REMOVE relation `capRemoves8` (the inverse of `capInserts8`).

The cap remove has NO shared before/after path; the faithful remove claim is: the removed cap `leaf`
(carrying its authority edge) was a MEMBER of BEFORE (`MembersAt8 beforeRoot leaf`), its key
(`keyOf leaf = leaf.slot_hash`) is ABSENT from AFTER, and the committed cap key set shrinks by EXACTLY
that key. Packaged existentially over the (realizable) sorted key spine the BEFORE cap-root commits. -/

/-- **`capRemoves8 S8 beforeRoot leaf afterRoot`** — the faithful 8-felt CAP remove: the BEFORE cap-root
commits some sorted spine, the 7-field `leaf` is a MEMBER of the BEFORE cap-tree, `keyOf leaf` is ABSENT
from the AFTER cap-tree, and the AFTER cap-root commits the REMOVED spine (`sortedRemove (keyOf leaf)
spine`). Over the FULL committed BEFORE/AFTER 8-felt cap-root groups (~124-bit), NEVER lane-0. -/
def capRemoves8 (S8 : Cap8Scheme) (beforeRoot : Digest8) (leaf : CapLeaf) (afterRoot : Digest8) :
    Prop :=
  ∃ spine : List ℤ,
    SpineCommits S8 beforeRoot spine ∧
    MembersAt8 S8 beforeRoot leaf ∧
    keyOf leaf ∉ keysOf S8 afterRoot ∧
    SpineCommits S8 afterRoot (sortedRemove (keyOf leaf) spine)

/-- **`capRemoves8_setShrinks` — the faithful set-shrink consequence.** The AFTER committed cap key set
is EXACTLY the BEFORE set MINUS the removed `keyOf leaf` (`capRemove_sound`): revokeDelegation drops
precisely that key, nothing else — authority only shrinks. -/
theorem capRemoves8_setShrinks (S8 : Cap8Scheme) (beforeRoot : Digest8) (leaf : CapLeaf)
    (afterRoot : Digest8) (h : capRemoves8 S8 beforeRoot leaf afterRoot) :
    ∀ y, y ∈ keysOf S8 afterRoot ↔ (y ∈ keysOf S8 beforeRoot ∧ y ≠ keyOf leaf) := by
  obtain ⟨spine, hbefore, _hmem, _hgone, hafter⟩ := h
  exact capRemove_sound S8 beforeRoot afterRoot (keyOf leaf) spine hbefore hafter

/-- **`capRemoves8_was_present`** — the removed 7-field cap `leaf` (target/tier/facet) was a genuine
MEMBER of the BEFORE cap-tree at the FULL 8-felt cap-root: a real authority edge is being revoked, not a
lane-0 phantom. -/
theorem capRemoves8_was_present (S8 : Cap8Scheme) (beforeRoot : Digest8) (leaf : CapLeaf)
    (afterRoot : Digest8) (h : capRemoves8 S8 beforeRoot leaf afterRoot) :
    MembersAt8 S8 beforeRoot leaf := by
  obtain ⟨_spine, _hbefore, hmem, _hgone, _hafter⟩ := h
  exact hmem

/-- **`capRemoves8_gone`** — the removed `keyOf leaf` is genuinely ABSENT from AFTER (the revocation
took effect): the cap key is really gone, not silently retained. Anti-ghost: distinguishes a genuine
revokeDelegation from a no-op. -/
theorem capRemoves8_gone (S8 : Cap8Scheme) (beforeRoot : Digest8) (leaf : CapLeaf)
    (afterRoot : Digest8) (h : capRemoves8 S8 beforeRoot leaf afterRoot) :
    keyOf leaf ∉ keysOf S8 afterRoot := by
  obtain ⟨_spine, _hbefore, _hmem, hgone, _hafter⟩ := h
  exact hgone

/-! ## §B — THE KEYSTONE: `capRemove_writesTo8` (the before-membership + after-non-membership + recompute
FORCE the faithful cap remove). Covers `revokeDelegation`.

Given: the BEFORE cap-root commits a sorted spine; the 7-field `leaf` opens against the BEFORE cap-root
(`MembersAt8` — the revocation READ); a `GapOpen` covering `keyOf leaf` valid against the REMOVED spine
(the pred/succ bracket now adjacent in the AFTER cap-tree, whose neighbor openings ride the proven
`Cap8Scheme` recompose soundness); and the AFTER cap-root commits the removed spine — then the faithful
remove `capRemoves8` holds. The inverse of `CapInsertEmit.capInsert_writesTo8`. -/
theorem capRemove_writesTo8 (S8 : Cap8Scheme)
    (beforeRoot afterRoot : Digest8) (leaf : CapLeaf) (spine : List ℤ)
    (hbefore : SpineCommits S8 beforeRoot spine)
    (hbeforeMem : MembersAt8 S8 beforeRoot leaf)
    (g : GapOpen S8 afterRoot (keyOf leaf)) (hcov : g.coversSpine (sortedRemove (keyOf leaf) spine))
    (hafter : SpineCommits S8 afterRoot (sortedRemove (keyOf leaf) spine)) :
    capRemoves8 S8 beforeRoot leaf afterRoot := by
  -- (b) the removed-key non-membership in AFTER, from the covering gap over the removed spine.
  have hgone : keyOf leaf ∉ keysOf S8 afterRoot :=
    nonMembership_sound S8 afterRoot (keyOf leaf) (sortedRemove (keyOf leaf) spine) hafter g hcov
  -- (a)+(c) assemble the faithful remove relation.
  exact ⟨spine, hbefore, hbeforeMem, hgone, hafter⟩

/-- **`capRemove_writesTo8_setShrinks` — the KEYSTONE's headline consequence, in one shot.** From the
BEFORE cap-membership + the AFTER non-membership bracket + the two spine bindings, the AFTER committed
cap key set is EXACTLY the BEFORE set minus the removed `keyOf leaf`. The genuine faithful 8-felt cap
remove, over the ACTUAL sorted cap remove (NOT the attenuate update-at-key shared-spine). -/
theorem capRemove_writesTo8_setShrinks (S8 : Cap8Scheme)
    (beforeRoot afterRoot : Digest8) (leaf : CapLeaf) (spine : List ℤ)
    (hbefore : SpineCommits S8 beforeRoot spine)
    (hbeforeMem : MembersAt8 S8 beforeRoot leaf)
    (g : GapOpen S8 afterRoot (keyOf leaf)) (hcov : g.coversSpine (sortedRemove (keyOf leaf) spine))
    (hafter : SpineCommits S8 afterRoot (sortedRemove (keyOf leaf) spine)) :
    ∀ y, y ∈ keysOf S8 afterRoot ↔ (y ∈ keysOf S8 beforeRoot ∧ y ≠ keyOf leaf) :=
  capRemoves8_setShrinks S8 beforeRoot leaf afterRoot
    (capRemove_writesTo8 S8 beforeRoot afterRoot leaf spine hbefore hbeforeMem g hcov hafter)

#assert_axioms capRemoves8_setShrinks
#assert_axioms capRemoves8_was_present
#assert_axioms capRemoves8_gone
#assert_axioms capRemove_writesTo8
#assert_axioms capRemove_writesTo8_setShrinks

/-! ## §C — the DEPLOYED remove descriptor `effCapRemoveV3` + the trace-FORCED before-membership.

The remove-shaped cap descriptor a light client checks: the reused cap-membership read (`effCapOpenV3`)
whose `capRoot` group is welded to the committed BEFORE cap-root block — so the read opens the removed
cap leaf against BEFORE (exactly the cap-open READ revokeDelegation must exhibit). Its `Satisfied2`
TRACE-FORCES part (a) of the honest remove — `MembersAt8 beforeRoot (leafOf …)`, the removed-leaf
membership in the BEFORE cap-tree. SATISFIABLE by the honest revoke producer.

Parts (b) [the removed-key non-membership bracket in AFTER] and (c) [the set-recompute] ride the
deployed `.remove` node8-AIR map-op (deployed-faithful) and the realizable `GapOpen` / `SpineCommits`
carriers — the SAME named-realizable status `SpineCommits` carries throughout (a HYPOTHESIS, never an
axiom; never a fabricated shared path; never lane-0). The inverse of `CapInsertEmit.effCapInsertV3`. -/

/-! The descriptor defs `beforeCapRootWelds` / `effCapRemoveV3` LIVE in `CapOpenEmit` (the deployed
wrapper definitions there reference them, and this file imports `CapOpenEmit` — the defs cannot live
here without a cycle). This section proves the keystone theorems ABOUT them. -/

/-- Every constraint the remove descriptor APPENDS (the 8 BEFORE welds + the 32-constraint tombstone
spine) is a constraint of the remove descriptor. -/
theorem effCapRemoveV3_spineMem (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (c : VmConstraint2) (hc : c ∈ removeSpineConstraints base.traceWidth) :
    c ∈ (effCapRemoveV3 base name n).constraints :=
  List.mem_append_right _ hc

/-- Every BEFORE-weld constraint is a constraint of the remove descriptor. -/
theorem effCapRemoveV3_appMem (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (c : VmConstraint2) (hc : c ∈ beforeCapRootWelds base.traceWidth) :
    c ∈ (effCapRemoveV3 base name n).constraints :=
  effCapRemoveV3_spineMem base name n c (List.mem_append_left _ hc)

/-- Every TOMBSTONE-spine constraint is a constraint of the remove descriptor. -/
theorem effCapRemoveV3_tombMem (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (c : VmConstraint2) (hc : c ∈ removeTombstoneConstraints base.traceWidth) :
    c ∈ (effCapRemoveV3 base name n).constraints :=
  effCapRemoveV3_spineMem base name n c (List.mem_append_right _ hc)

/-- A `Satisfied2` of the remove descriptor strips (constraint-subset) to a `Satisfied2` of the reused
cap-membership read `effCapOpenV3` — the BEFORE welds are all `.base (.gate …)`, read no base column and
contribute no map/mem op. -/
theorem effCapRemoveV3_strips_to_capOpen (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (h : Satisfied2 hash (effCapRemoveV3 base name n) minit mfin maddrs t) :
    Satisfied2 hash (effCapOpenV3 base name n) minit mfin maddrs t := by
  have hmapOps : Dregg2.Circuit.DescriptorIR2.mapOpsOf (effCapRemoveV3 base name n)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf (effCapOpenV3 base name n) := by
    simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, effCapRemoveV3, removeSpineConstraints,
      beforeCapRootWelds, removeTombstoneConstraints, tombstoneZeroPins,
      List.filterMap_append, List.filterMap_map]
  have hmemOps : Dregg2.Circuit.DescriptorIR2.memOpsOf (effCapRemoveV3 base name n)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf (effCapOpenV3 base name n) := by
    simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, effCapRemoveV3, removeSpineConstraints,
      beforeCapRootWelds, removeTombstoneConstraints, tombstoneZeroPins,
      List.filterMap_append, List.filterMap_map]
  have hmemLog : Dregg2.Circuit.DescriptorIR2.memLog (effCapRemoveV3 base name n) t
      = Dregg2.Circuit.DescriptorIR2.memLog (effCapOpenV3 base name n) t := by
    simp [Dregg2.Circuit.DescriptorIR2.memLog, hmemOps]
  have hmapLog : Dregg2.Circuit.DescriptorIR2.mapLog (effCapRemoveV3 base name n) t
      = Dregg2.Circuit.DescriptorIR2.mapLog (effCapOpenV3 base name n) t := by
    simp [Dregg2.Circuit.DescriptorIR2.mapLog, hmapOps]
  exact
    { rowConstraints := fun i hi c hc =>
        h.rowConstraints i hi c (by
          show c ∈ (effCapOpenV3 base name n).constraints ++ removeSpineConstraints base.traceWidth
          exact List.mem_append_left _ hc)
      rowHashes := h.rowHashes
      rowRanges := h.rowRanges
      memAddrsNodup := h.memAddrsNodup
      memClosed := by have := h.memClosed; rwa [hmemLog] at this
      memDisciplined := by have := h.memDisciplined; rwa [hmemLog] at this
      memBalanced := by have := h.memBalanced; rwa [hmemLog] at this
      memTableFaithful := by have := h.memTableFaithful; rwa [hmemLog] at this
      mapTableFaithful := by have := h.mapTableFaithful; rwa [hmapLog] at this }

/-- Any BEFORE-weld `.base (.gate g)` constraint forces `g.eval ≡ 0 [ZMOD p]` on an active (non-last)
row — the field-faithful gate consequence (the ℤ equality follows under cell canonicality, at the
consumer). -/
theorem effCapRemoveV3_gate_forces (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effCapRemoveV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (g : EmittedExpr) (hin : VmConstraint2.base (.gate g) ∈ beforeCapRootWelds base.traceWidth) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have h := hrow _ (effCapRemoveV3_appMem base name n _ hin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
  simpa using h

/-- **`effCapRemoveV3_forces_beforeMembership`** — THE STEP-A DELIVERABLE: a `Satisfied2` of the remove
descriptor TRACE-FORCES `MembersAt8 beforeRoot (leafOf …)` over the FULL committed BEFORE cap-root group
(`capRootGroupCol EFFECT_VM_WIDTH`, the whole ~124-bit cap-root) at the read leaf — the removed-leaf
membership in the BEFORE cap-tree. -/
theorem effCapRemoveV3_forces_beforeMembership (S8 : Cap8Scheme)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapRemoveV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    -- the deployed cell canonicality (`0 ≤ · < p`): lifts the mod-`p` membership gates + welds to
    -- their ℤ form (the Merkle fold and `MembersAt8` are ℤ-level).
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    MembersAt8 S8 (fun k => (envAt t i).loc (capRootGroupCol EFFECT_VM_WIDTH k))
      (leafOf (capOpenCols base.traceWidth) (envAt t i)) := by
  set e := envAt t i with he
  set w := base.traceWidth with hw
  -- strip to the reused cap-open read, rebuild the membership CORE, read off the 8-felt membership.
  have hopenSat := effCapRemoveV3_strips_to_capOpen base name n hash minit mfin maddrs t hsat
  have hCore : MembershipCore hash t.tf (capOpenCols w) e :=
    effCapOpenV3_membershipCore base name n hash minit mfin maddrs t hopenSat i hi hnotlast hcells
  have hmem0 : MembersAt8 S8 (groupVal e (capOpenCols w).capRoot) (leafOf (capOpenCols w) e) :=
    membershipCore_opens S8 hash t.tf (capOpenCols w) e hChip hCore
  -- weld: the read capRoot group IS the committed BEFORE cap-root group.
  have hroot : groupVal e (capOpenCols w).capRoot
      = (fun k => e.loc (capRootGroupCol EFFECT_VM_WIDTH k)) := by
    funext k
    have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols w).capRoot k)
        (capRootGroupCol EFFECT_VM_WIDTH k))) ∈ beforeCapRootWelds w :=
      List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have hmod := effCapRemoveV3_gate_forces base name n hash minit mfin maddrs t hsat i hi hnotlast _ hin
    -- the eqGate residual collapses in `(−p, p)` under canonicality.
    unfold Dregg2.Circuit.Emit.CapOpenEmit.eqGate at hmod
    simp only [EmittedExpr.eval] at hmod
    have := diffGate_exact (hcells _) (hcells _) hmod
    simp only [groupVal]
    linarith
  rw [hroot] at hmem0
  exact hmem0

/-- **`effCapRemoveV3_forces_write8` — THE STEP-A+B+C DELIVERABLE (assurance layer).** A `Satisfied2` of
the remove descriptor, together with the realizable BEFORE spine binding + the AFTER non-membership
bracket (`GapOpen` over the removed spine) + the AFTER spine binding, FORCES the faithful 8-felt CAP
remove `capRemoves8` over the FULL committed BEFORE/AFTER cap-root groups: the removed 7-field leaf
membership in BEFORE is TRACE-FORCED; the removed-key non-membership in AFTER and the set-recompute ride
the realizable carriers (`SpineCommits`, a HYPOTHESIS — the deployed
`compute_canonical_capability_root_felt` fold — never an axiom, never lane-0). Covers `revokeDelegation`.
The inverse of `CapInsertEmit.effCapInsertV3_forces_write8`. -/
theorem effCapRemoveV3_forces_write8 (S8 : Cap8Scheme)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapRemoveV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (spine : List ℤ)
    (hbefore : SpineCommits S8 (fun k => (envAt t i).loc (capRootGroupCol EFFECT_VM_WIDTH k)) spine)
    (g : GapOpen S8 (fun k => (envAt t i).loc (capRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) k))
          (keyOf (leafOf (capOpenCols base.traceWidth) (envAt t i))))
    (hcov : g.coversSpine
              (sortedRemove (keyOf (leafOf (capOpenCols base.traceWidth) (envAt t i))) spine))
    (hafter : SpineCommits S8 (fun k => (envAt t i).loc (capRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) k))
                (sortedRemove (keyOf (leafOf (capOpenCols base.traceWidth) (envAt t i))) spine)) :
    capRemoves8 S8
        (fun k => (envAt t i).loc (capRootGroupCol EFFECT_VM_WIDTH k))
        (leafOf (capOpenCols base.traceWidth) (envAt t i))
        (fun k => (envAt t i).loc (capRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) k)) := by
  have hbeforeMem := effCapRemoveV3_forces_beforeMembership S8 base name n hash minit mfin maddrs t
    hChip hsat i hi hnotlast hcells
  exact capRemove_writesTo8 S8 _ _ (leafOf (capOpenCols base.traceWidth) (envAt t i)) spine
    hbefore hbeforeMem g hcov hafter

#assert_axioms effCapRemoveV3_forces_beforeMembership
#assert_axioms effCapRemoveV3_forces_write8

/-! ## §D — THE WRITE TOOTH: the TOMBSTONE after-spine, TRACE-FORCED (the light-client close).

⚑ **What this section closes, stated at the resolution it was measured.** Until it landed, §C's
`effCapRemoveV3_forces_write8` took the ENTIRE after side as HYPOTHESES (`GapOpen` + the AFTER
`SpineCommits`), and the committed descriptor put **zero gates on the AFTER cap-root group** — the
authority-only twin's `c452 == c87` / `c87 == c65` had been dropped with nothing in their place, and
these members declare NO map-ops. A prover could publish ANY 8-felt post-remove root, including one
that leaves the "revoked" capability LIVE, and `prove_vm_descriptor2` + `verify_vm_descriptor2` both
accepted. The only thing that moved was the AFTER block state-commitment, so a verifier that
independently RECOMPUTES the honest post-state rejected it — and a LEDGERLESS light client, which is
the threat model these members exist for, did not.

§D changes the KIND of the claim. `recomposeUp8 S8 0⁸ path = afterRoot` — the deployed tombstone
zero-fold of `cap_root.rs::CanonicalCapTree::remove_witness` — is now FORCED from `Satisfied2` over
the FULL 8-felt committed AFTER group, along the SAME path the revocation read opened the removed
leaf against (the `sib`/`dir` columns are literally shared, `afterSpineCols_dir`). Nothing in §D
rides `SpineCommits` or `GapOpen`.

⚠ **What §D does NOT do, named rather than laundered.** §A's `capRemoves8` models the remove as a
`sortedRemove` over a key spine — a COMPACTING remove. The deployed object is a TOMBSTONE: positions
do not shift, the slot is zeroed in place. Those are different post-trees, so §D does not discharge
§C's `SpineCommits`/`GapOpen` carriers and does not claim to; it forces the object the prover
actually runs. `capRemoveTombstones8` below is that object, and it is the one the light client now
checks. -/

/-- **`capRemoveTombstones8 S8 beforeRoot leaf afterRoot`** — the DEPLOYED tombstone remove: ONE
sibling path on which the removed leaf's 8-felt digest recomposes `beforeRoot` AND the empty-slot
digest `0⁸` recomposes `afterRoot`. Positions do not shift (every other capability's witness stays
valid), and the revoked key's slot is demonstrably EMPTY under the published post-root — over the
FULL committed 8-felt groups, never lane-0. -/
def capRemoveTombstones8 (S8 : Cap8Scheme) (beforeRoot : Digest8) (leaf : CapLeaf)
    (afterRoot : Digest8) : Prop :=
  ∃ path : List (Dregg2.Circuit.CapMerkleGeneric.StepG Digest8),
    recomposeUp8 S8 (capLeafDigest8 S8 leaf) path = beforeRoot ∧
    recomposeUp8 S8 (fun _ => 0) path = afterRoot

/-- The TOMBSTONE spine's own `SpineCore`, derived from `Satisfied2` of the remove descriptor. The
`dirBool` is the READ's (the `dir` columns are SHARED, `afterSpineCols_dir`), so no second direction
gate is emitted and the two folds provably walk the SAME path. `SpineCore` rather than
`MembershipCore` is the whole trick: a tombstone's level-0 input is a CONSTANT, so there is no leaf
absorb to carry. -/
theorem effCapRemoveV3_tombstoneSpine (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effCapRemoveV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (hdir : ∀ lvl < DEPTH,
      (dirBoolGate (capOpenCols base.traceWidth) lvl).eval (envAt t i).loc = 0) :
    SpineCore t.tf (afterSpineCols base.traceWidth) (envAt t i) := by
  have hrow := hsat.rowConstraints i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  refine { nodeHashed := ?_, dirBool := ?_, rootPinned := ?_ }
  · intro lvl hlvl
    have hin : VmConstraint2.lookup (nodeLookup (afterSpineCols base.traceWidth) lvl)
        ∈ removeTombstoneConstraints base.traceWidth := by
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      exact List.mem_map.mpr ⟨lvl, List.mem_range.mpr hlvl, rfl⟩
    have h := hrow _ (effCapRemoveV3_tombMem base name n _ hin)
    simpa [VmConstraint2.holdsAt] using h
  · intro lvl hlvl
    have := hdir lvl hlvl
    exact this
  · intro k
    have hin : VmConstraint2.base (.gate (rootPinGate (afterSpineCols base.traceWidth) k))
        ∈ removeTombstoneConstraints base.traceWidth := by
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have h := hrow _ (effCapRemoveV3_tombMem base name n _ hin)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
    have h' : (rootPinGate (afterSpineCols base.traceWidth) k).eval (envAt t i).loc
        ≡ 0 [ZMOD 2013265921] := by simpa using h
    unfold Dregg2.Circuit.DeployedCapOpen.rootPinGate at h' ⊢
    simp only [EmittedExpr.eval] at h' ⊢
    exact diffGate_exact (hcells _) (hcells _) h'

/-- The 8 tombstone pins hold EXACTLY (over ℤ, not just mod `p`): the after-spine's level-0 input
group IS the deployed empty-slot digest `CAP_ZERO8 = 0⁸`. -/
theorem effCapRemoveV3_tombstoneZero (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hsat : Satisfied2 hash (effCapRemoveV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    groupVal (envAt t i) (afterSpineCols base.traceWidth).leafDigest = (fun _ => 0) := by
  have hrow := hsat.rowConstraints i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  funext k
  have hin : VmConstraint2.base (.gate (zeroPinGate ((afterSpineCols base.traceWidth).leafDigest k)))
      ∈ removeTombstoneConstraints base.traceWidth := by
    refine List.mem_append_right _ ?_
    exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
  have h := hrow _ (effCapRemoveV3_tombMem base name n _ hin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
  have h' : (zeroPinGate ((afterSpineCols base.traceWidth).leafDigest k)).eval (envAt t i).loc
      ≡ 0 [ZMOD 2013265921] := by simpa using h
  unfold zeroPinGate at h'
  simp only [EmittedExpr.eval] at h'
  rw [Int.modEq_zero_iff_dvd] at h'
  obtain ⟨c, hc⟩ := h'
  obtain ⟨hb0, hb1⟩ := hcells ((afterSpineCols base.traceWidth).leafDigest k)
  simp only [groupVal]
  omega

/-- **`effCapRemoveV3_forces_tombstoneFold` — THE DELIVERABLE.** A `Satisfied2` of the remove
descriptor TRACE-FORCES the committed AFTER cap-root GROUP to be the deployed TOMBSTONE ZERO-FOLD:
`CAP_ZERO8` recomposed up the SAME sibling path the revocation READ opened the removed leaf against.
The post-remove root is no longer host-trusted; it is pinned, lane-for-lane, by the wire. -/
theorem effCapRemoveV3_forces_tombstoneFold (S8 : Cap8Scheme)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapRemoveV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    recomposeUp8 S8 (fun _ => 0)
        (pathOf8 (capOpenCols base.traceWidth) (envAt t i) DEPTH)
      = (fun k => (envAt t i).loc (capRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) k)) := by
  have hopenSat := effCapRemoveV3_strips_to_capOpen base name n hash minit mfin maddrs t hsat
  have hReadCore : MembershipCore hash t.tf (capOpenCols base.traceWidth) (envAt t i) :=
    effCapOpenV3_membershipCore base name n hash minit mfin maddrs t hopenSat i hi hnotlast hcells
  have hspine := effCapRemoveV3_tombstoneSpine base name n hash minit mfin maddrs t hsat i hi
    hnotlast hcells hReadCore.dirBool
  have hfold := capOpen_recomposeFrom8 S8 t.tf (afterSpineCols base.traceWidth) (envAt t i)
    hChip hspine
  rw [effCapRemoveV3_tombstoneZero base name n hash minit mfin maddrs t hsat i hi hnotlast hcells]
    at hfold
  -- the two folds walk the SAME path (the `sib`/`dir` columns are literally shared)…
  have hpath : pathOf8 (afterSpineCols base.traceWidth) (envAt t i) DEPTH
      = pathOf8 (capOpenCols base.traceWidth) (envAt t i) DEPTH := rfl
  rw [hpath] at hfold
  -- …and the after-spine's `capRoot` group IS the committed AFTER cap-root block, by `rfl`.
  rw [hfold]
  rfl

/-- **`effCapRemoveV3_forces_tombstone8`** — both halves in one statement: the removed leaf was a
genuine MEMBER of the committed BEFORE cap-root, and the committed AFTER cap-root is the tombstone
zero-fold of that same path. This is the object a ledgerless light client now verifies, and it is
trace-forced end to end — no `SpineCommits`, no `GapOpen`, no host recomputation. -/
theorem effCapRemoveV3_forces_tombstone8 (S8 : Cap8Scheme)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapRemoveV3 base name n) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    capRemoveTombstones8 S8
        (fun k => (envAt t i).loc (capRootGroupCol EFFECT_VM_WIDTH k))
        (leafOf (capOpenCols base.traceWidth) (envAt t i))
        (fun k => (envAt t i).loc (capRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) k)) := by
  refine ⟨pathOf8 (capOpenCols base.traceWidth) (envAt t i) DEPTH, ?_, ?_⟩
  · -- the BEFORE leg: the read's own fold, welded to the committed BEFORE group.
    have hopenSat := effCapRemoveV3_strips_to_capOpen base name n hash minit mfin maddrs t hsat
    have hReadCore : MembershipCore hash t.tf (capOpenCols base.traceWidth) (envAt t i) :=
      effCapOpenV3_membershipCore base name n hash minit mfin maddrs t hopenSat i hi hnotlast hcells
    have hfold := capOpen_recomposeFrom8 S8 t.tf (capOpenCols base.traceWidth) (envAt t i)
      hChip hReadCore.toSpine
    have hleaf := Dregg2.Circuit.DeployedCapOpen.leafDigest_sound8 S8 hash t.tf
      (capOpenCols base.traceWidth) (envAt t i) hChip hReadCore
    rw [hleaf] at hfold
    -- weld: the read's appendix `capRoot` group IS the committed BEFORE cap-root group.
    have hroot : groupVal (envAt t i) (capOpenCols base.traceWidth).capRoot
        = (fun k => (envAt t i).loc (capRootGroupCol EFFECT_VM_WIDTH k)) := by
      funext k
      have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols base.traceWidth).capRoot k)
          (capRootGroupCol EFFECT_VM_WIDTH k))) ∈ beforeCapRootWelds base.traceWidth :=
        List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
      have hmod := effCapRemoveV3_gate_forces base name n hash minit mfin maddrs t hsat i hi
        hnotlast _ hin
      unfold Dregg2.Circuit.Emit.CapOpenEmit.eqGate at hmod
      simp only [EmittedExpr.eval] at hmod
      have := diffGate_exact (hcells _) (hcells _) hmod
      simp only [groupVal]
      linarith
    rwa [hroot] at hfold
  · exact effCapRemoveV3_forces_tombstoneFold S8 base name n hash minit mfin maddrs t hChip hsat
      i hi hnotlast hcells

/-- **`effCapRemoveV3_rejects_forged_afterRoot` — THE TOOTH, both polarities.** A trace whose
committed AFTER cap-root group is ANYTHING other than the tombstone zero-fold of the read's path is
**UNSAT**: no proof of the remove descriptor exists for it. This is the statement the deployed
`prove_vm_descriptor2` realizes — the fabricated post-remove root is refused at the PROVER, not
caught downstream by a verifier that recomputes the honest post-state. -/
theorem effCapRemoveV3_rejects_forged_afterRoot (S8 : Cap8Scheme)
    (base : EffectVmDescriptor2) (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (hforged : (fun k => (envAt t i).loc (capRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) k))
      ≠ recomposeUp8 S8 (fun _ => 0)
          (pathOf8 (capOpenCols base.traceWidth) (envAt t i) DEPTH)) :
    ¬ Satisfied2 hash (effCapRemoveV3 base name n) minit mfin maddrs t := by
  intro hsat
  exact hforged (effCapRemoveV3_forces_tombstoneFold S8 base name n hash minit mfin maddrs t
    hChip hsat i hi hnotlast hcells).symm

#assert_axioms effCapRemoveV3_tombstoneSpine
#assert_axioms effCapRemoveV3_tombstoneZero
#assert_axioms effCapRemoveV3_forces_tombstoneFold
#assert_axioms effCapRemoveV3_forces_tombstone8
#assert_axioms effCapRemoveV3_rejects_forged_afterRoot

end Dregg2.Circuit.Emit.CapRemoveEmit
