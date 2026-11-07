/-
# Dregg2.Circuit.Emit.AvailWideMembers — the HARDENED wide-transfer members (the WIDE-transfer
availability wrap-forgery closed: both wide transfer routes rebuilt over the §11.7 borrow-weld
face `transferVmDescriptorAvail`).

## What this module is

`AvailWireMembers` closed the NARROW transfer/burn cohort keys over the hardened availability
faces (`transferV3AvailWire` / `burnV3AvailWire`). The WIDE registry
(`WIDE_REGISTRY_STAGED_TSV`, `EmitWideRegistryProbe`) and its umem-welded twin
(`EmitWideUMemWeldRegistryProbe` / `EffectVmEmitUMemWeldWide`) still routed the transfer turns to
wide members built over the BARE `transferVmDescriptor` — so a wide/welded transfer proof carried
NO borrow gates and the GAP #4 underflow-wrap mint-from-nothing
(`docs/FINDING-modp-wrap-forgery-audit.md`, forgery 1) stayed open on the wide leg. This module
builds the two wide-transfer AVAIL members the emission retargets to:

  * **`transferV3MembershipAvailWide`** — the crown `transferVmDescriptor2R24` wide host: the
    membership-teeth transfer (`CarrierComposed.transferV3MembershipWide`) rebuilt over
    `v3OfFrozenWide transferVmDescriptorAvail`, with the rc pins at the AVAIL-shifted caveat rc
    carrier (`withDfaRcPinsAt AVAIL_WIDTH` — the fixed-geometry `withDfaRcPins` would read the
    WRONG columns on the widened face) and the membership teeth columns past the avail wide
    carriers (`2709..2710`, teeth PIs 50..51 UNCHANGED — same slots as the bare member, so the
    fold-arm PI convention `MEMBERSHIP_CLAIM_PI_LO = 50` survives);
  * **`transferCapOpenTBAvailWide`** — the live-only `transferCapOpenTBVmDescriptor2R24` host:
    `effCapOpenV3TB` (fully parametric in its base) over the same hardened rotated face,
    wide-appended at the AVAIL face base `TR_AVAIL_BB = AVAIL_WIDTH` (rotateV3 lays the rotated
    limbs at the FACE width, 198 on the hardened face).

The fee'd transfer has NO avail face (`transferFeeVmDescriptor` is a separate seam) and is not a
`liveOnlyWideHosts` member — out of scope here, named in HORIZONLOG. §7 closes the WIDE-BURN twin
(`burnV3AvailWide` / `burnAvailWideRefused` — the `burnVmDescriptor2R24` crown host rebuilt over
the §8¾ borrow-weld face `burnVmDescriptorAvail`; burn carries NO membership teeth, so the
retarget is rc-pins + `wideAppend` only and the PI count is UNCHANGED at 66).

## THE COLLAPSE KEYSTONE (`wideEmbedded_sound_v1`)

`wideAppend` RETIRES the host's two legacy 1-felt commit pins (`isLegacyCommitPin1`), so a
`Satisfied2` witness of a wide member does NOT recover `Satisfied2 (v3OfFrozenWide d)` verbatim —
but the v1 denotation of the PRE-ROTATION face `d` never rides those pins. `wideEmbedded_sound_v1`
is the membership-parametric fusion of `rotV3FrozenWide_sound_v1`: from a wide-faithful witness of
ANY descriptor `D` whose constraints EMBED the (legacy-pin-filtered) `v3OfFrozenWide d`
constraints, the FULL per-row v1 denotation `satisfiedVm hash d` returns — exactly what
`transferAvail_derives_availability_row` consumes. The three bullets mirror
`graduateV1Wide_sound` (embedded base constraints / the chained site-lookup walk / the per-width
range teeth — all `.base`/`.lookup` members that survive the pin filter; `hclean` certifies the
face's own constraints are never pin-shaped, decidably), and the site prefix returns through
`go_append_left` exactly as in `rotateV3_satisfiedVm_v1`.

## The refuse on the retargeted member

The crown transfer is a bare-cohort route, so the emitted wide row carries the capacity-floor
refuse. On the avail face the caveat type-tag columns ride `cavBaseOf AVAIL_WIDTH = 676` (not the
bare 682), so the refuse is `AvailWireMembers.gentianDeployedBareRefuseAt (cavBaseOf AVAIL_WIDTH)`
(aux blocks past the member's OWN width, above the wide carriers — the `gentianWideBareRefuse`
geometry at the avail caveat base). §6 re-closes the three capacity dodges on the refused member
via the column-parametric keystone `declared_tag_unsat_at`, so the flag-day teeth do not regress
through the retarget.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem; NO sorryAx.
-/
import Dregg2.Circuit.Emit.CarrierComposed
import Dregg2.Circuit.Emit.AvailWireMembers
import Dregg2.Circuit.Emit.CapOpenTurnPins

namespace Dregg2.Circuit.Emit.AvailWideMembers

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
  (EffectVmDescriptor VmConstraint satisfiedVm siteHoldsAll holdsVm_piFirst_true)
open Dregg2.Circuit.Emit.EffectVmEmitV2
  (graduableWide graduableWide_spec graduateV1Wide Satisfied2FaithfulWide WIDE_RANGE_WIDTHS
   rangeTidW rangeLookupW lookup_replaces_rangeW siteLookups_sound sitesFit_admitted mem_graduateSites)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (rotateV3 rotateV3FrozenAuthority rotateV3FrozenAuthority_constraints v3OfFrozenWide
   graduableWide_rotateV3FrozenAuthority rotV3Appendix go_append_left B_STATE_COMMIT B_SPAN)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide
  (wideAppend isLegacyCommitPin1 wideAppendixSpan)
open Dregg2.Circuit.Emit.CarrierComposed
  (withMembershipTeethPinsAt withMembershipTeethPinsAt_constraints wideAppend_mem_of_host)
open Dregg2.Circuit.Emit.AvailWireMembers
  (withDfaRcPinsAt withDfaRcPinsAt_constraints gentianDeployedBareRefuseAt cavBaseOf ebAt
   bcAt icAt ocAt fcAt blockGatesAt deployedRefuseGatesAt
   decodeAt_mem_blockAt refuseAt_mem_blockAt
   satisfied2_of_withDfaRcPinsAt satisfied2_of_gentianDeployedBareRefuseAt)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptorAvail AVAIL_WIDTH)
open Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat (RotCaveatManifest caveatCommit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Deos.BareCohortFloorRefuse (floorZeroRefuseGate)
open Dregg2.Deos.CarrierBoundFloorGadget (manifestTags)
open Dregg2.Deos.BareCohortFloorRefuseDeployed (declared_tag_unsat_at manifestOf)
open Dregg2.Deos.ConstraintBinding (tagSettleEscrow tagDischargeObligation tagVaultDeposit)

set_option autoImplicit false
set_option maxRecDepth 16000

/-! ## §1 — THE COLLAPSE KEYSTONE: the membership-parametric wide v1 collapse. -/

/-- **`wideEmbedded_sound_v1`** — the membership-parametric fusion of `rotV3FrozenWide_sound_v1`:
a wide-faithful witness of ANY descriptor `D` whose constraints EMBED the (legacy-pin-filtered)
`v3OfFrozenWide d` constraint set yields the FULL per-row v1 denotation of the PRE-ROTATION face
`d` (borrow-weld gates + 15-bit teeth INCLUDED). `hclean` certifies (decidably, per member) that
no face constraint is itself pin-shaped; the two retired 1-felt commit pins are `rotateV3`
appendix pins the face's v1 denotation never reads, so the collapse survives their retirement. -/
theorem wideEmbedded_sound_v1 (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (D : EffectVmDescriptor2) (bb ab : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduableWide d = true)
    (hclean : ∀ c ∈ d.constraints,
      isLegacyCommitPin1 bb ab (VmConstraint2.base c) = false)
    (hemb : ∀ c ∈ (v3OfFrozenWide d (sitesFit_admitted
        (graduableWide_spec (graduableWide_rotateV3FrozenAuthority hgrad)).2.1)).constraints,
      isLegacyCommitPin1 bb ab c = false → c ∈ D.constraints)
    (hf : Satisfied2FaithfulWide permOut hash D minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  have hgradr : graduableWide (rotateV3FrozenAuthority d) = true :=
    graduableWide_rotateV3FrozenAuthority hgrad
  obtain ⟨hwf, hfit, hbits⟩ := graduableWide_spec hgradr
  intro i hi
  have hrow := hf.rowConstraints i hi
  refine ⟨?_, ?_, ?_⟩
  · -- the ORIGINAL face's v1 constraints (never the retired pins — `hclean`)
    intro c hc
    have hcr : c ∈ (rotateV3FrozenAuthority d).constraints := by
      rw [rotateV3FrozenAuthority_constraints]
      exact List.mem_append_left _ (List.mem_append_left _ hc)
    have hmem : VmConstraint2.base c ∈ (v3OfFrozenWide d (sitesFit_admitted
        (graduableWide_spec hgradr).2.1)).constraints := by
      show VmConstraint2.base c ∈ (graduateV1Wide (rotateV3FrozenAuthority d)
        (sitesFit_admitted (graduableWide_spec hgradr).2.1)).constraints
      unfold graduateV1Wide
      simp only [List.mem_append, List.mem_map, List.mem_mapIdx]
      exact Or.inl (Or.inl ⟨c, hcr, rfl⟩)
    exact hrow _ (hemb _ hmem (hclean c hc))
  · -- the ORIGINAL face's hash sites: the FULL rotated chained walk, then the prefix
    have hall : siteHoldsAll hash (envAt t i) (rotateV3FrozenAuthority d).hashSites := by
      refine siteLookups_sound hash (t.tf .poseidon2) hf.chipSound (envAt t i)
        (rotateV3FrozenAuthority d).hashSites (rotateV3FrozenAuthority d).traceWidth hwf
        (sitesFit_admitted hfit) ?_
      · intro j hj
        have hmem : VmConstraint2.lookup
            (siteLookup (rotateV3FrozenAuthority d).hashSites
              (rotateV3FrozenAuthority d).hashSites[j]
              ((rotateV3FrozenAuthority d).traceWidth + (CHIP_OUT_LANES - 1) * j)
              (sitesFit_admitted hfit _ (List.getElem_mem hj)))
            ∈ (v3OfFrozenWide d (sitesFit_admitted
              (graduableWide_spec hgradr).2.1)).constraints := by
          show _ ∈ (graduateV1Wide (rotateV3FrozenAuthority d)
            (sitesFit_admitted (graduableWide_spec hgradr).2.1)).constraints
          unfold graduateV1Wide
          simp only [List.mem_append, List.mem_map, mem_graduateSites]
          exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
        exact hrow _ (hemb _ hmem rfl)
    exact go_append_left hash (envAt t i) [] d.hashSites (rotV3Appendix d.traceWidth) hall
  · -- the ORIGINAL face's range teeth, each via ITS OWN width's table (15-bit EXACT)
    intro r hr
    have hb : r.bits ∈ WIDE_RANGE_WIDTHS := hbits r hr
    have hmem : VmConstraint2.lookup (rangeLookupW r) ∈ (v3OfFrozenWide d (sitesFit_admitted
        (graduableWide_spec hgradr).2.1)).constraints := by
      show _ ∈ (graduateV1Wide (rotateV3FrozenAuthority d)
        (sitesFit_admitted (graduableWide_spec hgradr).2.1)).constraints
      unfold graduateV1Wide
      simp only [List.mem_append, List.mem_map, List.mem_mapIdx]
      exact Or.inr ⟨r, hr, rfl⟩
    exact lookup_replaces_rangeW r.bits t.tf (hf.rangeTablesWideFaithful r.bits hb)
      (envAt t i) r.wire (hrow _ (hemb _ hmem rfl))

#assert_axioms wideEmbedded_sound_v1

/-! ## §2 — the two wide-transfer AVAIL members. -/

/-- The hardened rotated graduated transfer face — the SAME term as
`RotatedKernelRefinementAvail.transferV3Avail` (`v3OfFrozenWide transferVmDescriptorAvail`),
restated here so the emission layer does not import the refinement tower. -/
def transferAvailV3W : EffectVmDescriptor2 := v3OfFrozenWide transferVmDescriptorAvail

/-- The AVAIL wide BEFORE base: `rotateV3` lays the rotated limbs at the hardened FACE width
(`AVAIL_WIDTH = 198` — the bare `TR_WIDE_BB = 188` shifted by the 10-column avail pad). -/
def TR_AVAIL_BB : Nat := AVAIL_WIDTH

#guard TR_AVAIL_BB == transferVmDescriptorAvail.traceWidth
#guard transferAvailV3W.piCount == 39
-- MODEL vs EMISSION (was the literal 1829 — decoration; the key nonet moved it).
#guard transferAvailV3W.traceWidth
  == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.gradRotWidthOf transferVmDescriptorAvail
#guard graduableWide transferVmDescriptorAvail
-- the Rust avail-pad key survives every wrapper (all append-only on the name)
#guard transferAvailV3W.name.startsWith "dregg-effectvm-transfer-v1-avail"

/-- The AVAIL wide membership teeth columns: past the avail wide carriers
(`1717 + 992 = 2709..2710` — the avail mirror of `MEMBERSHIP_TEETH_COL_WIDE = 2699`). The teeth
PI slots are UNCHANGED (50..51 — the avail rotated face publishes the same 46 + 4 rc PIs). -/
def MEMBERSHIP_TEETH_COL_AVAIL_WIDE : Nat := transferAvailV3W.traceWidth + wideAppendixSpan

-- ⚑ This was the literal `2821` with the relation below as its `#guard`.  The relation was the only
-- real content, so it is now the DEFINITION and the guard is gone: a teeth column that follows the
-- carriers cannot fall behind them, and a flag day moves it without anyone editing a number.

/-- The crown AVAIL wide host BEFORE the teeth-column width bump (named so the membership /
peel lemmas can `show` into it — `{ … with traceWidth := … }` keeps constraints verbatim). -/
def transferMembershipAvailWideBase : EffectVmDescriptor2 :=
  wideAppend
    (withMembershipTeethPinsAt MEMBERSHIP_TEETH_COL_AVAIL_WIDE
      (withDfaRcPinsAt AVAIL_WIDTH transferAvailV3W))
    TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN)

/-- **`transferV3MembershipAvailWide`** — the AVAIL crown wide transfer member (the
`transferVmDescriptor2R24` wide-registry host post-retarget): the membership-teeth transfer
rebuilt over the hardened availability face. Geometry mirror of
`CarrierComposed.transferV3MembershipWide` at the avail pad (+10 everywhere; teeth PIs 50..51
unchanged). -/
def transferV3MembershipAvailWide : EffectVmDescriptor2 :=
  { transferMembershipAvailWideBase with
    traceWidth := transferMembershipAvailWideBase.traceWidth + 2 }

theorem transferV3MembershipAvailWide_constraints :
    transferV3MembershipAvailWide.constraints
      = transferMembershipAvailWideBase.constraints := rfl

/-- **`transferCapOpenTBAvailWide`** — the AVAIL live-only TB wide transfer member (the
`transferCapOpenTBVmDescriptor2R24` host post-retarget): the turn-identity-pinned cap-open
transfer over the hardened face (`effCapOpenV3TB` is fully parametric in its base, so the
cap-open appendix and turn-identity pins ride the avail-shifted graduated width verbatim). -/
def transferCapOpenTBAvailWide : EffectVmDescriptor2 :=
  wideAppend
    (Dregg2.Circuit.Emit.CapOpenTurnPins.effCapOpenV3TB transferAvailV3W
      "dregg-effectvm-transfer-v1-avail-rot24-v3-capopen-eff-tb"
      Dregg2.Circuit.Emit.CapOpenEmit.EFF_TRANSFER)
    TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN)

/-- **`transferAvailWideRefused`** — the crown member as EMITTED under the bare-cohort
capacity-floor refuse, at the AVAIL-shifted caveat base (`cavBaseOf AVAIL_WIDTH = 676`; aux
blocks past the member's own width, above the wide carriers). This is the exact
`WIDE_REGISTRY_STAGED_TSV` row object for the transfer key post-retarget, and the host the
umem-welded twin welds (refuse-first, the runtime producer's composition). -/
def transferAvailWideRefused : EffectVmDescriptor2 :=
  gentianDeployedBareRefuseAt (cavBaseOf AVAIL_WIDTH) transferV3MembershipAvailWide

-- Geometry pins: the avail crown mirrors the bare crown (+10 pad): 68 PIs, the wide member plus its
-- two teeth columns; the TB member its cap-open/TB delta past that; the refused crown +45 aux.
-- ⚑ The widths were the literals 2823 / 3150 / 2823+45, retyped once per flag day and red once per
-- flag day. Each is now the RELATION it stood for: an emitted descriptor against another emitted
-- descriptor plus a delta the rotation geometry does not move.
#guard transferV3MembershipAvailWide.piCount == 61
#guard transferV3MembershipAvailWide.traceWidth
  == transferAvailV3W.traceWidth + wideAppendixSpan + 2
#guard transferV3MembershipAvailWide.name == "dregg-effectvm-transfer-v1-avail-rot24-v3-staged"
-- ⚑ 2026-07-30: TB piCount 65 → 63 and width 3024 → 3038, the two unforced `actor`/`dst`
-- publications deleted (`UnforcedPiPins`); the convergence re-emit rotates the wide registry FP.
#guard transferCapOpenTBAvailWide.piCount == 56
#guard transferCapOpenTBAvailWide.traceWidth
  == transferV3MembershipAvailWide.traceWidth + 327
#guard transferCapOpenTBAvailWide.name
  == "dregg-effectvm-transfer-v1-avail-rot24-v3-capopen-eff-tb"
#guard transferAvailWideRefused.traceWidth
  == transferV3MembershipAvailWide.traceWidth + 45
#guard transferAvailWideRefused.name
  == "dregg-effectvm-transfer-v1-avail-rot24-v3-staged-gentian-deployed-bare-refuse"
-- The bare crown twin for reference: same PI layout, avail-shifted columns.
#guard Dregg2.Circuit.Emit.CarrierComposed.transferV3MembershipWide.piCount == 61
#guard transferV3MembershipAvailWide.traceWidth
  == Dregg2.Circuit.Emit.CarrierComposed.transferV3MembershipWide.traceWidth + 10

/-! ## §3 — the pin-cleanliness + membership embeds. -/

/-- No hardened-face v1 constraint is a retired legacy commit pin: every face piBinding column
rides the v1 face (`< AVAIL_WIDTH`), far below the rotated commit carriers
(`TR_AVAIL_BB + B_STATE_COMMIT = 383` / `TR_AVAIL_BB + B_SPAN + B_STATE_COMMIT = 630`). Decidable —
the face is concrete. -/
theorem transferAvail_no_legacy_pins :
    transferVmDescriptorAvail.constraints.all
      (fun c => !isLegacyCommitPin1 TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) (VmConstraint2.base c))
      = true := by decide

theorem transferAvail_clean :
    ∀ c ∈ transferVmDescriptorAvail.constraints,
      isLegacyCommitPin1 TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) (VmConstraint2.base c) = false := by
  intro c hc
  have h := List.all_eq_true.mp transferAvail_no_legacy_pins c hc
  simpa using h

/-- Face-host constraint membership in the CROWN avail wide member: the rc pins and the teeth
pins only APPEND, and `wideAppend` keeps every non-pin host constraint
(`wideAppend_mem_of_host`); the trailing teeth width bump keeps constraints verbatim. -/
theorem availHost_mem_membershipAvailWide :
    ∀ c ∈ transferAvailV3W.constraints,
      isLegacyCommitPin1 TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) c = false →
      c ∈ transferV3MembershipAvailWide.constraints := by
  intro c hc hnp
  show c ∈ transferMembershipAvailWideBase.constraints
  exact wideAppend_mem_of_host _ TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) c
    (List.mem_append_left _ (List.mem_append_left _ hc)) hnp

/-- Face-host constraint membership in the TB avail wide member (`effCapOpenV3TB` = base
constraints ++ cap-open appendix ++ turn-identity pins — all appends). -/
theorem availHost_mem_tbAvailWide :
    ∀ c ∈ transferAvailV3W.constraints,
      isLegacyCommitPin1 TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) c = false →
      c ∈ transferCapOpenTBAvailWide.constraints := by
  intro c hc hnp
  exact wideAppend_mem_of_host _ TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) c
    (List.mem_append_left _ (List.mem_append_left _ hc)) hnp

/-! ## §4 — the per-member v1 collapses: the hardened face's FULL row denotation returns from a
wide-faithful witness of either retargeted member (the borrow-weld gates + 15-bit teeth the
availability keystone `transferAvail_derives_availability_row` consumes). -/

/-- The CROWN avail wide member forces the hardened face's v1 denotation on every row. -/
theorem membershipAvailWide_row_v1 (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2FaithfulWide permOut hash transferV3MembershipAvailWide
      minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash transferVmDescriptorAvail (envAt t i)
        (i == 0) (i + 1 == t.rows.length) :=
  wideEmbedded_sound_v1 permOut hash transferVmDescriptorAvail transferV3MembershipAvailWide
    TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) minit mfin maddrs t (by decide) transferAvail_clean
    availHost_mem_membershipAvailWide hf

/-- The TB avail wide member forces the hardened face's v1 denotation on every row. -/
theorem tbAvailWide_row_v1 (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2FaithfulWide permOut hash transferCapOpenTBAvailWide minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash transferVmDescriptorAvail (envAt t i)
        (i == 0) (i + 1 == t.rows.length) :=
  wideEmbedded_sound_v1 permOut hash transferVmDescriptorAvail transferCapOpenTBAvailWide
    TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) minit mfin maddrs t (by decide) transferAvail_clean
    availHost_mem_tbAvailWide hf

#assert_axioms membershipAvailWide_row_v1
#assert_axioms tbAvailWide_row_v1

/-! ## §5 — the membership-teeth exposure keystone, carried through the retarget (the fold arm's
admission premise — a genuine `PiBinding` at every claim slot — holds on the AVAIL member at the
SAME PI slots 50..51). -/

theorem transferV3MembershipAvailWide_publishes_teeth (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash transferV3MembershipAvailWide minit mfin maddrs t)
    (h0 : 0 < t.rows.length) :
    ∀ j : Fin 2, (envAt t 0).loc (MEMBERSHIP_TEETH_COL_AVAIL_WIDE + j.val)
      ≡ (envAt t 0).pub ((withDfaRcPinsAt AVAIL_WIDTH transferAvailV3W).piCount + j.val)
        [ZMOD 2013265921] := by
  intro j
  have hfirstt : ((0 : Nat) == 0) = true := rfl
  have hinHost : VmConstraint2.base
      (.piBinding .first (MEMBERSHIP_TEETH_COL_AVAIL_WIDE + j.val)
        ((withDfaRcPinsAt AVAIL_WIDTH transferAvailV3W).piCount + j.val))
      ∈ (withMembershipTeethPinsAt MEMBERSHIP_TEETH_COL_AVAIL_WIDE
          (withDfaRcPinsAt AVAIL_WIDTH transferAvailV3W)).constraints := by
    rw [withMembershipTeethPinsAt_constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩)
  have hnp : isLegacyCommitPin1 TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN)
      (VmConstraint2.base (.piBinding .first (MEMBERSHIP_TEETH_COL_AVAIL_WIDE + j.val)
        ((withDfaRcPinsAt AVAIL_WIDTH transferAvailV3W).piCount + j.val))) = false := by
    have hj : j.val < 2 := j.isLt
    -- ⚑ 383 -> 386 at the 2026-08-01 key nonet (`B_STATE_COMMIT` 185 -> 188), and the teeth column
    -- is DERIVED now, so `omega` needs its value produced here. Both `decide`s are the gate: named
    -- constants against a number, red the moment the geometry moves.
    have hbb : TR_AVAIL_BB + B_STATE_COMMIT = 395 := by decide
    have hteeth : MEMBERSHIP_TEETH_COL_AVAIL_WIDE = 2973 := by decide
    simp only [isLegacyCommitPin1, beq_eq_false_iff_ne, ne_eq, hbb, hteeth]
    omega
  have hin : VmConstraint2.base
      (.piBinding .first (MEMBERSHIP_TEETH_COL_AVAIL_WIDE + j.val)
        ((withDfaRcPinsAt AVAIL_WIDTH transferAvailV3W).piCount + j.val))
      ∈ transferV3MembershipAvailWide.constraints := by
    show _ ∈ transferMembershipAvailWideBase.constraints
    exact wideAppend_mem_of_host _ TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) _ hinHost hnp
  have h := hsat.rowConstraints 0 h0 _ hin
  simp only [VmConstraint2.holdsAt, hfirstt, holdsVm_piFirst_true] at h
  exact h

#assert_axioms transferV3MembershipAvailWide_publishes_teeth

/-! ## §6 — the capacity-floor refuse teeth, re-closed on the REFUSED avail wide member (the
flag-day dodges do not regress through the retarget). -/

/-- A member of ANY of the three refuse blocks is a constraint of the refused member. -/
theorem blockAt_mem_refusedWide (g : VmConstraint2)
    (hg : g ∈ blockGatesAt (cavBaseOf AVAIL_WIDTH) transferV3MembershipAvailWide.traceWidth
        (tagSettleEscrow : ℤ) 0
      ∨ g ∈ blockGatesAt (cavBaseOf AVAIL_WIDTH) transferV3MembershipAvailWide.traceWidth
        (tagDischargeObligation : ℤ) 1
      ∨ g ∈ blockGatesAt (cavBaseOf AVAIL_WIDTH) transferV3MembershipAvailWide.traceWidth
        (tagVaultDeposit : ℤ) 2) :
    g ∈ transferAvailWideRefused.constraints := by
  show g ∈ (gentianDeployedBareRefuseAt (cavBaseOf AVAIL_WIDTH)
    transferV3MembershipAvailWide).constraints
  unfold Dregg2.Circuit.Emit.AvailWireMembers.gentianDeployedBareRefuseAt
    Dregg2.Circuit.Emit.AvailWireMembers.deployedRefuseGatesAt
  refine List.mem_append_right _ ?_
  simp only [List.mem_append]
  tauto

/-- **THE THREE DODGES, CLOSED ON THE REFUSED AVAIL WIDE MEMBER.** For a cell whose committed
manifest declares capacity tag `T` at block `b` (escrow 0 / discharge 1 / vault 2), a satisfying
witness of `transferAvailWideRefused` is FALSE — the mirror of
`AvailWireMembers.declared_capacity_unsat_availWire` at the wide composition. -/
theorem declared_capacity_unsat_availWideRefused (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (tag : ℤ) (b : Nat)
    (hblock : blockGatesAt (cavBaseOf AVAIL_WIDTH) transferV3MembershipAvailWide.traceWidth tag b
        = blockGatesAt (cavBaseOf AVAIL_WIDTH) transferV3MembershipAvailWide.traceWidth
            (tagSettleEscrow : ℤ) 0
      ∨ blockGatesAt (cavBaseOf AVAIL_WIDTH) transferV3MembershipAvailWide.traceWidth tag b
        = blockGatesAt (cavBaseOf AVAIL_WIDTH) transferV3MembershipAvailWide.traceWidth
            (tagDischargeObligation : ℤ) 1
      ∨ blockGatesAt (cavBaseOf AVAIL_WIDTH) transferV3MembershipAvailWide.traceWidth tag b
        = blockGatesAt (cavBaseOf AVAIL_WIDTH) transferV3MembershipAvailWide.traceWidth
            (tagVaultDeposit : ℤ) 2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash transferAvailWideRefused minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (htag : 0 ≤ tag ∧ tag < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash
        (manifestOf (cavBaseOf AVAIL_WIDTH) (ebAt (cavBaseOf AVAIL_WIDTH)) (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : tag ∈ manifestTags committedManifest) :
    False := by
  refine declared_tag_unsat_at hash hCR tag (cavBaseOf AVAIL_WIDTH) (ebAt (cavBaseOf AVAIL_WIDTH))
    (bcAt transferV3MembershipAvailWide.traceWidth b)
    (icAt transferV3MembershipAvailWide.traceWidth b)
    (ocAt transferV3MembershipAvailWide.traceWidth b)
    (fcAt transferV3MembershipAvailWide.traceWidth b)
    transferAvailWideRefused
    (fun g hg => blockAt_mem_refusedWide g ?_)
    (blockAt_mem_refusedWide _ ?_)
    hsat hi hnl hcanon htag committedManifest hbind hreq
  · rcases hblock with h | h | h
    · exact Or.inl (h ▸ decodeAt_mem_blockAt (cavBaseOf AVAIL_WIDTH)
        transferV3MembershipAvailWide.traceWidth tag b g hg)
    · exact Or.inr (Or.inl (h ▸ decodeAt_mem_blockAt (cavBaseOf AVAIL_WIDTH)
        transferV3MembershipAvailWide.traceWidth tag b g hg))
    · exact Or.inr (Or.inr (h ▸ decodeAt_mem_blockAt (cavBaseOf AVAIL_WIDTH)
        transferV3MembershipAvailWide.traceWidth tag b g hg))
  · rcases hblock with h | h | h
    · exact Or.inl (h ▸ refuseAt_mem_blockAt (cavBaseOf AVAIL_WIDTH)
        transferV3MembershipAvailWide.traceWidth tag b)
    · exact Or.inr (Or.inl (h ▸ refuseAt_mem_blockAt (cavBaseOf AVAIL_WIDTH)
        transferV3MembershipAvailWide.traceWidth tag b))
    · exact Or.inr (Or.inr (h ▸ refuseAt_mem_blockAt (cavBaseOf AVAIL_WIDTH)
        transferV3MembershipAvailWide.traceWidth tag b))

/-- Escrow (block 0) is UNSAT under the refused avail wide member when declared. -/
theorem declared_escrow_unsat_availWideRefused (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash transferAvailWideRefused minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash
        (manifestOf (cavBaseOf AVAIL_WIDTH) (ebAt (cavBaseOf AVAIL_WIDTH)) (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagSettleEscrow : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_availWideRefused hash hCR _ 0 (Or.inl rfl) hsat hi hnl hcanon
    (by decide) committedManifest hbind hreq

/-- Discharge (block 1) is UNSAT under the refused avail wide member when declared. -/
theorem declared_discharge_unsat_availWideRefused (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash transferAvailWideRefused minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash
        (manifestOf (cavBaseOf AVAIL_WIDTH) (ebAt (cavBaseOf AVAIL_WIDTH)) (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagDischargeObligation : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_availWideRefused hash hCR _ 1 (Or.inr (Or.inl rfl)) hsat hi hnl hcanon
    (by decide) committedManifest hbind hreq

/-- Vault (block 2) is UNSAT under the refused avail wide member when declared. -/
theorem declared_vault_unsat_availWideRefused (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash transferAvailWideRefused minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash
        (manifestOf (cavBaseOf AVAIL_WIDTH) (ebAt (cavBaseOf AVAIL_WIDTH)) (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagVaultDeposit : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_availWideRefused hash hCR _ 2 (Or.inr (Or.inr rfl)) hsat hi hnl hcanon
    (by decide) committedManifest hbind hreq

#assert_axioms blockAt_mem_refusedWide
#assert_axioms declared_capacity_unsat_availWideRefused
#assert_axioms declared_escrow_unsat_availWideRefused
#assert_axioms declared_discharge_unsat_availWideRefused
#assert_axioms declared_vault_unsat_availWideRefused

/-! ## §7 — THE WIDE-BURN TWIN (the LAST wrap-class member): the `burnVmDescriptor2R24` wide
crown host rebuilt over the §8¾ borrow-weld face.

The bare wide burn (`v3RegistryCapOpenWide`'s cohort entry: `wideAppend (withDfaRcPins burnV3)
188 427`) carries NO borrow gates, so the burn underflow-wrap — the WELL-SUPPLY-INFLATION
mint-from-nothing (`docs/FINDING-modp-wrap-forgery-audit.md`, forgery 2), STRICTLY WORSE than
the transfer twin (the ledger frame credits the well `(a,a)` by the forged amount) — stayed open
on the wide/welded leg after the bare + narrow-wire closes. The retarget mirrors the transfer §2
member-for-member, MINUS the membership teeth (burn's crown host is the plain cohort wide
member): the hardened face `v3OfFrozenWide burnVmDescriptorAvail`, rc pins at the avail-shifted
carrier (`withDfaRcPinsAt 196`), `wideAppend` at the burn AVAIL face base — PI count UNCHANGED at
66, width 2699 → 2707 (+8 avail pad; burn is debit-only, no credit-carry twin). -/

/-- The hardened rotated graduated burn face — the SAME term as
`RotatedKernelRefinementMintBurnAvail.burnV3Avail` (`v3OfFrozenWide burnVmDescriptorAvail`),
restated here so the emission layer does not import the refinement tower. -/
def burnAvailV3W : EffectVmDescriptor2 :=
  v3OfFrozenWide Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail

/-- The burn AVAIL wide BEFORE base: `rotateV3` lays the rotated limbs at the hardened FACE
width (`EffectVmEmitBurn.AVAIL_WIDTH = 196` — the bare 188 shifted by the 8-column burn avail
pad). -/
def BU_AVAIL_BB : Nat := Dregg2.Circuit.Emit.EffectVmEmitBurn.AVAIL_WIDTH

#guard BU_AVAIL_BB == Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail.traceWidth
#guard BU_AVAIL_BB == 196
#guard burnAvailV3W.piCount == 39
-- MODEL vs EMISSION (was the literal 1827 — decoration the key nonet moved).
#guard burnAvailV3W.traceWidth
  == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.gradRotWidthOf Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail
#guard graduableWide Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail
-- the Rust avail-pad key survives every wrapper (all append-only on the name)
#guard burnAvailV3W.name.startsWith "dregg-effectvm-burn-v1-avail"

/-- **`burnV3AvailWide`** — the burn crown wide host post-retarget (the `burnVmDescriptor2R24`
wide-registry host): the plain cohort wide member rebuilt over the hardened availability face,
rc pins at the AVAIL-shifted caveat rc carrier, wide-appended at the burn AVAIL face base.
Geometry mirror of the bare wide burn at the avail pad (+8 everywhere; 66 PIs UNCHANGED — burn
carries no membership teeth). -/
def burnV3AvailWide : EffectVmDescriptor2 :=
  wideAppend (withDfaRcPinsAt BU_AVAIL_BB burnAvailV3W) BU_AVAIL_BB (BU_AVAIL_BB + B_SPAN)

/-- **`burnAvailWideRefused`** — the crown burn member as EMITTED under the bare-cohort
capacity-floor refuse, at the burn-AVAIL-shifted caveat base (`cavBaseOf 196 = 690`; aux blocks
past the member's OWN width, above the wide carriers). This is the exact
`WIDE_REGISTRY_STAGED_TSV` row object for the burn key post-retarget, and the host the
umem-welded twin welds (refuse-first, the runtime producer's composition). -/
def burnAvailWideRefused : EffectVmDescriptor2 :=
  gentianDeployedBareRefuseAt (cavBaseOf BU_AVAIL_BB) burnV3AvailWide

-- Geometry pins: the avail crown mirrors the bare wide burn (+8 pad): 66 PIs (46 + 4 rc + 16
-- wide anchors), the wide-graduated face plus the wide appendix; the refused crown +45 aux columns.
-- ⚑ The literals 2819 / 2819+45 were decoration and moved with the key nonet.
#guard burnV3AvailWide.piCount == 59
#guard burnV3AvailWide.traceWidth == burnAvailV3W.traceWidth + wideAppendixSpan
#guard burnV3AvailWide.name == "dregg-effectvm-burn-v1-avail-rot24-v3-staged"
#guard burnAvailWideRefused.piCount == 59
#guard burnAvailWideRefused.traceWidth == burnV3AvailWide.traceWidth + 45
#guard burnAvailWideRefused.name
  == "dregg-effectvm-burn-v1-avail-rot24-v3-staged-gentian-deployed-bare-refuse"
-- The bare wide burn twin for reference: SAME 66-PI layout, avail-shifted columns.
#guard (Dregg2.Circuit.Emit.CapOpenEmit.v3RegistryCapOpenWide.lookup
    "burnVmDescriptor2R24").any
  (fun d => d.piCount == 59 && d.traceWidth + 8 == burnV3AvailWide.traceWidth)

/-! ### §7.1 — the pin-cleanliness + membership embed (the `wideEmbedded_sound_v1` premises). -/

/-- No hardened-burn-face v1 constraint is a retired legacy commit pin: every face piBinding
column rides the v1 face (`< 196`), far below the rotated commit carriers
(`BU_AVAIL_BB + B_STATE_COMMIT` / `BU_AVAIL_BB + B_SPAN + B_STATE_COMMIT`). Decidable — the face is
concrete. -/
theorem burnAvail_no_legacy_pins :
    Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail.constraints.all
      (fun c => !isLegacyCommitPin1 BU_AVAIL_BB (BU_AVAIL_BB + B_SPAN) (VmConstraint2.base c))
      = true := by decide

theorem burnAvail_clean :
    ∀ c ∈ Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail.constraints,
      isLegacyCommitPin1 BU_AVAIL_BB (BU_AVAIL_BB + B_SPAN) (VmConstraint2.base c) = false := by
  intro c hc
  have h := List.all_eq_true.mp burnAvail_no_legacy_pins c hc
  simpa using h

/-- Face-host constraint membership in the burn avail wide member: the rc pins only APPEND, and
`wideAppend` keeps every non-pin host constraint (`wideAppend_mem_of_host`). -/
theorem availHost_mem_burnAvailWide :
    ∀ c ∈ burnAvailV3W.constraints,
      isLegacyCommitPin1 BU_AVAIL_BB (BU_AVAIL_BB + B_SPAN) c = false →
      c ∈ burnV3AvailWide.constraints := by
  intro c hc hnp
  refine wideAppend_mem_of_host _ BU_AVAIL_BB (BU_AVAIL_BB + B_SPAN) c ?_ hnp
  rw [withDfaRcPinsAt_constraints]
  exact List.mem_append_left _ hc

/-! ### §7.2 — the per-member v1 collapse: the hardened burn face's FULL row denotation returns
from a wide-faithful witness of the retargeted member (the borrow-weld gates + 15-bit teeth the
availability keystone `burnAvail_derives_availability_row` consumes). -/

/-- The burn crown avail wide member forces the hardened burn face's v1 denotation on every
row. -/
theorem burnAvailWide_row_v1 (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2FaithfulWide permOut hash burnV3AvailWide minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail
        (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  wideEmbedded_sound_v1 permOut hash
    Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail burnV3AvailWide
    BU_AVAIL_BB (BU_AVAIL_BB + B_SPAN) minit mfin maddrs t (by decide) burnAvail_clean
    availHost_mem_burnAvailWide hf

#assert_axioms burnAvail_clean
#assert_axioms availHost_mem_burnAvailWide
#assert_axioms burnAvailWide_row_v1

/-! ### §7.3 — the capacity-floor refuse teeth, re-closed on the REFUSED burn avail wide member
(the settle-as-BURN dodge does not regress through the retarget). -/

/-- A member of ANY of the three refuse blocks is a constraint of the refused burn member. -/
theorem blockAt_mem_burnRefusedWide (g : VmConstraint2)
    (hg : g ∈ blockGatesAt (cavBaseOf BU_AVAIL_BB) burnV3AvailWide.traceWidth
        (tagSettleEscrow : ℤ) 0
      ∨ g ∈ blockGatesAt (cavBaseOf BU_AVAIL_BB) burnV3AvailWide.traceWidth
        (tagDischargeObligation : ℤ) 1
      ∨ g ∈ blockGatesAt (cavBaseOf BU_AVAIL_BB) burnV3AvailWide.traceWidth
        (tagVaultDeposit : ℤ) 2) :
    g ∈ burnAvailWideRefused.constraints := by
  show g ∈ (gentianDeployedBareRefuseAt (cavBaseOf BU_AVAIL_BB) burnV3AvailWide).constraints
  unfold Dregg2.Circuit.Emit.AvailWireMembers.gentianDeployedBareRefuseAt
    Dregg2.Circuit.Emit.AvailWireMembers.deployedRefuseGatesAt
  refine List.mem_append_right _ ?_
  simp only [List.mem_append]
  tauto

/-- **THE THREE DODGES, CLOSED ON THE REFUSED BURN AVAIL WIDE MEMBER.** For a cell whose
committed manifest declares capacity tag `T` at block `b` (escrow 0 / discharge 1 / vault 2), a
satisfying witness of `burnAvailWideRefused` is FALSE — the burn mirror of
`declared_capacity_unsat_availWideRefused`. -/
theorem declared_capacity_unsat_burnAvailWideRefused (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (tag : ℤ) (b : Nat)
    (hblock : blockGatesAt (cavBaseOf BU_AVAIL_BB) burnV3AvailWide.traceWidth tag b
        = blockGatesAt (cavBaseOf BU_AVAIL_BB) burnV3AvailWide.traceWidth
            (tagSettleEscrow : ℤ) 0
      ∨ blockGatesAt (cavBaseOf BU_AVAIL_BB) burnV3AvailWide.traceWidth tag b
        = blockGatesAt (cavBaseOf BU_AVAIL_BB) burnV3AvailWide.traceWidth
            (tagDischargeObligation : ℤ) 1
      ∨ blockGatesAt (cavBaseOf BU_AVAIL_BB) burnV3AvailWide.traceWidth tag b
        = blockGatesAt (cavBaseOf BU_AVAIL_BB) burnV3AvailWide.traceWidth
            (tagVaultDeposit : ℤ) 2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash burnAvailWideRefused minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (htag : 0 ≤ tag ∧ tag < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash
        (manifestOf (cavBaseOf BU_AVAIL_BB) (ebAt (cavBaseOf BU_AVAIL_BB)) (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : tag ∈ manifestTags committedManifest) :
    False := by
  refine declared_tag_unsat_at hash hCR tag (cavBaseOf BU_AVAIL_BB)
    (ebAt (cavBaseOf BU_AVAIL_BB))
    (bcAt burnV3AvailWide.traceWidth b)
    (icAt burnV3AvailWide.traceWidth b)
    (ocAt burnV3AvailWide.traceWidth b)
    (fcAt burnV3AvailWide.traceWidth b)
    burnAvailWideRefused
    (fun g hg => blockAt_mem_burnRefusedWide g ?_)
    (blockAt_mem_burnRefusedWide _ ?_)
    hsat hi hnl hcanon htag committedManifest hbind hreq
  · rcases hblock with h | h | h
    · exact Or.inl (h ▸ decodeAt_mem_blockAt (cavBaseOf BU_AVAIL_BB)
        burnV3AvailWide.traceWidth tag b g hg)
    · exact Or.inr (Or.inl (h ▸ decodeAt_mem_blockAt (cavBaseOf BU_AVAIL_BB)
        burnV3AvailWide.traceWidth tag b g hg))
    · exact Or.inr (Or.inr (h ▸ decodeAt_mem_blockAt (cavBaseOf BU_AVAIL_BB)
        burnV3AvailWide.traceWidth tag b g hg))
  · rcases hblock with h | h | h
    · exact Or.inl (h ▸ refuseAt_mem_blockAt (cavBaseOf BU_AVAIL_BB)
        burnV3AvailWide.traceWidth tag b)
    · exact Or.inr (Or.inl (h ▸ refuseAt_mem_blockAt (cavBaseOf BU_AVAIL_BB)
        burnV3AvailWide.traceWidth tag b))
    · exact Or.inr (Or.inr (h ▸ refuseAt_mem_blockAt (cavBaseOf BU_AVAIL_BB)
        burnV3AvailWide.traceWidth tag b))

/-- Escrow (block 0) is UNSAT under the refused burn avail wide member when declared. -/
theorem declared_escrow_unsat_burnAvailWideRefused (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash burnAvailWideRefused minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash
        (manifestOf (cavBaseOf BU_AVAIL_BB) (ebAt (cavBaseOf BU_AVAIL_BB)) (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagSettleEscrow : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_burnAvailWideRefused hash hCR _ 0 (Or.inl rfl) hsat hi hnl hcanon
    (by decide) committedManifest hbind hreq

/-- Discharge (block 1) is UNSAT under the refused burn avail wide member when declared. -/
theorem declared_discharge_unsat_burnAvailWideRefused (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash burnAvailWideRefused minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash
        (manifestOf (cavBaseOf BU_AVAIL_BB) (ebAt (cavBaseOf BU_AVAIL_BB)) (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagDischargeObligation : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_burnAvailWideRefused hash hCR _ 1 (Or.inr (Or.inl rfl)) hsat hi hnl
    hcanon (by decide) committedManifest hbind hreq

/-- Vault (block 2) is UNSAT under the refused burn avail wide member when declared. -/
theorem declared_vault_unsat_burnAvailWideRefused (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash burnAvailWideRefused minit mfin maddrs t)
    (hi : 0 < t.rows.length) (hnl : (0 + 1 == t.rows.length) = false)
    (hcanon : ∀ r c, 0 ≤ (envAt t r).loc c ∧ (envAt t r).loc c < 2013265921)
    (committedManifest : RotCaveatManifest)
    (hbind : caveatCommit hash
        (manifestOf (cavBaseOf BU_AVAIL_BB) (ebAt (cavBaseOf BU_AVAIL_BB)) (envAt t 0).loc)
      = caveatCommit hash committedManifest)
    (hreq : (tagVaultDeposit : ℤ) ∈ manifestTags committedManifest) :
    False :=
  declared_capacity_unsat_burnAvailWideRefused hash hCR _ 2 (Or.inr (Or.inr rfl)) hsat hi hnl
    hcanon (by decide) committedManifest hbind hreq

#assert_axioms blockAt_mem_burnRefusedWide
#assert_axioms declared_capacity_unsat_burnAvailWideRefused
#assert_axioms declared_escrow_unsat_burnAvailWideRefused
#assert_axioms declared_discharge_unsat_burnAvailWideRefused
#assert_axioms declared_vault_unsat_burnAvailWideRefused

/-! ## §8 — the AVAIL cap-open EFF wide transfer member (the wide-cap-open-EFF availability
wrap-forgery twin — the `transferCapOpenEffVmDescriptor2R24` crown host post-retarget).

The TB twin (§2) is a LIVE-ONLY tail member; the EFF member is a CROWN member
(`v3RegistryCapOpenWide` position 42), so its retarget rides the crown override
(`EffectVmEmitUMemWeldWide.crownWideHosts` / the bare `EmitWideRegistryProbe` row), not the
live-only tail. Same shape either way: the already-flipped narrow member
(`RotatedKernelRefinementCapOpenAvail.transferCapOpenEffV3Avail` — the selector-gated
effect-general cap-open over the hardened rotated face) wide-appended at the AVAIL face base. -/

/-- **`transferCapOpenEffAvailWide`** — the AVAIL live cap-open EFF wide transfer member: the
selector-gated effect-general cap-open transfer (`withSelectorGate TRANSFER (effCapOpenV3 …)`,
fully parametric in its base) over the hardened rotated face, wide-appended at the AVAIL face
base `TR_AVAIL_BB`. The `transferCapOpenEffVmDescriptor2R24` crown key's post-retarget bytes —
the wide lift of the already-flipped narrow `transferCapOpenEffV3Avail` (definitionally
`wideAppend transferCapOpenEffV3Avail TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN)`; the refinement tower
states that tie, this layer restates the term so the emission layer does not import it). -/
def transferCapOpenEffAvailWide : EffectVmDescriptor2 :=
  wideAppend
    (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withSelectorGate
      Dregg2.Circuit.Emit.EffectVmEmit.sel.TRANSFER
      (Dregg2.Circuit.Emit.CapOpenEmit.effCapOpenV3 transferAvailV3W
        "dregg-effectvm-transfer-v1-avail-rot24-v3-capopen-eff"
        Dregg2.Circuit.Emit.CapOpenEmit.EFF_TRANSFER))
    TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN)

-- Geometry pins: the EFF member is the narrow avail cap-open plus the wide appendix (+16 PIs).
-- ⚑ The literal 3150 was decoration; stated as the relation, it rides the flag day.
#guard transferCapOpenEffAvailWide.piCount == 55
#guard transferCapOpenEffAvailWide.traceWidth
  == transferV3MembershipAvailWide.traceWidth + 327
#guard transferCapOpenEffAvailWide.name
  == "dregg-effectvm-transfer-v1-avail-rot24-v3-capopen-eff"

/-- Face-host constraint membership in the EFF avail wide member (`withSelectorGate` and
`effCapOpenV3` both only APPEND, and `wideAppend` keeps every non-pin host constraint). -/
theorem availHost_mem_effAvailWide :
    ∀ c ∈ transferAvailV3W.constraints,
      isLegacyCommitPin1 TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) c = false →
      c ∈ transferCapOpenEffAvailWide.constraints := by
  intro c hc hnp
  exact wideAppend_mem_of_host _ TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) c
    (List.mem_append_left _ (List.mem_append_left _ hc)) hnp

/-- No cap-open appendix constraint is a retired legacy commit pin (the appendix is all
`.lookup`s + `.base (.gate …)`s — never a `.piBinding`). Decidable — the appendix is concrete. -/
theorem capOpenAppendixAvail_no_legacy_pins :
    (Dregg2.Circuit.Emit.CapOpenEmit.capOpenConstraintsEff transferAvailV3W.traceWidth
        Dregg2.Circuit.Emit.CapOpenEmit.EFF_TRANSFER).all
      (fun c => !isLegacyCommitPin1 TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) c) = true := by decide

/-- **The cap-open AUTHORITY appendix rides the wide member VERBATIM** — every appendix
constraint (the depth-16 membership open, the submask facet gates, the mask-recon gates, the
selected-bit tooth) is a constraint of `transferCapOpenEffAvailWide`. This is what
`capOpenMem_satisfiedEff` / `capOpenMem_gate_forces` consume to re-establish the authority
keystones on the wide member: the wide weld does not break the facet gates. -/
theorem capOpenAppendix_mem_effAvailWide :
    ∀ c ∈ Dregg2.Circuit.Emit.CapOpenEmit.capOpenConstraintsEff transferAvailV3W.traceWidth
        Dregg2.Circuit.Emit.CapOpenEmit.EFF_TRANSFER,
      c ∈ transferCapOpenEffAvailWide.constraints := by
  intro c hc
  have hnp := List.all_eq_true.mp capOpenAppendixAvail_no_legacy_pins c hc
  exact wideAppend_mem_of_host _ TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) c
    (List.mem_append_left _ (List.mem_append_right _ hc)) (by simpa using hnp)

/-- The EFF avail wide member forces the hardened face's v1 denotation on every row (the
borrow-weld gates + 15-bit teeth `transferAvail_derives_availability_row` consumes). -/
theorem effAvailWide_row_v1 (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2FaithfulWide permOut hash transferCapOpenEffAvailWide minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash transferVmDescriptorAvail (envAt t i)
        (i == 0) (i + 1 == t.rows.length) :=
  wideEmbedded_sound_v1 permOut hash transferVmDescriptorAvail transferCapOpenEffAvailWide
    TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN) minit mfin maddrs t (by decide) transferAvail_clean
    availHost_mem_effAvailWide hf

#assert_axioms availHost_mem_effAvailWide
#assert_axioms capOpenAppendix_mem_effAvailWide
#assert_axioms effAvailWide_row_v1

end Dregg2.Circuit.Emit.AvailWideMembers
