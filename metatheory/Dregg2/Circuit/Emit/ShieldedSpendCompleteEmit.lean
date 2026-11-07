/-
# Dregg2.Circuit.Emit.ShieldedSpendCompleteEmit — the COMPLETE FSI2 spend descriptor
(Fork B pass B: membership + leaf sponge + nullifier + wide carrier, ONE routable object).

**This is Lean-authored AIR, emitted.** Rust parses the byte-pinned golden and supplies witnesses;
it authors no constraint. This module COMPLETES the landed membership descriptor
(`ShieldedSpendExactMembershipEmit.shieldedSpendExactDesc`, `e1f66f4fd`) into the full spend
relation Pass C can route as the `spend_circuit.rs` replacement WITHOUT dropping a soundness check.
The constraint list literally EXTENDS the landed membership core (its constraints are the prefix,
verbatim — `mem_of_membership_core`), so `root_is_pinned8` re-derives here unchanged
(`complete_root_is_pinned8`) and everything the membership rung proved stays proved of THIS object.

VK name: `dregg-shielded-spend-complete-fsi2::v1`. The membership-only
`dregg-shielded-spend-exact-fsi2::v1` remains the proven CORE RUNG and is NOT the route target —
routing it would drop the nullifier and the value binding, a regression worse than #15.

## The three completed pieces (each satisfiable AND refutable, none trivially true)

1. **The FSI2 leaf sponge** (`leafSponge` + `leafBind` + `noteTie`): row-0 `current[0..8]` is
   boundary-bound to the squeezed digest of an IN-TRACE `hash_many_8` sponge over the FSI2
   exact-linked leaf block `[FSI2, REAL=1, addr0, addr1, 0×14, 0×4(value: the HIDING column),
   nextTag, next0..15]` (`ShieldedExactMembershipFold.shieldedLeafBlock`, 39 felts —
   `cell/src/shielded_note_set.rs` `FSI2 ‖ addr17 ‖ value4 ‖ next17`), and `noteTie` pins
   `cCM ≡ addr0 + 2^16·addr1` — the `felt_to_bytes32`/`raw_to_u16_le` address image of the minted
   commitment (bytes 0..4 = the felt LE, so limbs 0,1 carry it and limbs 2..15 are zero).
   With `lkCM` (`cCM = hash_fact(cVMOD,[cAMOD,cOWNER,cRAND])` — byte-for-byte the relation
   `ShieldedShieldDescriptor.lkCM` mints, so `shield_mints_the_object_the_spend_opens` is the tie),
   the leaf the fold walks IS the note commitment the Shield minted. Teeth: `wrong_leaf_refused`
   (row-0 `current` decoupled from the leaf digest), `foreign_note_refused` (`cCM` decoupled from
   the opened address).

2. **The nullifier** (`lkNullifier` + `lkOwnerDerive` + the `piNUL` pin): `cNUL =
   hash_fact(cCM, key[0..4])` and `cOWNER = hash_fact(key[0..4])` (the C8 owner derivation — the
   double-spend closure: a fresh key commits a DIFFERENT note, it does not re-spend this one), with
   `cNUL` pinned to PI 0. The nullifier DERIVES from the opened note: a spend cannot publish a
   nullifier for a note it does not open. Teeth: `forged_nullifier_refused` /
   `foreign_nullifier_unsat`.

3. **The wide value carrier** (`carrierGates` + `carrierSites`): the 16 `piWide` lanes (already
   `.piBinding`-reserved by the membership core) are now the OUTPUT columns of two domain-separated
   arity-16 `cap_node8` chip absorbs over `[DOMAIN, v0..v3, a0..a2] ‖ [a3, rand, blind0..5]` —
   column-for-column the sidecar shape (`WideValueBindingEmit.wideLeft/wideRight`, same
   `DOMAIN_A`/`DOMAIN_B`, so the routed join `verify_same_opening` compares like against like) —
   with the R1/R2/R3 felt-width block: 128 boolean bit pins, 8 limb recompositions, and
   `cVMOD`/`cAMOD` recomposed from EXACTLY the limbs the carrier absorbs. `cVMOD`/`cRAND` are the
   SAME cells `lkCM` hashes into the note commitment, so the carrier opens the NOTE's own
   `(value, asset, randomness)` — `published_carrier_is_the_cap_node8_image` lands the published
   lanes on `permW (carrierIns …)`, the exact object
   `ShieldedWideJoinPin`/`WideValueBindingRefine.alias_separated_by_the_wide_carrier` separates
   under the named `WideCarrierCR` floor. NEVER `value mod p` relabelled: the lanes are permutation
   images of the full limb decomposition. Tooth: `decoupled_carrier_refused`.

Also repaired here (found while completing): the membership core's position-bit gates ride the
`when_transition()` domain and so did NOT bind on the LAST row — the row whose node digest is
pinned to the committed root. `lastRowBitRepair` re-lowers both bit gates as `.boundary .last`
(the deployed last-row-repair shape `ShieldedSpendDescriptor` uses). The landed membership golden
is unchanged; the completed descriptor carries the repair.

## What a satisfying trace is FORCED to carry (the Pass C interface)

Under `Satisfied2` + the chip-soundness floors (`ChipTableSoundState16 perm16` for the state16 bus,
`ChipTableSound hash` narrow-served for the fact bus, `ChipTableSoundN permW` for the wide bus):
  * `complete_root_is_pinned8` — the fold root ≡ the 8-lane committed PI (the #15 pin, unchanged);
  * `leaf_bound_to_current8` + `leaf_sponge_executes` — row-0 `current` IS the genuine sponge
    digest of the FSI2 leaf block in the trace;
  * `note_tied_to_leaf_address` + `cm_opens_row0` — that leaf's address ≡ `cCM`, and `cCM` is the
    genuine `hash_fact` note commitment of `(cVMOD, cAMOD, cOWNER, cRAND)`;
  * `nullifier_derived_row0` + `owner_derived_row0` + `nullifier_published` — the published
    nullifier is the genuine derivation from `cCM` and the spending key;
  * `carrierA_lanes_forced`/`carrierB_lanes_forced` + `published_carrier_is_the_cap_node8_image`
    — the 16 published lanes are the genuine domain-separated `cap_node8` images of the note's
    limb opening; `vmod_reduced`/`amod_reduced` + `spend_limb_canonical` tie the hashed felts to
    canonical 16-bit limbs (transition rows — the real 16-row membership trace has 15 of them).

## Honest scope — named, not laundered

  * The zero witness (`zero_witness_satisfies`) is a ONE-row trace: `.gate`/window constraints ride
    `when_transition()` and are vacuous there, exactly as in the landed
    `ShieldedSpendDescriptor.zero_witness_satisfies` precedent. The chip tables it carries are
    GENUINE `pz16`/`pz8`/`hzero` rows (not copied claims); satisfiability of the full 16-row
    membership geometry with the real permutation is the prover's job at the route step, where the
    Rust witness generator fills it (the same status as every landed sponge descriptor).
  * `addr0`/`addr1` carry no range pins HERE: the spend side opens a leaf the COMMITTED tree holds,
    and committed leaves are canonical by the append side (the L2 grow-gate owns canonicity). The
    tie is mod-p, which is exact on canonical commitments (< p).
  * The next-pointer cells (`cNEXTTAG`, `cNEXT*`) are free witnesses — membership pins the leaf to
    the committed root; the pointer content is whatever the committed leaf holds.
  * `deployed_admits_but_pin_rejects` stays LIVE — #15 flips at Pass C (the route), not here.
  * Floors: `ChipTableSound*` are hypotheses of the semantic theorems (the chip AIR's own
    faithfulness), `WideCarrierCR` is same-opening's named floor — satisfiable and refutable,
    never proven.

`#assert_axioms` on every keystone; the golden byte pin is `native_decide` + `#assert_compiled`
(compiled-string equality; the same check a `#guard` would run, with the trust said out loud).
-/
import Dregg2.Circuit.Emit.ShieldedSpendExactMembershipEmit
import Dregg2.Circuit.Emit.ShieldedSpendDescriptor
import Dregg2.Circuit.Emit.ShieldedExactMembershipFold
import Dregg2.Circuit.Emit.WideValueBindingRefine

namespace Dregg2.Circuit.Emit.ShieldedSpendCompleteEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId Table TraceFamily VmTrace zeroAsg envAt
   Satisfied2 mainTableDef poseidon2State16ChipTableDef poseidon2state16 chipLookupTupleState16
   chipRowState16 ChipTableSoundState16 chip_lookup_sound_state16 CHIP_STATE_LANES
   chipLookupTupleN chipRowN ChipTableSoundN chip_lookup_sound_N chipLookupTupleNarrow
   poseidon2narrow ChipTableSound emitVmJson2 memLog mapLog memOpsOf mapOpsOf
   CHIP_RATE CHIP_OUT_LANES)
open Dregg2.Circuit.ChipNarrowLookup (narrowTable narrowRow chip_lookup_narrow_sound_of_wide_table)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.Emit.BlindedMembershipEmit (ev ek eadd emul eneg esub)
open Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan (spongePlan State16Step stateCols)
open Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan (v3State16Lookup digestColsAt)
open Dregg2.Circuit.Emit.ShieldedSpendExactMembershipDescriptor
  (piCommitted piWide piNUL PI_COMMITTED_BASE PI_COMMITTED_LANES PI_WIDE_BASE PI_WIDE_LANES
   SPEND_PI_COUNT)
open Dregg2.Circuit.Emit.ShieldedSpendExactMembershipEmit
  (MCUR MB0 MB1 MSIB MWIDE MNODE M_WIDTH nodeDigestCols nodePreimage nodeSponge bitGates posBody
   contConstraints rootPins carrierPins shieldedSpendExactDesc)
open Dregg2.Circuit.Emit.ShieldedSpendDescriptor (factIns factIns_eval_4 factIns_eval_5
   NS_FACT_MARK hzero zChipRow)
open Dregg2.Circuit.Emit.ShieldedExactMembershipFold (SHIELDED_LEAF_DOMAIN)
open Dregg2.Circuit.Emit.WideValueBindingEmit (DOMAIN_A DOMAIN_B limbWeight U64_LIMBS LIMB_BITS
   BLIND_LANES)
open Dregg2.Circuit.Emit.WideValueBindingRefine (Canon bin_of_gate bitSum bitSum_bounds
   limbWeight_modEq sum_modEq carrierIns WideCarrierCR)
open Dregg2.Circuit.Emit.AirBuilder

set_option autoImplicit false
set_option maxRecDepth 8192

/-! ## §1 — the new columns (extending the membership core's 0..209 layout). -/

/-- `value mod p` — the narrow value felt `lkCM` absorbs, recomposed from the carrier limbs. -/
def cVMOD : Nat := 210
/-- `asset mod p`. -/
def cAMOD : Nat := 211
/-- The note owner (hidden; DERIVED from the spending key by `lkOwnerDerive`). -/
def cOWNER : Nat := 212
/-- The note randomness (hidden; absorbed by BOTH `lkCM` and the wide carrier — the coupling). -/
def cRAND : Nat := 213
/-- The recomputed note commitment `hash_fact(cVMOD,[cAMOD,cOWNER,cRAND])`. -/
def cCM : Nat := 214
/-- The published nullifier `hash_fact(cCM, key[0..4])` (pinned to `piNUL`). -/
def cNUL : Nat := 215
/-- Spending-key limb `i` (the deployed 4-limb binding). -/
def cKEY (i : Nat) : Nat := 216 + i
/-- Value `u16` limb `i` (little-endian; the carrier absorb + the `cVMOD` recomposition). -/
def cV (i : Nat) : Nat := 220 + i
/-- Asset `u16` limb `i`. -/
def cA (i : Nat) : Nat := 224 + i
/-- Carrier blind lane `i` (the sidecar's `BINDING_BLIND_LANES` twin). -/
def cBL (i : Nat) : Nat := 228 + i
/-- Leaf-address limb 0 — `cCM & 0xFFFF` on a canonical commitment. -/
def cADDR0 : Nat := 234
/-- Leaf-address limb 1 — `cCM >> 16` (fits `u15`: `p < 2^31`). -/
def cADDR1 : Nat := 235
/-- The opened leaf's `next_addr` tag (free witness — the committed leaf's content). -/
def cNEXTTAG : Nat := 236
/-- The opened leaf's `next_addr` limb `i` (free witness). -/
def cNEXT (i : Nat) : Nat := 237 + i
/-- The FSI2 leaf sponge state block (11 `state16` steps × 16 lanes: 253..428). -/
def LEAF_STATE_BASE : Nat := 253
/-- Base of the carrier bit-decomposition block (2 kinds × 4 limbs × 16 bits: 429..556). -/
def SPEND_BITS_BASE : Nat := 429
/-- Bit `b` of limb `i` of kind `k` (`0 = value`, `1 = asset`). -/
def cBit (k i b : Nat) : Nat := SPEND_BITS_BASE + (k * U64_LIMBS + i) * LIMB_BITS + b
/-- Limb `i` of kind `k` — the sidecar's `col::limb` shape over THIS layout. -/
def cLimbS (k i : Nat) : Nat := if k = 0 then cV i else cA i
/-- **The completed main-trace width.** -/
def C_WIDTH : Nat := SPEND_BITS_BASE + 2 * U64_LIMBS * LIMB_BITS

theorem c_width_val : C_WIDTH = 557 := rfl
theorem new_columns_start_after_the_core : M_WIDTH = 210 := rfl

/-! ## §2 — piece 1: the FSI2 leaf sponge, the leaf↔current bind, and the note tie. -/

/-- The FSI2 exact-linked leaf preimage, IN THE TRACE: `[FSI2, REAL=1, addr0, addr1, 0×14,
0×4 (the HIDING value column — zero BY CONSTRUCTION, `shielded_note_set.rs` R1), nextTag,
next0..15]` — 39 felts, the `shieldedLeafBlock` shape with the Shield-minted address image
(`felt_to_bytes32` ∘ `raw_to_u16_le`: limbs 0,1 carry the commitment felt, limbs 2..15 are zero). -/
def leafPreimage : List EmittedExpr :=
  [.const SHIELDED_LEAF_DOMAIN, .const 1, .var cADDR0, .var cADDR1]
    ++ List.replicate 14 (.const 0)
    ++ List.replicate 4 (.const 0)
    ++ (.var cNEXTTAG :: (List.range 16).map fun i => .var (cNEXT i))

theorem leafPreimage_length : leafPreimage.length = 39 := rfl

/-- The leaf sponge plan — the SAME deployed `hash_many_8` schedule (`spongePlan`) the node fold
uses: 10 rate-4 absorbs + 1 squeeze over the 39-felt block. -/
def leafPlan : List State16Step := spongePlan LEAF_STATE_BASE leafPreimage

/-- The node sponge plan (the membership core's — named here for the execution theorems). -/
def nodePlan : List State16Step := spongePlan MNODE nodePreimage

/-- The FSI2 leaf digest columns (8 lanes, the `digestColsAt` convention at 10 absorb chunks). -/
def leafDigestCols : List Nat := digestColsAt LEAF_STATE_BASE 10

theorem leafPlan_length : leafPlan.length = 11 := rfl
theorem leafDigestCols_val : leafDigestCols = [397, 398, 399, 400, 413, 414, 415, 416] := rfl

/-- The leaf sponge lookups (state16 bus, every row; row 0 is the read). -/
def leafSponge : List VmConstraint2 := leafPlan.map v3State16Lookup

/-- **The leaf↔fold bind**: row-0 `current[lane] − leafDigest[lane]` — the membership fold's
opened leaf IS the sponge digest of the FSI2 leaf block. -/
def leafBind : List VmConstraint2 :=
  (List.range 8).map fun lane =>
    .base (.boundary .first (esub (ev (MCUR + lane)) (ev (leafDigestCols.getD lane 0))))

/-- **The note tie**: row-0 `cCM − (addr0 + 2^16·addr1)` — the opened leaf's address IS the note
commitment's `raw_to_u16_le` image. -/
def noteTieBody : EmittedExpr :=
  esub (ev cCM) (eadd (ev cADDR0) (emul (ek 65536) (ev cADDR1)))

def noteTie : VmConstraint2 := .base (.boundary .first noteTieBody)

/-! ## §3 — piece 2: the nullifier derivation (the C4′/C8 shapes at the FSI2 spend). -/

/-- C6: `cCM = hash_fact(cVMOD,[cAMOD,cOWNER,cRAND])` — byte-for-byte the relation the Shield
mints (`ShieldedShieldDescriptor.lkCM`; `shield_mints_the_object_the_spend_opens` is the tie). -/
def lkCM : VmConstraint2 :=
  .lookup ⟨poseidon2narrow, chipLookupTupleNarrow (factIns [cVMOD, cAMOD, cOWNER, cRAND]) cCM⟩

/-- C4′: `cNUL = hash_fact(cCM, key[0..4])` — the nullifier derives from the OPENED note. -/
def lkNullifier : VmConstraint2 :=
  .lookup ⟨poseidon2narrow,
    chipLookupTupleNarrow (factIns [cCM, cKEY 0, cKEY 1, cKEY 2, cKEY 3]) cNUL⟩

/-- C8: `cOWNER = hash_fact(key[0..4])` — the double-spend closure (a fresh key commits a
DIFFERENT note; it cannot re-nullify this one). -/
def lkOwnerDerive : VmConstraint2 :=
  .lookup ⟨poseidon2narrow, chipLookupTupleNarrow (factIns [cKEY 0, cKEY 1, cKEY 2, cKEY 3]) cOWNER⟩

/-- The nullifier PI pin (PI 0 — the slot the membership core reserved and never pinned). -/
def nulPin : VmConstraint2 := .base (.piBinding .first cNUL piNUL)

/-! ## §4 — piece 3: the wide `u64` carrier (the sidecar shape, absorbed from the NOTE's cells). -/

/-- R2 — `limb − Σ 2^b·bit` (the sidecar's `limb_recompose`, over this layout). -/
def limbRecomposeHeadS (k i : Nat) : Head :=
  (List.range LIMB_BITS).foldl (fun h b => h.addLin (-(2 ^ b : ℤ)) (cBit k i b))
    (Head.lin 1 (cLimbS k i))

/-- R3 — `out − Σ (2^{16i} mod p)·limb_i`: `cVMOD`/`cAMOD` are DERIVED from the limbs the
carrier absorbs — the same cells `lkCM` hashes. No second free value. -/
def u64RecomposeHeadS (k out : Nat) : Head :=
  (List.range U64_LIMBS).foldl (fun h i => h.addLin (-(limbWeight i)) (cLimbS k i))
    (Head.lin 1 out)

/-- R1+R2 for one limb. -/
def limbGatesS (k i : Nat) : List VmConstraint2 :=
  ((List.range LIMB_BITS).map fun b => binGate (cBit k i b)) ++ [cgH (limbRecomposeHeadS k i)]

/-- The felt-width gate block: 128 boolean pins + 8 limb recompositions + the 2 reductions. -/
def carrierGates : List VmConstraint2 :=
  ((List.range 2).flatMap fun k => (List.range U64_LIMBS).flatMap fun i => limbGatesS k i)
    ++ [cgH (u64RecomposeHeadS 0 cVMOD), cgH (u64RecomposeHeadS 1 cAMOD)]

/-- The `node8` LEFT half at a domain separator — the sidecar's `wideLeft`, over this layout. -/
def spendWideLeft (domain : ℤ) : List EmittedExpr :=
  (.const domain) :: ((List.range U64_LIMBS).map fun i => EmittedExpr.var (cV i))
    ++ ((List.range 3).map fun i => EmittedExpr.var (cA i))

/-- The `node8` RIGHT half, shared by both domains — the sidecar's `wideRight`. -/
def spendWideRight : List EmittedExpr :=
  (.var (cA 3)) :: (.var cRAND) :: ((List.range BLIND_LANES).map fun i => EmittedExpr.var (cBL i))

/-- The 8 output columns of a carrier site based at `base`. -/
def spendWideOut (base : Nat) : List Nat := (List.range CHIP_OUT_LANES).map (base + ·)

/-- One domain-separated carrier site: the OUTPUTS are the already-PI-pinned `MWIDE` lanes. -/
def wideSiteS (domain : ℤ) (base : Nat) : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN (spendWideLeft domain ++ spendWideRight)
    (spendWideOut base)⟩

/-- The two carrier sites: `DOMAIN_A` fills `piWide[0..8]`, `DOMAIN_B` fills `piWide[8..16]` —
the routed join's `[BabyBear; 16]` comparison object, column-for-column the sidecar layout. -/
def carrierSites : List VmConstraint2 := [wideSiteS DOMAIN_A MWIDE, wideSiteS DOMAIN_B (MWIDE + 8)]

/-! ## §5 — the last-row bit repair (found while completing; see the module docblock). -/

/-- The membership core's bit gates re-lowered on the LAST row — the row whose node digest is
pinned to the committed root (`.gate` rides `when_transition()` and does not bind there). -/
def lastRowBitRepair : List VmConstraint2 :=
  [.base (.boundary .last (posBody MB0)), .base (.boundary .last (posBody MB1))]

/-! ## §6 — the completed descriptor. -/

/-- The completed constraint list: the LANDED membership core verbatim (its list is the prefix),
then the last-row repair, the leaf sponge + binds, the nullifier block, and the carrier block. -/
def completeConstraints : List VmConstraint2 :=
  shieldedSpendExactDesc.constraints
    ++ lastRowBitRepair
    ++ leafSponge ++ leafBind ++ [noteTie]
    ++ [lkCM, lkNullifier, lkOwnerDerive, nulPin]
    ++ carrierGates ++ carrierSites

/-- **`shieldedSpendCompleteDesc`** — the complete FSI2 spend descriptor: membership + leaf
sponge + nullifier + wide carrier, 25 PIs (`[nullifier] ++ committedRoot[8] ++ wideCarrier[16]`).
THE routable object for Pass C. -/
def shieldedSpendCompleteDesc : EffectVmDescriptor2 :=
  { name        := "dregg-shielded-spend-complete-fsi2::v1"
  , traceWidth  := C_WIDTH
  , piCount     := SPEND_PI_COUNT
  , tables      := [mainTableDef C_WIDTH, poseidon2State16ChipTableDef]
  , constraints := completeConstraints
  , hashSites   := []
  , ranges      := [] }

-- Structural pins (named, axiom-visible — not `#guard`s).
theorem complete_width : shieldedSpendCompleteDesc.traceWidth = 557 := rfl
theorem complete_pi_count : shieldedSpendCompleteDesc.piCount = 25 := rfl
theorem complete_name :
    shieldedSpendCompleteDesc.name = "dregg-shielded-spend-complete-fsi2::v1" := rfl
theorem leafSponge_length : leafSponge.length = 11 := rfl
theorem carrierGates_length : carrierGates.length = 138 := rfl
/-- 44 core + 2 last-row repair + 11 leaf sponge + 8 leaf binds + 1 note tie + 4 fact block
+ 138 carrier gates + 2 carrier sites. -/
theorem constraint_census : completeConstraints.length = 210 := rfl

/-- The membership core is the PREFIX of the completed list — nothing the landed rung proved is
weakened; every core constraint is a constraint of the completed descriptor. -/
theorem mem_of_membership_core {c : VmConstraint2}
    (hc : c ∈ shieldedSpendExactDesc.constraints) :
    c ∈ shieldedSpendCompleteDesc.constraints := by
  simp only [shieldedSpendCompleteDesc, completeConstraints, List.mem_append]
  tauto

/-! ## §7 — membership lemmas (the only place the emission order is relied on). -/

section Membership

theorem mem_leafSponge {s : State16Step} (hs : s ∈ leafPlan) :
    v3State16Lookup s ∈ shieldedSpendCompleteDesc.constraints := by
  have h1 : v3State16Lookup s ∈ leafSponge := List.mem_map.mpr ⟨s, hs, rfl⟩
  simp only [shieldedSpendCompleteDesc, completeConstraints, List.mem_append]
  tauto

theorem mem_nodeSponge {s : State16Step} (hs : s ∈ nodePlan) :
    v3State16Lookup s ∈ shieldedSpendCompleteDesc.constraints := by
  refine mem_of_membership_core ?_
  have h1 : v3State16Lookup s ∈ nodeSponge := List.mem_map.mpr ⟨s, hs, rfl⟩
  simp only [shieldedSpendExactDesc, List.mem_append]
  tauto

theorem mem_leafBind {lane : Nat} (h : lane < 8) :
    (VmConstraint2.base (.boundary .first
      (esub (ev (MCUR + lane)) (ev (leafDigestCols.getD lane 0)))))
      ∈ shieldedSpendCompleteDesc.constraints := by
  have h1 : (VmConstraint2.base (.boundary .first
      (esub (ev (MCUR + lane)) (ev (leafDigestCols.getD lane 0))))) ∈ leafBind :=
    List.mem_map.mpr ⟨lane, List.mem_range.mpr h, rfl⟩
  simp only [shieldedSpendCompleteDesc, completeConstraints, List.mem_append]
  tauto

theorem mem_noteTie : noteTie ∈ shieldedSpendCompleteDesc.constraints := by
  simp only [shieldedSpendCompleteDesc, completeConstraints, List.mem_append]
  simp [List.mem_cons]

theorem mem_lkCM : lkCM ∈ shieldedSpendCompleteDesc.constraints := by
  simp only [shieldedSpendCompleteDesc, completeConstraints, List.mem_append]
  simp [List.mem_cons]

theorem mem_lkNullifier : lkNullifier ∈ shieldedSpendCompleteDesc.constraints := by
  simp only [shieldedSpendCompleteDesc, completeConstraints, List.mem_append]
  simp [List.mem_cons]

theorem mem_lkOwnerDerive : lkOwnerDerive ∈ shieldedSpendCompleteDesc.constraints := by
  simp only [shieldedSpendCompleteDesc, completeConstraints, List.mem_append]
  simp [List.mem_cons]

theorem mem_nulPin : nulPin ∈ shieldedSpendCompleteDesc.constraints := by
  simp only [shieldedSpendCompleteDesc, completeConstraints, List.mem_append]
  simp [List.mem_cons]

theorem mem_carrierGate {x : VmConstraint2} (hx : x ∈ carrierGates) :
    x ∈ shieldedSpendCompleteDesc.constraints := by
  simp only [shieldedSpendCompleteDesc, completeConstraints, List.mem_append]
  tauto

theorem mem_binS {k i b : Nat} (hk : k < 2) (hi : i < U64_LIMBS) (hb : b < LIMB_BITS) :
    binGate (cBit k i b) ∈ shieldedSpendCompleteDesc.constraints := by
  refine mem_carrierGate ?_
  have h1 : binGate (cBit k i b) ∈ limbGatesS k i := by
    simp only [limbGatesS, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩)
  simp only [carrierGates, List.mem_append]
  exact Or.inl (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
    List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, h1⟩⟩)

theorem mem_limbRecomposeS {k i : Nat} (hk : k < 2) (hi : i < U64_LIMBS) :
    cgH (limbRecomposeHeadS k i) ∈ shieldedSpendCompleteDesc.constraints := by
  refine mem_carrierGate ?_
  have h1 : cgH (limbRecomposeHeadS k i) ∈ limbGatesS k i := by
    simp only [limbGatesS, List.mem_append]
    exact Or.inr (by simp)
  simp only [carrierGates, List.mem_append]
  exact Or.inl (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
    List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, h1⟩⟩)

theorem mem_vmodRecompose :
    cgH (u64RecomposeHeadS 0 cVMOD) ∈ shieldedSpendCompleteDesc.constraints := by
  refine mem_carrierGate ?_
  simp only [carrierGates, List.mem_append]
  simp

theorem mem_amodRecompose :
    cgH (u64RecomposeHeadS 1 cAMOD) ∈ shieldedSpendCompleteDesc.constraints := by
  refine mem_carrierGate ?_
  simp only [carrierGates, List.mem_append]
  simp

theorem mem_wideSiteA : wideSiteS DOMAIN_A MWIDE ∈ shieldedSpendCompleteDesc.constraints := by
  simp only [shieldedSpendCompleteDesc, completeConstraints, List.mem_append]
  simp [carrierSites]

theorem mem_wideSiteB :
    wideSiteS DOMAIN_B (MWIDE + 8) ∈ shieldedSpendCompleteDesc.constraints := by
  simp only [shieldedSpendCompleteDesc, completeConstraints, List.mem_append]
  simp [carrierSites]

theorem mem_carrierPin {i : Nat} (hi : i < 16) :
    (VmConstraint2.base (.piBinding .first (MWIDE + i) (PI_WIDE_BASE + i)))
      ∈ shieldedSpendCompleteDesc.constraints := by
  refine mem_of_membership_core ?_
  have h1 : (VmConstraint2.base (.piBinding .first (MWIDE + i) (PI_WIDE_BASE + i)))
      ∈ carrierPins := List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  simp only [shieldedSpendExactDesc, List.mem_append]
  tauto

theorem mem_rootPin {lane : Nat} (h : lane < 8) :
    (VmConstraint2.base (.piBinding .last (nodeDigestCols.getD lane 0)
      (PI_COMMITTED_BASE + lane))) ∈ shieldedSpendCompleteDesc.constraints := by
  refine mem_of_membership_core ?_
  have h1 : (VmConstraint2.base (.piBinding .last (nodeDigestCols.getD lane 0)
      (PI_COMMITTED_BASE + lane))) ∈ rootPins := List.mem_map.mpr ⟨lane, List.mem_range.mpr h, rfl⟩
  simp only [shieldedSpendExactDesc, List.mem_append]
  tauto

end Membership

/-! ## §8 — extraction levers (the `Satisfied2` readers every keystone runs through). -/

section Extraction
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The row assignment at index `i`. -/
def rowOf (t : VmTrace) (i : Nat) : Assignment := (envAt t i).loc

private theorem rows_pos_of_ne (hne : t.rows ≠ []) : 0 < t.rows.length := by
  cases hr : t.rows with
  | nil => exact absurd hr hne
  | cons _ _ => simp

private theorem modeq_of_sub {x y : ℤ} (h : x + -1 * y ≡ 0 [ZMOD 2013265921]) :
    x ≡ y [ZMOD 2013265921] := by
  have hd := Int.modEq_iff_dvd.mp h
  have he : (0 : ℤ) - (x + -1 * y) = y - x := by ring
  rw [he] at hd
  exact Int.modEq_iff_dvd.mpr hd

/-- A first-row PI binding forces its column ≡ its PI. -/
theorem cPinFirst (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) {c k : Nat}
    (hm : (VmConstraint2.base (.piBinding .first c k)) ∈ shieldedSpendCompleteDesc.constraints) :
    rowOf t 0 c ≡ t.pub k [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 (rows_pos_of_ne hne) _ hm
  simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, rowOf, envAt] using h rfl

/-- A first-row boundary forces its body ≡ 0 on row 0. -/
theorem cBoundaryFirst (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) {b : EmittedExpr}
    (hm : (VmConstraint2.base (.boundary .first b)) ∈ shieldedSpendCompleteDesc.constraints) :
    b.eval (rowOf t 0) ≡ 0 [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 (rows_pos_of_ne hne) _ hm
  simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, rowOf, envAt] using h rfl

/-- A lookup holds on every row of a satisfying trace. -/
theorem cLookup (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) {l : Lookup}
    (hm : VmConstraint2.lookup l ∈ shieldedSpendCompleteDesc.constraints) :
    l.holdsAt t.tf (envAt t i) := hsat.rowConstraints i hi _ hm

/-- A `Head` gate forces its head ≡ 0 on a transition row. -/
theorem cGateH (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) {h : Head}
    (hm : cgH h ∈ shieldedSpendCompleteDesc.constraints) :
    evalH h (rowOf t i) ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hm
  have hlf : (i + 1 == t.rows.length) = false := by
    have hne : i + 1 ≠ t.rows.length := by omega
    simpa using hne
  have hb : (headToExpr h).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
    simpa only [cgH, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc
  rwa [headToExpr_eval] at hb

/-- The booleanity form of `cGateH`. -/
theorem cBinS (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) {c : Nat}
    (hm : binGate c ∈ shieldedSpendCompleteDesc.constraints) (hcan : Canon (rowOf t i c)) :
    rowOf t i c = 0 ∨ rowOf t i c = 1 := by
  have hrc := hsat.rowConstraints i (by omega) _ hm
  have hlf : (i + 1 == t.rows.length) = false := by
    have hne : i + 1 ≠ t.rows.length := by omega
    simpa using hne
  have hb : (gBin c).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
    simpa only [binGate, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc
  exact bin_of_gate hb hcan

end Extraction

/-! ## §9 — keystone 0 (continuity): the #15 root pin, on THE ROUTED OBJECT. -/

/-- **`complete_root_is_pinned8`** — `root_is_pinned8` re-derived over the completed descriptor:
a satisfying trace's LAST-row node digest ≡ the committed-root PI on all eight lanes. The #15 pin
survives completion intact; Pass C routes THIS statement. -/
theorem complete_root_is_pinned8 (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t) (lane : Fin 8) :
    t.rows.getD (t.rows.length - 1) zeroAsg (nodeDigestCols.getD lane.val 0)
      ≡ t.pub (PI_COMMITTED_BASE + lane.val) [ZMOD 2013265921] := by
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons _ _ => simp
  have hlt : t.rows.length - 1 < t.rows.length := by omega
  have h := hsat.rowConstraints (t.rows.length - 1) hlt _ (mem_rootPin lane.isLt)
  have hlastb : ((t.rows.length - 1) + 1 == t.rows.length) = true := by
    have : t.rows.length - 1 + 1 = t.rows.length := by omega
    simpa using this
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt] at h
  exact h hlastb

/-! ## §10 — keystone 1: the leaf the fold walks IS the note commitment. -/

section Leaf
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- One sponge step genuinely executed by `perm16` on assignment `a`. -/
def SpongeStepHolds (perm16 : List ℤ → List ℤ) (a : Assignment) (step : State16Step) : Prop :=
  step.outputCols.map a = perm16 (step.input.map (·.eval a))

/-- **The leaf sponge EXECUTES**: under a sound state16 table, every one of the 11 leaf-plan
permutation sites is a genuine complete-state transition on every row — in particular row 0's leaf
digest columns carry the genuine `hash_many_8` schedule of the FSI2 leaf preimage cells. -/
theorem leaf_sponge_executes (perm16 : List ℤ → List ℤ)
    (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hchip : ChipTableSoundState16 perm16 (t.tf poseidon2state16))
    (i : Nat) (hi : i < t.rows.length) :
    ∀ step ∈ leafPlan, SpongeStepHolds perm16 (rowOf t i) step := by
  intro step hstep
  have hc := cLookup hsat i hi (mem_leafSponge hstep)
  simp only [Lookup.holdsAt] at hc
  exact chip_lookup_sound_state16 perm16 (t.tf poseidon2state16) hchip
    (rowOf t i) step.input step.outputCols
    (by
      have hall : leafPlan.all (fun s => s.input.length == 16) = true := by decide
      have hs := List.all_eq_true.mp hall step hstep
      have h16 : step.input.length = 16 := by simpa using of_decide_eq_true hs
      exact h16)
    hc

/-- **The node sponge EXECUTES** — the same statement for the membership core's 10 node sites
(the fold rows genuinely permute; the landed rung asserted this only structurally). -/
theorem node_sponge_executes (perm16 : List ℤ → List ℤ)
    (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hchip : ChipTableSoundState16 perm16 (t.tf poseidon2state16))
    (i : Nat) (hi : i < t.rows.length) :
    ∀ step ∈ nodePlan, SpongeStepHolds perm16 (rowOf t i) step := by
  intro step hstep
  have hc := cLookup hsat i hi (mem_nodeSponge hstep)
  simp only [Lookup.holdsAt] at hc
  exact chip_lookup_sound_state16 perm16 (t.tf poseidon2state16) hchip
    (rowOf t i) step.input step.outputCols
    (by
      have hall : nodePlan.all (fun s => s.input.length == 16) = true := by decide
      have hs := List.all_eq_true.mp hall step hstep
      have h16 : step.input.length = 16 := by simpa using of_decide_eq_true hs
      exact h16)
    hc

/-- **The fold's opened leaf IS the leaf-sponge digest**: row-0 `current[lane]` ≡ the leaf digest
column, all eight lanes. -/
theorem leaf_bound_to_current8 (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (lane : Fin 8) :
    rowOf t 0 (MCUR + lane.val) ≡ rowOf t 0 (leafDigestCols.getD lane.val 0) [ZMOD 2013265921] := by
  have hb := cBoundaryFirst hsat hne (mem_leafBind lane.isLt)
  simp only [esub, eadd, emul, eneg, ev, ek, EmittedExpr.eval] at hb
  exact modeq_of_sub hb

/-- **The opened leaf's address IS the note commitment**: row-0 `cCM ≡ addr0 + 2^16·addr1`. -/
theorem note_tied_to_leaf_address
    (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t) (hne : t.rows ≠ []) :
    rowOf t 0 cCM ≡ rowOf t 0 cADDR0 + 65536 * rowOf t 0 cADDR1 [ZMOD 2013265921] := by
  have hb := cBoundaryFirst hsat hne mem_noteTie
  simp only [noteTieBody, esub, eadd, emul, eneg, ev, ek, EmittedExpr.eval] at hb
  exact modeq_of_sub hb

/-- **The note commitment is genuinely opened** (under a sound narrow-served chip table):
row 0 carries `cCM = hash_fact(cVMOD,[cAMOD,cOWNER,cRAND])` — the SAME relation the Shield mints. -/
theorem cm_opens_row0 (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2)) :
    rowOf t 0 cCM
      = hash [rowOf t 0 cVMOD, rowOf t 0 cAMOD, rowOf t 0 cOWNER, rowOf t 0 cRAND,
              0, NS_FACT_MARK, 1] := by
  have hk := cLookup hsat 0 (rows_pos_of_ne hne) mem_lkCM
  simp only [Lookup.holdsAt] at hk
  rw [hwire] at hk
  have hlen : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted
      (factIns [cVMOD, cAMOD, cOWNER, cRAND]).length := by chip_arity_admitted
  have e := chip_lookup_narrow_sound_of_wide_table hash (t.tf TableId.poseidon2) hChip
    ((envAt t 0).loc) _ cCM hlen hk
  rw [factIns_eval_4] at e
  exact e

end Leaf

/-! ## §11 — keystone 2: the nullifier derives from the opened note. -/

section Nullifier
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The published nullifier is the row-0 `cNUL` cell (PI 0 pin — the slot the membership core
reserved; pinned HERE). -/
theorem nullifier_published (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) : rowOf t 0 cNUL ≡ t.pub piNUL [ZMOD 2013265921] :=
  cPinFirst hsat hne mem_nulPin

/-- **The nullifier derivation** (under a sound narrow-served chip table): row 0 carries
`cNUL = hash_fact(cCM, key[0..4])` — the nullifier of the note the leaf opens, not a free label. -/
theorem nullifier_derived_row0 (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2)) :
    rowOf t 0 cNUL
      = hash [rowOf t 0 cCM, rowOf t 0 (cKEY 0), rowOf t 0 (cKEY 1), rowOf t 0 (cKEY 2),
              rowOf t 0 (cKEY 3), NS_FACT_MARK, 1] := by
  have hk := cLookup hsat 0 (rows_pos_of_ne hne) mem_lkNullifier
  simp only [Lookup.holdsAt] at hk
  rw [hwire] at hk
  have hlen : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted
      (factIns [cCM, cKEY 0, cKEY 1, cKEY 2, cKEY 3]).length := by chip_arity_admitted
  have e := chip_lookup_narrow_sound_of_wide_table hash (t.tf TableId.poseidon2) hChip
    ((envAt t 0).loc) _ cNUL hlen hk
  rw [factIns_eval_5] at e
  exact e

/-- **The C8 owner derivation** — the double-spend closure: the owner the note commits IS a
function of the spending key, so a fresh key commits a DIFFERENT note. -/
theorem owner_derived_row0 (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2)) :
    rowOf t 0 cOWNER
      = hash [rowOf t 0 (cKEY 0), rowOf t 0 (cKEY 1), rowOf t 0 (cKEY 2), rowOf t 0 (cKEY 3),
              0, NS_FACT_MARK, 1] := by
  have hk := cLookup hsat 0 (rows_pos_of_ne hne) mem_lkOwnerDerive
  simp only [Lookup.holdsAt] at hk
  rw [hwire] at hk
  have hlen : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted
      (factIns [cKEY 0, cKEY 1, cKEY 2, cKEY 3]).length := by chip_arity_admitted
  have e := chip_lookup_narrow_sound_of_wide_table hash (t.tf TableId.poseidon2) hChip
    ((envAt t 0).loc) _ cOWNER hlen hk
  rw [factIns_eval_4] at e
  exact e

end Nullifier

/-! ## §12 — keystone 3: the 16 `piWide` lanes are the real `cap_node8` image. -/

section Carrier
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
variable {permW : List ℤ → List ℤ}

/-- The 16 chip inputs a spend carrier site absorbs, as values. -/
def spendWideIns (a : Assignment) (domain : ℤ) : List ℤ :=
  [domain, a (cV 0), a (cV 1), a (cV 2), a (cV 3), a (cA 0), a (cA 1), a (cA 2),
   a (cA 3), a cRAND, a (cBL 0), a (cBL 1), a (cBL 2), a (cBL 3), a (cBL 4), a (cBL 5)]

theorem spendWideIns_eval (a : Assignment) (domain : ℤ) :
    (spendWideLeft domain ++ spendWideRight).map (·.eval a) = spendWideIns a domain := rfl

/-- The spend's limb opening as the abstract 8-limb vector (`carrierIns` convention). -/
def spendLimbs (a : Assignment) (i : Nat) : ℤ := if i < 4 then a (cV i) else a (cA (i - 4))

/-- The spend's blind vector. -/
def spendBlinds (a : Assignment) (i : Nat) : ℤ := a (cBL i)

/-- **The absorb IS the sidecar's `carrierIns` shape** — the spend-side carrier absorbs the exact
object same-opening's `WideCarrierCR` floor separates (`alias_separated_by_the_wide_carrier`).
This is the join-compatibility fact: same order, same domain slot, same randomness slot. -/
theorem spendWideIns_is_carrierIns (a : Assignment) (domain : ℤ) :
    spendWideIns a domain = carrierIns domain (spendLimbs a) (a cRAND) (spendBlinds a) := rfl

/-- Reading lane `j` off a carrier's output block. -/
theorem spendWideOut_getD (a : Assignment) (base j : Nat) (hj : j < 8) :
    ((spendWideOut base).map a).getD j 0 = a (base + j) := by
  interval_cases j <;> rfl

/-- The generic per-site forcing: all eight output lanes are the genuine wide-chip image. -/
theorem carrier_lanes_forced_at (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permW (t.tf TableId.poseidon2)) (i : Nat) (hi : i < t.rows.length)
    {domain : ℤ} {base : Nat}
    (hm : wideSiteS domain base ∈ shieldedSpendCompleteDesc.constraints) :
    (spendWideOut base).map (rowOf t i) = permW (spendWideIns (rowOf t i) domain) := by
  have hh := cLookup hsat i hi (l := ⟨TableId.poseidon2,
    chipLookupTupleN (spendWideLeft domain ++ spendWideRight) (spendWideOut base)⟩) hm
  simp only [Lookup.holdsAt] at hh
  have := chip_lookup_sound_N permW (t.tf TableId.poseidon2) hSound (rowOf t i)
    (spendWideLeft domain ++ spendWideRight) (spendWideOut base)
    (of_decide_eq_true (Eq.refl true)) hh
  rwa [spendWideIns_eval] at this

/-- The `DOMAIN_A` carrier lanes (`MWIDE..MWIDE+7`) are the genuine squeeze. -/
theorem carrierA_lanes_forced (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permW (t.tf TableId.poseidon2)) (i : Nat) (hi : i < t.rows.length) :
    (spendWideOut MWIDE).map (rowOf t i) = permW (spendWideIns (rowOf t i) DOMAIN_A) :=
  carrier_lanes_forced_at hsat hSound i hi mem_wideSiteA

/-- The `DOMAIN_B` carrier lanes (`MWIDE+8..MWIDE+15`). -/
theorem carrierB_lanes_forced (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permW (t.tf TableId.poseidon2)) (i : Nat) (hi : i < t.rows.length) :
    (spendWideOut (MWIDE + 8)).map (rowOf t i) = permW (spendWideIns (rowOf t i) DOMAIN_B) :=
  carrier_lanes_forced_at hsat hSound i hi mem_wideSiteB

/-- The published carrier lane ≡ the in-trace `MWIDE` cell (pin extraction; lanes 0..16). -/
theorem carrier_published (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) (lane : Fin 16) :
    rowOf t 0 (MWIDE + lane.val) ≡ t.pub (PI_WIDE_BASE + lane.val) [ZMOD 2013265921] :=
  cPinFirst hsat hne (mem_carrierPin lane.isLt)

/-- **THE CARRIER KEYSTONE (`published_carrier_is_the_cap_node8_image`).** Row 0's published
`piWide` lane `j < 8` ≡ lane `j` of `permW (carrierIns DOMAIN_A (spendLimbs …) rand blinds)` —
the REAL `cap_node8` image over the note's own limb opening, THE object same-opening's routed join
compares and its `WideCarrierCR` floor separates. NOT `value mod p` relabelled: the lane is a
permutation image of the full limb decomposition (`spendWideIns_is_carrierIns`). -/
theorem published_carrier_is_the_cap_node8_image
    (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permW (t.tf TableId.poseidon2)) (hne : t.rows ≠ [])
    {j : Nat} (hj : j < 8) :
    t.pub (PI_WIDE_BASE + j)
      ≡ (permW (carrierIns DOMAIN_A (spendLimbs (rowOf t 0)) (rowOf t 0 cRAND)
          (spendBlinds (rowOf t 0)))).getD j 0 [ZMOD 2013265921] := by
  have hlanes := carrierA_lanes_forced hsat hSound 0 (rows_pos_of_ne hne)
  have hpin := carrier_published hsat hne ⟨j, by omega⟩
  have hval : rowOf t 0 (MWIDE + j)
      = (permW (spendWideIns (rowOf t 0) DOMAIN_A)).getD j 0 := by
    rw [← spendWideOut_getD (rowOf t 0) MWIDE j hj, hlanes]
  rw [hval, spendWideIns_is_carrierIns] at hpin
  exact hpin.symm

/-- The second half: lanes `8..16` land on the `DOMAIN_B` image. Sixteen lanes, two domains —
the full `[BabyBear; 16]` object `verify_same_opening` compares. -/
theorem published_carrierB_is_the_cap_node8_image
    (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permW (t.tf TableId.poseidon2)) (hne : t.rows ≠ [])
    {lane : Nat} (hlo : 8 ≤ lane) (hhi : lane < 16) :
    t.pub (PI_WIDE_BASE + lane)
      ≡ (permW (carrierIns DOMAIN_B (spendLimbs (rowOf t 0)) (rowOf t 0 cRAND)
          (spendBlinds (rowOf t 0)))).getD (lane - 8) 0 [ZMOD 2013265921] := by
  have hlanes := carrierB_lanes_forced hsat hSound 0 (rows_pos_of_ne hne)
  have hpin := carrier_published hsat hne ⟨lane, by omega⟩
  have hj : lane - 8 < 8 := by omega
  have hcol : MWIDE + lane = (MWIDE + 8) + (lane - 8) := by omega
  have hval : rowOf t 0 ((MWIDE + 8) + (lane - 8))
      = (permW (spendWideIns (rowOf t 0) DOMAIN_B)).getD (lane - 8) 0 := by
    rw [← spendWideOut_getD (rowOf t 0) (MWIDE + 8) (lane - 8) hj, hlanes]
  rw [hcol, hval, spendWideIns_is_carrierIns] at hpin
  exact hpin.symm

/-- The `u64` a kind's four limb cells denote. -/
def u64OfS (a : Assignment) (k : Nat) : ℤ :=
  ((List.range U64_LIMBS).map fun i => (2 ^ (LIMB_BITS * i) : ℤ) * a (cLimbS k i)).sum

private theorem limbRecomposeHeadS_eval (a : Assignment) (k i : Nat) :
    evalH (limbRecomposeHeadS k i) a
      = a (cLimbS k i) - bitSum a (fun b => cBit k i b) LIMB_BITS := by
  simp only [limbRecomposeHeadS, evalH_foldl_addLinG, evalH_lin, bitSum]
  have : ∀ xs : List Nat,
      (xs.map fun b => -(2 ^ b : ℤ) * a (cBit k i b)).sum
        = -(xs.map fun b => (2 ^ b : ℤ) * a (cBit k i b)).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [this]
  ring

private theorem u64RecomposeHeadS_eval (a : Assignment) (k out : Nat) :
    evalH (u64RecomposeHeadS k out) a
      = a out - ((List.range U64_LIMBS).map fun i => limbWeight i * a (cLimbS k i)).sum := by
  simp only [u64RecomposeHeadS, evalH_foldl_addLinG, evalH_lin]
  have : ∀ xs : List Nat,
      (xs.map fun i => -(limbWeight i) * a (cLimbS k i)).sum
        = -(xs.map fun i => limbWeight i * a (cLimbS k i)).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [this]
  ring

/-- **The limbs are FORCED canonical 16-bit cells** (transition rows — the felt-width repair): the
limb cell IS the weighted sum of its own boolean bits, hence in `[0, 2^16)`. -/
theorem spend_limb_canonical (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (i₀ : Nat) (hi₀ : i₀ + 1 < t.rows.length) {k i : Nat} (hk : k < 2) (hi : i < U64_LIMBS)
    (hcan : Canon (rowOf t i₀ (cLimbS k i)))
    (hcanb : ∀ b, b < LIMB_BITS → Canon (rowOf t i₀ (cBit k i b))) :
    rowOf t i₀ (cLimbS k i) = bitSum (rowOf t i₀) (fun b => cBit k i b) LIMB_BITS
      ∧ 0 ≤ rowOf t i₀ (cLimbS k i) ∧ rowOf t i₀ (cLimbS k i) < 65536 := by
  have hbits : ∀ b, b < LIMB_BITS → rowOf t i₀ (cBit k i b) = 0 ∨ rowOf t i₀ (cBit k i b) = 1 :=
    fun b hb => cBinS hsat i₀ hi₀ (mem_binS hk hi hb) (hcanb b hb)
  obtain ⟨hs0, hs1⟩ := bitSum_bounds (rowOf t i₀) (fun b => cBit k i b) LIMB_BITS hbits
  have hgate := cGateH hsat i₀ hi₀ (mem_limbRecomposeS hk hi)
  rw [limbRecomposeHeadS_eval] at hgate
  have hdvd : (2013265921 : ℤ) ∣
      rowOf t i₀ (cLimbS k i) - bitSum (rowOf t i₀) (fun b => cBit k i b) LIMB_BITS :=
    Int.modEq_zero_iff_dvd.mp hgate
  obtain ⟨hc0, hc1⟩ := hcan
  have hlt : (2 : ℤ) ^ LIMB_BITS = 65536 := by norm_num [LIMB_BITS]
  rw [hlt] at hs1
  obtain ⟨c, hc⟩ := hdvd
  have heq : rowOf t i₀ (cLimbS k i)
      = bitSum (rowOf t i₀) (fun b => cBit k i b) LIMB_BITS := by omega
  exact ⟨heq, by omega, by omega⟩

/-- **`cVMOD` is the reduction of the full `u64` the carrier absorbs** — the value `lkCM` hashes
into the note commitment is not a second free value. -/
theorem vmod_reduced (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (i₀ : Nat) (hi₀ : i₀ + 1 < t.rows.length) :
    rowOf t i₀ cVMOD ≡ u64OfS (rowOf t i₀) 0 [ZMOD 2013265921] := by
  have hgate := cGateH hsat i₀ hi₀ mem_vmodRecompose
  rw [u64RecomposeHeadS_eval] at hgate
  have hs : ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimbS 0 i)).sum
      ≡ u64OfS (rowOf t i₀) 0 [ZMOD 2013265921] := by
    refine sum_modEq _ _ _ fun i _ => ?_
    exact Int.ModEq.mul_right _ (limbWeight_modEq i)
  have h2 : rowOf t i₀ cVMOD
      ≡ ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimbS 0 i)).sum
      [ZMOD 2013265921] := by
    simpa using Int.ModEq.add_right
      (((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimbS 0 i)).sum) hgate
  exact h2.trans hs

/-- The asset half. -/
theorem amod_reduced (hsat : Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t)
    (i₀ : Nat) (hi₀ : i₀ + 1 < t.rows.length) :
    rowOf t i₀ cAMOD ≡ u64OfS (rowOf t i₀) 1 [ZMOD 2013265921] := by
  have hgate := cGateH hsat i₀ hi₀ mem_amodRecompose
  rw [u64RecomposeHeadS_eval] at hgate
  have hs : ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimbS 1 i)).sum
      ≡ u64OfS (rowOf t i₀) 1 [ZMOD 2013265921] := by
    refine sum_modEq _ _ _ fun i _ => ?_
    exact Int.ModEq.mul_right _ (limbWeight_modEq i)
  have h2 : rowOf t i₀ cAMOD
      ≡ ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimbS 1 i)).sum
      [ZMOD 2013265921] := by
    simpa using Int.ModEq.add_right
      (((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimbS 1 i)).sum) hgate
  exact h2.trans hs

/-- The two domains are genuinely separated (the two halves cannot be one image relabelled). -/
theorem carrier_domains_separated : DOMAIN_A ≠ DOMAIN_B := by decide

end Carrier

/-! ## §13 — THE TEETH: forged nullifier / decoupled carrier / wrong leaf / foreign note, each
REFUSED, each mutation asserted present before the verdict. -/

section Teeth

/-- General: a trace whose published nullifier decouples from the derived `cNUL` cell is UNSAT. -/
theorem foreign_nullifier_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hforge : ¬ (rowOf t 0 cNUL ≡ t.pub piNUL [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t :=
  fun hsat => hforge (nullifier_published hsat hne)

/-- General: a published carrier lane decoupled from the in-trace `cap_node8` output is UNSAT. -/
theorem decoupled_carrier_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ []) (lane : Fin 16)
    (hforge : ¬ (rowOf t 0 (MWIDE + lane.val) ≡ t.pub (PI_WIDE_BASE + lane.val)
      [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t :=
  fun hsat => hforge (carrier_published hsat hne lane)

/-- General: a row-0 `current` lane decoupled from the leaf-sponge digest is UNSAT — the fold
cannot walk a leaf that is not the in-trace FSI2 leaf block's digest. -/
theorem wrong_leaf_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ []) (lane : Fin 8)
    (hforge : ¬ (rowOf t 0 (MCUR + lane.val) ≡ rowOf t 0 (leafDigestCols.getD lane.val 0)
      [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t :=
  fun hsat => hforge (leaf_bound_to_current8 hsat hne lane)

/-- General: a `cCM` decoupled from the opened leaf's address is UNSAT — a spend cannot claim a
note commitment its opened leaf does not carry (the forged-nullifier-for-an-unopened-note gate). -/
theorem foreign_note_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hforge : ¬ (rowOf t 0 cCM ≡ rowOf t 0 cADDR0 + 65536 * rowOf t 0 cADDR1
      [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedSpendCompleteDesc minit mfin maddrs t :=
  fun hsat => hforge (note_tied_to_leaf_address hsat hne)

/-! Concrete refused instances — the mutation exhibited, then the refusal. Each forged object
differs from the honest zero witness (§14) in EXACTLY the mutated cell. -/

/-- Forged public inputs: the published nullifier is `1` against an all-zero trace. -/
def forgedNulPub : Assignment := fun k => if k = piNUL then 1 else 0

/-- The mutation is PRESENT: the forged public nullifier differs from the honest one. -/
theorem forged_nul_mutation_present : forgedNulPub piNUL = 1 ∧ zeroAsg piNUL = 0 := by
  constructor <;> rfl

/-- Forged public inputs: wide carrier lane 0 is `1` against an all-zero trace. -/
def forgedCarrierPub : Assignment := fun k => if k = PI_WIDE_BASE then 1 else 0

theorem forged_carrier_mutation_present :
    forgedCarrierPub PI_WIDE_BASE = 1 ∧ zeroAsg PI_WIDE_BASE = 0 := by
  constructor <;> rfl

/-- Forged row: `current[0] = 1` while the leaf sponge digests to `0` lanes. -/
def wrongLeafRow : Assignment := fun c => if c = MCUR then 1 else 0

theorem wrong_leaf_mutation_present :
    wrongLeafRow MCUR = 1 ∧ wrongLeafRow (leafDigestCols.getD 0 0) = 0 := by
  constructor <;> rfl

/-- Forged row: `cCM = 1` while the opened leaf's address limbs are zero. -/
def foreignNoteRow : Assignment := fun c => if c = cCM then 1 else 0

theorem foreign_note_mutation_present :
    foreignNoteRow cCM = 1 ∧ foreignNoteRow cADDR0 = 0 ∧ foreignNoteRow cADDR1 = 0 := by
  refine ⟨rfl, rfl, rfl⟩

private theorem one_ne_zero_mod_p : ¬ ((0 : ℤ) ≡ 1 [ZMOD 2013265921]) := by decide

private theorem one_ne_zero_mod_p' : ¬ ((1 : ℤ) ≡ 0 [ZMOD 2013265921]) := by decide

/-- **REFUSED: the forged nullifier.** -/
theorem forged_nullifier_refused (tf : TraceFamily) :
    ¬ Satisfied2 hzero shieldedSpendCompleteDesc (fun _ => 0) (fun _ => (0, 0)) []
      { rows := [zeroAsg], pub := forgedNulPub, tf := tf } :=
  foreign_nullifier_unsat hzero _ _ [] _ (by simp)
    (by
      show ¬ ((0 : ℤ) ≡ forgedNulPub piNUL [ZMOD 2013265921])
      simpa [forgedNulPub] using one_ne_zero_mod_p)

/-- **REFUSED: the decoupled carrier.** -/
theorem decoupled_carrier_refused (tf : TraceFamily) :
    ¬ Satisfied2 hzero shieldedSpendCompleteDesc (fun _ => 0) (fun _ => (0, 0)) []
      { rows := [zeroAsg], pub := forgedCarrierPub, tf := tf } :=
  decoupled_carrier_unsat hzero _ _ [] _ (by simp) ⟨0, by omega⟩
    (by
      show ¬ ((0 : ℤ) ≡ forgedCarrierPub (PI_WIDE_BASE + 0) [ZMOD 2013265921])
      simpa [forgedCarrierPub] using one_ne_zero_mod_p)

/-- **REFUSED: the wrong leaf.** -/
theorem wrong_leaf_refused (tf : TraceFamily) :
    ¬ Satisfied2 hzero shieldedSpendCompleteDesc (fun _ => 0) (fun _ => (0, 0)) []
      { rows := [wrongLeafRow], pub := zeroAsg, tf := tf } :=
  wrong_leaf_unsat hzero _ _ [] _ (by simp) ⟨0, by omega⟩
    (by
      show ¬ (wrongLeafRow (MCUR + 0) ≡ wrongLeafRow (leafDigestCols.getD 0 0)
        [ZMOD 2013265921])
      rw [show wrongLeafRow (MCUR + 0) = 1 from if_pos rfl,
        show wrongLeafRow (leafDigestCols.getD 0 0) = 0 from if_neg (by decide)]
      exact one_ne_zero_mod_p')

/-- **REFUSED: the foreign note** — a claimed commitment the opened leaf does not carry. -/
theorem foreign_note_refused (tf : TraceFamily) :
    ¬ Satisfied2 hzero shieldedSpendCompleteDesc (fun _ => 0) (fun _ => (0, 0)) []
      { rows := [foreignNoteRow], pub := zeroAsg, tf := tf } :=
  foreign_note_unsat hzero _ _ [] _ (by simp)
    (by
      show ¬ (foreignNoteRow cCM ≡ foreignNoteRow cADDR0 + 65536 * foreignNoteRow cADDR1
        [ZMOD 2013265921])
      rw [show foreignNoteRow cCM = 1 from if_pos rfl,
        show foreignNoteRow cADDR0 = 0 from if_neg (by decide),
        show foreignNoteRow cADDR1 = 0 from if_neg (by decide)]
      simpa using one_ne_zero_mod_p')

end Teeth

/-! ## §14 — SATISFIABILITY: an explicit witness with GENUINE chip tables (`pz16`/`pz8`/`hzero`
rows — never copied claims), so the teeth are not vacuously true of an empty relation. One-row
trace: the algebraic gates ride `when_transition()` and are vacuous there (the landed
`ShieldedSpendDescriptor` precedent, named in the docblock); every lookup, boundary and pin BINDS. -/

section Witness

/-- The zero permutation (the abstract-permutation witness carrier, `hzero`'s 16-lane twin). -/
def pz16 : List ℤ → List ℤ := fun _ => List.replicate 16 0

/-- The zero 8-lane squeeze (the wide-chip witness carrier). -/
def pz8 : List ℤ → List ℤ := fun _ => List.replicate 8 0

/-- All 21 state16 steps the completed descriptor looks up. -/
def czSteps : List State16Step := nodePlan ++ leafPlan

/-- The state16 table of the zero witness: the evaluated tuples themselves — each row is a
GENUINE `chipRowState16 pz16` row (`czState16_sound`). -/
def czState16 : Table :=
  czSteps.map fun step =>
    (chipLookupTupleState16 step.input step.outputCols step.width).map (·.eval zeroAsg)

private theorem map_zeroAsg_eq_replicate (l : List Nat) :
    l.map (fun x => zeroAsg x) = List.replicate l.length 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.replicate_succ, ih, zeroAsg]

theorem czState16_sound : ChipTableSoundState16 pz16 czState16 := by
  intro r hr
  simp only [czState16, List.mem_map] at hr
  obtain ⟨step, hstep, rfl⟩ := hr
  refine ⟨step.input.map (·.eval zeroAsg), by simpa using (step.width.trans rfl : step.input.length = CHIP_STATE_LANES), rfl, ?_⟩
  have houtlen : step.outputCols.length = 16 := by
    have hall : czSteps.all (fun s => s.outputCols.length == 16) = true := by decide
    have hs := List.all_eq_true.mp hall step hstep
    simpa using of_decide_eq_true hs
  simp only [chipRowState16, chipRowN, chipLookupTupleState16, chipLookupTupleN,
    Dregg2.Circuit.DescriptorIR2.map_eval_padToE, List.map_cons, List.map_append, List.map_map,
    Function.comp_def, EmittedExpr.eval, List.length_map, pz16]
  congr 1
  rw [map_zeroAsg_eq_replicate, houtlen]

/-- The wide chip table of the zero witness: the shared fact row (`zChipRow` — arity 7, genuine
`hzero`/`pz8`) plus the two carrier rows (arity 16, genuine `pz8`). -/
def czWideRowA : List ℤ :=
  (16 : ℤ) :: [DOMAIN_A, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ++ List.replicate 8 0

def czWideRowB : List ℤ :=
  (16 : ℤ) :: [DOMAIN_B, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ++ List.replicate 8 0

def czWide : Table := [zChipRow, czWideRowA, czWideRowB]

/-- Every row of the zero witness's wide table is a genuine `chipRowN pz8` row. -/
theorem czWide_soundN : ChipTableSoundN pz8 czWide := by
  intro r hr
  simp only [czWide, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨[0, 0, 0, 0, 0, 64207, 1], of_decide_eq_true (Eq.refl true), by decide⟩
  · exact ⟨[DOMAIN_A, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      of_decide_eq_true (Eq.refl true), by decide⟩
  · exact ⟨[DOMAIN_B, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      of_decide_eq_true (Eq.refl true), by decide⟩

/-- The zero-witness trace family: state16 rows, wide rows, and the narrow bus wired as the
18-prefix of the wide table — ONE physical chip serving both buses (the deployed serving). -/
def czTf : TraceFamily := fun tid =>
  if tid = poseidon2state16 then czState16
  else if tid = TableId.poseidon2 then czWide
  else if tid = poseidon2narrow then narrowTable czWide
  else []

/-- The narrow bus IS the 18-prefix of the wide table (definitional — the `hwire` shape). -/
theorem czTf_narrow_wire : czTf poseidon2narrow = narrowTable (czTf TableId.poseidon2) := rfl

/-- The zero-witness trace. -/
def czTrace : VmTrace := { rows := [zeroAsg], pub := zeroAsg, tf := czTf }

/-- **The completed descriptor is SATISFIABLE** — an explicit witness over genuine chip tables. -/
theorem zero_witness_satisfies :
    Satisfied2 hzero shieldedSpendCompleteDesc (fun _ => 0) (fun _ => (0, 0)) [] czTrace := by
  have hmemops : memOpsOf shieldedSpendCompleteDesc = [] := by rfl
  have hmapops : mapOpsOf shieldedSpendCompleteDesc = [] := by rfl
  have hmemlog : memLog shieldedSpendCompleteDesc czTrace = [] := by
    simp [memLog, hmemops, czTrace]
  have hmaplog : mapLog shieldedSpendCompleteDesc czTrace = [] := by
    simp [mapLog, hmapops, czTrace]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    have hi0 : i = 0 := by
      have : i < 1 := by simpa [czTrace] using hi
      omega
    subst hi0
    simp only [shieldedSpendCompleteDesc, completeConstraints, shieldedSpendExactDesc,
      List.mem_append] at hc
    -- Block by block (12 leaves, left-assoc: the 5 core blocks, then the 7 completion blocks).
    -- The one-row window: isFirst = true, isLast = true.
    rcases hc with ((((((((((hc | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc
    · -- nodeSponge
      obtain ⟨step, hstep, rfl⟩ := List.mem_map.mp hc
      show (chipLookupTupleState16 step.input step.outputCols step.width).map
        (·.eval (envAt czTrace 0).loc) ∈ czTrace.tf poseidon2state16
      have : (envAt czTrace 0).loc = zeroAsg := rfl
      rw [this]
      exact List.mem_map.mpr ⟨step, List.mem_append.mpr (Or.inl hstep), rfl⟩
    · -- bitGates: `.gate` on the last row — vacuous
      simp only [Dregg2.Circuit.Emit.ShieldedSpendExactMembershipEmit.bitGates,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact trivial
    · -- contConstraints: transition windows on the last row — vacuous
      obtain ⟨lane, _, rfl⟩ := List.mem_map.mp hc
      intro hfalse
      simp [czTrace] at hfalse
    · -- rootPins: 0 ≡ 0
      obtain ⟨lane, _, rfl⟩ := List.mem_map.mp hc
      intro _
      exact Int.ModEq.refl _
    · -- carrierPins: 0 ≡ 0
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      intro _
      exact Int.ModEq.refl _
    · -- lastRowBitRepair: posBody evals to 0 at zero
      simp only [lastRowBitRepair, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact fun _ => by decide
    · -- leafSponge
      obtain ⟨step, hstep, rfl⟩ := List.mem_map.mp hc
      show (chipLookupTupleState16 step.input step.outputCols step.width).map
        (·.eval (envAt czTrace 0).loc) ∈ czTrace.tf poseidon2state16
      have : (envAt czTrace 0).loc = zeroAsg := rfl
      rw [this]
      exact List.mem_map.mpr ⟨step, List.mem_append.mpr (Or.inr hstep), rfl⟩
    · -- leafBind: 0 − 0 ≡ 0 (both cells are `zeroAsg`, whatever the lane)
      obtain ⟨lane, _, rfl⟩ := List.mem_map.mp hc
      intro _
      show (0 : ℤ) + -1 * 0 ≡ 0 [ZMOD 2013265921]
      decide
    · -- noteTie
      simp only [List.mem_singleton] at hc
      subst hc
      exact fun _ => by decide
    · -- the fact block: three narrow lookups + the nullifier pin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · show (chipLookupTupleNarrow (factIns [cVMOD, cAMOD, cOWNER, cRAND]) cCM).map
          (·.eval (envAt czTrace 0).loc) ∈ czTrace.tf poseidon2narrow
        decide
      · show (chipLookupTupleNarrow (factIns [cCM, cKEY 0, cKEY 1, cKEY 2, cKEY 3]) cNUL).map
          (·.eval (envAt czTrace 0).loc) ∈ czTrace.tf poseidon2narrow
        decide
      · show (chipLookupTupleNarrow (factIns [cKEY 0, cKEY 1, cKEY 2, cKEY 3]) cOWNER).map
          (·.eval (envAt czTrace 0).loc) ∈ czTrace.tf poseidon2narrow
        decide
      · intro _
        exact Int.ModEq.refl _
    · -- carrierGates: `.gate`s on the last row — all vacuous
      rcases List.mem_append.mp hc with hbin | hrec
      · obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hbin
        obtain ⟨i, _, hi'⟩ := List.mem_flatMap.mp hk
        rcases List.mem_append.mp hi' with hb | hr
        · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb
          exact trivial
        · simp only [List.mem_singleton] at hr
          subst hr
          exact trivial
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrec
        rcases hrec with rfl | rfl <;> exact trivial
    · -- carrierSites: the two wide lookups
      simp only [carrierSites, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · show (chipLookupTupleN (spendWideLeft DOMAIN_A ++ spendWideRight)
          (spendWideOut MWIDE)).map (·.eval (envAt czTrace 0).loc)
            ∈ czTrace.tf TableId.poseidon2
        decide
      · show (chipLookupTupleN (spendWideLeft DOMAIN_B ++ spendWideRight)
          (spendWideOut (MWIDE + 8))).map (·.eval (envAt czTrace 0).loc)
            ∈ czTrace.tf TableId.poseidon2
        decide
  · -- rowHashes: no v1 hash sites
    intro i _
    exact trivial
  · -- rowRanges: no ranges
    intro i _ r hr
    simp [shieldedSpendCompleteDesc] at hr
  · -- memAddrsNodup
    simp
  · -- memClosed
    intro op hop
    rw [hmemlog] at hop
    cases hop
  · -- memDisciplined
    rw [hmemlog]
    trivial
  · -- memBalanced
    rw [hmemlog]
    rfl
  · -- memTableFaithful
    rw [hmemlog]
    rfl
  · -- mapTableFaithful
    rw [hmaplog]
    rfl

end Witness

/-! ## §15 — the byte-pinned wire golden (`emitVmJson2 shieldedSpendCompleteDesc`). Rust reads
this raw string at the route step (the `wide_value_binding.rs` pattern: `include_str!` + split the
`def … : String := r#"…"#` golden + `parse_vm_descriptor2` + prove/verify through
`Plonky3HidingFriReference`). -/

def SHIELDED_SPEND_COMPLETE_GOLDEN : String := r#"{"name":"dregg-shielded-spend-complete-fsi2::v1","ir":2,"trace_width":557,"public_input_count":25,"challenges":0,"tables":[{"id":0,"name":"main","arity":557,"sem":"main"},{"id":9,"name":"poseidon2_state16_chip","arity":33,"sem":"poseidon2_chip","params":{"field_modulus":2013265921,"d":4,"width":16,"sbox_degree":7,"sbox_registers":1,"half_full_rounds":4,"partial_rounds":13,"rate":8,"rc_source":"BABYBEAR_POSEIDON2_RC_16","internal_diag_source":"BABYBEAR_POSEIDON2_INTERNAL_DIAG_16"}}],"constraints":[{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"const","v":0},"r":{"t":"const","v":1179864626}},{"t":"add","l":{"t":"const","v":0},"r":{"t":"add","l":{"t":"var","v":10},"r":{"t":"mul","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":10}}}}}},{"t":"add","l":{"t":"const","v":0},"r":{"t":"add","l":{"t":"var","v":11},"r":{"t":"mul","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"add","l":{"t":"var","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":11}}}}}},{"t":"add","l":{"t":"const","v":0},"r":{"t":"add","l":{"t":"var","v":12},"r":{"t":"mul","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"add","l":{"t":"var","v":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":12}}}}}},{"t":"const","v":33},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":50},{"t":"var","v":51},{"t":"var","v":52},{"t":"var","v":53},{"t":"var","v":54},{"t":"var","v":55},{"t":"var","v":56},{"t":"var","v":57},{"t":"var","v":58},{"t":"var","v":59},{"t":"var","v":60},{"t":"var","v":61},{"t":"var","v":62},{"t":"var","v":63},{"t":"var","v":64},{"t":"var","v":65}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":50},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"mul","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"add","l":{"t":"var","v":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":13}}}}}},{"t":"add","l":{"t":"var","v":51},"r":{"t":"add","l":{"t":"var","v":14},"r":{"t":"mul","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"add","l":{"t":"var","v":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":14}}}}}},{"t":"add","l":{"t":"var","v":52},"r":{"t":"add","l":{"t":"var","v":15},"r":{"t":"mul","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":15}}}}}},{"t":"add","l":{"t":"var","v":53},"r":{"t":"add","l":{"t":"var","v":16},"r":{"t":"mul","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"add","l":{"t":"var","v":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}}}}},{"t":"var","v":54},{"t":"var","v":55},{"t":"var","v":56},{"t":"var","v":57},{"t":"var","v":58},{"t":"var","v":59},{"t":"var","v":60},{"t":"var","v":61},{"t":"var","v":62},{"t":"var","v":63},{"t":"var","v":64},{"t":"var","v":65},{"t":"var","v":66},{"t":"var","v":67},{"t":"var","v":68},{"t":"var","v":69},{"t":"var","v":70},{"t":"var","v":71},{"t":"var","v":72},{"t":"var","v":73},{"t":"var","v":74},{"t":"var","v":75},{"t":"var","v":76},{"t":"var","v":77},{"t":"var","v":78},{"t":"var","v":79},{"t":"var","v":80},{"t":"var","v":81}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":66},"r":{"t":"add","l":{"t":"var","v":17},"r":{"t":"mul","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"add","l":{"t":"var","v":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":17}}}}}},{"t":"add","l":{"t":"var","v":67},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}},"r":{"t":"mul","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":18},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}}},{"t":"add","l":{"t":"var","v":68},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}},"r":{"t":"mul","l":{"t":"var","v":1},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":19},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}}},{"t":"add","l":{"t":"var","v":69},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":12},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":20},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}}},{"t":"var","v":70},{"t":"var","v":71},{"t":"var","v":72},{"t":"var","v":73},{"t":"var","v":74},{"t":"var","v":75},{"t":"var","v":76},{"t":"var","v":77},{"t":"var","v":78},{"t":"var","v":79},{"t":"var","v":80},{"t":"var","v":81},{"t":"var","v":82},{"t":"var","v":83},{"t":"var","v":84},{"t":"var","v":85},{"t":"var","v":86},{"t":"var","v":87},{"t":"var","v":88},{"t":"var","v":89},{"t":"var","v":90},{"t":"var","v":91},{"t":"var","v":92},{"t":"var","v":93},{"t":"var","v":94},{"t":"var","v":95},{"t":"var","v":96},{"t":"var","v":97}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":82},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":13},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}},"r":{"t":"mul","l":{"t":"var","v":3},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":21},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}}},{"t":"add","l":{"t":"var","v":83},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":14},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}},"r":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":22},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}}},{"t":"add","l":{"t":"var","v":84},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":23},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}}},{"t":"add","l":{"t":"var","v":85},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":24},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}}},{"t":"var","v":86},{"t":"var","v":87},{"t":"var","v":88},{"t":"var","v":89},{"t":"var","v":90},{"t":"var","v":91},{"t":"var","v":92},{"t":"var","v":93},{"t":"var","v":94},{"t":"var","v":95},{"t":"var","v":96},{"t":"var","v":97},{"t":"var","v":98},{"t":"var","v":99},{"t":"var","v":100},{"t":"var","v":101},{"t":"var","v":102},{"t":"var","v":103},{"t":"var","v":104},{"t":"var","v":105},{"t":"var","v":106},{"t":"var","v":107},{"t":"var","v":108},{"t":"var","v":109},{"t":"var","v":110},{"t":"var","v":111},{"t":"var","v":112},{"t":"var","v":113}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":98},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":17},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":25},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}}},{"t":"add","l":{"t":"var","v":99},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":18},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":26},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}},{"t":"add","l":{"t":"var","v":100},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":19},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":1},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":27},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}},{"t":"add","l":{"t":"var","v":101},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":20},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":28},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}},{"t":"var","v":102},{"t":"var","v":103},{"t":"var","v":104},{"t":"var","v":105},{"t":"var","v":106},{"t":"var","v":107},{"t":"var","v":108},{"t":"var","v":109},{"t":"var","v":110},{"t":"var","v":111},{"t":"var","v":112},{"t":"var","v":113},{"t":"var","v":114},{"t":"var","v":115},{"t":"var","v":116},{"t":"var","v":117},{"t":"var","v":118},{"t":"var","v":119},{"t":"var","v":120},{"t":"var","v":121},{"t":"var","v":122},{"t":"var","v":123},{"t":"var","v":124},{"t":"var","v":125},{"t":"var","v":126},{"t":"var","v":127},{"t":"var","v":128},{"t":"var","v":129}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":114},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":21},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":3},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":29},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}},{"t":"add","l":{"t":"var","v":115},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":22},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":30},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}},{"t":"add","l":{"t":"var","v":116},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":23},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":31},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}},{"t":"add","l":{"t":"var","v":117},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":24},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}},{"t":"var","v":118},{"t":"var","v":119},{"t":"var","v":120},{"t":"var","v":121},{"t":"var","v":122},{"t":"var","v":123},{"t":"var","v":124},{"t":"var","v":125},{"t":"var","v":126},{"t":"var","v":127},{"t":"var","v":128},{"t":"var","v":129},{"t":"var","v":130},{"t":"var","v":131},{"t":"var","v":132},{"t":"var","v":133},{"t":"var","v":134},{"t":"var","v":135},{"t":"var","v":136},{"t":"var","v":137},{"t":"var","v":138},{"t":"var","v":139},{"t":"var","v":140},{"t":"var","v":141},{"t":"var","v":142},{"t":"var","v":143},{"t":"var","v":144},{"t":"var","v":145}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":130},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":25},"r":{"t":"add","l":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}}},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"var","v":9}}}},"r":{"t":"mul","l":{"t":"var","v":33},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}}}}},{"t":"add","l":{"t":"var","v":131},"r":{"t":"add","l":{"t":"var","v":26},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":26}}}}}},{"t":"add","l":{"t":"var","v":132},"r":{"t":"add","l":{"t":"var","v":27},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"var","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":27}}}}}},{"t":"add","l":{"t":"var","v":133},"r":{"t":"add","l":{"t":"var","v":28},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"var","v":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":28}}}}}},{"t":"var","v":134},{"t":"var","v":135},{"t":"var","v":136},{"t":"var","v":137},{"t":"var","v":138},{"t":"var","v":139},{"t":"var","v":140},{"t":"var","v":141},{"t":"var","v":142},{"t":"var","v":143},{"t":"var","v":144},{"t":"var","v":145},{"t":"var","v":146},{"t":"var","v":147},{"t":"var","v":148},{"t":"var","v":149},{"t":"var","v":150},{"t":"var","v":151},{"t":"var","v":152},{"t":"var","v":153},{"t":"var","v":154},{"t":"var","v":155},{"t":"var","v":156},{"t":"var","v":157},{"t":"var","v":158},{"t":"var","v":159},{"t":"var","v":160},{"t":"var","v":161}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":146},"r":{"t":"add","l":{"t":"var","v":29},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"var","v":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":29}}}}}},{"t":"add","l":{"t":"var","v":147},"r":{"t":"add","l":{"t":"var","v":30},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"var","v":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":30}}}}}},{"t":"add","l":{"t":"var","v":148},"r":{"t":"add","l":{"t":"var","v":31},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":31}}}}}},{"t":"add","l":{"t":"var","v":149},"r":{"t":"add","l":{"t":"var","v":32},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"var","v":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":32}}}}}},{"t":"var","v":150},{"t":"var","v":151},{"t":"var","v":152},{"t":"var","v":153},{"t":"var","v":154},{"t":"var","v":155},{"t":"var","v":156},{"t":"var","v":157},{"t":"var","v":158},{"t":"var","v":159},{"t":"var","v":160},{"t":"var","v":161},{"t":"var","v":162},{"t":"var","v":163},{"t":"var","v":164},{"t":"var","v":165},{"t":"var","v":166},{"t":"var","v":167},{"t":"var","v":168},{"t":"var","v":169},{"t":"var","v":170},{"t":"var","v":171},{"t":"var","v":172},{"t":"var","v":173},{"t":"var","v":174},{"t":"var","v":175},{"t":"var","v":176},{"t":"var","v":177}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":162},"r":{"t":"add","l":{"t":"var","v":33},"r":{"t":"mul","l":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"var","v":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":33}}}}}},{"t":"add","l":{"t":"var","v":163},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":164},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":165},"r":{"t":"const","v":0}},{"t":"var","v":166},{"t":"var","v":167},{"t":"var","v":168},{"t":"var","v":169},{"t":"var","v":170},{"t":"var","v":171},{"t":"var","v":172},{"t":"var","v":173},{"t":"var","v":174},{"t":"var","v":175},{"t":"var","v":176},{"t":"var","v":177},{"t":"var","v":178},{"t":"var","v":179},{"t":"var","v":180},{"t":"var","v":181},{"t":"var","v":182},{"t":"var","v":183},{"t":"var","v":184},{"t":"var","v":185},{"t":"var","v":186},{"t":"var","v":187},{"t":"var","v":188},{"t":"var","v":189},{"t":"var","v":190},{"t":"var","v":191},{"t":"var","v":192},{"t":"var","v":193}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"var","v":178},{"t":"var","v":179},{"t":"var","v":180},{"t":"var","v":181},{"t":"var","v":182},{"t":"var","v":183},{"t":"var","v":184},{"t":"var","v":185},{"t":"var","v":186},{"t":"var","v":187},{"t":"var","v":188},{"t":"var","v":189},{"t":"var","v":190},{"t":"var","v":191},{"t":"var","v":192},{"t":"var","v":193},{"t":"var","v":194},{"t":"var","v":195},{"t":"var","v":196},{"t":"var","v":197},{"t":"var","v":198},{"t":"var","v":199},{"t":"var","v":200},{"t":"var","v":201},{"t":"var","v":202},{"t":"var","v":203},{"t":"var","v":204},{"t":"var","v":205},{"t":"var","v":206},{"t":"var","v":207},{"t":"var","v":208},{"t":"var","v":209}]},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"var","v":8},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"const","v":1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"add","l":{"t":"var","v":9},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"const","v":1}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":178}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":179}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":180}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":181}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":194}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":195}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":196}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":197}}}},{"t":"pi_binding","row":"last","col":178,"pi_index":1},{"t":"pi_binding","row":"last","col":179,"pi_index":2},{"t":"pi_binding","row":"last","col":180,"pi_index":3},{"t":"pi_binding","row":"last","col":181,"pi_index":4},{"t":"pi_binding","row":"last","col":194,"pi_index":5},{"t":"pi_binding","row":"last","col":195,"pi_index":6},{"t":"pi_binding","row":"last","col":196,"pi_index":7},{"t":"pi_binding","row":"last","col":197,"pi_index":8},{"t":"pi_binding","row":"first","col":34,"pi_index":9},{"t":"pi_binding","row":"first","col":35,"pi_index":10},{"t":"pi_binding","row":"first","col":36,"pi_index":11},{"t":"pi_binding","row":"first","col":37,"pi_index":12},{"t":"pi_binding","row":"first","col":38,"pi_index":13},{"t":"pi_binding","row":"first","col":39,"pi_index":14},{"t":"pi_binding","row":"first","col":40,"pi_index":15},{"t":"pi_binding","row":"first","col":41,"pi_index":16},{"t":"pi_binding","row":"first","col":42,"pi_index":17},{"t":"pi_binding","row":"first","col":43,"pi_index":18},{"t":"pi_binding","row":"first","col":44,"pi_index":19},{"t":"pi_binding","row":"first","col":45,"pi_index":20},{"t":"pi_binding","row":"first","col":46,"pi_index":21},{"t":"pi_binding","row":"first","col":47,"pi_index":22},{"t":"pi_binding","row":"first","col":48,"pi_index":23},{"t":"pi_binding","row":"first","col":49,"pi_index":24},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"var","v":8},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"const","v":1}}}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"add","l":{"t":"var","v":9},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"const","v":1}}}}},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"const","v":0},"r":{"t":"const","v":1179863346}},{"t":"add","l":{"t":"const","v":0},"r":{"t":"const","v":1}},{"t":"add","l":{"t":"const","v":0},"r":{"t":"var","v":234}},{"t":"add","l":{"t":"const","v":0},"r":{"t":"var","v":235}},{"t":"const","v":39},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":253},{"t":"var","v":254},{"t":"var","v":255},{"t":"var","v":256},{"t":"var","v":257},{"t":"var","v":258},{"t":"var","v":259},{"t":"var","v":260},{"t":"var","v":261},{"t":"var","v":262},{"t":"var","v":263},{"t":"var","v":264},{"t":"var","v":265},{"t":"var","v":266},{"t":"var","v":267},{"t":"var","v":268}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":253},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":254},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":255},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":256},"r":{"t":"const","v":0}},{"t":"var","v":257},{"t":"var","v":258},{"t":"var","v":259},{"t":"var","v":260},{"t":"var","v":261},{"t":"var","v":262},{"t":"var","v":263},{"t":"var","v":264},{"t":"var","v":265},{"t":"var","v":266},{"t":"var","v":267},{"t":"var","v":268},{"t":"var","v":269},{"t":"var","v":270},{"t":"var","v":271},{"t":"var","v":272},{"t":"var","v":273},{"t":"var","v":274},{"t":"var","v":275},{"t":"var","v":276},{"t":"var","v":277},{"t":"var","v":278},{"t":"var","v":279},{"t":"var","v":280},{"t":"var","v":281},{"t":"var","v":282},{"t":"var","v":283},{"t":"var","v":284}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":269},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":270},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":271},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":272},"r":{"t":"const","v":0}},{"t":"var","v":273},{"t":"var","v":274},{"t":"var","v":275},{"t":"var","v":276},{"t":"var","v":277},{"t":"var","v":278},{"t":"var","v":279},{"t":"var","v":280},{"t":"var","v":281},{"t":"var","v":282},{"t":"var","v":283},{"t":"var","v":284},{"t":"var","v":285},{"t":"var","v":286},{"t":"var","v":287},{"t":"var","v":288},{"t":"var","v":289},{"t":"var","v":290},{"t":"var","v":291},{"t":"var","v":292},{"t":"var","v":293},{"t":"var","v":294},{"t":"var","v":295},{"t":"var","v":296},{"t":"var","v":297},{"t":"var","v":298},{"t":"var","v":299},{"t":"var","v":300}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":285},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":286},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":287},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":288},"r":{"t":"const","v":0}},{"t":"var","v":289},{"t":"var","v":290},{"t":"var","v":291},{"t":"var","v":292},{"t":"var","v":293},{"t":"var","v":294},{"t":"var","v":295},{"t":"var","v":296},{"t":"var","v":297},{"t":"var","v":298},{"t":"var","v":299},{"t":"var","v":300},{"t":"var","v":301},{"t":"var","v":302},{"t":"var","v":303},{"t":"var","v":304},{"t":"var","v":305},{"t":"var","v":306},{"t":"var","v":307},{"t":"var","v":308},{"t":"var","v":309},{"t":"var","v":310},{"t":"var","v":311},{"t":"var","v":312},{"t":"var","v":313},{"t":"var","v":314},{"t":"var","v":315},{"t":"var","v":316}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":301},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":302},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":303},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":304},"r":{"t":"const","v":0}},{"t":"var","v":305},{"t":"var","v":306},{"t":"var","v":307},{"t":"var","v":308},{"t":"var","v":309},{"t":"var","v":310},{"t":"var","v":311},{"t":"var","v":312},{"t":"var","v":313},{"t":"var","v":314},{"t":"var","v":315},{"t":"var","v":316},{"t":"var","v":317},{"t":"var","v":318},{"t":"var","v":319},{"t":"var","v":320},{"t":"var","v":321},{"t":"var","v":322},{"t":"var","v":323},{"t":"var","v":324},{"t":"var","v":325},{"t":"var","v":326},{"t":"var","v":327},{"t":"var","v":328},{"t":"var","v":329},{"t":"var","v":330},{"t":"var","v":331},{"t":"var","v":332}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":317},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":318},"r":{"t":"const","v":0}},{"t":"add","l":{"t":"var","v":319},"r":{"t":"var","v":236}},{"t":"add","l":{"t":"var","v":320},"r":{"t":"var","v":237}},{"t":"var","v":321},{"t":"var","v":322},{"t":"var","v":323},{"t":"var","v":324},{"t":"var","v":325},{"t":"var","v":326},{"t":"var","v":327},{"t":"var","v":328},{"t":"var","v":329},{"t":"var","v":330},{"t":"var","v":331},{"t":"var","v":332},{"t":"var","v":333},{"t":"var","v":334},{"t":"var","v":335},{"t":"var","v":336},{"t":"var","v":337},{"t":"var","v":338},{"t":"var","v":339},{"t":"var","v":340},{"t":"var","v":341},{"t":"var","v":342},{"t":"var","v":343},{"t":"var","v":344},{"t":"var","v":345},{"t":"var","v":346},{"t":"var","v":347},{"t":"var","v":348}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":333},"r":{"t":"var","v":238}},{"t":"add","l":{"t":"var","v":334},"r":{"t":"var","v":239}},{"t":"add","l":{"t":"var","v":335},"r":{"t":"var","v":240}},{"t":"add","l":{"t":"var","v":336},"r":{"t":"var","v":241}},{"t":"var","v":337},{"t":"var","v":338},{"t":"var","v":339},{"t":"var","v":340},{"t":"var","v":341},{"t":"var","v":342},{"t":"var","v":343},{"t":"var","v":344},{"t":"var","v":345},{"t":"var","v":346},{"t":"var","v":347},{"t":"var","v":348},{"t":"var","v":349},{"t":"var","v":350},{"t":"var","v":351},{"t":"var","v":352},{"t":"var","v":353},{"t":"var","v":354},{"t":"var","v":355},{"t":"var","v":356},{"t":"var","v":357},{"t":"var","v":358},{"t":"var","v":359},{"t":"var","v":360},{"t":"var","v":361},{"t":"var","v":362},{"t":"var","v":363},{"t":"var","v":364}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":349},"r":{"t":"var","v":242}},{"t":"add","l":{"t":"var","v":350},"r":{"t":"var","v":243}},{"t":"add","l":{"t":"var","v":351},"r":{"t":"var","v":244}},{"t":"add","l":{"t":"var","v":352},"r":{"t":"var","v":245}},{"t":"var","v":353},{"t":"var","v":354},{"t":"var","v":355},{"t":"var","v":356},{"t":"var","v":357},{"t":"var","v":358},{"t":"var","v":359},{"t":"var","v":360},{"t":"var","v":361},{"t":"var","v":362},{"t":"var","v":363},{"t":"var","v":364},{"t":"var","v":365},{"t":"var","v":366},{"t":"var","v":367},{"t":"var","v":368},{"t":"var","v":369},{"t":"var","v":370},{"t":"var","v":371},{"t":"var","v":372},{"t":"var","v":373},{"t":"var","v":374},{"t":"var","v":375},{"t":"var","v":376},{"t":"var","v":377},{"t":"var","v":378},{"t":"var","v":379},{"t":"var","v":380}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":365},"r":{"t":"var","v":246}},{"t":"add","l":{"t":"var","v":366},"r":{"t":"var","v":247}},{"t":"add","l":{"t":"var","v":367},"r":{"t":"var","v":248}},{"t":"add","l":{"t":"var","v":368},"r":{"t":"var","v":249}},{"t":"var","v":369},{"t":"var","v":370},{"t":"var","v":371},{"t":"var","v":372},{"t":"var","v":373},{"t":"var","v":374},{"t":"var","v":375},{"t":"var","v":376},{"t":"var","v":377},{"t":"var","v":378},{"t":"var","v":379},{"t":"var","v":380},{"t":"var","v":381},{"t":"var","v":382},{"t":"var","v":383},{"t":"var","v":384},{"t":"var","v":385},{"t":"var","v":386},{"t":"var","v":387},{"t":"var","v":388},{"t":"var","v":389},{"t":"var","v":390},{"t":"var","v":391},{"t":"var","v":392},{"t":"var","v":393},{"t":"var","v":394},{"t":"var","v":395},{"t":"var","v":396}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"add","l":{"t":"var","v":381},"r":{"t":"var","v":250}},{"t":"add","l":{"t":"var","v":382},"r":{"t":"var","v":251}},{"t":"add","l":{"t":"var","v":383},"r":{"t":"var","v":252}},{"t":"add","l":{"t":"var","v":384},"r":{"t":"const","v":0}},{"t":"var","v":385},{"t":"var","v":386},{"t":"var","v":387},{"t":"var","v":388},{"t":"var","v":389},{"t":"var","v":390},{"t":"var","v":391},{"t":"var","v":392},{"t":"var","v":393},{"t":"var","v":394},{"t":"var","v":395},{"t":"var","v":396},{"t":"var","v":397},{"t":"var","v":398},{"t":"var","v":399},{"t":"var","v":400},{"t":"var","v":401},{"t":"var","v":402},{"t":"var","v":403},{"t":"var","v":404},{"t":"var","v":405},{"t":"var","v":406},{"t":"var","v":407},{"t":"var","v":408},{"t":"var","v":409},{"t":"var","v":410},{"t":"var","v":411},{"t":"var","v":412}]},{"t":"lookup","table":9,"tuple":[{"t":"const","v":16},{"t":"var","v":397},{"t":"var","v":398},{"t":"var","v":399},{"t":"var","v":400},{"t":"var","v":401},{"t":"var","v":402},{"t":"var","v":403},{"t":"var","v":404},{"t":"var","v":405},{"t":"var","v":406},{"t":"var","v":407},{"t":"var","v":408},{"t":"var","v":409},{"t":"var","v":410},{"t":"var","v":411},{"t":"var","v":412},{"t":"var","v":413},{"t":"var","v":414},{"t":"var","v":415},{"t":"var","v":416},{"t":"var","v":417},{"t":"var","v":418},{"t":"var","v":419},{"t":"var","v":420},{"t":"var","v":421},{"t":"var","v":422},{"t":"var","v":423},{"t":"var","v":424},{"t":"var","v":425},{"t":"var","v":426},{"t":"var","v":427},{"t":"var","v":428}]},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":397}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":398}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":399}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":400}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":413}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":414}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":415}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":416}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":214},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"var","v":234},"r":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":235}}}}}},{"t":"lookup","table":8,"tuple":[{"t":"const","v":7},{"t":"var","v":210},{"t":"var","v":211},{"t":"var","v":212},{"t":"var","v":213},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":214}]},{"t":"lookup","table":8,"tuple":[{"t":"const","v":7},{"t":"var","v":214},{"t":"var","v":216},{"t":"var","v":217},{"t":"var","v":218},{"t":"var","v":219},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":215}]},{"t":"lookup","table":8,"tuple":[{"t":"const","v":7},{"t":"var","v":216},{"t":"var","v":217},{"t":"var","v":218},{"t":"var","v":219},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":212}]},{"t":"pi_binding","row":"first","col":215,"pi_index":0},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":429},"r":{"t":"add","l":{"t":"var","v":429},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":430},"r":{"t":"add","l":{"t":"var","v":430},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":431},"r":{"t":"add","l":{"t":"var","v":431},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":432},"r":{"t":"add","l":{"t":"var","v":432},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":433},"r":{"t":"add","l":{"t":"var","v":433},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":434},"r":{"t":"add","l":{"t":"var","v":434},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":435},"r":{"t":"add","l":{"t":"var","v":435},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":436},"r":{"t":"add","l":{"t":"var","v":436},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":437},"r":{"t":"add","l":{"t":"var","v":437},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":438},"r":{"t":"add","l":{"t":"var","v":438},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":439},"r":{"t":"add","l":{"t":"var","v":439},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":440},"r":{"t":"add","l":{"t":"var","v":440},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":441},"r":{"t":"add","l":{"t":"var","v":441},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":442},"r":{"t":"add","l":{"t":"var","v":442},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":443},"r":{"t":"add","l":{"t":"var","v":443},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":444},"r":{"t":"add","l":{"t":"var","v":444},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":220}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":429}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":430}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":431}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":432}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":433}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":434}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":435}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":436}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":437}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":438}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":439}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":440}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":441}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":442}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":443}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":444}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":445},"r":{"t":"add","l":{"t":"var","v":445},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":446},"r":{"t":"add","l":{"t":"var","v":446},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":447},"r":{"t":"add","l":{"t":"var","v":447},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":448},"r":{"t":"add","l":{"t":"var","v":448},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":449},"r":{"t":"add","l":{"t":"var","v":449},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":450},"r":{"t":"add","l":{"t":"var","v":450},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":451},"r":{"t":"add","l":{"t":"var","v":451},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":452},"r":{"t":"add","l":{"t":"var","v":452},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":453},"r":{"t":"add","l":{"t":"var","v":453},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":454},"r":{"t":"add","l":{"t":"var","v":454},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":455},"r":{"t":"add","l":{"t":"var","v":455},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":456},"r":{"t":"add","l":{"t":"var","v":456},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":457},"r":{"t":"add","l":{"t":"var","v":457},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":458},"r":{"t":"add","l":{"t":"var","v":458},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":459},"r":{"t":"add","l":{"t":"var","v":459},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":460},"r":{"t":"add","l":{"t":"var","v":460},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":221}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":445}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":446}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":447}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":448}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":449}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":450}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":451}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":452}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":453}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":454}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":455}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":456}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":457}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":458}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":459}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":460}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":461},"r":{"t":"add","l":{"t":"var","v":461},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":462},"r":{"t":"add","l":{"t":"var","v":462},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":463},"r":{"t":"add","l":{"t":"var","v":463},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":464},"r":{"t":"add","l":{"t":"var","v":464},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":465},"r":{"t":"add","l":{"t":"var","v":465},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":466},"r":{"t":"add","l":{"t":"var","v":466},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":467},"r":{"t":"add","l":{"t":"var","v":467},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":468},"r":{"t":"add","l":{"t":"var","v":468},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":469},"r":{"t":"add","l":{"t":"var","v":469},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":470},"r":{"t":"add","l":{"t":"var","v":470},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":471},"r":{"t":"add","l":{"t":"var","v":471},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":472},"r":{"t":"add","l":{"t":"var","v":472},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":473},"r":{"t":"add","l":{"t":"var","v":473},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":474},"r":{"t":"add","l":{"t":"var","v":474},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":475},"r":{"t":"add","l":{"t":"var","v":475},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":476},"r":{"t":"add","l":{"t":"var","v":476},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":222}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":461}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":462}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":463}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":464}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":465}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":466}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":467}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":468}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":469}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":470}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":471}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":472}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":473}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":474}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":475}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":476}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":477},"r":{"t":"add","l":{"t":"var","v":477},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":478},"r":{"t":"add","l":{"t":"var","v":478},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":479},"r":{"t":"add","l":{"t":"var","v":479},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":480},"r":{"t":"add","l":{"t":"var","v":480},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":481},"r":{"t":"add","l":{"t":"var","v":481},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":482},"r":{"t":"add","l":{"t":"var","v":482},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":483},"r":{"t":"add","l":{"t":"var","v":483},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":484},"r":{"t":"add","l":{"t":"var","v":484},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":485},"r":{"t":"add","l":{"t":"var","v":485},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":486},"r":{"t":"add","l":{"t":"var","v":486},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":487},"r":{"t":"add","l":{"t":"var","v":487},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":488},"r":{"t":"add","l":{"t":"var","v":488},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":489},"r":{"t":"add","l":{"t":"var","v":489},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":490},"r":{"t":"add","l":{"t":"var","v":490},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":491},"r":{"t":"add","l":{"t":"var","v":491},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":492},"r":{"t":"add","l":{"t":"var","v":492},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":223}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":477}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":478}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":479}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":480}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":481}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":482}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":483}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":484}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":485}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":486}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":487}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":488}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":489}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":490}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":491}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":492}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":493},"r":{"t":"add","l":{"t":"var","v":493},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":494},"r":{"t":"add","l":{"t":"var","v":494},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":495},"r":{"t":"add","l":{"t":"var","v":495},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":496},"r":{"t":"add","l":{"t":"var","v":496},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":497},"r":{"t":"add","l":{"t":"var","v":497},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":498},"r":{"t":"add","l":{"t":"var","v":498},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":499},"r":{"t":"add","l":{"t":"var","v":499},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":500},"r":{"t":"add","l":{"t":"var","v":500},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":501},"r":{"t":"add","l":{"t":"var","v":501},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":502},"r":{"t":"add","l":{"t":"var","v":502},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":503},"r":{"t":"add","l":{"t":"var","v":503},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":504},"r":{"t":"add","l":{"t":"var","v":504},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":505},"r":{"t":"add","l":{"t":"var","v":505},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":506},"r":{"t":"add","l":{"t":"var","v":506},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":507},"r":{"t":"add","l":{"t":"var","v":507},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":508},"r":{"t":"add","l":{"t":"var","v":508},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":224}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":493}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":494}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":495}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":496}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":497}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":498}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":499}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":500}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":501}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":502}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":503}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":504}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":505}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":506}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":507}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":508}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":509},"r":{"t":"add","l":{"t":"var","v":509},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":510},"r":{"t":"add","l":{"t":"var","v":510},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":511},"r":{"t":"add","l":{"t":"var","v":511},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":512},"r":{"t":"add","l":{"t":"var","v":512},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":513},"r":{"t":"add","l":{"t":"var","v":513},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":514},"r":{"t":"add","l":{"t":"var","v":514},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":515},"r":{"t":"add","l":{"t":"var","v":515},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":516},"r":{"t":"add","l":{"t":"var","v":516},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":517},"r":{"t":"add","l":{"t":"var","v":517},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":518},"r":{"t":"add","l":{"t":"var","v":518},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":519},"r":{"t":"add","l":{"t":"var","v":519},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":520},"r":{"t":"add","l":{"t":"var","v":520},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":521},"r":{"t":"add","l":{"t":"var","v":521},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":522},"r":{"t":"add","l":{"t":"var","v":522},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":523},"r":{"t":"add","l":{"t":"var","v":523},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":524},"r":{"t":"add","l":{"t":"var","v":524},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":225}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":509}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":510}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":511}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":512}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":513}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":514}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":515}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":516}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":517}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":518}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":519}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":520}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":521}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":522}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":523}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":524}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":525},"r":{"t":"add","l":{"t":"var","v":525},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":526},"r":{"t":"add","l":{"t":"var","v":526},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":527},"r":{"t":"add","l":{"t":"var","v":527},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":528},"r":{"t":"add","l":{"t":"var","v":528},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":529},"r":{"t":"add","l":{"t":"var","v":529},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":530},"r":{"t":"add","l":{"t":"var","v":530},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":531},"r":{"t":"add","l":{"t":"var","v":531},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":532},"r":{"t":"add","l":{"t":"var","v":532},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":533},"r":{"t":"add","l":{"t":"var","v":533},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":534},"r":{"t":"add","l":{"t":"var","v":534},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":535},"r":{"t":"add","l":{"t":"var","v":535},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":536},"r":{"t":"add","l":{"t":"var","v":536},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":537},"r":{"t":"add","l":{"t":"var","v":537},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":538},"r":{"t":"add","l":{"t":"var","v":538},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":539},"r":{"t":"add","l":{"t":"var","v":539},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":540},"r":{"t":"add","l":{"t":"var","v":540},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":226}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":525}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":526}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":527}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":528}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":529}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":530}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":531}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":532}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":533}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":534}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":535}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":536}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":537}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":538}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":539}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":540}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":541},"r":{"t":"add","l":{"t":"var","v":541},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":542},"r":{"t":"add","l":{"t":"var","v":542},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":543},"r":{"t":"add","l":{"t":"var","v":543},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":544},"r":{"t":"add","l":{"t":"var","v":544},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":545},"r":{"t":"add","l":{"t":"var","v":545},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":546},"r":{"t":"add","l":{"t":"var","v":546},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":547},"r":{"t":"add","l":{"t":"var","v":547},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":548},"r":{"t":"add","l":{"t":"var","v":548},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":549},"r":{"t":"add","l":{"t":"var","v":549},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":550},"r":{"t":"add","l":{"t":"var","v":550},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":551},"r":{"t":"add","l":{"t":"var","v":551},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":552},"r":{"t":"add","l":{"t":"var","v":552},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":553},"r":{"t":"add","l":{"t":"var","v":553},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":554},"r":{"t":"add","l":{"t":"var","v":554},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":555},"r":{"t":"add","l":{"t":"var","v":555},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":556},"r":{"t":"add","l":{"t":"var","v":556},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":227}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":541}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":542}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":543}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":544}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":545}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":546}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":547}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":548}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":549}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":550}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":551}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":552}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":553}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":554}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":555}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":556}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":210}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":220}}},"r":{"t":"mul","l":{"t":"const","v":-65536},"r":{"t":"var","v":221}}},"r":{"t":"mul","l":{"t":"const","v":-268435454},"r":{"t":"var","v":222}}},"r":{"t":"mul","l":{"t":"const","v":-268295646},"r":{"t":"var","v":223}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":211}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":224}}},"r":{"t":"mul","l":{"t":"const","v":-65536},"r":{"t":"var","v":225}}},"r":{"t":"mul","l":{"t":"const","v":-268435454},"r":{"t":"var","v":226}}},"r":{"t":"mul","l":{"t":"const","v":-268295646},"r":{"t":"var","v":227}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"const","v":1447185968},{"t":"var","v":220},{"t":"var","v":221},{"t":"var","v":222},{"t":"var","v":223},{"t":"var","v":224},{"t":"var","v":225},{"t":"var","v":226},{"t":"var","v":227},{"t":"var","v":213},{"t":"var","v":228},{"t":"var","v":229},{"t":"var","v":230},{"t":"var","v":231},{"t":"var","v":232},{"t":"var","v":233},{"t":"var","v":34},{"t":"var","v":35},{"t":"var","v":36},{"t":"var","v":37},{"t":"var","v":38},{"t":"var","v":39},{"t":"var","v":40},{"t":"var","v":41}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"const","v":1447185969},{"t":"var","v":220},{"t":"var","v":221},{"t":"var","v":222},{"t":"var","v":223},{"t":"var","v":224},{"t":"var","v":225},{"t":"var","v":226},{"t":"var","v":227},{"t":"var","v":213},{"t":"var","v":228},{"t":"var","v":229},{"t":"var","v":230},{"t":"var","v":231},{"t":"var","v":232},{"t":"var","v":233},{"t":"var","v":42},{"t":"var","v":43},{"t":"var","v":44},{"t":"var","v":45},{"t":"var","v":46},{"t":"var","v":47},{"t":"var","v":48},{"t":"var","v":49}]}],"hash_sites":[],"ranges":[]}"#

/-- The emitted wire bytes ARE the pinned golden (compiled-string equality — the same check a
`#guard` would run, with the compiler trust said out loud: `#assert_compiled` in §16). -/
theorem complete_emits_golden :
    emitVmJson2 shieldedSpendCompleteDesc = SHIELDED_SPEND_COMPLETE_GOLDEN := by
  native_decide

/-! ## §16 — axiom hygiene. -/

#assert_axioms complete_root_is_pinned8
#assert_axioms mem_of_membership_core
#assert_axioms leaf_sponge_executes
#assert_axioms node_sponge_executes
#assert_axioms leaf_bound_to_current8
#assert_axioms note_tied_to_leaf_address
#assert_axioms cm_opens_row0
#assert_axioms nullifier_published
#assert_axioms nullifier_derived_row0
#assert_axioms owner_derived_row0
#assert_axioms carrierA_lanes_forced
#assert_axioms carrierB_lanes_forced
#assert_axioms carrier_published
#assert_axioms published_carrier_is_the_cap_node8_image
#assert_axioms published_carrierB_is_the_cap_node8_image
#assert_axioms spendWideIns_is_carrierIns
#assert_axioms spend_limb_canonical
#assert_axioms vmod_reduced
#assert_axioms amod_reduced
#assert_axioms foreign_nullifier_unsat
#assert_axioms decoupled_carrier_unsat
#assert_axioms wrong_leaf_unsat
#assert_axioms foreign_note_unsat
#assert_axioms forged_nullifier_refused
#assert_axioms decoupled_carrier_refused
#assert_axioms wrong_leaf_refused
#assert_axioms foreign_note_refused
#assert_axioms czState16_sound
#assert_axioms czWide_soundN
#assert_axioms czTf_narrow_wire
#assert_axioms zero_witness_satisfies
#assert_compiled complete_emits_golden

end Dregg2.Circuit.Emit.ShieldedSpendCompleteEmit
