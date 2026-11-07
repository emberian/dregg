/-
# Dregg2.Circuit.Emit.CarrierOctetGates — the v12 PER-CARRIER GATE KEYSTONES (big-bang parallel lane).

The three reusable in-AIR gate families the four v12-walled carriers need, written against the
announced v12 geometry (NUM_PRE_LIMBS 88→112, B_SPAN 119→151, the three zeroed octets — now
child_vk8@89..96 · contract_hash8@97..104 · pubkey8@105..112 after the REVOKED-ROOT +1 shift —
`docs/deos/V12-GEOMETRY-EPOCH-PLAN.md`),
BUILT AGAINST monolith checkpoint `85170b24c` (STEP 1b — all Emit consumers green at B_SPAN = 151).

  1. **THE OCTET-EQUALITY GATE** (`octetTeethGates` / `withOctetTeeth`) — the perms/VK-weld shape
     (`permsVKWeldGate`, EffectVmEmitRotationV3 §5.PV) generalized to an 8-limb GROUP: 8 unconditional
     `eqGate`s forcing 8 published TAIL teeth columns == the committed octet limbs of a rotated block
     (BEFORE / AFTER / BOTH — parametric `blockBase`). Instantiated for the factory `child_vk8` teeth
     (octet @ `B_CHILD_VK8`; hatchery-invariant RIDES the same octet, `invariant_digest === child_vk`)
     and the hatchery-contract `contract_hash8` teeth (@ `B_CONTRACT_HASH8`). Direct equality — the
     material is already the 32B hash's 8 limbs, no hash gate needed (plan §4).

  2. **THE COMPRESS GATE** (sovereign `withSovereignKeyCommit` + membership
     `withMembershipPubkeyCompress`) — in-AIR Poseidon2 compression of the committed pubkey octet
     (@ `B_PUBKEY8`) == the teeth felts the executor checks, via the SAME wide chip lookups every
     8-felt keystone rides (`chipLookupTupleN` / `chip_lookup_sound_N`, the `HeapOpenEmit`/
     `CapOpenEmit` emission pattern). Parametric over the chip absorb `A : List ℤ → Digest8`
     (`descriptor_ir2::chip_absorb_all_lanes` — the ONE deployed Poseidon2 chip).

  3. **THE FIELDS-ROOT READ-OPEN** (`effFieldsReadOpenV3`) — membership's `authorized_root` anchor:
     the EXISTING fields-open read appendix (`FieldsOpenEmit.fieldsOpenConstraints`, `effFieldsOpenV3`)
     plus welds binding the appendix root group to the committed BEFORE `fields_root` block (limb
     `B_FIELDS_ROOT` = 36 + completions — `beforeRootWeldsF`, reused verbatim), the read leaf's addr
     to a declared `set_root_index` column, and the read leaf's VALUE to the published root-teeth
     column. Forcing: `Satisfied2` ⟹ the teeth felt IS a fields-map value membership-authenticated
     under the committed ~124-bit `fields_root` (`fieldsReadAt8`). NOT geometry (plan §1 / O3).

## ⚑ THE EXECUTOR-COMPRESS VERDICT — REWRITTEN 2026-08-08, AND THE OLD ONE WAS A LIVE WOUND

  * **sovereign — MATCH, over the NONET.** `TurnExecutor::pubkey_to_witness_key_commit`
    (`turn/src/executor/proof_verify.rs`), `trace_rotated::append_sovereign_key_commit_rider` and
    `keyCommitSpec` below are all `effect_vm::helpers::key_commit_teeth_from_nonet`: the nine
    base-`2^29` lanes of the key (`helpers::key_limbs9`, Lean authority
    `Circuit.KeyLanes9.keyToLanes9`), then FOUR `hash_4_to_1` compressions over the interleave quads
    `[0,1,2,3] · [4,5,6,7] · [8,0,4,2] · [1,5,3,7]` (`quadIdx`, whose Rust twin
    `helpers::KEY_COMMIT_QUAD_IDX` is generated from THIS matrix by `EmitLayoutManifest`).
    `hash_4_to_1(x) = perm(st[0..4]=x, st[4]=4, 0…)[0]` is EXACTLY the deployed chip's arity-4 row
    (`chip_absorb_all_lanes(4, x)[0]`), so the KEY_COMMIT teeth (4 felts,
    `columns.rs::WITNESS_KEY_COMMIT_0..3` = aux offsets 23..26, row-0-pinned to PI) are FOUR arity-4
    chip lookups over the committed nonet. ⚑ The producer fill of the pubkey nonet is
    `helpers::key_limbs9(pubkey)` into `PUBKEY_NONET_LANE_COL`.

    ⚠ **WHAT THIS PARAGRAPH SAID BEFORE, AND WHY IT MATTERED.** It said the quads were
    `[0,1,2,3]·[4,5,6,7]·[0,4,2,6]·[1,5,3,7]` over the eight-column OCTET, and that
    `commit/src/typed.rs::canonical_32_to_felts_4` was that function. Both halves rotted, in
    opposite directions and on different days:

      1. `6441705e8` (the key-nonet flag day) rewrote `canonical_32_to_felts_4` into ONE arity-16
         absorb over the nonet and re-pointed the executor at it, on a census that recorded the
         four-felt id fold as "off-AIR — no descriptor width, no PI count, no VK". The census missed
         `pubkey_to_witness_key_commit`, which IS that function and IS on-AIR. From that commit the
         executor's teeth and the published teeth were DIFFERENT FUNCTIONS: transcript divergence,
         `InvalidPowWitness`, and `rotated_sovereign_make_sovereign_proves_and_verifies` red while
         its nine record-pin siblings passed.
      2. Independently, the octet cover was never enough. Lane 8 carries source bit 255, which is an
         Ed25519 key's x-sign, so `A` and `−A` — a keypair the attacker holds the private half of —
         published BIT-IDENTICAL teeth. Re-pointing the executor back at the octet recipe would have
         made the member green again while re-opening exactly that.

    The repair does both at once: nine lanes in the AIR (row 2 `[0,4,2,6] → [8,0,4,2]`, unchanged
    arity and unchanged `KEY_COMMIT_SPAN`) and ONE named Rust denotation the executor, the producer
    rider and this spec all name.

  * **membership — MISMATCH (named, not fudged).** `membership_verifier.rs:67 compress` =
    `poseidon2::hash_many(BabyBear::encode_hash(pk))`: (i) `encode_hash` = **full 32-bit LE limbs**
    (`field.rs:212`, mod-p lossy) — a DIFFERENT limb decomposition from sovereign's 30-bit
    `canonical_32_to_felts_8`, so ONE committed pubkey octet cannot serve both executors' functions
    as-is; (ii) `hash_many` over 8 limbs is a **rate-4 TWO-permutation sponge** (`poseidon2.rs:377`
    — `st[4] = len` tag, absorb 4, permute, absorb 4, permute, squeeze `st[0]`), which NO deployed
    chip arity computes: the chip is single-permutation per row, its non-{7,11,16} arities seed
    `st[4]=tag, st[5..7]=0` and DROP inputs 4..6 (`chip_absorb_all_lanes`), and a two-lookup chain
    is impossible because the capacity lanes 8..15 of the intermediate state are unexposed.
    `withMembershipPubkeyCompress` therefore realizes the CHIP-NATIVE injective 1-felt compress —
    the arity-16 `node8` row over `pubkey8 ‖ 0⁸` (every limb genuinely seeded, the same lane every
    cap/heap/fields node rides) — and the WIRING step owes the executor re-alignment:
    `membership_verifier.rs::compress` (+ its twins `apply.rs::compress`, SDK `bytes_to_babybear`,
    and the membership-STARK leaf domain) must move to the chip-native form (or a hash_many chip
    capability must be added) BEFORE the gate goes live. Firing the gate against the misaligned
    executor would bind teeth the executor never checks — the fail-open law forbids it.

## Offsets — ALL derived from the canonical constants (never literals)

`B_CARRIER_OCTETS := 89` (deployed literal — Rust `trace_rotated.rs::B_CHILD_VK_OCTET`);
`B_CHILD_VK8 / B_CONTRACT_HASH8 / B_PUBKEY8 := B_CARRIER_OCTETS + 0/8/16`;
`BEFORE_BLOCK_BASE := EFFECT_VM_WIDTH`; `AFTER_BLOCK_BASE := EFFECT_VM_WIDTH + B_SPAN`.
`#guard`s pin them to the deployed 89/97/105 and tie `AFTER_BLOCK_OFF == B_SPAN`.

## Scope (the big-bang contract)

NO descriptor wiring, NO registry touch, NO regen here — the big-bang regen (the coordinating
lane) wires these fragments into the carrier descriptors, bumps `public_input_count`, and row-0
pins the teeth columns to TAIL PIs. Teeth/param column indices are PARAMETRIC (`teethPiLo`,
`idxCol`, `rootTeethCol`) for exactly that reason. Every forcing lemma is TRACE-FORCED — derived
from `Satisfied2`'s row constraints, never from `henc`'s `SpineCommits`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the
named chip-soundness hypotheses (`ChipTableSoundN`), exactly as in `FieldsOpenEmit`/`HeapOpenEmit`.
-/
import Dregg2.Circuit.DeployedCapOpen
import Dregg2.Circuit.DeployedFieldsTree
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.CapOpenEmit
import Dregg2.Circuit.Emit.FieldsOpenEmit

namespace Dregg2.Circuit.Emit.CarrierOctetGates

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv EFFECT_VM_WIDTH VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (Table TraceFamily Lookup VmConstraint2 EffectVmDescriptor2 ChipTableSoundN Satisfied2
   chipLookupTupleN chip_lookup_sound_N CHIP_RATE VmTrace envAt ChipArityAdmitted)
open Dregg2.Circuit.DeployedCapOpen (DEPTH digestCols digestCols_map groupVal pathOf8)
open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedFieldsTree (Fields8Scheme)
open Dregg2.Circuit.DeployedFieldsTree.Fields8Scheme (fieldsLeafDigest8 recomposeUp8)
open Dregg2.Circuit.CapMerkleGeneric (StepG)
open Dregg2.Circuit.Emit.CapOpenEmit (capOpenCols eqGate eqGate_eval diffGate_exact CAP_OPEN_SPAN)
open Dregg2.Circuit.Emit.FieldsOpenEmit
  (fieldsOpenConstraints effFieldsOpenV3 effFieldsOpenV3_core fieldsOpen_recompose8
   FieldsMembershipCore fieldsPermOut fieldsLeafTripleOf beforeRootWeldsF)

set_option autoImplicit false

/-! ## §0 — the v12 octet geometry, derived from the canonical constants. -/

/-- The base of the three v12 carrier-material octets (LITERAL 89 since the REVOKED-ROOT
flag-day's +1 shift — Rust `trace_rotated.rs::B_CHILD_VK_OCTET = 89`; was 88 in v13. The
fields[0..7] completion lanes 1..7 (113..=168), the circuit-only cells_root completion 169..=175
and — since the NINTH-LANE flag day — the eight `fields[slot]` lane-8 columns 176..=183 ride PAST
the carrier octets, so the octet base no longer tracks `B_IROOT`. There are NO pads left: the two
that used to sit at 176/177 were consumed by the nonet, `rotated184.pads = []`). -/
def B_CARRIER_OCTETS : Nat := 89

/-- The factory `child_vk8` octet base (in-block limb offset; M1 of the v12 plan). The
hatchery-invariant carrier RIDES this same octet (`invariant_digest === child_vk`). -/
def B_CHILD_VK8 : Nat := B_CARRIER_OCTETS

/-- The hatchery-contract `contract_hash8` octet base (M2). -/
def B_CONTRACT_HASH8 : Nat := B_CARRIER_OCTETS + 8

/-- The sovereign/membership `pubkey8` octet base (M3 — raw key limbs, NOT a pre-hashed fold, so
the in-AIR compress gate can recompute the teeth; plan O2). -/
def B_PUBKEY8 : Nat := B_CARRIER_OCTETS + 16

/-- The rotated BEFORE block base (the v1 spine is `EFFECT_VM_WIDTH` wide; blocks append after). -/
def BEFORE_BLOCK_BASE : Nat := EFFECT_VM_WIDTH

/-- The rotated AFTER block base — derived from `B_SPAN`, never the literal. -/
def AFTER_BLOCK_BASE : Nat :=
  EFFECT_VM_WIDTH + Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_SPAN

-- Self-test pins: the derived offsets equal the DEPLOYED layout (Rust `trace_rotated.rs`:
-- `B_CHILD_VK_OCTET = 89` · `B_CONTRACT_HASH_OCTET = 97` · `B_PUBKEY_OCTET = 105`, the
-- REVOKED-ROOT +1 shift), and the monolith's AFTER-block offset is exactly B_SPAN (so
-- `AFTER_BLOCK_BASE` matches every group-col reader).
#guard B_CARRIER_OCTETS == 89
#guard B_CHILD_VK8 == 89
#guard B_CONTRACT_HASH8 == 97
#guard B_PUBKEY8 == 105
-- NINTH-LANE geometry (re-derived from `RotatedLayout.rotated196`, column order): the pubkey octet
-- (105..=112, 8 limbs) + the fields lanes 1..7 window (113..=168, 56 limbs) + the circuit-only
-- cells_root completion (169..=175, 7 limbs) + the eight fields NINTH lanes (176..=183, 8 limbs —
-- the fields-nonet run, which ATE the two former pads at 176/177 and the six new columns 178..183)
-- + the three KEY-nonet ninth lanes (184..=186) ride between the carrier octets and the iroot.
--
-- ⚑ RE-TYPED 2026-08-01 for the KEY-NONET flag day (`76c3f7b9b`): `+ 8` was the whole run, and the
-- key nonet appended THREE more columns — `child_vk` lane 8 at 184, `contract_hash` lane 8 at 185
-- and the owner key's lane 8 (the Ed25519 sign bit) at 186 — taking the region 184 -> 187. The
-- number is not raised: each of the three is NAMED below against the constant
-- `EffectVmEmitRotationV3` derives from `rotated196.octetLaneCol`, so this reads TWO independent
-- sources and can disagree, rather than restating its own arithmetic.
--   105 + 8 + 56 + 7 + 8 + 3 + 7 + 2 = 196 = B_IROOT   (was 105 + 8 + 56 + 7 + 8 + 3 = 187; the
--   `+ 7 + 2` are the receipt root's lanes 1..7 and the two pads, the iroot-widening flag day).
#guard B_PUBKEY8 + 8 + 56 + 7 + 8 + 3 + 7 + 2 == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_IROOT
-- WHICH three: the key nonet opens exactly where the fields nonet ends, and its last lane is the
-- last pre-limb — so the `+ 3` above is those columns and nothing else.
#guard Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_CHILD_VK_NINTH_LANE
    == B_PUBKEY8 + 8 + 56 + 7 + 8
#guard Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_CONTRACT_HASH_NINTH_LANE
    == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_CHILD_VK_NINTH_LANE + 1
#guard Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_PUBKEY_NINTH_LANE
    == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_CONTRACT_HASH_NINTH_LANE + 1
#guard Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_PUBKEY_NINTH_LANE + 1
    == (Dregg2.Circuit.Emit.rotated196.irootLaneCol 1).getD 0
#guard Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_PUBKEY_NINTH_LANE + 1 + 7 + 2
    == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_IROOT
#guard Dregg2.Circuit.Emit.EffectVmEmitRotationV3.AFTER_BLOCK_OFF
    == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_SPAN
#guard AFTER_BLOCK_BASE == EFFECT_VM_WIDTH + Dregg2.Circuit.Emit.EffectVmEmitRotationV3.AFTER_BLOCK_OFF

/-- The 8-felt column GROUP of an octet in the block based at `blockBase` (contiguous limbs
`octetBase .. octetBase+7`, unlike the roots' scattered completion limbs — the octets are
v12-native, laid contiguously). -/
def octetGroupCol (blockBase octetBase : Nat) : Fin 8 → Nat :=
  fun i => blockBase + octetBase + i.val

/-- The committed octet read off the row env as a `Digest8`. -/
def octetVals (env : VmRowEnv) (blockBase octetBase : Nat) : Digest8 :=
  groupVal env (octetGroupCol blockBase octetBase)

/-! ## §1 — THE OCTET-EQUALITY GATE (factory · hatchery-contract · hatchery-invariant).

The perms/VK weld (`permsVKWeldGate`) pins ONE committed authority sub-limb to ONE declared
column; the octet gate is its 8-limb GROUP form: 8 unconditional `eqGate`s pinning the published
teeth columns (row-0-PI-pinned by the regen, like the KEY_COMMIT teeth) to the committed octet
limbs. Unconditional per-descriptor — the v12 primary layout gives each material a fixed home so
each carrier's gate needs no selector (plan §2c: "each gate is unconditional per-descriptor,
which is more auditable under the anti-vacuity discipline"). -/

/-- The 8 octet-teeth equality gates: `teethPiLo + i == blockBase + octetBase + i` for `i < 8`. -/
def octetTeethGates (blockBase octetBase teethPiLo : Nat) : List VmConstraint2 :=
  (List.finRange 8).map (fun i =>
    VmConstraint2.base (.gate (eqGate (teethPiLo + i.val) (octetGroupCol blockBase octetBase i))))

/-- **`withOctetTeeth base blockBase octetBase teethPiLo`** — a descriptor PLUS the octet-teeth
weld. Constraints-only (the teeth columns are caller-owned — existing teeth cols or new TAIL
columns the regen widens for); sites/ranges/tables untouched, so every existing keystone composes
verbatim. -/
def withOctetTeeth (base : EffectVmDescriptor2) (blockBase octetBase teethPiLo : Nat) :
    EffectVmDescriptor2 :=
  { base with constraints := base.constraints ++ octetTeethGates blockBase octetBase teethPiLo }

/-- Every octet-teeth gate is a constraint of the welded descriptor. -/
theorem withOctetTeeth_mem (base : EffectVmDescriptor2) (blockBase octetBase teethPiLo : Nat)
    (i : Fin 8) :
    VmConstraint2.base (.gate (eqGate (teethPiLo + i.val) (octetGroupCol blockBase octetBase i)))
      ∈ (withOctetTeeth base blockBase octetBase teethPiLo).constraints := by
  show _ ∈ base.constraints ++ octetTeethGates blockBase octetBase teethPiLo
  exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

/-- **The generalized forcing** — any descriptor CONTAINING the octet-teeth gates forces, on every
active (non-last) row of a `Satisfied2` witness, every published tooth column EQUAL to its
committed octet limb. Stated over a `⊆`-hypothesis so single-block, both-block, and composed
descriptors all consume it. TRACE-FORCED (from `Satisfied2.rowConstraints`, never `henc`).
Field-faithful: the gates arrive `≡ 0 [ZMOD p]` (`holdsVm`); the ℤ equalities are recovered
through cell canonicality (the difference lies in `(−p, p)` and collapses). -/
theorem octetTeethGates_force (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (blockBase octetBase teethPiLo : Nat)
    (hsub : ∀ c ∈ octetTeethGates blockBase octetBase teethPiLo, c ∈ d.constraints)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash d minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    ∀ k : Fin 8, (envAt t i).loc (teethPiLo + k.val)
      = octetVals (envAt t i) blockBase octetBase k := by
  intro k
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have hin : VmConstraint2.base
      (.gate (eqGate (teethPiLo + k.val) (octetGroupCol blockBase octetBase k)))
      ∈ octetTeethGates blockBase octetBase teethPiLo :=
    List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
  have h := hsat.rowConstraints i hi _ (hsub _ hin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
  have h' : (eqGate (teethPiLo + k.val) (octetGroupCol blockBase octetBase k)).eval
      (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by simpa using h
  unfold eqGate at h'
  simp only [EmittedExpr.eval] at h'
  have := diffGate_exact (hcells _) (hcells _) h'
  show (envAt t i).loc (teethPiLo + k.val) = (envAt t i).loc (octetGroupCol blockBase octetBase k)
  linarith

/-- **`withOctetTeeth_forces`** — the single-block instantiation of the generalized forcing. -/
theorem withOctetTeeth_forces (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (blockBase octetBase teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withOctetTeeth base blockBase octetBase teethPiLo) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    ∀ k : Fin 8, (envAt t i).loc (teethPiLo + k.val)
      = octetVals (envAt t i) blockBase octetBase k :=
  octetTeethGates_force hash _ blockBase octetBase teethPiLo
    (fun _ hc => List.mem_append_right _ hc) minit mfin maddrs t hsat i hi hnotlast hcells

/-- **TOOTH — `withOctetTeeth_rejects_forged`.** A row whose published tooth diverges from the
committed octet limb (a forged `child_vk` / `contract_hash` exposure) does NOT satisfy the welded
descriptor — UNSAT for a ledgerless client, no trusted post-cell. -/
theorem withOctetTeeth_rejects_forged (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (blockBase octetBase teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) (k : Fin 8)
    (hforged : (envAt t i).loc (teethPiLo + k.val)
      ≠ octetVals (envAt t i) blockBase octetBase k) :
    ¬ Satisfied2 hash (withOctetTeeth base blockBase octetBase teethPiLo) minit mfin maddrs t :=
  fun hsat => hforged
    (withOctetTeeth_forces hash base blockBase octetBase teethPiLo minit mfin maddrs t hsat
      i hi hnotlast hcells k)

/-- **`withOctetTeethBoth`** — the BOTH-blocks weld: the same teeth pinned to the octet in the
BEFORE **and** AFTER blocks (transitively forcing before == after octet continuity through the
teeth — the completion-freeze shape for a value-turn carrier context). -/
def withOctetTeethBoth (base : EffectVmDescriptor2) (octetBase teethPiLo : Nat) :
    EffectVmDescriptor2 :=
  withOctetTeeth (withOctetTeeth base BEFORE_BLOCK_BASE octetBase teethPiLo)
    AFTER_BLOCK_BASE octetBase teethPiLo

/-- Both-blocks forcing: the teeth equal the BEFORE octet AND the AFTER octet (hence the two
committed octets agree). -/
theorem withOctetTeethBoth_forces (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (octetBase teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withOctetTeethBoth base octetBase teethPiLo) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    ∀ k : Fin 8,
      (envAt t i).loc (teethPiLo + k.val) = octetVals (envAt t i) BEFORE_BLOCK_BASE octetBase k
      ∧ (envAt t i).loc (teethPiLo + k.val) = octetVals (envAt t i) AFTER_BLOCK_BASE octetBase k := by
  intro k
  constructor
  · exact octetTeethGates_force hash _ BEFORE_BLOCK_BASE octetBase teethPiLo
      (fun _ hc => by
        show _ ∈ (withOctetTeeth base BEFORE_BLOCK_BASE octetBase teethPiLo).constraints
          ++ octetTeethGates AFTER_BLOCK_BASE octetBase teethPiLo
        exact List.mem_append_left _ (List.mem_append_right _ hc))
      minit mfin maddrs t hsat i hi hnotlast hcells k
  · exact octetTeethGates_force hash _ AFTER_BLOCK_BASE octetBase teethPiLo
      (fun _ hc => List.mem_append_right _ hc) minit mfin maddrs t hsat i hi hnotlast hcells k

/-! ### §1a — the carrier instantiations.

  * **factory** — `child_vk8` teeth on the CreateCellFromFactory descriptor: the 8 published TAIL
    teeth == the committed `effective_vk` limbs (the STEP-2 fill; kills the `child_vk_derived`
    misnomer's laundering). AFTER-block by default (the child's installed authority is
    post-state material); the regen picks via `blockBase` if the producer fills both.
  * **hatchery-invariant** — RIDES the SAME gate + octet (`invariant_digest === child_vk`,
    WELD-STATE §3): no separate keystone, instantiate `withFactoryChildVkTeeth` on its leg.
  * **hatchery-contract** — `contract_hash8` teeth on the hatchery-mint descriptor. -/

/-- Factory: the `child_vk8` octet-teeth weld (AFTER block — the child's installed authority). -/
def withFactoryChildVkTeeth (base : EffectVmDescriptor2) (teethPiLo : Nat) :
    EffectVmDescriptor2 :=
  withOctetTeeth base AFTER_BLOCK_BASE B_CHILD_VK8 teethPiLo

/-- Factory forcing: the 8 published child-vk teeth ARE the committed `child_vk8` octet. The
hatchery-invariant carrier consumes this SAME lemma on its leg (`invariant_digest === child_vk`). -/
theorem withFactoryChildVkTeeth_forces (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withFactoryChildVkTeeth base teethPiLo) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    ∀ k : Fin 8, (envAt t i).loc (teethPiLo + k.val)
      = octetVals (envAt t i) AFTER_BLOCK_BASE B_CHILD_VK8 k :=
  withOctetTeeth_forces hash base AFTER_BLOCK_BASE B_CHILD_VK8 teethPiLo
    minit mfin maddrs t hsat i hi hnotlast hcells

/-- Hatchery-contract: the `contract_hash8` octet-teeth weld (AFTER block — the attested
contract of the hatchery-mint row). -/
def withHatcheryContractTeeth (base : EffectVmDescriptor2) (teethPiLo : Nat) :
    EffectVmDescriptor2 :=
  withOctetTeeth base AFTER_BLOCK_BASE B_CONTRACT_HASH8 teethPiLo

/-- Hatchery-contract forcing: the 8 published contract-hash teeth ARE the committed
`contract_hash8` octet. -/
theorem withHatcheryContractTeeth_forces (hash : List ℤ → ℤ) (base : EffectVmDescriptor2)
    (teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withHatcheryContractTeeth base teethPiLo) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    ∀ k : Fin 8, (envAt t i).loc (teethPiLo + k.val)
      = octetVals (envAt t i) AFTER_BLOCK_BASE B_CONTRACT_HASH8 k :=
  withOctetTeeth_forces hash base AFTER_BLOCK_BASE B_CONTRACT_HASH8 teethPiLo
    minit mfin maddrs t hsat i hi hnotlast hcells

#assert_axioms octetTeethGates_force
#assert_axioms withOctetTeeth_forces
#assert_axioms withOctetTeeth_rejects_forged
#assert_axioms withOctetTeethBoth_forces
#assert_axioms withFactoryChildVkTeeth_forces
#assert_axioms withHatcheryContractTeeth_forces

-- Self-tests: shape + a biting eval pair (holds on an agreeing assignment, BITES on a forged one).
#guard (octetTeethGates 0 0 100).length == 8
private def octetTestGood : Nat → ℤ := fun n => if n ≥ 100 then ((n - 100 : Nat) : ℤ) else (n : ℤ)
private def octetTestForged : Nat → ℤ := fun n => if n == 100 then 99 else octetTestGood n
#guard (octetTeethGates 0 0 100).all (fun c =>
  match c with
  | .base (.gate g) => g.eval octetTestGood == 0
  | _ => false)
#guard (octetTeethGates 0 0 100).any (fun c =>
  match c with
  | .base (.gate g) => g.eval octetTestForged != 0
  | _ => false)

/-! ## §2 — THE COMPRESS GATE (sovereign KEY_COMMIT · membership sender-leaf).

Parametric over the ONE deployed chip absorb `A : List ℤ → Digest8`
(`descriptor_ir2::chip_absorb_all_lanes` — the same carrier `Cap8Scheme`/`Heap8Scheme`/
`Fields8Scheme` package as `chipAbsorb8`). The lookups are the standard wide tuples
(`chipLookupTupleN`), so `chip_lookup_sound_N` forces every digest lane; the teeth welds then pin
the executor-checked felts to lane 0. See the module-doc EXECUTOR-COMPRESS VERDICT: sovereign is
an EXACT match (4 × arity-4 = `hash_4_to_1` interleave); membership is chip-native `node8`
(arity-16, `pubkey8 ‖ 0⁸`) with the executor re-alignment NAMED as owed at wiring. -/

/-- The wide permutation output of a chip absorb (the `capPermOut`/`fieldsPermOut` shape). -/
def permOutOf (A : List ℤ → Digest8) : List ℤ → List ℤ := fun xs => List.ofFn (A xs)

/-! ### §2a — sovereign: the 4-felt KEY_COMMIT interleave over the committed **NONET**.

⚑ **THE NINTH LANE ENTERS THE TEETH (2026-08-08).** Until today this section read the committed
EIGHT columns `B_PUBKEY8 .. +8` and nothing else. Those eight are the base-`2^29` nonet's lanes
0..7; lane 8 — `B_PUBKEY_NINTH_LANE`, the column the key-nonet flag day allocated — was absorbed
into `state_commit` and read by the canonicity range lookup, but **no key-commit quad touched it**.
An Ed25519 key keeps its x-sign in source bit 255, which is bit 23 of lane 8 and of NO other lane,
so `A` and `−A` produced BIT-IDENTICAL KEY_COMMIT teeth: the deployed sovereign teeth could not
separate a key from its negation. `keyCommitSpec` is now a function of all nine lanes.

**The cover is full at UNCHANGED arity and UNCHANGED span.** Row 2 moves `[0,4,2,6] → [8,0,4,2]`:
still four inputs, still four quads, still `KEY_COMMIT_SPAN = 32`, still four arity-4 chip rows.
Lane 6 is retained by row 1 and lane 0 by row 0, so nothing is dropped —
`quadIdx_covers_every_lane` proves the union is all of `Fin 9` and
`quadIdx_row2_reads_the_ninth_lane` names where lane 8 enters. -/

/-- **THE NINTH LANE OF A CARRIER OCTET**, as the positional map `ROTATED_OCTET_BASES →
ROTATED_OCTET_NINTH_LANES` the emitted layout carries (Rust twin
`layout_generated::ROTATED_OCTET_NINTH_LANES`, whose positional parity with `ROTATED_OCTET_BASES`
`effect_vm::helpers::PUBKEY_NONET_LANE_COL` asserts at compile time). Each value is read from
`EffectVmEmitRotationV3`, which reads it from the verified `RotatedLayout.octetLaneCol` — this file
re-spells no coordinate.

⚠ NOT a stride. The ninth lanes sit 74–97 columns past their octets, past the whole completion
band; `octetBase + 8` is `fields[0]`'s completion window. -/
def ninthLaneOf (octetBase : Nat) : Nat :=
  if octetBase = B_CHILD_VK8 then Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_CHILD_VK_NINTH_LANE
  else if octetBase = B_CONTRACT_HASH8 then
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_CONTRACT_HASH_NINTH_LANE
  else Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_PUBKEY_NINTH_LANE

theorem ninthLaneOf_pubkey : ninthLaneOf B_PUBKEY8
    = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_PUBKEY_NINTH_LANE := by decide

theorem ninthLaneOf_childVk : ninthLaneOf B_CHILD_VK8
    = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_CHILD_VK_NINTH_LANE := by decide

theorem ninthLaneOf_contractHash : ninthLaneOf B_CONTRACT_HASH8
    = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_CONTRACT_HASH_NINTH_LANE := by decide

/-- ⚑ **THE NINTH LANE IS NOT ADJACENT TO ITS OCTET.** The one shape a reader is tempted to write
(`octetBase + 8`) lands inside the fields completion band. Stated so the temptation is refuted by a
term rather than by a comment. -/
theorem ninthLaneOf_pubkey_is_not_flush : ninthLaneOf B_PUBKEY8 ≠ B_PUBKEY8 + 8 := by decide

/-- **THE NINE COMMITTED COLUMNS of a carrier NONET** in the block based at `blockBase`: lanes 0..7
are the contiguous octet, lane 8 is [`ninthLaneOf`]. The nonet column map the KEY_COMMIT quads read
— the Lean twin of `effect_vm::helpers::PUBKEY_NONET_LANE_COL` (offset by `blockBase`). -/
def nonetLaneCol (blockBase octetBase : Nat) : Fin 9 → Nat := fun i =>
  if i.val < 8 then blockBase + octetBase + i.val else blockBase + ninthLaneOf octetBase

theorem nonetLaneCol_octet (blockBase octetBase : Nat) (i : Fin 9) (hi : i.val < 8) :
    nonetLaneCol blockBase octetBase i = octetGroupCol blockBase octetBase ⟨i.val, hi⟩ := by
  simp [nonetLaneCol, octetGroupCol, hi]

theorem nonetLaneCol_lane8 (blockBase octetBase : Nat) :
    nonetLaneCol blockBase octetBase 8 = blockBase + ninthLaneOf octetBase := by
  simp [nonetLaneCol]

/-- The committed nonet read off the row env. -/
def nonetVals (env : VmRowEnv) (blockBase octetBase : Nat) : Fin 9 → ℤ :=
  fun i => env.loc (nonetLaneCol blockBase octetBase i)

/-- Lanes 0..7 of the nonet ARE the octet this file's other gates read — the two views agree where
they overlap, so `withOctetTeeth` and `withSovereignKeyCommit` cannot drift onto different columns. -/
theorem nonetVals_octet (env : VmRowEnv) (blockBase octetBase : Nat) (i : Fin 9) (hi : i.val < 8) :
    nonetVals env blockBase octetBase i = octetVals env blockBase octetBase ⟨i.val, hi⟩ := by
  simp [nonetVals, octetVals, groupVal, nonetLaneCol_octet blockBase octetBase i hi]

/-- The KEY_COMMIT interleave matrix: quad `q`'s `j`-th input LANE of the committed nonet. Rows:
`[0,1,2,3] · [4,5,6,7] · [8,0,4,2] · [1,5,3,7]`.

⚑ Row 2's first entry is the ninth lane. It replaced a lane-6 read that row 1 already carried, so
the arity did not move and neither did the span. -/
def quadIdx (q j : Fin 4) : Fin 9 :=
  match q.val, j.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 2 | 0, 3 => 3
  | 1, 0 => 4 | 1, 1 => 5 | 1, 2 => 6 | 1, 3 => 7
  | 2, 0 => 8 | 2, 1 => 0 | 2, 2 => 4 | 2, 3 => 2
  | 3, 0 => 1 | 3, 1 => 5 | 3, 2 => 3 | 3, 3 => 7
  | _, _ => 0

/-- The four rows, named. (Ex-`#guard`s — `docs/GUARD-DISCIPLINE.md`: the Rust twin
`effect_vm::helpers::KEY_COMMIT_QUAD_IDX` is generated from this very matrix, so these are the pins
a hand-edit on either side has to survive.) -/
theorem quadIdx_row0 : (List.finRange 4).map (quadIdx 0) = ([0, 1, 2, 3] : List (Fin 9)) := by decide

theorem quadIdx_row1 : (List.finRange 4).map (quadIdx 1) = ([4, 5, 6, 7] : List (Fin 9)) := by decide

theorem quadIdx_row2 : (List.finRange 4).map (quadIdx 2) = ([8, 0, 4, 2] : List (Fin 9)) := by decide

theorem quadIdx_row3 : (List.finRange 4).map (quadIdx 3) = ([1, 5, 3, 7] : List (Fin 9)) := by decide

/-- ⚑⚑ **THE FULL COVER — the load-bearing claim of the 2026-08-08 repair.** EVERY lane of the
committed nonet is read by SOME quad. Without this the teeth are a function of a proper subset of
the committed key and two distinct keys agreeing off that subset publish identical teeth; with it,
a change in any lane changes the input list of at least one arity-4 chip row. -/
theorem quadIdx_covers_every_lane : ∀ l : Fin 9, ∃ q j : Fin 4, quadIdx q j = l := by decide

/-- …and WHERE the ninth lane enters: quad 2, input 0, and nowhere else. This is the coordinate an
Ed25519 key's x-sign (source bit 255 = lane 8 bit 23) travels through, so it is the coordinate that
separates a key from its negation. -/
theorem quadIdx_row2_reads_the_ninth_lane :
    quadIdx 2 0 = 8 ∧ (∀ q j : Fin 4, quadIdx q j = 8 → q = 2 ∧ j = 0) := by decide

/-- The arity did NOT move: every quad still absorbs exactly four lanes, so the emitted chip rows
are the same arity-4 rows the deployed table already admits and `KEY_COMMIT_SPAN` is unchanged. -/
theorem quadIdx_arity_is_four (q : Fin 4) : ((List.finRange 4).map (quadIdx q)).length = 4 := rfl

/-- Quad `q`'s 4 input column expressions, read off the committed nonet. -/
def quadCols (blockBase octetBase : Nat) (q : Fin 4) : List EmittedExpr :=
  (List.finRange 4).map (fun j => EmittedExpr.var (nonetLaneCol blockBase octetBase (quadIdx q j)))

theorem quadCols_eval (blockBase octetBase : Nat) (q : Fin 4) (env : VmRowEnv) :
    (quadCols blockBase octetBase q).map (·.eval env.loc)
      = (List.finRange 4).map
          (fun j => nonetVals env blockBase octetBase (quadIdx q j)) := by
  simp [quadCols, EmittedExpr.eval, nonetVals, List.map_map, Function.comp_def]

/-- **The executor's KEY_COMMIT function over the committed nonet** — quad `q`'s single squeezed
felt: `A (interleave q non) 0`. At `A := chip_absorb_all_lanes` this IS
`effect_vm::helpers::key_commit_teeth_from_nonet(nonet)[q]`, which is what
`TurnExecutor::pubkey_to_witness_key_commit` and
`trace_rotated::append_sovereign_key_commit_rider` BOTH call (arity-4 chip row ≡ `hash_4_to_1`,
verified — module doc). -/
def keyCommitSpec (A : List ℤ → Digest8) (non : Fin 9 → ℤ) (q : Fin 4) : ℤ :=
  A ((List.finRange 4).map (fun j => non (quadIdx q j))) 0

/-- ⚑ **THE SEPARATION, AT THE SPEC.** Any two committed nonets that differ in lane 8 — and `(A,
−A)` differ in lane 8 and NOWHERE ELSE, since an Ed25519 key's x-sign is source bit 255 — feed quad
2 two DIFFERENT input lists. So under any `A` that separates those two lists (which the chip
soundness supplies as collision resistance, not injectivity — say it at that resolution) the
published teeth differ. Under the retired `[0,4,2,6]` matrix all four quads received identical input
lists on that pair and NO hypothesis on `A` could have separated them: the teeth were a function of
lanes 0..7 alone. -/
theorem lane8_reaches_quad2_input (non non' : Fin 9 → ℤ) (h8 : non 8 ≠ non' 8) :
    (List.finRange 4).map (fun j => non (quadIdx 2 j))
      ≠ (List.finRange 4).map (fun j => non' (quadIdx 2 j)) := by
  intro h
  have h0 : non (quadIdx 2 0) = non' (quadIdx 2 0) := by
    have := congrArg (fun xs => xs.getD 0 0) h
    simpa using this
  rw [quadIdx_row2_reads_the_ninth_lane.1] at h0
  exact h8 h0

#assert_axioms ninthLaneOf_pubkey
#assert_axioms ninthLaneOf_pubkey_is_not_flush
#assert_axioms nonetVals_octet
#assert_axioms quadIdx_row0
#assert_axioms quadIdx_row1
#assert_axioms quadIdx_row2
#assert_axioms quadIdx_row3
#assert_axioms quadIdx_covers_every_lane
#assert_axioms quadIdx_row2_reads_the_ninth_lane
#assert_axioms lane8_reaches_quad2_input

/-- The 4 × 8 appendix digest-column groups (quad `q`, lane `i`) based at `dgBase`. -/
def keyCommitDigestCol (dgBase : Nat) (q : Fin 4) : Fin 8 → Nat :=
  fun i => dgBase + 8 * q.val + i.val

/-- Quad `q`'s wide chip lookup: absorb the 4 interleaved octet columns, output = the 8 bound
digest columns (the whole permutation block — the standard wide-tuple emission). -/
def keyCommitLookup (blockBase octetBase dgBase : Nat) (q : Fin 4) : Lookup :=
  { table := .poseidon2
  , tuple := chipLookupTupleN (quadCols blockBase octetBase q)
      (digestCols (keyCommitDigestCol dgBase q)) }

/-- The sovereign key-commit constraint fragment: 4 chip lookups + 4 teeth welds
(`teethPiLo + q == lane 0 of quad q's digest group`). -/
def keyCommitConstraints (blockBase octetBase dgBase teethPiLo : Nat) : List VmConstraint2 :=
  ((List.finRange 4).map (fun q =>
      VmConstraint2.lookup (keyCommitLookup blockBase octetBase dgBase q)))
  ++ ((List.finRange 4).map (fun q =>
      VmConstraint2.base (.gate (eqGate (teethPiLo + q.val) (keyCommitDigestCol dgBase q 0)))))

/-- The key-commit appendix span: 4 quads × 8 digest lanes. ⚑ UNCHANGED by the ninth-lane repair —
the cover widened from eight lanes to nine INSIDE the existing four arity-4 rows, so no column, no
table and no PI moved. -/
def KEY_COMMIT_SPAN : Nat := 32

/-- **`withSovereignKeyCommit base teethPiLo`** — a descriptor WIDENED by the key-commit appendix:
the 4 published KEY_COMMIT teeth (`SOVEREIGN_WITNESS_KEY_COMMIT`, `columns.rs` aux offsets 23..26,
row-0-pinned to PI) are forced equal to the in-AIR `key_commit_teeth_from_nonet` of the committed
BEFORE-block pubkey NONET — lanes 0..7 at `B_PUBKEY8`, lane 8 at `B_PUBKEY_NINTH_LANE` (the
OPERATED cell's owner key — `before_cell.public_key()`). -/
def withSovereignKeyCommit (base : EffectVmDescriptor2) (teethPiLo : Nat) :
    EffectVmDescriptor2 :=
  { base with
    traceWidth  := base.traceWidth + KEY_COMMIT_SPAN
    constraints := base.constraints
      ++ keyCommitConstraints BEFORE_BLOCK_BASE B_PUBKEY8 base.traceWidth teethPiLo }

/-- **The generalized key-commit forcing** — any descriptor containing the fragment forces, under
the chip-table soundness, every published KEY_COMMIT tooth EQUAL to the executor's compress of the
committed NONET: `teeth[q] = A (interleave q (committed pubkey nonet)) 0` — nine lanes, so a key
and its negation (which differ only in lane 8) cannot publish the same teeth. -/
theorem keyCommitConstraints_force (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (blockBase octetBase dgBase teethPiLo : Nat)
    (hsub : ∀ c ∈ keyCommitConstraints blockBase octetBase dgBase teethPiLo, c ∈ d.constraints)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (hsat : Satisfied2 hash d minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    ∀ q : Fin 4, (envAt t i).loc (teethPiLo + q.val)
      = keyCommitSpec A (nonetVals (envAt t i) blockBase octetBase) q := by
  intro q
  set e := envAt t i with he
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  -- the lookup forces the digest group to the genuine permutation output of the quad.
  have hlkin : VmConstraint2.lookup (keyCommitLookup blockBase octetBase dgBase q)
      ∈ keyCommitConstraints blockBase octetBase dgBase teethPiLo := by
    refine List.mem_append_left _ ?_
    exact List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩
  have hlk := hsat.rowConstraints i hi _ (hsub _ hlkin)
  have hmem : (chipLookupTupleN (quadCols blockBase octetBase q)
      (digestCols (keyCommitDigestCol dgBase q))).map (·.eval e.loc) ∈ t.tf .poseidon2 := by
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, keyCommitLookup] using hlk
  have hlen : ChipArityAdmitted (quadCols blockBase octetBase q).length := of_decide_eq_true (Eq.refl true)
  have hforce := chip_lookup_sound_N (permOutOf A) (t.tf .poseidon2) hChip e.loc
    (quadCols blockBase octetBase q) (digestCols (keyCommitDigestCol dgBase q)) hlen hmem
  rw [digestCols_map, quadCols_eval] at hforce
  have hreal : permOutOf A ((List.finRange 4).map
      (fun j => nonetVals e blockBase octetBase (quadIdx q j)))
      = List.ofFn (A ((List.finRange 4).map
          (fun j => nonetVals e blockBase octetBase (quadIdx q j)))) := rfl
  rw [hreal] at hforce
  have hgrp := List.ofFn_inj.mp hforce
  have hlane0 : e.loc (keyCommitDigestCol dgBase q 0)
      = keyCommitSpec A (nonetVals e blockBase octetBase) q := by
    have := congrFun hgrp 0
    simpa [groupVal, keyCommitSpec] using this
  -- the weld pins the tooth to lane 0.
  have hwin : VmConstraint2.base (.gate (eqGate (teethPiLo + q.val)
      (keyCommitDigestCol dgBase q 0)))
      ∈ keyCommitConstraints blockBase octetBase dgBase teethPiLo := by
    refine List.mem_append_right _ ?_
    exact List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩
  have hw := hsat.rowConstraints i hi _ (hsub _ hwin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at hw
  have hw' : (eqGate (teethPiLo + q.val) (keyCommitDigestCol dgBase q 0)).eval e.loc
      ≡ 0 [ZMOD 2013265921] := by simpa using hw
  unfold eqGate at hw'
  simp only [EmittedExpr.eval] at hw'
  have hdiff := diffGate_exact (hcells _) (hcells _) hw'
  have hweld : e.loc (teethPiLo + q.val) = e.loc (keyCommitDigestCol dgBase q 0) := by linarith
  rw [hweld, hlane0]

/-- **`withSovereignKeyCommit_forces` — THE SOVEREIGN KEYSTONE.** A `Satisfied2` of the welded
descriptor, under the chip soundness, forces the 4 published KEY_COMMIT teeth EQUAL to
`key_commit_teeth_from_nonet` (at `A := chip_absorb_all_lanes`) of the committed BEFORE pubkey
NONET — a forged owner key is UNSAT for a ledgerless client (P1 + P2 together, no laundered
vacuity), and since 2026-08-08 that includes a key swapped for its NEGATION, which lane 8 is the
only committed column to see. -/
theorem withSovereignKeyCommit_forces (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (base : EffectVmDescriptor2) (teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (withSovereignKeyCommit base teethPiLo) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    ∀ q : Fin 4, (envAt t i).loc (teethPiLo + q.val)
      = keyCommitSpec A (nonetVals (envAt t i) BEFORE_BLOCK_BASE B_PUBKEY8) q :=
  keyCommitConstraints_force A hash _ BEFORE_BLOCK_BASE B_PUBKEY8 base.traceWidth teethPiLo
    (fun _ hc => List.mem_append_right _ hc) minit mfin maddrs t hChip hsat i hi hnotlast hcells

/-- **TOOTH — `withSovereignKeyCommit_rejects_forged`.** A row whose published KEY_COMMIT tooth is
NOT the compress of the committed pubkey NONET (a forged sovereign key — including the negation of
the honest one) is UNSAT. -/
theorem withSovereignKeyCommit_rejects_forged (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (base : EffectVmDescriptor2) (teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) (q : Fin 4)
    (hforged : (envAt t i).loc (teethPiLo + q.val)
      ≠ keyCommitSpec A (nonetVals (envAt t i) BEFORE_BLOCK_BASE B_PUBKEY8) q) :
    ¬ Satisfied2 hash (withSovereignKeyCommit base teethPiLo) minit mfin maddrs t :=
  fun hsat => hforged
    (withSovereignKeyCommit_forces A hash base teethPiLo minit mfin maddrs t hChip hsat
      i hi hnotlast hcells q)

/-- **THE PEEL — `Satisfied2 (withSovereignKeyCommit base teethPiLo) ⟹ Satisfied2 base`.** The
key-commit compose only APPENDS constraints (4 chip lookups + 4 teeth-weld gates) and widens
`traceWidth` (which `Satisfied2` never reads): the inner constraints stay members
(`List.mem_append_left`), the sites / ranges are the record-update-inherited `base` fields, and the
appended fragment contributes NO mem/map op — so every existing per-effect soundness lemma lifts to
the composed descriptor by peeling the compose first. The `withSovereignKeyCommit` analog of
`effFieldsWriteV3_satisfied2_strips_to_base` (the deployed-refusal precedent); the missing lemma the
big-bang registry re-key needed. -/
theorem satisfied2_of_withSovereignKeyCommit (hash : List ℤ → ℤ)
    (base : EffectVmDescriptor2) (teethPiLo : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash (withSovereignKeyCommit base teethPiLo) minit mfin maddrs t) :
    Satisfied2 hash base minit mfin maddrs t := by
  have hmapOps : Dregg2.Circuit.DescriptorIR2.mapOpsOf (withSovereignKeyCommit base teethPiLo)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf base := by
    simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, withSovereignKeyCommit, keyCommitConstraints,
      List.filterMap_append, List.filterMap_map]
  have hmemOps : Dregg2.Circuit.DescriptorIR2.memOpsOf (withSovereignKeyCommit base teethPiLo)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf base := by
    simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, withSovereignKeyCommit, keyCommitConstraints,
      List.filterMap_append, List.filterMap_map]
  have hmemLog : Dregg2.Circuit.DescriptorIR2.memLog (withSovereignKeyCommit base teethPiLo) t
      = Dregg2.Circuit.DescriptorIR2.memLog base t := by
    simp [Dregg2.Circuit.DescriptorIR2.memLog, hmemOps]
  have hmapLog : Dregg2.Circuit.DescriptorIR2.mapLog (withSovereignKeyCommit base teethPiLo) t
      = Dregg2.Circuit.DescriptorIR2.mapLog base t := by
    simp [Dregg2.Circuit.DescriptorIR2.mapLog, hmapOps]
  exact
    { rowConstraints := fun i hi c hc =>
        h.rowConstraints i hi c (by
          show c ∈ base.constraints
            ++ keyCommitConstraints BEFORE_BLOCK_BASE B_PUBKEY8 base.traceWidth teethPiLo
          exact List.mem_append_left _ hc)
      rowHashes := h.rowHashes
      rowRanges := h.rowRanges
      memAddrsNodup := h.memAddrsNodup
      memClosed := by have := h.memClosed; rwa [hmemLog] at this
      memDisciplined := by have := h.memDisciplined; rwa [hmemLog] at this
      memBalanced := by have := h.memBalanced; rwa [hmemLog] at this
      memTableFaithful := by have := h.memTableFaithful; rwa [hmemLog] at this
      mapTableFaithful := by have := h.mapTableFaithful; rwa [hmapLog] at this }

#assert_axioms satisfied2_of_withSovereignKeyCommit

/-! ### §2b — membership: the 1-felt sender-leaf compress (chip-native `node8` form).

⚑ NAMED MISMATCH — **CLOSED 2026-08-01, and this block was STALE FOR WEEKS.**

`turn/src/executor/membership_verifier.rs:95-97` is `dregg_commit::typed::compress_member` — chip-native
lane 0 of the arity-16 `node8` absorb, i.e. exactly `pubkeyCompress1Spec`. Its own doc at `:88-94`
records that it REPLACED the `hash_many(encode_hash(bytes))` two-permutation sponge. So the gate below
already realizes the deployed function, and the executor re-alignment this block scoped as future work
is **done**.

⚠ This stale paragraph cost real work: it was quoted as the blocker in a brief that would have taken a
VK epoch to fix a mismatch that no longer existed. **The refutation was two lines, in the very file this
paragraph accuses.** A doc-comment naming a mismatch is a claim with a date on it.

⚠ What actually blocks the LEAF leg is different and still open: `B_PUBKEY_OCTET` carries the operated
cell's OWNER key (`turn/src/rotation_witness.rs:560-561`) while `SenderAuthorized` exists to authorize a
sender who is NOT the owner, and the executor compresses `PredicateInput::Sender`
(`membership_verifier.rs:208`). The leg needs a committed SENDER-pubkey octet — the twin of the owner
fill — and nothing else. -/

/-- The arity-16 `node8`-form input block: the 8 committed octet columns ‖ 8 literal zeros. -/
def pubkeyNode8Inputs (blockBase octetBase : Nat) : List EmittedExpr :=
  ((List.finRange 8).map (fun i => EmittedExpr.var (octetGroupCol blockBase octetBase i)))
    ++ List.replicate 8 (EmittedExpr.const 0)

theorem pubkeyNode8Inputs_eval (blockBase octetBase : Nat) (env : VmRowEnv) :
    (pubkeyNode8Inputs blockBase octetBase).map (·.eval env.loc)
      = List.ofFn (octetVals env blockBase octetBase) ++ List.replicate 8 0 := by
  simp only [pubkeyNode8Inputs, List.map_append, List.map_map]
  rfl

/-- **The chip-native 1-felt pubkey compress** — lane 0 of the arity-16 `node8` absorb over
`oct ‖ 0⁸`. The executor-side function membership must re-align to (or a `hash_many` chip
capability added) at wiring time — see the module-doc verdict. -/
def pubkeyCompress1Spec (A : List ℤ → Digest8) (oct : Digest8) : ℤ :=
  A (List.ofFn oct ++ List.replicate 8 0) 0

/-- The 8 appendix digest columns of the compress lookup, based at `dgBase`. -/
def pubkeyCompressDigestCol (dgBase : Nat) : Fin 8 → Nat := fun i => dgBase + i.val

/-- The compress chip lookup: absorb `pubkey8 ‖ 0⁸` (arity 16 = the `node8` full-seed row — every
committed limb enters the state), output = the 8 bound digest columns. -/
def pubkeyCompressLookup (blockBase octetBase dgBase : Nat) : Lookup :=
  { table := .poseidon2
  , tuple := chipLookupTupleN (pubkeyNode8Inputs blockBase octetBase)
      (digestCols (pubkeyCompressDigestCol dgBase)) }

/-- The membership compress fragment: 1 chip lookup + 1 leaf-teeth weld. -/
def pubkeyCompressConstraints (blockBase octetBase dgBase leafTeethCol : Nat) :
    List VmConstraint2 :=
  [ VmConstraint2.lookup (pubkeyCompressLookup blockBase octetBase dgBase)
  , VmConstraint2.base (.gate (eqGate leafTeethCol (pubkeyCompressDigestCol dgBase 0))) ]

/-- The compress appendix span: one 8-lane digest group. -/
def PUBKEY_COMPRESS_SPAN : Nat := 8

/-- **`withMembershipPubkeyCompress base leafTeethCol`** — a descriptor WIDENED by the compress
appendix: the published sender-leaf tooth == the in-AIR compress of the committed BEFORE-block
pubkey octet (the turn actor's key — plan O1(a): one turn-level `pubkey8`, absorbed per block). -/
def withMembershipPubkeyCompress (base : EffectVmDescriptor2) (leafTeethCol : Nat) :
    EffectVmDescriptor2 :=
  { base with
    traceWidth  := base.traceWidth + PUBKEY_COMPRESS_SPAN
    constraints := base.constraints
      ++ pubkeyCompressConstraints BEFORE_BLOCK_BASE B_PUBKEY8 base.traceWidth leafTeethCol }

/-- **The generalized compress forcing** — any descriptor containing the fragment forces, under
the chip soundness, the published leaf tooth EQUAL to the chip-native compress of the committed
octet. -/
theorem pubkeyCompressConstraints_force (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (blockBase octetBase dgBase leafTeethCol : Nat)
    (hsub : ∀ c ∈ pubkeyCompressConstraints blockBase octetBase dgBase leafTeethCol,
      c ∈ d.constraints)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (hsat : Satisfied2 hash d minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    (envAt t i).loc leafTeethCol
      = pubkeyCompress1Spec A (octetVals (envAt t i) blockBase octetBase) := by
  set e := envAt t i with he
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have hlkin : VmConstraint2.lookup (pubkeyCompressLookup blockBase octetBase dgBase)
      ∈ pubkeyCompressConstraints blockBase octetBase dgBase leafTeethCol :=
    List.mem_cons_self
  have hlk := hsat.rowConstraints i hi _ (hsub _ hlkin)
  have hmem : (chipLookupTupleN (pubkeyNode8Inputs blockBase octetBase)
      (digestCols (pubkeyCompressDigestCol dgBase))).map (·.eval e.loc) ∈ t.tf .poseidon2 := by
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, pubkeyCompressLookup] using hlk
  have hlen : ChipArityAdmitted (pubkeyNode8Inputs blockBase octetBase).length := of_decide_eq_true (Eq.refl true)
  have hforce := chip_lookup_sound_N (permOutOf A) (t.tf .poseidon2) hChip e.loc
    (pubkeyNode8Inputs blockBase octetBase) (digestCols (pubkeyCompressDigestCol dgBase))
    hlen hmem
  rw [digestCols_map, pubkeyNode8Inputs_eval] at hforce
  have hreal : permOutOf A (List.ofFn (octetVals e blockBase octetBase) ++ List.replicate 8 0)
      = List.ofFn (A (List.ofFn (octetVals e blockBase octetBase) ++ List.replicate 8 0)) := rfl
  rw [hreal] at hforce
  have hgrp := List.ofFn_inj.mp hforce
  have hlane0 : e.loc (pubkeyCompressDigestCol dgBase 0)
      = pubkeyCompress1Spec A (octetVals e blockBase octetBase) := by
    have := congrFun hgrp 0
    simpa [groupVal, pubkeyCompress1Spec] using this
  have hwin : VmConstraint2.base (.gate (eqGate leafTeethCol (pubkeyCompressDigestCol dgBase 0)))
      ∈ pubkeyCompressConstraints blockBase octetBase dgBase leafTeethCol := by
    simp [pubkeyCompressConstraints]
  have hw := hsat.rowConstraints i hi _ (hsub _ hwin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at hw
  have hw' : (eqGate leafTeethCol (pubkeyCompressDigestCol dgBase 0)).eval e.loc
      ≡ 0 [ZMOD 2013265921] := by simpa using hw
  unfold eqGate at hw'
  simp only [EmittedExpr.eval] at hw'
  have hdiff := diffGate_exact (hcells _) (hcells _) hw'
  have hweld : e.loc leafTeethCol = e.loc (pubkeyCompressDigestCol dgBase 0) := by linarith
  rw [hweld, hlane0]

/-- **`withMembershipPubkeyCompress_forces` — THE MEMBERSHIP-SENDER KEYSTONE.** A `Satisfied2` of
the welded descriptor forces the published sender-leaf tooth EQUAL to the chip-native compress of
the committed pubkey octet — a forged sender key is UNSAT (modulo the NAMED executor
re-alignment, module doc). -/
theorem withMembershipPubkeyCompress_forces (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (base : EffectVmDescriptor2) (leafTeethCol : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (withMembershipPubkeyCompress base leafTeethCol) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    (envAt t i).loc leafTeethCol
      = pubkeyCompress1Spec A (octetVals (envAt t i) BEFORE_BLOCK_BASE B_PUBKEY8) :=
  pubkeyCompressConstraints_force A hash _ BEFORE_BLOCK_BASE B_PUBKEY8 base.traceWidth
    leafTeethCol (fun _ hc => List.mem_append_right _ hc) minit mfin maddrs t hChip hsat
    i hi hnotlast hcells

/-- **TOOTH — `withMembershipPubkeyCompress_rejects_forged`.** -/
theorem withMembershipPubkeyCompress_rejects_forged (A : List ℤ → Digest8) (hash : List ℤ → ℤ)
    (base : EffectVmDescriptor2) (leafTeethCol : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (permOutOf A) (t.tf .poseidon2))
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (hforged : (envAt t i).loc leafTeethCol
      ≠ pubkeyCompress1Spec A (octetVals (envAt t i) BEFORE_BLOCK_BASE B_PUBKEY8)) :
    ¬ Satisfied2 hash (withMembershipPubkeyCompress base leafTeethCol) minit mfin maddrs t :=
  fun hsat => hforged
    (withMembershipPubkeyCompress_forces A hash base leafTeethCol minit mfin maddrs t hChip hsat
      i hi hnotlast hcells)

#assert_axioms keyCommitConstraints_force
#assert_axioms withSovereignKeyCommit_forces
#assert_axioms withSovereignKeyCommit_rejects_forged
#assert_axioms pubkeyCompressConstraints_force
#assert_axioms withMembershipPubkeyCompress_forces
#assert_axioms withMembershipPubkeyCompress_rejects_forged

-- Shape pins: tuple shapes (the 25-wide chip tuple: 1 arity + CHIP_RATE inputs + 8 lanes) and
-- fragment sizes. ⚑ The key-commit fragment is UNCHANGED in every one of these by the ninth-lane
-- repair — that is the claim "full cover at unchanged arity and unchanged span" cashed out.
theorem keyCommitLookup_tuple_len (blockBase octetBase dgBase : Nat) (q : Fin 4) :
    (keyCommitLookup blockBase octetBase dgBase q).tuple.length = 25 := rfl

theorem pubkeyCompressLookup_tuple_len (blockBase octetBase dgBase : Nat) :
    (pubkeyCompressLookup blockBase octetBase dgBase).tuple.length = 25 := rfl

theorem keyCommitConstraints_len (blockBase octetBase dgBase teethPiLo : Nat) :
    (keyCommitConstraints blockBase octetBase dgBase teethPiLo).length = 8 := rfl

theorem pubkeyCompressConstraints_len (blockBase octetBase dgBase leafTeethCol : Nat) :
    (pubkeyCompressConstraints blockBase octetBase dgBase leafTeethCol).length = 2 := rfl

theorem pubkeyNode8Inputs_len (blockBase octetBase : Nat) :
    (pubkeyNode8Inputs blockBase octetBase).length = 16 := rfl

/-- A concrete `keyCommitSpec` evaluation on the identity nonet under a summing `A`. The point is
that it BITES: `12` was the answer under the retired `[0,4,2,6]` matrix and `14` is the answer under
`[8,0,4,2]`, so a silent revert to eight lanes fails here. -/
theorem keyCommitSpec_quad2_on_identity_nonet :
    keyCommitSpec (fun xs _ => xs.sum) (fun i => (i.val : ℤ)) 2 = 14 := by decide

theorem keyCommitSpec_quad3_on_identity_nonet :
    keyCommitSpec (fun xs _ => xs.sum) (fun i => (i.val : ℤ)) 3 = 16 := by decide

/-- ⚑ **AND IT SEPARATES A KEY FROM ITS NEGATION, computably.** Two nonets identical on lanes 0..7
and differing only in lane 8 — the shape `(A, −A)` presents — publish DIFFERENT quad-2 teeth under
the summing `A`. Under the retired matrix both sides were `12`. This is the exhibit at the spec; the
exhibit at the deployed prover is `circuit-prove/tests/sovereign_key_negation_teeth_separate.rs`. -/
theorem keyCommitSpec_separates_a_lane8_flip :
    keyCommitSpec (fun xs _ => xs.sum) (fun i => (i.val : ℤ)) 2
      ≠ keyCommitSpec (fun xs _ => xs.sum)
          (fun i => if i = 8 then (9 : ℤ) else (i.val : ℤ)) 2 := by decide

theorem pubkeyCompress1Spec_on_identity_octet :
    pubkeyCompress1Spec (fun xs _ => xs.sum) (fun i => (i.val : ℤ)) = 28 := by decide

#assert_axioms keyCommitConstraints_len
#assert_axioms keyCommitSpec_quad2_on_identity_nonet
#assert_axioms keyCommitSpec_separates_a_lane8_flip

/-! ## §3 — THE FIELDS-ROOT READ-OPEN (membership `authorized_root`).

NOT geometry (plan O3): `fields_root` (limb `B_FIELDS_ROOT` = 36 + completions) is ALREADY a
committed-faithful 8-felt root; the authorized-set root is a fields-map VALUE under it. The gate
is the EXISTING fields-open READ appendix (`fieldsOpenConstraints` — leaf lookup, 16 shared
`node8` levels, dir booleanity, root pin) plus three welds: the appendix root group == the
committed BEFORE `fields_root` block (`beforeRootWeldsF`, reused verbatim), the read leaf's addr
== the declared `set_root_index` column, and the read leaf's VALUE == the published root-teeth
column. -/

/-- **`fieldsReadAt8 S8 root k v`** — the faithful 8-felt fields-map READ: some LINKED IMT leaf
`(k, v, next)` membership-authenticates the `(k, v)` map entry under the ~124-bit `root` (the IMT
pointer is existential at the map level). The read twin of `fieldsWritesTo8`. -/
def fieldsReadAt8 (S8 : Fields8Scheme) (root : Digest8) (k v : ℤ) : Prop :=
  ∃ (next : ℤ) (path : List (StepG Digest8)),
    recomposeUp8 S8 (fieldsLeafDigest8 S8 (k, v, next)) path = root

/-- The three read-open welds: 8 before-root pins (reused `beforeRootWeldsF`) + the key bind
(`leaf 0 == idxCol`, the declared `set_root_index` column) + the value expose (`leaf 1 ==
rootTeethCol`, the published authorized-root tooth). -/
def fieldsReadOpenWelds (w idxCol rootTeethCol : Nat) : List VmConstraint2 :=
  beforeRootWeldsF w
  ++ [ VmConstraint2.base (.gate (eqGate ((capOpenCols w).leaf 0) idxCol))
     , VmConstraint2.base (.gate (eqGate ((capOpenCols w).leaf 1) rootTeethCol)) ]

/-- **`effFieldsReadOpenV3 base name idxCol rootTeethCol`** — the fields-open READ descriptor:
`effFieldsOpenV3` (the read appendix, width `+CAP_OPEN_SPAN`) plus the read-open welds. -/
def effFieldsReadOpenV3 (base : EffectVmDescriptor2) (name : String)
    (idxCol rootTeethCol : Nat) : EffectVmDescriptor2 :=
  { effFieldsOpenV3 base name with
    constraints := (effFieldsOpenV3 base name).constraints
      ++ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol }

/-- Every read-open weld is a constraint of the descriptor. -/
theorem effFieldsReadOpenV3_weldMem (base : EffectVmDescriptor2) (name : String)
    (idxCol rootTeethCol : Nat) (c : VmConstraint2)
    (hc : c ∈ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol) :
    c ∈ (effFieldsReadOpenV3 base name idxCol rootTeethCol).constraints :=
  List.mem_append_right _ hc

/-- A `Satisfied2` of the read-open descriptor strips to a `Satisfied2` of the bare
`effFieldsOpenV3` — the welds are all `.base (.gate …)`, contributing no map/mem op. -/
theorem effFieldsReadOpenV3_strips_to_fieldsOpen (hash : List ℤ → ℤ)
    (base : EffectVmDescriptor2) (name : String) (idxCol rootTeethCol : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2 hash (effFieldsReadOpenV3 base name idxCol rootTeethCol)
      minit mfin maddrs t) :
    Satisfied2 hash (effFieldsOpenV3 base name) minit mfin maddrs t := by
  have hmapOps : Dregg2.Circuit.DescriptorIR2.mapOpsOf
        (effFieldsReadOpenV3 base name idxCol rootTeethCol)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf (effFieldsOpenV3 base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.mapOpsOf, effFieldsReadOpenV3, fieldsReadOpenWelds,
      Dregg2.Circuit.Emit.FieldsOpenEmit.beforeRootWeldsF,
      List.filterMap_append, List.filterMap_map]
  have hmemOps : Dregg2.Circuit.DescriptorIR2.memOpsOf
        (effFieldsReadOpenV3 base name idxCol rootTeethCol)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf (effFieldsOpenV3 base name) := by
    simp [Dregg2.Circuit.DescriptorIR2.memOpsOf, effFieldsReadOpenV3, fieldsReadOpenWelds,
      Dregg2.Circuit.Emit.FieldsOpenEmit.beforeRootWeldsF,
      List.filterMap_append, List.filterMap_map]
  have hmemLog : Dregg2.Circuit.DescriptorIR2.memLog
        (effFieldsReadOpenV3 base name idxCol rootTeethCol) t
      = Dregg2.Circuit.DescriptorIR2.memLog (effFieldsOpenV3 base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.memLog, hmemOps]
  have hmapLog : Dregg2.Circuit.DescriptorIR2.mapLog
        (effFieldsReadOpenV3 base name idxCol rootTeethCol) t
      = Dregg2.Circuit.DescriptorIR2.mapLog (effFieldsOpenV3 base name) t := by
    simp [Dregg2.Circuit.DescriptorIR2.mapLog, hmapOps]
  exact
    { rowConstraints := fun i hi c hc =>
        h.rowConstraints i hi c (by
          show c ∈ (effFieldsOpenV3 base name).constraints
            ++ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol
          exact List.mem_append_left _ hc)
      rowHashes := h.rowHashes
      rowRanges := h.rowRanges
      memAddrsNodup := h.memAddrsNodup
      memClosed := by have := h.memClosed; rwa [hmemLog] at this
      memDisciplined := by have := h.memDisciplined; rwa [hmemLog] at this
      memBalanced := by have := h.memBalanced; rwa [hmemLog] at this
      memTableFaithful := by have := h.memTableFaithful; rwa [hmemLog] at this
      mapTableFaithful := by have := h.mapTableFaithful; rwa [hmapLog] at this }

/-- Any read-open weld gate forces `eval ≡ 0 [ZMOD p]` on an active (non-last) row — the
field-faithful consequence (`holdsVm` binds under `when_transition`, reduced by `hlastf`). -/
theorem fieldsReadOpen_gate_forces (base : EffectVmDescriptor2) (name : String)
    (idxCol rootTeethCol : Nat) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (effFieldsReadOpenV3 base name idxCol rootTeethCol)
      minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (g : EmittedExpr)
    (hin : VmConstraint2.base (.gate g)
      ∈ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have h := hsat.rowConstraints i hi _
    (effFieldsReadOpenV3_weldMem base name idxCol rootTeethCol _ hin)
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlastf] at h
  simpa using h

/-- A read-open COLUMN weld (`eqGate a b`) forces the ℤ equality `loc a = loc b` on an active row,
under cell canonicality: the mod-`p` congruence's residual lies in `(−p, p)` and collapses. -/
theorem fieldsReadOpen_eqGate_forces (base : EffectVmDescriptor2) (name : String)
    (idxCol rootTeethCol : Nat) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (effFieldsReadOpenV3 base name idxCol rootTeethCol)
      minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (a b : Nat)
    (hin : VmConstraint2.base (.gate (eqGate a b))
      ∈ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol) :
    (envAt t i).loc a = (envAt t i).loc b := by
  have h := fieldsReadOpen_gate_forces base name idxCol rootTeethCol hash minit mfin maddrs t
    hsat i hi hnotlast _ hin
  unfold eqGate at h
  simp only [EmittedExpr.eval] at h
  have := diffGate_exact (hcells a) (hcells b) h
  linarith

/-- **`effFieldsReadOpenV3_forces_read8` — THE MEMBERSHIP-ROOT KEYSTONE.** A `Satisfied2` of the
read-open descriptor TRACE-FORCES: the published root-teeth felt IS the fields-map value at the
declared `set_root_index`, membership-authenticated under the committed BEFORE ~124-bit
`fields_root` block. A forged authorized-root tooth (any value NOT under the committed fields
root at that key) is UNSAT for a ledgerless client. -/
theorem effFieldsReadOpenV3_forces_read8 (S8 : Fields8Scheme)
    (base : EffectVmDescriptor2) (name : String) (idxCol rootTeethCol : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effFieldsReadOpenV3 base name idxCol rootTeethCol)
      minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921) :
    fieldsReadAt8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols (envAt t i))
      ((envAt t i).loc idxCol) ((envAt t i).loc rootTeethCol) := by
  set e := envAt t i with he
  -- the read core (leaf lookup, node lookups, dir booleanity, root pin) via the strip.
  have hstrip := effFieldsReadOpenV3_strips_to_fieldsOpen hash base name idxCol rootTeethCol
    minit mfin maddrs t hsat
  have hcore : FieldsMembershipCore t.tf (capOpenCols base.traceWidth) e :=
    effFieldsOpenV3_core base name hash minit mfin maddrs t hstrip i hi hnotlast hcells
  have hrec := fieldsOpen_recompose8 S8 t.tf (capOpenCols base.traceWidth) e hChip hcore
  -- weld: the appendix root group IS the committed BEFORE fields-root block.
  have hroot : groupVal e (capOpenCols base.traceWidth).capRoot
      = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols e := by
    funext k
    have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols base.traceWidth).capRoot k)
        (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.fieldsRootGroupCol EFFECT_VM_WIDTH k)))
        ∈ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol := by
      refine List.mem_append_left _ ?_
      exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩
    have := fieldsReadOpen_eqGate_forces base name idxCol rootTeethCol hash minit mfin maddrs t
      hsat i hi hnotlast hcells _ _ hin
    simpa [groupVal, Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols] using this
  -- weld: the read leaf's addr is the declared set_root_index column.
  have hidx : e.loc ((capOpenCols base.traceWidth).leaf 0) = e.loc idxCol := by
    have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols base.traceWidth).leaf 0) idxCol))
        ∈ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol := by
      refine List.mem_append_right _ ?_
      simp
    exact fieldsReadOpen_eqGate_forces base name idxCol rootTeethCol hash minit mfin maddrs t
      hsat i hi hnotlast hcells _ _ hin
  -- weld: the read leaf's value is the published root-teeth column.
  have hval : e.loc ((capOpenCols base.traceWidth).leaf 1) = e.loc rootTeethCol := by
    have hin : VmConstraint2.base (.gate (eqGate ((capOpenCols base.traceWidth).leaf 1)
        rootTeethCol))
        ∈ fieldsReadOpenWelds base.traceWidth idxCol rootTeethCol := by
      refine List.mem_append_right _ ?_
      simp
    exact fieldsReadOpen_eqGate_forces base name idxCol rootTeethCol hash minit mfin maddrs t
      hsat i hi hnotlast hcells _ _ hin
  -- assemble the read: the IMT pointer (leaf col 2) is the existential `next` witness.
  have htriple : fieldsLeafTripleOf (capOpenCols base.traceWidth) e
      = (e.loc idxCol, e.loc rootTeethCol, e.loc ((capOpenCols base.traceWidth).leaf 2)) := by
    unfold Dregg2.Circuit.Emit.FieldsOpenEmit.fieldsLeafTripleOf
    rw [hidx, hval]
  rw [htriple, hroot] at hrec
  exact ⟨e.loc ((capOpenCols base.traceWidth).leaf 2),
    pathOf8 (capOpenCols base.traceWidth) e DEPTH, hrec⟩

/-- **TOOTH — `effFieldsReadOpenV3_rejects_nonmember`.** If NO path authenticates the published
`(set_root_index, root-teeth)` pair under the committed fields root, the descriptor is UNSAT. -/
theorem effFieldsReadOpenV3_rejects_nonmember (S8 : Fields8Scheme)
    (base : EffectVmDescriptor2) (name : String) (idxCol rootTeethCol : Nat)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (t.tf .poseidon2))
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2013265921)
    (hnon : ¬ fieldsReadAt8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols (envAt t i))
      ((envAt t i).loc idxCol) ((envAt t i).loc rootTeethCol)) :
    ¬ Satisfied2 hash (effFieldsReadOpenV3 base name idxCol rootTeethCol) minit mfin maddrs t :=
  fun hsat => hnon
    (effFieldsReadOpenV3_forces_read8 S8 base name idxCol rootTeethCol hash minit mfin maddrs t
      hChip hsat i hi hnotlast hcells)

#assert_axioms effFieldsReadOpenV3_strips_to_fieldsOpen
#assert_axioms fieldsReadOpen_gate_forces
#assert_axioms effFieldsReadOpenV3_forces_read8
#assert_axioms effFieldsReadOpenV3_rejects_nonmember

-- Self-tests: the weld fragment carries exactly 8 root pins + 2 binds.
#guard (fieldsReadOpenWelds 500 1 2).length == 10

end Dregg2.Circuit.Emit.CarrierOctetGates
