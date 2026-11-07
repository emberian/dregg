/-
# Dregg2.Circuit.Emit.ShieldedWideValueLinkDescriptor — the WIDE (8-felt) value binding:
# residual #17's STRUCTURAL half, in the AIR.

**This is Lean-authored AIR.** This module authors the algebra; Rust parses the emitted IR2
bytes and supplies witnesses — it constructs no constraints. It is the §D STRUCTURAL lane the
spend-circuit port named (`ShieldedSpendPortResidual` §D / "Named residual"): the deployed
`value_binding` is a ONE-FELT (~31-bit) Poseidon2 squeeze (`spend_circuit.rs` C7a,
`hash_fact(value, [asset, randomness, 0])`), and a 1-felt tag over a `u64 × u64 × felt`
opening space is STRUCTURALLY collidable — `narrow_binding_collision_exists` below PROVES
(pigeonhole, no crypto) that EVERY BabyBear-bounded 1-felt binding admits two distinct
canonical openings with the same tag; a birthday search finds one in ~2^15.5 queries. This
module widens the binding to the FULL 8-lane Poseidon2 squeeze over a faithful multi-limb
value/asset encoding, so forging a binding requires a genuine wide-Poseidon2 collision.

## What this descriptor IS (`shieldedWideValueLinkDesc`)

One clearing slot per trace row, the WIDE twin of `shieldedValueLinkDesc` (lane 2). Per row,
from the SAME witness cells:

* **(a) faithful multi-limb inputs.** `value` and `asset` each ride FOUR 16-bit limbs
  (`wide_value_binding.rs` `U64_LIMBS`/`LIMB_BITS`), range-checked IN the descriptor
  (`ranges`, the range-table tooth) — the full `u64` is representable, nothing aliases mod p
  before hashing. Two recomposition gates pin the compatibility felts
  `value_mod_p = Σ 2^{16i}·v_i`, `asset_mod_p = Σ 2^{16i}·a_i` (the `u64_recompose` shape).
* **(b) the WIDE value binding, chip-bound.** An 8-lane wide chip lookup
  (`chipLookupTupleN` — the `chip_lookup_sound_N` wide lever, Phase B-ROTATION) forces the 8
  digest columns to the FULL squeezed output `permOut [DOMAIN, v0..v3, a0..a3, randomness, 0]`
  of the genuine permutation (domain-separated: `"VBN0"`, `wide_value_binding.rs:47`; the
  trailing zero lands the site on the chip AIR's arity-11 row, the `wireCommitR8` final-chunk
  discipline). All 8 lanes are PI-pinned — the published binding IS 8 felts.
* **(c) the leaf link.** `leaf_commit = hash_fact(value_mod_p, [asset_mod_p, owner,
  randomness])` stays the deployed narrow fact site (the note tree is the narrow tree until
  the Ristretto-retire deploy), over the SAME recomposed cells — so the wide binding and the
  membership leaf share ONE opening; the narrow hash is the HEAD (lane 0) of the same
  permutation (`headHash`), exactly the deployed `hash_many` = `state[0]` relationship.
* **(d) Σ-conservation over the multi-limb value.** The cumulative column folds
  `value_mod_p − out_val` — and `value_mod_p` is (a)'s recomposition of exactly the limbs the
  WIDE digest absorbs, so the conserved value is the value the 8-felt binding binds. No
  second free value to decouple.

## What is PROVED here

* **`wide_value_link_bound`** — the keystone, `value_link_bound` re-derived over the 8-felt
  binding: a `Satisfied2` trace forces, on EVERY row, the 8 wide-binding cells to the genuine
  full-width squeeze of the limb cells, the leaf commit to the genuine narrow fact digest of
  the SAME recomposed cells, both recompositions, and 16-bit-canonical limbs; row 0 pins all
  8 binding lanes + the leaf to the PIs.
* **`wide_conservation_holds` / `wide_mint_unbalanced_unsat`** — the in-AIR Σ-fold over the
  recomposed multi-limb value ≡ Σ out (mod p), and the mint tooth.
* **`wide_decoupled_unsat`** — publishing a lane-0 PI that is not the genuine wide digest of
  the leaf's own limbs is UNSAT.
* **`narrow_binding_collision_exists`** — THE STRUCTURAL REFUTATION of the 1-felt shape:
  every BabyBear-bounded 1-felt binding has two DISTINCT canonical openings with equal tags
  (pigeonhole over 2^32 openings vs p < 2^31 tags; the birthday attack finds such a pair in
  ~2^15.5). No hypothesis — the narrow floor is not weak, it is UNSATISFIABLE.
* **`wide_binding_binds`** — THE PAYOFF: under the NAMED wide floor (`WideBindingCR`), two
  satisfying traces publishing the SAME 8-felt binding open the SAME (value-limbs,
  asset-limbs, randomness) — same `u64` value — so their conserved values agree.
  **`birthday_collision_no_longer_forges`** composes the two: every 1-felt binding admits a
  canonical collision pair, and on ANY such pair the 8-felt binding still separates.

## The NAMED floor (legitimate, and shown non-vacuous)

`WideBindingCR permOut` — injectivity of the 8-lane squeeze ON CANONICAL OPENINGS ONLY
(limbs < 2^16, randomness < p). This is deliberately NOT the deleted-FALSE
`Poseidon2WideCR` (`∀ xs ys` over infinite `List ℤ` — pigeonhole-refuted,
VACUITY-SWEEP FINDING 2): the canonical opening space has ~2^159 elements while the 8-felt
range has ~p^8 ≈ 2^248, so counting does NOT refute this floor —
`wideBindingCR_satisfiable` exhibits a width-8 inhabitant (`packPerm`), where the SAME
statement at 1 felt is REFUTED outright by `narrow_binding_collision_exists`. That is the
entire point of the widening. For real Poseidon2 the floor is standard wide-output CR
(collisions exist beyond the canonical domain; finding a canonical-domain collision is the
priced game — `InjectiveFloorRegrounded.wireCommitR8_binds_advantage_bound` is the
advantage-bounded form of the same family).

## What this lane does NOT close (named honestly)

* **The Ristretto-retire deploy** (#17's other half): retiring `commit_hidden_asset`
  (Shor-broken DLog) and routing `apply_shielded_transfer` through the ring-clearing apex is
  Rust + descriptor-JSON golden regen + VK regen — the deploy lane, NOT this file.
* The NOTE TREE is still the narrow 1-felt leaf tree; `leaf_commit` here is the
  compatibility join. Precommitting the wide carrier at note creation is part of the deploy.
* The ℤ-integer conservation lift still rides the named `VALUE_BITS` range residual (the
  limbs are canonical, but Σ over many rows can wrap mod p — same residual as lane 2).
* The mod-p pins are field-faithful; exactness at the junctions uses the deployed
  canonical-BabyBear-representative discipline (`hOutCanon`/pub-canonicity hypotheses in
  `wide_binding_binds` — representation facts of the deployed encoder, not crypto).

## Axiom hygiene

Definitional descriptor + both-polarity teeth + explicit satisfying witness; crypto floor
enters as the NAMED hypothesis `WideBindingCR` (satisfiability PROVED, narrow counterpart
REFUTED), never an axiom. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.BlindedMembershipEmit
import Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor
import Dregg2.Circuit.Emit.EffectVmEmitRotationR

namespace Dregg2.Circuit.Emit.ShieldedWideValueLinkDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow VmRowEnv VmConstraint VmRange)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId Table TraceFamily VmTrace zeroAsg envAt
   Satisfied2 chipLookupTupleNarrow poseidon2narrow ChipTableSound chipRow
   chipLookupTupleN ChipTableSoundN chip_lookup_sound_N chipRowN
   CHIP_RATE CHIP_OUT_LANES padToE padTo emitVmJson2 WindowExpr WindowConstraint
   memLog mapLog)
open Dregg2.Circuit.Emit.BlindedMembershipEmit (ev ek eadd emul eneg esub)
open Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor
  (factIns NS_FACT_MARK rowAt prefixSum factIns_eval_4 hzero)
open Dregg2.Circuit.ChipNarrowLookup (narrowTable chip_lookup_narrow_sound_of_wide_table)
open Dregg2.Circuit.Emit.EffectVmEmitRotationR (Poseidon2Width8)

set_option autoImplicit false

/-! ## §1 — the trace column layout: one WIDE clearing slot per row. -/

/-- Value 16-bit limbs `v0..v3` (WITNESS; little-endian, `value = Σ 2^{16i}·v_i` over `u64`). -/
def cV (i : Nat) : Nat := i
/-- Asset 16-bit limbs `a0..a3` (witness). -/
def cA (i : Nat) : Nat := 4 + i
/-- Note owner (witness; leaf-commitment preimage limb). -/
def cOWNER : Nat := 8
/-- Commitment randomness (witness; absorbed into BOTH the leaf and the wide binding). -/
def cRAND : Nat := 9
/-- The recomposed compatibility felt `value mod p` (the cell the leaf hashes + conservation
folds; pinned to the limb recomposition by `recompVBody`). -/
def cVMOD : Nat := 10
/-- The recomposed compatibility felt `asset mod p`. -/
def cAMOD : Nat := 11
/-- Recomputed note commitment `hash_fact(value_mod_p, [asset_mod_p, owner, randomness])`. -/
def cLEAF : Nat := 12
/-- The row's output value `out_val` (witness). -/
def cOUT : Nat := 13
/-- The running conservation accumulator `Σ (value_mod_p − out_val)` up to this row. -/
def cACC : Nat := 14
/-- The 8 WIDE value-binding digest lanes (the full squeezed permutation output). -/
def cWB (j : Nat) : Nat := 15 + j
/-- Main-trace width: 15 clearing columns + 8 wide digest lanes. The leaf fact site's 7 chip lane
columns (the Rust `alloc_lanes()` discipline) are GONE (E7 narrowing, `ChipNarrowLookup.lean`) — they
were the trailing suffix `[23, 30)` and entered no soundness conclusion. The WIDE value-binding site
(`chipLookupTupleN`, the `chip_lookup_sound_N` lever) is NOT narrowed: its 8 squeezed lanes ARE its
conclusion, not exposed padding. -/
def WVL_WIDTH : Nat := 23

/-- PIs 0..7: the published WIDE `value_binding` (all 8 lanes). PI 8: the leaf commit. -/
def piLEAF : Nat := 8
/-- Number of public inputs: `[wide_binding[0..8], leaf_commit]`. -/
def WVL_PI_COUNT : Nat := 9

/-! ## §2 — the wide absorb + the constraint blocks. -/

/-- The wide-binding domain separator — `"VBN0"` = `0x56424E30`
(`wide_value_binding.rs:47` `DOMAIN_A`), an explicit first input. -/
def WIDE_VB_DOMAIN : ℤ := 1447185968

/-- The wide-binding absorb: `[DOMAIN, v0..v3, a0..a3, randomness, 0]` — 11 inputs. The
trailing zero input does not change the permutation output but lands the emitted chip lookup
on the chip AIR's WIDE (arity-11) row (the deployed chip pins `in7..in10 == 0` for every
arity ≠ 11 — the `wireCommitR8` final-chunk discipline; here in7..in9 = `a2,a3,randomness`
are genuinely nonzero). -/
def wideBindIns : List EmittedExpr :=
  [ek WIDE_VB_DOMAIN, ev (cV 0), ev (cV 1), ev (cV 2), ev (cV 3),
   ev (cA 0), ev (cA 1), ev (cA 2), ev (cA 3), ev cRAND, ek 0]

/-- The 8 wide digest columns. -/
def wideCols : List Nat := [15, 16, 17, 18, 19, 20, 21, 22]

/-- **The WIDE value-binding site** — the `chip_lookup_sound_N` lever: all 8 squeezed lanes
of the genuine permutation are forced, not just `state[0]`. -/
def wideBindLookup : VmConstraint2 :=
  .lookup ⟨.poseidon2, chipLookupTupleN wideBindIns wideCols⟩

/-- The leaf-commit recompute — `leaf_commit = hash_fact(value_mod_p, [asset_mod_p, owner,
randomness])`, every row: the deployed narrow fact site (lane 1's C6a shape), over the SAME
recomposed cells the wide binding's limbs pin. -/
def lkLeafCommit : VmConstraint2 :=
  .lookup ⟨poseidon2narrow,
    chipLookupTupleNarrow (factIns [cVMOD, cAMOD, cOWNER, cRAND]) cLEAF⟩

/-- `Σ 2^{16i}·limb_i` over the 4-limb block at `base` (little-endian `u64_recompose`). -/
def limbRecompE (base : Nat) : EmittedExpr :=
  eadd (ev base) (eadd (emul (ek 65536) (ev (base + 1)))
    (eadd (emul (ek 4294967296) (ev (base + 2)))
      (emul (ek 281474976710656) (ev (base + 3)))))

/-- The value recomposition gate body: `value_mod_p − Σ 2^{16i}·v_i`. -/
def recompVBody : EmittedExpr := esub (ev cVMOD) (limbRecompE 0)
/-- The asset recomposition gate body: `asset_mod_p − Σ 2^{16i}·a_i`. -/
def recompABody : EmittedExpr := esub (ev cAMOD) (limbRecompE 4)

/-- `a − b` over a row window. -/
def wsub (a b : WindowExpr) : WindowExpr := .add a (.mul (.const (-1)) b)

/-- The conservation step: `next.acc − (acc + (next.value_mod_p − next.out_val))`. -/
def accWindow : WindowExpr :=
  wsub (.nxt cACC) (.add (.loc cACC) (wsub (.nxt cVMOD) (.nxt cOUT)))

def accStep : WindowConstraint := ⟨accWindow, true⟩

/-- The conservation seed (first row): `acc − (value_mod_p − out_val)`. -/
def seedBody : EmittedExpr := esub (ev cACC) (esub (ev cVMOD) (ev cOUT))

/-- **The WIDE VALUE-LINK block** — the two recomposition gates (per-row + last-row
re-lowering, since per-row gates ride the `when_transition()` domain), the narrow leaf fact
site, and the 8-lane wide binding site. -/
def wideLinkConstraints : List VmConstraint2 :=
  [ .base (.gate recompVBody)
  , .base (.gate recompABody)
  , lkLeafCommit
  , wideBindLookup
  , .base (.boundary .last recompVBody)
  , .base (.boundary .last recompABody) ]

/-- **The Σ-CONSERVATION block** — seed + windowed cumulative step + final-row zero. -/
def conservationConstraints : List VmConstraint2 :=
  [ .windowGate accStep
  , .base (.boundary .first seedBody)
  , .base (.boundary .last (ev cACC)) ]

/-- The row-0 claim pins: ALL 8 wide-binding lanes + the leaf commit. -/
def claimPins : List VmConstraint2 :=
  [ .base (.piBinding .first 15 0)
  , .base (.piBinding .first 16 1)
  , .base (.piBinding .first 17 2)
  , .base (.piBinding .first 18 3)
  , .base (.piBinding .first 19 4)
  , .base (.piBinding .first 20 5)
  , .base (.piBinding .first 21 6)
  , .base (.piBinding .first 22 7)
  , .base (.piBinding .first cLEAF piLEAF) ]

def wideLinkClearConstraints : List VmConstraint2 :=
  wideLinkConstraints ++ conservationConstraints ++ claimPins

/-- The 16-bit range teeth on the 8 limb columns — the faithful multi-limb encoding
(`wide_value_binding.rs` "every limb is bit-constrained in the AIR"; here the range table). -/
def limbRanges : List VmRange :=
  [⟨0, 16⟩, ⟨1, 16⟩, ⟨2, 16⟩, ⟨3, 16⟩, ⟨4, 16⟩, ⟨5, 16⟩, ⟨6, 16⟩, ⟨7, 16⟩]

/-- **`shieldedWideValueLinkDesc`** — the Lean-authored WIDE value-binding + Σ-conservation
clearing descriptor (residual #17's structural half). Staged-additive: rides as an
`Effect::Custom` carrier; no deployed descriptor or registry entry changes here. -/
def shieldedWideValueLinkDesc : EffectVmDescriptor2 :=
  { name        := "dregg-shielded-wide-value-link-conserve::v1"
  , traceWidth  := WVL_WIDTH
  , piCount     := WVL_PI_COUNT
  , tables      := []
  , constraints := wideLinkClearConstraints
  , hashSites   := []
  , ranges      := limbRanges }

-- Non-vacuous structural pins.
#guard shieldedWideValueLinkDesc.traceWidth == 23
#guard shieldedWideValueLinkDesc.piCount == 9
#guard shieldedWideValueLinkDesc.constraints.length == 18
#guard shieldedWideValueLinkDesc.ranges.length == 8
#guard wideBindIns.length == 11
#guard (chipLookupTupleN wideBindIns wideCols).length == 1 + CHIP_RATE + 8
#guard (chipLookupTupleNarrow (factIns [cVMOD, cAMOD, cOWNER, cRAND]) cLEAF).length
  == 1 + CHIP_RATE + 1
-- The narrowing dropped exactly CHIP_OUT_LANES − 1 = 7 main columns for the same forced leaf
-- equation; the WIDE 8-lane binding site is untouched.
#guard WVL_WIDTH + (CHIP_OUT_LANES - 1) == 30
#guard poseidon2narrow.wireId == 8
#guard wideCols == (List.range 8).map cWB

-- Window canaries: the conservation step vanishes iff the accumulator threads the net.
#guard decide (accWindow.eval
  { loc := fun c => if c = cACC then 1 else 0
  , nxt := fun c => if c = cVMOD then 3 else if c = cOUT then 4 else 0
  , pub := zeroAsg } = 0)
#guard decide (¬ (accWindow.eval
  { loc := fun c => if c = cACC then 1 else 0
  , nxt := fun c => if c = cVMOD then 3 else if c = cOUT then 5 else 0
  , pub := zeroAsg } = 0))

/-! ## §3 — openings, the canonical domain, and the NAMED wide floor. -/

/-- A wide-binding opening: the witness cells the 8-felt binding absorbs. -/
structure WideOpening where
  v0 : ℤ
  v1 : ℤ
  v2 : ℤ
  v3 : ℤ
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  rand : ℤ
  deriving DecidableEq, Repr

/-- The wide absorb of an opening (the evaluated `wideBindIns`). -/
def wideAbsorb (o : WideOpening) : List ℤ :=
  [WIDE_VB_DOMAIN, o.v0, o.v1, o.v2, o.v3, o.a0, o.a1, o.a2, o.a3, o.rand, 0]

/-- CANONICAL opening: every limb a genuine 16-bit value, randomness a canonical BabyBear
felt. The domain the deployed encoder produces — and the domain the floor quantifies over. -/
def CanonicalOpening (o : WideOpening) : Prop :=
  (0 ≤ o.v0 ∧ o.v0 < 65536) ∧ (0 ≤ o.v1 ∧ o.v1 < 65536) ∧
  (0 ≤ o.v2 ∧ o.v2 < 65536) ∧ (0 ≤ o.v3 ∧ o.v3 < 65536) ∧
  (0 ≤ o.a0 ∧ o.a0 < 65536) ∧ (0 ≤ o.a1 ∧ o.a1 < 65536) ∧
  (0 ≤ o.a2 ∧ o.a2 < 65536) ∧ (0 ≤ o.a3 ∧ o.a3 < 65536) ∧
  (0 ≤ o.rand ∧ o.rand < 2013265921)

/-- **THE NAMED FLOOR (`WideBindingCR`).** The 8-lane squeeze separates CANONICAL openings.
Deliberately NOT the deleted-FALSE `Poseidon2WideCR` (injectivity over ALL of `List ℤ`,
pigeonhole-refuted): the canonical domain has ~2^159 elements against a ~2^248 range, so
counting does not refute THIS floor — `wideBindingCR_satisfiable` inhabits it, while the
1-felt counterpart is REFUTED by `narrow_binding_collision_exists`. For real Poseidon2 this
is standard wide-output collision resistance restricted to the honest encoding domain. -/
def WideBindingCR (permOut : List ℤ → List ℤ) : Prop :=
  ∀ o₁ o₂ : WideOpening, CanonicalOpening o₁ → CanonicalOpening o₂ →
    permOut (wideAbsorb o₁) = permOut (wideAbsorb o₂) → o₁ = o₂

/-- The narrow hash is the HEAD of the wide squeeze — the deployed `hash_many = state[0]`
relationship (`chipRowN_head_eq_hash`'s content, as a function). -/
def headHash (permOut : List ℤ → List ℤ) : List ℤ → ℤ := fun xs => (permOut xs).getD 0 0

/-- A WIDE-sound chip table is also NARROW-sound at the head hash: every `chipRowN` row is a
`chipRow (headHash permOut)` row whose lanes are the squeeze's lanes 1..7. -/
theorem chipTableSound_of_soundN (permOut : List ℤ → List ℤ) (hW : Poseidon2Width8 permOut)
    (tbl : Table) (h : ChipTableSoundN permOut tbl) :
    ChipTableSound (headHash permOut) tbl := by
  intro r hr
  obtain ⟨ins, hlen, hrow⟩ := h r hr
  have h8 := hW ins
  cases hp : permOut ins with
  | nil => rw [hp] at h8; simp at h8
  | cons hd tl =>
    refine ⟨ins, tl, hlen, ?_, ?_⟩
    · have hl := congrArg List.length hp
      rw [h8] at hl
      simp only [List.length_cons] at hl
      simp only [CHIP_OUT_LANES]
      omega
    · rw [hrow]
      unfold chipRowN chipRow headHash
      rw [hp]
      simp

/-! ## §4 — extraction helpers: read the per-row facts out of a `Satisfied2` witness. -/

def vmodAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i cVMOD
def outAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i cOUT
def accAt (t : VmTrace) (i : Nat) : ℤ := rowAt t i cACC
/-- The row's net contribution `value_mod_p − out_val`. -/
def netAt (t : VmTrace) (i : Nat) : ℤ := vmodAt t i - outAt t i
/-- The row's wide-binding opening: the limb/randomness cells. -/
def openingAt (t : VmTrace) (i : Nat) : WideOpening :=
  ⟨rowAt t i 0, rowAt t i 1, rowAt t i 2, rowAt t i 3,
   rowAt t i 4, rowAt t i 5, rowAt t i 6, rowAt t i 7, rowAt t i cRAND⟩

private theorem modeqOfShape {e a b : ℤ} (hshape : e = a - b)
    (h : e ≡ 0 [ZMOD 2013265921]) : a ≡ b [ZMOD 2013265921] := by
  subst hshape
  have hd := Int.modEq_iff_dvd.mp h
  have he : (0 : ℤ) - (a - b) = b - a := by ring
  rw [he] at hd
  exact Int.modEq_iff_dvd.mpr hd

private theorem eqOfModeqCanon {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha0 : 0 ≤ a) (ha : a < 2013265921) (hb0 : 0 ≤ b) (hb : b < 2013265921) : a = b := by
  have h' : a % 2013265921 = b % 2013265921 := h
  rwa [Int.emod_eq_of_lt ha0 ha, Int.emod_eq_of_lt hb0 hb] at h'

/-- The evaluated wide absorb IS the row's opening's absorb. -/
theorem wideBindIns_eval (a : Assignment) :
    wideBindIns.map (·.eval a) = wideAbsorb ⟨a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 9⟩ := by
  simp [wideBindIns, wideAbsorb, ev, ek, cV, cA, cRAND, EmittedExpr.eval]

theorem wideCols_map (f : Nat → ℤ) :
    wideCols.map f = [f 15, f 16, f 17, f 18, f 19, f 20, f 21, f 22] := rfl

section Extract

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
  {t : VmTrace}

/-- Generic PI-pin extraction at row 0. -/
private theorem pin_extract (hsat : Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t)
    (hpos : 0 < t.rows.length) {col k : Nat}
    (hmem : VmConstraint2.base (.piBinding .first col k) ∈ shieldedWideValueLinkDesc.constraints) :
    rowAt t 0 col ≡ t.pub k [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 hpos _ hmem
  simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at h
  simpa only [rowAt] using h rfl

/-- Generic gate-body extraction on EVERY row (per-row gate off the last row, the last-row
boundary re-lowering on it) — the `pad_zero` case-split shape. -/
private theorem gate_extract (hsat : Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) {body : EmittedExpr}
    (hg : VmConstraint2.base (.gate body) ∈ shieldedWideValueLinkDesc.constraints)
    (hb : VmConstraint2.base (.boundary .last body) ∈ shieldedWideValueLinkDesc.constraints) :
    body.eval (rowAt t i) ≡ 0 [ZMOD 2013265921] := by
  by_cases hl : i + 1 = t.rows.length
  · have h := hsat.rowConstraints i hi _ hb
    have hbt : (i + 1 == t.rows.length) = true := by simpa using hl
    simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
      Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at h
    simpa only [rowAt] using h hbt
  · have h := hsat.rowConstraints i hi _ hg
    have hlf : (i + 1 == t.rows.length) = false := by simpa using hl
    simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
      Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, hlf, envAt] at h
    simpa only [rowAt] using h

/-- The value recomposition holds (mod p) on every row. -/
theorem recomp_value (hsat : Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) :
    vmodAt t i ≡ rowAt t i 0 + 65536 * rowAt t i 1 + 4294967296 * rowAt t i 2
      + 281474976710656 * rowAt t i 3 [ZMOD 2013265921] := by
  have h := gate_extract hsat hi
    (body := recompVBody)
    (by simp [shieldedWideValueLinkDesc, wideLinkClearConstraints, wideLinkConstraints,
      conservationConstraints, claimPins])
    (by simp [shieldedWideValueLinkDesc, wideLinkClearConstraints, wideLinkConstraints,
      conservationConstraints, claimPins])
  simp only [recompVBody, limbRecompE, esub, eadd, emul, eneg, ev, ek,
    EmittedExpr.eval, cVMOD] at h
  exact modeqOfShape (by unfold vmodAt rowAt; unfold cVMOD; ring) h

/-- The asset recomposition holds (mod p) on every row. -/
theorem recomp_asset (hsat : Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) :
    rowAt t i cAMOD ≡ rowAt t i 4 + 65536 * rowAt t i 5 + 4294967296 * rowAt t i 6
      + 281474976710656 * rowAt t i 7 [ZMOD 2013265921] := by
  have h := gate_extract hsat hi
    (body := recompABody)
    (by simp [shieldedWideValueLinkDesc, wideLinkClearConstraints, wideLinkConstraints,
      conservationConstraints, claimPins])
    (by simp [shieldedWideValueLinkDesc, wideLinkClearConstraints, wideLinkConstraints,
      conservationConstraints, claimPins])
  simp only [recompABody, limbRecompE, esub, eadd, emul, eneg, ev, ek,
    EmittedExpr.eval, cAMOD] at h
  exact modeqOfShape (by unfold rowAt; unfold cAMOD; ring) h

/-- Every limb cell is 16-bit canonical — the descriptor's range teeth. -/
theorem limbs_canonical (hsat : Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) {c : Nat} (hc : c < 8) :
    0 ≤ rowAt t i c ∧ rowAt t i c < 65536 := by
  have hmem : (⟨c, 16⟩ : VmRange) ∈ shieldedWideValueLinkDesc.ranges := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [shieldedWideValueLinkDesc, limbRanges]
  have h := hsat.rowRanges i hi _ hmem
  simp only [Dregg2.Circuit.Emit.EffectVmEmit.VmRange.holds, envAt] at h
  norm_num at h
  simpa only [rowAt, List.getD_eq_getElem?_getD] using h

/-- **The 8 wide digest columns are FORCED** to the genuine full-width squeeze of the row's
own limb/randomness cells — the `chip_lookup_sound_N` lever fired at this site. -/
theorem wide_digest_forced (permOut : List ℤ → List ℤ)
    (hChipW : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hsat : Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) :
    wideCols.map (rowAt t i) = permOut (wideAbsorb (openingAt t i)) := by
  have hrow := hsat.rowConstraints i hi wideBindLookup
    (by simp [shieldedWideValueLinkDesc, wideLinkClearConstraints, wideLinkConstraints,
      conservationConstraints, claimPins])
  have hmem : (chipLookupTupleN wideBindIns wideCols).map (·.eval (rowAt t i))
      ∈ t.tf TableId.poseidon2 := by
    simpa only [wideBindLookup, Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt, envAt, rowAt] using hrow
  have h := chip_lookup_sound_N permOut (t.tf TableId.poseidon2) hChipW (rowAt t i)
    wideBindIns wideCols (by decide) hmem
  rw [wideBindIns_eval] at h
  exact h

/-- **The leaf commit is FORCED** to the genuine narrow fact digest (the HEAD of the same
permutation) of the recomposed value/asset cells + owner + randomness. -/
theorem leaf_forced (permOut : List ℤ → List ℤ) (hW : Poseidon2Width8 permOut)
    (hChipW : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2))
    (hsat : Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) :
    rowAt t i cLEAF
      = headHash permOut [rowAt t i cVMOD, rowAt t i cAMOD, rowAt t i cOWNER, rowAt t i cRAND,
          0, NS_FACT_MARK, 1] := by
  have hChip := chipTableSound_of_soundN permOut hW _ hChipW
  have hrow := hsat.rowConstraints i hi lkLeafCommit
    (by simp [shieldedWideValueLinkDesc, wideLinkClearConstraints, wideLinkConstraints,
      conservationConstraints, claimPins])
  have hmem : (chipLookupTupleNarrow (factIns [cVMOD, cAMOD, cOWNER, cRAND]) cLEAF).map
      (·.eval (rowAt t i)) ∈ narrowTable (t.tf TableId.poseidon2) := by
    have h0 : (chipLookupTupleNarrow (factIns [cVMOD, cAMOD, cOWNER, cRAND]) cLEAF).map
        (·.eval (rowAt t i)) ∈ t.tf poseidon2narrow := by
      simpa only [lkLeafCommit, Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
        Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt, envAt, rowAt] using hrow
    rwa [hwire] at h0
  have h := chip_lookup_narrow_sound_of_wide_table (headHash permOut) (t.tf TableId.poseidon2)
    hChip (rowAt t i) _ cLEAF (by decide) hmem
  rw [factIns_eval_4] at h
  exact h

/-- **The accumulator IS the running sum (mod p)** — seed + window step, by induction. -/
theorem acc_folds (hsat : Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t) :
    ∀ j, j < t.rows.length → accAt t j ≡ prefixSum (netAt t) j [ZMOD 2013265921] := by
  intro j
  induction j with
  | zero =>
      intro hj
      have h := hsat.rowConstraints 0 hj (.base (.boundary .first seedBody))
        (by simp [shieldedWideValueLinkDesc, wideLinkClearConstraints, wideLinkConstraints,
          conservationConstraints, claimPins])
      simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
        Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at h
      have h0 := h rfl
      simp only [seedBody, esub, eadd, emul, eneg, ev, ek, EmittedExpr.eval] at h0
      simp only [prefixSum, netAt, vmodAt, outAt, accAt, rowAt]
      exact modeqOfShape (by ring) h0
  | succ n ih =>
      intro hj
      have hn : n < t.rows.length := by omega
      have hnl : n + 1 ≠ t.rows.length := by omega
      have h := hsat.rowConstraints n hn (.windowGate accStep)
        (by simp [shieldedWideValueLinkDesc, wideLinkClearConstraints, wideLinkConstraints,
          conservationConstraints, claimPins])
      have hlf : (n + 1 == t.rows.length) = false := by simpa using hnl
      have honT : accStep.onTransition = true := rfl
      have hbody : accStep.body = accWindow := rfl
      simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
        Dregg2.Circuit.DescriptorIR2.WindowConstraint.holdsAt, honT, if_true] at h
      have h1 := h hlf
      simp only [hbody, accWindow, wsub, Dregg2.Circuit.DescriptorIR2.WindowExpr.eval,
        envAt] at h1
      have hstep : accAt t (n + 1) ≡ accAt t n + netAt t (n + 1) [ZMOD 2013265921] := by
        simp only [accAt, netAt, vmodAt, outAt, rowAt]
        exact modeqOfShape (by ring) h1
      have hplus := Int.ModEq.add_right (netAt t (n + 1)) (ih hn)
      simpa only [prefixSum] using hstep.trans hplus

/-- The final accumulator vanishes (mod p) — the last-row conservation boundary. -/
private theorem acc_final (hsat : Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t)
    (hne : t.rows ≠ []) :
    accAt t (t.rows.length - 1) ≡ 0 [ZMOD 2013265921] := by
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons a l => simp
  have hlt : t.rows.length - 1 < t.rows.length := by omega
  have h := hsat.rowConstraints (t.rows.length - 1) hlt (.base (.boundary .last (ev cACC)))
    (by simp [shieldedWideValueLinkDesc, wideLinkClearConstraints, wideLinkConstraints,
      conservationConstraints, claimPins])
  have hlastb : ((t.rows.length - 1) + 1 == t.rows.length) = true := by
    have hx : t.rows.length - 1 + 1 = t.rows.length := by omega
    simpa using hx
  simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm, envAt] at h
  simpa only [ev, EmittedExpr.eval, accAt, rowAt] using h hlastb

end Extract

/-! ## §5 — `wide_value_link_bound`: `value_link_bound` re-derived over the 8-felt binding. -/

/-- **⚑ KEYSTONE (`wide_value_link_bound`).** Under a sound WIDE chip table, a `Satisfied2`
trace forces, on EVERY row: the 8 wide-binding cells are the genuine FULL-WIDTH squeeze
`permOut [DOMAIN, v0..v3, a0..a3, randomness, 0]` of the row's own limb cells; the leaf
commit is the genuine narrow fact digest (the HEAD of the SAME permutation) of the recomposed
`value_mod_p`/`asset_mod_p` + owner + randomness; both recompositions pin the compatibility
felts to the limbs (mod p); and every limb is 16-bit canonical. Row 0 pins ALL 8 binding
lanes + the leaf commit to the PIs (field-faithful, ZMOD 2013265921). So the value that
conserves (§6) is the recomposition of exactly the limbs the published 8-felt binding
binds — the value-link, at 8 felts. -/
theorem wide_value_link_bound (permOut : List ℤ → List ℤ) (hW : Poseidon2Width8 permOut)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t)
    (hChipW : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2)) :
    (∀ i, i < t.rows.length →
        wideCols.map (rowAt t i) = permOut (wideAbsorb (openingAt t i))
        ∧ rowAt t i cLEAF
            = headHash permOut [rowAt t i cVMOD, rowAt t i cAMOD, rowAt t i cOWNER,
                rowAt t i cRAND, 0, NS_FACT_MARK, 1]
        ∧ (vmodAt t i ≡ rowAt t i 0 + 65536 * rowAt t i 1 + 4294967296 * rowAt t i 2
            + 281474976710656 * rowAt t i 3 [ZMOD 2013265921])
        ∧ (rowAt t i cAMOD ≡ rowAt t i 4 + 65536 * rowAt t i 5 + 4294967296 * rowAt t i 6
            + 281474976710656 * rowAt t i 7 [ZMOD 2013265921])
        ∧ (∀ c, c < 8 → 0 ≤ rowAt t i c ∧ rowAt t i c < 65536))
    ∧ (∀ j, j < 8 → rowAt t 0 (cWB j) ≡ t.pub j [ZMOD 2013265921])
    ∧ (rowAt t 0 cLEAF ≡ t.pub piLEAF [ZMOD 2013265921]) := by
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons a l => simp
  refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
  · exact ⟨wide_digest_forced permOut hChipW hsat hi,
      leaf_forced permOut hW hChipW hwire hsat hi,
      recomp_value hsat hi, recomp_asset hsat hi,
      fun c hc => limbs_canonical hsat hi hc⟩
  · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact pin_extract hsat hpos
        (by simp [shieldedWideValueLinkDesc, wideLinkClearConstraints, wideLinkConstraints,
          conservationConstraints, claimPins, cWB])
  · exact pin_extract hsat hpos
      (by simp [shieldedWideValueLinkDesc, wideLinkClearConstraints, wideLinkConstraints,
        conservationConstraints, claimPins])

/-- **THE DECOUPLING TOOTH, at 8 felts.** A trace whose published lane-0 PI is not (mod p)
the genuine lane-0 of the wide squeeze of the leaf's own limb cells admits NO satisfying
assignment. (Any single decoupled lane refutes; lane 0 is stated as the canonical
falsifier.) -/
theorem wide_decoupled_unsat (permOut : List ℤ → List ℤ) (hW : Poseidon2Width8 permOut)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hChipW : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2))
    (hforge : ¬ (t.pub 0
      ≡ (permOut (wideAbsorb (openingAt t 0))).getD 0 0 [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t := by
  intro hsat
  obtain ⟨hrows, hpins, _⟩ := wide_value_link_bound permOut hW hash minit mfin maddrs t hne
    hsat hChipW hwire
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons a l => simp
  have hlanes := (hrows 0 hpos).1
  have hlane0 : rowAt t 0 15 = (permOut (wideAbsorb (openingAt t 0))).getD 0 0 := by
    rw [← hlanes]
    rfl
  have hpin0 := hpins 0 (by omega)
  rw [show cWB 0 = 15 from rfl, hlane0] at hpin0
  exact hforge hpin0.symm

/-! ## §6 — conservation over the multi-limb value + the mint tooth. -/

/-- **`wide_conservation_holds`.** A satisfying trace's recomposed values CONSERVE:
`Σᵢ value_mod_p[i] ≡ Σⱼ out_val[j] [ZMOD 2013265921]` — over the SAME cells the recomposition
gates pin to the limbs the WIDE binding hashes (§5). Field conservation; the ℤ-integer lift
is the named `VALUE_BITS` range residual (header). -/
theorem wide_conservation_holds (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t) :
    prefixSum (vmodAt t) (t.rows.length - 1)
      ≡ prefixSum (outAt t) (t.rows.length - 1) [ZMOD 2013265921] := by
  have hsplit : ∀ n : Nat,
      prefixSum (netAt t) n = prefixSum (vmodAt t) n - prefixSum (outAt t) n := by
    intro n
    induction n with
    | zero => simp only [prefixSum, netAt]
    | succ m ih => simp only [prefixSum, ih, netAt]; ring
  have hfold := acc_folds hsat (t.rows.length - 1)
    (by
      have hpos : 0 < t.rows.length := by
        cases hr : t.rows with
        | nil => exact absurd hr hne
        | cons a l => simp
      omega)
  have hz : prefixSum (netAt t) (t.rows.length - 1) ≡ 0 [ZMOD 2013265921] :=
    hfold.symm.trans (acc_final hsat hne)
  rw [hsplit] at hz
  exact modeqOfShape rfl hz

/-- **THE MINT TOOTH.** An unbalanced trace — `Σ value_mod_p ≢ Σ out_val (mod p)` — admits NO
satisfying assignment. -/
theorem wide_mint_unbalanced_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hforge : ¬ (prefixSum (vmodAt t) (t.rows.length - 1)
      ≡ prefixSum (outAt t) (t.rows.length - 1) [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedWideValueLinkDesc minit mfin maddrs t :=
  fun hsat => hforge (wide_conservation_holds hash minit mfin maddrs t hne hsat)

/-! ## §7 — the 1-felt shape REFUTED, the wide floor INHABITED, the binding PROVED. -/

/-- The pigeonhole probe: canonical openings varying only the `(v0, v1)` base-2^16 digits. -/
private def collProbe (k : Fin 2013265922) : WideOpening :=
  ⟨(((k : ℕ) % 65536 : ℕ) : ℤ), (((k : ℕ) / 65536 : ℕ) : ℤ), 0, 0, 0, 0, 0, 0, 0⟩

private theorem collProbe_canonical (k : Fin 2013265922) : CanonicalOpening (collProbe k) := by
  have hk : (k : ℕ) < 2013265922 := k.isLt
  simp only [CanonicalOpening, collProbe]
  omega

/-- **⚑ THE STRUCTURAL REFUTATION OF THE 1-FELT BINDING.** EVERY BabyBear-bounded one-felt
binding — the deployed C7a `hash_fact` squeeze included, but ANY function whatsoever — admits
two DISTINCT canonical openings with the SAME tag: 2^32 openings that vary only `(v0, v1)`
cannot inject into `p < 2^31` felts (pigeonhole; the birthday attack finds such a pair in
~2^15.5 queries). No crypto hypothesis: the 1-felt floor is not weak, it is UNSATISFIABLE.
This is residual #17's wound, as a theorem. -/
theorem narrow_binding_collision_exists (bind : WideOpening → ℤ)
    (hbound : ∀ o : WideOpening, CanonicalOpening o →
      0 ≤ bind o ∧ bind o < 2013265921) :
    ∃ o₁ o₂ : WideOpening, CanonicalOpening o₁ ∧ CanonicalOpening o₂ ∧ o₁ ≠ o₂ ∧
      bind o₁ = bind o₂ := by
  -- 2^31-ish canonical openings varying only (v0, v1), mapped into p felts, cannot inject.
  obtain ⟨k, k', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin 2013265922 =>
      (⟨(bind (collProbe k)).toNat, by
        have h := hbound (collProbe k) (collProbe_canonical k)
        omega⟩ : Fin 2013265921))
    (by simp only [Fintype.card_fin]; omega)
  refine ⟨collProbe k, collProbe k', collProbe_canonical k, collProbe_canonical k', ?_, ?_⟩
  · -- distinct fin indices give distinct openings (the (v0, v1) base-2^16 digits of k)
    intro hmk
    apply hne
    have h0 : (((k : ℕ) % 65536 : ℕ) : ℤ) = (((k' : ℕ) % 65536 : ℕ) : ℤ) :=
      congrArg WideOpening.v0 hmk
    have h1 : (((k : ℕ) / 65536 : ℕ) : ℤ) = (((k' : ℕ) / 65536 : ℕ) : ℤ) :=
      congrArg WideOpening.v1 hmk
    have h0' : (k : ℕ) % 65536 = (k' : ℕ) % 65536 := by exact_mod_cast h0
    have h1' : (k : ℕ) / 65536 = (k' : ℕ) / 65536 := by exact_mod_cast h1
    exact Fin.val_injective (by omega)
  · -- equal Fin images + canonical bounds give equal tags
    have hkb := hbound (collProbe k) (collProbe_canonical k)
    have hkb' := hbound (collProbe k') (collProbe_canonical k')
    have htn : (bind (collProbe k)).toNat = (bind (collProbe k')).toNat :=
      congrArg Fin.val heq
    omega

/-- The explicit width-8 inhabitant of the wide floor: pack each `(v_i, a_i)` limb pair into
one lane (`v_i + 2^16·a_i` — injective on 16-bit limbs), randomness on lane 4. -/
def packPerm : List ℤ → List ℤ := fun xs =>
  match xs with
  | [_, v0, v1, v2, v3, a0, a1, a2, a3, r, _] =>
      [v0 + 65536 * a0, v1 + 65536 * a1, v2 + 65536 * a2, v3 + 65536 * a3, r, 0, 0, 0]
  | _ => [0, 0, 0, 0, 0, 0, 0, 0]

/-- **The wide floor is INHABITED** — `WideBindingCR` is not counting-refutable (contrast
`narrow_binding_collision_exists`, which refutes EVERY 1-felt counterpart outright): the
canonical domain (~2^159) fits injectively into 8 lanes (~2^248), and `packPerm` witnesses
it at width 8. THIS is what the widening buys; real Poseidon2 replaces the packing with the
priced CR game. -/
theorem wideBindingCR_satisfiable : Poseidon2Width8 packPerm ∧ WideBindingCR packPerm := by
  constructor
  · intro xs
    unfold packPerm
    split <;> rfl
  · intro o₁ o₂ h₁ h₂ heq
    cases o₁ with | mk p0 p1 p2 p3 q0 q1 q2 q3 pr =>
    cases o₂ with | mk s0 s1 s2 s3 u0 u1 u2 u3 sr =>
    simp only [CanonicalOpening] at h₁ h₂
    have h : [p0 + 65536 * q0, p1 + 65536 * q1, p2 + 65536 * q2, p3 + 65536 * q3,
        pr, 0, 0, 0]
        = [s0 + 65536 * u0, s1 + 65536 * u1, s2 + 65536 * u2, s3 + 65536 * u3,
        sr, 0, 0, 0] := heq
    injection h with e0 h
    injection h with e1 h
    injection h with e2 h
    injection h with e3 h
    injection h with er h
    simp only [WideOpening.mk.injEq]
    omega

/-- Under the wide floor, distinct canonical openings SEPARATE at 8 felts — the direct
contrapositive the teeth compose with. -/
theorem wide_refuses_distinct_openings (permOut : List ℤ → List ℤ)
    (hCR : WideBindingCR permOut) {o₁ o₂ : WideOpening}
    (h₁ : CanonicalOpening o₁) (h₂ : CanonicalOpening o₂) (hne : o₁ ≠ o₂) :
    permOut (wideAbsorb o₁) ≠ permOut (wideAbsorb o₂) :=
  fun h => hne (hCR o₁ o₂ h₁ h₂ h)

/-- **⚑ THE HEADLINE (`birthday_collision_no_longer_forges`).** For EVERY BabyBear-bounded
1-felt legacy binding there is a canonical collision pair (the ~2^15.5 birthday surface,
`narrow_binding_collision_exists`) — and on ANY such pair, the 8-felt wide binding still
SEPARATES under the named floor. A birthday collision on one felt no longer forges a
`value_binding`. -/
theorem birthday_collision_no_longer_forges (permOut : List ℤ → List ℤ)
    (hCR : WideBindingCR permOut) (legacy : WideOpening → ℤ)
    (hbound : ∀ o : WideOpening, CanonicalOpening o →
      0 ≤ legacy o ∧ legacy o < 2013265921) :
    ∃ o₁ o₂ : WideOpening, CanonicalOpening o₁ ∧ CanonicalOpening o₂ ∧ o₁ ≠ o₂ ∧
      legacy o₁ = legacy o₂ ∧
      permOut (wideAbsorb o₁) ≠ permOut (wideAbsorb o₂) := by
  obtain ⟨o₁, o₂, h₁, h₂, hne, hcoll⟩ := narrow_binding_collision_exists legacy hbound
  exact ⟨o₁, o₂, h₁, h₂, hne, hcoll,
    wide_refuses_distinct_openings permOut hCR h₁ h₂ hne⟩

/-- **⚑ THE PAYOFF (`wide_binding_binds`).** Under the NAMED floor, two satisfying traces
publishing the SAME 8-felt wide binding open the SAME `(value-limbs, asset-limbs,
randomness)` — the full `u64` value, not its mod-p shadow — and their conserved
`value_mod_p` cells agree (mod p). Forging a `value_binding` now requires a genuine
wide-Poseidon2 canonical collision; the 1-felt birthday attack
(`narrow_binding_collision_exists`) buys nothing. The canonicity hypotheses (`hOutCanon`,
`hPubCanon`, `hRand*`) are the deployed canonical-BabyBear-representative discipline —
representation facts, not crypto. -/
theorem wide_binding_binds (permOut : List ℤ → List ℤ) (hW : Poseidon2Width8 permOut)
    (hCR : WideBindingCR permOut)
    (hOutCanon : ∀ xs : List ℤ, ∀ y ∈ permOut xs, 0 ≤ y ∧ y < 2013265921)
    (hash₁ hash₂ : List ℤ → ℤ) (minit₁ minit₂ : ℤ → ℤ) (mfin₁ mfin₂ : ℤ → ℤ × Nat)
    (maddrs₁ maddrs₂ : List ℤ) (t₁ t₂ : VmTrace)
    (hne₁ : t₁.rows ≠ []) (hne₂ : t₂.rows ≠ [])
    (hsat₁ : Satisfied2 hash₁ shieldedWideValueLinkDesc minit₁ mfin₁ maddrs₁ t₁)
    (hsat₂ : Satisfied2 hash₂ shieldedWideValueLinkDesc minit₂ mfin₂ maddrs₂ t₂)
    (hChipW₁ : ChipTableSoundN permOut (t₁.tf TableId.poseidon2))
    (hChipW₂ : ChipTableSoundN permOut (t₂.tf TableId.poseidon2))
    (hwire₁ : t₁.tf poseidon2narrow = narrowTable (t₁.tf TableId.poseidon2))
    (hwire₂ : t₂.tf poseidon2narrow = narrowTable (t₂.tf TableId.poseidon2))
    (hRand₁ : 0 ≤ rowAt t₁ 0 cRAND ∧ rowAt t₁ 0 cRAND < 2013265921)
    (hRand₂ : 0 ≤ rowAt t₂ 0 cRAND ∧ rowAt t₂ 0 cRAND < 2013265921)
    (hPub : ∀ j, j < 8 → t₁.pub j = t₂.pub j)
    (hPubCanon : ∀ j, j < 8 → 0 ≤ t₁.pub j ∧ t₁.pub j < 2013265921) :
    openingAt t₁ 0 = openingAt t₂ 0 ∧
      (vmodAt t₁ 0 ≡ vmodAt t₂ 0 [ZMOD 2013265921]) := by
  have hpos₁ : 0 < t₁.rows.length := by
    cases hr : t₁.rows with
    | nil => exact absurd hr hne₁
    | cons a l => simp
  have hpos₂ : 0 < t₂.rows.length := by
    cases hr : t₂.rows with
    | nil => exact absurd hr hne₂
    | cons a l => simp
  obtain ⟨hrows₁, hpins₁, _⟩ := wide_value_link_bound permOut hW hash₁ minit₁ mfin₁ maddrs₁ t₁
    hne₁ hsat₁ hChipW₁ hwire₁
  obtain ⟨hrows₂, hpins₂, _⟩ := wide_value_link_bound permOut hW hash₂ minit₂ mfin₂ maddrs₂ t₂
    hne₂ hsat₂ hChipW₂ hwire₂
  have hl₁ := (hrows₁ 0 hpos₁).1
  have hl₂ := (hrows₂ 0 hpos₂).1
  -- each lane is canonical (it sits in a permOut image)…
  have hlaneCanon₁ : ∀ j, j < 8 →
      0 ≤ rowAt t₁ 0 (cWB j) ∧ rowAt t₁ 0 (cWB j) < 2013265921 := by
    intro j hj
    have hmem : rowAt t₁ 0 (cWB j) ∈ permOut (wideAbsorb (openingAt t₁ 0)) := by
      rw [← hl₁, wideCols_map]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [cWB]
    exact hOutCanon _ _ hmem
  have hlaneCanon₂ : ∀ j, j < 8 →
      0 ≤ rowAt t₂ 0 (cWB j) ∧ rowAt t₂ 0 (cWB j) < 2013265921 := by
    intro j hj
    have hmem : rowAt t₂ 0 (cWB j) ∈ permOut (wideAbsorb (openingAt t₂ 0)) := by
      rw [← hl₂, wideCols_map]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [cWB]
    exact hOutCanon _ _ hmem
  -- …so the mod-p pins give EXACT lane equality across the two traces.
  have hlaneEq : ∀ j, j < 8 → rowAt t₁ 0 (cWB j) = rowAt t₂ 0 (cWB j) := by
    intro j hj
    have hc₁ := hlaneCanon₁ j hj
    have hc₂ := hlaneCanon₂ j hj
    have hpc := hPubCanon j hj
    have hpc₂ : 0 ≤ t₂.pub j ∧ t₂.pub j < 2013265921 := by rw [← hPub j hj]; exact hpc
    have e₁ : rowAt t₁ 0 (cWB j) = t₁.pub j :=
      eqOfModeqCanon (hpins₁ j hj) hc₁.1 hc₁.2 hpc.1 hpc.2
    have e₂ : rowAt t₂ 0 (cWB j) = t₂.pub j :=
      eqOfModeqCanon (hpins₂ j hj) hc₂.1 hc₂.2 hpc₂.1 hpc₂.2
    rw [e₁, e₂, hPub j hj]
  -- exact digest-list equality, then the floor.
  have hdig : permOut (wideAbsorb (openingAt t₁ 0)) = permOut (wideAbsorb (openingAt t₂ 0)) := by
    rw [← hl₁, ← hl₂, wideCols_map, wideCols_map]
    have e0 := hlaneEq 0 (by omega)
    have e1 := hlaneEq 1 (by omega)
    have e2 := hlaneEq 2 (by omega)
    have e3 := hlaneEq 3 (by omega)
    have e4 := hlaneEq 4 (by omega)
    have e5 := hlaneEq 5 (by omega)
    have e6 := hlaneEq 6 (by omega)
    have e7 := hlaneEq 7 (by omega)
    simp only [cWB, Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 e6 e7
    simp only [List.cons.injEq, and_true]
    exact ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩
  have hcanon₁ : CanonicalOpening (openingAt t₁ 0) := by
    have hlimb := (hrows₁ 0 hpos₁).2.2.2.2
    have h0 := hlimb 0 (by decide)
    have h1 := hlimb 1 (by decide)
    have h2 := hlimb 2 (by decide)
    have h3 := hlimb 3 (by decide)
    have h4 := hlimb 4 (by decide)
    have h5 := hlimb 5 (by decide)
    have h6 := hlimb 6 (by decide)
    have h7 := hlimb 7 (by decide)
    simp only [CanonicalOpening, openingAt]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, hRand₁⟩
  have hcanon₂ : CanonicalOpening (openingAt t₂ 0) := by
    have hlimb := (hrows₂ 0 hpos₂).2.2.2.2
    have h0 := hlimb 0 (by decide)
    have h1 := hlimb 1 (by decide)
    have h2 := hlimb 2 (by decide)
    have h3 := hlimb 3 (by decide)
    have h4 := hlimb 4 (by decide)
    have h5 := hlimb 5 (by decide)
    have h6 := hlimb 6 (by decide)
    have h7 := hlimb 7 (by decide)
    simp only [CanonicalOpening, openingAt]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, hRand₂⟩
  have hopen : openingAt t₁ 0 = openingAt t₂ 0 := hCR _ _ hcanon₁ hcanon₂ hdig
  refine ⟨hopen, ?_⟩
  -- equal openings ⇒ the recomposed conserved values agree (mod p).
  have hr₁ := (hrows₁ 0 hpos₁).2.2.1
  have hr₂ := (hrows₂ 0 hpos₂).2.2.1
  have hv0 : rowAt t₁ 0 0 = rowAt t₂ 0 0 := congrArg WideOpening.v0 hopen
  have hv1 : rowAt t₁ 0 1 = rowAt t₂ 0 1 := congrArg WideOpening.v1 hopen
  have hv2 : rowAt t₁ 0 2 = rowAt t₂ 0 2 := congrArg WideOpening.v2 hopen
  have hv3 : rowAt t₁ 0 3 = rowAt t₂ 0 3 := congrArg WideOpening.v3 hopen
  rw [hv0, hv1, hv2, hv3] at hr₁
  exact hr₁.trans hr₂.symm

/-! ## §8 — non-vacuity: an explicit HONEST BALANCED witness, and the teeth exercised. -/

/-- The zero wide squeeze — the abstract-hash carrier for the concrete witnesses (the chip
table below carries genuine `chipRowN permOut0` rows). Width 8 always. -/
def permOut0 : List ℤ → List ℤ := fun _ => [0, 0, 0, 0, 0, 0, 0, 0]

theorem permOut0_width8 : Poseidon2Width8 permOut0 := fun _ => rfl

/-- Honest row 0: value 5 (limbs `[5,0,0,0]`), asset 2 (`[2,0,0,0]`), owner 9, randomness 3,
recomposed `value_mod_p = 5` / `asset_mod_p = 2`, out_val 4, acc = 5 − 4 = 1. -/
def honRow0 : Assignment := fun j =>
  if j = 0 then 5 else if j = 4 then 2 else if j = 8 then 9 else if j = 9 then 3
  else if j = 10 then 5 else if j = 11 then 2 else if j = 13 then 4 else if j = 14 then 1
  else 0

/-- Honest row 1: value 3, asset 2, owner 8, randomness 6, out_val 4, acc = 1 + 3 − 4 = 0. -/
def honRow1 : Assignment := fun j =>
  if j = 0 then 3 else if j = 4 then 2 else if j = 8 then 8 else if j = 9 then 6
  else if j = 10 then 3 else if j = 11 then 2 else if j = 13 then 4 else 0

/-- Row 0's genuine WIDE chip row: `arity 11 :: padded [DOMAIN,5,0,0,0,2,0,0,0,3,0] :: 8 zero
lanes` (`permOut0`'s squeeze). -/
def wideChip0 : List ℤ :=
  [11, 1447185968, 5, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0]
/-- Row 0's genuine leaf chip row: `arity 7 :: padded [5,2,9,3,0,MARK,1] :: 8 lanes`. -/
def leafChip0 : List ℤ :=
  [7, 5, 2, 9, 3, 0, 64207, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0]
/-- Row 1's genuine WIDE chip row. -/
def wideChip1 : List ℤ :=
  [11, 1447185968, 3, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0]
/-- Row 1's genuine leaf chip row. -/
def leafChip1 : List ℤ :=
  [7, 3, 2, 8, 6, 0, 64207, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0]

/-- The witness trace family: the chip table carries exactly the four genuine wide rows. -/
def honChipTbl : List (List ℤ) := [wideChip0, leafChip0, wideChip1, leafChip1]

def honTf : TraceFamily := fun tid =>
  match tid with
  | .poseidon2 => honChipTbl
  | .custom 3  => narrowTable honChipTbl
  | _ => []

/-- The honest family wires the NARROW bus to the 18-prefix of its wide chip table — ONE physical
chip serving both buses, exactly the deployed Rust `narrow_hist` serving (definitional). -/
theorem honTf_narrow_wire :
    honTf poseidon2narrow = narrowTable (honTf TableId.poseidon2) := rfl

/-- The honest balanced 2-row witness: 5 + 3 in ≡ 4 + 4 out. -/
def honestTrace : VmTrace := { rows := [honRow0, honRow1], pub := zeroAsg, tf := honTf }

-- The witness really is balanced; the mint below really is not.
#guard decide (prefixSum (vmodAt honestTrace) 1 = 8 ∧ prefixSum (outAt honestTrace) 1 = 8)

/-- The witness chip table is WIDE-sound: every row is a genuine `chipRowN permOut0` tuple. -/
theorem honTf_soundN : ChipTableSoundN permOut0 (honTf TableId.poseidon2) := by
  intro r hr
  simp only [honTf, honChipTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨[1447185968, 5, 0, 0, 0, 2, 0, 0, 0, 3, 0], by decide, by decide⟩
  · exact ⟨[5, 2, 9, 3, 0, 64207, 1], by decide, by decide⟩
  · exact ⟨[1447185968, 3, 0, 0, 0, 2, 0, 0, 0, 6, 0], by decide, by decide⟩
  · exact ⟨[3, 2, 8, 6, 0, 64207, 1], by decide, by decide⟩

/-- **The descriptor is SATISFIABLE by an honest balanced clearing** — an explicit witness,
so the UNSAT teeth are not vacuously true of an empty relation. -/
theorem honest_balanced_satisfies :
    Satisfied2 hzero shieldedWideValueLinkDesc (fun _ => 0) (fun _ => (0, 0)) [] honestTrace := by
  have hmemlog : memLog shieldedWideValueLinkDesc honestTrace = [] := rfl
  have hmaplog : mapLog shieldedWideValueLinkDesc honestTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    have hi2 : i = 0 ∨ i = 1 := by
      have hx : i < 2 := hi
      omega
    simp only [shieldedWideValueLinkDesc, wideLinkClearConstraints, wideLinkConstraints,
      conservationConstraints, claimPins, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hi2 with rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [lkLeafCommit, wideBindLookup, recompVBody, recompABody, limbRecompE,
        accStep, accWindow, wsub, seedBody, esub, eadd, emul, eneg, ev, ek,
        Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
        Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt,
        Dregg2.Circuit.DescriptorIR2.WindowConstraint.holdsAt,
        Dregg2.Circuit.Emit.EffectVmEmit.VmConstraint.holdsVm,
        Dregg2.Circuit.DescriptorIR2.WindowExpr.eval,
        envAt, honestTrace, honTf, EmittedExpr.eval,
        List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceBEq, reduceIte, reduceCtorEq] <;>
      decide
  · -- rowHashes: no v1 hash sites
    intro i _
    exact trivial
  · -- rowRanges: the 8 limb teeth on both rows
    intro i hi r hr
    have hi2 : i = 0 ∨ i = 1 := by
      have hx : i < 2 := hi
      omega
    simp only [shieldedWideValueLinkDesc, limbRanges, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hi2 with rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Dregg2.Circuit.Emit.EffectVmEmit.VmRange.holds, envAt, honestTrace] <;>
      decide
  · -- memAddrsNodup
    simp
  · -- memClosed
    intro op hop
    rw [hmemlog] at hop
    cases hop
  · -- memDisciplined
    rw [hmemlog]
    trivial
  · -- memBalanced (empty boundary, empty log)
    rw [hmemlog]
    rfl
  · -- memTableFaithful
    rw [hmemlog]
    rfl
  · -- mapTableFaithful
    rw [hmaplog]
    rfl

/-- A concrete MINT attempt: same honest inputs (5 + 3 = 8 in) but 4 + 5 = 9 out. -/
def mintRow1 : Assignment := fun j =>
  if j = 0 then 3 else if j = 4 then 2 else if j = 8 then 8 else if j = 9 then 6
  else if j = 10 then 3 else if j = 11 then 2 else if j = 13 then 5 else 0

def mintTrace : VmTrace := { rows := [honRow0, mintRow1], pub := zeroAsg, tf := honTf }

#guard decide (prefixSum (vmodAt mintTrace) 1 = 8 ∧ prefixSum (outAt mintTrace) 1 = 9)

/-- **The mint tooth BITES a concrete forged instance** (8 in, 9 out ⇒ refused). -/
theorem mint_refused :
    ¬ Satisfied2 hzero shieldedWideValueLinkDesc (fun _ => 0) (fun _ => (0, 0)) [] mintTrace :=
  wide_mint_unbalanced_unsat hzero (fun _ => 0) (fun _ => (0, 0)) [] mintTrace
    (by simp [mintTrace]) (by decide)

/-- A concrete DECOUPLING attempt: the honest rows, but the published lane-0 wide-binding PI
is 1 while the genuine wide squeeze of the leaf's cells is `permOut0 … = [0,…]`. -/
def decoupledPub : Assignment := fun k => if k = 0 then 1 else 0

def decoupledTrace : VmTrace := { rows := [honRow0, honRow1], pub := decoupledPub, tf := honTf }

/-- **The decoupling tooth BITES a concrete forged instance** (published wide binding ≠ the
leaf's genuine 8-felt digest ⇒ refused). -/
theorem decoupled_refused :
    ¬ Satisfied2 hzero shieldedWideValueLinkDesc (fun _ => 0) (fun _ => (0, 0)) []
      decoupledTrace :=
  wide_decoupled_unsat permOut0 permOut0_width8 hzero (fun _ => 0) (fun _ => (0, 0)) []
    decoupledTrace (by simp [decoupledTrace]) honTf_soundN (by rfl) (by decide)

/-- **The headline fires on concrete carriers**: the inhabited floor (`packPerm`) against the
all-zero legacy binding — the collision pair exists, the wide binding separates it. -/
theorem birthday_tooth_fires :
    ∃ o₁ o₂ : WideOpening, CanonicalOpening o₁ ∧ CanonicalOpening o₂ ∧ o₁ ≠ o₂ ∧
      (fun _ : WideOpening => (0 : ℤ)) o₁ = (fun _ : WideOpening => (0 : ℤ)) o₂ ∧
      packPerm (wideAbsorb o₁) ≠ packPerm (wideAbsorb o₂) :=
  birthday_collision_no_longer_forges packPerm wideBindingCR_satisfiable.2
    (fun _ => 0) (fun _ _ => by simp)

/-! ## §9 — the byte-pinned wire golden (generated once via `#eval repr (emitVmJson2 …)`;
the Rust decoder ingests THIS string at the coordinated integrator step). -/

/-- Exact emitted-wire golden (generated via
`#eval repr (emitVmJson2 shieldedWideValueLinkDesc)`). Rust includes these bytes verbatim at
the coordinated integrator step. -/
def SHIELDED_WIDE_VALUE_LINK_CONSERVE_GOLDEN : String :=
  "{\"name\":\"dregg-shielded-wide-value-link-conserve::v1\",\"ir\":2,\"trace_width\":23,\"public_input_count\":9,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"var\",\"v\":1}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4294967296},\"r\":{\"t\":\"var\",\"v\":2}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":281474976710656},\"r\":{\"t\":\"var\",\"v\":3}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4294967296},\"r\":{\"t\":\"var\",\"v\":6}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":281474976710656},\"r\":{\"t\":\"var\",\"v\":7}}}}}}}},{\"t\":\"lookup\",\"table\":8,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":12}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":11},{\"t\":\"const\",\"v\":1447185968},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":9},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22}]},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"var\",\"v\":1}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4294967296},\"r\":{\"t\":\"var\",\"v\":2}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":281474976710656},\"r\":{\"t\":\"var\",\"v\":3}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4294967296},\"r\":{\"t\":\"var\",\"v\":6}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":281474976710656},\"r\":{\"t\":\"var\",\"v\":7}}}}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":13}}}}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"var\",\"v\":14}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":15,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":16,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":17,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":18,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":19,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":20,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":21,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":22,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":12,\"pi_index\":8}],\"hash_sites\":[],\"ranges\":[{\"wire\":0,\"bits\":16},{\"wire\":1,\"bits\":16},{\"wire\":2,\"bits\":16},{\"wire\":3,\"bits\":16},{\"wire\":4,\"bits\":16},{\"wire\":5,\"bits\":16},{\"wire\":6,\"bits\":16},{\"wire\":7,\"bits\":16}]}"

#guard emitVmJson2 shieldedWideValueLinkDesc == SHIELDED_WIDE_VALUE_LINK_CONSERVE_GOLDEN

/-! ## §10 — axiom hygiene on the keystones. -/

#assert_axioms honTf_narrow_wire
#assert_axioms wide_value_link_bound
#assert_axioms wide_decoupled_unsat
#assert_axioms wide_conservation_holds
#assert_axioms wide_mint_unbalanced_unsat
#assert_axioms narrow_binding_collision_exists
#assert_axioms wideBindingCR_satisfiable
#assert_axioms birthday_collision_no_longer_forges
#assert_axioms wide_binding_binds
#assert_axioms chipTableSound_of_soundN
#assert_axioms honest_balanced_satisfies
#assert_axioms mint_refused
#assert_axioms decoupled_refused
#assert_axioms birthday_tooth_fires

end Dregg2.Circuit.Emit.ShieldedWideValueLinkDescriptor
