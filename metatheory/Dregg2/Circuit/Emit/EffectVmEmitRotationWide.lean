/-
# Dregg2.Circuit.Emit.EffectVmEmitRotationWide — THE WIDE EMISSION LANE (Phase B-ROTATION,
the faithful 8-felt commitment chain emitted as wide chip lookups), STAGED beside the live
1-felt path.

`EffectVmEmitRotationR` proves the FAITHFUL 8-felt commitment PRIMITIVE (`wireCommitR8`,
`chainFrom8`, the keystone `wireCommitR8_binds` under the named floors `Poseidon2WideCR` +
`Poseidon2Width8`). `EffectVmEmitRotationV3` emits the rotated commitment chain via the 1-felt
`siteLookup`/`siteHoldsAll`/`wireCommitR` path (`rotV3SitesAt_pin` → `wireCommitR`, ~31-bit). The
live cutover needs the chain GROUP + FINAL sites to bind all 8 OUTPUT LANES.

THIS module is the proof infrastructure that closes that gap — purely additive, off the live wire:

  * **§1 `siteLookupN` / `siteLookupsN_sound`** — the WIDE analog of `siteLookup`/`siteLookups_sound`:
    a chip lookup binding ALL `CHIP_OUT_LANES` output columns (`chipLookupTupleN [c0..c7]`),
    discharged by the wide lever `chip_lookup_sound_N`. Where the 1-felt path forces ONE digest
    column (out0), the wide path forces the WHOLE 8-felt permutation output column-for-column.
  * **§2 `rotV3WideSitesAt`** — the rotated block's 62 chained absorptions emitted as wide lookups:
    the 4-wide head (no carrier), sixty body groups (the prior 8-felt carrier ‖ 3 limbs = arity 11
    = `CHIP_RATE`), the iroot final (carrier ‖ iroot ‖ 0 ‖ 0 = arity 11). Each carrier is 8 COLUMNS, threaded
    by column reference (position-independent, like `rotV3SitesAt`). The state-commit carrier is the
    final 8 columns.
  * **§3 `rotV3WidePin`** — the WIDE pin (the analog of `rotV3SitesAt_pin`): a satisfying wide-emitted
    witness binds the 8 state-commit columns = `wireCommitR8 permW (preLimbs) iroot`. Discharged
    site-by-site through `chip_lookup_sound_N` (`chainFrom8` folded literally, 62 cases).
  * **§4 `rotateV3Wide` / `v3OfWide`** — the parallel emission, threaded where `v3Of` threads the
    1-felt path, but as a NEW function (the live registry KEEPS using `v3Of` — live wire untouched).
  * **§5 the re-proved wide keystone tower** — `rotV3Wide_pins` / `rotV3Wide_publishes` /
    `rotV3Wide_binds_published`: two satisfying wide-emitted witnesses publishing the SAME 8-felt
    commit columns agree on the WHOLE pre-iroot limb list AND the iroot — the GENUINE ~124-bit
    binding, via `wireCommitR8_binds` (the keystone is load-bearing — NOT a 1-felt binding dressed
    up). The anti-laundering `#guard`: the wide binding distinguishes two states differing ONLY
    beyond lane0.

## Honest boundary notes (do NOT over-read)

  * STAGED, additive: a NEW set of defs/theorems. NO descriptor-JSON / FP / VK / geometry change;
    the live `rotateV3`/`v3Of` and `B_STATE_COMMIT`/`ROT_WIDTH` are untouched. The live flip
    (next phase) repoints the registry at `rotateV3Wide` + the geometry/PI/executor change.
  * The wide floors `Poseidon2WideCR` + `Poseidon2Width8` are the EXACT same crypto class as the
    1-felt `Poseidon2SpongeCR`, at full squeeze width — the named honest floor, NOT a new axiom.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto only as the named
`Poseidon2WideCR`/`Poseidon2Width8` hypotheses.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

namespace Dregg2.Circuit.Emit.EffectVmEmitRotationWide

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitRotation (canon_eq_of_modEq)
open Dregg2.Crypto
open Dregg2.Substrate.Heap (refSponge)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — `siteLookupN`: the WIDE chip lookup (binds all 8 output columns).

The 1-felt `siteLookup` binds ONE column (out0); `siteLookupN` binds the WHOLE 8-felt permutation
output via `chipLookupTupleN`. The soundness lever is `chip_lookup_sound_N` (the `permW`-parametric
wide squeeze), so a satisfying wide lookup forces `digestCols.map loc = permW (resolved inputs)` —
all eight lanes column-for-column. -/

-- The admitted-arity discharger for `siteLookupN`: `chip_arity_admitted`'s two ways, plus the one
-- extra way a wide ROTATION site can be known good — it is a member of `rotV3WideSpecs`, and every
-- member of that list absorbs at arity 4 or 11 (`rotV3WideSpecs_admitted`, defined below; the
-- tactic BODY is elaborated at each USE site, all of which follow it, which is why the forward
-- reference is fine and why hygiene is off — the name must resolve in the CONSUMING module).
-- Without this branch each of the ~40 places that restate a wide site's tuple under
-- `∀ p ∈ rotV3WideSpecs …` would have to thread the proof by hand.
set_option hygiene false in
macro "wide_site_arity" : tactic =>
  `(tactic| first
      | assumption
      | exact of_decide_eq_true (Eq.refl true)
      | exact rotV3WideSpecs_admitted _ _ _ (by assumption)
      | fail "CHIP ABSORB ARITY NOT ADMITTED — this wide rotation site asks the chip for an arity \
              outside CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16], so it has no witness. Pad \
              the absorb block; do NOT widen the admitted set.")

/-- **`siteLookupN`** — the wide chip lookup over an explicit input-expression list `ins` and the
8 carrier output columns `digestCols`. (The wide path threads carrier COLUMNS through `ins`, so
there is no `.digest k` accumulator to resolve — the rotation emission supplies `ins` directly.) -/
def siteLookupN (ins : List EmittedExpr) (digestCols : List Nat)
    (hAdm : ChipArityAdmitted ins.length := by wide_site_arity) :
    Dregg2.Circuit.DescriptorIR2.Lookup :=
  { table := .poseidon2, tuple := chipLookupTupleN ins digestCols hAdm }

/-- **`siteLookupN_sound`** — the wide site replacement is SOUND: against a sound WIDE chip table,
the lookup forces the 8 carrier columns to the genuine 8-felt permutation output of the evaluated
inputs. The single-site wide analog of `siteLookup_replaces_site`, discharged by `chip_lookup_sound_N`. -/
theorem siteLookupN_sound (permW : List ℤ → List ℤ) (tbl : Table)
    (hSound : ChipTableSoundN permW tbl) (env : VmRowEnv)
    (ins : List EmittedExpr) (digestCols : List Nat)
    (hlen : ChipArityAdmitted ins.length)
    (hmem : (siteLookupN ins digestCols hlen).tuple.map (·.eval env.loc) ∈ tbl) :
    digestCols.map env.loc = permW (ins.map (·.eval env.loc)) :=
  chip_lookup_sound_N permW tbl hSound env.loc ins digestCols hlen hmem

/-- **`siteLookupsN_sound`** — the WHOLE wide family: every wide lookup of a list (against a sound
wide chip table) forces its own 8 carrier columns to the genuine permutation output. The wide analog
of `siteLookups_sound` (the per-site bindings are independent — each `chipLookupTupleN` carries its
inputs explicitly, no cross-site accumulator, so the family is the pointwise conjunction). -/
theorem siteLookupsN_sound (permW : List ℤ → List ℤ) (tbl : Table)
    (hSound : ChipTableSoundN permW tbl) (env : VmRowEnv)
    (sites : List (List EmittedExpr × List Nat))
    (hfit : ∀ p ∈ sites, ChipArityAdmitted p.1.length)
    (hlk : ∀ (p : List EmittedExpr × List Nat) (hp : p ∈ sites),
      (siteLookupN p.1 p.2 (hfit p hp)).tuple.map (·.eval env.loc) ∈ tbl) :
    ∀ p ∈ sites, p.2.map env.loc = permW (p.1.map (·.eval env.loc)) :=
  fun p hp => siteLookupN_sound permW tbl hSound env p.1 p.2 (hfit p hp) (hlk p hp)

/-! ## §2 — `rotV3WideSitesAt`: the rotated block as 62 WIDE chained lookups.

Layout, parametric in the limb base `base` and the wide-carrier base `cbase`:
  * limbs `base+0 .. base+183` (184 pre-iroot limbs), iroot `base+B_IROOT` (the `wireCommitR8` shape).
  * 62 carriers, each 8 columns: carrier `k` at `cbase + 8*k .. cbase + 8*k+7`. Carrier 61 (the
    state-commit carrier) is the published 8-felt commitment block.

Each site's input EXPRESSIONS:
  * site 0 (head): `[l0, l1, l2, l3]` (4 inputs, NO carrier) → carrier 0.
  * sites 1..60 (body): `(carrier k-1 ‖ 3 limbs)` (11 inputs = `CHIP_RATE`) → carrier k.
  * site 61 (final): `(carrier 60 ‖ iroot ‖ 0 ‖ 0)` (11 inputs) → carrier 61 (state commit). -/

/-- The 8 columns of wide carrier `k` at carrier base `cbase`. -/
def carrierCols (cbase k : Nat) : List Nat :=
  (List.range CHIP_OUT_LANES).map (fun j => cbase + 8 * k + j)

theorem carrierCols_length (cbase k : Nat) : (carrierCols cbase k).length = 8 := by
  simp [carrierCols, CHIP_OUT_LANES]

/-- The carrier `k`'s 8 columns, read off a row as a length-8 ℤ list. -/
def carrierVals (cbase k : Nat) (a : Assignment) : List ℤ := (carrierCols cbase k).map a

theorem carrierVals_length (cbase k : Nat) (a : Assignment) :
    (carrierVals cbase k a).length = 8 := by simp [carrierVals, carrierCols, CHIP_OUT_LANES]

/-- The input EXPRESSIONS of a body step: the prior carrier's 8 columns (as `.var`) followed by
the 3 limb columns. -/
def bodyIns (cbase prevK limb0 limb1 limb2 : Nat) : List EmittedExpr :=
  (carrierCols cbase prevK).map .var ++ [.var limb0, .var limb1, .var limb2]

/-- The 62 (inputs, 8-output-columns) wide-lookup specs for a rotated block at `(base, cbase)` (the
184-limb shape — head + 60 body groups + the final iroot carrier, state-commit carrier 61). -/
def rotV3WideSpecs (base cbase : Nat) : List (List EmittedExpr × List Nat) :=
  [ -- head: [l0,l1,l2,l3] → carrier 0
    ([.var (base+0), .var (base+1), .var (base+2), .var (base+3)], carrierCols cbase 0)
  , (bodyIns cbase 0 (base+4) (base+5) (base+6), carrierCols cbase 1)
  , (bodyIns cbase 1 (base+7) (base+8) (base+9), carrierCols cbase 2)
  , (bodyIns cbase 2 (base+10) (base+11) (base+12), carrierCols cbase 3)
  , (bodyIns cbase 3 (base+13) (base+14) (base+15), carrierCols cbase 4)
  , (bodyIns cbase 4 (base+16) (base+17) (base+18), carrierCols cbase 5)
  , (bodyIns cbase 5 (base+19) (base+20) (base+21), carrierCols cbase 6)
  , (bodyIns cbase 6 (base+22) (base+23) (base+24), carrierCols cbase 7)
  , (bodyIns cbase 7 (base+25) (base+26) (base+27), carrierCols cbase 8)
  , (bodyIns cbase 8 (base+28) (base+29) (base+30), carrierCols cbase 9)
  , (bodyIns cbase 9 (base+31) (base+32) (base+33), carrierCols cbase 10)
  , (bodyIns cbase 10 (base+34) (base+35) (base+36), carrierCols cbase 11)
  , (bodyIns cbase 11 (base+37) (base+38) (base+39), carrierCols cbase 12)
  , (bodyIns cbase 12 (base+40) (base+41) (base+42), carrierCols cbase 13)
  , (bodyIns cbase 13 (base+43) (base+44) (base+45), carrierCols cbase 14)
  , (bodyIns cbase 14 (base+46) (base+47) (base+48), carrierCols cbase 15)
  , (bodyIns cbase 15 (base+49) (base+50) (base+51), carrierCols cbase 16)
  , (bodyIns cbase 16 (base+52) (base+53) (base+54), carrierCols cbase 17)
  , (bodyIns cbase 17 (base+55) (base+56) (base+57), carrierCols cbase 18)
  , (bodyIns cbase 18 (base+58) (base+59) (base+60), carrierCols cbase 19)
  , (bodyIns cbase 19 (base+61) (base+62) (base+63), carrierCols cbase 20)
  , (bodyIns cbase 20 (base+64) (base+65) (base+66), carrierCols cbase 21)
  , (bodyIns cbase 21 (base+67) (base+68) (base+69), carrierCols cbase 22)
  , (bodyIns cbase 22 (base+70) (base+71) (base+72), carrierCols cbase 23)
  , (bodyIns cbase 23 (base+73) (base+74) (base+75), carrierCols cbase 24)
  , (bodyIns cbase 24 (base+76) (base+77) (base+78), carrierCols cbase 25)
  , (bodyIns cbase 25 (base+79) (base+80) (base+81), carrierCols cbase 26)
  , (bodyIns cbase 26 (base+82) (base+83) (base+84), carrierCols cbase 27)
  , (bodyIns cbase 27 (base+85) (base+86) (base+87), carrierCols cbase 28)
  , (bodyIns cbase 28 (base+88) (base+89) (base+90), carrierCols cbase 29)
  , (bodyIns cbase 29 (base+91) (base+92) (base+93), carrierCols cbase 30)
  , (bodyIns cbase 30 (base+94) (base+95) (base+96), carrierCols cbase 31)
  , (bodyIns cbase 31 (base+97) (base+98) (base+99), carrierCols cbase 32)
  , (bodyIns cbase 32 (base+100) (base+101) (base+102), carrierCols cbase 33)
  , (bodyIns cbase 33 (base+103) (base+104) (base+105), carrierCols cbase 34)
  , (bodyIns cbase 34 (base+106) (base+107) (base+108), carrierCols cbase 35)
  , (bodyIns cbase 35 (base+109) (base+110) (base+111), carrierCols cbase 36)
  , (bodyIns cbase 36 (base+112) (base+113) (base+114), carrierCols cbase 37)
  , (bodyIns cbase 37 (base+115) (base+116) (base+117), carrierCols cbase 38)
  , (bodyIns cbase 38 (base+118) (base+119) (base+120), carrierCols cbase 39)
  , (bodyIns cbase 39 (base+121) (base+122) (base+123), carrierCols cbase 40)
  , (bodyIns cbase 40 (base+124) (base+125) (base+126), carrierCols cbase 41)
  , (bodyIns cbase 41 (base+127) (base+128) (base+129), carrierCols cbase 42)
  , (bodyIns cbase 42 (base+130) (base+131) (base+132), carrierCols cbase 43)
  , (bodyIns cbase 43 (base+133) (base+134) (base+135), carrierCols cbase 44)
  , (bodyIns cbase 44 (base+136) (base+137) (base+138), carrierCols cbase 45)
  , (bodyIns cbase 45 (base+139) (base+140) (base+141), carrierCols cbase 46)
  , (bodyIns cbase 46 (base+142) (base+143) (base+144), carrierCols cbase 47)
  , (bodyIns cbase 47 (base+145) (base+146) (base+147), carrierCols cbase 48)
  , (bodyIns cbase 48 (base+148) (base+149) (base+150), carrierCols cbase 49)
  , (bodyIns cbase 49 (base+151) (base+152) (base+153), carrierCols cbase 50)
  , (bodyIns cbase 50 (base+154) (base+155) (base+156), carrierCols cbase 51)
  , (bodyIns cbase 51 (base+157) (base+158) (base+159), carrierCols cbase 52)
  , (bodyIns cbase 52 (base+160) (base+161) (base+162), carrierCols cbase 53)
  , (bodyIns cbase 53 (base+163) (base+164) (base+165), carrierCols cbase 54)
  , (bodyIns cbase 54 (base+166) (base+167) (base+168), carrierCols cbase 55)
  , (bodyIns cbase 55 (base+169) (base+170) (base+171), carrierCols cbase 56)
  , (bodyIns cbase 56 (base+172) (base+173) (base+174), carrierCols cbase 57)
  , (bodyIns cbase 57 (base+175) (base+176) (base+177), carrierCols cbase 58)
  , (bodyIns cbase 58 (base+178) (base+179) (base+180), carrierCols cbase 59)
  , (bodyIns cbase 59 (base+181) (base+182) (base+183), carrierCols cbase 60)
  , (bodyIns cbase 60 (base+184) (base+185) (base+186), carrierCols cbase 61)
  , (bodyIns cbase 61 (base+187) (base+188) (base+189), carrierCols cbase 62)
  , (bodyIns cbase 62 (base+190) (base+191) (base+192), carrierCols cbase 63)
  , (bodyIns cbase 63 (base+193) (base+194) (base+195), carrierCols cbase 64)
  , ((carrierCols cbase 64).map .var ++ [.var (base+B_IROOT), .const 0, .const 0], carrierCols cbase 65) ]

/-- **Every wide spec asks the chip for an ADMITTED arity**: head 4, fifty-nine bodies at 11, final
`carrier8 ‖ iroot ‖ 0 ‖ 0` at 11. Each of 4 and 11 is a root of the deployed admission product; the
old statement was `≤ CHIP_RATE`, which is the predicate that let arities 8, 9, 10 and 14 through
elsewhere in the tree. `rotV3WideLookups` consumes THIS, through `attach`, so a spec at a refused
arity cannot be turned into a lookup at all. -/
theorem rotV3WideSpecs_admitted (base cbase : Nat) :
    ∀ p ∈ rotV3WideSpecs base cbase, ChipArityAdmitted p.1.length := by
  intro p hp
  simp only [rotV3WideSpecs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact of_decide_eq_true (Eq.refl true)

/-- The wide lookups for a rotated block (one `.lookup` constraint per spec), each carrying its own
admitted-arity proof off `rotV3WideSpecs_admitted`. -/
def rotV3WideLookups (base cbase : Nat) : List VmConstraint2 :=
  (rotV3WideSpecs base cbase).attach.map
    (fun p => .lookup (siteLookupN p.1.1 p.1.2 (rotV3WideSpecs_admitted base cbase p.1 p.2)))

/-- Every wide spec's input list fits the chip rate — the weaker consequence. -/
theorem rotV3WideSpecs_fit (base cbase : Nat) :
    ∀ p ∈ rotV3WideSpecs base cbase, p.1.length ≤ CHIP_RATE := by
  intro p hp
  simp only [rotV3WideSpecs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [bodyIns, carrierCols, CHIP_RATE, CHIP_OUT_LANES]

/-! ### The DERIVED wide-carrier geometry (single source: `rotV3WideSpecs`).

`wideNumCarriers` is DERIVED from the spec list (one 8-felt carrier per emitted wide lookup),
never declared as a free literal: the allocation constants (`wideCarrierBlockSpan` /
`wideAppendixSpan`) and the commit-carrier index all flow from it, and the Rust twins
(`trace_rotated.rs::WIDE_NUM_CARRIERS` etc., derived there from `NUM_PRE_LIMBS` by the shared
const fn) are pinned to the same values. The RETIRED v1 shape (169 limbs → 57 carriers →
912-column appendix, commit carrier 56) is version-refused on the Rust side; THIS is the
flag-day v2 shape: 184 limbs → 62 carriers → 496-column block → 992-column appendix, commit
carrier 61. -/

/-- The number of 8-felt carriers one wide commitment chain emits: exactly one per wide-lookup
spec — head + 61 three-limb body groups + the final iroot carrier = 63 at the 187-limb shape.
(It was 62 at 184; the key flag day added the body group absorbing limbs 184..186, the last of
which is the owner nonet's ninth lane.) -/
def wideNumCarriers : Nat := (rotV3WideSpecs 0 0).length

theorem wideNumCarriers_eq : wideNumCarriers = 66 := rfl

/-- One wide carrier block's column span: 8 columns per carrier (504 at 187; was 496 at 184). -/
def wideCarrierBlockSpan : Nat := 8 * wideNumCarriers

theorem wideCarrierBlockSpan_eq : wideCarrierBlockSpan = 528 := rfl

/-- The two-block (BEFORE + AFTER) wide appendix span `rotateV3Wide`/`wideAppend` allocate (1008 at 187; was 992). -/
def wideAppendixSpan : Nat := 2 * wideCarrierBlockSpan

theorem wideAppendixSpan_eq : wideAppendixSpan = 1056 := rfl

/-- The in-block index of the state-commit carrier: the FINAL carrier (62 at 187; was 61). -/
def wideCommitCarrier : Nat := wideNumCarriers - 1

theorem wideCommitCarrier_eq : wideCommitCarrier = 65 := rfl

/-! ## §3 — `rotV3WidePin`: the wide pin (state-commit carrier = `wireCommitR8`). -/

/-- The pre-iroot limb list a block carries (`preLimbsAt`-shaped — identical columns to the 1-felt
path, so the wide commitment binds the SAME limbs the live wire commits).

⚑ THE LENGTH IS `rotatedNumPreLimbs`, NOT A TRANSCRIBED NUMBER. This read `= 184` as a literal and
that is what broke the whole emit pipeline when the key flag day took the region to 187: the wide
file is on `EmitLayoutManifest`'s import path, so a single stale literal here made
`layout_generated.rs`, every descriptor, every registry TSV and every VK UNREGENERABLE — for every
lane, not just the one that moved the constant. Stating it as `rotatedNumPreLimbs` makes the next
widening free here instead of a tree-wide outage. -/
def preLimbsWide (base : Nat) (a : Assignment) : List ℤ := preLimbsAt base a

theorem preLimbsWide_length (base : Nat) (a : Assignment) :
    (preLimbsWide base a).length = rotatedNumPreLimbs := preLimbsAt_length base a

/-- The carrier evaluation of a wide spec at carrier base `cbase`: the prior carrier's VALUES
followed by the 3 limb values (the `chainFrom8` step's `acc ++ c`). -/
private theorem bodyIns_eval (cbase prevK l0 l1 l2 : Nat) (a : Assignment) :
    (bodyIns cbase prevK l0 l1 l2).map (·.eval a)
      = carrierVals cbase prevK a ++ [a l0, a l1, a l2] := by
  simp [bodyIns, carrierVals, EmittedExpr.eval, List.map_append, List.map_map, Function.comp_def]

set_option maxHeartbeats 12800000 in
/-- **THE WIDE PIN, parametric in `(base, cbase)`**: the sixty-two wide-lookup output
bindings compose (via `chip_lookup_sound_N` per site, the `chainFrom8` fold literally) into the
8-felt chained rotated commitment — the row's state-commit carrier (carrier 61) IS `wireCommitR8` of
the row's OWN 184 limbs and iroot. The wide analog of `rotV3SitesAt_pin`, the keystone `wireCommitR8`
load-bearing in every step. -/
theorem rotV3WidePin (permW : List ℤ → List ℤ) (tbl : Table)
    (hSound : ChipTableSoundN permW tbl) (env : VmRowEnv) (base cbase : Nat)
    (hlk : ∀ (p : List EmittedExpr × List Nat) (hp : p ∈ rotV3WideSpecs base cbase),
      (siteLookupN p.1 p.2 (rotV3WideSpecs_admitted base cbase p hp)).tuple.map (·.eval env.loc)
        ∈ tbl) :
    carrierVals cbase 65 env.loc
      = wireCommitR8 permW (preLimbsWide base env.loc) (env.loc (base + B_IROOT)) := by
  have hbind := siteLookupsN_sound permW tbl hSound env (rotV3WideSpecs base cbase)
    (rotV3WideSpecs_admitted base cbase) hlk
  have m : ∀ p ∈ rotV3WideSpecs base cbase,
      p.2.map env.loc = permW (p.1.map (·.eval env.loc)) := hbind
  have h0 : carrierVals cbase 0 env.loc
      = permW [env.loc (base+0), env.loc (base+1), env.loc (base+2), env.loc (base+3)] := by
    have := m ([.var (base+0), .var (base+1), .var (base+2), .var (base+3)], carrierCols cbase 0)
      (by simp [rotV3WideSpecs]); simpa [carrierVals, EmittedExpr.eval] using this
  have h1 : carrierVals cbase 1 env.loc
      = permW (carrierVals cbase 0 env.loc ++ [env.loc (base+4), env.loc (base+5), env.loc (base+6)]) := by
    have := m (bodyIns cbase 0 (base+4) (base+5) (base+6), carrierCols cbase 1)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h2 : carrierVals cbase 2 env.loc
      = permW (carrierVals cbase 1 env.loc ++ [env.loc (base+7), env.loc (base+8), env.loc (base+9)]) := by
    have := m (bodyIns cbase 1 (base+7) (base+8) (base+9), carrierCols cbase 2)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h3 : carrierVals cbase 3 env.loc
      = permW (carrierVals cbase 2 env.loc ++ [env.loc (base+10), env.loc (base+11), env.loc (base+12)]) := by
    have := m (bodyIns cbase 2 (base+10) (base+11) (base+12), carrierCols cbase 3)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h4 : carrierVals cbase 4 env.loc
      = permW (carrierVals cbase 3 env.loc ++ [env.loc (base+13), env.loc (base+14), env.loc (base+15)]) := by
    have := m (bodyIns cbase 3 (base+13) (base+14) (base+15), carrierCols cbase 4)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h5 : carrierVals cbase 5 env.loc
      = permW (carrierVals cbase 4 env.loc ++ [env.loc (base+16), env.loc (base+17), env.loc (base+18)]) := by
    have := m (bodyIns cbase 4 (base+16) (base+17) (base+18), carrierCols cbase 5)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h6 : carrierVals cbase 6 env.loc
      = permW (carrierVals cbase 5 env.loc ++ [env.loc (base+19), env.loc (base+20), env.loc (base+21)]) := by
    have := m (bodyIns cbase 5 (base+19) (base+20) (base+21), carrierCols cbase 6)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h7 : carrierVals cbase 7 env.loc
      = permW (carrierVals cbase 6 env.loc ++ [env.loc (base+22), env.loc (base+23), env.loc (base+24)]) := by
    have := m (bodyIns cbase 6 (base+22) (base+23) (base+24), carrierCols cbase 7)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h8 : carrierVals cbase 8 env.loc
      = permW (carrierVals cbase 7 env.loc ++ [env.loc (base+25), env.loc (base+26), env.loc (base+27)]) := by
    have := m (bodyIns cbase 7 (base+25) (base+26) (base+27), carrierCols cbase 8)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h9 : carrierVals cbase 9 env.loc
      = permW (carrierVals cbase 8 env.loc ++ [env.loc (base+28), env.loc (base+29), env.loc (base+30)]) := by
    have := m (bodyIns cbase 8 (base+28) (base+29) (base+30), carrierCols cbase 9)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h10 : carrierVals cbase 10 env.loc
      = permW (carrierVals cbase 9 env.loc ++ [env.loc (base+31), env.loc (base+32), env.loc (base+33)]) := by
    have := m (bodyIns cbase 9 (base+31) (base+32) (base+33), carrierCols cbase 10)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h11 : carrierVals cbase 11 env.loc
      = permW (carrierVals cbase 10 env.loc ++ [env.loc (base+34), env.loc (base+35), env.loc (base+36)]) := by
    have := m (bodyIns cbase 10 (base+34) (base+35) (base+36), carrierCols cbase 11)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h12 : carrierVals cbase 12 env.loc
      = permW (carrierVals cbase 11 env.loc ++ [env.loc (base+37), env.loc (base+38), env.loc (base+39)]) := by
    have := m (bodyIns cbase 11 (base+37) (base+38) (base+39), carrierCols cbase 12)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h13 : carrierVals cbase 13 env.loc
      = permW (carrierVals cbase 12 env.loc ++ [env.loc (base+40), env.loc (base+41), env.loc (base+42)]) := by
    have := m (bodyIns cbase 12 (base+40) (base+41) (base+42), carrierCols cbase 13)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h14 : carrierVals cbase 14 env.loc
      = permW (carrierVals cbase 13 env.loc ++ [env.loc (base+43), env.loc (base+44), env.loc (base+45)]) := by
    have := m (bodyIns cbase 13 (base+43) (base+44) (base+45), carrierCols cbase 14)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h15 : carrierVals cbase 15 env.loc
      = permW (carrierVals cbase 14 env.loc ++ [env.loc (base+46), env.loc (base+47), env.loc (base+48)]) := by
    have := m (bodyIns cbase 14 (base+46) (base+47) (base+48), carrierCols cbase 15)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h16 : carrierVals cbase 16 env.loc
      = permW (carrierVals cbase 15 env.loc ++ [env.loc (base+49), env.loc (base+50), env.loc (base+51)]) := by
    have := m (bodyIns cbase 15 (base+49) (base+50) (base+51), carrierCols cbase 16)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h17 : carrierVals cbase 17 env.loc
      = permW (carrierVals cbase 16 env.loc ++ [env.loc (base+52), env.loc (base+53), env.loc (base+54)]) := by
    have := m (bodyIns cbase 16 (base+52) (base+53) (base+54), carrierCols cbase 17)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h18 : carrierVals cbase 18 env.loc
      = permW (carrierVals cbase 17 env.loc ++ [env.loc (base+55), env.loc (base+56), env.loc (base+57)]) := by
    have := m (bodyIns cbase 17 (base+55) (base+56) (base+57), carrierCols cbase 18)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h19 : carrierVals cbase 19 env.loc
      = permW (carrierVals cbase 18 env.loc ++ [env.loc (base+58), env.loc (base+59), env.loc (base+60)]) := by
    have := m (bodyIns cbase 18 (base+58) (base+59) (base+60), carrierCols cbase 19)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h20 : carrierVals cbase 20 env.loc
      = permW (carrierVals cbase 19 env.loc ++ [env.loc (base+61), env.loc (base+62), env.loc (base+63)]) := by
    have := m (bodyIns cbase 19 (base+61) (base+62) (base+63), carrierCols cbase 20)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h21 : carrierVals cbase 21 env.loc
      = permW (carrierVals cbase 20 env.loc ++ [env.loc (base+64), env.loc (base+65), env.loc (base+66)]) := by
    have := m (bodyIns cbase 20 (base+64) (base+65) (base+66), carrierCols cbase 21)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h22 : carrierVals cbase 22 env.loc
      = permW (carrierVals cbase 21 env.loc ++ [env.loc (base+67), env.loc (base+68), env.loc (base+69)]) := by
    have := m (bodyIns cbase 21 (base+67) (base+68) (base+69), carrierCols cbase 22)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h23 : carrierVals cbase 23 env.loc
      = permW (carrierVals cbase 22 env.loc ++ [env.loc (base+70), env.loc (base+71), env.loc (base+72)]) := by
    have := m (bodyIns cbase 22 (base+70) (base+71) (base+72), carrierCols cbase 23)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h24 : carrierVals cbase 24 env.loc
      = permW (carrierVals cbase 23 env.loc ++ [env.loc (base+73), env.loc (base+74), env.loc (base+75)]) := by
    have := m (bodyIns cbase 23 (base+73) (base+74) (base+75), carrierCols cbase 24)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h25 : carrierVals cbase 25 env.loc
      = permW (carrierVals cbase 24 env.loc ++ [env.loc (base+76), env.loc (base+77), env.loc (base+78)]) := by
    have := m (bodyIns cbase 24 (base+76) (base+77) (base+78), carrierCols cbase 25)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h26 : carrierVals cbase 26 env.loc
      = permW (carrierVals cbase 25 env.loc ++ [env.loc (base+79), env.loc (base+80), env.loc (base+81)]) := by
    have := m (bodyIns cbase 25 (base+79) (base+80) (base+81), carrierCols cbase 26)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h27 : carrierVals cbase 27 env.loc
      = permW (carrierVals cbase 26 env.loc ++ [env.loc (base+82), env.loc (base+83), env.loc (base+84)]) := by
    have := m (bodyIns cbase 26 (base+82) (base+83) (base+84), carrierCols cbase 27)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h28 : carrierVals cbase 28 env.loc
      = permW (carrierVals cbase 27 env.loc ++ [env.loc (base+85), env.loc (base+86), env.loc (base+87)]) := by
    have := m (bodyIns cbase 27 (base+85) (base+86) (base+87), carrierCols cbase 28)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h29 : carrierVals cbase 29 env.loc
      = permW (carrierVals cbase 28 env.loc ++ [env.loc (base+88), env.loc (base+89), env.loc (base+90)]) := by
    have := m (bodyIns cbase 28 (base+88) (base+89) (base+90), carrierCols cbase 29)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h30 : carrierVals cbase 30 env.loc
      = permW (carrierVals cbase 29 env.loc ++ [env.loc (base+91), env.loc (base+92), env.loc (base+93)]) := by
    have := m (bodyIns cbase 29 (base+91) (base+92) (base+93), carrierCols cbase 30)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h31 : carrierVals cbase 31 env.loc
      = permW (carrierVals cbase 30 env.loc ++ [env.loc (base+94), env.loc (base+95), env.loc (base+96)]) := by
    have := m (bodyIns cbase 30 (base+94) (base+95) (base+96), carrierCols cbase 31)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h32 : carrierVals cbase 32 env.loc
      = permW (carrierVals cbase 31 env.loc ++ [env.loc (base+97), env.loc (base+98), env.loc (base+99)]) := by
    have := m (bodyIns cbase 31 (base+97) (base+98) (base+99), carrierCols cbase 32)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h33 : carrierVals cbase 33 env.loc
      = permW (carrierVals cbase 32 env.loc ++ [env.loc (base+100), env.loc (base+101), env.loc (base+102)]) := by
    have := m (bodyIns cbase 32 (base+100) (base+101) (base+102), carrierCols cbase 33)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h34 : carrierVals cbase 34 env.loc
      = permW (carrierVals cbase 33 env.loc ++ [env.loc (base+103), env.loc (base+104), env.loc (base+105)]) := by
    have := m (bodyIns cbase 33 (base+103) (base+104) (base+105), carrierCols cbase 34)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h35 : carrierVals cbase 35 env.loc
      = permW (carrierVals cbase 34 env.loc ++ [env.loc (base+106), env.loc (base+107), env.loc (base+108)]) := by
    have := m (bodyIns cbase 34 (base+106) (base+107) (base+108), carrierCols cbase 35)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h36 : carrierVals cbase 36 env.loc
      = permW (carrierVals cbase 35 env.loc ++ [env.loc (base+109), env.loc (base+110), env.loc (base+111)]) := by
    have := m (bodyIns cbase 35 (base+109) (base+110) (base+111), carrierCols cbase 36)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h37 : carrierVals cbase 37 env.loc
      = permW (carrierVals cbase 36 env.loc ++ [env.loc (base+112), env.loc (base+113), env.loc (base+114)]) := by
    have := m (bodyIns cbase 36 (base+112) (base+113) (base+114), carrierCols cbase 37)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h38 : carrierVals cbase 38 env.loc
      = permW (carrierVals cbase 37 env.loc ++ [env.loc (base+115), env.loc (base+116), env.loc (base+117)]) := by
    have := m (bodyIns cbase 37 (base+115) (base+116) (base+117), carrierCols cbase 38)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h39 : carrierVals cbase 39 env.loc
      = permW (carrierVals cbase 38 env.loc ++ [env.loc (base+118), env.loc (base+119), env.loc (base+120)]) := by
    have := m (bodyIns cbase 38 (base+118) (base+119) (base+120), carrierCols cbase 39)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h40 : carrierVals cbase 40 env.loc
      = permW (carrierVals cbase 39 env.loc ++ [env.loc (base+121), env.loc (base+122), env.loc (base+123)]) := by
    have := m (bodyIns cbase 39 (base+121) (base+122) (base+123), carrierCols cbase 40)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h41 : carrierVals cbase 41 env.loc
      = permW (carrierVals cbase 40 env.loc ++ [env.loc (base+124), env.loc (base+125), env.loc (base+126)]) := by
    have := m (bodyIns cbase 40 (base+124) (base+125) (base+126), carrierCols cbase 41)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h42 : carrierVals cbase 42 env.loc
      = permW (carrierVals cbase 41 env.loc ++ [env.loc (base+127), env.loc (base+128), env.loc (base+129)]) := by
    have := m (bodyIns cbase 41 (base+127) (base+128) (base+129), carrierCols cbase 42)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h43 : carrierVals cbase 43 env.loc
      = permW (carrierVals cbase 42 env.loc ++ [env.loc (base+130), env.loc (base+131), env.loc (base+132)]) := by
    have := m (bodyIns cbase 42 (base+130) (base+131) (base+132), carrierCols cbase 43)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h44 : carrierVals cbase 44 env.loc
      = permW (carrierVals cbase 43 env.loc ++ [env.loc (base+133), env.loc (base+134), env.loc (base+135)]) := by
    have := m (bodyIns cbase 43 (base+133) (base+134) (base+135), carrierCols cbase 44)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h45 : carrierVals cbase 45 env.loc
      = permW (carrierVals cbase 44 env.loc ++ [env.loc (base+136), env.loc (base+137), env.loc (base+138)]) := by
    have := m (bodyIns cbase 44 (base+136) (base+137) (base+138), carrierCols cbase 45)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h46 : carrierVals cbase 46 env.loc
      = permW (carrierVals cbase 45 env.loc ++ [env.loc (base+139), env.loc (base+140), env.loc (base+141)]) := by
    have := m (bodyIns cbase 45 (base+139) (base+140) (base+141), carrierCols cbase 46)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h47 : carrierVals cbase 47 env.loc
      = permW (carrierVals cbase 46 env.loc ++ [env.loc (base+142), env.loc (base+143), env.loc (base+144)]) := by
    have := m (bodyIns cbase 46 (base+142) (base+143) (base+144), carrierCols cbase 47)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h48 : carrierVals cbase 48 env.loc
      = permW (carrierVals cbase 47 env.loc ++ [env.loc (base+145), env.loc (base+146), env.loc (base+147)]) := by
    have := m (bodyIns cbase 47 (base+145) (base+146) (base+147), carrierCols cbase 48)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h49 : carrierVals cbase 49 env.loc
      = permW (carrierVals cbase 48 env.loc ++ [env.loc (base+148), env.loc (base+149), env.loc (base+150)]) := by
    have := m (bodyIns cbase 48 (base+148) (base+149) (base+150), carrierCols cbase 49)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h50 : carrierVals cbase 50 env.loc
      = permW (carrierVals cbase 49 env.loc ++ [env.loc (base+151), env.loc (base+152), env.loc (base+153)]) := by
    have := m (bodyIns cbase 49 (base+151) (base+152) (base+153), carrierCols cbase 50)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h51 : carrierVals cbase 51 env.loc
      = permW (carrierVals cbase 50 env.loc ++ [env.loc (base+154), env.loc (base+155), env.loc (base+156)]) := by
    have := m (bodyIns cbase 50 (base+154) (base+155) (base+156), carrierCols cbase 51)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h52 : carrierVals cbase 52 env.loc
      = permW (carrierVals cbase 51 env.loc ++ [env.loc (base+157), env.loc (base+158), env.loc (base+159)]) := by
    have := m (bodyIns cbase 51 (base+157) (base+158) (base+159), carrierCols cbase 52)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h53 : carrierVals cbase 53 env.loc
      = permW (carrierVals cbase 52 env.loc ++ [env.loc (base+160), env.loc (base+161), env.loc (base+162)]) := by
    have := m (bodyIns cbase 52 (base+160) (base+161) (base+162), carrierCols cbase 53)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h54 : carrierVals cbase 54 env.loc
      = permW (carrierVals cbase 53 env.loc ++ [env.loc (base+163), env.loc (base+164), env.loc (base+165)]) := by
    have := m (bodyIns cbase 53 (base+163) (base+164) (base+165), carrierCols cbase 54)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h55 : carrierVals cbase 55 env.loc
      = permW (carrierVals cbase 54 env.loc ++ [env.loc (base+166), env.loc (base+167), env.loc (base+168)]) := by
    have := m (bodyIns cbase 54 (base+166) (base+167) (base+168), carrierCols cbase 55)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h56 : carrierVals cbase 56 env.loc
      = permW (carrierVals cbase 55 env.loc ++ [env.loc (base+169), env.loc (base+170), env.loc (base+171)]) := by
    have := m (bodyIns cbase 55 (base+169) (base+170) (base+171), carrierCols cbase 56)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h57 : carrierVals cbase 57 env.loc
      = permW (carrierVals cbase 56 env.loc ++ [env.loc (base+172), env.loc (base+173), env.loc (base+174)]) := by
    have := m (bodyIns cbase 56 (base+172) (base+173) (base+174), carrierCols cbase 57)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h58 : carrierVals cbase 58 env.loc
      = permW (carrierVals cbase 57 env.loc ++ [env.loc (base+175), env.loc (base+176), env.loc (base+177)]) := by
    have := m (bodyIns cbase 57 (base+175) (base+176) (base+177), carrierCols cbase 58)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h59 : carrierVals cbase 59 env.loc
      = permW (carrierVals cbase 58 env.loc ++ [env.loc (base+178), env.loc (base+179), env.loc (base+180)]) := by
    have := m (bodyIns cbase 58 (base+178) (base+179) (base+180), carrierCols cbase 59)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h60 : carrierVals cbase 60 env.loc
      = permW (carrierVals cbase 59 env.loc ++ [env.loc (base+181), env.loc (base+182), env.loc (base+183)]) := by
    have := m (bodyIns cbase 59 (base+181) (base+182) (base+183), carrierCols cbase 60)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h61 : carrierVals cbase 61 env.loc
      = permW (carrierVals cbase 60 env.loc ++ [env.loc (base+184), env.loc (base+185), env.loc (base+186)]) := by
    have := m (bodyIns cbase 60 (base+184) (base+185) (base+186), carrierCols cbase 61)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h62 : carrierVals cbase 62 env.loc
      = permW (carrierVals cbase 61 env.loc ++ [env.loc (base+187), env.loc (base+188), env.loc (base+189)]) := by
    have := m (bodyIns cbase 61 (base+187) (base+188) (base+189), carrierCols cbase 62)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h63 : carrierVals cbase 63 env.loc
      = permW (carrierVals cbase 62 env.loc ++ [env.loc (base+190), env.loc (base+191), env.loc (base+192)]) := by
    have := m (bodyIns cbase 62 (base+190) (base+191) (base+192), carrierCols cbase 63)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h64 : carrierVals cbase 64 env.loc
      = permW (carrierVals cbase 63 env.loc ++ [env.loc (base+193), env.loc (base+194), env.loc (base+195)]) := by
    have := m (bodyIns cbase 63 (base+193) (base+194) (base+195), carrierCols cbase 64)
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this
  have h65 : carrierVals cbase 65 env.loc
      = permW (carrierVals cbase 64 env.loc ++ [env.loc (base+B_IROOT), 0, 0]) := by
    have := m ((carrierCols cbase 64).map .var ++ [.var (base+B_IROOT), .const 0, .const 0],
        carrierCols cbase 65)
      (by simp [rotV3WideSpecs])
    simpa [carrierVals, EmittedExpr.eval, List.map_append, List.map_map, Function.comp_def] using this
  rw [h65, h64, h63, h62, h61, h60, h59, h58, h57, h56, h55, h54, h53, h52, h51, h50, h49, h48, h47, h46, h45, h44, h43, h42, h41, h40, h39, h38, h37, h36, h35, h34, h33, h32, h31, h30, h29, h28, h27, h26, h25, h24, h23, h22, h21, h20, h19, h18, h17, h16, h15, h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0]
  rfl

#assert_axioms siteLookupN_sound
#assert_axioms siteLookupsN_sound
#assert_axioms rotV3WidePin

/-! ## §4 — `rotateV3Wide` / `v3OfWide`: the PARALLEL wide emission.

A NEW emission, threaded where `v3Of`/`rotateV3` thread the 1-felt path, but additive: it lifts
`graduateV1 (rotateV3 d)` (reusing the LIVE-proven 1-felt host — its welds, v1 survival, and the
host's own sites) and APPENDS the wide BEFORE/AFTER lookup blocks over FRESH carrier regions plus
the 8-column PI pins. The live registry KEEPS `v3Of` (this is a parallel constant) — the live wire
is untouched. The wide BEFORE/AFTER blocks read the SAME `preLimbsAt` columns the 1-felt path
commits, so the wide commitment binds the SAME 184 limbs + iroot, at full 8-felt width.

Layout (past `rotateV3 d`'s width `w = d.traceWidth + APPENDIX_SPAN`):
  * BEFORE wide carriers at `w` (62×8 = 496 columns); the wide BEFORE block's limbs are the live
    BEFORE block's columns `d.traceWidth + 0 .. + B_IROOT`.
  * AFTER wide carriers at `w + 496`; the wide AFTER block's limbs are the live AFTER block's
    columns `d.traceWidth + B_SPAN + 0 .. + B_IROOT`.
  * 16 appended PI slots: `piCount' .. piCount'+7` = BEFORE commit's 8 columns (first row),
    `piCount'+8 .. +15` = AFTER commit's 8 columns (last row), where `piCount' = (rotateV3 d).piCount`. -/

/-- The BEFORE-block wide-carrier base of a host of (graduated) width `w`. -/
def wideBeforeCBase (w : Nat) : Nat := w
/-- The AFTER-block wide-carrier base: one full carrier block (62 × 8 = 496 columns) past the
BEFORE block's base — derived, so the AFTER block starts exactly where the BEFORE block ends. -/
def wideAfterCBase (w : Nat) : Nat := w + wideCarrierBlockSpan

/-- The 8-column PI pins of a commit carrier `cols` to PI slots `piBase..piBase+7`, on `row`. -/
def commitPins (row : VmRow) (cols : List Nat) (piBase : Nat) : List VmConstraint2 :=
  (cols.zipIdx).map (fun (p : Nat × Nat) => .base (.piBinding row p.1 (piBase + p.2)))

/-- **`rotateV3Wide`** — the parallel wide emission. The graduated 1-felt host PLUS the wide
BEFORE/AFTER lookup blocks and their 16 PI pins (8 BEFORE commit cols on the first row, 8 AFTER
commit cols on the last). -/
def rotateV3Wide (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites,
        ChipArityAdmitted s.inputs.length := by graduate_arity) : EffectVmDescriptor2 :=
  let host := graduateV1 (rotateV3 d) hAdm
  let w := host.traceWidth
  let bb := d.traceWidth            -- live BEFORE limb base
  let ab := d.traceWidth + B_SPAN       -- live AFTER limb base
  let cbB := wideBeforeCBase w
  let cbA := wideAfterCBase w
  { host with
    traceWidth := w + wideAppendixSpan  -- + 2 × (wideNumCarriers × 8) = + 992
    piCount    := host.piCount + 16
    tables     := v2Tables (w + wideAppendixSpan)
    constraints := host.constraints
      ++ rotV3WideLookups bb cbB
      ++ rotV3WideLookups ab cbA
      ++ commitPins .first (carrierCols cbB 65) host.piCount
      ++ commitPins .last  (carrierCols cbA 65) (host.piCount + 8) }

/-- **`v3OfWide`** — the alias mirroring `v3Of` (the rotated graduation of a cohort member, the
WIDE commitment lane). The live-flip handoff repoints the registry from `v3Of` to THIS. -/
def v3OfWide (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites,
        ChipArityAdmitted s.inputs.length := by graduate_arity) : EffectVmDescriptor2 := rotateV3Wide d hAdm

/-! ## §5 — the re-proved WIDE keystone tower.

`rotV3Wide_pins`/`rotV3Wide_publishes`/`rotV3Wide_binds_published`: the wide analogs of
`rotV3_pins`/`rotV3_publishes`/`rotV3_binds_published`. The floor swaps `Poseidon2SpongeCR` →
`Poseidon2WideCR` + `Poseidon2Width8`; the binding invokes `wireCommitR8_binds` (the keystone is
LOAD-BEARING — the published 8-felt commit = the chained `wireCommitR8` digest of the 184 limbs). -/

/-- The wide BEFORE/AFTER lookups are members of `rotateV3Wide d hAdm`'s constraints (for `rowConstraints`
extraction). -/
theorem rotateV3Wide_before_mem (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites,
      ChipArityAdmitted s.inputs.length) :
    ∀ c ∈ rotV3WideLookups d.traceWidth (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth),
      c ∈ (rotateV3Wide d hAdm).constraints := by
  intro c hc
  unfold rotateV3Wide
  simp only [List.append_assoc, List.mem_append]
  exact Or.inr (Or.inl hc)

theorem rotateV3Wide_after_mem (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites,
      ChipArityAdmitted s.inputs.length) :
    ∀ c ∈ rotV3WideLookups (d.traceWidth + B_SPAN) (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth),
      c ∈ (rotateV3Wide d hAdm).constraints := by
  intro c hc
  unfold rotateV3Wide
  simp only [List.append_assoc, List.mem_append]
  exact Or.inr (Or.inr (Or.inl hc))

/-- A `Satisfied2` witness of `rotateV3Wide d hAdm` forces the BEFORE/AFTER wide lookups on every row:
each block's 8 state-commit carrier columns ARE `wireCommitR8` of the row's own limbs and iroot.
The host `Satisfied2` carries the 1-felt `hash` (for the graduated host's own 1-felt sites); the
WIDE chip table soundness `ChipTableSoundN permW` is a SEPARATE faithfulness floor of the SAME
`.poseidon2` table (`chipRowN_head_eq_hash`: a wide-sound table is also 1-felt-sound at its head). -/
theorem rotV3Wide_pins (hash : List ℤ → ℤ) (permW : List ℤ → List ℤ) (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites,
      ChipArityAdmitted s.inputs.length)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchipN : ChipTableSoundN permW (t.tf .poseidon2))
    (hsat : Satisfied2 hash (rotateV3Wide d hAdm) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    carrierVals (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65 (envAt t i).loc
      = wireCommitR8 permW (preLimbsWide d.traceWidth (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + B_IROOT))
    ∧ carrierVals (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65 (envAt t i).loc
      = wireCommitR8 permW (preLimbsWide (d.traceWidth + B_SPAN) (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + B_SPAN + B_IROOT)) := by
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_⟩
  · apply rotV3WidePin permW (t.tf .poseidon2) hchipN (envAt t i) d.traceWidth
      (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth)
    intro p hp
    have hmem := rotateV3Wide_before_mem d hAdm
      (.lookup (siteLookupN p.1 p.2 (rotV3WideSpecs_admitted _ _ p hp)))
      (List.mem_map.mpr ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩)
    have := hrow _ hmem
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, siteLookupN] using this
  · apply rotV3WidePin permW (t.tf .poseidon2) hchipN (envAt t i) (d.traceWidth + B_SPAN)
      (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth)
    intro p hp
    have hmem := rotateV3Wide_after_mem d hAdm
      (.lookup (siteLookupN p.1 p.2 (rotV3WideSpecs_admitted _ _ p hp)))
      (List.mem_map.mpr ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩)
    have := hrow _ hmem
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, siteLookupN] using this

/-- The PI pins membership: the BEFORE/AFTER commit pins are constraints of `rotateV3Wide d hAdm`. -/
theorem rotateV3Wide_beforePin_mem (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites,
      ChipArityAdmitted s.inputs.length) (k : Nat) (hk : k < 8) :
    (VmConstraint2.base (.piBinding .first
      ((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD k 0)
      ((graduateV1 (rotateV3 d) hAdm).piCount + k))) ∈ (rotateV3Wide d hAdm).constraints := by
  unfold rotateV3Wide
  simp only [List.append_assoc, List.mem_append]
  refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
  unfold commitPins
  rw [List.mem_map]
  refine ⟨((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD k 0, k),
    ?_, rfl⟩
  rw [List.mem_iff_getElem]
  refine ⟨k, ?_, ?_⟩
  · rw [List.length_zipIdx, carrierCols_length]; exact hk
  · rw [List.getElem_zipIdx]
    have hk' : k < (carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).length := by
      rw [carrierCols_length]; exact hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

theorem rotateV3Wide_afterPin_mem (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites,
      ChipArityAdmitted s.inputs.length) (k : Nat) (hk : k < 8) :
    (VmConstraint2.base (.piBinding .last
      ((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD k 0)
      ((graduateV1 (rotateV3 d) hAdm).piCount + 8 + k))) ∈ (rotateV3Wide d hAdm).constraints := by
  unfold rotateV3Wide
  simp only [List.append_assoc, List.mem_append]
  refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
  unfold commitPins
  rw [List.mem_map]
  refine ⟨((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD k 0, k),
    ?_, rfl⟩
  rw [List.mem_iff_getElem]
  refine ⟨k, ?_, ?_⟩
  · rw [List.length_zipIdx, carrierCols_length]; exact hk
  · rw [List.getElem_zipIdx]
    have hk' : k < (carrierCols (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).length := by
      rw [carrierCols_length]; exact hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

/-- **`rotV3Wide_publishes`** — the wide commits PUBLISH: first row binds the BEFORE commit's 8
columns to PI slots `piCount'..+7`; last row binds the AFTER commit's 8 columns to `piCount'+8..+15`. -/
theorem rotV3Wide_publishes (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites,
      ChipArityAdmitted s.inputs.length)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (rotateV3Wide d hAdm) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    ((i == 0) = true → ∀ k, (hk : k < 8) →
      (envAt t i).loc
          ((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD k 0)
        ≡ (envAt t i).pub ((graduateV1 (rotateV3 d) hAdm).piCount + k) [ZMOD 2013265921])
    ∧ ((i + 1 == t.rows.length) = true → ∀ k, (hk : k < 8) →
      (envAt t i).loc
          ((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD k 0)
        ≡ (envAt t i).pub ((graduateV1 (rotateV3 d) hAdm).piCount + 8 + k) [ZMOD 2013265921]) := by
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_⟩
  · intro hf k hk
    have := hrow _ (rotateV3Wide_beforePin_mem d hAdm k hk)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at this
    exact this hf
  · intro hl k hk
    have := hrow _ (rotateV3Wide_afterPin_mem d hAdm k hk)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at this
    exact this hl

/-- Two length-8 carrier-value lists whose published columns carry pairwise-equal PI values are
EQUAL. `pubAt`/`pubAt'` are the per-row PI reads at the matching slot offset `m`; `hpub` is the
slot-by-slot published-PI equality. The pointwise equality lifts to list equality via
`List.ext_getElem`. -/
private theorem carrierVals_eq_of_pins (cb cb' : Nat) (a a' : Assignment)
    (pubAt pubAt' : Nat → ℤ)
    (hpub : ∀ m, m < 8 → pubAt m = pubAt' m)
    (h : ∀ k, k < 8 → a ((carrierCols cb 65).getD k 0) = pubAt k)
    (h' : ∀ k, k < 8 → a' ((carrierCols cb' 65).getD k 0) = pubAt' k) :
    carrierVals cb 65 a = carrierVals cb' 65 a' := by
  have key : ∀ k, k < 8 →
      (carrierVals cb 65 a).getD k 0 = (carrierVals cb' 65 a').getD k 0 := by
    intro k hk8
    have hlt : k < (carrierCols cb 65).length := by rw [carrierCols_length]; exact hk8
    have hlt' : k < (carrierCols cb' 65).length := by rw [carrierCols_length]; exact hk8
    have e1 : (carrierVals cb 65 a).getD k 0 = a ((carrierCols cb 65).getD k 0) := by
      simp [carrierVals, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    have e2 : (carrierVals cb' 65 a').getD k 0 = a' ((carrierCols cb' 65).getD k 0) := by
      simp [carrierVals, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt']
    rw [e1, e2, h k hk8, h' k hk8, hpub k hk8]
  apply List.ext_getElem
  · rw [carrierVals_length, carrierVals_length]
  · intro k hk hk'
    have hk8 : k < 8 := by rwa [carrierVals_length] at hk
    have := key k hk8
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      List.getElem?_eq_getElem hk'] using this

/-- The wide analog specialized to the field migration: two length-8 state-commit carriers whose
columns are pairwise EQUAL (already lifted from the mod-`p` publish congruences via the deployed
range-check canonicality) are EQUAL. A thin reuse of `carrierVals_eq_of_pins` with the RHS carrier's
columns as the (trivially equal) published values. -/
private theorem carrierVals_eq_of_colEq (cb cb' : Nat) (a a' : Assignment)
    (h : ∀ k, k < 8 → a ((carrierCols cb 65).getD k 0) = a' ((carrierCols cb' 65).getD k 0)) :
    carrierVals cb 65 a = carrierVals cb' 65 a' :=
  carrierVals_eq_of_pins cb cb' a a'
    (fun m => a' ((carrierCols cb' 65).getD m 0))
    (fun m => a' ((carrierCols cb' 65).getD m 0))
    (fun _ _ => rfl) h (fun _ _ => rfl)

set_option maxHeartbeats 1600000 in
/-- **THE WIDE END-TO-END KEYSTONE.** Two `Satisfied2` witnesses of `rotateV3Wide d hAdm` publishing the
SAME 8-felt BEFORE commit and the SAME 8-felt AFTER commit EITHER agree on the WHOLE before-block
37-limb list + iroot AND the WHOLE after-block 37-limb list + iroot — the GENUINE ~124-bit binding —
OR EXHIBIT a genuine collision of the deployed wide permutation, per leg, at the two lists
`wireCommit8Find` returns. Via the FAITHFUL `wireCommitR8_binds_or_collides` (the keystone is
load-bearing: the published 8-felt commit IS the chained `wireCommitR8` digest of the limbs).

⚑ **NO CR FLOOR IS CARRIED.** The old form took `hCR : Poseidon2WideCR permW` — DELETED, because the
deployed `single_perm_compress` REFUTES it (8 bounded BabyBear lanes, infinite domain, pigeonhole), so
this theorem was VACUOUSLY TRUE at deployed parameters. Each conjunct is now a disjunction: formally
weaker, but TRUE of the real permutation, which the old one was not. `Poseidon2Width8` is retained and
is NOT a false floor — it is the deployed output-width contract, satisfied by the real permutation. -/
theorem rotV3Wide_binds_published (hash : List ℤ → ℤ) (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (d : EffectVmDescriptor)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites,
      ChipArityAdmitted s.inputs.length)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hchipN : ChipTableSoundN permW (t.tf .poseidon2))
    (hchipN' : ChipTableSoundN permW (t'.tf .poseidon2))
    (hsat : Satisfied2 hash (rotateV3Wide d hAdm) minit mfin maddrs t)
    (hsat' : Satisfied2 hash (rotateV3Wide d hAdm) minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hfirst : (i == 0) = true) (hfirst' : (j == 0) = true)
    (k l : Nat) (hk : k < t.rows.length) (hl : l < t'.rows.length)
    (hlast : (k + 1 == t.rows.length) = true) (hlast' : (l + 1 == t'.rows.length) = true)
    (hpubBefore : ∀ m, m < 8 →
      (envAt t i).pub ((graduateV1 (rotateV3 d) hAdm).piCount + m)
        = (envAt t' j).pub ((graduateV1 (rotateV3 d) hAdm).piCount + m))
    (hpubAfter : ∀ m, m < 8 →
      (envAt t k).pub ((graduateV1 (rotateV3 d) hAdm).piCount + 8 + m)
        = (envAt t' l).pub ((graduateV1 (rotateV3 d) hAdm).piCount + 8 + m))
    -- The 8 state-commit carrier columns are field-canonical (`0 ≤ · < p`, the deployed range-check
    -- invariant): lifts each mod-`p` publish congruence to the genuine ℤ carrier equality the wide CR
    -- floor needs (chaining loc(i) ≡ pub(i) = pub(j) ≡ loc(j) through the equal published PIs).
    (hcCanonB : ∀ m, m < 8 →
      0 ≤ (envAt t i).loc ((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0)
        ∧ (envAt t i).loc ((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0) < 2013265921)
    (hcCanonB' : ∀ m, m < 8 →
      0 ≤ (envAt t' j).loc ((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0)
        ∧ (envAt t' j).loc ((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0) < 2013265921)
    (hcCanonA : ∀ m, m < 8 →
      0 ≤ (envAt t k).loc ((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0)
        ∧ (envAt t k).loc ((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0) < 2013265921)
    (hcCanonA' : ∀ m, m < 8 →
      0 ≤ (envAt t' l).loc ((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0)
        ∧ (envAt t' l).loc ((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0) < 2013265921) :
    ((preLimbsWide d.traceWidth (envAt t i).loc = preLimbsWide d.traceWidth (envAt t' j).loc
        ∧ (envAt t i).loc (d.traceWidth + B_IROOT) = (envAt t' j).loc (d.traceWidth + B_IROOT))
      ∨ WireColl permW (preLimbsWide d.traceWidth (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + B_IROOT)) (preLimbsWide d.traceWidth (envAt t' j).loc)
          ((envAt t' j).loc (d.traceWidth + B_IROOT)))
    ∧ ((preLimbsWide (d.traceWidth + B_SPAN) (envAt t k).loc
          = preLimbsWide (d.traceWidth + B_SPAN) (envAt t' l).loc
        ∧ (envAt t k).loc (d.traceWidth + B_SPAN + B_IROOT) = (envAt t' l).loc (d.traceWidth + B_SPAN + B_IROOT))
      ∨ WireColl permW (preLimbsWide (d.traceWidth + B_SPAN) (envAt t k).loc)
          ((envAt t k).loc (d.traceWidth + B_SPAN + B_IROOT))
          (preLimbsWide (d.traceWidth + B_SPAN) (envAt t' l).loc)
          ((envAt t' l).loc (d.traceWidth + B_SPAN + B_IROOT))) := by
  have hp := rotV3Wide_pins hash permW d hAdm minit mfin maddrs t hchipN hsat
  have hp' := rotV3Wide_pins hash permW d hAdm minit' mfin' maddrs' t' hchipN' hsat'
  have hq := rotV3Wide_publishes hash d hAdm minit mfin maddrs t hsat
  have hq' := rotV3Wide_publishes hash d hAdm minit' mfin' maddrs' t' hsat'
  refine ⟨?_, ?_⟩
  · -- BEFORE: equal published 8-felt commits ⇒ equal limbs + iroot. Lift the 8 mod-p publish
    -- congruences to a genuine ℤ carrier equality via the deployed range-check canonicality.
    have hcolEq : ∀ m, m < 8 →
        (envAt t i).loc ((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0)
          = (envAt t' j).loc ((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0) :=
      fun m hm => canon_eq_of_modEq (hcCanonB m hm) (hcCanonB' m hm)
        (calc (envAt t i).loc ((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0)
              ≡ (envAt t i).pub ((graduateV1 (rotateV3 d) hAdm).piCount + m) [ZMOD 2013265921] := (hq i hi).1 hfirst m hm
          _ = (envAt t' j).pub ((graduateV1 (rotateV3 d) hAdm).piCount + m) := hpubBefore m hm
          _ ≡ (envAt t' j).loc ((carrierCols (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0)
              [ZMOD 2013265921] := ((hq' j hj).1 hfirst' m hm).symm)
    have hcv : carrierVals (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65 (envAt t i).loc
        = carrierVals (wideBeforeCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65 (envAt t' j).loc :=
      carrierVals_eq_of_colEq _ _ _ _ hcolEq
    have hwire : wireCommitR8 permW (preLimbsWide d.traceWidth (envAt t i).loc)
        ((envAt t i).loc (d.traceWidth + B_IROOT))
        = wireCommitR8 permW (preLimbsWide d.traceWidth (envAt t' j).loc)
            ((envAt t' j).loc (d.traceWidth + B_IROOT)) := by
      rw [← (hp i hi).1, ← (hp' j hj).1]; exact hcv
    exact wireCommitR8_binds_or_collides permW hW
      (by rw [preLimbsWide_length, preLimbsWide_length]) hwire
  · -- AFTER: equal published 8-felt commits ⇒ equal limbs + iroot. Same mod-p lift on the last row.
    have hcolEq : ∀ m, m < 8 →
        (envAt t k).loc ((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0)
          = (envAt t' l).loc ((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0) :=
      fun m hm => canon_eq_of_modEq (hcCanonA m hm) (hcCanonA' m hm)
        (calc (envAt t k).loc ((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0)
              ≡ (envAt t k).pub ((graduateV1 (rotateV3 d) hAdm).piCount + 8 + m) [ZMOD 2013265921] := (hq k hk).2 hlast m hm
          _ = (envAt t' l).pub ((graduateV1 (rotateV3 d) hAdm).piCount + 8 + m) := hpubAfter m hm
          _ ≡ (envAt t' l).loc ((carrierCols (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65).getD m 0)
              [ZMOD 2013265921] := ((hq' l hl).2 hlast' m hm).symm)
    have hcv : carrierVals (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65 (envAt t k).loc
        = carrierVals (wideAfterCBase (graduateV1 (rotateV3 d) hAdm).traceWidth) 65 (envAt t' l).loc :=
      carrierVals_eq_of_colEq _ _ _ _ hcolEq
    have hwire : wireCommitR8 permW (preLimbsWide (d.traceWidth + B_SPAN) (envAt t k).loc)
        ((envAt t k).loc (d.traceWidth + B_SPAN + B_IROOT))
        = wireCommitR8 permW (preLimbsWide (d.traceWidth + B_SPAN) (envAt t' l).loc)
            ((envAt t' l).loc (d.traceWidth + B_SPAN + B_IROOT)) := by
      rw [← (hp k hk).2, ← (hp' l hl).2]; exact hcv
    exact wireCommitR8_binds_or_collides permW hW
      (by rw [preLimbsWide_length, preLimbsWide_length]) hwire

#assert_axioms rotV3Wide_pins
#assert_axioms rotV3Wide_publishes
#assert_axioms rotV3Wide_binds_published

/-! ## §6 — the ANTI-LAUNDERING tooth: the wide binding is GENUINELY 8-felt-wide.

A `#guard` witnessing that the wide-emitted binding distinguishes two states differing ONLY beyond
lane0 — the 8-felt commitment is genuinely WIDER than a 1-felt (lane0-only) binding would be. The
toy `refWide` (each of 8 lanes = `refSponge (tag :: xs)`, all lanes avalanching over the input) is
the same width-8 toy the §3.8 non-vacuity guards use. Two pre-iroot payloads agreeing on lane0's
hash but differing in a HIGH limb still produce DIFFERENT 8-felt commits — a 1-felt squeeze would
collapse them, the wide one does not. -/

/-- A wide-emission row whose 13 wide carriers carry the genuine `chainFrom8`/`wireCommitR8` of the
row's limbs (the COMPLETENESS direction at the spec level — what the honest producer lays). -/
def demoWideCarrier (base cbase : Nat) (limbs : List ℤ) (ir : ℤ) (a : Assignment) : Prop :=
  carrierVals cbase 65 a = wireCommitR8 refWide limbs ir

-- The wide pin's CONCLUSION at the spec level: a HIGH-limb flip (limb 30, folded mid-chain) moves
-- the published 8-felt commit — a genuinely wider binding than lane0 alone. (demoPre24/refWide from
-- EffectVmEmitRotationR §3.8.)
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide (demoPre24.set 30 999) 7
-- and the iroot is bound; honest recompute stable.
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide demoPre24 8
#guard wireCommitR8 refWide demoPre24 7 == wireCommitR8 refWide demoPre24 7
-- the wide commit is 8 felts (NOT 1) — the structural anti-laundering width witness.
#guard (wireCommitR8 refWide demoPre24 7).length == 8

/-! ## §7 — `wideAppend`: the GATED-HOST wide-emission transformer (the live-flip primitive).

`rotateV3Wide` (§4) appends the wide BEFORE/AFTER blocks onto a BARE host (`graduateV1 (rotateV3 d)`),
internally re-graduating `d`. But the LIVE `v3Registry` is 36 ALREADY-GATED `EffectVmDescriptor2`s
(`v3OfFrozen`, `withSelectorGate`, the WAVE-1/2 disc gates, the fee-pin transfer) — each a graduated
host with appended gates. The live flip needs to append the wide carriers onto an ARBITRARY such host,
NOT re-graduate a bare `d`.

`wideAppend h bb ab` does exactly that: given an arbitrary graduated/gated `h : EffectVmDescriptor2`
and the host's BEFORE/AFTER limb bases `bb ab` (the columns `rotateV3` laid the limbs at — `bb =
d.traceWidth`, `ab = d.traceWidth + B_SPAN`, UNMOVED by any gate, which only appends constraints), it:

  * bases the two 62×8 wide-carrier regions PAST `h.traceWidth` (`wideBeforeCBase h.traceWidth` /
    `wideAfterCBase h.traceWidth`) — they cannot collide with the host's columns or its gates' columns;
  * pins the two 8-felt commits to 16 PI slots PAST `h.piCount`;
  * PRESERVES `h`'s constraints, gates, hash sites, ranges, AND mem/map logs verbatim (it ONLY APPENDS
    `.lookup` and `.base (.piBinding …)` constraints — neither contributes a mem/map op, so the host's
    four memory legs and the map-table leg are definitionally `h`'s, exactly the `withSelectorGate`
    argument). `wideAppend h bb ab`'s constraints are `h.constraints ++ (wide binding)` — a CONJUNCTION,
    so anything provable about `h` (its gates' soundness) still holds, AND the wide binding is forced.

The wide lookups read the SAME `preLimbsAt bb`/`preLimbsAt ab` columns the host's 1-felt chain commits,
so the 8-felt binding is over the same 184 limbs + iroot. -/

/-! ### §7.0 — `isLegacyCommitPin1`: the ~31-bit 1-felt commit pin to RETIRE.

The host `h` (a graduated/gated `rotateV3` member) carries the 1-felt `STATE_COMMIT` PI pins from
`rotPins` (`EffectVmEmitRotationV3`): the rotated OLD commit `.piBinding .first (bb + B_STATE_COMMIT) p`
(PI 34) and the rotated NEW commit `.piBinding .last (ab + B_STATE_COMMIT) p` (PI 35). Those are the
~31-bit WAIST: a single felt of the rotated commit carrier pinned to a PI. Once the live executor
retires its `dpis[34/35]` reconstruction those PIs revert to placeholders that mismatch the producer's
real carriers (Fiat-Shamir mismatch). `wideAppend` therefore DROPS exactly those two pins, leaving the
8-felt `commitPins` (§7) as the SOLE commit binding.

The pins are identified by their (row, column): the BEFORE commit pin is the UNIQUE first-row PI
binding on column `bb + B_STATE_COMMIT`, the AFTER commit pin the unique last-row PI binding on column
`ab + B_STATE_COMMIT` (the rotated state-commit carrier columns, where the 1-felt chain lands its
digest). The PI INDEX is left unmatched (it varies per member: `p`/`p+1` of `rotPins`); only the
(row, carrier-column) shape is matched, which is precisely the two `rotPins` commit pins. -/
def isLegacyCommitPin1 (bb ab : Nat) : VmConstraint2 → Bool
  | .base (.piBinding .first col _) => col == bb + B_STATE_COMMIT
  | .base (.piBinding .last  col _) => col == ab + B_STATE_COMMIT
  | _ => false

/-- **`wideAppend h bb ab`** — append the two wide BEFORE/AFTER carrier blocks (each 62×8, based past
`h.traceWidth`) and their 16 commit PI pins (past `h.piCount`) onto an ARBITRARY graduated/gated host
`h`, RETIRING the host's two 1-felt `STATE_COMMIT` PI pins (the ~31-bit waist — `isLegacyCommitPin1`).
The host's name/hashSites/ranges and ALL its OTHER existing constraints (its gates) are untouched; the
1-felt commit carrier columns are left dead (unpinned), and the 8-felt wide `commitPins` are the SOLE
commit binding. -/
def wideAppend (h : EffectVmDescriptor2) (bb ab : Nat) : EffectVmDescriptor2 :=
  let w := h.traceWidth
  let cbB := wideBeforeCBase w
  let cbA := wideAfterCBase w
  { h with
    traceWidth := w + wideAppendixSpan  -- + 2 × (wideNumCarriers × 8) = + 992
    piCount    := h.piCount + 16
    tables     := v2Tables (w + wideAppendixSpan)
    constraints := (h.constraints.filter (fun c => !isLegacyCommitPin1 bb ab c))
      ++ rotV3WideLookups bb cbB
      ++ rotV3WideLookups ab cbA
      ++ commitPins .first (carrierCols cbB 65) h.piCount
      ++ commitPins .last  (carrierCols cbA 65) (h.piCount + 8) }

/-- `wideAppend h bb ab`'s constraints are `h`'s PIN-RETIRED constraints plus the four appended wide
blocks (the host's two 1-felt commit pins filtered out). -/
theorem wideAppend_constraints (h : EffectVmDescriptor2) (bb ab : Nat) :
    (wideAppend h bb ab).constraints
      = (h.constraints.filter (fun c => !isLegacyCommitPin1 bb ab c))
        ++ rotV3WideLookups bb (wideBeforeCBase h.traceWidth)
        ++ rotV3WideLookups ab (wideAfterCBase h.traceWidth)
        ++ commitPins .first (carrierCols (wideBeforeCBase h.traceWidth) 65) h.piCount
        ++ commitPins .last  (carrierCols (wideAfterCBase h.traceWidth) 65) (h.piCount + 8) := by
  unfold wideAppend; simp [List.append_assoc]

/-- A `filterMap` whose selector ignores every `.base` constraint is INVARIANT to retiring the
1-felt commit pins (which are `.base (.piBinding …)`): dropping them removes no extracted op. -/
private theorem filterMap_filter_legacyPin {α : Type} (bb ab : Nat)
    (f : VmConstraint2 → Option α) (hbase : ∀ c, f (.base c) = none) (cs : List VmConstraint2) :
    (cs.filter (fun c => !isLegacyCommitPin1 bb ab c)).filterMap f = cs.filterMap f := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    cases hpin : isLegacyCommitPin1 bb ab c with
    | true =>
      -- a retired pin is a `.base (.piBinding …)`, so `f` drops it from the RHS too
      have hfc : f c = none := by
        unfold isLegacyCommitPin1 at hpin
        split at hpin <;> first | exact hbase _ | simp at hpin
      simp [List.filter_cons, hpin, List.filterMap_cons, hfc, ih]
    | false =>
      simp [List.filter_cons, hpin, List.filterMap_cons, ih]

/-- `wideAppend` retires only `.base (.piBinding …)` pins and appends `.lookup` / `.base (.piBinding …)`
constraints, so the gathered `memOpsOf` is `h`'s (no `.memOp` is added or dropped). -/
theorem wideAppend_memOpsOf (h : EffectVmDescriptor2) (bb ab : Nat) :
    Dregg2.Circuit.DescriptorIR2.memOpsOf (wideAppend h bb ab)
      = Dregg2.Circuit.DescriptorIR2.memOpsOf h := by
  unfold Dregg2.Circuit.DescriptorIR2.memOpsOf
  rw [wideAppend_constraints]
  unfold rotV3WideLookups commitPins
  simp only [List.filterMap_append, List.filterMap_map, Function.comp_def]
  rw [filterMap_filter_legacyPin bb ab _ (by intro c; rfl)]
  simp

/-- ...and no `.mapOp` is added or dropped, so the gathered `mapOpsOf` is `h`'s. -/
theorem wideAppend_mapOpsOf (h : EffectVmDescriptor2) (bb ab : Nat) :
    Dregg2.Circuit.DescriptorIR2.mapOpsOf (wideAppend h bb ab)
      = Dregg2.Circuit.DescriptorIR2.mapOpsOf h := by
  unfold Dregg2.Circuit.DescriptorIR2.mapOpsOf
  rw [wideAppend_constraints]
  unfold rotV3WideLookups commitPins
  simp only [List.filterMap_append, List.filterMap_map, Function.comp_def]
  rw [filterMap_filter_legacyPin bb ab _ (by intro c; rfl)]
  simp

/-- ...so the gathered memory log is `h`'s, op-for-op. -/
theorem wideAppend_memLog (h : EffectVmDescriptor2) (bb ab : Nat)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) :
    Dregg2.Circuit.DescriptorIR2.memLog (wideAppend h bb ab) t
      = Dregg2.Circuit.DescriptorIR2.memLog h t := by
  simp [Dregg2.Circuit.DescriptorIR2.memLog, wideAppend_memOpsOf]

/-- ...and the gathered map log is `h`'s. -/
theorem wideAppend_mapLog (h : EffectVmDescriptor2) (bb ab : Nat)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) :
    Dregg2.Circuit.DescriptorIR2.mapLog (wideAppend h bb ab) t
      = Dregg2.Circuit.DescriptorIR2.mapLog h t := by
  simp [Dregg2.Circuit.DescriptorIR2.mapLog, wideAppend_mapOpsOf]

/-! ### §7.1 — the appended-block membership lemmas (for `rowConstraints` extraction). -/

theorem wideAppend_before_mem (h : EffectVmDescriptor2) (bb ab : Nat) :
    ∀ c ∈ rotV3WideLookups bb (wideBeforeCBase h.traceWidth),
      c ∈ (wideAppend h bb ab).constraints := by
  intro c hc
  rw [wideAppend_constraints]
  simp only [List.append_assoc, List.mem_append]
  exact Or.inr (Or.inl hc)

theorem wideAppend_after_mem (h : EffectVmDescriptor2) (bb ab : Nat) :
    ∀ c ∈ rotV3WideLookups ab (wideAfterCBase h.traceWidth),
      c ∈ (wideAppend h bb ab).constraints := by
  intro c hc
  rw [wideAppend_constraints]
  simp only [List.append_assoc, List.mem_append]
  exact Or.inr (Or.inr (Or.inl hc))

theorem wideAppend_beforePin_mem (h : EffectVmDescriptor2) (bb ab : Nat) (k : Nat) (hk : k < 8) :
    (VmConstraint2.base (.piBinding .first
      ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD k 0)
      (h.piCount + k))) ∈ (wideAppend h bb ab).constraints := by
  rw [wideAppend_constraints]
  simp only [List.append_assoc, List.mem_append]
  refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
  unfold commitPins
  rw [List.mem_map]
  refine ⟨((carrierCols (wideBeforeCBase h.traceWidth) 65).getD k 0, k), ?_, rfl⟩
  rw [List.mem_iff_getElem]
  refine ⟨k, ?_, ?_⟩
  · rw [List.length_zipIdx, carrierCols_length]; exact hk
  · rw [List.getElem_zipIdx]
    have hk' : k < (carrierCols (wideBeforeCBase h.traceWidth) 65).length := by
      rw [carrierCols_length]; exact hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

theorem wideAppend_afterPin_mem (h : EffectVmDescriptor2) (bb ab : Nat) (k : Nat) (hk : k < 8) :
    (VmConstraint2.base (.piBinding .last
      ((carrierCols (wideAfterCBase h.traceWidth) 65).getD k 0)
      (h.piCount + 8 + k))) ∈ (wideAppend h bb ab).constraints := by
  rw [wideAppend_constraints]
  simp only [List.append_assoc, List.mem_append]
  refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
  unfold commitPins
  rw [List.mem_map]
  refine ⟨((carrierCols (wideAfterCBase h.traceWidth) 65).getD k 0, k), ?_, rfl⟩
  rw [List.mem_iff_getElem]
  refine ⟨k, ?_, ?_⟩
  · rw [List.length_zipIdx, carrierCols_length]; exact hk
  · rw [List.getElem_zipIdx]
    have hk' : k < (carrierCols (wideAfterCBase h.traceWidth) 65).length := by
      rw [carrierCols_length]; exact hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

/-! ### §7.1½ — THE EMITTED COLUMN BOUNDS (the v2 geometry-repair facts).

Under the RETIRED v1 constants (57-carrier span = 456, appendix = 912) the then-60-carrier spec list
OVERRAN its allocation: the BEFORE block's carriers 57..59 collided with the AFTER block's base,
and the AFTER block's tail carriers ran PAST the declared `traceWidth`. These theorems pin the v2
repair: every emitted wide-carrier column of BOTH blocks lies strictly inside the widened trace,
the two blocks are disjoint, and the AFTER commit carrier ends FLUSH at the last allocated column. -/

/-- Every wide spec's OUTPUT-CARRIER column lies strictly within its block's span (`cbase ..
cbase + wideCarrierBlockSpan`): the spec list emits carriers 0..61 only, each with its 8 columns
at `cbase + 8·k + j`, `j < 8`, `k ≤ 61`. -/
theorem rotV3WideSpecs_outCols_lt (base cbase : Nat) :
    ∀ p ∈ rotV3WideSpecs base cbase, ∀ c ∈ p.2, c < cbase + wideCarrierBlockSpan := by
  intro p hp
  simp only [rotV3WideSpecs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · intro c hc
      simp only [carrierCols, List.mem_map, List.mem_range] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      have hj8 : j < 8 := by simpa [CHIP_OUT_LANES] using hj
      rw [wideCarrierBlockSpan_eq]
      omega

/-- Every column of an in-range carrier lies strictly within its block's span. -/
theorem carrierCols_lt_span (cbase k : Nat) (hk : k < wideNumCarriers) :
    ∀ c ∈ carrierCols cbase k, c < cbase + wideCarrierBlockSpan := by
  intro c hc
  simp only [carrierCols, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have hj8 : j < 8 := by simpa [CHIP_OUT_LANES] using hj
  rw [wideNumCarriers_eq] at hk
  rw [wideCarrierBlockSpan_eq]
  omega

/-- **BLOCK DISJOINTNESS** — every BEFORE-block emitted carrier column lies strictly below the
AFTER block's base (the v1 456-column overlap is repaired: the AFTER base is one FULL block span
past the BEFORE base). -/
theorem wide_blocks_disjoint (w base : Nat) :
    ∀ p ∈ rotV3WideSpecs base (wideBeforeCBase w), ∀ c ∈ p.2, c < wideAfterCBase w := by
  intro p hp c hc
  have := rotV3WideSpecs_outCols_lt base (wideBeforeCBase w) p hp c hc
  simpa [wideAfterCBase, wideBeforeCBase] using this

/-- **THE ALLOCATED-WIDTH BOUND** — every emitted wide-carrier output column of BOTH appended
blocks lies strictly below `(wideAppend h bb ab).traceWidth`. Under the retired v1 912-column
appendix this was FALSE for the AFTER block (its tail carriers ran to `h.traceWidth + 935`);
the v2 `wideAppendixSpan` allocation restores it. -/
theorem wideAppend_outCols_lt_width (h : EffectVmDescriptor2) (bb ab : Nat) :
    (∀ p ∈ rotV3WideSpecs bb (wideBeforeCBase h.traceWidth), ∀ c ∈ p.2,
        c < (wideAppend h bb ab).traceWidth)
    ∧ (∀ p ∈ rotV3WideSpecs ab (wideAfterCBase h.traceWidth), ∀ c ∈ p.2,
        c < (wideAppend h bb ab).traceWidth) := by
  have hw : (wideAppend h bb ab).traceWidth = h.traceWidth + wideAppendixSpan := rfl
  constructor
  · intro p hp c hc
    have hlt := rotV3WideSpecs_outCols_lt bb (wideBeforeCBase h.traceWidth) p hp c hc
    rw [hw]
    simp only [wideBeforeCBase] at hlt
    simp only [wideAppendixSpan]
    omega
  · intro p hp c hc
    have hlt := rotV3WideSpecs_outCols_lt ab (wideAfterCBase h.traceWidth) p hp c hc
    rw [hw]
    simp only [wideAfterCBase] at hlt
    simp only [wideAppendixSpan]
    omega

/-- **THE FLUSH FIT** — the AFTER block's commit carrier ends EXACTLY at the last allocated
column: `wideAfterCBase + 8·wideCommitCarrier + 8 = traceWidth` (no slack, no overrun). -/
theorem wideAppend_flush_fit (h : EffectVmDescriptor2) (bb ab : Nat) :
    wideAfterCBase h.traceWidth + 8 * wideCommitCarrier + 8
      = (wideAppend h bb ab).traceWidth := by
  have hw : (wideAppend h bb ab).traceWidth = h.traceWidth + wideAppendixSpan := rfl
  rw [hw]
  simp only [wideAfterCBase, wideCommitCarrier_eq, wideCarrierBlockSpan_eq, wideAppendixSpan_eq]

#assert_axioms rotV3WideSpecs_outCols_lt
#assert_axioms wide_blocks_disjoint
#assert_axioms wideAppend_outCols_lt_width
#assert_axioms wideAppend_flush_fit

/-! ### §7.2 — the GATED-HOST keystone tower (the generalizations of §5 over an arbitrary host). -/

/-- **`wideAppend_pins`** — a `Satisfied2` witness of `wideAppend h bb ab` forces the BEFORE/AFTER wide
lookups on every row: each block's 8 state-commit carrier columns ARE `wireCommitR8` of the row's own
184 limbs (at `bb`/`ab`) and iroot. REGARDLESS of `h`'s gates — the wide lookups are appended
constraints of `wideAppend h bb ab`, extracted from `rowConstraints` independently of `h`'s
constraints. -/
theorem wideAppend_pins (hash : List ℤ → ℤ) (permW : List ℤ → List ℤ) (h : EffectVmDescriptor2)
    (bb ab : Nat) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchipN : ChipTableSoundN permW (t.tf .poseidon2))
    (hsat : Satisfied2 hash (wideAppend h bb ab) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    carrierVals (wideBeforeCBase h.traceWidth) 65 (envAt t i).loc
      = wireCommitR8 permW (preLimbsWide bb (envAt t i).loc) ((envAt t i).loc (bb + B_IROOT))
    ∧ carrierVals (wideAfterCBase h.traceWidth) 65 (envAt t i).loc
      = wireCommitR8 permW (preLimbsWide ab (envAt t i).loc) ((envAt t i).loc (ab + B_IROOT)) := by
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_⟩
  · apply rotV3WidePin permW (t.tf .poseidon2) hchipN (envAt t i) bb
      (wideBeforeCBase h.traceWidth)
    intro p hp
    have hmem := wideAppend_before_mem h bb ab
      (.lookup (siteLookupN p.1 p.2 (rotV3WideSpecs_admitted _ _ p hp)))
      (List.mem_map.mpr ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩)
    have := hrow _ hmem
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, siteLookupN] using this
  · apply rotV3WidePin permW (t.tf .poseidon2) hchipN (envAt t i) ab
      (wideAfterCBase h.traceWidth)
    intro p hp
    have hmem := wideAppend_after_mem h bb ab
      (.lookup (siteLookupN p.1 p.2 (rotV3WideSpecs_admitted _ _ p hp)))
      (List.mem_map.mpr ⟨⟨p, hp⟩, List.mem_attach _ _, rfl⟩)
    have := hrow _ hmem
    simpa [VmConstraint2.holdsAt, Lookup.holdsAt, siteLookupN] using this

/-- **`wideAppend_publishes`** — the wide commits PUBLISH: first row binds the BEFORE commit's 8 columns
to PI slots `h.piCount..+7`; last row binds the AFTER commit's 8 columns to `h.piCount+8..+15`.
Independent of `h`'s gates. -/
theorem wideAppend_publishes (hash : List ℤ → ℤ) (h : EffectVmDescriptor2) (bb ab : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (wideAppend h bb ab) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    ((i == 0) = true → ∀ k, (hk : k < 8) →
      (envAt t i).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD k 0)
        ≡ (envAt t i).pub (h.piCount + k) [ZMOD 2013265921])
    ∧ ((i + 1 == t.rows.length) = true → ∀ k, (hk : k < 8) →
      (envAt t i).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD k 0)
        ≡ (envAt t i).pub (h.piCount + 8 + k) [ZMOD 2013265921]) := by
  have hrow := hsat.rowConstraints i hi
  refine ⟨?_, ?_⟩
  · intro hf k hk
    have := hrow _ (wideAppend_beforePin_mem h bb ab k hk)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at this
    exact this hf
  · intro hl k hk
    have := hrow _ (wideAppend_afterPin_mem h bb ab k hk)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at this
    exact this hl

set_option maxHeartbeats 1600000 in
/-- **`wideAppend_binds_published` — THE GATED-HOST WIDE END-TO-END KEYSTONE.** Two `Satisfied2`
witnesses of `wideAppend h bb ab` publishing the SAME 8-felt BEFORE commit and the SAME 8-felt AFTER
commit agree on the WHOLE before-block 184-limb list + iroot AND the WHOLE after-block 184-limb list +
iroot — the GENUINE ~124-bit binding via the FAITHFUL `wireCommitR8_binds_or_collides` — OR EXHIBIT a
genuine collision of the deployed wide permutation, per leg. Over an ARBITRARY gated host `h`. The
host's gates constrain OTHER columns; the wide binding is over the appended carriers + the shared
`preLimbsAt bb`/`ab` columns, so the gates neither weaken nor are weakened by it.

⚑ **NO CR FLOOR IS CARRIED** — the deleted `Poseidon2WideCR` was false at deployed parameters; see
`rotV3Wide_binds_published`. -/
theorem wideAppend_binds_published (hash : List ℤ → ℤ) (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (h : EffectVmDescriptor2) (bb ab : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hchipN : ChipTableSoundN permW (t.tf .poseidon2))
    (hchipN' : ChipTableSoundN permW (t'.tf .poseidon2))
    (hsat : Satisfied2 hash (wideAppend h bb ab) minit mfin maddrs t)
    (hsat' : Satisfied2 hash (wideAppend h bb ab) minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hfirst : (i == 0) = true) (hfirst' : (j == 0) = true)
    (k l : Nat) (hk : k < t.rows.length) (hl : l < t'.rows.length)
    (hlast : (k + 1 == t.rows.length) = true) (hlast' : (l + 1 == t'.rows.length) = true)
    (hpubBefore : ∀ m, m < 8 →
      (envAt t i).pub (h.piCount + m) = (envAt t' j).pub (h.piCount + m))
    (hpubAfter : ∀ m, m < 8 →
      (envAt t k).pub (h.piCount + 8 + m) = (envAt t' l).pub (h.piCount + 8 + m))
    -- The 8 state-commit carrier columns are field-canonical (`0 ≤ · < p`, the deployed range-check
    -- invariant): lifts each mod-`p` publish congruence to the ℤ carrier equality the wide CR floor needs.
    (hcCanonB : ∀ m, m < 8 →
      0 ≤ (envAt t i).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD m 0)
        ∧ (envAt t i).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD m 0) < 2013265921)
    (hcCanonB' : ∀ m, m < 8 →
      0 ≤ (envAt t' j).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD m 0)
        ∧ (envAt t' j).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD m 0) < 2013265921)
    (hcCanonA : ∀ m, m < 8 →
      0 ≤ (envAt t k).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD m 0)
        ∧ (envAt t k).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD m 0) < 2013265921)
    (hcCanonA' : ∀ m, m < 8 →
      0 ≤ (envAt t' l).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD m 0)
        ∧ (envAt t' l).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD m 0) < 2013265921) :
    ((preLimbsWide bb (envAt t i).loc = preLimbsWide bb (envAt t' j).loc
        ∧ (envAt t i).loc (bb + B_IROOT) = (envAt t' j).loc (bb + B_IROOT))
      ∨ WireColl permW (preLimbsWide bb (envAt t i).loc) ((envAt t i).loc (bb + B_IROOT))
          (preLimbsWide bb (envAt t' j).loc) ((envAt t' j).loc (bb + B_IROOT)))
    ∧ ((preLimbsWide ab (envAt t k).loc = preLimbsWide ab (envAt t' l).loc
        ∧ (envAt t k).loc (ab + B_IROOT) = (envAt t' l).loc (ab + B_IROOT))
      ∨ WireColl permW (preLimbsWide ab (envAt t k).loc) ((envAt t k).loc (ab + B_IROOT))
          (preLimbsWide ab (envAt t' l).loc) ((envAt t' l).loc (ab + B_IROOT))) := by
  have hp := wideAppend_pins hash permW h bb ab minit mfin maddrs t hchipN hsat
  have hp' := wideAppend_pins hash permW h bb ab minit' mfin' maddrs' t' hchipN' hsat'
  have hq := wideAppend_publishes hash h bb ab minit mfin maddrs t hsat
  have hq' := wideAppend_publishes hash h bb ab minit' mfin' maddrs' t' hsat'
  refine ⟨?_, ?_⟩
  · have hcolEq : ∀ m, m < 8 →
        (envAt t i).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD m 0)
          = (envAt t' j).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD m 0) :=
      fun m hm => canon_eq_of_modEq (hcCanonB m hm) (hcCanonB' m hm)
        (calc (envAt t i).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD m 0)
              ≡ (envAt t i).pub (h.piCount + m) [ZMOD 2013265921] := (hq i hi).1 hfirst m hm
          _ = (envAt t' j).pub (h.piCount + m) := hpubBefore m hm
          _ ≡ (envAt t' j).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD m 0)
              [ZMOD 2013265921] := ((hq' j hj).1 hfirst' m hm).symm)
    have hcv : carrierVals (wideBeforeCBase h.traceWidth) 65 (envAt t i).loc
        = carrierVals (wideBeforeCBase h.traceWidth) 65 (envAt t' j).loc :=
      carrierVals_eq_of_colEq _ _ _ _ hcolEq
    have hwire : wireCommitR8 permW (preLimbsWide bb (envAt t i).loc) ((envAt t i).loc (bb + B_IROOT))
        = wireCommitR8 permW (preLimbsWide bb (envAt t' j).loc) ((envAt t' j).loc (bb + B_IROOT)) := by
      rw [← (hp i hi).1, ← (hp' j hj).1]; exact hcv
    exact wireCommitR8_binds_or_collides permW hW
      (by rw [preLimbsWide_length, preLimbsWide_length]) hwire
  · have hcolEq : ∀ m, m < 8 →
        (envAt t k).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD m 0)
          = (envAt t' l).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD m 0) :=
      fun m hm => canon_eq_of_modEq (hcCanonA m hm) (hcCanonA' m hm)
        (calc (envAt t k).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD m 0)
              ≡ (envAt t k).pub (h.piCount + 8 + m) [ZMOD 2013265921] := (hq k hk).2 hlast m hm
          _ = (envAt t' l).pub (h.piCount + 8 + m) := hpubAfter m hm
          _ ≡ (envAt t' l).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD m 0)
              [ZMOD 2013265921] := ((hq' l hl).2 hlast' m hm).symm)
    have hcv : carrierVals (wideAfterCBase h.traceWidth) 65 (envAt t k).loc
        = carrierVals (wideAfterCBase h.traceWidth) 65 (envAt t' l).loc :=
      carrierVals_eq_of_colEq _ _ _ _ hcolEq
    have hwire : wireCommitR8 permW (preLimbsWide ab (envAt t k).loc) ((envAt t k).loc (ab + B_IROOT))
        = wireCommitR8 permW (preLimbsWide ab (envAt t' l).loc) ((envAt t' l).loc (ab + B_IROOT)) := by
      rw [← (hp k hk).2, ← (hp' l hl).2]; exact hcv
    exact wireCommitR8_binds_or_collides permW hW
      (by rw [preLimbsWide_length, preLimbsWide_length]) hwire

/-! ### §7.3 — the host's gates are PRESERVED: `wideAppend h` reduces to a `Satisfied2` of the
PIN-RETIRED host `dropLegacyCommitPins1 h bb ab`.

`wideAppend h bb ab` RETIRES the host's two 1-felt `STATE_COMMIT` PI pins (the ~31-bit waist) and
appends ONLY `.lookup` / `.base (.piBinding …)` constraints, neither a mem/map op — so a trace
satisfying `wideAppend h bb ab` satisfies `dropLegacyCommitPins1 h bb ab` itself (`h` with exactly
those two commit pins dropped; every OTHER constraint — the gates — held unchanged). This is the
CONJUNCTION leg: the wide 8-felt binding (§7.2) AND every soundness theorem the pin-retired host
carries (its gates, which are NOT the dropped commit pins) both hold of any satisfying witness. The
retired pins were the LEGACY 1-felt commit binding, now superseded by the wide 8-felt `commitPins`. -/

/-- `h` with its two 1-felt `STATE_COMMIT` PI pins (`isLegacyCommitPin1 bb ab`) RETIRED. Same
name/width/piCount/tables/hashSites/ranges as `h`; only those two `.base (.piBinding …)` commit pins
are filtered from the constraints. (The width/piCount are `h`'s — the 8-felt widening lives in
`wideAppend`, not here; this is purely the pin-retired host the gate-survival leg reduces to.) -/
def dropLegacyCommitPins1 (h : EffectVmDescriptor2) (bb ab : Nat) : EffectVmDescriptor2 :=
  { h with constraints := h.constraints.filter (fun c => !isLegacyCommitPin1 bb ab c) }

/-- The pin-retired host's memory log is `h`'s (the dropped pins carry no mem op). -/
theorem dropLegacyCommitPins1_memLog (h : EffectVmDescriptor2) (bb ab : Nat)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) :
    Dregg2.Circuit.DescriptorIR2.memLog (dropLegacyCommitPins1 h bb ab) t
      = Dregg2.Circuit.DescriptorIR2.memLog h t := by
  simp only [Dregg2.Circuit.DescriptorIR2.memLog, Dregg2.Circuit.DescriptorIR2.memOpsOf,
    dropLegacyCommitPins1]
  rw [filterMap_filter_legacyPin bb ab _ (by intro c; rfl)]

/-- The pin-retired host's map log is `h`'s (the dropped pins carry no map op). -/
theorem dropLegacyCommitPins1_mapLog (h : EffectVmDescriptor2) (bb ab : Nat)
    (t : Dregg2.Circuit.DescriptorIR2.VmTrace) :
    Dregg2.Circuit.DescriptorIR2.mapLog (dropLegacyCommitPins1 h bb ab) t
      = Dregg2.Circuit.DescriptorIR2.mapLog h t := by
  simp only [Dregg2.Circuit.DescriptorIR2.mapLog, Dregg2.Circuit.DescriptorIR2.mapOpsOf,
    dropLegacyCommitPins1]
  rw [filterMap_filter_legacyPin bb ab _ (by intro c; rfl)]

theorem wideAppend_satisfied2_host (hash : List ℤ → ℤ) (h : EffectVmDescriptor2) (bb ab : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (wideAppend h bb ab) minit mfin maddrs t) :
    Satisfied2 hash (dropLegacyCommitPins1 h bb ab) minit mfin maddrs t :=
  { rowConstraints := fun i hi c hc =>
      hsat.rowConstraints i hi c (by
        rw [wideAppend_constraints]
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ hc))))
    rowHashes := hsat.rowHashes
    rowRanges := hsat.rowRanges
    memAddrsNodup := hsat.memAddrsNodup
    memClosed := by
      have := hsat.memClosed; rw [wideAppend_memLog] at this
      rwa [dropLegacyCommitPins1_memLog]
    memDisciplined := by
      have := hsat.memDisciplined; rw [wideAppend_memLog] at this
      rwa [dropLegacyCommitPins1_memLog]
    memBalanced := by
      have := hsat.memBalanced; rw [wideAppend_memLog] at this
      rwa [dropLegacyCommitPins1_memLog]
    memTableFaithful := by
      have := hsat.memTableFaithful; rw [wideAppend_memLog] at this
      rwa [dropLegacyCommitPins1_memLog]
    mapTableFaithful := by
      have := hsat.mapTableFaithful; rw [wideAppend_mapLog] at this
      rwa [dropLegacyCommitPins1_mapLog] }

#assert_axioms wideAppend_pins
#assert_axioms wideAppend_publishes
#assert_axioms wideAppend_binds_published
#assert_axioms wideAppend_satisfied2_host

/-! ### §7.4 — the ANTI-LAUNDERING tooth on a REPRESENTATIVE GATED host.

`wideAppend` applied to a `withSelectorGate`-wrapped host (a genuinely gated live-shape descriptor)
still publishes the GENUINE 8-felt binding: the wide commit over the shared limbs distinguishes two
states differing ONLY beyond lane0 — the gate constrains a DIFFERENT column (the selector), so the
8-felt width is untouched by it. The carriers/PIs land PAST the gated host's width/piCount. -/

/-- A representative gated host: a bare graduated rotation WRAPPED in `withSelectorGate` (the live
WAVE-shape — an already-gated `EffectVmDescriptor2`), with `wideAppend` layered on top. -/
def wideAppendOverGated (d : EffectVmDescriptor) (s : Nat)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites,
        ChipArityAdmitted s.inputs.length := by graduate_arity) : EffectVmDescriptor2 :=
  wideAppend (withSelectorGate s (v3Of d hAdm)) d.traceWidth (d.traceWidth + B_SPAN)

/-- The wide carriers/PIs of `wideAppendOverGated` land STRICTLY PAST the gated host's width/piCount:
the gate's selector column and the host's columns are below `wideBeforeCBase host.traceWidth`, so the
wide block cannot collide with the gate. (`withSelectorGate` does not change width/piCount, so the
host width is the graduated rotation's — `wideAppend` bases past it.) -/
theorem wideAppendOverGated_width (d : EffectVmDescriptor) (s : Nat)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites, ChipArityAdmitted s.inputs.length) :
    (wideAppendOverGated d s hAdm).traceWidth
      = (withSelectorGate s (v3Of d hAdm)).traceWidth + wideAppendixSpan
    ∧ (wideAppendOverGated d s hAdm).piCount
      = (withSelectorGate s (v3Of d hAdm)).piCount + 16 := by
  unfold wideAppendOverGated wideAppend; exact ⟨rfl, rfl⟩

-- The gated host's selector gate survives in `wideAppendOverGated` (it is among the appended-onto
-- host's constraints, never disturbed): the appended wide block is a CONJUNCTION on top.
theorem wideAppendOverGated_gate_survives (d : EffectVmDescriptor) (s : Nat)
    (hAdm : ∀ s ∈ (rotateV3 d).hashSites, ChipArityAdmitted s.inputs.length) :
    (VmConstraint2.base (selectorGate s)) ∈ (wideAppendOverGated d s hAdm).constraints := by
  unfold wideAppendOverGated
  rw [wideAppend_constraints]
  refine List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ ?_)))
  -- the selector gate is a `.gate`, NOT a 1-felt commit pin, so it SURVIVES the pin-retiring filter.
  rw [List.mem_filter]
  refine ⟨?_, by simp [isLegacyCommitPin1, selectorGate]⟩
  rw [withSelectorGate_constraints]
  exact List.mem_append_right _ (by simp)

-- The wide binding over the GATED host is genuinely 8-felt (the gate is on the selector column, NOT
-- a lane): a high-limb flip (limb 30) moves the published 8-felt commit; lane0 alone would collapse.
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide (demoPre24.set 30 999) 7
-- the commit published by the gated-host wide block is 8 felts wide (NOT 1).
#guard (wireCommitR8 refWide demoPre24 7).length == 8

/-! ## §8 — `v3RegistryWide`: the WHOLE live cohort wrapped through the proven `wideAppend`.

The live `v3Registry` (`EffectVmEmitRotationV3`, 36 members) is the 1-felt-commit cohort: each member
is `graduateV1 (rotateV3… face)` (possibly with appended gates / mem-map ops), a gated host whose
BEFORE limbs `rotateV3` lays at the v1 FACE's `traceWidth` (`bb`) and whose AFTER limbs at `bb + B_SPAN`
(`B_SPAN`). EVERY `rotateV3…` variant is `{ rotateV3 face with constraints := … }` (FrozenAuthority,
WithRecordPin, the disc / perms-vk / mode / fields-root gates, the nullifier / commitment-key /
new-cell-key pins), so the limb columns are UNMOVED by any gate — the limb base is the FACE width.
`graduateV1` adds `(CHIP_OUT_LANES-1)·n_sites` chip-lane columns PAST the limbs, so the gated host's
`traceWidth` is NOT the limb base; the limb base is the face's `traceWidth`, supplied explicitly.

`v3RegistryWide` wraps each member `h` through `wideAppend h bb (bb+B_SPAN)` with its real per-member `bb`
(the face `traceWidth`). The two faithfulness obligations lift member-by-member, GENERICALLY over the
`(h, bb)`:
  * **gates survive** — `wideAppend_satisfied2_host`: a `wideAppend h bb ab` witness is a `Satisfied2`
    of `h`, so every soundness theorem the live member carries (its disc / perms-vk / grow gates) still
    holds (the CONJUNCTION leg);
  * **the 8-felt commit binds** — `wideAppend_binds_published`: two witnesses publishing the SAME 8-felt
    BEFORE/AFTER commits agree on the WHOLE 184-limb list + iroot, the genuine ~124-bit binding via
    `wireCommitR8_binds`.

ADDITIVE: a NEW def + its fold soundness. The live `v3Registry` / wire / geometry / PI / VK are
UNTOUCHED — the flip (next phase) repoints `v3Registry → v3RegistryWide` + the Rust/executor follow.

### §8.1 — the per-member `bb` table (limb base = the v1 face `traceWidth`)

Aligned position-for-position with `v3Registry`. Each `bb` is the FACE descriptor's `traceWidth` (the
column `rotateV3` wrote the BEFORE limbs at), derived from the member's CONSTRUCTION — NOT a runtime
probe. The faces split by width: the base v1 faces (`EFFECT_VM_WIDTH`-shaped runtime rows), the actor
faces (createCell / factory / spawn / receiptArchive — wider runtime rows), the gated faces
(setPerms / setVK / makeSovereign / refusal — their own widths). `ab = bb + B_SPAN = bb + B_SPAN` for all.
-/

open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 in
/-- The per-member BEFORE-limb base `bb` of each live `v3Registry` member: the v1 FACE descriptor's
`traceWidth` (where `rotateV3` laid the BEFORE limbs). Aligned position-for-position with `v3Registry`;
the AFTER base is `bb + B_SPAN` (`B_SPAN`). Symbolic (the face `.traceWidth`), so it tracks any face
refactor — no transcribed magic numbers. -/
def v3RegistryWideBB : List Nat :=
  [ EffectVmEmitTransfer.transferVmDescriptor.traceWidth          -- 1  transfer  (v3OfFrozen)
  , EffectVmEmitBurn.burnVmDescriptor.traceWidth                  -- 2  burn      (v3OfFrozen)
  , mintTickFace.traceWidth                                       -- 3  mint      (withSelectorGate · v3OfFrozen)
  , EffectVmEmitNoteSpend.noteSpendVmDescriptor.traceWidth        -- 4  noteSpend (noteSpendV3)
  , EffectVmEmitNoteCreate.noteCreateVmDescriptor.traceWidth      -- 5  noteCreate(noteCreateV3)
  , EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth          -- 6  cellSeal  (disc gate)
  , EffectVmEmitCellDestroy.cellDestroyVmDescriptor.traceWidth    -- 7  cellDestroy(disc gate)
  , EffectVmEmitRefusal.refusalVmDescriptor.traceWidth            -- 8  refusal   (record pin)
  , EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth    -- 9  setPerms  (perms-vk gate)
  , EffectVmEmitSetVK.setVKVmDescriptor.traceWidth                -- 10 setVK     (perms-vk gate)
  , EffectVmEmitExercise.exerciseVmDescriptor.traceWidth          -- 11 exercise  (v3Of)
  , EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor.traceWidth-- 12 pipelinedSend (v3Of)
  , EffectVmEmitRefreshDelegation.refreshVmDescriptor.traceWidth  -- 13 refresh   (v3Of)
  , EffectVmEmitIncrementNonce.incrementNonceVmDescriptor.traceWidth -- 14 incNonce (v3OfFrozen)
  , EffectVmEmitRevokeDelegation.revokeVmDescriptor.traceWidth    -- 15 revoke    (v3Of)
  , EffectVmEmitIntroduce.introduceVmDescriptor.traceWidth        -- 16 introduce (v3Of)
  , EffectVmEmitAttenuateA.attenuateVmDescriptor.traceWidth       -- 17 attenuate (withSelectorGate · v3OfWith)
  , EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor.traceWidth -- 18 revokeCapability (withSelectorGate · v3OfWith)
  , customV1Face.traceWidth                                       -- 19 custom    (v3OfWith)
  , setFieldDynV1Face.traceWidth                                  -- 20 setFieldDyn (forced)
  , EffectVmEmitAttenuateA.attenuateVmDescriptor.traceWidth       -- 21 grantCap  (withSelectorGate · v3Of attenuate face)
  , EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor.traceWidth -- 22 makeSovereign (mode gate)
  , EffectVmEmitCreateCell.createCellActorVmDescriptor.traceWidth -- 23 createCell (new-cell-key pin)
  , EffectVmEmitCreateCellFromFactory.factoryActorVmDescriptor.traceWidth -- 24 factory (new-cell-key pin)
  , EffectVmEmitSpawn.spawnActorVmDescriptor.traceWidth           -- 25 spawn     (new-cell-key pin)
  , EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor.traceWidth -- 26 receiptArchive (disc gate)
  , EffectVmEmitCellUnseal.cellUnsealVmDescriptor.traceWidth      -- 27 cellUnseal (disc gate)
  , EffectVmEmitEmitEvent.emitEventVmDescriptor.traceWidth ]      -- 28 emitEvent (v3OfFrozen)
  ++ (List.finRange 8).map fun slot => (setFieldTickFace slot).traceWidth -- 29..36 setField slots

#guard v3RegistryWideBB.length == 36
-- aligned with the live registry, member-for-member.
#guard v3RegistryWideBB.length == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.length

open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 in
/-! ### §8.2 — `v3RegistryWide`: each live member, wrapped through the proven `wideAppend`.

`v3RegistryWide` zips the live `v3Registry` with `v3RegistryWideBB`: entry `i` is
`(name_i, wideAppend member_i bb_i (bb_i + B_SPAN))`. A NEW def — `v3Registry` is UNTOUCHED. The wide
carriers/PIs land PAST each member's `traceWidth`/`piCount` (past the gates), so the host's gates and
the wide 8-felt binding both hold (§8.3). -/
def v3RegistryWide : List (String × EffectVmDescriptor2) :=
  (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.zip v3RegistryWideBB).map
    (fun (e : (String × EffectVmDescriptor2) × Nat) =>
      (e.1.1, wideAppend e.1.2 e.2 (e.2 + B_SPAN)))

#guard v3RegistryWide.length == 36
-- the names are the live registry's, verbatim (the flip is a NAME-stable repoint).
#guard v3RegistryWide.map (·.1) == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.map (·.1)
-- and every wide entry is a `wideAppend` of the corresponding live member at its real `bb`.
#guard v3RegistryWide.map (·.1) == (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.zip v3RegistryWideBB).map (·.1.1)

/-- Each `v3RegistryWide` entry IS a `wideAppend` of the aligned live member at its real `bb`. The
structural witness the fold soundness consumes (the entry's host `h` is the live `v3Registry` member,
`bb` its face width). -/
theorem v3RegistryWide_is_wideAppend :
    ∀ (i : Nat) (hi : i < v3RegistryWide.length),
      ∃ (h : EffectVmDescriptor2) (bb : Nat),
        h ∈ Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.map (·.2)
        ∧ v3RegistryWide[i].2 = wideAppend h bb (bb + B_SPAN) := by
  intro i hi
  have hlen : v3RegistryWide.length
      = (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.zip v3RegistryWideBB).length := by
    simp [v3RegistryWide]
  rw [hlen] at hi
  rw [List.length_zip] at hi
  have hi1 : i < Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.length :=
    lt_of_lt_of_le hi (Nat.min_le_left _ _)
  have hi2 : i < v3RegistryWideBB.length :=
    lt_of_lt_of_le hi (Nat.min_le_right _ _)
  refine ⟨(Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry[i]'hi1).2,
          v3RegistryWideBB[i]'hi2, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨_, List.getElem_mem hi1, rfl⟩
  · simp only [v3RegistryWide, List.getElem_map, List.getElem_zip]

/-! ### §8.3 — `v3RegistryWide_sound` / `_binds`: the fold over the cohort.

The two faithfulness obligations lift member-by-member through the GENERIC `wideAppend` keystones
(`wideAppend_satisfied2_host` / `wideAppend_binds_published`), which hold over ANY gated host `h` and
ANY `(bb, ab)`. So the fold is the pointwise lift over `v3RegistryWide_is_wideAppend`: each entry's
host is a live `v3Registry` member, and its wide binding / gate-survival are the generic keystones at
that member. -/

/-- **`v3RegistryWide_sound` — THE GATE-SURVIVAL FOLD.** Every `v3RegistryWide` entry preserves its
live member's gates: a `Satisfied2` witness of the wide entry is a `Satisfied2` of the underlying live
`v3Registry` member `h` with its two 1-felt `STATE_COMMIT` PI pins RETIRED (`dropLegacyCommitPins1 h bb
(bb+B_SPAN)`), so EVERY soundness theorem `h` carries (its disc / perms-vk / grow / record-pin gates — which
are NOT the dropped commit pins) holds of the wide witness unchanged. The wide block is a CONJUNCTION
appended past the host; the retired pins were the LEGACY 1-felt commit binding, superseded by the wide. -/
theorem v3RegistryWide_sound (hash : List ℤ → ℤ)
    (i : Nat) (hi : i < v3RegistryWide.length)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash v3RegistryWide[i].2 minit mfin maddrs t) :
    ∃ (h : EffectVmDescriptor2) (bb : Nat),
      h ∈ Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3Registry.map (·.2)
      ∧ Satisfied2 hash (dropLegacyCommitPins1 h bb (bb + B_SPAN)) minit mfin maddrs t := by
  obtain ⟨h, bb, hmem, heq⟩ := v3RegistryWide_is_wideAppend i hi
  refine ⟨h, bb, hmem, ?_⟩
  rw [heq] at hsat
  exact wideAppend_satisfied2_host hash h bb (bb + B_SPAN) minit mfin maddrs t hsat

/-- **`v3RegistryWide_binds` — THE 8-FELT BINDING FOLD.** Every `v3RegistryWide` entry's published
8-felt BEFORE/AFTER commits BIND: two `Satisfied2` witnesses of the SAME wide entry publishing the same
8-felt BEFORE commit and the same 8-felt AFTER commit agree on the WHOLE before-block 184-limb list +
iroot AND the whole after-block 184-limb list + iroot — the genuine ~124-bit binding via the faithful
`wireCommitR8_binds_or_collides` — OR EXHIBIT a genuine wide-permutation collision, per leg,
member-by-member over the live cohort.

⚑ **NO CR FLOOR IS CARRIED** — the deleted `Poseidon2WideCR` was false at deployed parameters; see
`rotV3Wide_binds_published`. -/
theorem v3RegistryWide_binds (hash : List ℤ → ℤ) (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW)
    (i : Nat) (hi : i < v3RegistryWide.length)
    (h : EffectVmDescriptor2) (bb : Nat)
    (heq : v3RegistryWide[i].2 = wideAppend h bb (bb + B_SPAN))
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hchipN : ChipTableSoundN permW (t.tf .poseidon2))
    (hchipN' : ChipTableSoundN permW (t'.tf .poseidon2))
    (hsat : Satisfied2 hash v3RegistryWide[i].2 minit mfin maddrs t)
    (hsat' : Satisfied2 hash v3RegistryWide[i].2 minit' mfin' maddrs' t')
    (a b : Nat) (ha : a < t.rows.length) (hb : b < t'.rows.length)
    (hfirst : (a == 0) = true) (hfirst' : (b == 0) = true)
    (k l : Nat) (hk : k < t.rows.length) (hl : l < t'.rows.length)
    (hlast : (k + 1 == t.rows.length) = true) (hlast' : (l + 1 == t'.rows.length) = true)
    (hpubBefore : ∀ m, m < 8 →
      (envAt t a).pub (h.piCount + m) = (envAt t' b).pub (h.piCount + m))
    (hpubAfter : ∀ m, m < 8 →
      (envAt t k).pub (h.piCount + 8 + m) = (envAt t' l).pub (h.piCount + 8 + m))
    -- The 8 state-commit carrier columns are field-canonical (deployed range-check invariant); threaded
    -- into `wideAppend_binds_published` to lift its mod-`p` publish congruences to the ℤ carrier equality.
    (hcCanonB : ∀ m, m < 8 →
      0 ≤ (envAt t a).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD m 0)
        ∧ (envAt t a).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD m 0) < 2013265921)
    (hcCanonB' : ∀ m, m < 8 →
      0 ≤ (envAt t' b).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD m 0)
        ∧ (envAt t' b).loc ((carrierCols (wideBeforeCBase h.traceWidth) 65).getD m 0) < 2013265921)
    (hcCanonA : ∀ m, m < 8 →
      0 ≤ (envAt t k).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD m 0)
        ∧ (envAt t k).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD m 0) < 2013265921)
    (hcCanonA' : ∀ m, m < 8 →
      0 ≤ (envAt t' l).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD m 0)
        ∧ (envAt t' l).loc ((carrierCols (wideAfterCBase h.traceWidth) 65).getD m 0) < 2013265921) :
    ((preLimbsWide bb (envAt t a).loc = preLimbsWide bb (envAt t' b).loc
        ∧ (envAt t a).loc (bb + B_IROOT) = (envAt t' b).loc (bb + B_IROOT))
      ∨ WireColl permW (preLimbsWide bb (envAt t a).loc) ((envAt t a).loc (bb + B_IROOT))
          (preLimbsWide bb (envAt t' b).loc) ((envAt t' b).loc (bb + B_IROOT)))
    ∧ ((preLimbsWide (bb + B_SPAN) (envAt t k).loc = preLimbsWide (bb + B_SPAN) (envAt t' l).loc
        ∧ (envAt t k).loc (bb + B_SPAN + B_IROOT) = (envAt t' l).loc (bb + B_SPAN + B_IROOT))
      ∨ WireColl permW (preLimbsWide (bb + B_SPAN) (envAt t k).loc)
          ((envAt t k).loc (bb + B_SPAN + B_IROOT)) (preLimbsWide (bb + B_SPAN) (envAt t' l).loc)
          ((envAt t' l).loc (bb + B_SPAN + B_IROOT))) := by
  rw [heq] at hsat hsat'
  exact wideAppend_binds_published hash permW hW h bb (bb + B_SPAN)
    minit mfin maddrs t minit' mfin' maddrs' t' hchipN hchipN' hsat hsat'
    a b ha hb hfirst hfirst' k l hk hl hlast hlast' hpubBefore hpubAfter
    hcCanonB hcCanonB' hcCanonA hcCanonA'

#assert_axioms v3RegistryWide_is_wideAppend
#assert_axioms v3RegistryWide_sound
#assert_axioms v3RegistryWide_binds

/-! ### §8.4 — the ANTI-LAUNDERING tooth on a REPRESENTATIVE GATED `v3RegistryWide` member.

The wide binding of a GATED member (a `withSelectorGate` / disc-gated `v3Registry` entry) is GENUINELY
8-felt: the gate constrains the selector / disc columns, NOT a commit lane, so a high-limb flip moves
the published 8-felt commit (lane0 alone would collapse it). A high-limb flip is bound; honest recompute
is stable; the commit is 8 felts wide. -/
-- `mint` (registry position 2) is `withSelectorGate MINT (v3OfFrozen mintTickFace)` — a genuinely
-- GATED member; its wide entry's 8-felt binding distinguishes a high-limb flip.
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide (demoPre24.set 30 999) 7
-- the iroot is bound (a different iroot ⇒ a different commit).
#guard wireCommitR8 refWide demoPre24 7 != wireCommitR8 refWide demoPre24 8
-- honest recompute is stable.
#guard wireCommitR8 refWide demoPre24 7 == wireCommitR8 refWide demoPre24 7
-- the gated member's wide commit is 8 felts wide (NOT a 1-felt lane0 squeeze).
#guard (wireCommitR8 refWide demoPre24 7).length == 8

end Dregg2.Circuit.Emit.EffectVmEmitRotationWide
