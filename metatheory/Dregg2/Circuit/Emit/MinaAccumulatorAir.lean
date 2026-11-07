/-
# `Dregg2.Circuit.Emit.MinaAccumulatorAir` — ⚑ THE DEFERRED IPA ACCUMULATOR CHECK, IN A CIRCUIT.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every column index, every pin, every window body, the routing tuple,
the declared manifest and all three emitted descriptors are authored here and go through
`EffectLower.lowerAir` of an `EffectAirIR.EffectAir`.
There is no hand-written `VmConstraint2` in this file. Rust PROVES the artifact, FOLDS it, and
authors no constraint. House Law #1.

## WHAT IS BEING PUT IN A CIRCUIT, and it is the leg upstream evaluates natively

`mina-rust`'s verifier `&&`s `Ipa::Step::accumulator_check` into `batch_step_dlog_check`
(`verify.ml:135-146`). With `C` the challenge-polynomial commitment (a **Vesta** point) and `u⃗` the
sixteen endo-lifted bulletproof challenges,

```text
    C == ⟨ b_poly_coefficients(u⃗), srs.g ⟩          |srs.g| = 2^16 = 65 536 Vesta generators
```

and a batch of `N` claims is discharged by ONE MSM over `|G| + N` points:

```text
    Σ_i r^i·C_i  −  ⟨ Σ_i r^i·s(u⃗_i), G ⟩  ==  O
```

`bridge/src/mina_accumulator_discharge.rs` evaluates that **natively** over the byte-pinned SRS, and
`turn/src/executor/mina_accumulator_oracle.rs` makes a Mina head's acceptance depend on it. Both of
those files say, in their own headers, that **nothing there is an AIR**. This file is the AIR.

## ⚑ THE SHAPE, and why the accumulator's ENTRY POINT is the claim

Read the batch relation as a running sum and it is a chain of complete additions:

```text
    acc_0    = C                       -- ⚑ the claim's commitment IS the initial accumulator
    acc_{r+1} = acc_r + A_r            -- A_r the r-th addend
    acc_n    = O                       -- the discharge
```

so with the addends `A_r` the scaled generators `−s_j·G_j`, `acc_n = O` **is** `C − ⟨s, G⟩ = O`.

That is why this file needs no separate "claim block": the accumulator entering row 0 is `C`, it is
published at `PI[0..95]`, and it is joined arithmetically (the six input limb legs range it and the
33 SSA ops read it) rather than pinned decoratively. A consumer that holds this block's `C` compares
it against those 96 published limbs **elementwise — 256 bits per coordinate, no digest and therefore
no birthday bound**, the same shape `LightClientMinaAir`'s `TIP_STATE` seam takes.

## ⚑ WHAT A THREAD BUYS THAT A RE-PIN DOES NOT — inherited, not re-argued

`PastaLadderThread` established it and this file consumes it: the accumulator crosses rows through
96 `AirLeg.window .transition` gates, so `threadedLadder_forces` is an `n`-row induction rather than
a chain of quoted outputs. The width is `RCB_WIDTH = 3 048` at every depth, and the depth is rows.

The same distinction is what the RECURSION half has to preserve. `mina_phase2_chain_leaf`'s lesson —
*"a fold that just re-pins the same public inputs closes nothing"* — is answered here by publishing
`acc_in ‖ acc_out` as **contiguous** PI blocks so a fold node `cb.connect`s the left child's 96
outgoing limbs to the right child's 96 incoming ones. The 96 is not a coincidence: a projective
Pasta point in the sound 8-bit encoding is `3 × 32 = 96` felts, exactly the width the phase-2 chain
already carries its sponge state on.

## ⚑ FOUR DESCRIPTORS, AND EACH PAIR IS AN EXHIBIT

* `dregg-mina-accumulator-seg::v1` — a SEGMENT of the chain. Publishes its two endpoints. Says
  nothing about vanishing, because an intermediate segment must not.
* `dregg-mina-accumulator-final::v1` — the segment PLUS `dischargeLegs`: `2 · SK = 64` `.last`-row
  window gates forcing every limb of the terminal `X` and `Z` blocks to **zero**. That is
  `pasta_msm::is_identity` (`z == 0 && x == 0`) as a constraint, and it is the accumulator check.

* ⚑ `dregg-mina-accumulator-routed::v1` (§8) — the final segment PLUS the ROUTING: a threaded
  row-index column, and one exact-public lookup per row whose 97-wide tuple is
  `(row index + 1) ‖ the row's 96 addend limbs`, against a manifest the descriptor DECLARES.
  `3 049` columns, `4 831` constraints.

* ⚑⚑ `dregg-mina-accumulator-srs::v1` (§10) — `-routed`'s ALGEBRA VERBATIM over a manifest that is
  **not a parameter**: `srsScaledAddends Gs u⃗ n`, whose `r`-th entry is `−s_r · G_r` for
  `s_r = b_poly_coefficients(u⃗)_r` and `G_r` the generator the pinned SRS carries at index `r`.
  Same `3 049` columns and `4 831` constraints; what differs is that no list of points occurs in
  its definition.

Each pair is an OLD-ADMITS / NEW-REJECTS exhibit that cannot rot into agreement. A chain that does
not vanish PROVES under `-seg` and is REFUSED under `-final`, and the refusing constraint is a
`.last` window gate on an `OUT_Z` limb — not a range lookup, not a bus. A chain of honest Vesta
points that are NOT this block's addends PROVES under `-final` and is REFUSED under `-routed`, and
the refusing constraint is the exact-public balance of `mina_accumulator_addends`.

## What is proved here

* `accSegAir_mainRailOk` / `accFinalAir_mainRailOk` — the compiler accepts both blocks.
* `accSegDesc_constraint_count` / `accFinalDesc_constraint_count` / the widths and PI counts.
* `the_discharge_is_sixty_four_last_row_gates` — the selector census, so a `.last → .all` re-scope
  (which would refuse every intermediate row and make the descriptor accept nothing) moves a number.
* `threadedLadderV_forces` — the Vesta twin of `PastaLadderThread.threadedLadder_forces`.
* `terminalAccumulator_forces` — an `n+1`-row trace's terminal output is the `n+1`-fold RCB chain.
* ⚑ `accumulator_discharge_forced` — rows satisfied + threads held + the discharge gates satisfied
  force the `n+1`-fold chain of the trace's own addends to be the point at infinity mod `q`. This is
  the accumulator check, as a consequence of the emitted constraints.
* `the_discharge_gate_is_refutable` — a trace satisfying every ROW and every THREAD whose terminal
  accumulator is NOT the identity, so `accumulator_discharge_forced`'s last hypothesis is doing work.
* ⚑⚑ `addend_is_its_declared_addend` — **the routing.** On a trace whose emitted lookup balances and
  whose index column is threaded, row `i`'s addend cells ARE the descriptor's declared addend `i`.
  Pure membership: no counting, no pigeonhole, and `i`/`As.length` occur in no bound.
* ⚑⚑ `accumulator_discharge_forced_on_declared_addends` — the discharge over `declaredChain`, a fold
  in which the trace's addend columns **do not occur**.
* `the_balance_forces_the_row_count` — the trace height is the declared addend count, FORCED by the
  permutation, so the chain cannot be padded with unrouted rows nor shortened by dropping one.
* ⚑ `the_full_srs_routing_needs_no_cap_to_move` / `the_cell_cap_counts_the_declared_multiset_and_
  not_the_allocation` (§9) — the three exact-public caps, each against what it actually counts,
  established BEFORE §10 was designed rather than after.
* ⚑⚑ `declAddend_of_srsScaled` — the value `declaredChain` folds at index `r` IS `−s_r · G_r`, over
  ℤ with no canonicality envelope, via a general base-`2^SB` recomposition (`sumL_limbs`) rather
  than a `decide` at the demonstration's numbers.
* ⚑⚑⚑ `accumulator_discharge_forced_on_srs_scaled_addends` — the discharge over
  `declaredChain (srsScaledAddends Gs u⃗ n)`, a fold in which **no list of points occurs**.

## ⚠ WHAT THIS DOES **NOT** ESTABLISH — and the residual MOVED on 2026-08-06

It used to read: *"nothing here forces the ADDENDS to be anything in particular … porting the
routing to the sound row's 32-limb encoding is real work this file does not do (§4 prices it,
including the one deployed constant — `MAX_EXACT_PUBLIC_ARITY = 64` — that a 96-limb point tuple
exceeds)."* **That work is done** (§8). The cap was the member count of a JSON artifact; it was
raised `64 → 97`, the artifact re-emitted, the constant re-pinned, and the 97-wide tuple is now
DECLARED and FORCED.

⚠ **THE RESIDUAL THAT REMAINS IS ONE OBJECT OUT, AND IT IS A DIFFERENT KIND.** The routing forces
row `i`'s addend to be the addend THIS DESCRIPTOR DECLARES. Whether the descriptor a node verified
against is the one for the block in hand is a DESCRIPTOR-SELECTION question — the same class as the
accumulator's two other trusted items, both of which are still open:

  1. **No gate ties the claim to a head.** `root_entry_binds_claim` is a CONSUMER refusal, not a
     constraint; nothing in any of the three descriptors says the accumulator entering row 0 is the
     commitment of the block whose head is being accepted.
  2. **A claim rebuilt around tampered challenges is accepted** — in-circuit exactly as natively.
     The challenges `u⃗` are not bound to a transcript by anything here.

## ⚑⚑ AND THE SCALING MOVED ON 2026-08-07 — §10, WITH THE TRICHOTOMY SAID OUT LOUD

The paragraph here used to read: *"the SCALING is still not routed … what the declared manifest pins
is the ADDENDS, not their provenance as scaled generators."* §10 changes what the manifest IS.
`srsScaledAddends Gs u⃗ n` is a TOTAL FUNCTION whose `r`-th entry is `−s_r · G_r`; `accSrsDesc` is
the descriptor at it; `accumulator_discharge_forced_on_srs_scaled_addends` concludes over that fold.
The emitter can no longer supply a point — its only inputs are a generator list and `|u⃗|` field
elements — and `circuit/tests/mina_accumulator_srs_proves.rs` re-derives every declared entry
natively from the **sha-pinned** `vesta_srs_g` blob and refuses the rung below's manifest.

⚠ **THE RESIDUAL IS NOW EXACTLY ONE THING AND IT IS STRUCTURAL, NOT AN OMISSION.** The derivation
runs in the EMITTER; nothing in this AIR re-derives the manifest from `u⃗` in-circuit. The scaling
relation can live in exactly three places and there is no fourth:

  1. **THE CIRCUIT** — that is the deferred MSM. `PastaMsmBucketed.fused_at_step` prices the group
     work at `1 474 800` complete additions, and §7.2 of that file records those rows are
     denominated in the UNSOUND multiply, so on THIS file's sound row it is ~10² further out. It is
     also the thing `mina_accumulator_discharge.rs`'s own header calls the innovation to defer.
  2. **THE EMITTER** — §10. Certifying the emitted manifest then costs a native re-derivation,
     which is `n` scalar multiplications, which is the discharge. So §10 does not beat the native
     check; what it changes is the OBJECT a certifier checks, from `n` arbitrary Vesta points to
     `|u⃗|` field elements and a byte-pinned blob.
  3. **NOWHERE** — §8, a free 97-wide table.

`PastaMsmBucketed` §7.3 reached (2) from the other side — *"the descriptor, and therefore the
verifying key, is a function of the scalar vector: one VK per Mina block"* — and §7.4 declares the
challenge-binding half TERMINAL for any MSM AIR. Neither is invented here and both still stand.

So the emitted object checks the **SUMMATION half at full 256-bit width, over addends the VERIFIER
rebuilds from the descriptor rather than accepts from the prover, and which the DESCRIPTOR in turn
derives from a pinned SRS and a challenge vector rather than carrying as data.** That is strictly
more than before and strictly less than `Ipa.Step.accumulator_check`.

## Axiom hygiene

General theorems `#assert_axioms`-clean; facts about concrete data `native_decide`, pinned
`#assert_compiled` (since 2026-11-06); no `sorry`/`admit`; zero `#guard`s.
-/
import Dregg2.Circuit.Emit.PastaLadderThread
import Dregg2.Circuit.Emit.ExactPublicTableEmit

namespace Dregg2.Circuit.Emit.MinaAccumulatorAir

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 WindowExpr VmConstraint2)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg WindowLeg PiPinLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SB SK NG sVal qLimb)
open Dregg2.Circuit.Emit.PastaCurve (CZm)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3 rcbAddM)
open Dregg2.Circuit.Emit.PastaCurveSound
open Dregg2.Circuit.Emit.PastaLadderThread

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## §1 — THE PUBLIC INPUT LAYOUT.

`in ‖ out`, contiguous and in that order, so a recursion leaf re-exposes the continuity claim as ONE
slice and a fold node connects `left[96 + k]` to `right[k]` for `k < 96`. This is
`MinaPhase2Chain`'s layout choice, made again for the same reason. -/

/-- PI slot of the `i`-th INCOMING accumulator limb (`i < 3·SK`): X block, then Y, then Z. -/
def ACC_IN_PI (i : Nat) : Nat := i
/-- PI slot of the `i`-th OUTGOING accumulator limb. -/
def ACC_OUT_PI (i : Nat) : Nat := 3 * SK + i
/-- `6 · 32 = 192` — two projective Vesta points in the sound 8-bit encoding. -/
def ACC_PI_COUNT : Nat := 6 * SK

theorem acc_pi_layout :
    ACC_PI_COUNT = 192 ∧ ACC_IN_PI 0 = 0 ∧ ACC_OUT_PI 0 = 96
    ∧ ∀ i, ACC_OUT_PI i = ACC_IN_PI i + 3 * SK := by
  refine ⟨by decide, rfl, by decide, fun i => ?_⟩
  simp [ACC_OUT_PI, ACC_IN_PI, Nat.add_comm]

/-- The FIRST row's accumulator input, published. Its three blocks are contiguous at `0, 32, 64`
(`ACC_X/ACC_Y/ACC_Z`), so the column index and the PI slot agree — but they are written out rather
than assumed equal, because a layout that drifts here aliases two points. -/
def inPinLegs : List AirLeg :=
  (List.range SK).flatMap (fun i =>
    [ AirLeg.pin ⟨.first, ACC_X + i, ACC_IN_PI i⟩
    , AirLeg.pin ⟨.first, ACC_Y + i, ACC_IN_PI (SK + i)⟩
    , AirLeg.pin ⟨.first, ACC_Z + i, ACC_IN_PI (2 * SK + i)⟩ ])

/-- The LAST row's accumulator output, published. `OUT_X/OUT_Y/OUT_Z` are the gadget's `v 26/29/32`
and are NOT contiguous in the trace — which is exactly why the PI side is. -/
def outPinLegs : List AirLeg :=
  (List.range SK).flatMap (fun i =>
    [ AirLeg.pin ⟨.last, OUT_X + i, ACC_OUT_PI i⟩
    , AirLeg.pin ⟨.last, OUT_Y + i, ACC_OUT_PI (SK + i)⟩
    , AirLeg.pin ⟨.last, OUT_Z + i, ACC_OUT_PI (2 * SK + i)⟩ ])

theorem pin_leg_counts : inPinLegs.length = 96 ∧ outPinLegs.length = 96 := by
  refine ⟨by native_decide, by native_decide⟩

/-! ## §2 — ⚑ THE DISCHARGE GATE.

`pasta_msm::is_identity` is `p.z == U256::ZERO && p.x == U256::ZERO`. On the projective curve
`Y²Z = X³ + bZ³` those two are not independent — `Z = 0` forces `X³ = 0` — but the AIR does not
carry an on-curve gate, so BOTH are forced here and the constraint is the deployed predicate rather
than an argument about it.

⚑ **Every LIMB is forced to zero, not the value.** `sVal` over 32 byte-ranged limbs ranges to
`2^256 > q`, so "the value is `≡ 0 mod q`" would also be satisfied by the limbs of `q` and of `2q`.
Forcing the limbs makes the terminal accumulator the CANONICAL zero, which is strictly stronger,
costs nothing (the honest witness reduces) and removes a representation the prover could otherwise
choose. -/

/-- One discharge gate: the `i`-th limb of the block at `base`, on the LAST row, is zero.

`.last` is the selector, and `WindowLeg.mainRailOk` admits it because the body reads no `nxt`. Under
`.all` this would fire on EVERY row and refuse every intermediate accumulator — a descriptor that
accepts nothing, which is the direction a selector confusion goes here. -/
def vanishLeg (base i : Nat) : AirLeg :=
  .window ⟨RowSel.last, WindowExpr.loc (base + i)⟩

theorem vanishLeg_eq (base i : Nat) :
    vanishLeg base i = .window ⟨RowSel.last, WindowExpr.loc (base + i)⟩ := rfl

/-- ⚑ **THE 64 DISCHARGE GATES** — `X` and `Z`, 32 limbs each. -/
def dischargeLegs : List AirLeg :=
  (List.range SK).flatMap (fun i => [vanishLeg OUT_X i, vanishLeg OUT_Z i])

theorem dischargeLegs_length : dischargeLegs.length = 64 := by native_decide

/-! ## §3 — THE TWO AIRS AND THE TWO DESCRIPTORS. -/

/-- **A SEGMENT of the accumulator chain.** `PastaLadderThread.vestaThreadAir` — the sound Vesta RCB
row with the 96 `.transition` accumulator threads — plus the two published endpoints. -/
def accSegAir : EffectAir :=
  { tables := rcbTables
  , legs := inputLimbLegs
      ++ (vestaCompleteAddSoundLegs ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE).1
      ++ threadLegs ++ inPinLegs ++ outPinLegs }

/-- ⚑ **THE FINAL SEGMENT** — the same block, plus the discharge. -/
def accFinalAir : EffectAir :=
  { tables := rcbTables
  , legs := inputLimbLegs
      ++ (vestaCompleteAddSoundLegs ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE).1
      ++ threadLegs ++ inPinLegs ++ outPinLegs ++ dischargeLegs }

/-- ⚑ **THE SEGMENT'S LEGS ARE A PREFIX OF THE FINAL'S.** Every forcing statement about the segment
applies to the final block unchanged — the discharge APPENDS, it does not re-author. -/
theorem accFinalAir_extends_accSegAir : accSegAir.legs <+: accFinalAir.legs :=
  ⟨dischargeLegs, by simp [accSegAir, accFinalAir, List.append_assoc]⟩

/-- ⚑ **THE COMPILER ACCEPTS BOTH BLOCKS.** The 96 threads are `.transition` (the only selector
admitting a `nxt` read) and the 64 discharge gates are `.last` with no `nxt` read. A `.last` thread
or an `.all` discharge would lower to `refuseConstraints` and this would be false. -/
theorem accSegAir_mainRailOk : accSegAir.mainRailOk = true := by native_decide

theorem accFinalAir_mainRailOk : accFinalAir.mainRailOk = true := by native_decide

/-- ⚑ **THE SELECTOR CENSUS.** 96 `.transition` threads and 64 `.last` discharge gates, and NONE at
`.all` or `.first`. The two families are byte-identical algebra under a different selector, so the
counts are what keep a re-scope visible: `.last → .all` on the discharge refuses every intermediate
row (a descriptor accepting nothing), `.transition → .all` on the thread accepts strictly more
(`TableAirIR.TableGate.transition_strictly_weaker`). Neither moves a constraint COUNT. -/
theorem the_discharge_is_sixty_four_last_row_gates :
    accFinalAir.windowCountSel RowSel.transition = 96
    ∧ accFinalAir.windowCountSel RowSel.last = 64
    ∧ accFinalAir.windowCountSel RowSel.all = 0
    ∧ accFinalAir.windowCountSel RowSel.first = 0
    ∧ accSegAir.windowCountSel RowSel.last = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- The emitted SEGMENT descriptor. -/
def accSegDesc : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir
    "dregg-mina-accumulator-seg::v1" RCB_WIDTH ACC_PI_COUNT [] accSegAir

/-- The emitted FINAL descriptor. -/
def accFinalDesc : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir
    "dregg-mina-accumulator-final::v1" RCB_WIDTH ACC_PI_COUNT [] accFinalAir

/-- `4 476` sound row-local constraints + `96` accumulator threads + `192` endpoint pins. -/
theorem accSegDesc_constraint_count : accSegDesc.constraints.length = 4476 + 96 + 192 := by native_decide

/-- …and the final segment is that plus the `64` discharge gates. -/
theorem accFinalDesc_constraint_count :
    accFinalDesc.constraints.length = 4476 + 96 + 192 + 64 := by native_decide

theorem accSegDesc_width : accSegDesc.traceWidth = 3048 := rfl
theorem accFinalDesc_width : accFinalDesc.traceWidth = 3048 := rfl
theorem accSegDesc_piCount : accSegDesc.piCount = 192 := rfl
theorem accFinalDesc_piCount : accFinalDesc.piCount = 192 := rfl

/-- ⚑ **A NAME IS A KEY.** The two descriptors are different objects and must not share one;
`reference-a-display-name-is-not-a-key` records three wrong lookups in one day from exactly this. -/
theorem the_two_descriptors_do_not_share_a_name : accSegDesc.name ≠ accFinalDesc.name := by native_decide

/-- ⚑ …and they differ in their CONSTRAINTS, not only in their names. A rename with no algebra
behind it is the shape that makes a registry lookup resolve to a look-alike. -/
theorem the_two_descriptors_differ : accSegDesc.constraints ≠ accFinalDesc.constraints := by
  intro h
  have := congrArg List.length h
  rw [accSegDesc_constraint_count, accFinalDesc_constraint_count] at this
  omega

/-! ## §4 — ⚑ THE GEOMETRY, AS NUMBERS RATHER THAN AS A WORRY.

Three facts, each measured on the emitted object, and the third is the one that says what is NOT
here. -/

/-- The deployed base-trace ceiling (`MAX_EXACT_PUBLIC_ROWS`, `circuit/src/descriptor_ir2.rs`). -/
def DREGG_MAX_ROWS : Nat := 2097152
/-- The deployed exact-public ARITY cap. ⚑ **READ FROM THE EMITTER, NOT TRANSCRIBED.** It was a
literal `64` here, and this file's own §4 is where the retraction that moved it was written; a
transcription would have gone on proving a dead fact one paragraph below its own refutation. -/
def MAX_EP_ARITY : Nat := Dregg2.Circuit.Emit.ExactPublicTableEmit.EP_MAX_ARITY
/-- The Step/Tick SRS width, `2^16`. -/
def STEP_SRS : Nat := 65536

/-- Rows a segment of `k` complete additions needs: one row each. -/
def segRows (k : Nat) : Nat := k

/-- Committed cells a `k`-row segment carries at this width. -/
def segCells (k : Nat) : Nat := k * 3048

/-- ⚑ **ONE INSTANCE CANNOT HOLD THE FULL-WIDTH SUM, AND THE FOLD IS WHY THAT IS NOT THE END.**
`PastaMsmBucketed.fused_at_step` prices the whole `2^16`-generator MSM at `1 474 800` complete
additions. At `3 048` columns that is `4.5 · 10⁹` committed cells — so the full-width chain is a
FOLD of segments, not one proof, and the recursion is load-bearing rather than an optimisation. -/
theorem the_full_width_sum_needs_the_fold :
    segCells 1474800 = 4495190400
    ∧ 1000 * DREGG_MAX_ROWS < segCells 1474800 := by
  refine ⟨by native_decide, by native_decide⟩

/-- ⚑ **THE ROUTING RESIDUAL — REFUSED AT HEAD, BUT THE CAP IS NOT A PRICE.**

Forcing the addend of row `r` to be a DECLARED SRS generator is an exact-public lookup whose tuple
is the generator index plus the point's limbs. In the sound encoding a projective point is
`3 · 32 = 96` limbs, so the tuple is `97` wide against the deployed `MAX_EXACT_PUBLIC_ARITY = 64`
(`circuit/src/descriptor_ir2.rs:531`), and `check_descriptor2` refuses it (`:2135`). **That refusal
is real and nothing should be designed as though it were not.**

⚠ **BUT THE EARLIER DRAFT OF THIS DOCBLOCK CALLED 64 A PRICE, AND IT IS NOT ONE.** Read at source
2026-08-06: the constant's ONLY other use is a drift guard whose own message says the remedy —
*"the emitted exact-public family covers {family_len} arities but this file admits
{MAX_EXACT_PUBLIC_ARITY}; re-emit `dregg-ir2-exact-public-v1.json` or re-pin the cap"*
(`descriptor_ir2.rs:6737-6742`). So 64 is **the number of members in a checked-in JSON artifact**,
pinned on both sides so the two cannot drift. It is exact as that, and it bounds no resource: the
committed object is `next_pow2(distinct) × (arity + 2)` preprocessed cells in ONE instance
(`ExactPublicManifest::of` at `:3370`, `prep_width` at `:3386`), and at `2^16` distinct generators
a 97-wide table is **6 488 064** cells — 26 MB, one instance.

⚑ It was introduced (`dc285da37`, 2026-07-22) under a comment justifying ROWS and CELLS — *"each row
becomes one batch instance, so bound the grammar before allocation"* — which is an argument about
instance count, and arity does not scale instance count. Its two siblings in that comment have since
moved by `2^14×` and `2^13×`; 64 has never been touched. `a-cost-verdict-outlives-its-premise`.

⚠ **AND THE REMEDY THIS DOCBLOCK USED TO PRESCRIBE IS THE MORE EXPENSIVE ONE** —
see `the_split_remedy_costs_more_than_the_wide_table`.

## ⚑⚑ CLOSED 2026-08-06 — THE CAP WAS RAISED AND THE TUPLE IS DECLARED

`EP_MAX_ARITY` went `64 → 97` (`ExactPublicTableEmit`, `descriptor_ir2.rs:591`), the family artifact
was re-emitted at `128 142` bytes, and `MAX_EXACT_PUBLIC_ARITY` was re-pinned on the Rust side. §8
now DECLARES the 97-wide tuple (`addendTable`) and §8b FORCES it
(`addend_is_its_declared_addend`). Neither the split remedy nor the wide-table cost estimate was
needed: the cap bounded a JSON member count, not a resource. -/
theorem the_routing_tuple_used_to_not_fit_and_now_does :
    64 < 1 + 3 * SK
    ∧ 1 + 3 * SK = 97
    ∧ 1 + 3 * SK ≤ MAX_EP_ARITY
    ∧ MAX_EP_ARITY = 1 + 3 * SK := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The preprocessed width an exact-public table of arity `a` commits: the table id, `a` value
columns, and the pinned multiplicity (`ExactPublicManifest::prep_width`, `descriptor_ir2.rs:3386`).
Written here so the comparison below is against the deployed geometry rather than against a guess. -/
def epPrepWidth (a : Nat) : Nat := a + 2

/-- ⚑⚑ **THE SPLIT REMEDY COSTS MORE THAN THE WIDE TABLE IT AVOIDS.**

This file used to prescribe `PastaMsmBucketed.split_srs_cells_fit`'s medicine — split the 96 limbs
across two tables keyed by the same index, `49 + 49`, clearing the arity cap. Over the same `2^16`
distinct generators that costs `2 · 2^16 · 51 = 6 684 672` preprocessed cells against the single
97-wide table's `2^16 · 99 = 6 488 064`: **196 608 cells MORE**, because each half pays its own
`table_id` and `multiplicity` column. It also costs a second batch instance, a second bus, a second
FRI opening set — and a soundness leg the wide table does not have, since **nothing forces the two
halves keyed by index `r` to name limbs of the SAME generator.**

⚠ And the citation was transplanted across two caps that share no mechanism: `split_srs_cells_fit`
is a theorem about `MAX_EXACT_PUBLIC_CELLS`, not about the ARITY cap this file is blocked by. -/
theorem the_split_remedy_costs_more_than_the_wide_table :
    STEP_SRS * epPrepWidth (1 + 3 * SK) = 6488064
    ∧ 2 * (STEP_SRS * epPrepWidth (1 + (3 * SK) / 2)) = 6684672
    ∧ STEP_SRS * epPrepWidth (1 + 3 * SK)
        < 2 * (STEP_SRS * epPrepWidth (1 + (3 * SK) / 2)) := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- The SRS the routing would have to cover, and the fact the fold's leaf count is set by the
segment height rather than by the generator count. -/
theorem the_step_srs_is_two_to_the_sixteen : STEP_SRS = 2 ^ 16 := by native_decide

/-! ### ⚑⚑ §4.1 — WHERE THE 3 048 COLUMNS GO, AND WHICH OF THEM CROSS A ROW BOUNDARY.

The fold's bill is paid in COLUMNS: `circuit-prove/tests/mina_accumulator_leaf_anatomy.rs` measures
the leaf wrap's in-circuit verifier at **2 878 067 ops** for this 3 048-column descriptor against
**248 555** for the 469-column `pasta-fq-chainlink::v1` that folds 46 leaves in production — and the
same measurement's ROW sweep moves the figure by **0.5% across 1 → 8 inner rows**. So the width is
the whole bill and the height is free, and the question this section answers is not "how big is the
row" but **"how much of the row is scratch that only exists because 33 SSA ops share one row."**

Every number below is `decide`d from the layout definitions the descriptor is emitted from — not a
second copy of them. -/

/-- The six INPUT blocks: `ACC_X/Y/Z ‖ ADD_X/Y/Z`, `SK` limbs each. -/
def censusInputs : Nat := 6 * SK
/-- The 33 SSA intermediates, `SK` limbs each (`vBase`). -/
def censusSSA : Nat := 33 * SK
/-- The 12 MULTIPLY witnesses: `SK` quotient limbs then `NG - 1` carries each (`mWit`). -/
def censusMul : Nat := 12 * (SK + (NG - 1))
/-- The 2 CONSTANT-MULTIPLY witnesses, `SK` columns each (`sWit`). -/
def censusSmul : Nat := 2 * SK
/-- The 19 ADD/SUB witnesses, `SK` columns each (`aWit`). -/
def censusAddSub : Nat := 19 * SK

/-- ⚑ **THE COLUMN CENSUS.** Five blocks, each named, summing to the width the descriptor declares.
A layout change that moved a stride would move one of these five numbers rather than only the total,
which is what makes this a census and not a restatement of `rcb_width_eq`. -/
theorem the_column_census :
    censusInputs = 192 ∧ censusSSA = 1056 ∧ censusMul = 1128 ∧ censusSmul = 64
    ∧ censusAddSub = 608
    ∧ censusInputs + censusSSA + censusMul + censusSmul + censusAddSub = RCB_WIDTH
    ∧ accSegDesc.traceWidth = RCB_WIDTH
    ∧ accFinalDesc.traceWidth = RCB_WIDTH := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, rfl, rfl⟩

/-- ⚑ **THE CARRIES ALONE ARE BETWEEN A FIFTH AND A QUARTER OF THE ROW.** `12 · (NG − 1) = 744`
columns exist only to carry a 256-bit schoolbook product's partial sums. Said separately from
`censusMul` because the quotient limbs and the carries are different work and a narrower encoding
moves them differently.

⚠ The bracket is two-sided on purpose. This theorem's first draft asserted `4 · 744 > RCB_WIDTH`
— "a quarter of the row" rounded UP — and the kernel refused it: `2 976 < 3 048`. A one-sided bound
on a fraction is exactly where a flattering round survives, so both sides are stated. -/
theorem the_multiply_carries_are_seven_hundred_forty_four :
    12 * (NG - 1) = 744
    ∧ 4 * (12 * (NG - 1)) < RCB_WIDTH
    ∧ 5 * (12 * (NG - 1)) > RCB_WIDTH := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- ⚑⚑ **ONLY 288 OF THE 3 048 COLUMNS CROSS A ROW BOUNDARY — THE OTHER 2 760 ARE SCRATCH.**

The six input blocks are read by the row's own gadget and by the 96 `.transition` threads; the three
output blocks `OUT_X/OUT_Y/OUT_Z` are pinned on `.last` and threaded forward. **Nothing else in the
row is visible outside it.** `9.4%` of the width is the row's interface and `90.6%` is intermediates
that exist because one complete addition is one row.

⚑ This is the number that says the narrowing is a LAYOUT change and not a soundness change: a row
carrying ONE SSA op instead of 33 does not have to hold the other 32 ops' scratch, and every
constraint `swCompleteAddSoundLegs` emits is a statement about a single op's operands and output.
`PastaLadderThread` made exactly this move one rail down — the row-local ladder was 731 136 columns
in one row before depth became rows — and the emitted width has been flat at `RCB_WIDTH` ever since,
which is precisely why the bill moved up a rail instead of going away. -/
theorem the_row_boundary_is_two_hundred_eighty_eight :
    censusInputs + 3 * SK = 288
    ∧ RCB_WIDTH - (censusInputs + 3 * SK) = 2760
    ∧ 10 * (censusInputs + 3 * SK) < RCB_WIDTH := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- …and the three output blocks live INSIDE the scratch region rather than in a reserved band, so
the `288` above counts distinct columns rather than a reserved prefix. `OUT_X/Y/Z` are `vBase`
slots 26 / 29 / 32 — the gadget's own SSA results, pinned where they land. -/
theorem the_outputs_are_scratch_slots :
    OUT_X = vBase IN_BASE 26 ∧ OUT_Y = vBase IN_BASE 29 ∧ OUT_Z = vBase IN_BASE 32
    ∧ IN_BASE ≤ OUT_X ∧ OUT_Z + SK ≤ RCB_WIDTH := by
  refine ⟨rfl, rfl, rfl, by native_decide, by native_decide⟩

/-! ## §5 — ⚑ THE VESTA TWIN OF THE THREADED INDUCTION.

`PastaLadderThread.threadedLadder_forces` is stated at the PALLAS base prime, because `row_forces`
consumes `pallasCompleteAddSound_forces`. The accumulator leg is Step/Tick on **Vesta**, so the
induction is re-run at `q` against `vestaCompleteAddSound_forces`. The proof body is the same three
moves — the row's own forcing, the thread's carry, and `rcbTraceZ_congr` transporting the induction
hypothesis through the RCB formula — because none of them mentions which prime. -/

/-- ⚑ **THE ROW'S DEPLOYED SATISFACTION AT `q`.** Field for field what
`vestaCompleteAddSound_forces` consumes, packaged so the induction quantifies over rows. -/
structure RowSoundV (tr : Trace) (r : Nat) : Prop where
  hX1 : Ranged (tr r) ACC_X
  hY1 : Ranged (tr r) ACC_Y
  hZ1 : Ranged (tr r) ACC_Z
  hX2 : Ranged (tr r) ADD_X
  hY2 : Ranged (tr r) ADD_Y
  hZ2 : Ranged (tr r) ADD_Z
  hv  : ∀ i, i < 33 → Ranged (tr r) (vBase IN_BASE i)
  hm  : ∀ k, k < 12 → MulWitRanged (tr r) (mWit IN_BASE k)
  hs  : ∀ k, k < 2 → SmulWitRanged (tr r) (sWit IN_BASE k)
  hb  : ∀ k, k < 19 → AddSubWitRanged (tr r) (aWit IN_BASE k)
  hG  : RcbSat (tr r) qLimb (curveB3 : ℤ) ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE

/-- One Vesta row, forced. -/
theorem rowV_forces (tr : Trace) (r : Nat) (hR : RowSoundV tr r) :
    CZ3 (qN : ℤ) (accOut tr r)
      (rcbOutZ (curveB3 : ℤ) (accIn tr r).1 (accIn tr r).2.1 (accIn tr r).2.2
        (addend tr r).1 (addend tr r).2.1 (addend tr r).2.2) :=
  vestaCompleteAddSound_forces (tr r) ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE
    hR.hX1 hR.hY1 hR.hZ1 hR.hX2 hR.hY2 hR.hZ2 hR.hv hR.hm hR.hs hR.hb hR.hG

/-- ⚑ **THE COMPOSITION THEOREM AT `q`.** `n` rows of DEPLOYED satisfaction plus `n` held threads
force the accumulator entering row `n` to be congruent — mod the real Vesta-base prime — to the
`n`-fold RCB chain of the addends the trace supplied. No row's output is quoted; each is forced. -/
theorem threadedLadderV_forces (tr : Trace) : ∀ n : Nat,
    (∀ r, r < n → RowSoundV tr r) → (∀ r, r < n → Threaded tr r) →
    CZ3 (qN : ℤ) (accIn tr n) (chainRef tr n)
  | 0, _, _ => CZ3.refl _
  | n + 1, hrow, hthread => by
      have ih : CZ3 (qN : ℤ) (accIn tr n) (chainRef tr n) :=
        threadedLadderV_forces tr n (fun r hr => hrow r (Nat.lt_succ_of_lt hr))
          (fun r hr => hthread r (Nat.lt_succ_of_lt hr))
      have hcarry : accIn tr (n + 1) = accOut tr n :=
        threaded_carries tr n (hthread n (Nat.lt_succ_self n))
      have hrowf := rowV_forces tr n (hrow n (Nat.lt_succ_self n))
      have hstep : CZ3 (qN : ℤ)
          (rcbOutZ (curveB3 : ℤ) (accIn tr n).1 (accIn tr n).2.1 (accIn tr n).2.2
            (addend tr n).1 (addend tr n).2.1 (addend tr n).2.2)
          (chainRef tr (n + 1)) :=
        rcbTraceZ_congr (curveB3 : ℤ) ih.1 ih.2.1 ih.2.2
          (CZm.refl _) (CZm.refl _) (CZm.refl _)
      rw [hcarry]
      exact CZ3.trans hrowf hstep

/-- ⚑ **THE TERMINAL OUTPUT IS THE WHOLE CHAIN.**

The last row of an `n+1`-row trace is where the discharge gates fire, and its `.transition` legs do
NOT fire (`when_transition` is every row BUT the last). So the statement has to reach the LAST ROW'S
OUTPUT, which `threadedLadderV_forces` alone does not: it stops at the accumulator entering row `n`.
One more application of the row's own forcing, transported through `rcbTraceZ_congr`, closes it —
and this is exactly the seam where an off-by-one would silently drop the final addend. -/
theorem terminalAccumulator_forces (tr : Trace) (n : Nat)
    (hrow : ∀ r, r ≤ n → RowSoundV tr r) (hthread : ∀ r, r < n → Threaded tr r) :
    CZ3 (qN : ℤ) (accOut tr n) (chainRef tr (n + 1)) := by
  have ih : CZ3 (qN : ℤ) (accIn tr n) (chainRef tr n) :=
    threadedLadderV_forces tr n (fun r hr => hrow r (Nat.le_of_lt hr)) hthread
  have hrowf := rowV_forces tr n (hrow n (Nat.le_refl n))
  exact CZ3.trans hrowf
    (rcbTraceZ_congr (curveB3 : ℤ) ih.1 ih.2.1 ih.2.2 (CZm.refl _) (CZm.refl _) (CZm.refl _))

/-! ## §6 — ⚑ THE DISCHARGE, FORCED. -/

/-- A block of `SK` limbs that are all zero recomposes to zero. This is the step that makes the
limbwise gate a statement about the VALUE, and it is the direction that needs no range hypothesis —
zero limbs recompose to zero whatever their declared width. -/
theorem sVal_eq_zero (a : Assignment) (b : Nat) (h : ∀ i, i < SK → a (b + i) = 0) :
    sVal a b = 0 := by
  unfold sVal Dregg2.Circuit.Emit.PastaFieldSound.sumL
  refine List.sum_eq_zero ?_
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [h i hi]
  ring

/-- ⚑ **THE DISCHARGE GATES, AS THE PROVER SATISFIES THEM.** The 64 `.last` window bodies vanish on
row `n` exactly when every limb of that row's `OUT_X` and `OUT_Z` blocks is zero. This is
`dischargeLegs`' body read as a fact about the trace. -/
def Discharged (tr : Trace) (n : Nat) : Prop :=
  (∀ i, i < SK → tr n (OUT_X + i) = 0) ∧ (∀ i, i < SK → tr n (OUT_Z + i) = 0)

/-- A satisfied discharge makes the terminal accumulator the CANONICAL point at infinity — the two
coordinates `pasta_msm::is_identity` reads, both exactly `0` rather than merely `≡ 0`. -/
theorem discharged_is_the_identity (tr : Trace) (n : Nat) (h : Discharged tr n) :
    (accOut tr n).1 = 0 ∧ (accOut tr n).2.2 = 0 :=
  ⟨sVal_eq_zero _ _ h.1, sVal_eq_zero _ _ h.2⟩

/-- ⚑⚑ **THE ACCUMULATOR CHECK, FORCED BY THE EMITTED CONSTRAINTS.**

`n+1` rows of deployed satisfaction, `n` held threads, and the 64 discharge gates force the
`n+1`-fold RCB chain of the trace's own addends — starting from the accumulator published at
`PI[0..95]` — to be the point at infinity mod the real Vesta-base prime.

Read against the relation this file exists for: with `acc_0 = C` and the addends the scaled
generators, this says `C − ⟨s(u⃗), G⟩ = O`, which is `Ipa.Step.accumulator_check`.

⚠ **IT SAYS NOTHING ABOUT WHAT THE ADDENDS ARE.** The limit is not softened: on THIS descriptor
(`-final`, which declares no manifest and emits no routing lookup) the chain is still the fold of
whatever `ADD_X/Y/Z` the trace supplies, and calling this the whole check would be the substitution
this repo keeps finding.

⚑ **WHAT CHANGED IS THAT A DESCRIPTOR EXISTS FOR WHICH THE STRONGER STATEMENT IS TRUE.** §8's
`dregg-mina-accumulator-routed::v1` routes the addends against a declared exact-public manifest and
`accumulator_discharge_forced_on_declared_addends` concludes over `declaredChain` — a fold in which
the trace's addend columns do not occur. `-final` is KEPT as the OLD-ADMITS pole of that pair: a
chain whose addends are honest Vesta points that are not this block's proves here and is refused
there. -/
theorem accumulator_discharge_forced (tr : Trace) (n : Nat)
    (hrow : ∀ r, r ≤ n → RowSoundV tr r) (hthread : ∀ r, r < n → Threaded tr r)
    (hd : Discharged tr n) :
    CZm (qN : ℤ) (chainRef tr (n + 1)).1 0
    ∧ CZm (qN : ℤ) (chainRef tr (n + 1)).2.2 0 := by
  have hterm := terminalAccumulator_forces tr n hrow hthread
  have hz := discharged_is_the_identity tr n hd
  refine ⟨?_, ?_⟩
  · have := CZm.symm hterm.1
    rw [hz.1] at this
    exact CZm.symm (CZm.symm this)
  · have := CZm.symm hterm.2.2
    rw [hz.2] at this
    exact CZm.symm (CZm.symm this)

/-! ### ⚠ THE NON-VACUITY OF `RowSoundV` IS WITNESSED BEHAVIOURALLY, NOT IN THIS KERNEL.

`accumulator_discharge_forced` would be vacuous if `RowSoundV` were unsatisfiable, and **nothing in
this file proves it is not**. What witnesses it is the deployed prover accepting the honest trace
under `dregg-mina-accumulator-final::v1` (`circuit/tests/mina_accumulator_air_proves.rs`, both
polarities, release) — behavioural evidence, one rail down, and `PastaLadderThread`'s
`threadedLadder_forces` has exactly the same status.

⚑ This is UNDONE WORK wearing a caveat, not a theorem of the model, so here is what it would cost.
A kernel witness means exhibiting one `Assignment` and discharging `RcbSat` on it — 33 SSA ops, 12
multiply witnesses at 32 quotient limbs and 62 carries each, all reduced at `q`. That is the
`decide`-through-a-real-field-element shape `minted-poseidon2-perm-is-a-reduction-bomb` measured at
47.6 GB for ONE permutation, so it is a `native_decide` + `#assert_compiled` job (a confession, not a
certificate) or a genuine satisfiability lemma over `rcbSoundRow` — which is the thing actually worth
building, because it would serve every descriptor in this cone rather than this one.

⚠ And the OTHER end is not closed either: these theorems speak the SOURCE vocabulary (`RcbSat`,
`Ranged`), and this file lowers with `lowerAir` rather than the certified `lowerTiedAir`, so the
`AirLeg.forces` bridge from the emitted constraints back to those predicates is inherited from
`PastaCurveSound`/`EffectLowerCertified` rather than re-established here. `lowerTiedAir` was not used
because `EffectAir.pinsTied` is a quadratic `decide` over ~4 000 legs against 192 pins; that is a
cost, and a cost is not a reason to call the weaker thing done.

## §7 — ⚑ AND THE LAST HYPOTHESIS IS DOING WORK.

A theorem whose final hypothesis were unsatisfiable, or satisfied by everything, would prove nothing
about the gate it is named for. Both directions are exhibited: a trace where `Discharged` HOLDS and
one where it FAILS, over assignments that agree everywhere the discharge does not look. -/

/-- The everywhere-zero trace: every limb of every block is `0`. -/
def zeroTrace : Trace := fun _ _ => 0

/-- The trace that is zero except for the terminal accumulator's low `X` limb. -/
def oneTrace : Trace := fun _ c => if c = OUT_X then 1 else 0

theorem zeroTrace_is_discharged (n : Nat) : Discharged zeroTrace n :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- ⚑ **THE REFUTATION.** `oneTrace` differs from `zeroTrace` in exactly ONE cell, that cell is
INSIDE the declared 8-bit limb width (so no range lookup can be what separates them), and the
discharge gate refuses it. A falsifier that moved a zero into a zero is the failure this exhibit is
built against: the moved value is `1`, and it is asserted to be nonzero. -/
theorem the_discharge_gate_is_refutable :
    ¬ Discharged oneTrace 0 ∧ oneTrace 0 OUT_X = 1 ∧ oneTrace 0 OUT_X ≠ zeroTrace 0 OUT_X := by
  refine ⟨?_, by decide, by decide⟩
  intro h
  have h0 := h.1 0 (by decide)
  simp [oneTrace] at h0

/-- …and the two exhibits agree on every cell the discharge does NOT read, so the refusal above is
about the gate and not about collateral damage. -/
theorem the_two_exhibits_differ_in_one_cell :
    ∀ c, c ≠ OUT_X → oneTrace 0 c = zeroTrace 0 c := by
  intro c hc
  simp only [oneTrace, zeroTrace, if_neg hc]

/-! ## §8 — ⚑⚑ THE ROUTING: THE ADDENDS ARE THE DESCRIPTOR'S, NOT THE PROVER'S.

§4 priced this and the price was retracted at source: `MAX_EXACT_PUBLIC_ARITY` is the member count
of a checked-in JSON artifact and bounds no resource. It went `64 → 97` on 2026-08-06
(`ExactPublicTableEmit.EP_MAX_ARITY`, `descriptor_ir2.rs:591`, the artifact re-emitted at
`128 142` bytes), so the 97-wide routing tuple this section needs is admissible and the section
exists.

**The mechanism, and it is the SAME one `PastaMsmBound` used one rail down.** A THREADED row-index
column, and ONE exact-public lookup per row whose tuple is `(row index + 1) ‖ the row's 96 addend
limbs`. `TableSem.exactPublicRows` is a PERMUTATION, not a containment
(`DescriptorIR2.PublicLookupBalanced`), so the declaration says *these addends and no others* — no
omission, no duplication, no substitution.

⚑ **WHAT THAT BUYS, EXACTLY.** `accumulator_discharge_forced` forces the chain of the TRACE'S OWN
addends to vanish. `accumulator_discharge_forced_on_declared_addends` forces the chain of the
DESCRIPTOR'S DECLARED addends to vanish — a statement in which the trace's addend columns do not
appear at all. The verifier REBUILDS the declared manifest from the descriptor bytes (it is a
preprocessed matrix, `ExactPublicManifest::preprocessed`), so those addends are VK-pinned, not
prover-supplied.

⚠ **AND WHAT IT DOES NOT BUY, said at the resolution it is at.** It moves the trust ONE OBJECT
OUT: from *"the addends the prover wrote"* to *"the addends this descriptor declares"*. Whether the
descriptor a node verified against is the one for the block in hand is a DESCRIPTOR-SELECTION
question, the same class as the accumulator's other two trusted items (§9), and it is not closed
here. What is closed is that a prover holding a fixed descriptor can no longer choose them.

⚑ **THE UNROUTED DESCRIPTOR IS KEPT, AND IT IS NOT COMPATIBILITY.** `-final` is the OLD-ADMITS pole
of the routing falsifier: a trace whose addends are honest points that are NOT this block's PROVES
under `-final` and is REFUSED under `-routed`. A pair that cannot rot into agreement is the whole
exhibit, exactly as `-seg`/`-final` is for the discharge. -/

/-- A projective point over ℕ — the shape a manifest row carries. -/
abbrev Pt3 : Type := Nat × Nat × Nat

/-- The `j`-th of a point's `3 · SK` limb cells, in `ADD_X ‖ ADD_Y ‖ ADD_Z` order — the SAME order
the trace's addend blocks sit in, which is why the tuple is one contiguous `List.range`. -/
def coordLimb (P : Pt3) (j : Nat) : Nat :=
  if j < SK then (P.1 / 2 ^ (Dregg2.Circuit.Emit.PastaFieldSound.SB * j))
                   % 2 ^ Dregg2.Circuit.Emit.PastaFieldSound.SB
  else if j < 2 * SK then (P.2.1 / 2 ^ (Dregg2.Circuit.Emit.PastaFieldSound.SB * (j - SK)))
                             % 2 ^ Dregg2.Circuit.Emit.PastaFieldSound.SB
  else (P.2.2 / 2 ^ (Dregg2.Circuit.Emit.PastaFieldSound.SB * (j - 2 * SK)))
         % 2 ^ Dregg2.Circuit.Emit.PastaFieldSound.SB

/-- ⚑ **THE ROW-INDEX COLUMN** — one column past the RCB row. It is the ONLY thing the routing adds
to the committed width: `3 048 → 3 049`, `+0.033%`. -/
def RIDX : Nat := RCB_WIDTH
/-- The routed descriptor's declared trace width. -/
def ROUTED_WIDTH : Nat := RCB_WIDTH + 1

theorem the_routing_costs_one_column :
    ROUTED_WIDTH = 3049 ∧ RIDX = 3048 ∧ ROUTED_WIDTH = RCB_WIDTH + 1 := by
  refine ⟨by native_decide, by native_decide, rfl⟩

/-- The row index starts at zero. `.first` lowers to a `VmConstraint.boundary`, whose body reads
`env.loc` alone — which is why the body may not mention `nxt`. -/
def ridxStartLeg : AirLeg := .window ⟨RowSel.first, WindowExpr.loc RIDX⟩

/-- …and advances by exactly one. `.transition` is the only selector under which `nxt` is the
genuine successor; under `.all` the last row's `nxt` is p3's WRAP row and this would say something
else exactly where padding hides. -/
def ridxThreadLeg : AirLeg :=
  .window ⟨RowSel.transition,
    WindowExpr.add (.nxt RIDX) (.mul (.const (-1)) (.add (.loc RIDX) (.const 1)))⟩

/-- The routing tuple's width: the key plus a projective point's `3 · 32` limbs. ⚑ This is the `97`
`the_routing_tuple_does_not_fit_one_table` priced, and it is now what the emitted object declares
rather than what it is blocked by. -/
def ADDEND_TUP : Nat := 1 + 3 * SK

theorem the_declared_tuple_is_the_priced_one : ADDEND_TUP = 97 ∧ ADDEND_TUP = 1 + 3 * SK := by
  refine ⟨by native_decide, rfl⟩

/-- The addend manifest's wire id. ⚑ `.custom 128 ⇒ wireId 133`: clear of `main` and of the three
`rangeTidW` tables this row already declares (`.custom (64 + bits)`, `bits ≤ 16 ⇒ at most
.custom 80`), and far above the reserved ids the deployed parser refuses (`≤ TID_P2_STATE16 = 9`).
`routedTables_ids_are_distinct` is the check; `reference-a-display-name-is-not-a-key`. -/
def ADDEND_TID : Dregg2.Circuit.DescriptorIR2.TableId := .custom 128

/-- ⚑ **THE QUERIED TUPLE.** The key is `RIDX + 1`, never `RIDX`: a manifest whose live key space
includes `0` cannot be distinguished from an all-zero tuple, which is the trap `PastaMsmBound` and
`MinaWrapVerifierProgram` both document and avoid the same way. The 96 limb cells are `ADD_X + j`
for `j < 3·SK`, which is contiguous exactly because `ADD_X/ADD_Y/ADD_Z = 3·SK/4·SK/5·SK`. -/
def addendTuple : List Dregg2.Circuit.Expr :=
  Dregg2.Circuit.Expr.add (.var RIDX) (.const 1)
    :: (List.range (3 * SK)).map (fun j => Dregg2.Circuit.Expr.var (ADD_X + j))

theorem addendTuple_length : addendTuple.length = ADDEND_TUP := by native_decide

/-- ⚑ **THE ONE LOOKUP.** `.query` at multiplicity 1 — the only shape `Ir2Air::Main` implements, and
`LookupLeg.mainRailOk` REFUSES anything else rather than lowering a leg the deployed rail cannot
serve. -/
def addendLookupLeg : AirLeg :=
  .lookup { table := ADDEND_TID, tuple := addendTuple, mult := .const 1, op := .query }

/-- The manifest row for INDEX `i`: the key, then the declared addend's 96 limbs. -/
def addendRow (As : List Pt3) (i : Nat) : List Nat :=
  (i + 1) :: (List.range (3 * SK)).map (coordLimb (As.getD i (0, 0, 0)))

/-- ⚑ **THE DECLARED ADDENDS**, one manifest row per trace row. Its LENGTH is the trace height —
forced, not assumed, because the exact-public semantics is a PERMUTATION
(`the_balance_forces_the_row_count`). -/
def addendManifest (As : List Pt3) : List (List Nat) :=
  (List.range As.length).map (addendRow As)

/-- The declared table. -/
def addendTable (As : List Pt3) : Dregg2.Circuit.DescriptorIR2.TableDef :=
  ⟨ADDEND_TID, "mina_accumulator_addends", ADDEND_TUP, .exactPublicRows (addendManifest As)⟩

/-- The routed block's tables: the RCB row's four with the MAIN table re-declared at the widened
trace width, plus the addend manifest. -/
def routedTables (As : List Pt3) : List Dregg2.Circuit.DescriptorIR2.TableDef :=
  Dregg2.Circuit.DescriptorIR2.mainTableDef ROUTED_WIDTH
    :: (rcbTables.drop 1 ++ [addendTable As])

/-- ⚑ **THE FIVE TABLE IDS ARE DISTINCT**, so the addend manifest gets its own LogUp bus and cannot
pool with the three range tables. A collision here would make the routing balance against a range
table's rows, which is a refusal nobody would read as a routing failure. -/
theorem routedTables_ids_are_distinct (As : List Pt3) :
    ((routedTables As).map (·.id)).dedup.length = 5
    ∧ (routedTables As).length = 5 := by
  have hid : (routedTables As).map (·.id) = (routedTables []).map (·.id) := rfl
  have hlen : (routedTables As).length = (routedTables []).length := rfl
  rw [hid, hlen]
  refine ⟨by decide, by decide⟩

/-- **THE ROUTED BLOCK.** `accFinalAir`'s legs verbatim — the sound Vesta row, the 96 threads, the
192 endpoint pins, the 64 discharge gates — plus the index origin, the index thread and the one
lookup. Nothing is re-authored. -/
def accRoutedAir : EffectAir :=
  { tables := routedTables []
  , legs := accFinalAir.legs ++ [ridxStartLeg, ridxThreadLeg, addendLookupLeg] }

/-- …and the same block over a DECLARED addend list. The legs do not depend on it; only the manifest
does, which is what makes the descriptor per-block and the ALGEBRA fixed. -/
def accRoutedAirOn (As : List Pt3) : EffectAir :=
  { accRoutedAir with tables := routedTables As }

/-- ⚑ **THE FINAL BLOCK'S LEGS ARE A PREFIX OF THE ROUTED ONE'S.** Every forcing statement in §5–§7
applies to the routed descriptor unchanged — the routing APPENDS. -/
theorem accRoutedAir_extends_accFinalAir (As : List Pt3) :
    accFinalAir.legs <+: (accRoutedAirOn As).legs :=
  ⟨[ridxStartLeg, ridxThreadLeg, addendLookupLeg], rfl⟩

/-- ⚑ **THE DECLARED MANIFEST TOUCHES NOTHING BUT THE MANIFEST.** The legs — and therefore every
emitted constraint, every selector count and the whole algebra — are the SAME object at every `As`.
This is what makes `-routed` one AIR with a per-block preprocessed matrix rather than a new circuit
per block, and it is what lets every shape theorem below be `decide`d at one instance. -/
theorem the_legs_do_not_depend_on_the_declared_addends (As : List Pt3) :
    (accRoutedAirOn As).legs = accRoutedAir.legs := rfl

/-- ⚑ **THE COMPILER ACCEPTS THE ROUTED BLOCK.** The index origin is `.first` with no `nxt` read,
the index thread is `.transition`, and the lookup is a `.query` at multiplicity 1. A `.all` origin,
a `.first` thread or a `.provide` lookup each lower to `refuseConstraints` and this would be false. -/
theorem accRoutedAir_mainRailOk (As : List Pt3) : (accRoutedAirOn As).mainRailOk = true := by
  show accRoutedAir.mainRailOk = true
  native_decide

/-- ⚑ **THE ROUTED BLOCK, EMITTED UNDER A GIVEN NAME.** The name is a parameter because §10 emits a
SECOND descriptor over the SAME algebra and a DERIVED manifest, and `reference-a-display-name-is-not-
a-key` is why it may not reuse this one's. Nothing but `.name` depends on it — which is exactly what
`the_srs_descriptor_differs_from_the_routed_one_only_in_its_name_and_its_manifest` states, and what
makes `srs_balance_is_routed_balance` an `Iff.rfl`. -/
def accRoutedDescNamed (nm : String) (As : List Pt3) : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir nm ROUTED_WIDTH ACC_PI_COUNT [] (accRoutedAirOn As)

/-- The emitted ROUTED descriptor. -/
def accRoutedDesc (As : List Pt3) : EffectVmDescriptor2 :=
  accRoutedDescNamed "dregg-mina-accumulator-routed::v1" As

/-- The emitted constraints are the same list at every `As` — the corollary of
`the_legs_do_not_depend_on_the_declared_addends` that the shape pins are stated through. -/
theorem accRoutedDesc_constraints_eq (As : List Pt3) :
    (accRoutedDesc As).constraints = (accRoutedDesc []).constraints := rfl

theorem accRoutedDesc_name (As : List Pt3) :
    (accRoutedDesc As).name = "dregg-mina-accumulator-routed::v1" := rfl

/-- `4 476 + 96 + 192 + 64` from `-final`, plus the index origin, the index thread and the lookup. -/
theorem accRoutedDesc_constraint_count (As : List Pt3) :
    (accRoutedDesc As).constraints.length = 4476 + 96 + 192 + 64 + 3 := by
  rw [accRoutedDesc_constraints_eq]; native_decide

theorem accRoutedDesc_width (As : List Pt3) : (accRoutedDesc As).traceWidth = 3049 := rfl
theorem accRoutedDesc_piCount (As : List Pt3) : (accRoutedDesc As).piCount = 192 := rfl

/-- ⚑ **THREE NAMES, THREE OBJECTS.** A registry lookup that resolved `-routed` to `-final` would
serve a descriptor with no routing at all and every shape pin would still pass. -/
theorem the_three_descriptors_do_not_share_a_name (As : List Pt3) :
    accSegDesc.name ≠ accFinalDesc.name
    ∧ accFinalDesc.name ≠ (accRoutedDesc As).name
    ∧ accSegDesc.name ≠ (accRoutedDesc As).name := by
  rw [accRoutedDesc_name]
  refine ⟨by decide, by decide, by decide⟩

/-- ⚑ **THE SELECTOR CENSUS, ROUTED.** One more `.transition` (the index thread) and the file's
FIRST `.first` gate (the index origin); the 64 `.last` discharge gates and the 96 accumulator
threads are untouched. A `.first → .all` re-scope on the origin would pin EVERY row's index to zero
— a descriptor accepting only one-row traces — and it moves this number. -/
theorem the_routed_selector_census (As : List Pt3) :
    (accRoutedAirOn As).windowCountSel RowSel.transition = 97
    ∧ (accRoutedAirOn As).windowCountSel RowSel.last = 64
    ∧ (accRoutedAirOn As).windowCountSel RowSel.first = 1
    ∧ (accRoutedAirOn As).windowCountSel RowSel.all = 0
    ∧ (accRoutedAirOn As).lookupCount = 1 := by
  show accRoutedAir.windowCountSel RowSel.transition = 97
    ∧ accRoutedAir.windowCountSel RowSel.last = 64
    ∧ accRoutedAir.windowCountSel RowSel.first = 1
    ∧ accRoutedAir.windowCountSel RowSel.all = 0
    ∧ accRoutedAir.lookupCount = 1
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩


/-! ### §8a — THE DEMONSTRATION'S DECLARED ADDENDS.

⚠ These are a PARAMETER CHOICE, not AIR: `accRoutedDesc` is stated over an arbitrary `As` and every
theorem in §8b–§8d quantifies over it. What lives here is the ONE list the checked-in artifact and
the checked-in trace fixtures both derive from, so the descriptor's manifest and the trace's addend
columns cannot drift apart the way two transcriptions would. -/

/-- The Vesta generator, projective. -/
def Gv3 : Pt3 := (Dregg2.Circuit.Emit.PastaCurve.Gv.1, Dregg2.Circuit.Emit.PastaCurve.Gv.2, 1)

/-- `−P = (X : −Y : Z)`, reduced at the Vesta base prime. The additive inverse a complete addition
sends to `O`. -/
def negV (P : Pt3) : Pt3 := (P.1, (qN - P.2.1 % qN) % qN, P.2.2)

/-- The accumulator after `k` additions of `Q`, by the same complete formula the row computes. -/
def walkV (Q : Pt3) : Pt3 → Nat → Pt3
  | P, 0 => P
  | P, (k + 1) =>
      walkV Q (Dregg2.Circuit.Emit.PastaCurveComplete.rcbAddM qN curveB3 P Q) k

/-- ⚑ **THE DEMONSTRATION'S DECLARED ADDENDS** — seven generator adds, then the negation of the
running accumulator, which is what closes the chain at the point at infinity. Eight rows: a power of
two, which the deployed prover requires of a base trace. -/
def demoAddends : List Pt3 :=
  List.replicate 7 Gv3 ++ [negV (walkV Gv3 Gv3 7)]

/-- The emitted ROUTED descriptor at the demonstration's manifest — the checked-in artifact. -/
def accRoutedDemoDesc : EffectVmDescriptor2 := accRoutedDesc demoAddends

/-! ### §8b — ⚑⚑ THE ROUTING, FORCED.

Three moves, and none of them is new: the index column is threaded (the shape §5 uses for the
accumulator), the balance is read against `DescriptorIR2.PublicLookupBalanced` (the IR's OWN
exact-public denotation), and the key pins the row (`PastaMsmBound.row_tuple_is_its_manifest_row`,
one rail down, minus the doubling-row case this chain does not have). -/

open Dregg2.Circuit.DescriptorIR2 (VmTrace zeroAsg lookupLog exactPublicTable PublicLookupBalanced)
open Dregg2.Circuit.Emit.EffectLower (lowerAirLegs lowerLeg)

/-- The row index starts at zero — `ridxStartLeg`'s body read as a fact about the trace. -/
def IdxStarted (tr : Trace) : Prop := tr 0 RIDX = 0

/-- …and advances by exactly one — `ridxThreadLeg`'s body read as a fact about the trace. -/
def IdxThreaded (tr : Trace) (r : Nat) : Prop := tr (r + 1) RIDX = tr r RIDX + 1

/-- ⚑ **THE INDEX COLUMN IS THE ROW'S OWN INDEX.** The emitted origin plus the emitted thread, for
every row below the height. `H` is universally quantified and occurs only as the induction bound:
the statement at `H = 8` is the statement at `H = 65 536`. -/
theorem ridx_is_the_row_index (tr : Trace) (H : Nat)
    (h0 : IdxStarted tr) (h : ∀ r, r + 1 < H → IdxThreaded tr r) :
    ∀ i, i < H → tr i RIDX = (i : ℤ) := by
  intro i
  induction i with
  | zero => intro _; simpa using h0
  | succ m ih =>
    intro hm
    have hstep : tr (m + 1) RIDX = tr m RIDX + 1 := h m hm
    rw [hstep, ih (by omega)]
    push_cast
    ring

/-- Trace row `j`, with the deployed off-the-end default. -/
def rowAt (t : VmTrace) (j : Nat) : Assignment := t.rows.getD j zeroAsg

/-- ⚑ A `VmTrace` READ AS A `Trace`. Not a bridge, an identity: the two views are the same function,
so every §5–§7 theorem applies to a `VmTrace` verbatim and no hypothesis relates them. -/
def traceOf (t : VmTrace) : Trace := rowAt t

theorem traceOf_apply (t : VmTrace) (j : Nat) : traceOf t j = rowAt t j := rfl

/-- Trace row `j` is a row of the trace. -/
theorem rowAt_mem (t : VmTrace) (j : Nat) (hj : j < t.rows.length) : rowAt t j ∈ t.rows := by
  have : rowAt t j = t.rows[j] := by simp [rowAt, List.getD, List.getElem?_eq_getElem hj]
  rw [this]
  exact List.getElem_mem hj

/-- The emitted routing tuple, evaluated on a row. -/
def addTupleOf (a : Assignment) : List ℤ :=
  (addendTuple.map Dregg2.Exec.CircuitEmit.emitExpr).map
    (fun e => Dregg2.Exec.CircuitEmit.EmittedExpr.eval e a)

/-- The tuple in explicit form: the key, then the row's own 96 addend cells. -/
theorem addTupleOf_cons (a : Assignment) :
    addTupleOf a = (a RIDX + 1) :: (List.range (3 * SK)).map (fun j => a (ADD_X + j)) := by
  simp [addTupleOf, addendTuple, Dregg2.Exec.CircuitEmit.emitExpr,
    Dregg2.Exec.CircuitEmit.EmittedExpr.eval, List.map_map, Function.comp_def]

theorem addTupleOf_head (a : Assignment) : (addTupleOf a).head? = some (a RIDX + 1) := by
  rw [addTupleOf_cons]; rfl

/-- The manifest row's KEY. ⚑ It is `i + 1`, never `i`: a live key space containing `0` cannot be
told from an all-zero tuple, the trap `PastaMsmBound` and `MinaWrapVerifierProgram` both avoid. -/
theorem addendRow_head (As : List Pt3) (i : Nat) : (addendRow As i).head? = some (i + 1) := rfl

/-- …and the same key in the INTEGER denotation the lookup log speaks. -/
theorem addendRow_map_head (As : List Pt3) (i : Nat) :
    ((addendRow As i).map Int.ofNat).head? = some (((i + 1 : Nat) : ℤ)) := rfl

/-- ⚑ **TWO MANIFEST ROWS WITH THE SAME KEY ARE THE SAME ROW** — what turns a multiset membership
into a POINTWISE statement. Proved from the manifest's `def`, so it holds at every declared length
rather than at the demonstration's. -/
theorem addend_manifest_key_unique (As : List Pt3) {r s : List Nat}
    (hr : r ∈ addendManifest As) (hs : s ∈ addendManifest As)
    (hk : r.head? = s.head?) : r = s := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs
  rw [addendRow_head, addendRow_head] at hk
  have hij : i = j := by simpa using hk
  rw [hij]

/-- A constraint that is not a lookup AT THE ADDEND TABLE. -/
def notAddendLookup : VmConstraint2 → Bool
  | .lookup l => !(l.table == ADDEND_TID)
  | _         => true

/-- ⚑ **ONLY THE ROUTING LEG TARGETS THE ADDEND TABLE.** This is a real check and not a restatement
of "there is one lookup leg": the row's six `AirLeg.limbs` legs lower to 192 `.lookup` constraints
of their own, at the three `rangeTidW` tables. A second lookup reaching this table would make the
log below a `flatMap` of PAIRS and every pointwise conclusion false. -/
theorem only_the_routing_leg_targets_the_addend_table :
    accFinalDesc.constraints.all notAddendLookup = true := by native_decide

/-- A bare-AIR descriptor's constraints are its legs, lowered — stated over a VARIABLE `air`, so
the kernel checks the `[] ++ _ ++ []` steps once, on a variable, and never on a concrete leg list
(on `accFinalAir` it unfolded and compared all 4,800 lowered constraints: 92 s of kernel time). -/
theorem lowerAir_constraints (nm : String) (w p : Nat) (air : EffectAir) :
    (Dregg2.Circuit.Emit.EffectLower.lowerAir nm w p [] air).constraints
      = air.legs.flatMap lowerLeg := by
  simp only [Dregg2.Circuit.Emit.EffectLower.lowerAir, Dregg2.Circuit.Emit.EffectLower.assemble,
    Dregg2.Circuit.Emit.EffectLower.lowerAirLegs, List.map_nil, List.nil_append, List.append_nil]

/-- The routed block's legs are the final block's, then the three routing legs. -/
theorem accRoutedAir_legs :
    accRoutedAir.legs = accFinalAir.legs ++ [ridxStartLeg, ridxThreadLeg, addendLookupLeg] := by
  rw [accRoutedAir]

/-- The routed descriptor's constraints are the final descriptor's, then the three routing ones. -/
theorem routed_constraints_split (As : List Pt3) :
    (accRoutedDesc As).constraints
      = accFinalDesc.constraints
          ++ [ridxStartLeg, ridxThreadLeg, addendLookupLeg].flatMap lowerLeg := by
  unfold accRoutedDesc accRoutedDescNamed accFinalDesc
  rw [lowerAir_constraints, lowerAir_constraints, the_legs_do_not_depend_on_the_declared_addends,
    accRoutedAir_legs, List.flatMap_append]

/-- A `flatMap` of singletons IS a `map`. -/
theorem flatMap_singleton_map {α β : Type} (f : α → List β) (g : α → β) (l : List α)
    (h : ∀ x, f x = [g x]) : l.flatMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons _ rest ih => simp [h, ih]

/-- A constraint list with no addend lookup contributes nothing to the addend log. Stated over an
ABSTRACT `f` so it applies to `lookupLog`'s own anonymous matcher. -/
theorem filterMap_of_noAddendLookup {β : Type} (f : VmConstraint2 → Option β)
    (l : List VmConstraint2) (hnl : ∀ c, notAddendLookup c = true → f c = none)
    (h : l.all notAddendLookup = true) : l.filterMap f = [] := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [hnl a h.1, ih h.2]

/-- The three routing constraints contribute EXACTLY the row's own tuple to the addend log: the two
index legs are a boundary and a window (neither is a lookup), and the routing leg lowers to one
`.lookup` at `ADDEND_TID` whose evaluated tuple IS `addTupleOf`. -/
theorem routing_leg_filterMap (row : Assignment) :
    (([ridxStartLeg, ridxThreadLeg, addendLookupLeg].flatMap lowerLeg).filterMap
      (fun c => match c with
        | .lookup l => if l.table = ADDEND_TID then some (l.tuple.map (·.eval row)) else none
        | _ => none))
      = [addTupleOf row] := rfl

/-- ⚑ **THE ADDEND LOG IS THE PER-ROW TUPLE MAP.** Exactly one emitted lookup targets the addend
table, it fires on every row, and the 192 range lookups are filtered out by table id. -/
theorem addend_lookupLog_is_rowMap (As : List Pt3) (t : VmTrace) :
    lookupLog (accRoutedDesc As) t ADDEND_TID = t.rows.map addTupleOf := by
  unfold lookupLog
  refine flatMap_singleton_map _ addTupleOf t.rows (fun row => ?_)
  rw [routed_constraints_split As, List.filterMap_append,
    filterMap_of_noAddendLookup _ accFinalDesc.constraints
      (fun c hc => by cases c <;> simp_all [notAddendLookup])
      only_the_routing_leg_targets_the_addend_table]
  exact routing_leg_filterMap row

/-- The exact-public balance the declaration demands, unfolded at THIS table. -/
theorem addend_balance (As : List Pt3) (t : VmTrace)
    (hbal : PublicLookupBalanced (accRoutedDesc As) t) :
    (t.rows.map addTupleOf).Perm (exactPublicTable (addendManifest As)) := by
  have hmem : addendTable As ∈ (accRoutedDesc As).tables := by
    show addendTable As ∈ routedTables As
    simp [routedTables]
  have h := hbal (addendTable As) hmem
  simpa [addendTable, ← addend_lookupLog_is_rowMap As t] using h

/-- ⚑ **THE BALANCE FORCES THE ROW COUNT** — the trace has exactly as many rows as the descriptor
declares addends. `exactPublicRows` is a PERMUTATION, so this is not assumed anywhere below: a
prover cannot pad the chain with unrouted rows, and cannot drop a declared addend either. -/
theorem the_balance_forces_the_row_count (As : List Pt3) (t : VmTrace)
    (hbal : PublicLookupBalanced (accRoutedDesc As) t) : t.rows.length = As.length := by
  have h := (addend_balance As t hbal).length_eq
  simpa [exactPublicTable, addendManifest] using h

/-- ⚑⚑ **THE DELIVERABLE — ROW `i`'S TUPLE IS THE MANIFEST'S ROW `i`.**

On a trace whose emitted routing lookup balances against the emitted manifest and whose index column
is the threaded row index, row `i`'s addend cells ARE the descriptor's declared addend `i`. `i` and
`As.length` are universally quantified and occur in no bound: the statement at eight rows is the
statement at `2^16`.

⚠ The argument is pure MEMBERSHIP — no counting, no pigeonhole. The manifest's row `i` is IN the
manifest, so by the permutation it is SOME trace row's tuple; the key `RIDX + 1` plus
`addend_manifest_key_unique` pins that row to be row `i`. -/
theorem addend_is_its_declared_addend (As : List Pt3) (t : VmTrace) (i : Nat)
    (hbal : PublicLookupBalanced (accRoutedDesc As) t)
    (hridx : ∀ j, j < t.rows.length → rowAt t j RIDX = (j : ℤ))
    (hi : i < As.length) :
    addTupleOf (rowAt t i) = (addendRow As i).map Int.ofNat := by
  have hperm := addend_balance As t hbal
  have hlen : t.rows.length = As.length := the_balance_forces_the_row_count As t hbal
  have hmiM : addendRow As i ∈ addendManifest As :=
    List.mem_map_of_mem (List.mem_range.mpr hi)
  have hmiL : (addendRow As i).map Int.ofNat ∈ t.rows.map addTupleOf :=
    hperm.mem_iff.mpr (List.mem_map_of_mem hmiM)
  obtain ⟨r, hr, hrEq⟩ := List.mem_map.mp hmiL
  obtain ⟨j, hj, hjr⟩ : ∃ j, j < t.rows.length ∧ rowAt t j = r := by
    obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hr
    exact ⟨j, hj, by simp [rowAt, List.getD, List.getElem?_eq_getElem hj, hje]⟩
  have hkey : some (((i + 1 : Nat) : ℤ)) = some ((j : ℤ) + 1) := by
    have h1 : (addTupleOf (rowAt t j)).head? = some (rowAt t j RIDX + 1) := addTupleOf_head _
    have hrj : rowAt t j RIDX = (j : ℤ) := hridx j hj
    rw [hjr, hrEq, ← hjr, hrj, addendRow_map_head] at h1
    exact h1
  have hji : j = i := by
    have hz : (i : ℤ) = (j : ℤ) := by
      have := Option.some.inj hkey
      push_cast at this
      linarith
    exact_mod_cast hz.symm
  rw [← hjr, hji] at hrEq
  exact hrEq

/-! ### §8c — from the tuple to the VALUE the chain folds. -/

/-- Two `map`s over the same `List.range` agree pointwise. -/
theorem range_map_pointwise {α : Type} (n : Nat) (f g : Nat → α)
    (h : (List.range n).map f = (List.range n).map g) : ∀ i, i < n → f i = g i := by
  intro i hi
  have hlt : i < ((List.range n).map f).length := by simp [hi]
  have h2 := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_range hi] at h2
  simpa using h2

/-- ⚑ **AND LIMBWISE.** Row `i`'s addend CELL `ADD_X + j` is the declared point's `j`-th limb — the
form the chain's `sVal` reads, rather than a statement about a tuple. -/
theorem addend_limbs_are_declared (As : List Pt3) (t : VmTrace) (i : Nat)
    (hbal : PublicLookupBalanced (accRoutedDesc As) t)
    (hridx : ∀ j, j < t.rows.length → rowAt t j RIDX = (j : ℤ))
    (hi : i < As.length) :
    ∀ j, j < 3 * SK →
      rowAt t i (ADD_X + j) = ((coordLimb (As.getD i (0, 0, 0)) j : Nat) : ℤ) := by
  have h := addend_is_its_declared_addend As t i hbal hridx hi
  rw [addTupleOf_cons, addendRow] at h
  simp only [List.map_cons, List.map_map, Function.comp_def] at h
  have htail := (List.cons.inj h).2
  exact range_map_pointwise (3 * SK) _ _ htail

/-- Pointwise congruence for the limb sum `sVal` is built from. -/
theorem sumL_congr {α : Type} (l : List α) (f g : α → ℤ) (h : ∀ x ∈ l, f x = g x) :
    Dregg2.Circuit.Emit.PastaFieldSound.sumL l f
      = Dregg2.Circuit.Emit.PastaFieldSound.sumL l g := by
  unfold Dregg2.Circuit.Emit.PastaFieldSound.sumL
  exact congrArg List.sum (List.map_congr_left h)

/-- The DECLARED coordinate value at limb OFFSET `off`: the recomposition of the declared point's
limbs, in exactly the form `sVal` computes on the row. The three coordinates sit at offsets
`0 / SK / 2·SK`, which is the same layout the row's `ADD_X/ADD_Y/ADD_Z` blocks sit in. -/
def declVal (P : Pt3) (off : Nat) : ℤ :=
  Dregg2.Circuit.Emit.PastaFieldSound.sumL (List.range SK)
    (fun i => ((2 : ℤ) ^ Dregg2.Circuit.Emit.PastaFieldSound.SB) ^ i
                * ((coordLimb P (off + i) : Nat) : ℤ))

/-- The declared addend of index `r`, as the projective triple the chain folds. -/
def declAddend (As : List Pt3) (r : Nat) : ℤ × ℤ × ℤ :=
  (declVal (As.getD r (0, 0, 0)) 0, declVal (As.getD r (0, 0, 0)) SK,
   declVal (As.getD r (0, 0, 0)) (2 * SK))

/-- One coordinate: a block whose every cell is the declared limb recomposes to the declared value.
⚠ No range hypothesis and no bound on the coordinate is needed — this is an identity between two
sums over the SAME limb cells, not a claim that the recomposition is the point's integer. -/
theorem sVal_is_declVal (P : Pt3) (a : Assignment) (base off : Nat)
    (hb : base = ADD_X + off) (hoff : off + SK ≤ 3 * SK)
    (h : ∀ j, j < 3 * SK → a (ADD_X + j) = ((coordLimb P j : Nat) : ℤ)) :
    sVal a base = declVal P off := by
  subst hb
  unfold sVal declVal
  refine sumL_congr _ _ _ (fun x hx => ?_)
  have hxr : x < SK := List.mem_range.mp hx
  rw [show ADD_X + off + x = ADD_X + (off + x) from by omega, h (off + x) (by omega)]

/-- ⚑⚑ **THE ROW'S ADDEND VALUE IS THE DECLARED ONE** — the three `sVal`s `chainRef` reads are the
three declared recompositions. This is the rung that carries the routing out of the lookup tuple and
into the chain's own vocabulary. -/
theorem addend_value_is_declared (As : List Pt3) (t : VmTrace) (i : Nat)
    (hbal : PublicLookupBalanced (accRoutedDesc As) t)
    (hridx : ∀ j, j < t.rows.length → rowAt t j RIDX = (j : ℤ))
    (hi : i < As.length) :
    addend (traceOf t) i = declAddend As i := by
  have hl := addend_limbs_are_declared As t i hbal hridx hi
  have e0 : sVal (rowAt t i) ADD_X = declVal (As.getD i (0, 0, 0)) 0 :=
    sVal_is_declVal _ _ ADD_X 0 rfl (by decide) hl
  have e1 : sVal (rowAt t i) ADD_Y = declVal (As.getD i (0, 0, 0)) SK :=
    sVal_is_declVal _ _ ADD_Y SK rfl (by decide) hl
  have e2 : sVal (rowAt t i) ADD_Z = declVal (As.getD i (0, 0, 0)) (2 * SK) :=
    sVal_is_declVal _ _ ADD_Z (2 * SK) rfl (by decide) hl
  show (sVal (rowAt t i) ADD_X, sVal (rowAt t i) ADD_Y, sVal (rowAt t i) ADD_Z) = _
  rw [e0, e1, e2]
  rfl

/-! ### §8d — ⚑⚑ THE STRENGTHENED DISCHARGE. -/

/-- ⚑ **THE DECLARED CHAIN** — the RCB fold over the addends the DESCRIPTOR declares, from the
accumulator the trace carries into row 0 (which is the published `PI[0..95]`). ⚠ The trace's addend
columns do not occur in this definition at all; that absence is the point. -/
def declaredChain (As : List Pt3) (tr : Trace) : Nat → ℤ × ℤ × ℤ
  | 0 => accIn tr 0
  | n + 1 =>
      let P := declaredChain As tr n
      rcbOutZ (curveB3 : ℤ) P.1 P.2.1 P.2.2
        (declAddend As n).1 (declAddend As n).2.1 (declAddend As n).2.2

/-- The trace's chain IS the declared chain, once every addend is routed. -/
theorem chain_is_the_declared_chain (As : List Pt3) (t : VmTrace) (m : Nat)
    (hm : ∀ r, r < m → addend (traceOf t) r = declAddend As r) :
    chainRef (traceOf t) m = declaredChain As (traceOf t) m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    simp only [chainRef, declaredChain, ih (fun r hr => hm r (Nat.lt_succ_of_lt hr)),
      hm k (Nat.lt_succ_self k)]

/-- ⚑⚑⚑ **THE ACCUMULATOR CHECK OVER THE DESCRIPTOR'S OWN ADDENDS.**

`n+1` rows of deployed satisfaction, `n` held accumulator threads, the 64 discharge gates, the
emitted index origin and index thread, and the emitted routing balance force the `n+1`-fold RCB
chain **of the addends this descriptor DECLARES** — starting from the accumulator published at
`PI[0..95]` — to be the point at infinity mod the real Vesta-base prime.

⚑ **READ THE CONCLUSION AGAINST `accumulator_discharge_forced`'S.** That one says
`chainRef tr (n+1) ≡ O`: a fold over `sVal (tr r) ADD_X/Y/Z`, i.e. over columns the prover fills.
This one says `declaredChain As (traceOf t) (n+1) ≡ O`: a fold over `declAddend As r`, in which the
trace's addend columns **do not occur**. The verifier rebuilds `As` from the descriptor bytes
(`ExactPublicManifest::preprocessed`), so those addends are VK-pinned.

⚠ The row count is FORCED, not assumed: `the_balance_forces_the_row_count` derives
`t.rows.length = As.length` from the permutation, so a prover can neither pad the chain with
unrouted rows nor drop a declared addend. `hheight` only names `n` for the discharge's `.last`. -/
theorem accumulator_discharge_forced_on_declared_addends
    (As : List Pt3) (t : VmTrace) (n : Nat)
    (hrow : ∀ r, r ≤ n → RowSoundV (traceOf t) r)
    (hthread : ∀ r, r < n → Threaded (traceOf t) r)
    (hd : Discharged (traceOf t) n)
    (hbal : PublicLookupBalanced (accRoutedDesc As) t)
    (h0 : IdxStarted (traceOf t))
    (hidx : ∀ r, r + 1 < t.rows.length → IdxThreaded (traceOf t) r)
    (hheight : t.rows.length = n + 1) :
    CZm (qN : ℤ) (declaredChain As (traceOf t) (n + 1)).1 0
    ∧ CZm (qN : ℤ) (declaredChain As (traceOf t) (n + 1)).2.2 0 := by
  have hridx : ∀ j, j < t.rows.length → rowAt t j RIDX = (j : ℤ) :=
    ridx_is_the_row_index (traceOf t) t.rows.length h0 hidx
  have hlen : t.rows.length = As.length := the_balance_forces_the_row_count As t hbal
  have hchain : chainRef (traceOf t) (n + 1) = declaredChain As (traceOf t) (n + 1) :=
    chain_is_the_declared_chain As t (n + 1) (fun r hr =>
      addend_value_is_declared As t r hbal hridx (by omega))
  have hcore := accumulator_discharge_forced (traceOf t) n hrow hthread hd
  rw [hchain] at hcore
  exact hcore

/-! ### §8e — ⚠ AND THE ROUTING KEY IS DOING WORK.

The Rust side carries the deployed polarity (`circuit/tests/mina_accumulator_routing_proves.rs`: an
honest chain PROVES and a chain whose addends are real Vesta points that are NOT the declared ones
is REFUSED). What is exhibited here is the KEY's separating power, because a routing whose key
collapsed would make `addend_manifest_key_unique` vacuous while every shape pin still passed. -/

/-- A row that is zero everywhere except the index column. -/
def idxRow (k : ℤ) : Assignment := fun c => if c = RIDX then k else 0

/-- ⚑ **THE KEY SEPARATES TWO ROWS WITH IDENTICAL ADDEND CELLS.** `idxRow 0` and `idxRow 1` agree on
every one of the 96 addend columns — all zero — and their tuples still differ, in the KEY field. So
a prover cannot serve row `i`'s declared addend from row `j`, and the pointwise conclusion of
`addend_is_its_declared_addend` is not an artifact of the addends happening to be distinct.

⚠ The moved value is `1`: NONZERO, and inside the declared 8-bit limb width, so nothing here is a
falsifier that moved a zero into a zero. -/
theorem the_routing_key_separates_rows :
    (addTupleOf (idxRow 0)).head? = some 1
    ∧ (addTupleOf (idxRow 1)).head? = some 2
    ∧ (∀ j, j < 3 * SK → idxRow 0 (ADD_X + j) = idxRow 1 (ADD_X + j))
    ∧ addTupleOf (idxRow 0) ≠ addTupleOf (idxRow 1) := by
  have h0 : (addTupleOf (idxRow 0)).head? = some 1 := by
    rw [addTupleOf_head]; norm_num [idxRow]
  have h1 : (addTupleOf (idxRow 1)).head? = some 2 := by
    rw [addTupleOf_head]; norm_num [idxRow]
  refine ⟨h0, h1, ?_, ?_⟩
  · intro j hj
    have hne : ADD_X + j ≠ RIDX := by
      simp only [ADD_X, RIDX, RCB_WIDTH, IN_BASE] at *
      omega
    simp [idxRow, hne]
  · intro h
    rw [h, h1] at h0
    exact absurd (Option.some.inj h0) (by decide)

/-! ### §8f — ⚠ WHAT STANDING EACH HALF OF §8 HAS, AND THEY ARE NOT THE SAME.

§6's note applies unchanged to the ROW half and is not re-argued: `RowSoundV`, `Threaded` — and now
`IdxStarted`/`IdxThreaded` — are the emitted bodies READ AS FACTS ABOUT THE TRACE, and the
`AirLeg.forces` bridge from the emitted constraints back to them is inherited from
`PastaCurveSound`/`EffectLowerCertified` rather than re-established here, because this file lowers
with `lowerAir` and not the certified `lowerTiedAir`. A reader arriving at §8 alone would otherwise
take the two index predicates for something they are not.

⚑ **THE ROUTING HALF STANDS DIFFERENTLY, AND BETTER.** `PublicLookupBalanced` is not a transcription
of an emitted body — it is `DescriptorIR2`'s OWN denotation of the `exactPublicRows` declaration, the
same predicate `demoPublic_duplicate_omission_refused` exercises in both polarities, and the deployed
realization of it is a LogUp PERMUTATION the VERIFIER checks. That is measured rather than argued:
`circuit/tests/mina_accumulator_routing_proves.rs` puts a forged trace past the producer's pre-flight
(`prove_vm_descriptor2_unchecked`) and the deployed verifier refuses it with
`LookupError("GlobalCumulativeMismatch(None): ir2_exact_public_a97")`.

⚠ And the non-vacuity of the routing hypothesis is behavioural, like §6's: what witnesses that
`PublicLookupBalanced (accRoutedDesc demoAddends)` is satisfiable at all is the deployed prover
accepting the honest trace, not anything in this kernel. -/

/-! ## §9 — ⚑⚑ THE CAPS §10 STANDS ON, READ AT SOURCE BEFORE §10 WAS DESIGNED.

⚠ Twice in this cone a cap was designed around before it was read. §4 priced a routing against
`MAX_EXACT_PUBLIC_ARITY = 64` and the constant turned out to be **the member count of a JSON
artifact**, bounding no resource. `the_split_remedy_costs_more_than_the_wide_table` retired a
prescribed remedy that cost MORE than the thing it avoided. And `PastaMsmBucketed` §6c corrected its
own SRS over-count from `21×` to `10×` because the model had forgotten both the all-zero pad row and
`next_pow2`. So the caps are stated here, each against **what it actually counts**, first.

Read at source 2026-08-07, `circuit/src/descriptor_ir2.rs`:

| constant | line | enforced against | what it counts |
|---|---|---|---|
| `MAX_EXACT_PUBLIC_ROWS = 2^21` | `:590` | `rows.len()` (`:2231`) | the DECLARED manifest length, duplicates kept |
| `MAX_EXACT_PUBLIC_CELLS = 2^25` | `:621` | `rows.len() * arity` (`:2232`) | the DECLARED multiset, duplicates kept |
| `MAX_EXACT_PUBLIC_ARITY = 97` | `:616` | a JSON member count (`:6844`) | nothing allocated |

⚑ And the matrix anything MATERIALISES is `ExactPublicManifest::committed_shape` (`:3495`) —
`max (next_pow2 |distinct rows|) 2 × (arity + 2)` — **which is compared against no cap at all.**
`check_descriptor2` is the ONLY enforcement site for the first two and it runs on the declared list
before a cell is allocated. -/

/-- `MAX_EXACT_PUBLIC_ROWS` (`descriptor_ir2.rs:590`). It bounds `rows.len()` of the DECLARED
manifest. Because the exact-public semantics is a PERMUTATION, the declared length is also the trace
height (`the_balance_forces_the_row_count`), so for a routed chain this is the one cap that IS a
height ceiling — not by denomination but by the balance. -/
def EP_ROWS_CAP : Nat := 2097152

/-- `MAX_EXACT_PUBLIC_CELLS` (`descriptor_ir2.rs:621`). It bounds `rows.len() * arity`. -/
def EP_CELLS_CAP : Nat := 33554432

/-- What the CELL cap counts: the declared multiset, duplicates kept. -/
def epDeclaredCells (rows arity : Nat) : Nat := rows * arity

/-- What the verifier COMMITS: `committed_shape`'s height times `prep_width = arity + 2` (the table
id column and the pinned multiplicity column, neither of which the cap's arithmetic sees). -/
def epCommittedCells (height arity : Nat) : Nat := height * (arity + 2)

/-- ⚑⚑ **THE CELL CAP AND THE ALLOCATION DISAGREE IN BOTH DIRECTIONS, AND BOTH DIRECTIONS ARE
EXHIBITED.** A manifest with NO duplicates commits MORE than the cap counts (two extra columns); one
with many duplicates declares far more than it commits. The second exhibit is `PastaMsmBucketed`'s
own SRS manifest — `1 474 800` declared rows at arity `28`, whose `65 537` distinct rows round to a
committed height of `2^17` — and it reproduces that file's `10×` bracket from this file's own two
definitions rather than by citing it.

⚠ This is the theorem that says a cell figure alone never decides admissibility. `srs_cells_exceed_
the_deployed_cap` is TRUE and the object it refuses commits `3 932 160` cells, an eighth of the cap. -/
theorem the_cell_cap_counts_the_declared_multiset_and_not_the_allocation :
    epDeclaredCells 65536 ADDEND_TUP < epCommittedCells 65536 ADDEND_TUP
    ∧ epCommittedCells 131072 28 < epDeclaredCells 1474800 28
    ∧ EP_CELLS_CAP < epDeclaredCells 1474800 28
    ∧ epCommittedCells 131072 28 < EP_CELLS_CAP
    ∧ 10 * epCommittedCells 131072 28 ≤ epDeclaredCells 1474800 28
    ∧ epDeclaredCells 1474800 28 < 11 * epCommittedCells 131072 28 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- ⚑⚑ **NO CAP HAS TO MOVE FOR THE FULL-WIDTH SRS ROUTING.**

§10 routes one 97-wide tuple per row against a manifest whose rows are the SRS generators. At the
real object that manifest is `2^16` rows — one per generator, **no duplicates and no pad**, because
the routing declares one manifest row per trace row and the trace height is the generator count.
`65 536 ≤ 2^21`, `65 536 · 97 = 6 356 992 < 2^25` declared, and `65 536 · 99 = 6 488 064 < 2^25`
committed — the committed height is `next_pow2 65 536 = 65 536` exactly, with no `65 537`th distinct
row to push it up a rung.

⚑ So the cap that refuses `PastaMsmBucketed`'s SRS manifest does **not** refuse this one, and the
difference is not width: it is that the windowed layout re-declares every generator once per window
(`20 ×`) and then pads, while the routing declares each once. Same generators, same arity class,
one cap verdict apart. -/
theorem the_full_srs_routing_needs_no_cap_to_move :
    STEP_SRS ≤ EP_ROWS_CAP
    ∧ epDeclaredCells STEP_SRS ADDEND_TUP = 6356992
    ∧ epDeclaredCells STEP_SRS ADDEND_TUP < EP_CELLS_CAP
    ∧ epCommittedCells STEP_SRS ADDEND_TUP = 6488064
    ∧ epCommittedCells STEP_SRS ADDEND_TUP < EP_CELLS_CAP
    ∧ ADDEND_TUP ≤ MAX_EP_ARITY := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- …and the demonstration's own manifest, measured against the same three caps. Stated separately
so the eight-row instance is not read as evidence about the `2^16`-row one. -/
theorem the_demonstration_manifest_is_far_inside_every_cap :
    epDeclaredCells 8 ADDEND_TUP = 776
    ∧ epDeclaredCells 8 ADDEND_TUP < EP_CELLS_CAP
    ∧ 8 ≤ EP_ROWS_CAP := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-! ## §10 — ⚑⚑⚑ THE DECLARED ADDENDS ARE `−s_r · G_r`, DERIVED RATHER THAN DECLARED.

§8 forced the trace's addend cells to be **the descriptor's declared addend `i`**, and said plainly
that this is one object out from the brief: *"nothing says the declared addends are `−s_r·G_r`."*
A prover holding a fixed descriptor could no longer choose them; whoever emitted the descriptor
still could, because `As : List Pt3` is a free parameter and `accRoutedDesc` will emit any 97-wide
table it is handed.

⚑ **THIS SECTION REMOVES THE FREE PARAMETER.** `srsScaledAddends` is a TOTAL FUNCTION of
  * `Gs` — the generator list, and
  * `u⃗` — the endo-lifted bulletproof challenges,

whose `r`-th entry is `−s_r · G_r` with `s_r = b_poly_coefficients(u⃗)_r` and the scalar
multiplication run **by the same complete formula the row computes** (`rcbAddM qN curveB3`, so a
doubling and an identity are handled without a case split). There is no path by which the emitter
supplies a point: the only inputs are a generator list and 16 field elements.

`accSrsDesc` is the descriptor at that manifest. Its algebra is `-routed`'s VERBATIM — same legs,
same constraints, same width, same selector census — so every forcing theorem of §5–§8 applies to it
unchanged, and the ONE thing that differs is what the manifest is a function of.

## ⚠ WHAT THIS DOES NOT BUY, AT FULL RESOLUTION, AND IT IS THE HONEST HALF OF THE SECTION

**`Gs` and `u⃗` are EMITTER parameters, and nothing in this AIR derives the manifest from them.**
The derivation is a Lean function evaluated at emission time; the verifier rebuilds the manifest
from the descriptor bytes and never re-runs it. So a node that wants to know the manifest belongs to
this block must re-derive it natively — which is `2^16` scalar multiplications, i.e. the very MSM
`bridge/src/mina_accumulator_discharge.rs` performs. ⚑ **Stated as the trichotomy it is: the scaling
relation can live in the CIRCUIT (that is the deferred MSM — `PastaMsmBucketed.fused_at_step` prices
the group work at `1 474 800` complete additions, and §7.2 of that file records those rows are
denominated in the UNSOUND multiply, so on THIS file's sound row it is ~10² further out), or in the
EMITTER (this section — and certifying the emitted manifest then costs exactly the native discharge),
or NOWHERE (§8, a free table). There is no fourth place.** What §10 buys is that the middle option is
now a function with named inputs instead of a list, so the object a certifier must check went from
`n` arbitrary Vesta points to `|u⃗|` field elements and a byte-pinned blob.

`PastaMsmBucketed` §7.3 reached the same conclusion from the other side — *"the descriptor, and
therefore the verifying key, is a function of the scalar vector: one VK per Mina block"* — and §7.4
declares the challenge-binding half TERMINAL for any MSM AIR. Neither is invented here; both are
inherited, and both still stand. -/

/-- The identity, in the projective coordinates the RCB formula is complete over
(`PastaCurveComplete.Oproj`). -/
def OprojN : Pt3 := (0, 1, 0)

/-- Every coordinate reduced at the Vesta base prime. ⚑ Applied at the end of the derivation so the
declared point is CANONICAL by construction: `coordLimb` reads base-`2^SB` digits, and a manifest
carrying a non-canonical representative would declare limbs no honest witness can produce. -/
def redPt (P : Pt3) : Pt3 := (P.1 % qN, P.2.1 % qN, P.2.2 % qN)

theorem redPt_lt (P : Pt3) :
    (redPt P).1 < qN ∧ (redPt P).2.1 < qN ∧ (redPt P).2.2 < qN := by
  have hq : 0 < qN := by decide
  exact ⟨Nat.mod_lt _ hq, Nat.mod_lt _ hq, Nat.mod_lt _ hq⟩

/-- One double-and-add step, LSB-first: the accumulator absorbs `P` when the low bit is set and `P`
doubles. ⚑ The doubling is `rcbAddM qN curveB3 P P` — the SAME strongly-unified formula the row
computes, so nothing here is a second curve arithmetic. -/
def smulAux : Nat → Pt3 → Pt3 → Pt3
  | 0, _, acc => acc
  | (k + 1), P, acc =>
      smulAux ((k + 1) / 2) (rcbAddM qN curveB3 P P)
        (if (k + 1) % 2 = 1 then rcbAddM qN curveB3 acc P else acc)
  termination_by k => k
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

/-- ⚑ `[k]·P` on Vesta. -/
def smulV (k : Nat) (P : Pt3) : Pt3 := smulAux k P OprojN

/-- ⚑ **`b_poly_coefficients`, at modulus `m`** — `s_i = ∏_{j : bit j of i is set} u_{|u|−1−j}`.

That index convention is o1-labs' and is not a choice made here: `poly-commitment/src/commitment.rs`
`:382-394` (tag `0.3.0`) builds `s[i] = s[i − 2^m] · chals[rounds − 1 − m]` with `m = ⌊log₂ i⌋`, and
`dregg_circuit::pasta_msm::b_poly_coefficients_at` (`:316-340`) decodes it to exactly this product.
`b(X) = ∏_{i<k} (1 + u_i · X^{2^{k−1−i}})` is the polynomial it is the coefficient vector of. -/
def bPolyCoeff (m : Nat) (u : List Nat) (i : Nat) : Nat :=
  (List.range u.length).foldl
    (fun acc j => if (i / 2 ^ j) % 2 = 1 then acc * u.getD (u.length - 1 - j) 1 % m else acc) 1

/-- ⚑⚑ **THE DECLARED ADDENDS, DERIVED.** `A_r = −s_r · G_r`, canonical.

The scalars are `b_poly_coefficients(u⃗)` at the Vesta SCALAR prime `pN` — `PastaCurve::Vesta.
scalar()` is `P_PASTA` (`pasta_msm.rs:58-64`), and the generators' coordinates reduce at the Vesta
BASE prime `qN`. Mixing the two is the silent wrong-field bug this comment exists to prevent. -/
def srsScaledAddends (Gs : List Pt3) (u : List Nat) (n : Nat) : List Pt3 :=
  (List.range n).map
    (fun r => redPt (negV (smulV (bPolyCoeff pN u r) (Gs.getD r (0, 0, 0)))))

theorem srsScaledAddends_length (Gs : List Pt3) (u : List Nat) (n : Nat) :
    (srsScaledAddends Gs u n).length = n := by
  simp [srsScaledAddends]

/-- ⚑ **ROW `r`'S DECLARED ADDEND IS THE NEGATED SCALAR MULTIPLE.** No quantifier over the list: the
`r`-th entry IS the derivation applied at `r`. -/
theorem srs_declared_addend_is_the_negated_scalar_multiple
    (Gs : List Pt3) (u : List Nat) (n r : Nat) (hr : r < n) :
    (srsScaledAddends Gs u n).getD r (0, 0, 0)
      = redPt (negV (smulV (bPolyCoeff pN u r) (Gs.getD r (0, 0, 0)))) := by
  have hlt : r < (List.range n).length := by simpa using hr
  simp [srsScaledAddends, List.getD, List.getElem?_map,
    List.getElem?_eq_getElem hlt, List.getElem_range]

/-! ### §10a — FROM THE DECLARED POINT TO THE VALUE THE CHAIN FOLDS.

`declAddend` recomposes `coordLimb`'s base-`2^SB` digits. That recomposition is the identity on any
coordinate below `2^(SB·SK) = 2^256`, and `redPt` puts every coordinate below `qN`. Proved as a
GENERAL digit fact rather than `decide`d at the demonstration's numbers — the latter would be a
`native_decide` through 256-bit arithmetic and would say nothing at `2^16` rows. -/

/-- ⚑ **BASE-`2^SB` RECOMPOSITION.** The `n` low digits of `v`, weighted, sum to `v mod 2^(SB·n)`.
Induction on `n`; no bound on `v` is needed, which is why the statement carries the `%`. -/
theorem nat_mod_split (x A B : Nat) :
    x % (A * B) = A * ((x / A) % B) + x % A := by
  have h1 : x % (A * B) % A = x % A := Nat.mod_mod_of_dvd x ⟨B, rfl⟩
  have h2 : x % (A * B) / A = x / A % B := Nat.mod_mul_right_div_self x A B
  conv_lhs => rw [← Nat.div_add_mod (x % (A * B)) A]
  rw [h1, h2]

theorem sumL_limbs (v : Nat) : ∀ n : Nat,
    Dregg2.Circuit.Emit.PastaFieldSound.sumL (List.range n)
      (fun i => ((2 : ℤ) ^ SB) ^ i * (((v / 2 ^ (SB * i)) % 2 ^ SB : Nat) : ℤ))
      = ((v % 2 ^ (SB * n) : Nat) : ℤ)
  | 0 => by simp [Dregg2.Circuit.Emit.PastaFieldSound.sumL]
  | n + 1 => by
    have ih := sumL_limbs v n
    have hab : 2 ^ (SB * (n + 1)) = 2 ^ (SB * n) * 2 ^ SB := by
      rw [← pow_add, Nat.mul_succ]
    have hcast : ((2 : ℤ) ^ SB) ^ n = ((2 ^ (SB * n) : Nat) : ℤ) := by
      push_cast; rw [pow_mul]
    unfold Dregg2.Circuit.Emit.PastaFieldSound.sumL at ih ⊢
    rw [List.range_succ, List.map_append, List.sum_append, ih, hab,
      nat_mod_split v (2 ^ (SB * n)) (2 ^ SB)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Nat.cast_add, Nat.cast_mul]
    rw [hcast]
    ring

/-- The declared coordinate value IS the coordinate, for any coordinate below `2^256`. -/
theorem declVal_of_lt (P : Pt3) (off : Nat) (c : Nat)
    (hc : c < 2 ^ (Dregg2.Circuit.Emit.PastaFieldSound.SB * SK))
    (hoff : ∀ i, i < SK → coordLimb P (off + i)
      = (c / 2 ^ (Dregg2.Circuit.Emit.PastaFieldSound.SB * i))
          % 2 ^ Dregg2.Circuit.Emit.PastaFieldSound.SB) :
    declVal P off = (c : ℤ) := by
  unfold declVal
  rw [sumL_congr _ _ (fun i => ((2 : ℤ) ^ Dregg2.Circuit.Emit.PastaFieldSound.SB) ^ i
        * (((c / 2 ^ (Dregg2.Circuit.Emit.PastaFieldSound.SB * i))
             % 2 ^ Dregg2.Circuit.Emit.PastaFieldSound.SB : Nat) : ℤ))
      (fun i hi => by rw [hoff i (List.mem_range.mp hi)])]
  rw [sumL_limbs c SK, Nat.mod_eq_of_lt hc]

/-- A point's three coordinates in the ℤ denotation `declaredChain` folds. -/
def ptZ (P : Pt3) : ℤ × ℤ × ℤ := ((P.1 : ℤ), (P.2.1 : ℤ), (P.2.2 : ℤ))

/-- ⚑ **THE DECLARED ADDEND'S VALUE IS THE POINT**, for any manifest entry whose coordinates are
canonical. Stated over an arbitrary `P` and an arbitrary `As` so it is a fact about the ROUTING's
recomposition, not about §10's derivation — §8's demonstration manifest satisfies it too. -/
theorem declAddend_of_getD (As : List Pt3) (r : Nat) (P : Pt3)
    (hget : As.getD r (0, 0, 0) = P)
    (h1 : P.1 < qN) (h2 : P.2.1 < qN) (h3 : P.2.2 < qN) :
    declAddend As r = ptZ P := by
  have hq : qN < 2 ^ (Dregg2.Circuit.Emit.PastaFieldSound.SB * SK) := by decide
  have hsk : (0 : Nat) < SK := by decide
  unfold declAddend ptZ
  rw [hget]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · refine declVal_of_lt P 0 P.1 (lt_trans h1 hq) (fun i hi => ?_)
    have e0 : 0 + i = i := by omega
    rw [e0]
    simp [coordLimb, hi]
  · refine declVal_of_lt P SK P.2.1 (lt_trans h2 hq) (fun i hi => ?_)
    have n1 : ¬ (SK + i < SK) := by omega
    have p2 : SK + i < 2 * SK := by omega
    have e1 : SK + i - SK = i := by omega
    simp [coordLimb, n1, p2, e1]
  · refine declVal_of_lt P (2 * SK) P.2.2 (lt_trans h3 hq) (fun i hi => ?_)
    have n1 : ¬ (2 * SK + i < SK) := by omega
    have n2 : ¬ (2 * SK + i < 2 * SK) := by omega
    have e2 : 2 * SK + i - 2 * SK = i := by omega
    simp [coordLimb, n1, n2, e2]

/-- ⚑⚑ **THE DECLARED ADDEND IS `−s_r · G_r`, AS THE VALUE THE CHAIN FOLDS.** The three
recompositions `declaredChain` reads are the three coordinates of the derived point — no `%` and no
canonicality envelope, because `redPt` reduced at `qN` and `qN < 2^256`. -/
theorem declAddend_of_srsScaled (Gs : List Pt3) (u : List Nat) (n r : Nat) (hr : r < n) :
    declAddend (srsScaledAddends Gs u n) r
      = ptZ (redPt (negV (smulV (bPolyCoeff pN u r) (Gs.getD r (0, 0, 0))))) := by
  have hb := redPt_lt (negV (smulV (bPolyCoeff pN u r) (Gs.getD r (0, 0, 0))))
  exact declAddend_of_getD _ r _
    (srs_declared_addend_is_the_negated_scalar_multiple Gs u n r hr) hb.1 hb.2.1 hb.2.2

/-! ### §10b — ⚑⚑ THE SRS DESCRIPTOR, AND THE DISCHARGE OVER THE SCALAR MULTIPLES. -/

/-- ⚑⚑ **THE EMITTED SRS DESCRIPTOR.** `-routed`'s algebra, verbatim; a manifest that is the image
of `srsScaledAddends`. -/
def accSrsDesc (Gs : List Pt3) (u : List Nat) (n : Nat) : EffectVmDescriptor2 :=
  accRoutedDescNamed "dregg-mina-accumulator-srs::v1" (srsScaledAddends Gs u n)

theorem accSrsDesc_name (Gs : List Pt3) (u : List Nat) (n : Nat) :
    (accSrsDesc Gs u n).name = "dregg-mina-accumulator-srs::v1" := rfl

/-- ⚑ **FOUR NAMES, FOUR OBJECTS.** A registry lookup that resolved `-srs` to `-routed` would serve
a descriptor whose manifest is a free parameter and every shape pin would still pass. -/
theorem the_four_descriptors_do_not_share_a_name (As : List Pt3)
    (Gs : List Pt3) (u : List Nat) (n : Nat) :
    accSegDesc.name ≠ (accSrsDesc Gs u n).name
    ∧ accFinalDesc.name ≠ (accSrsDesc Gs u n).name
    ∧ (accRoutedDesc As).name ≠ (accSrsDesc Gs u n).name := by
  rw [accSrsDesc_name, accRoutedDesc_name]
  refine ⟨by decide, by decide, by decide⟩

/-- ⚑ **THE ALGEBRA IS THE SAME OBJECT.** Constraints, width, PI count and table ids are `-routed`'s
at every `Gs`, `u⃗` and `n`; only `.name` and the manifest differ. This is what makes §5–§8's forcing
theorems apply to `-srs` without being restated, and it is what
`srs_balance_is_routed_balance` is `rfl` on. -/
theorem the_srs_descriptor_differs_from_the_routed_one_only_in_its_name_and_its_manifest
    (Gs : List Pt3) (u : List Nat) (n : Nat) :
    (accSrsDesc Gs u n).constraints = (accRoutedDesc []).constraints
    ∧ (accSrsDesc Gs u n).traceWidth = ROUTED_WIDTH
    ∧ (accSrsDesc Gs u n).piCount = ACC_PI_COUNT
    ∧ ((accSrsDesc Gs u n).tables.map (·.id))
        = ((accRoutedDesc []).tables.map (·.id)) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE BALANCE TRANSFERS BY DEFINITION.** `PublicLookupBalanced` projects `.tables` and
`.constraints` and nothing else, and neither depends on the name — so the routing hypothesis of §8
is literally the same proposition on `-srs`. Not a bridge: `Iff.rfl`. -/
theorem srs_balance_is_routed_balance (Gs : List Pt3) (u : List Nat) (n : Nat) (t : VmTrace) :
    PublicLookupBalanced (accSrsDesc Gs u n) t
      ↔ PublicLookupBalanced (accRoutedDesc (srsScaledAddends Gs u n)) t := Iff.rfl

/-- ⚑⚑⚑ **THE ACCUMULATOR CHECK OVER THE PINNED SCALAR MULTIPLES.**

`n+1` rows of deployed satisfaction, `n` held accumulator threads, the 64 discharge gates, the
emitted index origin and thread, and the emitted routing balance force the `n+1`-fold RCB chain
**of `−s_r · G_r`** — starting from the accumulator published at `PI[0..95]` — to be the point at
infinity mod the real Vesta-base prime.

⚑ **READ THE CONCLUSION AGAINST §8d'S.** `accumulator_discharge_forced_on_declared_addends`
concludes over `declaredChain As`, a fold whose addends are whatever list the emitter was handed.
This one concludes over `declaredChain (srsScaledAddends Gs u n)`, a fold whose addends are the
image of a function of a generator list and `u⃗` — **no list of points occurs in the statement.**

⚠ The limit is §10's docblock and is not softened here: the derivation runs in the EMITTER, so a
certifier still re-derives it natively. What moved is the object it re-derives FROM. -/
theorem accumulator_discharge_forced_on_srs_scaled_addends
    (Gs : List Pt3) (u : List Nat) (n : Nat) (t : VmTrace) (m : Nat)
    (hrow : ∀ r, r ≤ m → RowSoundV (traceOf t) r)
    (hthread : ∀ r, r < m → Threaded (traceOf t) r)
    (hd : Discharged (traceOf t) m)
    (hbal : PublicLookupBalanced (accSrsDesc Gs u n) t)
    (h0 : IdxStarted (traceOf t))
    (hidx : ∀ r, r + 1 < t.rows.length → IdxThreaded (traceOf t) r)
    (hheight : t.rows.length = m + 1) :
    CZm (qN : ℤ) (declaredChain (srsScaledAddends Gs u n) (traceOf t) (m + 1)).1 0
    ∧ CZm (qN : ℤ) (declaredChain (srsScaledAddends Gs u n) (traceOf t) (m + 1)).2.2 0 :=
  accumulator_discharge_forced_on_declared_addends (srsScaledAddends Gs u n) t m
    hrow hthread hd ((srs_balance_is_routed_balance Gs u n t).mp hbal) h0 hidx hheight

/-- ⚑⚑ **AND THE FOLD'S ADDENDS, NAMED.** Every step of `declaredChain (srsScaledAddends Gs u n)`
adds exactly `−s_r · G_r`. Together with the theorem above this is the deliverable: *the chain that
is forced to vanish is the chain of the scalar multiples of the supplied generators.* -/
theorem the_forced_chain_adds_the_scalar_multiples
    (Gs : List Pt3) (u : List Nat) (n : Nat) (tr : Trace) (r : Nat) (hr : r < n) :
    declaredChain (srsScaledAddends Gs u n) tr (r + 1)
      = (let P := declaredChain (srsScaledAddends Gs u n) tr r
         let A := ptZ (redPt (negV (smulV (bPolyCoeff pN u r) (Gs.getD r (0, 0, 0)))))
         rcbOutZ (curveB3 : ℤ) P.1 P.2.1 P.2.2 A.1 A.2.1 A.2.2) := by
  show (let P := declaredChain (srsScaledAddends Gs u n) tr r
        rcbOutZ (curveB3 : ℤ) P.1 P.2.1 P.2.2
          (declAddend (srsScaledAddends Gs u n) r).1
          (declAddend (srsScaledAddends Gs u n) r).2.1
          (declAddend (srsScaledAddends Gs u n) r).2.2) = _
  rw [declAddend_of_srsScaled Gs u n r hr]

/-! ### §10c — ⚠ THE DERIVATION IS REFUTABLE, AND WHERE EACH HALF IS MEASURED.

A derivation that collapsed — `bPolyCoeff` returning `1`, `smulV` ignoring its scalar — would make
every theorem above true and the manifest wrong, and no shape pin in this file would move. Both
halves are therefore exhibited separating. They are exhibited in DIFFERENT PLACES and that is a
decision, not an omission:

* the CHALLENGE half is pure `Nat` arithmetic and is `decide`d here;
* ⚠ the CURVE half is **not** evaluated in this kernel. `smulV` runs `rcbAddM`, whose `rcbTraceM`
  body is a 33-step `let`-chain with heavy reuse, and `minted-poseidon2-perm-is-a-reduction-bomb`
  measured exactly that shape at `47.6 GB` for ONE permutation because `whnf` zeta-expands `let`
  helpers. A `decide` through `[2]·G ≠ [1]·G` would be that bomb. It is measured instead in
  `circuit/tests/mina_accumulator_srs_proves.rs`, against `dregg_circuit::pasta_msm::scalar_mul_at`
  over the **sha-pinned** `VESTA_SRS_G_BIN` — which is better evidence than a kernel `decide` would
  have been, because it checks this derivation against the DEPLOYED native arithmetic and the
  byte-pinned blob rather than against itself. -/

/-- `[0]·P` is the RCB identity `(0 : 1 : 0)`, not a zero triple — a `smulV` seeded with `(0,0,0)`
would make the empty chain add a point off the curve. One equation of the recursion; no field
element is reduced. -/
theorem smulV_at_zero (P : Pt3) : smulV 0 P = OprojN := by
  simp [smulV, smulAux]

/-- ⚑ **THE CHALLENGES MOVE THE COEFFICIENTS, AND IN THE o1-labs ORDER.** At `u⃗ = [3, 5]` the four
coefficients are `1, u₁, u₀, u₀·u₁` — index `1` reads the LAST challenge and index `2` the FIRST. A
`bPolyCoeff` that dropped the `|u|−1−j` reversal would swap these two, produce a manifest that is a
PERMUTATION of the right one, and leave every other theorem in §10 true.

⚠ The moved values are `3` and `5`: nonzero, distinct, and neither is the identity of the product —
so this is not a falsifier that moved a zero into a zero. -/
theorem the_challenge_order_is_the_o1labs_one :
    bPolyCoeff pN [3, 5] 0 = 1
    ∧ bPolyCoeff pN [3, 5] 1 = 5
    ∧ bPolyCoeff pN [3, 5] 2 = 3
    ∧ bPolyCoeff pN [3, 5] 3 = 15
    ∧ bPolyCoeff pN [3, 5] 1 ≠ bPolyCoeff pN [3, 5] 2 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- …and the coefficient vector is not constant in the challenges: one challenge changes and every
odd index changes with it. This is the half that says the manifest is a function OF `u⃗` and not
merely a function that ignores it. -/
theorem the_coefficients_are_not_constant_in_the_challenges :
    bPolyCoeff pN [3, 5] 1 ≠ bPolyCoeff pN [3, 7] 1
    ∧ bPolyCoeff pN [3, 5] 2 ≠ bPolyCoeff pN [11, 5] 2 := by
  refine ⟨by native_decide, by native_decide⟩

/-! ## §11 — ⚑⚑⚑ THE HEAD BIND: THE CLAIM STOPS BEING A NUMBER A CONSUMER REMEMBERS TO COMPARE.

## The defect this closes, quoted from the object that carries it

`bridge/src/mina_accumulator_discharge.rs::root_entry_binds_claim` compares a verified fold root's
`acc_in` block against a claim the caller holds, elementwise over 96 lanes, and its own docblock
says what it is: *"It is a REFUSAL made by the consumer, not a gate; say it that way."* Its second
paragraph names what it still does not reach — *"nor does it relate the claim to a tracked head."*

So: a node that verifies an accumulator root and **forgets to call that function** accepts *any*
discharging claim. Nothing in the emitted bytes says which chain's head the claim belongs to. That
is the accumulator's second trusted item, and it is the one this section closes.

## ⚑ WHAT IS NOW A CONSTRAINT, AND SAY WHICH OBJECT IT IS ABOUT

The object is `dregg-mina-accumulator-head::v1` — `-srs`'s ALGEBRA VERBATIM (same manifest, same
4 831 routed constraints, same selector census on the routed prefix) plus TWELVE constraints:

    guard on      HEAD_OK = 1 on the FIRST row                     (.first window gate)
    guard off     HEAD_OK = 0 on every later row                   (.transition window gate)
    nine pins     HEAD_STATE i ↦ PI[192 + i]                       (.first pi bindings)
    ONE proof_bind  guard HEAD_OK
                    commit  = HEAD_STATE(9) ‖ ACC_X..ACC_Z(96)     — 105 lanes
                    vk      = HEAD_VK(9), pinned to the HEAD PROGRAM's fingerprint
                    bound   = the DECLARED head's nine lanes ‖ the DECLARED claim's 96 limbs

`ProofBind.holdsAt`'s third conjunct is `zeroLanes guard commit bound`, so under `HEAD_OK = 1` the
row's nine published head lanes and its ninety-six entry-accumulator limbs are forced, **lane by
lane, to the descriptor's declared pair**. `Ir2Air::eval`'s `ProofBind` arm emits the same
`1 + 9 + 105` polynomials. **105 lanes, elementwise, no digest, therefore no birthday bound** — the
shape §"THE SHAPE" already claims for the claim block and `LightClientMinaAir` §2c landed for
`TIP_STATE`.

## ⚑ WHY `bound` IS LITERALS AND NOT COLUMNS — the opposite call from `linkBindLeg`, deliberately

`LightClientMinaAir.linkBindLeg` takes `bound := none` and argues it is the STRONGER choice, because
there `commit` is already a PI-bound column and a `bound` congruence *"could only compare it to
itself, which is decoration"* (`feedback-a-pin-against-its-own-definition-is-decoration`). That
argument is about comparing a column to ITS OWN definition. Here `bound` is a vector of DESCRIPTOR
LITERALS, so the congruence compares a PI-bound column to a **VK-declared constant** — which is the
entire difference between *"the prover publishes whatever claim it likes"* and *"the descriptor
declares the claim."* The two calls are opposite because the two situations are.

## ⚠ AND WHAT THE NINETY-SIX CLAIM LITERALS DO **NOT** ADD, said before a reader assumes it

Given the routing and the discharge, the entry accumulator is already DETERMINED as a *point*:
`accumulator_discharge_forced_on_srs_scaled_addends` forces `C + Σ_r (−s_r·G_r) = O`, so
`C = Σ_r s_r·G_r`. The claim half of `bound` therefore adds (i) the canonical projective
REPRESENTATIVE — the discharge fixes the point, not the triple — and (ii) the elementwise statement
of the PAIR inside one emitted object. **It is the head half that carries the new content**: nine
lanes of a Mina protocol-state hash that no other constraint in this file mentions.

## ⚑ WHY THE GUARD IS FORCED ON AT `.first` AND OFF EVERYWHERE ELSE, and it is not a style choice

`Satisfied2Custom.proofBound` quantifies over EVERY row, and `Ir2Air::eval` asserts the seam's
polynomials on every row. A seam whose commit lanes are the row's own `ACC_X..` block would then
demand a sub-proof per row, one per intermediate accumulator — which is not the sentence. And a
guard that is a FREE column is the vacuity `LightClientMinaLinkAir` names: a prover sets it to zero
and the whole seam evaporates for one felt. Both are closed by the same two window gates: `.first`
forces `HEAD_OK = 1` (so the seam cannot be switched off — `the_unguarded_head_row_is_refused` is
the exhibit), `.transition` forces `HEAD_OK = 0` on every successor (so the obligation is the FIRST
ROW's and there is exactly one).

## ⚠ WHAT STANDING EACH HALF OF THE SEAM HAS, AND THEY ARE NOT THE SAME

* **ROW-LOCAL — a CONSTRAINT, and it is what closes item 2.** The guard is a bit, the nine `HEAD_VK`
  columns equal `MINA_HEAD_VK_LANES`, and the 105 commit lanes equal the declared pair. All of it is
  in `constraints`, all of it is refutable, and the refusals are exhibited in
  `circuit/tests/mina_accumulator_head_proves.rs` against `prove_vm_descriptor2_unchecked` so the
  verdict is the AIR's and not the producer's pre-flight.

* ⚠ **OFF-ROW — an OBLIGATION, and NO PROGRAM IN THIS TREE CAN DISCHARGE IT TODAY.**
  `ProofBind.boundAt` reads *"∃ a verifying sub-proof of the pinned program whose `piCommit` is
  these 105 lanes."* The pinned program is `dregg-mina-lightclient-verify::v1`, which publishes the
  head's nine `TIP_STATE` lanes (PI 9..17) and **does not publish the block's
  challenge-polynomial commitment at all**. So the existential names evidence that does not yet
  exist. That is **UNDONE WORK with a named shape, not a caveat and not a theorem of the model.**

  ⚠ And the cheap version of that work is REFUSED here rather than shipped: appending 96 free PI
  slots to the head descriptor would make `boundTo` dischargeable by a head proof that *published*
  a claim nothing forced — the same vacuity one layer down, and the same shape this tree already
  calls out about `CONJ_PI` (*"a published block nothing refuses"*). The content version is that the
  head DERIVES `messages_for_next_wrap_proof.challenge_polynomial_commitment` from the block, which
  is Pasta arithmetic on a BabyBear rail and is the ≈10⁹-constraint wall `LightClientMinaAir`'s own
  §"Public inputs" prices. Nothing here is cheaper than that number and nothing here pretends to be.

* ⚠ **DESCRIPTOR SELECTION is untouched, and it is §8's residual verbatim.** Whether the descriptor
  a node verified against is the one for the block in hand is not closed here. What IS closed: given
  a descriptor, a prover can no longer present a claim it does not declare, or publish a head it does
  not declare. The consumer's residue shrank from *"96 lanes it must have obtained out of band"* to
  *"nine lanes against a head it already tracks"*, and `check_subproof_program_pin`'s idiom —
  recompute the pinned program's fingerprint at VERIFY time — applies to `MINA_HEAD_VK_LANES`
  unchanged.

## ⚑ FLAG DAY (findable, and this is the fifth coupling of its kind)

**Re-emitting `dregg-mina-lightclient-verify-v1.json` MOVES `MINA_HEAD_VK_LANES` and therefore
re-emits and re-VKs `dregg-mina-accumulator-head::v1`.** That is intended and it is exactly what
`CHAINLINK_VK_LANES`, `LINK_VK_LANES` and `CONJ_VK_LANES` already cost on the head side: a light
client must not keep accepting accumulator roots that name a head program no descriptor has.
**NOTHING BELOW MOVES:** `-seg`, `-final`, `-routed` and `-srs` are byte-identical, PI slots 0..191
are untouched and 192..200 are APPENDED, and `root_entry_binds_claim` still reads the same
`acc_in` block. A new artifact is emitted (`mina-accumulator-head.json`); nothing is re-genesised. -/

/-- The nine `Faithful9` key lanes a 32-byte Mina protocol-state hash occupies: `8·29 + 24 = 256`
bits exactly, so the encoding is injective (`fieldToLanes9_injective`) and the tie is worth the whole
object rather than a ~31-bit projection of it. -/
def HEAD_LANES : Nat := 9

/-- ⚑ **THE SEAM'S GUARD** — one column past the routing's row index. Forced to `1` on the first row
and to `0` on every successor; it is never a free witness. -/
def HEAD_OK : Nat := ROUTED_WIDTH

/-- The `i`-th published lane of the head this claim is declared to belong to. -/
def HEAD_STATE (i : Nat) : Nat := ROUTED_WIDTH + 1 + i

/-- The `i`-th attested HEAD-PROGRAM fingerprint lane. Pinned by `vkPin`, not by a PI binding — the
program identity is the descriptor's, not something a consumer supplies. -/
def HEAD_VK (i : Nat) : Nat := ROUTED_WIDTH + 1 + HEAD_LANES + i

/-- The head-bound descriptor's declared trace width. -/
def HEADED_WIDTH : Nat := ROUTED_WIDTH + 1 + 2 * HEAD_LANES

/-- ⚑ **NINETEEN COLUMNS, AND THE BLOCKS DO NOT OVERLAP.** A `HEAD_STATE`/`HEAD_VK` collision would
make the program pin and the head pin the same cells, so the seam would pin the fingerprint to the
head and read as satisfied — written out rather than assumed. -/
theorem the_head_seam_costs_nineteen_columns :
    HEADED_WIDTH = 3068 ∧ HEADED_WIDTH = ROUTED_WIDTH + 19
    ∧ HEAD_OK = 3049 ∧ HEAD_STATE 0 = 3050 ∧ HEAD_STATE 8 = 3058
    ∧ HEAD_VK 0 = 3059 ∧ HEAD_VK 8 = 3067
    ∧ ∀ i j, i < HEAD_LANES → j < HEAD_LANES → HEAD_STATE i ≠ HEAD_VK j := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro i j hi hj
  simp only [HEAD_STATE, HEAD_VK, HEAD_LANES, ROUTED_WIDTH, RCB_WIDTH] at *
  omega

/-- PI slot of the `i`-th published head lane — APPENDED after the accumulator's 192. -/
def PI_HEAD (i : Nat) : Nat := ACC_PI_COUNT + i

/-- `192 + 9`. -/
def HEAD_PI_COUNT : Nat := ACC_PI_COUNT + HEAD_LANES

/-- ⚑ **APPENDED: NO EXISTING SLOT MOVES.** `acc_in ‖ acc_out` keeps slots 0..191 and the fold's
`left[96 + k] ↔ right[k]` connect is unaffected, which is why this is not a fold flag day. -/
theorem head_pi_layout :
    HEAD_PI_COUNT = 201 ∧ PI_HEAD 0 = 192 ∧ PI_HEAD 8 = 200
    ∧ ACC_PI_COUNT ≤ PI_HEAD 0 ∧ ∀ i, PI_HEAD i = ACC_PI_COUNT + i := by
  refine ⟨by decide, by decide, by decide, by decide, fun _ => rfl⟩

/-- ⚑ **THE GUARD IS FORCED ON.** `.first` lowers to a `VmConstraint.boundary` whose body reads
`env.loc` alone. Setting `HEAD_OK = 0` — the "switch the seam off for one felt" move — makes this
gate false, which is `the_unguarded_head_row_is_refused`. -/
def headOkOnLeg : AirLeg :=
  .window ⟨RowSel.first, WindowExpr.add (.loc HEAD_OK) (.const (-1))⟩

/-- ⚑ **…AND OFF ON EVERY SUCCESSOR**, so the off-row obligation is the FIRST ROW'S and there is
exactly one of it. `.transition` is the only selector under which `nxt` is the genuine successor. -/
def headOkOffLeg : AirLeg :=
  .window ⟨RowSel.transition, WindowExpr.nxt HEAD_OK⟩

/-- The nine head lanes, published. -/
def headStatePinLegs : List AirLeg :=
  (List.range HEAD_LANES).map (fun i => AirLeg.pin ⟨.first, HEAD_STATE i, PI_HEAD i⟩)

theorem headStatePinLegs_length : headStatePinLegs.length = 9 := by native_decide

/-- ⚑⚑ **THE HEAD PROGRAM'S IDENTITY, AS NINE LANES — MEASURED, NEVER INVENTED.** The `Faithful9`
key lanes of `effect_vm_descriptor2_semantic_fingerprint(dregg-mina-lightclient-verify::v1)` —
blake3 (derive-key, context `EFFECT_VM_DESCRIPTOR2_FINGERPRINT_CONTEXT`) over that descriptor's
CANONICAL bytes at `w=77, pi=39, cons=74`. In this tree the descriptor IS the verifying
key: `verify_vm_descriptor2(&desc, &proof, &pis)` takes no other key material.

⚑ These digits are measured from the served artifact by `circuit/examples/conj_fingerprint.rs` and
independently re-derived in pure Lean by `scripts/check-vk-pin-literals.sh`, as well as by
`mina_accumulator_head_proves.rs::the_pinned_head_program_is_the_served_head_descriptor`. Those gates
exist because `75df624cf` once re-emitted a descriptor and left a `vkPin` naming a program no
descriptor in this tree had. -/
def MINA_HEAD_VK_LANES : List ℤ :=
  -- ⚑ MOVED 2026-08-08. `dregg-mina-lightclient-verify-v1.json` re-emitted twice over on that day's
  -- pin flag day: `LightClientMinaAir.CHAINLINK_VK_LANES` had gone stale against a re-emitted
  -- `pasta-fq-chainlink.json`, and `LINK_VK_LANES` moved with the segment descriptor (whose own
  -- `ABSORB_VK_LANES` had gone stale against a re-emitted `pasta-fp-absorb.json`). Two rungs down,
  -- this one. `the_pinned_head_program_is_the_served_head_descriptor` was RED at HEAD on exactly
  -- this comparison and is what named it. Recomputed from the NEW bytes:
  --   cargo run -p dregg-circuit --example conj_fingerprint -- \
  --     circuit/descriptors/by-name/dregg-mina-lightclient-verify-v1.json
  --   fp=e64df5b684619a0fe22cafe11fd0115298591fa37212848e638e6a6a25599f7e
  --
  -- ⚑ FINAL CASCADE RUNG, 2026-08-11. After the canonical-record flag day widened the three
  -- Pasta leaf programs and their final fingerprints propagated through the link, the emitted head
  -- retained geometry `77/39/74` and fingerprints to:
  --   fp=2a431795898a925498fff71d753050c3303f83a4ce5fd0f09ba5db35787c2d32
  [353846058, 76829772, 503309845, 6351419, 334695477, 266818113, 376423233, 252099444, 3288444]

theorem the_head_vk_pin_is_nine_lanes : MINA_HEAD_VK_LANES.length = HEAD_LANES := by native_decide

/-- ⚑ **THE SENTENCE THE SUB-PROOF MUST EXPOSE** — the head, then the claim, as columns. 105 lanes:
`commit` is the width of the STATEMENT, not of the program fingerprint, and the two have been
measured separately since 2026-08-06 (`ProofBind.widthOk`). The 96 claim lanes are `ACC_X + j` for
`j < 3·SK`, contiguous exactly because `ACC_X/ACC_Y/ACC_Z = 0/32/64`. -/
def headCommitLanes : List Dregg2.Circuit.Expr :=
  (List.range HEAD_LANES).map (fun i => Dregg2.Circuit.Expr.var (HEAD_STATE i))
    ++ (List.range (3 * SK)).map (fun j => Dregg2.Circuit.Expr.var (ACC_X + j))

theorem headCommitLanes_length : headCommitLanes.length = 105 := by native_decide

/-- ⚑ **THE DECLARED PAIR, AS LITERALS.** `H` is the head's nine lanes; `C` the claim, whose 96
`coordLimb` digits are the SAME base-`2^8` decomposition the manifest rows and the trace's addend
cells use — one layout, not a second transcription. -/
def headBoundLanes (H : List ℤ) (C : Pt3) : List Dregg2.Circuit.Expr :=
  (List.range HEAD_LANES).map (fun i => Dregg2.Circuit.Expr.const (H.getD i 0))
    ++ (List.range (3 * SK)).map (fun j => Dregg2.Circuit.Expr.const ((coordLimb C j : ℤ)))

theorem headBoundLanes_length (H : List ℤ) (C : Pt3) : (headBoundLanes H C).length = 105 := by
  simp only [headBoundLanes, List.length_append, List.length_map, List.length_range]
  decide

/-- ⚑⚑ **THE SEAM.** Guard `HEAD_OK`; the attested program is nine `HEAD_VK` columns pinned to the
head descriptor's fingerprint; the declared commitment is the 105-lane pair. `BindLeg.mainRailOk`
refuses a seam that pins NEITHER half (`ProofBind.isDeclarative`, whose existential quantifies over
every program), one below the nine-lane floor, and a pin naming fewer lanes than the vector it pins —
so this leg could not be weakened into any of those and still lower. -/
def headBindLeg (H : List ℤ) (C : Pt3) : AirLeg :=
  .bind { guard := .var HEAD_OK
        , commit := headCommitLanes
        , vk := (List.range HEAD_LANES).map (fun i => Dregg2.Circuit.Expr.var (HEAD_VK i))
        , vkPin := some MINA_HEAD_VK_LANES
        , bound := .bound (headBoundLanes H C) }

/-- The routed block's tables at the WIDENED main declaration. Only the main table's width moves;
the three range tables and the addend manifest are `routedTables`' verbatim. -/
def headedTables (As : List Pt3) : List Dregg2.Circuit.DescriptorIR2.TableDef :=
  Dregg2.Circuit.DescriptorIR2.mainTableDef HEADED_WIDTH
    :: (rcbTables.drop 1 ++ [addendTable As])

theorem headedTables_ids_are_the_routed_ones (As : List Pt3) :
    (headedTables As).map (·.id) = (routedTables As).map (·.id) := rfl

/-- ⚑ **THE HEAD-BOUND BLOCK** — `accRoutedAir`'s legs VERBATIM plus the twelve. Nothing is
re-authored, so every forcing theorem of §5–§10 applies unchanged. -/
def accHeadAir (As : List Pt3) (H : List ℤ) (C : Pt3) : EffectAir :=
  { tables := headedTables As
  , legs := accRoutedAir.legs ++ [headOkOnLeg, headOkOffLeg]
              ++ headStatePinLegs ++ [headBindLeg H C] }

/-- ⚑ **THE ROUTED BLOCK'S LEGS ARE A PREFIX.** The head bind APPENDS; it does not re-author the
routing, the threads, the discharge or the pins. -/
theorem accHeadAir_extends_accRoutedAir (As : List Pt3) (H : List ℤ) (C : Pt3) :
    accRoutedAir.legs <+: (accHeadAir As H C).legs :=
  ⟨[headOkOnLeg, headOkOffLeg] ++ headStatePinLegs ++ [headBindLeg H C], by
    simp [accHeadAir, List.append_assoc]⟩

/-- ⚑ **THE COMPILER ACCEPTS IT, AT EVERY DECLARED PAIR.** `BindLeg.mainRailOk` reads only lengths,
and `headCommitLanes`/`headBoundLanes` are `List.range`-shaped, so the verdict does not depend on
`H` or `C` — a descriptor emitted at a different head cannot be the one that stops lowering. -/
theorem accHeadAir_mainRailOk (As : List Pt3) (H : List ℤ) (C : Pt3) :
    (accHeadAir As H C).mainRailOk = true := by
  simp only [EffectAir.mainRailOk, accHeadAir, List.all_append, Bool.and_eq_true]
  refine ⟨⟨⟨accRoutedAir_mainRailOk [], by native_decide⟩, by native_decide⟩, ?_⟩
  simp only [List.all_cons, List.all_nil, Bool.and_true, AirLeg.mainRailOk, headBindLeg,
    Dregg2.Circuit.EffectAirIR.BindLeg.mainRailOk, headCommitLanes, headBoundLanes,
    Option.isNone, Dregg2.Circuit.DescriptorIR2.CommitBindingOf.isPort, List.length_append, List.length_map, List.length_range,
    MINA_HEAD_VK_LANES]
  decide

/-- ⚑ **THE SELECTOR CENSUS, HEAD-BOUND.** One more `.first` (the guard's forcing gate) and one more
`.transition` (the guard's off-gate) than `-routed`; the 64 `.last` discharge gates and the 96
accumulator threads are untouched, and there is still no `.all`. A `.first → .all` re-scope on the
guard would force `HEAD_OK = 1` on every row and re-arm the per-row obligation the off-gate exists to
retire — and it moves this number. -/
theorem the_head_selector_census (As : List Pt3) (H : List ℤ) (C : Pt3) :
    (accHeadAir As H C).windowCountSel RowSel.transition = 98
    ∧ (accHeadAir As H C).windowCountSel RowSel.last = 64
    ∧ (accHeadAir As H C).windowCountSel RowSel.first = 2
    ∧ (accHeadAir As H C).windowCountSel RowSel.all = 0
    ∧ (accHeadAir As H C).lookupCount = 1 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE HEAD-BOUND DESCRIPTOR, EMITTED UNDER A GIVEN NAME.** -/
def accHeadDescNamed (nm : String) (As : List Pt3) (H : List ℤ) (C : Pt3) : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir nm HEADED_WIDTH HEAD_PI_COUNT [] (accHeadAir As H C)

/-- ⚑⚑ **THE EMITTED HEAD-BOUND DESCRIPTOR** — `-srs`'s manifest (a function of the pinned SRS and
the challenges) with the head seam on top. -/
def accHeadDesc (Gs : List Pt3) (u : List Nat) (n : Nat) (H : List ℤ) (C : Pt3) :
    EffectVmDescriptor2 :=
  accHeadDescNamed "dregg-mina-accumulator-head::v1" (srsScaledAddends Gs u n) H C

theorem accHeadDesc_name (Gs : List Pt3) (u : List Nat) (n : Nat) (H : List ℤ) (C : Pt3) :
    (accHeadDesc Gs u n H C).name = "dregg-mina-accumulator-head::v1" := rfl

theorem accHeadDesc_width (Gs : List Pt3) (u : List Nat) (n : Nat) (H : List ℤ) (C : Pt3) :
    (accHeadDesc Gs u n H C).traceWidth = 3068 := rfl

theorem accHeadDesc_piCount (Gs : List Pt3) (u : List Nat) (n : Nat) (H : List ℤ) (C : Pt3) :
    (accHeadDesc Gs u n H C).piCount = 201 := rfl

/-- ⚑ **FIVE NAMES, FIVE OBJECTS.** A registry lookup that resolved `-head` to `-srs` would serve a
descriptor with no head seam at all and every shape pin below would still pass —
`reference-a-display-name-is-not-a-key` records three wrong lookups in one day from exactly this. -/
theorem the_five_descriptors_do_not_share_a_name (As : List Pt3)
    (Gs : List Pt3) (u : List Nat) (n : Nat) (H : List ℤ) (C : Pt3) :
    accSegDesc.name ≠ (accHeadDesc Gs u n H C).name
    ∧ accFinalDesc.name ≠ (accHeadDesc Gs u n H C).name
    ∧ (accRoutedDesc As).name ≠ (accHeadDesc Gs u n H C).name
    ∧ (accSrsDesc Gs u n).name ≠ (accHeadDesc Gs u n H C).name := by
  rw [accHeadDesc_name, accRoutedDesc_name, accSrsDesc_name]
  refine ⟨by decide, by decide, by decide, by decide⟩

set_option maxHeartbeats 0 in
/-- ⚑ **TWELVE CONSTRAINTS, AND THE ROUTED 4 831 ARE A PREFIX.** `4 831 + 1 + 1 + 9 + 1`. A leg
lowers to at least one constraint (`lowerLeg_ne_nil`), so this count is a real pin on the leg list
and a dropped seam cannot hide in it. -/
theorem accHeadDesc_constraint_count (Gs : List Pt3) (u : List Nat) (n : Nat)
    (H : List ℤ) (C : Pt3) :
    (accHeadDesc Gs u n H C).constraints.length = 4476 + 96 + 192 + 64 + 3 + 12 := rfl

set_option maxHeartbeats 0 in
/-- ⚑ **THE SEAM IS NOT DECLARATIVE.** `proofBindDeclarative` counts seams that pin NEITHER the
program nor the commitment — the shape whose existential quantifies over every program and every
statement. This descriptor's count is ZERO, on the emitted object, in the authoring language, one
stage upstream of the bytes. -/
theorem the_head_seam_is_not_declarative (Gs : List Pt3) (u : List Nat) (n : Nat)
    (H : List ℤ) (C : Pt3) :
    Dregg2.Circuit.DescriptorIR2.proofBindDeclarative (accHeadDesc Gs u n H C) = 0 := rfl

/-! ### §11b — ⚠⚠ THE THIRD TRUSTED ITEM, CLASSIFIED: **theorem of the relation**, and what moved.

The accumulator's third trusted item reads *"a claim rebuilt around tampered challenges is accepted,
in-circuit exactly as natively."* It is asked of this section because §11 is the first rung that
could plausibly touch it. Classify it before pricing it.

## ⚑ IT IS A THEOREM OF THE RELATION, AND THEREFORE TERMINAL FOR ANY AIR OF THAT RELATION

The relation the accumulator checks is

    R(C, u⃗)  ⟺  C = Σ_r b_poly_coefficients(u⃗)_r · G_r

and `srsScaledAddends` is the *function* whose graph that is: for EVERY `u⃗′` there is exactly one
`C′ = f(u⃗′)` with `R(C′, u⃗′)`. So *"a rebuilt pair satisfies `R`"* is not a defect of the AIR — it
is what it means for `R` to be a function graph, and it is why the item's own wording says *"exactly
as natively"*: `mina-rust`'s `Ipa::Step::accumulator_check` accepts the rebuilt pair too. **No AIR
for `R`, at any width, on any field, can separate `(C, u⃗)` from `(f(u⃗′), u⃗′)`.** That half is
TERMINAL and no amount of work on this file moves it. ⚠ It is not *"undone work in a caveat's
clothes"* and must not be priced as though a bigger circuit would fix it.

## ⚑ WHAT IS TRANSMUTABLE IS THE TIE, AND §11 MOVED IT

The exploit `R`'s functionality permits is *presenting a rebuilt pair where the original was
expected*. That is a statement about what a VERIFIER accepts, not about `R`, and it has now changed
shape twice:

* §10 put `u⃗` in the DESCRIPTOR: the manifest is `srsScaledAddends Gs u⃗ n`, so a tampered `u⃗′` is a
  different manifest, a different descriptor and therefore a different VK. A rebuilt claim cannot be
  presented under the original descriptor's routing.
* §11 puts the HEAD in the same object. So under a FIXED `-head` descriptor a rebuilt claim `C′` is
  refused by the seam's `bound` congruence, elementwise, before the routing is even consulted.

⚑ **The residue is therefore exactly DESCRIPTOR SELECTION** — an attacker who can make a node
verify against a descriptor of their choosing can still present `(u⃗′, C′)` under a `-head`
descriptor that declares the honest head beside `C′`, because nothing in this file relates the
declared head to the declared manifest. Two things would close that and neither is cheap or hidden:
the seam's OFF-ROW half (a head proof that EXPOSES the pair — §11's named undone work), or the
scaling relation in-circuit (the deferred MSM, `PastaMsmBucketed.fused_at_step`'s `1 474 800`
complete additions on the UNSOUND multiply, so ~10² further out on this file's sound row).

⚠ **Say the standing plainly: item 3's premise is closed as a theorem, its exploit is narrowed to
descriptor selection, and descriptor selection is NOT closed here.** -/

/-! ### §11a — ⚑⚑ WHAT THE SEAM FORCES, AS A THEOREM ABOUT THE EMITTED `ProofBind`.

⚠ **SAY WHICH OBJECT.** These are statements about `headProofBind H C` — the `DescriptorIR2.ProofBind`
that `lowerBindLeg` actually emits into `(accHeadDesc …).constraints` — and not about the source
`BindLeg`, not about a re-spelling of it. `the_emitted_seam_is_the_lowered_leg` is the `rfl` that
makes them the same object; without it every theorem below would be true about a look-alike. -/

/-- The emitted seam. -/
def headProofBind (H : List ℤ) (C : Pt3) : Dregg2.Circuit.DescriptorIR2.ProofBind :=
  { guard := Dregg2.Exec.CircuitEmit.emitExpr (Dregg2.Circuit.Expr.var HEAD_OK)
  , commit := headCommitLanes.map Dregg2.Exec.CircuitEmit.emitExpr
  , vk := ((List.range HEAD_LANES).map
      (fun i => Dregg2.Circuit.Expr.var (HEAD_VK i))).map Dregg2.Exec.CircuitEmit.emitExpr
  , vkPin := some MINA_HEAD_VK_LANES
  , bound := .bound ((headBoundLanes H C).map Dregg2.Exec.CircuitEmit.emitExpr) }

/-- ⚑ **THE EMITTED SEAM IS THE LOWERED LEG** — one object, two spellings, joined by `rfl`. -/
theorem the_emitted_seam_is_the_lowered_leg (H : List ℤ) (C : Pt3) :
    Dregg2.Circuit.Emit.EffectLower.lowerLeg (headBindLeg H C)
      = [VmConstraint2.proofBind (headProofBind H C)] := rfl

/-- …and it is the ONLY `proofBind` the descriptor carries, so "the seam" is not ambiguous. -/
theorem the_head_descriptor_has_exactly_one_seam (Gs : List Pt3) (u : List Nat) (n : Nat)
    (H : List ℤ) (C : Pt3) :
    Dregg2.Circuit.DescriptorIR2.proofBindsOf (accHeadDesc Gs u n H C) = [headProofBind H C] := rfl

set_option maxHeartbeats 0 in
/-- ⚑ **THE PAIRS THE SEAM COMPARES, NAMED.** `zeroLanes` quantifies over `commit.zip bound`; this
is that list, spelled as *the nine head pairs, then the ninety-six claim pairs*. `rfl` — one object,
two spellings — so the theorem below needs no index projection between it and `ProofBind.holdsAt`. -/
theorem the_seam_pairs_are_the_head_then_the_claim (H : List ℤ) (C : Pt3)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv) :
    ((headProofBind H C).commit.map (fun e => e.eval env.loc)).zip
        (((headBoundLanes H C).map Dregg2.Exec.CircuitEmit.emitExpr).map
          (fun e => e.eval env.loc))
      = ((List.range HEAD_LANES).map (fun i => (env.loc (HEAD_STATE i), H.getD i 0)))
          ++ ((List.range (3 * SK)).map
                (fun j => (env.loc (ACC_X + j), ((coordLimb C j : Nat) : ℤ)))) := rfl

/-- ⚑⚑ **THE HEAD IS FORCED.** Under the guard, the row's `i`-th published head lane IS the declared
head's `i`-th lane, in BabyBear. This is the constraint item 2 asked for: it is in `constraints`,
`Ir2Air::eval` asserts the same polynomial, and nothing about it is a consumer's memory. The exhibit
that it can go red is `the_wrong_head_claim_is_refused_by_the_air` in the Rust tooth. -/
theorem the_head_seam_forces_the_declared_head (H : List ℤ) (C : Pt3)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (hh : (headProofBind H C).holdsAt env) (hg : env.loc HEAD_OK = 1)
    (i : Nat) (hi : i < HEAD_LANES) :
    env.loc (HEAD_STATE i) ≡ H.getD i 0 [ZMOD 2013265921] := by
  obtain ⟨-, -, hb⟩ := hh
  have hguard : (headProofBind H C).guard.eval env.loc = 1 := hg
  rw [hguard] at hb
  obtain ⟨-, hz⟩ := hb
  have hmem : (env.loc (HEAD_STATE i), H.getD i 0)
      ∈ ((headProofBind H C).commit.map (fun e => e.eval env.loc)).zip
          (((headBoundLanes H C).map Dregg2.Exec.CircuitEmit.emitExpr).map
            (fun e => e.eval env.loc)) := by
    rw [the_seam_pairs_are_the_head_then_the_claim]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  have h1 := hz _ hmem
  rw [one_mul] at h1
  exact Int.modEq_iff_dvd.mpr (by simpa using Int.modEq_iff_dvd.mp h1)

/-- ⚑⚑ **…AND SO IS THE CLAIM.** The row's `j`-th entry-accumulator limb is the declared claim's
`j`-th `coordLimb` digit. ⚠ Read this against §11's docblock: given the routing and the discharge
the entry accumulator was already determined as a POINT, so what this adds is the canonical
projective representative and the elementwise statement of the pair — the NEW content is the head
half above. -/
theorem the_head_seam_forces_the_declared_claim (H : List ℤ) (C : Pt3)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (hh : (headProofBind H C).holdsAt env) (hg : env.loc HEAD_OK = 1)
    (j : Nat) (hj : j < 3 * SK) :
    env.loc (ACC_X + j) ≡ ((coordLimb C j : Nat) : ℤ) [ZMOD 2013265921] := by
  obtain ⟨-, -, hb⟩ := hh
  have hguard : (headProofBind H C).guard.eval env.loc = 1 := hg
  rw [hguard] at hb
  obtain ⟨-, hz⟩ := hb
  have hmem : (env.loc (ACC_X + j), ((coordLimb C j : Nat) : ℤ))
      ∈ ((headProofBind H C).commit.map (fun e => e.eval env.loc)).zip
          (((headBoundLanes H C).map Dregg2.Exec.CircuitEmit.emitExpr).map
            (fun e => e.eval env.loc)) := by
    rw [the_seam_pairs_are_the_head_then_the_claim]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  have h1 := hz _ hmem
  rw [one_mul] at h1
  exact Int.modEq_iff_dvd.mpr (by simpa using Int.modEq_iff_dvd.mp h1)

/-- ⚑ **AND THE PROGRAM PIN IS FORCED TOO** — the attested `HEAD_VK` lane is the head descriptor's
fingerprint lane, which is what makes a re-emit of that descriptor a FLAG DAY here rather than a
silence. `forged_head_program_refused` is the exhibit. -/
theorem the_head_seam_forces_the_declared_program (H : List ℤ) (C : Pt3)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (hh : (headProofBind H C).holdsAt env) (hg : env.loc HEAD_OK = 1)
    (i : Nat) (hi : i < HEAD_LANES) :
    env.loc (HEAD_VK i) ≡ MINA_HEAD_VK_LANES.getD i 0 [ZMOD 2013265921] := by
  obtain ⟨-, hv, -⟩ := hh
  have hguard : (headProofBind H C).guard.eval env.loc = 1 := hg
  rw [hguard] at hv
  obtain ⟨-, hz⟩ := hv
  have hpairs : ((headProofBind H C).vk.map (fun e => e.eval env.loc)).zip MINA_HEAD_VK_LANES
      = (List.range HEAD_LANES).map
          (fun k => (env.loc (HEAD_VK k), MINA_HEAD_VK_LANES.getD k 0)) := rfl
  have hmem : (env.loc (HEAD_VK i), MINA_HEAD_VK_LANES.getD i 0)
      ∈ ((headProofBind H C).vk.map (fun e => e.eval env.loc)).zip MINA_HEAD_VK_LANES := by
    rw [hpairs]
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have h1 := hz _ hmem
  rw [one_mul] at h1
  exact Int.modEq_iff_dvd.mpr (by simpa using Int.modEq_iff_dvd.mp h1)

#assert_axioms acc_pi_layout
#assert_compiled pin_leg_counts
#assert_compiled dischargeLegs_length
#assert_axioms accFinalAir_extends_accSegAir
#assert_compiled accSegAir_mainRailOk
#assert_compiled accFinalAir_mainRailOk
#assert_compiled the_discharge_is_sixty_four_last_row_gates
#assert_compiled accSegDesc_constraint_count
#assert_compiled accFinalDesc_constraint_count
#assert_compiled the_two_descriptors_do_not_share_a_name
#assert_compiled the_two_descriptors_differ
#assert_compiled the_full_width_sum_needs_the_fold
#assert_compiled the_routing_tuple_used_to_not_fit_and_now_does
#assert_compiled the_split_remedy_costs_more_than_the_wide_table
#assert_compiled the_column_census
#assert_compiled the_multiply_carries_are_seven_hundred_forty_four
#assert_compiled the_row_boundary_is_two_hundred_eighty_eight
#assert_compiled the_outputs_are_scratch_slots
#assert_axioms rowV_forces
#assert_axioms threadedLadderV_forces
#assert_axioms terminalAccumulator_forces
#assert_axioms sVal_eq_zero
#assert_axioms discharged_is_the_identity
#assert_axioms accumulator_discharge_forced
#assert_axioms the_discharge_gate_is_refutable
#assert_axioms the_two_exhibits_differ_in_one_cell
#assert_axioms accRoutedDesc_constraints_eq
#assert_axioms accRoutedDesc_name
#assert_axioms traceOf_apply
#assert_axioms rowAt_mem
#assert_axioms addTupleOf_head
#assert_axioms addendRow_head
#assert_axioms addendRow_map_head
#assert_axioms flatMap_singleton_map
#assert_axioms filterMap_of_noAddendLookup
#assert_axioms sumL_congr
#assert_compiled the_routing_costs_one_column
#assert_compiled the_declared_tuple_is_the_priced_one
#assert_compiled addendTuple_length
#assert_axioms routedTables_ids_are_distinct
#assert_axioms accRoutedAir_extends_accFinalAir
#assert_axioms the_legs_do_not_depend_on_the_declared_addends
#assert_compiled accRoutedAir_mainRailOk
#assert_compiled accRoutedDesc_constraint_count
#assert_axioms the_three_descriptors_do_not_share_a_name
#assert_compiled the_routed_selector_census
#assert_axioms ridx_is_the_row_index
#assert_axioms addTupleOf_cons
#assert_axioms addend_manifest_key_unique
#assert_compiled only_the_routing_leg_targets_the_addend_table
#assert_axioms lowerAir_constraints
#assert_axioms accRoutedAir_legs
#assert_axioms routed_constraints_split
#assert_axioms routing_leg_filterMap
#assert_compiled addend_lookupLog_is_rowMap
#assert_compiled addend_balance
#assert_compiled the_balance_forces_the_row_count
#assert_compiled addend_is_its_declared_addend
#assert_axioms range_map_pointwise
#assert_compiled addend_limbs_are_declared
#assert_axioms sVal_is_declVal
#assert_compiled addend_value_is_declared
#assert_axioms chain_is_the_declared_chain
#assert_compiled accumulator_discharge_forced_on_declared_addends
#assert_axioms the_routing_key_separates_rows
#assert_compiled the_cell_cap_counts_the_declared_multiset_and_not_the_allocation
#assert_compiled the_full_srs_routing_needs_no_cap_to_move
#assert_compiled the_demonstration_manifest_is_far_inside_every_cap
#assert_axioms redPt_lt
#assert_axioms srsScaledAddends_length
#assert_axioms srs_declared_addend_is_the_negated_scalar_multiple
#assert_axioms sumL_limbs
#assert_axioms nat_mod_split
#assert_axioms declVal_of_lt
#assert_axioms declAddend_of_getD
#assert_axioms declAddend_of_srsScaled
#assert_axioms accSrsDesc_name
#assert_axioms the_four_descriptors_do_not_share_a_name
#assert_axioms the_srs_descriptor_differs_from_the_routed_one_only_in_its_name_and_its_manifest
#assert_axioms srs_balance_is_routed_balance
#assert_compiled accumulator_discharge_forced_on_srs_scaled_addends
#assert_axioms the_forced_chain_adds_the_scalar_multiples
#assert_axioms smulV_at_zero
#assert_compiled the_challenge_order_is_the_o1labs_one
#assert_compiled the_coefficients_are_not_constant_in_the_challenges
#assert_axioms the_head_seam_costs_nineteen_columns
#assert_axioms head_pi_layout
#assert_compiled headStatePinLegs_length
#assert_compiled the_head_vk_pin_is_nine_lanes
#assert_compiled headCommitLanes_length
#assert_axioms headBoundLanes_length
#assert_axioms headedTables_ids_are_the_routed_ones
#assert_axioms accHeadAir_extends_accRoutedAir
#assert_compiled accHeadAir_mainRailOk
#assert_axioms the_head_selector_census
#assert_axioms accHeadDesc_name
#assert_axioms the_five_descriptors_do_not_share_a_name
#assert_axioms accHeadDesc_constraint_count
#assert_axioms the_head_seam_is_not_declarative
#assert_axioms the_emitted_seam_is_the_lowered_leg
#assert_axioms the_head_descriptor_has_exactly_one_seam
#assert_axioms the_seam_pairs_are_the_head_then_the_claim
#assert_axioms the_head_seam_forces_the_declared_head
#assert_axioms the_head_seam_forces_the_declared_claim
#assert_axioms the_head_seam_forces_the_declared_program

#assert_compiled the_step_srs_is_two_to_the_sixteen
end Dregg2.Circuit.Emit.MinaAccumulatorAir
