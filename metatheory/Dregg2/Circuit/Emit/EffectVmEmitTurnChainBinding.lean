/-
# `EffectVmEmitTurnChainBinding` — the deployed whole-history TURN-CHAIN binding,
# emitted from Lean (law #1).

`circuit-prove/src/ivc_turn_chain.rs::TurnChainBindingAir` is the sequential binding
proof a whole-history verifier consumes.  One row carries

  `[old_root, new_root, acc_in, acc_out, idx, is_real, real_count]`

and the hand-authored Rust AIR appends a 352-column inlined Poseidon2 permutation witness
(width 359).  The IR-v2 descriptor below expresses the SAME statement through the shared,
Lean-described Poseidon2 chip lookup: seven exposed output lanes replace the private inlined
permutation block, so the main trace is 14 columns while the permutation AIR remains a declared
shared-table obligation.  This is the same compaction already used by the IVC-state-transition,
bundle-fold, and cross-side emitters; it does not weaken the hash equation.

## Exact constraint inventory (the Rust AIR's 14 sites)

1. `new_root[i] = old_root[i+1]` (transition) — the temporal tooth.
2. `old_root[0] = pi[genesis_root]`.
3. `new_root[last] = pi[final_root]`.
4. `acc_in[0] = 0`.
5. `acc_out[i] = acc_in[i+1]` (transition).
6. `acc_out[last] = pi[chain_digest]`.
7. `acc_out = Poseidon2([acc_in, old_root, new_root, idx], arity=4)` on every row.
8. `idx[0] = 0`.
9. `idx[i+1] = idx[i] + 1` (transition).
10. `is_real` is boolean on EVERY row.
11. `next_is_real * (1 - is_real) = 0` (transition; real rows precede padding).
12. `real_count[0] = is_real[0]`.
13. `real_count[i+1] = real_count[i] + is_real[i+1]` (transition).
14. `real_count[last] = pi[num_turns]`.

The five inter-row laws are `windowGate`s with `onTransition := true`.  In particular, root
continuity and index increment DO fire across the real-to-padding boundary: the deployed rotated
trace pads with `(old_root,new_root)=(final_root,final_root)`, continues the index, and continues
the genuine hash chain.  The duplicate-last-row padding argument in
`EffectVmEmitIvcStateTransition` therefore does not apply here.

One deliberate grammar detail is load-bearing: constraint 10 uses an every-row `windowGate`
(`onTransition := false`) whose body reads only `loc`.  A v2 `.base (.gate ...)` is evaluated by
`Ir2Air` under `when_transition()` and would be vacuous on the last row, unlike Rust's bare
`builder.assert_bool`.  The every-row form gives exact semantic parity without extending IR-v2.

## Proof ladder in this module

* Rung 0: the descriptor shape and emitted bytes are pinned.
* Rung 1: `turnChain_descriptor_refines_rust_air` derives the exact Rust row semantics from any
  satisfying descriptor window and a sound shared Poseidon2 chip table.
* Rung 2: `turnChain_descriptor_iff_rust_air` proves equivalence against the canonical genuine
  chip row for that window — every emitted constraint iff the corresponding Rust AIR site.
* Non-vacuity: `honestTrace_satisfies` is a four-row witness with two real rows followed by two
  padding rows.  Three concrete forged windows (continuity, index, real-count) are formally UNSAT.
-/
import Dregg2.Circuit.ChipNarrowLookup
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Tactics

namespace Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.ChipNarrowLookup
  (narrowTable narrowRow narrowRow_chipRow chip_lookup_narrow_sound_of_wide_table)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option autoImplicit false

/-! ## §1 — Main-trace and public-input layout. -/

namespace Chain

def OLD_ROOT : Nat := 0
def NEW_ROOT : Nat := 1
def ACC_IN : Nat := 2
def ACC_OUT : Nat := 3
def IDX : Nat := 4
def IS_REAL : Nat := 5
def REAL_COUNT : Nat := 6

/-- Seven scalar columns.  The seven exposed Poseidon2 output lanes 1..7 the WIDE `TID_P2` tuple
carried are GONE (E7 narrowing, `ChipNarrowLookup.lean`): they sat at lane positions 18..24 of the
25-wide tuple and entered no soundness conclusion.  Lane 0 is `ACC_OUT` and stays. -/
def WIDTH : Nat := 7

def PI_GENESIS_ROOT : Nat := 0
def PI_FINAL_ROOT : Nat := 1
def PI_NUM_TURNS : Nat := 2
def PI_CHAIN_DIGEST : Nat := 3
def PI_COUNT : Nat := 4

end Chain

/-! ## §2 — The fourteen emitted constraints. -/

open WindowExpr (loc nxt)

/-- Temporal continuity: `new_root[i] = old_root[i+1]`. -/
def rootContinuity : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body := .add (loc Chain.NEW_ROOT) (.mul (.const (-1)) (nxt Chain.OLD_ROOT)) }

/-- First state endpoint. -/
def firstOldRootBind : VmConstraint2 :=
  .base (.piBinding .first Chain.OLD_ROOT Chain.PI_GENESIS_ROOT)

/-- Last state endpoint. -/
def lastNewRootBind : VmConstraint2 :=
  .base (.piBinding .last Chain.NEW_ROOT Chain.PI_FINAL_ROOT)

/-- The digest chain starts from zero. -/
def firstAccZero : VmConstraint2 :=
  .base (.boundary .first (.var Chain.ACC_IN))

/-- Digest continuity: `acc_out[i] = acc_in[i+1]`. -/
def accContinuity : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body := .add (loc Chain.ACC_OUT) (.mul (.const (-1)) (nxt Chain.ACC_IN)) }

/-- The final digest is public. -/
def lastAccBind : VmConstraint2 :=
  .base (.piBinding .last Chain.ACC_OUT Chain.PI_CHAIN_DIGEST)

/-- Per-row TURN-CHAIN hash.  The preimage order is exactly
`[acc_in, old_root, new_root, idx]`; there is NO IVC domain tag and NO `old_hash`. -/
def perRowHash : VmConstraint2 :=
  .lookup
    { table := poseidon2narrow
    , tuple := chipLookupTupleNarrow
        [.var Chain.ACC_IN, .var Chain.OLD_ROOT, .var Chain.NEW_ROOT, .var Chain.IDX]
        Chain.ACC_OUT }

/-- The positional index starts at zero. -/
def firstIdxZero : VmConstraint2 :=
  .base (.boundary .first (.var Chain.IDX))

/-- Positional counter: `idx[i+1] = idx[i] + 1`. -/
def idxIncrement : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body :=
        .add (nxt Chain.IDX)
          (.add (.mul (.const (-1)) (loc Chain.IDX)) (.const (-1))) }

/-- `is_real * (is_real - 1) = 0` on EVERY row.  This is intentionally an every-row
`windowGate`, not `.base (.gate ...)`: the latter is transition-only in IR-v2. -/
def isRealBoolean : VmConstraint2 :=
  .windowGate
    { onTransition := false
    , body :=
        .mul (loc Chain.IS_REAL)
          (.add (loc Chain.IS_REAL) (.const (-1))) }

/-- Real rows form a prefix: forbid a `0 -> 1` transition. -/
def realMonotone : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body :=
        .mul (nxt Chain.IS_REAL)
          (.add (.const 1) (.mul (.const (-1)) (loc Chain.IS_REAL))) }

/-- Seed the real-row counter. -/
def firstRealCount : VmConstraint2 :=
  .base (.boundary .first
    (.add (.var Chain.REAL_COUNT) (.mul (.const (-1)) (.var Chain.IS_REAL))))

/-- Accumulate the next row's `is_real`, matching the Rust AIR exactly. -/
def realCountAccum : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body :=
        .add (nxt Chain.REAL_COUNT)
          (.add (.mul (.const (-1)) (loc Chain.REAL_COUNT))
                (.mul (.const (-1)) (nxt Chain.IS_REAL))) }

/-- The published number of turns is the final cumulative real-row count. -/
def lastRealCountBind : VmConstraint2 :=
  .base (.piBinding .last Chain.REAL_COUNT Chain.PI_NUM_TURNS)

def turnChainConstraints : List VmConstraint2 :=
  [ rootContinuity
  , firstOldRootBind
  , lastNewRootBind
  , firstAccZero
  , accContinuity
  , lastAccBind
  , perRowHash
  , firstIdxZero
  , idxIncrement
  , isRealBoolean
  , realMonotone
  , firstRealCount
  , realCountAccum
  , lastRealCountBind ]

/-- The law-#1 replacement for `TurnChainBindingAir`. -/
def turnChainBindingDescriptor : EffectVmDescriptor2 :=
  { name := "dregg-turn-chain-binding-v2"
  , traceWidth := Chain.WIDTH
  , piCount := Chain.PI_COUNT
  , tables := []
  , constraints := turnChainConstraints
  , hashSites := []
  , ranges := [] }

/-! ## §3 — Rung 0: shape and wire tripwires. -/

#guard Chain.WIDTH == 7
-- The narrowing dropped exactly CHIP_OUT_LANES - 1 = 7 main columns for the same forced
-- digest equation.
#guard Chain.WIDTH + (CHIP_OUT_LANES - 1) == 14
#guard poseidon2narrow.wireId == 8
#guard turnChainBindingDescriptor.piCount == 4
#guard turnChainConstraints.length == 14
#guard (turnChainConstraints.filter (fun c => match c with
  | .windowGate _ => true | _ => false)).length == 6
#guard (turnChainConstraints.filter (fun c => match c with
  | .windowGate w => !w.onTransition | _ => false)).length == 1
#guard (turnChainConstraints.filter (fun c => match c with
  | .lookup _ => true | _ => false)).length == 1
#guard (turnChainConstraints.filter (fun c => match c with
  | .base (.piBinding _ _ _) => true | _ => false)).length == 4
#guard (turnChainConstraints.filter (fun c => match c with
  | .base (.boundary _ _) => true | _ => false)).length == 3
#guard (emitVmJson2 turnChainBindingDescriptor).startsWith
  "{\"name\":\"dregg-turn-chain-binding-v2\",\"ir\":2"

/-- Byte-pinned law-#1 artifact.  Rust's eventual cutover includes this exact string rather than
re-authoring any of the constraints below. -/
def TURN_CHAIN_BINDING_GOLDEN : String :=
  "{\"name\":\"dregg-turn-chain-binding-v2\",\"ir\":2,\"trace_width\":7,\"public_input_count\":4,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":0}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":1,\"pi_index\":1},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":2}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":2}}}},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":3,\"pi_index\":3},{\"t\":\"lookup\",\"table\":8,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":4},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":3}]},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":4}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":5},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":5},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":5}}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":6}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":5}}}}},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":6,\"pi_index\":2}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 turnChainBindingDescriptor == TURN_CHAIN_BINDING_GOLDEN

/-! ## §4 — The exact Rust AIR row semantics. -/

/-- The ordered four-felt preimage the deployed turn-chain hash consumes. -/
def hashInputs (env : VmRowEnv) : List ℤ :=
  [env.loc Chain.ACC_IN, env.loc Chain.OLD_ROOT, env.loc Chain.NEW_ROOT, env.loc Chain.IDX]

/-- A direct field-level transcription of the fourteen `TurnChainBindingAir::eval` sites.
Every arithmetic assertion is stated modulo the BabyBear prime, exactly as the AIR; the hash
site is the abstract genuine arity-4 Poseidon2 function. -/
def RustTurnChainRow (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) : Prop :=
  (isLast = false →
      env.loc Chain.NEW_ROOT - env.nxt Chain.OLD_ROOT ≡ 0 [ZMOD 2013265921]) ∧
  (isFirst = true →
      env.loc Chain.OLD_ROOT ≡ env.pub Chain.PI_GENESIS_ROOT [ZMOD 2013265921]) ∧
  (isLast = true →
      env.loc Chain.NEW_ROOT ≡ env.pub Chain.PI_FINAL_ROOT [ZMOD 2013265921]) ∧
  (isFirst = true → env.loc Chain.ACC_IN ≡ 0 [ZMOD 2013265921]) ∧
  (isLast = false →
      env.loc Chain.ACC_OUT - env.nxt Chain.ACC_IN ≡ 0 [ZMOD 2013265921]) ∧
  (isLast = true →
      env.loc Chain.ACC_OUT ≡ env.pub Chain.PI_CHAIN_DIGEST [ZMOD 2013265921]) ∧
  env.loc Chain.ACC_OUT = hash (hashInputs env) ∧
  (isFirst = true → env.loc Chain.IDX ≡ 0 [ZMOD 2013265921]) ∧
  (isLast = false →
      env.nxt Chain.IDX + (-env.loc Chain.IDX + -1) ≡ 0 [ZMOD 2013265921]) ∧
  (env.loc Chain.IS_REAL * (env.loc Chain.IS_REAL - 1) ≡ 0 [ZMOD 2013265921]) ∧
  (isLast = false →
      env.nxt Chain.IS_REAL * (1 - env.loc Chain.IS_REAL) ≡ 0 [ZMOD 2013265921]) ∧
  (isFirst = true →
      env.loc Chain.REAL_COUNT - env.loc Chain.IS_REAL ≡ 0 [ZMOD 2013265921]) ∧
  (isLast = false →
      env.nxt Chain.REAL_COUNT + (-env.loc Chain.REAL_COUNT + -env.nxt Chain.IS_REAL)
        ≡ 0 [ZMOD 2013265921]) ∧
  (isLast = true →
      env.loc Chain.REAL_COUNT ≡ env.pub Chain.PI_NUM_TURNS [ZMOD 2013265921])

/-- The emitted descriptor's constraint-set denotation on one row window. -/
def turnChainWindowHolds (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ turnChainBindingDescriptor.constraints,
    c.holdsAt hash tf env isFirst isLast

/-! ## §5 — Hash-table realization and Rung 1/Rung 2. -/

/-- The seven permutation lanes of the PHYSICAL chip row.  After the E7 narrowing they are no
longer main-trace columns — they live only inside the chip, so the row model carries them as the
canonical zero block. -/
def hashLanes : List ℤ := List.replicate (CHIP_OUT_LANES - 1) 0

/-- The canonical genuine WIDE chip table for one row window: exactly the arity-4 permutation row
whose input is the turn-chain preimage and whose output lane 0 is `hash (hashInputs env)`.
This is a concrete table, not an assumed carrier. -/
def canonicalRowWide (hash : List ℤ → ℤ) (env : VmRowEnv) : List (List ℤ) :=
  [chipRow hash (hashInputs env) hashLanes]

/-- ONE physical chip serving TWO buses: `.poseidon2` carries the genuine 25-wide row and the NARROW
bus (`poseidon2narrow = .custom 3`) carries its 18-prefix — exactly the deployed Rust `narrow_hist`
serving. -/
def canonicalRowTf (hash : List ℤ → ℤ) (env : VmRowEnv) : TraceFamily := fun tid =>
  match tid with
  | .poseidon2 => canonicalRowWide hash env
  | .custom 3  => narrowTable (canonicalRowWide hash env)
  | _ => []

/-- The canonical family wires the narrow bus to the 18-prefix of the wide chip table
(definitional). -/
theorem canonicalRowTf_narrow_wire (hash : List ℤ → ℤ) (env : VmRowEnv) :
    canonicalRowTf hash env poseidon2narrow = narrowTable (canonicalRowTf hash env .poseidon2) :=
  rfl

/-- The canonical row table is genuinely chip-sound, by construction. -/
theorem canonicalRowTf_chipSound (hash : List ℤ → ℤ) (env : VmRowEnv) :
    ChipTableSound hash (canonicalRowTf hash env .poseidon2) := by
  intro r hr
  simp only [canonicalRowTf, canonicalRowWide, List.mem_singleton] at hr
  subst r
  refine ⟨hashInputs env, hashLanes, ?_, ?_, rfl⟩
  · show Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted (hashInputs env).length
    simp only [hashInputs]
    chip_arity_admitted
  · simp [hashLanes, CHIP_OUT_LANES]

/-- Completeness of the per-row chip lookup against the canonical genuine row. -/
theorem perRowHash_complete (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hhash : env.loc Chain.ACC_OUT = hash (hashInputs env)) :
    perRowHash.holdsAt hash (canonicalRowTf hash env) env false false := by
  simp only [perRowHash, VmConstraint2.holdsAt, Lookup.holdsAt, canonicalRowTf, canonicalRowWide,
    poseidon2narrow, narrowTable, List.map_cons, List.map_nil]
  rw [narrowRow_chipRow hash (hashInputs env) hashLanes (by simp [hashInputs, CHIP_RATE])]
  rw [show hashInputs env =
    [env.loc Chain.ACC_IN, env.loc Chain.OLD_ROOT, env.loc Chain.NEW_ROOT, env.loc Chain.IDX] from rfl]
  simp [chipLookupTupleNarrow, chipRowNarrow, padToE, padTo,
    EmittedExpr.eval, CHIP_RATE, hhash, hashInputs]

/-- The canonical lookup is EXACTLY the genuine per-row hash equation. -/
theorem perRowHash_canonical_iff (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) :
    perRowHash.holdsAt hash (canonicalRowTf hash env) env isFirst isLast ↔
      env.loc Chain.ACC_OUT = hash (hashInputs env) := by
  constructor
  · intro h
    have hs := canonicalRowTf_chipSound hash env
    simp only [perRowHash, VmConstraint2.holdsAt, Lookup.holdsAt] at h
    rw [canonicalRowTf_narrow_wire hash env] at h
    have hh := chip_lookup_narrow_sound_of_wide_table hash (canonicalRowTf hash env .poseidon2) hs
      env.loc [.var Chain.ACC_IN, .var Chain.OLD_ROOT, .var Chain.NEW_ROOT, .var Chain.IDX]
      Chain.ACC_OUT (by chip_arity_admitted) h
    simpa [hashInputs, EmittedExpr.eval] using hh
  · intro h
    exact perRowHash_complete hash env h

/-- **Rung 1 (functional soundness).** A satisfying emitted row window over any SOUND shared
Poseidon2 chip table enforces every one of the fourteen Rust AIR sites. -/
theorem turnChain_descriptor_refines_rust_air
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (hchip : ChipTableSound hash (tf .poseidon2))
    (hwire : tf poseidon2narrow = narrowTable (tf .poseidon2))
    (h : turnChainWindowHolds hash tf env isFirst isLast) :
    RustTurnChainRow hash env isFirst isLast := by
  have hh : env.loc Chain.ACC_OUT = hash (hashInputs env) := by
    have hc := h perRowHash (by simp [turnChainBindingDescriptor, turnChainConstraints])
    simp only [perRowHash, VmConstraint2.holdsAt, Lookup.holdsAt] at hc
    rw [hwire] at hc
    have hs := chip_lookup_narrow_sound_of_wide_table hash (tf .poseidon2) hchip env.loc
      [.var Chain.ACC_IN, .var Chain.OLD_ROOT, .var Chain.NEW_ROOT, .var Chain.IDX]
      Chain.ACC_OUT (by chip_arity_admitted) hc
    simpa [hashInputs, EmittedExpr.eval] using hs
  have hroot := h rootContinuity (by simp [turnChainBindingDescriptor, turnChainConstraints])
  have hold := h firstOldRootBind (by simp [turnChainBindingDescriptor, turnChainConstraints])
  have hnew := h lastNewRootBind (by simp [turnChainBindingDescriptor, turnChainConstraints])
  have ha0 := h firstAccZero (by simp [turnChainBindingDescriptor, turnChainConstraints])
  have hacc := h accContinuity (by simp [turnChainBindingDescriptor, turnChainConstraints])
  have haccl := h lastAccBind (by simp [turnChainBindingDescriptor, turnChainConstraints])
  have hi0 := h firstIdxZero (by simp [turnChainBindingDescriptor, turnChainConstraints])
  have hidx := h idxIncrement (by simp [turnChainBindingDescriptor, turnChainConstraints])
  have hbool := h isRealBoolean (by simp [turnChainBindingDescriptor, turnChainConstraints])
  have hmono := h realMonotone (by simp [turnChainBindingDescriptor, turnChainConstraints])
  have hcount0 := h firstRealCount (by simp [turnChainBindingDescriptor, turnChainConstraints])
  have hcount := h realCountAccum (by simp [turnChainBindingDescriptor, turnChainConstraints])
  have hcountl := h lastRealCountBind (by simp [turnChainBindingDescriptor, turnChainConstraints])
  unfold RustTurnChainRow
  simp only [rootContinuity, accContinuity, idxIncrement, isRealBoolean, realMonotone,
    realCountAccum, VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
    if_true, neg_mul, one_mul] at hroot hacc hidx hbool hmono hcount
  simp only [firstOldRootBind, lastNewRootBind, firstAccZero, lastAccBind, firstIdxZero,
    firstRealCount, lastRealCountBind, VmConstraint2.holdsAt, VmConstraint.holdsVm,
    EmittedExpr.eval, neg_mul, one_mul] at hold hnew ha0 haccl hi0 hcount0 hcountl
  refine ⟨?_, hold, hnew, ha0, ?_, haccl, hh, hi0, ?_, ?_, ?_, ?_, ?_, hcountl⟩
  · simpa only [sub_eq_add_neg] using hroot
  · simpa only [sub_eq_add_neg, add_assoc] using hacc
  · simpa only [neg_mul, one_mul] using hidx
  · simpa only [sub_eq_add_neg, Bool.false_eq_true, ↓reduceIte] using hbool
  · simpa only [sub_eq_add_neg] using hmono
  · simpa only [sub_eq_add_neg] using hcount0
  · simpa only [neg_mul, one_mul] using hcount

/-- **Rung 2 (semantic equivalence).** Against the canonical genuine chip row for this window,
the emitted descriptor's FULL constraint set is equivalent to the exact fourteen-site Rust AIR
semantics.  No constraint is added, omitted, or carried only as unconstrained metadata. -/
theorem turnChain_descriptor_iff_rust_air
    (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool) :
    turnChainWindowHolds hash (canonicalRowTf hash env) env isFirst isLast ↔
      RustTurnChainRow hash env isFirst isLast := by
  constructor
  · exact turnChain_descriptor_refines_rust_air hash (canonicalRowTf hash env) env
      isFirst isLast (canonicalRowTf_chipSound hash env) (canonicalRowTf_narrow_wire hash env)
  · intro hr c hc
    unfold RustTurnChainRow at hr
    rcases hr with ⟨hroot, hold, hnew, ha0, hacc, haccl, hhash, hi0, hidx, hbool,
      hmono, hcount0, hcount, hcountl⟩
    simp only [turnChainBindingDescriptor, turnChainConstraints, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [rootContinuity, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
        WindowExpr.eval, sub_eq_add_neg] using hroot
    · exact hold
    · exact hnew
    · exact ha0
    · simpa [accContinuity, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
        WindowExpr.eval, sub_eq_add_neg, add_assoc] using hacc
    · exact haccl
    · exact (perRowHash_canonical_iff hash env isFirst isLast).mpr hhash
    · exact hi0
    · simpa [idxIncrement, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
        WindowExpr.eval] using hidx
    · simpa [isRealBoolean, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
        WindowExpr.eval, sub_eq_add_neg] using hbool
    · simpa [realMonotone, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
        WindowExpr.eval, sub_eq_add_neg] using hmono
    · simpa [firstRealCount, VmConstraint2.holdsAt, VmConstraint.holdsVm,
        EmittedExpr.eval, sub_eq_add_neg] using hcount0
    · simpa [realCountAccum, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
        WindowExpr.eval] using hcount
    · exact hcountl

/-! ## §6 — The three requested adversarial teeth. -/

theorem turnChain_rejects_broken_continuity
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst : Bool)
    (hnew : 0 ≤ env.loc Chain.NEW_ROOT ∧ env.loc Chain.NEW_ROOT < 2013265921)
    (hold : 0 ≤ env.nxt Chain.OLD_ROOT ∧ env.nxt Chain.OLD_ROOT < 2013265921)
    (hbad : env.loc Chain.NEW_ROOT ≠ env.nxt Chain.OLD_ROOT) :
    ¬ turnChainWindowHolds hash tf env isFirst false := by
  intro h
  have hc := h rootContinuity (by simp [turnChainBindingDescriptor, turnChainConstraints])
  simp only [rootContinuity, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
    WindowExpr.eval, ↓reduceIte] at hc
  exact EffectVmEmitTransfer.not_modEq_zero_of_canon
    (x := env.loc Chain.NEW_ROOT + -1 * env.nxt Chain.OLD_ROOT)
    (a := env.loc Chain.NEW_ROOT) (b := env.nxt Chain.OLD_ROOT)
    (by ring) hnew hold hbad (hc trivial)

theorem turnChain_rejects_bad_idx_step
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst : Bool)
    (hnext : 0 ≤ env.nxt Chain.IDX ∧ env.nxt Chain.IDX < 2013265921)
    (hexpect : 0 ≤ env.loc Chain.IDX + 1 ∧ env.loc Chain.IDX + 1 < 2013265921)
    (hbad : env.nxt Chain.IDX ≠ env.loc Chain.IDX + 1) :
    ¬ turnChainWindowHolds hash tf env isFirst false := by
  intro h
  have hc := h idxIncrement (by simp [turnChainBindingDescriptor, turnChainConstraints])
  simp only [idxIncrement, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
    WindowExpr.eval, ↓reduceIte] at hc
  exact EffectVmEmitTransfer.not_modEq_zero_of_canon
    (x := env.nxt Chain.IDX + (-1 * env.loc Chain.IDX + -1))
    (a := env.nxt Chain.IDX) (b := env.loc Chain.IDX + 1)
    (by ring) hnext hexpect hbad (hc trivial)

theorem turnChain_rejects_bad_real_count
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst : Bool)
    (hnext : 0 ≤ env.nxt Chain.REAL_COUNT ∧ env.nxt Chain.REAL_COUNT < 2013265921)
    (hexpect : 0 ≤ env.loc Chain.REAL_COUNT + env.nxt Chain.IS_REAL ∧
      env.loc Chain.REAL_COUNT + env.nxt Chain.IS_REAL < 2013265921)
    (hbad : env.nxt Chain.REAL_COUNT ≠
      env.loc Chain.REAL_COUNT + env.nxt Chain.IS_REAL) :
    ¬ turnChainWindowHolds hash tf env isFirst false := by
  intro h
  have hc := h realCountAccum (by simp [turnChainBindingDescriptor, turnChainConstraints])
  simp only [realCountAccum, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
    WindowExpr.eval, ↓reduceIte] at hc
  exact EffectVmEmitTransfer.not_modEq_zero_of_canon
    (x := env.nxt Chain.REAL_COUNT +
      (-1 * env.loc Chain.REAL_COUNT + -1 * env.nxt Chain.IS_REAL))
    (a := env.nxt Chain.REAL_COUNT)
    (b := env.loc Chain.REAL_COUNT + env.nxt Chain.IS_REAL)
    (by ring) hnext hexpect hbad (hc trivial)

/-! ## §7 — Concrete honest and forged witnesses (non-vacuity). -/

def rowOf (xs : List ℤ) : Assignment := fun i => xs.getD i 0

/-- A deliberately simple abstract hash for the executable witness.  The chip table below is
still genuinely `ChipTableSound` for it; cryptographic strength is irrelevant to SAT non-vacuity. -/
def hash99 : List ℤ → ℤ := fun _ => 99

def honest0 : Assignment := rowOf [10, 20, 0, 99, 0, 1, 1]
def honest1 : Assignment := rowOf [20, 30, 99, 99, 1, 1, 2]
def pad0 : Assignment := rowOf [30, 30, 99, 99, 2, 0, 2]
def pad1 : Assignment := rowOf [30, 30, 99, 99, 3, 0, 2]
def honestPub : Assignment := rowOf [10, 30, 2, 99]

/-- The PHYSICAL 25-wide chip row a trace row names: the 18-wide narrow key the emitted lookup now
reads, extended by the seven permutation lanes the chip still witnesses internally. -/
def chipTupleAt (a : Assignment) : List ℤ :=
  (chipLookupTupleNarrow
    [.var Chain.ACC_IN, .var Chain.OLD_ROOT, .var Chain.NEW_ROOT, .var Chain.IDX]
    Chain.ACC_OUT).map (·.eval a) ++ List.replicate (CHIP_OUT_LANES - 1) 0

def honestChipTbl : List (List ℤ) :=
  [chipTupleAt honest0, chipTupleAt honest1, chipTupleAt pad0, chipTupleAt pad1]

def honestTf : TraceFamily := fun tid =>
  match tid with
  | .poseidon2 => honestChipTbl
  | .custom 3  => narrowTable honestChipTbl
  | _ => []

/-- The honest family wires the narrow bus to the 18-prefix of its wide chip table
(definitional). -/
theorem honestTf_narrow_wire :
    honestTf poseidon2narrow = narrowTable (honestTf .poseidon2) := rfl

def honestTrace : VmTrace :=
  { rows := [honest0, honest1, pad0, pad1]
  , pub := honestPub
  , tf := honestTf }

#guard honestTrace.rows.length == 4
#guard honest0 Chain.NEW_ROOT == honest1 Chain.OLD_ROOT
#guard honest1 Chain.NEW_ROOT == pad0 Chain.OLD_ROOT
#guard pad0 Chain.NEW_ROOT == pad1 Chain.OLD_ROOT
#guard honest1 Chain.IDX + 1 == pad0 Chain.IDX
#guard pad0 Chain.IDX + 1 == pad1 Chain.IDX
#guard honest1 Chain.REAL_COUNT == pad0 Chain.REAL_COUNT
#guard pad0 Chain.REAL_COUNT == pad1 Chain.REAL_COUNT
#guard pad1 Chain.REAL_COUNT == honestPub Chain.PI_NUM_TURNS
#eval (honestTrace.rows.length, honestTrace.pub Chain.PI_NUM_TURNS,
  honestTrace.pub Chain.PI_CHAIN_DIGEST)

theorem memOpsOf_turnChain : memOpsOf turnChainBindingDescriptor = [] := rfl

theorem mapOpsOf_turnChain : mapOpsOf turnChainBindingDescriptor = [] := rfl

theorem memLog_turnChain (t : VmTrace) : memLog turnChainBindingDescriptor t = [] := by
  simp [memLog, memOpsOf_turnChain]

theorem mapLog_turnChain (t : VmTrace) : mapLog turnChainBindingDescriptor t = [] := by
  simp [mapLog, mapOpsOf_turnChain]

theorem honestTf_chipSound : ChipTableSound hash99 (honestTf .poseidon2) := by
  intro r hr
  simp only [honestTf, honestChipTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨[0, 10, 20, 0], List.replicate 7 0, by decide, by decide, by decide⟩
  · exact ⟨[99, 20, 30, 1], List.replicate 7 0, by decide, by decide, by decide⟩
  · exact ⟨[99, 30, 30, 2], List.replicate 7 0, by decide, by decide, by decide⟩
  · exact ⟨[99, 30, 30, 3], List.replicate 7 0, by decide, by decide, by decide⟩

/-- Four rows (two real, two padding) satisfy the FULL emitted descriptor.  This directly
demonstrates that continuity, index increment, and hash continuation are padding-safe. -/
theorem honestTrace_satisfies :
    Satisfied2 hash99 turnChainBindingDescriptor (fun _ => 0) (fun _ => (0, 0)) [] honestTrace where
  rowConstraints := by
    intro i hi c hc
    have hi4 : i < 4 := by simpa [honestTrace] using hi
    simp only [turnChainBindingDescriptor] at hc
    interval_cases i <;> fin_cases hc <;>
      norm_num [rootContinuity, firstOldRootBind, lastNewRootBind, firstAccZero,
        accContinuity, lastAccBind, perRowHash, firstIdxZero, idxIncrement, isRealBoolean,
        realMonotone, firstRealCount, realCountAccum, lastRealCountBind,
        VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
        WindowExpr.eval, Lookup.holdsAt, honestTrace, honestTf, honestChipTbl, chipTupleAt,
        poseidon2narrow, narrowTable, narrowRow,
        honest0, honest1, pad0, pad1, honestPub, rowOf, envAt, zeroAsg,
        chipLookupTupleNarrow, padToE, padTo, EmittedExpr.eval, CHIP_RATE,
        CHIP_OUT_LANES, Chain.OLD_ROOT, Chain.NEW_ROOT, Chain.ACC_IN, Chain.ACC_OUT,
        Chain.IDX, Chain.IS_REAL, Chain.REAL_COUNT, Chain.PI_GENESIS_ROOT,
        Chain.PI_FINAL_ROOT, Chain.PI_NUM_TURNS, Chain.PI_CHAIN_DIGEST] at * <;>
      try decide
  rowHashes := by intro i _; trivial
  rowRanges := by
    intro i _ r hr
    simp [turnChainBindingDescriptor] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by
    intro op hop
    rw [memLog_turnChain] at hop
    simp at hop
  memDisciplined := by
    rw [memLog_turnChain]
    trivial
  memBalanced := by
    rw [memLog_turnChain]
    exact memCheck_nil _ _
  memTableFaithful := by
    rw [memLog_turnChain]
    rfl
  mapTableFaithful := by
    rw [mapLog_turnChain]
    rfl

/-- Rung 1 fires non-vacuously on every row of the honest padded trace. -/
theorem honestTrace_matches_rust :
    ∀ i, i < honestTrace.rows.length →
      RustTurnChainRow hash99 (envAt honestTrace i)
        (i == 0) (i + 1 == honestTrace.rows.length) := by
  intro i hi
  apply turnChain_descriptor_refines_rust_air hash99 honestTf (envAt honestTrace i)
    (i == 0) (i + 1 == honestTrace.rows.length) honestTf_chipSound honestTf_narrow_wire
  intro c hc
  exact honestTrace_satisfies.rowConstraints i hi c hc

def forgedContinuityNext : Assignment := rowOf [21, 30, 99, 99, 1, 1, 2]
def forgedIdxNext : Assignment := rowOf [20, 30, 99, 99, 2, 1, 2]
def forgedCountNext : Assignment := rowOf [20, 30, 99, 99, 1, 1, 3]

def forgedContinuityEnv : VmRowEnv :=
  { loc := honest0, nxt := forgedContinuityNext, pub := honestPub }
def forgedIdxEnv : VmRowEnv :=
  { loc := honest0, nxt := forgedIdxNext, pub := honestPub }
def forgedCountEnv : VmRowEnv :=
  { loc := honest0, nxt := forgedCountNext, pub := honestPub }

#guard honest0 Chain.NEW_ROOT != forgedContinuityNext Chain.OLD_ROOT
#guard forgedIdxNext Chain.IDX != honest0 Chain.IDX + 1
#guard forgedCountNext Chain.REAL_COUNT !=
  honest0 Chain.REAL_COUNT + forgedCountNext Chain.IS_REAL

theorem forged_continuity_row_refuted :
    ¬ turnChainWindowHolds hash99 honestTf forgedContinuityEnv true false := by
  apply turnChain_rejects_broken_continuity hash99 honestTf forgedContinuityEnv true
  · norm_num [forgedContinuityEnv, honest0, rowOf, Chain.NEW_ROOT]
  · norm_num [forgedContinuityEnv, forgedContinuityNext, rowOf, Chain.OLD_ROOT]
  · norm_num [forgedContinuityEnv, honest0, forgedContinuityNext, rowOf,
      Chain.NEW_ROOT, Chain.OLD_ROOT]

theorem forged_idx_row_refuted :
    ¬ turnChainWindowHolds hash99 honestTf forgedIdxEnv true false := by
  apply turnChain_rejects_bad_idx_step hash99 honestTf forgedIdxEnv true
  · norm_num [forgedIdxEnv, forgedIdxNext, rowOf, Chain.IDX]
  · norm_num [forgedIdxEnv, honest0, rowOf, Chain.IDX]
  · norm_num [forgedIdxEnv, honest0, forgedIdxNext, rowOf, Chain.IDX]

theorem forged_real_count_row_refuted :
    ¬ turnChainWindowHolds hash99 honestTf forgedCountEnv true false := by
  apply turnChain_rejects_bad_real_count hash99 honestTf forgedCountEnv true
  · norm_num [forgedCountEnv, forgedCountNext, rowOf, Chain.REAL_COUNT]
  · norm_num [forgedCountEnv, honest0, forgedCountNext, rowOf,
      Chain.REAL_COUNT, Chain.IS_REAL]
  · norm_num [forgedCountEnv, honest0, forgedCountNext, rowOf,
      Chain.REAL_COUNT, Chain.IS_REAL]

/-! ## §8 — Axiom hygiene: every theorem in this module is pinned. -/

#assert_axioms canonicalRowTf_narrow_wire
#assert_axioms canonicalRowTf_chipSound
#assert_axioms perRowHash_complete
#assert_axioms perRowHash_canonical_iff
#assert_axioms turnChain_descriptor_refines_rust_air
#assert_axioms turnChain_descriptor_iff_rust_air
#assert_axioms turnChain_rejects_broken_continuity
#assert_axioms turnChain_rejects_bad_idx_step
#assert_axioms turnChain_rejects_bad_real_count
#assert_axioms memOpsOf_turnChain
#assert_axioms mapOpsOf_turnChain
#assert_axioms memLog_turnChain
#assert_axioms mapLog_turnChain
#assert_axioms honestTf_narrow_wire
#assert_axioms honestTf_chipSound
#assert_axioms honestTrace_satisfies
#assert_axioms honestTrace_matches_rust
#assert_axioms forged_continuity_row_refuted
#assert_axioms forged_idx_row_refuted
#assert_axioms forged_real_count_row_refuted

end Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding
