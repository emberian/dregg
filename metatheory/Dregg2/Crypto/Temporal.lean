/-
# Dregg2.Crypto.Temporal — the FOURTH end-to-end §8 discharge: a temporal-window predicate.

**The next obligation after Merkle (membership), Pedersen (conservation), NonMembership (absence)
(`docs/rebuild/PHASE-CRYPTOKERNEL.md §5` "Path to the rest": Temporal/Dfa "need `Lookup`/`Gated` in
`CircuitIR`; dial `fullDisclosure`/`selective`").** Where the prior kinds discharged membership /
conservation / absence, this discharges a TIME-WINDOW predicate: the witnessed event time `t` lies
in the disclosed closed interval `[lo, hi]`. This is the `temporal_predicate_air` family
(`circuit/src/temporal_predicate_dsl.rs`): the AIR carries a `DIFF` column and a `DIFF_BITS`
bit-decomposition with a high-bit-zero range constraint (`temporal_predicate_dsl.rs:151-172`,
`PredicateType::{Gte,Lte,InRangeLow,InRangeHigh}`) — i.e. the comparison is the honest
bit-decomposition range gadget, NOT a primitive. The window check `lo ≤ t ≤ hi` is exactly TWO such
comparisons (`t - lo ≥ 0` and `hi - t ≥ 0`), each `RecordCircuit.range_iff`. The cascade mirrors the
prior kinds:

    temporal_bridge       : Satisfies temporalCircuit (lo,hi,t) ↔ (lo ≤ t ∧ t ≤ hi)
      [the gadget, FULLY proven — TWO `range_iff` comparison gadgets, NO primitive seam]
    temporal_verify_sound : verify accepts → (lo ≤ t ∧ t ≤ hi)
      [DERIVED off the bridge, given the STARK `extractable` carrier]
    temporal_dial_wired   : the dial pinned to the verifier at the `selective` floor
      [the window [lo,hi] is DISCLOSED, the exact event time t may be hidden ⇒ `selective`]

**The bounds combinatorics are the genuinely-grounded part** (and the heart of the bridge): a value
with a valid `n`-bit boolean decomposition of `t - lo` (resp. `hi - t`) provably satisfies `lo ≤ t`
(resp. `t ≤ hi`) — `RecordCircuit.range_proves_le`, fully proved, no crypto. There is NO primitive
seam inside the temporal gadget at all: unlike Merkle's `compress`, the window predicate is pure
comparison combinatorics. The ONLY cryptographic residue is the STARK `extractable` carrier (a
`Prop`, passed as a hypothesis), binding the disclosed `(lo, hi, t)` to a satisfying trace — never the
bounds algebra, which is unconditional. Exactly the discipline the rails demand.
-/
import Dregg2.Crypto.Primitives
import Dregg2.Exec.RecordCircuit
import Dregg2.Authority.Predicate
import Metatheory.EpistemicDial
import Dregg2.Tactics

namespace Dregg2.Crypto.Temporal

open Dregg2.Crypto Dregg2.Exec.RecordCircuit

/-! ## The temporal relation (the statement algebra) — a closed-interval window check.

The witnessed event time `t` lies in the disclosed window `[lo, hi]`: `lo ≤ t ∧ t ≤ hi`. This is the
real `temporal_predicate` semantics (`temporal_predicate_dsl.rs:280-281`: `Gte`/`Lte` over a
threshold; a window is the conjunction of a lower and an upper threshold). Everything is over `ℤ` (the
field is `BabyBear` in Rust; the comparison gadget is the same bit-decomposition either way). -/

/-- **`InWindow lo hi t`** — the temporal statement: the event time `t` lies in the closed interval
`[lo, hi]`. The relation the verifier's accepting bit must certify. -/
def InWindow (lo hi t : Int) : Prop := lo ≤ t ∧ t ≤ hi

/-! ## `CircuitIR` — the temporal AIR's two range gadgets (`DIFF` + `DIFF_BITS`), no primitive seam.

Mirrors `temporal_predicate_dsl.rs`'s comparison columns: `DIFF` carries `value - threshold` (here,
the two differences `t - lo` and `hi - t`), and `DIFF_BITS` is its little-endian boolean
decomposition with the high-bit-zero constraint forcing non-negativity (`dsl:151-172`). A window is
TWO such comparisons. We carry the two bit-witnesses directly — `loBits` decomposes `t - lo` (proving
`lo ≤ t`), `hiBits` decomposes `hi - t` (proving `t ≤ hi`). NO `compress`, NO hash: the temporal
gadget is pure comparison combinatorics, so there is NO primitive seam to flag. -/

/-- **The temporal circuit IR** — the trace: the two range-gadget bit-witnesses, one for each side of
the window. `loBits` is the boolean decomposition of `t - lo` (the lower-bound `Gte` gadget),
`hiBits` of `hi - t` (the upper-bound `Lte` gadget). -/
structure CircuitIR where
  /-- Little-endian boolean bits decomposing `t - lo` (the `DIFF_BITS` of the lower-bound gadget). -/
  loBits : List Int
  /-- Little-endian boolean bits decomposing `hi - t` (the `DIFF_BITS` of the upper-bound gadget). -/
  hiBits : List Int
  deriving Repr

/-- **`Satisfies circuit lo hi t`** — the full temporal AIR check, over the disclosed window `(lo, hi)`
and the witnessed time `t`: each side's `DIFF_BITS` is boolean (`Binary` per-bit gate) and recomposes
the corresponding difference (`DIFF` recomposition gate): `bitsToInt loBits = t - lo` and
`bitsToInt hiBits = hi - t`. Booleanity + recomposition is exactly the `range_iff` gadget — soundness
gives `0 ≤ diff`, i.e. the comparison. This is the conjunction `temporal_predicate_dsl` enforces. -/
def Satisfies (circuit : CircuitIR) (lo hi t : Int) : Prop :=
  -- lower-bound gadget: loBits is a boolean decomposition of t - lo (⇒ 0 ≤ t - lo ⇒ lo ≤ t).
  (Boolean circuit.loBits ∧ bitsToInt circuit.loBits = t - lo) ∧
  -- upper-bound gadget: hiBits is a boolean decomposition of hi - t (⇒ 0 ≤ hi - t ⇒ t ≤ hi).
  (Boolean circuit.hiBits ∧ bitsToInt circuit.hiBits = hi - t)

/-! ## The bridge — `Satisfies ↔ InWindow`, FULLY proven (NO primitive seam).

Both directions ride the honest `range_iff` gadget (`Exec/RecordCircuit.lean`), which has NO assumed
soundness. `→` (SOUNDNESS): each satisfied range gadget's `range_proves_le` forces its comparison, so
both bounds hold. `←` (COMPLETENESS): the two comparisons give non-negative differences, each with a
boolean decomposition by `range_complete`/`le_iff_range`. There is NO `compress` here, so NO primitive
seam at all — the temporal predicate is pure comparison combinatorics. -/

/-- **`temporal_sound` (the `→` half).** A satisfying trace PROVES the window: each side's range
gadget (`range_proves_le`) forces its comparison — `loBits` recomposing `t - lo` gives `lo ≤ t`,
`hiBits` recomposing `hi - t` gives `t ≤ hi`. Fully proved, no crypto. -/
theorem temporal_sound (circuit : CircuitIR) (lo hi t : Int)
    (h : Satisfies circuit lo hi t) : InWindow lo hi t := by
  obtain ⟨⟨hloBool, hloRec⟩, ⟨hhiBool, hhiRec⟩⟩ := h
  refine ⟨?_, ?_⟩
  · -- range_proves_le : Boolean bits → bitsToInt bits = b - a → a ≤ b, with (a,b) = (lo, t).
    exact range_proves_le lo t circuit.loBits hloBool hloRec
  · -- with (a, b) = (t, hi): bitsToInt hiBits = hi - t ⇒ t ≤ hi.
    exact range_proves_le t hi circuit.hiBits hhiBool hhiRec

/-- **`temporal_complete` (the `←` half).** A genuine window membership has a satisfying trace: from
`lo ≤ t` build a boolean decomposition of `t - lo` (`le_iff_range`/`range_complete`), from `t ≤ hi`
one of `hi - t`. The bit-counts `n`/`m` are the prover's chosen widths (any width whose `2^width`
exceeds the difference works); we take the canonical `Int.toNat`-based widths. -/
theorem temporal_complete (lo hi t : Int) (h : InWindow lo hi t) :
    ∃ circuit : CircuitIR, Satisfies circuit lo hi t := by
  obtain ⟨hlo, hhi⟩ := h
  -- Non-negative differences, each gets a boolean decomposition at a sufficient bit-width.
  have hlo0 : (0 : Int) ≤ t - lo := by omega
  have hhi0 : (0 : Int) ≤ hi - t := by omega
  -- A width whose 2^width strictly exceeds the difference (the difference fits in `d+1` bits).
  obtain ⟨loBits, _, hloBool, hloRec⟩ :=
    range_complete (t - lo).toNat (t - lo) hlo0 (by
      have : (t - lo) = ((t - lo).toNat : Int) := (Int.toNat_of_nonneg hlo0).symm
      rw [this]; exact_mod_cast Nat.lt_two_pow_self)
  obtain ⟨hiBits, _, hhiBool, hhiRec⟩ :=
    range_complete (hi - t).toNat (hi - t) hhi0 (by
      have : (hi - t) = ((hi - t).toNat : Int) := (Int.toNat_of_nonneg hhi0).symm
      rw [this]; exact_mod_cast Nat.lt_two_pow_self)
  exact ⟨⟨loBits, hiBits⟩, ⟨hloBool, hloRec⟩, ⟨hhiBool, hhiRec⟩⟩

/-- **`temporal_bridge` — THE deliverable (the analog of `merkle_bridge`/`pedersen_conservation_bridge`).**
The temporal AIR's satisfiability is EXACTLY the window membership `lo ≤ t ∧ t ≤ hi`:

  * `→` (SOUNDNESS): a satisfying trace's two range gadgets force both bounds (`range_proves_le`).
  * `←` (COMPLETENESS): a genuine window membership yields a satisfying trace (two boolean
    decompositions via `range_complete`).

The window predicate is pure comparison combinatorics — NO `compress`, NO primitive seam ANYWHERE in
this gadget (unlike Merkle). The ONLY cryptographic residue is the STARK `extractable` carrier
(consumed by `temporal_verify_sound`), binding the disclosed `(lo, hi, t)` to a satisfying trace. -/
theorem temporal_bridge (lo hi t : Int) :
    (∃ circuit : CircuitIR, Satisfies circuit lo hi t) ↔ InWindow lo hi t :=
  ⟨fun ⟨c, hc⟩ => temporal_sound c lo hi t hc, temporal_complete lo hi t⟩

-- TRIPWIRES: the temporal gadget is FULLY proven with NO primitive seam — both bridge directions are
-- kernel-clean (axioms ⊆ {propext, Classical.choice, Quot.sound}). The window check is pure
-- comparison combinatorics (two `range_iff` gadgets); there is no hash/`compress` to flag.
#assert_axioms temporal_sound
#assert_axioms temporal_complete
#assert_axioms temporal_bridge

/-! ## Layer B — the temporal `VerifierKernel`: `verify` + carrier + DERIVED `verify_sound`.

Mirrors `MerkleVerifierKernel`/`PedersenVerifierKernel`/`NonMembershipVerifierKernel`. `verify` is the
§8 oracle over the disclosed `(lo, hi, t)`; `extractable` (STARK soundness) gives "accept ⇒ a
satisfying trace exists"; `temporal_verify_sound` is DERIVED off the bridge's soundness half. -/

/-- **The disclosed temporal statement** — the public inputs the verifier sees: the window bounds
`(lo, hi)` and the event time `t`. (At the `selective` floor the window is disclosed; the exact event
time may be the hidden witness — see the dial below. Here all three are the public statement for the
verify law; the floor wiring is about WHAT ELSE is leaked.) -/
structure Statement where
  /-- The lower window bound (public). -/
  lo : Int
  /-- The upper window bound (public). -/
  hi : Int
  /-- The witnessed event time. -/
  t : Int
  deriving Repr

/-- **Layer B — the temporal `VerifierKernel`.** The §8 `verify` oracle over the disclosed statement,
and the STARK `extractable` carrier. `extract` unpacks `extractable` to its operational content: an
accepted proof witnesses a satisfying trace for the disclosed `(lo, hi, t)` — the existence the
FRI/Fiat-Shamir soundness delivers. NO Pedersen `binding` carrier here (no commitment), NO `compress`
CR (no hash): the only assumption is STARK extractability. -/
class TemporalVerifierKernel (Proof : Type) where
  /-- **The §8 verify oracle** (`stark::verify` for the temporal-predicate AIR): does `proof`
  discharge the disclosed window statement `(lo, hi, t)`? -/
  verify : Statement → Proof → Bool
  /-- **CARRIER — STARK extractability/soundness** (FRI + Fiat-Shamir): accept ⇒ a satisfying trace
  exists. A `Prop`; never proved, never `sorry`. -/
  extractable : Prop
  /-- `extractable` UNPACKED: an accepted proof witnesses a satisfying temporal trace for the
  disclosed window/time. The named form the bridge composes with — STARK soundness. -/
  extract : extractable →
    ∀ (stmt : Statement) (proof : Proof), verify stmt proof = true →
      ∃ circuit : CircuitIR, Satisfies circuit stmt.lo stmt.hi stmt.t

variable {Proof : Type}

/-- **`temporal_verify_sound` — the DERIVED verify law (the analog of `merkle_verify_sound`).** Given
the STARK-soundness carrier `extractable`, an accepted temporal proof PROVES the event time lies in
the disclosed window:

    verify stmt proof = true  →  InWindow stmt.lo stmt.hi stmt.t

The proof composes `extract` (accept ⇒ satisfying trace, the crypto carrier) with `temporal_bridge`'s
SOUNDNESS half (satisfying trace ⇒ window, FULLY proved via the two `range_iff` gadgets). The verify
law is DERIVED, not assumed; the only hypothesis is `extractable`. -/
theorem temporal_verify_sound [K : TemporalVerifierKernel Proof]
    (hext : K.extractable) (stmt : Statement) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    InWindow stmt.lo stmt.hi stmt.t := by
  obtain ⟨circuit, hsat⟩ := K.extract hext stmt proof haccept
  exact (temporal_bridge stmt.lo stmt.hi stmt.t).1 ⟨circuit, hsat⟩

#assert_axioms temporal_verify_sound

/-! ## Layer C — the kind obligation + the DIAL wiring at the `selective` floor.

The temporal window `[lo, hi]` is DISCLOSED (the verifier learns WHICH window the event falls in), but
the exact event time `t` may be blinded — the proof testifies "`t ∈ [lo, hi]`" without revealing `t`
itself. So the epistemic floor is `selective` (chosen facts — the window — plus the conclusion), NOT
the `acceptanceOnly` ZK bottom (which would hide the window too) and NOT `fullDisclosure` (which would
reveal the exact time). This matches `PHASE-CRYPTOKERNEL.md §5` ("dial `fullDisclosure`/`selective`")
and parallels Pedersen, which also sits at `selective` (it discloses the commitments). We wire
`EpistemicDial.DiscloseAt` to the verifier exactly as `PredicateKernel` does. -/

open Dregg2.Authority.Predicate Dregg2.Laws Metatheory

/-- **`KindObligation`** for temporal — statement algebra `Statement`, **dial floor = `selective`**
(the window is disclosed, the exact event time may be hidden; chosen facts + the conclusion). -/
structure KindObligation where
  /-- The public-input algebra: the disclosed window + time. -/
  Statement : Type
  /-- The dial floor — `selective` for temporal (window disclosed, time may be blinded). -/
  dialFloor : Dial

/-- The temporal kind's obligation: statement = the disclosed window/time, floor = `selective`. -/
def temporalKindObligation : KindObligation where
  Statement := Statement
  dialFloor := Dial.selective

@[simp] theorem temporalKindObligation_floor :
    temporalKindObligation.dialFloor = Dial.selective := rfl

/-- `selective` is strictly above the ZK floor: the temporal proof discloses MORE than a blinded
acceptance bit (it reveals the window), so the floor is non-degenerate above `acceptanceOnly`. -/
theorem temporal_floor_above_bot :
    (⊥ : Dial) < temporalKindObligation.dialFloor := by
  show Dial.acceptanceOnly < Dial.selective
  exact Dial.acceptanceOnly_lt_selective

/-! ### The dial wiring — `DiscloseAt` instantiated at the temporal verifier's `selective` floor.
The registry/dial machinery lives at universe 0; the temporal `Statement`/`Proof` are already there. -/

section Wiring

variable {P : Type}

/-- A `Verifier Statement P` from the kernel's §8 `verify` oracle. -/
def temporalVerifier [K : TemporalVerifierKernel P] : Verifier Statement P :=
  fun stmt proof => K.verify stmt proof

/-- The temporal-kind registry: the §8 `verify` oracle installed at `temporal`. -/
def temporalReg [TemporalVerifierKernel P]
    (base : Registry Statement P) : Registry Statement P :=
  fun j => if j = .temporal then some temporalVerifier else base j

/-- The `Verifiable` seam this kind dispatches through (explicit `base`, not auto-synthesized). -/
@[reducible] def temporalSeam [TemporalVerifierKernel P]
    (base : Registry Statement P) : Verifiable Statement P :=
  verifiableOfRegistry (temporalReg base) .temporal

/-- **`temporalDisclose` — the dial pinned to the temporal verifier.** `accepts d` is the
position-independent `Discharged stmt proof`; `accepts_eq := fun _ => Iff.rfl`. Realizes "instantiate
`DiscloseAt` at the `selective` floor (the window is disclosed, the exact time may be blinded)". -/
def temporalDisclose [TemporalVerifierKernel P]
    (base : Registry Statement P) (stmt : Statement) (proof : P) :
    @DiscloseAt Unit Statement P _ (temporalSeam base) :=
  letI : Verifiable Statement P := temporalSeam base
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := stmt
    wit := proof
    accepts := fun _ => Discharged stmt proof
    accepts_eq := fun _ => Iff.rfl }

/-- **`temporal_dial_wired` — THE DIAL WIRING (the analog of `pedersen_dial_wired`).** The temporal
kind's epistemic floor is `selective` (window disclosed, time may be blinded), the dial's bottom
notch's acceptance bit IS the temporal verifier's `Discharged` bit, and — given STARK `extractable` —
an accepting proof PROVES the window membership. The dial is pinned to the per-kind verifier. -/
theorem temporal_dial_wired [K : TemporalVerifierKernel P]
    (hext : K.extractable)
    (base : Registry Statement P) (stmt : Statement) (proof : P) :
    -- (1) the floor is selective:
    temporalKindObligation.dialFloor = Dial.selective ∧
    -- (2) the dial's bottom notch accepts IFF the temporal verifier discharges:
    (@DiscloseAt.accepts Unit Statement P _ (temporalSeam base)
        (temporalDisclose base stmt proof) (⊥ : Dial)
      ↔ @Discharged Statement P (temporalSeam base) stmt proof) ∧
    -- (3) and an accepting proof PROVES the window membership (the cascade):
    (K.verify stmt proof = true → InWindow stmt.lo stmt.hi stmt.t) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact @DiscloseAt.accepts_bot_iff_discharged Unit Statement P _ (temporalSeam base)
      (temporalDisclose base stmt proof)
  · exact fun haccept => temporal_verify_sound hext stmt proof haccept

/-- **`temporal_registry_cascade` — the §8 discharge through the registry (the analog of
`merkle_registry_cascade`).** Registering the temporal kind, an accepted proof both `Discharged`s the
kind's predicate (the registry keystone, `registry_sound`) AND — given the STARK `extractable`
carrier — PROVES the window membership (`temporal_verify_sound`). The cascade
`registry_sound ∘ temporal_verify_sound`; the single trust boundary is `extractable`. -/
theorem temporal_registry_cascade [K : TemporalVerifierKernel P]
    (hext : K.extractable)
    (base : Registry Statement P)
    (stmt : Statement) (proof : P)
    (haccept : K.verify stmt proof = true) :
    (@Discharged Statement P (verifiableOfRegistry (temporalReg base) .temporal) stmt proof)
      ∧ InWindow stmt.lo stmt.hi stmt.t := by
  refine ⟨?_, temporal_verify_sound hext stmt proof haccept⟩
  apply registry_sound (temporalReg base) .temporal stmt proof
  show registryVerify (temporalReg base) .temporal stmt proof = true
  unfold registryVerify temporalReg
  simp only [↓reduceIte]
  exact haccept

end Wiring

#assert_axioms temporal_dial_wired
#assert_axioms temporal_registry_cascade

/-! ## `Reference` — a concrete kernel + non-vacuity witnesses over `ℤ`.

A degenerate temporal verifier kernel `def` (NOT a global `instance`, to avoid silent
auto-resolution) witnessing the bridge / verify-sound / cascade end-to-end. NOT real crypto. -/

namespace Reference

/-- A concrete window/time over `ℤ`: window `[10, 20]`, event time `15` — genuinely inside. -/
def sampleStmt : Statement := { lo := 10, hi := 20, t := 15 }

/-- Non-vacuity of the BRIDGE: `15 ∈ [10, 20]`, so a satisfying trace exists (via `temporal_complete`,
the two boolean decompositions of `15 - 10 = 5` and `20 - 15 = 5`). -/
example : ∃ circuit : CircuitIR, Satisfies circuit 10 20 15 :=
  temporal_complete 10 20 15 ⟨by norm_num, by norm_num⟩

/-- Non-vacuity of the SOUNDNESS heart: any satisfying trace for `(10, 20, 15)` proves `15 ∈ [10, 20]`.
We exhibit a concrete trace (`loBits = bits of 5`, `hiBits = bits of 5`) and run `temporal_sound`. -/
example : InWindow 10 20 15 := by
  obtain ⟨circuit, hsat⟩ := temporal_complete 10 20 15 ⟨by norm_num, by norm_num⟩
  exact temporal_sound circuit 10 20 15 hsat

/-- A degenerate reference temporal verifier kernel over `ℤ` (`def`, not a global `instance`).
`verify` accepts iff `stmt.lo ≤ stmt.t ∧ stmt.t ≤ stmt.hi` (the decidable window check directly);
`extractable := True`. `extract` rebuilds the satisfying trace from the accepted window via
`temporal_complete`. -/
@[reducible] def refKernel : TemporalVerifierKernel Int where
  verify stmt _ := decide (stmt.lo ≤ stmt.t ∧ stmt.t ≤ stmt.hi)
  extractable := True
  extract := by
    intro _ stmt _ haccept
    simp only [decide_eq_true_eq] at haccept
    exact temporal_complete stmt.lo stmt.hi stmt.t haccept

/-- The empty base registry over the toy `ℤ` temporal statement/proof. -/
def base : Registry Statement Int := fun _ => none

/-- Non-vacuity of `temporal_verify_sound`: at the reference kernel an accepted proof proves the event
lies in the window. -/
example : InWindow sampleStmt.lo sampleStmt.hi sampleStmt.t :=
  temporal_verify_sound (K := refKernel) trivial sampleStmt 0 (by decide)

/-- Non-vacuity of the FULL cascade: at the reference kernel an accepted proof both `Discharged`s the
registry predicate AND proves the window membership. A NAMED witness so its axiom footprint is
checkable. -/
theorem reference_cascade_nonvacuous :
    (@Discharged Statement Int
        (verifiableOfRegistry (@temporalReg Int refKernel base) .temporal) sampleStmt 0)
      ∧ InWindow sampleStmt.lo sampleStmt.hi sampleStmt.t :=
  temporal_registry_cascade (K := refKernel) trivial base sampleStmt 0 (by decide)

-- The non-vacuity witness's axiom footprint (the task's `#print axioms` requirement): the reference
-- cascade rests only on the three standard kernel axioms — NO `sorryAx`, NO crypto axiom.
#print axioms reference_cascade_nonvacuous

/-- Non-vacuity of the dial wiring: the floor is `selective`, the dial's bottom notch is the verifier's
bit, and an accepting proof proves the window membership. -/
example : temporalKindObligation.dialFloor = Dial.selective :=
  (temporal_dial_wired (K := refKernel) trivial base sampleStmt 0).1

end Reference

-- TRIPWIRES: the temporal bridge + derived verify-soundness + cascade + dial wiring are kernel-clean.
-- The bridge is FULLY proved via TWO `range_iff` comparison gadgets — NO primitive seam ANYWHERE
-- (the temporal predicate has no hash/commitment). The ONLY cryptographic residue is the
-- `extractable` carrier (passed as a hypothesis), never a hidden `sorry`.
#assert_axioms temporal_bridge
#assert_axioms temporal_verify_sound
#assert_axioms temporal_registry_cascade
#assert_axioms temporal_dial_wired

end Dregg2.Crypto.Temporal
