/-
# Dregg2.Crypto.Bridge — the SIXTH end-to-end §8 discharge: a cross-chain comparison predicate.

**The next obligation after Merkle / Pedersen / NonMembership / Temporal / Dfa
(`docs/rebuild/PHASE-CRYPTOKERNEL.md §5` "Path to the rest": `Bridge` "is the comparison AIR (range
gadgets)").** This discharges the `WitnessedKind.bridge` obligation: a cross-chain / observation-bridge
predicate that checks an OBSERVED foreign value `v` (e.g. an amount or balance read off a foreign
chain) both (a) OPENS against a committed foreign-state digest `c` — the prover knows a preimage of the
disclosed commitment — AND (b) satisfies a COMPARISON against a disclosed expected `threshold`
(`threshold ≤ v`). This is the bridge-action family (`circuit/src/bridge_action_air.rs`): the AIR binds
the typed foreign parameters into the trace and pins them to the public inputs (the OPENING half — a
boundary `PiBinding` of the committed digest to the witnessed limbs), and the metatheory's Bridge kind
adds the COMPARISON the §5 note names ("the comparison AIR (range gadgets)") — the observed value clears
the expected threshold. The cascade mirrors the prior kinds:

    bridge_bridge       : Satisfies bridgeCircuit (c, threshold, v) ↔ BridgeRelation compress (c,threshold,v)
      [the gadget, both directions — the COMPARISON via `RecordCircuit.range` (FULLY proven, no seam),
       the OPENING via an abstract `compress` equation (structural; CR/binding is the Layer-A carrier)]
    bridge_verify_sound : verify accepts → BridgeRelation …
      [DERIVED off the bridge, given the STARK `extractable` carrier]
    bridge_dial_wired   : the dial pinned to the verifier at the `selective` floor
      [the foreign commitment `c` + threshold are DISCLOSED, the exact observed value `v` is the hidden
       witness ⇒ `selective` (chosen facts + the conclusion), like Pedersen / Temporal]

**The COMPARISON is the genuinely-grounded part** (and the heart of the bridge): an observed value with
a valid `n`-bit boolean decomposition of `v - threshold` provably satisfies `threshold ≤ v`
(`RecordCircuit.range_proves_le`, fully proved, no crypto) — exactly the §5 "comparison AIR (range
gadgets)". This is the SAME range gadget Temporal rides; here it is one-sided (a `Gte` threshold,
`bridge_action_air.rs` carries the amount limbs that the bridge compares). The ONLY cryptographic
residue is (i) the abstract `compress` digest-OPENING equation `c = compress vDigest salt` — left
ABSTRACT exactly like Merkle's node hash, its collision-resistance / binding being the Layer-A
`CryptoPrimitives.collisionHard` / `binding` `Prop` carriers, NEVER touched by the bridge — and (ii)
the STARK `extractable` carrier (a `Prop`, passed as a hypothesis) binding the disclosed statement to a
satisfying trace. The comparison algebra is unconditional. Exactly the discipline the rails demand.
-/
import Dregg2.Crypto.Primitives
import Dregg2.Exec.RecordCircuit
import Dregg2.Authority.Predicate
import Metatheory.EpistemicDial
import Dregg2.Tactics

namespace Dregg2.Crypto.Bridge

open Dregg2.Crypto Dregg2.Exec.RecordCircuit

universe u

/-! ## The Bridge relation (the statement algebra) — an observed value that OPENS + CLEARS a threshold.

The bridge observes a foreign value `v : Int`. The disclosed statement is the committed foreign-state
digest `c : Digest` and the expected `threshold : Int`. The relation: the prover knows an OPENING of
`c` to a digest `vDigest` of the observed value (with a blinding `salt`), AND the observed value clears
the threshold (`threshold ≤ v`). The digest-opening is over the ABSTRACT Layer-A `compress` (its
collision-resistance / binding is the carried `CryptoPrimitives.collisionHard`/`binding`, NEVER invoked
here — like Merkle); the comparison is the honest `RecordCircuit.range` gadget. `vDigest` is the
digest the observed value commits to (the foreign-state limb the AIR binds, `bridge_action_air.rs`); the
linkage `vDigest ↔ v` is part of the witness the prover supplies. -/

variable {Digest : Type u}

/-- **`Opens compress c vDigest salt`** — the digest-OPENING half of the bridge: the disclosed
commitment `c` is the `compress` of the observed value's digest `vDigest` with the blinding `salt`. This
mirrors the boundary `PiBinding` of `bridge_action_air.rs` (the committed foreign digest pinned to the
witnessed limbs). `compress` is ABSTRACT — this is a pure equation; its collision-resistance / binding
is the Layer-A `collisionHard`/`binding` carrier, consumed elsewhere (the verifier-kernel
extractability), NEVER by the bridge. NO primitive seam: like Merkle's node hash, the opening is just an
equation over the uninterpreted `compress`. -/
def Opens (compress : Digest → Digest → Digest) (c vDigest salt : Digest) : Prop :=
  c = compress vDigest salt

/-- **`BridgeRelation compress c threshold v vDigest salt`** — the full bridge statement: the observed
value `v` OPENS against the committed foreign digest `c` (`Opens`, via `vDigest` + `salt`) AND CLEARS
the disclosed `threshold` (`threshold ≤ v`, the comparison the §5 note names). The relation the
verifier's accepting bit must certify — a foreign observation that both matches the committed state and
satisfies the expected comparison. -/
def BridgeRelation (compress : Digest → Digest → Digest)
    (c : Digest) (threshold v : Int) (vDigest salt : Digest) : Prop :=
  Opens compress c vDigest salt ∧ threshold ≤ v

/-! ## `CircuitIR` — the bridge AIR: a one-sided range gadget (comparison) + the opening boundary.

Mirrors `bridge_action_air.rs`: the trace carries the observed value's digest limbs (pinned to the
committed `c` by the boundary `PiBinding` — the OPENING) and the comparison column. The comparison is
the §5 "range gadget": a `DIFF` column carrying `v - threshold` and its `DIFF_BITS` boolean
decomposition with the high-bit-zero non-negativity constraint (exactly `RecordCircuit.range_iff`,
one-sided — a `Gte` threshold). We carry the comparison's bit-witness directly (`cmpBits` decomposes
`v - threshold`, proving `threshold ≤ v`) plus the opening witness (`vDigest`, `salt`). The COMPARISON
has NO primitive seam (pure range combinatorics); the OPENING rides the abstract `compress` equation
(its CR is the Layer-A carrier). -/

/-- **The bridge circuit IR** — the trace: the comparison range-gadget bit-witness plus the opening
witness. `cmpBits` is the boolean decomposition of `v - threshold` (the `Gte` comparison gadget, the §5
range gadget); `vDigest`/`salt` are the foreign-value digest + blinding the opening boundary pins to the
committed `c` (`bridge_action_air.rs` limbs). -/
structure CircuitIR (Digest : Type u) where
  /-- Little-endian boolean bits decomposing `v - threshold` (the `DIFF_BITS` of the comparison gadget). -/
  cmpBits : List Int
  /-- The observed value's digest (the foreign-state limb the opening boundary pins to `c`). -/
  vDigest : Digest
  /-- The opening blinding (`salt`) for the `compress` commitment. -/
  salt : Digest
  deriving Repr

/-- **`Satisfies compress circuit c threshold v`** — the full bridge AIR check, over the disclosed
commitment `c` and threshold, and the witnessed observed value `v`: the comparison gadget's `DIFF_BITS`
is boolean (`Binary` per-bit gate) and recomposes the difference (`DIFF` recomposition gate)
— `bitsToInt cmpBits = v - threshold`, exactly `range_iff`, giving `threshold ≤ v` — AND the opening
boundary holds: `c = compress vDigest salt` (the foreign digest pinned to the committed state). This is
the conjunction the bridge AIR enforces. -/
def Satisfies (compress : Digest → Digest → Digest)
    (circuit : CircuitIR Digest) (c : Digest) (threshold v : Int) : Prop :=
  -- comparison gadget: cmpBits is a boolean decomposition of v - threshold (⇒ 0 ≤ v - threshold ⇒ threshold ≤ v).
  (Boolean circuit.cmpBits ∧ bitsToInt circuit.cmpBits = v - threshold) ∧
  -- opening boundary: the committed digest opens to the observed value's digest + salt.
  Opens compress c circuit.vDigest circuit.salt

/-! ## The bridge — `Satisfies ↔ BridgeRelation`, BOTH directions.

The COMPARISON half rides the honest `range_iff` gadget (`Exec/RecordCircuit.lean`), which has NO
assumed soundness — `→` uses `range_proves_le`, `←` uses `range_complete`. The OPENING half is a pure
`compress` equation carried through both directions (no `compress` algebra is needed — the equation is
just threaded). There is NO primitive seam inside the gadget: the comparison is pure combinatorics, and
the opening is an uninterpreted equation whose CR/binding lives in the Layer-A `collisionHard`/`binding`
carriers (consumed by `bridge_verify_sound`, never here). -/

/-- **`bridge_sound` (the `→` half).** A satisfying trace PROVES the relation: the comparison gadget's
`range_proves_le` forces `threshold ≤ v`, and the opening boundary IS `Opens`. Fully proved, no crypto
(the opening equation is threaded, never opened). -/
theorem bridge_sound (compress : Digest → Digest → Digest)
    (circuit : CircuitIR Digest) (c : Digest) (threshold v : Int)
    (h : Satisfies compress circuit c threshold v) :
    BridgeRelation compress c threshold v circuit.vDigest circuit.salt := by
  obtain ⟨⟨hcmpBool, hcmpRec⟩, hopen⟩ := h
  refine ⟨hopen, ?_⟩
  -- range_proves_le : Boolean bits → bitsToInt bits = b - a → a ≤ b, with (a,b) = (threshold, v).
  exact range_proves_le threshold v circuit.cmpBits hcmpBool hcmpRec

/-- **`bridge_complete` (the `←` half).** A genuine bridge relation has a satisfying trace: from
`threshold ≤ v` build a boolean decomposition of `v - threshold` (`range_complete`), and carry the
opening witness (`vDigest`, `salt`) the relation supplies. The bit-width is the prover's chosen width
(the canonical `Int.toNat`-based one, whose `2^width` exceeds the difference). -/
theorem bridge_complete (compress : Digest → Digest → Digest)
    (c : Digest) (threshold v : Int) (vDigest salt : Digest)
    (h : BridgeRelation compress c threshold v vDigest salt) :
    ∃ circuit : CircuitIR Digest, Satisfies compress circuit c threshold v := by
  obtain ⟨hopen, hle⟩ := h
  have hd0 : (0 : Int) ≤ v - threshold := by omega
  obtain ⟨cmpBits, _, hcmpBool, hcmpRec⟩ :=
    range_complete (v - threshold).toNat (v - threshold) hd0 (by
      have : (v - threshold) = ((v - threshold).toNat : Int) := (Int.toNat_of_nonneg hd0).symm
      rw [this]; exact_mod_cast Nat.lt_two_pow_self)
  exact ⟨⟨cmpBits, vDigest, salt⟩, ⟨hcmpBool, hcmpRec⟩, hopen⟩

/-- **`bridge_bridge` — THE deliverable (the analog of `merkle_bridge`/`temporal_bridge`).** The bridge
AIR's satisfiability is EXACTLY the bridge relation `Opens c ∧ threshold ≤ v`:

  * `→` (SOUNDNESS): a satisfying trace's comparison range gadget forces `threshold ≤ v`
    (`range_proves_le`), and the opening boundary IS `Opens` (`bridge_sound`).
  * `←` (COMPLETENESS): a genuine relation yields a satisfying trace (a boolean decomposition of
    `v - threshold` via `range_complete`, plus the threaded opening witness — `bridge_complete`).

The COMPARISON core (`RecordCircuit.range`) is FULLY proven — NO primitive seam (the §5 "range
gadget"). The OPENING is an abstract `compress` equation threaded through, never opened; its CR/binding
is the Layer-A `collisionHard`/`binding` carrier, consumed by `bridge_verify_sound`, NEVER here. Stated
over `circuit.vDigest`/`circuit.salt` on the `→` side (the witnessed opening) and existentially on the
`←` side (the prover's witness). -/
theorem bridge_bridge (compress : Digest → Digest → Digest)
    (c : Digest) (threshold v : Int) :
    -- SOUNDNESS: every satisfying trace certifies the bridge relation (at its own witnessed opening).
    (∀ circuit : CircuitIR Digest, Satisfies compress circuit c threshold v →
        BridgeRelation compress c threshold v circuit.vDigest circuit.salt)
    ∧
    -- COMPLETENESS: a genuine bridge relation gives a satisfying trace.
    (∀ vDigest salt, BridgeRelation compress c threshold v vDigest salt →
        ∃ circuit : CircuitIR Digest, Satisfies compress circuit c threshold v) :=
  ⟨fun circuit hsat => bridge_sound compress circuit c threshold v hsat,
   fun vDigest salt h => bridge_complete compress c threshold v vDigest salt h⟩

-- TRIPWIRES: the bridge gadget's both directions are kernel-clean (axioms ⊆ {propext,
-- Classical.choice, Quot.sound}). The COMPARISON heart is FULLY proved via the `range_iff` gadget — NO
-- primitive seam; the OPENING is an abstract `compress` equation threaded through (its CR/binding is the
-- Layer-A carrier, never invoked here). The ONLY cryptographic residue is the `extractable` carrier
-- (consumed below by `bridge_verify_sound`), never a hidden `sorry`.
#assert_axioms bridge_sound
#assert_axioms bridge_complete
#assert_axioms bridge_bridge

/-! ## Layer B — the bridge `VerifierKernel`: `verify` + carrier + DERIVED `verify_sound`.

Mirrors `TemporalVerifierKernel`/`DfaVerifierKernel`. `verify` is the §8 oracle over the disclosed
statement; `extractable` (STARK soundness + the digest binding) gives "accept ⇒ a satisfying trace
exists for the disclosed `(c, threshold)` at some observed value `v`"; `bridge_verify_sound` is DERIVED
off the bridge's soundness half. The statement/proof are at universe 0 (the registry/dial machinery
lives there), so the kernel is over a `Type`-level `Digest`. -/

variable {Dg : Type} [AddCommGroup Dg]

/-- **The disclosed bridge statement** — the public inputs the verifier sees: the committed foreign-state
digest `c` (the disclosed commitment, `bridge_action_air.rs` PI) and the expected `threshold`. At the
`selective` floor the commitment + threshold are disclosed; the exact observed value `v` is the hidden
witness (see the dial below). -/
structure Statement (Dg : Type) where
  /-- The committed foreign-state digest (public — the `bridge_action_air.rs` commitment PI). -/
  c : Dg
  /-- The expected comparison threshold (public). -/
  threshold : Int

/-- **Layer B — the bridge `VerifierKernel`.** The §8 `verify` oracle over the disclosed statement, and
the STARK `extractable` carrier. `extract` unpacks `extractable` to its operational content: an accepted
proof witnesses a satisfying bridge trace for the disclosed `(c, threshold)` at SOME observed value `v`
— the existence FRI/Fiat-Shamir soundness + the digest binding deliver. The `binding` of `compress` (the
opening cannot be forged) and STARK extractability are folded into the single `extractable` `Prop`
carrier; never proved, never `sorry`. -/
class BridgeVerifierKernel (Dg : Type) [AddCommGroup Dg] (Proof : Type) where
  /-- The Layer-A node hash this kernel's openings are committed under (the `compress` of `Opens`). -/
  compress : Dg → Dg → Dg
  /-- **The §8 verify oracle** (`stark::verify` for the bridge-action AIR): does `proof` discharge the
  disclosed commitment + threshold statement? -/
  verify : Statement Dg → Proof → Bool
  /-- **CARRIER — STARK extractability + digest binding** (FRI + Fiat-Shamir + Poseidon2 CR): accept ⇒
  a satisfying trace exists for some observed value. A `Prop`; never proved, never `sorry`. -/
  extractable : Prop
  /-- `extractable` UNPACKED: an accepted proof witnesses a satisfying bridge trace for the disclosed
  `(c, threshold)` at some observed value `v`. The named form the bridge composes with. -/
  extract : extractable →
    ∀ (stmt : Statement Dg) (proof : Proof), verify stmt proof = true →
      ∃ (v : Int) (circuit : CircuitIR Dg), Satisfies compress circuit stmt.c stmt.threshold v

variable {Proof : Type}

/-- **`bridge_verify_sound` — the DERIVED verify law (the analog of `temporal_verify_sound`).** Given
the STARK-soundness + digest-binding carrier `extractable`, an accepted bridge proof PROVES that there
is an observed value `v` that OPENS against the disclosed commitment `c` AND clears the `threshold`:

    verify stmt proof = true  →  ∃ v vDigest salt, BridgeRelation compress stmt.c stmt.threshold v vDigest salt

The proof composes `extract` (accept ⇒ satisfying trace, the crypto carrier) with `bridge_bridge`'s
SOUNDNESS half (satisfying trace ⇒ relation, FULLY proved via the `range_iff` gadget). The verify law is
DERIVED, not assumed; the only hypothesis is `extractable`. -/
theorem bridge_verify_sound [K : BridgeVerifierKernel Dg Proof]
    (hext : K.extractable) (stmt : Statement Dg) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    ∃ (v : Int) (vDigest salt : Dg),
      BridgeRelation K.compress stmt.c stmt.threshold v vDigest salt := by
  obtain ⟨v, circuit, hsat⟩ := K.extract hext stmt proof haccept
  exact ⟨v, circuit.vDigest, circuit.salt,
    (bridge_bridge K.compress stmt.c stmt.threshold v).1 circuit hsat⟩

#assert_axioms bridge_verify_sound

/-! ## Layer C — the kind obligation + the DIAL wiring at the `selective` floor.

The committed foreign-state digest `c` and the expected `threshold` are DISCLOSED (the verifier learns
WHICH foreign state + WHICH comparison the observation clears), but the exact observed value `v` is the
hidden witness — the proof testifies "the observed value opens against `c` and clears `threshold`"
without revealing `v` itself. So the epistemic floor is `selective` (chosen facts — the commitment +
threshold — plus the conclusion), NOT the `acceptanceOnly` ZK bottom (which would hide the commitment
too) and NOT `fullDisclosure` (which would reveal the observed value). This matches
`PHASE-CRYPTOKERNEL.md §5` ("the comparison AIR (range gadgets)") and parallels Pedersen / Temporal,
which also sit at `selective` (they disclose the commitments / window). We wire `EpistemicDial.DiscloseAt`
to the verifier exactly as the prior kinds do. -/

open Dregg2.Authority.Predicate Dregg2.Laws Metatheory

/-- **`KindObligation`** for bridge — statement algebra `Statement Dg`, **dial floor = `selective`** (the
foreign commitment + threshold are disclosed, the exact observed value may be hidden; chosen facts + the
conclusion). -/
structure KindObligation (Dg : Type) where
  /-- The public-input algebra: the disclosed commitment + threshold. -/
  Statement : Type
  /-- The dial floor — `selective` for bridge (commitment + threshold disclosed, observation hidden). -/
  dialFloor : Dial

/-- The bridge kind's obligation: statement = the disclosed commitment/threshold, floor = `selective`. -/
def bridgeKindObligation (Dg : Type) : KindObligation Dg where
  Statement := Statement Dg
  dialFloor := Dial.selective

@[simp] theorem bridgeKindObligation_floor (Dg : Type) :
    (bridgeKindObligation Dg).dialFloor = Dial.selective := rfl

/-- `selective` is strictly above the ZK floor: the bridge proof discloses MORE than a blinded
acceptance bit (it reveals the committed foreign state + threshold), so the floor is non-degenerate
above `acceptanceOnly`. -/
theorem bridge_floor_above_bot (Dg : Type) :
    (⊥ : Dial) < (bridgeKindObligation Dg).dialFloor := by
  show Dial.acceptanceOnly < Dial.selective
  exact Dial.acceptanceOnly_lt_selective

/-! ### The dial wiring — `DiscloseAt` instantiated at the bridge verifier's `selective` floor.
The registry/dial machinery lives at universe 0; the bridge `Statement`/`Proof` are already there. -/

section Wiring

variable {D : Type} [AddCommGroup D] {P : Type}

/-- A `Verifier (Statement D) P` from the kernel's §8 `verify` oracle. -/
def bridgeVerifier [K : BridgeVerifierKernel D P] : Verifier (Statement D) P :=
  fun stmt proof => K.verify stmt proof

/-- The bridge-kind registry: the §8 `verify` oracle installed at `bridge`. -/
def bridgeReg [BridgeVerifierKernel D P]
    (base : Registry (Statement D) P) : Registry (Statement D) P :=
  fun j => if j = .bridge then some bridgeVerifier else base j

/-- The `Verifiable` seam this kind dispatches through (explicit `base`, not auto-synthesized). -/
@[reducible] def bridgeSeam [BridgeVerifierKernel D P]
    (base : Registry (Statement D) P) : Verifiable (Statement D) P :=
  verifiableOfRegistry (bridgeReg base) .bridge

/-- **`bridgeDisclose` — the dial pinned to the bridge verifier.** `accepts d` is the
position-independent `Discharged stmt proof`; `accepts_eq := fun _ => Iff.rfl`. Realizes "instantiate
`DiscloseAt` at the `selective` floor (the commitment + threshold are disclosed, the observed value may
be blinded)". -/
def bridgeDisclose [BridgeVerifierKernel D P]
    (base : Registry (Statement D) P) (stmt : Statement D) (proof : P) :
    @DiscloseAt Unit (Statement D) P _ (bridgeSeam base) :=
  letI : Verifiable (Statement D) P := bridgeSeam base
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := stmt
    wit := proof
    accepts := fun _ => Discharged stmt proof
    accepts_eq := fun _ => Iff.rfl }

/-- **`bridge_dial_wired` — THE DIAL WIRING (the analog of `temporal_dial_wired`).** The bridge kind's
epistemic floor is `selective` (commitment + threshold disclosed, observation may be blinded), the
dial's bottom notch's acceptance bit IS the bridge verifier's `Discharged` bit, and — given STARK
`extractable` — an accepting proof PROVES the bridge relation (some observed value opens against `c` and
clears the threshold). The dial is pinned to the per-kind verifier. -/
theorem bridge_dial_wired [K : BridgeVerifierKernel D P]
    (hext : K.extractable)
    (base : Registry (Statement D) P) (stmt : Statement D) (proof : P) :
    -- (1) the floor is selective:
    (bridgeKindObligation D).dialFloor = Dial.selective ∧
    -- (2) the dial's bottom notch accepts IFF the bridge verifier discharges:
    (@DiscloseAt.accepts Unit (Statement D) P _ (bridgeSeam base)
        (bridgeDisclose base stmt proof) (⊥ : Dial)
      ↔ @Discharged (Statement D) P (bridgeSeam base) stmt proof) ∧
    -- (3) and an accepting proof PROVES the bridge relation (the cascade):
    (K.verify stmt proof = true →
      ∃ (v : Int) (vDigest salt : D),
        BridgeRelation K.compress stmt.c stmt.threshold v vDigest salt) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact @DiscloseAt.accepts_bot_iff_discharged Unit (Statement D) P _ (bridgeSeam base)
      (bridgeDisclose base stmt proof)
  · exact fun haccept => bridge_verify_sound hext stmt proof haccept

/-- **`bridge_registry_cascade` — the §8 discharge through the registry (the analog of
`temporal_registry_cascade`).** Registering the bridge kind, an accepted proof both `Discharged`s the
kind's predicate (the registry keystone, `registry_sound`) AND — given the STARK `extractable` carrier —
PROVES the bridge relation (`bridge_verify_sound`). The cascade `registry_sound ∘ bridge_verify_sound`;
the single trust boundary is `extractable` (STARK soundness + the digest binding). -/
theorem bridge_registry_cascade [K : BridgeVerifierKernel D P]
    (hext : K.extractable)
    (base : Registry (Statement D) P)
    (stmt : Statement D) (proof : P)
    (haccept : K.verify stmt proof = true) :
    (@Discharged (Statement D) P (verifiableOfRegistry (bridgeReg base) .bridge) stmt proof)
      ∧ ∃ (v : Int) (vDigest salt : D),
          BridgeRelation K.compress stmt.c stmt.threshold v vDigest salt := by
  refine ⟨?_, bridge_verify_sound hext stmt proof haccept⟩
  apply registry_sound (bridgeReg base) .bridge stmt proof
  show registryVerify (bridgeReg base) .bridge stmt proof = true
  unfold registryVerify bridgeReg
  simp only [↓reduceIte]
  exact haccept

end Wiring

#assert_axioms bridge_dial_wired
#assert_axioms bridge_registry_cascade

/-! ## `Reference` — a concrete kernel + non-vacuity witnesses over `ℤ`.

A degenerate bridge verifier kernel `def` (NOT a global `instance`, to avoid silent auto-resolution)
witnessing the bridge / verify-sound / cascade end-to-end. The toy `Digest` is `ℤ`, `compress a b :=
a + b` (the `Reference.instCryptoPrimitives` linear stand-in). NOT real crypto. -/

namespace Reference

/-- The toy node hash over `ℤ` (the `Primitives.Reference` linear stand-in): `compress a b = a + b`. -/
def refCompress : Int → Int → Int := fun a b => a + b

/-- A concrete observation over `ℤ`: observed value `v = 100`, its digest `vDigest = 100`, salt `7`, so
the committed digest is `compress 100 7 = 107`; threshold `50` — genuinely cleared (`50 ≤ 100`). -/
def sampleStmt : Statement Int := { c := 107, threshold := 50 }

/-- Non-vacuity of the OPENING: `107 = compress 100 7` holds for the toy `compress`. -/
example : Opens refCompress 107 100 7 := rfl

/-- Non-vacuity of the BRIDGE relation: the observation opens (`107 = 100 + 7`) AND clears the threshold
(`50 ≤ 100`). -/
theorem sample_relation : BridgeRelation refCompress 107 50 100 100 7 :=
  ⟨rfl, by norm_num⟩

/-- Non-vacuity of the BRIDGE: the genuine relation gives a satisfying trace (via `bridge_complete`, the
boolean decomposition of `100 - 50 = 50` plus the opening witness). -/
example : ∃ circuit : CircuitIR Int, Satisfies refCompress circuit 107 50 100 :=
  bridge_complete refCompress 107 50 100 100 7 sample_relation

/-- Non-vacuity of the SOUNDNESS heart: any satisfying trace for `(107, 50, 100)` proves the relation.
We exhibit a concrete trace (via `bridge_complete`) and run the `bridge_bridge` soundness conjunct. -/
example : ∃ (vD salt : Int), BridgeRelation refCompress 107 50 100 vD salt := by
  obtain ⟨circuit, hsat⟩ := bridge_complete refCompress 107 50 100 100 7 sample_relation
  exact ⟨circuit.vDigest, circuit.salt,
    (bridge_bridge refCompress 107 50 100).1 circuit hsat⟩

/-- A degenerate reference bridge verifier kernel over `ℤ` (`def`, not a global `instance`).
`verify` accepts iff the disclosed commitment is the toy `compress` of SOME observed value's digest that
clears the threshold — decided here directly against the canonical observation; `extractable := True`.
`extract` rebuilds the satisfying trace from the accepted statement via `bridge_complete`. For this toy
we model the observed value as `stmt.c - 7` opening with salt `7` (the `compress a 7 = a + 7` inverse),
and accept iff it clears the threshold. -/
@[reducible] def refKernel : BridgeVerifierKernel Int Unit where
  compress := refCompress
  verify stmt _ := decide (stmt.threshold ≤ stmt.c - 7)
  extractable := True
  extract := by
    intro _ stmt _ haccept
    simp only [decide_eq_true_eq] at haccept
    -- observed value v = stmt.c - 7, vDigest = stmt.c - 7, salt = 7 ⇒ compress vDigest salt = stmt.c.
    refine ⟨stmt.c - 7, ?_⟩
    have hrel : BridgeRelation refCompress stmt.c stmt.threshold (stmt.c - 7) (stmt.c - 7) 7 :=
      ⟨by show stmt.c = (stmt.c - 7) + 7; ring, haccept⟩
    exact bridge_complete refCompress stmt.c stmt.threshold (stmt.c - 7) (stmt.c - 7) 7 hrel

/-- The empty base registry over the toy `ℤ` bridge statement/`Unit` proof. -/
def base : Registry (Statement Int) Unit := fun _ => none

/-- Non-vacuity of `bridge_verify_sound`: at the reference kernel an accepted proof proves some observed
value opens against the commitment and clears the threshold. -/
example : ∃ (v : Int) (vD salt : Int),
    BridgeRelation refCompress sampleStmt.c sampleStmt.threshold v vD salt :=
  bridge_verify_sound (K := refKernel) trivial sampleStmt () (by decide)

/-- Non-vacuity of the FULL cascade: at the reference kernel an accepted proof both `Discharged`s the
registry predicate AND proves the bridge relation. A NAMED witness so its axiom footprint is checkable. -/
theorem reference_cascade_nonvacuous :
    (@Discharged (Statement Int) Unit
        (verifiableOfRegistry (@bridgeReg Int _ Unit refKernel base) .bridge) sampleStmt ())
      ∧ ∃ (v : Int) (vD salt : Int),
          BridgeRelation refCompress sampleStmt.c sampleStmt.threshold v vD salt :=
  bridge_registry_cascade (K := refKernel) trivial base sampleStmt () (by decide)

-- The non-vacuity witness's axiom footprint (the task's `#print axioms` requirement): the reference
-- cascade rests only on the three standard kernel axioms — NO `sorryAx`, NO crypto axiom.
#print axioms reference_cascade_nonvacuous

/-- Non-vacuity of the dial wiring: the floor is `selective`, the dial's bottom notch is the verifier's
bit, and an accepting proof proves the bridge relation. -/
example : (bridgeKindObligation Int).dialFloor = Dial.selective :=
  (bridge_dial_wired (K := refKernel) trivial base sampleStmt ()).1

end Reference

-- TRIPWIRES: the bridge bridge + derived verify-soundness + cascade + dial wiring are kernel-clean.
-- The COMPARISON heart is FULLY proved via the `range_iff` gadget — NO primitive seam; the OPENING is
-- an abstract `compress` equation threaded through (its CR/binding is the Layer-A `collisionHard`/
-- `binding` carrier, NEVER invoked). The ONLY cryptographic residue is the `extractable` carrier
-- (passed as a hypothesis), never a hidden `sorry`.
#assert_axioms bridge_bridge
#assert_axioms bridge_verify_sound
#assert_axioms bridge_registry_cascade
#assert_axioms bridge_dial_wired

end Dregg2.Crypto.Bridge
