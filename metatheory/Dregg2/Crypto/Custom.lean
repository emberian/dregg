/-
# Dregg2.Crypto.Custom — the EIGHTH end-to-end §8 discharge: the OPEN `vk`-keyed extension point.

**The eighth (and final) `WitnessedKind` (`Authority/Predicate.lean::WitnessedKind.custom (vk)`,
`cell/src/predicate.rs::WitnessedPredicateKind::Custom { vk_hash }`).** Where the seven built-in
kinds (Merkle/Pedersen/NonMembership/Temporal/Dfa/Bridge/BlindedSet) each pin a FIXED relation and
circuit, `custom (vk)` is the OPEN EXTENSION POINT: an app registers a content-addressed
verification-key hash `vk` and supplies whatever `(CircuitIR, Relation)` that `vk` denotes. The
soundness cascade is then PARAMETRIC over the registered triple — any future kind inherits the
whole §8 discipline (`*_bridge` both directions + `*_verify_sound` derived off `extractable` +
`KindObligation`/`DiscloseAt` + `registry_cascade`) merely by registering a `vk`, a circuit, and a
relation. This is dregg1's `custom` map keyed on `vk_hash` (`predicate.rs:300`), lifted to the
metatheory so the registry is genuinely OPEN, not a closed enum of seven.

The cascade mirrors the built-ins, but PARAMETRIC over the registered relation:

    custom_bridge        : Satisfies (circuitOf vk) w ↔ Relation vk stmt w
      [the gadget — for ANY registered `(vk, Circuit, Relation)` triple, BOTH directions,
       discharged from the registration's own bridge field, no new seam]
    custom_verify_sound  : verify accepts → Relation vk stmt w   (DERIVED off the bridge + `extractable`)
    custom_dial_wired    : the dial pinned to the verifier at the registration's OWN floor
      [parametric: the registering kind supplies its dial floor; default `fullDisclosure`]
    custom_registry_cascade : `registry_sound ∘ custom_verify_sound`, through `custom (vk)`

**The parametricity IS the content.** A `CustomRegistration` bundles a `vk`, its circuit/statement
algebra, its relation, and the registration's OWN `bridge` (a `Prop`-level both-directions
equivalence the app proves for its circuit — the SAME shape `merkle_bridge` etc. discharge). The
`custom_bridge` theorem is then nothing but that field, surfaced; `custom_verify_sound` composes it
with the `extractable` carrier exactly as the built-ins do. The genuinely-cryptographic residue is
the same single seam: `extractable` (STARK soundness for the app's circuit) — never an `axiom` /
`sorry`. The `Reference` section REGISTERS a concrete toy `vk` (an equality circuit) and witnesses
the entire cascade end-to-end, proving the extension point is non-vacuous: registering a real
relation lights up the whole §8 machinery.

With this, ALL EIGHT `WitnessedKind`s are discharged and the registry is COMPLETE — the seven
built-ins by fixed relations, `custom (vk)` as the open inheritance point for everything to come.
-/
import Dregg2.Authority.Predicate
import Metatheory.EpistemicDial
import Dregg2.Tactics

namespace Dregg2.Crypto.Custom

open Dregg2.Authority.Predicate Dregg2.Laws Metatheory

universe u

/-! ## The registration — a `vk`-keyed `(Circuit, Statement, Witness, Relation, bridge)` bundle.

The open extension point's content. An app that wants a new witnessed kind registers a
`CustomRegistration`: a content-addressed `vk` (the BLAKE3 keyed-hash of its predicate bytes in
dregg1, a `Nat` here), the Lean types of its circuit / public statement / private witness, the
relation `vk` denotes, the `circuitOf` map from the registered `vk` to its `CircuitIR`, the
`Satisfies` predicate of that circuit, and — crucially — the registration's OWN both-directions
`bridge` (the same `Prop` shape `merkle_bridge` proves). Everything downstream (`custom_bridge`,
`custom_verify_sound`, the cascade) is parametric over THIS bundle: registering a relation lights
up the whole cascade, with no new seam beyond the circuit's `extractable`. -/

/-- **`CustomRegistration`** — the content-addressed registration of an open kind under `vk`.
Bundles the circuit/statement/witness algebras, the relation `vk` denotes, the chosen circuit
(`circuitOf`), its `Satisfies` predicate, and the app-supplied BRIDGE (the both-directions
equivalence `Satisfies (circuitOf) w ↔ Relation stmt w` — the SAME shape the built-ins discharge).
The registration is the open extension point's payload: any future kind IS such a bundle. -/
structure CustomRegistration where
  /-- The content-addressed verification-key hash keying this registration (dregg1 `vk_hash`). -/
  vk : Nat
  /-- The app's circuit IR algebra (its `CircuitIR`, abstract here). -/
  Circuit : Type u
  /-- The public statement algebra the verifier sees. -/
  Statement : Type u
  /-- The private witness algebra (the trace the prover supplies). -/
  Witness : Type u
  /-- The relation `vk` denotes: the statement-level predicate the app's circuit certifies. -/
  Relation : Statement → Witness → Prop
  /-- The circuit `vk` denotes (`circuitOf vk`): the concrete `CircuitIR` for this registration. -/
  circuit : Circuit
  /-- The `Satisfies` predicate of the registered circuit, over `(statement, witness)`. -/
  Satisfies : Circuit → Statement → Witness → Prop
  /-- **The app's BRIDGE** — the both-directions equivalence the registration PROVES for its own
  circuit, exactly the shape `merkle_bridge` discharges: a satisfying trace certifies the relation
  (soundness) and every related pair has a satisfying trace (completeness). This is the field the
  `custom_bridge` theorem surfaces; it is the registration's obligation, the SAME the built-ins
  meet. NOT an axiom — the app supplies a proof (the `Reference` section exhibits one). -/
  bridge : ∀ (stmt : Statement) (wit : Witness),
    Satisfies circuit stmt wit ↔ Relation stmt wit
  /-- The registration's OWN epistemic dial floor (parametric: the app supplies it; the built-ins
  pick `acceptanceOnly` for blinded kinds, `fullDisclosure` for public ones, etc.). Default for a
  bare custom kind is `fullDisclosure` (no privacy claim unless the app states one). -/
  dialFloor : Dial

/-! ## The bridge — `Satisfies (circuitOf vk) w ↔ Relation vk stmt w`, PARAMETRIC over the
registration. The built-ins prove a fixed bridge; `custom` surfaces the registration's own. -/

variable (R : CustomRegistration)

/-- **`custom_sound` (the `→` half), parametric.** A satisfying trace of the registered circuit
PROVES the registered relation — by the registration's own `bridge` (forward). The same shape as
`merkle_sound`, but for WHATEVER relation the registered `vk` denotes. -/
theorem custom_sound (stmt : R.Statement) (wit : R.Witness)
    (h : R.Satisfies R.circuit stmt wit) : R.Relation stmt wit :=
  (R.bridge stmt wit).mp h

/-- **`custom_complete` (the `←` half), parametric.** A related pair has a satisfying trace of the
registered circuit — by the registration's own `bridge` (backward). The analog of
`merkle_complete`, for the registered relation. -/
theorem custom_complete (stmt : R.Statement) (wit : R.Witness)
    (h : R.Relation stmt wit) : R.Satisfies R.circuit stmt wit :=
  (R.bridge stmt wit).mpr h

/-- **`custom_bridge` — THE deliverable (the parametric analog of `merkle_bridge`).** For the
registered `(vk, Circuit, Relation)` triple, the circuit's satisfiability is EXACTLY the registered
relation: a satisfying trace certifies it (`custom_sound`) and every related pair has a satisfying
trace (`custom_complete`). This is the registration's OWN `bridge`, surfaced — the open extension
point inherits the §8 bridge shape verbatim, parametric over the relation `vk` denotes. NO new
primitive seam: the registration discharges the equivalence (the app proves it for its circuit, the
same obligation the built-ins meet); the only crypto residue is the app circuit's `extractable`,
consumed by `custom_verify_sound`, never by the bridge. -/
theorem custom_bridge (stmt : R.Statement) (wit : R.Witness) :
    R.Satisfies R.circuit stmt wit ↔ R.Relation stmt wit :=
  R.bridge stmt wit

-- TRIPWIRES: the parametric custom bridge is the registration's own equivalence, surfaced —
-- kernel-clean, NO seam beyond the app's `extractable`. The relation is whatever `vk` denotes.
#assert_axioms custom_sound
#assert_axioms custom_complete
#assert_axioms custom_bridge

/-! ## Layer B — the custom `VerifierKernel`: `verify` + `extractable` + DERIVED `verify_sound`.

Mirrors `MerkleVerifierKernel`, but PARAMETRIC over the registration's statement/witness/relation.
`verify` is the §8 oracle for the app's circuit over the disclosed statement; `extractable` (STARK
soundness for THAT circuit) gives "accept ⇒ a satisfying trace of `circuitOf vk` exists";
`custom_verify_sound` is DERIVED off the registration's bridge soundness half. -/

/-- **Layer B — the custom `VerifierKernel`, parametric over a `CustomRegistration`.** The §8
`verify` oracle for the registered circuit over the disclosed statement, and the STARK `extractable`
carrier for THAT circuit. `extract` unpacks `extractable`: an accepted proof witnesses a satisfying
trace of the registered circuit for SOME witness — the existence FRI/Fiat-Shamir soundness delivers
for the app's circuit. The class is keyed on the registration `R` (the `vk` it carries identifies
the kind), so distinct registrations are distinct kernels — content-addressing at the type level. -/
class CustomVerifierKernel (R : CustomRegistration) (Proof : Type u) where
  /-- **The §8 verify oracle** (`stark::verify` for the registered circuit): does `proof` discharge
  the disclosed `stmt` under the relation `vk` denotes? An opaque `Bool`; soundness is `extractable`. -/
  verify : R.Statement → Proof → Bool
  /-- **CARRIER — STARK extractability/soundness** for the registered circuit (FRI + Fiat-Shamir): an
  accepted proof witnesses a satisfying trace. A `Prop`; never proved, never `sorry`. -/
  extractable : Prop
  /-- `extractable` UNPACKED: an accepted proof witnesses a satisfying trace of the registered
  circuit `R.circuit` for SOME witness, at the disclosed statement. The form the bridge composes
  with — exactly the built-ins' `extract` shape, parametric over the registration. -/
  extract : extractable →
    ∀ (stmt : R.Statement) (proof : Proof), verify stmt proof = true →
      ∃ wit : R.Witness, R.Satisfies R.circuit stmt wit

variable {Proof : Type u}

/-- **`custom_verify_sound` — the DERIVED verify law, PARAMETRIC (the analog of
`merkle_verify_sound`).** Given the STARK-soundness carrier `extractable` for the registered
circuit, an accepted custom proof PROVES the registered relation holds for SOME witness:

    verify stmt proof = true  →  ∃ wit, Relation vk stmt wit

The proof composes `extract` (accept ⇒ satisfying trace, the crypto carrier) with `custom_bridge`'s
SOUNDNESS half (= the registration's own bridge `.mp`). The verify law is DERIVED, not assumed; the
only hypothesis is `extractable`. The relation is WHATEVER the registered `vk` denotes — so EVERY
future open kind inherits this derived soundness merely by registering its circuit + relation +
bridge. -/
theorem custom_verify_sound [K : CustomVerifierKernel R Proof]
    (hext : K.extractable) (stmt : R.Statement) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    ∃ wit : R.Witness, R.Relation stmt wit := by
  obtain ⟨wit, hsat⟩ := K.extract hext stmt proof haccept
  exact ⟨wit, (custom_bridge R stmt wit).mp hsat⟩

#assert_axioms custom_verify_sound

/-! ## Layer C — the kind obligation + the DIAL wiring at the registration's OWN floor.

A custom kind discloses whatever its app states — so the epistemic floor is PARAMETRIC: the
registration carries its own `dialFloor` (the built-ins pick `acceptanceOnly`/`selective`/
`fullDisclosure`; a bare custom kind defaults to `fullDisclosure`, claiming no privacy unless the
app does). We wire `EpistemicDial.DiscloseAt` to the verifier at THAT floor, exactly as the
built-ins do, with the floor read off the registration. -/

/-- **`KindObligation`** for a custom kind — statement algebra = the registration's `Statement`,
**dial floor = the registration's OWN `dialFloor`** (parametric: the app supplies it; default
`fullDisclosure`). The open analog of `merkleKindObligation`/`dfaKindObligation`. -/
structure KindObligation where
  /-- The public-input algebra: the registration's disclosed statement type. -/
  Statement : Type u
  /-- The dial floor — the registration's own, parametric. -/
  dialFloor : Dial

/-- The custom kind's obligation: statement = the registration's `Statement`, floor = the
registration's OWN `dialFloor` (parametric — the registering kind supplies its floor). -/
def customKindObligation : KindObligation where
  Statement := R.Statement
  dialFloor := R.dialFloor

@[simp] theorem customKindObligation_floor :
    (customKindObligation R).dialFloor = R.dialFloor := rfl

/-! ### The dial wiring — `DiscloseAt` instantiated at the custom verifier's OWN floor (the
registry/dial machinery lives at universe 0, so we instantiate over `Type`). The registration `R`
is fixed at universe 0 for the wiring section. -/

section Wiring

variable (R : CustomRegistration.{0}) {P : Type}

/-- A `Verifier R.Statement P` from the kernel's §8 `verify` oracle for the registered circuit. -/
def customVerifier [K : CustomVerifierKernel R P] : Verifier R.Statement P :=
  fun stmt proof => K.verify stmt proof

/-- The custom-kind registry: the §8 `verify` oracle installed at `custom R.vk` (content-addressed
by the registration's `vk`). -/
def customReg [CustomVerifierKernel R P]
    (base : Registry R.Statement P) : Registry R.Statement P :=
  fun j => if j = .custom R.vk then some (customVerifier R) else base j

/-- The `Verifiable` seam this kind dispatches through (explicit `base`, not auto-synthesized). -/
@[reducible] def customSeam [CustomVerifierKernel R P]
    (base : Registry R.Statement P) : Verifiable R.Statement P :=
  verifiableOfRegistry (customReg R base) (.custom R.vk)

/-- **`customDisclose` — the dial pinned to the custom verifier.** `accepts d` is the
position-independent `Discharged stmt proof`; `accepts_eq := fun _ => Iff.rfl`. Realizes
"instantiate `DiscloseAt` at the registration's OWN floor". -/
def customDisclose [CustomVerifierKernel R P]
    (base : Registry R.Statement P) (stmt : R.Statement) (proof : P) :
    @DiscloseAt Unit R.Statement P _ (customSeam R base) :=
  letI : Verifiable R.Statement P := customSeam R base
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := stmt
    wit := proof
    accepts := fun _ => Discharged stmt proof
    accepts_eq := fun _ => Iff.rfl }

/-- **`custom_dial_wired` — THE DIAL WIRING, PARAMETRIC (the analog of `merkle_dial_wired`).** The
custom kind's epistemic floor is the registration's OWN `dialFloor` (parametric), the dial's bottom
notch's acceptance bit IS the verifier's `Discharged` bit, and — given STARK `extractable` for the
registered circuit — an accepting proof PROVES the registered relation holds for SOME witness. The
dial is pinned to the per-`vk` verifier. -/
theorem custom_dial_wired [K : CustomVerifierKernel R P]
    (hext : K.extractable)
    (base : Registry R.Statement P) (stmt : R.Statement) (proof : P) :
    -- (1) the floor is the registration's own:
    (customKindObligation R).dialFloor = R.dialFloor ∧
    -- (2) the dial's bottom notch accepts IFF the custom verifier discharges:
    (@DiscloseAt.accepts Unit R.Statement P _ (customSeam R base)
        (customDisclose R base stmt proof) (⊥ : Dial)
      ↔ @Discharged R.Statement P (customSeam R base) stmt proof) ∧
    -- (3) and an accepting proof PROVES the registered relation (the cascade):
    (K.verify stmt proof = true →
      ∃ wit : R.Witness, R.Relation stmt wit) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact @DiscloseAt.accepts_bot_iff_discharged Unit R.Statement P _ (customSeam R base)
      (customDisclose R base stmt proof)
  · exact fun haccept => custom_verify_sound R hext stmt proof haccept

/-- **`custom_registry_cascade` — the §8 discharge through the registry, PARAMETRIC (the analog of
`merkle_registry_cascade`, and the open analog of `Predicate.custom_is_open_extension`).**
Registering the custom kind at `custom R.vk`, an accepted proof both `Discharged`s the kind's
predicate (the registry keystone, `registry_sound`) AND — given the STARK `extractable` carrier for
the registered circuit — PROVES the registered relation holds for SOME witness
(`custom_verify_sound`). The cascade `registry_sound ∘ custom_verify_sound`; the single trust
boundary is `extractable`. THIS is the open inheritance point: any future kind registers its
`(vk, circuit, relation, bridge)` and gets the full cascade for free. -/
theorem custom_registry_cascade [K : CustomVerifierKernel R P]
    (hext : K.extractable)
    (base : Registry R.Statement P)
    (stmt : R.Statement) (proof : P)
    (haccept : K.verify stmt proof = true) :
    (@Discharged R.Statement P (verifiableOfRegistry (customReg R base) (.custom R.vk))
        stmt proof)
      ∧ ∃ wit : R.Witness, R.Relation stmt wit := by
  refine ⟨?_, custom_verify_sound R hext stmt proof haccept⟩
  apply registry_sound (customReg R base) (.custom R.vk) stmt proof
  show registryVerify (customReg R base) (.custom R.vk) stmt proof = true
  unfold registryVerify customReg
  simp only [↓reduceIte]
  exact haccept

end Wiring

#assert_axioms custom_dial_wired
#assert_axioms custom_registry_cascade

/-! ## `Reference` — REGISTER a concrete toy `vk` (an equality circuit) + non-vacuity end-to-end.

The open extension point is non-vacuous: we REGISTER a real `(vk, circuit, relation, bridge)` — a
toy "equality" kind over `ℤ` (`Relation stmt wit := stmt = wit`, the circuit a single equality
constraint) — and witness the WHOLE cascade (bridge / verify-sound / dial / registry cascade) at it.
Registering a relation lights up the §8 machinery; NOT real crypto, but a real registration. -/

namespace Reference

/-- The toy equality circuit: a single trivial cell carrying the claimed pair (the "constraint" is
`stmt = wit`, checked by the bridge below). -/
structure EqCircuit where
  deriving Repr

/-- The toy circuit's `Satisfies`: the single equality constraint `stmt = wit` (the equality
gadget — a one-row AIR `wit - stmt = 0`, fully decided, no primitive seam). -/
def eqSatisfies : EqCircuit → Int → Int → Prop :=
  fun _ stmt wit => stmt = wit

/-- **The reference registration** — a toy "equality" kind keyed at `vk = 7`. Statement/witness =
`ℤ`; relation = `stmt = wit`; circuit = the trivial `EqCircuit`; the BRIDGE is `Iff.rfl` (the
equality circuit's satisfiability IS the equality relation, definitionally — a FULLY proved bridge,
no seam); dial floor = `fullDisclosure` (a bare custom kind claims no privacy). This is a genuine
registration: an app would supply exactly such a bundle. -/
@[reducible] def eqRegistration : CustomRegistration.{0} where
  vk := 7
  Circuit := EqCircuit
  Statement := Int
  Witness := Int
  Relation := fun stmt wit => stmt = wit
  circuit := {}
  Satisfies := eqSatisfies
  bridge := fun _ _ => Iff.rfl
  dialFloor := Dial.fullDisclosure

/-- Non-vacuity of the BRIDGE: at the registered equality kind, the circuit is satisfied at `(5, 5)`
iff `5 = 5` — both directions, through the registration's own `bridge`. -/
example : eqRegistration.Satisfies eqRegistration.circuit 5 5 ↔ (5 : Int) = 5 :=
  custom_bridge eqRegistration 5 5

/-- A degenerate reference custom verifier kernel over the equality registration (`def`, not a
global `instance`). `verify stmt proof` accepts iff `stmt = proof` (the equality check, here the
proof IS the claimed equal witness); `extractable := True`. `extract` rebuilds the satisfying trace:
acceptance means `stmt = proof`, so `eqSatisfies {} stmt proof` holds at witness `proof`. -/
@[reducible] def refKernel : CustomVerifierKernel eqRegistration Int where
  verify stmt proof := decide (stmt = proof)
  extractable := True
  extract := by
    intro _ stmt proof haccept
    simp only [decide_eq_true_eq] at haccept
    exact ⟨proof, haccept⟩

/-- The empty base registry over the toy `ℤ` custom statement/proof. -/
def base : Registry Int Int := fun _ => none

/-- Non-vacuity of `custom_verify_sound`: at the reference kernel an accepted proof (here proof `5`
at statement `5`) yields SOME witness satisfying the registered relation (`5 = 5`). -/
example : ∃ wit : Int, eqRegistration.Relation 5 wit :=
  custom_verify_sound eqRegistration (K := refKernel) trivial 5 5 (by decide)

/-- Non-vacuity of the FULL cascade: at the reference kernel an accepted proof both `Discharged`s
the registry predicate at `custom 7` AND proves the registered relation. A NAMED witness so its
axiom footprint is checkable — the open extension point, fully lit. -/
theorem reference_cascade_nonvacuous :
    (@Discharged Int Int
        (verifiableOfRegistry (@customReg eqRegistration Int refKernel base) (.custom 7))
        5 5)
      ∧ ∃ wit : Int, eqRegistration.Relation 5 wit :=
  custom_registry_cascade eqRegistration (K := refKernel) trivial base 5 5 (by decide)

-- The non-vacuity witness's axiom footprint (the task's `#print axioms` requirement): the reference
-- cascade rests only on the standard axioms — NO `sorryAx`, NO crypto axiom.
#print axioms reference_cascade_nonvacuous

/-- Non-vacuity of the dial wiring: the floor is the registration's own (`fullDisclosure` for the
bare equality kind), the dial's bottom notch is the verifier's bit, and an accepting proof proves
the registered relation. -/
example :
    (customKindObligation eqRegistration).dialFloor = Dial.fullDisclosure :=
  (custom_dial_wired eqRegistration (K := refKernel) trivial base 5 5).1

/-- The open extension point separates by `vk` (content-addressing): a DIFFERENT `vk` is a distinct
registry slot, so the equality kind at `custom 7` is not consulted for `custom 8` — `Predicate`'s
`custom_distinct_vk`, instantiated at the reference registration. -/
example (v : Verifier Int Int) (stmt wit : Int) :
    registryVerify (fun k => if k = .custom 7 then some v else base k) (.custom 8) stmt wit
      = registryVerify base (.custom 8) stmt wit :=
  custom_distinct_vk base 7 8 (by decide) v stmt wit

end Reference

-- TRIPWIRES: the parametric custom bridge + derived verify-soundness + cascade + dial wiring are
-- kernel-clean. The bridge IS the registration's own equivalence (the app proves it for its
-- circuit, the SAME obligation the built-ins meet — the reference's is `Iff.rfl`, fully proved);
-- the ONLY cryptographic residue is the `extractable` carrier (passed as a hypothesis), never a
-- hidden `sorry`. This completes ALL EIGHT `WitnessedKind`s — the registry is OPEN and COMPLETE.
#assert_axioms custom_bridge
#assert_axioms custom_verify_sound
#assert_axioms custom_registry_cascade
#assert_axioms custom_dial_wired

end Dregg2.Crypto.Custom
