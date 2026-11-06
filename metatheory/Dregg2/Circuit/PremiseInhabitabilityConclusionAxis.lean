/-
# `Dregg2.Circuit.PremiseInhabitabilityConclusionAxis` — the TEN remaining carrier-gated kernels,
settled on the CONCLUSION axis.

`PremiseInhabitabilitySweepSettled` §9 found a THIRD vacuity mode that `CarrierLive` cannot see: if a
gated theorem's conclusion is TOTAL — true on every index — the theorem holds with the carrier AND
the acceptance hypothesis deleted, while the axiom audit stays clean and no `sorry` exists. It fired
that check at THREE of R11's thirteen carrier-gated kernels (`NonMembership` MODE 3 permanently,
`Merkle` MODE 3 at the reference node hash, `Temporal` NOT MODE 3) and named the remaining ten as
ENGINEERING: "one exhibited counterexample or one totality proof each".

This module is that engineering pass. All TEN are settled here as theorems:
`PortalFloor`, `Pedersen`, `Custom`, `Deco`, `Dfa`, `DfaAcceptanceAir`, `Cfg`, `Bridge`,
`BlindedSet`, `RangeProof`.

## §A the headline

**THREE MORE ARE MODE 3, all at their own IN-TREE reference instance** — and each one is the
`∃-image` shape: the conclusion asks for a preimage under an operation the reference instance makes
SURJECTIVE, so the existential is discharged by algebra with no proof in sight.

  * `Custom` — `custom_verify_sound`'s `∃ wit, R.Relation stmt wit` at the in-tree `eqRegistration`
    (`Relation stmt wit := stmt = wit`) is `∃ wit, stmt = wit`. TOTAL, witness `stmt`. The module's
    own non-vacuity example (`Custom.lean:353`) is that tautology. §3.
  * `Bridge` — `∃ v vDigest salt, c = compress vDigest salt ∧ threshold ≤ v` at
    `refCompress := (· + ·)`: take `vDigest := c`, `salt := 0`, `v := threshold`. TOTAL. §8.
  * `BlindedSet` — `∃ member, MerkleMembers compress root member` at `refCompress := (· + ·)`:
    the member is existential TOO, so this is weaker than the Merkle conclusion §9.3 already
    refuted. TOTAL. §9.

So MODE 3 now stands at FIVE of thirteen, and in every case the polarity INVERTS exactly as §9.3
found at Merkle: the REFERENCE instance is the vacuous one and the FORGE sibling — the broken oracle
the carrier repair uses as its refutation witness — is the one whose conclusion BITES.

**SEVEN are NOT MODE 3**, and SIX of those are refuted at EVERY instantiation — the counterexample
is a disclosed STATEMENT, so no oracle, no carrier and no deployment can repair it:

  * `Pedersen` (§2) — a disclosed statement whose commitment sums differ, at any `commit`.
  * `Deco` (§4) — a statement with `amountCents = 0`, at any signature/MAC/hash/schema.
  * `Dfa` (§5) — an automaton whose accept predicate is empty.
  * `DfaAcceptanceAir` (§6) — a public `finalState` outside the image of the table's `step`.
  * `Cfg` (§7) — the rule-free grammar, whose language is empty.
  * `RangeProof` (§10) — an empty window `hi < lo`, at any `commit`.

The seventh is per-instance because its conclusion is KERNEL data rather than statement data:

  * `PortalFloor` (§1) — `Holds` is a field of the class, so the verdict is per-instance. BOTH
    in-tree instances bite; a lawful MODE-3 instantiation is exhibited so this is not read as a
    class-level clearance.

## §B what the ten checks forced into the instrument (§0)

Two refinements, both needed by a kernel below and neither expressible with `ConclusionTotal` alone:

  * **`ConclusionTotalOn S C`** — RELATIVE totality: the conclusion is free on the sub-domain a
    statement-side predicate `S` carves out. `Deco` and `RangeProof` are not MODE 3, and yet at
    their in-tree reference kernels their conclusion is derivable, carrier deleted, from a
    predicate of the DISCLOSED STATEMENT ALONE (`1 ≤ amountCents`; `lo ≤ commitment ≤ hi`). A
    verifier can evaluate that predicate itself. The gated theorem is then worth exactly `S` — which
    is not nothing, and is not what "an accepted STARK proof proves X" advertises.
  * **`CarrierIdle acc C`** — the conclusion follows from ACCEPTANCE with the carrier deleted.
    MODE 3 is the special case where acceptance goes too. This is what `RangeProof`'s reference
    kernel exhibits at full strength: its conclusion is DEFINITIONALLY its acceptance test, so
    `range_verify_sound` there is `accept → accept` and the two crypto carriers buy nothing.

And one structural observation that costs one line and re-reads the whole sibling carrier repair
(§11): **a PROVED carrier is an IDLE carrier.** Wherever `extractable` is discharged by an in-tree
theorem — which is exactly what the 2026-07-25 repair did at all eight reference kernels — the gated
theorem carries no assumption at all, so no reference instance can ever witness that the carrier is
load-bearing. That work is done entirely by the FORGE sibling refutation, and this theorem is why
`CarrierAudit`'s `refuted` field is the whole content of the repair rather than half of it.

## §C ⚑ WHAT THIS DOES NOT SETTLE

The DEPLOYMENT verdict for all thirteen is UNCHANGED and UNKNOWN, for the reason
`PremiseInhabitabilitySweepSettled` §9.6 gives: settling it needs a kernel whose `compress` is real
Poseidon2 and whose `verify` is the deployed `stark::verify`, and that symbol is `opaque`/`@[extern]`
with NO Lean semantics. Nothing here touches that. Every MODE-3 verdict below that says "at the
reference instance" is a statement about a TOY oracle; every "at every instantiation" verdict is
stronger and says so in the theorem name.

Nor does a NOT-MODE-3 verdict mean a kernel is sound: it means the conclusion excludes SOMETHING, so
the theorem is not free on the conclusion axis. The carrier axis (`CarrierAudit`) and the acceptance
axis (`CarrierLive`) are separate, and `CarrierBites` is the conjunction of all three.
-/
import Dregg2.Circuit.PremiseInhabitabilitySweepSettled
import Dregg2.Crypto.Pedersen
import Dregg2.Crypto.Custom
import Dregg2.Crypto.Deco
import Dregg2.Crypto.Dfa
import Dregg2.Crypto.DfaAcceptanceAir
import Dregg2.Crypto.Cfg
import Dregg2.Crypto.Bridge
import Dregg2.Crypto.BlindedSet
import Dregg2.Crypto.RangeProof

namespace Dregg2.Circuit.PremiseInhabitabilityConclusionAxis

universe u v

open Dregg2.Circuit.PremiseInhabitability (Acc AcceptsSome RejectsAll ofBool)
open Dregg2.Circuit.PremiseInhabitabilitySweep (CarrierLive)
open Dregg2.Circuit.PremiseInhabitabilitySweepSettled
  (ConclusionTotal ConclusionBites CarrierBites totalConclusion_makes_the_gated_theorem_free
   not_conclusionTotal_of_conclusionBites carrierBites_excludes_totalConclusion)

set_option autoImplicit false

/-! ## §0 — THE INSTRUMENT, EXTENDED BY WHAT THE TEN CHECKS ACTUALLY NEEDED.

`ConclusionTotal` is a yes/no question and two of the ten answer "no" while still being free in a way
that matters. The two definitions here are the shapes those kernels forced. -/

/-- **`ConclusionTotalOn S C`** — the conclusion holds everywhere a STATEMENT-SIDE predicate `S`
holds. `ConclusionTotal` is `ConclusionTotalOn (fun _ => True)`. -/
def ConclusionTotalOn {ι : Type u} (S C : ι → Prop) : Prop := ∀ i, S i → C i

/-- **RELATIVE MODE 3.** On the sub-domain `S`, the gated theorem is free: carrier deleted,
acceptance deleted. If `S` is decidable from the disclosed statement, the theorem delivers exactly
`S` — whatever its name advertises. -/
theorem totalOn_makes_the_gated_theorem_free_on_S {ι : Type u} (carrier : Prop) (acc : Acc ι)
    {S C : ι → Prop} (h : ConclusionTotalOn S C) : carrier → ∀ i, S i → acc i → C i :=
  fun _ i hs _ => h i hs

theorem conclusionTotal_of_totalOn_true {ι : Type u} {C : ι → Prop}
    (h : ConclusionTotalOn (fun _ => True) C) : ConclusionTotal C := fun i => h i trivial

/-- **`CarrierIdle acc C`** — the conclusion follows from ACCEPTANCE ALONE, with the carrier
deleted. Strictly weaker than MODE 3 (which deletes acceptance too) and strictly stronger than
nothing: it says the `extractable` `Prop` — the whole cryptographic trust boundary the class exists
to name — is doing no work at this instantiation. -/
def CarrierIdle {ι : Type u} (acc : Acc ι) (C : ι → Prop) : Prop := ∀ i, acc i → C i

/-- MODE 3 implies the carrier is idle: deleting acceptance as well is more, not less. -/
theorem carrierIdle_of_conclusionTotal {ι : Type u} {acc : Acc ι} {C : ι → Prop}
    (h : ConclusionTotal C) : CarrierIdle acc C := fun i _ => h i

/-- An idle carrier makes the gated theorem free of its carrier. -/
theorem carrierIdle_makes_the_gated_theorem_carrier_free {ι : Type u} (carrier : Prop)
    {acc : Acc ι} {C : ι → Prop} (h : CarrierIdle acc C) : carrier → ∀ i, acc i → C i :=
  fun _ i hi => h i hi

/-- …and `CarrierIdle` is STRICTLY weaker than `ConclusionTotal`: the accept-`0`-only predicate on
`ℕ` with `C := (· = 0)` has an idle carrier and a conclusion that BITES. So a NOT-MODE-3 verdict does
NOT rescue a carrier from idleness, which is why §4 and §10 report both. -/
theorem carrierIdle_does_not_imply_conclusionTotal :
    ∃ (acc : Acc ℕ) (C : ℕ → Prop), CarrierIdle acc C ∧ ConclusionBites C := by
  refine ⟨ofBool (fun n => decide (n = 0)), fun n => n = 0, ?_, ⟨1, by decide⟩⟩
  intro i hi
  exact of_decide_eq_true hi

/-! ## §1 — `PortalFloor.VerifierKernel`: NOT MODE 3 at either in-tree instance.

`verifier_floor_sound`'s conclusion is `K.Holds stmt` for a `Holds : Stmt → Prop` the INSTANCE
supplies, so no class-level verdict exists — and unlike `Custom` and `Cfg` (whose parametricity §3
and §7 also face) this class has TWO concrete in-tree instances, so the per-instance question is
answerable at both. Both BITE. The parametric escape is exhibited too, so the reading is
"this class's verdict is per-instance and both its instances pass", not "this class is safe". -/

section PortalFloorRow

open Dregg2.Crypto.PortalFloor

/-- **THE REFERENCE INSTANCE BITES.** `Holds stmt := stmt = 0` fails at `stmt = 1`, so the STARK
floor's conclusion excludes something at the instance the tree ships. -/
theorem portalFloor_reference_conclusion_bites :
    ConclusionBites (fun s : Nat => (Reference.instVerifierKernel).Holds s) := by
  refine ⟨1, ?_⟩
  intro h
  have h' : (1 : Nat) = 0 := h
  exact absurd h' (by decide)

/-- **AND SO DOES THE FORGE INSTANCE** — `Holds _ := False` bites everywhere. Note the polarity here
is NOT the Merkle/Bridge/BlindedSet inversion: at this class both siblings are informative on the
conclusion axis, and the carrier axis is what separates them
(`instVerifierKernel_extractable` vs `instVerifierForge_not_extractable`). -/
theorem portalFloor_forge_conclusion_bites :
    ConclusionBites (fun s : Nat => (Reference.instVerifierForge).Holds s) :=
  ⟨0, id⟩

/-- A lawful `VerifierKernel` whose `Holds` is TOTAL — the class does not exclude MODE 3, it just
does not exhibit it. `verify_sound` is dischargeable for free precisely because the conclusion is. -/
@[reducible] def totalHoldsKernel : VerifierKernel Nat Nat where
  Holds _ := True
  verify _ _ := true
  extractable := True
  verify_sound := fun _ _ _ _ => trivial

/-- **THE PARAMETRIC ESCAPE, EXHIBITED.** At `totalHoldsKernel` the floor's conclusion is TOTAL and
`verifier_floor_sound` holds with the carrier and acceptance deleted — while `CarrierLive` reports
green (the carrier is `True` and the verifier accepts every proof). So §1's verdict is a statement
about the two in-tree instances and not about the class. -/
theorem portalFloor_admits_a_mode3_instantiation :
    ConclusionTotal (fun s : Nat => (totalHoldsKernel).Holds s)
      ∧ CarrierLive (totalHoldsKernel).extractable (ofBool fun p : Nat × Nat =>
          (totalHoldsKernel).verify p.1 p.2)
      ∧ ((totalHoldsKernel).extractable → ∀ s : Nat, ∀ p : Nat,
          (totalHoldsKernel).verify s p = true → (totalHoldsKernel).Holds s) :=
  ⟨fun _ => trivial, ⟨trivial, ⟨(0, 0), rfl⟩⟩, fun _ _ _ _ => trivial⟩

/-- **§1'S VERDICT.** NOT MODE 3 at either in-tree instance; MODE 3 reachable in the class. -/
theorem portalFloor_verdict :
    ¬ ConclusionTotal (fun s : Nat => (Reference.instVerifierKernel).Holds s)
      ∧ ¬ ConclusionTotal (fun s : Nat => (Reference.instVerifierForge).Holds s)
      ∧ ConclusionTotal (fun s : Nat => (totalHoldsKernel).Holds s) :=
  ⟨not_conclusionTotal_of_conclusionBites portalFloor_reference_conclusion_bites,
   not_conclusionTotal_of_conclusionBites portalFloor_forge_conclusion_bites,
   fun _ => trivial⟩

end PortalFloorRow

/-! ## §2 — `PedersenVerifierKernel`: NOT MODE 3 at EVERY instantiation.

`pedersen_verify_sound` concludes `∃ circuit, statementOf commit circuit = stmt ∧ Conserves circuit`.
The `statementOf` equation pins the trace's per-note commitments to the DISCLOSED lists, and
`Conserves`'s first conjunct equates their group sums — so the conclusion FORCES a relation between
two public fields of the statement. That is what a non-total conclusion looks like, and it holds at
every `commit`, every `Digest`, and every kernel: no toy oracle and no deployment can make this one
free. -/

section PedersenRow

open Dregg2.Crypto.Pedersen

/-- **THE CONCLUSION FORCES A PUBLIC EQUATION.** Any trace realizing the conclusion equates the
disclosed input- and output-commitment SUMS — a fact about the statement alone. -/
theorem pedersen_conclusion_forces_balanced_disclosure {Digest : Type u} [AddCommGroup Digest]
    (commit : Int → Int → Digest) (stmt : Statement Digest)
    (h : ∃ circuit : CircuitIR, statementOf commit circuit = stmt ∧ Conserves commit circuit) :
    stmt.insC.sum = stmt.outsC.sum := by
  obtain ⟨circuit, hst, hcons⟩ := h
  have hin : stmt.insC = circuit.ins.map (noteCommit commit) := by rw [← hst]; rfl
  have hout : stmt.outsC = circuit.outs.map (noteCommit commit) := by rw [← hst]; rfl
  rw [hin, hout]
  exact hcons.1

/-- **NOT MODE 3, AT EVERY INSTANTIATION.** At any statement whose disclosed commitment sums differ,
the conclusion is FALSE — for every `commit`, every `Digest`, every kernel. -/
theorem pedersen_conclusion_bites_at_unbalanced_disclosures {Digest : Type u} [AddCommGroup Digest]
    (commit : Int → Int → Digest) (stmt : Statement Digest)
    (hne : stmt.insC.sum ≠ stmt.outsC.sum) :
    ¬ (∃ circuit : CircuitIR, statementOf commit circuit = stmt ∧ Conserves commit circuit) :=
  fun h => hne (pedersen_conclusion_forces_balanced_disclosure commit stmt h)

/-- Fired at a concrete disclosure over `ℤ`: inputs summing to `1`, outputs to `0`. -/
theorem pedersen_conclusion_bites (commit : Int → Int → Int) :
    ConclusionBites (fun stmt : Statement Int =>
      ∃ circuit : CircuitIR, statementOf commit circuit = stmt ∧ Conserves commit circuit) :=
  ⟨{ insC := [1], outsC := [0] },
   pedersen_conclusion_bites_at_unbalanced_disclosures commit _ (by decide)⟩

/-- **§2'S VERDICT** — retaining the kernel as the subject so a change to the class's conclusion
breaks this rather than letting the finding lapse. -/
theorem pedersen_verdict (K : PedersenVerifierKernel Int Int) :
    ¬ ConclusionTotal (fun stmt : Statement Int =>
      ∃ circuit : CircuitIR, statementOf K.commit circuit = stmt ∧ Conserves K.commit circuit) :=
  not_conclusionTotal_of_conclusionBites (pedersen_conclusion_bites K.commit)

end PedersenRow

/-! ## §3 — `CustomVerifierKernel`: **MODE 3 AT THE IN-TREE REFERENCE REGISTRATION.**

`custom_verify_sound` concludes `∃ wit, R.Relation stmt wit`, parametric in the registration — so
`PremiseInhabitabilitySweepSettled` §9.6 recorded it as "whatever the registration says". That is
right about the class and it is not the end of the question, because the tree SHIPS a registration:
`Reference.eqRegistration`, whose relation is `stmt = wit` over `ℤ`. `∃ wit, stmt = wit` is a
tautology of equality — witness `stmt` — so the conclusion is TOTAL and `custom_verify_sound` is
free at the only registration anyone has written down.

And the polarity inverts exactly as it does at Merkle: at the FORGE registration (`Relation` = the
empty relation, the sibling whose carrier the repair REFUTES) the conclusion bites everywhere. -/

section CustomRow

open Dregg2.Crypto.Custom

/-- **THE TAUTOLOGY.** The reference registration's conclusion, with every hypothesis removed. -/
theorem eqRegistration_conclusion_is_total :
    ConclusionTotal (fun stmt : Reference.eqRegistration.Statement =>
      ∃ wit : Reference.eqRegistration.Witness, Reference.eqRegistration.Relation stmt wit) :=
  fun stmt => ⟨stmt, rfl⟩

/-- **AND THEREFORE `custom_verify_sound` IS FREE AT THE REFERENCE REGISTRATION** — the gated shape
holds with the carrier and the acceptance hypothesis DELETED, at ANY kernel over that registration
(the sibling lane's repaired `refKernel` included). The `extractable` carrier is doing no work. -/
theorem custom_verify_sound_is_free_at_the_reference_registration
    (K : CustomVerifierKernel Reference.eqRegistration Int) :
    K.extractable → ∀ p : Reference.eqRegistration.Statement × Int,
      (ofBool fun q : Reference.eqRegistration.Statement × Int => K.verify q.1 q.2) p →
        ∃ wit : Reference.eqRegistration.Witness, Reference.eqRegistration.Relation p.1 wit :=
  totalConclusion_makes_the_gated_theorem_free _ _ (fun p => eqRegistration_conclusion_is_total p.1)

/-- **THE MODULE'S OWN NON-VACUITY WITNESS IS THE TAUTOLOGY.** `Custom.lean:353` exhibits
`∃ wit : ℤ, eqRegistration.Relation 5 wit` by running the whole cascade through
`custom_verify_sound`. Here is the same proposition with the kernel, the carrier and the accepted
proof all deleted. -/
theorem custom_reference_nonvacuity_witness_needs_no_kernel :
    ∃ wit : Int, Reference.eqRegistration.Relation 5 wit :=
  ⟨5, rfl⟩

/-- **THE POLARITY INVERSION, AT THE REGISTRATION AXIS.** The forge registration — the one whose
carrier `forgeKernel_not_extractable` refutes — has a conclusion that BITES everywhere, while the
reference registration's is a tautology. On the conclusion axis the broken sibling is the
informative one. -/
theorem custom_conclusion_axis_inverts_against_the_carrier_axis :
    ConclusionTotal (fun stmt : Reference.eqRegistration.Statement =>
        ∃ wit : Reference.eqRegistration.Witness, Reference.eqRegistration.Relation stmt wit)
      ∧ ConclusionBites (fun stmt : Reference.emptyRegistration.Statement =>
        ∃ wit : Reference.emptyRegistration.Witness, Reference.emptyRegistration.Relation stmt wit) := by
  refine ⟨eqRegistration_conclusion_is_total, ⟨(0 : Int), ?_⟩⟩
  rintro ⟨_, hf⟩
  exact hf.elim

/-- `CarrierBites` is unreachable at the reference registration, whatever kernel is installed. -/
theorem custom_reference_carrierBites_is_unreachable
    (K : CustomVerifierKernel Reference.eqRegistration Int)
    (acc : Acc Reference.eqRegistration.Statement) :
    ¬ CarrierBites K.extractable acc
        (fun stmt => ∃ wit : Reference.eqRegistration.Witness,
          Reference.eqRegistration.Relation stmt wit) :=
  fun h => carrierBites_excludes_totalConclusion h eqRegistration_conclusion_is_total

end CustomRow

/-! ## §4 — `DecoVerifierKernel`: NOT MODE 3 at every instantiation, and RELATIVELY total at the
reference kernel.

`deco_verify_sound` concludes `∃ w, DecoRelation … stmt w`. Conjunct (5) of `DecoRelation` is
`1 ≤ stmt.facts.amountCents` — a predicate of the DISCLOSED STATEMENT with no witness in it — so the
existential cannot escape it and the conclusion BITES at every zero-amount statement, at every
oracle choice. That settles MODE 3 negatively, universally.

It does not settle what the theorem is WORTH, and the answer at the in-tree reference kernel is:
exactly conjunct (5). `refKernel_extractable`'s own proof builds its satisfying trace from the
amount hypothesis alone (the session key is echoed, the MAC oracle accepts everything, the opening is
canonical) — so the conclusion is derivable, carrier deleted, from `1 ≤ amountCents`, which the
verifier can evaluate itself. `ConclusionTotalOn` is the shape of that reading. -/

section DecoRow

open Dregg2.Crypto.Deco

/-- The conclusion FORCES a statement-side fact: the disclosed amount is non-zero. -/
theorem deco_conclusion_forces_nonzero_amount {Dg : Type}
    (sigVerify macVerify : Dg → Dg → Dg → Bool) (compress : Dg → Dg → Dg)
    (encode : PaymentFacts → Dg) (stmt : Statement Dg)
    (h : ∃ w : CircuitIR Dg, DecoRelation sigVerify macVerify compress encode stmt w) :
    1 ≤ stmt.facts.amountCents := by
  obtain ⟨_, _, _, _, _, hamt⟩ := h
  exact hamt

/-- **NOT MODE 3, AT EVERY INSTANTIATION.** At a zero-amount statement the conclusion is FALSE for
every witness — for every signature oracle, every MAC oracle, every hash and every schema. -/
theorem deco_conclusion_bites_at_zero_amount {Dg : Type}
    (sigVerify macVerify : Dg → Dg → Dg → Bool) (compress : Dg → Dg → Dg)
    (encode : PaymentFacts → Dg) (stmt : Statement Dg) (hzero : stmt.facts.amountCents = 0) :
    ¬ (∃ w : CircuitIR Dg, DecoRelation sigVerify macVerify compress encode stmt w) := by
  intro h
  have := deco_conclusion_forces_nonzero_amount sigVerify macVerify compress encode stmt h
  omega

theorem deco_conclusion_bites {Dg : Type} (d₀ : Dg)
    (sigVerify macVerify : Dg → Dg → Dg → Bool) (compress : Dg → Dg → Dg)
    (encode : PaymentFacts → Dg) :
    ConclusionBites (fun stmt : Statement Dg =>
      ∃ w : CircuitIR Dg, DecoRelation sigVerify macVerify compress encode stmt w) :=
  ⟨{ serverKey := d₀, facts := ⟨0, 840, 1, 999⟩ },
   deco_conclusion_bites_at_zero_amount sigVerify macVerify compress encode _ rfl⟩

/-- **§4'S FIRST VERDICT — NOT MODE 3**, at every kernel. -/
theorem deco_verdict (K : DecoVerifierKernel Int Unit) :
    ¬ ConclusionTotal (fun stmt : Statement Int =>
      ∃ w : CircuitIR Int, DecoRelation K.sigVerify K.macVerify K.compress K.encode stmt w) :=
  not_conclusionTotal_of_conclusionBites
    (deco_conclusion_bites (0 : Int) K.sigVerify K.macVerify K.compress K.encode)

/-- **§4'S SECOND VERDICT — RELATIVELY TOTAL AT THE REFERENCE KERNEL.** On every statement with a
non-zero amount the conclusion holds, carrier and acceptance deleted. So at this instance the
DECO cascade delivers the amount comparison and NOTHING about Stripe's signature: the witness is
built by echoing the server key into the session key, and the reference MAC oracle accepts
everything. -/
theorem deco_reference_conclusion_is_total_on_nonzero_amount :
    ConclusionTotalOn (fun stmt : Statement Int => 1 ≤ stmt.facts.amountCents)
      (fun stmt : Statement Int => ∃ w : CircuitIR Int,
        DecoRelation Reference.refSig Reference.refMac Reference.refCompress Reference.refEncode
          stmt w) := by
  intro stmt hamt
  refine ⟨{ sessionKey := stmt.serverKey, sig := 0,
            transcriptCommit := Reference.refEncode stmt.facts + 7, tag := 0,
            fieldsDigest := Reference.refEncode stmt.facts, salt := 7, amtBits := [] },
          ?_, rfl, rfl, rfl, hamt⟩
  show decide (stmt.serverKey = stmt.serverKey) = true
  simp

/-- **THE CONCLUSION DOES NOT SEPARATE ACCEPTED FROM REJECTED STATEMENTS AT THE REFERENCE KERNEL.**
It holds at a statement the reference verifier demonstrably REJECTS (server key `12 ≠ 11`), so the
authentication half of the DECO claim is not what the gated theorem is delivering there. The
rejection hypothesis is named `_hrej` because the proof does not use it. -/
theorem deco_reference_conclusion_holds_at_a_rejected_statement
    (_hrej : Reference.refKernel.verify { serverKey := 12, facts := ⟨2500, 840, 1, 999⟩ } ()
      = false) :
    ∃ w : CircuitIR Int, DecoRelation Reference.refSig Reference.refMac Reference.refCompress
      Reference.refEncode { serverKey := 12, facts := ⟨2500, 840, 1, 999⟩ } w :=
  deco_reference_conclusion_is_total_on_nonzero_amount _ (by decide)

/-- …and that statement really is rejected — so the previous theorem is not idle. -/
theorem deco_reference_rejects_that_statement :
    Reference.refKernel.verify { serverKey := 12, facts := ⟨2500, 840, 1, 999⟩ } () = false := by
  decide

/-- **THE CARRIER IS IDLE AT THE REFERENCE KERNEL.** Acceptance alone implies the conclusion: the
`extractable` `Prop` — the STARK trust boundary the class exists to name — buys nothing here. -/
theorem deco_reference_carrier_is_idle :
    CarrierIdle (ofBool fun p : Statement Int × Unit => Reference.refKernel.verify p.1 p.2)
      (fun p : Statement Int × Unit => ∃ w : CircuitIR Int,
        DecoRelation Reference.refSig Reference.refMac Reference.refCompress Reference.refEncode
          p.1 w) := by
  rintro ⟨stmt, u⟩ hacc
  have hacc' : decide (stmt.serverKey = 11 ∧ 1 ≤ stmt.facts.amountCents) = true := hacc
  simp only [decide_eq_true_eq] at hacc'
  exact deco_reference_conclusion_is_total_on_nonzero_amount stmt hacc'.2

end DecoRow

/-! ## §5 — `DfaVerifierKernel`: NOT MODE 3 at every instantiation.

`dfa_verify_sound` concludes `∃ trace, DfaAccepts stmt.δ stmt.q₀ stmt.accept trace`. The existential
is over the whole run, which is what makes MODE 3 plausible here — but `DfaAccepts` demands a
NON-EMPTY trace whose last `next` is ACCEPTING, so the conclusion forces the disclosed automaton to
have a reachable accepting state. At an automaton that accepts nothing there is no such trace.

⚑ 2026-11-05: this section's subject is the UNBOUND kernel, retained in `Dfa.lean` exactly for this
row and for its falsifier. The deployed-shape statement is now `Dfa.dfa_bound_verify_sound` over
`Dfa.BoundStatement` (the automaton PLUS a content commitment `c`), whose conclusion
`∃ w, commit w = stmt.c ∧ ∃ trace, DfaAccepts … ∧ traceWord trace = w` is a property of the RECORD
as well as the automaton; `Dfa.Reference.splice_fails_bound` exhibits the acceptance test that meets
this section's conclusion and refutes the bound one. The verdict below is unchanged (the bound
conclusion implies the unbound one, so it bites wherever this does). -/

section DfaRow

open Dregg2.Crypto.Dfa

/-- The conclusion FORCES the disclosed accept predicate to be non-empty. -/
theorem dfa_conclusion_forces_a_nonempty_accept_set {State Sym : Type}
    (stmt : Statement State Sym)
    (h : ∃ trace : List (Step State Sym), DfaAccepts stmt.δ stmt.q₀ stmt.accept trace) :
    ∃ q : State, stmt.accept q := by
  obtain ⟨_, _, last, _, _, _, hacc, _, _⟩ := h
  exact ⟨last.next, hacc⟩

/-- **NOT MODE 3, AT EVERY INSTANTIATION.** At an automaton whose accept predicate is empty, no run
satisfies the conclusion — whatever oracle, carrier or deployment is installed. -/
theorem dfa_conclusion_bites {State Sym : Type} (q₀ : State)
    (δ : State → Sym → State → Prop) :
    ConclusionBites (fun stmt : Statement State Sym =>
      ∃ trace : List (Step State Sym), DfaAccepts stmt.δ stmt.q₀ stmt.accept trace) := by
  refine ⟨{ δ := δ, q₀ := q₀, accept := fun _ => False }, ?_⟩
  intro h
  obtain ⟨q, hq⟩ := dfa_conclusion_forces_a_nonempty_accept_set _ h
  exact hq.elim

/-- **§5'S VERDICT.** No kernel is retained as the subject here, and deliberately: `dfa_verify_sound`'s
conclusion mentions ONLY the disclosed statement, so there is no kernel field a regression could
change. A kernel-shaped hypothesis would be decoration. -/
theorem dfa_verdict {State Sym : Type} (q₀ : State) (δ : State → Sym → State → Prop) :
    ¬ ConclusionTotal (fun stmt : Statement State Sym =>
      ∃ trace : List (Step State Sym), DfaAccepts stmt.δ stmt.q₀ stmt.accept trace) :=
  not_conclusionTotal_of_conclusionBites (dfa_conclusion_bites q₀ δ)

/-- **AND THE BITE IS ENTIRELY STATEMENT-SIDE**, which is the honest reading of what the theorem
delivers at the `fullDisclosure` floor: at a permissive automaton the conclusion holds with carrier
and acceptance deleted, so the gated theorem's content is a property of the PUBLIC automaton, not of
the proof. `ConclusionTotalOn` names the sub-domain. -/
theorem dfa_conclusion_is_free_at_a_permissive_automaton {State Sym : Type} (q₀ : State) (y : Sym) :
    ∃ trace : List (Step State Sym),
      DfaAccepts (fun _ _ _ => True) q₀ (fun _ => True) trace :=
  ⟨[⟨q₀, y, q₀⟩], ⟨q₀, y, q₀⟩, ⟨q₀, y, q₀⟩, rfl, rfl, rfl, trivial,
    fun _ _ => trivial, trivial⟩

end DfaRow

/-! ## §6 — `DfaAirVerifierKernel`: NOT MODE 3 at every instantiation.

`dfaAir_verify_sound` concludes `∃ rows, Satisfies … rows ∧ finalState = classify d (symbols rows)`.
`Satisfies` demands a NON-EMPTY row list whose last row's `next` is the public `finalState` (B2) and
whose every row's `next` is a table cell `d.step state sym` (TABLE). So the conclusion forces the
public `finalState` into the IMAGE of the disclosed table — refutable at any DFA that never reaches
the claimed classification. -/

section DfaAirRow

open Dregg2.Crypto (CryptoPrimitives)
open Dregg2.Crypto.DfaAcceptanceAir

/-- A non-empty list has a last element, and it is a member. Proved here rather than hunted in the
library so §6 does not ride on a lemma name. -/
theorem getLast?_mem {α : Type u} (l : List α) (h : l ≠ []) :
    ∃ a, l.getLast? = some a ∧ a ∈ l := by
  induction l with
  | nil => exact absurd rfl h
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨x, rfl, by simp⟩
    | cons y ys =>
      obtain ⟨a, ha, hmem⟩ := ih (by simp)
      exact ⟨a, by rw [List.getLast?_cons_cons]; exact ha, by simp [hmem]⟩

/-- The conclusion FORCES the public `finalState` to be a table cell of the disclosed DFA. -/
theorem dfaAir_conclusion_forces_finalState_in_the_table_image {St Sy Dg : Type} [AddCommGroup Dg]
    [CryptoPrimitives Dg] (stmt : Statement St Sy Dg)
    (h : ∃ rows : List (Row St Sy Dg),
      Satisfies stmt.d stmt.encState stmt.encSym stmt.tableCommitment stmt.initialState
        stmt.finalState stmt.routeCommitment rows
      ∧ stmt.finalState = classify stmt.d (symbols rows)) :
    ∃ (s : St) (y : Sy), stmt.d.step s y = stmt.finalState := by
  obtain ⟨rows, hsat, -⟩ := h
  obtain ⟨rn, hlast, hmem⟩ := getLast?_mem rows hsat.nonempty
  refine ⟨rn.state, rn.sym, ?_⟩
  rw [← hsat.table rn hmem]
  exact hsat.finalBoundary rn hlast

/-- A table DFA that can never leave `false` — the disclosed automaton the refutation uses. -/
def deadRouter : TableDfa Bool Bool where
  step _ _ := false
  start := false
  accepts := fun _ => True

/-- **NOT MODE 3, AT EVERY INSTANTIATION.** Claiming a classification the table cannot produce makes
the conclusion FALSE — for every digest algebra, every encoding, every commitment, every kernel. -/
theorem dfaAir_conclusion_bites {Dg : Type} [AddCommGroup Dg] [CryptoPrimitives Dg]
    (encState encSym : Bool → Dg) (tableCommitment routeCommitment : Dg) :
    ConclusionBites (fun stmt : Statement Bool Bool Dg =>
      ∃ rows : List (Row Bool Bool Dg),
        Satisfies stmt.d stmt.encState stmt.encSym stmt.tableCommitment stmt.initialState
          stmt.finalState stmt.routeCommitment rows
        ∧ stmt.finalState = classify stmt.d (symbols rows)) := by
  refine ⟨{ d := deadRouter, encState := encState, encSym := encSym,
            tableCommitment := tableCommitment, initialState := false, finalState := true,
            routeCommitment := routeCommitment }, ?_⟩
  intro h
  obtain ⟨s, y, hstep⟩ := dfaAir_conclusion_forces_finalState_in_the_table_image _ h
  have hstep' : (false : Bool) = true := hstep
  exact Bool.noConfusion hstep'

/-- **§6'S VERDICT.** As in §5 the conclusion is purely statement-side, so no kernel is retained. -/
theorem dfaAir_verdict {Dg : Type} [AddCommGroup Dg] [CryptoPrimitives Dg]
    (encState encSym : Bool → Dg) (tableCommitment routeCommitment : Dg) :
    ¬ ConclusionTotal (fun stmt : Statement Bool Bool Dg =>
      ∃ rows : List (Row Bool Bool Dg),
        Satisfies stmt.d stmt.encState stmt.encSym stmt.tableCommitment stmt.initialState
          stmt.finalState stmt.routeCommitment rows
        ∧ stmt.finalState = classify stmt.d (symbols rows)) :=
  not_conclusionTotal_of_conclusionBites
    (dfaAir_conclusion_bites encState encSym tableCommitment routeCommitment)

end DfaAirRow

/-! ## §7 — `CfgVerifierKernel`: NOT MODE 3, at an exhibited grammar.

`cfg_verify_sound` concludes `stmt.input ∈ stmt.g.language` — not an existential at all, so it is
the same shape as the `Temporal` control §9.4 used. It is refutable for the same kind of reason: a
grammar with NO rules generates the empty language, so no input is in it. -/

section CfgRow

open Dregg2.Crypto.Cfg

/-- A grammar with no productions, over the reference terminal/nonterminal alphabets. -/
def ruleFreeGrammar : ContextFreeGrammar Reference.Brk :=
  ⟨Reference.NTs, Reference.NTs.S, ∅⟩

/-- With no rules, `Derives` is equality: nothing rewrites. -/
theorem ruleFree_derives_eq (u v : List (Symbol Reference.Brk ruleFreeGrammar.NT))
    (h : ruleFreeGrammar.Derives u v) : u = v := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨r, hr, -⟩ := hstep
    have hr' : r ∈ (∅ : Finset (ContextFreeRule Reference.Brk ruleFreeGrammar.NT)) := hr
    simp at hr'

/-- **THE RULE-FREE GRAMMAR GENERATES NOTHING.** -/
theorem ruleFree_language_empty (w : List Reference.Brk) : w ∉ ruleFreeGrammar.language := by
  intro hmem
  have hder := (ContextFreeGrammar.mem_language_iff ruleFreeGrammar w).mp hmem
  have heq := ruleFree_derives_eq _ _ hder
  cases w with
  | nil => exact absurd heq (by simp)
  | cons a as => exact absurd heq (by simp)

/-- **NOT MODE 3.** The conclusion fails at every input of the rule-free grammar. -/
theorem cfg_conclusion_bites :
    ConclusionBites (fun stmt : Statement Reference.Brk => stmt.input ∈ stmt.g.language) :=
  ⟨{ g := ruleFreeGrammar, input := [] }, ruleFree_language_empty []⟩

/-- **§7'S VERDICT.** As in §5 and §6 the conclusion is purely statement-side, so no kernel is
retained. -/
theorem cfg_verdict :
    ¬ ConclusionTotal (fun stmt : Statement Reference.Brk => stmt.input ∈ stmt.g.language) :=
  not_conclusionTotal_of_conclusionBites cfg_conclusion_bites

end CfgRow

/-! ## §8 — `BridgeVerifierKernel`: **MODE 3 AT THE IN-TREE REFERENCE KERNEL.**

`bridge_verify_sound` concludes
`∃ v vDigest salt, Opens compress c vDigest salt ∧ threshold ≤ v`. The observed value `v` appears
ONLY in `threshold ≤ v`, which `v := threshold` discharges — so the whole conclusion collapses to
"the disclosed commitment `c` is in the IMAGE of `compress`". That is the `∃-image` shape, and at the
reference node hash `refCompress := (· + ·)` the image is everything.

The bite at the forge kernel (`compress ≡ 0`) is the same inversion §9.3 found at Merkle: the
sibling whose carrier the repair REFUTES is the one whose conclusion says something. -/

section BridgeRow

open Dregg2.Crypto.Bridge

/-- **THE CONCLUSION IS AN ∃-IMAGE CLAIM.** The threshold half is free at every statement; what
remains is exactly "the disclosed commitment is in the image of `compress`". -/
theorem bridge_conclusion_iff_commitment_in_image {Dg : Type} [AddCommGroup Dg]
    (compress : Dg → Dg → Dg) (stmt : Statement Dg) :
    (∃ (v : Int) (vDigest salt : Dg), BridgeRelation compress stmt.c stmt.threshold v vDigest salt)
      ↔ ∃ vDigest salt : Dg, stmt.c = compress vDigest salt := by
  constructor
  · rintro ⟨-, vD, salt, hopen, -⟩
    exact ⟨vD, salt, hopen⟩
  · rintro ⟨vD, salt, hopen⟩
    exact ⟨stmt.threshold, vD, salt, hopen, le_refl _⟩

/-- **MODE 3 AT THE REFERENCE NODE HASH.** `refCompress := (· + ·)` is surjective in each argument,
so every disclosed commitment opens: `vDigest := c`, `salt := 0`, `v := threshold`. -/
theorem bridge_conclusion_is_total_at_the_reference_compress :
    ConclusionTotal (fun stmt : Statement Int =>
      ∃ (v : Int) (vDigest salt : Int),
        BridgeRelation Reference.refCompress stmt.c stmt.threshold v vDigest salt) := by
  intro stmt
  refine ⟨stmt.threshold, stmt.c, 0, ?_, le_refl _⟩
  show stmt.c = stmt.c + 0
  omega

/-- **AND THEREFORE `bridge_verify_sound` IS FREE AT THE REFERENCE KERNEL** — the gated shape holds
with the carrier and the acceptance hypothesis DELETED, at the very instance whose repaired carrier
`refKernel_extractable` proves and whose `reference_cascade_nonvacuous` witness is offered as the
family's reassurance. -/
theorem bridge_verify_sound_is_free_at_the_reference_kernel (carrier : Prop)
    (acc : Acc (Statement Int)) :
    carrier → ∀ stmt, acc stmt → ∃ (v : Int) (vDigest salt : Int),
      BridgeRelation Reference.refCompress stmt.c stmt.threshold v vDigest salt :=
  totalConclusion_makes_the_gated_theorem_free carrier acc
    bridge_conclusion_is_total_at_the_reference_compress

/-- **THE POLARITY INVERSION.** At the forge kernel's collapsing node hash the conclusion BITES
(`c = 1` opens to nothing); at the reference kernel it is total. -/
theorem bridge_conclusion_axis_inverts_against_the_carrier_axis :
    ConclusionTotal (fun stmt : Statement Int =>
        ∃ (v : Int) (vDigest salt : Int),
          BridgeRelation Reference.refCompress stmt.c stmt.threshold v vDigest salt)
      ∧ ConclusionBites (fun stmt : Statement Int =>
        ∃ (v : Int) (vDigest salt : Int),
          BridgeRelation (fun _ _ => (0 : Int)) stmt.c stmt.threshold v vDigest salt) := by
  refine ⟨bridge_conclusion_is_total_at_the_reference_compress,
    ⟨{ c := 1, threshold := 0 }, ?_⟩⟩
  rintro ⟨v, vD, salt, hopen, hle⟩
  have hopen' : (1 : Int) = 0 := hopen
  exact absurd hopen' (by decide)

/-- `CarrierBites` is unreachable at the reference kernel. -/
theorem bridge_reference_carrierBites_is_unreachable (K : BridgeVerifierKernel Int Unit)
    (acc : Acc (Statement Int)) :
    ¬ CarrierBites K.extractable acc (fun stmt : Statement Int =>
      ∃ (v : Int) (vDigest salt : Int),
        BridgeRelation Reference.refCompress stmt.c stmt.threshold v vDigest salt) :=
  fun h => carrierBites_excludes_totalConclusion h
    bridge_conclusion_is_total_at_the_reference_compress

end BridgeRow

/-! ## §9 — `BlindedSetVerifierKernel`: **MODE 3 AT THE IN-TREE REFERENCE KERNEL.**

`blindedset_verify_sound` concludes `∃ member, MerkleMembers compress root member` — the SAME
`MerkleMembers` §9.3 already proved total at an additive node hash, with the member existentially
quantified as well, so it is strictly weaker than the Merkle conclusion. `BlindedSet.refCompress` is
that additive hash. The holder anonymity the existential is supposed to buy is exactly what makes
the conclusion free: nothing pins WHICH member, so a member can be invented. -/

section BlindedSetRow

open Dregg2.Crypto.BlindedSet
open Dregg2.Crypto.Merkle (MerkleMembers Step)

/-- **MODE 3 AT THE REFERENCE NODE HASH.** Member `0` with the single-step path `[⟨root, 0⟩]`
recomposes any issuer root under `(· + ·)`. -/
theorem blindedSet_conclusion_is_total_at_the_reference_compress :
    ConclusionTotal (fun stmt : Statement Int =>
      ∃ member : Int, MemberOf Reference.refCompress stmt.root member) := by
  intro stmt
  refine ⟨0, [{ sib := stmt.root, position := 0 }], List.cons_ne_nil _ _, ?_⟩
  show (0 : Int) + stmt.root = stmt.root
  omega

/-- **AND THEREFORE `blindedset_verify_sound` IS FREE AT THE REFERENCE KERNEL** — carrier and
acceptance deleted, at the instance whose repaired carrier `refKernel_extractable` proves. -/
theorem blindedset_verify_sound_is_free_at_the_reference_kernel (carrier : Prop)
    (acc : Acc (Statement Int)) :
    carrier → ∀ stmt, acc stmt → ∃ member : Int, MemberOf Reference.refCompress stmt.root member :=
  totalConclusion_makes_the_gated_theorem_free carrier acc
    blindedSet_conclusion_is_total_at_the_reference_compress

/-- **THE POLARITY INVERSION**, at the forge kernel's collapsing node hash: no member is authorized
at issuer root `1`. -/
theorem blindedSet_conclusion_axis_inverts_against_the_carrier_axis :
    ConclusionTotal (fun stmt : Statement Int =>
        ∃ member : Int, MemberOf Reference.refCompress stmt.root member)
      ∧ ConclusionBites (fun stmt : Statement Int =>
        ∃ member : Int, MemberOf (fun _ _ => (0 : Int)) stmt.root member) := by
  refine ⟨blindedSet_conclusion_is_total_at_the_reference_compress,
    ⟨{ root := 1, blindedMember := 0 }, ?_⟩⟩
  rintro ⟨member, path, hne, hrec⟩
  rw [Dregg2.Crypto.Reference.recompose_collapse path member hne] at hrec
  exact absurd hrec (by decide)

/-- `CarrierBites` is unreachable at the reference kernel. -/
theorem blindedSet_reference_carrierBites_is_unreachable (K : BlindedSetVerifierKernel Int Int)
    (acc : Acc (Statement Int)) :
    ¬ CarrierBites K.extractable acc (fun stmt : Statement Int =>
      ∃ member : Int, MemberOf Reference.refCompress stmt.root member) :=
  fun h => carrierBites_excludes_totalConclusion h
    blindedSet_conclusion_is_total_at_the_reference_compress

end BlindedSetRow

/-! ## §10 — `RangeProofKernel`: NOT MODE 3 at every instantiation — and the sharpest CARRIER-IDLE
instance in the family.

`range_verify_sound` concludes `∃ v r, commit v r = commitment ∧ InRange lo hi v`. `InRange` is
`lo ≤ v ∧ v ≤ hi`, so an EMPTY window refutes it whatever the commitment scheme: NOT MODE 3, at
every instantiation, exactly as `Temporal` (§9.4's control) fails at `lo = 1, hi = 0`.

What that yes/no answer hides is visible with `ConclusionTotalOn` and `CarrierIdle`. The in-tree
reference kernel sets `refCommit v r := v` — the commitment IS the value — so the conclusion is
LOGICALLY EQUIVALENT to `lo ≤ commitment ≤ hi`, which is verbatim the reference verifier's own
decidable acceptance test. `range_verify_sound` there is `accept → accept`, and BOTH crypto carriers
(`extractable`, `binding`) are idle. -/

section RangeProofRow

open Dregg2.Crypto.RangeProof

/-- **NOT MODE 3, AT EVERY INSTANTIATION.** An empty window admits no in-range value. -/
theorem range_conclusion_bites {Digest : Type u} (commit : Int → Int → Digest) (c : Digest) :
    ConclusionBites (fun stmt : Statement Digest =>
      ∃ v r : Int, commit v r = stmt.commitment ∧ InRange stmt.lo stmt.hi v) := by
  refine ⟨{ commitment := c, lo := 1, hi := 0 }, ?_⟩
  rintro ⟨v, -, -, hlo, hhi⟩
  have h1 : (1 : Int) ≤ v := hlo
  have h2 : v ≤ (0 : Int) := hhi
  omega

/-- **§10'S FIRST VERDICT**, with the kernel retained as the subject. -/
theorem range_verdict (K : RangeProofKernel Int Int) :
    ¬ ConclusionTotal (fun stmt : Statement Int =>
      ∃ v r : Int, K.commit v r = stmt.commitment ∧ InRange stmt.lo stmt.hi v) :=
  not_conclusionTotal_of_conclusionBites (range_conclusion_bites K.commit 0)

/-- **§10'S SECOND VERDICT — AT THE REFERENCE KERNEL THE CONCLUSION IS THE ACCEPTANCE TEST.** Not
merely implied by it: EQUIVALENT to it, in both directions, because `refCommit` is the identity in
the value. A soundness theorem whose conclusion is its own hypothesis re-read has nothing left to
deliver. -/
theorem range_reference_conclusion_is_the_acceptance_test (stmt : Statement Int) (proof : Int) :
    Reference.refKernel.verifyRange stmt.commitment stmt.lo stmt.hi proof = true
      ↔ ∃ v r : Int, Reference.refCommit v r = stmt.commitment ∧ InRange stmt.lo stmt.hi v := by
  constructor
  · intro hacc
    have hacc' : decide (stmt.lo ≤ stmt.commitment ∧ stmt.commitment ≤ stmt.hi) = true := hacc
    simp only [decide_eq_true_eq] at hacc'
    exact ⟨stmt.commitment, 0, rfl, hacc'.1, hacc'.2⟩
  · rintro ⟨v, r, hv, hlo, hhi⟩
    have hv' : v = stmt.commitment := hv
    subst hv'
    show decide (stmt.lo ≤ stmt.commitment ∧ stmt.commitment ≤ stmt.hi) = true
    simp only [decide_eq_true_eq]
    exact ⟨hlo, hhi⟩

/-- Relative totality, in the instrument's vocabulary: on the sub-domain the verifier itself decides,
the conclusion is free. -/
theorem range_reference_conclusion_is_total_on_the_window :
    ConclusionTotalOn
      (fun stmt : Statement Int => stmt.lo ≤ stmt.commitment ∧ stmt.commitment ≤ stmt.hi)
      (fun stmt : Statement Int =>
        ∃ v r : Int, Reference.refCommit v r = stmt.commitment ∧ InRange stmt.lo stmt.hi v) :=
  fun stmt h => ⟨stmt.commitment, 0, rfl, h.1, h.2⟩

/-- **BOTH CARRIERS ARE IDLE AT THE REFERENCE KERNEL.** Acceptance alone gives the conclusion, so
neither the Bulletproofs `extractable` nor the DLog `binding` is doing any work there. -/
theorem range_reference_carriers_are_idle :
    CarrierIdle
      (ofBool fun p : Statement Int × Int =>
        Reference.refKernel.verifyRange p.1.commitment p.1.lo p.1.hi p.2)
      (fun p : Statement Int × Int =>
        ∃ v r : Int, Reference.refCommit v r = p.1.commitment ∧ InRange p.1.lo p.1.hi v) := by
  rintro ⟨stmt, proof⟩ hacc
  exact (range_reference_conclusion_is_the_acceptance_test stmt proof).mp hacc

end RangeProofRow

/-! ### §10a — THE MODE-3 VERDICTS ARE PINNED TO THE ACTUAL REFERENCE KERNELS.

§8, §9 and §10 are stated at `refCompress` / `refCommit` rather than at `refKernel.compress` /
`refKernel.commit`, which would let the finding lapse silently if a kernel were re-pointed at a
different primitive. These three `rfl`s close that gap: the functions the verdicts are about ARE the
ones the in-tree kernels install. -/

theorem bridge_refKernel_compress_is_refCompress :
    Dregg2.Crypto.Bridge.Reference.refKernel.compress = Dregg2.Crypto.Bridge.Reference.refCompress :=
  rfl

theorem blindedSet_refKernel_compress_is_refCompress :
    Dregg2.Crypto.BlindedSet.Reference.refKernel.compress
      = Dregg2.Crypto.BlindedSet.Reference.refCompress :=
  rfl

theorem range_refKernel_commit_is_refCommit :
    Dregg2.Crypto.RangeProof.Reference.refKernel.commit
      = Dregg2.Crypto.RangeProof.Reference.refCommit :=
  rfl

/-! ## §11 — A PROVED CARRIER IS AN IDLE CARRIER, and what that does to the repair's evidence.

The 2026-07-25 carrier repair replaced `extractable := True` with an extractability-SHAPED `Prop` at
eight reference kernels and PROVED it at each (`*_extractable`). That is a real improvement on the
carrier axis — but it cannot, even in principle, demonstrate at those instances that the carrier is
LOAD-BEARING, because a carrier that is proved in Lean is a carrier the gated theorem does not need.
One line says so. The evidence that the carrier has content therefore lives ENTIRELY in the FORGE
sibling refutation (`*forge*_not_extractable`), which is exactly `CarrierAudit`'s `refuted` field —
so that field is the whole content of the repair, not half of it. -/

section ProvedCarrier

/-- **A PROVED CARRIER IS IDLE.** Wherever the carrier is discharged by an in-tree theorem, the
gated theorem carries no assumption: acceptance alone yields the conclusion. -/
theorem proved_carrier_is_idle {ι : Type u} {carrier : Prop} {acc : Acc ι} {C : ι → Prop}
    (hproved : carrier) (hthm : carrier → ∀ i, acc i → C i) : CarrierIdle acc C :=
  fun i hi => hthm hproved i hi

/-- Fired at the class the repair took its pattern FROM: `PortalFloor`'s reference kernel, whose
`extractable` is a proved theorem, so its STARK floor is idle there. The same one-liner applies at
each of the eight repaired reference kernels; §4 and §10 already exhibit it at two of them by a
different route. -/
theorem portalFloor_reference_carrier_is_idle :
    CarrierIdle
      (ofBool fun p : Nat × Nat =>
        Dregg2.Crypto.PortalFloor.Reference.instVerifierKernel.verify p.1 p.2)
      (fun p : Nat × Nat => Dregg2.Crypto.PortalFloor.Reference.instVerifierKernel.Holds p.1) :=
  proved_carrier_is_idle Dregg2.Crypto.PortalFloor.Reference.instVerifierKernel_extractable
    (fun h p hp =>
      Dregg2.Crypto.PortalFloor.Reference.instVerifierKernel.verify_sound h p.1 p.2 hp)

end ProvedCarrier

/-! ## §12 — THE TEN VERDICTS, ASSEMBLED, AND THE UPDATED R11 TABLE.

| kernel | file:line of the gated theorem | conclusion | verdict | theorem here |
|---|---|---|---|---|
| `PortalFloor.VerifierKernel` | `PortalFloor.lean:84` `verifier_floor_sound` | `K.Holds stmt` | **NOT MODE 3 at both in-tree instances**; class parametric, a MODE-3 instantiation exhibited | `portalFloor_verdict`, `portalFloor_admits_a_mode3_instantiation` |
| `PedersenVerifierKernel` | `Pedersen.lean:297` `pedersen_verify_sound` | `∃ circuit, statementOf = stmt ∧ Conserves` | **NOT MODE 3 at EVERY instantiation** — refuted at any unbalanced disclosure | `pedersen_conclusion_bites_at_unbalanced_disclosures`, `pedersen_verdict` |
| `CustomVerifierKernel` | `Custom.lean:137` `custom_verify_sound` | `∃ wit, R.Relation stmt wit` | **MODE 3 at the in-tree `eqRegistration`** (`∃ wit, stmt = wit`); bites at `emptyRegistration` | `eqRegistration_conclusion_is_total`, `custom_conclusion_axis_inverts_against_the_carrier_axis` |
| `DecoVerifierKernel` | `Deco.lean:296` `deco_verify_sound` | `∃ w, DecoRelation … stmt w` | **NOT MODE 3 at EVERY instantiation** (zero amount); at the reference kernel TOTAL ON `1 ≤ amountCents` and the carrier is IDLE | `deco_verdict`, `deco_reference_conclusion_is_total_on_nonzero_amount`, `deco_reference_carrier_is_idle` |
| `DfaVerifierKernel` | `Dfa.lean:200` `dfa_verify_sound` | `∃ trace, DfaAccepts …` | **NOT MODE 3 at EVERY instantiation** — refuted at an empty accept set | `dfa_conclusion_bites`, `dfa_verdict` |
| `DfaBoundVerifierKernel` (2026-11-05) | `Dfa.lean` `dfa_bound_verify_sound` | `∃ w, commit w = c ∧ ∃ trace, DfaAccepts … ∧ traceWord trace = w` | **NOT MODE 3** — strictly stronger than the row above, so it bites wherever that does; the splice (record-ignoring acceptance) meets the unbound shape and FAILS this one | `Dfa.Reference.splice_meets_unbound`, `Dfa.Reference.splice_fails_bound` |
| `DfaAirVerifierKernel` | `DfaAcceptanceAir.lean:526` `dfaAir_verify_sound` | `∃ rows, Satisfies … ∧ finalState = classify …` | **NOT MODE 3 at EVERY instantiation** — the public `finalState` must be a table cell | `dfaAir_conclusion_forces_finalState_in_the_table_image`, `dfaAir_verdict` |
| `CfgVerifierKernel` | `Cfg.lean:122` `cfg_verify_sound` | `stmt.input ∈ stmt.g.language` | **NOT MODE 3** — refuted at the rule-free grammar (same shape as the `Temporal` control) | `ruleFree_language_empty`, `cfg_verdict` |
| `BridgeVerifierKernel` | `Bridge.lean:205` `bridge_verify_sound` | `∃ v vD salt, Opens ∧ threshold ≤ v` | **MODE 3 at the in-tree reference kernel** — an `∃-image` claim under a surjective `compress`; bites at the forge hash | `bridge_conclusion_is_total_at_the_reference_compress`, `bridge_conclusion_axis_inverts_against_the_carrier_axis` |
| `BlindedSetVerifierKernel` | `BlindedSet.lean:193` `blindedset_verify_sound` | `∃ member, MerkleMembers compress root member` | **MODE 3 at the in-tree reference kernel** — weaker than the Merkle conclusion §9.3 refuted; bites at the forge hash | `blindedSet_conclusion_is_total_at_the_reference_compress`, `blindedSet_conclusion_axis_inverts_against_the_carrier_axis` |
| `RangeProofKernel` | `RangeProof.lean:208` `range_verify_sound` | `∃ v r, commit v r = c ∧ InRange lo hi v` | **NOT MODE 3 at EVERY instantiation** (empty window); at the reference kernel the conclusion IS the acceptance test and BOTH carriers are idle | `range_verdict`, `range_reference_conclusion_is_the_acceptance_test`, `range_reference_carriers_are_idle` |

**R11 after this module.** Of the thirteen carrier-gated kernels: **FIVE are MODE 3** at an in-tree
instance (`NonMembership` permanently, `Merkle`, `Custom`, `Bridge`, `BlindedSet` at their reference
oracles) and **EIGHT are not** (`Temporal`, `PortalFloor`, `Pedersen`, `Deco`, `Dfa`,
`DfaAcceptanceAir`, `Cfg`, `RangeProof`). The conclusion-axis question §9.6 left open for eleven is
CLOSED for all ten remaining; nothing on this axis is UNKNOWN any more.

**What is still UNKNOWN — and it is not effort.** The DEPLOYMENT verdict for all thirteen. Settling
it needs a kernel whose `compress` is real Poseidon2 and whose `verify` is the deployed
`stark::verify`; that symbol is `opaque`/`@[extern]` with no Lean semantics, so the object does not
exist in the tree and cannot be built by engineering. Every MODE-3 verdict here that names a
reference oracle is a statement about a TOY, and the four "at every instantiation" refutations are
the only ones that survive to a deployed instantiation — they say the conclusion is not free THERE
either, which is a lower bound on content and not a soundness claim.

**And the pattern, stated once.** Four of the five MODE-3 members are the `∃-image` shape `∃ w,
x = f w` at an instantiation where `f` is surjective — `Custom`'s `∃ wit, stmt = wit` (identity),
`Bridge`'s `∃ vD salt, c = compress vD salt`, `BlindedSet`'s and `Merkle`'s
`recompose … path = root`. The fifth, `NonMembership`, is the degenerate limit of the same shape:
its conclusion does not mention the pinned object AT ALL, so no instantiation can matter. The non-MODE-3 members are exactly those whose
conclusion retains a conjunct over PUBLIC data that no witness can supply (`Pedersen`'s sum
equation, `Deco`'s amount, `Dfa`'s accept set, `DfaAcceptanceAir`'s table image, `Cfg`'s language,
`RangeProof`'s and `Temporal`'s window). That is a usable design rule: a gated conclusion is free
exactly when its every conjunct is existentially reachable. -/

/-- **THE TEN VERDICTS AS ONE THEOREM** — so a regression in any one of the ten conclusions breaks
this rather than letting the sweep's table drift out of sync with the tree. Order matches §12. -/
theorem the_ten_verdicts
    (encState encSym : Bool → Int) (tableCommitment routeCommitment : Int) :
    -- 1  PortalFloor: not total at the reference instance
    (¬ ConclusionTotal (fun s : Nat =>
        (Dregg2.Crypto.PortalFloor.Reference.instVerifierKernel).Holds s))
    -- 2  Pedersen: not total at any commit
    ∧ (¬ ConclusionTotal (fun stmt : Dregg2.Crypto.Pedersen.Statement Int =>
        ∃ circuit : Dregg2.Crypto.Pedersen.CircuitIR,
          Dregg2.Crypto.Pedersen.statementOf (fun v r => v + r) circuit = stmt
            ∧ Dregg2.Crypto.Pedersen.Conserves (fun v r => v + r) circuit))
    -- 3  Custom: TOTAL at the in-tree registration
    ∧ ConclusionTotal (fun stmt : Dregg2.Crypto.Custom.Reference.eqRegistration.Statement =>
        ∃ wit : Dregg2.Crypto.Custom.Reference.eqRegistration.Witness,
          Dregg2.Crypto.Custom.Reference.eqRegistration.Relation stmt wit)
    -- 4  Deco: not total at any oracles
    ∧ (¬ ConclusionTotal (fun stmt : Dregg2.Crypto.Deco.Statement Int =>
        ∃ w : Dregg2.Crypto.Deco.CircuitIR Int,
          Dregg2.Crypto.Deco.DecoRelation Dregg2.Crypto.Deco.Reference.refSig
            Dregg2.Crypto.Deco.Reference.refMac Dregg2.Crypto.Deco.Reference.refCompress
            Dregg2.Crypto.Deco.Reference.refEncode stmt w))
    -- 5  Dfa: not total
    ∧ (¬ ConclusionTotal (fun stmt : Dregg2.Crypto.Dfa.Statement Nat Nat =>
        ∃ trace : List (Dregg2.Crypto.Dfa.Step Nat Nat),
          Dregg2.Crypto.Dfa.DfaAccepts stmt.δ stmt.q₀ stmt.accept trace))
    -- 6  DfaAcceptanceAir: not total
    ∧ (¬ ConclusionTotal (fun stmt : Dregg2.Crypto.DfaAcceptanceAir.Statement Bool Bool Int =>
        ∃ rows : List (Dregg2.Crypto.DfaAcceptanceAir.Row Bool Bool Int),
          Dregg2.Crypto.DfaAcceptanceAir.Satisfies stmt.d stmt.encState stmt.encSym
            stmt.tableCommitment stmt.initialState stmt.finalState stmt.routeCommitment rows
          ∧ stmt.finalState
              = Dregg2.Crypto.DfaAcceptanceAir.classify stmt.d
                  (Dregg2.Crypto.DfaAcceptanceAir.symbols rows)))
    -- 7  Cfg: not total
    ∧ (¬ ConclusionTotal (fun stmt : Dregg2.Crypto.Cfg.Statement Dregg2.Crypto.Cfg.Reference.Brk =>
        stmt.input ∈ stmt.g.language))
    -- 8  Bridge: TOTAL at the reference compress
    ∧ ConclusionTotal (fun stmt : Dregg2.Crypto.Bridge.Statement Int =>
        ∃ (v : Int) (vDigest salt : Int),
          Dregg2.Crypto.Bridge.BridgeRelation Dregg2.Crypto.Bridge.Reference.refCompress stmt.c
            stmt.threshold v vDigest salt)
    -- 9  BlindedSet: TOTAL at the reference compress
    ∧ ConclusionTotal (fun stmt : Dregg2.Crypto.BlindedSet.Statement Int =>
        ∃ member : Int,
          Dregg2.Crypto.BlindedSet.MemberOf Dregg2.Crypto.BlindedSet.Reference.refCompress
            stmt.root member)
    -- 10 RangeProof: not total at any commit
    ∧ (¬ ConclusionTotal (fun stmt : Dregg2.Crypto.RangeProof.Statement Int =>
        ∃ v r : Int, Dregg2.Crypto.RangeProof.Reference.refCommit v r = stmt.commitment
          ∧ Dregg2.Crypto.RangeProof.InRange stmt.lo stmt.hi v)) := by
  refine ⟨not_conclusionTotal_of_conclusionBites portalFloor_reference_conclusion_bites,
    not_conclusionTotal_of_conclusionBites (pedersen_conclusion_bites (fun v r => v + r)),
    eqRegistration_conclusion_is_total,
    not_conclusionTotal_of_conclusionBites
      (deco_conclusion_bites (0 : Int) Dregg2.Crypto.Deco.Reference.refSig
        Dregg2.Crypto.Deco.Reference.refMac Dregg2.Crypto.Deco.Reference.refCompress
        Dregg2.Crypto.Deco.Reference.refEncode),
    not_conclusionTotal_of_conclusionBites (dfa_conclusion_bites (0 : Nat) (fun _ _ _ => True)),
    not_conclusionTotal_of_conclusionBites
      (dfaAir_conclusion_bites encState encSym tableCommitment routeCommitment),
    not_conclusionTotal_of_conclusionBites cfg_conclusion_bites,
    bridge_conclusion_is_total_at_the_reference_compress,
    blindedSet_conclusion_is_total_at_the_reference_compress,
    not_conclusionTotal_of_conclusionBites
      (range_conclusion_bites Dregg2.Crypto.RangeProof.Reference.refCommit 0)⟩

/-! ## §13 — axiom-hygiene pins. `#assert_all_clean` throws on the FIRST name whose proof rests on
anything outside `{propext, Classical.choice, Quot.sound}`, and logs the count on success. As
`PremiseInhabitability` §B says, a clean audit here is structurally blind to the wound this module
measures — that is the whole reason the module exists. -/

#assert_all_clean [totalOn_makes_the_gated_theorem_free_on_S, conclusionTotal_of_totalOn_true,
  carrierIdle_of_conclusionTotal, carrierIdle_makes_the_gated_theorem_carrier_free,
  carrierIdle_does_not_imply_conclusionTotal,
  portalFloor_reference_conclusion_bites, portalFloor_forge_conclusion_bites,
  portalFloor_admits_a_mode3_instantiation, portalFloor_verdict,
  pedersen_conclusion_forces_balanced_disclosure, pedersen_conclusion_bites_at_unbalanced_disclosures,
  pedersen_conclusion_bites, pedersen_verdict,
  eqRegistration_conclusion_is_total, custom_verify_sound_is_free_at_the_reference_registration,
  custom_reference_nonvacuity_witness_needs_no_kernel,
  custom_conclusion_axis_inverts_against_the_carrier_axis,
  custom_reference_carrierBites_is_unreachable,
  deco_conclusion_forces_nonzero_amount, deco_conclusion_bites_at_zero_amount,
  deco_conclusion_bites, deco_verdict, deco_reference_conclusion_is_total_on_nonzero_amount,
  deco_reference_conclusion_holds_at_a_rejected_statement, deco_reference_rejects_that_statement,
  deco_reference_carrier_is_idle,
  dfa_conclusion_forces_a_nonempty_accept_set, dfa_conclusion_bites, dfa_verdict,
  dfa_conclusion_is_free_at_a_permissive_automaton,
  getLast?_mem, dfaAir_conclusion_forces_finalState_in_the_table_image, dfaAir_conclusion_bites,
  dfaAir_verdict,
  ruleFree_derives_eq, ruleFree_language_empty, cfg_conclusion_bites, cfg_verdict,
  bridge_conclusion_iff_commitment_in_image, bridge_conclusion_is_total_at_the_reference_compress,
  bridge_verify_sound_is_free_at_the_reference_kernel,
  bridge_conclusion_axis_inverts_against_the_carrier_axis,
  bridge_reference_carrierBites_is_unreachable,
  blindedSet_conclusion_is_total_at_the_reference_compress,
  blindedset_verify_sound_is_free_at_the_reference_kernel,
  blindedSet_conclusion_axis_inverts_against_the_carrier_axis,
  blindedSet_reference_carrierBites_is_unreachable,
  range_conclusion_bites, range_verdict, range_reference_conclusion_is_the_acceptance_test,
  range_reference_conclusion_is_total_on_the_window, range_reference_carriers_are_idle,
  bridge_refKernel_compress_is_refCompress, blindedSet_refKernel_compress_is_refCompress,
  range_refKernel_commit_is_refCommit,
  proved_carrier_is_idle, portalFloor_reference_carrier_is_idle,
  the_ten_verdicts]

-- The three headline verdicts, with their axiom sets PRINTED rather than only asserted.
#print axioms the_ten_verdicts
#print axioms eqRegistration_conclusion_is_total
#print axioms bridge_conclusion_is_total_at_the_reference_compress
#print axioms blindedSet_conclusion_is_total_at_the_reference_compress

end Dregg2.Circuit.PremiseInhabitabilityConclusionAxis
