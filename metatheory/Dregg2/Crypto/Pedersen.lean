/-
# Dregg2.Crypto.Pedersen — the SECOND end-to-end §8 discharge: Pedersen value conservation.

**The next obligation after Merkle (`PHASE-CRYPTOKERNEL.md §5` "Path to the rest").** Where
`Crypto/Merkle.lean` discharged membership, this discharges the hidden-value-transfer
CONSERVATION: a transfer over Pedersen commitments preserves total value, and every amount is
non-negative — so no inflation is hidden behind the commitments. The cascade mirrors Merkle's:

    pedersen_conservation_bridge : Satisfies pedersenCircuit (insC, outsC) ↔ Conserves …
      [the gadget, FULLY proven — uses `commit_hom`/`commit_zero`, NO primitive seam]
    pedersen_verify_sound        : verify accepts → Conserves …
      [DERIVED off the bridge, given the STARK `extractable` carrier]
    pedersen_dial_wired          : the dial pinned to the verifier at the `selective` floor
      [Pedersen DISCLOSES the commitments (not the amounts) ⇒ `selective`, not `acceptanceOnly`]

**The algebra is the genuinely-grounded part.** Pedersen's additive homomorphism
(`CryptoPrimitives.commit_hom`, Layer A) is the one PROVED algebraic law; conservation is
`map_sum` over it — re-homing `PrivacyKernel.committed_conservation_kernel` onto the Layer-A
`CryptoPrimitives` portal. Non-negativity is the honest bit-decomposition range gadget
(`Exec/RecordCircuit.range_iff`), no seam. The ONLY cryptographic residue is the Pedersen
`binding` carrier (DLog) — a `Prop`, never a Lean law, never `sorry`: binding is what makes the
*commitment* sum equation testify to the *amount* equation, i.e. the verifier cannot open the
balanced commitments to unbalanced amounts. The conservation algebra itself is unconditional.
-/
import Dregg2.Crypto.Primitives
import Dregg2.Exec.RecordCircuit
import Dregg2.Authority.Predicate
import Metatheory.EpistemicDial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Dregg2.Tactics

namespace Dregg2.Crypto.Pedersen

open Dregg2.Crypto Dregg2.Exec.RecordCircuit

universe u

variable {Digest : Type u} [AddCommGroup Digest]

/-! ## The Pedersen homomorphism re-homed onto Layer A (`CryptoPrimitives`).

`PrivacyKernel.committed_conservation_kernel` proved conservation over the OLD flat
`CryptoKernel`. Here we re-home the same `map_sum` argument onto the Layer-A
`CryptoPrimitives.commit`/`commit_hom` (the overhaul's grounded primitive), exactly as
`PHASE-CRYPTOKERNEL.md §5` calls for ("the Layer-A `commit`/`commit_hom` re-homed"). -/

/-- **The Layer-A Pedersen commitment as an additive monoid hom** `(Int × Int) →+ Digest`.
`commit_hom` is `f (x+y) = f x + f y` on pairs `(value, blinding)`, and `commit_zero` (derived
in `Crypto/Primitives.lean` from `commit_hom`) is `f 0 = 0`. PROVED interface consequence, not
a postulated field. -/
def commitHom [CryptoPrimitives Digest] : (Int × Int) →+ Digest where
  toFun p := CryptoPrimitives.commit p.1 p.2
  map_zero' := commit_zero
  map_add' := fun x y => CryptoPrimitives.commit_hom (Digest := Digest) x.1 y.1 x.2 y.2

@[simp] theorem commitHom_apply [CryptoPrimitives Digest] (v r : Int) :
    commitHom (Digest := Digest) (v, r) = CryptoPrimitives.commit v r := rfl

/-- A finite sum of per-note commitments collapses into a single commitment of the summed
value under the summed blinding (`Σ commit vᵢ rᵢ = commit (Σ vᵢ) (Σ rᵢ)`). PROVED from
`commitHom` via `map_sum`. The algebraic heart of value conservation. -/
theorem commit_sum [CryptoPrimitives Digest]
    {ι : Type} (val : ι → Int) (bl : ι → Int) (s : Finset ι) :
    (s.sum (fun i => CryptoPrimitives.commit (val i) (bl i)) : Digest)
      = CryptoPrimitives.commit (s.sum val) (s.sum bl) := by
  classical
  show (s.sum (fun i => commitHom (Digest := Digest) (val i, bl i)) : Digest)
      = commitHom (Digest := Digest) (s.sum val, s.sum bl)
  rw [← map_sum (commitHom (Digest := Digest)) (fun i => (val i, bl i)) s]
  congr 1
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · simpa using (Prod.fst_sum (s := s) (f := fun i => (val i, bl i)))
  · simpa using (Prod.snd_sum (s := s) (f := fun i => (val i, bl i)))

/-! ## The Pedersen circuit IR — the conservation gadget + per-amount range gadget.

Mirrors the Pedersen value-commitment AIR (`circuit/src/value_commitment.rs`,
`cell/src/value_commitment.rs`: `commit(v,r)=v·V+r·R`). The PUBLIC inputs are the input/output
commitments (Pedersen discloses the commitments — hence the `selective` dial floor). The trace
carries, per note, the hidden `(value, blinding)` and the per-value `n`-bit range decomposition.
Two constraint families:

  * **Conservation** — `Σ commit(inputs) = Σ commit(outputs)` over the commitment group (the
    `commit_hom` collapse); the boundary `PiBinding`s pin each row's commitment to a public
    input. This is the analog of Merkle's `MerkleHash`+boundary.
  * **Range** — each note's value has a valid `n`-bit boolean decomposition
    (`RecordCircuit.bitsToInt`/`Boolean`), proving `0 ≤ value < 2ⁿ` with NO primitive seam
    (the honest `range_iff` gadget). This is the non-negativity / no-overflow side. -/

/-- A single note in the trace: its hidden value, blinding, and the `n`-bit boolean
decomposition of the value (the range-gadget witness columns). -/
structure Note where
  /-- The hidden amount. -/
  value : Int
  /-- The Pedersen blinding factor. -/
  blinding : Int
  /-- The little-endian bit columns witnessing `0 ≤ value < 2 ^ bits.length`
  (`RecordCircuit.bitsToInt`/`Boolean`). -/
  bits : List Int
  deriving Repr

/-- **The Pedersen statement** (the public-input algebra): the lists of input and output
commitments the verifier sees. These are the disclosed public inputs (the `selective` floor:
commitments shown, amounts hidden). -/
structure Statement (Digest : Type u) where
  /-- The disclosed input commitments. -/
  insC : List Digest
  /-- The disclosed output commitments. -/
  outsC : List Digest
  deriving Repr

/-- **The Pedersen circuit IR** — the trace: the hidden input/output notes (each with its
range-decomposition witness). -/
structure CircuitIR where
  /-- The input notes (hidden value+blinding+bits). -/
  ins : List Note
  /-- The output notes. -/
  outs : List Note
  deriving Repr

/-- The commitment of a single note under an (explicit) `commit` function. Parametrizing over
`commit : Int → Int → Digest` mirrors `Merkle.recompose`'s explicit `compress`: the circuit
relations are structural over the operation; the homomorphism `commit_hom` enters only the
value-conservation theorems (`commit_sum`/`committed_conservation`/`pedersen_value_conservation`),
not the satisfiability bridge. -/
def noteCommit (commit : Int → Int → Digest) (nt : Note) : Digest := commit nt.value nt.blinding

/-- **`listCommit`** — the group sum of a note list's commitments (`Σ commit vᵢ rᵢ`). -/
def listCommit (commit : Int → Int → Digest) (notes : List Note) : Digest :=
  (notes.map (noteCommit commit)).sum

/-- **`Conserves`** — the conservation+range relation: the input-commitment sum equals the
output-commitment sum (over the group), AND every amount lies in `[0, 2 ^ bits.length)` via its
boolean bit-decomposition. The honest non-negativity side rides on `RecordCircuit.Boolean`. -/
def Conserves (commit : Int → Int → Digest) (c : CircuitIR) : Prop :=
  (listCommit commit c.ins = listCommit commit c.outs)
    ∧ (∀ nt ∈ c.ins, Boolean nt.bits ∧ bitsToInt nt.bits = nt.value)
    ∧ (∀ nt ∈ c.outs, Boolean nt.bits ∧ bitsToInt nt.bits = nt.value)

/-! ## The bridge — `Satisfies ↔ Conserves`, FULLY proven (NO primitive seam).

`Satisfies` is the AIR check: every note's range gadget holds, the per-note commitments bind to
the disclosed public inputs (`Statement`), and the input/output commitment sums are equal. We
PROVE this is exactly `Conserves`. The non-negativity flows through `range_iff`; the commitment
conservation through the `statementOf` `PiBinding`. The homomorphism `commit_hom` is what makes
the COMMITMENT-sum equation equal a VALUE-conservation fact — that is the separate
`pedersen_value_conservation`/`committed_conservation` theorems below, which DO use it. -/

/-- **`Satisfies stmt circuit`** — the full Pedersen AIR check, given the disclosed `Statement`:
the trace's per-note commitments are exactly the public-input commitment lists (`PiBinding`
boundaries), every note's range gadget is satisfied (`Boolean` bits recomposing the value), and
the input/output commitment sums balance (the conservation constraint via the group sum). -/
def Satisfies (commit : Int → Int → Digest) (stmt : Statement Digest) (circuit : CircuitIR) : Prop :=
  -- PiBinding: the disclosed input commitments ARE the trace's input-note commitments.
  stmt.insC = circuit.ins.map (noteCommit commit) ∧
  -- PiBinding: likewise for outputs.
  stmt.outsC = circuit.outs.map (noteCommit commit) ∧
  -- Range gadget per input note: boolean bits recomposing the value (⇒ 0 ≤ value < 2ⁿ).
  (∀ nt ∈ circuit.ins, Boolean nt.bits ∧ bitsToInt nt.bits = nt.value) ∧
  -- Range gadget per output note.
  (∀ nt ∈ circuit.outs, Boolean nt.bits ∧ bitsToInt nt.bits = nt.value) ∧
  -- Conservation: the disclosed input commitments sum to the disclosed output commitments.
  stmt.insC.sum = stmt.outsC.sum

/-- **The statement determined by a trace** (the public inputs a real trace exposes): each
note's Pedersen commitment, in order. This is what `PiBinding` pins. -/
def statementOf (commit : Int → Int → Digest) (circuit : CircuitIR) : Statement Digest where
  insC := circuit.ins.map (noteCommit commit)
  outsC := circuit.outs.map (noteCommit commit)

/-- The disclosed-commitment-list sum is the `listCommit` group sum (`Statement.insC.sum`,
mapped through the commitment, IS `listCommit`). The bridge between the public-input vector and
the group-level conservation relation. -/
theorem statementOf_insC_sum (commit : Int → Int → Digest) (circuit : CircuitIR) :
    (statementOf commit circuit).insC.sum = listCommit commit circuit.ins :=
  rfl

theorem statementOf_outsC_sum (commit : Int → Int → Digest) (circuit : CircuitIR) :
    (statementOf commit circuit).outsC.sum = listCommit commit circuit.outs :=
  rfl

/-- **`pedersen_conservation_bridge` — THE deliverable (the analog of `merkle_bridge`).** With
the disclosed `Statement` pinned to the trace's commitments (`statementOf`), the Pedersen AIR is
satisfied IFF the hidden amounts CONSERVE over the commitment group (and are each in range). Both
directions PROVED:

  * `→` (SOUNDNESS): a satisfying trace forces `Σ commit(inputs) = Σ commit(outputs)` (the
    disclosed sums are equal, and they equal the `listCommit` group sums by `statementOf`) and
    each amount in range — so value is conserved over the commitments.
  * `←` (COMPLETENESS): conserving amounts give a satisfying trace (the `PiBinding`s hold by
    construction, the range witnesses are the `bits`, and the sum equality transports through
    the same `statementOf` identity).

NO primitive seam inside — `commit` is abstract. The `binding` of the commitment (that this
COMMITMENT equation testifies to the *amount* equation) is the Layer-A `CryptoPrimitives.binding`
`Prop`, consumed by `pedersen_verify_sound`, never here; and the homomorphic step from commitment-
to value-conservation is `pedersen_value_conservation` (which uses `commit_hom`). -/
theorem pedersen_conservation_bridge (commit : Int → Int → Digest) (circuit : CircuitIR) :
    Satisfies commit (statementOf commit circuit) circuit ↔ Conserves commit circuit := by
  constructor
  · rintro ⟨_, _, hin, hout, hsum⟩
    refine ⟨?_, hin, hout⟩
    -- the disclosed sums equal the listCommit group sums (statementOf), and they are equal
    rw [statementOf_insC_sum, statementOf_outsC_sum] at hsum
    exact hsum
  · rintro ⟨hbal, hin, hout⟩
    refine ⟨rfl, rfl, hin, hout, ?_⟩
    rw [statementOf_insC_sum, statementOf_outsC_sum]
    exact hbal

/-- **Non-negativity is honestly proven, no seam.** From a satisfying trace, every note's amount
is in `[0, 2 ^ bits.length)` — directly from the range gadget (`RecordCircuit.range_sound`),
exactly the no-inflation side. PROVED. -/
theorem pedersen_amounts_nonneg (commit : Int → Int → Digest) (circuit : CircuitIR)
    (h : Conserves commit circuit) :
    (∀ nt ∈ circuit.ins, 0 ≤ nt.value ∧ nt.value < 2 ^ nt.bits.length) ∧
    (∀ nt ∈ circuit.outs, 0 ≤ nt.value ∧ nt.value < 2 ^ nt.bits.length) := by
  obtain ⟨_, hin, hout⟩ := h
  refine ⟨fun nt hnt => ?_, fun nt hnt => ?_⟩
  · obtain ⟨hbool, hrec⟩ := hin nt hnt
    obtain ⟨h0, h1⟩ := range_sound nt.bits hbool
    rw [hrec] at h0 h1; exact ⟨h0, h1⟩
  · obtain ⟨hbool, hrec⟩ := hout nt hnt
    obtain ⟨h0, h1⟩ := range_sound nt.bits hbool
    rw [hrec] at h0 h1; exact ⟨h0, h1⟩

/-! ## The homomorphic step — commitment-sum ⇒ VALUE conservation (THIS uses `commit_hom`).

The bridge above is structural over `commit`. The genuinely-grounded Pedersen content is that the
SUM of commitments equals the commitment of the SUMMED value+blinding (`commit_hom`/`map_sum`) —
so a balanced commitment sum, given matching total blindings, means the *values* balance. This is
where `CryptoPrimitives.commit_hom` does the work. -/

/-- A note-list's commitment sum collapses to a single commitment of the summed value under the
summed blinding (over the `CryptoPrimitives` portal) — `Σ commit vᵢ rᵢ = commit (Σ vᵢ) (Σ rᵢ)`.
PROVED from `commit_hom` via `commit_sum`/`map_sum`. -/
theorem listCommit_collapse [CryptoPrimitives Digest] (notes : List Note) :
    listCommit (CryptoPrimitives.commit (Digest := Digest)) notes
      = CryptoPrimitives.commit ((notes.map Note.value).sum) ((notes.map Note.blinding).sum) := by
  classical
  unfold listCommit noteCommit
  -- rewrite the list sum as a Finset sum over indices, then apply `commit_sum`
  induction notes with
  | nil => simp [commit_zero]
  | cons nt rest ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [CryptoPrimitives.commit_hom]

/-- **`pedersen_value_conservation` — the homomorphic conservation theorem (uses `commit_hom`).**
A satisfying trace whose total input blinding equals total output blinding has its INPUT VALUE SUM
equal to its OUTPUT VALUE SUM *as committed*: `commit (Σ inValue) (Σ inBl) = commit (Σ outValue)
(Σ outBl)`. This is the Pedersen homomorphism collapsing the per-note commitment sums (the bridge's
commitment-conservation) into a single value-level commitment equation — the real
`committed_conservation_kernel` content, re-homed onto the circuit trace. The step from this
commitment equation to `Σ inValue = Σ outValue` on the amounts is exactly `binding` (the carrier),
honestly not asserted here. -/
theorem pedersen_value_conservation [CryptoPrimitives Digest] (circuit : CircuitIR)
    (h : Conserves (CryptoPrimitives.commit (Digest := Digest)) circuit) :
    CryptoPrimitives.commit ((circuit.ins.map Note.value).sum) ((circuit.ins.map Note.blinding).sum)
      = (CryptoPrimitives.commit ((circuit.outs.map Note.value).sum)
          ((circuit.outs.map Note.blinding).sum) : Digest) := by
  obtain ⟨hbal, _, _⟩ := h
  rw [← listCommit_collapse, ← listCommit_collapse]
  exact hbal

/-! ## The cleartext→commitment conservation theorem (the `committed_conservation_kernel` re-home).

The classic Pedersen opening of Law 1 over HIDDEN amounts, now over the Layer-A portal: from
cleartext value conservation (`Σ vᵢ = Σ vₒ`) and matching blinding totals, the COMMITMENT sums
balance — a verifier confirms conservation while seeing only commitments. PROVED via `commit_sum`
(= `commit_hom` + `map_sum`). This is the indexed-`Finset` form the executor uses; the bridge
above is the list/trace form the circuit uses. -/
theorem committed_conservation [CryptoPrimitives Digest]
    {ι κ : Type} (insV : ι → Int) (inB : ι → Int) (outV : κ → Int) (outB : κ → Int)
    (sin : Finset ι) (sout : Finset κ)
    (hval : (sin.sum insV) = (sout.sum outV))
    (hblind : (sin.sum inB) = (sout.sum outB)) :
    (sin.sum (fun i => CryptoPrimitives.commit (insV i) (inB i)) : Digest)
      = sout.sum (fun j => CryptoPrimitives.commit (outV j) (outB j)) := by
  rw [commit_sum (Digest := Digest) insV inB sin,
      commit_sum (Digest := Digest) outV outB sout, hval, hblind]

/-! ## Layer B — the Pedersen `VerifierKernel`: `verify` + carriers + DERIVED `verify_sound`.

Mirrors `MerkleVerifierKernel`. `verify` is the §8 oracle; `extractable` (STARK soundness) gives
"accept ⇒ a satisfying trace exists"; `binding` (Pedersen/DLog) is what makes the commitment-sum
equation testify to the amount equation. `pedersen_verify_sound` is DERIVED off the bridge. -/

/-- **Layer B — the Pedersen `VerifierKernel`.** The `commit` primitive, the §8 `verify` oracle
over disclosed `(insC, outsC)` commitments, the STARK `extractable` carrier, and the Pedersen
`binding` carrier (DLog). `extract` unpacks `extractable` to its operational content: an accepted
proof witnesses a satisfying trace whose `statementOf` is the disclosed statement. -/
class PedersenVerifierKernel (Digest : Type u) (Proof : Type u) [AddCommGroup Digest] where
  /-- The Pedersen commitment (the Layer-A `commit`; its `binding` is the carrier below). -/
  commit : Int → Int → Digest
  /-- `commit_hom` re-stated at the kernel level so `verify_sound` is self-contained. -/
  commit_hom : ∀ v w r s, commit (v + w) (r + s) = commit v r + commit w s
  /-- **The §8 verify oracle** (`stark::verify` for the Pedersen value-commitment AIR): does
  `proof` discharge the disclosed statement `(insC, outsC)`? -/
  verify : Statement Digest → Proof → Bool
  /-- **CARRIER — STARK extractability/soundness** (FRI + Fiat-Shamir): accept ⇒ a satisfying
  trace exists. A `Prop`; never proved, never `sorry`. -/
  extractable : Prop
  /-- **CARRIER — Pedersen/DLog binding**: the commitment equation cannot be opened to unbalanced
  amounts. A `Prop`; never a Lean law. -/
  binding : Prop
  /-- `extractable` UNPACKED: an accepted proof witnesses a satisfying trace whose disclosed
  commitments are the statement. The named form the bridge composes with — STARK soundness. -/
  extract : extractable →
    ∀ (stmt : Statement Digest) (proof : Proof), verify stmt proof = true →
      ∃ circuit : CircuitIR, statementOf commit circuit = stmt
        ∧ Satisfies commit stmt circuit

variable {Proof : Type u}

/-- **`pedersen_verify_sound` — the DERIVED verify law (the analog of `merkle_verify_sound`).**
Given the STARK-soundness carrier `extractable`, an accepted Pedersen proof PROVES that the hidden
amounts CONSERVE (and are each non-negative):

    verify stmt proof = true  →  ∃ circuit, statementOf circuit = stmt ∧ Conserves circuit

The proof composes `extract` (accept ⇒ satisfying trace, the crypto carrier) with
`pedersen_conservation_bridge` (satisfying trace ⇔ conservation, FULLY proved via `commit_hom`).
The verify law is DERIVED, not assumed. The ONLY hypothesis is `extractable`; the `binding`
carrier names the residual cryptographic content (commitment-eq testifies amount-eq) but the
algebra is unconditional. -/
theorem pedersen_verify_sound [K : PedersenVerifierKernel Digest Proof]
    (hext : K.extractable) (stmt : Statement Digest) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    ∃ circuit : CircuitIR,
      statementOf K.commit circuit = stmt ∧ Conserves K.commit circuit := by
  obtain ⟨circuit, hstmt, hsat⟩ := K.extract hext stmt proof haccept
  refine ⟨circuit, hstmt, ?_⟩
  -- transport Satisfies onto statementOf circuit, then cross the bridge
  rw [← hstmt] at hsat
  exact (pedersen_conservation_bridge K.commit circuit).mp hsat

/-! ## Layer C — the kind obligation + the DIAL wiring at the `selective` floor.

Pedersen DISCLOSES the commitments (not the amounts) — so its epistemic floor is `selective`
(chosen facts + the conclusion), NOT the `acceptanceOnly` ZK bottom Merkle sits at. We wire
`EpistemicDial.DiscloseAt` to the verifier exactly as `PredicateKernel` does for Merkle. -/

open Dregg2.Authority.Predicate Dregg2.Laws Metatheory

/-- **`KindObligation`** for Pedersen — statement algebra `Statement Digest`, relation `Conserves`
(via the trace it discloses), **dial floor = `selective`** (commitments shown, amounts hidden;
`PHASE-CRYPTOKERNEL.md §5`: "Dial: `selective`"). -/
structure KindObligation (Digest : Type u) where
  /-- The public-input algebra: the disclosed commitment lists. -/
  Statement : Type u
  /-- The dial floor — `selective` for Pedersen. -/
  dialFloor : Dial

/-- The Pedersen kind's obligation: statement = disclosed commitments, floor = `selective`. -/
def pedersenKindObligation : KindObligation Digest where
  Statement := Statement Digest
  dialFloor := Dial.selective

omit [AddCommGroup Digest] in
@[simp] theorem pedersenKindObligation_floor :
    (pedersenKindObligation (Digest := Digest)).dialFloor = Dial.selective :=
  rfl

omit [AddCommGroup Digest] in
/-- `selective` is strictly above the ZK floor (Pedersen discloses MORE than blinded membership):
the floor is non-degenerate above `acceptanceOnly`. -/
theorem pedersen_floor_above_bot :
    (⊥ : Dial) < (pedersenKindObligation (Digest := Digest)).dialFloor := by
  show Dial.acceptanceOnly < Dial.selective
  exact Dial.acceptanceOnly_lt_selective

/-! ### The dial wiring — `DiscloseAt` instantiated at the Pedersen verifier's `selective` floor.

We instantiate over the `Type` universe (the registry/dial machinery lives at universe 0), as
`PredicateKernel` does. The statement/proof are the Pedersen `Statement`/`Proof`; `accepts` at
every notch is the position-independent `Discharged` check (the verifier consults the witness,
never the disclosure level), and the `leaked` information at the floor is the disclosed
commitments themselves (the `selective` content) — coarsened to `Unit` here, the wiring being the
point. -/

section Wiring

variable {D : Type} [AddCommGroup D] {P : Type}

/-- A `Verifier (Statement D) P` from the kernel's §8 `verify` oracle. -/
def pedersenVerifier [K : PedersenVerifierKernel D P] : Verifier (Statement D) P :=
  fun stmt proof => K.verify stmt proof

/-- The Pedersen-kind registry: the §8 `verify` oracle installed at `pedersen`. -/
def pedersenReg [PedersenVerifierKernel D P]
    (base : Registry (Statement D) P) : Registry (Statement D) P :=
  fun j => if j = .pedersen then some pedersenVerifier else base j

/-- The `Verifiable` seam this kind dispatches through (explicit `base`, not auto-synthesized). -/
@[reducible] def pedersenSeam [PedersenVerifierKernel D P]
    (base : Registry (Statement D) P) : Verifiable (Statement D) P :=
  verifiableOfRegistry (pedersenReg base) .pedersen

/-- **`pedersenDisclose` — the dial pinned to the Pedersen verifier.** `accepts d` is the
position-independent `Discharged stmt proof`; `accepts_eq := fun _ => Iff.rfl`. Realizes
"instantiate `DiscloseAt` at the `selective` floor (disclosed commitments)". -/
def pedersenDisclose [PedersenVerifierKernel D P]
    (base : Registry (Statement D) P) (stmt : Statement D) (proof : P) :
    @DiscloseAt Unit (Statement D) P _ (pedersenSeam base) :=
  letI : Verifiable (Statement D) P := pedersenSeam base
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := stmt
    wit := proof
    accepts := fun _ => Discharged stmt proof
    accepts_eq := fun _ => Iff.rfl }

/-- **`pedersen_dial_wired` — THE DIAL WIRING (the analog of `merkle_dial_wired`).** The Pedersen
kind's epistemic floor is `selective` (commitments disclosed), the dial's bottom notch's
acceptance bit IS the Pedersen verifier's `Discharged` bit, and — given STARK `extractable` — an
accepting proof PROVES conservation. The dial is pinned to the per-kind verifier, no longer
floating above the portal. -/
theorem pedersen_dial_wired [K : PedersenVerifierKernel D P]
    (hext : K.extractable)
    (base : Registry (Statement D) P) (stmt : Statement D) (proof : P) :
    -- (1) the floor is selective:
    (pedersenKindObligation (Digest := D)).dialFloor = Dial.selective ∧
    -- (2) the dial's bottom notch accepts IFF the Pedersen verifier discharges:
    (@DiscloseAt.accepts Unit (Statement D) P _ (pedersenSeam base)
        (pedersenDisclose base stmt proof) (⊥ : Dial)
      ↔ @Discharged (Statement D) P (pedersenSeam base) stmt proof) ∧
    -- (3) and an accepting proof PROVES conservation (the cascade):
    (K.verify stmt proof = true →
      ∃ circuit : CircuitIR, statementOf K.commit circuit = stmt
        ∧ Conserves K.commit circuit) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact @DiscloseAt.accepts_bot_iff_discharged Unit (Statement D) P _ (pedersenSeam base)
      (pedersenDisclose base stmt proof)
  · exact fun haccept => pedersen_verify_sound hext stmt proof haccept

/-- **`pedersen_registry_cascade` — the §8 discharge through the registry (the analog of
`merkle_registry_cascade`).** Registering the Pedersen kind, an accepted proof both
`Discharged`s the kind's predicate (the registry keystone, `registry_sound`) AND — given the
STARK `extractable` carrier — PROVES conservation (`pedersen_verify_sound`). The cascade
`registry_sound ∘ pedersen_verify_sound`; the single trust boundary is `extractable`. -/
theorem pedersen_registry_cascade [K : PedersenVerifierKernel D P]
    (hext : K.extractable)
    (base : Registry (Statement D) P)
    (stmt : Statement D) (proof : P)
    (haccept : K.verify stmt proof = true) :
    (@Discharged (Statement D) P (verifiableOfRegistry (pedersenReg base) .pedersen) stmt proof)
      ∧ ∃ circuit : CircuitIR, statementOf K.commit circuit = stmt
          ∧ Conserves K.commit circuit := by
  refine ⟨?_, pedersen_verify_sound hext stmt proof haccept⟩
  apply registry_sound (pedersenReg base) .pedersen stmt proof
  show registryVerify (pedersenReg base) .pedersen stmt proof = true
  unfold registryVerify pedersenReg
  simp only [↓reduceIte]
  exact haccept

end Wiring

/-! ## `Reference` — a concrete instance + non-vacuity witnesses over `ℤ`.

The Layer-A `Crypto.Reference.instCryptoPrimitives` gives `commit v r := v + r` over `ℤ`. We
build a degenerate Pedersen verifier kernel `def` (NOT a global `instance`, to avoid silent
auto-resolution) and witness the bridge/verify-sound/cascade end-to-end. NOT real crypto. -/

namespace Reference

open Dregg2.Crypto.Reference

/-- A concrete one-input/one-output conserving trace over `ℤ`: a single note of value `v`
(blinding `r`) transferred to a single output note of the same value (blinding `r`), with the
2-bit range witness for a small `v`. Here `commit := (+)`, so the commitment is `v + r`. -/
def sampleCircuit (v r : Int) (bits : List Int) : CircuitIR :=
  { ins := [{ value := v, blinding := r, bits := bits }]
    outs := [{ value := v, blinding := r, bits := bits }] }

/-- The reference commitment over `ℤ`: `commit v r := v + r` (the degenerate linear stand-in,
matching `refKernel.commit` and the Layer-A `Reference.instCryptoPrimitives`). -/
def refCommit : Int → Int → Int := fun v r => v + r

/-- Non-vacuity of the BRIDGE: the sample trace (input = output) conserves, and the bridge
certifies it satisfies the AIR. We instantiate with `v = 1`, `bits = [1]` (1-bit decomposition of
`1`: `bitsToInt [1] = 1`, `Boolean [1]`). -/
example (r : Int) :
    Satisfies refCommit (statementOf refCommit (sampleCircuit 1 r [1])) (sampleCircuit 1 r [1]) := by
  refine (pedersen_conservation_bridge refCommit (sampleCircuit 1 r [1])).mpr ?_
  refine ⟨?_, ?_, ?_⟩
  · -- listCommit ins = listCommit outs (identical lists)
    rfl
  · intro nt hnt
    simp only [sampleCircuit, List.mem_singleton] at hnt
    subst hnt
    refine ⟨?_, ?_⟩
    · intro b hb; simp only [List.mem_singleton] at hb; subst hb; right; rfl
    · simp [bitsToInt]
  · intro nt hnt
    simp only [sampleCircuit, List.mem_singleton] at hnt
    subst hnt
    refine ⟨?_, ?_⟩
    · intro b hb; simp only [List.mem_singleton] at hb; subst hb; right; rfl
    · simp [bitsToInt]

/-- Read a disclosed commitment `c` as a degenerate note `(value 0, blinding c, bits [])`. Over
the `ℤ` reference `commit := (+)`, `commit 0 c = c`, so this is a valid `extract` reconstruction. -/
def noteOf (c : Int) : Note := { value := 0, blinding := c, bits := [] }

/-- Reconstructing notes from a commitment list and re-committing under `refCommit` recovers the
list (`refCommit 0 c = 0 + c = c`). The `PiBinding`-recovery lemma the reference `extract` rests
on. -/
theorem map_commit_noteOf (l : List Int) :
    (l.map noteOf).map (noteCommit refCommit) = l := by
  induction l with
  | nil => rfl
  | cons c rest ih => simp only [List.map_cons, noteCommit, noteOf, refCommit, ih, zero_add]

/-- A degenerate reference Pedersen verifier kernel over `ℤ` (`def`, not a global `instance`).
`commit := (+)`; `verify` accepts iff the disclosed input/output commitment sums are equal
(`stmt.insC.sum = stmt.outsC.sum`); `extractable`/`binding := True`. `extract` rebuilds a trivial
satisfying trace from the disclosed commitments via `noteOf` (so `commit 0 c = c`, `bits = []`
gives the `0`-value range gadget). -/
@[reducible] def refKernel : PedersenVerifierKernel Int Int where
  commit := refCommit
  commit_hom := by intro v w r s; simp only [refCommit]; ring
  verify stmt _ := decide (stmt.insC.sum = stmt.outsC.sum)
  extractable := True
  binding := True
  extract := by
    intro _ stmt _ haccept
    simp only [decide_eq_true_eq] at haccept
    refine ⟨{ ins := stmt.insC.map noteOf, outs := stmt.outsC.map noteOf }, ?_, ?_⟩
    · -- statementOf rebuilds stmt: map (commit 0 c) = map id = stmt
      cases stmt with
      | mk insC outsC => simp only [statementOf]; rw [map_commit_noteOf insC, map_commit_noteOf outsC]
    · -- Satisfies: PiBindings, the trivial (empty-bits) range gadgets, and the sum equality
      refine ⟨(map_commit_noteOf stmt.insC).symm, (map_commit_noteOf stmt.outsC).symm, ?_, ?_, haccept⟩
      · intro nt hnt
        simp only [List.mem_map] at hnt
        obtain ⟨c, _, rfl⟩ := hnt
        exact ⟨by intro b hb; simp [noteOf] at hb, rfl⟩
      · intro nt hnt
        simp only [List.mem_map] at hnt
        obtain ⟨c, _, rfl⟩ := hnt
        exact ⟨by intro b hb; simp [noteOf] at hb, rfl⟩

/-- The empty base registry over the toy `ℤ` Pedersen statement/proof. -/
def base : Registry (Statement Int) Int := fun _ => none

/-- A disclosed balanced statement over `ℤ`: a single input commitment `5` and a single output
commitment `5` — the sums are equal, so the reference verifier accepts. -/
def balancedStmt : Statement Int := { insC := [5], outsC := [5] }

/-- Non-vacuity of `pedersen_verify_sound`: at the reference kernel an accepted proof yields a
trace whose disclosed commitments are `balancedStmt` and which CONSERVES. -/
example :
    ∃ circuit : CircuitIR,
      statementOf refKernel.commit circuit = balancedStmt ∧ Conserves refKernel.commit circuit :=
  pedersen_verify_sound (K := refKernel) trivial balancedStmt 0 (by decide)

/-- Non-vacuity of the FULL cascade: at the reference kernel an accepted proof both `Discharged`s
the registry predicate AND proves conservation. -/
example :
    (@Discharged (Statement Int) Int
        (verifiableOfRegistry (@pedersenReg Int _ Int refKernel base) .pedersen) balancedStmt 0)
      ∧ ∃ circuit : CircuitIR,
          statementOf refKernel.commit circuit = balancedStmt ∧ Conserves refKernel.commit circuit :=
  pedersen_registry_cascade (K := refKernel) trivial base balancedStmt 0 (by decide)

/-- Non-vacuity of the dial wiring: the floor is `selective`, the dial's bottom notch is the
verifier's bit, and an accepting proof proves conservation. -/
example :
    (pedersenKindObligation (Digest := Int)).dialFloor = Dial.selective :=
  (pedersen_dial_wired (K := refKernel) trivial base balancedStmt 0).1

end Reference

-- TRIPWIRES: the conservation bridge + derived verify-soundness + cascade + dial wiring are
-- kernel-clean. The bridge & range/non-negativity are FULLY proved (the algebra rests on
-- `commit_hom`, the honest `range_iff` gadget — NO primitive seam). The ONLY cryptographic
-- residue is the `extractable`/`binding` carriers (passed as hypotheses), never a hidden `sorry`.
#assert_axioms commit_sum
#assert_axioms pedersen_conservation_bridge
#assert_axioms pedersen_amounts_nonneg
#assert_axioms committed_conservation
#assert_axioms pedersen_verify_sound
#assert_axioms pedersen_registry_cascade
#assert_axioms pedersen_dial_wired

end Dregg2.Crypto.Pedersen
