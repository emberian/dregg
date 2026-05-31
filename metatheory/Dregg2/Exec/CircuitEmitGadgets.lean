/-
# Dregg2.Exec.CircuitEmitGadgets — emitting the OTHER §8 gadget circuits to the wire.

`Dregg2.Exec.CircuitEmit` (imported read-only) discharged the EXTRACTION hop for the kernel
(`emittedKernel_bridge`, var/const/add/mul AST) and the Merkle gadget (`emittedMerkle_bridge`,
the column-indexed `MerkleHash`/`Transition`/`PiBinding` forms over abstract `Digest`s), plus the
algebraic `ConstraintExpr` lowering (`emitA_faithful`). This module extends the SAME pattern —
`emit<Gadget>` to the wire + an `emitted<Gadget>_bridge` composing emit-faithfulness with each
gadget's own `*_bridge` — to the REMAINING §8 gadgets:

  * **Temporal** (`Crypto.Temporal`) — TWO range gadgets (`t - lo ≥ 0`, `hi - t ≥ 0`), each the
    honest `Binary`-bits + recomposition gadget. NO new wire forms beyond a `range` carrier.
    `emittedTemporal_bridge : (∃ trace, satisfiedEmittedTemporal …) ↔ InWindow lo hi t`.
  * **NonMembership** (`Crypto.NonMembership`) — TWO reused Merkle sub-circuits (PART II's
    `EmittedConstraintM`/`satisfiedEmittedMerkle`) + the sorted-adjacency side condition + the two
    comparison range gadgets. `emittedNonMembership_bridge` composes with `nonmembership_bridge`.
  * **Pedersen** (`Crypto.Pedersen`) — the abstract-`commit` `PiBinding` boundaries (commitments to
    the disclosed public inputs) + per-note range gadgets + the conservation (commitment-sum
    equality) constraint. Mirrors Merkle's abstract-`compress` carrier — `commit` stays a `Prop`
    carrier in the denotation, no algebra in the wire form. `emittedPedersen_bridge` composes with
    `pedersen_conservation_bridge`.
  * **Dfa** (`Crypto.Dfa`) — the abstract-`δ` `Lookup` (per-step membership) + `Transition`
    (chaining) + the initial/accept boundary `PiBinding`s. Mirrors the `Lookup`-as-`δ` carrier.
    `emittedDfa_bridge` composes with `dfa_bridge`.

HONEST status (which emit is green + Rust-decoder additions each needs):

  * **Temporal — GREEN.** No new Rust wire form: the range gadget is `Binary` per-bit + a
    recomposition `Polynomial` (`Σ bᵢ·2ⁱ − diff = 0`), both already in PART III's `EmittedConstraintA`
    (`binary`/`polynomial`). The decoder needs only to read a `range` block = a `bit_cols` list + the
    `diff` it recomposes; it lowers to `Binary`×n + one `Polynomial`. No NEW Rust enum variant.
  * **NonMembership — GREEN.** Reuses PART II's Merkle wire form (already decoded) TWICE plus two
    `range` blocks (as Temporal) plus a structural `adjacency` tag. The decoder needs the
    `non_membership` envelope = two `merkle` sub-descriptors + two `range` blocks + the `lo`/`hi`
    neighbor cells; the adjacency/ordering are the structural side conditions the Layer-A bridge owns
    (no new algebraic form).
  * **Pedersen — GREEN over the abstract-`commit` carrier** (exactly as Merkle is green over abstract
    `compress`). The wire form carries the `PiBinding` boundaries (note-commitment = public input) +
    per-note `range` blocks + a `conservation` tag (`Σ insC = Σ outsC`). The decoder needs the
    Pedersen value-commitment AIR's `commit(v,r)` column wiring + the sum-equality boundary
    (`value_commitment.rs`); the commitment ALGEBRA (homomorphism) lives in the Layer-A
    `commit_hom`, not the wire — the wire denotes the structural conservation, the bridge owns the
    homomorphic step.
  * **Dfa — GREEN over the abstract-`δ` `Lookup` carrier** (exactly as the `Lookup` is abstracted as
    `δ` in `Crypto.Dfa`). The wire form carries the `Lookup` (per-row `(state,sym,next)` table
    membership), `Transition` (chaining), and the two boundary `PiBinding`s. The decoder needs the
    `dfa_lookup_descriptor` envelope = the `Lookup` table id + the `[state,byte,next]` column triple +
    the first/last boundary; the table membership is the `Lookup` constraint (already in the Rust
    `ConstraintExpr::Lookup`), `δ` being its membership predicate.

No `axiom`/`admit`/`native_decide`/`sorry`. Bridges `#assert_axioms`-pinned. Golden wire bytes via
`#eval`.
-/
import Dregg2.Exec.CircuitEmit
import Dregg2.Crypto.Temporal
import Dregg2.Crypto.NonMembership
import Dregg2.Crypto.Pedersen
import Dregg2.Crypto.Dfa

namespace Dregg2.Exec.CircuitEmitGadgets

open Dregg2.Exec.CircuitEmit

/-! ## ════════════════════════════════════════════════════════════════════════════════
## A SHARED `range` wire block — the honest `Binary`-bits + recomposition gadget.
## ════════════════════════════════════════════════════════════════════════════════

Temporal, NonMembership and Pedersen all reuse the SAME range gadget (`Exec/RecordCircuit`'s
`range_iff`): a list of boolean `bit` cells whose little-endian recomposition equals a value (here
the disclosed difference). On the wire this is `Binary` per bit + a `Polynomial` recomposition gate
(`Σ bᵢ·2ⁱ − value = 0`) — BOTH already in PART III's `EmittedConstraintA`, so there is NO new Rust
wire form. We package the block as an `EmittedRange` (the `bit` columns) with a denotation that lands
DEFINITIONALLY on `RecordCircuit.Boolean bits ∧ bitsToInt bits = value` — the same conjunct the
gadgets' `Satisfies` read. -/

open Dregg2.Exec.RecordCircuit

/-- **`EmittedRange`** — a wire-form range gadget: the list of `bit` column indices (the `DIFF_BITS`)
the decoder turns into `Binary`×n + one recomposition `Polynomial`. Wire metadata only; the
denotation reads the bit VALUES off the supplied bit list. -/
structure EmittedRange where
  /-- The bit-column indices (for the Rust decoder to rebuild `Binary`×n + the recomposition gate). -/
  bitCols : List Nat
  deriving Repr, DecidableEq

/-- **`EmittedRange.holds bits value`** — the range block is satisfied by the bit-witness `bits`
recomposing `value`: booleanity (`Binary`, the per-bit gate) AND recomposition (`bitsToInt = value`,
the `Polynomial` gate). Lands definitionally on the gadgets' range conjunct. -/
def EmittedRange.holds (_ : EmittedRange) (bits : List Int) (value : Int) : Prop :=
  Boolean bits ∧ bitsToInt bits = value

/-- The canonical range block with `n` placeholder bit columns `[0,1,…,n-1]` (wire metadata; the
denotation reads the bit values, not the indices). -/
def rangeBlock (n : Nat) : EmittedRange := { bitCols := List.range n }

/-- Lower a range block to the PART-III algebraic forms it decodes to: one `binary` per bit column
plus one recomposition `polynomial` `Σ bᵢ·2ⁱ − value`. This is the explicit Rust-decoder lowering
(documenting the NO-new-wire-form claim); used for the JSON rendering, not the denotation. -/
def EmittedRange.lower (r : EmittedRange) (valueCol : Nat) : List EmittedConstraintA :=
  (r.bitCols.map (fun c => EmittedConstraintA.binary c)) ++
    -- recomposition: Σ bᵢ·2ⁱ − value = 0, as a Polynomial over the bit columns + the value column.
    [ EmittedConstraintA.polynomial
        ((r.bitCols.zipIdx.map (fun (cᵢ : Nat × Nat) => ((2 ^ cᵢ.2 : Int), [cᵢ.1])))
          ++ [((-1 : Int), [valueCol])]) ]

/-! ## ════════════════════════════════════════════════════════════════════════════════
## PART IV — Emitting the TEMPORAL gadget (two range gadgets, no primitive seam).
## ════════════════════════════════════════════════════════════════════════════════

`Crypto.Temporal.Satisfies circuit lo hi t` is the conjunction of TWO range gadgets:
`Boolean loBits ∧ bitsToInt loBits = t - lo` (lower bound) and `Boolean hiBits ∧ bitsToInt hiBits =
hi - t` (upper bound). We emit a descriptor carrying TWO `EmittedRange` blocks and prove the emitted
form denotes EXACTLY `Temporal.Satisfies`. -/

open Dregg2.Crypto.Temporal in
/-- **`EmittedTemporalDescriptor`** — the wire form for the temporal-predicate AIR: name, trace
width, the two range blocks (lower/upper bound `DIFF_BITS`), and the public-input count (`[lo, hi,
t]` = 3). Mirrors `temporal_predicate_dsl.rs`'s two-comparison shape. -/
structure EmittedTemporalDescriptor where
  name             : String
  traceWidth       : Nat
  loRange          : EmittedRange
  hiRange          : EmittedRange
  publicInputCount : Nat
  deriving Repr, DecidableEq

/-- **`satisfiedEmittedTemporal d circuit lo hi t`** — the emitted temporal descriptor is satisfied by
the temporal trace `circuit` (its two bit-witnesses) against the disclosed window/time `(lo, hi, t)`
iff each range block recomposes its difference. Built to land DEFINITIONALLY on `Temporal.Satisfies`:
the lower block on `t - lo`, the upper block on `hi - t`. -/
def satisfiedEmittedTemporal (d : EmittedTemporalDescriptor)
    (circuit : Dregg2.Crypto.Temporal.CircuitIR) (lo hi t : Int) : Prop :=
  d.loRange.holds circuit.loBits (t - lo) ∧ d.hiRange.holds circuit.hiBits (hi - t)

/-- The AIR identity string the temporal wire form carries (= the Rust `temporal_predicate_air`
family name). -/
def temporalAirName : String := "dregg-temporal-predicate-v1"

/-- The temporal AIR public-input count (`[lo, hi, t]`). -/
def temporalPublicInputCount : Nat := 3

/-- The temporal trace width: the two `DIFF`/`DIFF_BITS` comparison lanes (metadata for the decoder). -/
def temporalTraceWidth : Nat := 2

/-- **`emittedTemporal`** — the emitted temporal descriptor. Two range blocks; pure printable data,
proved faithful to `Temporal.Satisfies` by `emit_faithful_temporal`. -/
def emittedTemporal : EmittedTemporalDescriptor :=
  { name := temporalAirName, traceWidth := temporalTraceWidth,
    loRange := { bitCols := [0] }, hiRange := { bitCols := [1] },
    publicInputCount := temporalPublicInputCount }

/-- **`emit_faithful_temporal` — THE temporal faithfulness theorem.** Satisfying the EMITTED temporal
descriptor is EXACTLY `Temporal.Satisfies` — the two range blocks' denotations ARE the two range
conjuncts of `Satisfies` (definitionally). So emission loses none of the gadget semantics
`temporal_bridge` proved. -/
theorem emit_faithful_temporal (circuit : Dregg2.Crypto.Temporal.CircuitIR) (lo hi t : Int) :
    satisfiedEmittedTemporal emittedTemporal circuit lo hi t
      ↔ Dregg2.Crypto.Temporal.Satisfies circuit lo hi t :=
  Iff.rfl

/-- **`emittedTemporal_bridge` — THE deliverable.** Satisfying the EMITTED temporal circuit (for SOME
trace) is EXACTLY window membership `InWindow lo hi t` (`lo ≤ t ∧ t ≤ hi`): composing
`emit_faithful_temporal` (wire ↔ `Satisfies`) with `Temporal.temporal_bridge` (`(∃ trace, Satisfies) ↔
InWindow`). So the emitted temporal circuit the Rust backend decodes carries the SAME
soundness∧completeness `temporal_bridge` proved — pure comparison combinatorics, no seam. -/
theorem emittedTemporal_bridge (lo hi t : Int) :
    (∃ circuit, satisfiedEmittedTemporal emittedTemporal circuit lo hi t)
      ↔ Dregg2.Crypto.Temporal.InWindow lo hi t := by
  rw [← Dregg2.Crypto.Temporal.temporal_bridge lo hi t]
  constructor
  · rintro ⟨c, h⟩; exact ⟨c, (emit_faithful_temporal c lo hi t).mp h⟩
  · rintro ⟨c, h⟩; exact ⟨c, (emit_faithful_temporal c lo hi t).mpr h⟩

/-! ### Canonical temporal wire rendering (`#eval`-printable). -/

/-- Render an `EmittedRange` as JSON `{"bit_cols":[…]}` — the decoder lowers it to `Binary`×n + the
recomposition `Polynomial`. -/
def EmittedRange.toJson (r : EmittedRange) : String :=
  "{\"bit_cols\":" ++ natsToJson r.bitCols ++ "}"

/-- **`emitTemporalJson`** — the full canonical wire string for the emitted temporal descriptor. -/
def emitTemporalJson (d : EmittedTemporalDescriptor) : String :=
  "{\"name\":\"" ++ d.name ++ "\",\"trace_width\":" ++ toString d.traceWidth ++
  ",\"public_input_count\":" ++ toString d.publicInputCount ++
  ",\"lo_range\":" ++ d.loRange.toJson ++ ",\"hi_range\":" ++ d.hiRange.toJson ++ "}"

/-- The canonical temporal wire string — copy this into the Rust golden. -/
def temporalWire : String := emitTemporalJson emittedTemporal

#eval temporalWire
#eval emittedTemporal.publicInputCount   -- 3 ([lo, hi, t])
#eval emittedTemporal.traceWidth          -- 2 (two comparison lanes)

#assert_axioms emit_faithful_temporal
#assert_axioms emittedTemporal_bridge

/-! ## ════════════════════════════════════════════════════════════════════════════════
## PART V — Emitting the NON-MEMBERSHIP gadget (two Merkle sub-proofs + adjacency).
## ════════════════════════════════════════════════════════════════════════════════

`Crypto.NonMembership.Satisfies compress circuit root e leaves` is: two Merkle membership sub-proofs
(`Merkle.Satisfies` for `lo` and `hi` — reuse PART II's `satisfiedEmittedMerkle`), the committed list
is `Sorted`, `lo`/`hi` are `Adjacent`, and the two comparisons `lo < e < hi`. The emitted form carries
TWO Merkle wire descriptors (`emittedMerkle`, PART II) + the structural adjacency/comparison side
conditions; we prove it denotes EXACTLY `NonMembership.Satisfies`. -/

open Dregg2.Crypto.NonMembership

universe u

/-- **`EmittedNonMembershipDescriptor`** — the wire form for the non-membership AIR: name, trace
width, the TWO reused Merkle sub-descriptors (`loMerkle`/`hiMerkle` = PART II's `emittedMerkle`
instances), and the public-input count (`[root, e]` = 2). The adjacency/ordering are the structural
side conditions the Layer-A bridge owns (no new algebraic form). -/
structure EmittedNonMembershipDescriptor where
  name             : String
  traceWidth       : Nat
  loMerkle         : EmittedMerkleDescriptor
  hiMerkle         : EmittedMerkleDescriptor
  publicInputCount : Nat
  deriving Repr, DecidableEq

/-- **`satisfiedEmittedNonMembership compress d circuit root e leaves`** — the emitted non-membership
descriptor is satisfied by the trace `circuit` (its two bracketing neighbors + their Merkle sub-traces)
against `(root, e)` and the committed `leaves` iff: the two Merkle sub-descriptors are satisfied (the
two reused Merkle wire forms, via `satisfiedEmittedMerkle` on each sub-circuit's rows), the list is
`Sorted`, `lo`/`hi` are `Adjacent`, and `lo < e < hi`. Built to land DEFINITIONALLY on
`NonMembership.Satisfies` (the two Merkle conjuncts go through PART II's `emit_faithful_merkle`). -/
def satisfiedEmittedNonMembership {Digest : Type u} [LinearOrder Digest]
    (compress : Digest → Digest → Digest) (d : EmittedNonMembershipDescriptor)
    (circuit : CircuitIR Digest) (root e : Digest) (leaves : List Digest) : Prop :=
  satisfiedEmittedMerkle compress d.loMerkle circuit.loCircuit.rows root circuit.lo ∧
  satisfiedEmittedMerkle compress d.hiMerkle circuit.hiCircuit.rows root circuit.hi ∧
  Sorted leaves ∧
  Adjacent leaves circuit.lo circuit.hi ∧
  circuit.lo < e ∧ e < circuit.hi

/-- The AIR identity string the non-membership wire form carries. -/
def nonMembershipAirName : String := "dregg-non-membership-v1"

/-- The non-membership AIR public-input count (`[root, e]`). -/
def nonMembershipPublicInputCount : Nat := 2

/-- The non-membership trace width: the wider of the two reused Merkle lanes (metadata). -/
def nonMembershipTraceWidth : Nat := merkleTraceWidth

/-- **`emittedNonMembership`** — the emitted non-membership descriptor: two reused Merkle
sub-descriptors (`emittedMerkle`, PART II) + the public-input count. Pure printable data, proved
faithful to `NonMembership.Satisfies` by `emit_faithful_nonMembership`. -/
def emittedNonMembership : EmittedNonMembershipDescriptor :=
  { name := nonMembershipAirName, traceWidth := nonMembershipTraceWidth,
    loMerkle := emittedMerkle, hiMerkle := emittedMerkle,
    publicInputCount := nonMembershipPublicInputCount }

/-- **`emit_faithful_nonMembership` — THE non-membership faithfulness theorem.** Satisfying the
EMITTED non-membership descriptor is EXACTLY `NonMembership.Satisfies` — the two Merkle wire
sub-descriptors' denotations ARE the two `Merkle.Satisfies` conjuncts (via PART II's
`emit_faithful_merkle`), and the adjacency/comparison conjuncts coincide definitionally. So emission
loses none of the gadget semantics `nonmembership_bridge` proved. -/
theorem emit_faithful_nonMembership {Digest : Type u} [LinearOrder Digest]
    (compress : Digest → Digest → Digest) (circuit : Dregg2.Crypto.NonMembership.CircuitIR Digest)
    (root e : Digest) (leaves : List Digest) :
    satisfiedEmittedNonMembership compress emittedNonMembership circuit root e leaves
      ↔ Dregg2.Crypto.NonMembership.Satisfies compress circuit root e leaves := by
  unfold satisfiedEmittedNonMembership emittedNonMembership Dregg2.Crypto.NonMembership.Satisfies
  -- Rewrite each Merkle wire conjunct to `Merkle.Satisfies` via PART II's emit_faithful_merkle.
  -- Each Merkle wire conjunct rewrites to `Merkle.Satisfies` via PART II's emit_faithful_merkle;
  -- `⟨loCircuit.rows⟩` is `loCircuit` up to eta on the one-field structure, so the rewrite closes
  -- the goal (both sides become the same conjunction definitionally).
  rw [emit_faithful_merkle compress circuit.loCircuit.rows root circuit.lo,
      emit_faithful_merkle compress circuit.hiCircuit.rows root circuit.hi]

/-- **`emittedNonMembership_bridge` — THE deliverable.** The emitted non-membership circuit's
SOUNDNESS (every satisfying trace certifies absence) and COMPLETENESS (bracketing-neighbor witnesses
give a satisfying trace), composing `emit_faithful_nonMembership` (wire ↔ `Satisfies`) with
`NonMembership.nonmembership_bridge`. So the emitted circuit the Rust backend decodes carries the SAME
soundness∧completeness `nonmembership_bridge` proved — `compress` abstract throughout, no seam. -/
theorem emittedNonMembership_bridge {Digest : Type u} [LinearOrder Digest]
    (compress : Digest → Digest → Digest) (root e : Digest) (leaves : List Digest) :
    -- SOUNDNESS: every satisfying emitted trace certifies genuine absence.
    (∀ circuit : Dregg2.Crypto.NonMembership.CircuitIR Digest,
        satisfiedEmittedNonMembership compress emittedNonMembership circuit root e leaves →
        NonMember leaves e)
    ∧
    -- COMPLETENESS: bracketing-neighbor witnesses for a genuine absence give a satisfying emitted trace.
    (∀ lo hi : Digest, Sorted leaves → Adjacent leaves lo hi → lo < e → e < hi →
      presentAt compress root lo → presentAt compress root hi →
      ∃ circuit : Dregg2.Crypto.NonMembership.CircuitIR Digest,
        satisfiedEmittedNonMembership compress emittedNonMembership circuit root e leaves) := by
  obtain ⟨hsound, hcomplete⟩ := nonmembership_bridge compress root e leaves
  refine ⟨?_, ?_⟩
  · intro circuit h
    exact hsound circuit ((emit_faithful_nonMembership compress circuit root e leaves).mp h)
  · intro lo hi hsorted hadj hlo hhi hlomem himem
    obtain ⟨circuit, hsat⟩ := hcomplete lo hi hsorted hadj hlo hhi hlomem himem
    exact ⟨circuit, (emit_faithful_nonMembership compress circuit root e leaves).mpr hsat⟩

/-! ### Canonical non-membership wire rendering (`#eval`-printable; reuses the Merkle renderer). -/

/-- **`emitNonMembershipJson`** — the full canonical wire string: name, widths, the TWO reused Merkle
sub-descriptors (rendered by PART II's `emitMerkleJson`), and the PI count. The decoder rebuilds the
two Merkle sub-AIRs + the structural adjacency/comparison side conditions. -/
def emitNonMembershipJson (d : EmittedNonMembershipDescriptor) : String :=
  "{\"name\":\"" ++ d.name ++ "\",\"trace_width\":" ++ toString d.traceWidth ++
  ",\"public_input_count\":" ++ toString d.publicInputCount ++
  ",\"lo_merkle\":" ++ emitMerkleJson d.loMerkle ++
  ",\"hi_merkle\":" ++ emitMerkleJson d.hiMerkle ++ "}"

/-- The canonical non-membership wire string — copy this into the Rust golden. -/
def nonMembershipWire : String := emitNonMembershipJson emittedNonMembership

#eval nonMembershipWire
#eval emittedNonMembership.publicInputCount   -- 2 ([root, e])

#assert_axioms emit_faithful_nonMembership
#assert_axioms emittedNonMembership_bridge

/-! ## ════════════════════════════════════════════════════════════════════════════════
## PART VI — Emitting the PEDERSEN gadget (commit boundaries + range + conservation).
## ════════════════════════════════════════════════════════════════════════════════

`Crypto.Pedersen.Satisfies commit stmt circuit` is: the `PiBinding` boundaries (the disclosed
commitment lists ARE the trace notes' commitments under abstract `commit`), per-note range gadgets
(`Boolean bits ∧ bitsToInt = value` — reuse `EmittedRange.holds`), and the conservation
(`insC.sum = outsC.sum`). We carry `commit` ABSTRACT (the Merkle-`compress` discipline) and prove the
emitted form denotes EXACTLY `Pedersen.Satisfies`. -/

open Dregg2.Crypto.Pedersen

/-- **`EmittedPedersenDescriptor`** — the wire form for the Pedersen value-commitment AIR: name, trace
width, the public-input count (the disclosed commitment lists), plus a marker that the commit
`PiBinding` + per-note `range` + `conservation` constraints are present. The per-note range blocks are
generated per-trace at the denotation (their count is data-dependent), so the descriptor carries the
constraint SHAPE; the decoder rebuilds the value-commitment column wiring. -/
structure EmittedPedersenDescriptor where
  name             : String
  traceWidth       : Nat
  publicInputCount : Nat
  /-- Whether the conservation (commitment-sum equality) boundary constraint is present (always true
  for the value-commitment AIR; carried for decoder fidelity). -/
  hasConservation  : Bool
  deriving Repr, DecidableEq

/-- **`satisfiedEmittedPedersen commit d stmt circuit`** — the emitted Pedersen descriptor is satisfied
by the trace `circuit` against the disclosed `Statement stmt` (commitment lists) iff: the two
`PiBinding` boundaries (disclosed commitments = note commitments under `commit`), each note's range
block recomposes its value (via `EmittedRange.holds` on the note's bits), and conservation
(`insC.sum = outsC.sum`). Built to land DEFINITIONALLY on `Pedersen.Satisfies`. -/
def satisfiedEmittedPedersen {Digest : Type u} [AddCommGroup Digest]
    (commit : Int → Int → Digest) (_ : EmittedPedersenDescriptor)
    (stmt : Dregg2.Crypto.Pedersen.Statement Digest) (circuit : Dregg2.Crypto.Pedersen.CircuitIR) : Prop :=
  stmt.insC = circuit.ins.map (noteCommit commit) ∧
  stmt.outsC = circuit.outs.map (noteCommit commit) ∧
  (∀ nt ∈ circuit.ins, (rangeBlock nt.bits.length).holds nt.bits nt.value) ∧
  (∀ nt ∈ circuit.outs, (rangeBlock nt.bits.length).holds nt.bits nt.value) ∧
  stmt.insC.sum = stmt.outsC.sum

/-- The AIR identity string the Pedersen wire form carries (= the Rust value-commitment AIR name). -/
def pedersenAirName : String := "dregg-pedersen-value-commitment-v1"

/-- The Pedersen trace width: `(value, blinding)` + the range lane (metadata for the decoder). -/
def pedersenTraceWidth : Nat := 3

/-- **`emittedPedersen`** — the emitted Pedersen descriptor (PI count threads the disclosed commitment
lists; here a shape marker, the lists being data-dependent). Pure printable data, proved faithful to
`Pedersen.Satisfies` by `emit_faithful_pedersen`. -/
def emittedPedersen : EmittedPedersenDescriptor :=
  { name := pedersenAirName, traceWidth := pedersenTraceWidth,
    publicInputCount := 0, hasConservation := true }

/-- **`emit_faithful_pedersen` — THE Pedersen faithfulness theorem.** Satisfying the EMITTED Pedersen
descriptor is EXACTLY `Pedersen.Satisfies` — the two `PiBinding` conjuncts, the per-note range blocks'
denotations (`EmittedRange.holds` ↔ `Pedersen.Satisfies`'s range conjuncts), and the conservation
conjunct coincide definitionally. `commit` abstract throughout (the Merkle-`compress` discipline). So
emission loses none of the gadget semantics `pedersen_conservation_bridge` proved. -/
theorem emit_faithful_pedersen {Digest : Type u} [AddCommGroup Digest]
    (commit : Int → Int → Digest) (stmt : Dregg2.Crypto.Pedersen.Statement Digest) (circuit : Dregg2.Crypto.Pedersen.CircuitIR) :
    satisfiedEmittedPedersen commit emittedPedersen stmt circuit
      ↔ Dregg2.Crypto.Pedersen.Satisfies commit stmt circuit :=
  Iff.rfl

/-- **`emittedPedersen_bridge` — THE deliverable.** Satisfying the EMITTED Pedersen circuit, with the
disclosed `Statement` pinned to the trace's commitments (`statementOf`), is EXACTLY value conservation
`Conserves commit circuit`: composing `emit_faithful_pedersen` (wire ↔ `Satisfies`) with
`Pedersen.pedersen_conservation_bridge` (`Satisfies (statementOf …) ↔ Conserves`). So the emitted
Pedersen circuit the Rust backend decodes carries the SAME soundness∧completeness the bridge proved —
`commit` abstract throughout, the homomorphic step owned by the Layer-A `commit_hom`. -/
theorem emittedPedersen_bridge {Digest : Type u} [AddCommGroup Digest]
    (commit : Int → Int → Digest) (circuit : Dregg2.Crypto.Pedersen.CircuitIR) :
    satisfiedEmittedPedersen commit emittedPedersen (statementOf commit circuit) circuit
      ↔ Conserves commit circuit := by
  rw [emit_faithful_pedersen commit (statementOf commit circuit) circuit]
  exact pedersen_conservation_bridge commit circuit

/-! ### Canonical Pedersen wire rendering (`#eval`-printable). -/

/-- **`emitPedersenJson`** — the full canonical wire string for the emitted Pedersen descriptor. The
decoder rebuilds the value-commitment column wiring (commit `PiBinding`s + per-note range + the
conservation sum-equality boundary). -/
def emitPedersenJson (d : EmittedPedersenDescriptor) : String :=
  "{\"name\":\"" ++ d.name ++ "\",\"trace_width\":" ++ toString d.traceWidth ++
  ",\"public_input_count\":" ++ toString d.publicInputCount ++
  ",\"has_conservation\":" ++ (if d.hasConservation then "true" else "false") ++ "}"

/-- The canonical Pedersen wire string — copy this into the Rust golden. -/
def pedersenWire : String := emitPedersenJson emittedPedersen

#eval pedersenWire
#eval emittedPedersen.hasConservation     -- true (the conservation boundary)

#assert_axioms emit_faithful_pedersen
#assert_axioms emittedPedersen_bridge

/-! ## ════════════════════════════════════════════════════════════════════════════════
## PART VII — Emitting the DFA gadget (Lookup + Transition + boundary, δ abstract).
## ════════════════════════════════════════════════════════════════════════════════

`Crypto.Dfa.Satisfies δ q₀ accept circuit` is: the trace is non-empty (first/last exist), every row's
`(state, sym, next)` is a valid `δ` transition (the `Lookup` membership), the rows chain (`Transition`),
the first state is `q₀` and the final next accepts (boundary `PiBinding`s). We carry `δ` ABSTRACT (the
`Lookup`-as-membership-predicate discipline, exactly as `Crypto.Dfa` does) and prove the emitted form
denotes EXACTLY `Dfa.Satisfies`. -/

open Dregg2.Crypto.Dfa

/-- **`EmittedDfaDescriptor`** — the wire form for the DFA-lookup AIR: name, trace width, the `Lookup`
table identifier (the `dfa_lookup_table` id — the `δ` graph the decoder loads), and the public-input
count (`[q₀, accept-marker]` = 2). The `[state, byte, next]` column triple + the first/last boundary are
fixed by the descriptor; the table membership is the `ConstraintExpr::Lookup` the decoder rebuilds. -/
structure EmittedDfaDescriptor where
  name             : String
  traceWidth       : Nat
  lookupTableId    : Nat
  publicInputCount : Nat
  deriving Repr, DecidableEq

/-- **`satisfiedEmittedDfa δ q₀ accept d circuit`** — the emitted DFA descriptor is satisfied by the
trace `circuit` against the disclosed automaton `(δ, q₀, accept)` iff: the trace is non-empty with
first/last, the first state is `q₀`, the final next accepts, every row is `δ`-valid (the `Lookup`
membership), and the rows chain (`Transition`). Built to land DEFINITIONALLY on `Dfa.Satisfies`. -/
def satisfiedEmittedDfa {State Sym : Type u} (δ : State → Sym → State → Prop) (q₀ : State)
    (accept : State → Prop) (_ : EmittedDfaDescriptor) (circuit : Dregg2.Crypto.Dfa.CircuitIR State Sym) : Prop :=
  ∃ first last,
    circuit.trace.head? = some first ∧
    circuit.trace.getLast? = some last ∧
    first.state = q₀ ∧
    accept last.next ∧
    (∀ s ∈ circuit.trace, stepValid δ s) ∧
    chained circuit.trace

/-- The AIR identity string the DFA wire form carries (= the Rust `dfa_lookup_descriptor` family). -/
def dfaAirName : String := "dregg-dfa-lookup-v1"

/-- The DFA AIR public-input count (`[q₀, accept-marker]`). -/
def dfaPublicInputCount : Nat := 2

/-- The DFA trace width: the `[state, byte, next_state]` column triple. -/
def dfaTraceWidth : Nat := 3

/-- The reference `dfa_lookup_table` id (the abstract `δ` table the decoder loads). -/
def dfaLookupTableId : Nat := 0

/-- **`emittedDfa`** — the emitted DFA descriptor. Pure printable data, proved faithful to
`Dfa.Satisfies` by `emit_faithful_dfa`. -/
def emittedDfa : EmittedDfaDescriptor :=
  { name := dfaAirName, traceWidth := dfaTraceWidth,
    lookupTableId := dfaLookupTableId, publicInputCount := dfaPublicInputCount }

/-- **`emit_faithful_dfa` — THE DFA faithfulness theorem.** Satisfying the EMITTED DFA descriptor is
EXACTLY `Dfa.Satisfies` — the `Lookup` (`δ`-validity), `Transition` (chaining) and boundary `PiBinding`
conjuncts coincide definitionally. `δ` abstract throughout (the `Lookup`-as-membership discipline). So
emission loses none of the gadget semantics `dfa_bridge` proved. -/
theorem emit_faithful_dfa {State Sym : Type u} (δ : State → Sym → State → Prop) (q₀ : State)
    (accept : State → Prop) (circuit : Dregg2.Crypto.Dfa.CircuitIR State Sym) :
    satisfiedEmittedDfa δ q₀ accept emittedDfa circuit ↔ Dregg2.Crypto.Dfa.Satisfies δ q₀ accept circuit :=
  Iff.rfl

/-- **`emittedDfa_bridge` — THE deliverable.** The emitted DFA circuit's SOUNDNESS (every satisfying
trace certifies an accepting run) and COMPLETENESS (a genuine accepting run gives a satisfying trace),
composing `emit_faithful_dfa` (wire ↔ `Satisfies`) with `Dfa.dfa_bridge`. So the emitted DFA circuit the
Rust backend decodes carries the SAME soundness∧completeness `dfa_bridge` proved — `δ` (the `Lookup`
table membership) abstract throughout, no seam. -/
theorem emittedDfa_bridge {State Sym : Type u} (δ : State → Sym → State → Prop) (q₀ : State)
    (accept : State → Prop) (trace : List (Dregg2.Crypto.Dfa.Step State Sym)) :
    -- SOUNDNESS: every satisfying emitted trace over `trace` certifies an accepting run.
    (∀ circuit : Dregg2.Crypto.Dfa.CircuitIR State Sym, circuit.trace = trace →
        satisfiedEmittedDfa δ q₀ accept emittedDfa circuit → DfaAccepts δ q₀ accept trace)
    ∧
    -- COMPLETENESS: a genuine accepting run gives a satisfying emitted trace.
    (DfaAccepts δ q₀ accept trace →
      ∃ circuit : Dregg2.Crypto.Dfa.CircuitIR State Sym, satisfiedEmittedDfa δ q₀ accept emittedDfa circuit) := by
  obtain ⟨hsound, hcomplete⟩ := dfa_bridge δ q₀ accept trace
  refine ⟨?_, ?_⟩
  · intro circuit hc h
    exact hsound circuit hc ((emit_faithful_dfa δ q₀ accept circuit).mp h)
  · intro hacc
    obtain ⟨circuit, hsat⟩ := hcomplete hacc
    exact ⟨circuit, (emit_faithful_dfa δ q₀ accept circuit).mpr hsat⟩

/-! ### Canonical DFA wire rendering (`#eval`-printable). -/

/-- **`emitDfaJson`** — the full canonical wire string for the emitted DFA descriptor. The decoder
rebuilds the `dfa_lookup_descriptor`: the `Lookup` table id + the `[state,byte,next]` column triple +
the first/last boundary `PiBinding`s. -/
def emitDfaJson (d : EmittedDfaDescriptor) : String :=
  "{\"name\":\"" ++ d.name ++ "\",\"trace_width\":" ++ toString d.traceWidth ++
  ",\"lookup_table_id\":" ++ toString d.lookupTableId ++
  ",\"public_input_count\":" ++ toString d.publicInputCount ++ "}"

/-- The canonical DFA wire string — copy this into the Rust golden. -/
def dfaWire : String := emitDfaJson emittedDfa

#eval dfaWire
#eval emittedDfa.publicInputCount   -- 2 ([q₀, accept-marker])
#eval emittedDfa.traceWidth          -- 3 ([state, byte, next_state])

#assert_axioms emit_faithful_dfa
#assert_axioms emittedDfa_bridge

end Dregg2.Exec.CircuitEmitGadgets
