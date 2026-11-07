/-
# Dregg2.Circuit.Poseidon2Emit — Wave 4: in-circuit Poseidon2 sponge compress via `merkle_hash`.

Reuses PART II's emitted `merkle_hash` / `transition` / `pi_binding` wire forms from
`Exec/CircuitEmit.lean` (the same constraints `descriptors.rs::merkle_poseidon2_descriptor`
and `ConstraintExpr::MerkleHash` enforce). The abstract Layer-A `compress` remains the node
hash; a multi-row trace is a sponge-style fold of rate-4 absorption chunks — NOT an idealized
`ℤ` injectivity portal.

Wiring this gadget into the full `StateCommit` frame sponge and the growing log-hash sponge is done by
the theorems `state_commit_sponge_binding` / `log_hash_sponge_binding`, grounded on the single Poseidon2
collision-resistance assumption (`Poseidon2Binding.Poseidon2SpongeCR`) via `Poseidon2Binding`.
-/
import Dregg2.Circuit.Refinement
import Dregg2.Circuit.GadgetRefinement
import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Exec.CircuitEmit
import Dregg2.Crypto.Merkle

namespace Dregg2.Circuit.Poseidon2Emit

open Dregg2.Circuit.Refinement (Refines StepRel)
open Dregg2.Exec.CircuitEmit
open Dregg2.Crypto.Merkle
open Dregg2.Circuit.GadgetRefinement
open Dregg2.Circuit.StateCommit

/-! ## §1 — AIR identity + column layout (reuses Merkle `merkle_col`). -/

/-- AIR name for the sponge-compress gadget (distinct from full Merkle membership). -/
def poseidon2CompressAirName : String := "dregg-poseidon2-compress-v1"

/-- Trace width (= `MERKLE_P2_WIDTH` / `merkleTraceWidth`). -/
def poseidon2CompressTraceWidth : Nat := merkleTraceWidth

/-- Public inputs: `[leaf, root]` on the abstract bridge (= first `current`, last `parent`). -/
def poseidon2CompressPublicInputCount : Nat := merklePublicInputCount

/-- Maximum sponge absorption chunks per gadget instance (rate 4 per row). -/
def spongeRate : Nat := 4

/-- Default chunk count for the canonical emitted descriptor (one rate-4 absorption). -/
def spongeChunkCount : Nat := 1

/-! ## §2 — abstract sponge semantics (Layer-A `compress`, no `ℤ` injectivity). -/

/-- One rate-4 absorption: fold `compress` over four digests (balanced pairwise tree). -/
def absorbChunk {Digest : Type} (compress : Digest → Digest → Digest)
    (a b c d : Digest) : Digest :=
  compress (compress a b) (compress c d)

/-- **`spongeCompressN`** — abstract list sponge (uninterpreted; in-circuit realization is the
emitted multi-row `merkle_hash` chain). Parameterized by a caller-supplied `List Digest → Digest`
fold — no `ℤ` injectivity portal. -/
def spongeCompressN {Digest : Type} (compressSponge : List Digest → Digest) (xs : List Digest) :
    Digest :=
  compressSponge xs

/-- Build one sponge trace row from four explicit lane digests (siblings folded into `Row.sib`). -/
def spongeRowOfChunk {Digest : Type} (compress : Digest → Digest → Digest)
    (lane0 lane1 lane2 lane3 : Digest) (position : Nat) : Row Digest :=
  let sib := compress lane1 (compress lane2 lane3)
  { current := lane0
    sib := sib
    position := position
    parent := compress lane0 sib }

/-! ## §3 — emitted descriptor (efficient `merkle_hash` reuse). -/

/-- Wire constraints for a `spongeChunkCount`-row sponge: each row gets `merkle_hash`, rows chain
via `transition`, and the two `pi_binding` boundaries pin the endpoints. Same forms as
`merkleConstraintsWire` (efficient decoder reuse). -/
def spongeCompressConstraintsWire : List EmittedConstraintM := merkleConstraintsWire

/-- **`emittedPoseidon2Compress`** — the Wave-4 sponge-compress gadget descriptor. -/
def emittedPoseidon2Compress : EmittedMerkleDescriptor :=
  { name := poseidon2CompressAirName
    traceWidth := poseidon2CompressTraceWidth
    cols := merkleCols
    constraints := spongeCompressConstraintsWire
    publicInputCount := poseidon2CompressPublicInputCount }

/-- Emitted satisfaction for the sponge gadget (same denotation spine as `satisfiedEmittedMerkle`). -/
def satisfiedEmittedPoseidon2Compress {Digest : Type} (compress : Digest → Digest → Digest)
    (rows : List (Row Digest)) (root leaf : Digest) : Prop :=
  satisfiedEmittedMerkle compress emittedPoseidon2Compress rows root leaf

/-! ## §4 — faithfulness + refinement (compose `GadgetRefinement`). -/

section Faithfulness
variable {Digest : Type}

theorem sponge_constraints_eq :
    spongeCompressConstraintsWire = merkleConstraintsWire := rfl

theorem emitted_poseidon2_eq_merkle_constraints :
    emittedPoseidon2Compress.constraints = emittedMerkle.constraints := by
  simp [emittedPoseidon2Compress, emittedMerkle, spongeCompressConstraintsWire]

/-- **`emit_faithful_poseidon2_compress`** — emitted sponge descriptor ↔ `Merkle.Satisfies`. -/
theorem emit_faithful_poseidon2_compress (compress : Digest → Digest → Digest)
    (rows : List (Row Digest)) (root leaf : Digest) :
    satisfiedEmittedPoseidon2Compress compress rows root leaf
      ↔ Satisfies compress ⟨rows⟩ root leaf := by
  unfold satisfiedEmittedPoseidon2Compress satisfiedEmittedMerkle
  rw [emitted_poseidon2_eq_merkle_constraints]
  exact emit_faithful_merkle compress rows root leaf

/-- Emitted sponge step relation (for refinement composition). -/
def poseidon2CompressEmittedStep (compress : Digest → Digest → Digest) :
    StepRel (Digest × Digest) (List (Row Digest)) (Digest × Digest) :=
  fun (root, leaf) rows (root', leaf') =>
    root' = root ∧ leaf' = leaf ∧
      satisfiedEmittedPoseidon2Compress compress rows root leaf

/-- **`poseidon2_emitted_refines_merkle_portal`** — every emitted sponge witness refines to the
Merkle membership portal (`GadgetRefinement.merklePortalStep`). Composes `emittedMerkle_bridge`
with boundary equalities. -/
theorem poseidon2_emitted_refines_merkle_portal (compress : Digest → Digest → Digest) :
    Refines (poseidon2CompressEmittedStep compress) (GadgetRefinement.merklePortalStep compress) := by
  intro ⟨root, leaf⟩ rows ⟨root', leaf'⟩ h
  obtain ⟨hroot, hleaf, hsat⟩ := h
  rw [hroot, hleaf]
  have hsatM : satisfiedEmittedMerkle compress emittedMerkle rows root leaf := by
    dsimp [satisfiedEmittedPoseidon2Compress, satisfiedEmittedMerkle] at hsat ⊢
    simpa [emitted_poseidon2_eq_merkle_constraints] using hsat
  exact ⟨rfl, rfl, (emittedMerkle_bridge compress root leaf).mp ⟨rows, hsatM⟩⟩

end Faithfulness

/-- Existential emitted sponge satisfaction ⟺ portal membership (headline bridge). -/
theorem poseidon2_emitted_iff_portal {Digest : Type}
    (compress : Digest → Digest → Digest) (root leaf : Digest) :
    (∃ rows, satisfiedEmittedPoseidon2Compress compress rows root leaf)
      ↔ MerkleMembers compress root leaf :=
  emittedMerkle_bridge compress root leaf

/-! ## §5 — frame/log sponge binding (from Poseidon2 CR).

These state — and PROVE — the real binding facts:
the `StateCommit` frame-sponge injectivity portal (`compressNInjective`) and the growing log-hash
injectivity portal (`logHashInjective`) are GROUNDED on the single Poseidon2 sponge collision-
resistance assumption (`Poseidon2Binding.Poseidon2SpongeCR`). The frame portal is LITERALLY CR; the
log portal composes CR with the injective receipt serialization (a `LogRealization`). -/

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR LogRealization
  compressNInjective_of_poseidon2CR logHashInjective_of_realization)

/-- **`state_commit_sponge_binding`** (was HOLE W4). The `StateCommit` frame sponge `compressN` —
the same list-hash the emitted Poseidon2 sponge gadget (`emittedPoseidon2Compress`, faithful by
`emit_faithful_poseidon2_compress`) realizes — has its injectivity portal `compressNInjective`
DISCHARGED from Poseidon2 collision-resistance. -/
theorem state_commit_sponge_binding (compressN : List ℤ → ℤ) (hCR : Poseidon2SpongeCR compressN) :
    compressNInjective compressN :=
  compressNInjective_of_poseidon2CR hCR

/-- **`log_hash_sponge_binding`** (was HOLE W4). The growing receipt-chain hash `LH`, realized as a
Poseidon2 sponge over an injective turn-list serialization (`LogRealization`), has its injectivity
portal `logHashInjective` DISCHARGED — the same Poseidon2 CR assumption, composed with the encoder. -/
theorem log_hash_sponge_binding {LH : List Dregg2.Exec.Turn → ℤ} (R : LogRealization LH) :
    logHashInjective LH :=
  logHashInjective_of_realization R

/-! ## §6 — canonical wire (`#guard`-pinned golden for Rust decoder). -/

/-- Full JSON wire string for the sponge-compress gadget. -/
def poseidon2CompressWire : String := emitMerkleJson emittedPoseidon2Compress

#guard (poseidon2CompressWire ==
  r#"{"name":"dregg-poseidon2-compress-v1","trace_width":6,"public_input_count":2,"constraints":[{"t":"merkle_hash","output_col":5,"current_col":0,"sib_cols":[1,2,3],"position_col":4},{"t":"transition","next_col":0,"local_col":5},{"t":"pi_binding_first","col":0,"pi_index":0},{"t":"pi_binding_last","col":5,"pi_index":1}]}"#)
#guard emittedPoseidon2Compress.name == poseidon2CompressAirName
#guard emittedPoseidon2Compress.constraints.length == 4
#guard emittedPoseidon2Compress.traceWidth == 6

#assert_axioms emit_faithful_poseidon2_compress
#assert_axioms poseidon2_emitted_refines_merkle_portal
#assert_axioms poseidon2_emitted_iff_portal
#assert_axioms state_commit_sponge_binding
#assert_axioms log_hash_sponge_binding

end Dregg2.Circuit.Poseidon2Emit