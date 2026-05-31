/-
# Dregg2.Exec.CircuitEmit — the EXTRACTION EMITTER: Lean circuit data → a deterministic
wire encoding the real Rust backend can decode, with a PROVED faithfulness theorem.

`Circuit.lean` gives us the verified circuit IR (`ConstraintSystem` = `List Constraint`,
`Expr` = var/const/add/mul over the field) plus the keystone

    bridge : satisfied kernelCircuit (encode s t s') ↔ fullStepInv s t s'

so checking `kernelCircuit` *is* checking the verified `fullStepInv`. What was MISSING is the
last hop: getting `kernelCircuit` — pure Lean *data* — OUT of Lean and into the real Rust
prover/verifier (`circuit/src/dsl/circuit.rs`'s `CircuitDescriptor`/`ConstraintExpr`) in a way
that PROVES the wire form did not lose the semantics `bridge` certified.

This module supplies that hop:

  * **`EmittedDescriptor`** — a Lean structure mirroring the *fields* of Rust's
    `CircuitDescriptor` (name, trace_width, constraints), where each constraint is a pair of
    `EmittedExpr` ASTs (mirroring the var/const/add/mul shape; the generic
    `ConstraintExpr::Polynomial`/AST surface). It is `Repr`-printable, so `#eval emitJson …`
    prints the canonical wire string the Rust decoder parses.
  * **`emit`** — the deterministic serializer `ConstraintSystem → EmittedDescriptor`.
  * **`decodeE`** — the inverse `EmittedDescriptor → ConstraintSystem`.
  * **`satisfiedEmitted`** — `satisfied` lifted to the emitted form.
  * **`emit_faithful`** — `satisfied cs a ↔ satisfiedEmitted (emit cs) a`: the wire form
    DENOTES the same constraint system, so the semantics `bridge` proved survive emission.
    Proved via a structure-preserving round trip (`decodeE_emit : decodeE (emit cs) = cs`),
    so faithfulness is definitional + `bridge`-compatible. `#assert_axioms`-pinned.

The Rust side (in `dregg-lean-ffi`) decodes the printed wire string back into a real
`circuit::dsl::CircuitDescriptor` and checks its `AirDescriptor::fingerprint` equals the
Rust-native AIR's — the binding "the AIR the backend runs IS the AIR Lean proved the bridge
for". See `dregg-lean-ffi/src/circuit_decode.rs`.
-/
import Dregg2.Circuit

namespace Dregg2.Exec.CircuitEmit

open Dregg2.Circuit

/-! ## The emitted expression AST — a faithful mirror of `Circuit.Expr`.

`EmittedExpr` is `Expr` re-spelled as a tagged wire form: a `var`/`const`/`add`/`mul` AST.
We keep it a *separate* inductive (rather than reusing `Expr`) so the emitter is an explicit
serialization step with its own faithfulness obligation — the wire form is not the proof
object by fiat; the round trip is proved. -/

/-- A wire-form arithmetic expression: the tagged mirror of `Circuit.Expr`. -/
inductive EmittedExpr where
  | var   : Nat → EmittedExpr
  | const : Int → EmittedExpr
  | add   : EmittedExpr → EmittedExpr → EmittedExpr
  | mul   : EmittedExpr → EmittedExpr → EmittedExpr
  deriving Repr, DecidableEq

/-- A wire-form constraint: the gate equation `lhs = rhs` as two `EmittedExpr`. -/
structure EmittedConstraint where
  lhs : EmittedExpr
  rhs : EmittedExpr
  deriving Repr, DecidableEq

/-- A wire-form descriptor mirroring the relevant fields of Rust's `CircuitDescriptor`:
the AIR name, the trace width (number of distinct wires), and the constraint list. The
witness-vector layout is implicit (variable index = column index), exactly as in
`Circuit.encode`. -/
structure EmittedDescriptor where
  name        : String
  traceWidth  : Nat
  constraints : List EmittedConstraint
  deriving Repr, DecidableEq

/-! ## `emit` — the deterministic serializer. -/

/-- Serialize a `Circuit.Expr` to its wire form. Structure-preserving by construction. -/
def emitExpr : Expr → EmittedExpr
  | .var v     => .var v
  | .const c   => .const c
  | .add e₁ e₂ => .add (emitExpr e₁) (emitExpr e₂)
  | .mul e₁ e₂ => .mul (emitExpr e₁) (emitExpr e₂)

/-- Serialize a single `Constraint` to its wire form. -/
def emitConstraint (c : Constraint) : EmittedConstraint :=
  { lhs := emitExpr c.lhs, rhs := emitExpr c.rhs }

/-- The number of distinct wires the kernel circuit uses: the 6 named columns of
`Circuit.encode` (`vTotalPre … vChainOk`). This is the `trace_width` the Rust descriptor
must declare. -/
def kernelTraceWidth : Nat := 6

/-- **`emit`** — the deterministic serializer `ConstraintSystem → EmittedDescriptor`. The
name binds the wire form to a specific AIR identity (matching the Rust-native AIR name). -/
def emit (name : String) (width : Nat) (cs : ConstraintSystem) : EmittedDescriptor :=
  { name := name, traceWidth := width, constraints := cs.map emitConstraint }

/-! ## `decodeE` — the inverse (deserializer), used only to state/prove faithfulness. -/

/-- Deserialize a wire-form expression back to a `Circuit.Expr`. -/
def decodeExpr : EmittedExpr → Expr
  | .var v     => .var v
  | .const c   => .const c
  | .add e₁ e₂ => .add (decodeExpr e₁) (decodeExpr e₂)
  | .mul e₁ e₂ => .mul (decodeExpr e₁) (decodeExpr e₂)

/-- Deserialize a wire-form constraint. -/
def decodeConstraint (c : EmittedConstraint) : Constraint :=
  { lhs := decodeExpr c.lhs, rhs := decodeExpr c.rhs }

/-- Deserialize a whole emitted descriptor back to a `ConstraintSystem`. -/
def decodeE (d : EmittedDescriptor) : ConstraintSystem :=
  d.constraints.map decodeConstraint

/-! ## `satisfiedEmitted` — `satisfied` lifted to the emitted (decoded) form. -/

/-- Evaluate an emitted expression directly (so the wire form has a standalone denotation,
not only via decode). -/
def EmittedExpr.eval : EmittedExpr → Assignment → Int
  | .var v,     a => a v
  | .const c,   _ => c
  | .add e₁ e₂, a => e₁.eval a + e₂.eval a
  | .mul e₁ e₂, a => e₁.eval a * e₂.eval a

/-- An emitted constraint holds iff both decoded sides evaluate equal. -/
def EmittedConstraint.holds (c : EmittedConstraint) (a : Assignment) : Prop :=
  c.lhs.eval a = c.rhs.eval a

/-- The emitted descriptor is **satisfied** iff every emitted constraint holds — the wire
form's own notion of satisfaction. -/
def satisfiedEmitted (d : EmittedDescriptor) (a : Assignment) : Prop :=
  ∀ c ∈ d.constraints, c.holds a

/-! ## Round-trip + evaluation-agreement lemmas (the spine of faithfulness). -/

/-- `decodeExpr ∘ emitExpr = id`: emission then decode recovers the original expression. -/
theorem decodeExpr_emitExpr (e : Expr) : decodeExpr (emitExpr e) = e := by
  induction e with
  | var v => rfl
  | const c => rfl
  | add e₁ e₂ ih₁ ih₂ => simp [emitExpr, decodeExpr, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => simp [emitExpr, decodeExpr, ih₁, ih₂]

/-- The emitted expression's standalone `eval` agrees with the original `Expr.eval`: the
wire denotation is faithful pointwise. -/
theorem emitExpr_eval (e : Expr) (a : Assignment) :
    (emitExpr e).eval a = e.eval a := by
  induction e with
  | var v => rfl
  | const c => rfl
  | add e₁ e₂ ih₁ ih₂ => simp [emitExpr, EmittedExpr.eval, Expr.eval, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => simp [emitExpr, EmittedExpr.eval, Expr.eval, ih₁, ih₂]

/-- A single constraint and its emitted form hold on EXACTLY the same assignments. -/
theorem emitConstraint_holds (c : Constraint) (a : Assignment) :
    (emitConstraint c).holds a ↔ c.holds a := by
  unfold emitConstraint EmittedConstraint.holds Constraint.holds
  simp only [emitExpr_eval]

/-! ## `emit_faithful` — THE deliverable: the wire form denotes the same system. -/

/-- **`emit_faithful`.** Satisfying the emitted descriptor is EXACTLY satisfying the source
constraint system, for every assignment. So `emit` loses none of the semantics `Circuit.bridge`
proved: composing `emit_faithful` with `bridge` gives that satisfying the *wire form* of
`kernelCircuit` is `fullStepInv`. (`name`/`width` are wire metadata and do not affect
satisfaction; they carry the AIR identity the Rust fingerprint check binds.) -/
theorem emit_faithful (name : String) (width : Nat) (cs : ConstraintSystem) (a : Assignment) :
    satisfied cs a ↔ satisfiedEmitted (emit name width cs) a := by
  unfold satisfied satisfiedEmitted emit
  simp only [List.mem_map]
  constructor
  · rintro h c ⟨c₀, hc₀, rfl⟩
    exact (emitConstraint_holds c₀ a).mpr (h c₀ hc₀)
  · intro h c hc
    exact (emitConstraint_holds c a).mp (h (emitConstraint c) ⟨c, hc, rfl⟩)

/-- `decodeConstraint ∘ emitConstraint = id` on a single constraint. -/
theorem decodeConstraint_emitConstraint (c : Constraint) :
    decodeConstraint (emitConstraint c) = c := by
  unfold decodeConstraint emitConstraint
  simp only [decodeExpr_emitExpr]

/-- **`emit` is injective in the constraint payload** (the round trip recovers the source, so
distinct constraint systems serialize to distinct descriptors under a fixed name/width): no
two systems collide on the wire. -/
theorem decodeE_emit (name : String) (width : Nat) (cs : ConstraintSystem) :
    decodeE (emit name width cs) = cs := by
  unfold decodeE emit
  simp only [List.map_map]
  rw [show (decodeConstraint ∘ emitConstraint) = id from
        funext (fun c => decodeConstraint_emitConstraint c)]
  exact List.map_id cs

/-! ## The concrete kernel-circuit emission (the extraction target). -/

/-- The AIR identity string the wire form carries. The Rust decoder pins the native AIR to
this name so the fingerprint binding is name-aware. -/
def kernelAirName : String := "dregg-kernel-step-v1"

/-- **The emitted kernel circuit** — `kernelCircuit` serialized to the wire form. THIS is the
object that extracts to Rust: pure printable data, proved faithful by `emit_faithful`. -/
def emittedKernel : EmittedDescriptor :=
  emit kernelAirName kernelTraceWidth kernelCircuit

/-- **End-to-end faithfulness for the kernel circuit**: satisfying the EMITTED kernel circuit
is exactly the verified `fullStepInv` (composing `emit_faithful` with `Circuit.bridge`). The
wire form the Rust backend decodes carries the full §8 soundness∧completeness content. -/
theorem emittedKernel_bridge (s : Dregg2.Exec.ChainedState) (t : Dregg2.Exec.Turn)
    (s' : Dregg2.Exec.ChainedState) :
    satisfiedEmitted emittedKernel (encode s t s') ↔ Dregg2.Exec.fullStepInv s t s' := by
  unfold emittedKernel
  rw [← emit_faithful]
  exact bridge s t s'

/-! ## The canonical wire string (`#eval`-printable; the byte form Rust decodes).

A deterministic, minimal JSON renderer. The Rust decoder (`circuit_decode.rs`) parses this
exact grammar. Keeping the renderer in Lean (not a derived `ToJson`) makes the wire grammar
explicit and stable. -/

/-- Render an integer as a JSON number (no spaces). -/
private def jInt (n : Int) : String := toString n

/-- Render an emitted expression as JSON: `{"t":"var","v":N}` / `{"t":"const","v":N}` /
`{"t":"add"|"mul","l":…,"r":…}`. -/
def EmittedExpr.toJson : EmittedExpr → String
  | .var v     => "{\"t\":\"var\",\"v\":" ++ toString v ++ "}"
  | .const c   => "{\"t\":\"const\",\"v\":" ++ jInt c ++ "}"
  | .add l r   => "{\"t\":\"add\",\"l\":" ++ l.toJson ++ ",\"r\":" ++ r.toJson ++ "}"
  | .mul l r   => "{\"t\":\"mul\",\"l\":" ++ l.toJson ++ ",\"r\":" ++ r.toJson ++ "}"

/-- Render a constraint as JSON `{"lhs":…,"rhs":…}`. -/
def EmittedConstraint.toJson (c : EmittedConstraint) : String :=
  "{\"lhs\":" ++ c.lhs.toJson ++ ",\"rhs\":" ++ c.rhs.toJson ++ "}"

/-- Render a list of constraints as a JSON array. -/
private def constraintsToJson : List EmittedConstraint → String
  | []      => "[]"
  | [c]     => "[" ++ c.toJson ++ "]"
  | c :: cs => "[" ++ c.toJson ++ (cs.foldl (fun acc x => acc ++ "," ++ x.toJson) "") ++ "]"

/-- **`emitJson`** — the full canonical wire string for an emitted descriptor. This is what
`#eval` prints and the Rust decoder ingests. -/
def emitJson (d : EmittedDescriptor) : String :=
  "{\"name\":\"" ++ d.name ++ "\",\"trace_width\":" ++ toString d.traceWidth ++
  ",\"constraints\":" ++ constraintsToJson d.constraints ++ "}"

/-- The canonical wire string for the kernel circuit — copy this into the Rust golden. -/
def kernelWire : String := emitJson emittedKernel

-- Print the wire string + sanity facts. `#eval kernelWire` prints the bytes the Rust
-- decoder parses; the Rust differential pins this exact string as its golden input.
#eval kernelWire
#eval emittedKernel.constraints.length   -- 4 gates
#eval emittedKernel.traceWidth            -- 6 wires

/-! ## Axiom-hygiene pins (the §8 honesty tripwire). -/

#assert_axioms emit_faithful
#assert_axioms decodeE_emit
#assert_axioms emittedKernel_bridge

end Dregg2.Exec.CircuitEmit
