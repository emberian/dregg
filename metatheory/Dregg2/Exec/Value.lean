/-
# Dregg2.Exec.Value — the Preserves data substrate for dregg2 cells (`dregg2 §5`).

dregg1 models a cell's mutable state as **8 fixed `[u8;32]` slots** (`cell/src/state.rs`,
`STATE_SLOTS`) — a global-uniform-circuit artifact inherited from Mina, where heterogeneous
cells (`RateLimit`/`BoundDelta`/`CapabilityUniqueness`) strain against bit-positional slots.
dregg2 replaces this with a **content-addressed, name-keyed data-model value** (the Preserves
direction): cell-state is a typed *record* whose fields are NAMED, not bit-positioned (so
adding a field can never silently rebind another — the `EffectMask`/slot-fragility fix), and
whose identity is the hash of its canonical schema (the AIR-id, un-freezing the Urbit trap).

This module is the FOUNDATION for the rest of the executable kernel (`Program` = the
structure-map, the cell, the forest turn). The prize it sets up is a **circuit compiler over
records**: a `Schema` fixes a wire layout, so a record transition compiles to an arithmetic
constraint system. Very little ZK tooling works over *structured* records; the `flatten` /
`width` discipline below — `flatten_width`: a value flattens to a vector whose length is a
function of the SCHEMA alone — is exactly what makes an AIR over records well-defined.

## The two-register honesty (mirrors `Resource.lean`'s camera)
The `Value` model is FULL (arbitrarily nested records over the scalar/digest/symbol leaves).
The *circuit-compilable* fragment is the sub-fragment that flattens to a fixed-width field
vector. A malformed (non-conforming) value still flattens — the flattening is **type-directed**
and defaults absent/ill-typed fields to `0` — so the circuit *width* is a property of the
schema, never of the witness (`flatten_width`). The witness may be malformed; the wire count
cannot. (This is the data-tier shadow of `Resource.lean`'s "full camera, ZK-able sub-fragment".)

Pure, computable, `#eval`-able; Lean-core only (no Mathlib import) so it type-checks fast.
-/

namespace Dregg2.Exec

/-- A field element — the scalar a circuit wire carries. `Int` is the field stand-in (it
matches `Circuit.lean`'s `Assignment := Var → ℤ`), so a flattened value IS a circuit-witness
prefix. -/
abbrev FieldElem := Int

/-- A field name (record key). **Names, not bit positions** — the `dregg2 §5` fix. -/
abbrev FieldName := String

/-- **Schema field types** — the declared *shape* of (part of) a cell's state. A cell's
AIR-id is the hash of (the canonical encoding of) this. The three leaves are the
circuit-native scalars; `record` nests. (Bounded `vector`s / `set`s are a later extension;
nested records already make this genuinely "ZK over records".) -/
inductive Ty where
  /-- One field element (a balance, a counter, an amount). -/
  | scalar
  /-- A 32-byte hash / commitment / cell-reference — one wire in the field stand-in. -/
  | digest
  /-- An interned tag (a method id, an enum case) — one field element. -/
  | symbol
  /-- A nested, name-keyed sub-record. -/
  | record : List (FieldName × Ty) → Ty
  deriving Repr

/-- The top-level cell-state shape: an ordered list of named, typed fields. -/
abbrev Schema := List (FieldName × Ty)

/-- **A Preserves-style data value** — a cell's mutable state. Preserves `Double`s are
forbidden (`dregg2 §5`); `digest`/`symbol` carry as `Nat` (the canonical-encoding / interned
id). -/
inductive Value where
  | int    : Int → Value
  | dig    : Nat → Value
  | sym    : Nat → Value
  | record : List (FieldName × Value) → Value
  deriving Repr

instance : Inhabited Ty := ⟨.scalar⟩
instance : Inhabited Value := ⟨.int 0⟩

/-! ## `width` — the wire count a type occupies (the schema-determined circuit width). -/

mutual
/-- **`width t`** — how many field-element wires a value of type `t` flattens to. A function
of the TYPE alone; this is the circuit's fixed column count. -/
def width : Ty → Nat
  | .scalar   => 1
  | .digest   => 1
  | .symbol   => 1
  | .record fs => widthFields fs
def widthFields : List (FieldName × Ty) → Nat
  | []            => 0
  | (_, t) :: rest => width t + widthFields rest
end

/-! ## `conforms` — does a value match a schema's shape? (the well-formedness predicate). -/

mutual
/-- **`conforms v t`** — `v` has the shape `t`: leaves match their constructor, and for each
schema field the record carries a conforming value. (Open records: extra value-fields beyond
the schema are ignored — the schema is a lower bound on structure.) -/
def conforms : Value → Ty → Bool
  | .int _,    .scalar  => true
  | .dig _,    .digest  => true
  | .sym _,    .symbol  => true
  | .record vs, .record fs => conformsFields vs fs
  | _, _ => false
def conformsFields : List (FieldName × Value) → List (FieldName × Ty) → Bool
  | _,  []              => true
  | vs, (name, t) :: rest =>
      (match vs.find? (fun p => p.1 == name) with
       | some p => conforms p.2 t
       | none   => false)
      && conformsFields vs rest
end

/-! ## `flatten` — the type-directed flattening to a fixed-width field vector (the witness). -/

mutual
/-- **`flatten t v`** — lay `v` out as a field-element vector under the wire layout `t`
prescribes. **Type-directed**: it reads `v` where the shape matches and defaults to `0`
elsewhere, so its length is `width t` for *any* `v` (`flatten_width`). This is the circuit
witness: `flatten oldType old ++ flatten newType new` is exactly the wire assignment a
record-transition AIR ranges over. -/
def flatten : Ty → Value → List FieldElem
  | .scalar,    .int i  => [i]
  | .digest,    .dig d  => [(d : Int)]
  | .symbol,    .sym s  => [(s : Int)]
  | .record fs, .record vs => flattenFields fs vs
  -- Malformed/ill-typed witness ⇒ zeros of the schema-determined width (the wire count is a
  -- property of the schema, not the witness):
  | t, _ => List.replicate (width t) 0
def flattenFields : List (FieldName × Ty) → List (FieldName × Value) → List FieldElem
  | [],              _  => []
  | (name, t) :: rest, vs =>
      (match vs.find? (fun p => p.1 == name) with
       | some p => flatten t p.2
       | none   => List.replicate (width t) 0)
      ++ flattenFields rest vs
end

/-! ## `flatten_width` — the foundation lemma: width is a function of the SCHEMA alone. -/

mutual
/-- **`flatten_width` (PROVED)** — every value flattens to exactly `width t` field elements,
*regardless of whether it conforms*. This is what makes a record→circuit compiler well-defined:
the AIR's column count is fixed by the schema, and a malformed witness changes the *values* on
the wires (failing constraints) but never the *number* of wires. The circuit-compilable
fragment of the full `Value` model is exactly "the part with a schema to flatten against". -/
theorem flatten_width : ∀ (t : Ty) (v : Value), (flatten t v).length = width t
  | .scalar, v => by cases v <;> simp [flatten, width]
  | .digest, v => by cases v <;> simp [flatten, width]
  | .symbol, v => by cases v <;> simp [flatten, width]
  | .record fs, v => by
      cases v with
      | record vs => simpa only [flatten] using flattenFields_width fs vs
      | int _ => simp [flatten, width, List.length_replicate]
      | dig _ => simp [flatten, width, List.length_replicate]
      | sym _ => simp [flatten, width, List.length_replicate]
termination_by t _ => sizeOf t
theorem flattenFields_width : ∀ (fs : List (FieldName × Ty)) (vs : List (FieldName × Value)),
    (flattenFields fs vs).length = widthFields fs
  | [],                _  => rfl
  | (name, t) :: rest, vs => by
      simp only [flattenFields, widthFields, List.length_append]
      rw [flattenFields_width rest vs]
      cases h : vs.find? (fun p => p.1 == name) with
      | some p => simp only [flatten_width t p.2]
      | none   => simp only [List.length_replicate]
termination_by fs _ => sizeOf fs
end

/-! ## `fieldOffset` — where a named field's wires start (the circuit compiler's address map). -/

/-- **`fieldOffset schema name`** — the (wire offset, type) of a top-level field `name` in
the flattened vector, or `none` if absent. The record-circuit compiler uses this to place a
constraint's gates on the right wires: a constraint naming field `name` compiles to gates over
wires `[off, off + width ty)`. -/
def fieldOffset : Schema → FieldName → Option (Nat × Ty)
  | [],                _      => none
  | (name, t) :: rest, target =>
      if name == target then some (0, t)
      else match fieldOffset rest target with
           | some p => some (width t + p.1, p.2)
           | none   => none

/-- The offset of a named field never lands beyond the record's total width (a sanity bound
the circuit compiler relies on to stay in-bounds). PROVED. -/
theorem fieldOffset_lt_width : ∀ (schema : Schema) (name : FieldName) (off : Nat) (ty : Ty),
    fieldOffset schema name = some (off, ty) → off + width ty ≤ widthFields schema
  | [],                _,    _,   _,  h => by simp [fieldOffset] at h
  | (n, t) :: rest,    name, off, ty, h => by
      simp only [fieldOffset] at h
      by_cases hn : (n == name) = true
      · rw [if_pos hn] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [widthFields]; omega
      · rw [if_neg hn] at h
        cases hr : fieldOffset rest name with
        | none => rw [hr] at h; simp at h
        | some p =>
            rw [hr] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ih := fieldOffset_lt_width rest name p.1 p.2 hr
            simp only [widthFields]; omega

/-! ## It runs (`#eval`) — an account cell as a record. -/

/-- A simple account-cell schema: a balance, a nonce, and an owner reference. -/
def accountSchema : Schema :=
  [("balance", .scalar), ("nonce", .scalar), ("owner", .digest)]

/-- A conforming account value: 100 balance, nonce 0, owner-ref 42. -/
def acct0 : Value :=
  .record [("balance", .int 100), ("nonce", .int 0), ("owner", .dig 42)]

/-- A nested schema — an account that holds a sub-record `limits {daily, perTx}`. -/
def nestedSchema : Schema :=
  [("balance", .scalar),
   ("limits", .record [("daily", .scalar), ("perTx", .scalar)])]

def nested0 : Value :=
  .record [("balance", .int 100),
           ("limits", .record [("daily", .int 50), ("perTx", .int 10)])]

#eval width (.record accountSchema)              -- 3
#eval conforms acct0 (.record accountSchema)     -- true
#eval flatten (.record accountSchema) acct0      -- [100, 0, 42]
#eval fieldOffset accountSchema "nonce"          -- some (1, scalar)
#eval fieldOffset accountSchema "owner"          -- some (2, digest)

#eval width (.record nestedSchema)               -- 3  (1 + (1+1))
#eval conforms nested0 (.record nestedSchema)    -- true
#eval flatten (.record nestedSchema) nested0     -- [100, 50, 10]  (nested record inlined)

-- A malformed witness still flattens to the schema width (here 3), defaulting to 0:
#eval flatten (.record accountSchema) (.int 7)   -- [0, 0, 0]
#eval (flatten (.record accountSchema) (.int 7)).length = width (.record accountSchema)  -- true

end Dregg2.Exec
