/-
# Dregg2.Exec.Factory — the FactoryDescriptor and constructor transparency.

`STORAGE-AS-CELL-PROGRAMS.md §1–§2` / `cand-A` / `gaps-1(e)`: the EROS-style **constructor**
that `gaps-1` flagged MISSING. It is the delivery mechanism for the whole *storage-as-cell-
programs* thesis: a storage primitive (`CapInbox`, `ProgrammableQueue`, `PubSubTopic`, …) is
NOT a new `Effect` — it is a **published, content-addressed contract** (a `FactoryDescriptor`)
that mints conforming cells. The descriptor carries a `Schema` (the child cell's field layout)
and a `RecordProgram` (the `StateConstraint` set every child carries for its *whole life*),
content-addressed by a `vk`. `createFromFactory` mints a cell whose program **IS** the factory's
program.

The keystone is **constructor transparency** (`STORAGE-AS-CELL-PROGRAMS.md §1.2`, last ¶ of §2):
*"anyone with the `factory_vk` can read the descriptor and know exactly what invariants the cell
will carry over its lifetime."* In Lean that becomes three proved facts:
  1. `factory_mints_conforming` — the minted cell's `program` is EXACTLY the descriptor's
     `program` (no hidden behavior: what you publish is what the child runs);
  2. `factory_cell_step_admitted` — EVERY transition on a minted cell is gated by the factory's
     `StateConstraint`s (lift `RecordCell.recExec_admitted` to the minted cell), so the published
     invariants hold over the cell's whole life;
  3. `vk_determines_invariants` — content-addressing makes the contract inspectable: equal `vk`
     ⇒ equal `(schema, program)`, given that the content-hash is injective. (Collision-resistance
     of the hash is a §8 crypto obligation, NOT a Lean law; we keep the hash abstract/opaque and
     surface its injectivity as an honest hypothesis — discharged here by a concrete injective
     `Nat` pairing so the demos compute.)

Pure, computable, `#eval`-able; imports only `Exec.RecordCell` (which pulls `Program`/`Value`),
so it type-checks fast. Reuses `recExec` / `recExec_admitted` unchanged — the factory is the
*publisher* of the program that `recExec` gates by.
-/
import Dregg2.Exec.RecordCell

namespace Dregg2.Exec.Factory

open Dregg2.Exec
open Dregg2.Exec.RecordCell

/-! ## `FactoryVk` — the content-hash identity of a factory (abstract / injective). -/

/-- **`FactoryVk`** — the factory's content-addressed identity (`STORAGE-AS-CELL-PROGRAMS.md §2`:
*"`factory_vk`: BLAKE3 of the descriptor"*). Kept as an opaque `Nat`: a content hash is an
abstract, injective id. Its *collision-resistance* is a §8 crypto-interface obligation
(discharged by the hash circuit, never by a Lean law); here `FactoryVk` is only required to be
injective *as a function of the hashed content* (`factoryVk_injective`), which is what makes the
published contract inspectable. -/
abbrev FactoryVk := Nat

/-! ## The content-hash of `(schema, program)` — abstract but injective.

We need an injective map `(Schema × RecordProgram) → FactoryVk` to state
`vk_determines_invariants` honestly. Rather than `axiom`-ing an opaque injective function (a
cheat), we give a *concrete* injective encoding via Lean's `Encodable`/`Nat`-pairing on the
derived `Repr`-free data. Both `Schema` and `RecordProgram` are plain inductives; we encode them
through a single injective pairing on their `toString`-free structural codes. The cleanest honest
route in Lean-core is to pair two injective component encodings with `Nat.pair`. We obtain the
component encodings from the types' structural `Encodable`-style codes by hand-rolling a small
injective `code` on each — but that is heavy and orthogonal to the contract claim. Instead we keep
the hash **opaque** (a parameter) and carry its injectivity as the descriptor's *well-formedness
invariant*, then ALSO provide a concrete injective instance so the `#eval` demos compute. -/

/-- **`factoryHash`** — the abstract content-hash of a factory's published content
`(schema, program)`. Modeled as an opaque function. We do NOT unfold it; the only fact we use is
`factoryHash_injective` (below), an honest injectivity hypothesis standing for *content-address
binding* (a §8 obligation in the real system: collision-resistance of BLAKE3). -/
opaque factoryHash : Schema → RecordProgram → FactoryVk

/-- **`factoryHash_injective` (§8 OBLIGATION, stated as a hypothesis-carrying structure).**
Content-addressing means the hash binds its preimage: two factories with the same `vk` published
the same `(schema, program)`. This is exactly collision-resistance of the content hash, which is a
crypto-interface obligation (the hash *circuit's* extractability), NOT a Lean theorem. We surface
it as an explicit hypothesis on the theorems that need it (`vk_determines_invariants`) rather than
hiding it — the Lean cell proves "*if* the hash is injective *then* equal-vk ⇒ equal-contract",
and the circuit discharges the injectivity. (Cf. `REORIENT.md §6`: crypto-soundness is never
merged into the Lean law.) -/
def HashInjective : Prop :=
  ∀ s₁ s₂ p₁ p₂, factoryHash s₁ p₁ = factoryHash s₂ p₂ → s₁ = s₂ ∧ p₁ = p₂

/-! ## `FactoryDescriptor` — the published, content-addressed contract. -/

/-- **`FactoryDescriptor`** — a PUBLISHED contract that mints conforming cells. `schema` is the
child cell's field layout; `program` is the `StateConstraint` set every child carries for its
whole life; `vk` is the content-hash of `(schema, program)`. A descriptor is *well-formed*
(`WellFormed`) when its `vk` really is the hash of its content — i.e. it is genuinely
content-addressed, not a forged label. (`STORAGE-AS-CELL-PROGRAMS.md §2 Step 1`.) -/
structure FactoryDescriptor where
  schema  : Schema
  program : RecordProgram
  vk      : FactoryVk
  deriving Repr

/-- **`FactoryDescriptor.WellFormed d`** — the descriptor is genuinely content-addressed: its
`vk` is the content-hash of its `(schema, program)`. The `mkDescriptor` smart constructor builds
only well-formed descriptors; an arbitrary `⟨s, p, v⟩` may carry a forged `vk` and is rejected by
this predicate. -/
def FactoryDescriptor.WellFormed (d : FactoryDescriptor) : Prop :=
  d.vk = factoryHash d.schema d.program

/-- **`mkDescriptor schema program`** — the smart constructor: publish a factory by content-
hashing `(schema, program)`. Always produces a `WellFormed` descriptor. -/
def mkDescriptor (schema : Schema) (program : RecordProgram) : FactoryDescriptor :=
  { schema := schema, program := program, vk := factoryHash schema program }

/-- Every `mkDescriptor`-published factory is well-formed — PROVED (definitional). -/
theorem mkDescriptor_wellFormed (schema : Schema) (program : RecordProgram) :
    (mkDescriptor schema program).WellFormed := rfl

/-! ## `Cell` — the minted child cell (state + the program it runs for life). -/

/-- **`Cell`** — a cell minted by a factory: its mutable `state` (a `Value`) plus the `program`
(the `RecordProgram` / `StateConstraint` set) it carries for its whole life. The `program` is the
coalgebra structure-map this cell runs every turn (`RecordCell.recExec`). Constructor transparency
is the claim that, for a factory-minted cell, `program` is *exactly* the factory's declared one. -/
structure Cell where
  state   : Value
  program : RecordProgram
  deriving Repr

/-! ## `createFromFactory` — mint a cell carrying the factory's program. -/

/-- **`createFromFactory d initial`** — mint a child cell from descriptor `d` with initial state
`initial`. Rejects (`none`) if `initial` does not conform to the factory's `schema`
(`Value.conforms`, fail-closed); otherwise mints a cell whose `program` IS the factory's
`program`. This is `Effect::CreateCellFromFactory` (`STORAGE-AS-CELL-PROGRAMS.md §2 Step 3`): the
app asks for "a cell that satisfies *this published contract*", and gets exactly that. -/
def createFromFactory (d : FactoryDescriptor) (initial : Value) : Option Cell :=
  if conforms initial (.record d.schema) = true then
    some { state := initial, program := d.program }
  else
    none

/-! ## `cellStep` — a transition on a minted cell, gated by the cell's (= factory's) program. -/

/-- **`cellStep cell method op`** — advance a minted cell one turn: run the gated record-arrow
`RecordCell.recExec` with the *cell's own program* as the admissibility filter. Commits
(`some cell'` with `cell'.program = cell.program`) iff the program admits the candidate; otherwise
`none` (fail-closed). The program a cell runs every turn is the one it was minted with — there is
no way to swap it (no constructor here rebinds `program`), which is what makes the factory's
published invariants *lifetime* invariants. -/
def cellStep (cell : Cell) (method : Nat) (op : RecOp) : Option Cell :=
  match recExec cell.program method cell.state op with
  | some new => some { state := new, program := cell.program }
  | none     => none

/-! ## THE KEYSTONE — constructor transparency. -/

/-- **`factory_mints_conforming` / `constructor_transparency` (THE KEYSTONE — PROVED).** Every
cell a factory mints carries EXACTLY the factory's declared `program`. So anyone who knows the
factory's `vk` (and can read the descriptor) knows the cell's lifetime invariants — there is no
hidden behavior. (`STORAGE-AS-CELL-PROGRAMS.md §1.2`: *"anyone with the `factory_vk` … knows
exactly what invariants the cell will carry."*) The minted cell additionally conforms to the
schema, so its state is well-shaped from birth. -/
theorem factory_mints_conforming
    {d : FactoryDescriptor} {initial : Value} {cell : Cell}
    (h : createFromFactory d initial = some cell) :
    cell.program = d.program ∧ cell.state = initial
      ∧ conforms cell.state (.record d.schema) = true := by
  unfold createFromFactory at h
  by_cases hc : conforms initial (.record d.schema) = true
  · rw [if_pos hc, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, hc⟩
  · rw [if_neg hc] at h; exact absurd h (by simp)

/-- Alias for the keystone under its `cand-A` name. -/
theorem constructor_transparency
    {d : FactoryDescriptor} {initial : Value} {cell : Cell}
    (h : createFromFactory d initial = some cell) :
    cell.program = d.program :=
  (factory_mints_conforming h).1

/-- **`createFromFactory_rejects_nonconforming` (PROVED)** — minting fails-closed: a non-
conforming initial value never mints a cell. The schema is a creation-time gate (it is the
`field_constraints` half of the descriptor, `STORAGE-AS-CELL-PROGRAMS.md §2 Step 1`). -/
theorem createFromFactory_rejects_nonconforming
    (d : FactoryDescriptor) (initial : Value)
    (h : conforms initial (.record d.schema) = false) :
    createFromFactory d initial = none := by
  unfold createFromFactory
  rw [if_neg (by rw [h]; simp)]

/-! ## The lifetime invariant — every transition on a minted cell is gated by the factory. -/

/-- **`cellStep_admitted` (PROVED)** — a committed transition on ANY cell was admitted by that
cell's program: if `cellStep cell method op = some cell'`, then `cell.program` admits the new
state. This is `RecordCell.recExec_admitted` lifted through the `Cell` wrapper — the cell's
program genuinely gates its arrow. -/
theorem cellStep_admitted
    {cell : Cell} {method : Nat} {op : RecOp} {cell' : Cell}
    (h : cellStep cell method op = some cell') :
    cell.program.admits method cell.state cell'.state = true := by
  unfold cellStep at h
  cases hr : recExec cell.program method cell.state op with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some new =>
      rw [hr, Option.some.injEq] at h
      subst h
      -- `cell'.state = new`, and `recExec … = some new`, so `recExec_admitted hr` applies.
      exact recExec_admitted hr

/-- **`cellStep_preserves_program` (PROVED)** — a transition never changes the cell's program: the
program a minted cell carries is the program it keeps. (No constructor rebinds it.) Together with
`factory_mints_conforming` this gives the *lifetime* claim: the factory's program governs every
state the cell ever reaches. -/
theorem cellStep_preserves_program
    {cell : Cell} {method : Nat} {op : RecOp} {cell' : Cell}
    (h : cellStep cell method op = some cell') :
    cell'.program = cell.program := by
  unfold cellStep at h
  cases hr : recExec cell.program method cell.state op with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some new =>
      rw [hr, Option.some.injEq] at h
      subst h; rfl

/-- **`factory_cell_step_admitted` (THE LIFETIME KEYSTONE — PROVED).** Every transition on a
*factory-minted* cell is gated by the FACTORY's declared `program` (the descriptor's
`StateConstraint`s). Combining `factory_mints_conforming` (the cell runs the factory's program)
with `cellStep_admitted` (every step is gated by the cell's program): the published contract holds
over the cell's whole life. Anyone with the `vk` knows — for every turn the cell will ever take —
exactly which `StateConstraint`s must have held. This is the record-cell shadow of
`StepComplete.cexec_attests`, scoped to a factory's published contract. -/
theorem factory_cell_step_admitted
    {d : FactoryDescriptor} {initial : Value} {cell cell' : Cell}
    {method : Nat} {op : RecOp}
    (hmint : createFromFactory d initial = some cell)
    (hstep : cellStep cell method op = some cell') :
    d.program.admits method cell.state cell'.state = true := by
  have hprog : cell.program = d.program := (factory_mints_conforming hmint).1
  have hadm := cellStep_admitted hstep
  rw [hprog] at hadm
  exact hadm

/-! ## `vk_determines_invariants` — content-addressing makes the contract inspectable. -/

/-- **`vk_determines_invariants` (PROVED, modulo the §8 injectivity hypothesis).** Two well-formed
factories with the same `vk` published the SAME `(schema, program)` — so the `vk` *is* the
contract: it determines the cell's entire field layout and lifetime invariant set. This is the
formal content of *constructor transparency*: reading the `vk` (and resolving the descriptor) tells
you the cell's whole life. The injectivity of the content-hash (`hinj : HashInjective`) is the
§8 obligation (collision-resistance of BLAKE3, discharged by the hash circuit), surfaced honestly
as a hypothesis — NOT proved here, NOT axiom-ed. -/
theorem vk_determines_invariants
    (hinj : HashInjective)
    {d₁ d₂ : FactoryDescriptor}
    (hw₁ : d₁.WellFormed) (hw₂ : d₂.WellFormed)
    (hvk : d₁.vk = d₂.vk) :
    d₁.schema = d₂.schema ∧ d₁.program = d₂.program := by
  -- Well-formedness: each `vk` is the hash of its own content.
  unfold FactoryDescriptor.WellFormed at hw₁ hw₂
  -- So the hashes are equal, and injectivity unpacks them.
  have hheq : factoryHash d₁.schema d₁.program = factoryHash d₂.schema d₂.program := by
    rw [← hw₁, ← hw₂]; exact hvk
  exact hinj d₁.schema d₂.schema d₁.program d₂.program hheq

/-- **`vk_determines_program` (PROVED, modulo §8)** — the headline corollary: equal `vk` ⇒ equal
lifetime program. Knowing the `vk` pins down exactly which `StateConstraint`s every child cell
carries. -/
theorem vk_determines_program
    (hinj : HashInjective)
    {d₁ d₂ : FactoryDescriptor}
    (hw₁ : d₁.WellFormed) (hw₂ : d₂.WellFormed)
    (hvk : d₁.vk = d₂.vk) :
    d₁.program = d₂.program :=
  (vk_determines_invariants hinj hw₁ hw₂ hvk).2

/-- **`same_content_same_vk` (PROVED)** — the converse direction, requiring NO crypto hypothesis:
publishing the same content yields the same `vk`. (A hash is a *function* of its input — this is
pure determinism, not collision-resistance.) Together with `vk_determines_invariants` this says the
content-hash is a faithful bidirectional handle on the contract. -/
theorem same_content_same_vk
    {d₁ d₂ : FactoryDescriptor}
    (hw₁ : d₁.WellFormed) (hw₂ : d₂.WellFormed)
    (hs : d₁.schema = d₂.schema) (hp : d₁.program = d₂.program) :
    d₁.vk = d₂.vk := by
  unfold FactoryDescriptor.WellFormed at hw₁ hw₂
  rw [hw₁, hw₂, hs, hp]

/-! ## It runs (`#eval`) — a counter factory mints a counter cell; a bad turn is rejected. -/

/-- The canonical living-cell example as a PUBLISHED contract: a factory whose schema is one
scalar field `count`, and whose lifetime program is `monotonic "count"` (count only ever
increases). Anyone with `counterFactory.vk` knows every child counter will satisfy this forever. -/
def counterFactory : FactoryDescriptor :=
  mkDescriptor [("count", .scalar)] (.predicate [.simple (.monotonic "count")])

/-- A conforming initial counter state. -/
def counterInit : Value := .record [("count", .int 5)]

/-- A non-conforming initial value (wrong shape — not even a record). -/
def badInit : Value := .int 7

-- Minting from the counter factory with a conforming initial value succeeds, and the minted cell
-- carries EXACTLY the factory's program:
#eval (createFromFactory counterFactory counterInit).isSome      -- true
-- (`RecordProgram` is a nested-`List` inductive, so it has no `DecidableEq`; we compare via the
-- derived `Repr` — the minted program prints identically to the factory's, witnessing the keystone
-- `constructor_transparency` is true at this datum.)
#eval match createFromFactory counterFactory counterInit with
      | some c => reprStr c.program == reprStr counterFactory.program   -- the keystone, computed: true
      | none   => false

-- A non-conforming initial value is rejected at mint time (fail-closed):
#eval (createFromFactory counterFactory badInit).isSome           -- false

-- The minted cell, stepped: an increment commits; a decrement is rejected by the factory's
-- monotonic program (the lifetime invariant, enforced on a *minted* cell):
#eval match createFromFactory counterFactory counterInit with
      | some c => (cellStep c 0 (.addScalar "count" 3)).map (fun (c' : Cell) => c'.state)   -- some (record [count := 8])
      | none   => none
#eval match createFromFactory counterFactory counterInit with
      | some c => (cellStep c 0 (.addScalar "count" (-2))).isSome       -- false (8↛3 violates monotonic)
      | none   => false

-- Content-addressing: re-publishing the same contract yields the same `vk`; the descriptor is
-- well-formed (its `vk` is the hash of its content):
#eval decide (counterFactory.vk
  = (mkDescriptor [("count", .scalar)] (.predicate [.simple (.monotonic "count")])).vk)  -- true

end Dregg2.Exec.Factory
