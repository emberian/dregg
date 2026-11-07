/-
# A certified Gabbay matrix instance in the live descriptor IR-v2

This module connects the rational matrix semantics and its finite-field
projection certificate to the descriptor relation used by the running dregg
proof stack.  The compiled source schema is a three-entry graph of a unary
Skolem function.  Its two matrix rows are interpolated at the one-based nodes
`1,2,3`, and the source formula requires every output to equal its input plus
one.

The trace carries denominator-cleared coefficients for `2 * P(X)`.  For row
values `y1,y2,y3` those coefficients are

* `6*y1 - 6*y2 + 2*y3`,
* `-5*y1 + 8*y2 - 3*y3`,
* `y1 - 2*y2 + y3`.

Thus interpolation needs no witness-authored division and every evaluation
gate is an exact integer identity before reduction modulo BabyBear.

Acceptance is three LINEAR gates `output j - input j - 1`, one per declared
column, together with a 30-bit range tooth on each of the six entry columns.
It is deliberately *not* the sum of the three squared residuals.  A sum of
squares is not a faithful conjunction over BabyBear: `284861408 ^ 2 = -1`
there, so `1 ^ 2 + 284861408 ^ 2 + 0 ^ 2` vanishes in the field while every
individual equation fails (`Dregg2.Verify.DirectLogicAdversarialFalsifierV2`
carries that table as a live regression canary).  The old design compensated
with a Lean-side `LiveProjectionCertificate` asserting the integer numerator
never wrapped — a premise that was never serialized into the descriptor, so
the emitted bytes did not enforce what made them sound.  That premise is now
DELETED: the atom gates plus the six emitted 30-bit LOOKUPS discharge the
no-wrap condition on the wire, and the linear gates are also strictly cheaper
(zero nonlinear products instead of three).

Name the enforcing instrument exactly, because the field name misleads: the
descriptor's `ranges` field is `[]` BY CONSTRUCTION (`ranges := []`, see
`compileDescriptor`).  The v1 `VmRange` carrier is not what bounds anything
here.  Enforcement is six `VmConstraint2.lookup` constraints against the
declared `range` table id `2` of width `WIRE_BITS = 30` — one per entry
column — which is the graduated form the deployed assembly actually builds
(`{"t":"lookup","table":2,...}` in the emitted bytes).  Every claim below
that a bound is "on the wire" means those six lookups, never `ranges`.

The main theorem is an exact live relation, not an analogy: the constructed
IR-v2 trace satisfies the emitted descriptor iff the ordinary `Holds` semantics
satisfies the original bounded formula — and the soundness direction now needs
no side condition on the CLAIM, because the range lookups are part of the
descriptor.  It is still a statement about the constructed `traceOf table`,
which supplies the honest range table the lookups are read against; for the
prover-chosen-trace polarity see `StatementSatisfied` and the residual named
in `Dregg2.Verify.DirectLogicAdversarialFalsifierV2` §0.
The final examples construct the successor trace and refuse both a tampered
entry and the known unchecked modulus-five projection.

This is deliberately the largest faithful fixed-arity fragment established
here.  A symbolic compiler for arbitrary matrix length would additionally need
an emitted interpolation algorithm and certified denominator/no-wrap cost;
IR-v2 itself is fixed to BabyBear and cannot soundly select a witness-authored
modulus.
-/
import Dregg2.Metatheory.GabbayFiniteFieldProjection
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Metatheory.GabbayDescriptorIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmRange)
open GabbayMatrixSemantics
open GabbayFiniteFieldProjection

set_option autoImplicit false

/-! ## 1. Source tables and their ordinary semantics -/

/-- A concrete two-row, three-column graph table. -/
structure ThreeEntryTable where
  input : Fin 3 -> Int
  output : Fin 3 -> Int

/-- Turn the graph into the intrinsically sized matrix expected by the source
semantics. -/
def sourceMatrix (table : ThreeEntryTable) : IntMatrix 2 where
  length := 3
  length_pos := by decide
  cell row col := if row.1 = 0 then table.input col else table.output col

@[simp] theorem sourceMatrix_input (table : ThreeEntryTable) (j : Fin 3) :
    (sourceMatrix table).cell inputRow j = table.input j := by
  simp [sourceMatrix, inputRow]

@[simp] theorem sourceMatrix_output (table : ThreeEntryTable) (j : Fin 3) :
    (sourceMatrix table).cell outputRow j = table.output j := by
  simp [sourceMatrix, outputRow]

/-- The source valuation determined by a concrete table. -/
def sourceValuation (table : ThreeEntryTable) : Valuation skolemSignature
  | .table => sourceMatrix table

/-- Ordinary source truth is pointwise successor truth at the three declared
columns. -/
theorem holds_iff_entries (table : ThreeEntryTable) :
    Holds (sourceValuation table) 0 successorSkolemFormula <->
      forall j : Fin 3, table.output j = table.input j + 1 := by
  simp only [successorSkolemFormula, Holds]
  have hout (j : Fin (sourceValuation table SkolemSymbol.table).length) :=
    eval_lookup_index_at_node (sourceValuation table) (SkolemSymbol.table : skolemSignature.Symbol)
      outputRow j
  have hin (j : Fin (sourceValuation table SkolemSymbol.table).length) :=
    eval_lookup_index_at_node (sourceValuation table) (SkolemSymbol.table : skolemSignature.Symbol)
      inputRow j
  constructor
  · intro h j
    have hj := h j
    rw [hout j, evalTerm_add, hin j, evalTerm_rational] at hj
    exact_mod_cast hj
  · intro h j
    rw [hout j, evalTerm_add, hin j, evalTerm_rational]
    exact_mod_cast h j

/-- The RETIRED sum-of-squares acceptance numerator.  No emitted gate reads it
any more; it is kept only to state the field-cancellation counterexample that
retired it (`residualNumerator = 0` over the integers does imply the three
equations, but `≡ 0 [ZMOD 2013265921]` does not). -/
def residualNumerator (table : ThreeEntryTable) : Int :=
  (table.output 0 - table.input 0 - 1) ^ 2 +
  (table.output 1 - table.input 1 - 1) ^ 2 +
  (table.output 2 - table.input 2 - 1) ^ 2

/-! ## 1b. The wire-checked entry domain -/

/-- Width of the range tooth emitted on every entry column: 30 bits, the
deployed BabyBear range-table width.  `2 ^ 30 < 2013265921`, so a 30-bit
column is canonical and no entry difference can reach a nonzero multiple of
the modulus. -/
def WIRE_BITS : Nat := 30

theorem wire_bound_lt_modulus : (2 : Int) ^ WIRE_BITS < 2013265921 := by
  norm_num [WIRE_BITS]

/-- The emitted range tooth's denotation, spelled out (the defining namespace is
not opened wholesale here). -/
theorem rangeHolds_def (env : VmRowEnv) (w b : Nat) :
    Dregg2.Circuit.Emit.EffectVmEmit.VmRange.holds env ⟨w, b⟩ <->
      (0 <= env.loc w /\ env.loc w < 2 ^ b) := Iff.rfl

/-- The domain the emitted descriptor CHECKS: every claimed cell is a 30-bit
field element.  This is not a Lean-side side condition on the TABLE — it is
exactly what the descriptor's six emitted 30-bit LOOKUPS against range table
`2` assert on every row (NOT the `ranges` field, which is `[]` here), so
soundness DERIVES it instead of assuming it (contrast the deleted
`LiveProjectionCertificate`).

One premise does survive, one level down and one level up: a lookup only
bounds anything against an HONEST range table (`HonestRangeTable`, i.e.
`t.tf .range = rangeRows WIRE_BITS`), which is a property of the TRACE FAMILY
the carrier hands us, not of the descriptor bytes.  `traceOf` installs it by
construction, so every theorem about the constructed trace is unconditional;
`Satisfied2` does not enforce it for an arbitrary trace.  See the residual
named in `Dregg2.Verify.DirectLogicAdversarialFalsifierV2` §0. -/
def WireBoundedTable (table : ThreeEntryTable) : Prop :=
  (∀ j, 0 <= table.input j /\ table.input j < 2 ^ WIRE_BITS) /\
  (∀ j, 0 <= table.output j /\ table.output j < 2 ^ WIRE_BITS)

/-- The atom-gate no-wrap step, on the wire-checked domain: a BabyBear-zero
entry difference between two 30-bit columns is an exact integer zero. -/
theorem entry_eq_of_modEq_of_bounded {inp out : Int}
    (hi : 0 <= inp /\ inp < 2 ^ WIRE_BITS)
    (ho : 0 <= out /\ out < 2 ^ WIRE_BITS)
    (h : out - inp - 1 ≡ 0 [ZMOD 2013265921]) : out = inp + 1 := by
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  simp only [WIRE_BITS] at hi ho
  norm_num at hi ho
  omega

/-! ## 2. Denominator-cleared row interpolation -/

/-- Integral coefficients of `2 * P(X)` for the unique degree-below-three
interpolant through `y(1),y(2),y(3)`. -/
def twiceCoefficients (y : Fin 3 -> Int) : Fin 3 -> Int
  | 0 => 6 * y 0 - 6 * y 1 + 2 * y 2
  | 1 => -5 * y 0 + 8 * y 1 - 3 * y 2
  | 2 => y 0 - 2 * y 1 + y 2

/-- Evaluation of the cleared coefficient witness recovers twice the exact
entry at every interpolation node. -/
theorem twiceCoefficients_eval (y : Fin 3 -> Int) (j : Fin 3) :
    twiceCoefficients y 0 + twiceCoefficients y 1 * (j.1 + 1) +
        twiceCoefficients y 2 * (j.1 + 1) ^ 2 = 2 * y j := by
  fin_cases j <;> simp [twiceCoefficients] <;> ring

/-! ## 3. Concrete live descriptor -/

def inputCol (j : Fin 3) : Nat := j.1
def outputCol (j : Fin 3) : Nat := 3 + j.1
def inputCoeffCol (k : Fin 3) : Nat := 6 + k.1
def outputCoeffCol (k : Fin 3) : Nat := 9 + k.1
def TRACE_WIDTH : Nat := 12

def negW (x : WindowExpr) : WindowExpr := .mul (.const (-1)) x
def subW (x y : WindowExpr) : WindowExpr := .add x (negW y)
def scaleW (n : Int) (x : WindowExpr) : WindowExpr := .mul (.const n) x

/-- Evaluate a denominator-cleared quadratic coefficient row at one of the
three declared one-based nodes, then bind it to twice the entry column. -/
def interpolationBody (coeffCol : Fin 3 -> Nat) (entry : Nat)
    (node : Nat) : WindowExpr :=
  subW
    (.add (.add (.loc (coeffCol 0))
      (scaleW node (.loc (coeffCol 1))))
      (scaleW (node ^ 2) (.loc (coeffCol 2))))
    (scaleW 2 (.loc entry))

/-- One acceptance atom: the `j`-th successor equation as a LINEAR gate.  This
is the whole logical content of acceptance; there is no squared residual and no
numerator column, because a field sum of squares is not a conjunction. -/
def entryAtomBody (j : Fin 3) : WindowExpr :=
  subW (subW (.loc (outputCol j)) (.loc (inputCol j))) (.const 1)

def always (body : WindowExpr) : VmConstraint2 :=
  .windowGate { body := body, onTransition := false }

/-- Interpolation binding plus one linear acceptance atom per declared column.
Every gate is always-on, including the final row. -/
def gabbayConstraints : List VmConstraint2 :=
  [ always (interpolationBody inputCoeffCol (inputCol 0) 1)
  , always (interpolationBody inputCoeffCol (inputCol 1) 2)
  , always (interpolationBody inputCoeffCol (inputCol 2) 3)
  , always (interpolationBody outputCoeffCol (outputCol 0) 1)
  , always (interpolationBody outputCoeffCol (outputCol 1) 2)
  , always (interpolationBody outputCoeffCol (outputCol 2) 3)
  , always (entryAtomBody 0)
  , always (entryAtomBody 1)
  , always (entryAtomBody 2) ]

/-- The emitted no-wrap teeth, in the GRADUATED v2 form: a 30-bit range LOOKUP
on each of the six entry columns, against the declared shared range table.
These are the serialized form of what the retired `LiveProjectionCertificate`
merely asserted in Lean.

The graduated form is deliberate.  The v1 `ranges` carrier would also be
checked by `Satisfied2`, but the deployed assembly refuses a v2 descriptor
carrying it (`circuit/src/descriptor_ir2.rs` `check_descriptor2`: "v2 assembly
requires a GRADUATED descriptor"), so those bytes would enforce the bound only
in Lean.  A range lookup is realized for real: the assembly lowers it to a
byte-limb decomposition at the width PINNED by the committed table id and
refuses any row with `value >= 2^bits`. -/
def rangeLookup (col : Nat) : VmConstraint2 :=
  .lookup ⟨.range, [.var col]⟩

def entryRangeLookups : List VmConstraint2 :=
  [ rangeLookup (inputCol 0), rangeLookup (inputCol 1), rangeLookup (inputCol 2)
  , rangeLookup (outputCol 0), rangeLookup (outputCol 1)
  , rangeLookup (outputCol 2) ]

/-- The honest range table: the one relation a range lookup is a lookup INTO.
It is a condition on the witness's auxiliary tables, not on the claim, and the
deployed assembly discharges it by CONSTRUCTING the limb decomposition itself
rather than reading a prover-supplied table. -/
def HonestRangeTable (t : VmTrace) : Prop := t.tf .range = rangeRows WIRE_BITS

/-- The fixed-schema compiler target in the live v2 grammar. -/
def compileDescriptor : EffectVmDescriptor2 :=
  { name := "dregg-gabbay-three-entry-skolem-v2"
  , traceWidth := TRACE_WIDTH
  , piCount := 0
  , tables := [mainTableDef TRACE_WIDTH, rangeTableDef WIRE_BITS]
  , constraints := gabbayConstraints ++ entryRangeLookups
  , hashSites := []
  , ranges := [] }

theorem atom_constraint_mem (j : Fin 3) :
    always (entryAtomBody j) ∈ compileDescriptor.constraints := by
  fin_cases j <;> simp [compileDescriptor, gabbayConstraints]

theorem input_range_mem (j : Fin 3) :
    rangeLookup (inputCol j) ∈ compileDescriptor.constraints := by
  fin_cases j <;> simp [compileDescriptor, entryRangeLookups, rangeLookup]

theorem output_range_mem (j : Fin 3) :
    rangeLookup (outputCol j) ∈ compileDescriptor.constraints := by
  fin_cases j <;> simp [compileDescriptor, entryRangeLookups, rangeLookup]

/-! ## 4. Constructive trace -/

def rowOf (table : ThreeEntryTable) : Assignment
  | 0 => table.input 0
  | 1 => table.input 1
  | 2 => table.input 2
  | 3 => table.output 0
  | 4 => table.output 1
  | 5 => table.output 2
  | 6 => twiceCoefficients table.input 0
  | 7 => twiceCoefficients table.input 1
  | 8 => twiceCoefficients table.input 2
  | 9 => twiceCoefficients table.output 0
  | 10 => twiceCoefficients table.output 1
  | 11 => twiceCoefficients table.output 2
  | _ => 0

/-- The constructed trace's auxiliary tables: the honest range table at the
declared width, and nothing else. -/
def traceTables : TraceFamily
  | .range => rangeRows WIRE_BITS
  | _ => []

def traceOf (table : ThreeEntryTable) : VmTrace :=
  { rows := [rowOf table], pub := zeroAsg, tf := traceTables }

theorem traceOf_honest_range (table : ThreeEntryTable) :
    HonestRangeTable (traceOf table) := by
  simp only [HonestRangeTable, traceOf, traceTables]

@[simp] theorem traceOf_loc (table : ThreeEntryTable) :
    (envAt (traceOf table) 0).loc = rowOf table := by
  simp [envAt, traceOf]

@[simp] theorem rowOf_input (table : ThreeEntryTable) (j : Fin 3) :
    rowOf table (inputCol j) = table.input j := by
  fin_cases j <;> rfl

@[simp] theorem rowOf_output (table : ThreeEntryTable) (j : Fin 3) :
    rowOf table (outputCol j) = table.output j := by
  fin_cases j <;> rfl

@[simp] theorem rowOf_inputCoefficient (table : ThreeEntryTable) (k : Fin 3) :
    rowOf table (inputCoeffCol k) = twiceCoefficients table.input k := by
  fin_cases k <;> rfl

@[simp] theorem rowOf_outputCoefficient (table : ThreeEntryTable) (k : Fin 3) :
    rowOf table (outputCoeffCol k) = twiceCoefficients table.output k := by
  fin_cases k <;> rfl

theorem memLog_compileDescriptor (table : ThreeEntryTable) :
    memLog compileDescriptor (traceOf table) = [] := by
  simp [memLog, memOpsOf, compileDescriptor, gabbayConstraints,
    entryRangeLookups, rangeLookup, always]

theorem mapLog_compileDescriptor (table : ThreeEntryTable) :
    mapLog compileDescriptor (traceOf table) = [] := by
  simp [mapLog, mapOpsOf, compileDescriptor, gabbayConstraints,
    entryRangeLookups, rangeLookup, always]

/-- A wire-bounded input column really is a row of the honest range table. -/
theorem inputRangeLookup_holds (table : ThreeEntryTable)
    (hbound : WireBoundedTable table) (j : Fin 3) :
    Lookup.holdsAt (traceOf table).tf (envAt (traceOf table) 0)
      ⟨.range, [.var (inputCol j)]⟩ :=
  lookup_range_complete WIRE_BITS _ (traceOf_honest_range table) _ _
    (by simpa [rangeHolds_def, traceOf_loc] using hbound.1 j)

theorem outputRangeLookup_holds (table : ThreeEntryTable)
    (hbound : WireBoundedTable table) (j : Fin 3) :
    Lookup.holdsAt (traceOf table).tf (envAt (traceOf table) 0)
      ⟨.range, [.var (outputCol j)]⟩ :=
  lookup_range_complete WIRE_BITS _ (traceOf_honest_range table) _ _
    (by simpa [rangeHolds_def, traceOf_loc] using hbound.2 j)

/-- All non-acceptance gates of the constructed trace are exact integer
identities.  Consequently source truth constructs a full live `Satisfied2`
witness. -/
theorem trace_complete (hash : List Int -> Int) (table : ThreeEntryTable)
    (hbound : WireBoundedTable table)
    (hholds : Holds (sourceValuation table) 0 successorSkolemFormula) :
    Satisfied2 hash compileDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf table) := by
  have hentries := (holds_iff_entries table).1 hholds
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    have hi0 : i = 0 := by simp [traceOf] at hi; omega
    subst i
    simp only [compileDescriptor] at hc
    simp only [gabbayConstraints, entryRangeLookups, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      simp only [always, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
        Bool.false_eq_true, if_false]
    · change (interpolationBody inputCoeffCol (inputCol 0) 1).eval
          (envAt (traceOf table) 0) ≡ 0 [ZMOD 2013265921]
      simp [interpolationBody, subW, negW, scaleW, WindowExpr.eval,
        traceOf_loc, twiceCoefficients]
      ring_nf
      exact Int.ModEq.refl 0
    · change (interpolationBody inputCoeffCol (inputCol 1) 2).eval
          (envAt (traceOf table) 0) ≡ 0 [ZMOD 2013265921]
      simp [interpolationBody, subW, negW, scaleW, WindowExpr.eval,
        traceOf_loc, twiceCoefficients]
      ring_nf
      exact Int.ModEq.refl 0
    · change (interpolationBody inputCoeffCol (inputCol 2) 3).eval
          (envAt (traceOf table) 0) ≡ 0 [ZMOD 2013265921]
      simp [interpolationBody, subW, negW, scaleW, WindowExpr.eval,
        traceOf_loc, twiceCoefficients]
      ring_nf
      exact Int.ModEq.refl 0
    · change (interpolationBody outputCoeffCol (outputCol 0) 1).eval
          (envAt (traceOf table) 0) ≡ 0 [ZMOD 2013265921]
      simp [interpolationBody, subW, negW, scaleW, WindowExpr.eval,
        traceOf_loc, twiceCoefficients]
      ring_nf
      exact Int.ModEq.refl 0
    · change (interpolationBody outputCoeffCol (outputCol 1) 2).eval
          (envAt (traceOf table) 0) ≡ 0 [ZMOD 2013265921]
      simp [interpolationBody, subW, negW, scaleW, WindowExpr.eval,
        traceOf_loc, twiceCoefficients]
      ring_nf
      exact Int.ModEq.refl 0
    · change (interpolationBody outputCoeffCol (outputCol 2) 3).eval
          (envAt (traceOf table) 0) ≡ 0 [ZMOD 2013265921]
      simp [interpolationBody, subW, negW, scaleW, WindowExpr.eval,
        traceOf_loc, twiceCoefficients]
      ring_nf
      exact Int.ModEq.refl 0
    · change (entryAtomBody 0).eval (envAt (traceOf table) 0) ≡ 0
        [ZMOD 2013265921]
      simp [entryAtomBody, subW, negW, WindowExpr.eval, traceOf_loc,
        hentries 0]
    · change (entryAtomBody 1).eval (envAt (traceOf table) 0) ≡ 0
        [ZMOD 2013265921]
      simp [entryAtomBody, subW, negW, WindowExpr.eval, traceOf_loc,
        hentries 1]
    · change (entryAtomBody 2).eval (envAt (traceOf table) 0) ≡ 0
        [ZMOD 2013265921]
      simp [entryAtomBody, subW, negW, WindowExpr.eval, traceOf_loc,
        hentries 2]
    · exact inputRangeLookup_holds table hbound 0
    · exact inputRangeLookup_holds table hbound 1
    · exact inputRangeLookup_holds table hbound 2
    · exact outputRangeLookup_holds table hbound 0
    · exact outputRangeLookup_holds table hbound 1
    · exact outputRangeLookup_holds table hbound 2
  · intro i hi
    trivial
  · intro i hi r hr
    simp [compileDescriptor] at hr
  · intro op hop
    rw [memLog_compileDescriptor table] at hop
    cases hop
  · rw [memLog_compileDescriptor table]
    trivial
  · rw [memLog_compileDescriptor table]
    exact memCheck_nil _ _
  · rw [memLog_compileDescriptor table]
    rfl
  · rw [mapLog_compileDescriptor table]
    rfl

/-! ## 5. Certified soundness and the exact live relation -/

/-- Any accepting constructed trace satisfies each acceptance atom in BabyBear. -/
theorem accepting_trace_atom_modEq_zero {hash : List Int -> Int}
    {table : ThreeEntryTable} (j : Fin 3)
    (hsat : Satisfied2 hash compileDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf table)) :
    table.output j - table.input j - 1 ≡ 0 [ZMOD 2013265921] := by
  have hgate := hsat.rowConstraints 0 (by simp [traceOf])
    (always (entryAtomBody j)) (atom_constraint_mem j)
  simpa [always, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
    entryAtomBody, subW, negW, WindowExpr.eval, traceOf_loc, sub_eq_add_neg]
    using hgate

/-- The descriptor's own range teeth force the wire-checked domain: an
accepting trace's entries ARE 30-bit.  This is the fact that used to be the
unserialized `LiveProjectionCertificate` premise.  Here it is unconditional,
because the constructed trace carries the honest range table by construction. -/
theorem accepting_trace_wire_bounded {hash : List Int -> Int}
    {table : ThreeEntryTable}
    (hsat : Satisfied2 hash compileDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf table)) :
    WireBoundedTable table := by
  have hlen : (0 : Nat) < (traceOf table).rows.length := by simp [traceOf]
  constructor
  · intro j
    have h := hsat.rowConstraints 0 hlen _ (input_range_mem j)
    have hb := lookup_replaces_range WIRE_BITS _ (traceOf_honest_range table)
      _ _ h
    simpa [rangeHolds_def, traceOf_loc] using hb
  · intro j
    have h := hsat.rowConstraints 0 hlen _ (output_range_mem j)
    have hb := lookup_replaces_range WIRE_BITS _ (traceOf_honest_range table)
      _ _ h
    simpa [rangeHolds_def, traceOf_loc] using hb

/-- **Certified soundness of the live acceptance gates, with no side condition
on the claimed table.**  Both halves of the old `LiveProjectionCertificate` are
now discharged by the descriptor itself: the six emitted 30-bit lookups bound
the entries and the linear atoms carry acceptance, so acceptance proves the
source formula with `WireBoundedTable` DERIVED rather than assumed.

Read the quantifier exactly.  This is not a statement about an arbitrary
accepting trace: it quantifies over `traceOf table`, the CONSTRUCTED trace for
`table`, and it is what lets the constructed trace discharge
`HonestRangeTable` by construction (via `accepting_trace_wire_bounded`).  The
statement-level, prover-chosen-trace polarity lives in
`GabbayDescriptorIR2PublicBinding.statement_sound`, which quantifies over any
`trace` but carries `HonestRangeTable trace` in `StatementSatisfied` as an
explicit premise — see the residual named in
`Dregg2.Verify.DirectLogicAdversarialFalsifierV2` §0. -/
theorem trace_sound (hash : List Int -> Int) (table : ThreeEntryTable)
    (hsat : Satisfied2 hash compileDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf table)) :
    Holds (sourceValuation table) 0 successorSkolemFormula := by
  have hbound := accepting_trace_wire_bounded hsat
  rw [holds_iff_entries]
  intro j
  exact entry_eq_of_modEq_of_bounded (hbound.1 j) (hbound.2 j)
    (accepting_trace_atom_modEq_zero j hsat)

/-- **Exact live compiler theorem.**  On the wire-checked 30-bit domain the
constructive IR-v2 trace accepts iff the ordinary bounded matrix formula holds.
The bound is a premise only for COMPLETENESS (it names which statements the
descriptor can express); soundness needs it nowhere, because the descriptor
checks it. -/
theorem trace_satisfied_iff_holds (hash : List Int -> Int)
    (table : ThreeEntryTable) (hbound : WireBoundedTable table) :
    Satisfied2 hash compileDescriptor (fun _ => 0)
        (fun _ => ((0 : Int), 0)) [] (traceOf table) <->
      Holds (sourceValuation table) 0 successorSkolemFormula := by
  exact ⟨trace_sound hash table, trace_complete hash table hbound⟩

/-! ## 6. Successor witness and refusal cases -/

def successorEntries : ThreeEntryTable where
  input j := j.1
  output j := j.1 + 1

theorem successorEntries_cell (row : Fin 2) (col : Fin 3) :
    (sourceMatrix successorEntries).cell row col =
      successorTable.cell row col := by
  fin_cases row <;> fin_cases col <;> rfl

theorem successorEntries_holds :
    Holds (sourceValuation successorEntries) 0 successorSkolemFormula := by
  rw [holds_iff_entries]
  intro j
  rfl

theorem successorEntries_wireBounded : WireBoundedTable successorEntries := by
  constructor <;> intro j <;> fin_cases j <;>
    norm_num [successorEntries, WIRE_BITS]

/-- Constructive live witness for the canonical successor table. -/
theorem successor_trace_satisfies (hash : List Int -> Int) :
    Satisfied2 hash compileDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf successorEntries) :=
  trace_complete hash successorEntries successorEntries_wireBounded
    successorEntries_holds

/-- One altered output entry. -/
def tamperedEntries : ThreeEntryTable where
  input
    | 0 => 0
    | 1 => 1
    | 2 => 2
  output
    | 0 => 2
    | 1 => 2
    | 2 => 3

theorem tamperedEntries_not_holds :
    ¬ Holds (sourceValuation tamperedEntries) 0 successorSkolemFormula := by
  rw [holds_iff_entries]
  intro h
  have h0 := h 0
  norm_num [tamperedEntries] at h0

theorem tamperedEntries_wireBounded : WireBoundedTable tamperedEntries := by
  constructor <;> intro j <;> fin_cases j <;>
    norm_num [tamperedEntries, WIRE_BITS]

/-- The live relation refuses the one-cell tamper — with no side condition. -/
theorem tampered_trace_refused (hash : List Int -> Int) :
    ¬ Satisfied2 hash compileDescriptor (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (traceOf tamperedEntries) := by
  intro hsat
  exact tamperedEntries_not_holds (trace_sound hash tamperedEntries hsat)

/-- The unchecked modulus-five counterexample cannot enter this compiler: its
projection certificate is uninhabited.  Live IR-v2 is BabyBear-fixed. -/
theorem bad_prime_projection_refused :
    ¬ FormulaProjectionCertificate successorValuation 0 badPrimeFormula 5 :=
  badPrime_certificate_rejected

/-- The bad modulus is not the live descriptor field. -/
theorem modulus_five_is_not_live : (5 : Nat) ≠ 2013265921 := by decide

/-! ## 7. Exact wire bytes

The PRIVATE descriptor's bytes are pinned here, exactly as the public variant's
are in `GabbayDescriptorIR2PublicBinding`.  Without this pin the six range teeth
that carry the no-wrap condition could be dropped from `entryRangeLookups` and
nothing byte-level would notice: the `constraints.length = 15` count in
`GabbayDescriptorIR2PublicBoundary` sees HOW MANY constraints there are, not
WHICH.  The pinned string carries `"sem":"range","bits":30` on table 2 and six
`{"t":"lookup","table":2,...}` entries over columns 0-5, so the width and the
teeth are both proof-visible wire facts. -/
def compileDescriptorBytes : String := emitVmJson2 compileDescriptor

#guard compileDescriptorBytes ==
  "{\"name\":\"dregg-gabbay-three-entry-skolem-v2\",\"ir\":2,\"trace_width\":12,\"public_input_count\":0,\"challenges\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":12,\"sem\":\"main\"},{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":30}],\"constraints\":[{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"loc\",\"c\":7}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"loc\",\"c\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"loc\",\"c\":0}}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"loc\",\"c\":7}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"loc\",\"c\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"loc\",\"c\":1}}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"loc\",\"c\":7}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":9},\"r\":{\"t\":\"loc\",\"c\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"loc\",\"c\":2}}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"loc\",\"c\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"loc\",\"c\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"loc\",\"c\":3}}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"loc\",\"c\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"loc\",\"c\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"loc\",\"c\":4}}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"loc\",\"c\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":9},\"r\":{\"t\":\"loc\",\"c\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"loc\",\"c\":5}}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"const\",\"v\":1}}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":0}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":1}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":2}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":3}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":4}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":5}]}],\"hash_sites\":[],\"ranges\":[]}"

#assert_all_clean [sourceMatrix_input, sourceMatrix_output, holds_iff_entries,
  wire_bound_lt_modulus, entry_eq_of_modEq_of_bounded,
  twiceCoefficients_eval, atom_constraint_mem, input_range_mem,
  output_range_mem, traceOf_honest_range, inputRangeLookup_holds,
  outputRangeLookup_holds, traceOf_loc, rowOf_input,
  rowOf_output, rowOf_inputCoefficient, rowOf_outputCoefficient,
  memLog_compileDescriptor, mapLog_compileDescriptor, trace_complete,
  accepting_trace_atom_modEq_zero, accepting_trace_wire_bounded,
  trace_sound, trace_satisfied_iff_holds,
  successorEntries_cell, successorEntries_holds, successorEntries_wireBounded,
  successor_trace_satisfies, tamperedEntries_not_holds,
  tamperedEntries_wireBounded,
  tampered_trace_refused, bad_prime_projection_refused,
  modulus_five_is_not_live]

end Dregg2.Metatheory.GabbayDescriptorIR2
