/- Full-width ordered-route AIR. Arity 13 is padded to admitted arity 16;
all eight predecessor and output lanes participate. The base descriptor remains policy identity. -/
import Dregg2.Circuit.Emit.DfaRoutingTableEmit
namespace Dregg2.Circuit.Emit.RouteChain8
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow VmConstraint)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit (envAt_loc envAt_nxt)
set_option autoImplicit false
structure Config where
  baseWidth : Nat
  basePiCount : Nat
  current : Nat
  symbol : Nat
  next : Nat
  domain : Nat
  seed : Option Nat
  deriving Repr
def lanes : List Nat := [0,1,2,3,4,5,6,7]
def acc (c : Config) (j : Nat) : Nat := c.baseWidth + j
def out (c : Config) (j : Nat) : Nat := c.baseWidth + 8 + j
def index (c : Config) : Nat := c.baseWidth + 16
def routePi (c : Config) (j : Nat) : Nat := c.basePiCount + j
def lengthPi (c : Config) : Nat := c.basePiCount + 8
def inputs (c : Config) : List EmittedExpr :=
  [.const c.domain, .var (index c), .var c.current, .var c.symbol, .var c.next,
   .var (acc c 0), .var (acc c 1), .var (acc c 2), .var (acc c 3),
   .var (acc c 4), .var (acc c 5), .var (acc c 6), .var (acc c 7),
   .const 0, .const 0, .const 0]
def chip (c : Config) : VmConstraint2 :=
  .lookup ⟨.poseidon2, chipLookupTupleN (inputs c) (lanes.map (out c))⟩
def copy (c : Config) (j : Nat) : VmConstraint2 :=
  .windowGate ⟨.add (.nxt (acc c j)) (.mul (.const (-1)) (.loc (out c j))), true⟩
def seedPin (c : Config) (j : Nat) : VmConstraint2 :=
  match c.seed with
  | none => .base (.boundary .first (.var (acc c j)))
  | some k => .base (.piBinding .first (acc c j) (k+j))
def outputPin (c : Config) (j : Nat) : VmConstraint2 :=
  .base (.piBinding .last (out c j) (routePi c j))
def indexFirst (c : Config) : VmConstraint2 :=
  .base (.boundary .first (.add (.var (index c)) (.const (-1))))
def indexStep (c : Config) : VmConstraint2 :=
  .windowGate ⟨.add (.add (.nxt (index c)) (.mul (.const (-1)) (.loc (index c))))
    (.const (-1)), true⟩
def indexLast (c : Config) : VmConstraint2 :=
  .base (.piBinding .last (index c) (lengthPi c))
def constraints (c : Config) : List VmConstraint2 :=
  [chip c] ++ lanes.map (copy c) ++ lanes.map (seedPin c) ++
    lanes.map (outputPin c) ++ [indexFirst c, indexStep c, indexLast c]
def decorate (name : String) (d : EffectVmDescriptor2) (c : Config) : EffectVmDescriptor2 :=
  { d with
    name := name
    traceWidth := c.baseWidth + 17
    piCount := c.basePiCount + 9
    tables := d.tables ++ [poseidon2ChipTableDef]
    constraints := d.constraints ++ constraints c }
/-- Structural costs, independent of table size and word length. -/
theorem shape (name : String) (d : EffectVmDescriptor2) (c : Config) :
    (decorate name d c).traceWidth = c.baseWidth + 17 ∧
    (decorate name d c).piCount = c.basePiCount + 9 ∧
    (decorate name d c).constraints.length = d.constraints.length + 28 := by
  simp [decorate, constraints, lanes]
theorem base_tables (name : String) (d : EffectVmDescriptor2) (c : Config)
    (td : TableDef) (h : td ∈ d.tables) : td ∈ (decorate name d c).tables :=
  List.mem_append_left _ h
theorem memOps_decorate (name : String) (d : EffectVmDescriptor2) (c : Config) :
    memOpsOf (decorate name d c) = memOpsOf d := by
  cases h : c.seed <;> simp [memOpsOf, decorate, constraints, lanes, chip, copy,
    seedPin, outputPin, indexFirst, indexStep, indexLast, h]
theorem mapOps_decorate (name : String) (d : EffectVmDescriptor2) (c : Config) :
    mapOpsOf (decorate name d c) = mapOpsOf d := by
  cases h : c.seed <;> simp [mapOpsOf, decorate, constraints, lanes, chip, copy,
    seedPin, outputPin, indexFirst, indexStep, indexLast, h]
theorem lookupLog_decorate (name : String) (d : EffectVmDescriptor2) (c : Config)
    (t : VmTrace) (tid : TableId) (hne : tid ≠ .poseidon2) :
    lookupLog (decorate name d c) t tid = lookupLog d t tid := by
  cases h : c.seed <;> simp [lookupLog, decorate, constraints, lanes, chip, copy,
    seedPin, outputPin, indexFirst, indexStep, indexLast, h, Ne.symm hne]
/-- Forgetting the new columns preserves every base obligation, including memory/map logs. -/
theorem forget {hash : List ℤ → ℤ} {name : String} {d : EffectVmDescriptor2}
    {c : Config} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (decorate name d c) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t := by
  have hm : memLog (decorate name d c) t = memLog d t := by simp [memLog, memOps_decorate]
  have hp : mapLog (decorate name d c) t = mapLog d t := by simp [mapLog, mapOps_decorate]
  exact {
    rowConstraints := fun i hi x hx => h.rowConstraints i hi x (List.mem_append_left _ hx)
    rowHashes := h.rowHashes
    rowRanges := h.rowRanges
    memAddrsNodup := h.memAddrsNodup
    memClosed := by simpa [hm] using h.memClosed
    memDisciplined := by simpa [hm] using h.memDisciplined
    memBalanced := by simpa [hm] using h.memBalanced
    memTableFaithful := by simpa [hm] using h.memTableFaithful
    mapTableFaithful := by simpa [hp] using h.mapTableFaithful }
theorem forgetPublic {hash : List ℤ → ℤ} {name : String} {d : EffectVmDescriptor2}
    {c : Config} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hids : ∀ td ∈ d.tables, td.id ≠ .poseidon2)
    (h : Satisfied2Public hash (decorate name d c) minit mfin maddrs t) :
    Satisfied2Public hash d minit mfin maddrs t := by
  refine { forget h.toSatisfied2 with
    publicTablesFaithful := fun td htd => h.publicTablesFaithful td (base_tables _ _ _ _ htd)
    publicLookupBalanced := ?_ }
  intro td htd
  have hb := h.publicLookupBalanced td (base_tables _ _ _ _ htd)
  cases hs : td.sem <;> simp only [hs] at hb ⊢ <;> try trivial
  simpa only [lookupLog_decorate name d c t td.id (hids td htd)] using hb
section Extract
variable {hash : List ℤ → ℤ} {name : String} {d : EffectVmDescriptor2}
variable {c : Config} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
/-- Every generated row constrains all eight outputs. -/
theorem row_hash (H : List ℤ → List ℤ) (hs : ChipTableSoundN H (t.tf .poseidon2))
    (h : Satisfied2 hash (decorate name d c) minit mfin maddrs t)
    {i : Nat} (hi : i < t.rows.length) :
    (lanes.map (out c)).map (t.rows[i]) = H ((inputs c).map (·.eval (t.rows[i]))) := by
  apply chip_lookup_sound_N H (t.tf .poseidon2) hs (t.rows[i]) (inputs c)
    (lanes.map (out c)) (by chip_arity_admitted)
  have hc := h.rowConstraints i hi (chip c) (by simp [decorate, constraints])
  simpa only [chip, VmConstraint2.holdsAt, Lookup.holdsAt, envAt_loc hi] using hc
end Extract
/-- info: 'Dregg2.Circuit.Emit.RouteChain8.row_hash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_hash
end Dregg2.Circuit.Emit.RouteChain8
