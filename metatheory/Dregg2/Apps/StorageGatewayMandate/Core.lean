/-
# Dregg2.Apps.StorageGatewayMandate.Core — object-store mandate + VFS admissibility (Phase A).

A storage-gateway mandate models a content-addressed object store: bucket/prefix labels, GET/PUT/LIST
ops, a Stingray `Slice` volume budget, and compartment clearance for reads. Pure, computable,
`#eval`-able.
-/
import Dregg2.Authority.ClearanceGraph
import Dregg2.Exec.Kernel
import Dregg2.Exec.Value
import Dregg2.Proof.Stingray
import Dregg2.Tactics

namespace Dregg2.Apps.StorageGatewayMandate

open Dregg2.Exec
open Dregg2.Authority.ClearanceGraph
open Dregg2.Proof.Stingray

/-! ## Object-store types. -/

/-- Storage gateway operation (VFS row: GET / PUT / LIST). -/
inductive StorageOp where
  | GET
  | PUT
  | LIST
  deriving Repr, DecidableEq

/-- Encode an op as an `Int` field value for `setFieldA`. -/
def StorageOp.toInt : StorageOp → Int
  | .GET  => 0
  | .PUT  => 1
  | .LIST => 2

/-- Decode an op field value (demo-facing). -/
def StorageOp.ofInt (n : Int) : Option StorageOp :=
  if n = 0 then some .GET
  else if n = 1 then some .PUT
  else if n = 2 then some .LIST
  else none

/-- Content-addressed blob reference (BLAKE3 hash stand-in). -/
structure BlobRef where
  hash : Nat
  deriving Repr, DecidableEq

/-- One storage request: op + object key + optional blob hash (PUT). -/
structure StorageRequest where
  op   : StorageOp
  key  : String
  blob : Option BlobRef := none
  deriving Repr, DecidableEq

/-- The storage-gateway mandate carried by the gateway cell. -/
structure StorageMandate where
  bucket          : Label
  keyPrefix       : String
  allowedOps      : List StorageOp
  putCost         : Nat
  getCost         : Nat
  listCost        : Nat
  actorLabels     : List Label
  clearanceGraph  : ClearanceGraph
  readCompartment : Label
  volumeBudget    : Slice
  anchor          : Nat := 42
  tracker         : CellId := 0
  deriving Repr, DecidableEq

/-! ## Admissibility predicates. -/

/-- Whether `op` is listed in the mandate's allowed set. -/
def opAllowed (m : StorageMandate) (op : StorageOp) : Bool :=
  m.allowedOps.contains op

/-- Object key lies under the mandated prefix (`pfx.isPrefixOf key`). -/
def keyUnderPrefix (pfx key : String) : Bool :=
  pfx.isPrefixOf key

/-- PUT is authorized only when the key matches the mandated prefix. -/
def putPrefixOK (m : StorageMandate) (key : String) : Bool :=
  keyUnderPrefix m.keyPrefix key

/-- GET requires compartment clearance on `readCompartment`. -/
def getClearanceOK (m : StorageMandate) : Bool :=
  mayRead m.clearanceGraph m.actorLabels m.readCompartment

/-- Per-op volume debit against the Stingray slice. -/
def opCost (m : StorageMandate) (op : StorageOp) : Nat :=
  match op with
  | .GET  => m.getCost
  | .PUT  => m.putCost
  | .LIST => m.listCost

/-- **Runtime mandate state**: live Stingray slice + commitment anchor. -/
structure SgmRuntime where
  volume : Slice
  anchor : Nat
  deriving Repr, DecidableEq

def SgmRuntime.WF (s : SgmRuntime) : Prop := s.volume.spent ≤ s.volume.ceiling

def SgmRuntime.init (m : StorageMandate) : SgmRuntime :=
  { volume := m.volumeBudget, anchor := m.anchor }

instance (s : SgmRuntime) : Decidable (s.WF) := by
  unfold SgmRuntime.WF; infer_instance

/-- **`sgmAdmitM`** — predicate-level one-step admission: op allowed, prefix/clearance gates,
volume debit via `Slice.tryDebit`. -/
def sgmAdmitM (m : StorageMandate) (s : SgmRuntime) (req : StorageRequest) : Option SgmRuntime :=
  if opAllowed m req.op then
    match req.op with
    | .GET =>
      if getClearanceOK m then
        (s.volume.tryDebit m.getCost).map fun v => { s with volume := v }
      else
        none
    | .PUT =>
      if putPrefixOK m req.key then
        (s.volume.tryDebit m.putCost).map fun v => { s with volume := v }
      else
        none
    | .LIST =>
      (s.volume.tryDebit m.listCost).map fun v => { s with volume := v }
  else
    none

/-! ## The EXECUTOR ADMIT TABLE — `sgmAdmitM`'s op-leg baked into a decision table.

The executor sees only a scalar write of the op code to `last_op`. We bake the op-allowlist ∧
GET-clearance leg of `sgmAdmitM` into a finite `(old, new)` decision table: an op code `n` is an
admitted `new` value iff its op is allowed AND (if it is GET, clearance holds). The cell's program
carries an `.admitTable lastOpSlot` with THIS table, so a no-clearance GET (or a disallowed op) is
NOT in the table and the executor rejects the `last_op` write — internalizing the off-line
op-allowlist ∧ clearance admission. (Prefix-on-PUT is over the key STRING, not a scalar, so it stays
a predicate-layer obligation; volume is the separate `boundedBy`/`monotonic` leg.) -/

/-- The op-leg of `sgmAdmitM`: op allowed AND (GET ⇒ clearance). The part the executor can decide off
the scalar op code (prefix/volume are the other legs). -/
def sgmOpAdmitted (m : StorageMandate) (op : StorageOp) : Bool :=
  opAllowed m op && (match op with | .GET => getClearanceOK m | _ => true)

/-- The `(old, new)` decision table baked from `sgmAdmitM`'s op-leg: for every admitted op, the pair
`(_, op.toInt)` for any prior op code `old ∈ {0,1,2}` (a `last_op` rewrite from any recorded op). -/
def sgmOpAdmitTable (m : StorageMandate) : List (Int × Int) :=
  ([(-1 : Int), 0, 1, 2]).flatMap fun old =>
    ([StorageOp.GET, StorageOp.PUT, StorageOp.LIST]).filterMap fun op =>
      if sgmOpAdmitted m op then some (old, op.toInt) else none

/-- **`sgmOpAdmitTable_mem_iff`.** The table contains `(old, op.toInt)` (for a valid prior op
code `old ∈ {-1,0,1,2}`) iff the op is admitted by `sgmAdmitM`'s op-leg. -/
theorem sgmOpAdmitTable_mem_iff (m : StorageMandate) (old : Int) (op : StorageOp)
    (hold : old ∈ [(-1 : Int), 0, 1, 2]) :
    (old, op.toInt) ∈ sgmOpAdmitTable m ↔ sgmOpAdmitted m op = true := by
  unfold sgmOpAdmitTable
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨o, _, ho⟩
    rw [List.mem_filterMap] at ho
    obtain ⟨op', _, hop'⟩ := ho
    by_cases had : sgmOpAdmitted m op'
    · rw [if_pos had] at hop'
      simp only [Option.some.injEq, Prod.mk.injEq] at hop'
      obtain ⟨_, hcode⟩ := hop'
      have : op' = op := by cases op <;> cases op' <;> simp_all [StorageOp.toInt]
      subst this; exact had
    · rw [if_neg had] at hop'; exact absurd hop' (by simp)
  · intro had
    exact ⟨old, hold, by rw [List.mem_filterMap]; exact ⟨op, by cases op <;> simp, by rw [if_pos had]⟩⟩

/-! ## One-step lemmas. -/

theorem tryDebit_preserves_spent_le (s s' : Slice) (cost : Nat) (hwf : s.spent ≤ s.ceiling)
    (h : s.tryDebit cost = some s') : s'.spent ≤ s'.ceiling := by
  obtain ⟨hsp, hcl⟩ := tryDebit_spent h
  have hrem := (tryDebit_isSome_iff s cost).mp (by rw [h]; simp)
  have hbound : cost ≤ s.ceiling - s.spent := by simpa [Slice.remaining] using hrem
  rw [hsp, hcl]
  omega

theorem sgm_op_not_allowed_rejected (m : StorageMandate) (s : SgmRuntime) (req : StorageRequest)
    (hop : opAllowed m req.op = false) :
    sgmAdmitM m s req = none := by
  unfold sgmAdmitM
  simp [hop]

theorem sgm_prefix_violation_rejected (m : StorageMandate) (s : SgmRuntime) (key : String)
    (hop : opAllowed m .PUT = true) (hpfx : putPrefixOK m key = false) :
    sgmAdmitM m s { op := .PUT, key := key } = none := by
  simp [sgmAdmitM, hop, hpfx, ↓reduceIte]

theorem sgm_clearance_fail_rejected (m : StorageMandate) (s : SgmRuntime) (key : String)
    (hop : opAllowed m .GET = true) (hcl : getClearanceOK m = false) :
    sgmAdmitM m s { op := .GET, key := key } = none := by
  simp [sgmAdmitM, hop, hcl, ↓reduceIte]

theorem sgm_over_debit_rejected_get (m : StorageMandate) (s : SgmRuntime) (key : String)
    (hop : opAllowed m .GET = true) (hdeb : (s.volume.tryDebit m.getCost).isSome = false) :
    sgmAdmitM m s { op := .GET, key := key } = none := by
  have hnone : s.volume.tryDebit m.getCost = none := by
    cases hvol : s.volume.tryDebit m.getCost with
    | none => rfl
    | some v => simp [hvol] at hdeb
  simp [sgmAdmitM, hop, hnone, Option.map_none, ↓reduceIte]

theorem sgm_over_debit_rejected_put (m : StorageMandate) (s : SgmRuntime) (key : String)
    (hop : opAllowed m .PUT = true) (hpfx : putPrefixOK m key = true)
    (hdeb : (s.volume.tryDebit m.putCost).isSome = false) :
    sgmAdmitM m s { op := .PUT, key := key } = none := by
  have hnone : s.volume.tryDebit m.putCost = none := by
    cases hvol : s.volume.tryDebit m.putCost with
    | none => rfl
    | some v => simp [hvol] at hdeb
  simp [sgmAdmitM, hop, hpfx, hnone, Option.map_none, ↓reduceIte]

theorem sgm_over_debit_rejected_list (m : StorageMandate) (s : SgmRuntime) (key : String)
    (hop : opAllowed m .LIST = true) (hdeb : (s.volume.tryDebit m.listCost).isSome = false) :
    sgmAdmitM m s { op := .LIST, key := key } = none := by
  have hnone : s.volume.tryDebit m.listCost = none := by
    cases hvol : s.volume.tryDebit m.listCost with
    | none => rfl
    | some v => simp [hvol] at hdeb
  simp [sgmAdmitM, hop, hnone, Option.map_none]

theorem sgm_over_debit_rejected (m : StorageMandate) (s : SgmRuntime) (req : StorageRequest)
    (hop : opAllowed m req.op = true)
    (hget : req.op = .GET → getClearanceOK m = true)
    (hput : req.op = .PUT → putPrefixOK m req.key = true)
    (hdeb : (s.volume.tryDebit (opCost m req.op)).isSome = false) :
    sgmAdmitM m s req = none := by
  obtain ⟨op, key, blob⟩ := req
  cases op with
  | GET =>
      exact sgm_over_debit_rejected_get m s key hop (by simpa [opCost] using hdeb)
  | PUT =>
      exact sgm_over_debit_rejected_put m s key hop (hput rfl) (by simpa [opCost] using hdeb)
  | LIST =>
      exact sgm_over_debit_rejected_list m s key hop (by simpa [opCost] using hdeb)

theorem sgmAdmitM_preserves_WF_get (m : StorageMandate) (s s' : SgmRuntime) (key : String)
    (hwf : s.WF) (hop : opAllowed m .GET = true) (hcl : getClearanceOK m = true)
    (h : sgmAdmitM m s { op := .GET, key := key } = some s') : s'.WF := by
  unfold SgmRuntime.WF at hwf ⊢
  unfold sgmAdmitM at h
  simp only [hop, hcl, ↓reduceIte] at h
  cases hvol : s.volume.tryDebit m.getCost with
  | none =>
      exfalso
      simpa [hvol, Option.map_none] using h
  | some v =>
      have heq : s' = { s with volume := v } :=
        Eq.symm (Option.some.inj (by simpa [hvol, Option.map_some] using h))
      rw [heq]
      exact tryDebit_preserves_spent_le s.volume v m.getCost hwf hvol

theorem sgmAdmitM_preserves_WF_put (m : StorageMandate) (s s' : SgmRuntime) (key : String)
    (hwf : s.WF) (hop : opAllowed m .PUT = true) (hpfx : putPrefixOK m key = true)
    (h : sgmAdmitM m s { op := .PUT, key := key } = some s') : s'.WF := by
  unfold SgmRuntime.WF at hwf ⊢
  unfold sgmAdmitM at h
  simp only [hop, hpfx, ↓reduceIte] at h
  cases hvol : s.volume.tryDebit m.putCost with
  | none =>
      exfalso
      simpa [hvol, Option.map_none] using h
  | some v =>
      have heq : s' = { s with volume := v } :=
        Eq.symm (Option.some.inj (by simpa [hvol, Option.map_some] using h))
      rw [heq]
      exact tryDebit_preserves_spent_le s.volume v m.putCost hwf hvol

theorem sgmAdmitM_preserves_WF_list (m : StorageMandate) (s s' : SgmRuntime) (key : String)
    (hwf : s.WF) (hop : opAllowed m .LIST = true)
    (h : sgmAdmitM m s { op := .LIST, key := key } = some s') : s'.WF := by
  unfold SgmRuntime.WF at hwf ⊢
  unfold sgmAdmitM at h
  simp only [hop, ↓reduceIte] at h
  cases hvol : s.volume.tryDebit m.listCost with
  | none =>
      exfalso
      simpa [hvol, Option.map_none] using h
  | some v =>
      have heq : s' = { s with volume := v } :=
        Eq.symm (Option.some.inj (by simpa [hvol, Option.map_some] using h))
      rw [heq]
      exact tryDebit_preserves_spent_le s.volume v m.listCost hwf hvol

theorem sgmAdmitM_preserves_WF (m : StorageMandate) (s s' : SgmRuntime) (req : StorageRequest)
    (hwf : s.WF) (h : sgmAdmitM m s req = some s') : s'.WF := by
  obtain ⟨op, key, blob⟩ := req
  cases hop : opAllowed m op with
  | false =>
      exfalso
      simpa [sgmAdmitM, hop] using h
  | true =>
      cases op with
      | GET =>
          by_cases hcl : getClearanceOK m
          · exact sgmAdmitM_preserves_WF_get m s s' key hwf hop hcl h
          · exfalso; simpa [sgmAdmitM, hop, hcl, ↓reduceIte] using h
      | PUT =>
          by_cases hpfx : putPrefixOK m key
          · exact sgmAdmitM_preserves_WF_put m s s' key hwf hop hpfx h
          · exfalso; simpa [sgmAdmitM, hop, hpfx, ↓reduceIte] using h
      | LIST =>
          exact sgmAdmitM_preserves_WF_list m s s' key hwf hop h

/-! ## Demo mandate + guards. -/

abbrev objectKeySlot : FieldName := "object_key"
abbrev lastOpSlot : FieldName := "last_op"
abbrev volumeSpentSlot : FieldName := "volume_spent"
abbrev commitmentAnchorSlot : FieldName := "commitment_anchor"
abbrev mandateCell : CellId := 0

def demoGraph : ClearanceGraph :=
  { edges := [ (Label.named "writer", Label.named "storage-read") ] }

/-- Writer may PUT/GET/LIST under `uploads/` with a 10-unit Stingray slice. -/
def demoMandate : StorageMandate :=
  { bucket := Label.named "app-bucket"
  , keyPrefix := "uploads/"
  , allowedOps := [.PUT, .GET, .LIST]
  , putCost := 5
  , getCost := 1
  , listCost := 2
  , actorLabels := [Label.named "writer"]
  , clearanceGraph := demoGraph
  , readCompartment := Label.named "storage-read"
  , volumeBudget := { ceiling := 10, spent := 0 }
  , anchor := 42
  , tracker := 100 }

/-- Guest actor lacks read clearance (GET rejected). -/
def guestMandate : StorageMandate :=
  { demoMandate with actorLabels := [Label.named "guest"] }

/-- PUT-only mandate for prefix authorization demo. -/
def putOnlyMandate : StorageMandate :=
  { demoMandate with allowedOps := [.PUT] }

def demoPutReq : StorageRequest :=
  { op := .PUT, key := "uploads/doc.txt", blob := some { hash := 3735928559 } }

def demoBadPutReq : StorageRequest :=
  { op := .PUT, key := "secret/doc.txt", blob := some { hash := 2989 } }

def demoGetReq : StorageRequest :=
  { op := .GET, key := "uploads/doc.txt" }

#guard opAllowed demoMandate .PUT
#guard putPrefixOK demoMandate "uploads/doc.txt"
#guard putPrefixOK demoMandate "secret/doc.txt" == false
#guard getClearanceOK demoMandate
#guard getClearanceOK guestMandate == false
#guard (sgmAdmitM demoMandate (SgmRuntime.init demoMandate) demoPutReq).isSome
#guard (sgmAdmitM demoMandate (SgmRuntime.init demoMandate) demoBadPutReq).isSome == false
#guard (sgmAdmitM guestMandate (SgmRuntime.init guestMandate) demoGetReq).isSome == false
#guard (sgmAdmitM demoMandate (SgmRuntime.init demoMandate) demoGetReq).isSome
#guard ((demoMandate.volumeBudget.tryDebit demoMandate.putCost).bind
          (fun s' => s'.tryDebit demoMandate.putCost)).isSome
#guard (((demoMandate.volumeBudget.tryDebit demoMandate.putCost).bind
           (fun s' => s'.tryDebit demoMandate.putCost)).bind
          (fun s'' => s''.tryDebit demoMandate.putCost)).isSome == false

/-! ## §C — DIFFERENTIAL CORPUS (mirror-drift tooth for `starbridge-storage-gateway-mandate`).

`starbridge-apps/storage-gateway-mandate/src/lib.rs::sgm_admit` is a HAND-PORT of `sgmAdmitM`
(op-allowlist ∧ prefix-on-PUT ∧ clearance-on-GET ∧ volume-debit). A hand port can SILENTLY
DRIFT — e.g. dropping the GET-clearance leg, or flipping the debit `≤` to `<` — and the proven
`sgmAdmitM` theorems would never notice the Rust copy diverged.

`sgmDiffCorpus` enumerates a fixed grid of `(mandate, request, spent)` and emits, per row, the
admission DECISION as `(admitted, newSpent)` — `newSpent = 0` when rejected. The Rust test
`starbridge-apps/storage-gateway-mandate/tests/sgm_lean_differential.rs` enumerates the IDENTICAL
grid through `sgm_admit` and asserts the SAME vector. Drift on either side fails:
  * Rust `sgm_admit` changes  → Rust vector ≠ `SGM_LEAN_DECISIONS` literal  → test FAIL;
  * Lean `sgmAdmitM` changes   → this `#guard` trips at Lean build, forcing a re-pin that
    re-exposes any Rust drift.

Grid (matches the Rust corpus order):
  mandates = [demo (PUT/GET/LIST, clearance✓), guest (clearance✗), putOnly]
  requests = [PUT uploads/a (cost 5), PUT secret/a (bad prefix), GET uploads/a (cost 1),
              LIST x (cost 2)]
  spents   = [0, 4, 8, 10]   (against ceiling 10)
The runtime state's ceiling is fixed at 10 (the demo `volumeBudget.ceiling`). -/

/-- A runtime at `spent` with the demo ceiling 10. -/
def sgmRtAt (spent : Nat) : SgmRuntime := { volume := { ceiling := 10, spent := spent }, anchor := 42 }

def sgmDiffMandates : List StorageMandate := [demoMandate, guestMandate, putOnlyMandate]

def sgmDiffReqs : List StorageRequest :=
  [ { op := .PUT,  key := "uploads/a" }
  , { op := .PUT,  key := "secret/a" }
  , { op := .GET,  key := "uploads/a" }
  , { op := .LIST, key := "x" } ]

def sgmDiffSpents : List Nat := [0, 4, 8, 10]

/-- Per-row decision: `(admitted, newSpent)`; `newSpent = 0` on reject. Row-major over
mandates × reqs × spents (3 × 4 × 4 = 48 rows). -/
def sgmDiffCorpus : List (Bool × Nat) :=
  sgmDiffMandates.flatMap fun m =>
    sgmDiffReqs.flatMap fun req =>
      sgmDiffSpents.map fun sp =>
        match sgmAdmitM m (sgmRtAt sp) req with
        | some s' => (true, s'.volume.spent)
        | none    => (false, 0)

-- PINNED: the 48-row decision vector. The Rust differential test pins the identical literal.
-- A drift in `sgmAdmitM` (or `sgm_admit`) breaks one of the two pins.
#guard sgmDiffCorpus ==
  [ -- demoMandate (allows PUT/GET/LIST, prefix uploads/, clearance✓; costs put5 get1 list2)
    -- PUT uploads/a (cost 5): admit while spent+5 ≤ 10
    (true, 5), (true, 9), (false, 0), (false, 0),
    -- PUT secret/a (bad prefix): always reject
    (false, 0), (false, 0), (false, 0), (false, 0),
    -- GET uploads/a (cost 1, clearance✓): admit while spent+1 ≤ 10
    (true, 1), (true, 5), (true, 9), (false, 0),
    -- LIST x (cost 2): admit while spent+2 ≤ 10
    (true, 2), (true, 6), (true, 10), (false, 0),
    -- guestMandate (clearance✗ — GET rejected; PUT/LIST unaffected)
    -- PUT uploads/a (cost 5)
    (true, 5), (true, 9), (false, 0), (false, 0),
    -- PUT secret/a (bad prefix)
    (false, 0), (false, 0), (false, 0), (false, 0),
    -- GET uploads/a (NO clearance): always reject
    (false, 0), (false, 0), (false, 0), (false, 0),
    -- LIST x (cost 2)
    (true, 2), (true, 6), (true, 10), (false, 0),
    -- putOnlyMandate (allows ONLY PUT — GET/LIST not in allowlist → rejected)
    -- PUT uploads/a (cost 5)
    (true, 5), (true, 9), (false, 0), (false, 0),
    -- PUT secret/a (bad prefix)
    (false, 0), (false, 0), (false, 0), (false, 0),
    -- GET uploads/a (op not allowed): always reject
    (false, 0), (false, 0), (false, 0), (false, 0),
    -- LIST x (op not allowed): always reject
    (false, 0), (false, 0), (false, 0), (false, 0) ]

#assert_axioms tryDebit_preserves_spent_le
#assert_axioms sgm_op_not_allowed_rejected
#assert_axioms sgm_prefix_violation_rejected
#assert_axioms sgm_clearance_fail_rejected
#assert_axioms sgm_over_debit_rejected
#assert_axioms sgmAdmitM_preserves_WF
#assert_axioms sgmOpAdmitTable_mem_iff

end Dregg2.Apps.StorageGatewayMandate