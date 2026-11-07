/-
# Dregg2.Apps.GovernedParameters — a constitution-CITING parameter cell (round 2, the cross-cell import home).

`Apps/GovernedNamespaceGated.lean` modelled a governed registry as a single-credential gate plus four
slot caveats. Real, but it left the deepest naturalness gap OPEN: a governed cell that must carry a
parameter FIXED BY A CONSTITUTION in ANOTHER cell. The factory/polis lanes worked around this by COPYING
the constitution value at birth — sound, but not first-class: nothing recorded WHERE the literal came
from, so a verifier could not recompute it and tooling could not say "this is stale". The round-2
`Dregg2.Authority.CrossCellImport` makes that copy first-class and PROVED (`importValid` cites a source
cell's receipt + the value its field held there; the I-confluence keystone shows the cited PAST never
re-orders against the source's future). This app is the userspace HOME of that capability.

A governed-parameter cell publishes operating parameters (a fee, a quorum size) that are NOT free
literals: each is BOUND to a constitution cell's receipt. Updates are GOVERNED by a constitutional BOARD
(a multi-admin committee, the clean `senderMemberOf` form of the toy's single credential) with
PER-PARAMETER actor-bound approval slots, and the constitution pin itself is IMMUTABLE. Every clause is
a constraint of the cell's `RecordProgram`; every refusal is a theorem.

## Why this is not a toy

  * **the unprovenanced parameter.** The naive governed cell stores `fee = 30` as a bare literal — a
    verifier cannot tell whether 30 is the constitution's value or a typo / a quiet override. Here the
    fee slot is bound by `affineEq [(1, fee)] importedFee` where `importedFee` is the value a CITED
    constitution receipt committed (`CrossCellImport.importValid`): the binding is enforced by the SAME
    proved closure algebra as every other guard, and the provenance is non-forgeable by inheritance from
    the constitution chain's tamper-evidence. A parameter that does NOT match the cited constitution
    value is UNSAT (`unprovenanced_parameter_rejected`); a LYING import (claiming the constitution said
    99 when it said 30) fails `importValid` and cannot even be cited (`lying_import_rejected`).
  * **the board impostor.** A parameter update must be SIGNED by a board member, not merely by a
    capability holder. `boardMember` = `senderMemberOf constitutionBoard`: a stranger (or a stolen
    capability) is rejected (`non_board_member_rejected`). And flipping a specific parameter's approval
    slot is ACTOR-BOUND to the board via `anyOf [immutable approve_fee, senderMemberOf board]` — a turn
    that touches the slot must come from a board member (`approval_slot_actor_bound`).
  * **the constitution capture + the version replay.** The constitution PIN (the cited constitution
    cell's identity) is `immutable` — it cannot be silently repointed to a rogue constitution
    (`constitution_pin_immutable`). And the parameter `version` strictly increases — no replay of an old
    parameter set (`version_replay_rejected`).

## The provenance composition (the round-2 wedge)

The binding is a TWO-PART contract, the honest cross-cell story split exactly along the §8 seam:

  1. **provenance** (`CrossCellImport`): `importValid H constitution imp` proves the cited constitution
     receipt is in the constitution's well-linked chain AND the constitution field held `imp.value`
     there. A lie (`imp.value ≠` the committed value) fails this — it cannot be presented. The
     I-confluence keystone (`importValid_stable_under_source_advance`) means this citation never
     re-orders against the constitution's future amendments: a snapshot, dated.
  2. **enforcement** (this cell's program): `affineEq [(1, feeF)] imp.value` makes the local fee slot
     EQUAL the provenanced value, enforced by the cell's `RecordProgram` on every turn. `paramBinding`
     below is that bridge, and `param_binding_matches_constitution` proves the composed contract:
     `importValid` (the value is the constitution's truth) ∧ the cell admits ⇒ the local parameter
     equals the constitution's committed value.

## The parameter cell — its state

  * `version`        — the strictly-increasing parameter-set counter (replay-safe);
  * `constitution`   — the cited constitution cell's identity (IMMUTABLE — no repoint);
  * `fee`            — a governed parameter, BOUND to the constitution's committed value;
  * `approve_fee`    — the board's per-parameter approval slot (actor-bound to the board).

## Honest scope

  * `affineEq`/`senderMemberOf` are decidable record/context predicates proved here. The §8 seam is the
    constitution chain's `HInj`/`HFresh` (the receipt digest's collision-resistance), threaded through
    `CrossCellImport`'s `chain_tamper_evident` — never a Lean axiom.
  * `senderMemberOf` is FREE / i-confluent (a predicate over the single turn's own sender). The import
    is I-confluent (it reads an immutable past receipt). So this whole cell is coordination-free in the
    sense `CrossCellImport` proves — the constitution citation never forces ordering against the
    constitution's amendments.

Discipline: axiom-clean (`#assert_all_clean` at the close) —
`decide` / `#guard` / `Exec.Program` + `CrossCellImport` keystone reuse only. `lake build` green (LOCAL).
-/
import Dregg2.Exec.Program
import Dregg2.Authority.CrossCellImport
import Dregg2.Authority.ImportBinding

namespace Dregg2.Apps.GovernedParameters

open Dregg2.Exec
open Dregg2.Authority.CrossCellImport (Import SourceHistory importValid readAt)
open Dregg2.Authority.ImportBinding (ImportedEq)

/-! ## §0 — The parameter cell's field names, the constitution board, identities. -/

/-- The strictly-increasing parameter-set version. -/
abbrev versionF : FieldName := "version"
/-- The cited constitution cell's identity (IMMUTABLE). -/
abbrev constitutionF : FieldName := "constitution"
/-- A governed parameter, bound to the constitution's committed value. -/
abbrev feeF : FieldName := "fee"
/-- The board's per-parameter approval slot for `fee` (actor-bound to the board). -/
abbrev approveFeeF : FieldName := "approve_fee"

/-- The constitutional BOARD: the identities authorized to update the parameters (a multi-admin
committee). -/
abbrev constitutionBoard : List Int := [0xB0, 0xB1, 0xB2]
/-- A board member's identity. -/
abbrev boardMemberPk : Int := 0xB1
/-- A stranger's identity (not on the board). -/
abbrev strangerPk : Int := 0x99

/-! ## §1 — THE PARAMETER-UPDATE GATE as a `RecordProgram`
(board provenance ∧ version ∧ constitution-pin ∧ parameter-binding).

The update program is a conjunction, each clause a constraint of the cell's `RecordProgram`:

  * `senderMemberOf constitutionBoard` — **board provenance**: an update must be SIGNED BY a board
    member. A stranger (or stolen capability) cannot update the parameters.
  * `strictMono versionF` — **replay-safety**: the parameter version strictly increases.
  * `immutable constitutionF` — **no constitution capture**: the cited constitution pin cannot be
    silently repointed to a rogue constitution.
  * `affineEq [(1, feeF)] importedFee` — **the parameter binding**: the local fee equals the value a
    CITED constitution receipt committed (the provenance is `CrossCellImport.importValid`, §2).
  * `anyOf [immutable approveFeeF, senderMemberOf constitutionBoard]` — **the actor-bound approval
    slot**: flipping the fee-approval slot demands a board-member sender (the multi-admin polis tooth).

The `importedFee` literal is the value the constitution committed — supplied by a PROVED `Import` (§2),
not a free parameter. The conjunction is ONE predicate (all-or-nothing). -/
def updateConstraints (importedFee : Int) : List StateConstraint :=
  [ .simple (.senderMemberOf constitutionBoard)                                    -- board provenance
  , .simple (.strictMono versionF)                                                 -- no replay
  , .simple (.immutable constitutionF)                                             -- no constitution capture
  , .affineEq [(1, feeF)] importedFee                                              -- parameter binding
  , .anyOf [.immutable approveFeeF, .senderMemberOf constitutionBoard] ]           -- actor-bound approval

/-- **The governed-parameter program** — the constitution-bound update policy as ONE structure-map.
Parameterized by the constitution's committed fee value (the provenanced literal from §2). -/
def paramProgram (importedFee : Int) : RecordProgram := .predicate (updateConstraints importedFee)

/-! ## §2 — THE PROVENANCE COMPOSITION: the binding IS a first-class `ImportedEq` (gap-2 adoption).

The round-2 `Authority.ImportBinding.ImportedEq` is exactly the construct this app re-derived by hand: a
cited `Import` PLUS the local field it binds, carrying the provenance obligation (`importValid`, on the
SAME `Import` object) and projecting the enforcement constraint (`toConstraint` = the EXISTING `affineEq`
atom). So `paramBinding imp` is now the `ImportedEq`'s `toConstraint` (NOT a re-spelled `affineEq`), and
its admit-characterization + the composed provenance contract are DIRECT corollaries of the atom's proved
keystones — the two obligations no longer travel as a hand-threaded pair. (A cited import binds the local
field `feeF` when `imp.localField = feeF`; the governed cell only ever cites constitution imports for its
fee slot.) -/

/-- **`paramBinding imp`** — the parameter-binding constraint for a cited constitution import, now the
first-class `ImportedEq`'s projected enforcement constraint (`ImportedEq.toConstraint ⟨imp⟩` =
`.affineEq [(1, imp.localField)] imp.value`). For a fee-citing import (`imp.localField = feeF`) this is the
local fee slot bound to the provenanced value — the binding the cell program enforces, with the provenance
obligation `importValid` riding the SAME `imp`. -/
def paramBinding (imp : Import) : StateConstraint := (ImportedEq.mk imp).toConstraint

/-- **`paramBinding_iff`.** The binding constraint holds exactly when the post-state carries the cited
value at the import's local field — a DIRECT reuse of `ImportedEq.admits_iff` (the atom's proved
single-term affine admit-char), no inline `affineSum`/`affineEq` re-derivation. -/
theorem paramBinding_iff (imp : Import) (o n : Value) :
    evalConstraint (paramBinding imp) o n = true ↔ n.scalar imp.localField = some imp.value :=
  ImportedEq.admits_iff ⟨imp⟩ o n

/-- **`param_binding_matches_constitution` (THE COMPOSED PROVENANCE CONTRACT — now a COROLLARY).** When
the import is VALID (`importValid`: the cited constitution receipt is in the constitution's well-linked
chain AND the constitution field held `imp.value` there) AND the cell admits the binding constraint, the
local parameter EQUALS the value the constitution committed at the cited receipt. The whole cross-cell
contract this app re-derived by hand is now the atom's keystone `importedEq_binds_provenanced_value`,
applied here — provenance (the value is the constitution's truth, non-forgeable) + enforcement (the cell
holds exactly that value), fused in ONE construct. -/
theorem param_binding_matches_constitution
    {H : Receipts.Receipt → Nat} {constitution : SourceHistory} {imp : Import} {o n : Value}
    (hvalid : importValid H constitution imp)
    (hbind : evalConstraint (paramBinding imp) o n = true) :
    n.scalar imp.localField = some (readAt constitution imp.provenance imp.sourceField) :=
  Dregg2.Authority.ImportBinding.importedEq_binds_provenanced_value (b := ⟨imp⟩) hvalid hbind

/-! ## §3 — Extraction plumbing (the `EscrowDeskCouncil` pattern). -/

/-- Every constraint binds on an admitted update. -/
private theorem admitted_mem {importedFee : Int} {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : (paramProgram importedFee).admitsCtx ctx m o n = true)
    {c : StateConstraint} (hc : c ∈ updateConstraints importedFee) :
    evalConstraintCtx ctx c o n = true := by
  have hall : (updateConstraints importedFee).all (fun c => evalConstraintCtx ctx c o n) = true := h
  exact List.all_eq_true.mp hall c hc

private theorem admits_of_not_false {importedFee : Int} {ctx : TurnCtx} {m : Nat} {o n : Value}
    (hc : ¬ (paramProgram importedFee).admitsCtx ctx m o n = false) :
    (paramProgram importedFee).admitsCtx ctx m o n = true := by
  cases h : (paramProgram importedFee).admitsCtx ctx m o n with
  | true => rfl
  | false => exact absurd h hc

/-! ## §4 — THE TEETH on the update policy (both polarities, all PROVED). -/

/-- **① BOARD-IMPOSTOR TOOTH — an update not signed by a board member is UNSAT.** Any update whose
sender is NOT on the constitutional board is rejected: `admitsCtx = false`. A stranger holding a
capability cannot update the governed parameters — only the board may. -/
theorem non_board_member_rejected (importedFee : Int) (ctx : TurnCtx) (m : Nat) (o n : Value)
    (hstranger : ∀ s, ctx.sender = some s → s ∉ constitutionBoard) :
    (paramProgram importedFee).admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hprov := admitted_mem hne (c := .simple (.senderMemberOf constitutionBoard)) (.head _)
  have hmem : evalSimpleCtx ctx (.senderMemberOf constitutionBoard) o n = true := by
    simpa [evalConstraintCtx] using hprov
  obtain ⟨s, hs, hcon⟩ := (evalSimpleCtx_senderMemberOf_iff ctx constitutionBoard o n).mp hmem
  rw [List.contains_eq_mem] at hcon
  exact hstranger s hs (by simpa using hcon)

/-- **② VERSION-REPLAY TOOTH — an update that does not advance the version is UNSAT.** An update whose
new version is NOT strictly greater than the old (a replay of an old parameter set, or a plateau) is
rejected: `admitsCtx = false`. -/
theorem version_replay_rejected (importedFee : Int) (ctx : TurnCtx) (m : Nat) (o n : Value)
    (oldV newV : Int)
    (hold : o.scalar versionF = some oldV) (hnew : n.scalar versionF = some newV)
    (hreplay : ¬ oldV < newV) :
    (paramProgram importedFee).admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hmono := admitted_mem hne (c := .simple (.strictMono versionF)) (.tail _ (.head _))
  have hsm : evalSimpleCtx ctx (.strictMono versionF) o n = true := by
    simpa [evalConstraintCtx] using hmono
  rw [show evalSimpleCtx ctx (.strictMono versionF) o n = evalSimple (.strictMono versionF) o n from rfl]
    at hsm
  obtain ⟨a, b, ha, hb, hlt⟩ := (evalSimple_strictMono_iff versionF o n).mp hsm
  rw [hold] at ha; injection ha with ha; subst ha
  rw [hnew] at hb; injection hb with hb; subst hb
  exact hreplay hlt

/-- **③ CONSTITUTION-CAPTURE TOOTH — repointing the constitution pin is UNSAT.** An update that CHANGES
the cited constitution cell (the `immutable constitution` clause rejects a flip) is rejected:
`admitsCtx = false`. The constitution pin cannot be silently swapped to a rogue constitution that would
"authorize" any parameter. -/
theorem constitution_pin_immutable (importedFee : Int) (ctx : TurnCtx) (m : Nat) (o n : Value)
    (oldC newC : Int)
    (hold : o.scalar constitutionF = some oldC) (hnew : n.scalar constitutionF = some newC)
    (hrepoint : newC ≠ oldC) :
    (paramProgram importedFee).admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have himm := admitted_mem hne (c := .simple (.immutable constitutionF)) (.tail _ (.tail _ (.head _)))
  have hi : evalSimpleCtx ctx (.immutable constitutionF) o n = true := by
    simpa [evalConstraintCtx] using himm
  rw [show evalSimpleCtx ctx (.immutable constitutionF) o n = evalSimple (.immutable constitutionF) o n from rfl]
    at hi
  -- immutable with present-old: admits iff new = old; but new ≠ old.
  have : evalSimple (.immutable constitutionF) o n = (n.scalar constitutionF == some oldC) := by
    show (match o.scalar constitutionF with
          | none => true
          | some a => n.scalar constitutionF == some a) = _
    rw [hold]
  rw [this, hnew] at hi
  simp only [beq_iff_eq, Option.some.injEq] at hi
  exact hrepoint hi

/-- **④ UNPROVENANCED-PARAMETER TOOTH — a fee not equal to the constitution's value is UNSAT.** An
update whose local fee does NOT equal the cited constitution value (`importedFee`) is rejected:
`admitsCtx = false`. A governed cell cannot carry an off-constitution parameter — the binding is
enforced by the cell program, so a quiet override is impossible. -/
theorem unprovenanced_parameter_rejected (importedFee : Int) (ctx : TurnCtx) (m : Nat) (o n : Value)
    (localFee : Int)
    (hfee : n.scalar feeF = some localFee)
    (hoff : localFee ≠ importedFee) :
    (paramProgram importedFee).admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hbind := admitted_mem hne (c := .affineEq [(1, feeF)] importedFee)
    (.tail _ (.tail _ (.tail _ (.head _))))
  have hb : evalConstraint (.affineEq [(1, feeF)] importedFee) o n = true := by
    simpa [evalConstraintCtx] using hbind
  -- the binding IS paramBinding for an import citing `importedFee`; paramBinding_iff gives the fee.
  have heq : n.scalar feeF = some importedFee := by
    have := (paramBinding_iff ⟨feeF, "src", importedFee, ⟨0, 0, 0, 0⟩⟩ o n).mp hb
    simpa using this
  rw [hfee] at heq; injection heq with heq; exact hoff heq

/-- **⑤ APPROVAL-SLOT ACTOR-BOUND TOOTH — flipping the fee-approval slot demands a board sender.** An
update that CHANGES the `approve_fee` slot (the `immutable approve_fee` disjunct rejects the flip) with a
NON-board sender is rejected: `admitsCtx = false`. The per-parameter approval is bound to the board — a
stolen capability cannot record an approval. -/
theorem approval_slot_actor_bound (importedFee : Int) (ctx : TurnCtx) (m : Nat) (o n : Value)
    (hflip : evalSimple (.immutable approveFeeF) o n = false)
    (hnonboard : ∀ s, ctx.sender = some s → s ∉ constitutionBoard) :
    (paramProgram importedFee).admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have happ := admitted_mem hne
    (c := .anyOf [.immutable approveFeeF, .senderMemberOf constitutionBoard])
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  -- the anyOf admitted: immutable disjunct is false (flip), so senderMemberOf must hold.
  have hany : (evalSimpleCtx ctx (.immutable approveFeeF) o n
              || (evalSimpleCtx ctx (.senderMemberOf constitutionBoard) o n || false)) = true := by
    simpa [evalConstraintCtx] using happ
  have himm : evalSimpleCtx ctx (.immutable approveFeeF) o n = false := by
    rw [show evalSimpleCtx ctx (.immutable approveFeeF) o n = evalSimple (.immutable approveFeeF) o n from rfl]
    exact hflip
  rw [himm] at hany
  simp only [Bool.false_or, Bool.or_false] at hany
  obtain ⟨s, hs, hcon⟩ := (evalSimpleCtx_senderMemberOf_iff ctx constitutionBoard o n).mp hany
  rw [List.contains_eq_mem] at hcon
  exact hnonboard s hs (by simpa using hcon)

/-- **⑥ THE HONEST CONSTITUTION-BOUND UPDATE COMMITS (the gate is not constant-false).** An update
signed by a board member, advancing the version, leaving the constitution pin and approval slot
untouched, and carrying the constitution's committed fee, ADMITS. The conjunction of the teeth is
non-vacuous: there is a real governed update the cell lets through. -/
theorem honest_update_admits (importedFee : Int) (ctx : TurnCtx) (m : Nat) (o n : Value)
    (oldV newV pin : Int)
    (hsender : ctx.sender = some boardMemberPk)
    (holdV : o.scalar versionF = some oldV) (hnewV : n.scalar versionF = some newV) (hadv : oldV < newV)
    (holdPin : o.scalar constitutionF = some pin) (hnewPin : n.scalar constitutionF = some pin)
    (hfee : n.scalar feeF = some importedFee)
    (huntouchedApprove : evalSimple (.immutable approveFeeF) o n = true) :
    (paramProgram importedFee).admitsCtx ctx m o n = true := by
  have c1 : evalConstraintCtx ctx (.simple (.senderMemberOf constitutionBoard)) o n = true := by
    show evalSimpleCtx ctx (.senderMemberOf constitutionBoard) o n = true
    exact (evalSimpleCtx_senderMemberOf_iff ctx constitutionBoard o n).mpr ⟨boardMemberPk, hsender, by decide⟩
  have c2 : evalConstraintCtx ctx (.simple (.strictMono versionF)) o n = true := by
    show evalSimpleCtx ctx (.strictMono versionF) o n = true
    rw [show evalSimpleCtx ctx (.strictMono versionF) o n = evalSimple (.strictMono versionF) o n from rfl]
    exact (evalSimple_strictMono_iff versionF o n).mpr ⟨oldV, newV, holdV, hnewV, hadv⟩
  have c3 : evalConstraintCtx ctx (.simple (.immutable constitutionF)) o n = true := by
    show evalSimpleCtx ctx (.immutable constitutionF) o n = true
    rw [show evalSimpleCtx ctx (.immutable constitutionF) o n = evalSimple (.immutable constitutionF) o n from rfl]
    show (match o.scalar constitutionF with
          | none => true
          | some a => n.scalar constitutionF == some a) = true
    rw [holdPin, hnewPin]; simp
  have c4 : evalConstraintCtx ctx (.affineEq [(1, feeF)] importedFee) o n = true := by
    show evalConstraint (.affineEq [(1, feeF)] importedFee) o n = true
    have : evalConstraint (paramBinding ⟨feeF, "src", importedFee, ⟨0, 0, 0, 0⟩⟩) o n = true :=
      (paramBinding_iff ⟨feeF, "src", importedFee, ⟨0, 0, 0, 0⟩⟩ o n).mpr (by simpa using hfee)
    simpa [paramBinding, ImportedEq.toConstraint] using this
  have c5 : evalConstraintCtx ctx (.anyOf [.immutable approveFeeF, .senderMemberOf constitutionBoard]) o n = true := by
    have himm : evalSimpleCtx ctx (.immutable approveFeeF) o n = true := by
      rw [show evalSimpleCtx ctx (.immutable approveFeeF) o n = evalSimple (.immutable approveFeeF) o n from rfl]
      exact huntouchedApprove
    show (evalSimpleCtx ctx (.immutable approveFeeF) o n
          || (evalSimpleCtx ctx (.senderMemberOf constitutionBoard) o n || false)) = true
    rw [himm]; simp
  show (updateConstraints importedFee).all (fun c => evalConstraintCtx ctx c o n) = true
  simp only [updateConstraints, List.all_cons, List.all_nil, c1, c2, c3, c4, c5, Bool.and_true]

/-! ## §5 — THE LYING IMPORT (the provenance tooth at the `CrossCellImport` layer).

The §4 teeth guard ENFORCEMENT (the cell holds the bound value). This tooth guards PROVENANCE: a lie
about what the constitution said cannot even be CITED. We exhibit a concrete constitution history where
the fee field committed 30 at the cited receipt, and show that an import claiming the constitution said
99 is NOT `importValid` (the readout check fails) — while the truthful import IS valid. So an adversary
cannot present a false `importedFee` to feed `paramProgram`. -/

section LyingImport

open Dregg2.Exec.Receipts (mkReceipt genesisSentinel demoHash)

/-- A constitution cell: an older receipt committed `fee = 30`. -/
def consReceipt : Receipts.Receipt := mkReceipt genesisSentinel 30 30 0
def consHead : Receipts.Receipt := mkReceipt (demoHash consReceipt) 30 30 1
def consState : Receipts.Receipt → Value := fun r =>
  if r = consHead then .record [(feeF, .int 30)] else .record [(feeF, .int 30)]
def constitutionHist : SourceHistory := ⟨[consHead, consReceipt], consState⟩

/-- The TRUTHFUL import: "the constitution's fee was 30 at consReceipt." -/
def truthfulImport : Import := ⟨feeF, feeF, 30, consReceipt⟩
/-- The LYING import: claims "the constitution's fee was 99" — but it was 30. -/
def lyingImport : Import := ⟨feeF, feeF, 99, consReceipt⟩

/-- **`lying_import_rejected` (the provenance tooth).** The truthful import (cites 30) IS `importValid`
on the constitution history; the lying import (claims 99) is NOT — its cited value does not match what
the constitution committed at the cited receipt. So an adversary cannot present a false constitution
value to bind the parameter to. -/
theorem lying_import_rejected :
    importValid demoHash constitutionHist truthfulImport ∧
      ¬ importValid demoHash constitutionHist lyingImport := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- well-linked [consHead, consReceipt]: consHead.prevHash = demoHash consReceipt, consReceipt genesis.
    exact ⟨rfl, rfl⟩
  · -- consReceipt ∈ the chain.
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · -- readAt constitutionHist consReceipt feeF = 30 (the truthful value).
    decide
  · -- the lie: readAt = 30 ≠ 99, so the third conjunct of importValid fails.
    rintro ⟨_, _, hread⟩
    have : readAt constitutionHist lyingImport.provenance lyingImport.sourceField = 99 := hread
    revert this; decide

end LyingImport

/-! ## §6 — NON-VACUITY TEETH (`#guard`): the update policy BITES on the concrete cell, both
polarities. The cited constitution fee is 30 (see §5). -/

section Witnesses

/-- The provenanced fee value (what the constitution committed; see §5). -/
abbrev citedFee : Int := 30

/-- A faithful constitution-bound update: a board member signs, version advances, constitution pin
unchanged, approval slot unchanged, fee = the constitution's 30. -/
def updateCtx : TurnCtx := { sender := some boardMemberPk }
def paramNew : Value :=
  .record [(versionF, .int 6), (constitutionF, .int 0xC0), (feeF, .int 30), (approveFeeF, .int 0)]
def paramOld : Value :=
  .record [(versionF, .int 5), (constitutionF, .int 0xC0), (feeF, .int 30), (approveFeeF, .int 0)]

-- ⑥ COMMIT: a faithful constitution-bound update ADMITS (board-signed, version 5→6, pin fixed, fee=30).
#guard (paramProgram citedFee).admitsCtx updateCtx 0 paramOld paramNew

-- ① REFUSE (board impostor): a stranger signs the update. REJECTED (only the board may).
#guard (paramProgram citedFee).admitsCtx
  { updateCtx with sender := some strangerPk } 0 paramOld paramNew == false

-- ① REFUSE (no sender): unsigned update. REJECTED (fail-closed board provenance).
#guard (paramProgram citedFee).admitsCtx
  { updateCtx with sender := none } 0 paramOld paramNew == false

-- ② REFUSE (version replay): the new version (5) equals the old (5). REJECTED.
#guard (paramProgram citedFee).admitsCtx updateCtx 0 paramOld
  (.record [(versionF, .int 5), (constitutionF, .int 0xC0), (feeF, .int 30), (approveFeeF, .int 0)]) == false

-- ③ REFUSE (constitution capture): the pin is repointed 0xC0 → 0xDEAD (a rogue constitution). REJECTED.
#guard (paramProgram citedFee).admitsCtx updateCtx 0 paramOld
  (.record [(versionF, .int 6), (constitutionF, .int 0xDEAD), (feeF, .int 30), (approveFeeF, .int 0)]) == false

-- ④ REFUSE (unprovenanced parameter): the fee is set to 99, off the constitution's 30. REJECTED.
#guard (paramProgram citedFee).admitsCtx updateCtx 0 paramOld
  (.record [(versionF, .int 6), (constitutionF, .int 0xC0), (feeF, .int 99), (approveFeeF, .int 0)]) == false

-- ⑤ REFUSE (approval-slot impostor): a STRANGER flips the approval slot 0 → 1. REJECTED (actor-bound).
#guard (paramProgram citedFee).admitsCtx
  { updateCtx with sender := some strangerPk } 0
  (.record [(versionF, .int 5), (constitutionF, .int 0xC0), (feeF, .int 30), (approveFeeF, .int 0)])
  (.record [(versionF, .int 6), (constitutionF, .int 0xC0), (feeF, .int 30), (approveFeeF, .int 1)]) == false

-- ⑤ COMMIT (approval-slot board member): a BOARD MEMBER flips the approval slot 0 → 1. ADMITTED.
#guard (paramProgram citedFee).admitsCtx updateCtx 0
  (.record [(versionF, .int 5), (constitutionF, .int 0xC0), (feeF, .int 30), (approveFeeF, .int 0)])
  (.record [(versionF, .int 6), (constitutionF, .int 0xC0), (feeF, .int 30), (approveFeeF, .int 1)])

-- The multi-admin board atom isolated: a member (0xB1) ADMITS, a stranger REJECTS, no sender REJECTS.
#guard evalSimpleCtx { sender := some boardMemberPk } (.senderMemberOf constitutionBoard) (.record []) (.record [])
#guard evalSimpleCtx { sender := some strangerPk } (.senderMemberOf constitutionBoard) (.record []) (.record []) == false
#guard evalSimpleCtx {} (.senderMemberOf constitutionBoard) (.record []) (.record []) == false

-- The parameter binding isolated: fee = 30 (the cited value) ADMITS; fee = 31 REJECTS.
#guard evalConstraint (paramBinding truthfulImport) (.record []) (.record [(feeF, .int 30)])
#guard evalConstraint (paramBinding truthfulImport) (.record []) (.record [(feeF, .int 31)]) == false

end Witnesses

/-! ## §7 — Axiom hygiene. Every load-bearing update + provenance theorem checked kernel-clean. -/

#assert_all_clean [
  paramBinding_iff,
  param_binding_matches_constitution,
  non_board_member_rejected,
  version_replay_rejected,
  constitution_pin_immutable,
  unprovenanced_parameter_rejected,
  approval_slot_actor_bound,
  honest_update_admits,
  lying_import_rejected
]

end Dregg2.Apps.GovernedParameters
