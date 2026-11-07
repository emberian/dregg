/-
# AttendantContinuityAggregate — owner-wide, replay-first companion continuity

An attendant should remain the same cared-for thing across sessions, crashes,
projection rebuilds, and later mechanic revisions.  This module joins the
proof-carrying `AttendantKernel` transition receipt to the generic
`EventSourcing` kernel without moving any attendant semantics into a database
adapter.

The aggregate is deliberately owner-wide for one activated template.  The
kernel spends activity credits in an owner-global `OwnerLedger`; independent
per-attendant streams could otherwise race that ledger and accept the same
credit once for each attendant.  One dense stream therefore carries:

* every owned attendant's exact current kernel projection;
* the one exact owner ledger shared by those attendants;
* care, repair, equipment, and capability history indexes;
* exact canon-settled activity-credit keys and receipt identifiers;
* dense replay and snapshot/cache recovery.

This is pre-Aspect continuity only.  It assigns no personality, lore, copying,
custody-market, or future Aspect semantics.
-/
import Dregg2.Games.PathOfAngels.AttendantKernel
import Dregg2.Games.PathOfAngels.EventSourcing
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.AttendantContinuityAggregate

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.Attendant

set_option autoImplicit false

/-! ## Receipt-derived continuity vocabulary -/

/-- An index over a kernel-emitted event, never a second transition language. -/
inductive Activity where
  | cared (mode : CareMode) (key : ReceiptKey) (amount : Nat)
  | trained (key : ReceiptKey) (amount : Nat)
  | equipped (equipment : EquipmentId) (capability : Option Capability)
  | unequipped
  | deployed (mission : MissionId) (equipment : EquipmentId)
      (capability : Capability) (strength : Nat)
  | returned (mission : MissionId)
  | epochAdvanced (epoch : EpochId)
deriving DecidableEq

def Activity.creditKey? : Activity → Option ReceiptKey
  | .cared _ key _ => some key
  | .trained key _ => some key
  | _ => none

def Activity.isCare : Activity → Bool
  | .cared .. => true
  | _ => false

def Activity.isMaintenance : Activity → Bool
  | .cared .repair _ _ => true
  | _ => false

def Activity.equipment? : Activity → Option EquipmentId
  | .equipped equipment _ => some equipment
  | .deployed _ equipment _ _ => some equipment
  | _ => none

def Activity.capability? : Activity → Option Capability
  | .equipped _ capability => capability
  | .deployed _ _ capability _ => some capability
  | _ => none

/-! ## Canonical CAS wire -/

/-- Finite replay check for the exact successor produced by
`Attendant.evaluateCasTransition`.  This is not a second CAS transition
function: production receipts below retain the actual `evaluateCasTransition`
equation, and `evaluateCasTransition_implies_wire_valid` proves that equation
entails every finite field checked here. -/
def casTransitionWireValid (before : CanonicalCasState)
    (identity : CasTransitionIdentity) (after : CanonicalCasState) : Bool :=
  decide (
    identity.expectedHead = before.head ∧
    identity.expectedRevision = before.revision ∧
    identity.nextRevision = identity.expectedRevision + 1 ∧
    identity.nextHead ≠ identity.expectedHead ∧
    identity.nullifier ∉ before.consumedNullifiers ∧
    after.head = identity.nextHead ∧
    after.revision = identity.nextRevision ∧
    after.consumedNullifiers = insert identity.nullifier before.consumedNullifiers)

theorem evaluateCasTransition_implies_wire_valid
    (before after : CanonicalCasState) (tooth : Tier0CasTooth)
    (h : evaluateCasTransition before tooth = some after) :
    casTransitionWireValid before tooth.identity after = true := by
  unfold evaluateCasTransition at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rw [← Option.some.inj h]
  simp_all [casTransitionWireValid, Tier0CasTooth.identity]

/-- Exact reducer-facing view of one proof-carrying receipt.  Local sequence
and action counters remain per attendant; the `EventSourcing` cursor is the
independent owner-wide sequence. -/
structure ReceiptView (Key State Ledger : Type) where
  subject : Key
  receiptId : Digest32
  beforeState : State
  beforeLedger : Ledger
  afterState : State
  afterLedger : Ledger
  beforeSequence : Nat
  afterSequence : Nat
  beforeCounter : Nat
  afterCounter : Nat
  cas : CasTransitionIdentity
  beforeCas : CanonicalCasState
  afterCas : CanonicalCasState
  activity : Activity
  settledCredit : Option ReceiptKey
deriving DecidableEq

structure ReceiptModel (Receipt Key State Ledger : Type) where
  view : Receipt → ReceiptView Key State Ledger

/-! ## Finite owner-wide projection -/

def rowKeys {Key State : Type} (rows : List (Key × State)) : List Key :=
  rows.map Prod.fst

def lookupRow {Key State : Type} [DecidableEq Key] (subject : Key) :
    List (Key × State) → Option State
  | [] => none
  | (key, state) :: rest =>
      if subject = key then some state else lookupRow subject rest

/-- Replace the unique row named by `subject`.  The reducer first requires a
unique row table and a successful exact lookup, so this never inserts or
silently selects among duplicates. -/
def replaceRow {Key State : Type} [DecidableEq Key] (subject : Key) (after : State) :
    List (Key × State) → List (Key × State)
  | [] => []
  | (key, state) :: rest =>
      if subject = key then (key, after) :: rest
      else (key, state) :: replaceRow subject after rest

theorem lookupRow_replaceRow_self {Key State : Type} [DecidableEq Key]
    (subject : Key) (before after : State) (rows : List (Key × State))
    (h : lookupRow subject rows = some before) :
    lookupRow subject (replaceRow subject after rows) = some after := by
  induction rows with
  | nil => simp [lookupRow] at h
  | cons row rest ih =>
      rcases row with ⟨key, state⟩
      by_cases same : subject = key
      · simp [lookupRow, replaceRow, same]
      · simp [lookupRow, replaceRow, same] at h ⊢
        exact ih h

theorem rowKeys_replaceRow {Key State : Type} [DecidableEq Key]
    (subject : Key) (after : State) (rows : List (Key × State)) :
    rowKeys (replaceRow subject after rows) = rowKeys rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨key, state⟩
      by_cases same : subject = key
      · simp [replaceRow, rowKeys, same]
      · simp only [replaceRow, same, if_false, rowKeys, List.map_cons]
        change key :: rowKeys (replaceRow subject after rest) = key :: rowKeys rest
        exact congrArg (List.cons key) ih

/-- Exact companion rows and exact global owner ledger are authoritative.
Everything after `receiptCount` is a replay-derived search/index cache. -/
structure Projection (Key State Ledger : Type) where
  rows : List (Key × State)
  liveLedger : Ledger
  canonicalCas : CanonicalCasState
  receiptCount : Nat
  careCount : Nat
  maintenanceCount : Nat
  equipmentSeen : Finset EquipmentId
  capabilitiesSeen : Finset Capability
  settledCredits : Finset ReceiptKey
  receiptIds : Finset Digest32
  lastSubject : Option Key
  lastReceipt : Option Digest32
deriving DecidableEq

def Projection.initial {Key State Ledger : Type} (rows : List (Key × State))
    (ledger : Ledger) (canonicalCas : CanonicalCasState) : Projection Key State Ledger where
  rows
  liveLedger := ledger
  canonicalCas
  receiptCount := 0
  careCount := 0
  maintenanceCount := 0
  equipmentSeen := ∅
  capabilitiesSeen := ∅
  settledCredits := ∅
  receiptIds := ∅
  lastSubject := none
  lastReceipt := none

private def insertOption {α : Type} [DecidableEq α] (value : Option α)
    (values : Finset α) : Finset α :=
  match value with
  | none => values
  | some item => insert item values

private def acceptedProjection {Key State Ledger : Type}
    [DecidableEq Key] (before : Projection Key State Ledger)
    (view : ReceiptView Key State Ledger) (settledCredits : Finset ReceiptKey) :
    Projection Key State Ledger where
  rows := replaceRow view.subject view.afterState before.rows
  liveLedger := view.afterLedger
  canonicalCas := view.afterCas
  receiptCount := before.receiptCount + 1
  careCount := before.careCount + if view.activity.isCare then 1 else 0
  maintenanceCount := before.maintenanceCount +
    if view.activity.isMaintenance then 1 else 0
  equipmentSeen := insertOption view.activity.equipment? before.equipmentSeen
  capabilitiesSeen := insertOption view.activity.capability? before.capabilitiesSeen
  settledCredits
  receiptIds := insert view.receiptId before.receiptIds
  lastSubject := some view.subject
  lastReceipt := some view.receiptId

private def reduceView {Key State Ledger : Type}
    [DecidableEq Key] [DecidableEq State] [DecidableEq Ledger]
    (before : Projection Key State Ledger) (view : ReceiptView Key State Ledger) :
    Option (Projection Key State Ledger) :=
  if _unique : (rowKeys before.rows).Nodup then
    match lookupRow view.subject before.rows with
    | none => none
    | some current =>
        if view.beforeState != current then none else
        if view.beforeLedger != before.liveLedger then none else
        if view.beforeCas != before.canonicalCas then none else
        if casTransitionWireValid view.beforeCas view.cas view.afterCas != true then none else
        if view.afterSequence != view.beforeSequence + 1 then none else
        if view.afterCounter != view.beforeCounter + 1 then none else
        if view.receiptId ∈ before.receiptIds then none else
        if view.activity.creditKey? != view.settledCredit then none else
        match view.settledCredit with
        | some key =>
            if key ∈ before.settledCredits then none
            else some (acceptedProjection before view (insert key before.settledCredits))
        | none => some (acceptedProjection before view before.settledCredits)
  else none

/-- Apply one exact receipt.  `EventSourcing` checks aggregate, schema, global
dense sequence, predecessor, payload digest, and event digest.  This reducer
checks unique companion rows, exact subject pre-state, the one global ledger,
local sequence/counter advancement, receipt replay, and owner-global settled
credit replay. -/
def reduceReceipt {Receipt Key State Ledger : Type}
    [DecidableEq Key] [DecidableEq State] [DecidableEq Ledger]
    (model : ReceiptModel Receipt Key State Ledger) :
    EventSourcing.Reducer (Projection Key State Ledger) Receipt := fun before receipt =>
  reduceView before (model.view receipt)

theorem reduceReceipt_success_exact {Receipt Key State Ledger : Type}
    [DecidableEq Key] [DecidableEq State] [DecidableEq Ledger]
    (model : ReceiptModel Receipt Key State Ledger)
    (before after : Projection Key State Ledger) (receipt : Receipt)
    (h : reduceReceipt model before receipt = some after) :
    after.rows = replaceRow (model.view receipt).subject
        (model.view receipt).afterState before.rows ∧
      after.liveLedger = (model.view receipt).afterLedger ∧
      after.canonicalCas = (model.view receipt).afterCas ∧
      after.receiptCount = before.receiptCount + 1 ∧
      (model.view receipt).receiptId ∈ after.receiptIds ∧
      rowKeys after.rows = rowKeys before.rows := by
  unfold reduceReceipt reduceView at h
  split at h <;> try contradiction
  cases hlookup : lookupRow (model.view receipt).subject before.rows with
  | none =>
      rw [hlookup] at h
      contradiction
  | some current =>
      rw [hlookup] at h
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      cases hs : (model.view receipt).settledCredit with
      | some key =>
          simp only [hs] at h
          split at h <;> try contradiction
          split at h <;> try contradiction
          rw [← Option.some.inj h]
          exact ⟨rfl, rfl, rfl, rfl, by simp [acceptedProjection], rowKeys_replaceRow _ _ _⟩
      | none =>
          simp only [hs] at h
          split at h <;> try contradiction
          rw [← Option.some.inj h]
          exact ⟨rfl, rfl, rfl, rfl, by simp [acceptedProjection], rowKeys_replaceRow _ _ _⟩

theorem reduceReceipt_duplicate_receipt_refused {Receipt Key State Ledger : Type}
    [DecidableEq Key] [DecidableEq State] [DecidableEq Ledger]
    (model : ReceiptModel Receipt Key State Ledger)
    (before : Projection Key State Ledger) (receipt : Receipt)
    (spent : (model.view receipt).receiptId ∈ before.receiptIds) :
    reduceReceipt model before receipt = none := by
  unfold reduceReceipt reduceView
  split
  · cases lookupRow (model.view receipt).subject before.rows <;> simp_all
  · rfl

theorem reduceReceipt_duplicate_credit_refused {Receipt Key State Ledger : Type}
    [DecidableEq Key] [DecidableEq State] [DecidableEq Ledger]
    (model : ReceiptModel Receipt Key State Ledger)
    (before : Projection Key State Ledger) (receipt : Receipt) (key : ReceiptKey)
    (credit : (model.view receipt).settledCredit = some key)
    (activity : (model.view receipt).activity.creditKey? = some key)
    (spent : key ∈ before.settledCredits) :
    reduceReceipt model before receipt = none := by
  unfold reduceReceipt reduceView
  split
  · cases lookupRow (model.view receipt).subject before.rows <;> simp_all
  · rfl

/-! ## Production adapter: existential proof-carrying Attendant receipts -/

/-- One owner-wide stream can carry receipts for any of the owner's attendants.
The dependent package retains the exact `OwnedInstance` against which the
kernel proof was checked. -/
structure OwnerReceipt (oracle : IdentityOracle) (template : Template) where
  owned : OwnedInstance oracle template
  receipt : TransitionReceipt template owned

/-- A locally valid step becomes a candidate for atomic commitment only
together with the exact canonical CAS successor for its tooth/nullifier.  A
Lean value cannot make a host compare-and-swap atomic; the durable store must
append the event and advance its CAS cell in one transaction. -/
structure CanonicalOwnerReceipt (oracle : IdentityOracle) (template : Template) where
  candidate : OwnerReceipt oracle template
  beforeCas : CanonicalCasState
  afterCas : CanonicalCasState
  casApplied : evaluateCasTransition beforeCas
    candidate.receipt.envelope.authority.tooth = some afterCas

/-- Finite exact wire committed at the payload digest boundary.  Function-valued
authority oracles are excluded; their exact binding, digest, finite preimage,
and successful kernel equation are retained. -/
structure AttendantReceiptWire where
  attendantKey : AttendantKey
  instancePolicy : InstancePolicy
  beforeLedger : OwnerLedger
  before : Attendant.Projection
  commandBinding : CommandBinding
  signer : Digest32
  finalizedTurnRoot : Digest32
  commandDigest : Digest32
  cas : CasTransitionIdentity
  beforeCas : CanonicalCasState
  afterCas : CanonicalCasState
  action : ActionPreimage
  result : StepResult
deriving DecidableEq

def ownerReceiptWire {oracle : IdentityOracle} {template : Template}
    (payload : CanonicalOwnerReceipt oracle template) : AttendantReceiptWire where
  attendantKey := payload.candidate.owned.key
  instancePolicy := payload.candidate.owned.policy
  beforeLedger := payload.candidate.receipt.beforeLedger
  before := payload.candidate.receipt.before
  commandBinding := payload.candidate.receipt.envelope.authority.binding
  signer := payload.candidate.receipt.envelope.authority.signer
  finalizedTurnRoot := payload.candidate.receipt.envelope.authority.finalizedTurnRoot
  commandDigest := payload.candidate.receipt.envelope.authority.commandDigest
  cas := payload.candidate.receipt.envelope.authority.tooth.identity
  beforeCas := payload.beforeCas
  afterCas := payload.afterCas
  action := payload.candidate.receipt.envelope.action.preimage
  result := payload.candidate.receipt.result

def activityOfKernelEvent (template : Template) : Attendant.Event → Activity
  | .cared mode key amount => .cared mode key amount
  | .trained key amount => .trained key amount
  | .equipped equipment =>
      .equipped equipment ((template.findEquipment equipment).map EquipmentSpec.capability)
  | .unequipped => .unequipped
  | .deployed authorization => .deployed authorization.mission authorization.equipment
      authorization.capability authorization.strength
  | .returned mission => .returned mission
  | .epochAdvanced epoch => .epochAdvanced epoch

/-- All hash-like functions are named deployment boundaries.  This module
proves no collision resistance, serialization injectivity, or canonical codec
for these functions.  The unbounded production obligation is one canonical
codec covering every field of `AttendantReceiptWire`, the complete genesis
rows/ledger/CAS state, and `EventStatement`, followed by cryptographic digests
with deployment-domain separation. -/
structure Boundary where
  ownerTemplateKey : Digest32 → Digest32 → Digest32
  genesisHead : List (AttendantKey × Attendant.Projection) → OwnerLedger →
    CanonicalCasState → Digest32
  receiptDigest : AttendantReceiptWire → Digest32
  eventDigest : EventSourcing.EventStatement → Digest32

abbrev ATTENDANT_CONTINUITY_STREAM_KIND : Nat := 10

/-- Union of every attendant-local consumed-credit key in a closed roster. -/
def rowConsumedCredits (rows : List (AttendantKey × Attendant.Projection)) :
    Finset ReceiptKey :=
  rows.foldl (fun keys row => keys ∪ row.2.mutable.consumed.keys) ∅

def rowConsumedCreditSets (rows : List (AttendantKey × Attendant.Projection)) :
    List (Finset ReceiptKey) :=
  rows.map (fun row => row.2.mutable.consumed.keys)

/-- A closed-roster checkpoint.  The constructor is opaque: production cannot
splice arbitrary rows into an earlier ledger.  Its future canonical decoder
must be colocated with an audited issuance/opening replay and establish these
proofs.  Until that producer exists, this aggregate is intentionally not a
deployable genesis codec.  Issuance is frozen after this checkpoint because the
reducer preserves the exact row-key list. -/
structure Genesis (template : Template) where
  private mk ::
  rows : List (AttendantKey × Attendant.Projection)
  ledger : OwnerLedger
  canonicalCas : CanonicalCasState
  rowsUnique : (rowKeys rows).Nodup
  closedRoster : (rowKeys rows).toFinset = ledger.issued
  spentCreditsExact : rowConsumedCredits rows = ledger.spentCredits
  spentCreditsDisjoint : (rowConsumedCreditSets rows).Pairwise Disjoint
  casHeadExact : canonicalCas.head = ledger.canonicalHead
  casRevisionExact : canonicalCas.revision = ledger.canonicalRevision
  ledgerFederation : ledger.federationId = template.federationId
  ledgerContent : ledger.contentRoot = template.contentRoot
  ledgerActivation : ledger.activationDigest = template.activationDigest
  ledgerSession : ledger.contentSession = template.contentSession
  rowValid : ∀ row ∈ rows,
    row.1.owner = ledger.owner ∧
      row.1 ∈ ledger.issued ∧
      row.2.attendantKey = row.1 ∧
      row.2.templatePolicy = template.policy ∧
      row.2.federationId = template.federationId ∧
      row.2.contentRoot = template.contentRoot ∧
      row.2.activationDigest = template.activationDigest ∧
      row.2.contentSession = template.contentSession

def streamSpec (boundary : Boundary) (template : Template) (genesis : Genesis template) :
    EventSourcing.StreamSpec where
  aggregate := {
    namespaceId := template.federationId
    kind := ATTENDANT_CONTINUITY_STREAM_KIND
    key := boundary.ownerTemplateKey genesis.ledger.owner template.activationDigest
  }
  version := ⟨template.schemaVersion⟩
  genesisHead := boundary.genesisHead genesis.rows genesis.ledger genesis.canonicalCas

def receiptView {oracle : IdentityOracle} (boundary : Boundary) (template : Template)
    (payload : CanonicalOwnerReceipt oracle template) :
    ReceiptView AttendantKey Attendant.Projection OwnerLedger where
  subject := payload.candidate.owned.key
  receiptId := boundary.receiptDigest (ownerReceiptWire payload)
  beforeState := payload.candidate.receipt.before
  beforeLedger := payload.candidate.receipt.beforeLedger
  afterState := payload.candidate.receipt.result.after
  afterLedger := payload.candidate.receipt.result.afterLedger
  beforeSequence := payload.candidate.receipt.before.sequence.val
  afterSequence := payload.candidate.receipt.result.after.sequence.val
  beforeCounter := payload.candidate.receipt.before.nextCounter.val
  afterCounter := payload.candidate.receipt.result.after.nextCounter.val
  cas := payload.candidate.receipt.envelope.authority.tooth.identity
  beforeCas := payload.beforeCas
  afterCas := payload.afterCas
  activity := activityOfKernelEvent template payload.candidate.receipt.result.event
  settledCredit := payload.candidate.receipt.result.allocation.map CreditAllocation.receiptKey

def receiptModel {oracle : IdentityOracle} (boundary : Boundary) (template : Template) :
    ReceiptModel (CanonicalOwnerReceipt oracle template) AttendantKey
      Attendant.Projection OwnerLedger where
  view := receiptView boundary template

def wireDigestBoundary (boundary : Boundary) :
    EventSourcing.DigestBoundary AttendantReceiptWire where
  payloadDigest := boundary.receiptDigest
  eventDigest := boundary.eventDigest

def initialProjection {template : Template} (genesis : Genesis template) :
    Projection AttendantKey Attendant.Projection OwnerLedger :=
  { Projection.initial genesis.rows genesis.ledger genesis.canonicalCas with
    settledCredits := genesis.ledger.spentCredits }

/-- Full production aggregate invariant.  In addition to exact replay fields,
no credit may appear in two attendant-local histories, the frozen roster is the
ledger's exact issued set, and the canonical CAS cell is the ledger head. -/
def aggregateAligned
    (state : Projection AttendantKey Attendant.Projection OwnerLedger) : Bool :=
  decide (
    (rowKeys state.rows).Nodup ∧
    (rowKeys state.rows).toFinset = state.liveLedger.issued ∧
    rowConsumedCredits state.rows = state.liveLedger.spentCredits ∧
    (rowConsumedCreditSets state.rows).Pairwise Disjoint ∧
    state.canonicalCas.head = state.liveLedger.canonicalHead ∧
    state.canonicalCas.revision = state.liveLedger.canonicalRevision)

theorem initialProjection_aligned {template : Template} (genesis : Genesis template) :
    aggregateAligned (initialProjection genesis) = true := by
  simp only [aggregateAligned, decide_eq_true_eq]
  exact ⟨genesis.rowsUnique, genesis.closedRoster, genesis.spentCreditsExact,
    genesis.spentCreditsDisjoint, genesis.casHeadExact, genesis.casRevisionExact⟩

/-- Recovery re-verifies a finite persisted wire into an actual kernel receipt.
The proof rules out an adapter that maps wire A to an otherwise-valid receipt B;
the reducer repeats that comparison at runtime before accepting the successor. -/
structure WireVerifier (oracle : IdentityOracle) (template : Template) where
  verify : AttendantReceiptWire → Option (CanonicalOwnerReceipt oracle template)
  wireExact : ∀ wire payload, verify wire = some payload → ownerReceiptWire payload = wire

def reduceWireReceipt {oracle : IdentityOracle} (boundary : Boundary)
    (template : Template) (verifier : WireVerifier oracle template) :
    EventSourcing.Reducer
      (Projection AttendantKey Attendant.Projection OwnerLedger) AttendantReceiptWire :=
  fun before wire => do
    if aggregateAligned before then
      let payload ← verifier.verify wire
      if ownerReceiptWire payload != wire then none
      else do
        let after ← reduceReceipt (receiptModel boundary template) before payload
        if aggregateAligned after then some after else none
    else none

abbrev AttendantEnvelope := EventSourcing.EventEnvelope AttendantReceiptWire

/-! ## Snapshot caches that cannot become authority -/

/-- A snapshot sealed to the exact spec, digest boundary, reducer, genesis, and
prefix that produced it.  The constructor is private; persisted raw caches must
pass `revalidateSnapshotCandidate` before they can reach `resumeCertified`. -/
structure CertifiedSnapshot {State Payload : Type}
    (spec : EventSourcing.StreamSpec)
    (digests : EventSourcing.DigestBoundary Payload)
    (reduce : EventSourcing.Reducer State Payload) (initial : State) where
  private mk ::
  leading : List (EventSourcing.EventEnvelope Payload)
  snapshot : EventSourcing.Snapshot State

def certifySnapshot {State Payload : Type} (spec : EventSourcing.StreamSpec)
    (digests : EventSourcing.DigestBoundary Payload)
    (reduce : EventSourcing.Reducer State Payload) (initial : State)
    (leading : List (EventSourcing.EventEnvelope Payload)) :
    Except EventSourcing.Error (CertifiedSnapshot spec digests reduce initial) :=
  (EventSourcing.snapshotPrefix spec digests reduce initial leading).map
    fun snapshot => ⟨leading, snapshot⟩

/-- Raw persisted cache admission.  Cursor-only checking is insufficient: the
complete projection is compared against exact prefix replay, including CAS,
receipt IDs, and spent-credit indexes. -/
def revalidateSnapshotCandidate {State Payload : Type} [DecidableEq State]
    (spec : EventSourcing.StreamSpec)
    (digests : EventSourcing.DigestBoundary Payload)
    (reduce : EventSourcing.Reducer State Payload) (initial : State)
    (leading : List (EventSourcing.EventEnvelope Payload))
    (candidate : EventSourcing.Snapshot State) :
    Except EventSourcing.Error (CertifiedSnapshot spec digests reduce initial) :=
  match EventSourcing.snapshotPrefix spec digests reduce initial leading with
  | .error error => .error error
  | .ok actual =>
      if actual == candidate then
        .ok {
          leading
          snapshot := candidate
        }
      else .error .reducerRejected

def resumeCertified {State Payload : Type} (spec : EventSourcing.StreamSpec)
    (digests : EventSourcing.DigestBoundary Payload)
    (reduce : EventSourcing.Reducer State Payload) (initial : State)
    (snapshot : CertifiedSnapshot spec digests reduce initial)
    (suffix : List (EventSourcing.EventEnvelope Payload)) :
    Except EventSourcing.Error (EventSourcing.ReplayState State) :=
  EventSourcing.resumeSnapshot spec digests reduce snapshot.snapshot suffix

/- `Except`'s bind and map on a constructor, as rewrite rules: under v4.35's transparency
`simp` no longer unfolds the `Monad (Except ε)` instance to reach them. -/
private theorem except_bind_error {ε α β : Type _} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl
private theorem except_bind_ok {ε α β : Type _} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
private theorem except_map_error {ε α β : Type _} (g : α → β) (e : ε) :
    Except.map g (Except.error e : Except ε α) = Except.error e := rfl
private theorem except_map_ok {ε α β : Type _} (g : α → β) (a : α) :
    Except.map g (Except.ok a : Except ε α) = Except.ok (g a) := rfl

theorem certify_then_resume_cache_equivalence {State Payload : Type}
    (spec : EventSourcing.StreamSpec)
    (digests : EventSourcing.DigestBoundary Payload)
    (reduce : EventSourcing.Reducer State Payload) (initial : State)
    (leading : List (EventSourcing.EventEnvelope Payload))
    (suffix : List (EventSourcing.EventEnvelope Payload)) :
    (do
      let snapshot ← certifySnapshot spec digests reduce initial leading
      resumeCertified spec digests reduce initial snapshot suffix) =
      EventSourcing.rebuild spec digests reduce initial (leading ++ suffix) := by
  cases hprefix : EventSourcing.snapshotPrefix spec digests reduce initial leading with
  | error error =>
      have exact := EventSourcing.snapshot_cache_equivalence spec digests reduce initial
        leading suffix
      rw [hprefix] at exact
      simpa [certifySnapshot, hprefix, except_bind_error, except_map_error] using exact
  | ok snapshot =>
      have exact := EventSourcing.snapshot_cache_equivalence spec digests reduce initial
        leading suffix
      rw [hprefix] at exact
      simpa [certifySnapshot, hprefix, resumeCertified, except_bind_ok, except_map_ok] using exact

abbrev AttendantCertifiedSnapshot {oracle : IdentityOracle}
    (boundary : Boundary) (template : Template) (genesis : Genesis template)
    (verifier : WireVerifier oracle template) :=
  CertifiedSnapshot (streamSpec boundary template genesis) (wireDigestBoundary boundary)
    (reduceWireReceipt boundary template verifier) (initialProjection genesis)

def rebuild {oracle : IdentityOracle} (boundary : Boundary) (template : Template)
    (genesis : Genesis template) (verifier : WireVerifier oracle template)
    (events : List AttendantEnvelope) :
    Except EventSourcing.Error
      (EventSourcing.ReplayState
        (Projection AttendantKey Attendant.Projection OwnerLedger)) :=
  EventSourcing.rebuild (streamSpec boundary template genesis)
    (wireDigestBoundary boundary)
    (reduceWireReceipt boundary template verifier)
    (initialProjection genesis) events

def snapshotPrefix {oracle : IdentityOracle} (boundary : Boundary) (template : Template)
    (genesis : Genesis template) (verifier : WireVerifier oracle template)
    (events : List AttendantEnvelope) :
    Except EventSourcing.Error
      (AttendantCertifiedSnapshot boundary template genesis verifier) :=
  certifySnapshot (streamSpec boundary template genesis)
    (wireDigestBoundary boundary)
    (reduceWireReceipt boundary template verifier)
    (initialProjection genesis) events

def revalidateSnapshot {oracle : IdentityOracle} (boundary : Boundary)
    (template : Template) (genesis : Genesis template)
    (verifier : WireVerifier oracle template) (leading : List AttendantEnvelope)
    (candidate : EventSourcing.Snapshot
      (Projection AttendantKey Attendant.Projection OwnerLedger)) :
    Except EventSourcing.Error
      (AttendantCertifiedSnapshot boundary template genesis verifier) :=
  revalidateSnapshotCandidate (streamSpec boundary template genesis)
    (wireDigestBoundary boundary)
    (reduceWireReceipt boundary template verifier)
    (initialProjection genesis) leading candidate

def resumeSnapshot {oracle : IdentityOracle} (boundary : Boundary) (template : Template)
    (genesis : Genesis template) (verifier : WireVerifier oracle template)
    (snapshot : AttendantCertifiedSnapshot boundary template genesis verifier)
    (events : List AttendantEnvelope) :
    Except EventSourcing.Error
      (EventSourcing.ReplayState
        (Projection AttendantKey Attendant.Projection OwnerLedger)) :=
  resumeCertified (streamSpec boundary template genesis)
    (wireDigestBoundary boundary)
    (reduceWireReceipt boundary template verifier) (initialProjection genesis) snapshot events

theorem production_reduce_uses_exact_kernel_successor {oracle : IdentityOracle}
    (boundary : Boundary) (template : Template)
    (before after : Projection AttendantKey Attendant.Projection OwnerLedger)
    (payload : CanonicalOwnerReceipt oracle template)
    (h : reduceReceipt (receiptModel boundary template) before payload = some after) :
    after.rows = replaceRow payload.candidate.owned.key
        payload.candidate.receipt.result.after before.rows ∧
      after.liveLedger = payload.candidate.receipt.result.afterLedger ∧
      after.canonicalCas = payload.afterCas ∧
      after.receiptCount = before.receiptCount + 1 ∧
      rowKeys after.rows = rowKeys before.rows := by
  have exact := reduceReceipt_success_exact
    (receiptModel boundary template) before after payload h
  exact ⟨exact.1, exact.2.1, exact.2.2.1, exact.2.2.2.1,
    exact.2.2.2.2.2⟩

theorem production_receipt_is_kernel_authorized {oracle : IdentityOracle}
    {template : Template} (payload : CanonicalOwnerReceipt oracle template) :
    evaluateAuthenticatedStepCandidate template payload.candidate.owned
      payload.candidate.receipt.beforeLedger payload.candidate.receipt.before
      payload.candidate.receipt.envelope = some payload.candidate.receipt.result :=
  payload.candidate.receipt.applied

theorem production_receipt_has_valid_canonical_successor {oracle : IdentityOracle}
    {template : Template} (payload : CanonicalOwnerReceipt oracle template) :
    evaluateCasTransition payload.beforeCas
      payload.candidate.receipt.envelope.authority.tooth = some payload.afterCas :=
  payload.casApplied

theorem production_receipt_records_nullifier_and_fresh_head {oracle : IdentityOracle}
    {template : Template} (payload : CanonicalOwnerReceipt oracle template) :
    payload.candidate.receipt.envelope.authority.tooth.nullifier ∈
        payload.afterCas.consumedNullifiers ∧
      payload.candidate.receipt.envelope.authority.tooth.nextHead ≠
        payload.candidate.receipt.envelope.authority.tooth.expectedHead := by
  have exact := evaluateCasTransition_records_successor payload.casApplied
  exact ⟨exact.2.2.1, exact.2.2.2.2⟩

theorem production_receipt_nullifier_was_fresh {oracle : IdentityOracle}
    {template : Template} (payload : CanonicalOwnerReceipt oracle template) :
    payload.candidate.receipt.envelope.authority.tooth.nullifier ∉
      payload.beforeCas.consumedNullifiers := by
  have valid := evaluateCasTransition_implies_wire_valid payload.beforeCas payload.afterCas
    payload.candidate.receipt.envelope.authority.tooth payload.casApplied
  simp only [casTransitionWireValid, decide_eq_true_eq] at valid
  exact valid.2.2.2.2.1

theorem production_wire_success_has_exact_kernel_witness {oracle : IdentityOracle}
    (boundary : Boundary) (template : Template) (verifier : WireVerifier oracle template)
    (before after : Projection AttendantKey Attendant.Projection OwnerLedger)
    (wire : AttendantReceiptWire)
    (h : reduceWireReceipt boundary template verifier before wire = some after) :
    ∃ payload : CanonicalOwnerReceipt oracle template,
      verifier.verify wire = some payload ∧
      ownerReceiptWire payload = wire ∧
      reduceReceipt (receiptModel boundary template) before payload = some after := by
  unfold reduceWireReceipt at h
  cases hv : verifier.verify wire with
  | none => simp [hv] at h
  | some payload =>
      have exactWire := verifier.wireExact wire payload hv
      refine ⟨payload, rfl, exactWire, ?_⟩
      simp [hv, exactWire] at h
      have reduced := h.2
      cases hr : reduceReceipt (receiptModel boundary template) before payload with
      | none => simp [hr] at reduced
      | some produced =>
          rw [hr] at reduced
          cases ha : aggregateAligned produced with
          | false => simp [ha] at reduced
          | true =>
              have same := Option.some.inj (by simpa [ha] using reduced)
              exact congrArg some same

theorem reduceWireReceipt_success_aligned {oracle : IdentityOracle}
    (boundary : Boundary) (template : Template) (verifier : WireVerifier oracle template)
    (before after : Projection AttendantKey Attendant.Projection OwnerLedger)
    (wire : AttendantReceiptWire)
    (h : reduceWireReceipt boundary template verifier before wire = some after) :
    aggregateAligned before = true ∧ aggregateAligned after = true := by
  rcases production_wire_success_has_exact_kernel_witness boundary template verifier
    before after wire h with ⟨payload, verified, exactWire, reduced⟩
  unfold reduceWireReceipt at h
  simpa [verified, exactWire, reduced] using h

/-- The production reducer is a preservation gate, not merely a successor
cache: every success keeps the frozen row-key order and re-establishes the
closed roster, exact spent-credit union, pairwise disjoint local histories,
and ledger/CAS head alignment. -/
theorem production_success_preserves_aggregate_invariants {oracle : IdentityOracle}
    (boundary : Boundary) (template : Template) (verifier : WireVerifier oracle template)
    (before after : Projection AttendantKey Attendant.Projection OwnerLedger)
    (wire : AttendantReceiptWire)
    (h : reduceWireReceipt boundary template verifier before wire = some after) :
    rowKeys after.rows = rowKeys before.rows ∧
      (rowKeys after.rows).toFinset = after.liveLedger.issued ∧
      rowConsumedCredits after.rows = after.liveLedger.spentCredits ∧
      (rowConsumedCreditSets after.rows).Pairwise Disjoint ∧
      after.canonicalCas.head = after.liveLedger.canonicalHead ∧
      after.canonicalCas.revision = after.liveLedger.canonicalRevision := by
  rcases production_wire_success_has_exact_kernel_witness boundary template verifier
    before after wire h with ⟨payload, _, _, reduced⟩
  have exact := reduceReceipt_success_exact
    (receiptModel boundary template) before after payload reduced
  have aligned := (reduceWireReceipt_success_aligned boundary template verifier
    before after wire h).2
  simp only [aggregateAligned, decide_eq_true_eq] at aligned
  exact ⟨exact.2.2.2.2.2, aligned.2.1, aligned.2.2.1, aligned.2.2.2.1,
    aligned.2.2.2.2.1, aligned.2.2.2.2.2⟩

theorem production_receipt_preserves_companion_identity {oracle : IdentityOracle}
    {template : Template} (payload : CanonicalOwnerReceipt oracle template) :
    payload.candidate.receipt.result.after.attendantKey =
        payload.candidate.receipt.before.attendantKey ∧
      payload.candidate.receipt.result.after.instancePolicy =
        payload.candidate.receipt.before.instancePolicy := by
  exact ⟨payload.candidate.receipt.identity_domain_preserved.1,
    continuity_identity_survives_transition payload.candidate.receipt⟩

theorem production_snapshot_recovery_exact {oracle : IdentityOracle}
    (boundary : Boundary) (template : Template) (genesis : Genesis template)
    (verifier : WireVerifier oracle template)
    (leading suffix : List AttendantEnvelope) :
    (do
      let snapshot ← snapshotPrefix boundary template genesis verifier leading
      resumeSnapshot boundary template genesis verifier snapshot suffix) =
      rebuild boundary template genesis verifier (leading ++ suffix) := by
  exact certify_then_resume_cache_equivalence
    (streamSpec boundary template genesis)
    (wireDigestBoundary boundary)
    (reduceWireReceipt boundary template verifier)
    (initialProjection genesis) leading suffix

/-! ## Closed executable cross-companion hostile replay suite

⚑ **THE SUITE NO LONGER EVALUATES IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here made every
game-fixture regression a hard failure of every Rust proving target. The suite's
STATEMENTS stay here, each as an evaluation-free `check_* : Bool` definition beside the
private mock fixtures; the EVALUATION — each `check_* = true`, pinned by `native_decide` +
`#assert_compiled` — lives in `AttendantContinuityAggregateFixtures.lean`, rooted in the
`PathOfAngelsGuards` library: a plain `lake build` still runs every pin, and a stale
fixture reds the guard library instead of the archive. The hostile checks pin the EXACT
refusal error, which refutes acceptance by construction; the snapshot probes were already
fail-closed Bools. Named residue: none — every evaluation moved. -/

private def digestByte (n : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨n % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def receiptKey (counter : Nat) : ReceiptKey where
  federationId := digestByte 7
  contentSession := digestByte 8
  contentEpoch := ⟨3⟩
  playerKey := digestByte 9
  playerCounter := counter

private structure MockReceipt where
  tag : Nat
  view : ReceiptView Nat Nat Nat
deriving DecidableEq

private def mockModel : ReceiptModel MockReceipt Nat Nat Nat where
  view := MockReceipt.view

private def mockSpec : EventSourcing.StreamSpec where
  aggregate := {
    namespaceId := digestByte 1
    kind := ATTENDANT_CONTINUITY_STREAM_KIND
    key := digestByte 2
  }
  version := ⟨4⟩
  genesisHead := digestByte 44

private def mockDigests : EventSourcing.DigestBoundary MockReceipt where
  payloadDigest receipt := digestByte (80 + receipt.tag)
  eventDigest statement := digestByte (120 + statement.sequence)

private def mockCas0 : CanonicalCasState where
  head := digestByte 30
  revision := 0
  consumedNullifiers := ∅

private def mockCasIdentity (before : CanonicalCasState) (next nullifier : Nat) :
    CasTransitionIdentity where
  expectedHead := before.head
  nextHead := digestByte next
  expectedRevision := before.revision
  nextRevision := before.revision + 1
  finalizedRoot := digestByte (next + 40)
  nullifier := digestByte nullifier

private def mockCasAfter (before : CanonicalCasState) (identity : CasTransitionIdentity) :
    CanonicalCasState where
  head := identity.nextHead
  revision := identity.nextRevision
  consumedNullifiers := insert identity.nullifier before.consumedNullifiers

private def careCas := mockCasIdentity mockCas0 31 71
private def mockCas1 := mockCasAfter mockCas0 careCas
private def equipCas := mockCasIdentity mockCas1 32 72
private def mockCas2 := mockCasAfter mockCas1 equipCas
private def maintenanceCas := mockCasIdentity mockCas2 33 73
private def mockCas3 := mockCasAfter mockCas2 maintenanceCas

private def mockInitial : Projection Nat Nat Nat :=
  Projection.initial [(10, 0), (11, 50)] 0 mockCas0

private def careReceipt : MockReceipt where
  tag := 1
  view := {
    subject := 10
    receiptId := digestByte 61
    beforeState := 0
    beforeLedger := 0
    afterState := 1
    afterLedger := 1
    beforeSequence := 0
    afterSequence := 1
    beforeCounter := 0
    afterCounter := 1
    cas := careCas
    beforeCas := mockCas0
    afterCas := mockCas1
    activity := .cared .recharge (receiptKey 1) 5
    settledCredit := some (receiptKey 1)
  }

private def equipReceipt : MockReceipt where
  tag := 2
  view := {
    subject := 10
    receiptId := digestByte 62
    beforeState := 1
    beforeLedger := 1
    afterState := 2
    afterLedger := 2
    beforeSequence := 1
    afterSequence := 2
    beforeCounter := 1
    afterCounter := 2
    cas := equipCas
    beforeCas := mockCas1
    afterCas := mockCas2
    activity := .equipped ⟨3⟩ (some .survey)
    settledCredit := none
  }

private def maintenanceReceipt : MockReceipt where
  tag := 3
  view := {
    subject := 11
    receiptId := digestByte 63
    beforeState := 50
    beforeLedger := 2
    afterState := 51
    afterLedger := 3
    beforeSequence := 0
    afterSequence := 1
    beforeCounter := 0
    afterCounter := 1
    cas := maintenanceCas
    beforeCas := mockCas2
    afterCas := mockCas3
    activity := .cared .repair (receiptKey 2) 7
    settledCredit := some (receiptKey 2)
  }

private def mockEnvelope (sequence : Nat) (predecessor : Digest32)
    (receipt : MockReceipt) : EventSourcing.EventEnvelope MockReceipt :=
  let statement : EventSourcing.EventStatement := {
    aggregate := mockSpec.aggregate
    version := mockSpec.version
    sequence
    predecessor
    payloadDigest := mockDigests.payloadDigest receipt
  }
  { statement, payload := receipt, eventDigest := mockDigests.eventDigest statement }

private def eventOne := mockEnvelope 1 mockSpec.genesisHead careReceipt
private def eventTwo := mockEnvelope 2 eventOne.eventDigest equipReceipt
private def eventThree := mockEnvelope 3 eventTwo.eventDigest maintenanceReceipt

private structure MockSummary where
  attendantTen : Option Nat
  attendantEleven : Option Nat
  liveLedger : Nat
  receiptCount : Nat
  careCount : Nat
  maintenanceCount : Nat
  equipmentSeen : Nat
  capabilitiesSeen : Nat
  settledCredits : Nat
  receipts : Nat
  lastSubject : Option Nat
  casRevision : Nat
  casNullifiers : Nat
deriving DecidableEq, Repr

private def mockSummary (state : Projection Nat Nat Nat) : MockSummary where
  attendantTen := lookupRow 10 state.rows
  attendantEleven := lookupRow 11 state.rows
  liveLedger := state.liveLedger
  receiptCount := state.receiptCount
  careCount := state.careCount
  maintenanceCount := state.maintenanceCount
  equipmentSeen := state.equipmentSeen.card
  capabilitiesSeen := state.capabilitiesSeen.card
  settledCredits := state.settledCredits.card
  receipts := state.receiptIds.card
  lastSubject := state.lastSubject
  casRevision := state.canonicalCas.revision
  casNullifiers := state.canonicalCas.consumedNullifiers.card

private def mockRebuild (events : List (EventSourcing.EventEnvelope MockReceipt)) :=
  EventSourcing.rebuild mockSpec mockDigests (reduceReceipt mockModel) mockInitial events

private def denseRecoveryExpected : MockSummary where
  attendantTen := some 2
  attendantEleven := some 51
  liveLedger := 3
  receiptCount := 3
  careCount := 2
  maintenanceCount := 1
  equipmentSeen := 1
  capabilitiesSeen := 1
  settledCredits := 2
  receipts := 3
  lastSubject := some 11
  casRevision := 3
  casNullifiers := 3

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_dense_cross_companion_recovery : Bool :=
  decide ((mockRebuild [eventOne, eventTwo, eventThree]).map
    (fun state => mockSummary state.projection) = .ok denseRecoveryExpected)

private def forgedTransplantReceipt : MockReceipt :=
  { maintenanceReceipt with tag := 4, view := {
      maintenanceReceipt.view with
      receiptId := digestByte 64
      beforeState := 2
      settledCredit := some (receiptKey 4)
      activity := .cared .repair (receiptKey 4) 7
    } }

private def staleLedgerReceipt : MockReceipt :=
  { maintenanceReceipt with tag := 5, view := {
      maintenanceReceipt.view with
      receiptId := digestByte 65
      beforeLedger := 1
      settledCredit := some (receiptKey 5)
      activity := .cared .repair (receiptKey 5) 7
    } }

private def duplicateReceipt : MockReceipt :=
  { maintenanceReceipt with tag := 6, view := {
      maintenanceReceipt.view with
      receiptId := careReceipt.view.receiptId
      settledCredit := some (receiptKey 6)
      activity := .cared .repair (receiptKey 6) 7
    } }

private def duplicateCreditReceipt : MockReceipt :=
  { maintenanceReceipt with tag := 7, view := {
      maintenanceReceipt.view with
      receiptId := digestByte 67
      settledCredit := careReceipt.view.settledCredit
      activity := .cared .repair (receiptKey 1) 7
    } }

private def unknownCompanionReceipt : MockReceipt :=
  { maintenanceReceipt with tag := 8, view := {
      maintenanceReceipt.view with
      subject := 12
      receiptId := digestByte 68
      settledCredit := some (receiptKey 8)
      activity := .cared .repair (receiptKey 8) 7
    } }

private def skippedLocalSequenceReceipt : MockReceipt :=
  { maintenanceReceipt with tag := 9, view := {
      maintenanceReceipt.view with
      receiptId := digestByte 69
      afterSequence := 2
      settledCredit := some (receiptKey 9)
      activity := .cared .repair (receiptKey 9) 7
    } }

private def reusedNullifierCas := mockCasIdentity mockCas2 34 71
private def reusedNullifierAfter := mockCasAfter mockCas2 reusedNullifierCas

private def reusedNullifierReceipt : MockReceipt :=
  { maintenanceReceipt with tag := 10, view := {
      maintenanceReceipt.view with
      receiptId := digestByte 70
      cas := reusedNullifierCas
      afterCas := reusedNullifierAfter
      settledCredit := some (receiptKey 10)
      activity := .cared .repair (receiptKey 10) 7
    } }

private def mismatchedBeforeCasIdentity := mockCasIdentity mockCas1 35 75
private def mismatchedBeforeCasAfter := mockCasAfter mockCas1 mismatchedBeforeCasIdentity

private def mismatchedBeforeCasReceipt : MockReceipt :=
  { maintenanceReceipt with tag := 11, view := {
      maintenanceReceipt.view with
      receiptId := digestByte 71
      cas := mismatchedBeforeCasIdentity
      beforeCas := mockCas1
      afterCas := mismatchedBeforeCasAfter
      settledCredit := some (receiptKey 11)
      activity := .cared .repair (receiptKey 11) 7
    } }

private def sameHeadCas : CasTransitionIdentity where
  expectedHead := mockCas2.head
  nextHead := mockCas2.head
  expectedRevision := mockCas2.revision
  nextRevision := mockCas2.revision + 1
  finalizedRoot := digestByte 199
  nullifier := digestByte 76

private def sameHeadAfter := mockCasAfter mockCas2 sameHeadCas

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_gap_refused : Bool :=
  decide (mockRebuild [eventTwo] = .error (.wrongSequence 1 2))

private def wrongPredecessorEnvelope : EventSourcing.EventEnvelope MockReceipt :=
  { eventTwo with statement := {
    eventTwo.statement with predecessor := digestByte 200 } }

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_wrong_predecessor_refused : Bool :=
  decide (mockRebuild [eventOne, wrongPredecessorEnvelope] = .error .wrongPredecessor)

private def payloadSubstitutionEnvelope : EventSourcing.EventEnvelope MockReceipt :=
  { eventThree with payload := forgedTransplantReceipt }

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_payload_substitution_refused : Bool :=
  decide (mockRebuild [eventOne, eventTwo, payloadSubstitutionEnvelope] =
    .error .wrongPayloadDigest)

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_cross_companion_prestate_transplant_refused : Bool :=
  decide (mockRebuild [eventOne, eventTwo,
    mockEnvelope 3 eventTwo.eventDigest forgedTransplantReceipt] = .error .reducerRejected)

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_stale_owner_ledger_refused : Bool :=
  decide (mockRebuild [eventOne, eventTwo,
    mockEnvelope 3 eventTwo.eventDigest staleLedgerReceipt] = .error .reducerRejected)

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_duplicate_receipt_refused : Bool :=
  decide (mockRebuild [eventOne, eventTwo,
    mockEnvelope 3 eventTwo.eventDigest duplicateReceipt] = .error .reducerRejected)

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_duplicate_settled_credit_refused : Bool :=
  decide (mockRebuild [eventOne, eventTwo,
    mockEnvelope 3 eventTwo.eventDigest duplicateCreditReceipt] = .error .reducerRejected)

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_unknown_companion_refused : Bool :=
  decide (mockRebuild [eventOne, eventTwo,
    mockEnvelope 3 eventTwo.eventDigest unknownCompanionReceipt] = .error .reducerRejected)

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_skipped_local_sequence_refused : Bool :=
  decide (mockRebuild [eventOne, eventTwo,
    mockEnvelope 3 eventTwo.eventDigest skippedLocalSequenceReceipt] = .error .reducerRejected)

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_production_boundary_reused_nullifier_refused : Bool :=
  !(casTransitionWireValid mockCas2 reusedNullifierCas reusedNullifierAfter)

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_production_boundary_same_head_successor_refused : Bool :=
  !(casTransitionWireValid mockCas2 sameHeadCas sameHeadAfter)

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_reused_global_nullifier_refused : Bool :=
  decide (mockRebuild [eventOne, eventTwo,
    mockEnvelope 3 eventTwo.eventDigest reusedNullifierReceipt] = .error .reducerRejected)

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_canonical_state_mismatch_refused : Bool :=
  decide (mockRebuild [eventOne, eventTwo,
    mockEnvelope 3 eventTwo.eventDigest mismatchedBeforeCasReceipt] = .error .reducerRejected)

private def duplicateRowTable : Projection Nat Nat Nat :=
  Projection.initial [(10, 0), (10, 7), (11, 50)] 0 mockCas0

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_duplicate_row_table_refused : Bool :=
  decide (EventSourcing.rebuild mockSpec mockDigests (reduceReceipt mockModel)
    duplicateRowTable [eventOne] = .error .reducerRejected)

private def certifiedRecoveryProbe :
    Except EventSourcing.Error (EventSourcing.ReplayState (Projection Nat Nat Nat)) := do
  let snapshot ← certifySnapshot mockSpec mockDigests (reduceReceipt mockModel)
    mockInitial [eventOne, eventTwo]
  resumeCertified mockSpec mockDigests (reduceReceipt mockModel)
    mockInitial snapshot [eventThree]

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_certified_snapshot_recovery_matches_genesis_replay : Bool :=
  decide (certifiedRecoveryProbe = mockRebuild [eventOne, eventTwo, eventThree])

private def oldSnapshotClaimingLongerPrefixIsRejected : Bool :=
  match EventSourcing.snapshotPrefix mockSpec mockDigests (reduceReceipt mockModel)
      mockInitial [eventOne] with
  | .error _ => false
  | .ok old =>
      match revalidateSnapshotCandidate mockSpec mockDigests (reduceReceipt mockModel)
          mockInitial [eventOne, eventTwo] old with
      | .error .reducerRejected => true
      | _ => false

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_old_snapshot_empty_suffix_refused : Bool :=
  oldSnapshotClaimingLongerPrefixIsRejected

private def resetSpendSnapshotIsRejected : Bool :=
  match EventSourcing.snapshotPrefix mockSpec mockDigests (reduceReceipt mockModel)
      mockInitial [eventOne, eventTwo] with
  | .error _ => false
  | .ok actual =>
      let resetProjection := {
        actual.projection with settledCredits := ∅, receiptIds := ∅ }
      let forged := { actual with projection := resetProjection }
      match revalidateSnapshotCandidate mockSpec mockDigests (reduceReceipt mockModel)
          mockInitial [eventOne, eventTwo] forged with
      | .error .reducerRejected => true
      | _ => false

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_reset_spend_and_receipt_sets_snapshot_refused : Bool :=
  resetSpendSnapshotIsRejected

private def resetCanonicalCasSnapshotIsRejected : Bool :=
  match EventSourcing.snapshotPrefix mockSpec mockDigests (reduceReceipt mockModel)
      mockInitial [eventOne, eventTwo] with
  | .error _ => false
  | .ok actual =>
      let forged := { actual with projection := {
        actual.projection with canonicalCas := mockCas1 } }
      match revalidateSnapshotCandidate mockSpec mockDigests (reduceReceipt mockModel)
          mockInitial [eventOne, eventTwo] forged with
      | .error .reducerRejected => true
      | _ => false

/-- (Pinned `= true` in `AttendantContinuityAggregateFixtures`.) -/
def check_hostile_reset_canonical_cas_snapshot_refused : Bool :=
  resetCanonicalCasSnapshotIsRejected

#assert_axioms lookupRow_replaceRow_self
#assert_axioms rowKeys_replaceRow
#assert_axioms evaluateCasTransition_implies_wire_valid
#assert_axioms reduceReceipt_success_exact
#assert_axioms reduceReceipt_duplicate_receipt_refused
#assert_axioms reduceReceipt_duplicate_credit_refused
#assert_axioms initialProjection_aligned
#assert_axioms production_reduce_uses_exact_kernel_successor
#assert_axioms production_receipt_is_kernel_authorized
#assert_axioms production_receipt_has_valid_canonical_successor
#assert_axioms production_receipt_records_nullifier_and_fresh_head
#assert_axioms production_receipt_nullifier_was_fresh
#assert_axioms production_wire_success_has_exact_kernel_witness
#assert_axioms reduceWireReceipt_success_aligned
#assert_axioms production_success_preserves_aggregate_invariants
#assert_axioms production_receipt_preserves_companion_identity
#assert_axioms production_snapshot_recovery_exact
#assert_axioms certify_then_resume_cache_equivalence

-- The nineteen suite pins (`#assert_compiled` + `native_decide`) live in
-- `AttendantContinuityAggregateFixtures.lean`, rooted in `PathOfAngelsGuards` — see the
-- suite header above.

end Dregg2.Games.PathOfAngels.AttendantContinuityAggregate
