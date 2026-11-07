/-
# EventBatch — the fixture EVALUATION, out of the crypto archive's build

`EventBatch.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its fixtures ran thirteen `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace.
The fixtures' STATEMENTS remain in `EventBatch.lean` as evaluation-free `check_* : Bool`
definitions, beside the private fixture material they must see; THIS module is where they
are RUN. It is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI`
by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The hostile checks pin the EXACT refusal error,
which refutes acceptance by construction. Named residue: none.
-/
import Dregg2.Games.PathOfAngels.EventBatch
import Batteries.Tactic.OpenPrivate

namespace Dregg2.Games.PathOfAngels.EventBatch

set_option autoImplicit false
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.EventSourcing
-- The laboratory reads these runtime helpers; they stay private to the runtime module.
open private digestByte event fixtureBoundary fixtureWorld stream zeroDigest from Dregg2.Games.PathOfAngels.EventBatch

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

private def fixtureCoordinate : FinalizedTurnCoordinate where
  world := fixtureWorld
  commitOrdinal := 7
  blockId := digestByte 8
  turnHash := digestByte 9
  receiptHash := digestByte 10
  actorRoot := digestByte 11
  signer := digestByte 12

private def initialHead (kind key genesis : Nat) : StreamHead where
  stream := stream kind key
  sequence := 0
  head := digestByte genesis

private def canonHead := initialHead 2 20 30
private def attendantHead := initialHead 10 21 31
private def firstCanon := event 0 canonHead.stream 1 30 40
private def attendant := event 1 attendantHead.stream 1 31 41
private def secondCanon := event 2 canonHead.stream 2 103 42

private def fixtureStatement : Statement where
  coordinate := fixtureCoordinate
  events := [firstCanon, attendant, secondCanon]

private def fixtureEnvelope : Envelope where
  statement := fixtureStatement
  batchDigest := fixtureBoundary.batchDigest fixtureStatement

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_fixture_cross_aggregate_batch_accepts : Bool :=
  (applyBatch fixtureBoundary [canonHead, attendantHead] fixtureEnvelope).isOk

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_fixture_repeated_stream_is_explicitly_chained : Bool :=
  decide ((applyBatch fixtureBoundary [canonHead, attendantHead] fixtureEnvelope).map
    (fun applied =>
      (headFor? applied.successorHeads canonHead.stream).map StreamHead.sequence) =
    .ok (some 2))

private def fixtureSuccessorHeads : List StreamHead :=
  [ { stream := canonHead.stream, sequence := 2, head := secondCanon.eventDigest }
  , { stream := attendantHead.stream, sequence := 1, head := attendant.eventDigest } ]

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_fixture_cross_aggregate_successors_are_exact : Bool :=
  decide (applyBatch fixtureBoundary [canonHead, attendantHead] fixtureEnvelope =
    .ok {
      coordinate := fixtureCoordinate
      batchDigest := fixtureEnvelope.batchDigest
      events := fixtureStatement.events
      successorHeads := fixtureSuccessorHeads
    })

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_hostile_semantic_reapplication_refused : Bool :=
  decide (applyBatch fixtureBoundary fixtureSuccessorHeads fixtureEnvelope =
    .error .wrongSequence)

private def gapEvent : IndexedEvent :=
  { secondCanon with statement := { secondCanon.statement with sequence := 3 } }

private def gapStatement : Statement :=
  { fixtureStatement with events := [firstCanon, attendant, gapEvent] }

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_hostile_event_gap_refused : Bool :=
  decide (applyBatch fixtureBoundary [canonHead, attendantHead]
    { statement := gapStatement, batchDigest := fixtureBoundary.batchDigest gapStatement } =
    .error .wrongSequence)

private def crossPredecessorEvent : IndexedEvent :=
  { attendant with statement :=
    { attendant.statement with predecessor := firstCanon.eventDigest } }

private def crossPredecessorStatement : Statement :=
  { fixtureStatement with events := [firstCanon, crossPredecessorEvent] }

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_hostile_cross_stream_predecessor_refused : Bool :=
  decide (applyBatch fixtureBoundary [canonHead, attendantHead]
    { statement := crossPredecessorStatement
      batchDigest := fixtureBoundary.batchDigest crossPredecessorStatement } =
    .error .wrongPredecessor)

private def reorderedStatement : Statement :=
  { fixtureStatement with events := [attendant, firstCanon] }

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_hostile_index_reorder_refused : Bool :=
  decide (applyBatch fixtureBoundary [canonHead, attendantHead]
    { statement := reorderedStatement
      batchDigest := fixtureBoundary.batchDigest reorderedStatement } =
    .error .wrongEventIndex)

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_hostile_batch_digest_refused : Bool :=
  decide (applyBatch fixtureBoundary [canonHead, attendantHead]
    { fixtureEnvelope with batchDigest := digestByte 255 } = .error .wrongBatchDigest)

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_hostile_duplicate_initial_stream_refused : Bool :=
  decide (applyBatch fixtureBoundary [canonHead, canonHead, attendantHead] fixtureEnvelope =
    .error .duplicateInitialStream)

private def foreignFederationStatement : Statement :=
  let foreignAggregate := { firstCanon.statement.aggregate with namespaceId := digestByte 99 }
  let badStatement := { firstCanon.statement with aggregate := foreignAggregate }
  let bad : IndexedEvent :=
    ⟨firstCanon.eventIndex, badStatement, fixtureBoundary.eventDigest badStatement⟩
  { fixtureStatement with events := [bad] }

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_hostile_foreign_federation_refused : Bool :=
  decide (applyBatch fixtureBoundary [canonHead, attendantHead]
    { statement := foreignFederationStatement
      batchDigest := fixtureBoundary.batchDigest foreignFederationStatement } =
    .error .wrongFederationNamespace)

private def activationWorld : WorldIdentity :=
  { fixtureWorld with activationDigest := digestByte 90 }
private def sessionWorld : WorldIdentity :=
  { fixtureWorld with contentSession := digestByte 91 }
private def epochWorld : WorldIdentity :=
  { fixtureWorld with contentEpoch := ⟨6⟩ }

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_world_scoped_streams_separate_activation_session_and_epoch : Bool :=
  (streamOfStatement activationWorld firstCanon.statement != canonHead.stream) &&
    (streamOfStatement sessionWorld firstCanon.statement != canonHead.stream) &&
    (streamOfStatement epochWorld firstCanon.statement != canonHead.stream)

private def rollbackStatement : Statement :=
  let rollbackWorld := { fixtureWorld with
    activationDigest := digestByte 90
    contentSession := digestByte 91
    contentEpoch := ⟨4⟩ }
  { fixtureStatement with coordinate := { fixtureCoordinate with world := rollbackWorld } }

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_hostile_reused_stream_after_world_rollback_refused : Bool :=
  decide (applyBatch fixtureBoundary [canonHead, attendantHead]
    { statement := rollbackStatement
      batchDigest := fixtureBoundary.batchDigest rollbackStatement } =
    .error .invalidInitialHead)

private def zeroWorldStatement : Statement :=
  let zeroWorld := { fixtureWorld with contentSession := zeroDigest }
  { fixtureStatement with coordinate := { fixtureCoordinate with world := zeroWorld } }

/-- (Pinned `= true` in `EventBatchFixtures`.) -/
def check_hostile_zero_world_identity_refused : Bool :=
  decide (applyBatch fixtureBoundary [canonHead, attendantHead]
    { statement := zeroWorldStatement
      batchDigest := fixtureBoundary.batchDigest zeroWorldStatement } =
    .error .invalidCoordinateIdentity)

theorem fixture_cross_aggregate_batch_accepts :
    check_fixture_cross_aggregate_batch_accepts = true := by native_decide

theorem fixture_repeated_stream_is_explicitly_chained :
    check_fixture_repeated_stream_is_explicitly_chained = true := by native_decide

theorem fixture_cross_aggregate_successors_are_exact :
    check_fixture_cross_aggregate_successors_are_exact = true := by native_decide

theorem hostile_semantic_reapplication_refused :
    check_hostile_semantic_reapplication_refused = true := by native_decide

theorem hostile_event_gap_refused :
    check_hostile_event_gap_refused = true := by native_decide

theorem hostile_cross_stream_predecessor_refused :
    check_hostile_cross_stream_predecessor_refused = true := by native_decide

theorem hostile_index_reorder_refused :
    check_hostile_index_reorder_refused = true := by native_decide

theorem hostile_batch_digest_refused :
    check_hostile_batch_digest_refused = true := by native_decide

theorem hostile_duplicate_initial_stream_refused :
    check_hostile_duplicate_initial_stream_refused = true := by native_decide

theorem hostile_foreign_federation_refused :
    check_hostile_foreign_federation_refused = true := by native_decide

theorem world_scoped_streams_separate_activation_session_and_epoch :
    check_world_scoped_streams_separate_activation_session_and_epoch = true := by
  native_decide

theorem hostile_reused_stream_after_world_rollback_refused :
    check_hostile_reused_stream_after_world_rollback_refused = true := by native_decide

theorem hostile_zero_world_identity_refused :
    check_hostile_zero_world_identity_refused = true := by native_decide

#assert_compiled fixture_cross_aggregate_batch_accepts
#assert_compiled fixture_repeated_stream_is_explicitly_chained
#assert_compiled fixture_cross_aggregate_successors_are_exact
#assert_compiled hostile_semantic_reapplication_refused
#assert_compiled hostile_event_gap_refused
#assert_compiled hostile_cross_stream_predecessor_refused
#assert_compiled hostile_index_reorder_refused
#assert_compiled hostile_batch_digest_refused
#assert_compiled hostile_duplicate_initial_stream_refused
#assert_compiled hostile_foreign_federation_refused
#assert_compiled world_scoped_streams_separate_activation_session_and_epoch
#assert_compiled hostile_reused_stream_after_world_rollback_refused
#assert_compiled hostile_zero_world_identity_refused

end Dregg2.Games.PathOfAngels.EventBatch
