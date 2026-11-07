/-
# EventSourcing — the adversarial-teeth EVALUATION, out of the crypto archive's build

`EventSourcing.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its adversarial teeth ran eight `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace.
The teeth's STATEMENTS remain in `EventSourcing.lean` as evaluation-free `check_* : Bool`
definitions, beside the private fixtures they must see; THIS module is where they are RUN.
It is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by
NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The hostile checks pin the EXACT refusal error, which
subsumes the old `fail_if_success` "not accepted" harness. Named residue: none.
-/
import Dregg2.Games.PathOfAngels.EventSourcing
import Batteries.Tactic.OpenPrivate

namespace Dregg2.Games.PathOfAngels.EventSourcing

set_option autoImplicit false
open Dregg2.Games.PathOfAngels
-- The laboratory reads these runtime helpers; they stay private to the runtime module.
open private digestByte eventOne eventTwo fixtureDigests fixtureReducer fixtureSpec
   wrongAggregate from Dregg2.Games.PathOfAngels.EventSourcing

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- The dense two-event stream rebuilds to exactly 0 + 7 + 11.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_fixture_dense_rebuild : Bool :=
  decide (rebuildProjection fixtureSpec fixtureDigests fixtureReducer 0 [eventOne, eventTwo] =
    .ok 18)

/-- A stream that skips sequence 1 is refused with the exact gap error — the
exact-error equality refutes acceptance by construction.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_gap_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests fixtureReducer 0 [eventTwo] =
    .error (.wrongSequence 1 2))

/-- Reordered events are refused at the first out-of-sequence statement.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_reorder_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests fixtureReducer 0 [eventTwo, eventOne] =
    .error (.wrongSequence 1 2))

private def wrongAggregateEvent : EventEnvelope Nat :=
  { eventOne with statement := { eventOne.statement with aggregate := wrongAggregate } }

/-- An event carrying a foreign aggregate id is refused.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_wrong_aggregate_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests fixtureReducer 0 [wrongAggregateEvent] =
    .error .wrongAggregate)

private def wrongVersionEvent : EventEnvelope Nat :=
  { eventOne with statement := { eventOne.statement with version := ⟨4⟩ } }

/-- An event carrying a foreign schema version is refused.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_wrong_version_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests fixtureReducer 0 [wrongVersionEvent] =
    .error .wrongVersion)

private def wrongPredecessorEvent : EventEnvelope Nat :=
  { eventTwo with statement := { eventTwo.statement with predecessor := digestByte 99 } }

/-- A successor naming the wrong predecessor head is refused.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_wrong_predecessor_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests fixtureReducer 0 [eventOne, wrongPredecessorEvent] =
    .error .wrongPredecessor)

private def forgedAggregateSnapshot : Snapshot Nat where
  cursor := { fixtureSpec.genesisCursor with aggregate := wrongAggregate }
  projection := 777

/-- A snapshot forged for a foreign aggregate is refused even with an empty suffix.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_wrong_aggregate_snapshot_empty_suffix_refused : Bool :=
  decide (resumeSnapshot fixtureSpec fixtureDigests fixtureReducer forgedAggregateSnapshot [] =
    .error .snapshotAggregate)

private def forgedVersionSnapshot : Snapshot Nat where
  cursor := { fixtureSpec.genesisCursor with version := ⟨4⟩ }
  projection := 777

/-- A snapshot forged for a foreign schema version is refused even with an empty suffix.
(Pinned `= true` in `EventSourcingFixtures`.) -/
def check_hostile_wrong_version_snapshot_empty_suffix_refused : Bool :=
  decide (resumeSnapshot fixtureSpec fixtureDigests fixtureReducer forgedVersionSnapshot [] =
    .error .snapshotVersion)

theorem fixture_dense_rebuild :
    check_fixture_dense_rebuild = true := by native_decide

theorem hostile_gap_refused :
    check_hostile_gap_refused = true := by native_decide

theorem hostile_reorder_refused :
    check_hostile_reorder_refused = true := by native_decide

theorem hostile_wrong_aggregate_refused :
    check_hostile_wrong_aggregate_refused = true := by native_decide

theorem hostile_wrong_version_refused :
    check_hostile_wrong_version_refused = true := by native_decide

theorem hostile_wrong_predecessor_refused :
    check_hostile_wrong_predecessor_refused = true := by native_decide

theorem hostile_wrong_aggregate_snapshot_empty_suffix_refused :
    check_hostile_wrong_aggregate_snapshot_empty_suffix_refused = true := by native_decide

theorem hostile_wrong_version_snapshot_empty_suffix_refused :
    check_hostile_wrong_version_snapshot_empty_suffix_refused = true := by native_decide

#assert_compiled fixture_dense_rebuild
#assert_compiled hostile_gap_refused
#assert_compiled hostile_reorder_refused
#assert_compiled hostile_wrong_aggregate_refused
#assert_compiled hostile_wrong_version_refused
#assert_compiled hostile_wrong_predecessor_refused
#assert_compiled hostile_wrong_aggregate_snapshot_empty_suffix_refused
#assert_compiled hostile_wrong_version_snapshot_empty_suffix_refused

end Dregg2.Games.PathOfAngels.EventSourcing
