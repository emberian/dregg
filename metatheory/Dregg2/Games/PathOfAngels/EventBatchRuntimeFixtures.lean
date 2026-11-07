/-
# EventBatchRuntime — the teeth EVALUATION, out of the crypto archive's build

`EventBatchRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its multi-stream fixture and hostile teeth ran twenty
`native_decide` pins at elaboration — so any game-fixture regression was a hard failure
of every Rust proving target in the workspace. The teeth's STATEMENTS remain in
`EventBatchRuntime.lean` as evaluation-free `check_* : Bool` definitions, beside the
private fixture material and the `@[export]` FFI surface they exercise; THIS module is
where they are RUN. It is rooted in the `PathOfAngelsGuards` library and reachable from
`Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose
prerequisite plan refuses answers `false`, so a broken prerequisite reds THIS module.
Named residue: none.
-/
import Dregg2.Games.PathOfAngels.EventBatchRuntime
import Batteries.Tactic.OpenPrivate

namespace Dregg2.Games.PathOfAngels.EventBatchRuntime

set_option autoImplicit false
open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.EventSourcing
-- The laboratory reads these runtime helpers; they stay private to the runtime module.
open private headFor? from Dregg2.Games.PathOfAngels.EventBatchRuntime

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

private def fixtureDigest (n : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  length_eq := by simp

private def fixtureWorld : WorldWire := {
  federationId := fixtureDigest 1
  contentRoot := fixtureDigest 2
  activationDigest := fixtureDigest 3
  contentSession := fixtureDigest 4
  contentEpoch := 5
}

private def fixtureCoordinate : CoordinateWire := {
  world := fixtureWorld
  commitOrdinal := 7
  blockId := fixtureDigest 8
  turnHash := fixtureDigest 9
  receiptHash := fixtureDigest 10
  actorRoot := fixtureDigest 11
  signer := fixtureDigest 12
}

private def fixtureStream (kind key : Nat) : StreamWire := {
  world := fixtureWorld
  kind
  key := fixtureDigest key
  version := 1
}

private def fixtureBytes (values : List Nat) : OpaqueBytes := ⟨values⟩

private def fixtureHead (kind key genesis storage projection : Nat) : HeadWire :=
  let bytes := fixtureBytes [projection, projection + 1]
  {
    stream := fixtureStream kind key
    sequence := 0
    semanticHead := fixtureDigest genesis
    storageHeadDigest := fixtureDigest storage
    projectionDigest := digestBytes PROJECTION_DIGEST_DOMAIN bytes.bytes
    projection := bytes
    origin := "genesis"
  }

private def canonHead : HeadWire := fixtureHead 2 20 30 31 32
private def attendantHead : HeadWire := fixtureHead 10 21 40 41 42

private def fixtureEvent (eventIndex : Nat) (stream : StreamWire) (sequence : Nat)
    (predecessor : Digest32) (payload projection : List Nat) : CandidateEventWire :=
  let payloadBytes := fixtureBytes payload
  let projectionBytes := fixtureBytes projection
  let statement : StatementWire := {
    namespaceId := stream.world.federationId
    kind := stream.kind
    key := stream.key
    version := stream.version
    sequence
    predecessor
    payloadDigest := digestBytes PAYLOAD_DIGEST_DOMAIN payloadBytes.bytes
  }
  {
    eventIndex
    statement
    eventDigest := digestBoundary.eventDigest statement.toSemantic
    payload := payloadBytes
    successorProjectionDigest := digestBytes PROJECTION_DIGEST_DOMAIN projectionBytes.bytes
    successorProjection := projectionBytes
  }

private def firstCanon : CandidateEventWire :=
  fixtureEvent 0 canonHead.stream 1 canonHead.semanticHead [1, 2, 3] [10, 11]

private def attendant : CandidateEventWire :=
  fixtureEvent 1 attendantHead.stream 1 attendantHead.semanticHead [4, 5] [12, 13]

private def secondCanon : CandidateEventWire :=
  fixtureEvent 2 canonHead.stream 2 firstCanon.eventDigest [6, 7] [14, 15]

private def fixtureEvents : List CandidateEventWire := [firstCanon, attendant, secondCanon]

private def fixtureBinding (event : CandidateEventWire) (storage : Nat) :
    AuthorityEventBindingWire := {
  eventIndex := event.eventIndex
  receiptHash := fixtureCoordinate.receiptHash
  actorRoot := fixtureCoordinate.actorRoot
  signer := fixtureCoordinate.signer
  eventDigest := event.eventDigest
  payloadDigest := event.statement.payloadDigest
  successorProjectionDigest := event.successorProjectionDigest
  successorStorageHeadDigest := fixtureDigest storage
}

private def fixtureHeads : List HeadWire := [canonHead, attendantHead]

private def fixtureInput : InputWire := {
  authority := {
    coordinate := fixtureCoordinate
    initialHeadsDigest := initialHeadsDigest fixtureHeads
    events := [fixtureBinding firstCanon 50, fixtureBinding attendant 51,
      fixtureBinding secondCanon 52]
  }
  coordinate := fixtureCoordinate
  initialHeads := fixtureHeads
  events := fixtureEvents
}

private def fixtureInitialHeadsDigestInput : InitialHeadsDigestInputWire := {
  coordinate := fixtureCoordinate
  initialHeads := fixtureHeads
}

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_fixture_canonical_decode_accepts : Bool :=
  decide (decodeInput fixtureInput.toJson = some fixtureInput)

/-- Fail-closed: a refused plan answers `false`.
(Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_fixture_multi_stream_repeated_stream_plans : Bool :=
  match planInput? fixtureInput with
  | none => false
  | some prepared =>
      prepared.events.length == 3 &&
      (headFor? prepared.successorHeads canonHead.stream).map HeadWire.sequence == some 2 &&
      (headFor? prepared.successorHeads attendantHead.stream).map HeadWire.sequence == some 1

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_fixture_repeated_stream_uses_prior_successor_storage_digest : Bool :=
  match planInput? fixtureInput with
  | some prepared =>
      (prepared.events[2]?).map PreparedEventWire.expectedPredecessorHeadDigest ==
        some (fixtureDigest 50)
  | none => false

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_fixture_ffi_emits_nonempty_canonical_plan : Bool :=
  planFFI fixtureInput.toJson != ""

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_fixture_initial_heads_digest_export_is_exact : Bool :=
  decide (initialHeadsDigestFFI fixtureInitialHeadsDigestInput.toJson =
    (InitialHeadsDigestOutputWire.mk (initialHeadsDigest fixtureHeads)).toJson)

private def crossWorldHeadsInput : InitialHeadsDigestInputWire :=
  let foreignWorld := { fixtureWorld with contentSession := fixtureDigest 99 }
  let foreignStream := { canonHead.stream with world := foreignWorld }
  let foreignHead := { canonHead with stream := foreignStream }
  { fixtureInitialHeadsDigestInput with initialHeads := [foreignHead, attendantHead] }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_initial_heads_digest_cross_world_refused : Bool :=
  decide (initialHeadsDigestFFI crossWorldHeadsInput.toJson = "")

private def zeroWorldHeadsInput : InitialHeadsDigestInputWire :=
  let zeroWorld := { fixtureWorld with contentEpoch := 0 }
  { fixtureInitialHeadsDigestInput with
    coordinate := { fixtureCoordinate with world := zeroWorld } }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_initial_heads_digest_zero_world_refused : Bool :=
  decide (initialHeadsDigestFFI zeroWorldHeadsInput.toJson = "")

private def reorderedInput : InputWire :=
  { fixtureInput with events := [attendant, firstCanon, secondCanon] }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_reorder_refused : Bool := (planInput? reorderedInput).isNone

private def payloadMutationInput : InputWire :=
  let changed := { firstCanon with payload := fixtureBytes [99, 2, 3] }
  { fixtureInput with events := [changed, attendant, secondCanon] }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_payload_mutation_refused : Bool := (planInput? payloadMutationInput).isNone

private def projectionMutationInput : InputWire :=
  let changed := { attendant with successorProjection := fixtureBytes [99, 13] }
  { fixtureInput with events := [firstCanon, changed, secondCanon] }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_projection_mutation_refused : Bool :=
  (planInput? projectionMutationInput).isNone

private def crossWorldInput : InputWire :=
  let foreignWorld := { fixtureWorld with activationDigest := fixtureDigest 99 }
  { fixtureInput with coordinate := { fixtureCoordinate with world := foreignWorld } }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_cross_world_refused : Bool := (planInput? crossWorldInput).isNone

private def crossActorInput : InputWire :=
  { fixtureInput with coordinate := { fixtureCoordinate with actorRoot := fixtureDigest 99 } }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_cross_actor_refused : Bool := (planInput? crossActorInput).isNone

private def forgedActorBindingInput : InputWire :=
  let first := { fixtureBinding firstCanon 50 with actorRoot := fixtureDigest 99 }
  { fixtureInput with authority := { fixtureInput.authority with events :=
    [first, fixtureBinding attendant 51, fixtureBinding secondCanon 52] } }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_authority_actor_binding_refused : Bool :=
  (planInput? forgedActorBindingInput).isNone

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_noncanonical_trailing_byte_refused : Bool :=
  (decodeInput (fixtureInput.toJson ++ " ")).isNone

private def unknownFieldBytes : String :=
  (fixtureInput.toJson.dropEnd 1).toString ++ ",\"extra\":0}"

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_unknown_field_refused : Bool := (decodeInput unknownFieldBytes).isNone

private def emptyBatchInput : InputWire :=
  { fixtureInput with
    authority := { fixtureInput.authority with events := [] }
    events := [] }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_empty_batch_refused : Bool := (planInput? emptyBatchInput).isNone

private def oversizedEventCountInput : InputWire :=
  { fixtureInput with
    authority := { fixtureInput.authority with
      events := List.replicate (MAX_EVENTS + 1) (fixtureBinding firstCanon 50) }
    events := List.replicate (MAX_EVENTS + 1) firstCanon }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_event_count_refused : Bool := (planInput? oversizedEventCountInput).isNone

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_wire_size_refused : Bool :=
  (decodeInputWithLimit 4 fixtureInput.toJson).isNone

private def u64OverflowInput : InputWire :=
  let coordinate := { fixtureCoordinate with
    world := { fixtureWorld with contentEpoch := 2 ^ 64 } }
  { fixtureInput with
    coordinate
    authority := { fixtureInput.authority with coordinate } }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_u64_overflow_refused : Bool := (planInput? u64OverflowInput).isNone

private def sequenceOverflowInput : InputWire :=
  let event := { firstCanon with statement := { firstCanon.statement with sequence := 2 ^ 64 } }
  { fixtureInput with events := [event, attendant, secondCanon] }

/-- (Pinned `= true` in `EventBatchRuntimeFixtures`.) -/
def check_hostile_sequence_overflow_refused : Bool :=
  (planInput? sequenceOverflowInput).isNone

theorem fixture_canonical_decode_accepts :
    check_fixture_canonical_decode_accepts = true := by native_decide

theorem fixture_multi_stream_repeated_stream_plans :
    check_fixture_multi_stream_repeated_stream_plans = true := by native_decide

theorem fixture_repeated_stream_uses_prior_successor_storage_digest :
    check_fixture_repeated_stream_uses_prior_successor_storage_digest = true := by
  native_decide

theorem fixture_ffi_emits_nonempty_canonical_plan :
    check_fixture_ffi_emits_nonempty_canonical_plan = true := by native_decide

theorem fixture_initial_heads_digest_export_is_exact :
    check_fixture_initial_heads_digest_export_is_exact = true := by native_decide

theorem hostile_initial_heads_digest_cross_world_refused :
    check_hostile_initial_heads_digest_cross_world_refused = true := by native_decide

theorem hostile_initial_heads_digest_zero_world_refused :
    check_hostile_initial_heads_digest_zero_world_refused = true := by native_decide

theorem hostile_reorder_refused :
    check_hostile_reorder_refused = true := by native_decide

theorem hostile_payload_mutation_refused :
    check_hostile_payload_mutation_refused = true := by native_decide

theorem hostile_projection_mutation_refused :
    check_hostile_projection_mutation_refused = true := by native_decide

theorem hostile_cross_world_refused :
    check_hostile_cross_world_refused = true := by native_decide

theorem hostile_cross_actor_refused :
    check_hostile_cross_actor_refused = true := by native_decide

theorem hostile_authority_actor_binding_refused :
    check_hostile_authority_actor_binding_refused = true := by native_decide

theorem hostile_noncanonical_trailing_byte_refused :
    check_hostile_noncanonical_trailing_byte_refused = true := by native_decide

theorem hostile_unknown_field_refused :
    check_hostile_unknown_field_refused = true := by native_decide

theorem hostile_empty_batch_refused :
    check_hostile_empty_batch_refused = true := by native_decide

theorem hostile_event_count_refused :
    check_hostile_event_count_refused = true := by native_decide

theorem hostile_wire_size_refused :
    check_hostile_wire_size_refused = true := by native_decide

theorem hostile_u64_overflow_refused :
    check_hostile_u64_overflow_refused = true := by native_decide

theorem hostile_sequence_overflow_refused :
    check_hostile_sequence_overflow_refused = true := by native_decide

#assert_compiled fixture_canonical_decode_accepts
#assert_compiled fixture_multi_stream_repeated_stream_plans
#assert_compiled fixture_repeated_stream_uses_prior_successor_storage_digest
#assert_compiled fixture_ffi_emits_nonempty_canonical_plan
#assert_compiled fixture_initial_heads_digest_export_is_exact
#assert_compiled hostile_initial_heads_digest_cross_world_refused
#assert_compiled hostile_initial_heads_digest_zero_world_refused
#assert_compiled hostile_reorder_refused
#assert_compiled hostile_payload_mutation_refused
#assert_compiled hostile_projection_mutation_refused
#assert_compiled hostile_cross_world_refused
#assert_compiled hostile_cross_actor_refused
#assert_compiled hostile_authority_actor_binding_refused
#assert_compiled hostile_noncanonical_trailing_byte_refused
#assert_compiled hostile_unknown_field_refused
#assert_compiled hostile_empty_batch_refused
#assert_compiled hostile_event_count_refused
#assert_compiled hostile_wire_size_refused
#assert_compiled hostile_u64_overflow_refused
#assert_compiled hostile_sequence_overflow_refused

end Dregg2.Games.PathOfAngels.EventBatchRuntime
