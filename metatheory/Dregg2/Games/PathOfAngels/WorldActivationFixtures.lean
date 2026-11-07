/-
# WorldActivation — the honest/hostile witness EVALUATION, out of the crypto archive's build

`WorldActivation.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its witness section ran twelve `native_decide` pins at elaboration — so any
fixture regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). The witnesses' STATEMENTS remain
in `WorldActivation.lean` as evaluation-free `check_* : Bool` definitions, beside the private
fixture envelopes and lineage they exercise; THIS module is where they are RUN. It is rooted in
the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose
`Except` lands on any arm but the asserted one answers `false`, so a regression reds THIS
module.

⚠ Named residue: NONE. Nothing in `WorldActivation` demands a proof as data at construction,
so all twelve pins moved.
-/
import Dregg2.Games.PathOfAngels.WorldActivation
import Batteries.Tactic.OpenPrivate

namespace Dregg2.Games.PathOfAngels.WorldActivation

set_option autoImplicit false
open Lean
open Dregg2.Games.PathOfAngels
-- The laboratory reads these runtime helpers; they stay private to the runtime module.
open private digestByte pin world zeroDigest from Dregg2.Games.PathOfAngels.WorldActivation

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

private def signatureByte (value : Nat) : Signature64 where
  bytes := List.replicate 64 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def bootstrapEnvelope : SignedActivationEnvelope where
  statement := {
    world := world 4 10 11 12
    counter := 4
    predecessorHead := zeroDigest
    kind := .advance
    rollbackTarget := none
  }
  curatorKey := pin
  signature := signatureByte 91

private def recordOf (envelope : SignedActivationEnvelope) : ActivationRecord where
  envelope
  envelopeDigest := (envelopeDigest? envelope).getD zeroDigest

private def bootstrapState : State := [recordOf bootstrapEnvelope]

private def successorEnvelope : SignedActivationEnvelope where
  statement := {
    world := world 5 20 21 22
    counter := 5
    predecessorHead := (recordOf bootstrapEnvelope).envelopeDigest
    kind := .advance
    rollbackTarget := none
  }
  curatorKey := pin
  signature := signatureByte 92

/-- Fail-closed refusal shape: the judged lineage rejected the envelope with exactly this
error.  Every other arm — a different error, or acceptance — answers `false`. -/
private def refusedWith (result : Except Error State) (error : Error) : Bool :=
  match result with
  | .error actual => actual == error
  | .ok _ => false

/-- The honest successor advance is admitted.
(Pinned `= true` in `WorldActivationFixtures`.) -/
def check_honest_successor_accepts : Bool :=
  (admit pin true bootstrapState successorEnvelope).isOk

private def staleEpochEnvelope : SignedActivationEnvelope :=
  { successorEnvelope with statement :=
    { successorEnvelope.statement with world := world 4 20 21 22 } }

/-- Re-using the predecessor's content epoch is refused as a stale/skipped epoch.
(Pinned `= true` in `WorldActivationFixtures`.) -/
def check_stale_epoch_refused : Bool :=
  refusedWith (admit pin true bootstrapState staleEpochEnvelope) .staleOrSkippedEpoch

private def counterSkipEnvelope : SignedActivationEnvelope :=
  { successorEnvelope with statement := { successorEnvelope.statement with counter := 6 } }

/-- The activation counter advances by exactly one; a skip is refused.
(Pinned `= true` in `WorldActivationFixtures`.) -/
def check_counter_skip_refused : Bool :=
  refusedWith (admit pin true bootstrapState counterSkipEnvelope) .wrongCounter

private def wrongPredecessorEnvelope : SignedActivationEnvelope :=
  { successorEnvelope with statement :=
    { successorEnvelope.statement with predecessorHead := digestByte 88 } }

/-- The signed predecessor head must be the durable head's envelope digest.
(Pinned `= true` in `WorldActivationFixtures`.) -/
def check_wrong_predecessor_refused : Bool :=
  refusedWith (admit pin true bootstrapState wrongPredecessorEnvelope) .wrongPredecessor

private def unrecordedRollbackEnvelope : SignedActivationEnvelope :=
  { successorEnvelope with statement :=
    { successorEnvelope.statement with
      world := bootstrapEnvelope.statement.world
      kind := .rollback
      rollbackTarget := some (digestByte 77) } }

/-- A rollback may only name a digest that is actually in the replayed lineage.
(Pinned `= true` in `WorldActivationFixtures`.) -/
def check_unrecorded_rollback_refused : Bool :=
  refusedWith (admit pin true bootstrapState unrecordedRollbackEnvelope) .rollbackTargetMissing

private def wrongCuratorEnvelope : SignedActivationEnvelope :=
  { successorEnvelope with curatorKey := digestByte 89 }

/-- The envelope's curator key must be the externally distributed pin.
(Pinned `= true` in `WorldActivationFixtures`.) -/
def check_wrong_curator_key_refused : Bool :=
  refusedWith (admit pin true bootstrapState wrongCuratorEnvelope) .wrongCuratorKey

/-- Without the host's native Ed25519 verdict nothing is admitted, however
structurally perfect the envelope is. (Pinned `= true` in `WorldActivationFixtures`.) -/
def check_unverified_native_signature_refused : Bool :=
  refusedWith (admit pin false bootstrapState successorEnvelope) .nativeSignatureNotVerified

/-- Same federation, different content root, is NOT the active world.
(Pinned `= true` in `WorldActivationFixtures`.) -/
def check_same_federation_different_content_refused_by_active_world : Bool :=
  !(authorizesWorld bootstrapState (world 4 99 11 12))

/-- Same federation, different content session, is NOT the active world.
(Pinned `= true` in `WorldActivationFixtures`.) -/
def check_same_federation_different_session_refused_by_active_world : Bool :=
  !(authorizesWorld bootstrapState (world 4 10 11 99))

private def successorState : State :=
  (admit pin true bootstrapState successorEnvelope).toOption.getD []

private def rollbackEnvelope : SignedActivationEnvelope where
  statement := {
    world := bootstrapEnvelope.statement.world
    counter := 6
    predecessorHead := (recordOf successorEnvelope).envelopeDigest
    kind := .rollback
    rollbackTarget := some (recordOf bootstrapEnvelope).envelopeDigest
  }
  curatorKey := pin
  signature := signatureByte 93

/-- A rollback naming a recorded envelope is admitted and restores that record's ENTIRE
`WorldIdentity`, not a federation-only projection.  Fail-closed: a refusal, or an accepted
lineage with no active world, answers `false`.
(Pinned `= true` in `WorldActivationFixtures`.) -/
def check_recorded_rollback_accepts_and_restores_exact_world : Bool :=
  match (admit pin true successorState rollbackEnvelope).map activeWorld? with
  | .ok (some restored) => restored == bootstrapEnvelope.statement.world
  | _ => false

private def fixtureInput : InputWire where
  externalCuratorKeyPin := pin
  nativeSignatureVerified := true
  state := bootstrapState
  envelope := successorEnvelope

/-- The canonical input wire decodes back to the exact value that encoded it.
(Pinned `= true` in `WorldActivationFixtures`.) -/
def check_fixture_canonical_input_roundtrips : Bool :=
  decodeInput fixtureInput.toJson == some fixtureInput

private def honestAuthorizeInput : AuthorizeInputWire where
  externalCuratorKeyPin := pin
  nativeSignaturesVerified := true
  state := bootstrapState
  candidate := bootstrapEnvelope.statement.world

/-- The exact-world query answers `"1"` for the durable active head and `"0"` for the same
federation with different content. (Pinned `= true` in `WorldActivationFixtures`.) -/
def check_exact_world_query_accepts_head_and_refuses_other_content : Bool :=
  (authorizesWire honestAuthorizeInput.toJson == "1") &&
  (authorizesWire { honestAuthorizeInput with candidate := world 4 99 11 12 }.toJson == "0")

theorem honest_successor_accepts :
    check_honest_successor_accepts = true := by native_decide

theorem stale_epoch_refused :
    check_stale_epoch_refused = true := by native_decide

theorem counter_skip_refused :
    check_counter_skip_refused = true := by native_decide

theorem wrong_predecessor_refused :
    check_wrong_predecessor_refused = true := by native_decide

theorem unrecorded_rollback_refused :
    check_unrecorded_rollback_refused = true := by native_decide

theorem wrong_curator_key_refused :
    check_wrong_curator_key_refused = true := by native_decide

theorem unverified_native_signature_refused :
    check_unverified_native_signature_refused = true := by native_decide

theorem same_federation_different_content_refused_by_active_world :
    check_same_federation_different_content_refused_by_active_world = true := by native_decide

theorem same_federation_different_session_refused_by_active_world :
    check_same_federation_different_session_refused_by_active_world = true := by native_decide

theorem recorded_rollback_accepts_and_restores_exact_world :
    check_recorded_rollback_accepts_and_restores_exact_world = true := by native_decide

theorem fixture_canonical_input_roundtrips :
    check_fixture_canonical_input_roundtrips = true := by native_decide

theorem exact_world_query_accepts_head_and_refuses_other_content :
    check_exact_world_query_accepts_head_and_refuses_other_content = true := by native_decide

#assert_compiled honest_successor_accepts
#assert_compiled stale_epoch_refused
#assert_compiled counter_skip_refused
#assert_compiled wrong_predecessor_refused
#assert_compiled unrecorded_rollback_refused
#assert_compiled wrong_curator_key_refused
#assert_compiled unverified_native_signature_refused
#assert_compiled same_federation_different_content_refused_by_active_world
#assert_compiled same_federation_different_session_refused_by_active_world
#assert_compiled recorded_rollback_accepts_and_restores_exact_world
#assert_compiled fixture_canonical_input_roundtrips
#assert_compiled exact_world_query_accepts_head_and_refuses_other_content

end Dregg2.Games.PathOfAngels.WorldActivation
