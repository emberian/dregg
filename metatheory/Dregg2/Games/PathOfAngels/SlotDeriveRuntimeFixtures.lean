/-
# Slot-derive runtime — the fixture-pin EVALUATION, out of the crypto archive's build

`SlotDeriveRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its thirteen fixture pins ran `native_decide` at elaboration —
each one a Poseidon2 sponge evaluation — so any derivation-fixture regression was a hard
failure of every Rust proving target in the workspace (the compilation-unit coupling the
stale-fixture outage measured). The pins' STATEMENTS remain in `SlotDeriveRuntime.lean` as
evaluation-free `check_* : Bool` definitions; THIS module is where they are RUN. It is
rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — no construction there demands a proof as data.
-/
import Dregg2.Games.PathOfAngels.SlotDeriveRuntime
import Batteries.Tactic.OpenPrivate

namespace Dregg2.Games.PathOfAngels.SlotDeriveRuntime

set_option autoImplicit false
open Lean (Json)
open Dregg2.Games.PathOfAngels
-- The laboratory reads these runtime helpers; they stay private to the runtime module.
open private hexDigest jsonString from Dregg2.Games.PathOfAngels.SlotDeriveRuntime

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

def fixtureRequestBytes : String := fixtureRequest.toJson

/-- (Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_request_roundtrips : Bool :=
  decide (decodeRequest fixtureRequestBytes = some fixtureRequest)

/-- ⚑ **THE FIXTURE REQUEST DRAWS.**  `derive?` is partial now, so every pin below is a
statement about a `some`; without this one they could all be satisfied by a refusal and
the whole compiled suite would read green against an export that answers nothing.
(Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_derives : Bool := (derive? fixtureRequest).isSome

/-- The export answers, and its answer is the canonical reply it would have written.
(Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_export_answers : Bool :=
  decide (some (slotDeriveFFI fixtureRequestBytes) = (derive? fixtureRequest).map Reply.toJson)

/-- The answer is non-empty, so the refusal sentinel is unambiguous on this wire.
(Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_export_is_not_the_refusal : Bool :=
  decide (slotDeriveFFI fixtureRequestBytes ≠ "")

/-- (Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_reply_is_canonical_and_states_the_format : Bool :=
  ((derive? fixtureRequest).map Reply.toJson).any
    (fun j => j.startsWith ("{\"format\":\"" ++ OUTPUT_FORMAT ++ "\""))

/-- ⚠ The reply does not echo the secret.  A one-instance check, and it is exactly one:
the general statement is that `Reply` has no secret FIELD, which is a type-level fact
visible above, not a theorem. (Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_reply_does_not_carry_the_secret : Bool :=
  decide (((derive? fixtureRequest).map
    (fun r => (r.toJson.splitOn FIXTURE_SECRET_HEX).length)) = some 1)

/-- (Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_trailing_byte_refused : Bool :=
  decide (slotDeriveFFI (fixtureRequestBytes ++ "\n") = "")

/-- (Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_unknown_field_refused : Bool :=
  decide (slotDeriveFFI
    (fixtureRequestBytes.replace "\"slot\":9" "\"slot\":9,\"extra\":0") = "")

/-- (Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_uppercase_digest_refused : Bool :=
  decide (slotDeriveFFI
    (fixtureRequestBytes.replace FIXTURE_FEDERATION_HEX
      (String.toUpper FIXTURE_FEDERATION_HEX)) = "")

/-- (Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_wrong_format_refused : Bool :=
  decide (slotDeriveFFI (fixtureRequestBytes.replace INPUT_FORMAT "POA-SLOT-DERIVE-2") = "")

/-- Key ORDER is pinned by the seal, not merely key membership: the same eight fields
in a different order re-encode to different bytes and are refused. -/
def transposedRequestBytes : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"secret\":" ++ jsonString FIXTURE_SECRET_HEX ++
    ",\"slot\":9" ++
    ",\"mission_id\":1,\"epoch\":1" ++
    ",\"federation_id\":" ++ jsonString FIXTURE_FEDERATION_HEX ++
    ",\"content_session\":" ++ jsonString FIXTURE_SESSION_HEX ++
    ",\"player_key\":" ++ jsonString FIXTURE_PLAYER_HEX ++ "}"

/-- (Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_transposed_keys_refused : Bool :=
  decide (slotDeriveFFI transposedRequestBytes = "")

/-- ⚑ A DIFFERENT SECRET DRAWS A DIFFERENT INSTANCE, through the export, on the wire.
Everything else is held fixed — slot, mission, epoch, federation, session, player — so
this is the export-level form of `HiddenInstance.published_context_does_not_determine_
the_run_seed`, and it is what makes the derivation worth calling at all. -/
def otherSecretRequest : Request :=
  { fixtureRequest with
    secret := hexDigest "8888888888888888888888888888888888888888888888888888888888888888" }

/-- (Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_other_secret_draws_another_instance : Bool :=
  decide ((derive? fixtureRequest).map Reply.runSeed ≠
      (derive? otherSecretRequest).map Reply.runSeed) &&
    decide ((derive? fixtureRequest).map Reply.commitment ≠
      (derive? otherSecretRequest).map Reply.commitment)

/-- (Pinned `= true` in `SlotDeriveRuntimeFixtures`.) -/
def check_fixture_commitment_is_player_independent_but_the_seed_is_not : Bool :=
  decide ((derive? fixtureRequest).map Reply.commitment =
      (derive? otherPlayerRequest).map Reply.commitment) &&
    decide ((derive? fixtureRequest).map Reply.runSeed ≠
      (derive? otherPlayerRequest).map Reply.runSeed)

theorem fixture_request_roundtrips :
    check_fixture_request_roundtrips = true := by native_decide

theorem fixture_derives :
    check_fixture_derives = true := by native_decide

theorem fixture_export_answers :
    check_fixture_export_answers = true := by native_decide

theorem fixture_export_is_not_the_refusal :
    check_fixture_export_is_not_the_refusal = true := by native_decide

theorem fixture_reply_is_canonical_and_states_the_format :
    check_fixture_reply_is_canonical_and_states_the_format = true := by native_decide

theorem fixture_reply_does_not_carry_the_secret :
    check_fixture_reply_does_not_carry_the_secret = true := by native_decide

theorem fixture_trailing_byte_refused :
    check_fixture_trailing_byte_refused = true := by native_decide

theorem fixture_unknown_field_refused :
    check_fixture_unknown_field_refused = true := by native_decide

theorem fixture_uppercase_digest_refused :
    check_fixture_uppercase_digest_refused = true := by native_decide

theorem fixture_wrong_format_refused :
    check_fixture_wrong_format_refused = true := by native_decide

theorem fixture_transposed_keys_refused :
    check_fixture_transposed_keys_refused = true := by native_decide

theorem fixture_other_secret_draws_another_instance :
    check_fixture_other_secret_draws_another_instance = true := by native_decide

theorem fixture_commitment_is_player_independent_but_the_seed_is_not :
    check_fixture_commitment_is_player_independent_but_the_seed_is_not = true := by
  native_decide

#assert_compiled fixture_request_roundtrips
#assert_compiled fixture_derives
#assert_compiled fixture_export_answers
#assert_compiled fixture_export_is_not_the_refusal
#assert_compiled fixture_reply_is_canonical_and_states_the_format
#assert_compiled fixture_reply_does_not_carry_the_secret
#assert_compiled fixture_trailing_byte_refused
#assert_compiled fixture_unknown_field_refused
#assert_compiled fixture_uppercase_digest_refused
#assert_compiled fixture_wrong_format_refused
#assert_compiled fixture_transposed_keys_refused
#assert_compiled fixture_other_secret_draws_another_instance
#assert_compiled fixture_commitment_is_player_independent_but_the_seed_is_not

end Dregg2.Games.PathOfAngels.SlotDeriveRuntime
