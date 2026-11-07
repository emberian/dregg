/-
# Path of Angels — sealed-salvage Bazaar workbook

One executable player journey, parameterized only by the two deployment
capabilities this module intentionally cannot fabricate:

* solve a real Signal mission whose checked contribution yields relic 9001;
* acquire the exact judged run in the Field Archive;
* list its already-crowned, indivisible note;
* fork one exact opened round into a cancellation branch and a sale branch;
* accept four opaque envelopes on the sale branch and close the book;
* run the existing opening-aware V1 Dark Bazaar authorization;
* consume its exact settlement and transfer custody to the taker.

The hostile workbook also exercises canonical-head forks, registry replay,
malformed custody, duplicate/capacity/cancellation timing, non-zero fee
refusals, house-blind refusal, expiry, wrong-batch settlement, replay,
double-listing, and the observation-only crown blocker.  The gameplay data is
closed; authority and crown certification remain explicit abstract inputs.
Facts which transit the existing native V1 fixture are named and accounted with
`#assert_compiled`; generic Bazaar laws remain kernel-pinned in `BazaarGame`.

## ⚑ Where the sponge runs, and where it does not

Admission now hashes: `Judged.admissionChecks` recomputes `HiddenInstance.commit` and
`HiddenInstance.runSeedFor`, both Poseidon2.  Reducing that decision in the KERNEL is
not slow, it is infeasible — 47.6 GB and 68 minutes on one file, MEASURED; see the `⚑`
note in `HiddenInstance`.  So this workbook evaluates the sponge only under COMPILED
evaluation, in exactly three named theorems, and never in the kernel:

* `live_run_seed_is_the_derived_draw` / `slot_commitment_is_the_committed_secret` —
  the two named digests below ARE the two sponge outputs;
* `run_is_admitted` — the whole of `admissionChecks`, which re-checks both of those
  derivations against the fixture's own `active`/`runClaim`.

`judged?` is then built through `Judged.judgeAdmitted`, which takes that admission as a
proof argument rather than re-deciding it, and `judged_is_the_authoritative_judge`
proves it is the same `Option JudgedRun` that `judgeActive` returns.  Everything after
that point — the whole persistent deployment story and every hostile refusal — reduces
in the kernel over literals, as it did before the run seed became derived.

⚠ What this costs, stated plainly: those three facts, and therefore every `rfl` below
them, rest on the Lean compiler rather than the kernel.  That is what `#assert_compiled`
on all of them says out loud.  No configuration of this workbook kernel-checks a derived
run seed: the one measurement anyone has is 47.6 GB of resident memory and 68 minutes of
CPU on a single file, still climbing into a 48 GB cap when it was killed.  That is the
whole reason the label is `#assert_compiled` and not `#assert_axioms`.
-/
import Dregg2.Games.PathOfAngels.BazaarGame

namespace Dregg2.Games.PathOfAngels.BazaarGameExamples

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DarkBazaar
open Dregg2.Games.PathOfAngels.BazaarGame
open Dregg2.Games.PathOfAngels.FieldArchive
open Market.DarkBazaarPrivateDescriptor

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def repeatedDigest (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by decide)⟩
  length_eq := by simp

private def literalDigest (bytes : List (Fin 256))
    (length_eq : bytes.length = 32) : Digest32 :=
  ⟨bytes, length_eq⟩

private def orderDigest0 : Digest32 := literalDigest
  [131, 202, 253, 59, 73, 44, 228, 46, 242, 130, 28, 98, 62, 30, 121, 14,
    242, 68, 142, 29, 57, 160, 158, 55, 154, 225, 1, 24, 61, 121, 191, 63]
  (by decide)

private def orderDigest1 : Digest32 := literalDigest
  [142, 234, 89, 77, 253, 28, 8, 88, 110, 168, 81, 20, 223, 236, 134, 29,
    86, 66, 50, 11, 202, 98, 101, 106, 139, 145, 3, 93, 4, 147, 142, 66]
  (by decide)

private def orderDigest2 : Digest32 := literalDigest
  [67, 85, 37, 116, 224, 134, 203, 32, 79, 158, 58, 17, 123, 21, 99, 76,
    168, 246, 77, 14, 185, 183, 34, 77, 218, 95, 29, 103, 4, 38, 243, 100]
  (by decide)

private def orderDigest3 : Digest32 := literalDigest
  [135, 243, 114, 85, 74, 170, 164, 58, 1, 109, 251, 64, 17, 206, 53, 106,
    104, 53, 154, 55, 22, 107, 149, 69, 222, 232, 41, 87, 206, 63, 129, 52]
  (by decide)

private def envelopeNullifier (slot : Fin 4) : OrderNullifier :=
  ⟨![orderDigest0, orderDigest1, orderDigest2, orderDigest3] slot⟩

def federation : Digest32 := repeatedDigest 1
def contentRoot : Digest32 := repeatedDigest 2
def activation : Digest32 := repeatedDigest 3
def contentSession : Digest32 := repeatedDigest 4
def actorRoot : Digest32 := repeatedDigest 6
def playerKey : Digest32 := repeatedDigest 7
def sellerDigest : Digest32 := repeatedDigest 17
def buyerDigest : Digest32 := repeatedDigest 34
def sourceRoot : Digest32 := repeatedDigest 51
def baseNullifier : Digest32 := repeatedDigest 113
def quoteNullifier : Digest32 := repeatedDigest 114

def relic : RelicId := ⟨9001⟩
def missionId : MissionId := ⟨4040⟩

def artifact : ArtifactRef where
  missionId
  artifactId := ⟨77⟩
  sourceDigest := repeatedDigest 70
  contentDigest := repeatedDigest 71

def reward : Contribution where
  intel := 0
  supplies := 0
  cohesion := 0
  influence := 0
  score := 1
  relics := {relic}
  relics_bounded := by simp

def budget : ContributionBudget where
  intel := 0
  supplies := 0
  cohesion := 0
  influence := 0
  score := 1
  relics := ⟨1, by decide⟩

/-- Everything the draw reads, fixed before the seed exists. -/
def missionContext : HiddenInstance.MissionContext where
  missionId := missionId
  epoch := ⟨1⟩
  federationId := federation
  contentSession := contentSession

/-- ⚠ The fixture's run seed is DERIVED.  `Judged.admissionChecks` requires
`active.runSeed` to be exactly `HiddenInstance.runSeedFor` of the committed slot
secret, this slot and this player, so a fixture that names a seed of its own is
refused — which is the whole point of the split, and this example is where it is
exercised end to end.

⚠ These five sit ABOVE `mission` and are named there.  They used to be stated twice —
once inline in `mission.runSeed`, once here — which is two shapes that agree today.

⚑ `liveRunSeed` and `slotCommitment` are written as the exact BYTES of the two sponge
outputs, and the two theorems below are what makes them the derivation rather than a
fixture's own invention.  They are not a relaxation and they are not a second shape:
`run_is_admitted` re-runs the *whole* of `admissionChecks`, including both derivation
conjuncts, under compiled evaluation, so a wrong byte here turns that `native_decide`
RED.  The reason the bytes cannot simply stay written as `HiddenInstance.runSeedFor
draw missionContext` is that `SignalTriangulation.judge` reads seed bytes 0..2 to pick
the puzzle, so every downstream `rfl` in this workbook would then reduce a Poseidon2
permutation in the kernel — 47.6 GB and 68 minutes for one file, MEASURED; see the `⚑`
note in `HiddenInstance`.  Compiled evaluation does the sponge; the kernel does not. -/
def slotSecret : HiddenInstance.SlotSecret := ⟨repeatedDigest 91⟩
def slot : EpochId := ⟨5⟩
def draw : HiddenInstance.Draw :=
  { secret := slotSecret, slot := slot, playerKey := playerKey }

def liveRunSeed : Digest32 := literalDigest
  [230, 78, 212, 73, 42, 145, 205, 88, 75, 33, 92, 167, 8, 34, 207, 209,
    12, 6, 76, 208, 127, 36, 89, 253, 134, 206, 238, 239, 176, 87, 109, 169]
  (by decide)

def slotCommitment : Digest32 := literalDigest
  [171, 128, 137, 208, 12, 70, 9, 210, 94, 83, 45, 75, 141, 35, 71, 122,
    146, 235, 81, 126, 187, 226, 13, 19, 199, 224, 101, 233, 66, 222, 93, 142]
  (by decide)

/-- The named seed IS the draw of the committed secret at this slot for this player. -/
theorem live_run_seed_is_the_derived_draw :
    liveRunSeed = HiddenInstance.runSeedFor draw missionContext := by
  native_decide

/-- The named commitment IS the commitment to that same secret at that same slot. -/
theorem slot_commitment_is_the_committed_secret :
    slotCommitment = HiddenInstance.commit slotSecret slot := by
  native_decide

def mission : MissionSpec where
  missionId
  artifact
  epoch := ⟨1⟩
  federationId := federation
  contentRoot
  activationDigest := activation
  contentSession
  -- The mission a judge holds carries the LIVE seed.  `MissionContext` is the
  -- projection the draw reads and it excludes `runSeed`, so this is a derivation
  -- and not a cycle — `HiddenInstance.context_ignores_the_run_seed`.
  -- ⚠ It names `liveRunSeed`, NOT a second inline copy of the draw: the secret and the
  -- slot are stated once, above, and the fixture below has to agree with THIS value or
  -- `admissionChecks` refuses.
  runSeed := liveRunSeed
  budget
  allowedRelics := {relic}
  privacy := .public
  ballot := .none
  artifact_matches := rfl
  allowed_relics_bounded := by simp

theorem reward_is_mission_accepted : mission.acceptsContribution reward = true := by
  native_decide

/-- ⚑ The instance `liveRunSeed` draws.  Because that seed is written as literal BYTES
(see the note above it), this measurement reduces IN THE KERNEL — `by decide`, not
`native_decide`.  The sponge stays where the note put it: in the three named compiled
theorems, and nowhere else in this workbook. -/
def signalTarget : SignalTriangulation.Code := { low := 2, mid := 0, high := 2 }

theorem signalTarget_is_the_drawn_instance :
    some signalTarget = SignalTriangulation.targetFromSeed? mission.runSeed := by decide

def signalConfig : SignalTriangulation.Config where
  target := signalTarget
  mission
  reward
  reward_accepted := reward_is_mission_accepted
  target_eq := signalTarget_is_the_drawn_instance

def active : ActiveRunState where
  game := .signal signalConfig
  federationId := federation
  contentRoot := contentRoot
  activationDigest := activation
  contentSession := contentSession
  contentEpoch := ⟨1⟩
  slot := slot
  slotSecret := slotSecret
  slotCommitment := slotCommitment
  runSeed := liveRunSeed
  world := WorldState.empty
  playerCounters := PlayerCounterTable.empty

def carrier : FinalizedCarrier where
  federationId := federation
  contentRoot := contentRoot
  activationDigest := activation
  contentSession := contentSession
  contentEpoch := ⟨1⟩
  actorRoot := actorRoot
  playerKey := playerKey
  currentPlayerCounter := 0

def runClaim : RunClaim where
  config := active.game.configClaim
  federationId := federation
  contentRoot := contentRoot
  activationDigest := activation
  contentSession := contentSession
  contentEpoch := ⟨1⟩
  slot := slot
  slotCommitment := slotCommitment
  actorRoot := actorRoot
  playerKey := playerKey
  claimedPreviousPlayerCounter := 0

def submitted : SubmittedRun := .signal [.submit signalConfig.target]

/-- Every authority and derivation check the judge performs on this journey, decided
once by compiled evaluation.  This is the whole of `admissionChecks`, which is where
`active.slotCommitment = commit …` and `active.runSeed = runSeedFor …` are checked, so
this single fact is what makes `liveRunSeed`/`slotCommitment` above the derived values
rather than named ones. -/
theorem run_is_admitted : admissionChecks active carrier runClaim = true := by
  native_decide

/-- ⚑ Built through `judgeAdmitted` rather than `judgeActive` so that the kernel never
re-decides `admissionChecks` — reducing that `dite` is the 47.6 GB Poseidon2 bomb.  The
theorem immediately below proves this is the SAME `Option JudgedRun` the authoritative
entry returns, so nothing here is a second judge. -/
def judged? : Option JudgedRun :=
  judgeAdmitted active carrier runClaim submitted run_is_admitted

theorem judged_is_the_authoritative_judge :
    judged? = judgeActive active carrier runClaim submitted :=
  (judgeActive_eq_judgeAdmitted active carrier runClaim submitted run_is_admitted).symm

def optionSomeB {T : Type} : Option T → Bool
  | some _ => true
  | none => false

theorem option_eq_some_get {T : Type} {value : Option T}
    (present : value.isSome = true) :
    value = some (value.get present) := by
  cases value <;> simp_all

theorem judged_available : optionSomeB judged? = true := by native_decide

theorem judged_isSome : judged?.isSome = true := by
  exact judged_available

def judged : JudgedRun := judged?.get judged_isSome

def archive : ArchiveState := acquire judged ArchiveState.empty

theorem judged_yielded_relic : relic ∈ judged.receipt.contribution.relics := by
  native_decide

def origin : SalvageOrigin where
  run := judged
  archive
  relic
  archived := by simp [archive, acquire]
  yielded := judged_yielded_relic

def seller : ParticipantId := ⟨sellerDigest⟩
def buyer : ParticipantId := ⟨buyerDigest⟩

def baseNote : AssetInput where
  nullifier := ⟨baseNullifier⟩
  owner := seller
  asset := .relic relic
  amount := 1

def authorityId : Digest32 := repeatedDigest 88

def substitutedNote : AssetInput where
  nullifier := ⟨repeatedDigest 115⟩
  owner := seller
  asset := .relic relic
  amount := 1

def substitutedSeller : ParticipantId := ⟨repeatedDigest 18⟩

def substitutedSellerNote : AssetInput where
  nullifier := ⟨repeatedDigest 116⟩
  owner := substitutedSeller
  asset := .relic relic
  amount := 1

def quoteNote : AssetInput where
  nullifier := ⟨quoteNullifier⟩
  owner := buyer
  asset := .intel
  amount := 10

def output : ClearingOutput := ⟨0, 1⟩

def pricing : PriceSchedule where
  buckets := 4
  buckets_pos := by decide
  quoteTick := 10
  quoteTick_pos := by decide

theorem seller_and_buyer_are_distinct : seller ≠ buyer := by native_decide

def spec : BatchSpec where
  federationId := federation
  contentRoot := contentRoot
  activationDigest := activation
  contentSession := contentSession
  contentEpoch := ⟨1⟩
  batchId := ⟨judged.receipt.playerCounter⟩
  sourceRoot := sourceRoot
  seller
  buyer
  parties_distinct := seller_and_buyer_are_distinct
  baseAsset := .relic relic
  quoteAsset := .intel
  assets_distinct := by decide
  pricing
  maxOrders := 4
  maxOrderQuantity := 15
  allowedOutputs := {output}

def privateOrder (slot : Fin 4) : Market.DarkBazaarPrivateDescriptor.PrivateOrder :=
  match slot.val with
  | 0 => ⟨⟨1, by omega⟩, ⟨1, by omega⟩⟩  -- bid one at bucket one
  | 1 => ⟨⟨4, by omega⟩, ⟨1, by omega⟩⟩  -- ask one at bucket zero
  | 2 => ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩  -- canonical padding
  | _ => ⟨⟨4, by omega⟩, ⟨0, by omega⟩⟩  -- canonical padding

def witness : PrivateWitness where
  orders := privateOrder
  blinding := fun lane => 777 + lane.val

def descriptorRoot : Fin 8 → Int :=
  V1.hash8 (rootPreimage V1.DESCRIPTOR_SESSION witness)

def bookCommitment : Digest32 := V1.digestOfRoot descriptorRoot

def orderNullifiers : Finset OrderNullifier :=
  V1.derivedOrderNullifiers descriptorRoot witness

def claim : SettlementClaim where
  spec
  privateBookCommitment := bookCommitment
  output
  baseInputs := {baseNote}
  quoteInputs := {quoteNote}
  orderNullifiers

def baseEscrow : EscrowLedger seller (.relic relic) where
  notes := {baseNote}
  notesWellFormed := by
    intro input member
    simp only [Finset.mem_singleton] at member
    subst input
    exact ⟨rfl, rfl, by decide⟩
  nullifiersInjective := by
    intro left hleft right hright _equal
    exact (Finset.mem_singleton.mp hleft).trans
      (Finset.mem_singleton.mp hright).symm

def quoteEscrow : EscrowLedger buyer .intel where
  notes := {quoteNote}
  notesWellFormed := by
    intro input member
    simp only [Finset.mem_singleton] at member
    subst input
    exact ⟨rfl, rfl, by decide⟩
  nullifiersInjective := by
    intro left hleft right hright _equal
    exact (Finset.mem_singleton.mp hleft).trans
      (Finset.mem_singleton.mp hright).symm

theorem escrow_nullifiers_are_disjoint :
    Disjoint (baseEscrow.notes.image AssetInput.nullifier)
      (quoteEscrow.notes.image AssetInput.nullifier) := by
  native_decide

def marketBefore : BazaarState :=
  BazaarState.funded spec baseEscrow quoteEscrow escrow_nullifiers_are_disjoint

def evidence? : Option (VerifiedSettlementEvidence claim) :=
  verifyV1? claim descriptorRoot witness

theorem evidence_available : optionSomeB evidence? = true := by native_decide

theorem evidence_isSome : evidence?.isSome = true := by
  exact evidence_available

def evidence : VerifiedSettlementEvidence claim := evidence?.get evidence_isSome

def marketAfter? : Option BazaarState := applySettlement claim evidence marketBefore

theorem settlement_applies : optionSomeB marketAfter? = true := by native_decide

theorem marketAfter_isSome : marketAfter?.isSome = true := by
  exact settlement_applies

def marketAfter : BazaarState := marketAfter?.get marketAfter_isSome

theorem market_after_exact :
    applySettlement claim evidence marketBefore = some marketAfter := by
  change marketAfter? = some marketAfter
  exact option_eq_some_get marketAfter_isSome

section FixtureAuthority

/- These are explicit abstract deployment inputs.  They are not generated by
the workbook: the constructors are private in `BazaarGame`, exactly because the
real deployment/crown verifier does not exist yet. -/
class FixtureCapabilities where
  authority : DeploymentAuthority authorityId
  registryGenesis : RegistryGenesis authority
  crownCertificate :
    UpstreamCrownCertificate authority origin seller baseNote sourceRoot
  envelopeAuthorization : (statement : EnvelopeStatement) →
    UpstreamEnvelopeAuthorization statement
  sameOpeningAuthorization :
    (statement : EnvelopeStatement) →
      (order : DarkBazaar.PrivateOrder) →
      UpstreamSameOpeningAuthorization statement order
  persistence : (candidate : PersistenceCandidate) →
    SuccessfulPersistence candidate.request

variable [fixture : FixtureCapabilities]

local notation "authority" => fixture.authority
local notation "registryGenesis" => fixture.registryGenesis
local notation "crownCertificate" => fixture.crownCertificate

def lot : CrownedSalvage := CrownedSalvage.ofUpstream crownCertificate

/-! ## Closed player session -/

def firstSchedule : RoundSchedule := ⟨0, 2, 6, 10⟩
def relistSchedule : RoundSchedule := ⟨8, 10, 13, 16⟩

def batchKey : BatchKey := spec.key

def refusalB {T : Type} (expected : Refusal) : Except Refusal T → Bool
  | .error actual => decide (actual = expected)
  | .ok _ => false

def acceptedB {E T : Type} : Except E T → Bool
  | .ok _ => true
  | .error _ => false

/-- Extract only after a named theorem proves success.  Unlike the former
`valueOr`, a failed command has no fallback state and cannot silently keep the
workbook moving. -/
def valueOfAccepted {E T : Type} (result : Except E T)
    (accepted : acceptedB result = true) : T :=
  match h : result with
  | .ok value => value
  | .error _ => False.elim (by simp [acceptedB] at accepted)

omit fixture in theorem accepted_result_is_exact {E T : Type} (result : Except E T)
    (accepted : acceptedB result = true) :
    result = .ok (valueOfAccepted result accepted) := by
  cases result with
  | error refusal => simp [acceptedB] at accepted
  | ok value => rfl

def crownRefusalB {T : Type} (expected : CrownAdmissionRefusal) :
    Except CrownAdmissionRefusal T → Bool
  | .error actual => decide (actual = expected)
  | .ok _ => false

def registryGenesisState : DeploymentRegistry :=
  DeploymentRegistry.open registryGenesis

def initialResult := registryGenesisState.initialize authority lot marketBefore
theorem initial_accepted : acceptedB initialResult = true := by
  rfl
def initialCandidate : PersistenceCandidate :=
  valueOfAccepted initialResult initial_accepted
def initial : DurableDeployment :=
  initialCandidate.continue (fixture.persistence initialCandidate)

theorem genesis_cas_is_explicit_and_exact :
    runtimeCas none initialCandidate.request =
      .ok (some initialCandidate.request.replacement) := by
  rfl

theorem restart_continuation_has_exact_persisted_key :
    initial.key = initialCandidate.request.replacement := by
  exact PersistenceCandidate.continuation_replacement_exact _ _

def firstOpenResult :=
  openAuthoredRound initial authority lot firstSchedule .zero .openingAwareJudge
theorem first_round_opens : acceptedB firstOpenResult = true := by
  rfl
def firstOpenCandidate : PersistenceCandidate :=
  valueOfAccepted firstOpenResult first_round_opens
def firstOpened : DurableDeployment :=
  firstOpenCandidate.continue (fixture.persistence firstOpenCandidate)

theorem first_open_has_pending_observation :
    firstOpened.observePending.isSome = true := by
  rfl
def firstPending : PendingObservation :=
  firstOpened.observePending.get first_open_has_pending_observation

def firstRoundId : RoundId := ⟨⟨1, by decide⟩⟩

theorem first_pending_round_exact : firstPending.round = firstRoundId := by
  rfl

theorem first_round_uses_only_authored_terms :
    firstOpened.observePending = some firstPending ∧
      firstPending.lot = lot.key ∧
      firstPending.orderCount = 0 ∧
      firstPending.closesAt = firstSchedule.closesAt ∧
      firstPending.expiresAt = firstSchedule.expiresAt ∧
      firstPending.status = .collecting ∧
      firstPending.preferenceIngress =
        .authenticatedCiphertextPendingOpening ∧
      firstPending.privacyGrade =
        .authenticatedCiphertextOnlyNoOpeningClaim ∧
      firstPending.envelopeBinding =
        .signatureVerifiedSameOpeningEncryptionProofMissing := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def authorization? : Option (V1.Authorization claim) :=
  V1.authorize? claim descriptorRoot witness

omit fixture in theorem authorization_available :
    optionSomeB authorization? = true := by
  native_decide

omit fixture in theorem authorization_isSome : authorization?.isSome = true := by
  exact authorization_available

def authorization : V1.Authorization claim :=
  authorization?.get authorization_isSome

omit fixture in theorem authorization_root_exact :
    authorization.root = descriptorRoot := by
  native_decide

omit fixture in theorem envelope_nullifier_exact (slot : Fin 4) :
    envelopeNullifier slot = (V1.orderId descriptorRoot slot).nullifier := by
  fin_cases slot <;> native_decide

def envelope (slot : Fin 4) : SealedEnvelope :=
  let statement : EnvelopeStatement := {
    actor := buyer
    round := firstRoundId
    batchKey
    nullifier := envelopeNullifier slot
    ciphertextCommitment := repeatedDigest (160 + slot.val)
    signatureCommitment := repeatedDigest (200 + slot.val)
  }
  SealedEnvelope.ofUpstream statement (fixture.envelopeAuthorization statement)

omit fixture in theorem signature_commitments_injective :
    Function.Injective (fun slot : Fin 4 => repeatedDigest (200 + slot.val)) := by
  decide

theorem envelope_statements_are_injective :
    Function.Injective (fun slot => (envelope slot).statement) := by
  intro left right equal
  apply signature_commitments_injective
  simpa only [envelope, SealedEnvelope.ofUpstream] using
    congrArg EnvelopeStatement.signatureCommitment equal

def bookReceipt : OpeningAwareBookReceipt :=
  OpeningAwareBookReceipt.ofUpstream claim authorization firstRoundId batchKey
    envelope envelope_statements_are_injective
    (by intro _slot; rfl)
    (by intro _slot; rfl)
    (by
      intro slot
      change envelopeNullifier slot =
        (V1.orderId authorization.root slot).nullifier
      rw [authorization_root_exact, envelope_nullifier_exact])
    (by intro slot; exact fixture.sameOpeningAuthorization _ (v1OrderAt authorization slot))

def receipt : OpeningAwareV1Receipt :=
  OpeningAwareV1Receipt.ofApplied bookReceipt evidence marketBefore marketAfter
    market_after_exact

def cancelResult := cancelRound firstOpened authority
theorem first_round_cancels : acceptedB cancelResult = true := by
  rfl
def cancelCandidate : PersistenceCandidate :=
  valueOfAccepted cancelResult first_round_cancels
def cancelled : DurableDeployment :=
  cancelCandidate.continue (fixture.persistence cancelCandidate)

def submit0Result := submitEnvelope firstOpened authority (envelope 0)
theorem envelope0_submits : acceptedB submit0Result = true := by
  rfl
def with0Candidate : PersistenceCandidate :=
  valueOfAccepted submit0Result envelope0_submits
def with0 : DurableDeployment :=
  with0Candidate.continue (fixture.persistence with0Candidate)

def submit1Result := submitEnvelope with0 authority (envelope 1)
theorem envelope1_submits : acceptedB submit1Result = true := by
  rfl
def with1Candidate : PersistenceCandidate :=
  valueOfAccepted submit1Result envelope1_submits
def with1 : DurableDeployment :=
  with1Candidate.continue (fixture.persistence with1Candidate)

def submit2Result := submitEnvelope with1 authority (envelope 2)
theorem envelope2_submits : acceptedB submit2Result = true := by
  rfl
def with2Candidate : PersistenceCandidate :=
  valueOfAccepted submit2Result envelope2_submits
def with2 : DurableDeployment :=
  with2Candidate.continue (fixture.persistence with2Candidate)

def submit3Result := submitEnvelope with2 authority (envelope 3)
theorem envelope3_submits : acceptedB submit3Result = true := by
  rfl
def with3Candidate : PersistenceCandidate :=
  valueOfAccepted submit3Result envelope3_submits
def with3 : DurableDeployment :=
  with3Candidate.continue (fixture.persistence with3Candidate)

theorem pending_view_is_honest_about_sealing_and_judge_visibility :
    ∃ observation,
      with3.observePending = some observation ∧
      observation.orderCount = 4 ∧
      observation.preferenceIngress =
        .authenticatedCiphertextPendingOpening ∧
      observation.privacyGrade =
        .authenticatedCiphertextOnlyNoOpeningClaim ∧
      observation.envelopeBinding =
        .signatureVerifiedSameOpeningEncryptionProofMissing := by
  refine ⟨_, rfl, rfl, rfl, rfl, rfl⟩

def closeClockResult := advanceClock with3 authority
theorem close_clock_advances : acceptedB closeClockResult = true := by
  rfl
def readyToCloseCandidate : PersistenceCandidate :=
  valueOfAccepted closeClockResult close_clock_advances
def readyToClose : DurableDeployment :=
  readyToCloseCandidate.continue (fixture.persistence readyToCloseCandidate)

def closeResult := closeRound readyToClose authority bookReceipt
theorem exact_book_closes : acceptedB closeResult = true := by
  rfl
def closeCandidate : PersistenceCandidate :=
  valueOfAccepted closeResult exact_book_closes
def closed : DurableDeployment :=
  closeCandidate.continue (fixture.persistence closeCandidate)

theorem closed_has_pending_observation : closed.observePending.isSome = true := by
  rfl

def closedPending : PendingObservation :=
  closed.observePending.get closed_has_pending_observation

theorem closed_pending_exact : closed.observePending = some closedPending := by
  exact option_eq_some_get closed_has_pending_observation

theorem closed_pending_lot_exact : closedPending.lot = lot.key := by
  rfl

theorem closed_view_records_exact_same_opening_binding :
    ∃ observation,
      closed.observePending = some observation ∧
      observation.orderCount = 4 ∧
      observation.status = .awaitingOpeningAwareJudge ∧
      observation.preferenceIngress = .v1SameOpeningBound ∧
      observation.privacyGrade =
        .commitmentsPublicOpeningVisibleToJudge ∧
      observation.envelopeBinding =
        .v1CiphertextsBoundToExactPrivateOrders := by
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

def settleResult := settleRound closed authority receipt
theorem exact_settlement_accepts : acceptedB settleResult = true := by
  rfl
def settleCandidate : PersistenceCandidate :=
  valueOfAccepted settleResult exact_settlement_accepts
def settled : DurableDeployment :=
  settleCandidate.continue (fixture.persistence settleCandidate)

theorem settled_story_and_custody_are_exact :
    settled.key.history.length = 1 ∧
      lot.key ∉ settled.key.inventory.maker ∧
      lot.key ∈ settled.key.inventory.taker ∧
      lot.key ∉ settled.key.inventory.escrow ∧
      claim.spec.key ∈ settled.key.consumedSettlements ∧
      settled.key.market = observeState marketAfter ∧
      settled.observePending = none := by
  have keyExact : settled.key = settleCandidate.request.replacement :=
    PersistenceCandidate.continuation_replacement_exact _ _
  have custody := settleRound_success_moves_observed_lot closed authority receipt
    settleCandidate closedPending closed_pending_exact
    (accepted_result_is_exact settleResult exact_settlement_accepts)
  have custodyExact :
      lot.key ∉ settleCandidate.request.replacement.inventory.maker ∧
        lot.key ∈ settleCandidate.request.replacement.inventory.taker ∧
        lot.key ∉ settleCandidate.request.replacement.inventory.escrow ∧
        claim.spec.key ∈ settleCandidate.request.replacement.consumedSettlements := by
    -- v4.35: simp no longer unfolds `receipt.claim` to `claim`; the identity is definitional.
    have hclaim : receipt.claim.spec.key = claim.spec.key := rfl
    simpa [closed_pending_lot_exact, hclaim] using custody
  rw [keyExact]
  exact ⟨rfl, custodyExact.1, custodyExact.2.1, custodyExact.2.2.1,
    custodyExact.2.2.2, rfl, rfl⟩

theorem settlement_consumes_every_private_order_nullifier :
    claim.orderNullifiers ⊆ settled.key.market.consumedOrderNullifiers := by
  change claim.orderNullifiers ⊆
    (observeState marketAfter).consumedOrderNullifiers
  exact applySettlement_consumes_order_nullifiers evidence market_after_exact

theorem receipt_currency_arithmetic_is_u64_bounded :
    receipt.claim.quotePrice ≤ Wire.u64Max ∧
      receipt.claim.quoteAmount ≤ Wire.u64Max :=
  receipt.quote_currency_bounded

theorem latest_clearing_is_public_bounded_and_preference_free :
    ∃ clearing,
      settled.observeLatestClearing = some clearing ∧
      clearing.lot = lot.key ∧
      clearing.quoteAsset = .intel ∧
      clearing.bucket = 0 ∧
      clearing.unitQuote = 10 ∧
      clearing.volume = 1 ∧
      clearing.totalQuote = 10 ∧
      clearing.orderCount = 4 ∧
      clearing.privacyGrade = .commitmentsPublicOpeningVisibleToJudge ∧
      clearing.preferenceIngress = .v1SameOpeningBound := by
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Hostile and unsupported paths -/

/-- The cancel successor won the external CAS.  A perfectly valid order
proposal computed from the losing pre-cancel fork is therefore refused before
it can become canonical. -/
theorem serialized_cancel_wins_and_same_old_submit_loses :
    runtimeCas cancelCandidate.request.expected cancelCandidate.request =
        .ok (some cancelCandidate.request.replacement) ∧
      runtimeCas (some cancelCandidate.request.replacement) with0Candidate.request =
        .error .staleCanonicalHead := by
  constructor <;> rfl

theorem substituted_note_rejected_by_exact_certificate :
    crownRefusalB .noteDoesNotMatchCertificate
      (CrownedSalvage.admitRequested crownCertificate seller substitutedNote) = true := by
  rfl

theorem substituted_seller_rejected_by_exact_certificate :
    crownRefusalB .sellerDoesNotMatchCertificate
      (CrownedSalvage.admitRequested crownCertificate substitutedSeller baseNote) = true := by
  rfl

def duplicateResult :=
  submitEnvelope with0 authority (envelope 0)
theorem duplicate_nullifier_refused :
    refusalB .duplicateOrderNullifier duplicateResult = true := by
  rfl

def replayedNullifierEnvelope : SealedEnvelope :=
  let statement : EnvelopeStatement := {
    actor := buyer
    round := firstPending.round
    batchKey
    nullifier := (envelope 0).nullifier
    ciphertextCommitment := repeatedDigest 250
    signatureCommitment := repeatedDigest 251
  }
  SealedEnvelope.ofUpstream statement (fixture.envelopeAuthorization statement)

theorem changed_ciphertext_cannot_replay_nullifier :
    refusalB .duplicateOrderNullifier
      (submitEnvelope with0 authority replayedNullifierEnvelope) = true := by
  rfl

def fifthEnvelope : SealedEnvelope :=
  let statement : EnvelopeStatement := {
    actor := buyer
    round := firstPending.round
    batchKey
    nullifier := ⟨repeatedDigest 220⟩
    ciphertextCommitment := repeatedDigest 221
    signatureCommitment := repeatedDigest 222
  }
  SealedEnvelope.ofUpstream statement (fixture.envelopeAuthorization statement)

theorem fifth_envelope_refused_at_capacity :
    refusalB .orderCapacityReached
      (submitEnvelope with3 authority fifthEnvelope) = true := by
  rfl

def nonzeroFees : FeePolicy := ⟨1, 0⟩

def nonzeroSettlementFees : FeePolicy := ⟨0, 1⟩

theorem listing_fee_refused_without_conserving_receipt :
    refusalB .nonzeroListingFeeNeedsConservingReceipt
      (openAuthoredRound initial authority lot firstSchedule nonzeroFees
        .openingAwareJudge) = true := by
  rfl

theorem settlement_fee_refused_without_conserving_receipt :
    refusalB .nonzeroSettlementFeeNeedsConservingReceipt
      (openAuthoredRound initial authority lot firstSchedule nonzeroSettlementFees
        .openingAwareJudge) = true := by
  rfl

theorem substituted_buyer_refused_as_unauthored_market :
    refusalB .authoredMarketMismatch
      (openRound initial authority lot substitutedSeller .intel firstSchedule 4 .zero
        .openingAwareJudge) = true := by
  rfl

theorem substituted_currency_refused_as_unauthored_market :
    refusalB .authoredMarketMismatch
      (openRound initial authority lot buyer .supplies firstSchedule 4 .zero
        .openingAwareJudge) = true := by
  rfl

theorem substituted_order_bound_refused_as_unauthored_market :
    refusalB .authoredMarketMismatch
      (openRound initial authority lot buyer .intel firstSchedule 3 .zero
        .openingAwareJudge) = true := by
  rfl

theorem house_blind_refused_before_custody_lock :
    refusalB .houseBlindProofUnavailable
      (openRound initial authority lot buyer .intel firstSchedule 4 .zero
        .houseBlind) = true := by
  rfl

def expiryClock1Result := advanceClock closed authority
theorem expiry_clock1_accepts : acceptedB expiryClock1Result = true := by
  rfl
def expiryClock1Candidate := valueOfAccepted expiryClock1Result expiry_clock1_accepts
def expiryClock1 : DurableDeployment :=
  expiryClock1Candidate.continue (fixture.persistence expiryClock1Candidate)
def expiryClock2Result := advanceClock expiryClock1 authority
theorem expiry_clock2_accepts : acceptedB expiryClock2Result = true := by
  rfl
def expiryClock2Candidate := valueOfAccepted expiryClock2Result expiry_clock2_accepts
def expiryClock2 : DurableDeployment :=
  expiryClock2Candidate.continue (fixture.persistence expiryClock2Candidate)
def expiryClock3Result := advanceClock expiryClock2 authority
theorem expiry_clock3_accepts : acceptedB expiryClock3Result = true := by
  rfl
def expiryClock3Candidate := valueOfAccepted expiryClock3Result expiry_clock3_accepts
def expiryClock3 : DurableDeployment :=
  expiryClock3Candidate.continue (fixture.persistence expiryClock3Candidate)

theorem expiry_clock3_has_pending_observation :
    expiryClock3.observePending.isSome = true := by
  rfl

def expiryPending : PendingObservation :=
  expiryClock3.observePending.get expiry_clock3_has_pending_observation

theorem expiry_pending_exact : expiryClock3.observePending = some expiryPending := by
  exact option_eq_some_get expiry_clock3_has_pending_observation

theorem expiry_pending_lot_exact : expiryPending.lot = lot.key := by
  rfl

theorem clock_cannot_cross_active_expiry :
    refusalB .activeRoundRequiresExpiry
      (advanceClock expiryClock3 authority) = true := by
  rfl

def expireResult := expireRound expiryClock3 authority
theorem expired_round_accepts : acceptedB expireResult = true := by
  rfl
def expireCandidate := valueOfAccepted expireResult expired_round_accepts
def expired : DurableDeployment :=
  expireCandidate.continue (fixture.persistence expireCandidate)

theorem expiry_returns_lot :
    lot.key ∈ expired.key.inventory.maker ∧
      lot.key ∉ expired.key.inventory.escrow ∧
      expired.observePending = none := by
  have keyExact : expired.key = expireCandidate.request.replacement :=
    PersistenceCandidate.continuation_replacement_exact _ _
  have custody := expireRound_success_returns_observed_lot expiryClock3 authority
    expireCandidate expiryPending expiry_pending_exact
    (accepted_result_is_exact expireResult expired_round_accepts)
  have custodyExact :
      lot.key ∈ expireCandidate.request.replacement.inventory.maker ∧
        lot.key ∉ expireCandidate.request.replacement.inventory.escrow := by
    simpa [expiry_pending_lot_exact] using custody
  rw [keyExact]
  exact ⟨custodyExact.1, custodyExact.2, rfl⟩

theorem settlement_replay_refused :
    refusalB .noOpenRound (settleRound settled authority receipt) = true := by
  rfl

theorem sold_lot_double_list_refused :
    refusalB .lotNotMakerOwned
      (openRound settled authority lot buyer .intel relistSchedule 4 .zero
        .openingAwareJudge) = true := by
  rfl

omit fixture in theorem eligible_origin_remains_observation_only :
    inspectEligible origin = .observationOnly origin .runtimeCrownProofMissing := rfl

#assert_compiled live_run_seed_is_the_derived_draw
#assert_compiled slot_commitment_is_the_committed_secret
#assert_compiled run_is_admitted
#assert_compiled judged_is_the_authoritative_judge
#assert_compiled reward_is_mission_accepted
#assert_compiled judged_available
#assert_compiled judged_isSome
#assert_compiled judged_yielded_relic
#assert_compiled seller_and_buyer_are_distinct
#assert_compiled escrow_nullifiers_are_disjoint
#assert_compiled evidence_available
#assert_compiled evidence_isSome
#assert_compiled settlement_applies
#assert_compiled marketAfter_isSome
#assert_compiled market_after_exact
#assert_axioms option_eq_some_get
#assert_axioms accepted_result_is_exact
#assert_compiled initial_accepted
#assert_compiled genesis_cas_is_explicit_and_exact
#assert_compiled restart_continuation_has_exact_persisted_key
#assert_compiled first_round_opens
#assert_compiled first_open_has_pending_observation
#assert_compiled first_pending_round_exact
#assert_compiled first_round_uses_only_authored_terms
#assert_compiled authorization_available
#assert_compiled authorization_isSome
#assert_compiled authorization_root_exact
#assert_compiled envelope_nullifier_exact
#assert_axioms signature_commitments_injective
#assert_compiled envelope_statements_are_injective
#assert_compiled first_round_cancels
#assert_compiled envelope0_submits
#assert_compiled envelope1_submits
#assert_compiled envelope2_submits
#assert_compiled envelope3_submits
#assert_compiled pending_view_is_honest_about_sealing_and_judge_visibility
#assert_compiled close_clock_advances
#assert_compiled exact_book_closes
#assert_compiled closed_has_pending_observation
#assert_compiled closed_pending_exact
#assert_compiled closed_pending_lot_exact
#assert_compiled closed_view_records_exact_same_opening_binding
#assert_compiled exact_settlement_accepts
#assert_compiled settled_story_and_custody_are_exact
#assert_compiled settlement_consumes_every_private_order_nullifier
#assert_compiled receipt_currency_arithmetic_is_u64_bounded
#assert_compiled latest_clearing_is_public_bounded_and_preference_free
#assert_compiled serialized_cancel_wins_and_same_old_submit_loses
#assert_compiled substituted_note_rejected_by_exact_certificate
#assert_compiled substituted_seller_rejected_by_exact_certificate
#assert_compiled duplicate_nullifier_refused
#assert_compiled changed_ciphertext_cannot_replay_nullifier
#assert_compiled fifth_envelope_refused_at_capacity
#assert_compiled listing_fee_refused_without_conserving_receipt
#assert_compiled settlement_fee_refused_without_conserving_receipt
#assert_compiled substituted_buyer_refused_as_unauthored_market
#assert_compiled substituted_currency_refused_as_unauthored_market
#assert_compiled substituted_order_bound_refused_as_unauthored_market
#assert_compiled house_blind_refused_before_custody_lock
#assert_compiled expiry_clock1_accepts
#assert_compiled expiry_clock2_accepts
#assert_compiled expiry_clock3_accepts
#assert_compiled expiry_clock3_has_pending_observation
#assert_compiled expiry_pending_exact
#assert_compiled expiry_pending_lot_exact
#assert_compiled clock_cannot_cross_active_expiry
#assert_compiled expired_round_accepts
#assert_compiled expiry_returns_lot
#assert_compiled settlement_replay_refused
#assert_compiled sold_lot_double_list_refused
#assert_compiled eligible_origin_remains_observation_only

end FixtureAuthority

end Dregg2.Games.PathOfAngels.BazaarGameExamples
