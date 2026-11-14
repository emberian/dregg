/-
# Dregg2.Distributed.SelfSettlement — the dregg-native SELF-SETTLEMENT effect (NEW-B/NEW-C, first slice).

**What this is (the Zeko "settle to itself" loop, as a dregg turn EFFECT).** Zeko is a Mina L2 whose
state is a zkApp account on Mina L1; each L2 block produces a recursive SNARK; the L1 account verifies
the *whole* L2 history and holds its state commitment — Mina settling to Mina. dregg already has the
hard half of that (`Circuit.RecursiveAggregation` + `Distributed.FinalizedLightClient`: a light client
that verifies ONE succinct aggregate and learns the whole child chain executed, is ordered, conserves,
and was BFT-finalized — the part Mina does NOT have machine-checked). What was missing is the
*self-settlement loop*: a dregg-native L1 verifier expressed as a **turn effect** that verifies a child
`WholeChainProof` INSIDE a turn and commits the child's finalized root into a dregg-L1 rollup account.

**SUBSTRATE, SAID OUT LOUD (HOUSE LAW #1).** The settlement's verification predicate is **authored in
Lean, here**. Nothing in this campaign hand-writes a Rust AIR: the constraint set the prover will run is
to be EMITTED from Lean (a descriptor under `Dregg2/Circuit/Emit/`, reusing `ivc_turn_chain`'s in-circuit
recursion verifier as the gadget), and Rust only CALLS the emitted artifact. That emit is a NAMED
RESIDUAL below — it is not claimed as done.

  1. `RollupAccount` — the dregg-L1 account that holds a child chain's registered genesis, its latest
     finalized root and height; the native mirror of `chain/contracts/DreggPeerRegistry.sol`'s
     `_latestRoot`/`_latestHeight`. `Option ℤ` for the root makes the UNSET state `none`, never a `0`
     reinterpretable as "proven" — the Nomad law BY CONSTRUCTION (`unset_account_proves_nothing`).
     The account is keyed by the child's GENESIS ROOT (its cryptographic identity), not only by a
     nominal `childId` — so a freshly fabricated child chain cannot settle into it
     (`fabricated_genesis_cannot_settle`).
  2. `SettleChildChain` — the effect payload: the child aggregate (`WholeChainProof`), the child's
     `FinalityCert`, the shown finalized root, and the claimed height.
  3. `SettleAccepts` — the effect's acceptance predicate: the THREE-LEG light-client acceptance of the
     child's whole FINALIZED history (verify the aggregate, bind the root, genuine super-ratification
     quorum) PLUS the registered-genesis pin, the height tie, and the monotone advance. The first four
     legs are EXACTLY `FinalizedLightClient.light_client_accepts_finalized_history`'s hypotheses — so the
     child proof is verified through the **native BabyBear in-circuit recursion** boundary
     (`EngineSound`/`verify`), NOT the vacuous cross-field gnark wrap (`FriCarrierVacuity`).
  4. `settle_attests_finalized_child` — accepting a settlement attests the child's whole finalized
     history (every child turn executed, ordered, quorum-finalized). Direct reuse of the proven headline.
  5. `settled_root_is_child_final_fold` / `receipt_root_is_child_final_fold` (**THE L2-COMMITMENT
     BINDING LEMMA**) — the root the parent L1 account/receipt now holds IS the genuine fold of the
     child's whole history. The L2 commitment sitting on the L1 is bound to the child's entire executed,
     finalized history — no re-execution. `settlement_root_is_unique` adds the anti-equivocation edge:
     no two accepted settlements of one child history can commit different roots.
  6. `settle_conserves_child_producer_witness` — child value-conservation from an executor-genuine
     `StateChained` witness. It is `FinalizedLightClient.finalized_history_conserves` under a new name:
     the statement mentions no parent, no settlement and no account, and it does NOT consume the
     settlement. ⚠ The stronger verification-derived form is DELIBERATELY NOT TAKEN: see the floor
     note below.
  7. Teeth: stale/replayed (`stale_settlement_rejected`), forged anchor (`forged_anchor_cannot_settle`),
     root mismatch (`root_mismatch_cannot_settle`), fabricated child genesis
     (`fabricated_genesis_cannot_settle`), and the unset account proving nothing.
  8. Non-vacuity: the settlement FIRES on the realizing child chain of `FinalizedLightClient`
     (`settle_fires_on_real_child`), advancing a registered account by a real, quorum-finalized child.

**⚠ THE CONSERVATION LEG THE L1 CANNOT YET HAVE (a refused import, not an oversight).** The strong
form — the parent deriving child value-conservation from the SETTLEMENT'S OWN legs (`h.engine` +
`h.root_ok`), with no prover-supplied `StateChained` — would ride
`RecursiveAggregation.conserves_from_verification`. That theorem carries `compressInjective`,
`compressNInjective` and `cellLeafInjective`, all of which THIS TREE REFUTES at deployed BabyBear
parameters; a settlement-level restatement would therefore be VACUOUSLY TRUE at deployment and would
tell an operator nothing about the shipping system. It was written, measured against the floor ratchet,
and REMOVED rather than recorded as a new floor carrier. What remains here is the honest
producer-witness form. Adopting the strong form requires the `_or_collides` + total-extractor PORT of
`conserves_from_verification` upstream first — named, not carried.

**⚑ THE HEIGHT REGISTER IS NOW PINNED (2026-07-28) — and the "residual" it named never existed.** This
header used to say `Aggregate.numTurns` is pinned by NO leg of `EngineSound`, carry
`engineSound_numTurns_irrelevant` + `settle_accepts_inflated_height` as the proof of it, and name
"pin `numTurns` in the chain-binding AIR" as the remaining work. The AIR had pinned it all along:
`Emit/EffectVmEmitTurnChainBinding.lean` constraint 14 (`lastRealCountBind`,
`real_count[last] = pi[num_turns]`) is in the byte-golden descriptor, and
`BindingAirSound.Satisfies.count` models it. The leak was one layer up — the keystone
`binding_air_discharges_binding_sound` held the count in its hypothesis and dropped it, so
`EngineSound.binding_sound` had nowhere to put it. Carried across now (no new crypto), so
`binding_sound` and `AggregateAttests.turns_pinned` give `agg.numTurns = steps.length`, and §8 proves
the opposite of what it used to: `settle_height_is_child_turn_count` (the height IS the child's turn
count), `inflated_height_cannot_settle` (the tooth), `settlement_height_is_unique`,
`replayed_settlement_cannot_advance`. The three superseded theorems are DELETED, not kept alongside.

**Why the native recursion, not the gnark wrap (the single most important design constraint).** The
cross-field gnark wrap (STARK→BN254→Groth16) is the EXTERNAL-EVM settlement path and its FRI carrier is
proven vacuous (`Dregg2.Circuit.FriCarrierVacuity`, ~31-bit deployed query floor). A *dregg-native*
self-settlement verifies the child with the **native BabyBear in-circuit recursion** of
`ivc_turn_chain`, whose floor is the genuine `EngineSound` boundary. By reusing
`light_client_accepts_finalized_history` unchanged, this effect inherits exactly that boundary and
nothing weaker.

**The honest slice-vs-remaining split (claim the slice, not a working L2).** THIS SLICE authors, in
Lean: the effect data, its acceptance predicate, the whole-finalized-child attestation, the
L2-commitment binding lemma, the PRODUCER-WITNESS conservation (the verification-derived form is
REFUSED — see the floor note), the monotone/anti-ghost teeth, the height pin + its teeth, and
non-vacuity. There is **no working L2** here: nothing executes, nothing is emitted, no Rust calls
this yet.

**NAMED RESIDUALS (NOT built here):**
  * **Recursion-as-effect THREADING.** Wiring `SettleChildChain` into the real turn `Effect` inductive
    (`Dregg2.Exec.Effect`) + the executor (`recCexec`/`execFullTurnA`), and EMITTING its verify-constraint
    as a real descriptor under `Dregg2/Circuit/Emit/` (reusing `ivc_turn_chain`'s in-circuit recursion
    verifier as the gadget). This slice keeps `verify : Proof → Bool` opaque exactly as
    `RecursiveAggregation` does — the concrete instantiation (the in-circuit BabyBear recursion inside a
    turn circuit) is that threading, and the SAME named crypto floor.
  * **The online FOLD DRIVER (`fold_two_turns`, `circuit-prove/src/ivc_turn_chain.rs:5678`).** For an
    UNBOUNDED settled child (Zeko's perpetual accumulator). The soundness induction is already proven
    (`RecursiveAggregation.accumulate_preserves_wellformed`); the crypto driver is unbuilt. Optional for
    a bounded-window rollup.
  * **The concrete L1 account CELL + deposit/withdraw bridge (NEW-C full).** Persisting `RollupAccount`
    as a real `RecordKernelState` cell advanced only by the effect, with deposits/withdrawals binding
    the commitment (reusing `Dregg2.Bridge.HoldingFoldRecursive`). This slice models the account
    abstractly (`RollupAccount` + `applySettle`); the concrete cell + its emit is the remaining assembly.
  * **The `_or_collides` port of `conserves_from_verification`**, without which the L1 cannot inherit
    child conservation from verification non-vacuously (see the floor note above).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). Verified with
`lake build Dregg2.Distributed.SelfSettlement`.
-/
import Dregg2.Distributed.FinalizedLightClient

namespace Dregg2.Distributed.SelfSettlement

open Dregg2.Exec (RecChainedState recCexec recTotal)
open Dregg2.Distributed.HistoryAggregation
  (ChainStep foldedFinalRoot lastStateOf StateChained)
open Dregg2.Circuit.RecursiveAggregation
  (Aggregate EngineSound AggregateAttests)
open Dregg2.Distributed.FinalizedLightClient
  (FinalityCert CertValid Bound FinalizedHistoryAttested
   light_client_accepts_finalized_history finalized_history_conserves
   not_final_leader_invalidates root_mismatch_unbinds)

section Effect

variable (Proof : Type)
variable (verify : Proof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-! ## 1. The L1 ROLLUP ACCOUNT — the dregg-native mirror of `DreggPeerRegistry`'s state.

`DreggPeerRegistry.sol` holds, per child `chainId`, `_latestRoot` + `_latestHeight`, advanced only by a
proof-gated `submitPeerFinality`, monotone, with the NOMAD LAW (`bytes32(0)` is never recorded, so an
uninitialized slot never reads as "proven"). A dregg-native L1 rollup account is the SAME shape as
in-state data, advanced only by the settlement EFFECT, with two deliberate strengthenings:

  * the latest root is `Option ℤ`, so `none` is the UNSET default and there is no `0`-that-reads-as-
    proven — the Nomad hazard is absent BY CONSTRUCTION (the unset shape refuses to answer rather than
    reinterpret);
  * the account REGISTERS the child's genesis root. A nominal `chainId` is not a cryptographic
    identity: without the genesis pin, a prover could fold a freshly fabricated chain of its own
    choosing and settle it into the account. `childGenesis` is what the settlement is checked against
    (`fabricated_genesis_cannot_settle`, `settle_starts_at_registered_genesis`). -/

/-- **`RollupAccount`** — a dregg-L1 account tracking one child chain's settled state: the child
identity, the child's REGISTERED genesis root (its cryptographic identity), its latest settled root
(`none` = nothing settled yet — the Nomad default), and the height (the child `num_turns`) at which
that root was settled. Advanced ONLY by `applySettle`. -/
structure RollupAccount where
  /-- The child chain identity (the `srcChainId` analogue — nominal, NOT the cryptographic identity). -/
  childId      : ℤ
  /-- The child chain's REGISTERED genesis root — the chain's cryptographic identity, fixed at
  registration and never advanced by a settlement. -/
  childGenesis : ℤ
  /-- The child's latest settled state root; `none` = UNSET (nothing settled — the Nomad default). -/
  latestRoot   : Option ℤ
  /-- The child `num_turns` at which `latestRoot` was settled (0 for a fresh account). -/
  latestHeight : Nat

/-- **`RollupAccount.register c gen`** — a fresh L1 rollup account for child `c` whose chain starts at
the registered genesis root `gen`: nothing settled, height 0. -/
def RollupAccount.register (c : ℤ) (gen : ℤ) : RollupAccount := ⟨c, gen, none, 0⟩

/-- **`RollupAccount.provenRoot acc r`** — the account currently attests child root `r`. A fresh
account (`latestRoot = none`) attests NOTHING — the Nomad law (`unset_account_proves_nothing`). -/
def RollupAccount.provenRoot (acc : RollupAccount) (r : ℤ) : Prop := acc.latestRoot = some r

/-! ## 2. The SETTLEMENT EFFECT — a turn effect verifying a child `WholeChainProof`. -/

/-- **`SettleChildChain`** — the settlement effect payload the parent turn carries: the child's
succinct aggregate (`WholeChainProof` = `Aggregate Proof`), the child's finality certificate, the
shown finalized root, and the claimed new height. The parent turn sees ONLY this — never the child's
steps, never its states. -/
structure SettleChildChain where
  /-- The child chain's succinct whole-history aggregate (the `WholeChainProof`). -/
  childAgg      : Aggregate Proof
  /-- The child chain's finality certificate (quorum / tau over the finalized head). -/
  childCert     : FinalityCert
  /-- The finalized child state root this settlement commits into the L1 account. -/
  finalizedRoot : ℤ
  /-- The height this settlement claims — tied to the aggregate's public `numTurns` by
  `SettleAccepts.height_is_count`. See the module header: that public field is NOT engine-pinned. -/
  newHeight     : Nat

/-! ## 3. The VERIFICATION PREDICATE — when the settlement effect ACCEPTS.

The predicate is the THREE-LEG finalized-light-client acceptance (`light_client_accepts_finalized_history`)
of the child's whole history — verify the aggregate, bind the root, genuine super-ratification quorum —
PLUS the registered-genesis pin, the height tie, and the account-level MONOTONE advance. It is
interpreted against the child's genesis `g` and step list `steps` exactly as `FinalizedLightClient` is
(threaded, never re-witnessed by the parent). -/

/-- **`SettleAccepts acc s g steps`** — the parent turn ACCEPTS settlement `s` against account `acc`
(interpreted against the child's genesis `g` + steps `steps`) when:
  * `engine` — the recursion engine is sound for the child aggregate (the NAMED native-BabyBear floor);
  * `root_ok` — the child aggregate's root verifies (`verify s.childAgg.root = true`);
  * `bound` — the root seam binds (`agg.finalRoot = cert.finalizedRoot = s.finalizedRoot`);
  * `cert_ok` — the child's finality cert is a genuine super-ratification quorum (the node's real rule);
  * `genesis_ok` — the child aggregate's public genesis root IS the account's REGISTERED genesis (a
    fabricated child chain cannot settle here);
  * `height_is_count` — the claimed height is the aggregate's public `numTurns` (advisory — see header);
  * `monotone` — the height strictly advances (`acc.latestHeight < s.newHeight`) — replay/stale refused.
The first four legs are EXACTLY `light_client_accepts_finalized_history`'s hypotheses. -/
structure SettleAccepts (acc : RollupAccount) (s : SettleChildChain Proof)
    (g : RecChainedState) (steps : List ChainStep) : Prop where
  /-- The recursion engine soundness for the child aggregate — the native-BabyBear `EngineSound`
  boundary (NOT the vacuous gnark wrap). -/
  engine          : EngineSound Proof verify CH RH cmb compress compressN s.childAgg g steps
  /-- The child aggregate's root verifies. -/
  root_ok         : verify s.childAgg.root = true
  /-- The root seam: the aggregate's, the cert's, and the shown finalized root all coincide. -/
  bound           : Bound Proof s.childAgg s.childCert s.finalizedRoot
  /-- The child's finality cert is a genuine super-ratification quorum (the node's real `tau` rule). -/
  cert_ok         : CertValid s.childCert
  /-- The settled chain is THE REGISTERED CHILD: its public genesis root is the account's. -/
  genesis_ok      : s.childAgg.genesisRoot = acc.childGenesis
  /-- The claimed height is the aggregate's public turn count. -/
  height_is_count : s.newHeight = s.childAgg.numTurns
  /-- Monotone finality: the settled height strictly advances (a stale/replayed root is refused). -/
  monotone        : acc.latestHeight < s.newHeight

/-- **`applySettle acc s`** — the L1 account state transition the settlement effect performs: commit the
child's finalized root and advance the height. This is the ONLY writer of a `RollupAccount` (the
`DreggPeerRegistry` "record" step). The `childId` and the REGISTERED `childGenesis` are preserved — a
settlement never re-homes an account nor re-registers its chain. -/
def applySettle (acc : RollupAccount) (s : SettleChildChain Proof) : RollupAccount :=
  { childId      := acc.childId
  , childGenesis := acc.childGenesis
  , latestRoot   := some s.finalizedRoot
  , latestHeight := s.newHeight }

/-! ## 4. The RECEIPT the settlement effect leaves (the through-line: a turn leaves a receipt). -/

/-- **`SettleReceipt`** — the receipt the parent turn leaves when the settlement commits: which child
chain, the root committed, the height. (`DreggPeerRegistry`'s `PeerFinalityProven` event.) The
BINDING LEMMA below proves this `settledRoot` is the child's genuine whole-history fold. -/
structure SettleReceipt where
  /-- The child chain settled. -/
  childId     : ℤ
  /-- The finalized child root committed by this settlement. -/
  settledRoot : ℤ
  /-- The height at which it settled. -/
  height      : Nat

/-- **`emitReceipt s childId`** — the receipt a settlement of child `childId` leaves in the parent turn. -/
def emitReceipt (s : SettleChildChain Proof) (childId : ℤ) : SettleReceipt :=
  ⟨childId, s.finalizedRoot, s.newHeight⟩

/-! ## 5. THE HEADLINE — accepting a settlement attests the child's whole FINALIZED history. -/

/-- **`settle_attests_finalized_child` (THE SETTLEMENT HEADLINE).** When the parent turn accepts a
settlement, it obtains `FinalizedHistoryAttested` for the child: every child turn executed correctly,
the child chain is correctly ordered, the endpoint root is the genuine fold, AND that root was
finalized by a BFT super-ratification quorum — the parent re-executing nothing of the child. A direct
reuse of the proven `light_client_accepts_finalized_history` (hence of the native-BabyBear recursion
light client `light_client_verifies_whole_history`). -/
theorem settle_attests_finalized_child
    (acc : RollupAccount) (s : SettleChildChain Proof) (g : RecChainedState) (steps : List ChainStep)
    (h : SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps) :
    FinalizedHistoryAttested Proof CH RH cmb compress compressN
      s.childAgg g steps s.childCert s.finalizedRoot :=
  light_client_accepts_finalized_history Proof verify CH RH cmb compress compressN
    s.childAgg g steps s.childCert s.finalizedRoot h.engine h.root_ok h.bound h.cert_ok

/-! ## 6. THE L2-COMMITMENT BINDING LEMMA — the L1 root IS the child's genuine whole-history fold. -/

/-- **`settled_root_is_child_final_fold` (THE L2-COMMITMENT BINDING LEMMA — account side).** After the
settlement commits, the root sitting in the parent L1 account IS the genuine fold of the child's WHOLE
history: `(applySettle acc s).latestRoot = some (foldedFinalRoot … g steps)`. The L2 commitment the L1
now holds is BOUND to the child's entire executed, correctly-ordered, quorum-finalized history — the
parent stored one field element and thereby committed to the whole child chain. -/
theorem settled_root_is_child_final_fold
    (acc : RollupAccount) (s : SettleChildChain Proof) (g : RecChainedState) (steps : List ChainStep)
    (h : SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps) :
    (applySettle Proof acc s).latestRoot
      = some (foldedFinalRoot CH RH cmb compress compressN g steps) := by
  have hatt := settle_attests_finalized_child Proof verify CH RH cmb compress compressN acc s g steps h
  -- the shown root is the aggregate's finalRoot (Bound), which is the genuine fold (AggregateAttests).
  have h1 : s.finalizedRoot = s.childAgg.finalRoot := hatt.root_is_finalized.1.symm
  have h2 : s.childAgg.finalRoot = foldedFinalRoot CH RH cmb compress compressN g steps :=
    hatt.history.final_is_genuine_fold
  simp only [applySettle, h1, h2]

/-- **`receipt_root_is_child_final_fold` (THE L2-COMMITMENT BINDING LEMMA — receipt side).** The
`settledRoot` in the receipt the parent turn LEAVES is the genuine fold of the child's whole history.
So the child root is bound in the parent turn's receipt, not merely in transient account state — an
auditor reading the receipt reads a commitment to the child's entire finalized history. -/
theorem receipt_root_is_child_final_fold
    (acc : RollupAccount) (s : SettleChildChain Proof) (g : RecChainedState) (steps : List ChainStep)
    (h : SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps) :
    (emitReceipt Proof s acc.childId).settledRoot
      = foldedFinalRoot CH RH cmb compress compressN g steps := by
  have hatt := settle_attests_finalized_child Proof verify CH RH cmb compress compressN acc s g steps h
  have h1 : s.finalizedRoot = s.childAgg.finalRoot := hatt.root_is_finalized.1.symm
  have h2 : s.childAgg.finalRoot = foldedFinalRoot CH RH cmb compress compressN g steps :=
    hatt.history.final_is_genuine_fold
  simp only [emitReceipt, h1, h2]

/-- **`settlement_root_is_unique` (THE ANTI-EQUIVOCATION EDGE).** Two ACCEPTED settlements of the SAME
child history commit the SAME root — whatever accounts, certs or claimed heights they carry. So the
committed L2 commitment is a FUNCTION of the child's history: a prover cannot present one child chain
to two parents (or twice to one) and have different roots recorded. -/
theorem settlement_root_is_unique
    (acc acc' : RollupAccount) (s s' : SettleChildChain Proof)
    (g : RecChainedState) (steps : List ChainStep)
    (h : SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps)
    (h' : SettleAccepts Proof verify CH RH cmb compress compressN acc' s' g steps) :
    s.finalizedRoot = s'.finalizedRoot := by
  have hatt := settle_attests_finalized_child Proof verify CH RH cmb compress compressN acc s g steps h
  have hatt' := settle_attests_finalized_child Proof verify CH RH cmb compress compressN acc' s' g steps h'
  have e1 : s.finalizedRoot = foldedFinalRoot CH RH cmb compress compressN g steps := by
    rw [← hatt.root_is_finalized.1]; exact hatt.history.final_is_genuine_fold
  have e2 : s'.finalizedRoot = foldedFinalRoot CH RH cmb compress compressN g steps := by
    rw [← hatt'.root_is_finalized.1]; exact hatt'.history.final_is_genuine_fold
  rw [e1, e2]

/-- **`settle_starts_at_registered_genesis` (the child is THE registered child).** An accepted
settlement's history genuinely STARTS at the account's registered genesis: the registered
`childGenesis` IS the first step's pre-root. So the parent is not merely told which chain it settled —
the verified aggregate pins it (`AggregateAttests.genesis_pinned`). -/
theorem settle_starts_at_registered_genesis
    (acc : RollupAccount) (s : SettleChildChain Proof) (g : RecChainedState) (steps : List ChainStep)
    (st : ChainStep) (hhead : steps.head? = some st)
    (h : SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps) :
    acc.childGenesis
      = Dregg2.Distributed.HistoryAggregation.ChainStep.oldRoot CH RH cmb compress compressN st := by
  have hatt := settle_attests_finalized_child Proof verify CH RH cmb compress compressN acc s g steps h
  have hp := hatt.history.genesis_pinned
  simp only [hhead] at hp
  rw [← h.genesis_ok]
  exact hp

/-- **`settle_advances_monotone`.** The settlement strictly ADVANCES the account height — the rollup
account is a monotone register (`DreggPeerRegistry`'s monotone-height law), so a later reader sees a
height that only ever grows. -/
theorem settle_advances_monotone
    (acc : RollupAccount) (s : SettleChildChain Proof) (g : RecChainedState) (steps : List ChainStep)
    (h : SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps) :
    acc.latestHeight < (applySettle Proof acc s).latestHeight := by
  simpa [applySettle] using h.monotone

/-- **`settled_account_proves_root`.** After settlement, the account attests exactly the committed
finalized root — the dregg-native `isProvenPeerRoot` reading true for the just-settled root. -/
theorem settled_account_proves_root
    (acc : RollupAccount) (s : SettleChildChain Proof) :
    (applySettle Proof acc s).provenRoot s.finalizedRoot := by
  simp [applySettle, RollupAccount.provenRoot]

/-- **`settle_preserves_registration`.** A settlement never re-registers the child: the account's
registered genesis is untouched by the write. So the identity the next settlement is checked against
cannot be moved by a settlement. -/
theorem settle_preserves_registration
    (acc : RollupAccount) (s : SettleChildChain Proof) :
    (applySettle Proof acc s).childGenesis = acc.childGenesis := rfl

/-! ## 7. CONSERVATION over the settled child history — and the form that is REFUSED.

The strong form (conservation derived from the settlement's own `engine` + `root_ok` legs, no
prover-supplied `StateChained`) rides `RecursiveAggregation.conserves_from_verification`, which carries
`compressInjective` / `compressNInjective` / `cellLeafInjective` — floors THIS TREE REFUTES at deployed
BabyBear parameters. A settlement-level restatement would be vacuous at deployment, so it is NOT taken
here; the port is a named residual (module header). Only the honest producer-witness form remains, and
it is labelled as consuming a witness rather than the settlement. -/

/-- **`settle_conserves_child_producer_witness`.** Given the executor-genuine `StateChained` witness
directly, value is conserved over the child's whole history. This is the producer-supplied route
(`FinalizedLightClient.finalized_history_conserves`): it does NOT consume the settlement, and it is
NOT the L1 learning conservation from the proof. That stronger statement is refused above until
`conserves_from_verification` is ported off its refuted floor. -/
theorem settle_conserves_child_producer_witness
    (g : RecChainedState) (steps : List ChainStep) (hch : StateChained g steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  finalized_history_conserves g steps hch

/-! ## 8. THE HEIGHT REGISTER IS PROOF-PINNED — repaired 2026-07-28, supersedes the measurement.

**What this section used to say, and why it was wrong.** It carried `engineSound_numTurns_irrelevant`
(an `EngineSound` witness transports across an arbitrary `numTurns`) and `settle_accepts_inflated_height`
(hence a prover inflates the settled height at will), and named "pin `numTurns` in the chain-binding
AIR" as the residual. **That residual did not exist.** The deployed AIR has pinned the count since it
was emitted: `Emit/EffectVmEmitTurnChainBinding.lean` constraint 14 is
`real_count[last] = pi[num_turns]` (`lastRealCountBind`, `PI_NUM_TURNS`), byte-golden in
`TURN_CHAIN_BINDING_GOLDEN`, with `firstRealCount`/`realCountAccum`/`realMonotone` making `real_count`
the genuine count of real rows; and `BindingAirSound.Satisfies.count` models exactly that.

The hole was in the MODEL's carry-across: `binding_air_discharges_binding_sound` held
`Satisfies.count` in its hypothesis and concluded only three of four facts, so
`EngineSound.binding_sound` had no slot for the count and `Aggregate.numTurns` arrived at every client
as an unconstrained public register. Fixing it costs no crypto (`Satisfies.count` +
`represents_length`, both structural). `binding_sound` and `AggregateAttests.turns_pinned` now carry
`agg.numTurns = steps.length`, so `engineSound_numTurns_irrelevant` is no longer PROVABLE — it is
false — and the two theorems below replace it with the opposite content. -/

/-- **`settle_height_is_child_turn_count` (THE PIN — supersedes `settle_accepts_inflated_height`).** An
ACCEPTED settlement's claimed height IS the number of turns in the child's history. Not an advisory
register: the binding AIR's real-count constraint forces the aggregate's public `numTurns` to the chain
length, `SettleAccepts.height_is_count` ties the claimed height to it, so the height the L1 records is
as bound as the root it records. -/
theorem settle_height_is_child_turn_count
    (acc : RollupAccount) (s : SettleChildChain Proof) (g : RecChainedState) (steps : List ChainStep)
    (h : SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps) :
    s.newHeight = steps.length := by
  have hatt := settle_attests_finalized_child Proof verify CH RH cmb compress compressN acc s g steps h
  rw [h.height_is_count]
  exact hatt.history.turns_pinned

/-- **`settled_account_height_is_child_turn_count`.** The same pin read off the ACCOUNT after the write:
the height the L1 holds for this child is the child's genuine turn count. -/
theorem settled_account_height_is_child_turn_count
    (acc : RollupAccount) (s : SettleChildChain Proof) (g : RecChainedState) (steps : List ChainStep)
    (h : SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps) :
    (applySettle Proof acc s).latestHeight = steps.length := by
  simpa [applySettle] using
    settle_height_is_child_turn_count Proof verify CH RH cmb compress compressN acc s g steps h

/-- **`inflated_height_cannot_settle` (THE HEIGHT-INFLATION TOOTH — the refusal that used to be an
acceptance).** A settlement claiming ANY height other than the child's true turn count is REJECTED,
however monotone, however genuinely proven and finalized the child chain is. This is the exact negation
of the deleted `settle_accepts_inflated_height`, which constructed such a settlement and proved it
accepted. -/
theorem inflated_height_cannot_settle
    (acc : RollupAccount) (s : SettleChildChain Proof) (g : RecChainedState) (steps : List ChainStep)
    (hbad : s.newHeight ≠ steps.length) :
    ¬ SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps := fun h =>
  hbad (settle_height_is_child_turn_count Proof verify CH RH cmb compress compressN acc s g steps h)

/-- **`settlement_height_is_unique` (the anti-equivocation edge for the REGISTER, matching
`settlement_root_is_unique` for the commitment).** Two accepted settlements of the same child history
record the SAME height, whatever accounts or certs they carry. Before the pin this was false: the same
history could be settled at any two heights above the accounts'. -/
theorem settlement_height_is_unique
    (acc acc' : RollupAccount) (s s' : SettleChildChain Proof)
    (g : RecChainedState) (steps : List ChainStep)
    (h : SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps)
    (h' : SettleAccepts Proof verify CH RH cmb compress compressN acc' s' g steps) :
    s.newHeight = s'.newHeight := by
  rw [settle_height_is_child_turn_count Proof verify CH RH cmb compress compressN acc s g steps h,
      settle_height_is_child_turn_count Proof verify CH RH cmb compress compressN acc' s' g steps h']

/-- **`replayed_settlement_cannot_advance` (what the pin buys the monotone register).** A child chain
cannot be settled TWICE into the same account: the second settlement of the same history would need to
claim a height strictly above the first, and the pin forces both to the same turn count. So the account
advances only when the CHILD advances — the monotone leg is no longer satisfiable by inflating a
number. -/
theorem replayed_settlement_cannot_advance
    (acc : RollupAccount) (s s' : SettleChildChain Proof)
    (g : RecChainedState) (steps : List ChainStep)
    (h : SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps) :
    ¬ SettleAccepts Proof verify CH RH cmb compress compressN
        (applySettle Proof acc s) s' g steps := by
  intro h'
  have hs := settle_height_is_child_turn_count Proof verify CH RH cmb compress compressN acc s g steps h
  have hs' := settle_height_is_child_turn_count Proof verify CH RH cmb compress compressN
    (applySettle Proof acc s) s' g steps h'
  have hm := h'.monotone
  simp only [applySettle] at hm
  omega

end Effect

/-! ## 9. THE ANTI-GHOST TEETH — a stale, forged, mismatched or fabricated settlement is REJECTED. -/

section Teeth

variable (Proof : Type)
variable (verify : Proof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **`unset_account_proves_nothing` (THE NOMAD LAW).** A freshly registered L1 rollup account
(`latestRoot = none`) attests NO root — no `0`-default that reads as "proven". The exact hazard
`DreggPeerRegistry` guards (`bytes32(0)` never recorded), here ABSENT BY CONSTRUCTION via `Option`. -/
theorem unset_account_proves_nothing (c gen r : ℤ) :
    ¬ (RollupAccount.register c gen).provenRoot r := by
  simp [RollupAccount.register, RollupAccount.provenRoot]

/-- **`stale_settlement_rejected` (the replay tooth).** A settlement whose claimed height does NOT
strictly advance the account (`s.newHeight ≤ acc.latestHeight`) cannot be accepted — the `monotone`
leg is contradictory. A replayed or stale child root is REFUSED (`DreggPeerRegistry.NonMonotoneHeight`). -/
theorem stale_settlement_rejected
    (acc : RollupAccount) (s : SettleChildChain Proof) (g : RecChainedState) (steps : List ChainStep)
    (hstale : s.newHeight ≤ acc.latestHeight) :
    ¬ SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps := by
  intro h
  have := h.monotone
  omega

/-- **`forged_anchor_cannot_settle` (the forged-cert tooth).** If the node's finality rule does NOT
anchor a settlement's claimed cert anchor for its wave (`finalLeaderAt … ≠ some cert.anchor` — a forged,
non-leader claim), the cert is not `CertValid`, so leg 3 (`cert_ok`) cannot be supplied: the settlement
is REJECTED. Rides `FinalizedLightClient.not_final_leader_invalidates`. -/
theorem forged_anchor_cannot_settle
    (acc : RollupAccount) (s : SettleChildChain Proof) (g : RecChainedState) (steps : List ChainStep)
    (hne : Dregg2.Distributed.BlocklaceFinality.finalLeaderAt
             s.childCert.lace s.childCert.participants s.childCert.wave s.childCert.wavelength
             ≠ some s.childCert.anchor) :
    ¬ SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps := by
  intro h
  exact not_final_leader_invalidates s.childCert hne h.cert_ok

/-- **`root_mismatch_cannot_settle` (the seam tooth).** If a settlement's cert finalized a DIFFERENT
root than the one shown (`cert.finalizedRoot ≠ s.finalizedRoot`), it cannot satisfy `Bound`, so the
settlement is REJECTED — a valid child proof of history A cannot be paired with a finality cert for a
different root B. Rides `FinalizedLightClient.root_mismatch_unbinds`. -/
theorem root_mismatch_cannot_settle
    (acc : RollupAccount) (s : SettleChildChain Proof) (g : RecChainedState) (steps : List ChainStep)
    (hmis : s.childCert.finalizedRoot ≠ s.finalizedRoot) :
    ¬ SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps := by
  intro h
  exact root_mismatch_unbinds Proof s.childAgg s.childCert s.finalizedRoot hmis h.bound

/-- **`fabricated_genesis_cannot_settle` (the WRONG-CHAIN tooth).** A settlement whose child aggregate
starts at a genesis root OTHER than the account's registered one is REJECTED. A prover cannot fabricate
a fresh child chain (however honestly folded, however genuinely finalized by its own quorum) and settle
it into an account registered for a different chain — the account's identity is cryptographic, not
nominal. -/
theorem fabricated_genesis_cannot_settle
    (acc : RollupAccount) (s : SettleChildChain Proof) (g : RecChainedState) (steps : List ChainStep)
    (hne : s.childAgg.genesisRoot ≠ acc.childGenesis) :
    ¬ SettleAccepts Proof verify CH RH cmb compress compressN acc s g steps := by
  intro h
  exact hne h.genesis_ok

end Teeth

/-! ## 10. NON-VACUITY — the settlement FIRES on the realizing finalized child chain.

The predicate would be hollow if `SettleAccepts` were unsatisfiable. We reuse `FinalizedLightClient`'s
realizing instance (`realAggregate` over the honest 1-step child, `realCert` over the finalized `trace3`
wave-0 leader, `real_engine_sound`, `real_bound`) and settle it into a freshly REGISTERED L1 account,
firing the settlement and reading off the advance + the L2-commitment binding. As in
`FinalizedLightClient`, the concrete `CertValid realCert` was not kernel-reducible when this was
written (the round map rode `Array.qsort`; since dregg issue #100 it reduces, and discharging
`hcert` by `decide` is owed), so it is taken parametrically (`hcert`) — its executable existence is re-witnessed by the
`#guard`s below, over the node's REAL finality rule on `trace3`. -/

section Realize

open Dregg2.Circuit.RecursiveAggregation
  (RealProof realVerify zCH zRH zcmb zcompress zcompressN realAggregate realSteps real_engine_sound)
open Dregg2.Exec.ConsensusExec (teethGenesis)
open Dregg2.Distributed.FinalizedLightClient (realCert realAnchor real_bound)
open Dregg2.Distributed.BlocklaceFinality (finalLeaderAt isSuperRatified waveLastRound)

/-- The L1 rollup account registered for the realizing child chain — keyed by that chain's genuine
public genesis root, nothing settled yet. -/
def realAccount : RollupAccount := RollupAccount.register 7 realAggregate.genesisRoot

/-- The settlement of the realizing finalized child (`realAggregate` + `realCert`), committing the
child's genuine final root. `newHeight = 1` = the aggregate's public `numTurns`. -/
def realSettle : SettleChildChain RealProof where
  childAgg      := realAggregate
  childCert     := realCert
  finalizedRoot := realAggregate.finalRoot
  newHeight     := 1

/-! **EXECUTABLE WITNESS the realizing cert is valid + carries a real quorum** (re-witnessed here for
self-containment; a false `#guard` is a build error — the node's REAL rule on `trace3`). -/
#guard finalLeaderAt realCert.lace realCert.participants realCert.wave realCert.wavelength
        == some realAnchor                                   -- CertValid realCert (executable)
#guard isSuperRatified realCert.lace realCert.participants realCert.anchor
        (waveLastRound realCert.wave realCert.wavelength)    -- CertQuorum realCert = true (executable)

/-- **`settle_fires_on_real_child` (NON-VACUITY, parametric in the realized cert).** For any valid child
cert, the settlement is ACCEPTED over the realizing finalized child chain into the registered account:
all four crypto legs are discharged (`real_engine_sound`, `realVerify`, `real_bound`, the supplied
`hcert`), the child IS the registered chain, the height is the aggregate's count (`1`), and it advances
the registered height `0`. So `SettleAccepts` is INHABITED on a real, quorum-finalized child — the
predicate is not vacuous. -/
theorem settle_fires_on_real_child
    (hcert : CertValid realCert) :
    SettleAccepts RealProof realVerify zCH zRH zcmb zcompress zcompressN
      realAccount realSettle teethGenesis realSteps where
  engine          := real_engine_sound
  root_ok         := rfl
  bound           := real_bound
  cert_ok         := hcert
  genesis_ok      := rfl
  height_is_count := rfl
  monotone        := by decide

/-- **`real_settlement_binds_child_fold` (the binding FIRES on a real chain).** On the realizing
instance, the root the L1 account holds IS the child's genuine whole-history fold — a real, non-vacuous
firing of the L2-commitment binding lemma. -/
theorem real_settlement_binds_child_fold
    (hcert : CertValid realCert) :
    (applySettle RealProof realAccount realSettle).latestRoot
      = some (foldedFinalRoot zCH zRH zcmb zcompress zcompressN teethGenesis realSteps) :=
  settled_root_is_child_final_fold RealProof realVerify zCH zRH zcmb zcompress zcompressN
    realAccount realSettle teethGenesis realSteps (settle_fires_on_real_child hcert)

/-- **`real_settlement_advances` (the advance FIRES).** The realizing settlement advances the registered
account's height from `0` to `1` — a genuine monotone advance on a real finalized child. -/
theorem real_settlement_advances
    (hcert : CertValid realCert) :
    realAccount.latestHeight < (applySettle RealProof realAccount realSettle).latestHeight :=
  settle_advances_monotone RealProof realVerify zCH zRH zcmb zcompress zcompressN
    realAccount realSettle teethGenesis realSteps (settle_fires_on_real_child hcert)

end Realize

/-! ## 11. Axiom hygiene. -/

#assert_axioms Dregg2.Distributed.SelfSettlement.settle_attests_finalized_child
#assert_axioms Dregg2.Distributed.SelfSettlement.settled_root_is_child_final_fold
#assert_axioms Dregg2.Distributed.SelfSettlement.receipt_root_is_child_final_fold
#assert_axioms Dregg2.Distributed.SelfSettlement.settlement_root_is_unique
#assert_axioms Dregg2.Distributed.SelfSettlement.settle_starts_at_registered_genesis
#assert_axioms Dregg2.Distributed.SelfSettlement.settle_advances_monotone
#assert_axioms Dregg2.Distributed.SelfSettlement.settled_account_proves_root
#assert_axioms Dregg2.Distributed.SelfSettlement.settle_preserves_registration
#assert_axioms Dregg2.Distributed.SelfSettlement.settle_conserves_child_producer_witness
#assert_axioms Dregg2.Distributed.SelfSettlement.settle_height_is_child_turn_count
#assert_axioms Dregg2.Distributed.SelfSettlement.settled_account_height_is_child_turn_count
#assert_axioms Dregg2.Distributed.SelfSettlement.inflated_height_cannot_settle
#assert_axioms Dregg2.Distributed.SelfSettlement.settlement_height_is_unique
#assert_axioms Dregg2.Distributed.SelfSettlement.replayed_settlement_cannot_advance
#assert_axioms Dregg2.Distributed.SelfSettlement.unset_account_proves_nothing
#assert_axioms Dregg2.Distributed.SelfSettlement.stale_settlement_rejected
#assert_axioms Dregg2.Distributed.SelfSettlement.forged_anchor_cannot_settle
#assert_axioms Dregg2.Distributed.SelfSettlement.root_mismatch_cannot_settle
#assert_axioms Dregg2.Distributed.SelfSettlement.fabricated_genesis_cannot_settle
#assert_axioms Dregg2.Distributed.SelfSettlement.settle_fires_on_real_child
#assert_axioms Dregg2.Distributed.SelfSettlement.real_settlement_binds_child_fold
#assert_axioms Dregg2.Distributed.SelfSettlement.real_settlement_advances

end Dregg2.Distributed.SelfSettlement
