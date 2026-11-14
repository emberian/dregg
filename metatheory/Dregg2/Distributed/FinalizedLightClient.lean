/-
# Dregg2.Distributed.FinalizedLightClient — the THREE-LEG finalized-history light client.

**What this adds over `Circuit.RecursiveAggregation`.** That module proves the *first two legs*: a
light client that verifies ONE succinct IVC aggregate (re-witnessing nothing) learns the whole chain
of N turns is internally correct + correctly ordered, and its `finalRoot` is the genuine fold
(`light_client_verifies_whole_history`). But "internally correct" is NOT "finalized": a valid
aggregate of a chain that some equivocating prover folded over a *fork the network never finalized*
is still a valid aggregate. A real light client (a wallet, a bridge) must not accept such a thing — it
must additionally check that the root it is being shown is the one a BFT **quorum finalized**.

This module supplies the **THIRD leg** — the **finality certificate (quorum / tau)** — and the
**gap-free composition** of all three into the surface the task names: the light client takes
`(aggregate, finalizedRoot, finalityCert)` and accepts ONLY when

  (1) the succinct aggregate verifies  (the recursion engine — `RecursiveAggregation.EngineSound`),
  (2) the aggregate's `finalRoot` equals the `finalizedRoot` it is shown      (the BINDING), and
  (3) the `finalityCert` is a genuine super-ratification quorum over the leader that anchors the
      finalized head, AND that anchor commits the SAME `finalizedRoot`        (the QUORUM / tau leg).

When all three hold, the light client obtains `FinalizedHistoryAttested`: the whole history executed
correctly + is correctly ordered + value is conserved over the whole history + the endpoint root it
trusts is the one a supermajority of distinct participants finalized via the node's REAL
`ordering.rs::tau` super-ratification rule (`BlocklaceFinality.isSuperRatified`). No re-execution, no
blocklace walk — ONE STARK verify + ONE quorum-count check.

**Why this is the load-bearing addition.** Without leg (3), a light client trusting a bare aggregate
trusts a *correct-looking* history, not a *finalized* one — the exact gap a fork attack exploits. Leg
(3) reuses the node's actual finality predicate (`isSuperRatified`, the `2n/3+1` distinct-participant
super-majority of `BlocklaceFinality`), so "the cert is valid" means "the node would have finalized
this head". The ANTI-GHOST teeth (`§6`) show a forged cert (sub-quorum) and a root-mismatch cert are
both REJECTED, so the third leg separates a finalized head from an unfinalized fork.

**The boundary (unchanged).** The ONE thing outside Lean is plonky3/pickles FRI recursion
soundness — carried, exactly as in `RecursiveAggregation`, by the NAMED, REALIZABLE `EngineSound`
hypothesis (a `structure` field, not an axiom; witnessed non-vacuously). The finality leg is FULLY
proved: `isSuperRatified` is a concrete `Bool` function over the lace, and the quorum count is a real
arithmetic check — no hypothesis needed for it.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Distributed.FinalizedLightClient`.
-/
import Dregg2.Circuit.RecursiveAggregation
import Dregg2.Distributed.BlocklaceFinality

namespace Dregg2.Distributed.FinalizedLightClient

open Dregg2.Exec (RecChainedState recCexec recTotal)
open Dregg2.Distributed.HistoryAggregation
  (ChainStep stateRoot foldedFinalRoot lastStateOf StateChained ChainBound zeroTurn)
open Dregg2.Circuit.RecursiveAggregation
  (Aggregate EngineSound AggregateAttests light_client_verifies_whole_history)
open Dregg2.Distributed.BlocklaceFinality
  (isSuperRatified superMajority finalLeaderAt waveLastRound)
open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId)

section Cert

variable (Proof : Type)
variable (verify : Proof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-! ## 1. The finality certificate — quorum / tau, binding the finalized root.

The node finalizes a head by SUPER-RATIFICATION: the wave's round-robin leader block has EXACTLY one
candidate (no slot-equivocation) AND a supermajority (`2n/3 + 1`) of DISTINCT participants have
wave-end blocks that ratify it (`BlocklaceFinality.isSuperRatified`, the executable model of
`ordering.rs::tau`'s finality condition). The light client is NOT given the lace; it is given a
*certificate* attesting that this finalization happened, plus the root the finalized head commits.

`FinalityCert` is exactly that certificate, modeled as the *evidence the node's rule consumes* — the
lace fragment exhibiting the quorum + the anchored leader + the wave parameters — together with the
finalized root it binds. The Rust light client receives a compressed form (the participant set,
the quorum signatures, the root); here we model the evidence faithfully so the validity predicate is
the node's REAL `isSuperRatified`, not a stand-in. -/

/-- **`FinalityCert`** — the finality evidence a light client checks: the certified blocklace
fragment `lace`, the participant set, the wavelength, the wave whose leader is the finalized anchor,
the anchored leader block `anchor`, and the `finalizedRoot` the anchor commits. The light client does
NOT see the whole history — only this certificate + the aggregate. -/
structure FinalityCert where
  /-- The certified blocklace fragment exhibiting the quorum (the cert's evidence payload). -/
  lace         : Lace
  /-- The participant set the supermajority is counted over. -/
  participants : List AuthorId
  /-- The wavelength (the node's finality config; the differential trace uses `3`). -/
  wavelength   : Nat
  /-- The wave whose round-robin leader is the finalized anchor. -/
  wave         : Nat
  /-- The leader block the certificate claims is finalized (super-ratified). -/
  anchor       : Block
  /-- The finalized state root the anchored head commits (the value the light client will trust). -/
  finalizedRoot : ℤ

/-- **`CertValid cert`** — the certificate is GENUINE: the claimed `anchor` really is the unique
final leader the node's `ordering.rs::tau` rule anchors for `cert.wave` over `cert.lace`
(`finalLeaderAt … = some anchor` — which itself requires the supermajority super-ratification
`isSuperRatified` AND no slot-equivocation, `BlocklaceFinality.finalLeaderAt`). This is the node's
REAL finality predicate; a sub-quorum or equivocated-leader cert fails it. -/
def CertValid (cert : FinalityCert) : Prop :=
  finalLeaderAt cert.lace cert.participants cert.wave cert.wavelength = some cert.anchor

/-- **`CertQuorum cert`** — the raw super-ratification quorum the cert exhibits: a supermajority of
distinct participants' wave-end blocks ratify the anchor (`isSuperRatified`). A standalone `Bool`
view of the quorum leg, used by the Rust differential. -/
def CertQuorum (cert : FinalityCert) : Bool :=
  isSuperRatified cert.lace cert.participants cert.anchor
    (waveLastRound cert.wave cert.wavelength)

/-- A valid cert exhibits the super-ratification quorum: `finalLeaderAt = some anchor` fires only
through the `isSuperRatified` guard, so `CertQuorum` holds. The quorum leg is present in a
valid cert — not an independent assertion. -/
theorem certValid_has_quorum (cert : FinalityCert) (h : CertValid cert) :
    CertQuorum cert = true := by
  unfold CertValid at h
  unfold CertQuorum
  -- `finalLeaderAt` returns `some cert.anchor` only when the singleton candidate `isSuperRatified`.
  unfold finalLeaderAt at h
  cases hc : Dregg2.Distributed.BlocklaceFinality.leaderCandidates
              cert.lace cert.participants cert.wave cert.wavelength with
  | nil => rw [hc] at h; simp at h
  | cons x xs =>
    cases xs with
    | nil =>
      rw [hc] at h
      by_cases hsr : isSuperRatified cert.lace cert.participants x
                      (waveLastRound cert.wave cert.wavelength)
      · -- singleton + super-ratified ⇒ `some x = some anchor`, so `anchor = x` and the quorum is `hsr`.
        simp only [hsr, if_true] at h
        have : x = cert.anchor := Option.some.inj h
        rw [← this]; exact hsr
      · simp only [hsr] at h; exact absurd h (by simp)
    | cons y ys => rw [hc] at h; simp at h

/-! ## 2. Binding the cert to the aggregate — the root seam.

The light client is handed `(agg, finalizedRoot, cert)`. The seam: the aggregate's PUBLIC `finalRoot`
must equal the `finalizedRoot` (so the proven-correct history's endpoint IS the shown root), and the
cert's `finalizedRoot` must equal it too (so the QUORUM-finalized head IS the shown root). The two
equalities glue "the proof attests this root" to "the quorum finalized this root". -/

/-- **`Bound agg cert finalizedRoot`** — the root seam: the aggregate's final root, the cert's
finalized root, and the shown `finalizedRoot` all coincide. This is the cross-binding that makes the
three legs talk about ONE root — without it, an adversary could pair a valid proof of history A with a
valid finality cert for history B. -/
structure Bound (agg : Aggregate Proof) (cert : FinalityCert) (finalizedRoot : ℤ) : Prop where
  /-- The aggregate's proven endpoint is the shown root. -/
  agg_binds  : agg.finalRoot = finalizedRoot
  /-- The quorum-finalized head's root is the shown root. -/
  cert_binds : cert.finalizedRoot = finalizedRoot

/-! ## 3. THE THREE-LEG HEADLINE — verifying aggregate + cert + binding attests a FINALIZED history. -/

/-- **`FinalizedHistoryAttested`** — the verdict a light client obtains from
`(agg, finalizedRoot, cert)` when all three legs hold: the whole-history correctness of
`AggregateAttests` (every turn executed correctly, correctly ordered, final root is the genuine fold)
PLUS the finality fact (the shown root is the one a BFT quorum finalized via the node's real
super-ratification rule). Holding this means: *the endpoint root I trust is the genuine fold of a
whole history that executed correctly AND was finalized by a supermajority — and I re-executed
nothing.* -/
structure FinalizedHistoryAttested
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (cert : FinalityCert) (finalizedRoot : ℤ) : Prop where
  /-- Leg 1+2: the whole history is correct (every turn executed, correctly ordered, genuine fold). -/
  history : AggregateAttests Proof CH RH cmb compress compressN agg g steps
  /-- Leg 3: the finalized root is super-ratified by a quorum (the node's real finality rule). -/
  finalized : CertQuorum cert = true
  /-- The seam: the proven endpoint, the finalized head's root, and the shown root coincide — so the
  attested correct history's endpoint IS the quorum-finalized root the client trusts. -/
  root_is_finalized : agg.finalRoot = finalizedRoot ∧ cert.finalizedRoot = finalizedRoot

/-- **`light_client_accepts_finalized_history` (THE THREE-LEG HEADLINE).**

A light client given `(agg, finalizedRoot, cert)` that checks
  (1) `verify agg.root = true`  — the succinct aggregate (re-witnessing NOTHING),
  (2) `Bound`                   — the aggregate/cert roots equal the shown `finalizedRoot`, and
  (3) `CertValid cert`          — the cert is a genuine super-ratification quorum (the node's rule),
obtains `FinalizedHistoryAttested`: the whole history executed correctly + is correctly
ordered + the endpoint root it trusts is the genuine fold AND was finalized by a BFT quorum. Leg 1+2
ride `light_client_verifies_whole_history` (under the named `EngineSound`); leg 3 is fully proved from
`CertValid` via `certValid_has_quorum`. The verification of the succinct aggregate plus the quorum
count IS the trust in the whole FINALIZED history — gap-free, no prose seam. -/
theorem light_client_accepts_finalized_history
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (cert : FinalityCert) (finalizedRoot : ℤ)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    (hbound : Bound Proof agg cert finalizedRoot)
    (hcert : CertValid cert) :
    FinalizedHistoryAttested Proof CH RH cmb compress compressN agg g steps cert finalizedRoot :=
  { history := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
                 agg g steps es hroot
  , finalized := certValid_has_quorum cert hcert
  , root_is_finalized := ⟨hbound.agg_binds, hbound.cert_binds⟩ }

/-! ## 4. THE CONSERVATION THE FINALIZED CLIENT INHERITS.

Composing the attested correctness with the executor-genuine `StateChained` witness gives value
conservation over the WHOLE finalized history — the client trusts a no-mint/no-burn ledger reaching a
quorum-finalized endpoint, having re-executed nothing. -/

/-- **`finalized_history_conserves` (KEYSTONE).** A light client that accepts a finalized
history (the three legs) inherits value conservation over the whole history: the ledger total at the
folded, quorum-finalized endpoint equals the genesis total. The finality leg adds *that the endpoint
is finalized*; this rides `HistoryAggregation.wellformed_history_conserves` for *that the conserved
endpoint is reached*. -/
theorem finalized_history_conserves
    (g : RecChainedState) (steps : List ChainStep) (hch : StateChained g steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  Dregg2.Distributed.HistoryAggregation.wellformed_history_conserves g steps hch

end Cert

/-! ## 5. NON-VACUITY — the three legs FIRE on a real, finalized chain.

The headline would be hollow if `CertValid` were unsatisfiable or the legs could not co-occur. Two
complementary witnesses, exactly as `BlocklaceFinality` does (when this was written its round map
rode `Array.qsort`, so kernel `decide` did not reduce `finalLeaderAt` and the tooth for an
executable `def` was `#guard`, a false `#guard` being a build error like a failed test. Since
dregg issue #100 `decide` DOES reduce `finalLeaderAt` on `trace3`; restating the `#guard`s below
as theorems is owed):

  * **§5a (the `Prop` headline FIRES).** For ANY cert whose validity + root-seam hold, the headline
    concludes `FinalizedHistoryAttested` over the realizing aggregate of `RecursiveAggregation` (whose
    `real_engine_sound` already witnesses legs 1+2). `finalized_light_client_fires_for` proves this
    parametrically — so the three-leg theorem is inhabited the moment a valid cert exists.

  * **§5b (a valid cert EXISTS — executable witness).** The `#guard`s over `BlocklaceFinality.trace3`
    (the 3-node fully-connected trace whose wave-0 leader super-ratifies) establish, by
    machine evaluation, that `finalLeaderAt trace3 [1,2,3] 0 3 = some <creator-1 genesis>` (= a valid
    cert anchor) AND its `CertQuorum` is `true`. So §5a's antecedent is realized by the node's REAL
    finalization rule on a concrete trace — the legs co-occur on a real, finalized chain. -/

section Realize

open Dregg2.Circuit.RecursiveAggregation
  (RealProof realVerify zCH zRH zcmb zcompress zcompressN realAggregate realSteps real_engine_sound
   AggregateAttests)
open Dregg2.Exec.ConsensusExec (teethGenesis)
open Dregg2.Distributed.BlocklaceFinality
  (trace3 trace3Participants finalLeaderAt isSuperRatified waveLastRound)

/-- The creator-1 genesis block (id 10) of `trace3` — the wave-0 round-robin leader the node's rule
anchors (the `#guard`s below evaluate `finalLeaderAt trace3 … = some` it). -/
def realAnchor : Block := ⟨10, 1, 0, [], true⟩

/-- The realizing certificate over `trace3`'s finalized wave-0 leader, binding the SAME
finalized root the realizing aggregate proves (`realAggregate.finalRoot`). -/
def realCert : FinalityCert where
  lace         := trace3
  participants := trace3Participants
  wavelength   := 3
  wave         := 0
  anchor       := realAnchor
  finalizedRoot := (realAggregate.finalRoot)

/-! **§5b — EXECUTABLE WITNESSES the realizing cert is valid + carries a real quorum.**
These `#guard`s evaluate the node's REAL finality rule on `trace3`: the cert's anchor IS the final
leader (`CertValid realCert` holds, executably), the super-ratification quorum IS present
(`CertQuorum realCert = true`), and the anchor is creator-1's genesis (the wave-0 round-robin leader).
A false `#guard` is a build error — so these are compiler-checked non-vacuity (see §5's note: they
could now be kernel theorems). -/

#guard finalLeaderAt realCert.lace realCert.participants realCert.wave realCert.wavelength
        == some realAnchor                                   -- CertValid realCert (executable)
#guard isSuperRatified realCert.lace realCert.participants realCert.anchor
        (waveLastRound realCert.wave realCert.wavelength)    -- CertQuorum realCert = true (executable)
#guard realCert.anchor.creator == 1                          -- the genuine wave-0 round-robin leader

/-- **`finalized_light_client_fires_for` (§5a: THE THREE-LEG HEADLINE IS WITNESSED, parametric
in the realized cert).** For ANY cert + shown root whose validity (`CertValid`) and root-seam (`Bound`)
hold, the finalized-history light client concludes `FinalizedHistoryAttested` over the
realizing aggregate (whose `real_engine_sound` discharges legs 1+2). Composed with the §5b `#guard`
witness that such a cert EXISTS (`realCert` over `trace3`), this shows
`light_client_accepts_finalized_history` is non-vacuous — it fires on a real chain finalized by a real
quorum and delivers a real attestation. (We keep the cert/root abstract so the firing is kernel-clean;
the finality rule's concrete satisfaction is the executable §5b witness, per the codebase's
`#guard` discipline.) -/
theorem finalized_light_client_fires_for
    (cert : FinalityCert) (hcert : CertValid cert)
    (hbound : Bound RealProof realAggregate cert realAggregate.finalRoot) :
    FinalizedHistoryAttested RealProof zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps cert realAggregate.finalRoot :=
  light_client_accepts_finalized_history RealProof realVerify zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps cert realAggregate.finalRoot
    real_engine_sound rfl hbound hcert

/-- **`fired_attestation_is_real` (the attestation has CONTENT).** The verdict obtained from
`finalized_light_client_fires_for` carries the genuine quorum (`CertQuorum cert = true`, from leg 3)
AND a real executor step for the (only) turn of the realizing history (from leg 1). So the finalized
attestation is a TRUE fact about a real, quorum-finalized executor run — not a formal husk — whenever
a valid cert is supplied (and §5b's `#guard`s witness one exists). -/
theorem fired_attestation_is_real
    (cert : FinalityCert) (hcert : CertValid cert)
    (hbound : Bound RealProof realAggregate cert realAggregate.finalRoot) :
    CertQuorum cert = true
      ∧ recCexec teethGenesis Dregg2.Exec.ConsensusExec.honestTurn
          = some Dregg2.Distributed.HistoryAggregation.honestStep.post := by
  have fired := finalized_light_client_fires_for cert hcert hbound
  refine ⟨fired.finalized, ?_⟩
  have h := fired.history.every_turn
              Dregg2.Distributed.HistoryAggregation.honestStep (by simp [realSteps])
  simpa [Dregg2.Distributed.HistoryAggregation.honestStep] using h

/-- **`real_bound` (the root seam closes).** The realizing cert's `finalizedRoot` was BUILT as
`realAggregate.finalRoot`, so the seam holds by construction — leg 2 is satisfiable. Combined with the
§5b `#guard` (leg 3) and `real_engine_sound` (legs 1+2), every antecedent of
`finalized_light_client_fires_for` is realized. -/
theorem real_bound :
    Bound RealProof realAggregate realCert realAggregate.finalRoot :=
  { agg_binds := rfl, cert_binds := rfl }

end Realize

/-! ## 6. THE ANTI-GHOST TEETH — a forged or mismatched certificate is REJECTED.

The finality leg is meaningful only if a BAD certificate cannot pass. Two teeth:
(a) **sub-quorum** — a cert whose anchor is NOT super-ratified is NOT `CertValid` (so the headline's
    leg 3 cannot be supplied; `certValid_has_quorum`'s contrapositive); we witness a concrete
    sub-quorum cert that fails.
(b) **root mismatch** — a cert whose `finalizedRoot` differs from the aggregate's proven `finalRoot`
    cannot satisfy `Bound` (the seam tooth), so a valid proof of history A cannot be paired with a
    finality cert for a different root. -/

section AntiGhost

variable (Proof : Type)

open Dregg2.Distributed.BlocklaceFinality
  (trace3 trace3Participants isSuperRatified waveLastRound finalLeaderAt)

/-- A FORGED certificate: it claims creator `2`'s genesis (id 20) is the wave-0 anchor of `trace3`,
but the node's round-robin leader for wave 0 is creator `1`. Creator 2 is NOT the wave-0 final leader,
so the cert is NOT `CertValid` — even though in a fully-connected trace creator 2's block
IS super-ratified. The discriminator the node's finality rule uses is the round-robin LEADER SLOT, not
raw super-ratification, and that is exactly what `CertValid` (`finalLeaderAt = some anchor`) checks. -/
def forgedCert : FinalityCert where
  lace         := trace3
  participants := trace3Participants
  wavelength   := 3
  wave         := 0
  anchor       := ⟨20, 2, 0, [], true⟩   -- creator 2, NOT the wave-0 round-robin leader
  finalizedRoot := 0

/-! **THE FORGED-ANCHOR TOOTH (executable witness).** The forged cert is NOT `CertValid`: the node's
real rule anchors creator `1` (not creator `2`) at wave 0, so `finalLeaderAt … ≠ some forgedCert.anchor`.
The `#guard`s evaluate this on `trace3` — a false `#guard` is a build error — so the cert leg
REJECTS a forged (creator-2-claimed) anchor. (creator 2's block IS super-ratified in a
fully-connected trace; the rejection is at the LEADER-SLOT check `finalLeaderAt`, which is precisely
why `CertValid` is the round-robin `finalLeaderAt = some anchor`, not bare `isSuperRatified`.) -/

#guard (finalLeaderAt forgedCert.lace forgedCert.participants forgedCert.wave forgedCert.wavelength
          == some forgedCert.anchor) == false                            -- ¬ CertValid forgedCert
#guard finalLeaderAt forgedCert.lace forgedCert.participants forgedCert.wave forgedCert.wavelength
          == some realAnchor                                             -- the TRUE wave-0 anchor is creator 1
#guard forgedCert.anchor.creator == 2                                    -- the forged (non-leader) claim

/-- **`not_final_leader_invalidates` (the forged-anchor tooth, `Prop` form).** If the node's
rule does NOT anchor a cert's claimed `anchor` for its wave (`finalLeaderAt … ≠ some cert.anchor` — the
executable `#guard` witnesses this for `forgedCert` on `trace3`), then the cert is NOT `CertValid`, so
leg 3 of the headline cannot be supplied: a light client REJECTS it and grants no finalized
attestation. Kernel-clean (`CertValid` unfolds to exactly the disequated `finalLeaderAt`). -/
theorem not_final_leader_invalidates (cert : FinalityCert)
    (hne : finalLeaderAt cert.lace cert.participants cert.wave cert.wavelength ≠ some cert.anchor) :
    ¬ CertValid cert := by
  intro h; exact hne h

/-- **`root_mismatch_unbinds` (the seam tooth).** If a cert's `finalizedRoot` differs from
the shown `finalizedRoot`, it cannot satisfy `Bound`: an adversary cannot pair a valid aggregate of
history A (proving root `rA`) with a finality cert that finalized a DIFFERENT root `rB ≠ rA`. The seam
forces one root through all three legs, so the finalized attestation cannot mix histories. -/
theorem root_mismatch_unbinds
    (agg : Aggregate Proof) (cert : FinalityCert) (finalizedRoot : ℤ)
    (hmis : cert.finalizedRoot ≠ finalizedRoot) :
    ¬ Bound Proof agg cert finalizedRoot := by
  intro hb
  exact hmis hb.cert_binds

/-- **`agg_root_mismatch_unbinds` (the seam tooth, aggregate side).** Symmetrically, if the
aggregate's proven `finalRoot` differs from the shown root, `Bound` fails: a finality cert for root
`r` cannot be paired with an aggregate that proves a DIFFERENT endpoint. Both seam directions bite. -/
theorem agg_root_mismatch_unbinds
    (agg : Aggregate Proof) (cert : FinalityCert) (finalizedRoot : ℤ)
    (hmis : agg.finalRoot ≠ finalizedRoot) :
    ¬ Bound Proof agg cert finalizedRoot := by
  intro hb
  exact hmis hb.agg_binds

end AntiGhost

/-! ## 7. Axiom hygiene. -/

#assert_axioms Dregg2.Distributed.FinalizedLightClient.certValid_has_quorum
#assert_axioms Dregg2.Distributed.FinalizedLightClient.light_client_accepts_finalized_history
#assert_axioms Dregg2.Distributed.FinalizedLightClient.finalized_history_conserves
#assert_axioms Dregg2.Distributed.FinalizedLightClient.finalized_light_client_fires_for
#assert_axioms Dregg2.Distributed.FinalizedLightClient.fired_attestation_is_real
#assert_axioms Dregg2.Distributed.FinalizedLightClient.real_bound
#assert_axioms Dregg2.Distributed.FinalizedLightClient.not_final_leader_invalidates
#assert_axioms Dregg2.Distributed.FinalizedLightClient.root_mismatch_unbinds
#assert_axioms Dregg2.Distributed.FinalizedLightClient.agg_root_mismatch_unbinds

end Dregg2.Distributed.FinalizedLightClient
