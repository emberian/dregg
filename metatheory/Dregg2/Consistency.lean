/-
# Dregg2.Consistency — the GLOBAL CONSISTENCY WITNESS (non-vacuity + non-contradiction).

**The worry this module answers.** The dregg2 metatheory conditions a large fraction of its
keystones on Prop-carrying typeclasses and structure-field hypotheses (`World`, the BFT
`BFTModel`/`Pacemaker`, the privacy `GraphPrivacyKernel`/`BlindedMembershipKernel`, the
cross-cell `Hyperedge`/`JointBinding`, the cross-vat `CryptoKernel`, the deniability
`HolderAnonymity`, …) and on three by-design `sorry`s. If those carriers were jointly
*unsatisfiable* the whole edifice would be VACUOUS (every conditioned theorem trivially true);
if their conjunction derived `False` it would be CONTRADICTORY (everything provable). Either
failure would make "PROVED, axiom-clean" worthless.

**What this module proves.** A concrete, NON-TRIVIAL, axiom-clean *consistency witness*: every
SYSTEM-LEVEL Prop-carrier is INHABITED by a discriminating model — one a reader cannot dismiss
as `fun _ => True` / `Unit`-collapse, because each carries an `example` *tooth* showing genuine
separation (it REJECTS a dishonest input). The capstone `dregg_consistent` packages the joint
inhabitation as a single inhabited record; cluster lemmas record the interacting carriers'
co-instantiation. The model citizen imitated throughout is
`Spec.VatBoundary.phi_functorial_concrete` — a *discriminating* verifier, not Verify-always-true.

**What this module does NOT prove.** FAITHFULNESS to real dregg or real cryptography (the
separate Rust-grounding axis). The CRYPTO-STANDARD carriers (`collisionHard`, `binding`,
`extractable`, `unforgeable`, …) are NECESSARILY Lean-trivial to discharge — you cannot prove
DLog-hardness in Lean. They are HONEST, isolated in §4, and explicitly NOT counted as the
non-vacuity evidence. The non-vacuity evidence is the SYSTEM-LEVEL discriminating witnesses.

**Reuse vs new.** Ten of eleven system-level carriers already had non-trivial axiom-clean
witnesses (`graphRef`, `memRefNat`, `World.Reference`, `BFT.Inhabited.model`,
`BFTLiveness.Inhabited.pacemaker`, `CordialMiners.Inhabited.superRatifyG1`, `ringHyperedge` +
`hyper_binding_is_proper`, `JointTurn.binding_is_proper`, `CryptoKernel.Reference`,
`phi_functorial_concrete`) — this module REUSES them and re-exhibits their teeth. The ONE
surface finding — `HolderAnonymity` carried a TRIVIAL-ONLY witness (`view ≡ 0`,
`ViewIndistinguishable ≡ True`, the all-True shape the audit already killed twice) — is closed
HERE additively by a NEW discriminating witness `discriminatingAnon` (a non-constant
root-indexed `view`, `ViewIndistinguishable := Eq`), matching the `Privacy.lean` idiom.

This is an ADDITIVE module: it edits NO existing carrier and introduces NO
`sorry`/`admit`/`axiom`/`native_decide`. -/

import Mathlib.Tactic
import Dregg2.Boundary
import Dregg2.Privacy
import Dregg2.World
import Dregg2.CryptoKernel
import Dregg2.Hyperedge
import Dregg2.JointTurn
import Dregg2.Proof.BFT
import Dregg2.Proof.BFTLiveness
import Dregg2.Proof.CordialMiners
import Dregg2.Crypto.BlindedSet
import Dregg2.Spec.VatBoundary

namespace Dregg2.Consistency

open Dregg2 Dregg2.Privacy Dregg2.World Dregg2.Crypto Dregg2.Proof
open Dregg2.Crypto.BlindedSet Dregg2.Laws

/-- A `local instance` mirroring `VatBoundary`'s section-local `concreteVerifiable`
(`Verify s b := b`, accepts `true`, REJECTS `false`). Needed ONLY so the type
`Spec.PhiFunctorial Unit Unit Bool …` is nameable here (its `[Verifiable Statement Witness]`
must resolve); definitionally equal to VatBoundary's, so `phi_functorial_concrete` reuses
verbatim. Section-scoped — it never leaks as a global default. -/
local instance concreteVerifiable : Verifiable Unit Bool := ⟨fun _ b => b⟩

/-! ## §1 — The ONE newly-witnessed carrier: a DISCRIMINATING `HolderAnonymity`.

The consistency surface flagged exactly one TRIVIAL-ONLY system-level carrier:
`HolderAnonymity.hides_law`'s conclusion `ViewIndistinguishable : Nat → Nat → Prop`, whose
only witness (`BlindedSet.Reference.anonKernel`) discharged it with `view ≡ 0`,
`ViewIndistinguishable ≡ fun _ _ => True` — the SAME all-True shape the audit already caught and
killed for `GraphPrivacyKernel` and `ExecRights=Unit`. At that witness `blindedset_hides_holder`
says only `True`, so the hiding content is VACUOUS.

We close it the way `Privacy.lean` closed `GraphPrivacyKernel` (`memberView`/`hides_law`,
witnessed by `memRefNat`): a CONCRETE view-equality conclusion (`ViewIndistinguishable := Eq`)
over a genuinely NON-CONSTANT `view`. The model (over `Digest := Int`):

  * `compress := BlindedSet.Reference.refCompress` (= `(·+·)`) — the reference node hash, so
    `MemberOf` is genuinely inhabited (`ref_member_at` exhibits real members);
  * `view _ root := root.toNat` — the observer-view depends ONLY on the issuer ROOT, never on
    WHICH member. This is the honest model of holder anonymity: the blinded transcript collapses
    the member but reveals the (public) root. It is GENUINELY NON-CONSTANT (different roots ⇒
    different views — the tooth that rules out the `fun _ _ => 0` masquerade);
  * `ViewIndistinguishable := Eq` — concrete information-theoretic indistinguishability on the
    view, NOT the abstract `True`-collapsible carrier.

`hides_law` then closes by `rfl` (two members of the SAME root have the SAME root-indexed view),
and the witness DISCRIMINATES: members of DIFFERENT roots get DIFFERENT views (proved below). -/

/-- **The discriminating holder-anonymity witness (NEW, the closed surface finding).**
`view _ root := root.toNat` collapses *which* member while separating issuer roots;
`ViewIndistinguishable := Eq` is the concrete view-equality conclusion (NOT the all-True carrier).
A `def`, not a global `instance` — like `Privacy.graphRef`/`memRefNat`, it witnesses the interface
is inhabitable by a non-trivial model without silently satisfying a genuine `[HolderAnonymity]`
obligation. (`@[reducible]` only silences the class-typed-`def` lint — exactly as
`Privacy.graphRef`/`memRefNat` do; it does NOT make this an auto-resolved instance.) -/
@[reducible] def discriminatingAnon : HolderAnonymity Int where
  compress := BlindedSet.Reference.refCompress
  view _ root := root.toNat
  ViewIndistinguishable := Eq
  hides_law _ _ _ _ _ := rfl

/-- **TOOTH 1 — the hiding law is genuine (collapses the member).** Two authorized members `m`,
`m'` of the SAME issuer `root` produce EQUAL views — the verifier confirms "authorized" while
learning nothing about *which* holder. Routed through `blindedset_hides_holder` (so it is the
real conditioned theorem, not a bypass), inhabited at the discriminating witness. -/
example (root m m' : Int)
    (h : MemberOf discriminatingAnon.compress root m)
    (h' : MemberOf discriminatingAnon.compress root m') :
    discriminatingAnon.ViewIndistinguishable
      (discriminatingAnon.view m root) (discriminatingAnon.view m' root) :=
  @blindedset_hides_holder Int discriminatingAnon root m m' h h'

/-- **TOOTH 2 — the view is GENUINELY NON-CONSTANT (the all-True/`≡0` masquerade is impossible).**
Two issuer roots `3` and `5` give DIFFERENT views, so `view` is not `fun _ _ => c` and
`ViewIndistinguishable` is the honest `Eq`, not a `True`-collapse. This is the
`phi_functorial_concrete`-shaped tooth: the model rejects the degenerate reading. -/
example (m m' : Int) :
    discriminatingAnon.view m 3 ≠ discriminatingAnon.view m' 5 := by
  show (3 : Int).toNat ≠ (5 : Int).toNat
  decide

/-- **TOOTH 3 — the conditioned theorem is non-vacuously satisfiable: REAL members exist.**
`compress := refCompress` makes `MemberOf` genuinely inhabited (`ref_member_at`), so the hiding
law speaks about an actual authorized-member pair, not an empty premise. Here `1` and `2` are
both authorized members of root `3` (paths `1 + 2 = 3` and `2 + 1 = 3`). -/
example : MemberOf discriminatingAnon.compress 3 1 ∧ MemberOf discriminatingAnon.compress 3 2 := by
  refine ⟨?_, ?_⟩
  · have := BlindedSet.Reference.ref_member_at (x := 1) (s := 2); simpa using this
  · have := BlindedSet.Reference.ref_member_at (x := 2) (s := 1); simpa using this

/-- **TOOTH 4 — the hiding holds for those REAL members, computed at the witness.** Combining
TOOTH 1 and TOOTH 3: members `1` and `2` of root `3` are authorized AND have indistinguishable
views — the full non-vacuous holder-anonymity statement at the discriminating witness. -/
example :
    discriminatingAnon.ViewIndistinguishable
      (discriminatingAnon.view 1 3) (discriminatingAnon.view 2 3) := by
  have h1 : MemberOf discriminatingAnon.compress 3 1 := by
    have := BlindedSet.Reference.ref_member_at (x := 1) (s := 2); simpa using this
  have h2 : MemberOf discriminatingAnon.compress 3 2 := by
    have := BlindedSet.Reference.ref_member_at (x := 2) (s := 1); simpa using this
  exact @blindedset_hides_holder Int discriminatingAnon 3 1 2 h1 h2

/-! ## §2 — The REUSED system-level witnesses, re-exhibited with teeth.

Each of the remaining ten system-level carriers already has a NON-TRIVIAL axiom-clean witness
in its home module. We re-expose each as a named handle (so the capstone can bundle them) and
re-check a *discrimination tooth* — the property that distinguishes the witness from the trivial
model — so this module's non-vacuity claim does not merely cite the surface but re-verifies it. -/

/-! ### §2.1 — Privacy: `graphRef` (stealth/nullifier) + `memRefNat` (blinded membership). -/

/-- Handle: the non-trivial graph-privacy witness (`addrView a := a.oneTimeKey % 2`, non-constant). -/
abbrev graphPrivacyWitness : GraphPrivacyKernel := Privacy.Reference.graphRef
/-- Handle: the non-trivial blinded-membership witness (`memberOf e _ := e < 2`, genuine predicate). -/
abbrev blindedMembershipWitness : BlindedMembershipKernel Nat := Privacy.Reference.memRefNat

/-- TOOTH — `graphRef`'s `addrView` is non-constant: addresses for the two recipients differ.
(This is the property that rules out the killed all-True `GraphPrivacyKernel`.) -/
example : @GraphPrivacyKernel.addrView graphPrivacyWitness ⟨0⟩
    ≠ @GraphPrivacyKernel.addrView graphPrivacyWitness ⟨1⟩ := by
  show (0 : Nat) % 2 ≠ 1 % 2; decide

/-- TOOTH — `memRefNat`'s membership predicate is GENUINE, not `fun _ => True`: `2` is no member. -/
example (sc : SetCommitment Nat) :
    ¬ @BlindedMembershipKernel.memberOf Nat _ blindedMembershipWitness 2 sc := by
  show ¬ (2 < 2); decide

/-! ### §2.2 — Network/consensus: `World.Reference` ⊗ `BFT.Inhabited.model` ⊗
`BFTLiveness.Inhabited.pacemaker`, all over `Msg = Vote`. -/

/-- Handle: the reference `World` (`recv r := fixedVotes.take r`, real append-only schedule). -/
abbrev worldWitness : World World.Reference.M := inferInstance
/-- Handle: the BFT model at the minimal `n=4,f=1` floor (three honest voters, empty adversary). -/
abbrev bftWitness : BFT.BFTModel BFT.Inhabited.cfg BFT.Inhabited.votes := BFT.Inhabited.model
/-- Handle: the reference pacemaker over `World.Reference` (GST=3, honest leader every view). -/
abbrev pacemakerWitness :
    BFTLiveness.Pacemaker World.Reference.M BFTLiveness.Inhabited.votesOf BFTLiveness.Inhabited.cfg :=
  BFTLiveness.Inhabited.pacemaker

/-- TOOTH — the reference world's schedule genuinely DELIVERS a quorum (computes `true`),
so the `World` witness is not an empty network. -/
example : quorumReached ((World.recv (Msg := World.Reference.M) 3)) ⟨3, 0, 3⟩ 7 = true := by decide

/-- TOOTH — `bft_agreement` APPLIES to the BFT witness: two `n−f`-quorum blocks must coincide.
This is the safety theorem holding *of the inhabiting model* — non-vacuous. -/
example (b₁ b₂ : Nat)
    (hq1 : BFT.Inhabited.cfg.n - BFT.Inhabited.cfg.f ≤ (votersFor BFT.Inhabited.votes b₁).length)
    (hq2 : BFT.Inhabited.cfg.n - BFT.Inhabited.cfg.f ≤ (votersFor BFT.Inhabited.votes b₂).length) :
    b₁ = b₂ :=
  BFT.bft_agreement BFT.Inhabited.cfg BFT.Inhabited.votes bftWitness b₁ b₂ hq1 hq2

/-- TOOTH — liveness is DERIVED for the pacemaker witness (a `GSTRound` genuinely obtains and the
`World.gst_liveness` conclusion follows): the quorum is derived from delivery, not assumed. -/
example : ∃ (block r : Nat), BFTLiveness.Inhabited.cfg.threshold ≤
    ((((BFTLiveness.Inhabited.votesOf (World.recv (Msg := World.Reference.M) r)).filter
      (fun v => v.block = block)).map (·.voter)).dedup).length :=
  BFTLiveness.gst_liveness_of_pacemaker
    BFTLiveness.Inhabited.votesOf BFTLiveness.Inhabited.cfg pacemakerWitness

/-! ### §2.3 — DAG-BFT ratification: `SuperRatification`, DERIVED from the real lace. -/

/-- Handle: the `SuperRatification` whose votes/quorum are CONSTRUCTED from the real `ratLace`
(`SuperRatification.ofLace`), not hypothesized structure data. -/
noncomputable abbrev superRatificationWitness :
    CordialMiners.SuperRatification CordialMiners.Inhabited.state CordialMiners.Inhabited.cfg
      CordialMiners.Inhabited.rg1 :=
  CordialMiners.Inhabited.superRatifyG1

/-- TOOTH — the ratifying quorum is genuinely met ON THE LACE (`≥ n−f = 3` distinct ratifiers
computed via `ratifyingVoters`), not assumed: `rg1` is committed. -/
example : CordialMiners.Committed CordialMiners.Inhabited.state CordialMiners.Inhabited.cfg
    CordialMiners.Inhabited.rg1 :=
  CordialMiners.Inhabited.g1_committed

/-! ### §2.4 — Cross-cell binding: `Hyperedge` (apex) + `JointBinding` (binary) are PROPER. -/

/-- Handle: a real `N`-cycle hyperedge over ℤ with Σ-zero half-edges (here `N = 3`, `δ = id`). -/
noncomputable abbrev hyperedgeWitness :=
  Hyperedge.ringHyperedge 3 (fun i => (i : ℤ))

/-- TOOTH — the hyperedge binding is a PROPER subobject (PROVED): some product config is NOT
`HyperAdmissible` (CG-5 `1 ≠ 0`), so the binding carries genuine content (not vacuous). -/
example : ∃ (T : Boundary.TurnCoalg Unit Unit)
    (turnId : Unit → JointTurn.TurnIdOf (TurnId := Unit) T)
    (halfEdge : Unit → JointTurn.HalfEdgeOf (Bal := Nat) T)
    (xs : Unit → T.Carrier) (t : Unit),
    ¬ Hyperedge.HyperAdmissible Unit T turnId halfEdge xs t :=
  Hyperedge.hyper_binding_is_proper

/-- TOOTH — the binary `JointBinding` is likewise a PROPER subobject (PROVED): some product
config is excluded by CG-5 `1 + 1 ≠ 0`. The cross-cell binding is more than per-cell × per-cell. -/
example : ∃ (T₁ T₂ : Boundary.TurnCoalg Unit Unit)
    (turnId₁ : JointTurn.TurnIdOf (TurnId := Unit) T₁) (turnId₂ : JointTurn.TurnIdOf (TurnId := Unit) T₂)
    (half₁ : JointTurn.HalfEdgeOf (Bal := Nat) T₁) (half₂ : JointTurn.HalfEdgeOf (Bal := Nat) T₂)
    (x₁ : T₁.Carrier) (x₂ : T₂.Carrier) (t : Unit),
    ¬ JointTurn.JointAdmissible T₁ T₂ turnId₁ turnId₂ half₁ half₂ x₁ x₂ t :=
  JointTurn.binding_is_proper

/-! ### §2.5 — Cross-vat oracle: `CryptoKernel.Reference` is a DISCRIMINATING verify seam. -/

/-- Handle: the reference cross-vat crypto kernel (`verify stmt proof := decide (stmt = proof)`,
a discriminating echo-verifier — it REJECTS non-matching proofs). -/
abbrev cryptoKernelWitness : CryptoKernel Crypto.Reference.D Crypto.Reference.P := inferInstance

/-- TOOTH — the reference `verify` is DISCRIMINATING: it ACCEPTS a matching proof... -/
example : CryptoKernel.verify (Digest := Crypto.Reference.D) (Proof := Crypto.Reference.P) 7 7 = true := by
  decide
/-- ...and REJECTS a non-matching one (it is NOT Verify-always-true). -/
example : CryptoKernel.verify (Digest := Crypto.Reference.D) (Proof := Crypto.Reference.P) 7 8 = false := by
  decide

/-! ### §2.6 — Cross-vat functoriality: `phi_functorial_concrete` (the model citizen). -/

/-- Handle: the model-citizen discriminating verifier-functor witness (PROVED, axiom-clean).
Reused verbatim under this module's `concreteVerifiable` (definitionally VatBoundary's). -/
abbrev phiFunctorialWitness :
    Spec.PhiFunctorial (CellId := Bool) (Rights := Unit) Unit Unit Bool
      (Spec.Phi (Request := Unit) (Statement := Unit) (fun _ => ())) :=
  Spec.phi_functorial_concrete

/-! ## §3 — THE CAPSTONE: joint non-trivial inhabitation.

The eleven system-level carriers do not all share a single type parameter (privacy is over
`StealthAddr`/`Nat`, consensus over `Vote`, cross-cell over `TurnCoalg`, cross-vat over
`Int`/`Bool`), so a SINGLE joint `instance` is a type-parameter clash. As anticipated by the
task brief, we therefore package the joint inhabitation as one INHABITED RECORD bundling all the
discriminating witnesses simultaneously (the honest "fall back" form), plus cluster-consistency
lemmas where carriers genuinely INTERACT over a shared type (network ⊗ BFT ⊗ pacemaker over
`Vote`; BFT ⊗ ratification; the closed `HolderAnonymity` over `Int`). The bundle being inhabited
means: NO carrier's witness is `False`/empty, and they coexist in one Lean context without
deriving `False` — the system is neither vacuous nor contradictory at the system level. -/

/-- **`SystemModel`** — a single record carrying ALL inhabitable system-level carriers'
discriminating witnesses at once. Its INHABITATION (`dregg_consistent` below) is the
joint-consistency statement: every carrier is satisfiable by a non-trivial model,
simultaneously, in one context. (The cross-cell `Hyperedge`/`JointBinding` carriers are
*parametric* proper-subobject facts, not a single typeclass to inhabit; their non-triviality is
the PROVED `hyper_binding_is_proper`/`binding_is_proper` reused as teeth in §2.4 and pinned.) -/
structure SystemModel where
  /-- Graph privacy: non-constant `addrView` (not all-True). -/
  graphPrivacy : GraphPrivacyKernel
  /-- Blinded membership: genuine `memberOf` predicate. -/
  blindedMembership : BlindedMembershipKernel Nat
  /-- Network: append-only `recv` schedule + premise-conditioned liveness. -/
  world : World World.Reference.M
  /-- BFT floor `n > 3f` at the minimal `n=4,f=1`. -/
  bft : BFT.BFTModel BFT.Inhabited.cfg BFT.Inhabited.votes
  /-- Pacemaker: GST + honest-leader synchronization, quorum DERIVED from delivery. -/
  pacemaker :
    BFTLiveness.Pacemaker World.Reference.M BFTLiveness.Inhabited.votesOf BFTLiveness.Inhabited.cfg
  /-- DAG-BFT ratification quorum, DERIVED from the real lace. -/
  superRatification :
    CordialMiners.SuperRatification CordialMiners.Inhabited.state CordialMiners.Inhabited.cfg
      CordialMiners.Inhabited.rg1
  /-- Cross-vat verify oracle: discriminating echo-verifier. -/
  cryptoKernel : CryptoKernel Crypto.Reference.D Crypto.Reference.P
  /-- Cross-vat functor laws: the discriminating verifier-functor (model citizen). -/
  phiFunctorial :
    Spec.PhiFunctorial (CellId := Bool) (Rights := Unit) Unit Unit Bool
      (Spec.Phi (Request := Unit) (Statement := Unit) (fun _ => ()))
  /-- Holder anonymity: the NEW discriminating witness (closed surface finding). -/
  holderAnonymity : HolderAnonymity Int

/-- **`dregg_consistent` — THE CAPSTONE (PROVED).** The system-level Prop-carrier surface is
JOINTLY INHABITED by a non-trivial model: every carrier's discriminating witness coexists in one
`SystemModel`. Because the record is inhabited, the conjunction of the carriers is satisfiable —
the assumptions are NOT unsatisfiable (no vacuity) and do NOT derive `False` (no contradiction). -/
noncomputable def dregg_consistent : SystemModel where
  graphPrivacy := graphPrivacyWitness
  blindedMembership := blindedMembershipWitness
  world := worldWitness
  bft := bftWitness
  pacemaker := pacemakerWitness
  superRatification := superRatificationWitness
  cryptoKernel := cryptoKernelWitness
  phiFunctorial := phiFunctorialWitness
  holderAnonymity := discriminatingAnon

/-- **The capstone, as an inhabitation statement.** `SystemModel` is `Nonempty` — the
system-level assumptions are jointly satisfiable. -/
theorem dregg_consistent_nonempty : Nonempty SystemModel := ⟨dregg_consistent⟩

/-! ### §3.1 — Cluster-consistency lemmas (where carriers INTERACT over a shared type).

A per-carrier witness is necessary but not sufficient: carriers sharing a type could be jointly
unsatisfiable or derive `False`. We discharge the three genuine interactions the surface
identified, over the SAME witnesses bundled in `dregg_consistent`. -/

/-- **Cluster A — network ⊗ BFT ⊗ pacemaker (all over `Vote`) are CO-CONSISTENT.** Over the
reference world: the pacemaker derives liveness (a delivered quorum) AND the BFT model satisfies
safety (`bft_agreement`) — liveness and safety hold of the SAME reference network without
deriving `False`. (The `bft_safety` `False`-conclusion fires only on two CONFLICTING quorums,
which the single-block `votes` never supplies — the intended safety contradiction, not a model
inconsistency.) -/
theorem cluster_network_bft_pacemaker_consistent :
    (∃ (block r : Nat), BFTLiveness.Inhabited.cfg.threshold ≤
        ((((BFTLiveness.Inhabited.votesOf (World.recv (Msg := World.Reference.M) r)).filter
          (fun v => v.block = block)).map (·.voter)).dedup).length)
      ∧ (∀ b₁ b₂ : Nat,
          BFT.Inhabited.cfg.n - BFT.Inhabited.cfg.f ≤ (votersFor BFT.Inhabited.votes b₁).length →
          BFT.Inhabited.cfg.n - BFT.Inhabited.cfg.f ≤ (votersFor BFT.Inhabited.votes b₂).length →
          b₁ = b₂) :=
  ⟨BFTLiveness.gst_liveness_of_pacemaker
      BFTLiveness.Inhabited.votesOf BFTLiveness.Inhabited.cfg pacemakerWitness,
   fun b₁ b₂ hq1 hq2 =>
     BFT.bft_agreement BFT.Inhabited.cfg BFT.Inhabited.votes bftWitness b₁ b₂ hq1 hq2⟩

/-- **Cluster B — BFT ⊗ ratification are CO-CONSISTENT.** The DAG-BFT commit (`rg1` super-ratified
from the lace) and the BFT safety floor coexist: the ratification quorum is DERIVED from the real
lace and the same `n−f` intersection core gives safety. Both hold; neither contradicts the other. -/
theorem cluster_bft_ratification_consistent :
    CordialMiners.Committed CordialMiners.Inhabited.state CordialMiners.Inhabited.cfg
        CordialMiners.Inhabited.rg1
      ∧ Nonempty (CordialMiners.SuperRatification CordialMiners.Inhabited.state
          CordialMiners.Inhabited.cfg CordialMiners.Inhabited.rg1) :=
  ⟨CordialMiners.Inhabited.g1_committed, ⟨superRatificationWitness⟩⟩

/-- **Cluster C — holder anonymity ⊗ real membership are CO-CONSISTENT (the CLOSED finding).**
Over `Int` with `compress := refCompress`: real authorized members EXIST (`MemberOf` inhabited)
AND their views are indistinguishable (`hides_law`), all at the NEW discriminating witness — the
hiding is non-vacuous because the membership premise is genuinely met. -/
theorem cluster_anonymity_membership_consistent :
    (MemberOf discriminatingAnon.compress 3 1 ∧ MemberOf discriminatingAnon.compress 3 2)
      ∧ discriminatingAnon.ViewIndistinguishable
          (discriminatingAnon.view 1 3) (discriminatingAnon.view 2 3) := by
  have h1 : MemberOf discriminatingAnon.compress 3 1 := by
    have := BlindedSet.Reference.ref_member_at (x := 1) (s := 2); simpa using this
  have h2 : MemberOf discriminatingAnon.compress 3 2 := by
    have := BlindedSet.Reference.ref_member_at (x := 2) (s := 1); simpa using this
  exact ⟨⟨h1, h2⟩, @blindedset_hides_holder Int discriminatingAnon 3 1 2 h1 h2⟩

/-! ## §4 — CRYPTO-STANDARD carriers (necessarily Lean-trivial — HONEST, isolated, NOT counted).

These are bare `Prop` carriers for cryptographic hardness (DLog, collision-resistance, STARK/FRI
soundness, foreign-chain finality). You CANNOT prove them in Lean, so a `True` discharge in the
reference instance is CORRECT and EXPECTED — and is NOT the non-vacuity evidence. We list them
here ONLY to keep them visibly separate from the system-level witnesses above; the conditioned
theorems consume them as EXPLICIT hypotheses, never silently.

Representative reference discharges (all `= True`, all honest):
  * `CryptoKernel.collisionHard`         (Poseidon2/BLAKE3 collision-resistance)
  * `CryptoPrimitives.{collisionHard,binding,unlinkable}`
  * `{Pedersen,Merkle,Dfa,Temporal,Bridge,BlindedSet,NonMembership,Custom}VerifierKernel.extractable`
  * `MacKernel.unforgeable`              (HMAC-SHA256 unforgeability)
  * `DischargeCrypto.cryptoSound`        (discharged `False` — advertises toy-unsoundness)
  * `ProofForest.ProofNode.StepProofValid`, `EffectsSupply.ForeignFinal`
  * `UCBridge.FComDischarge.{correct,perfectHiding,bindingReducesToDLog}` (CryptHOL-proof data)

We exhibit ONE representative reference discharge to make the isolation literal — the reference
`CryptoKernel.collisionHard` IS `True` (the honest crypto boundary). This `example` is the ONLY
place a `True`-carrier appears in this module, and it is explicitly flagged crypto-standard. -/

/-- ISOLATED crypto-standard boundary: the reference `CryptoKernel`'s `collisionHard` carrier is
`True` — the HONEST Lean discharge of a hardness assumption (Poseidon2 CR). This is NOT non-vacuity
evidence; it is the necessarily-trivial crypto seam, here only to keep it visibly separate. -/
example : @CryptoKernel.collisionHard Crypto.Reference.D Crypto.Reference.P _ cryptoKernelWitness :=
  trivial

/-! ## §5 — Axiom hygiene: the capstone and cluster lemmas are kernel-clean.

Every consistency keystone depends ONLY on the three standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no fresh `axiom`. The
discriminating `HolderAnonymity` witness and the joint `SystemModel` inhabitation are pinned;
the reused witnesses carry their own pins in their home modules (re-checked via the teeth above). -/

#assert_axioms discriminatingAnon
#assert_axioms dregg_consistent
#assert_axioms dregg_consistent_nonempty
#assert_axioms cluster_network_bft_pacemaker_consistent
#assert_axioms cluster_bft_ratification_consistent
#assert_axioms cluster_anonymity_membership_consistent

-- The crypto-standard isolation example and the per-witness teeth are anonymous `example`s
-- (no name to pin); the named keystones above are the audited surface.

#print axioms dregg_consistent_nonempty

end Dregg2.Consistency
