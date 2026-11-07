/-
# Dregg2.Consistency — the global consistency witness (non-vacuity + non-contradiction).

The dregg2 metatheory conditions its keystones on Prop-carrying typeclasses (`World`,
`BFTModel`/`Pacemaker`, `GraphPrivacyKernel`/`BlindedMembershipKernel`, `Hyperedge`/`JointBinding`,
`CryptoKernel`, `HolderAnonymity`, …). If those carriers were jointly unsatisfiable the whole
edifice would be vacuous; if their conjunction derived `False` it would be contradictory.

This module proves a concrete, axiom-clean consistency witness: every system-level Prop-carrier
is inhabited by a discriminating model — one that rejects dishonest inputs (each carries a
tooth `example`). `dregg_consistent` packages the joint inhabitation as a single record; cluster
lemmas check co-instantiation of interacting carriers.

OPEN: faithfulness to the real Rust system is a separate grounding axis, not proved here.
The crypto-standard carriers (`collisionHard`, `binding`, `extractable`, …) cannot be proved in
Lean — they are isolated in §4 and are NOT the non-vacuity evidence.
-/

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

/-! ## §1 — A discriminating `HolderAnonymity` witness.

The prior `HolderAnonymity` witness had `view ≡ 0`, `ViewIndistinguishable ≡ fun _ _ => True` —
an all-True collapse making `blindedset_hides_holder` vacuous. We replace it with a concrete,
discriminating witness (over `Digest := Int`):

  * `compress := BlindedSet.Reference.refCompress` (`= (·+·)`), so `MemberOf` is
    inhabited via `ref_member_at`;
  * `view _ root := root.toNat` — depends only on the issuer root, not which member. Different
    roots give different views (the tooth ruling out `fun _ _ => 0`);
  * `ViewIndistinguishable := Eq` — concrete equality, not the `True`-collapsible carrier.

`hides_law` closes by `rfl` (two members of the same root have the same root-indexed view). -/

/-- **The discriminating holder-anonymity witness.**
`view _ root := root.toNat` collapses which member while separating issuer roots;
`ViewIndistinguishable := Eq` is the concrete view-equality conclusion (not `True`-collapsible).
A `def`, not a global `instance`, following the `Privacy.graphRef`/`memRefNat` idiom: witnesses
the interface is inhabitable by a non-trivial model without silently satisfying a `[HolderAnonymity]`
obligation. (`@[reducible]` only silences the class-typed-`def` lint.) -/
@[reducible] def discriminatingAnon : HolderAnonymity Int where
  compress := BlindedSet.Reference.refCompress
  view _ root := root.toNat
  ViewIndistinguishable := Eq
  hides_law _ _ _ _ _ := rfl

/-- Tooth 1 — the hiding law is genuine: two authorized members of the same issuer root produce
equal views. Routed through `blindedset_hides_holder` at the discriminating witness. -/
example (root m m' : Int)
    (h : MemberOf discriminatingAnon.compress root m)
    (h' : MemberOf discriminatingAnon.compress root m') :
    discriminatingAnon.ViewIndistinguishable
      (discriminatingAnon.view m root) (discriminatingAnon.view m' root) :=
  @blindedset_hides_holder Int discriminatingAnon root m m' h h'

/-- Tooth 2 — the view is non-constant: roots `3` and `5` give different views, so
`view ≢ fun _ _ => c` and `ViewIndistinguishable` is the honest `Eq`, not a `True`-collapse. -/
example (m m' : Int) :
    discriminatingAnon.view m 3 ≠ discriminatingAnon.view m' 5 := by
  show (3 : Int).toNat ≠ (5 : Int).toNat
  decide

/-- Tooth 3 — real members exist: `compress := refCompress` makes `MemberOf` inhabited
(`ref_member_at`). Here `1` and `2` are authorized members of root `3`. -/
example : MemberOf discriminatingAnon.compress 3 1 ∧ MemberOf discriminatingAnon.compress 3 2 := by
  refine ⟨?_, ?_⟩
  · have := BlindedSet.Reference.ref_member_at (x := 1) (s := 2); simpa [HolderAnonymity.compress] using this
  · have := BlindedSet.Reference.ref_member_at (x := 2) (s := 1); simpa [HolderAnonymity.compress] using this

/-- Tooth 4 — the full non-vacuous statement: members `1` and `2` of root `3` are authorized
and have indistinguishable views at the discriminating witness. -/
example :
    discriminatingAnon.ViewIndistinguishable
      (discriminatingAnon.view 1 3) (discriminatingAnon.view 2 3) := by
  have h1 : MemberOf discriminatingAnon.compress 3 1 := by
    have := BlindedSet.Reference.ref_member_at (x := 1) (s := 2); simpa [HolderAnonymity.compress] using this
  have h2 : MemberOf discriminatingAnon.compress 3 2 := by
    have := BlindedSet.Reference.ref_member_at (x := 2) (s := 1); simpa [HolderAnonymity.compress] using this
  exact @blindedset_hides_holder Int discriminatingAnon 3 1 2 h1 h2

/-! ## §2 — Reused system-level witnesses, re-exhibited with teeth.

The remaining system-level carriers have non-trivial axiom-clean witnesses in their home modules.
We re-expose each as a named handle and re-check a discrimination tooth that distinguishes the
witness from the trivial model. -/

/-! ### §2.1 — Privacy: `graphRef` (stealth/nullifier) + `memRefNat` (blinded membership). -/

/-- Handle: the non-trivial graph-privacy witness (`addrView a := a.oneTimeKey % 2`, non-constant). -/
abbrev graphPrivacyWitness : GraphPrivacyKernel := Privacy.Reference.graphRef
/-- Handle: the non-trivial blinded-membership witness (`memberOf e _ := e < 2`, genuine predicate). -/
abbrev blindedMembershipWitness : BlindedMembershipKernel Nat := Privacy.Reference.memRefNat

/-- Tooth — `graphRef`'s `addrView` is non-constant: addresses for two recipients differ. -/
example : @GraphPrivacyKernel.addrView graphPrivacyWitness ⟨0⟩
    ≠ @GraphPrivacyKernel.addrView graphPrivacyWitness ⟨1⟩ := by
  show (0 : Nat) % 2 ≠ 1 % 2; decide

/-- Tooth — `memRefNat`'s membership predicate is genuine, not `fun _ => True`: `2` is no member. -/
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

/-- Tooth — the reference world's schedule delivers a quorum (computes `true`). -/
example : quorumReached ((World.recv (Msg := World.Reference.M) 3)) ⟨3, 0, 3⟩ 7 = true := by decide

/-- Tooth — `bft_agreement` applies to the BFT witness: two `n−f`-quorum blocks must coincide. -/
example (b₁ b₂ : Nat)
    (hq1 : BFT.Inhabited.cfg.n - BFT.Inhabited.cfg.f ≤ (votersFor BFT.Inhabited.votes b₁).length)
    (hq2 : BFT.Inhabited.cfg.n - BFT.Inhabited.cfg.f ≤ (votersFor BFT.Inhabited.votes b₂).length) :
    b₁ = b₂ :=
  BFT.bft_agreement BFT.Inhabited.cfg BFT.Inhabited.votes bftWitness b₁ b₂ hq1 hq2

/-- Tooth — liveness is derived for the pacemaker witness: the quorum follows from delivery. -/
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

/-- Tooth — the ratifying quorum is met on the lace (`≥ n−f = 3` ratifiers), not
assumed: `rg1` is committed. -/
example : CordialMiners.Committed CordialMiners.Inhabited.state CordialMiners.Inhabited.cfg
    CordialMiners.Inhabited.rg1 :=
  CordialMiners.Inhabited.g1_committed

/-! ### §2.4 — Cross-cell binding: `Hyperedge` (apex) + `JointBinding` (binary) are PROPER. -/

/-- Handle: a real `N`-cycle hyperedge over ℤ with Σ-zero half-edges (here `N = 3`, `δ = id`). -/
noncomputable abbrev hyperedgeWitness :=
  Hyperedge.ringHyperedge 3 (fun i => (i : ℤ))

/-- Tooth — the hyperedge binding is a proper subobject: some product config is not
`HyperAdmissible` (CG-5 `1 ≠ 0`), so the binding carries genuine content. -/
example : ∃ (T : Boundary.TurnCoalg Unit Unit)
    (turnId : Unit → JointTurn.TurnIdOf (TurnId := Unit) T)
    (halfEdge : Unit → JointTurn.HalfEdgeOf (Bal := Nat) T)
    (xs : Unit → T.Carrier) (t : Unit),
    ¬ Hyperedge.HyperAdmissible Unit T turnId halfEdge xs t :=
  Hyperedge.hyper_binding_is_proper

/-- Tooth — the binary `JointBinding` is likewise a proper subobject: some product config is
excluded by CG-5 `1 + 1 ≠ 0`. The cross-cell binding is more than per-cell × per-cell. -/
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

/-- Tooth — the reference `verify` accepts a matching proof... -/
example : CryptoKernel.verify (Digest := Crypto.Reference.D) (Proof := Crypto.Reference.P) 7 7 = true := by
  decide
/-- ...and rejects a non-matching one (not Verify-always-true). -/
example : CryptoKernel.verify (Digest := Crypto.Reference.D) (Proof := Crypto.Reference.P) 7 8 = false := by
  decide

/-! ### §2.6 — Cross-vat functoriality: `phi_functorial_concrete` (the model citizen). -/

/-- Handle: the discriminating verifier-functor witness, reused under this module's
`concreteVerifiable` (definitionally equal to VatBoundary's). -/
abbrev phiFunctorialWitness :
    Spec.PhiFunctorial (CellId := Bool) (Rights := Unit) Unit Unit Bool
      (Spec.Phi (Request := Unit) (Statement := Unit) (fun _ => ())) :=
  Spec.phi_functorial_concrete

/-! ## §3 — The capstone: joint non-trivial inhabitation.

The system-level carriers do not all share a single type parameter (privacy over `StealthAddr`/`Nat`,
consensus over `Vote`, cross-cell over `TurnCoalg`, cross-vat over `Int`/`Bool`), so a single
joint `instance` is a type-parameter clash. We therefore package the joint inhabitation as one
inhabited record bundling all discriminating witnesses simultaneously, plus cluster-consistency
lemmas where carriers interact over a shared type. The bundle being inhabited means
all carriers coexist in one Lean context without deriving `False`: the system is neither vacuous
nor contradictory at the system level. -/

/-- `SystemModel` — a record bundling all system-level carriers' discriminating witnesses.
Its inhabitation (`dregg_consistent`) is the joint-consistency statement. The cross-cell
`Hyperedge`/`JointBinding` carriers are parametric proper-subobject facts rather than typeclasses;
their non-triviality is `hyper_binding_is_proper`/`binding_is_proper`, exhibited as teeth in §2.4. -/
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

/-- `dregg_consistent` — the joint non-vacuity capstone. The system-level Prop-carriers are
jointly inhabited by discriminating witnesses: every carrier coexists in one `SystemModel`,
confirming the assumptions are satisfiable (no vacuity) and do not derive `False` (no contradiction). -/
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

/-- `SystemModel` is `Nonempty` — the system-level assumptions are jointly satisfiable. -/
theorem dregg_consistent_nonempty : Nonempty SystemModel := ⟨dregg_consistent⟩

/-! ### §3.1 — Cluster-consistency lemmas.

Carriers sharing a type parameter could be jointly unsatisfiable even if individually satisfied.
We discharge the three genuine interactions over the same witnesses as `dregg_consistent`. -/

/-- **Cluster A — network ⊗ BFT ⊗ pacemaker are co-consistent.** Over the reference world the
pacemaker derives liveness and the BFT model satisfies safety (`bft_agreement`) simultaneously —
liveness and safety hold of the same reference network without deriving `False`. -/
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

/-- **Cluster B — BFT ⊗ ratification are co-consistent.** The DAG-BFT commit (`rg1` super-ratified
from the lace) and the BFT safety floor coexist without contradiction. -/
theorem cluster_bft_ratification_consistent :
    CordialMiners.Committed CordialMiners.Inhabited.state CordialMiners.Inhabited.cfg
        CordialMiners.Inhabited.rg1
      ∧ Nonempty (CordialMiners.SuperRatification CordialMiners.Inhabited.state
          CordialMiners.Inhabited.cfg CordialMiners.Inhabited.rg1) :=
  ⟨CordialMiners.Inhabited.g1_committed, ⟨superRatificationWitness⟩⟩

/-- **Cluster C — holder anonymity ⊗ real membership are co-consistent.** Over `Int` with
`compress := refCompress`: real authorized members exist and their views are indistinguishable at
the discriminating witness — the hiding is non-vacuous. -/
theorem cluster_anonymity_membership_consistent :
    (MemberOf discriminatingAnon.compress 3 1 ∧ MemberOf discriminatingAnon.compress 3 2)
      ∧ discriminatingAnon.ViewIndistinguishable
          (discriminatingAnon.view 1 3) (discriminatingAnon.view 2 3) := by
  have h1 : MemberOf discriminatingAnon.compress 3 1 := by
    have := BlindedSet.Reference.ref_member_at (x := 1) (s := 2); simpa [HolderAnonymity.compress] using this
  have h2 : MemberOf discriminatingAnon.compress 3 2 := by
    have := BlindedSet.Reference.ref_member_at (x := 2) (s := 1); simpa [HolderAnonymity.compress] using this
  exact ⟨⟨h1, h2⟩, @blindedset_hides_holder Int discriminatingAnon 3 1 2 h1 h2⟩

/-! ## §4 — Crypto-standard carriers (necessarily Lean-trivial — isolated, not counted).

These `Prop` carriers cover cryptographic hardness (DLog, collision-resistance, STARK/FRI soundness,
foreign-chain finality). They cannot be proved in Lean; a `True` discharge in the reference
instance is correct and expected, and is NOT the non-vacuity evidence. They are isolated here
so they remain visibly separate from the system-level witnesses above; conditioned theorems
consume them as explicit hypotheses, never silently.

Representative reference discharges (all `= True`, all honest):
  `CryptoKernel.collisionHard`, `CryptoPrimitives.{collisionHard,binding,unlinkable}`,
  `{Pedersen,Merkle,Dfa,…}VerifierKernel.extractable`, `MacKernel.unforgeable`,
  `DischargeCrypto.cryptoSound` (discharged `False` — advertises toy-unsoundness),
  `UCBridge.FComDischarge.{correct,perfectHiding,bindingReducesToDLog}` (CryptHOL-proof data). -/

/-- Isolated crypto-standard boundary: the reference `CryptoKernel`'s `collisionHard` is `True` —
the honest Lean discharge of a hardness assumption (Poseidon2 CR). Not non-vacuity evidence;
necessarily trivial, isolated here to keep it visibly separate. -/
example : @CryptoKernel.collisionHard Crypto.Reference.D Crypto.Reference.P _ cryptoKernelWitness :=
  trivial

/-! ## §5 — Axiom hygiene.

Every consistency keystone depends only on the three standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`). -/

#assert_axioms discriminatingAnon
#assert_axioms dregg_consistent
#assert_axioms dregg_consistent_nonempty
#assert_axioms cluster_network_bft_pacemaker_consistent
#assert_axioms cluster_bft_ratification_consistent
#assert_axioms cluster_anonymity_membership_consistent

-- The crypto-standard isolation example and per-witness teeth are anonymous `example`s.

#print axioms dregg_consistent_nonempty

end Dregg2.Consistency
