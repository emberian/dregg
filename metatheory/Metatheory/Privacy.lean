/-
# Metatheory.Privacy — the three privacy tiers, on existing cryptographic primitives.

This module encodes dregg2's privacy stack as three first-class tiers (see
`docs/rebuild/dregg2.md §6a` and `docs/rebuild/dregg2-multicell-privacy.md §2`),
distinguished by *what* is hidden, each grounded in deployed crypto:

  1. **Field tier** — *hide a field's value from the schema-public view.* A
     `FieldVisibility` marks each slot `public`/`private`; the public projection
     `project : State → FieldVisibility → Obs` reveals only the public fields. The
     load-bearing law (`field_projection_hides_private`) is that the projection is
     *independent of* the private-field values — selective disclosure. (Zcash
     viewing-key / `FieldVisibility` on `Preserves` records, `00-synthesis §5.1`.)

  2. **Value tier** — *hide an amount while proving it conserves.* A `Commitment`
     with a hiding, **additively-homomorphic** `commit : Value → Blinding →
     Commitment` (Pedersen over Ristretto, `cell/value_commitment.rs`). Conservation
     (`Core.Conservation`, the value tier rides Law 1) is re-expressed *on
     commitments*: `committed_conservation` says Σ committed inputs = Σ committed
     outputs — a Pedersen opening of `Core.conservation_step` that conserves value
     **without revealing amounts**. The homomorphism is an axiom/field of the
     structure, since the witness is the hiding cryptographic map, not a Lean
     computation.

  3. **Graph tier** — *hide who-interacts-with-whom.* Three composing mechanisms:
     `StealthAddr` + `unlinkable` (two payments to the same recipient are
     computationally indistinguishable — EIP-5564/Monero one-time keys,
     `cell/src/stealth.rs`); a `ZkAuthChain` (an auth-derivation/delegation path
     proven legal in ZK, `Verify`-checkable without revealing the nodes — anonymous
     delegation); and `BlindedSet` membership (`memberOf`, ZK-checkable, hides which
     element — `AuthorizedSet::BlindedSet`, Poseidon2 commitment).

  4. **anonymity ⊗ nullifier reconciliation** — the non-obvious one (`§2`, Zcash).
     A `Nullifier` is a *deterministic* per-note tag. The two halves that must hold
     together: `nullifier_prevents_double_spend` (same note ⇒ same nullifier ⇒
     rejected on reuse — determinism gives uniqueness) AND `nullifier_hides_identity`
     (the nullifier is unlinkable to the holder — anonymity). Reconciliation:
     anonymity (unlinkable) and no-double-spend (deterministic uniqueness) are NOT in
     tension; nullifiers gate contention over the spent set without deanonymizing.

Style: spec-first, grind up. Crypto-soundness of the underlying maps (Pedersen
binding/hiding, ZK extractability, the indistinguishability advantage bound) is a
circuit/cryptographic obligation, NEVER discharged in this Lean law (cf.
`Boundary.lean` §8 caveat); here those maps are abstract carriers and the
indistinguishability/hiding facts are stated as honest `Prop`s left `sorry`.
-/
import Metatheory.Core
import Metatheory.Laws
import Metatheory.Resource
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Metatheory.Privacy

open Metatheory.Core
open Metatheory.Laws
open Metatheory.Resource

universe u

/-! ## Tier 1 — Field privacy (selective disclosure). -/

/-- Per-field visibility: a field is either `public` (revealed in the schema-public
view) or `private` (withheld). Marks each named slot of a `Preserves` record. -/
inductive Visibility where
  /-- Revealed in the schema-public view. -/
  | pub
  /-- Withheld from the schema-public view. -/
  | priv
  deriving DecidableEq, Repr

/-- A `FieldVisibility` over a field-name space `Name`: the public/private mask the
schema attaches to each slot (`dregg2.md §6a` tier 1). -/
abbrev FieldVisibility (Name : Type u) := Name → Visibility

/-- The state of a cell as a per-field assignment of values: a record mapping each
field name to its (private) value in `V`. -/
abbrev State (Name : Type u) (V : Type u) := Name → V

/-- The schema-public observation: the value of a field as seen *after* projection,
`none` when the field is private (withheld), `some v` when public. -/
abbrev Obs (Name : Type u) (V : Type u) := Name → Option V

/-- **The public projection.** Reveal only the `public` fields of a state; withhold
(`none`) the `private` ones. Computable and cheap, so it is defined, not `sorry`'d. -/
def project {Name V : Type u} (s : State Name V) (vis : FieldVisibility Name) :
    Obs Name V :=
  fun n => match vis n with
    | Visibility.pub  => some (s n)
    | Visibility.priv => none

/-- **Field tier law: the projection hides private fields.** If two states agree on
every `public` field, their projections are equal — i.e. the public view is
*independent of* the values stored in `private` fields. This is exactly selective
disclosure: a verifier learns the public slots and provably nothing about the rest. -/
theorem field_projection_hides_private
    {Name V : Type u} (vis : FieldVisibility Name) (s s' : State Name V)
    (hpub : ∀ n, vis n = Visibility.pub → s n = s' n) :
    project s vis = project s' vis := by
  funext n
  unfold project
  cases hv : vis n with
  | pub  => rw [hpub n hv]
  | priv => rfl

/-! ## Tier 2 — Value privacy (Pedersen commitments + committed conservation).

The value tier rides `Core.Conservation`: conservation (Law 1) is re-expressed over
hiding commitments so value is conserved without revealing amounts. -/

/-- **A Pedersen-style commitment scheme**, valued over a value monoid `V` and a
blinding monoid `B`, landing in a commitment monoid `C`.

`commit v r` is *hiding* (the blinding `r` masks `v`) and **additively
homomorphic**: committing a sum equals the monoid-sum of the commitments. The
homomorphism is an **axiom/field** of the structure — it is the algebraic content of
Pedersen `Com(v,r) = v·G + r·H` over Ristretto, the cryptographic carrier, not a Lean
computation. Binding/hiding *advantages* are circuit obligations, never proven here. -/
structure Commitment (V B C : Type u) [AddCommMonoid V] [AddCommMonoid B]
    [AddCommMonoid C] where
  /-- The hiding commitment map: value × blinding ↦ commitment. -/
  commit : V → B → C
  /-- **Additive homomorphism** (Pedersen): `commit (a+b) (r+s) = commit a r + commit
  b s`. This is what lets the conservation equalizer run over commitments. -/
  homomorphic : ∀ (a b : V) (r s : B),
    commit (a + b) (r + s) = commit a r + commit b s
  /-- The commitment of `0` value under `0` blinding is the identity commitment — the
  unit compatible with the homomorphism (the neutral note). -/
  commit_zero : commit 0 0 = 0

/-- The homomorphism collapses a finite sum of per-note commitments into a single
commitment of the summed value under the summed blinding. Proved by `Finset`
induction off `Commitment.homomorphic` + `commit_zero`. -/
private theorem commit_sum
    {V B C ι : Type u} [AddCommMonoid V] [AddCommMonoid B] [AddCommMonoid C]
    (scheme : Commitment V B C) (val : ι → V) (bl : ι → B) (s : Finset ι) :
    s.sum (fun i => scheme.commit (val i) (bl i))
      = scheme.commit (s.sum val) (s.sum bl) := by
  classical
  induction s using Finset.induction with
  | empty => simp [scheme.commit_zero]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih,
      scheme.homomorphic]

/-- **Value tier law: committed conservation.** Given a commitment scheme and a
conservation measure `cons : Core.Conservation V` on the value monoid `V`, and a
turn-step witnessed by indexed input/output notes with blindings, the **sum of
committed inputs equals the sum of committed outputs** whenever the cleartext value
conserves (the Pedersen opening of `Core.conservation_step`). Because `commit` is
hiding, this equality holds over commitments alone — value is conserved *without
revealing the amounts*. The blinding totals must match (`Σ rᵢ = Σ sⱼ`), which the
prover arranges; the homomorphism then collapses the per-note sum to a commitment of
the (conserved) value total. -/
theorem committed_conservation
    {V B C : Type u} [AddCommMonoid V] [AddCommMonoid B] [AddCommMonoid C]
    (scheme : Commitment V B C)
    {ι κ : Type u} (insV : ι → V) (inB : ι → B) (outV : κ → V) (outB : κ → B)
    (sin : Finset ι) (sout : Finset κ)
    -- cleartext conservation (Law 1 on the value monoid): inputs sum = outputs sum
    (hval : (sin.sum insV) = (sout.sum outV))
    -- blinding totals match (prover-chosen): inputs' blinding sum = outputs'
    (hblind : (sin.sum inB) = (sout.sum outB)) :
    (sin.sum (fun i => scheme.commit (insV i) (inB i)))
      = (sout.sum (fun j => scheme.commit (outV j) (outB j))) := by
  rw [commit_sum scheme insV inB sin, commit_sum scheme outV outB sout, hval, hblind]

/-! ### Value tier ⇒ camera: the commitment is a monoid hom, and committed
conservation is the Pedersen opening of `Core`/`Resource` conservation.

The value tier does not merely *resemble* the resource world — it *lands* in it.
The Pedersen `homomorphic` axiom is exactly the statement that the commitment map,
read on the pair (value, blinding), is an additive monoid homomorphism into the
commitment monoid `C`. And `committed_conservation` is the literal image, under that
hom, of `Core`'s cleartext conservation (`conservation_ordinary`, a corollary of Law
1's `conservation_step`) — value conserved on commitments *without revealing amounts*.
These are real bridge lemmas (fully PROVED), not restatements. -/

/-- **The commitment as an additive monoid homomorphism.** The Pedersen homomorphism
makes `fun p => commit p.1 p.2` a genuine `AddMonoidHom` from the product value⊕blinding
monoid `V × B` into the commitment monoid `C`: `homomorphic` is precisely
`f (x + y) = f x + f y` on pairs, and `commit_zero` is `f 0 = 0`. This is the algebraic
content of the value tier expressed in the language of the `Resource`/`Core` monoids —
the committed amounts form a `AddCommMonoid`-compatible image. -/
def commitHom {V B C : Type u} [AddCommMonoid V] [AddCommMonoid B] [AddCommMonoid C]
    (scheme : Commitment V B C) : (V × B) →+ C where
  toFun p := scheme.commit p.1 p.2
  map_zero' := scheme.commit_zero
  map_add' := fun x y => scheme.homomorphic x.1 y.1 x.2 y.2

/-- `commitHom` agrees with `commit` definitionally — the bridge does not change the
map, it only re-types it as a hom. -/
@[simp] theorem commitHom_apply
    {V B C : Type u} [AddCommMonoid V] [AddCommMonoid B] [AddCommMonoid C]
    (scheme : Commitment V B C) (v : V) (r : B) :
    commitHom scheme (v, r) = scheme.commit v r := rfl

/-- Being a monoid hom, `commitHom` sends a `Finset` sum of (value, blinding) pairs to
the sum of the commitments — `commit_sum` recovered from the bundled-hom machinery, the
canonical resource-world fact `Σ (f xᵢ) = f (Σ xᵢ)`. -/
theorem commitHom_sum {V B C ι : Type u} [AddCommMonoid V] [AddCommMonoid B]
    [AddCommMonoid C] (scheme : Commitment V B C) (vr : ι → V × B) (s : Finset ι) :
    s.sum (fun i => scheme.commit (vr i).1 (vr i).2) = commitHom scheme (s.sum vr) := by
  classical
  rw [map_sum (commitHom scheme) vr s]
  rfl

/-- **Bridge to `Core.Conservation` (the Pedersen opening of Law 1).** Take any
`Core.Conservation V` measure and an *ordinary* turn `f : Turn A B`. `Core` (Law 1)
gives cleartext conservation `count A = count B` (`conservation_ordinary`, a *proved*
corollary of the primitive `conservation_step`). Committing each side under matching
blindings, the commitment equality follows *purely from the homomorphism* — so a
verifier confirms Law 1 held on this turn while seeing only commitments, never the
counts. This is `committed_conservation` specialised to the single-note image of a real
`Core` turn: the value tier riding `Core.Conservation`. -/
theorem committed_conservation_of_core
    {V B C : Type u} [AddCommMonoid V] [AddCommMonoid B] [AddCommMonoid C]
    (scheme : Commitment V B C) (cons : Core.Conservation V)
    {A A' : Core.Cell} (f : Core.Turn A A') (h : f.tag = Core.TurnTag.ordinary)
    (r : B) :
    scheme.commit (cons.count A) r = scheme.commit (cons.count A') r := by
  rw [Core.conservation_ordinary cons f h]

/-- **Committed conservation is a frame-preserving update on the commitment camera.**
Equal commitments give a trivially frame-preserving update in *any* `ResourceAlgebra`
structure one puts on the commitment carrier `C`: the conserved-value commitment may
replace itself against every frame. Concretely, when the cleartext value conserves over
an ordinary `Core` turn, the resulting commitment is `Resource.Fpu`-related to itself —
the `committed_conservation` equality, read in the camera tier (`Resource.Fpu`,
`Resource.ConservesResource`), recovering Law 1's resource shadow on hidden amounts. -/
theorem committed_conservation_is_fpu
    {V B C : Type u} [AddCommMonoid V] [AddCommMonoid B] [AddCommMonoid C]
    [Resource.ResourceAlgebra C]
    (scheme : Commitment V B C) (cons : Core.Conservation V)
    {A A' : Core.Cell} (f : Core.Turn A A') (h : f.tag = Core.TurnTag.ordinary)
    (r : B) :
    Resource.ConservesResource
      (scheme.commit (cons.count A) r) (scheme.commit (cons.count A') r) := by
  unfold Resource.ConservesResource
  rw [committed_conservation_of_core scheme cons f h r]
  exact Resource.Fpu.refl _

/-! ## Tier 3 — Graph privacy (stealth · ZK auth-chain · blinded membership). -/

/-- A **stealth address**: an abstract one-time destination key derived per-turn from
a recipient's view/spend keys and an ephemeral scalar (EIP-5564/Monero;
`cell/src/stealth.rs`). Concrete data is opaque here; what matters is the
unlinkability relation below. -/
structure StealthAddr where
  /-- The one-time public key bytes (opaque). -/
  oneTimeKey : Nat
  deriving DecidableEq, Repr

/-- A long-term recipient identity (the spend key behind any number of stealth
addresses). -/
structure Recipient where
  id : Nat
  deriving DecidableEq, Repr

/-- `derivedFrom a R` : the stealth address `a` is a legitimate one-time key for
recipient `R` (there exists an ephemeral scalar producing it). Abstract — the witness
is the DH derivation, a cryptographic carrier. -/
def derivedFrom (a : StealthAddr) (R : Recipient) : Prop := sorry

/-- **Computational indistinguishability** of two stealth addresses, stated
abstractly as a `Prop`: no efficient observer can tell them apart (the
advantage-bound is a cryptographic obligation, not a Lean fact). -/
def Indistinguishable (a a' : StealthAddr) : Prop := sorry

/-- **Graph tier law: stealth unlinkability.** Two stealth addresses derived for the
*same* recipient are computationally indistinguishable — i.e. two payments to one
recipient cannot be linked on the public graph (per-invocation unlinkability,
`§2 graph`). -/
theorem unlinkable
    (R : Recipient) (a a' : StealthAddr)
    (h : derivedFrom a R) (h' : derivedFrom a' R) :
    Indistinguishable a a' := by
  -- PRIMITIVE/OPEN: crypto-soundness (DH/one-time-key indistinguishability advantage)
  -- over abstract carriers `derivedFrom`/`Indistinguishable`; circuit obligation, §8 caveat.
  sorry

/-- An **abstract delegation/auth-derivation path** (a CDT chain of capability
derivations): the sequence of nodes from a root authority to the invoker. The graph
tier hides these nodes. -/
structure AuthPath where
  /-- The ordered node ids along the derivation (the secret the ZK proof hides). -/
  nodes : List Nat
  deriving Repr

/-- `LegalDerivation path` : the path is a legal capability-derivation chain (each
hop a valid attenuation/delegation). The honest content the ZK proof attests. -/
def LegalDerivation (path : AuthPath) : Prop := sorry

/-- A **ZK auth-chain proof object** over a witness space `W`: a `Verify`-checkable
certificate (via `Laws.Verifiable`) that *some* legal derivation path exists, carried
as predicate `pred` and witness `wit`, **without revealing the path itself**
(anonymous delegation, `dregg2.md §6a` tier 3). `W` is explicit so instance
resolution sees the carrier. -/
structure ZkAuthChain (P W : Type u) [Verifiable P W] where
  /-- The verifier-local predicate "a legal derivation exists for this invocation." -/
  pred : P
  /-- The hidden witness (the path + blindings); `Verify pred wit` accepts it. -/
  wit : W

/-- **Graph tier law: ZK auth-chain soundness, path-hiding.** If the verifier accepts
the chain's witness (`Discharged`), then a legal derivation path exists — yet the
verifier only ever touched `pred`/`wit`, never the path's nodes. The existential
*hides* the path while the verify-side certifies legality (soundness-by-verification,
`Laws.search_sound` flavour). -/
theorem zkauthchain_sound
    {P W : Type u} [Verifiable P W] (chain : ZkAuthChain P W)
    (h : Discharged chain.pred chain.wit) :
    ∃ path : AuthPath, LegalDerivation path := by
  -- PRIMITIVE/OPEN: ZK extractability — `Discharged` accept ⇒ a `LegalDerivation`
  -- witness exists is a knowledge-soundness obligation over abstract `LegalDerivation`; §8.
  sorry

/-- A **set commitment** over an element space `Elem`: a single short commitment
(Poseidon2 root) to a whole authorized/issuer set, revealing neither the members nor
their count (`AuthorizedSet::BlindedSet`). -/
structure SetCommitment (Elem : Type u) where
  /-- The commitment root (opaque). -/
  root : Nat
  deriving Repr

/-- **Blinded-set membership** `memberOf e sc` : element `e` is committed in the set
`sc`. ZK-checkable (the witness is a Merkle/accumulator opening) and **hides which
element** is being tested — authorized-without-revealing-which. Abstract Prop. -/
def memberOf {Elem : Type u} (e : Elem) (sc : SetCommitment Elem) : Prop := sorry

/-- A **membership proof** `MemProof e sc` is the ZK-checkable witness that `e ∈ sc`,
carried as a `Verifiable` predicate/witness pair so the verifier touches the
commitment and the (blinded) witness, never the element. `W` explicit for instance
resolution. -/
structure MemProof (P W : Type u) [Verifiable P W] (Elem : Type u)
    (sc : SetCommitment Elem) where
  /-- The predicate "the committed element opens at `sc.root`". -/
  pred : P
  /-- The blinded opening witness. -/
  wit : W

/-- **Graph tier law: blinded membership hides the element.** Two *distinct* elements
can each be a witnessed member of the *same* commitment `sc`, and the verifier,
seeing only `sc` and a `Discharged` proof, cannot tell which was tested: the two
membership facts are simultaneously satisfiable while `e ≠ e'`. So a verifier learns
membership-holds but provably not *which* element (holder-blinding; `dregg2.md §6a`,
blinded-queue / issuer-set). -/
theorem blinded_membership_hides_element
    {Elem : Type u} (sc : SetCommitment Elem) :
    ∃ e e' : Elem, e ≠ e' ∧ memberOf e sc ∧ memberOf e' sc := by
  -- PRIMITIVE/OPEN: hiding of the blinded set — two distinct elements both opening the
  -- same root is the hiding property of `memberOf` (abstract Prop carrier); circuit, §8.
  sorry

/-! ## Tier 3 reconciliation — anonymity ⊗ nullifier (no double-spend). -/

/-- A **note**: a unit of committed value/authority that can be spent at most once
(Zcash note). Opaque secret seed; its nullifier is derived deterministically. -/
structure Note where
  /-- The note's secret seed / position (the spend-key-bound preimage). -/
  seed : Nat
  deriving DecidableEq, Repr

/-- A **nullifier**: the deterministic per-note tag published on spend (Zcash
`nf = PRF_nk(ρ)`). Same note ⇒ same nullifier; a spent set of nullifiers gates
double-spends without revealing the spender. -/
structure Nullifier where
  tag : Nat
  deriving DecidableEq, Repr

/-- **The deterministic nullifier map.** Each note has exactly one nullifier
(a function of the note), which is what makes reuse detectable. Abstract carrier
(PRF under the spend key); declared as data, opening is a circuit obligation. -/
def nullifierOf : Note → Nullifier := sorry

/-- A **spent set**: the published set of consumed nullifiers (the public contention
gate over the concurrent spent-note set). -/
abbrev SpentSet := Nullifier → Bool

/-- `accepted spent n` : a spend of nullifier `n` against the published `spent` set is
accepted iff `n` is not already present (fail-closed on reuse). -/
def accepted (spent : SpentSet) (n : Nullifier) : Prop := spent n = false

/-- **Reconciliation, half 1 — no double-spend (determinism ⇒ uniqueness).** Spending
the *same* note twice yields the *same* nullifier; once that nullifier is in the spent
set, the second spend is rejected. So determinism of `nullifierOf` enforces
at-most-once spend over the concurrent set. -/
theorem nullifier_prevents_double_spend
    (note : Note) (spent : SpentSet)
    -- the note was already spent: its nullifier is recorded
    (hspent : spent (nullifierOf note) = true) :
    ¬ accepted spent (nullifierOf note) := by
  -- Pure structural fact (no crypto): `accepted` means `spent … = false`, contradicting
  -- `hspent : spent … = true`. Determinism of `nullifierOf` is what makes the *same* note
  -- yield this *same* tag (carrier-level), but the rejection itself is decidable Bool logic.
  unfold accepted
  rw [hspent]
  simp

/-- **Reconciliation, half 2 — anonymity (the nullifier hides the holder).** The
published nullifier is unlinkable to the note's holder/identity: it is computationally
indistinguishable from a fresh random tag, so observing nullifiers-out reveals nothing
about *who* spent. Stated abstractly (the advantage bound is a circuit obligation). -/
def UnlinkableToHolder (n : Nullifier) : Prop := sorry

theorem nullifier_hides_identity (note : Note) :
    UnlinkableToHolder (nullifierOf note) := by
  -- PRIMITIVE/OPEN: anonymity advantage bound on the abstract `UnlinkableToHolder` carrier
  -- (nullifier ≈ fresh random tag); pure crypto-soundness obligation, never in Lean, §8.
  sorry

/-- **The reconciliation theorem.** Anonymity (the nullifier hides the holder) and
no-double-spend (deterministic uniqueness gates reuse) hold *together*, for every note
— they are not in tension. This is the Zcash-style answer to "anonymous parties in a
contended JointTurn": the spent set orders/gates contention while the spender stays
hidden (`§2`, the anonymity ⊗ consensus reconciliation). -/
theorem anonymity_nullifier_reconciliation
    (note : Note) (spent : SpentSet)
    (hspent : spent (nullifierOf note) = true) :
    UnlinkableToHolder (nullifierOf note)
      ∧ ¬ accepted spent (nullifierOf note) := by
  -- Reconciliation = the conjunction of the two halves. The no-double-spend half is the
  -- proved structural lemma; the anonymity half reduces to the sibling primitive
  -- `nullifier_hides_identity` (the single remaining crypto carrier). No new `sorry` here.
  exact ⟨nullifier_hides_identity note,
    nullifier_prevents_double_spend note spent hspent⟩

end Metatheory.Privacy
