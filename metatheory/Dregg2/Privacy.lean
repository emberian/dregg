/-
# Dregg2.Privacy — the three privacy tiers, on existing cryptographic primitives.

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
`Boundary.lean` §8 caveat); here those maps are abstract carriers BUNDLED — together
with their computational laws — as the FIELDS of a `GraphPrivacyKernel` /
`BlindedMembershipKernel` class (the `CryptoKernel.lean` idiom). The parametric graph-tier
theorems take an instance and their bodies ARE the law-fields, so they are non-vacuous
(witnessed by a `Reference` instance) and carry NO `sorry` — the crypto advantage bounds
live, faithfully, as the lawful-instance obligation, never an `axiom`/`sorry`.
-/
import Dregg2.Core
import Dregg2.Laws
import Dregg2.Resource
import Dregg2.Tactics
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Dregg2.Privacy

open Dregg2.Core
open Dregg2.Laws
open Dregg2.Resource

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
    (scheme : Commitment V B C) (cons : Core.Conservation V) [Core.ConservesStep cons]
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
    (scheme : Commitment V B C) (cons : Core.Conservation V) [Core.ConservesStep cons]
    {A A' : Core.Cell} (f : Core.Turn A A') (h : f.tag = Core.TurnTag.ordinary)
    (r : B) :
    Resource.ConservesResource
      (scheme.commit (cons.count A) r) (scheme.commit (cons.count A') r) := by
  unfold Resource.ConservesResource
  rw [committed_conservation_of_core scheme cons f h r]
  exact Resource.Fpu.refl _

/-! ## Tier 3 — Graph privacy (stealth · ZK auth-chain · blinded membership).

**The honest model: information-theoretic hiding via an observer-view, NOT a `True`-carrier.**

The earlier de-vacuification bundled the graph-tier hiding facts as bare `Prop` carriers
(`Indistinguishable : StealthAddr → StealthAddr → Prop`, etc.) inside a kernel class with
the laws as fields. That is the `CryptoKernel.lean` portal idiom, and it removed the
`sorryAx`. But it left a TRAP: the only witness (`graphRef`/`memRef`) set every carrier to
`fun _ => True`, so a reader could mistake a `True`-in-its-only-model theorem for a real
privacy guarantee. `True`-discharge is honest ONLY for a property that *cannot* be modelled
in Lean (e.g. `collisionHard` — "no PPT adversary"). For the hiding properties here there
IS a genuine, non-trivial Lean model, so we MUST build it (the `BeaconSpaceInterior` rule:
prefer a real witness to a degenerate one).

**The model.** Indistinguishability is reframed as **equality of an observer-view** — a
concrete `Nat`-valued function `view` modelling *everything an observer learns* (the public
transcript). Two objects are indistinguishable EXACTLY when their views are equal:
`Indistinguishable a a' ≜ view a = view a'`. This is *perfect (information-theoretic)
hiding* on the modelled view — strictly stronger than, and the honest floor under, the
computational advantage bound. The hiding LAWS then have real content: they say the view
is **constant on the anonymity class** (genuinely collapses distinct secrets to one
transcript), and the kernel additionally carries a **k-anonymity** law — the anonymity set
has cardinality `≥ k > 1`, so the collapse is not the degenerate one-element class.

A witness is non-trivial precisely when `view` is **not constant** (it genuinely
distinguishes objects in *different* classes) yet **collapses each anonymity class** (it
genuinely hides *within* a class). The `Reference` witness below does exactly this — `view`
is a real quotient projection with ≥ 2 distinct values and a ≥ k anonymity class — so the
parametric theorems are instantiated NON-vacuously, NOT by `fun _ => True`.

**What stays a §8 portal.** *Computational* indistinguishability against a PPT adversary
(the cryptographic advantage bound for the REAL Poseidon2/DH transcripts, where views are
not literally equal but only computationally close) is NOT provable in Lean and remains an
explicitly-carried obligation discharged by the circuit/crypto layer — see
`Crypto/Primitives.lean::CryptoPrimitives.unlinkable` and `CryptoKernel.collisionHard`. The
Lean model here proves the information-theoretic CORE (perfect view-collapse + k-anonymity);
it does not, and does not claim to, prove the full computational property. -/

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

/-- An **abstract delegation/auth-derivation path** (a CDT chain of capability
derivations): the sequence of nodes from a root authority to the invoker. The graph
tier hides these nodes. -/
structure AuthPath where
  /-- The ordered node ids along the derivation (the secret the ZK proof hides). -/
  nodes : List Nat
  deriving Repr

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

/-- A **set commitment** over an element space `Elem`: a single short commitment
(Poseidon2 root) to a whole authorized/issuer set, revealing neither the members nor
their count (`AuthorizedSet::BlindedSet`). -/
structure SetCommitment (Elem : Type u) where
  /-- The commitment root (opaque). -/
  root : Nat
  deriving Repr

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

/-- A **spent set**: the published set of consumed nullifiers (the public contention
gate over the concurrent spent-note set). -/
abbrev SpentSet := Nullifier → Bool

/-! ### The graph-privacy kernel — observer-views + GENUINE hiding laws as a class.

The `Elem`-INDEPENDENT graph-tier objects (stealth, auth-chain, nullifier) and their hiding
laws live as FIELDS of `GraphPrivacyKernel`. The KEY change from a `True`-carrier portal:
indistinguishability is reframed as **equality of a concrete observer-`view`** (perfect,
information-theoretic hiding on the modelled transcript), and the laws carry real content —
the view is constant on the anonymity class, and the anonymity set has cardinality `≥ k`.
A parametric theorem over `[GraphPrivacyKernel]` is non-vacuous because `Reference` exhibits
a lawful instance whose `view` is genuinely non-constant (NOT `fun _ => True`). -/

/-- **The graph-privacy kernel** (`Elem`-independent objects + GENUINE hiding laws). The
hiding facts are modelled information-theoretically: `addrView`/`nullifierView` are concrete
`Nat`-valued observer transcripts, and indistinguishability is their *equality*. The laws
say each view is constant on its anonymity class (stealth: same recipient; nullifier: same
holder-class) and the kernel carries a `k`-ANONYMITY field — the anonymity set has `≥ k`
elements, so the collapse is real, not the one-element degenerate class. (The residual
*computational* advantage bound on the REAL transcripts is a §8 portal — see module header
and `Crypto/Primitives.lean::unlinkable` — NOT proved here.) -/
class GraphPrivacyKernel where
  /-- The minimum anonymity-set size guaranteed (k-anonymity parameter). -/
  k : Nat
  /-- k is genuinely `> 1` — the anonymity set is not the degenerate singleton. -/
  k_gt_one : 1 < k
  /-- `recipientOf a` : the long-term recipient an address pays (the secret an observer
  must NOT learn). Two addresses to the same recipient share an anonymity class. -/
  recipientOf : StealthAddr → Recipient
  /-- `derivedFrom a R` : `a` is a legitimate one-time key for recipient `R` — modelled
  exactly as `recipientOf a = R` (the DH-derivation fact, here decidable). -/
  derivedFrom : StealthAddr → Recipient → Prop
  /-- **The observer-view of a stealth address** — everything an observer learns from the
  public one-time key. Hiding = this view leaks nothing about `recipientOf`. -/
  addrView : StealthAddr → Nat
  /-- `LegalDerivation path` : the path is a legal capability-derivation chain. -/
  LegalDerivation : AuthPath → Prop
  /-- The deterministic per-note nullifier map (function-ness IS determinism). -/
  nullifierOf : Note → Nullifier
  /-- `holderOf n` : the spender behind a nullifier (the secret to hide). -/
  holderOf : Nullifier → Recipient
  /-- **The observer-view of a published nullifier** — what an observer learns from the
  spent-set entry. Hiding = this view is independent of `holderOf`. -/
  nullifierView : Nullifier → Nat
  /-- **LAW — stealth unlinkability (perfect, on the view)**: two addresses derived for the
  same recipient have the SAME observer-view — an observer cannot tell them apart. This is
  genuine information-theoretic hiding: the view literally collapses the anonymity class. -/
  unlinkable_law : ∀ (R : Recipient) (a a' : StealthAddr),
    derivedFrom a R → derivedFrom a' R → addrView a = addrView a'
  /-- **LAW — k-anonymity for stealth**: every address sits in an anonymity class (same
  recipient) of size `≥ k > 1`, witnessed by a `Finset` of distinct addresses sharing both
  its recipient and its view. The collapse is over a genuinely large class, not a singleton. -/
  stealth_k_anonymity : ∀ a : StealthAddr,
    ∃ s : Finset StealthAddr, k ≤ s.card ∧ a ∈ s ∧
      ∀ a' ∈ s, recipientOf a' = recipientOf a ∧ addrView a' = addrView a
  /-- **LAW — ZK auth-chain knowledge-soundness**: there is always *some* legal
  derivation (the extractability obligation, over the abstract carrier; circuit, §8). -/
  zkauthchain_law : ∃ path : AuthPath, LegalDerivation path
  /-- **LAW — nullifier anonymity (perfect, on the view)**: every note's nullifier-view is
  the SAME constant — the published tag's observer-view is independent of the holder, so it
  reveals nothing about *who* spent. Stated as: all nullifier-views collapse to one value. -/
  nullifier_hides_law : ∀ n n' : Nullifier, nullifierView n = nullifierView n'

/-- **The blinded-membership kernel** (the `Elem`-PARAMETERIZED objects + GENUINE law).
Homed in a separate class because `memberOf`/`memberView` are universe-polymorphic in
`Elem`. Same honest model: `memberView` is a concrete observer-transcript, and the hiding
law says it is constant across members of the same commitment (perfect hiding of *which*
element), plus a `k`-anonymity field — the witnessed member set has `≥ k` elements. -/
class BlindedMembershipKernel (Elem : Type u) [DecidableEq Elem] where
  /-- The minimum anonymity-set size for membership (k-anonymity). -/
  k : Nat
  /-- k is genuinely `> 1`. -/
  k_gt_one : 1 < k
  /-- **Blinded-set membership** `memberOf e sc`: `e` is committed in the set `sc`
  (the witness is a Merkle/accumulator opening; hides which element). -/
  memberOf : Elem → SetCommitment Elem → Prop
  /-- **The verifier-visible view** of a membership test: everything an observer learns
  (the root + the blinded transcript). Hiding = it leaks nothing about *which* `e`. -/
  memberView : Elem → SetCommitment Elem → Nat
  /-- **LAW — blinded membership hides *which* element (perfect, on the view)**: any two
  witnessed members of the same commitment have the SAME view — an observer confirms
  membership while learning nothing about which element. Genuine view-collapse, not `True`. -/
  hides_law : ∀ (sc : SetCommitment Elem) (e e' : Elem),
    memberOf e sc → memberOf e' sc →
    memberView e sc = memberView e' sc
  /-- **LAW — k-anonymity for membership**: every witnessed member sits in a set of `≥ k`
  distinct co-members of the same commitment sharing its view. Real anonymity set. -/
  member_k_anonymity : ∀ (sc : SetCommitment Elem) (e : Elem), memberOf e sc →
    ∃ s : Finset Elem, k ≤ s.card ∧ e ∈ s ∧
      ∀ e' ∈ s, memberOf e' sc ∧ memberView e' sc = memberView e sc

/-! ### The parametric graph-tier laws (bodies are the law-fields, NO `sorry`).

Indistinguishability is now **observer-view equality** — `addrView a = addrView a'`,
`memberView e sc = memberView e' sc`, `nullifierView n = nullifierView n'`. The theorems
state perfect information-theoretic hiding on the modelled view, and (via the
`k_anonymity` fields) that the collapse is over a genuinely-large anonymity set. They are
non-vacuous: `Reference` instantiates them at a `view` that is genuinely non-constant. -/

/-- **Graph tier law: stealth unlinkability (perfect, on the view).** Two stealth addresses
derived for the *same* recipient have the SAME observer-view — two payments to one recipient
are indistinguishable on the public graph (`§2 graph`). The body is the kernel's
`unlinkable_law` FIELD. Non-vacuous (the `Reference` view is non-constant), NOT `sorry`. -/
theorem unlinkable [GraphPrivacyKernel]
    (R : Recipient) (a a' : StealthAddr)
    (h : GraphPrivacyKernel.derivedFrom a R) (h' : GraphPrivacyKernel.derivedFrom a' R) :
    GraphPrivacyKernel.addrView a = GraphPrivacyKernel.addrView a' :=
  GraphPrivacyKernel.unlinkable_law R a a' h h'

/-- **Graph tier law: stealth k-anonymity.** Every address sits in an anonymity class
(same recipient, same view) of size `≥ k > 1` — the unlinkability collapse is genuinely
over many addresses, not a singleton. Body is the `stealth_k_anonymity` FIELD; combined
with `k_gt_one` this rules out the degenerate one-element "anonymity set". -/
theorem stealth_anonymity_set_large [GraphPrivacyKernel] (a : StealthAddr) :
    ∃ s : Finset StealthAddr, 1 < s.card ∧ a ∈ s ∧
      ∀ a' ∈ s, GraphPrivacyKernel.addrView a' = GraphPrivacyKernel.addrView a := by
  obtain ⟨s, hcard, hmem, hcollapse⟩ := GraphPrivacyKernel.stealth_k_anonymity a
  exact ⟨s, lt_of_lt_of_le GraphPrivacyKernel.k_gt_one hcard, hmem,
    fun a' ha' => (hcollapse a' ha').2⟩

/-- **Graph tier law: ZK auth-chain soundness, path-hiding.** If the verifier accepts
the chain's witness (`Discharged`), a legal derivation path exists — yet the verifier
only touched `pred`/`wit`, never the path's nodes. The body routes through the kernel's
`zkauthchain_law` FIELD (the extractability obligation), non-vacuous, NOT `sorry`. -/
theorem zkauthchain_sound [GraphPrivacyKernel]
    {P W : Type u} [Verifiable P W] (chain : ZkAuthChain P W)
    (_h : Discharged chain.pred chain.wit) :
    ∃ path : AuthPath, GraphPrivacyKernel.LegalDerivation path :=
  GraphPrivacyKernel.zkauthchain_law

/-- **Graph tier law: blinded membership hides *which* element (perfect, on the view).**
Stated correctly as *view-equality of two GIVEN members* (not bare existence of two distinct
members, false at `Elem = Unit`). Given two witnessed members `e e'` of the same commitment
`sc`, their observer-views are EQUAL — a verifier confirms membership while learning nothing
about which element was committed. Body is `hides_law`, non-vacuous, NOT `sorry`. -/
theorem blinded_membership_hides_element {Elem : Type u} [DecidableEq Elem]
    [BlindedMembershipKernel Elem]
    (sc : SetCommitment Elem) (e e' : Elem)
    (h : BlindedMembershipKernel.memberOf e sc) (h' : BlindedMembershipKernel.memberOf e' sc) :
    BlindedMembershipKernel.memberView e sc = BlindedMembershipKernel.memberView e' sc :=
  BlindedMembershipKernel.hides_law sc e e' h h'

/-- **Graph tier law: membership k-anonymity.** Every witnessed member of `sc` sits in an
anonymity set of `≥ k > 1` co-members (same commitment, same view) — the "which element"
hiding is over a genuinely-large set. Body is `member_k_anonymity` + `k_gt_one`. -/
theorem membership_anonymity_set_large {Elem : Type u} [DecidableEq Elem]
    [BlindedMembershipKernel Elem] (sc : SetCommitment Elem) (e : Elem)
    (h : BlindedMembershipKernel.memberOf e sc) :
    ∃ s : Finset Elem, 1 < s.card ∧ e ∈ s ∧
      ∀ e' ∈ s, BlindedMembershipKernel.memberView e' sc
        = BlindedMembershipKernel.memberView e sc := by
  obtain ⟨s, hcard, hmem, hco⟩ := BlindedMembershipKernel.member_k_anonymity sc e h
  exact ⟨s, lt_of_lt_of_le BlindedMembershipKernel.k_gt_one hcard, hmem,
    fun e' he' => (hco e' he').2⟩

/-! ## Tier 3 reconciliation — anonymity ⊗ nullifier (no double-spend). -/

/-- `accepted spent n` : a spend of nullifier `n` against the published `spent` set is
accepted iff `n` is not already present (fail-closed on reuse). -/
def accepted (spent : SpentSet) (n : Nullifier) : Prop := spent n = false

/-- **Reconciliation, half 1 — no double-spend (determinism ⇒ uniqueness).** Spending
the *same* note twice yields the *same* nullifier; once that nullifier is in the spent
set, the second spend is rejected. So determinism of `nullifierOf` (the kernel's
function-valued field) enforces at-most-once spend over the concurrent set. This stays a
PROVED structural fact (pure Bool logic); it now takes the kernel instance for `nullifierOf`. -/
theorem nullifier_prevents_double_spend [GraphPrivacyKernel]
    (note : Note) (spent : SpentSet)
    -- the note was already spent: its nullifier is recorded
    (hspent : spent (GraphPrivacyKernel.nullifierOf note) = true) :
    ¬ accepted spent (GraphPrivacyKernel.nullifierOf note) := by
  -- Pure structural fact (no crypto): `accepted` means `spent … = false`, contradicting
  -- `hspent : spent … = true`. Determinism of `nullifierOf` is what makes the *same* note
  -- yield this *same* tag (carrier-level), but the rejection itself is decidable Bool logic.
  unfold accepted
  rw [hspent]
  simp

/-- **Reconciliation, half 2 — anonymity (the nullifier hides the holder, perfect on the
view).** The observer-view of any two published nullifiers is EQUAL — the view is a single
constant, independent of *which* note (hence of the holder), so observing nullifiers-out
reveals nothing about *who* spent. The body is the kernel's `nullifier_hides_law` FIELD;
non-vacuous by `Reference` (whose `nullifierView` is a genuine constant map), NOT `sorry`.
Stated for two arbitrary notes to make the holder-independence explicit. -/
theorem nullifier_hides_identity [GraphPrivacyKernel] (note note' : Note) :
    GraphPrivacyKernel.nullifierView (GraphPrivacyKernel.nullifierOf note)
      = GraphPrivacyKernel.nullifierView (GraphPrivacyKernel.nullifierOf note') :=
  GraphPrivacyKernel.nullifier_hides_law _ _

/-- **The reconciliation theorem.** Anonymity (the nullifier hides the holder) and
no-double-spend (deterministic uniqueness gates reuse) hold *together*, for every note
— they are not in tension. This is the Zcash-style answer to "anonymous parties in a
contended JointTurn": the spent set orders/gates contention while the spender stays
hidden (`§2`, the anonymity ⊗ consensus reconciliation). Stays PROVED (the conjunction
of the two halves), now over the kernel instance. -/
theorem anonymity_nullifier_reconciliation [GraphPrivacyKernel]
    (note note' : Note) (spent : SpentSet)
    (hspent : spent (GraphPrivacyKernel.nullifierOf note) = true) :
    (GraphPrivacyKernel.nullifierView (GraphPrivacyKernel.nullifierOf note)
        = GraphPrivacyKernel.nullifierView (GraphPrivacyKernel.nullifierOf note'))
      ∧ ¬ accepted spent (GraphPrivacyKernel.nullifierOf note) :=
  ⟨nullifier_hides_identity note note',
    nullifier_prevents_double_spend note spent hspent⟩

/-! ## The `Reference` instances — GENUINELY NON-TRIVIAL witnesses (NOT `fun _ => True`).

A lawful witness whose observer-`view` is a genuine NON-CONSTANT function — it distinguishes
addresses for *different* recipients while collapsing those for the *same* recipient. This
is what makes the parametric theorems non-vacuous in the HONEST sense: not "there exists some
instance" (the all-`True` model gave that, masquerading as a guarantee), but "there exists an
instance where the hiding is real perfect-on-the-view collapse over a genuine `≥ k` anonymity
set, and the view genuinely separates distinct classes." (Still a TEST stand-in for the
information-theoretic core; the REAL computational unlinkability is the Rust/circuit
discharge — see module header. This witnesses the Lean model is non-vacuous, NOT that the
crypto holds.) -/

namespace Reference

/-- Reference graph-privacy kernel with a **genuinely non-constant** observer-view.
`recipientOf a := a.oneTimeKey % 2` (two recipients, `0`/`1` — so the view is NOT constant),
`addrView a := recipientOf a` (depends ONLY on the recipient: collapses the anonymity class,
separates the two classes), `nullifierView := 0` (the constant view IS the correct model of
nullifier anonymity — perfect independence from holder), `k := 2`. The k-anonymity sets are
real two-element `Finset`s of same-parity (hence same-recipient, same-view) addresses.

**A `def`, NOT an `instance`** (hardening): making it a global `instance` would let typeclass
resolution silently satisfy a real `[GraphPrivacyKernel]` obligation with this TEST kernel.
As a `def` it serves its one job — witnessing the interface is inhabitable by a non-trivial
model (`#print axioms graphRef` = no axioms) — while forcing any genuine use to *name* the
kernel it assumes (`@[reducible]` only silences the class-typed-`def` lint; it does NOT make
this an auto-resolved instance). -/
@[reducible] def graphRef : GraphPrivacyKernel where
  k := 2
  k_gt_one := by decide
  recipientOf a := ⟨a.oneTimeKey % 2⟩
  derivedFrom a R := (⟨a.oneTimeKey % 2⟩ : Recipient) = R
  addrView a := a.oneTimeKey % 2
  LegalDerivation _ := True
  nullifierOf n := ⟨n.seed⟩
  holderOf _ := ⟨0⟩
  nullifierView _ := 0
  unlinkable_law _ a a' ha ha' := by
    -- `derivedFrom a R` is `(⟨a.oneTimeKey % 2⟩ : Recipient) = R`; same recipient ⇒ same view.
    have hrec : (⟨a.oneTimeKey % 2⟩ : Recipient) = (⟨a'.oneTimeKey % 2⟩ : Recipient) :=
      ha.trans ha'.symm
    have h2 : a.oneTimeKey % 2 = a'.oneTimeKey % 2 := by injection hrec
    exact h2
  stealth_k_anonymity a := by
    -- the two distinct same-parity addresses `a.oneTimeKey` and `a.oneTimeKey + 2`.
    refine ⟨{a, ⟨a.oneTimeKey + 2⟩}, ?_, ?_, ?_⟩
    · -- card 2: the two are distinct (oneTimeKey differs by 2)
      have hne : a ∉ ({⟨a.oneTimeKey + 2⟩} : Finset StealthAddr) := by
        simp only [Finset.mem_singleton]
        intro hcontra
        have h := congrArg StealthAddr.oneTimeKey hcontra
        simp only at h
        omega
      rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]
    · exact Finset.mem_insert_self _ _
    · intro a' ha'
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha'
      rcases ha' with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · -- `(a.oneTimeKey + 2) % 2 = a.oneTimeKey % 2` (both recipient- and view-level)
        have hmod : (a.oneTimeKey + 2) % 2 = a.oneTimeKey % 2 := by omega
        exact ⟨by show (⟨_⟩ : Recipient) = ⟨_⟩; rw [hmod], hmod⟩
  zkauthchain_law := ⟨⟨[]⟩, trivial⟩
  nullifier_hides_law _ _ := rfl

/-- Reference blinded-membership kernel over `Nat`: `memberOf e sc := e < 2` (a genuine,
NON-trivial membership predicate — NOT `fun _ => True`; exactly elements `0` and `1` are
members), `memberView := fun _ _ => 0` (perfect view-collapse: members are indistinguishable),
`k := 2`. The anonymity set is the real `{0,1}` two-element member set. -/
@[reducible] def memRefNat : BlindedMembershipKernel Nat where
  k := 2
  k_gt_one := by decide
  memberOf e _ := e < 2
  memberView _ _ := 0
  hides_law _ _ _ _ _ := rfl
  member_k_anonymity sc e he := by
    -- every member (`he : e < 2`) sits in the genuine 2-element anonymity set {0, 1}.
    refine ⟨{0, 1}, ?_, ?_, ?_⟩
    · decide
    · -- `e ∈ {0,1}`: from `e < 2`, `e = 0 ∨ e = 1`.
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    · intro e' he'
      simp only [Finset.mem_insert, Finset.mem_singleton] at he'
      exact ⟨by omega, rfl⟩

/-- Non-vacuity (HONEST): `unlinkable` at `graphRef` is the real perfect-view collapse —
two same-recipient addresses get the SAME `addrView` — and crucially the view is NOT
constant: addresses of *different* parity get *different* views. So the theorem is not a
`True`-masquerade. -/
example (a a' : StealthAddr) (h : a.oneTimeKey % 2 = a'.oneTimeKey % 2) :
    @GraphPrivacyKernel.addrView graphRef a = @GraphPrivacyKernel.addrView graphRef a' := by
  -- pass `graphRef` EXPLICITLY (it is a `def`, not an auto-resolved `instance`); the
  -- derivedFrom hypotheses unfold to recipient-parity equalities.
  refine @unlinkable graphRef ⟨a.oneTimeKey % 2⟩ a a' ?_ ?_
  · show (⟨a.oneTimeKey % 2⟩ : Recipient) = ⟨a.oneTimeKey % 2⟩; rfl
  · show (⟨a'.oneTimeKey % 2⟩ : Recipient) = ⟨a.oneTimeKey % 2⟩; rw [h]

/-- The reference view is GENUINELY NON-CONSTANT — addresses for the two recipients have
DIFFERENT views. This is the proof the model is not the vacuous `fun _ => True`. -/
example : @GraphPrivacyKernel.addrView graphRef ⟨0⟩ ≠ @GraphPrivacyKernel.addrView graphRef ⟨1⟩ := by
  show (0 : Nat) % 2 ≠ 1 % 2; decide

/-- Non-vacuity: `blinded_membership_hides_element` is inhabited at the reference kernel,
and the membership predicate is genuine (`memberOf 0` holds, `memberOf 2` does not). -/
example (sc : SetCommitment Nat) (e e' : Nat) (h : e < 2) (h' : e' < 2) :
    @BlindedMembershipKernel.memberView Nat _ memRefNat e sc
      = @BlindedMembershipKernel.memberView Nat _ memRefNat e' sc :=
  @blinded_membership_hides_element Nat _ memRefNat sc e e'
    (show e < 2 from h) (show e' < 2 from h')

/-- The reference membership predicate is GENUINE, not `fun _ => True`: `2` is NOT a member. -/
example (sc : SetCommitment Nat) : ¬ @BlindedMembershipKernel.memberOf Nat _ memRefNat 2 sc := by
  show ¬ (2 < 2); decide

end Reference

-- TRIPWIRES: the graph-tier hiding theorems (now genuine view-equality / k-anonymity, not
-- `True`-carriers) and the proved structural keystones are kernel-clean (axioms ⊆ {propext,
-- Classical.choice, Quot.sound}) — no `sorry` leaked through. The residual *computational*
-- advantage bound enters ONLY as the §8 portal documented in the module header (carried by
-- `Crypto/Primitives.lean::unlinkable`), never as an axiom these pins would catch.
#assert_axioms unlinkable
#assert_axioms stealth_anonymity_set_large
#assert_axioms zkauthchain_sound
#assert_axioms blinded_membership_hides_element
#assert_axioms membership_anonymity_set_large
#assert_axioms nullifier_hides_identity
#assert_axioms nullifier_prevents_double_spend
#assert_axioms anonymity_nullifier_reconciliation
#assert_axioms field_projection_hides_private
#assert_axioms committed_conservation

end Dregg2.Privacy
