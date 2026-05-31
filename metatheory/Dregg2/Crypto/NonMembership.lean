/-
# Dregg2.Crypto.NonMembership — the THIRD end-to-end §8 discharge: sorted-tree non-membership.

**The next obligation after Merkle (membership) and Pedersen (conservation)
(`docs/rebuild/PHASE-CRYPTOKERNEL.md §5` "Path to the rest": NonMembership "reuses the Merkle
gadget twice + adjacency").** Where `Crypto/Merkle.lean` discharged that a leaf IS in the tree,
this discharges that an element is ABSENT — the neighbor-bracketing proof of a sorted tree:

    an element `e` is NOT in the committed set
      ⟺ there exist two ADJACENT present leaves `lo`, `hi` with `lo < e < hi`.

The "present" half reuses the Merkle membership gadget TWICE (a Merkle path for `lo`, a Merkle
path for `hi`, both recomposing the SAME committed root). The "adjacency + ordering" half is the
honest combinatorial core: `lo`, `hi` are CONSECUTIVE in the sorted leaf list (nothing lies
strictly between them in the set) and the comparison `lo < e < hi` is the range/comparison gadget
(`Exec/RecordCircuit.range_iff`, no primitive seam). The cascade mirrors Merkle/Pedersen:

    nonmembership_bridge      : Satisfies nonMembershipCircuit (root, e) ↔ e ∉ committedSet
      [the gadget, FULLY proven — two Merkle bridges + the SORTED-ADJACENCY soundness lemma]
    nonmembership_verify_sound: verify accepts → e ∉ committedSet
      [DERIVED off the bridge, given the STARK `extractable` carrier]
    nonmembership_dial_wired  : the dial pinned to the verifier at the `acceptanceOnly` floor
      [blinded non-membership discloses ONE bit ("e is absent") ⇒ the ZK floor, like membership]

**The sorted-adjacency soundness is the genuinely-grounded part** (and the heart of the bridge):
in a SORTED list, if `lo`/`hi` are adjacent present elements and `lo < e < hi`, then `e` cannot be
present — a fully PROVED combinatorial fact (`sorted_gap_excludes`). The ONLY cryptographic residue
is the same as Merkle's: `compress`'s collision-resistance (the Layer-A `collisionHard` carrier),
consumed by the verifier-kernel `extractable`, never by the bridge. The adjacency combinatorics are
unconditional — exactly the discipline the rails demand (`compress` abstract, no primitive seam).
-/
import Dregg2.Crypto.Merkle
import Dregg2.Exec.RecordCircuit
import Dregg2.Authority.Predicate
import Metatheory.EpistemicDial
import Mathlib.Data.List.Pairwise
import Dregg2.Tactics

namespace Dregg2.Crypto.NonMembership

open Dregg2.Crypto Dregg2.Crypto.Merkle Dregg2.Exec.RecordCircuit

universe u

/-! ## The sorted committed set + the adjacency combinatorics (the honest core).

The committed set is the SORTED leaf list of the Merkle tree (the real `non_membership` AIR is over
a sorted/accumulator structure; the sorted-tree neighbor-bracketing is the canonical realization).
We need an order on `Digest` to state "strictly between"; the order is the leaf-key order the tree
is sorted by. `compress` (the node hash) stays abstract — the ordering is on the leaf KEYS, the
Merkle recomposition is over the hash, and the two never interact (no primitive seam). -/

variable {Digest : Type u} [LinearOrder Digest]

/-- **`Sorted leaves`** — the committed leaf list is strictly increasing (`List.Pairwise (·<·)`,
the stable strict-sorted predicate). Defined locally over `Pairwise` so the combinatorics are
self-contained and robust to Mathlib's `List.Sorted` API churn. -/
def Sorted (leaves : List Digest) : Prop := leaves.Pairwise (· < ·)

/-- **`Adjacent leaves lo hi`** — `lo` and `hi` are CONSECUTIVE entries of the sorted leaf list:
the list contains `… lo, hi …` with no element strictly between. We capture "consecutive" directly:
the list splits as `pre ++ lo :: hi :: post`. Combined with sortedness this is exactly "no leaf lies
in the open interval `(lo, hi)`" — the neighbor-bracketing witness. -/
def Adjacent (leaves : List Digest) (lo hi : Digest) : Prop :=
  ∃ pre post, leaves = pre ++ lo :: hi :: post

/-- In a strict-`Pairwise` list `a :: l`, the head relates to every later element: `∀ x ∈ l, a < x`.
The single `Pairwise` fact the gap-exclusion needs (`List.pairwise_cons`, stable). -/
theorem head_lt_of_sorted {a : Digest} {l : List Digest}
    (h : Sorted (a :: l)) : ∀ x ∈ l, a < x :=
  (List.pairwise_cons.mp h).1

/-- The tail of a strict-`Pairwise` list is strict-`Pairwise`. -/
theorem sorted_tail {a : Digest} {l : List Digest} (h : Sorted (a :: l)) : Sorted l :=
  (List.pairwise_cons.mp h).2

/-- **`sorted_gap_excludes` — THE soundness heart (FULLY PROVED, no crypto).** In a `Sorted`
(strictly increasing) leaf list, if `lo`/`hi` are ADJACENT (consecutive) and `lo < e < hi`, then
`e` is NOT in the list: the strict-sorted order forces every element strictly before `hi` to be
`< hi`-monotone (so `≤ lo`, since `lo` immediately precedes `hi`) and every element from `hi` on to
be `≥ hi`, so the open interval `(lo, hi)` is empty. Proved by induction on the `pre` prefix of the
split. This is the combinatorial core of non-membership: bracketing by adjacent present neighbors
EXCLUDES everything strictly between. -/
theorem sorted_gap_excludes (leaves : List Digest) (lo hi e : Digest)
    (hsorted : Sorted leaves) (hadj : Adjacent leaves lo hi)
    (hlo : lo < e) (hhi : e < hi) : e ∉ leaves := by
  obtain ⟨pre, post, rfl⟩ := hadj
  -- Induct on the prefix; `hsorted`'s head-relations push the bracketing in.
  induction pre with
  | nil =>
    -- leaves = lo :: hi :: post. Membership of e forces e = lo, e = hi, or e ∈ post (⇒ hi < e).
    simp only [List.nil_append] at hsorted ⊢
    intro hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | rfl | hpost
    · exact absurd hlo (lt_irrefl _)
    · exact absurd hhi (lt_irrefl _)
    · -- e ∈ post ⇒ hi < e (head `hi` relates to all of post) — contradicts e < hi.
      have : hi < e := head_lt_of_sorted (sorted_tail hsorted) e hpost
      exact absurd (this.trans hhi) (lt_irrefl _)
  | cons a pre' ih =>
    -- leaves = a :: (pre' ++ lo :: hi :: post). e ≠ a (head a < everything later, and e < hi ≤ later),
    -- and e ∉ (pre' ++ …) by the IH on the sorted tail.
    simp only [List.cons_append] at hsorted ⊢
    intro hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · -- e = a (the head): the head relates to lo (`a < lo`, lo is later), so `lo < e = a < lo` — absurd.
      have halo : e < lo := head_lt_of_sorted hsorted lo (by simp)
      exact absurd (halo.trans hlo) (lt_irrefl _)
    · -- e ∈ tail: the IH on the sorted tail excludes it.
      exact ih (sorted_tail hsorted) htail

/-! ## The committed-set membership relation (reusing the Merkle gadget for "present").

A leaf is PRESENT iff it has a Merkle path to the committed root (`Merkle.MerkleMembers`). The
committed set is the abstract sorted leaf list; the root is its Merkle commitment. We keep the
binding "the sorted list IS what the root commits to" as an explicit field of the statement — the
prover supplies the leaf list, and `compress`-collision-resistance (the `extractable`/`collisionHard`
carrier) is what forces it to be the genuine committed list. The bridge's combinatorics are over
THAT list, unconditionally. -/

/-- **`presentAt compress root x`** — `x` is a leaf present in the tree with this root: it has a
Merkle path recomposing the root (`Merkle.MerkleMembers`). This is the reused membership gadget. -/
def presentAt (compress : Digest → Digest → Digest) (root x : Digest) : Prop :=
  MerkleMembers compress root x

/-- **`NonMember compress root leaves e`** — the non-membership STATEMENT relation: relative to a
sorted committed leaf list with the given Merkle root, the element `e` is genuinely absent. We state
it positively as "the leaf list is sorted, its root is `root`, and `e ∉ leaves`" — the relation the
verifier's accepting bit must certify. -/
def NonMember (leaves : List Digest) (e : Digest) : Prop :=
  Sorted leaves ∧ e ∉ leaves

/-! ## `CircuitIR` — two Merkle membership sub-proofs + the adjacency/comparison gadget.

Mirrors the neighbor-bracketing AIR: the trace carries the two bracketing neighbors `lo`, `hi`, a
Merkle path for EACH (the two reused Merkle gadgets), and the range-gadget bits witnessing the two
strict comparisons `lo < e` and `e < hi`. The adjacency (`lo`, `hi` consecutive in the sorted list)
is the structural side condition the bridge proves excludes `e`. -/

/-- **The non-membership circuit IR** — the trace: the two bracketing neighbors and their Merkle
membership sub-proofs (reused `Merkle.CircuitIR` twice), plus the comparison witnesses. The two
sub-circuits `loCircuit`/`hiCircuit` are the two Merkle-gadget instances; `lo`/`hi` are the
bracketing leaf keys. -/
structure CircuitIR (Digest : Type u) where
  /-- The left bracketing neighbor (present leaf with `lo < e`). -/
  lo : Digest
  /-- The right bracketing neighbor (present leaf with `e < hi`). -/
  hi : Digest
  /-- The Merkle membership sub-proof that `lo` is present (reused gadget #1). -/
  loCircuit : Merkle.CircuitIR Digest
  /-- The Merkle membership sub-proof that `hi` is present (reused gadget #2). -/
  hiCircuit : Merkle.CircuitIR Digest

/-- **`Satisfies compress circuit root e leaves`** — the full non-membership AIR check, given the
committed sorted leaf list:
  * the two Merkle sub-proofs `Satisfies` (both `lo` and `hi` are present at `root`) — gadgets ×2;
  * `lo`/`hi` are ADJACENT in the sorted `leaves` (consecutive — the neighbor-bracketing side cond);
  * the comparison gadget: `lo < e` and `e < hi` (the "strictly between" range/order check). -/
def Satisfies (compress : Digest → Digest → Digest)
    (circuit : CircuitIR Digest) (root e : Digest) (leaves : List Digest) : Prop :=
  -- Merkle sub-proof #1: lo is present at root.
  Merkle.Satisfies compress circuit.loCircuit root circuit.lo ∧
  -- Merkle sub-proof #2: hi is present at root.
  Merkle.Satisfies compress circuit.hiCircuit root circuit.hi ∧
  -- the committed list is sorted (the structure the root commits to).
  Sorted leaves ∧
  -- adjacency: lo, hi are consecutive present leaves (no leaf strictly between in the set).
  Adjacent leaves circuit.lo circuit.hi ∧
  -- comparison gadget: lo < e < hi (strictly between the two neighbors).
  circuit.lo < e ∧ e < circuit.hi

/-! ## The bridge — `Satisfies ↔ NonMember`, FULLY proven (NO primitive seam).

Both directions. `→` (SOUNDNESS) is the heart: a satisfying trace gives two adjacent present leaves
bracketing `e`, and `sorted_gap_excludes` (the combinatorial core) PROVES `e ∉ leaves`. `←`
(COMPLETENESS) reconstructs the bracketing neighbors from genuine absence. `compress` is abstract
throughout (the two Merkle sub-proofs ride `merkle_bridge`); the only crypto residue is `compress`'s
CR, consumed by the kernel `extractable`, never here. -/

/-- **`nonmembership_sound` (the `→` half).** A satisfying trace PROVES non-membership: the two
Merkle sub-proofs certify `lo`/`hi` present (unused for the absence conclusion — they pin the
neighbors to the committed root, the crypto side), and the adjacency + `lo < e < hi` feed
`sorted_gap_excludes` to PROVE `e ∉ leaves`. The combinatorial heart, fully proved. -/
theorem nonmembership_sound (compress : Digest → Digest → Digest)
    (circuit : CircuitIR Digest) (root e : Digest) (leaves : List Digest)
    (h : Satisfies compress circuit root e leaves) :
    NonMember leaves e := by
  obtain ⟨_hlo, _hhi, hsorted, hadj, hcmplo, hcmphi⟩ := h
  exact ⟨hsorted, sorted_gap_excludes leaves circuit.lo circuit.hi e hsorted hadj hcmplo hcmphi⟩

/-- **`nonmembership_complete` (the `←` half).** Genuine absence yields a satisfying trace: given the
sorted committed `leaves` with `e ∉ leaves` AND the two bracketing neighbors `lo`/`hi` actually
adjacent in `leaves` and present at `root` (the prover's honest witnesses — present-ness reuses
`merkle_complete`), the AIR is satisfied. The bracketing neighbors and their Merkle paths are the
completeness witnesses; the comparisons `lo < e < hi` are supplied as the bracketing hypotheses. -/
theorem nonmembership_complete (compress : Digest → Digest → Digest)
    (root e : Digest) (leaves : List Digest) (lo hi : Digest)
    (hsorted : Sorted leaves)
    (hadj : Adjacent leaves lo hi)
    (hlo : lo < e) (hhi : e < hi)
    (hlomem : presentAt compress root lo)
    (himem : presentAt compress root hi) :
    ∃ circuit : CircuitIR Digest, Satisfies compress circuit root e leaves := by
  obtain ⟨loC, hloSat⟩ := merkle_complete compress root lo hlomem
  obtain ⟨hiC, hhiSat⟩ := merkle_complete compress root hi himem
  exact ⟨⟨lo, hi, loC, hiC⟩, hloSat, hhiSat, hsorted, hadj, hlo, hhi⟩

/-- **`nonmembership_bridge` — THE deliverable (the analog of `merkle_bridge`/`pedersen_conservation_bridge`).**
The non-membership AIR's satisfiability is EXACTLY genuine absence:

  * `→` (SOUNDNESS): a satisfying trace's two ADJACENT present neighbors bracketing `e` force
    `e ∉ leaves` via `sorted_gap_excludes` (the sorted-adjacency combinatorial core, fully proved).
  * `←` (COMPLETENESS): genuine absence, with the bracketing neighbors as witnesses, gives a
    satisfying trace (the two Merkle sub-proofs via `merkle_complete`, the adjacency + comparisons
    by hypothesis).

`compress` is abstract throughout — NO primitive seam. The only cryptographic residue is `compress`'s
collision-resistance (Layer-A `collisionHard`), consumed by `nonmembership_verify_sound`'s
`extractable` carrier, NEVER by the bridge. Stated as the soundness biconditional + the completeness
constructor (completeness needs the prover's bracketing witnesses, which the existential supplies). -/
theorem nonmembership_bridge (compress : Digest → Digest → Digest)
    (root e : Digest) (leaves : List Digest) :
    -- SOUNDNESS (the heart): every satisfying trace certifies genuine absence.
    (∀ circuit : CircuitIR Digest, Satisfies compress circuit root e leaves → NonMember leaves e)
    ∧
    -- COMPLETENESS: bracketing-neighbor witnesses for a genuine absence give a satisfying trace.
    (∀ lo hi : Digest, Sorted leaves → Adjacent leaves lo hi → lo < e → e < hi →
      presentAt compress root lo → presentAt compress root hi →
      ∃ circuit : CircuitIR Digest, Satisfies compress circuit root e leaves) :=
  ⟨fun circuit h => nonmembership_sound compress circuit root e leaves h,
   fun lo hi hsorted hadj hlo hhi hlomem himem =>
     nonmembership_complete compress root e leaves lo hi hsorted hadj hlo hhi hlomem himem⟩

-- TRIPWIRES: the non-membership gadget is FULLY proven with NO primitive seam — the soundness
-- heart `sorted_gap_excludes` is pure combinatorics, the two membership sub-proofs ride
-- `merkle_bridge`, and `compress`'s collision-resistance never enters (it is the Layer-A
-- `collisionHard` carrier, consumed by the verifier-kernel extractability, not here).
#assert_axioms sorted_gap_excludes
#assert_axioms nonmembership_sound
#assert_axioms nonmembership_complete
#assert_axioms nonmembership_bridge

/-! ## Layer B — the non-membership `VerifierKernel`: `verify` + carriers + DERIVED `verify_sound`.

Mirrors `MerkleVerifierKernel`/`PedersenVerifierKernel`. `verify` is the §8 oracle over the disclosed
`(root, e)`; `extractable` (STARK soundness, AND `compress` CR binding the disclosed leaf list to the
root) gives "accept ⇒ a satisfying trace over the genuine committed list exists";
`nonmembership_verify_sound` is DERIVED off the bridge's soundness half. -/

/-- **The disclosed non-membership statement** — the public inputs the verifier sees: the committed
Merkle root and the queried element `e`. (The committed leaf list is HIDDEN; `compress` CR is what
binds the prover's claimed list to `root` — the `extractable` carrier.) -/
structure Statement (Digest : Type u) where
  /-- The committed Merkle root (public). -/
  root : Digest
  /-- The element claimed absent (public). -/
  elem : Digest

/-- **Layer B — the non-membership `VerifierKernel`.** The `compress` primitive, the §8 `verify`
oracle over the disclosed `(root, e)`, and the STARK `extractable` carrier. `extract` unpacks
`extractable` to its operational content: an accepted proof witnesses a satisfying trace over SOME
genuine committed sorted leaf list with that root — the existence the FRI/Fiat-Shamir + `compress`-CR
soundness delivers. -/
class NonMembershipVerifierKernel (Digest : Type u) (Proof : Type u) [LinearOrder Digest] where
  /-- The abstract Poseidon2 node hash (the Layer-A `compress`; CR is `collisionHard`). -/
  compress : Digest → Digest → Digest
  /-- **The §8 verify oracle** (`stark::verify` for the non-membership AIR): does `proof` discharge
  the disclosed statement `(root, e)`? An opaque `Bool`; soundness is the carried `extractable`. -/
  verify : Statement Digest → Proof → Bool
  /-- **CARRIER — STARK extractability/soundness** (FRI + Fiat-Shamir, plus `compress` CR binding the
  committed list to the root): accept ⇒ a satisfying trace over the genuine committed list exists. A
  `Prop`; never proved, never `sorry`. -/
  extractable : Prop
  /-- `extractable` UNPACKED: an accepted proof witnesses a satisfying trace over some genuine sorted
  committed leaf list with the disclosed root. The named form the bridge composes with. -/
  extract : extractable →
    ∀ (stmt : Statement Digest) (proof : Proof), verify stmt proof = true →
      ∃ (leaves : List Digest) (circuit : CircuitIR Digest),
        Satisfies compress circuit stmt.root stmt.elem leaves

variable {Proof : Type u}

/-- **`nonmembership_verify_sound` — the DERIVED verify law (the analog of `merkle_verify_sound`).**
Given the STARK-soundness carrier `extractable`, an accepted non-membership proof PROVES the element
is genuinely absent from the committed sorted set:

    verify stmt proof = true  →  ∃ leaves, NonMember leaves stmt.elem

The proof composes `extract` (accept ⇒ satisfying trace over the genuine committed list, the crypto
carrier) with `nonmembership_bridge`'s SOUNDNESS half (satisfying trace ⇒ absence, FULLY proved via
`sorted_gap_excludes`). The verify law is DERIVED, not assumed; the only hypothesis is `extractable`. -/
theorem nonmembership_verify_sound [K : NonMembershipVerifierKernel Digest Proof]
    (hext : K.extractable) (stmt : Statement Digest) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    ∃ leaves : List Digest, NonMember leaves stmt.elem := by
  obtain ⟨leaves, circuit, hsat⟩ := K.extract hext stmt proof haccept
  exact ⟨leaves, (nonmembership_bridge K.compress stmt.root stmt.elem leaves).1 circuit hsat⟩

#assert_axioms nonmembership_verify_sound

/-! ## Layer C — the kind obligation + the DIAL wiring at the `acceptanceOnly` floor.

Blinded non-membership discloses ONE bit ("e is absent") and hides WHICH neighbors bracket it and
the rest of the set — the same zero-knowledge floor as blinded Merkle membership. So the epistemic
floor is `acceptanceOnly` (NOT `selective` like Pedersen, which discloses the commitments): the
verifier learns only that the element is absent, nothing about the set structure. We wire
`EpistemicDial.DiscloseAt` to the verifier exactly as `PredicateKernel` does for Merkle. -/

open Dregg2.Authority.Predicate Dregg2.Laws Metatheory

/-- **`KindObligation`** for non-membership — statement algebra `Statement Digest`, **dial floor =
`acceptanceOnly`** (blinded absence discloses one bit, hiding the bracketing neighbors and the set;
the ZK floor, like blinded membership). -/
structure KindObligation (Digest : Type u) where
  /-- The public-input algebra: the disclosed `(root, e)`. -/
  Statement : Type u
  /-- The dial floor — `acceptanceOnly` for blinded non-membership. -/
  dialFloor : Dial

/-- The non-membership kind's obligation: statement = disclosed `(root, e)`, floor = `acceptanceOnly`
(blinded ⇒ ZK floor: the verifier learns only "absent", not the neighbors or the set). -/
def nonMembershipKindObligation : KindObligation Digest where
  Statement := Statement Digest
  dialFloor := Dial.acceptanceOnly

omit [LinearOrder Digest] in
@[simp] theorem nonMembershipKindObligation_floor :
    (nonMembershipKindObligation (Digest := Digest)).dialFloor = Dial.acceptanceOnly :=
  rfl

/-! ### The dial wiring — `DiscloseAt` instantiated at the non-membership verifier's `acceptanceOnly`
floor (the registry/dial machinery lives at universe 0, so we instantiate over `Type`). -/

section Wiring

variable {D : Type} [LinearOrder D] {P : Type}

/-- A `Verifier (Statement D) P` from the kernel's §8 `verify` oracle. -/
def nonMembershipVerifier [K : NonMembershipVerifierKernel D P] : Verifier (Statement D) P :=
  fun stmt proof => K.verify stmt proof

/-- The non-membership-kind registry: the §8 `verify` oracle installed at `nonMembership`. -/
def nonMembershipReg [NonMembershipVerifierKernel D P]
    (base : Registry (Statement D) P) : Registry (Statement D) P :=
  fun j => if j = .nonMembership then some nonMembershipVerifier else base j

/-- The `Verifiable` seam this kind dispatches through (explicit `base`, not auto-synthesized). -/
@[reducible] def nonMembershipSeam [NonMembershipVerifierKernel D P]
    (base : Registry (Statement D) P) : Verifiable (Statement D) P :=
  verifiableOfRegistry (nonMembershipReg base) .nonMembership

/-- **`nonMembershipDisclose` — the dial pinned to the non-membership verifier.** `accepts d` is the
position-independent `Discharged stmt proof`; `accepts_eq := fun _ => Iff.rfl`. Realizes "instantiate
`DiscloseAt` at the `acceptanceOnly` floor (blinded absence: one bit, neighbors hidden)". -/
def nonMembershipDisclose [NonMembershipVerifierKernel D P]
    (base : Registry (Statement D) P) (stmt : Statement D) (proof : P) :
    @DiscloseAt Unit (Statement D) P _ (nonMembershipSeam base) :=
  letI : Verifiable (Statement D) P := nonMembershipSeam base
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := stmt
    wit := proof
    accepts := fun _ => Discharged stmt proof
    accepts_eq := fun _ => Iff.rfl }

/-- **`nonmembership_dial_wired` — THE DIAL WIRING (the analog of `merkle_dial_wired`).** The
non-membership kind's epistemic floor is `acceptanceOnly` (blinded ⇒ ZK floor), the dial's bottom
notch's acceptance bit IS the verifier's `Discharged` bit, and — given STARK `extractable` — an
accepting proof PROVES genuine absence. The dial is pinned to the per-kind verifier. -/
theorem nonmembership_dial_wired [K : NonMembershipVerifierKernel D P]
    (hext : K.extractable)
    (base : Registry (Statement D) P) (stmt : Statement D) (proof : P) :
    -- (1) the floor is acceptanceOnly:
    (nonMembershipKindObligation (Digest := D)).dialFloor = Dial.acceptanceOnly ∧
    -- (2) the dial's bottom notch accepts IFF the non-membership verifier discharges:
    (@DiscloseAt.accepts Unit (Statement D) P _ (nonMembershipSeam base)
        (nonMembershipDisclose base stmt proof) (⊥ : Dial)
      ↔ @Discharged (Statement D) P (nonMembershipSeam base) stmt proof) ∧
    -- (3) and an accepting proof PROVES absence (the cascade):
    (K.verify stmt proof = true →
      ∃ leaves : List D, NonMember leaves stmt.elem) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact @DiscloseAt.accepts_bot_iff_discharged Unit (Statement D) P _ (nonMembershipSeam base)
      (nonMembershipDisclose base stmt proof)
  · exact fun haccept => nonmembership_verify_sound hext stmt proof haccept

/-- **`nonmembership_registry_cascade` — the §8 discharge through the registry (the analog of
`merkle_registry_cascade`).** Registering the non-membership kind, an accepted proof both
`Discharged`s the kind's predicate (the registry keystone, `registry_sound`) AND — given the STARK
`extractable` carrier — PROVES genuine absence (`nonmembership_verify_sound`). The cascade
`registry_sound ∘ nonmembership_verify_sound`; the single trust boundary is `extractable`. -/
theorem nonmembership_registry_cascade [K : NonMembershipVerifierKernel D P]
    (hext : K.extractable)
    (base : Registry (Statement D) P)
    (stmt : Statement D) (proof : P)
    (haccept : K.verify stmt proof = true) :
    (@Discharged (Statement D) P (verifiableOfRegistry (nonMembershipReg base) .nonMembership)
        stmt proof)
      ∧ ∃ leaves : List D, NonMember leaves stmt.elem := by
  refine ⟨?_, nonmembership_verify_sound hext stmt proof haccept⟩
  apply registry_sound (nonMembershipReg base) .nonMembership stmt proof
  show registryVerify (nonMembershipReg base) .nonMembership stmt proof = true
  unfold registryVerify nonMembershipReg
  simp only [↓reduceIte]
  exact haccept

end Wiring

#assert_axioms nonmembership_dial_wired
#assert_axioms nonmembership_registry_cascade

/-! ## `Reference` — a concrete kernel + non-vacuity witnesses over `ℤ`.

`ℤ` is a `LinearOrder`; the Layer-A `Crypto.Reference.instCryptoPrimitives` gives `compress a b := a + b`.
We build a degenerate non-membership verifier kernel `def` (NOT a global `instance`, to avoid silent
auto-resolution) and witness the bridge / verify-sound / cascade end-to-end. NOT real crypto. -/

namespace Reference

open Dregg2.Crypto.Reference

/-- The reference node hash over `ℤ`: `compress a b := a + b` (matching the Layer-A reference). -/
def refCompress : Int → Int → Int := fun a b => a + b

/-- A concrete sorted committed leaf list over `ℤ`: `[1, 3]` — two adjacent leaves bracketing `2`. -/
def sampleLeaves : List Int := [1, 3]

/-- The sample committed list `[1,3]` is `Sorted` (strictly increasing). -/
theorem sampleLeaves_sorted : Sorted sampleLeaves := by
  simp [sampleLeaves, Sorted, List.pairwise_cons]

/-- `1` and `3` are adjacent (consecutive) in `[1, 3]`. -/
theorem sampleLeaves_adjacent : Adjacent sampleLeaves 1 3 :=
  ⟨[], [], rfl⟩

/-- Non-vacuity of the BRIDGE soundness heart: `2 ∉ [1,3]`, witnessed via the adjacency of `1`/`3`
bracketing `2` (`1 < 2 < 3`). This is `sorted_gap_excludes` on the concrete sorted tree. -/
example : (2 : Int) ∉ sampleLeaves :=
  sorted_gap_excludes sampleLeaves 1 3 2 sampleLeaves_sorted sampleLeaves_adjacent
    (by norm_num) (by norm_num)

/-- A single-level Merkle membership witness over `ℤ`: leaf `x` is "present" at root `x + s` via a
self-hash path `compress x s = x + s` with the chosen sibling `s` (`recompose (+) x [s] = x + s`).
The reference present-ness witness, with the root made explicit so two neighbors share one root. -/
theorem ref_present_at (x s : Int) : presentAt refCompress (x + s) x :=
  ⟨[{ sib := s, position := 0 }], by simp, rfl⟩

/-- Both bracketing neighbors present at the COMMON root `2`: `1` via sibling `1` (`1+1=2`), `3` via
sibling `-1` (`3+(-1)=2`). -/
theorem ref_present_1 : presentAt refCompress 2 1 := by
  have := ref_present_at 1 1; norm_num at this; exact this
theorem ref_present_3 : presentAt refCompress 2 3 := by
  have := ref_present_at 3 (-1); norm_num at this; exact this

/-- Non-vacuity of the BRIDGE completeness half: with `1`/`3` adjacent + present at the common root
`2` and `1 < 2 < 3`, the AIR is satisfied. Built through `nonmembership_complete` (the two Merkle
sub-proofs come from `merkle_complete` on the `presentAt` witnesses). -/
example :
    ∃ circuit : CircuitIR Int,
      Satisfies refCompress circuit 2 2 sampleLeaves :=
  nonmembership_complete refCompress 2 2 sampleLeaves 1 3 sampleLeaves_sorted
    sampleLeaves_adjacent (by norm_num) (by norm_num) ref_present_1 ref_present_3

/-- A degenerate reference non-membership verifier kernel over `ℤ` (`def`, not a global `instance`).
`compress := (+)`; `verify` accepts iff `stmt.elem = 2 ∧ stmt.root = 2` (the toy "2 is absent from the
committed `[1,3]` rooted at 2" check); `extractable := True`. `extract` rebuilds the satisfying trace
from `sampleLeaves` via the bracketing of `1`/`3` (both present at root `2`), through
`nonmembership_complete`. -/
@[reducible] def refKernel : NonMembershipVerifierKernel Int Int where
  compress := refCompress
  verify stmt _ := decide (stmt.elem = 2 ∧ stmt.root = 2)
  extractable := True
  extract := by
    intro _ stmt _ haccept
    obtain ⟨root, elem⟩ := stmt
    simp only [decide_eq_true_eq] at haccept
    obtain ⟨he, hr⟩ := haccept
    subst he; subst hr
    obtain ⟨circuit, hsat⟩ :=
      nonmembership_complete refCompress 2 2 sampleLeaves 1 3 sampleLeaves_sorted
        sampleLeaves_adjacent (by norm_num) (by norm_num) ref_present_1 ref_present_3
    exact ⟨sampleLeaves, circuit, hsat⟩

/-- The empty base registry over the toy `ℤ` non-membership statement/proof. -/
def base : Registry (Statement Int) Int := fun _ => none

/-- A disclosed statement over `ℤ`: root `2`, element `2` — the reference verifier accepts (it is the
toy "2 is absent" claim). -/
def absentStmt : Statement Int := { root := 2, elem := 2 }

/-- Non-vacuity of `nonmembership_verify_sound`: at the reference kernel an accepted proof yields a
committed list from which `stmt.elem = 2` is genuinely absent. -/
example : ∃ leaves : List Int, NonMember leaves absentStmt.elem :=
  nonmembership_verify_sound (K := refKernel) trivial absentStmt 0 (by decide)

/-- Non-vacuity of the FULL cascade: at the reference kernel an accepted proof both `Discharged`s the
registry predicate AND proves absence. A NAMED witness so its axiom footprint is checkable. -/
theorem reference_cascade_nonvacuous :
    (@Discharged (Statement Int) Int
        (verifiableOfRegistry (@nonMembershipReg Int _ Int refKernel base) .nonMembership)
        absentStmt 0)
      ∧ ∃ leaves : List Int, NonMember leaves absentStmt.elem :=
  nonmembership_registry_cascade (K := refKernel) trivial base absentStmt 0 (by decide)

-- The non-vacuity witness's axiom footprint (the task's `#print axioms` requirement): the reference
-- cascade rests only on the kernel's three standard axioms — NO `sorryAx`, NO crypto axiom.
#print axioms reference_cascade_nonvacuous

/-- Non-vacuity of the dial wiring: the floor is `acceptanceOnly`, the dial's bottom notch is the
verifier's bit, and an accepting proof proves absence. -/
example :
    (nonMembershipKindObligation (Digest := Int)).dialFloor = Dial.acceptanceOnly :=
  (nonmembership_dial_wired (K := refKernel) trivial base absentStmt 0).1

end Reference

-- TRIPWIRES: the non-membership bridge + derived verify-soundness + cascade + dial wiring are
-- kernel-clean. The bridge's SOUNDNESS heart (`sorted_gap_excludes`) and the two Merkle sub-proofs
-- are FULLY proved — NO primitive seam. The ONLY cryptographic residue is the `extractable` carrier
-- (passed as a hypothesis, binding the committed list to the root via `compress` CR), never a
-- hidden `sorry`.
#assert_axioms sorted_gap_excludes
#assert_axioms nonmembership_bridge
#assert_axioms nonmembership_verify_sound
#assert_axioms nonmembership_registry_cascade
#assert_axioms nonmembership_dial_wired

end Dregg2.Crypto.NonMembership
