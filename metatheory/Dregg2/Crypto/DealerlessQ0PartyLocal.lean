/-
# Party-local q0 contribution and transcript laws

This module is the Lean image of the experimental q0 commitment round in
`fhegg-fhe/src/threshold/quorum.rs`.  It separates three facts which are easy
to blur at the implementation boundary:

1. a finalized public view contains exactly one context- and slot-key-bound
   contribution at every position of the ordered custody roster;
2. each party can retain and check its own opening without any coordinator or
   dealer receiving the list of openings; and
3. an externally pinned, binding transcript anchor makes two different public
   contribution lists incompatible.

The last qualifier is load-bearing.  Recomputing a digest independently in
two split views merely gives two different, internally valid digests.  This
file does not invent authenticated broadcast, signatures, or consensus around
that digest.  Likewise, commitment injectivity is an explicit hypothesis; the
module does not claim concrete SIS binding or hiding parameters.

The exact q0 radix codec from `PqShareCommitment` is lifted to complete rows.
It is lossless for canonical q0 residues but is deliberately shown *not* to be
an additive homomorphism at a radix carry.  Consequently the current Rust
round correctly binds an ordered list of party/slot commitments; it must not
silently sum commitments made under different slot keys, nor identify a sum
of encoded limbs with the encoding of a modular BFV sum.
-/

import Dregg2.Crypto.PqShareCommitment
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Dregg2.Crypto.DealerlessQ0PartyLocal

set_option autoImplicit false

open Dregg2.Crypto.PqShareCommitment

/-! ## Exact ordered public contribution round -/

/-- Public context fixed before the q0 contribution round.  The collective
key identity belongs here because Rust derives every slot key from both this
context and the pre-anchor DKG transcript. -/
structure RoundContext (Party Session CollectiveKey : Type*) where
  session : Session
  collectiveKey : CollectiveKey
  orderedRoster : List Party
  deriving DecidableEq, Repr

/-- A raw public q0 contribution.  It repeats the claimed context and slot key
so cross-session and wrong-slot substitutions are representable and refused
rather than excluded by construction.  The secret opening is absent. -/
structure PublicContribution
    (Party Session CollectiveKey KeyId Commitment : Type*) where
  claimedContext : RoundContext Party Session CollectiveKey
  party : Party
  keyId : KeyId
  commitment : Commitment
  deriving DecidableEq, Repr

/-- One contribution matches its exact ordered roster position and the key
derived for that position. -/
def PublicAccepted
    {Party Session CollectiveKey KeyId Commitment : Type*}
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (ctx : RoundContext Party Session CollectiveKey) (expected : Party)
    (c : PublicContribution Party Session CollectiveKey KeyId Commitment) : Prop :=
  c.claimedContext = ctx /\
  c.party = expected /\
  c.keyId = deriveKey ctx expected

/-- Recursive exact-roster verifier.  Only `[]/[]` accepts; omissions, extras,
and reordered parties reach a false branch. -/
def OrderedIncluded
    {Party Session CollectiveKey KeyId Commitment : Type*}
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (ctx : RoundContext Party Session CollectiveKey) :
    List Party ->
      List (PublicContribution Party Session CollectiveKey KeyId Commitment) -> Prop
  | [], [] => True
  | p :: ps, c :: cs =>
      PublicAccepted deriveKey ctx p c /\ OrderedIncluded deriveKey ctx ps cs
  | _, _ => False

/-- Public round acceptance also rules out a duplicated custody identity in
the roster itself. -/
def RoundAccepted
    {Party Session CollectiveKey KeyId Commitment : Type*} [DecidableEq Party]
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (ctx : RoundContext Party Session CollectiveKey)
    (cs : List (PublicContribution Party Session CollectiveKey KeyId Commitment)) : Prop :=
  ctx.orderedRoster.Nodup /\ OrderedIncluded deriveKey ctx ctx.orderedRoster cs

/-- Canonical public sequence covered by the follow-up transcript digest.
Order is data: the verifier never sorts this list. -/
def publicSequence
    {Party Session CollectiveKey KeyId Commitment : Type*}
    (cs : List (PublicContribution Party Session CollectiveKey KeyId Commitment)) :
    List (Party × KeyId × Commitment) :=
  cs.map fun c => (c.party, c.keyId, c.commitment)

theorem orderedIncluded_length
    {Party Session CollectiveKey KeyId Commitment : Type*}
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (ctx : RoundContext Party Session CollectiveKey) {roster : List Party}
    {cs : List (PublicContribution Party Session CollectiveKey KeyId Commitment)}
    (h : OrderedIncluded deriveKey ctx roster cs) : cs.length = roster.length := by
  induction roster generalizing cs with
  | nil => cases cs <;> simp_all [OrderedIncluded]
  | cons p ps ih =>
      cases cs with
      | nil => simp_all [OrderedIncluded]
      | cons c cs =>
          simp only [OrderedIncluded] at h
          simp [ih h.2]

/-- Acceptance contains one contribution for every roster position and no
additional contribution. -/
theorem accepted_complete_roster
    {Party Session CollectiveKey KeyId Commitment : Type*} [DecidableEq Party]
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (ctx : RoundContext Party Session CollectiveKey)
    {cs : List (PublicContribution Party Session CollectiveKey KeyId Commitment)}
    (h : RoundAccepted deriveKey ctx cs) : cs.length = ctx.orderedRoster.length :=
  orderedIncluded_length deriveKey ctx h.2

theorem orderedIncluded_parties
    {Party Session CollectiveKey KeyId Commitment : Type*}
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (ctx : RoundContext Party Session CollectiveKey) {roster : List Party}
    {cs : List (PublicContribution Party Session CollectiveKey KeyId Commitment)}
    (h : OrderedIncluded deriveKey ctx roster cs) : cs.map (fun c => c.party) = roster := by
  induction roster generalizing cs with
  | nil => cases cs <;> simp_all [OrderedIncluded]
  | cons p ps ih =>
      cases cs with
      | nil => simp_all [OrderedIncluded]
      | cons c cs =>
          simp only [OrderedIncluded] at h
          simp [h.1.2.1, ih h.2]

/-- The accepted public contribution order is exactly the caller-pinned
custody roster. -/
theorem accepted_parties_eq_ordered_roster
    {Party Session CollectiveKey KeyId Commitment : Type*} [DecidableEq Party]
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (ctx : RoundContext Party Session CollectiveKey)
    {cs : List (PublicContribution Party Session CollectiveKey KeyId Commitment)}
    (h : RoundAccepted deriveKey ctx cs) :
    cs.map (fun c => c.party) = ctx.orderedRoster :=
  orderedIncluded_parties deriveKey ctx h.2

theorem orderedIncluded_contexts
    {Party Session CollectiveKey KeyId Commitment : Type*}
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (ctx : RoundContext Party Session CollectiveKey) {roster : List Party}
    {cs : List (PublicContribution Party Session CollectiveKey KeyId Commitment)}
    (h : OrderedIncluded deriveKey ctx roster cs) :
    forall c, c ∈ cs -> c.claimedContext = ctx := by
  induction roster generalizing cs with
  | nil => cases cs <;> simp_all [OrderedIncluded]
  | cons p ps ih =>
      cases cs with
      | nil => simp_all [OrderedIncluded]
      | cons c cs =>
          simp only [OrderedIncluded] at h
          intro c' hc'
          simp only [List.mem_cons] at hc'
          rcases hc' with rfl | hc'
          · exact h.1.1
          · exact ih h.2 c' hc'

/-- A cross-session, cross-key, or cross-roster claimed context cannot be
hidden elsewhere in an otherwise well-shaped list. -/
theorem context_mismatch_refused
    {Party Session CollectiveKey KeyId Commitment : Type*} [DecidableEq Party]
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (ctx : RoundContext Party Session CollectiveKey)
    (cs : List (PublicContribution Party Session CollectiveKey KeyId Commitment))
    (hbad : exists c, c ∈ cs /\ c.claimedContext ≠ ctx) :
    Not (RoundAccepted deriveKey ctx cs) := by
  intro hacc
  obtain ⟨c, hc, hne⟩ := hbad
  exact hne (orderedIncluded_contexts deriveKey ctx hacc.2 c hc)

/-- An omitted or extra contribution is refused before transcript promotion. -/
theorem incomplete_roster_refused
    {Party Session CollectiveKey KeyId Commitment : Type*} [DecidableEq Party]
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (ctx : RoundContext Party Session CollectiveKey)
    (cs : List (PublicContribution Party Session CollectiveKey KeyId Commitment))
    (hne : cs.length ≠ ctx.orderedRoster.length) :
    Not (RoundAccepted deriveKey ctx cs) :=
  fun h => hne (accepted_complete_roster deriveKey ctx h)

/-- Reordering is not normalized away. -/
theorem reordered_roster_refused
    {Party Session CollectiveKey KeyId Commitment : Type*} [DecidableEq Party]
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (ctx : RoundContext Party Session CollectiveKey)
    (cs : List (PublicContribution Party Session CollectiveKey KeyId Commitment))
    (hne : cs.map (fun c => c.party) ≠ ctx.orderedRoster) :
    Not (RoundAccepted deriveKey ctx cs) :=
  fun h => hne (accepted_parties_eq_ordered_roster deriveKey ctx h)

/-! ## Binding and the precise split-view boundary -/

/-- An accepted view recomputes its digest from the exact typed context and
ordered public sequence.  `anchor` abstracts the canonical encoder plus hash. -/
def Anchored
    {Party Session CollectiveKey KeyId Commitment Digest : Type*} [DecidableEq Party]
    (anchor : RoundContext Party Session CollectiveKey ->
      List (Party × KeyId × Commitment) -> Digest)
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (ctx : RoundContext Party Session CollectiveKey)
    (cs : List (PublicContribution Party Session CollectiveKey KeyId Commitment))
    (digest : Digest) : Prop :=
  RoundAccepted deriveKey ctx cs /\ anchor ctx (publicSequence cs) = digest

/-- Computational hash binding is an explicit perimeter premise, never a
theorem about SHA-256 obtained from equality of Rust byte arrays. -/
def AnchorBinding
    {Party Session CollectiveKey KeyId Commitment Digest : Type*}
    (anchor : RoundContext Party Session CollectiveKey ->
      List (Party × KeyId × Commitment) -> Digest) : Prop :=
  forall ctx, Function.Injective (anchor ctx)

/-- Two accepted observers agreeing on one externally pinned digest agree on
the complete ordered public q0 contribution sequence. -/
theorem same_pinned_anchor_binds_public_sequence
    {Party Session CollectiveKey KeyId Commitment Digest : Type*} [DecidableEq Party]
    (anchor : RoundContext Party Session CollectiveKey ->
      List (Party × KeyId × Commitment) -> Digest)
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (hbind : AnchorBinding anchor)
    (ctx : RoundContext Party Session CollectiveKey)
    {xs ys : List (PublicContribution Party Session CollectiveKey KeyId Commitment)}
    {digest : Digest}
    (hx : Anchored anchor deriveKey ctx xs digest)
    (hy : Anchored anchor deriveKey ctx ys digest) :
    publicSequence xs = publicSequence ys := by
  apply hbind ctx
  exact hx.2.trans hy.2.symm

/-- A representable split view necessarily moves a binding digest. -/
theorem changed_public_sequence_changes_anchor
    {Party Session CollectiveKey KeyId Commitment Digest : Type*}
    (anchor : RoundContext Party Session CollectiveKey ->
      List (Party × KeyId × Commitment) -> Digest)
    (hbind : AnchorBinding anchor)
    (ctx : RoundContext Party Session CollectiveKey)
    {xs ys : List (PublicContribution Party Session CollectiveKey KeyId Commitment)}
    (hne : publicSequence xs ≠ publicSequence ys) :
    anchor ctx (publicSequence xs) ≠ anchor ctx (publicSequence ys) := by
  intro heq
  exact hne (hbind ctx heq)

/-- Therefore two different public views cannot both verify against the same
pinned digest.  This theorem spends a *shared pinned digest*; it does not
construct the authenticated broadcast needed to establish one. -/
theorem split_view_refused_at_pinned_anchor
    {Party Session CollectiveKey KeyId Commitment Digest : Type*} [DecidableEq Party]
    (anchor : RoundContext Party Session CollectiveKey ->
      List (Party × KeyId × Commitment) -> Digest)
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (hbind : AnchorBinding anchor)
    (ctx : RoundContext Party Session CollectiveKey)
    {xs ys : List (PublicContribution Party Session CollectiveKey KeyId Commitment)}
    {digest : Digest}
    (hne : publicSequence xs ≠ publicSequence ys) :
    Not (Anchored anchor deriveKey ctx xs digest /\
      Anchored anchor deriveKey ctx ys digest) := by
  rintro ⟨hx, hy⟩
  exact hne (same_pinned_anchor_binds_public_sequence anchor deriveKey hbind ctx hx hy)

/-! ## Party-local openings and dealer/viewer-free aggregation -/

/-- A party-local record pairs the public contribution with an opening retained
inside that party's custody.  The coordinator sees only `public`. -/
structure LocalContribution
    (Party Session CollectiveKey KeyId Commitment Opening : Type*) where
  published : PublicContribution Party Session CollectiveKey KeyId Commitment
  opening : Opening
  deriving DecidableEq, Repr

/-- The exact local bridge used by Rust's `bind_experimental_q0_share_commitment`:
the party, context, and slot key are right, and the retained opening verifies
against the public commitment at that position. -/
def ExactLocalOpening
    {Party Session CollectiveKey KeyId Commitment Opening : Type*}
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (commit : RoundContext Party Session CollectiveKey -> Party -> Opening -> Commitment)
    (ctx : RoundContext Party Session CollectiveKey) (expected : Party)
    (c : LocalContribution Party Session CollectiveKey KeyId Commitment Opening) : Prop :=
  PublicAccepted deriveKey ctx expected c.published /\
  commit ctx expected c.opening = c.published.commitment

def OrderedLocallyValid
    {Party Session CollectiveKey KeyId Commitment Opening : Type*}
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (commit : RoundContext Party Session CollectiveKey -> Party -> Opening -> Commitment)
    (ctx : RoundContext Party Session CollectiveKey) :
    List Party ->
      List (LocalContribution Party Session CollectiveKey KeyId Commitment Opening) -> Prop
  | [], [] => True
  | p :: ps, c :: cs =>
      ExactLocalOpening deriveKey commit ctx p c /\
        OrderedLocallyValid deriveKey commit ctx ps cs
  | _, _ => False

def eraseLocals
    {Party Session CollectiveKey KeyId Commitment Opening : Type*}
    (cs : List (LocalContribution Party Session CollectiveKey KeyId Commitment Opening)) :
    List (PublicContribution Party Session CollectiveKey KeyId Commitment) :=
  cs.map (fun c => c.published)

def LocalRoundAccepted
    {Party Session CollectiveKey KeyId Commitment Opening : Type*} [DecidableEq Party]
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (commit : RoundContext Party Session CollectiveKey -> Party -> Opening -> Commitment)
    (ctx : RoundContext Party Session CollectiveKey)
    (cs : List (LocalContribution Party Session CollectiveKey KeyId Commitment Opening)) : Prop :=
  ctx.orderedRoster.Nodup /\ OrderedLocallyValid deriveKey commit ctx ctx.orderedRoster cs

theorem orderedLocallyValid_erases
    {Party Session CollectiveKey KeyId Commitment Opening : Type*}
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (commit : RoundContext Party Session CollectiveKey -> Party -> Opening -> Commitment)
    (ctx : RoundContext Party Session CollectiveKey) {roster : List Party}
    {cs : List (LocalContribution Party Session CollectiveKey KeyId Commitment Opening)}
    (h : OrderedLocallyValid deriveKey commit ctx roster cs) :
    OrderedIncluded deriveKey ctx roster (eraseLocals cs) := by
  induction roster generalizing cs with
  | nil => cases cs <;> simp_all [OrderedLocallyValid, OrderedIncluded, eraseLocals]
  | cons p ps ih =>
      cases cs with
      | nil => simp_all [OrderedLocallyValid]
      | cons c cs =>
          simp only [OrderedLocallyValid] at h
          change PublicAccepted deriveKey ctx p c.published /\
            OrderedIncluded deriveKey ctx ps (eraseLocals cs)
          exact ⟨h.1.1, ih h.2⟩

/-- Every all-local accepting view projects to the public exact-roster view;
the converse intentionally does not hold because public data contains no
openings. -/
theorem local_acceptance_implies_public_acceptance
    {Party Session CollectiveKey KeyId Commitment Opening : Type*} [DecidableEq Party]
    (deriveKey : RoundContext Party Session CollectiveKey -> Party -> KeyId)
    (commit : RoundContext Party Session CollectiveKey -> Party -> Opening -> Commitment)
    (ctx : RoundContext Party Session CollectiveKey)
    {cs : List (LocalContribution Party Session CollectiveKey KeyId Commitment Opening)}
    (h : LocalRoundAccepted deriveKey commit ctx cs) :
    RoundAccepted deriveKey ctx (eraseLocals cs) :=
  ⟨h.1, orderedLocallyValid_erases deriveKey commit ctx h.2⟩

section Aggregate

variable {Rq M B N : Type*} [CommRing Rq]
variable [AddCommGroup M] [Module Rq M]
variable [AddCommGroup B] [Module Rq B]
variable [AddCommGroup N] [Module Rq N]

/-- Private aggregate computed only from the list of party-local openings.  No
dealer key, coordinator opening, or viewer value occurs in its type. -/
def aggregateOpenings
    {Party Session CollectiveKey KeyId Commitment : Type*}
    (cs : List (LocalContribution Party Session CollectiveKey KeyId Commitment (Opening M B))) :
    Opening M B :=
  (cs.map (fun c => c.opening)).sum

/-- The private aggregate is insensitive to a coordinator's enumeration order
at the algebra layer.  Protocol transcript order remains strict and is *not*
normalized by this theorem. -/
theorem aggregateOpenings_order_independent
    {Party Session CollectiveKey KeyId Commitment : Type*}
    {xs ys : List (LocalContribution Party Session CollectiveKey KeyId Commitment (Opening M B))}
    (hperm : (xs.map (fun c => c.opening)).Perm (ys.map (fun c => c.opening))) :
    aggregateOpenings xs = aggregateOpenings ys := by
  exact hperm.sum_eq

/-- If every opening uses one common linear map, committing the private
aggregate equals summing its individual commitments.  The current q0 Rust
round instead derives a different slot key for every party, so this theorem is
not a license to sum its public commitment list. -/
theorem commit_aggregate_under_common_key
    {Party Session CollectiveKey KeyId Commitment : Type*}
    (messageMap : M →ₗ[Rq] N) (blindingMap : B →ₗ[Rq] N)
    (cs : List (LocalContribution Party Session CollectiveKey KeyId Commitment (Opening M B))) :
    commit messageMap blindingMap (aggregateOpenings cs) =
      (cs.map (fun c => commit messageMap blindingMap c.opening)).sum := by
  rw [aggregateOpenings, commit_sum messageMap blindingMap (cs.map (fun c => c.opening)),
    List.map_map]
  rfl

end Aggregate

/-! ## Exact q0 row reconstruction and the non-homomorphic codec tooth -/

/-- Canonical party-local q0 row: exactly the deployed degree and every entry
is the unique natural representative below q0. -/
def CanonicalQ0Row (row : List Nat) : Prop :=
  row.length = bfvQ0Degree /\ forall x, x ∈ row -> x < bfvQ0Modulus

def encodeQ0Row (row : List Nat) : List (Nat × Nat × Nat) :=
  row.map bfvQ0EncodeRust

def decodeQ0Row (row : List (Nat × Nat × Nat)) : List Nat :=
  row.map bfvQ0Decode

theorem encodeQ0Row_length (row : List Nat) :
    (encodeQ0Row row).length = row.length := by
  simp [encodeQ0Row]

/-- The literal Rust three-limb loop reconstructs every complete canonical q0
party row exactly; this spends the already-proved scalar radix theorem. -/
theorem decodeQ0Row_encodeQ0Row (row : List Nat)
    (hcanon : forall x, x ∈ row -> x < bfvQ0Modulus) :
    decodeQ0Row (encodeQ0Row row) = row := by
  induction row with
  | nil => simp [encodeQ0Row, decodeQ0Row]
  | cons x xs ih =>
      have hx : x < bfvQ0Modulus := hcanon x (by simp)
      have hxs : forall y, y ∈ xs -> y < bfvQ0Modulus := by
        intro y hy
        exact hcanon y (by simp [hy])
      change bfvQ0Decode (bfvQ0EncodeRust x) :: decodeQ0Row (encodeQ0Row xs) = x :: xs
      rw [bfvQ0Decode_encodeRust x (bfvQ0Residue_fits x hx), ih hxs]

theorem canonicalQ0Row_roundTrip {row : List Nat} (h : CanonicalQ0Row row) :
    decodeQ0Row (encodeQ0Row row) = row :=
  decodeQ0Row_encodeQ0Row row h.2

/-- Coordinatewise integer addition of encoded triples.  This is *not* the
BFV modular addition operation and exists only to expose the carry trap. -/
def addEncodedQ0 (left right : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (left.1 + right.1, left.2.1 + right.2.1, left.2.2 + right.2.2)

/-- At the first radix carry, adding faithful limb encodings differs from
encoding the mathematical sum.  Any aggregate link needs carry/mod-q
constraints; injective radix reconstruction alone is insufficient. -/
theorem q0Encoding_not_additive_at_first_carry :
    addEncodedQ0 (bfvQ0EncodeRust (bfvQ0Radix - 1)) (bfvQ0EncodeRust 1) ≠
      bfvQ0EncodeRust bfvQ0Radix := by
  norm_num [addEncodedQ0, bfvQ0EncodeRust, bfvQ0Radix]

#guard bfvQ0EncodeRust 32767 == (32767, 0, 0)
#guard bfvQ0EncodeRust 32768 == (0, 1, 0)
#guard addEncodedQ0 (bfvQ0EncodeRust 32767) (bfvQ0EncodeRust 1) !=
  bfvQ0EncodeRust 32768

/-! ## Executable formation and split-view canaries -/

namespace Demo

def ctx : RoundContext Bool Bool Bool where
  session := false
  collectiveKey := true
  orderedRoster := [false, true]

def deriveKey (_ : RoundContext Bool Bool Bool) (party : Bool) : Nat :=
  if party then 22 else 11

def c0 : PublicContribution Bool Bool Bool Nat Nat where
  claimedContext := ctx
  party := false
  keyId := 11
  commitment := 7

def c1 : PublicContribution Bool Bool Bool Nat Nat where
  claimedContext := ctx
  party := true
  keyId := 22
  commitment := 109

def c1Split : PublicContribution Bool Bool Bool Nat Nat where
  claimedContext := ctx
  party := true
  keyId := 22
  commitment := 110

def honest : List (PublicContribution Bool Bool Bool Nat Nat) := [c0, c1]
def split : List (PublicContribution Bool Bool Bool Nat Nat) := [c0, c1Split]

/-- Identity is a binding executable stand-in for canonical typed bytes plus a
collision-resistant hash.  It carries no cryptographic claim. -/
def identityAnchor (_ : RoundContext Bool Bool Bool)
    (xs : List (Bool × Nat × Nat)) : List (Bool × Nat × Nat) := xs

def localCommit (_ : RoundContext Bool Bool Bool) (party : Bool) (opening : Nat) : Nat :=
  if party then opening + 100 else opening

def localHonest : List (LocalContribution Bool Bool Bool Nat Nat Nat) :=
  [{ published := c0, opening := 7 }, { published := c1, opening := 9 }]

def localWrongOpening : List (LocalContribution Bool Bool Bool Nat Nat Nat) :=
  [{ published := c0, opening := 8 }, { published := c1, opening := 9 }]

example : RoundAccepted deriveKey ctx honest := by
  simp [RoundAccepted, OrderedIncluded, PublicAccepted, deriveKey, ctx, honest, c0, c1]

example : Not (RoundAccepted deriveKey ctx [c1, c0]) := by
  simp [RoundAccepted, OrderedIncluded, PublicAccepted, deriveKey, ctx, c0, c1]

example : Not (RoundAccepted deriveKey ctx [c0]) := by
  simp [RoundAccepted, OrderedIncluded, PublicAccepted, deriveKey, ctx, c0]

example : LocalRoundAccepted deriveKey localCommit ctx localHonest := by
  simp [LocalRoundAccepted, OrderedLocallyValid, ExactLocalOpening, PublicAccepted,
    deriveKey, localCommit, ctx, localHonest, c0, c1]

example : Not (LocalRoundAccepted deriveKey localCommit ctx localWrongOpening) := by
  simp [LocalRoundAccepted, OrderedLocallyValid, ExactLocalOpening, PublicAccepted,
    deriveKey, localCommit, ctx, localWrongOpening, c0, c1]

example : AnchorBinding identityAnchor := by
  intro _ xs ys h
  exact h

/-- Each side of an unauthenticated split can recompute and accept its *own*
digest.  This is the executable canary preventing the binding theorem above
from being mislabeled authenticated broadcast. -/
example :
    Anchored identityAnchor deriveKey ctx honest (publicSequence honest) /\
    Anchored identityAnchor deriveKey ctx split (publicSequence split) := by
  constructor <;> simp [Anchored, RoundAccepted, OrderedIncluded, PublicAccepted,
    identityAnchor, honest, split, c0, c1, c1Split, ctx, deriveKey]

#guard publicSequence honest != publicSequence split

/-- Once one public anchor is pinned, the same split is impossible. -/
example : Not (Anchored identityAnchor deriveKey ctx honest (publicSequence honest) /\
    Anchored identityAnchor deriveKey ctx split (publicSequence honest)) := by
  apply split_view_refused_at_pinned_anchor identityAnchor deriveKey (by
    intro _ xs ys h
    exact h) ctx
  decide

end Demo

#assert_axioms accepted_complete_roster
#assert_axioms accepted_parties_eq_ordered_roster
#assert_axioms context_mismatch_refused
#assert_axioms incomplete_roster_refused
#assert_axioms reordered_roster_refused
#assert_axioms same_pinned_anchor_binds_public_sequence
#assert_axioms changed_public_sequence_changes_anchor
#assert_axioms split_view_refused_at_pinned_anchor
#assert_axioms local_acceptance_implies_public_acceptance
#assert_axioms aggregateOpenings_order_independent
#assert_axioms commit_aggregate_under_common_key
#assert_axioms decodeQ0Row_encodeQ0Row
#assert_axioms canonicalQ0Row_roundTrip
#assert_axioms q0Encoding_not_additive_at_first_carry

end Dregg2.Crypto.DealerlessQ0PartyLocal
