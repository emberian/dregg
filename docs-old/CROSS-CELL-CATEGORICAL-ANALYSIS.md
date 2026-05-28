# CROSS-CELL-CATEGORICAL-ANALYSIS — finding what isn't there

**Date:** 2026-05-24. **Status:** study/design lane; read-only on code;
one new `.md`. **Companion docs:**
`CROSS-CELL-COORDINATION.md`, `FEDERATION-AS-CELL.md`,
`PREDICATE-INVENTORY.md`, `SLOT-CAVEATS-DESIGN.md`,
`SLOT-CAVEATS-EVALUATION.md`, `STAGE-7-GAMMA-2-PI-DESIGN.md`,
`AUTHORIZATION-CUSTOM-DESIGN.md`, `BOUNDARIES.md`,
`PROOF-TO-ACTION-BINDING-SWEEP.md`,
`WITNESSED-RECEIPT-CHAIN-DESIGN.md`,
`DESIGN-receipts.md`, `DESIGN-captp-integration.md`,
`AUDIT-distributed-semantics.md`.

The honest motivation: the prior cross-cell coordination doc claimed the
algebra was *complete* and only the *ergonomics* leaked. The TL;DR
reads: "γ.2 + Custom + slot caveats span the design space." That claim
deserves a stress test from a different direction. *Categorical
analysis* is the test we're applying here — name the objects and
morphisms, look for missing duals and adjoints, see whether the holes
in the diagram correspond to anything an app would actually want.

This is a method that has worked for dregg before: the
`PREDICATE-INVENTORY` unification surfaced `WitnessedPredicate`
precisely by noticing that fifteen apparently-different predicate
shapes had the same `(commitment, input, proof, verifier)` Yoneda
signature. The same lens applied to *binding* and *agency* may surface
holes that pure use-case enumeration didn't.

The opinionated TL;DR — written first so it can be read alone:

> Six axes of dregg's substrate have **broken or partial dualities**.
> Three of them — *negation in `StateConstraint`*, *implication in
> `StateConstraint`*, and *unilateral binding (single-cell self-attestation
> as a structural sibling of γ.2 bilateral)* — point at real app needs
> and warrant prototype work. Two — *renunciation / proof-of-non-holding*
> and *refusal / proof-of-non-action* — point at categorical curiosities
> with thin app demand but interesting compositional payoff; defer.
> One — *the "witness producer" as a categorical dual to
> `WitnessedPredicate`* — turns out to be already-there but un-named;
> the act of naming it is the win, not new code.
>
> Beyond the missing-duals lens, the analysis turns up four
> **pushout / colimit shapes** that are absent from the current
> primitive set: *coequalizer-of-ring-trade* (provable cycle closure as
> a single artifact, today only implicit in call_forest), *pushout
> binding for delegation chains* (combining two grants into one
> attested handoff), *equalizer-of-agreement* (the set of states two
> programs agree on, useful for cross-cell view harmonization), and
> *initial-algebra-of-cross-cell-fold* (the categorical name for what
> γ.2's recursive composition is *converging toward* but doesn't yet
> name). One of these — the cycle-closure coequalizer — is a real
> ergonomic win and should be prototyped at the DSL surface; the others
> are clarifying observations.
>
> The verdict on the prior doc's claim: *correct, with three asterisks
> and four footnotes*. Pairwise + Custom + slot caveats does not leave
> *algebraically reachable* shapes inexpressible. But categorical
> hygiene surfaces a handful of natural duals whose presence would make
> the primitive set internally complete (every constructor having its
> dual; every limit having its colimit; every functor having its right
> adjoint when one exists). The missing pieces are small but cohere
> into a story.

The remainder of the doc earns this and is mercilessly honest about
which observations are real and which are mathematical wishful
thinking.

---

## §1. The categories — naming dregg's objects and morphisms

Categorical analysis pays its rent in two places: it forces explicit
names for what we've been pointing at, and it surfaces structural holes
(missing duals, broken adjunctions) that use-case-driven design tends
to miss. This section establishes the names.

We will work informally with several interlocking categories.
"Informally" is load-bearing: dregg is not a category in the strict
sense (we don't get associativity *up to definitional equality* in
most places; effects are partial; the substrate is computational), but
each of these collections *has enough structure to do diagram chasing*,
and the diagram chases generate questions.

### §1.1. **Cell** — the category of cells and effects

**Objects.** Cell states. Concretely, the inhabited type is
`(cell_id, public_field_view, private_state_commitment, nonce,
balance)` where the cell id is the *identity* of an object across its
state-transitions and the rest is its current value. Two cell states
with the same id are "the same object at different times"; two cell
states with different ids are different objects.

**Morphisms.** Effects that mutate cell state. The morphism
`s_1 →_{e} s_2` exists iff there is an `Effect e` such that applying `e`
to `s_1` produces `s_2` (and the cell's program admits the transition
— see §1.4 for the cell-program-as-functor view). Identity is the
empty effect (a `Turn` with no effects targeting the cell; today
encoded by the cell not being touched). Composition is *Turn-level
sequence-then-fold*: `e_2 ∘ e_1` is applying `e_1` then `e_2`,
provided both are admissible from the relevant intermediate state.

**Products.** *Partially.* The categorical product of two cell-states
`s_A × s_B` would be a state-pair acting as a single object. `dregg`
does have a notion — the *touched-set of a turn* is the simultaneous
state of several cells under a single Turn-event — but this is a
collection of objects under a shared morphism, not a product object in
the strict sense. The closest construction is `FederationState`, the
Merkle aggregation of all cells in a federation; this *is* a product-
shaped object in a sense (queries against a federation state factor
through queries against constituent cells). But Cell-the-category and
Federation-the-product live at different levels.

**Coproducts.** *Not present in a useful sense.* There is no `s_A + s_B`
that represents "either state A or state B" as a cell-state. The
closest thing is `AnyOf` at the `StateConstraint` level (§5.4), which
is a disjunction of *predicates*, not states.

**Terminal object.** *Yes — the "annihilated" cell.* A revoked or
sealed-away cell that no longer admits any effect is terminal in the
sense that every cell has a (trivial, monotonic) morphism *to* it (the
revocation effect). Today this is the `RevokeCapability` end-state.

**Initial object.** *Yes — the "uninstantiated" cell shape.* Before a
`PrincipalKey` materializes, the cell-state is empty (`Vec<FieldElement>`
of zeros, nonce 0, balance 0). Every cell has a unique morphism *from*
this initial point (the chain of all its prior turns).

**Subtle:** the category is *thin* on most pairs of objects — there's
either a uniquely-determined morphism between two states (their
canonical transition path) or no morphism at all. Cells don't admit
*multiple* essentially-different ways to go from `s_1` to `s_2`; the
trace is determined by the cell-program. This is a property
(thinness / posetal-locally) that simplifies a lot of subsequent
analysis: pull-backs reduce to meets, pushouts to joins, etc.

### §1.2. **Effect** — the category of effects

**Objects.** Effect kinds: `Transfer`, `Mint`, `GrantCapability`,
`RevokeCapability`, `Introduce`, `Custom { vk_hash }`, `NoteSpend`,
`NoteCreate`, `BridgeMint`, `BridgeBurn`, etc. (See
`turn::action::Effect`.)

**Morphisms.** Trickier. The natural morphism is *refinement*: a
`Transfer { from: A, to: B, amount: 10 }` refines `Transfer { from: A,
to: B }` (which refines `Transfer { from: A }`). This makes Effect a
*poset* where higher-arity instances refine lower-arity templates.

**Products.** *Yes — effect intersection.* The product of two effects
is the most general effect that refines both (when one exists). Two
unrelated effect-instances have no product; refinement-related ones
do. `dregg` doesn't surface this construction at any seam, but it lives
implicitly in `MatchSpec` and intent matching (which compute "the
most specific MatchSpec that satisfies both A and B").

**Coproducts.** *Yes — effect union (template).* The coproduct of two
effects is the most specific template that *generalizes* both. For
sibling effects (`Transfer { from: A, to: B, amount: 10 }` and
`Transfer { from: A, to: C, amount: 20 }`), the coproduct is `Transfer
{ from: A }`. This is what `Pattern` in `wire::dfa_router` reaches for
— matching multiple specific effects under a single classifier.

**Terminal object.** `Effect::Unchecked` — every effect refines this
"do anything." Today's `Authorization::Unchecked` carve-out is a
soundness hole because it makes this terminal too easy to reach; see
`EXECUTOR-HONESTY-AUDIT.md`.

**Initial object.** *Absent.* There is no "impossible effect" that
every effect generalizes. We could *manufacture* one — see §3.5 on
`Effect::Refusal` — but it doesn't naturally exist today.

### §1.3. **Predicate** — the category of state-predicates

**Objects.** Predicates over state transitions: `(old_state,
new_state, ctx) → bool`. Concretely: `StateConstraint`,
`Preconditions`, `CapabilityCaveat`, `FacetConstraint`.

**Morphisms.** *Implication.* `P → Q` iff `P` is *stronger* than `Q`:
every state-pair satisfying `P` also satisfies `Q`. Equivalently, `P
⊆ Q` viewed as subsets of state-pair space.

**Products.** *Yes — conjunction.* `P ∧ Q` is the predicate that
holds iff both `P` and `Q` hold. Today encoded implicitly as
`Vec<StateConstraint>` (every constraint must accept). This is the
"slot caveats list AND" pattern.

**Coproducts.** *Yes — disjunction.* `P ∨ Q` holds iff either holds.
Today encoded as `StateConstraint::AnyOf` (§5.1 of
`SLOT-CAVEATS-EVALUATION.md`).

**Terminal object.** `True` — the trivially-satisfied predicate.
Implicit (an empty `Vec<StateConstraint>` is the no-op constraint
list).

**Initial object.** `False` — the never-satisfied predicate.
*Absent today.* This is the first interesting hole; see §3.1.

**Subtle:** Predicate is a *Heyting algebra* if we have implication
(`P ⇒ Q`) and negation (`¬P`). `dregg` has neither — conjunction (Vec)
and disjunction (`AnyOf`) only. This is a real gap that §3 will
explore.

### §1.4. **Program** — programs as partial functors Cell → Cell

**Objects.** Cells (same as §1.1).

**Morphisms.** A `CellProgram` is a *partial function* on cell
transitions: given `(old_state, new_state, ctx)`, the program either
accepts (the transition is admissible) or rejects (it is not). This is
a *characteristic function* on Cell-morphisms — a sub-category-defining
constraint.

This makes a `CellProgram` itself an endofunctor on `Cell` (or rather,
*on its category of morphisms*): it determines which morphisms are
admitted. Today's `CellProgram::Predicate(Vec<StateConstraint>)`,
`CellProgram::Cases(Vec<TransitionCase>)`, and `CellProgram::Custom
{ ir_hash, ... }` are three ways to *encode* this functor.

**Sub-functor relation.** `CellProgram P1 ⊆ CellProgram P2` iff every
transition `P1` accepts, `P2` accepts. Today implicit; `is_facet_
attenuation` and `is_narrower_or_equal` realize a *capability-side*
shadow of this relation.

**Composition / monoid?** The set of all `CellProgram`s under
"intersection" (admit the transition iff both programs admit) is a
*meet-semilattice*. Under "union" (admit iff either admits) it's a
join-semilattice. Both operations are commutative and idempotent.
This is a fairly rich algebraic structure dregg doesn't currently
exploit at the program-composition surface — you can't naturally take
two `CellProgram`s and *merge* them; the cell has exactly one.

This is the first hint of a missing primitive: see §8 on monoidal
program composition.

### §1.5. **Authorization** — the category of authorization claims

**Objects.** Authorization modes: `Signature(pk, sig)`, `Proof { ...
}`, `Bearer(swiss)`, `CapTpDelivered { ... }`, `Custom { predicate,
descriptor }`, `Unchecked`.

**Morphisms.** *Attenuation* (refinement, restriction). One auth mode
attenuates another iff every action authorized by the first is also
authorized by the second. This is the `is_facet_attenuation` /
`is_narrower_or_equal` lattice (`CELL-CRATE-REVIEW.md`, `facet.rs`).

**Products / coproducts.** `Auth_A ∧ Auth_B` = "must provide both" —
today only encodable via `Authorization::Custom { predicate: ... }`
where the predicate is a custom AIR verifying both. `Auth_A ∨ Auth_B`
= "may provide either" — same story.

**Terminal object.** `Authorization::Unchecked`. Anyone can produce
it; it authorizes anything. Soundness hole.

**Initial object.** *Conceptually present, structurally absent.* The
"impossible authorization" that nobody can produce — useful for
*sealed* cells where no one is authorized to act (the cell has been
sealed for archival, say). Today encoded by deleting the cell or
revoking all its capabilities; no first-class shape.

**Subtle dual:** if `Authorization` says "this agent CAN do this
thing," its dual says "this agent CANNOT do this thing." `dregg`
doesn't have a *proof-of-incapacity* shape. See §3.2.

### §1.6. **Witness** — the category of witnesses (proof artifacts)

**Objects.** Witnessed assertions: `(commitment, public_input,
proof_bytes)` triples. A `WitnessedPredicate` is the verifier-side
view; a `Witness` is the prover-side artifact.

**Morphisms.** Witness *refinement* — a witness for a stronger
statement implies (is convertible to) a witness for a weaker
statement. (E.g., a witness for "I have ≥ 10 STARS" is a witness for
"I have ≥ 5 STARS" — provided the verifier accepts the same
commitment.)

**Yoneda-flavored observation.** The category of `WitnessedPredicate`s
is determined entirely by their (commitment, input-type, accept/reject)
behavior under verifier composition. This is why the
`PREDICATE-INVENTORY` unification works — fifteen seemingly-different
witnesses have the same algebraic shape because they have the same
Yoneda profile.

**The functor `Predicate → Witness`.** Every state-predicate over a
*commitment-inside* boundary has a *witness shape* (a proof someone
could produce to satisfy it). Not every state-predicate has a witness
— a *cleartext-inside* predicate is verified by inspection of the
state, with no proof artifact. So the functor is *partial*: defined
on predicates over committed / hidden state, undefined on cleartext.

The *right adjoint* of this functor — given a witness, recover the
predicate it satisfies — exists: `WitnessedPredicate.commitment` plus
`WitnessedPredicate.kind` uniquely identifies the predicate kind. This
is *the* adjunction that the inventory unification exploited.

### §1.7. **Federation** — the category of federations

**Objects.** Federation identities; a federation is a Merkle aggregation
of constituent cell-states plus a committee of authorities.

**Morphisms.** Federation state transitions, which are themselves
Merkle-root advances. Composition is sequential blocklace ordering.

**Key categorical observation per `FEDERATION-AS-CELL.md`.** Federation
is *structurally homomorphic* to Cell along six axes. This means we
have a partial functor `Federation → Cell` (each federation projects
to a "weird big cell") and *its left adjoint* (each cell embeds as a
"committee of one" trivial federation). The adjunction is real —
`FEDERATION-AS-CELL.md §1.10` enumerates it — but neither side is
type-system-explicit yet. The deeper claim of this category-level
view is that the right next move is the **unit / counit of the
adjunction**: the projection cell→fed and embedding fed→cell. These
already exist as code paths; naming them as adjunct functors is the
clarifying win.

### §1.8. **WitnessedReceipt** — the category of receipts (categorified Turns)

**Objects.** Receipts: tuples of `(cell_id, prev_receipt_hash, turn,
post_state_commitment, signature_or_proof)`.

**Morphisms.** Receipt-chain extension: `R_i →_{T} R_{i+1}` where
`R_{i+1}.prev_receipt_hash == hash(R_i)` and `T` is the turn between
them.

**Category structure.** This is a *free category on the cell's Turn
sequence* — a chain. The chain is the *initial algebra of the
"prepend-receipt" endofunctor*: take any receipt-tip and lift it to
its post-receipt-tip. This is the categorical name for what
`WitnessedReceipt::previous_receipt_hash` enforces.

**Functor `Cell → WitnessedReceipt`.** Each cell has a canonical
receipt-chain history. The functor sends `(cell-at-state-s)` to
"chain of receipts terminating at s." This functor is *full and
faithful* assuming a cell's state is fully determined by its
receipt-chain (which it is by chain-IVC reconstruction).

**The cross-cell categorification.** γ.2 binds *pairs* of receipts
from different cells under a single Turn. The category of γ.2-bound
receipt-pairs is a *quotient* of the product category Cell×Cell —
identifying receipt-pairs that share a `(turn_hash, transfer_id)`.
This is the categorical view of bilateral binding: γ.2 is the
*equalizer* (§5.3) of the two projections "this turn from A's view"
vs. "this turn from B's view." That view is generative: every other
γ.2-shaped binding (Grant, Introduce) is the same equalizer, in
different roles.

### §1.9. Summary of the categories

| Category | Objects | Morphisms | Has product? | Has coproduct? | Has initial? | Has terminal? |
|---|---|---|:-:|:-:|:-:|:-:|
| Cell | cell states | effects | partial (federation) | no | yes (empty) | yes (revoked) |
| Effect | effect kinds + refinements | refinement | yes | yes | **no** | yes (Unchecked) |
| Predicate | state predicates | implication | yes (Vec / AND) | yes (AnyOf / OR) | **no** | yes (empty / True) |
| Program | cell programs | sub-program | yes (meet) | yes (join) | yes (reject-all) | yes (accept-all) |
| Authorization | auth modes | attenuation | implicit (Custom) | implicit (Custom) | **no** | yes (Unchecked) |
| Witness | witnessed assertions | refinement | yes (AND-proof) | yes (OR-proof) | **no** | yes (trivial witness) |
| Federation | federation states | Merkle advance | yes | no | yes (empty fed) | yes (sealed fed) |
| WitnessedReceipt | receipts | chain extension | no (per-chain) | no | yes (genesis) | no (live chain) |

Reading the table: **the rows marked "no" for initial object are
candidates for missing duals**. Effect has no "impossible effect"
(no Refusal); Predicate has no `False` (no negation primitive — the
absence of `False` and absence of `Not` are the same hole because
`False = ¬True`); Authorization has no "incapacity" mode (no
Renunciation); Witness has no "impossibility witness" (no proof-of-
non-membership at the algebra level, though there are
construction-specific non-membership proofs).

The next four sections take each cluster.

---

## §2. Existing dualities — what dregg already has

Before naming missing dualities, name the present ones. This catalogs
the dualities that *do* work, so §3's "missing" claims are calibrated
against what's already there.

### §2.1. Issue ↔ Revoke (capability lifecycle)

**Form.** `GrantCapability` mints a cap; `RevokeCapability` retires
it. Together they form an *adjunction-flavored pair*: every grant
admits at most one revocation (modulo the chain-cap structure), and
every active capability has a unique "issue" event.

**Categorical name.** Pair of opposite morphisms in `Effect` —
specifically, *issue* takes (cell, cap-template) to (cell-with-cap),
and *revoke* takes (cell-with-cap) to (cell-without-cap). The
composition issue ∘ revoke = id (when cap unused) and revoke ∘ issue
= id (when revoke is idempotent on already-revoked).

**Strength.** Strong; well-modeled in tree.

**Health.** ✓ Both directions present, both adequately tested.

### §2.2. Sign ↔ Verify (authorization)

**Form.** Producer side: `sign(message, sk) → signature`. Consumer
side: `verify(message, pk, signature) → bool`. This is the
*standard cryptographic adjunction*: sign and verify are the two
halves of a digital-signature primitive.

**Categorical name.** Adjunction between the producer's
"knowledge of secret" category and the verifier's "acceptance"
category. The unit is `pk = derive_public(sk)`; the counit is
`verify(sign(m, sk), pk, m) = true`.

**Strength.** Strong; dregg has Ed25519, BLS, and is wiring
postquantum signature shapes.

**Health.** ✓.

### §2.3. Encrypt ↔ Decrypt (sealing)

**Form.** `seal(plaintext, recipient_pk)` ↔
`unseal(ciphertext, recipient_sk)`. Today: X25519 + ChaCha20 for the
seal/cap-delivery path (`cell::seal`).

**Categorical name.** Adjunction between *sender's knowledge of
plaintext* and *recipient's ability to extract*. Like sign/verify, a
classical cryptographic adjunction.

**Strength.** Strong, modulo: the sealing primitive is X25519, *not*
postquantum (per `BOUNDARIES.md §2.7`). This is a *crypto-primitive*
gap, not a categorical one.

**Health.** ✓ categorically, △ post-quantum.

### §2.4. Commit ↔ Open (commitments)

**Form.** `commit(value, blinding) → commitment` ↔
`open(commitment, value, blinding) → bool`. Pedersen commitments and
their proof structure (`cell::value_commitment`).

**Categorical name.** Adjunction between *prover's full knowledge* and
*verifier's reduced acceptance*. The hiding property (commitment
reveals nothing about value) plus the binding property (a commitment
opens to at most one value) is what makes this an adjunction in the
information-theoretic sense.

**Strength.** Strong.

**Health.** ✓.

### §2.5. Conjunction (Vec) ↔ Disjunction (AnyOf)

**Form.** `Vec<StateConstraint>` is implicit conjunction; every
constraint must accept. `StateConstraint::AnyOf(Vec<...>)` is single-
level disjunction; any variant accepts.

**Categorical name.** Product / coproduct in `Predicate`. The
universal property: a transition is admitted by `Vec<P>` iff it is
admitted by each `P_i`; admitted by `AnyOf(Vec<P>)` iff by some `P_i`.

**Strength.** Strong as a pair. But: **`AnyOf` is single-level only**
(per `SLOT-CAVEATS-EVALUATION.md` Finding 4). This is a *depth limit*,
not a missing dual — and it's documented. A future cleanup is to make
`AnyOf` recursive, after which conjunction and disjunction would be
truly dual.

**Health.** ✓ as a duality, △ depth-bound on disjunction side.

### §2.6. Sender ↔ Receiver (γ.2 bilateral)

**Form.** γ.2 Phase 1 binds the sender's projection of a Transfer to
the receiver's projection. Sender sees `direction=1, peer=receiver`;
receiver sees `direction=0, peer=sender`. The canonical `transfer_id`
makes them resolvable to the same effect.

**Categorical name.** *Equalizer* of two projections. Given the
canonical `effect_id`, the two per-cell views factor through a single
universal "this is the bilateral effect" object. The cross-cell join
is the equalizer arrow; the matching is the universal property.

**Strength.** Strong. This is the cleanest categorical structure in
the cross-cell substrate.

**Health.** ✓.

### §2.7. Cell ↔ Federation (six-axis homomorphism)

**Form.** Per `FEDERATION-AS-CELL.md`, six of nine axes are strongly
homomorphic between cell and federation. Two are weakly homomorphic
(state shape, nonce shape) and one is asymmetric (`peer_exchange`
analog absent on federation side).

**Categorical name.** Adjunction Cell ⊣ Federation: federation as the
right adjoint (the "wrap a cell in a committee of one") of the cell
abstraction, embedding being the left adjoint (the "treat a federation
as a weird big cell"). The asymmetric axis — `peer_exchange` on cells
but no direct federation handshake — corresponds to a *failure of the
adjunction's full naturality on that axis*. See §4.2 for the
implication.

**Strength.** Six axes strong, two weak, one asymmetric.

**Health.** △ — the asymmetric axis (cross-fed direct handshake)
points at a real missing surface that `FEDERATION-AS-CELL.md §1.9`
already flags.

### §2.8. Cleartext ↔ Commitment ↔ Acceptance ↔ Out-of-band (BOUNDARIES four-fold)

**Form.** `BOUNDARIES.md §5` proposes a four-fold boundary vocabulary:
who is *inside* under which knowledge regime. This is *not* a single
duality but a *square* — every datum has a position in a 2x2 grid of
(direct knowledge ↔ surrogate knowledge) and (positive observation ↔
negative observation).

**Categorical name.** The four boundary classes form a *poset* with
relations:
- cleartext-inside `≥` commitment-inside (knowing the value implies
  knowing the commitment).
- cleartext-inside `≥` acceptance-inside (knowing the value lets you
  decide acceptance).
- commitment-inside `?` acceptance-inside (incomparable in general —
  knowing the commitment doesn't imply ability to decide acceptance
  without the proof; knowing acceptance doesn't imply the
  commitment is known to *you*).

This poset is a *bounded lattice*: out-of-band is the bottom (knows
nothing), cleartext-inside is the top (knows everything).

**Strength.** Strong as a poset; explicitly documented.

**Health.** ✓ as a structure; △ as an enforced invariant (the audit
notes that dregg's *use* of this lattice is inconsistent; some
predicates leak across boundaries by surprise).

### §2.9. Summary of existing dualities

| Duality | Type | Strength | Codified? |
|---|---|---|---|
| Issue / Revoke | adjunction in Effect | strong | yes |
| Sign / Verify | crypto adjunction | strong | yes |
| Encrypt / Decrypt | crypto adjunction | strong (mod PQ) | yes |
| Commit / Open | commitment adjunction | strong | yes |
| Conjunction / Disjunction | product/coproduct in Predicate | strong (depth-bound) | partial |
| Sender / Receiver (γ.2) | equalizer in Cell pairs | strong | yes |
| Cell / Federation | adjunction (6/9 axes) | strong (where present) | study only |
| BOUNDARIES four-fold | bounded poset | strong | study only |

The rows marked "study only" point at architectural commitments not
yet realized in code. The rows marked "yes" are realized.

This catalog calibrates §3: we *do* have a lot of dualities. The
question is which ones are *missing* in a way that hurts.

---

## §3. Missing duals — the asymmetries that suggest real holes

Here is where the categorical method earns its keep. We walk the rows
where one side of a dual is present and the other is absent (or
implicit), and ask: does the missing side correspond to a real app
need?

### §3.1. Negation (¬P) and implication (P ⇒ Q) in StateConstraint

**The asymmetry.** Predicate has conjunction (implicit Vec) and
disjunction (AnyOf). It does *not* have negation. It does not have
implication. These are *the* two operators that turn a Boolean
algebra (or a Heyting algebra) into something compositionally
complete. Without negation, `Predicate` is *just* the
{∧, ∨, True}-fragment — a distributive lattice, not a Heyting algebra.

**Why it matters categorically.** A distributive lattice is *almost*
a Heyting algebra; the missing piece is exactly the implication
operation. With implication, every pair of predicates `(P, Q)`
admits a *largest predicate `P → Q`* such that `P ∧ (P → Q) → Q`.
This is the *exponential object* — the categorical name for "function
between predicates."

**Why it matters in dregg.** Three concrete app surfaces want this:

1. **Conditional escrow.** "Release iff (deadline passed) ⇒
   (counterparty did NOT publish proof of fulfillment)." Today
   this is hand-rolled in `apps/gallery` settlement logic; it
   structurally wants `Implies(deadline_predicate,
   Not(counterparty_proof))`.

2. **Anti-double-spend.** A nullifier check is *non-membership*: the
   predicate is `¬(nullifier ∈ spent_set)`. Today this is a
   bespoke `BridgedNullifierSet` (`cell::note_bridge:243`) with
   ad-hoc "is not in" semantics. There is a real
   `circuit::non_membership` AIR. But there's no *slot-caveat
   surface* that says `StateConstraint::Not(MemberOf { ... })`. The
   AIR exists; the predicate-level invocation doesn't.

3. **Default authorization with overrides.** "Authorize if
   (default rule applies) AND NOT (override applies)." Macaroon-
   style attenuation has this implicitly; slot caveats can't say it.

**Why it matters compositionally.** The biggest categorical win of
adding `Not` and `Implies` is that **conjunction-of-positives stops
being the only structural form**. Today, any "this thing is
forbidden" predicate has to be encoded as "the slot doesn't equal
the forbidden value" via `FieldEquals` or similar; the absence of a
general `Not` means every forbidden-thing rule is a special-case
positive predicate, not a structural negation.

**Implementation reading.** `Not` is *cheap* to add at the
`StateConstraint` level — evaluator flips the boolean. The AIR side
is where it bites: a STARK that enforces `¬P` requires either
- (a) negation in the constraint polynomial layer (some kinds support
  this trivially: `FieldEquals` ↔ `FieldNotEquals` is sign-flip),
- (b) general non-membership / disjointness arguments (the
  `non_membership` gadget), or
- (c) encoded as the dual: `Not(MemberOf(set))` ↔
  `MemberOf(complement_set)` *only when the set is small enough*.

Each is doable; the question is the slot-caveat-layer ergonomics.
The honest engineering call: add `StateConstraint::Not(Box<...>)`
where the inner is a *restricted* subset of simple constraints
(FieldEquals → FieldNotEquals; FieldGte → FieldLt; MerkleMember →
NonMember), with explicit unsupported inner forms returning a clear
typecheck error.

**Verdict on this missing dual.** *Real, with app demand.* Prototype.

### §3.2. Renunciation — proof-of-non-holding (Authorization dual)

**The asymmetry.** `Authorization::*` proves the agent *has* the
right to act. There is no `Renunciation::*` that proves the agent
*does not have* a particular capability — i.e., a verifiable
attestation of incapacity.

**Why it matters categorically.** This is the categorical dual of
`Authorization`: the initial object in the Authorization category
(§1.5). If `Authorization::Unchecked` is terminal (everyone has it),
`Renunciation::TotalLackOfCapability` would be initial (nobody can
forge it for someone else; only the agent themselves can produce
it for themselves).

The shape is: given a capability `c` and a holder `h`, produce a
proof "`h does not hold c at time t`." This is *not* the same as
"`c is revoked`" (which is a global property); it's a *per-holder*
property. Two main shapes:
- **Proof of non-membership in c-list.** Given the holder's
  capability-list Merkle root, prove `c` is not in it.
- **Time-bound renunciation.** Given a holder's signed declaration
  "I renounce all caps under selector `s` at time `t`," carry the
  signature forward.

**Why it matters in dregg.** Three potential app surfaces:

1. **Recusal in governance.** "I attest I do not hold a conflicting
   interest cap before voting on this proposal." Today: cleartext
   attestation in `apps/governed-namespace`. With Renunciation:
   structural proof.

2. **Compliance attestation.** "This cell can prove it has not
   received any caps of effect-class `bridge_mint` in the last
   30 days." Today: not expressible. With Renunciation +
   temporal: structural.

3. **Selective non-disclosure.** A cell wants to prove "I do not
   currently hold a capability for resource X" while not revealing
   what caps it *does* hold. The blinded-set non-membership shape
   already exists at the AIR layer (`circuit::non_membership`);
   wiring it into a `Renunciation` variant of `Authorization` is
   surface work.

**Why it might not matter in practice.** Most of the app demand can
be encoded as `Authorization::Custom { predicate:
WitnessedPredicate { kind: BlindedMembership, ... non-membership
proof } }`. The thing that's *missing* is the structural separation
between "I prove I have authority" and "I prove I lack authority."
For audit clarity, these probably want to be distinct variants. For
implementation, they share the gadget.

**Verdict on this missing dual.** *Real but small.* The app demand is
real (governance recusal, compliance attestation), but the existing
machinery (custom predicate with blinded non-membership) can carry
the load. Defer until an app forces the separation.

### §3.3. Refusal / NoOp — proof-of-non-action (Effect dual)

**The asymmetry.** `Effect::*` records something happening.
There is no `Effect::Refusal { reason_hash }` that records a deliberate,
auditable *non-action*. The "effect-of-not-acting" today is *implicit
in the absence of a turn* — which is not provable.

**Why it matters categorically.** Effect's missing initial object
(§1.2 table). If `Effect::Unchecked` is terminal (anything can be
under it), `Effect::Refusal` would be a structural witness of "no
effect was taken, deliberately."

The shape: a turn that touches a cell *only to record that the cell
refused some pending action*, with a hash of the reason. The cell's
state advances (nonce bumps; an `attempted_actions` log slot
appends; an `action_outcome` slot records "REFUSED:reason_hash"),
but no value, capability, or property changes.

**Why it matters in dregg.** Two surfaces:

1. **Auditable rejection in HFT-style flows.** "I received an order;
   I declined to fill; here is the proof that I declined and the
   reason." Without Refusal: the absence of a fill is unprovable
   (silence is indistinguishable from outage). With Refusal:
   structural.

2. **Permission denial as evidence.** "I rejected this turn proposal
   because the authorization predicate didn't satisfy." Currently
   the executor emits a `TurnError::*` that is *not* a structural
   artifact; it's a runtime error. A Refusal would lift this to a
   first-class artifact.

**Why it might not matter.** "Provable non-action" is a niche
requirement; most apps don't need it. The categorical pressure for
its existence (initial object in Effect) is mostly aesthetic. The
practical app cases above can be encoded as a `Custom` effect that
mutates an "audit log" slot.

**Verdict on this missing dual.** *Categorical curiosity with thin
app demand.* Defer; flag for when an HFT or compliance app forces it.

### §3.4. WitnessProducer — the dual of WitnessedPredicate

**The asymmetry.** `WitnessedPredicate` is the *consumer* side: given
a `(commitment, input, proof)` triple, accept-or-reject. There is no
named *producer* shape — the API for *constructing* such a triple from
a witness.

**Why it matters categorically.** Adjunctions need both functors.
`WitnessedPredicate` is the *forgetful* functor (given a full witness,
forget everything except the verification surface). The *free*
functor going the other direction — given a verification requirement,
exhibit the witness that satisfies it — exists as code in
every prover (`circuit::*` provers), but there is no *trait* surface
for "given a `WitnessedPredicateKind`, construct a witness."

**Why it matters in dregg.** Most of the prover-side code is hand-
rolled per kind: `BridgePredicateProof::new`,
`PortableNoteProof::from_witness`, `BlindedMerkleStarkAir::prove`,
etc. Each has its own witness type, error type, parameter shape. A
`WitnessProducer` trait — mirror image of `WitnessedPredicateVerifier`
from `PREDICATE-INVENTORY.md §3.3` — would:

```rust
pub trait WitnessProducer: Send + Sync {
    type Witness;
    fn produce(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        witness: &Self::Witness,
    ) -> Result<Vec<u8>, ProverError>;
    fn kind(&self) -> WitnessedPredicateKind;
}
```

The registry symmetry — every kind has both a verifier and a producer,
keyed by `WitnessedPredicateKind` — gives a clean *adjunction* between
prover-side and verifier-side. This is the categorical structure
implicit in every prove/verify pair.

**Why it matters in practice.** Audit clarity and SDK ergonomics.
With a unified producer surface, the SDK can synthesize the proof for
any registered predicate kind. Today's SDK has bespoke methods per
kind; the unification halves the API surface.

**Verdict on this missing dual.** *Real but not algebraically deep.*
This is *already half-implemented* — every prover effectively
implements this trait shape ad hoc. The win is *naming* it. Add the
trait; let existing provers implement it; no new gadgets. ~1
afternoon of work to land.

### §3.5. Unilateral binding — single-cell self-attestation as dual of γ.2 bilateral

**The asymmetry.** γ.2 Phase 1 binds *pairs* of cells (Transfer,
Grant) and *triples* (Introduce). There is no *unilateral* binding —
a structural primitive for "this single cell attests to a property
over its own state-transitions across multiple turns" *with the same
algebraic rigor as the bilateral case*.

**Why it matters categorically.** γ.2's bilateral binding is a 2-arity
construction; the trilateral Introduce is 3-arity. The natural
"missing" arity is 1 — and the dual of "a pair of cells co-attest" is
"a single cell self-attests."

The shape: a `StateConstraint::UnilateralBinding { slot, sequence_
property }` that says "across the cell's last `n` turns, the values
in slot `i` satisfy property `P`." This is *structurally* the temporal
predicate (`TemporalPredicateAir`) — but lifted to a γ.2-shaped public
input layout so the verifier loop treats it uniformly with the
bilateral case.

**Why it matters in dregg.** The temporal predicate exists
(`circuit::temporal_predicate_dsl`); its public inputs include
`threshold`, `num_steps`, and `(initial, final)` state roots. But its
*PI layout is custom* to the temporal AIR. A unilateral binding would
say: extend γ.2's PI scheme to include
`UNILATERAL_BINDING_ROOT` slots with a per-cell accumulator over
"self-attested temporal properties," dual to the
`OUTGOING_TRANSFER_ROOT` accumulator.

The benefit: the same verifier loop that walks γ.2's bilateral
accumulators can walk unilateral accumulators. Two flavors of
"this cell published structural evidence of a property" become
algebraically uniform.

**Why it matters in practice.** Three surfaces:

1. **Self-attested rate-limit compliance.** "Across my last 100
   turns, no slot moved by more than 10 per turn." Currently the
   temporal predicate AIR can prove this, but the cell's
   `WitnessedReceipt` doesn't carry a structural binding to that
   proof at the PI layer.

2. **Cross-turn invariant attestation.** "I am the cell `c`, and I
   attest to the verifier that my receipt-chain in the last `n`
   turns satisfies invariant `I`." Today: hand-rolled witness;
   the proof rides as an external blob.

3. **Sovereign cells.** A sovereign cell (`SOVEREIGN-WITNESS-AIR-
   DESIGN.md`) is *specifically* this pattern: a cell that proves
   things about its own history without federation mediation.
   Today the sovereign-witness AIR is its own circuit; lifting it
   to a unilateral-binding PI shape would make it compose with γ.2
   bilateral bindings in the same verifier loop.

**Verdict on this missing dual.** *Real, with significant app demand.*
The bilateral / trilateral / unilateral trio is a structural family;
the absence of unilateral is a real asymmetry. Sovereign cells are
the concrete app driver. Prototype.

### §3.6. Summary of missing-dual analysis

| Missing dual | Categorical role | App demand | Verdict |
|---|---|---|---|
| `Not(P)` / `Implies(P, Q)` in StateConstraint | initial object + exponential in Predicate | escrow, nullifier, anti-permission | **Prototype** |
| Renunciation (proof-of-non-holding) | initial object in Authorization | governance recusal, compliance | Defer |
| Refusal / NoOp in Effect | initial object in Effect | HFT decline, compliance | Defer |
| `WitnessProducer` trait | left adjoint of `WitnessedPredicateVerifier` | SDK clarity | **Land** (~1 day) |
| Unilateral binding (γ.2 1-arity) | 1-arity sibling of bilateral / trilateral | sovereign cells, self-attest | **Prototype** |

Three "prototype-or-land" items emerge: `Not / Implies` at the
predicate layer, `WitnessProducer` as a producer-side trait surface,
and unilateral γ.2 as a structural extension of the binding family.

---

## §4. Adjunctions — opposite functors

A *duality* is a single pair; an *adjunction* is a richer structure
where two functors `F: C → D` and `G: D → C` are connected by a
natural correspondence `Hom(F(c), d) ≅ Hom(c, G(d))`. Adjunctions
encode "this thing is *free*" / "this thing is *forgetful*" pairs
across systems.

`dregg` has several near-adjunctions, partially realized.

### §4.1. Predicate ⊣ Witness — free / forgetful

**Statement.** The *forgetful* functor `W: Witness → Predicate`
sends a witness `(commitment, input, proof)` to the predicate it
verifies (the predicate is determined by `commitment` plus
`WitnessedPredicateKind`). The *free* functor `F: Predicate →
Witness` sends a predicate to "the smallest witness shape that
satisfies it" — i.e., a witness-shape spec keyed by the predicate's
commitment.

**Adjunction.** `Hom_Witness(F(P), W) ≅ Hom_Predicate(P, W(W))`
should hold: given a predicate `P` and a witness `W`, the morphisms
"this free witness for P factors through W" correspond to morphisms
"P is implied by what W proves."

**Status in dregg.** Half-realized.
`WitnessedPredicateVerifier` is `W`. There is no named `F`
(prover-side trait). §3.4's `WitnessProducer` proposal *is* this
free functor.

**Win.** Naming this adjunction makes the unification of the
prover-side (today's bespoke provers per kind) the obvious next
move. The adjunction is *real* — the prover and verifier are inverse
where they meet — but its naming buys the structural clarity that
SDK refactor work would otherwise discover ad hoc.

**Action.** Add `WitnessProducer` trait per §3.4. Document the
adjunction.

### §4.2. Cell ⊣ Federation — committee-of-one / Merkle-aggregation

**Statement.** The *embedding* functor `E: Cell → Federation` sends
a cell to its "trivial federation" (committee of one over its
owning key). The *projection* functor `P: Federation → Cell` sends a
federation to its "summary cell" view (Merkle-aggregated state
commitment as a cell-state-commitment).

**Adjunction.** `Hom_Federation(E(c), F) ≅ Hom_Cell(c, P(F))`: a
federation-level morphism from `c`-as-fed to `F` corresponds to a
cell-level morphism from `c` to `F`-as-cell.

**Status in dregg.** Six of nine axes strongly homomorphic per
`FEDERATION-AS-CELL.md §1`. The functors are real but not type-
system-explicit. The asymmetric axis (`peer_exchange` for cells with
no federation analog) is *exactly* the place the adjunction's
naturality fails: there's a cell-side morphism (peer-exchange
transition) that has no federation-side image.

**Win.** Naming the adjunction makes the asymmetric axis a
structural finding rather than a coincidence. The
`FEDERATION-AS-CELL.md §1.9` recommendation — *add a cross-fed
direct handshake* — is the act of *restoring the adjunction's
naturality*. The categorical name for what we want is "the
left-adjoint of the federation-projection functor needs to be full
and faithful on the peer-exchange axis."

**Action.** Per the prior `FEDERATION-AS-CELL.md §9` recommendation:
add cross-fed direct attested-root handshake. The categorical
framing is the *reason* this is the right move (not just "by
analogy").

### §4.3. Local ⊣ Global — single-cell PIs ↔ bilateral PIs

**Statement.** γ.2's `outgoing_*_root` and `incoming_*_root`
accumulators are the *unit* and *counit* of an adjunction between
"the per-cell view of an effect" and "the cross-cell view."

Formally: the *local* functor `L: BilateralEffect → PerCellView`
projects a bilateral effect to its single-cell view from each
side. The *global* functor `G: PerCellView → BilateralEffect`
canonicalizes a per-cell view back to the bilateral effect (via
the canonical `transfer_id` / `grant_id` / `intro_id`).

**Adjunction.** `Hom_PerCellView(L(e), v) ≅ Hom_BilateralEffect(e, G(v))`:
"this per-cell view comes from this bilateral effect" corresponds
to "this bilateral effect projects to this per-cell view."

**Status in dregg.** Realized in γ.2 Phase 1. The `transfer_id`
derivation `H("dregg-transfer-id-v1", from, to, amount, nonce)` is
*literally* the universal arrow for the equalizer formed by
`L_from` and `L_to`. The cross-cell match loop in the verifier is
*precisely* checking the adjunction's coherence.

**Win.** This is the cleanest categorical structure dregg has, and
it's already realized. The naming clarifies *why* γ.2 works: it
makes the equalizer / adjunction explicit.

**Implication for the unilateral-binding proposal (§3.5):** the
unilateral case would be the *trivial* (1-arity) version of this
same adjunction. The per-cell view *is* the global view (no other
party). This is consistent with the proposal that unilateral
bindings are the 1-arity sibling of bilateral.

### §4.4. Receipt-chain ⊣ State-snapshot

**Statement.** Every cell's `WitnessedReceipt` chain is the
*history-functor* applied to the cell's state-snapshot. The
*forgetful* functor `S: ReceiptChain → State` sends a chain to its
current state-tip. The *free* functor `R: State → ReceiptChain`
sends a state to "the canonical receipt chain that produced it"
(reconstructed via chain-IVC).

**Adjunction.** `Hom_ReceiptChain(R(s), c) ≅ Hom_State(s, S(c))`:
"this canonical chain leads to this received chain" iff "this
state is reachable from this chain's tip-state."

**Status in dregg.** Half-realized — the *forgetful* is trivial
(`chain.tip().state`); the *free* is `WitnessedReceipt`-scope-2
replay (`turn::witnessed_receipt`), which constructs the canonical
chain from a state-tip. The chain-IVC direction
(`STAGE-7-PLUS-DESIGN.md`) is the categorical realization of this
free functor.

**Win.** Chain-IVC is the *categorical completion* of this
adjunction. Naming the adjunction makes chain-IVC the structural
next step, not an ad-hoc engineering choice.

**Action.** No new code suggested by the naming; the action is
already in flight via `STAGE-7-PLUS-DESIGN.md`. But the categorical
framing answers "why chain-IVC" — *because it completes the
state/history adjunction*.

### §4.5. Summary

| Adjunction | Status | Action |
|---|---|---|
| Predicate ⊣ Witness | half-realized (verifier only) | Add `WitnessProducer` (§3.4) |
| Cell ⊣ Federation | 6/9 axes strong; 1 asymmetric | Cross-fed handshake (per `FED-AS-CELL`) |
| Local ⊣ Global (γ.2) | fully realized | Document; extend with unilateral (§3.5) |
| Receipt-chain ⊣ State | half-realized | Chain-IVC (per `STAGE-7-PLUS`) |

---

## §5. Limits and colimits — cross-cell aggregation

Limits (products, pullbacks, equalizers) and colimits (coproducts,
pushouts, coequalizers) are the categorical generalizations of
"intersection" and "union" operations. They are the natural language
for *aggregation*.

This section walks the structurally-interesting cross-cell aggregation
shapes, names them, and asks which are present and which are missing.

### §5.1. Pullback — "two transitions over a shared resource"

**Form.** Given morphisms `f: A → C` and `g: B → C` (both ending at
`C`), the pullback `A ×_C B` is the *largest object* that fits into a
commuting square mapping back to both `A` and `B` and forward to `C`.

**`dregg` realization.** This is *exactly what γ.2 already computes
algebraically.* When two cells transition such that both transitions
must be consistent over a shared resource (e.g., the canonical
`transfer_id`), the resulting bilateral binding is the pullback of
the two transitions over the canonical `effect_id`:

```
sender_cell × bilateral_effect × receiver_cell
       \             |              /
        L_sender    L_id        L_receiver
              \      |        /
               \     |       /
              canonical_effect_id
```

The `outgoing_transfer_root` / `incoming_transfer_root` accumulators
plus the verifier's match-loop are *the pullback's universal arrow*
— "every per-cell view of this effect factors through the canonical
id."

**Strength.** Strong; already in tree. γ.2 Phase 1 *is* the pullback
construction.

**Health.** ✓.

### §5.2. Pushout — "smallest combined state that two transitions both factor through"

**Form.** Given morphisms `f: C → A` and `g: C → B` (both starting at
`C`), the pushout `A +_C B` is the *smallest object* that fits into a
commuting square mapping forward from both `A` and `B` and back from
`C`.

**`dregg` question.** Is there a pushout-shaped construction for
cross-cell coordination?

**Candidate scenarios where this would apply:**

1. **Multi-party atomic aggregation** (the proposal we *don't*
   want: `Effect::MultilateralAtomic` per `CROSS-CELL-COORDINATION.md
   §6.1`). The pushout shape says: given two pairwise effects
   sharing a common starting point (e.g., both originating from a
   matchmaker's intent dispatch), there's a *combined effect-object*
   that universally factors both. This is structurally the *coupled
   atomic action* shape.

2. **Delegation chain combination.** Given two grants `c → A` and `c
   → B` from the same source, the pushout would be "the combined
   delegation tree rooted at `c`." This is structurally what
   *capability cascades* (`captp::handoff` chains) already realize
   informally.

3. **Cross-federation handshake fusion.** Given two attested roots
   `f_a → r` and `f_b → r` sharing a destination, the pushout
   would be "the combined cross-fed attestation." Today this is
   per-federation; a pushout-shape would let two source federations
   co-attest a destination event.

**Status in dregg.** *Absent at the algebra layer.* The closest in-tree
construction is `intent::trustless::SealedTurn` (matchmaker fuses
counterparty intents), but it operates at the intent layer, not the
cross-cell-binding layer.

**Categorical reading.** Pushouts are *colimits of spans*. They are
the "smallest combined" construction; the dual of pullbacks. If dregg
has pullbacks (γ.2) and no pushouts, **the category is incomplete
for colimits**. The categorical pressure is to *add* a pushout-shaped
primitive. But the prior `CROSS-CELL-COORDINATION.md` analysis
explicitly *rejects* the multilateral atomic effect.

**Resolution.** The pushout pressure is real, but the prior
recommendation — "the call_forest IS the multilateral witness" — is a
*pushout encoding*, not a pushout absence. The call_forest declares
"these N effects all originate from this shared turn"; the per-cell
accumulators each factor through the call_forest. The call_forest is
the *colimit object* of the N pairwise edges sharing the turn's
origin.

This is fine, but the categorical lens suggests *making it explicit*.
Specifically: `Turn::call_forest` could be re-typed to indicate it's
the pushout-of-effects-sharing-a-turn. The pushout's universal
property — "every cross-cell coordination over this turn factors
through the call_forest" — is already what makes the verifier work.
Naming it pushout makes it composable with future cross-turn
coordinations.

**Verdict.** Pushout structure is *implicit* in `Turn::call_forest`.
Naming win, not new-primitive win. *Documentation, not code.*

### §5.3. Equalizer — "states where two morphisms agree"

**Form.** Given two parallel morphisms `f, g: A → B`, the equalizer
is the *largest sub-object* of `A` on which `f` and `g` agree.

**`dregg` realization.**

1. **γ.2 bilateral binding as equalizer.** §1.8 already named this:
   given two projections of a bilateral effect ("from sender's
   view," "from receiver's view"), the equalizer is the canonical
   `effect_id` that both views factor through. The equalizer
   *arrow* is "compute the canonical id from your local data and
   require it match the peer's."

2. **`peer_exchange` as equalizer.** Given Alice's and Bob's signed
   state transitions, the equalizer is the joint state-pair where
   their views agree on the transition's effects. The PeerStateTransition's
   signature plus continuity check *is* the equalizer arrow.

3. **Intent matching as equalizer.** Given two opposing intents
   (Alice wants X for Y; Bob wants Y for X), the equalizer is the
   set of price/quantity pairs they agree on. `intent::matcher::
   MatchSpec` realizes this.

**Equalizer's missing dual — coequalizer.** *Coequalizer is the
quotient where `f` and `g`'s outputs are identified.* In dregg terms:
given two divergent state-paths, the coequalizer is the "agreed-upon
identification" that makes them equivalent.

This is exactly what **ring trades** need:

> Given N cells with N transfers forming a ring, the coequalizer is
> the *cycle-closure identification* — "after this ring fires, the
> net result is no value flow at all, modulo the rate of trade."

Today: ring closure is checked *implicitly* per-cell-balance in the
executor's effect-apply step. There is no *first-class artifact* that
attests "this ring closes." A coequalizer primitive would be:

```rust
/// Attests that a set of bilateral transfers forms a closed cycle.
/// Verifier checks: every outflow is matched by an inflow in the cycle,
/// modulo a single canonical "value-equivalence" relation.
struct RingClosureAttestation {
    /// Canonical hash of the cycle's leg-set, order-independent.
    cycle_id: [u8; 32],
    /// Roots of the per-cell accumulators, one per participant.
    /// Ordering matches the call_forest's leg order.
    leg_roots: Vec<[u8; 32]>,
    /// Optional: per-leg value-equivalence witness (e.g., price proof).
    value_proofs: Vec<Option<WitnessedPredicate>>,
}
```

**Verdict on coequalizer.** *Real ergonomic win, prototype.* This is
what `CROSS-CELL-COORDINATION.md §2.3` flagged: "if we wanted 'the
ring closed atomically' to be an algebraically-bound property in PI,
we would add a custom `closure_id` that all N legs share." The
categorical name for this is *coequalizer of the N legs identifying
their cycle*. Doing the implementation as a DSL macro (per the prior
doc's §7.2) is the right path; the categorical framing makes it
explicit *what's being added*.

### §5.4. Initial / terminal objects across categories

We tabulated these in §1.9. The interesting missing initials —
Predicate-False (§3.1), Effect-Refusal (§3.3), Authorization-
Renunciation (§3.2) — are the missing-dual candidates already
analyzed.

### §5.5. Summary of limits / colimits

| Construction | Status in dregg | App-driven? |
|---|---|---|
| Pullback (intersection of effects over shared resource) | ✓ realized (γ.2) | yes |
| Pushout (combination of effects sharing origin) | implicit (`call_forest`) | naming win only |
| Equalizer (states where morphisms agree) | ✓ realized (γ.2, intent match) | yes |
| Coequalizer (quotient where outcomes identified) | **absent at algebra**; ring-trade need | **Prototype** |
| Initial in Predicate (False / Not) | absent (§3.1) | **Prototype** |
| Initial in Effect (Refusal) | absent (§3.3) | Defer |
| Initial in Authorization (Renunciation) | absent (§3.2) | Defer |

One real prototype emerges: *coequalizer-of-ring-closure*. This is
new structural content not surfaced by the use-case-enumeration
method.

---

## §6. Recursive / fixpoint structure — γ.2 as initial algebra

γ.2 binds *pairs* and *triples*. Recursion makes the binding a
*fold*. This section names the categorical structure that γ.2's
recursive composition is converging toward.

### §6.1. The cross-cell binding endofunctor

**Define** `F: SetOfCells → SetOfCells` as: `F(X) = X + (X × X) + (X
× X × X)`. This is "a set of cells, plus pairs (bilateral
bindings), plus triples (trilateral)."

A `Turn` produces an `F(X)`-structure — a list of effects, each of
which is a `0|1|2|3`-arity binding over the touched cells. The
verifier's accumulator walk consumes this structure.

### §6.2. Initial F-algebra

**Form.** The *initial F-algebra* is the smallest set `Y` with a
map `F(Y) → Y` such that any other F-algebra factors through it.
For dregg's γ.2 functor, the initial algebra is *the set of
turn-accumulator trees* — finite trees whose nodes are γ.2 bindings
of arity 0, 1, 2, or 3.

**Why this matters.** Initial algebras are *the categorical name for
recursive folds*. Every γ.2-shaped multi-turn aggregation
(`STAGE-7-GAMMA-2-PHASE-2-SKETCH.md`'s outer aggregation AIR) is a
*catamorphism over the initial F-algebra* — the structural recursion
that the outer aggregation realizes.

**What it surfaces.** The natural extension of γ.2 to multi-turn
aggregation is *the catamorphism that folds turn-trees to a single
attested root*. This is what the outer aggregation AIR does. Naming
it "catamorphism over initial F-algebra" makes the structural reason
clear: *any* fold over bilateral + trilateral + unilateral effects
*must* factor through this initial algebra.

**Implication for the missing unilateral arity (§3.5).** If
unilateral is the 1-arity branch of the binding functor, the
initial F-algebra *naturally* includes it. The fact that today's
γ.2 has 2-arity and 3-arity branches but no 1-arity branch makes the
initial algebra *partial* — there are turn-tree shapes that should
exist but don't. **This is the categorical reason §3.5's unilateral
binding is structurally motivated**.

### §6.2.1. The trivial 0-arity branch

The functor `F(X) = X + (X × X) + (X × X × X)` includes an `X`
summand for the *trivial* 0-arity branch — a binding "this cell
participated in the turn without any cross-cell effect." This is
already covered today (a cell can be touched without any γ.2-shaped
effect — e.g., the cell only mutates its own slots without any
bilateral edges). The 0-arity branch is *implicitly* there.

### §6.3. The Y combinator analogy

The brief asked: "γ.2 binds pairs; recursion makes the binding into
a fold. The Y combinator of cross-cell aggregation. What's the
categorical name?"

The categorical name is **catamorphism**, and the *fixed-point
operator* is the initial-algebra construction.

The Y combinator's role in untyped lambda calculus — exhibit the
fixed point of an arbitrary functional — is *exactly* what the
initial-algebra construction does for an endofunctor: it gives the
*type-level* fixed point of `F` (the smallest type closed under
`F`'s action).

The dregg realization: the verifier's recursive walk over a turn's
accumulator structure is a catamorphism; the *signature* of that
catamorphism is `F(accumulator_state) → accumulator_state`, and the
initial F-algebra is the type that universally encodes all such
recursive walks.

This naming buys nothing immediately, but it's the right anchor for
future *chain-IVC over cross-cell aggregation* work: chain-IVC is
the *iterated catamorphism* over the initial F-algebra applied
turn-by-turn.

### §6.4. Verdict

The recursive structure is *latent and consistent* with γ.2's
current design. The missing pieces are:
- The 1-arity branch (unilateral) — §3.5 reproposed.
- Explicit naming of the outer-aggregation AIR as a catamorphism
  over `F` — documentation win.

Neither is new work; both are *clarifying naming*.

---

## §7. Monads — what structures dregg?

Monads are the categorical name for sequencing-with-effects: a monad
`M` packages a type `X` into `M(X)` such that you can sequence
computations on `M(X)`. Several patterns in dregg are monadic; this
section names them.

### §7.1. The capability monad — actions with possible authorization failure

**Form.** Wrap an action `A` in `Cap(A)` = "an action that, when
executed, either authorizes-and-runs or fails-authorization." `return
a = Cap.Authorized(a)`; `bind (Cap.Auth(a)) f = f(a) | Cap.Denied`.

**Categorical name.** The *Maybe / Option monad*, with `Some` =
"authorization succeeded" and `None` = "authorization failed."

**`dregg` realization.** `Result<Action, AuthorizationError>` is the
naive form. The richer form — where the failure carries a *witness
of why* — is the *Either monad* with the left side being a structured
error type.

**Implication.** The monadic bind operation has a *natural shape*
for sequenced authorizations: "authorize this, then authorize that,
then run." Today this is hand-rolled in the executor. A first-class
monadic surface for this would clean up multi-step auth flows.

**Missing operation surfaced.** The monad's *algebra* suggests a
`Cap.either(a, b)` operator — try `a`'s auth; if it fails, try `b`'s.
This is the *coproduct* in the capability monad (§1.5's missing
coproduct). It's expressible today only via `Authorization::Custom`
with hand-rolled disjunction logic. **Naming it as monadic alternative
suggests `Authorization::OneOf(Vec<Authorization>)` would be a
natural first-class form.**

### §7.2. The state monad — cells are stateful

**Form.** A cell's transition is `(old_state, action) → (new_state,
output)`. This is *literally* the state monad with `State =
CellState`, returning the action's effect-application.

**Categorical name.** The State monad `S → (X, S)`.

**`dregg` realization.** `cell::program::TransitionCase::body` plus the
executor's effect-application loop *is* the state monad's bind. The
DSL's `#[dregg_caveat]` lowering is the *category-theoretic do-notation*
for the state monad.

**Missing operation.** Monadic *transformers* — combining state with
another monad. The combination "state + writer + reader" is exactly
what an effect VM is. The DSL's effect VM (`circuit::effect_vm`) is a
state-monad-transformer stack realized in trace columns. Naming it
clarifies the design.

### §7.3. The writer monad — WitnessedReceipt accumulates events

**Form.** Each turn accumulates a `WitnessedReceipt` recording its
effects. This is the *Writer monad* with the output being a receipt
chain.

**Categorical name.** Writer monad `(X, W)` where `W` is a monoid
(the receipt chain).

**`dregg` realization.** `turn::executor`'s receipt construction.

**Missing operation.** The writer monad's `tell` operation — "append
this to the log" — corresponds to *receipt-emission*. The natural
generalization is *receipt-side-channels*: emit a structured event to
a side log (e.g., for indexing) without affecting cell-state. Today
this exists as `Effect::Custom` or as application-layer event
emission; the writer-monad framing suggests a *Receipt::Emit { kind,
payload }* shape that's distinct from a state-mutating effect.

### §7.4. The reader monad — EvalContext as reader environment

**Form.** Predicate evaluation has access to `(height, epoch, sender,
preimage, ...)`. This is the *Reader monad* with environment =
`ValidationContext`.

**Categorical name.** Reader monad `R → X`.

**`dregg` realization.** `storage::programmable::ValidationContext` (or
its lifted equivalent). The evaluator threads this through every
predicate evaluation.

**Missing operation.** The reader monad's `local` operation —
"evaluate this sub-expression in a modified environment." `dregg`
doesn't have this; the context is global per turn. Conditional reads
(`ConditionalTurn`) come close but operate on whole turns, not
per-predicate-scope.

### §7.5. The continuation monad — CapTP promise pipelining

**Form.** CapTP's promise pipelining is *exactly* the continuation
monad: an action's continuation is "what to do with the result," and
pipelined sends fire continuations.

**Categorical name.** Continuation monad `(X → R) → R`.

**`dregg` realization.** `captp::pipeline` and the promise resolution
machinery.

**Missing operation.** The continuation monad's `callCC` ("call with
current continuation") — dregg doesn't have a structural way to
*reify* the current continuation as a first-class object. This would
be useful for *cancellation* / *failure recovery* flows in pipelined
sends. Today: hand-rolled per app.

### §7.6. The combined effect VM

The dregg effect VM (`circuit::effect_vm`) is *operationally*:
- state monad (cell state)
- + writer monad (receipt)
- + reader monad (validation context)
- + maybe monad (authorization may fail)

This is a *monad transformer stack*. The trace columns are the
*transformer interpretation*. Naming this aligns the effect VM's
design with a well-understood category-theoretic structure.

The win: when extending the effect VM (e.g., new effect kinds), the
monadic structure tells you *where* the extension lives. A new
non-failing pure effect: extend the writer monad. A new
authorization-sensitive effect: extend the maybe monad. A new
context-reading effect: extend the reader monad.

### §7.7. Verdict

The monad analysis surfaces three actionable observations:

1. **`Authorization::OneOf(Vec<Authorization>)`** — the capability
   monad's missing coproduct. Expressible today via Custom; naming as
   monadic alternative suggests promoting to a first-class variant.
   *Real ergonomic win.*

2. **`Receipt::Emit { kind, payload }` for side-channel events** — the
   writer monad's `tell` for non-state-mutating side-effects. Today
   ad-hoc via Custom; a first-class form would clarify indexing /
   pub-sub flows. *Defer until app demand.*

3. **Effect VM as monad transformer stack** — naming the design.
   *Documentation, not code.*

---

## §8. Functorial maps — programs as functors

§1.4 introduced `CellProgram` as a functor that constrains which
transitions are admitted. This section explores compositions.

### §8.1. CellProgram as characteristic function

**Form.** A `CellProgram` is a (partial) function `(old_state,
new_state, ctx) → bool`. As a functor from the category of state-
transitions, it's a *characteristic function* — selecting the
sub-category of admitted morphisms.

**Composition.** Two cell programs `P, Q`:
- *Intersection.* `P ∩ Q` admits a transition iff both admit. The
  meet in the program-lattice.
- *Union.* `P ∪ Q` admits a transition iff either admits. The
  join.

**Today.** A cell has *one* program. There is no in-tree primitive
for *combining* two programs on a single cell. The closest is
`CellProgram::Cases(Vec<TransitionCase>)` which is a list of
case-arms — a disjunction-flavored shape, but the cases are arms
of a *single* program, not a composition of two programs.

### §8.2. The inclusion functor

**Form.** A `CellProgram::Cases(vec![case_A])` is a *sub-program* of
`CellProgram::Cases(vec![case_A, case_B])` — every transition the
former admits, the latter also admits. The functor is *inclusion*.

**Implication.** This is the *attenuation* relation on programs —
analogous to capability attenuation. Today's `is_facet_attenuation`
realizes this on the capability side but not the program side.

A `CellProgram::is_attenuation_of(parent: &Self) -> bool` is the
program-side dual of `is_facet_attenuation`. It would let callers
check "this proposed program is a sub-program of this parent."

**Use case.** When upgrading a cell's program (e.g., for a new
case-arm), we want to verify the upgrade is a *valid extension* —
strictly more permissive (or strictly equivalent on the existing
cases). The attenuation check formalizes "the new program admits
everything the old program admitted and possibly more."

### §8.3. Program transformation as monoidal action

**Form.** Programs under either meet or join form a *monoid* (commutative,
associative, idempotent, with identity = `True` for meet, `False` for
join). This is a *semilattice*, which is a degenerate but well-defined
monoidal structure.

**`dregg` realization.** Implicit; not exposed.

**Implication.** If we expose program composition, two cells could
have *jointly-programmed* state-transitions: a transition is
admitted iff both cells' programs admit it. This is *exactly* the
γ.2 bilateral case but at the program level rather than the effect
level.

### §8.4. Verdict

Two soft actions:

1. **`CellProgram::Attenuation`** check (dual of facet attenuation
   for programs) — useful for cell-program upgrade validation.
   *Small but real.*

2. **Document the meet-semilattice structure** of programs to
   clarify the categorical role of cell-program composition.

Neither is urgent. The functorial-maps lens is the *least productive*
of the categorical lenses for surfacing app-driven gaps — most of
what it surfaces is documentation-flavored.

---

## §9. Missing primitives surfaced — the synthesis

This section consolidates the proposals from §3-§8 into a single
list, ranks them, and argues from the categorical principle plus the
app surface.

### §9.1. Tier 1 — Real gaps with app drivers (prototype these)

#### §9.1.1. `StateConstraint::Not(Box<SimpleStateConstraint>)` (and `Implies`)

- **Categorical principle.** Predicate is a distributive lattice
  today; with `Not` and `Implies` it becomes a Heyting algebra
  (intuitionistic logic). The missing operations are the *initial
  object* (`False`) and the *exponential* (`Implies`).
- **App driver.** Anti-permission, conditional escrow, non-membership
  in nullifier-set as a first-class predicate (today bespoke).
- **Implementation scope.** `StateConstraint::Not` over a restricted
  inner subset (FieldEquals, FieldGte/Lte, MerkleMember,
  BlindedMembership, MonotonicSequence). Evaluator flips boolean;
  AIR side uses kind-specific negation (sign-flip for inequalities;
  non-membership gadget for membership). `Implies(A, B)` reduces to
  `Or(Not(A), B)` once `Not` exists — minimal incremental work.
- **Soundness watch.** `Not` over a witness-attached predicate (e.g.,
  `Not(BlindedMembership)`) is *non-membership against a blinded
  set* — already supported by `circuit::non_membership` AIR. The
  wiring is the work.

#### §9.1.2. Unilateral γ.2 binding — `BoundDelta::Unilateral { slot, sequence_property }`

- **Categorical principle.** γ.2's binding functor has 2-arity (Transfer,
  Grant) and 3-arity (Introduce) branches but no 1-arity. The initial
  F-algebra of cross-cell binding is *partial* without the 1-arity
  branch (§6.2).
- **App driver.** Sovereign cells (`SOVEREIGN-WITNESS-AIR-DESIGN.md`);
  self-attested rate-limit compliance; cross-turn invariant attestation.
- **Implementation scope.** Extend γ.2's PI layout with
  `UNILATERAL_BINDING_ROOT_BASE` slots. Per-cell accumulator over
  self-attested temporal properties; same verifier loop structure as
  outgoing/incoming roots. The sovereign-witness AIR
  `circuit::sovereign_witness` already computes the underlying
  proofs; lifting them to γ.2-shape is mechanical PI layout work.
- **Soundness watch.** The unilateral binding is *self-witnessed* —
  no cross-side check available. The PI layout must include the
  cell's `cell_id` in the canonical id derivation; otherwise the
  binding doesn't distinguish "this cell attests" from "any cell
  attests."

#### §9.1.3. `RingClosureAttestation` — coequalizer of ring trades

- **Categorical principle.** Coequalizer of N pairwise effects
  identifying their cycle. The dual of γ.2's equalizer (which
  binds pairs); coequalizer aggregates them into a single
  cycle-closure artifact (§5.3).
- **App driver.** Orderbook ring fills (`apps/orderbook/ring_trade.rs`);
  DEX multi-pair settlements; circular intent matching.
- **Implementation scope.** DSL macro that mints N pairwise transfers
  with a shared `closure_id`, plus a `WitnessedPredicate { kind:
  Custom { vk_hash: ring_closure_vk }, commitment: cycle_id }` that
  proves "every leg's outflow matches an inflow in the cycle." The
  prior `CROSS-CELL-COORDINATION.md §7.2` already proposes the
  `ring_trade!` macro; this is its *closure attestation* component.
- **Categorical clarity.** The coequalizer's universal property —
  "every other identification of the legs' outcomes factors through
  this one" — is *what makes this primitive composable*. Two ring
  attestations over disjoint cycles compose; a ring attestation plus
  a bilateral transfer compose. The categorical naming buys
  composability.

#### §9.1.4. `WitnessProducer` trait — left adjoint of `WitnessedPredicateVerifier`

- **Categorical principle.** Predicate ⊣ Witness adjunction (§4.1)
  has a right adjoint (`WitnessedPredicateVerifier`) but no named
  left adjoint. The asymmetry is in the type system but *not* the
  code — every prover implements this shape ad hoc.
- **App driver.** SDK ergonomics; halves the prover-API surface
  by unifying per-kind prover methods.
- **Implementation scope.** Trait + per-kind impls. ~1 day to land.
  The existing provers `BridgePredicateProof::new`,
  `PortableNoteProof::from_witness`, etc., refactor to implement
  the trait.

### §9.2. Tier 2 — Categorical curiosities; defer

#### §9.2.1. `Renunciation` (proof-of-non-holding)

- **Categorical principle.** Initial object in Authorization.
- **App driver.** Governance recusal; compliance attestation.
- **Why defer.** Encodable today via `Authorization::Custom { predicate:
  BlindedMembership-with-non-membership-proof }`. The structural
  separation is *audit-clarity* but the gadget is shared. Land when
  an app forces the distinction.

#### §9.2.2. `Effect::Refusal { reason_hash }` (proof-of-non-action)

- **Categorical principle.** Initial object in Effect.
- **App driver.** Auditable rejection in HFT; structural permission
  denial.
- **Why defer.** Encodable today via `Effect::Custom { ... audit log
  mutation ... }`. The categorical pressure is aesthetic; the
  practical surface is thin.

#### §9.2.3. `Authorization::OneOf(Vec<Authorization>)`

- **Categorical principle.** Capability monad's missing coproduct;
  alternation.
- **App driver.** Multi-modal authorization (e.g., "this is
  authorized by a signature OR by a presentation proof").
- **Why defer.** Encodable today via `Authorization::Custom` with
  a disjunctive predicate. Naming-as-first-class would clean up the
  API but the math is the same.

### §9.3. Tier 3 — Documentation wins

- **Naming γ.2 as pullback / equalizer** (per §5).
- **Naming `Turn::call_forest` as pushout** of effects sharing a turn.
- **Naming effect VM as monad transformer stack** (state + writer +
  reader + maybe).
- **Naming `WitnessedReceipt` chain as initial algebra** of the
  prepend-receipt endofunctor.
- **Naming `Cell ⊣ Federation` adjunction** with its asymmetric axis
  (per `FEDERATION-AS-CELL`).
- **Naming chain-IVC as the completion of Receipt-chain ⊣ State
  adjunction** (per `STAGE-7-PLUS-DESIGN`).
- **Naming γ.2's outer aggregation as catamorphism** over the initial
  F-algebra (per §6).

These cost nothing beyond the doc edits; they buy clarity for future
work.

---

## §10. Verdict and recommendations

The category-theoretic analysis confirms `CROSS-CELL-COORDINATION.md`'s
claim — the algebra is dense and most app needs reduce to existing
primitives — but **identifies four real gaps and three real-but-
deferrable gaps** that the prior method missed.

### §10.1. What the prior verdict got right

- *Pairwise γ.2 + Custom + slot caveats* is structurally a *pullback +
  Heyting fragment + characteristic function* — three of the four
  basic categorical constructors. This is genuinely rich.
- *Adding `Effect::MultilateralAtomic` would be a redundant pushout*
  — the call_forest already realizes the pushout informally.
- *DSL macros over compositions, not new AIR primitives*, is the
  right ergonomic direction.

### §10.2. What the prior verdict missed

- **`Not` and `Implies` are categorically required for predicate
  completeness** (Heyting algebra). The absence is not "an ergonomic
  gap" — it is an *algebraic* gap at the predicate layer. The prior
  doc focused on *cross-cell* algebra and didn't analyze *per-cell
  predicate* algebra at the same depth.
- **Unilateral binding** is the missing 1-arity branch of the γ.2
  binding functor. The initial F-algebra (§6) is partial without it.
  Sovereign cells force the demand.
- **Coequalizer / ring closure** is a real colimit absence. The prior
  doc names "the call_forest is the multilateral witness" — true but
  *unstructured*. The categorical framing surfaces *cycle closure as
  a first-class artifact*.
- **The `Predicate ⊣ Witness` adjunction is half-implemented** — only
  the verifier side is named. `WitnessProducer` completes it.

### §10.3. Recommended next steps, ranked

1. **Prototype `StateConstraint::Not(Box<SimpleStateConstraint>)`.** 
   Add the variant + evaluator + AIR enforcement for the restricted
   inner-types subset. `Implies(A, B)` follows trivially as
   `Or(Not(A), B)`. **Highest leverage; smallest scope.**

2. **Land `WitnessProducer` trait.** Unifies the prover-side surface;
   no new gadgets; ~1 day. **Lowest cost; clarifies SDK.**

3. **Prototype unilateral γ.2 binding.** Extend PI layout; same
   verifier-loop structure as outgoing/incoming roots; sovereign
   witness AIR already has the gadget. **Closes structural family
   bilateral/trilateral/unilateral.**

4. **Prototype `RingClosureAttestation`.** As a DSL macro + custom
   `WitnessedPredicate` kind, per the prior doc's `ring_trade!`
   plus this doc's coequalizer framing. **Real ergonomic win for
   orderbook / DEX apps.**

5. **Document the categorical structure.** Edit the existing γ.2,
   call_forest, effect-VM, and receipt-chain docs to name the
   categorical roles (pullback, pushout, monad transformer stack,
   initial algebra). **Costs nothing; clarifies future work.**

6. **Defer (in this order): `Renunciation`, `Effect::Refusal`,
   `Authorization::OneOf`, `CellProgram::Attenuation` check.** Each
   has thin demand or is already-expressible-via-Custom. Promote when
   an app forces the distinction.

### §10.4. The opinionated bottom line

The categorical method earned its keep. It found four real prototypes
(`Not`, unilateral binding, ring-closure coequalizer, `WitnessProducer`),
three deferrable curiosities, and seven documentation wins. The
prior doc's "the algebra is complete, only ergonomics leak" was
*almost* right — but the asterisks matter:

> γ.2 + Custom + slot caveats is **almost** complete. It is missing:
> (a) the Heyting fragment of `Predicate` (`Not`, `Implies`);
> (b) the 1-arity branch of the binding functor (unilateral);
> (c) the coequalizer of the binding functor (ring closure as
> first-class);
> (d) the left adjoint of `WitnessedPredicateVerifier`
> (`WitnessProducer`).
>
> With those four additions, the algebra is **structurally complete**
> in the sense that every basic categorical constructor — limit,
> colimit, adjunction, initial algebra — has a named realization in
> the substrate. The ergonomic DSL macros from `CROSS-CELL-
> COORDINATION.md §7.2` then sit on a *structurally closed* substrate
> rather than an *approximately closed* one.

The method also reveals that dregg's substrate is **further along
than the use-case method suggested**: most of the rich categorical
constructions (pullbacks, equalizers, adjunctions, initial algebras)
are *already realized*. The missing pieces are surgically small. This
is good news.

Apply with proportionate energy: Tier 1 is real work this quarter;
Tier 2 is deferred until app demand; Tier 3 is doc edits over a
single afternoon.

---

## §11. Honesty appendix — where this method could be wrong

The category-theoretic method has known failure modes; I owe an
accounting.

### §11.1. The method finds *aesthetic* gaps as easily as *real* ones

A category with a terminal object and no initial object is
*aesthetically asymmetric*. It is not necessarily *practically
broken*. Three of the seven Tier-2/3 items in §9 are aesthetic-only:
they would round out the categorical picture but no app demands
them. I have tried to flag these honestly.

Where this analysis could be wrong: I may have over-rated one of the
Tier 1 items as app-driven when it's actually aesthetic. The most
suspect is *unilateral binding* (§3.5) — sovereign cells are real but
their categorical PI alignment may not actually buy them anything an
ad-hoc PI couldn't. I think it's still worth prototyping because the
ergonomic uniformity with γ.2 is real, but I hold the verdict at p ≈
0.7, not p = 1.

### §11.2. The method privileges *uniformity* over *fitness-for-purpose*

The categorical lens *wants* every constructor to have its dual.
This is a heuristic, not a theorem about software design. Some
asymmetries are *correct* — e.g., the absence of `Effect::Refusal`
may genuinely reflect that "non-action" isn't a thing that needs to
exist in the same algebra as "action" — and forcing the dual into
existence would be a category error (pun acknowledged).

I have tried to flag these (§3.3 specifically defers Refusal on
this basis). The risk is that other Tier-2 items also belong in the
"correctly asymmetric" bucket and I have over-promoted them.

### §11.3. The method's blind spot — *what isn't a category*

Categorical analysis sees what fits categorical structure. It is
deaf to:

- **Concurrent / partially-ordered processes.** Blocklace's DAG
  ordering, Cordial Miners' multi-leader rounds — these are not
  categorical structures; they're *process algebra* (CCS / CSP /
  pi-calculus territory). The category-as-cell mapping found in
  `FEDERATION-AS-CELL.md §3.4` correctly identifies this as the
  *limit* of the categorical lens — six axes uniform, three process-
  shaped.

- **Performance and resource bounds.** This method has nothing to say
  about whether γ.2's PI growth or the AIR's column-count blowup is
  acceptable. The prior doc's §9.1 ("performance pressure on giant
  rings") is precisely the right place to look for the categorical
  blind spot.

- **Privacy boundaries beyond the four-fold.** BOUNDARIES.md's
  inside/outside vocabulary is *almost* a categorical structure (a
  bounded poset, §2.8), but its enforcement is by cryptographic
  primitives whose properties are mathematical *facts*, not
  categorical *abstractions*. A categorical analysis cannot tell
  you whether your X25519 sealing is post-quantum (it isn't).

The method is one lens. The use-case-enumeration of the prior
doc is another. The privacy / boundary lens of `BOUNDARIES.md` is
a third. They overlap; they disagree on edge cases. The synthesis
is the value, not any one of them in isolation.

### §11.4. The strongest claim is the negative one

The most defensible claim of this analysis is *negative*: the prior
doc's algebra-is-complete verdict is **almost right** with these
specific four asterisks. The positive claim — that adding these four
fixes everything — is *less defensible*, because the analysis can
only see structural completeness, not whether *new* asymmetries will
emerge once these four are wired in.

This is the standard situation for category-theoretic design:
*find missing pieces by symmetry; verify by use*. The four prototypes
in §10.3 are the find-by-symmetry results. Whether they are *correct
finds* is determined by what apps do with them.

---

## §12. Closing — categorical hygiene as design discipline

The user said: "we previously did a categorical analysis of some of
these constructions and used that as a way to find missing duals in
the past, this is a valid method." This document affirms the
method, applies it freshly to the cross-cell substrate, and
recommends four concrete prototypes plus seven documentation edits.

The method is not for *over-formalizing what already works*. It is
for *noticing what isn't there*. The four Tier-1 items
(`Not`/`Implies`, unilateral binding, ring-closure coequalizer,
`WitnessProducer`) were each found by symmetry-noticing, not by
use-case-enumeration. Two of them — `Not`/`Implies` and unilateral
binding — have *significant* app demand once named.

The most important methodological observation: **the categorical
analysis and the use-case analysis disagreed on different items**,
and where they disagreed, the categorical lens was right to flag
gaps the use-case lens missed. *Not*-and-*Implies* in `Predicate`
were not surfaced by `CROSS-CELL-COORDINATION.md` precisely because
they aren't cross-cell — they're per-cell. The lens directs attention.

> **Final one-line recommendation:** prototype `Not`/`Implies` in
> StateConstraint, `WitnessProducer` trait, unilateral γ.2 binding,
> and `RingClosureAttestation`. Document the seven categorical
> namings (§9.3). Defer the rest until app pressure forces them.

The substrate is structurally rich. The gaps are surgically small.
This is the encouraging finding.
