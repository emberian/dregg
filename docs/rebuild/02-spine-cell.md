# 02 — Spine: Cell-as-Universal-Object

> **Lens:** Everything is a cell `= (identity, state-commitment, transition-rule)`,
> and everything that happens is a **predicate-gated morphism**. The categorical
> collapse is the primary organizing principle; seL4 reflection and fluid
> boundaries fall out of it.
>
> This is a **forward design exploration**, not an audit. It is also
> deliberately **self-adversarial**: §7 is the most important section. The
> user wants the hidden constraints of this lens mapped, not the lens sold.

---

## 0. Why this lens, in one breath

Dragon's Egg already *is* a thin posetal category dressed in ad-hoc clothes.
Objects are cell states (`CellId = BLAKE3(pk‖token)`, `cell/src/id.rs:3`);
morphisms are turns over a flat action sequence. The "structure" is scattered
across a dozen bespoke types: nullifier sets are a `Mutex<NullifierSet>`
side-table (`turn/src/journal.rs` rollback signature), revocation/authorized
sets are more side-tables, capabilities are c-list entries
(`cell/src/capability.rs:43`), the receipt chain is the persistence log
(`turn/src/witnessed_receipt.rs:246`), lifecycle is an enum
(`cell/src/lifecycle.rs:37`). Each of these reinvents "a thing with identity,
committed state, and rules for how it changes."

The cell lens says: **stop reinventing it. Name it once. Make everything that
object.** Then the category becomes uniform, the `Predicate ⊣ Witness`
adjunction (named but half-wired in `cell/src/predicate.rs:924`) can be made
total, and "proof is truth" becomes statable as a single law instead of a
per-subsystem patchwork.

The promise is real. The danger — that this is "everything is a file" all over
again — is also real, and §7 takes it seriously.

---

## 1. The irreducible primitives

### 1.1 The cell

A cell is the **least fixed point** of "a thing that has identity, a committed
current state, and a rule for legal change." Strip everything else away:

```
Cell = {
    id    : CellId,            // content-or-nonce-addressed stable name
    head  : Commitment,        // 32-byte commitment to current state value
    rule  : RuleRef,           // commitment to the transition relation
    state : Schema-typed value // the *actual* current value (see §3)
}
```

Three observations make this the *irreducible* primitive rather than an
arbitrary one:

1. **`head` is a commitment, not the value.** The value lives wherever it
   lives (in-memory cache, gossiped blob, archived off-chain). The cell's
   on-substrate footprint is `(id, head, rule)`. This is exactly the
   houyhnhnm "the log IS the inputs, not the bytes" stance: a cell is
   reconstructible from its rule + its input history; `head` is just the
   memoized fold.
2. **`rule` is itself a commitment** (a `RuleRef`, content-addressed like
   `canonical_program_vk` in `cell/src/predicate.rs:93`). This is what
   un-freezes the AIR (§3): the transition rule is *data inside the cell*,
   versioned with the cell, not a global frozen circuit.
3. **`id` is stable across rule and state changes.** Today `CellId` bakes
   `(pk, token)` at birth. In the rebuild, identity must survive a typed
   schema upgrade (the cell is "the same egg" before and after), so `id` is
   the birth identity, while `head` and `rule` evolve. (Tension: this means
   `id` is *not* content-addressed to current state — see §7.4.)

### 1.2 The morphism

A morphism is a **predicate-gated transition** between cell states:

```
Morphism = {
    src   : CellId @ head_pre        // the pre-state it consumes
    dst   : CellId @ head_post       // the post-state it produces
    gate  : Predicate                // what must hold for this to be legal
    proof : Witness                  // the evidence that gate holds (mandatory)
}
```

The single most important rebuild law lives here:

> **Totality of the adjunction (= "proof is truth"):** a morphism is
> well-formed **iff** it carries a `Witness` that the `Predicate` accepts. The
> witness side is *not optional*. There is no "executor checked it for you"
> path. The executor is a `WitnessProducer` (left adjoint,
> `cell/src/predicate.rs:964`) running ahead of time as a *cache*; the truth
> is `verify(gate, proof)`.

Today this law is violated four ways the rebuild must close
(all from the FIXED DECISION): authorization lives *outside* the proof
(`Authorization` enum, `turn/src/action.rs:206`); `effects_hash` is a host
commitment the AIR never re-derives; state-constraints/range are executor-side;
composition is classical not recursive. Under the cell lens every one of those
is "a gate whose witness side is missing" — a half-wired adjunction
(`NotYetWiredVerifier`, `cell/src/predicate.rs:792`). Closing them *is* finishing
the right adjoint.

### 1.3 That's it

Two primitives: **cell** and **predicate-gated morphism**. Everything in §1.4
is an attempt to express the current zoo of types as one of these two. Where it
works, we delete a type. Where it breaks (§7), we learn something.

### 1.4 What collapses INTO "cell"

| Current thing | As a cell | state | transition-rule | predicates that query it |
|---|---|---|---|---|
| **Nullifier set** (`cell/src/nullifier_set.rs:63`, a `Mutex` side-table) | ✅ clean win | set-root (Merkle/accumulator) | append-only: `insert` only, `remove` forbidden (`Terminal` linearity) | `MerkleMembership` / `NonMembership` (`predicate.rs:240/264`) query the **live** root, not a slot-snapshot |
| **Revocation set** | ✅ | accumulator root | append-only insert | `NonMembership` for non-revocation |
| **Authorized-sender set** | ✅ | set-root | governance-gated insert/remove | `BlindedSet` / `MerkleMembership` |
| **Commitments** (note commitments, value commitments) | ✅ | the commitment value itself | one-shot generative, then immutable | opening predicates, `PedersenEquality` |
| **Programs / rules** | ✅ (this is the un-freezing) | the program bytes / AIR descriptor | governance-gated upgrade morphism | `vk_hash` match; "is this the rule I expect" |
| **ReferenceGroup / strand-view** | ⚠️ partial (see §4.2, §7.3) | a *view-commitment* (root over member cells) | merge/governance | membership predicates |
| **Capability** | ⚠️ **strained** (see §7.1) | target+attenuation+caveats | attenuate (narrow-only), revoke (terminal) | order-theoretic `is_narrower_or_equal`; caveat predicates |
| **Strand / causal log** | ❌ **category error** (see §7.2) | — | — | — |

The headline collapse — and the audit's flagged highest-leverage simplification
— is the **set side-tables becoming cells**. Today a predicate can only query a
root *passed in from a slot* (`InputRef::Slot`, `predicate.rs:169`), a snapshot
that goes stale and that the executor must thread through by hand. As a cell, the
nullifier set has a live `head`, and a predicate gates against the live root via
a *cell-reference input* (a new `InputRef::Cell { id }`). The nullifier-set's own
append-only-ness is enforced by *its* transition rule being `Terminal`-class
(`turn/src/action.rs:711`) — no special-case executor logic. This deletes
`nullifier_set.rs`'s special status, the `Mutex` in the rollback signature, and
the snapshot-staleness class of bugs in one move.

---

## 2. The category, made uniform and total

### 2.1 Objects uniform

Every object is a cell. `CellState`'s 8 fixed `[u8;32]` slots
(`cell/src/state.rs:11,47`) — a Mina zkApp artifact — stop being *the* state
shape and become *one possible schema* a cell's rule may declare (§3). The
category `𝒞`:

- **Objects:** cells at a given `head` (i.e. `(CellId, Commitment)` pairs).
- **Morphisms:** predicate-gated transitions.
- **Identity:** the no-op turn (predicate `⊤`, trivial witness).
- **Composition:** sequencing turns; associative because receipt-chain hashing
  is associative.

This is still a **thin** category in the per-cell direction (between two fixed
heads there is essentially one legal step, modulo witness), which is *fine* —
thinness is honesty about a state machine. Richness lives in the **enrichment**.

### 2.2 The enrichment we genuinely need

Three layers, in increasing order of "do we actually need this":

**(a) Heyting-enriched hom (DEFINITELY need, mostly have).**
The hom-set between two cells is ordered by predicate strength: a morphism gated
by predicate `P` refines one gated by `P' ≤ P`. The current
`SimpleStateConstraint` lattice + `Not` is exactly a Heyting algebra of gates.
This is the `Predicate` half of the adjunction and it already exists. The
rebuild's job is *totality* (§2.3), not new structure.

**(b) Coproducts for branch (NEED, don't have).**
"Fork a strand onto an rbg subsystem"; "independent strands on a phone that
gossip" — these are **branch points**. The from-a-paper risk the audit flagged
is exactly *no fork/merge primitive*. Categorically a fork is a **coproduct of
cell-histories**: one pre-state, two post-states that both validly descend from
it. We need a first-class `Fork` morphism whose witness proves "both branches
are legal descendants of `head_pre`." This is genuinely new and genuinely
required by the vision. (Note: it is *not* a categorical coproduct in the strict
sense — see §7.5; it is a span / pushout-shaped merge primitive that we are
*choosing* to model, and we should not over-claim it as a free coproduct.)

**(c) Presheaf / sheaf over the gossip topology (NEED A WEAK FORM; over-claimed in docs-old).**
The polycentric "no single kernel" requirement means a cell's state is observed
differently by different strands (the `ReferenceGroup-as-VIEW` already gestures
at this). The honest structure is a **presheaf**: assign to each *observer/strand*
a view of the cell, with restriction maps along the gossip topology. The
*sheaf condition* (local agreeing views glue to a unique global view) is the
**merge law**: two strands that agree on overlap must merge to a unique state.
CRDT merge gives us this for commutative state; for non-commutative state the
sheaf condition *fails*, and that failure is a real fork that needs §2.2(b).

**What is over-claimed (cut it):** docs-old's talk of products, F-algebras,
pushouts as load-bearing. We do not need a topos. We need: a Heyting-enriched
thin category (have), a branch/merge span primitive (build), and a presheaf
view-structure with a CRDT-backed partial sheaf condition (build the weak form).
Anything beyond that is mathematician's cosplay until a concrete requirement
forces it.

### 2.3 The adjunction, made total

`Predicate ⊣ Witness` is named in code (`WitnessProducer` ⊣ `WitnessedPredicateVerifier`,
`predicate.rs:924/478`) but half-wired: verifiers are `NotYetWired`
(`predicate.rs:792`) and producers are stubs. "Proof is truth" = **the right
adjoint is total and mandatory**:

- Every gate kind has a registered verifier (no `NotYetWiredVerifier` in
  production; fail-closed is a transition state, not a destination).
- Every morphism carries a witness; the unit-counit law
  (`predicate.rs:934-941`) holds for *every* turn: `verify(gate, produce(gate, input)) = accept`.
- The four current gate surfaces (Precondition / StateConstraint /
  CapabilityCaveat / Authorization::Custom) collapse to **one**: a
  `WitnessedPredicate` + a `BindingSite{when, input, signed_by}`. The audit
  confirms all four already wrap one `WitnessedPredicate`; the rebuild deletes
  the four wrappers.

Concretely the morphism's `gate` is a *conjunction over the predicate lattice*
of: authorization-predicate ∧ effect-semantics-predicate ∧ state-constraint
∧ conservation. Today these are four code paths in four crates; under the lens
they are four meets in one Heyting algebra, discharged by one witness
(a recursively-composed proof — the "composition is recursive not classical"
fix is *literally* "the witness for a meet is the product of witnesses,
verified by a recursion circuit").

---

## 3. Houyhnhnm typed schema-upgrade: un-freezing the 8 slots and the AIR

### 3.1 Cell-state as an evolving ADT

Replace `CellState`'s frozen `[FieldElement; 8]` (`state.rs:47`) with a
**schema-typed value**:

```
CellState_v(S) = value : ⟦S⟧          // S is a schema (an ADT descriptor)
SchemaRef       = commitment to S      // lives in the cell's `rule`
```

The cell's `rule` commits to *both* the schema `S` and the transition relation
over `⟦S⟧`. The 8-slot array becomes the schema `S₀ = Record { fields: [F;8],
... }` — a legacy schema, not a privileged one. New cells declare richer
schemas: sum types, linear resources, nested records, the live set-root for a
nullifier-cell.

### 3.2 The upgrade morphism (houyhnhnm's `old→new` + linear drop)

A schema upgrade is **just a morphism** — the lens pays off here:

```
Upgrade : Cell@(S_old, head_old) → Cell@(S_new, head_new)
  gate  = "migrate is authorized by governance"
        ∧ "head_new = commit(f(decode(head_old)))"   // f : ⟦S_old⟧ → ⟦S_new⟧
  proof = witness that f was applied correctly
  drop  = linear consumption of the old-shape value  // no two live copies
```

The `old→new fn` `f` is carried as data (a `RuleRef` to the migration program),
content-addressed and versioned. The **linear drop** is enforced by the upgrade
morphism being `Terminal`-class on the old schema (`action.rs:711`): the old
value is consumed, not copied — there is never a live old-shape and new-shape
simultaneously. This is exactly `LinearityClass` doing structural work
(`action.rs:698`, the keeper).

### 3.3 How "proof is truth" survives an upgrade

This is the subtle part and the user asked for it directly. A proof made about a
cell *before* upgrade asserts a statement in terms of `S_old`. After upgrade the
cell speaks `S_new`. Two facts must hold for old proofs not to become lies:

1. **Old proofs remain valid statements about the past, not the present.**
   A receipt is bound to a specific `head` (`witnessed_receipt.rs:246`, the
   keeper). A proof about `head_old` is forever a true statement about
   `head_old`. The upgrade does not retroactively falsify history; it appends a
   morphism. "Proof is truth" is a statement about *each turn's local truth*,
   and the receipt chain preserves every local truth.

2. **The upgrade morphism itself bridges the two schemas in-proof.** The
   upgrade's witness proves `head_new = commit(f(decode(head_old)))`. So any
   *future* proof that needs to reason across the boundary can chain through the
   upgrade receipt: a recursion that verifies `(proof-about-S_old) ∘ (upgrade-proof)`
   yields a sound statement in `S_new`. The schema boundary is a **full-abstraction
   boundary** (the houyhnhnm requirement): `f` is the only sanctioned way across,
   and the upgrade proof is the witness that you went across honestly.

The frozen-AIR / "Urbit trap" dies because the AIR is no longer global: each
cell's `rule` *is* its AIR, versioned, and an upgrade is a normal governance-gated
morphism with its own proof. There is no monolithic circuit to freeze.

**Tension flagged for §7.6:** this requires *every verifier to be parameterized
by `SchemaRef`/`RuleRef`*, i.e. the verifier must load the cell's rule and prove
*against the rule the cell actually declares*. That is a recursion-heavy, "verify
the verifier" structure. It is the right design and it is expensive.

---

## 4. seL4 reflection and fluid boundaries under the cell lens

### 4.1 Is a capability a cell, a cell-reference, or a morphism?

**All three faces, and pretending it's only one is the trap (§7.1).** The clean
decomposition:

- The **authority to act** is a *morphism* (exercising a cap = taking a gated
  transition on the target). This is the E-language / object-capability reading:
  a capability is "permission to invoke."
- The **holding of that authority** is a *cell-reference* (an entry in a c-list,
  `CapabilityRef`, `capability.rs:43`). The c-list is itself cell-state.
- The **revocable, attenuatable object** behind it — the thing with identity that
  can be narrowed and killed — is a *cell* (a "capability cell" whose state is
  `(target, attenuation, caveats, revoked?)`, whose transitions are
  `attenuate` (narrow-only) and `revoke` (terminal)).

The **seL4 reflection** wants this tripartite view: seL4 caps are kernel objects
in a CNode with a derivation tree (revoke walks descendants). That maps cleanly:
a seL4 capability ⇒ a Dragon's Egg **capability cell** whose `id` is the
content-addressed `(badge, rights, object)`, whose attenuation lattice mirrors
seL4 rights-masking (`allowed_effects: EffectMask`, `capability.rs:71` is already
a rights mask), and whose derivation tree is a cell-genealogy (each `attenuate`
morphism records its parent → a CDT). A `revoke` on a parent is a `Terminal`
morphism that gates every descendant's future exercise on a non-revocation
predicate against the parent capability-cell's live `revoked?` root.

The reflection law: **seL4 cap ⟷ capability-cell** is a functor from the
kernel's CNode-poset into `𝒞`. seL4 unforgeability (caps only come from
caps) reflects to: a capability-cell can only be created by a morphism whose
witness exhibits a parent capability-cell + a valid attenuation. This is the
houyhnhnm "capability discipline" requirement made into a category law.

### 4.2 Is a strand / ReferenceGroup a cell?

**ReferenceGroup: yes, as a *view-cell*.** Its state is a view-commitment (a root
over the member cells it groups); its transitions are membership changes and
governance-lens updates. The audit already calls it "ReferenceGroup-as-VIEW";
the lens just names the view a cell with a presheaf-restriction transition rule.

**Strand: NO — this is §7.2, the category error.** A strand is a *log*, a
sequence of morphisms, an arrow-object, not a state-object. Forcing it into
"cell" is forcing an edge to be a vertex.

### 4.3 Is a fork a cell-level branch?

Yes — a fork is a §2.2(b) branch morphism producing two descendant heads of one
pre-state. "Fork a strand onto an rbg subsystem to evaluate in a container" =
take the branch morphism, ship one descendant head into the rbg container,
evaluate, and either merge back (sheaf glue, §2.2c) or keep divergent (a real
fork). The fluid-boundary requirement is satisfied because a head is portable:
it is `(id, head, rule)` + the receipt chain to reconstruct it. A phone strand
gossiping over Bluetooth ships heads + receipts; merge is the presheaf glue.

---

## 5. Migration "under and through": cut first, survive

**Cut first (the load-bearing simplifications):**

1. **Promote the set side-tables to cells.** `NullifierSet`, revocation set,
   authorized-sender set stop being `Mutex<...>` in the executor
   (`journal.rs` rollback signature) and become cells with append-only rules.
   Add `InputRef::Cell { id }` so predicates query live roots, deleting the
   slot-snapshot staleness path. *This is the single highest-leverage cut and
   should be first.*
2. **Collapse the four gates to one** `WitnessedPredicate + BindingSite`. Delete
   `Precondition` / `StateConstraint` / `CapabilityCaveat::Witnessed` /
   `Authorization::Custom` as separate surfaces; they already wrap one
   `WitnessedPredicate`.
3. **Pull authorization INSIDE the proof.** Delete the out-of-proof
   `Authorization::Signature/Proof` privileged path; authorization becomes a
   gate predicate like any other (a signature-verification predicate). This is
   the FIXED DECISION's core inversion.
4. **De-privilege the 8-slot state.** Make `S₀` a schema, not the schema.

**Survive (the keepers, untouched or lightly re-housed):**

- Capability substrate (`capability.rs`, `facet.rs`) — re-housed as
  capability-cells (§4.1) but the attenuation lattice and `EffectMask` survive
  verbatim.
- `WitnessedReceipt`-as-persistence (`witnessed_receipt.rs:246`) — *this is the
  log that IS the inputs*; it is the houyhnhnm orthogonal-persistence substrate
  already. Keep.
- `LinearityClass` (`action.rs:698`, exhaustive no-default) — becomes the
  conservation/linear-drop enforcement for morphisms *and* schema upgrades.
  Keep, lean on it harder.
- `CellLifecycle` terminal objects (`lifecycle.rs:37`) — already the
  state-machine the cell lens wants; `Migrated`/`Destroyed` are terminal objects
  in `𝒞`. Keep.
- `FieldVisibility` selective disclosure (`state.rs:18`) — becomes per-field
  visibility within a schema. Keep.
- The `Predicate ⊣ Witness` *names* (`predicate.rs`) — keep the trait shapes;
  finish the wiring (§2.3).

**Order:** (1) → add `InputRef::Cell` → (2) → (3) → schema work (§3) → branch/merge
(§2.2b). Steps 1–3 are mechanical collapses of things already shaped right.
Steps after are genuinely new structure and where the risk concentrates.

---

## 6. ... (intentionally folded into §7; the constraints ARE the deliverable)

---

## 7. CONSTRAINTS & TENSIONS — where cell-universalism strains (the real deliverable)

### 7.1 A capability is a RELATION/authority, not obviously an object

"Cap as cell" risks losing the two things that make capabilities *capabilities*:

- **Unforgeability.** A cap's whole point is "you cannot make one up." If a
  capability is "just a cell," and cells are creatable by morphisms, then
  forging a cap reduces to forging a cell-creation witness. The defense (§4.1:
  cap-cells only born from parent cap-cells) **works but is not free** — it
  smuggles the entire seL4 derivation-tree invariant into the cap-cell's
  transition rule. The relation (who-may-derive-from-whom) does not vanish by
  calling the endpoints "cells"; it relocates into the rule, where it must be
  enforced *every* exercise via a live non-revocation predicate against the
  ancestor chain. That is a per-exercise ancestor-walk proof. **Honest cost:**
  capabilities-as-cells trades a cheap c-list lookup for a recursive
  derivation-chain proof. For a phone strand gossiping in Bluetooth range,
  proving a 6-deep attenuation chain on every exercise may be prohibitive.
  *The relation was the cheap part; objectifying it made it expensive.*

- **The authority IS a morphism, the object is the residue.** §4.1 admits a cap
  is *three* things. If we are honest, the *primary* thing is the morphism
  (permission-to-invoke); the cell is the bookkeeping residue. So "everything is
  a cell" is already false for the most important security primitive: a cap is
  *primarily a morphism*. The lens survives only by saying "...and morphisms are
  first-class too," which quietly admits we have **two** universal primitives,
  not one. That's fine — but the slogan oversells.

### 7.2 A strand is a LOG, not a state — forcing it is a category error

A strand is `[morphism₀, morphism₁, ...]` — an arrow, not a vertex. You *can*
reify "the strand's current head" as a cell, but the strand-*as-such* (its
causal order, its branch structure, its gossip provenance) is the **path**, not
the **point**. Modeling a log as a cell loses the very thing logs are for:
ordering and provenance. The right move is to *not* collapse strands into cells —
keep morphisms/logs as first-class arrows. **This is the cleanest place the
"everything is a cell" universalism breaks, and we should let it break rather
than contort.** A strand is an object in a *different* category (a free category
on the cell-graph, or a path category), and the gossip topology is a functor
between strand-categories. Pretending otherwise is the failure mode.

### 7.3 Does this repeat "everything is a file"?

Yes, partially, and we must name the specific failure. "Everything is a file"
failed because it forced *streams, devices, sockets, processes* through one
byte-stream interface that fit none of them well (ioctl is the scar tissue). The
cell-lens analog: forcing *sets, capabilities, programs, views, and logs* through
one `(id, head, rule)` interface. The collapses that fit (sets, commitments,
programs — §1.4 ✅) fit because they genuinely *are* identity+committed-state+rule.
The collapses that strain (capabilities ⚠️, logs ❌) strain for the same reason
sockets strained against files: they have **essential structure orthogonal to
the universal interface** (caps: a derivation relation; logs: an order). The
discipline that avoids the file-failure: **collapse only where the essential
structure IS state-with-a-rule; refuse the collapse where the essence is a
relation or an order.** §1.4's ⚠️/❌ column is precisely that discipline applied.
The ioctl-equivalent we must watch for: a `Cell::special_op` escape hatch that
quietly readmits the orthogonal structure we pretended to eliminate.

### 7.4 Identity vs. content-addressing tension

§1.1 needs `id` stable across schema upgrades (the egg is the same egg), but the
current `CellId = BLAKE3(pk‖token)` and the houyhnhnm "code+data one versioned
history" instinct both pull toward content-addressing. You cannot have both
"identity is the content hash" and "identity survives a content change." The
rebuild must pick: **birth-identity** (stable, but then `id` is a mutable-cell
name, not a content address, reintroducing aliasing/GC questions) **vs.
content-identity** (every upgrade is a *new* cell with a forwarding pointer,
which is cleaner categorically — upgrade is a `Migrated` terminal morphism,
`lifecycle.rs:51` — but breaks "same egg" intuition and fragments capability
references across upgrades). I lean toward **content-identity + forwarding**
(it makes upgrade a normal terminal morphism and keeps content-addressing
honest), but it makes §4.1's capability references *upgrade-fragile*: a cap to
`cell@v1` does not automatically reach `cell@v2`. That is a real, unsolved
tension, not a detail.

### 7.5 The thin posetal category may lack the structure the vision needs

The honest categorical reading (from the audit) is **thin + posetal** — barely a
category. The vision wants branch/merge (coproducts/pushouts), polycentric views
(presheaves/sheaves), and full-abstraction boundaries (a rich-enough type
theory). **None of these are free in a thin poset.** §2.2 is honest that we must
*build* (b) and (c). The danger is **smuggling**: writing "fork is a coproduct"
makes it sound like the category structure gives it to us, when in fact a thin
category's coproduct (if it exists) is just a join, which does *not* capture
"two divergent histories" (a join would collapse them). So our `Fork` is **not**
a categorical coproduct; it is a chosen span/pushout primitive we implement and
must prove laws about by hand. Calling it a coproduct would be exactly the
docs-old over-claim we are trying to escape. **We are building richer structure
on top of a thin base; the lens does not hand it to us, and the doc must not
pretend it does.**

### 7.6 Per-cell rules make verification recursion-heavy and possibly slow

§3.3's payoff (no frozen AIR) has a cost: every verifier must be parameterized by
the cell's `RuleRef` and prove against the *declared* rule, which is "verify the
verifier" recursion on every turn. Combined with §7.1's per-exercise
derivation-chain proofs, the steady-state cost of a single honest turn under
full inversion is: (authorization proof) ∘ (effect-semantics proof against the
cell's rule) ∘ (state-constraint proof) ∘ (conservation proof) ∘ (cap-derivation
proof), all recursively folded. "Proof is truth" with per-cell rules means the
prover does a lot of work the old host-trusted executor did for free. On a
phone, in Bluetooth range, this is the binding constraint on whether the fluid-
boundary vision is *reachable* or merely *elegant*. The mitigation (folding/
accumulation schemes, deferred batch verification) is real but is itself
substantial new machinery the lens does not provide.

### 7.7 What the lens makes AWKWARD or gets WRONG

- **Ephemeral/zero-persistence authority** (the `Bearer` cap,
  `action.rs:222`, "exercised in the same turn it is delegated, no persistence
  in any cell's state") is *anti-cell*: its whole point is to have no cell. The
  lens wants to objectify it; the design wants it to vanish. Keep it as a pure
  morphism with an inline witness, and accept that "everything is a cell" has an
  explicit exception class.
- **Cross-cell atomic turns** (a turn touching N cells atomically) are awkward:
  the morphism in §1.2 is single-`src`/single-`dst`. Multi-cell turns are
  morphisms in the *product* category, which a thin per-cell category does not
  give you for free (§7.5 again). The `CallForest` (`turn/src/forest.rs:31`) is
  the current multi-cell vehicle, and the audit notes it is *enforcement-inert*
  (the tree shape is not enforced). Under the lens, multi-cell atomicity needs a
  genuine tensor/monoidal structure on `𝒞` (a `⊗` of cells with a conservation
  law across the tensor) — that is the honest home for `LinearityClass`
  conservation, and it is **more structure than "thin posetal" provides**.

---

## 8. Verdict

### (a) Minimal primitive set under this lens

1. **Cell** = `(CellId, head: Commitment, rule: RuleRef, state: ⟦Schema⟧)`.
2. **Predicate-gated morphism** = `(src, dst, gate: Predicate, proof: Witness)`,
   with the **mandatory-witness law** (proof is truth).
3. **Predicate lattice** (Heyting algebra of gates) + the **total `Predicate ⊣
   Witness` adjunction** (every gate has a registered verifier and producer).
4. **`InputRef::Cell`** — predicates query *live* cell heads, not slot snapshots.
   (The smallest new primitive with the largest leverage.)
5. **Schema + typed upgrade morphism** (old→new fn as data, linear drop via
   `Terminal` linearity).
6. **Branch/merge span primitive** (fork + presheaf/CRDT glue) — *explicitly not
   a free coproduct; built, with hand-proved laws.*
7. **A monoidal `⊗` on cells** for multi-cell atomic turns + conservation
   (where `LinearityClass` lives) — the structure the thin base does *not* give
   for free.

And two **first-class non-cells we must stop trying to objectify**: **morphisms/
logs (strands)** as arrows, and **the derivation relation** behind capabilities.

### (b) Honest one-paragraph verdict

Cell-as-universal-object is the **right spine but the wrong slogan**. It is right
that identity-plus-committed-state-plus-rule is the irreducible substrate and
that the highest-leverage rebuild moves (sets→cells, four-gates→one,
authorization-into-proof, un-freeze-the-AIR-via-per-cell-rules) all fall straight
out of taking it seriously. It is wrong as a *totalizing* claim: the design needs
**two** co-primary primitives (cells *and* morphisms), it must **refuse** to
collapse logs (an order) and capability-derivation (a relation) into cells on
pain of repeating the "everything is a file" ioctl-scar, and the thin posetal
base does **not** hand us the branch/merge, presheaf, monoidal, and recursive-
verification structure the houyhnhnm/seL4 vision requires — we build all of that
on top, and the doc must say "build," not "have." Adopt the cell as the spine;
adopt the predicate-gated morphism as its equal twin; treat §7.1–§7.7 as the
standing list of where the spine needs ribs it doesn't grow on its own; and never
let "everything is a cell" become the excuse that smuggles a relation or an order
into a state-object where it will rot into a special-case escape hatch.
