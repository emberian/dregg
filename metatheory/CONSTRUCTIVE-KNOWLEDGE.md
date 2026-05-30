# dregg, as a metatheory of constructive knowledge

> This file names the thing the directory has been *mis-calling* "Metatheory." There is an
> **actual metatheory** here — a distributed, intuitionistic logic of *constructive knowledge and
> authority* — and there is the **verification of dregg2** (the Lean proofs that the system realizes
> that logic). They interact, but they are not the same. This document is the former: the conceptual
> spine, discovered by reading the real dregg1 semantics end-to-end and asking "what is this, really?"

---

## 0. The thesis

**A capability is a piece of constructive knowledge: to *hold* one is to be able to *exhibit a
witness* that authorizes an act — never merely to assert it.** dregg is, underneath the bytes, a
**metatheory of how such knowledge is produced, combined, attenuated, propagated, and conserved
across a distributed network of mutually-untrusting knowers.** Everything else — cells, turns,
effects, the constraint catalog, finality, privacy — is a *projection* of that one idea.

This is why the verify/find seam, not the data model, is the heart of the system: the whole edifice
is organized around the asymmetry **proof-checking is cheap and trusted; proof-*search* is
undecidable and untrusted.** That is the [BHK / realizability](https://en.wikipedia.org/wiki/Realizability)
reading of intuitionistic logic, made operational and distributed.

---

## 1. The knowledge graph

The capability graph **is** a distributed knowledge graph:

- **nodes** are *cells* — the knowers / agents / objects, each with private state and a program;
- **edges** are *capabilities* — directed facts of the form "this cell can constructively demonstrate
  authority over that one," carrying *attenuated rights* (a facet: which acts the edge licenses);
- the graph is **partial and local**: no node sees the whole graph. You learn of an edge only when
  someone *presents a witness* for it. There is **no global registry of who-can-do-what** — the
  "capability-derivation-tree" is at most a *retrospective* log (the de-jure record), never a live
  oracle you consult. Authority is established by *exhibiting a discharging witness at the point of
  use*, and checking it.

A capability, then, is not a key in a lock — it is a **proof obligation you can discharge**.

---

## 2. A turn is an authorized inference step

A **turn** is one step of distributed inference: a forest of *actions*, each of which proposes to
move the knowledge graph from one state to a successor, **executed as a transaction** (all-or-nothing;
journalled, rolled back on any failure). An action carries:

- a **demand ⊣ supply** pair (the cell *demands* `AuthRequired`; the action *supplies* a witnessed
  `Authorization`) — this is exactly the **`Predicate ⊣ Witness` adjunction**: admissibility is
  "does the supplied witness realize the demanded predicate?", i.e. `Verify P w`;
- **guards** (preconditions / program-constraints / caveats) — *more* predicates over the proposed
  step, each again first-party (decidable now) or witnessed (a registry verifier discharges it);
- **effects** — the proposed graph mutation;
- a signed **binding** to a canonical message (federation, nonce, action, effects) — so an inference
  cannot be replayed into a context it was not proved for.

Soundness is not a property of one step but of the **unbounded life of the cell**: the cell is
*codata* (`νC. µI. StepProof I × (Turn ⇒ C)`), and "the cell stays correct forever" is a
**▶-guarded bisimulation** to a golden-oracle reference — "the knowledge never drifts from the truth
it claims." Step-completeness (each step really attests its full invariant) is what makes the
coinduction productive rather than a *drifting future* that type-checks while leaking.

---

## 3. The dynamics are knowledge *production*, not monotone descent

The characteristic — and easily-missed — fact: **authority/knowledge is produced, not merely spent.**
A model where "every step only narrows" (a monotone descent down a meet-semilattice) is *wrong*: it
forbids exactly the patterns that give capabilities their power (Mark Miller's discoveries). The real
dynamics have a **generative half** and a **restrictive half**, disciplined by one law.

**Generative (the knowledge graph grows):**
- **Introduction** (Granovetter): a knower who holds an edge to `Carol` may grant `Bob` a *new* edge
  to `Carol` — authorized transitive propagation of knowledge. Enforced (`apply_introduce`) to be
  **non-amplifying** (the conferred edge ≤ the introducer's own — *"granted permissions exceed
  introducer's own: amplification denied"*), **consensual** (the target must allow delegation), and
  **time-bounded** (introduced edges expire).
- **Rights amplification**: a *held amplifier* combines with another fact to yield access neither
  names alone — the **sealer/unsealer** pair (`unsealer-knowledge ⊗ sealed-box ⊢ contents`), the
  brand, the mint. "More than the parts" — and it does **not** break the discipline, precisely
  *because the amplifier is connectivity you already hold.*
- **Powerbox / mint / factory**: a designated authority that, by *its own* held authority, *creates
  fresh* edges/resource on an authorized gesture — the legitimate point where new authority enters.
- **Parenthood / endowment**: creating a cell endows the child; initial conditions seed the graph.

**Restrictive (the graph narrows / shrinks):**
- **Attenuation**: narrowing the rights *on an existing edge* (a caveat, a facet subset). This is the
  meet-semilattice "narrow-only" rule — but it governs **one edge's rights**, it is *not* the law of
  the whole system.
- **Revocation / expiry**: removing an edge (one-way / terminal).

**The one law that disciplines all of it — Miller's *"only connectivity begets connectivity"*:**
no ambient authority; you may confer/introduce/amplify *only* authority you (transitively) hold or
hold an amplifier for; every generative act is itself *authorized by held knowledge*, and the
generative ones are *receipt-disclosed* (the conservation typing forces a `Generative`/`Annihilative`
act to appear on-chain, un-strippable). Authority **grows**, but only through *authorized,
non-forgeable* construction. This is the substance of capability security, and it is an **epistemic
non-forgeability invariant**, not a lattice descent.

---

## 4. The three logical structures over a step

Each turn is judged by three *orthogonal* logics (a step may satisfy any subset):

1. **Conservation — a substructural / linear logic.** Resources cannot be copied or discarded for
   free; a `Conservative` move must pair with its dual (Σδ = 0); `Generative`/`Annihilative` moves
   are *disclosed* exceptions bound into the receipt. Conservation is **multi-domain** (balances ⊥
   note-value-per-asset ⊥ gas ⊥ cross-cell), each its own `excess = 0`. The "no free copy/discard"
   of linear logic is here a *security* law (no inflation, no loss), typed per effect
   (`LinearityClass`).
2. **Ordering — a temporal / modal logic.** *When* is a fact final? A four-tier finality lattice over
   one Merkle-CRDT DAG; effects commit at the **join (max)** of the written cells' tiers and never
   downgrade. "Knowledge becomes common knowledge" is the modal ascent up the tiers.
3. **Independence — the I-confluence lattice.** *Which* concurrent inferences commute (can be merged
   without coordination)? The join-semilattice of invariant-preserving merges — the
   coordination-free fragment. The live danger is a fact that *claims* tier-1 independence while its
   invariant is not actually merge-stable.

Conservation is the *linear* skeleton; ordering is the *modal* skeleton; independence is the
*concurrency* skeleton. The turn is where all three meet.

---

## 5. Knowledge crossing a trust boundary (the vat)

Inside a trust root, authority is **positional** ("caps-as-caps": holding the edge *is* the proof,
the mediator enforces it). Across a boundary, it becomes **epistemic** ("keys-as-keys": you must
*present a verifiable witness*, because the far side shares no mediator). The crossing is a
**named-lossy functor** Φ: *permission survives, authority does not* — confinement and
revocable-forwarding are dropped, which is *why* a forwarded capability becomes revocable by
construction. The hosted ↔ sovereign split is this made concrete: a hosted cell's full state lives
with its host; a **sovereign** cell keeps only a commitment and *proves* its own transitions (a STARK
in the public inputs), so a far federation can admit it knowing only how to *check a proof*, never
how to *re-run* the cell. Cross-cell atomicity is then **atomicity-as-proof**: each cell advances
(by execution or by proof), the aggregate must conserve (Σ proven-δ = 0), and they commit together —
with `Partial` commitments letting *several knowers co-sign one inference*.

---

## 6. The receipt is the history of knowledge; the witness is its content

Two coupled chains record the epistemic history:
- the **receipt chain** (per cell, `prev → hash`) is the *append-only log of what was inferred* —
  "the log is the truth, the database is a cache"; and
- the **witness bundle** (the full trace, bound by `witness_hash`) is the *content* that makes the
  inference **replayable** — which is exactly why checkpoint / restore / replay / time-travel are
  *theorems*, not features: you re-seed the unfold from a recorded witness.
Aggregating witness-hashes into one root is **recursive folding (IVC)** — the DAG of all knowledge
compressed to a single checkable claim.

---

## 7. Metatheory vs. verification (why the rename)

- **The metatheory** (this document, and the small Lean core that genuinely encodes it) is the
  *logic*: what a capability/proof/turn *is*; the demand⊣supply adjunction; the generative/restrictive
  authority dynamics and the non-forgeability invariant; the three substructural/modal/concurrency
  judgements; coinductive soundness. It is, deliberately, *candidate-independent* — it would be the
  metatheory of any system built this way.
- **The verification of dregg2** is the (much larger) body of Lean that proves *the dregg2 system*
  realizes that logic — the executable cells, the constraint catalog, the kernels, the protocols, the
  circuit bridges, the FFI cascade.

They interact (verification *discharges* the metatheory's obligations against a real system) but are
**not the same thing**, and conflating them under one name "Metatheory" hid the actual metatheory.
The corpus is being renamed so the verification reads as the verification of dregg2, and *this* —
the constructive-knowledge logic — keeps the name it earned.

> The egg metaphor still holds: we are learning what is inside without cracking it. What is inside is
> a living, distributed, capability-secure organism that *knows things by being able to prove them*,
> and whose life is the disciplined production of authorized knowledge over unbounded time. 🐉🥚
