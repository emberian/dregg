# Discoveries — synthesis of the 7-agent PDF-mining swarm

**For:** the rebuild-driving agent (holds `docs/rebuild/00-synthesis.md` + the spine docs in context).
**What this is:** a cross-cutting weave of seven `pdfs/LEARNINGS-*.md` files, each produced by an
agent that read a cluster of papers against `00-synthesis.md` and was told to be self-adversarial.
This document keeps the conclusions; the per-cluster files hold the grounded detail and `[G]`/`[C]`/`[F]`
(grounded-in-paper / grounded-in-code / forward-design) tags.

Source files (read these for the receipts):
- `LEARNINGS-capability-boundary.md` — Miller, capability-myths, take-grant, EROS, seL4-infoflow, Doerrie
- `LEARNINGS-continuations-await.md` — algebraic effects ×2, delimited & one-shot continuations, effective-concurrency, Concurrency-Among-Strangers
- `LEARNINGS-intent-matching.md` — HOU-undecidability (Coq), full-HOU, winner-determination
- `LEARNINGS-laws-linear-monoidal.md` — Girard, sessions-as-propositions, dependent-session-types, comparison, resource-theory, Selinger
- `LEARNINGS-metatheory-verification.md` — Lean4, Iris, Verdi, Velisarios, IronFleet, Igloo
- `LEARNINGS-ordering-consensus.md` — Byzantine-eventual-consistency, Merkle-CRDTs, CRDT-comprehensive, Mysticeti, Narwhal, local-first, cryptoconcurrency
- `LEARNINGS-keys-proofcarrying-schema.md` — Appel PCA, Garg PCA-intro, Macaroons, UCAN, Preserves, safe-schema-evolution

---

## 1. The headline: one seam, four independent derivations

The **VERIFY-tractable / FIND-intractable** split appeared in four agents that did not share notes:

| Agent | The intractable "find" | The tractable "verify" |
|---|---|---|
| continuations | finding/checking a correct handler is **undecidable** (Pretnar §6) | running a handler |
| intent-matching | **HOU undecidable**, bites at 2nd-order / the *flex head* = a variable in function position (Spies-Forster, machine-checked in Coq) | first-order / Miller-pattern matching is decidable, mostly poly |
| keys / proof-carrying | PCA **proof-search undecidable** (Appel-Felten) | proof-checking is linear |
| the two laws | the Predicate ⊣ Witness **Galois connection** is the order-theoretic shadow of exactly this | — |

**Promote this from "the intent matcher is bounded" to a system-wide principle:** every gate checks
cheaply; every *search* (match a fill, find a delegation path, find a handler, find an ordering) is
intractable and must be an **untrusted plugin that emits a checkable witness**. **TCB = the verifier,
never the solver.** Soundness is *by verification*, not *by construction*. This is the unifying law under
the await-family, the matcher, the auth-path search, and the finality search.

---

## 2. Two more convergences (high confidence — multiple agents agree)

**(a) "Membrane" is the wrong word.** Independently: capability-boundary (Miller's "membrane" is
narrowly a *transitively-applied revocable forwarder* — a pattern, not a trust boundary) + laws agent
(the boundary wants the *intuitionistic* presentation that enforces locality) + the user's own earlier
instinct. **Rename: vat / trust-root boundary** for the seL4-grain; reserve "membrane" for the
revocable-forwarder pattern dregg may add separately.

**(b) caps→keys loss is exact.** The forgetful functor Φ drops *precisely* Miller's Property F
(access-controlled delegation ⇒ confinement) + Property E in practice (composability ⇒ revocable
forwarders) [capability agent] = loses the mediator's structural guarantee, confinement, cheap
revocation, live interposition [keys agent]. So caps→keys makes the **Confinement** and **Irrevocability**
myths *true again*. **Φ⁻¹ needs a trusted minter.** PCA recovers public-verifiability + richer predicates,
**not** revocation or confinement. ⇒ "caps-inside / keys-between" is now a theorem with a stated loss,
not a slogan. The vat-boundary is principled-lossy *in a named direction*.

---

## 3. Corrections the swarm earned into `00-synthesis.md`

These are grounded; recommend applying them.

1. **Vocabulary:** membrane → **vat / trust-root boundary** (§ everywhere). Reserve "membrane" = revocable forwarder.

2. **Categorical base is wrong-sized.** It is **not** a "thin posetal category" — a thin category can't
   carry a nontrivial symmetry iso, which Law 1 needs. It is a **symmetric monoidal category, thin only in
   its ordering fragment** (Coecke-Fritz's two-layer SMC ↔ commutative-preordered-monoid split). Conservation
   stated structurally = **withholding the cartesian copy `Δ` and erase `◇` maps** (Selinger §6; = Girard's
   no-contraction/no-weakening). Headline theorem:
   > `conservation_comp`: `Σ_k` is a **strong monoidal functor** `(TurnCat, ⊗, I) → (ℕ, +, 0)`, **constant on
   > every non-mint/burn hom-set**.
   Note it's **invariance (`=`)**, stronger than a Coecke-Fritz monotone (`≥`); mint/burn are explicit typed generators.

3. **Fork is provably NOT a coproduct.** A coproduct re-imports the cocartesian merge-for-free that resource
   categories specifically lack. Fork/merge = `⊗`-manipulations + attenuation side-conditions. Kill the latent over-claim.

4. **Predicate ⊣ Witness is a `GaloisConnection` + `HeytingAlgebra`, not a heavy `Adjunction`** — both sides
   posetal, far cheaper in mathlib4; "half-wired" = the one-sided stub. (All mathlib paths verified present in `~/src/mathlib4`.)

5. **Drop "turn = free model of await".** Continuations are the *one* effect that is **not** algebraic
   (Plotkin-Power). The await substrate is **two layers**: a gate-engine (a handler / algebraic model) +
   a continuation-capture primitive (delimited continuations à la Dybvig prompts / `runCC`). And more
   precisely: **a turn IS the rollback handler** (Plotkin-Power §6.8 carries the held-until-commit list verbatim —
   commit = replay log, abort = discard = conservation-preserving refund). The deferred-prover keystone =
   "the commit-replay handler also emits the witness at the vat boundary."

6. **Qualify "the CDT IS the proof" (01-spine).** Miller's BA-vs-TP (Table 8.1): the path/CDT proof attests
   **permission (de-jure)** — sound — but **not authority (de-facto)**, which is *behavioral, recovered from the log*.
   A caretaker/forwarder makes the static cap-graph *lie* about real authority. This is the formal grounding of
   "truth is the log, not the cap-graph": the proof says you were *permitted*; what a cell can *eventually do* is BA.

7. **The 4-corners regime gains a well-formedness side-condition.** From BEC's theorem (a partition-tolerant,
   Byzantine-immune replica preserves an invariant **iff** all concurrent transactions are **I-confluent**:
   `I(x) ∧ I(y) ⇒ I(x ⊔ y)`): a cell may select **tier-1 (causal-only) ordering only if its state is a bounded
   join-semilattice with invariant-preserving joins.** The corner "tier-1 ordering + non-I-confluent invariant"
   is **unrealizable → a static type error**, not a runtime boundary concern. This also bounds §5.2 *sets-as-cells*:
   **hash-keyed nullifier uniqueness is tier-1-safe precisely because it is I-confluent; `balance≥0` is not**
   (needs ≥ tier-2/3, or single-owner per cryptoconcurrency).

---

## 4. Grounded facts worth recording (not corrections — confirmations with teeth)

- **The blocklace is a proven object.** Merkle-CRDT proves a Merkle-Clock DAG **is** a G-Set CvRDT
  (join = set union); BEC's `(v, hs, sig)` hash-DAG is the same shape. The blocklace is a join-semilattice CvRDT — grounded, not aspirational.
- **CryptoConcurrency independently re-derives per-cell finality:** single-owner state never needs consensus;
  shared state needs it **only on an actual overspend attempt** (dynamic). **Conflict is not pairwise** — three
  individually-fine spends can jointly overspend — so escalation triggers must be **sum/coverage predicates over
  the whole concurrent set**, not pairwise checks.
- **"One DAG, pluggable finality on top" is validated:** Narwhal separates dissemination (always-available DAG
  mempool) from ordering (pluggable); Mysticeti's uncertified-DAG + fast-path = "single-owner needs only reliable
  broadcast, not consensus" — same theorem-line, same DAG.
- **PCA = the auth-in-proof recovery, near-perfectly.** "Authorization = a proof in a logic the verifier checks,
  not an ACL" *is* "the PI attests the actor was permitted." Keep the in-circuit policy check decidable
  (Mina `spec_eval`-shaped lattice / Garg `says`/`controls` fragment); push delegation-path/∃-fill search into the
  deferred prover (= the §1 seam, one level up).
- **Discharge family confirmed mechanically:** a macaroon **third-party caveat** `cav@Loc⟨cId,vId⟩` discharged by a
  named gateway's separate proof = dregg's `ConditionalTurn`/`Await`; `bindForRequest = H(M'.sig :: M.sig)` = the
  intent-seal / binding-site. UCAN = DID-rooted attenuation-down-a-chain = keys-as-caps as a provenance log.

---

## 5. Concrete artifacts now specified for `./metatheory` (forward-design, paper-anchored)

- **Layout & order:** ~6–8 modules (Core / Laws / Authority / Boundary / Finality / Oracle). **State every
  theorem on day 1 with `sorry` bodies; discharge Core (category laws) + Conservation (the monoid-hom) first;
  the vat-boundary law LAST.** Mirrors l4v's "spec-first, grind up."

- **Vat-boundary law = two theorems** (the seL4 integrity case-split lifted: `part s ⤳ p` vs `part s ⤳̸ p`,
  subject→trust-root, transition→turn):
  - *intra-vat*: positional authorization (`∃ cap ∈ caps`, a mediator slot-read) admits the **trivial** witness.
  - *cross-vat*: admissibility ⇔ `Discharged P w` (`Verify P w = true`).
  The crypto substitution is **literally replacing the positional ∃ with the decidable verification** — a freely
  copyable, verifier-checkable object, no off-island mediator. Companion: authority confinement (the policy is an
  upper bound; no growth). Plus a `LossyMorphism` theorem: **structural unforgeability → cryptographic
  unforgeability, loss = revocation-by-construction** (= §2(b)).
  - *Existence proof it can be carried:* Doerrie's axiom-free, machine-checked Coq confinement proof has exactly
    this shape (`mutable` over-approximates `mutated`; the confinement test is **local to the minted caps** — a
    direct model for the deferred-prover's boundary check). **Still to read: the actual l4v integrity theorem in
    `~/dev/l4v` — neither the capability nor metatheory agent read it; it is the literal template to copy into
    `Authority/Positional.lean`.**

- **Matching:** `no_general_matcher` via a **reduction `HOU ⪯ GeneralMatch`** (Coq synthetic-undecidability style:
  axiomatize the HOU result, prove the one reduction) + dual `firstOrderMatch_decidable` (certifies the RingSolver
  fragment) + a `MatcherPlugin` contract requiring **soundness-by-verification only** (completeness/termination
  explicitly NOT required). Clearing honesty (Sandholm): Winner-Determination is NP-hard, **no PTAS**,
  inapproximable past ~`m^{1/2}` — a matcher plugin may only promise the tractable structured cases
  (interval/contiguous, single-item, submodular).

- **Await:** one `Await`/`Resolver` inductive (`named | gateway | exists P | registry`) — re-justifies W3-I as one
  primitive, not a fourth variant; **one-shot (linear) continuation typing**, with conservation falling out as a
  corollary (Dolan's runtime "raise on 2nd continue" becomes *derivable*, not ad-hoc). Multi-shot is sound only for
  non-conserved / `Copy` payloads (typed promotion rule). Held-until-commit = the rollback handler.

- **Conservation / category:** mathlib `MonoidalCategory` + `SymmetricCategory` (Law 1);
  `Preorder.smallCategory` for the thin ordering fragment (Law 2); `Order.GaloisConnection` + `HeytingAlgebra`
  (the adjunction). Open: whether rollback/time-travel needs a **traced** monoidal structure (Selinger §5).

- **Finality:** a `FinalityRule` trait with `admits(invariants, actions)` running the **I-confluence check** as a
  soundness gate; a **cell-state lattice requirement** as the tier-1 eligibility criterion; a **cross-tier
  composition rule**: *a turn commits at the **join** of its written cells' tiers; effects held until the join-tier
  commits; no finalized value downgrades; Law-1 (conservation) is tier-independent and only prunes the order search.*
  Finality-tier proof template (Velisarios): quorum-overlap lemma + certificates + agreement-from-past-events;
  **parameterize σ** instead of hardcoded `½(n+f)`. Realistic scope = **tier-3 BFT safety**; out of scope for now =
  liveness (only IronFleet does it, at huge cost), view-change, and the witness's crypto-soundness (a *circuit*
  obligation — **never merge it into the Lean law**; put the §8 caveat in the metatheory README).

- **Bridge:** wire the executable Lean core in as **backend #8 of the existing `dregg-dsl-differential` harness**,
  as the golden oracle (IGLOO's refinement *contract* — "verifier accepts ⇒ impl refines spec" — discharged
  *empirically*; honest caveat: over `sorry`'d regions it's cross-validation, not certification). A Lean
  `def … deriving DecidableEq/Repr` is *simultaneously* the proof target and a runnable `Verify P w : Bool` —
  this directly answers the peers' "huge-TCB / doesn't cohere" complaint. **Iris is overkill** for the skeleton/laws;
  reserve it (or a hand-rolled PCM argument) for the one future obligation that needs it: the concurrent live-session
  interior (`CapSession`).

- **Auth-in-proof STARK statement (6 clauses):** key → delegation → policy-entailment → effect-fold → replay →
  cell-root binding (cross-PI-bound). This is the composition that turns an effect-transition proof into a turn proof.

- **Schema / Preserves (closes both EffectMask bit-fragility AND frozen-AIR with one idea — identity = hash of
  canonical data-model value):** cell-state = name-keyed `Record @schema #"air-id"`; facet = canonical **Set of
  effect Symbols** (adding `transfer` adds an *element*, never shifts bit positions); `AIR-id = H(canonical(schema_decl))`;
  caps embedded as Embeddeds (= the caps→keys conversion point). Schema evolution = lazy per-cell `@schema` versioning
  + `migrate-on-read`; the relational-evolution result (lazily-migrated ≡ fresh-at-v2) transfers as a
  **commitment-equality obligation** on a `migrate-air`. **Joined with linear-drop:** a DROP over a *linear* slot must
  emit a conservation obligation (`Σ before = Σ after + Σ explicitly-dropped`) — so **an upgrade is sound iff
  transparent (the equality) AND conservative (linear-drop).** Caveat: forbid Preserves `Double`s and pin Embedded
  canonicalization before hashing committed state; the transparency theorem is linear-chain only (schema-DAG /
  fork-merge migration is open).

---

## 6. Two grounded code-checks to run now

1. **`finality.rs`:** confirm DAG heads are summarized **by hash, not vector-clock counters** — BEC §4.2 shows
   vector clocks are forgeable by a Byzantine node. (Real soundness check, not a design musing.)
2. **Audit `MatchSpec`:** is it *ever* genuinely 2nd-order today (a variable in function position), or is
   matching-undecidability currently **future-proofing** rather than a live concern? Decides how much of §1's
   matcher machinery matters *now*.
3. *(Minor)* macaroon HMAC shared-secret ≠ third-party-verifiable — use *structure*, not HMAC, for cross-domain caveats.

---

## 7. Next reads the agents explicitly queued

- **The actual l4v integrity theorem in `~/dev/l4v`** (Isabelle) — flagged by *two* agents as unread; the literal
  template for `Authority/Positional.lean` and the vat-boundary law.
- **Hyland-Levy-Plotkin-Power, "Combining algebraic effects with continuations" (TCS 2007)** + Bauer-Pretnar —
  required *before* making any "free model of await" claim in Lean (continuations aren't algebraic).
- The separate **Preserves *Schema* spec** (we have the core spec, not the schema spec) — for the schema-DAG /
  fork-merge migration gap.
- take-grant / typed-access-matrix for schema-DAG attenuation; `revocable-proof-systems.pdf` (already in library)
  for the revocation gap that keys-as-caps can't close.

---

## 8. Net

The seven adversarial readings **confirmed the skeleton** (turn = generator; cell/cap/proof = projections;
conservation + ordering = two laws) and **converged hard** on the verify/find seam and the caps→keys loss — but they
**corrected six specific claims** (the §3 list) and **sharpened the metatheory targets from prose into stateable Lean
theorems**. Nothing here is architecture-blocking; it's the difference between "the ideas cohere" asserted and the
same claim made precise enough to type-check. The single most load-bearing unread artifact is the **l4v integrity
theorem** — read it before writing `Authority/`.
