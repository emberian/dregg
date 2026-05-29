# 00 — Dragon's Egg Rebuild: Synthesis

> **Status:** the capstone of a multi-agent research + design interlock (2026-05-29). It
> weaves: the three spine explorations (`01`/`02`/`03`), five grounding studies (houyhnhnm,
> substrate/categorical, circuit-semantics, blocklace, readiness), three portability studies
> (Spritely, lineage, code-reality), two ancestor studies (constitutional/grassroots, Mina),
> and two integration studies (token/caveat/discharge, intent). Current-state claims are
> `file:line`-grounded; everything else is forward design for "rebuild **under and through**,
> not layer upon." The user has accepted substantial overhaul.
>
> **Provenance note:** several inputs returned inline (not to disk). This doc is the durable
> record. Where it says "a study found," that is one of the agent reports above.

---

## 0. The thesis in one breath

**Dragon's Egg is two ancestors' visions, each half-inherited, with a third philosophy
unrealized on top. The rebuild *completes the inheritances* rather than inventing:**

- From **Shapiro/grassroots** it got the *substrate* (the blocklace = a liquid CRDT) but built
  **solid-first** and bolted the liquid modes on (sometimes literally `#[cfg]`-compiled-out).
  → **Recover liquid-first**: finality becomes a per-cell *phase* on a pluggable menu (config,
  not rewrite).
- From **Mina** it got the *data model* (account≈cell, account-update-forest≈CallForest,
  8-field state, permission lattice, control coproduct, receipt chain) but **dropped the
  soundness model** — Mina binds authorization *in the proof*; dregg checks it in a *trusted
  executor*. → **Recover auth-in-proof**: compose the existing auth-AIR + permission-lattice +
  EffectVM into one proof whose public input is the committed, authorized turn ("proof is
  truth").
- From **houyhnhnm + Spritely + seL4/EROS** comes the *unrealized philosophy*: orthogonal
  persistence (the log is the inputs), capability discipline, full-abstraction membranes,
  linear resources, portable persistent objects. dregg already re-derived its three strongest
  tenets from cryptographic necessity; the rebuild makes them first-class.

The rebuild is therefore **mostly recovery + composition + collapse**, not green-field. That is
the honest, motivating framing.

---

## 1. The categorical skeleton (what the three spines converged on)

Three adversarial spine explorations (capability-as-spine, cell-as-spine, proof-as-spine) each,
pushed hard, **shed the same two things they could not own: conservation and ordering.** That
convergence *is* the structure:

> **The turn (morphism) is the generator. It has three faithful projections — none total — and
> sits under two ambient laws no projection owns.**

> **Update (`dregg2.md §2`, `study-choreography`):** "two laws" names the two ambient *category
> structures* (conservation, ordering). dregg2 carries a **third, orthogonal judgement** per
> turn — **I-confluence** (invariant-merge: do concurrent writes merge invariant-safely?) — which
> is **NOT** derivable from conservation or ordering and is **NOT the session type**. Read
> "two laws" below as the two ambient structures; treat I-confluence as a co-equal third
> judgement (`dregg2.md §2.3`).

- **Cell** = the **endpoint** projection (what an arrow lands on). `CellLifecycle`,
  `FieldVisibility` are *attested properties* of endpoints.
- **Capability** = the **gate/authority** projection. Here "proof is truth" is *native*: an
  exercise *is* the traversal of an authorized arrow (`01-spine-capability.md §2`).
- **Proof** = the **witness** projection (`03-spine-proof.md`); the executor is demoted to a
  cache + witness-builder.
- **Law 1 — Conservation** = the linear/symmetric-monoidal structure on the category
  (`LinearityClass`, `turn/src/action.rs:698`, exhaustive no-default match). All three spines
  keep it as irreducible. **`Σ_k` is a monoid-homomorphism `(Turns,∘) → (ℕ,+)` + invariance on
  ordinary turns** (`dregg2.md §2.1`, `Core.lean`); the "strong monoidal functor" packaging is
  decorative — the monoid-hom + invariance is the load-bearing content.
- **Law 2 — Ordering** = which arrows compose into which strand = canonicity = consensus. Both
  cap- and proof-spines independently proved this is **not subsumable** by any projection.

The honest categorical reading (from the substrate study, correcting the `docs-old` over-claim
of products/pushouts/F-algebras): a **symmetric-monoidal category, thin only in its ordering fragment** (correction — `discoveries §3.2`: NOT a plain thin posetal category; a thin category cannot carry the non-trivial symmetry iso Law 1 needs) — objects = cell states,
morphisms = turns over a *flat* action sequence — enriched with a **Heyting predicate algebra**
and a **`Predicate ⊣ Witness` adjunction** that is *named in code but only half-wired*
(verifiers still `NotYetWired`). The cell-spine verdict: **two co-primary primitives** (cell +
morphism), *not* one — a capability is a *morphism/relation*, a strand is a *log/arrow*;
forcing either into "cell" is a category error. Branch/merge, presheaf-views, monoidal
multi-cell turns are **not free** in this base — they must be built (and `Fork` is **not** a
categorical coproduct; calling it one repeats the over-claim).

Mechanical realization (Spritely): **a turn is a transaction whose outgoing effects are held
until it commits.** That one rule realizes conservation + ordering and gives rollback +
time-travel for free.

---

## 2. The trust-boundary / phase model (the operational core)

> **Terminology correction (`discoveries §2a/§3.1`):** the boundary object below is the
> **vat / trust-root boundary**, NOT a "membrane." Miller's *membrane* is narrowly a
> transitively-applied **revocable forwarder** (a pattern, not a trust boundary); reserve
> "membrane" for that revocable-forwarder pattern dregg may add separately. The crossing
> seam where caps↔keys convert and the witness side of `Predicate ⊣ Witness` becomes
> mandatory is the **vat-boundary**.

### 2.1 The cell is the vat-boundary; three grains
- **Cell = the sync / vat-boundary grain** (Spritely's *vat*: *near* = synchronous caps-as-caps,
  *far* = async keys-as-caps).
- **Host / principal = the trust-root grain** ("I trust my MacBook" / an seL4 CSpace). *New vs
  the lineage*, which rooted trust in the federation committee (`federation_id = H(committee)`);
  rooting it in the host is the seL4 bridge.
- **Reference-group = the consensus-topology grain** (the finality dial of §4).

A host runs *many* cells with local-async between them → a **graduated vat-boundary**:
sync-within-a-cell → async-local between same-host cells → async-remote off-host.

### 2.2 caps-as-caps vs keys-as-caps — and why proof-is-truth forces keys
- **caps-as-caps**: positional, mediator-enforced, unforgeable by *construction* (seL4 CDT; a
  live CapTP session; a trusted executor *within its boundary*). No secret — possession of the
  slot *is* authority.
- **keys-as-caps**: epistemic, crypto-unforgeable, *freely copyable* (knowing a key / holding a
  derivation proof *is* authority).
- **Demoting the executor to a cache (proof-is-truth) removes the mediator → authority must be
  epistemic.** So "the best dregg can do is keys-as-caps" is the *dual* of the inversion we
  chose. caps-as-caps survives only on **mediator islands** (seL4 kernel, live CapTP session,
  trusted host). The **vat-boundary is the caps↔keys conversion point**, principled-lossy:
  caps→keys drops the mediator's structural guarantee; keys→caps needs a *trusted minter* to
  re-establish one.

### 2.3 Liquid-first: porous by default, crystallizing to rigid by configuration
The recovered vision (`paper/sections/06-fabric.typ:178`): *"federation-as-spectrum … solo dev
(n=1) → startup → DAO → public network — **No separate code paths — only configuration of the
reference group**."* The substrate's **default phase is liquid** (local, mediated, gossiped,
plain-logged, *unproven*); **rigidity is a phase a boundary crystallizes into, locally, on
demand**:
- a local cell gets *shared* → its vat-boundary crystallizes a **proof obligation**;
- a casual friend-group decides to be *auditable* → its boundary crystallizes a **finality
  rule** (§4);
- a trusted-on-my-host app gets *exported/migrated* → the transcript crystallizes into a
  **portable, self-attesting cell** (§6).

Every inversion is the same phase transition at a different altitude:
proof-at-boundaries-not-keystrokes, caps-inside/keys-between, log-within/proof-across,
liquid-default/rigid-on-demand. Set **per boundary, by configuration** — a gradient, not a
binary. *The code today implements only the solid end and treats liquid as an escape hatch.*

### 2.4 Proof = the export format of the log; prove retroactively
- **Within a boundary the log is the manifest truth** (houyhnhnm orthogonal persistence; the
  `WitnessedReceipt` chain is *explicitly* "the persistence layer; the DB is the cache; the
  chain is the truth," `turn/src/turn.rs:6-38`).
- **Across a boundary the proof is the truth** — but it is just the *export format* of that log,
  generated **lazily, retroactively, at the crossing**.
- **Safety needs two axes** (Spritely): (1) **cheap eager pin** — append-only, causally-pinned
  receipt chain (`previous_receipt_hash`), prevents history-rewriting before proving; (2)
  **capability-sealed serialization** — an exporting/teleporting cell must not serialize
  authority it never held.

---

## 3. The universal gate (`WitnessedCondition`) and the await family

### 3.1 The gate
The four cell-side gates **collapse to one** `WitnessedPredicate` (confirmed: `Precondition`,
`StateConstraint`, `CapabilityCaveat`, `Authorization::Custom` all wrap it). The token side
shares the **binding input** (`AuthRequest`) but keeps a *distinct engine*. So the unification
is **"binding-site + engine," not "one caveat = one predicate":**

```
WitnessedCondition {
    binding: BindingSite { when: block_height, input: AuthRequest-facts, signed_by: issuer|cell },
    engine:  Datalog            // logic-eval (biscuit/macaroon)
           | WitnessedPredicate // proof-verify (STARK/Merkle registry)
           | Await,             // deferred-resolution (the continuation family — §3.2)
}
```

A gate is satisfied by **logic**, by **proof**, or by **awaiting a resolution**. Keep Datalog
and WitnessedPredicate as **two coherent sibling engines** (merging the *vocabularies* would
regress; the design agrees — `TOKEN-CAPABILITY-UNIFICATION.md:81`). Note: `Custom { vk_hash }`
in the predicate registry is *explicitly modeled on* the macaroon `CaveatType` ID-range registry
— the surfaces already converge on one registry idiom.

### 3.2 The await family = one continuation primitive, four faces
*A suspended morphism awaiting a predicate-satisfying resolution.* The codebase has all the
shapes but **they do not share a type**:

| Face | Resolver | Visibility | Code today |
|---|---|---|---|
| **zkpromise / zkawait** | *specified* party | private, point-to-point | `ConditionalTurn` + `ProofCondition` (`turn/src/conditional.rs`); CapTP promise |
| **discharge** (3rd-party caveat) | *named gateway* | semi-private | `macaroon` 3p caveat + `discharge_gateway` — *isomorphic* to `ConditionalTurn` |
| **intent** | *any* filler satisfying P (∃) | broadcast / market | `intent/` — fulfillment *literally* builds a `ConditionalTurn` (`fulfillment.rs:762-849`) |
| **(promise-graph)** | named, with cascade | registry | `PendingTurnRegistry` + `ResolutionCondition` (`turn/src/pending.rs`) |

**Intent is the inverse vat-boundary.** A vat-boundary gates a *complete* morphism crossing out
(proof of what passes); an intent gates the *missing half* (predicate on the filler) — same gate
machinery, opposite direction. An intent is a **continuation with an existentially-quantified
hole**: `λ(fill satisfying P). effects`.

**The VERIFY/FIND complexity seam (a real boundary):**
- **VERIFY a claimed fill = tractable** (predicate evaluation — the universal gate). Every face
  is cheap to check.
- **FIND a fill (matching) = undecidable in general** (existential predicate∩predicate). The
  intent code *structurally avoids* this: `RingSolver` is a bounded Johnson-cycle search over
  *structural* compatibility (`asset==asset ∧ amount≥want`), `max_ring_size`-capped; predicates
  are **one-sided fulfiller obligations, verified-not-solved** (`intent/src/solver.rs:219-318`,
  `matcher.rs`). **So "matching strategy" is a bounded, pluggable, domain-specific solver — like
  finality is a pluggable phase. A *general* matcher is provably out of reach.** Conservation
  *constrains* the search (`check_settlement_conservation`, `trustless.rs:643`) — prunes, does
  not decide.

### 3.3 The unification move (W3-I, now fully scoped)
1. Add `ResolutionCondition::AwaitFiller { predicate: WitnessedPredicate, conservation }` to
   `turn/src/pending.rs` — the **∃-resolver** variant the substrate lacks.
2. Replace `MatchSpec.predicate_requirements: Vec<PredicateRequirement>` with
   `Vec<WitnessedPredicate>` (the `predicate.rs` docs already assume this) — collapse the
   third predicate vocabulary.
3. Make `intent::fulfill` a thin shim over `PendingTurnRegistry::submit_pending` + `resolve`,
   running conservation + the canonical verify, escalating to the batch/consensus path **only
   when contended** (private intents stay on the local liquid fast path).
4. Fold **discharge** in as the `Await` engine of `WitnessedCondition` (presented-not-fetched).

→ **One continuation primitive** subsumes zkpromise/zkawait, discharge, intent, ConditionalTurn,
CapTP-promise.

---

## 4. Law 2 made concrete: the pluggable finality menu

The blocklace is a **CRDT** ("no global coordination or consensus"; partition/async-tolerant via
*eventual delivery*, not GST; Byzantine equivocation "harms only a finite prefix"). **Total
order is not in the blocklace** — it is added by τ (Cordial-Miners) *on top*, and dregg's
`τ_unified(B, G, C)` already runs τ *per reference-group*. The remaining work is small: make
`C` select the **finality rule**, and lift the hardcoded `½(n+f)` fault-bound into group config.

| Tier | mechanism | n / membership | quorum | synchrony | partition behavior |
|---|---|---|---|---|---|
| **1. Causal-only / CRDT** | add block; causal partial order | n=1+ | none | none | **never blocks** (phones over Bluetooth keep working) |
| **2. Ack-threshold** | settle on k acks, no leaders | small set | k-of-m (config) | none for safety | degrades to tier 1 |
| **3. Cordial-Miners τ-BFT** | waves + leader + 3-step ratify | known Π, n≥3 | ½(n+f) | GST or async | **stalls** on partition, resumes after GST |
| **4. Constitutional** | τ-BFT + self-amending `(P,σ,Δ)` | known P, PKI | σ (amendable, h-rule) | partial-sync | stalls + wall-clock deadline |

**Same DAG carries all four; a block written under tier 1 can be finalized under tier 3 later if
a group decides to order it** — crystallization (liquid→solid) at the finality layer. Tier 1 is
the liquid default that constitutional's σ∈[½,1) *provably cannot express*.

**On constitutional consensus (the user's "not directly, maybe"):** adopt its **amendment rules**
(h-rule, Sybil-resilient amend-P/σ/Δ) *as the tier-4 governance plugin* — they're local to a
group. **Reject as universals** its four globalism seams: single global total order;
GST-as-precondition-for-*any*-progress; fixed σ-quorum (forbids n=1); the synchronized wall-clock
voting deadline. The grassroots family's *own* layering confirms this: Constitutional Consensus
is the *bottom* sub-layer; organic federation (Participate/Federate/Join/Leave — dregg's "n=1
grows, no genesis ceremony") is on top. **Shed** grassroots' fairness/convergence machinery
(sortition, proportional representation) — a GST-shaped large-DAO option, not a law;
graceful-partition-fork lives in the blocklace/CRDT layer instead.

---

## 5. Keep / Diverge / Recover (grounded tables)

### 5.1 Keepers (faithful core — do NOT rewrite)
- **houyhnhnm-faithful, crypto-derived:** the capability substrate (`cell/capability.rs` +
  `facet.rs` + `Authorization`); `WitnessedReceipt`-as-persistence; `LinearityClass`;
  `CellLifecycle` terminal objects; `FieldVisibility` selective disclosure.
- **Mina-inherited, genuinely good:** the **permission lattice** (None/Either/Proof/Signature/
  Impossible + dregg's `Custom{vk_hash}`) — adopt Mina's in-circuit `spec_eval` (3-bool circuit)
  directly when auth moves into the proof; the **Authorization coproduct** (a faithful, richer
  extension of Mina's `Control.t`); **`proved_state`** semantics; the **receipt chain** — and
  *lean in* to Mina's **RFC-0006 receipt-chain-proving** + its in-circuit `Checked` cons (the
  precedent for the deferred-prover); **`CommitmentMode::Full|Partial`** (a *good* dregg-native
  divergence Mina lacks — serves multi-party turns).
- **token-side:** the **biscuit/macaroon split** (it *is* the inside/between vat-boundary, enforced
  by W3-F); `AuthRequest` as the shared binding-site; block-height-as-clock; the sorted-Merkle
  non-membership revocation type (already shared token↔cell).

### 5.2 Diverge / collapse (overhaul-accepted)
- **Sets → cells** (highest-leverage simplification): nullifier/revocation/authorized-sender
  sets are executor side-tables (`nullifier_set.rs`, `journal.rs:378`) with no `CellId`; make
  them cells whose state is a set-root + append-only program, so `MerkleMembership`/`NonMembership`
  query them through the existing slot-root path. *No principled reason they aren't cells.*
- **Four gates → one `WitnessedCondition`** (binding-site + engine; §3.1).
- **The CallForest tree → flatten or give it real frames.** Confirmed: dregg copied Mina's tree
  *and the `May_use_token` enum* (→ `DelegationMode`) but never built the caller/`caller_caller`
  token-owner frames that make Mina's tree load-bearing — so the modes are *dead* (only `None`
  enforced). Either rebuild frames around dregg's *capability* model, or flatten to
  `Vec<Action>` + explicit `Introduce` effects (what the executor honors today).
- **8 fixed state slots → content-addressed variable state.** A global-uniform-circuit artifact
  (`Nat.N8`); dregg's heterogeneous cells already strain (RateLimit/BoundDelta/CapabilityUniqueness
  can't fit and fail to executor passes). Keep the *commitment* discipline; drop the fixed arity.
  Pairs with houyhnhnm's typed-schema-upgrade and Spritely's **content-addressed descriptors**
  (facet/interface identity = hash-of-canonicalized-description, not bit position — closes the
  bit-positional `EffectMask` fragility *and* the frozen-AIR schema-upgrade gap).
- **Merge the capability representations:** collapse `Breadstuff` (still a bare 32-byte hash)
  into `Token`/`Bearer`; unify the two attenuation checks into one order relation.
- **Unify revocation substrates:** fold cap/bearer tombstone-channel into the Merkle
  non-membership accumulator (one revocation substrate).

### 5.3 Recover (the two inheritances)
- **auth-in-proof** (Mina): compose auth-AIR (`schnorr_air`/`native_signature_air` exist) +
  permission-lattice (`spec_eval`) + EffectVM into one statement whose PI is the committed
  authorized turn. Today auth is plain Rust in `authorize.rs`; the proof binds only
  `(action,resource)` and *excludes* auth/replay fields (`binding.rs:8-12`).
- **liquid-first** (grassroots): promote finality to a per-cell config phase (§4); un-gate the
  attestation paths the code compiled out (`peer_exchange` STARK is `#[cfg(zkvm)]`, off by
  default).

---

## 6. What exists in embryo vs what's missing

**Exists (un-unified / not first-class / sometimes off-by-default):**
- trusted interior + plain log: no-STARK sovereign-witness path (`cipherclerk.rs:4537`, executor
  re-executes, `execute.rs:391-580`); `peer_exchange` signed deltas (sig-only by default).
- cheap eager pin: the `previous_receipt_hash` chain, *framed as the truth* (`turn.rs:6-38`).
- proof = export of log: `WitnessBundle` retains the trace; scope-2 *re-verifies*.
- live caps-as-caps interior: `CapSession` export/import/promise tables (`captp/session.rs`).
- porous-vs-rigid knobs (scattered — *unify these into one phase*): sovereign-vs-hosted mode;
  optional `transition_proof`; opt-in `effect_binding_proofs`; Phase-2-vs-Phase-3.
- the await shapes (§3.2); the bounded intent solver; conservation checks; commit-reveal.

**Missing (the real new work):**
1. **The deferred-prover** — a driver that consumes a no-proof receipt-chain segment and emits
   proofs *retroactively at a vat-boundary*. Substrate exists; only the "prove from the kept log on
   demand" driver is absent. **Keystone.**
2. **First-class trust-boundary / vat-boundary / phase type** (no `island`/`TrustBoundary` type
   exists; the four scattered knobs are the same liquid↔solid dial).
3. **Intra-island fast path for cross-cell turns** (atomic turns are proof-uniform today — the
   reason "atomic cross-cell turn" never cohered).
4. **auth-in-proof composition** (§5.3).
5. **The await unification** — `AwaitFiller` ∃-resolver + one predicate type + intent-on-registry
   (§3.3); wire the **token-revocation** check (W3-F never checks `not_revoked`).
6. **Fork / merge** — the one hole *both* vision and code lack (only `DelegationMode::SnapshotRefresh`
   seed). Design: `merge = re-root iff every edge stays a monotone attenuation` (cap-spine §4.2)
   + capability-sealed recipe serialization (Spritely).
7. **Cell teleport/exit/autarky transport** — `migration.rs` is a freeze/timeout state-machine
   with **no bundle, no log/state transfer, no production caller**. The *zero-cost intra-fabric*
   model (membership-edit, shared DAG) + "ship `(id, head, rule)` + receipts" is the cleaner
   target than the heavy eager FREEZE/EXPORT protocol.
8. **On-chain mint/grant** (token P4-P5 unbuilt; `GrantCapability`→biscuit-block; capability tree
   as a view over the delegation graph).

---

## 7. Sequenced "rebuild under" plan

Cheapest-leverage first; each step *removes* trusted-executor surface or *unifies* a zoo.

1. **Collapse (cheap, high-leverage):** four gates → `WitnessedCondition`; **sets → cells**;
   CallForest → flat (or real frames); merge `Breadstuff` into `Token`/`Bearer`.
2. **The deferred-prover over the receipt chain** (keystone) + the first-class **phase** type
   (unify the four scattered knobs). "Inside" = append to the chain without proof; "vat-boundary" =
   where `require_scope2_witness` / a proof is required.
3. **auth-in-proof composition** (the Mina recovery) — compose auth-AIR + `spec_eval` + EffectVM;
   delete `authorize.rs`'s trust as each gap closes; `effects_hash` becomes an in-circuit fold.
4. **The await unification** (`AwaitFiller`, intent-on-registry, discharge-as-engine, token
   revocation) — W3-I, now whole.
5. **Pluggable finality** (the grassroots recovery) — `C` selects the tier; `½(n+f)` → config;
   constitutional rules as the tier-4 plugin (minus the four globalism seams).
6. **Fork/merge** + **portable-cell transport** (zero-cost intra-fabric + sealed recipe export).
7. **Content-addressed descriptors** (facet/AIR identity by hash; typed schema upgrade) +
   **ZK** (port EffectVM onto `HidingFriPcs`) — last, over an otherwise-complete statement.

This **subsumes the pending wave-3 lane W3-I** and reframes it: it was always an instance of
"make the proof attest more, trust the executor less, unify the await shapes."

---

## 8. Metatheory hook (`./metatheory`, Lean4)

Not decoration — a stress-test of whether the turn-as-generator *actually generates everything*.
Smallest adversarial seed:
1. **Base category** — objects = cell-states, morphisms = turns; `id`, `∘`.
2. **Conservation as a symmetric-monoidal / linear structure** — prove composition preserves the
   per-class sum (the claim all three spines asserted).
3. **Two authority models** (positional/caps-as-caps, epistemic/keys-as-caps) + a **lossy
   morphism** between them — *state precisely what's lost* (the seL4-reflection impedance
   mismatch, as a theorem not a hand-wave).
4. **The vat-boundary law** (the sharp target): a turn composing *purely within one trust-root*
   needs **no witness**; **crossing a vat-boundary is exactly where the witness side of
   `Predicate ⊣ Witness` becomes mandatory.** This is the claim the whole architecture rests on.

Lean buys coherence-checking of the skeleton and precision on the laws (and `Boundary.lean`
adds the third, independent **I-confluence** judgement — invariant-merge — orthogonal to both
conservation and ordering; see `dregg2.md §2.3`). It does **not**
establish *cryptographic* soundness (that the STARK attests the morphism) — a separate obligation
living in the circuit; conflating them would be its own mistake (note in the dir's README).

---

## 9. Decisions (resolved 2026-05-29)

1. **Path: Lean core first.** Build the small core semantics + laws *executably* in Lean4
   (`./metatheory`) before the Rust remold. Lean = semantic core + laws (+ later, the DSL via
   metaprogramming); **Rust stays the crypto/proving/transport/wasm engine** (do NOT reimplement
   the prover in Lean); **differential testing** bridges them (Lean = golden oracle, Rust checked
   against it — the `dregg-dsl-differential` pattern). Rationale: the peers' three complaints
   (hard-to-understand / huge-TCB / incoherent) are all about the *semantic layer*, not the
   crypto; Lean targets exactly that layer, and l4.verified is the existence-proof that
   machine-checking a cap system's integrity certifies something necessary (answers the
   "formalization sauce" risk).
2. **Regime coupling: 4-corners with diagonal default.** Authority-representation (caps/keys) and
   ordering (finality tier) are *independently* selectable per cell, but the coupled diagonal is
   the default. Off-diagonal corners are allowed (e.g. a proof-carrying cell that still wants
   single-writer ordering); the vat-boundary must handle all four corners.
3. **v1 Rust: freeze and rebuild later.** Freeze the current frontend/sdk/discord-bot/playground/
   wasm as a working v1 demo; do NOT actively maintain it. Rebuild the surface against the
   certified core later (the existing code is week-old and rebuildable; not precious).
4. **Interaction style: live-session-then-attest** (seL4 confines interactively to valid dregg
   actions; dregg attests quasi-batched / offline, under the hood) — the retroactive-from-log
   proof is the attest half.

---

## Appendix — input index (for re-grounding)

- Spine explorations: `docs/rebuild/01-spine-capability.md`, `02-spine-cell.md`, `03-spine-proof.md`.
- Continuation design: `docs/ZKPROMISE-ZKAWAIT-DESIGN.md`. Token design: `docs/TOKEN-CAPABILITY-UNIFICATION.md`.
- Key code coordinates: `turn/src/turn.rs:6-38` (receipt-chain-as-truth); `turn/src/action.rs:698`
  (LinearityClass), `:206` (Authorization), `:422` (Token); `turn/src/conditional.rs`,
  `turn/src/pending.rs` (await substrate); `cell/src/predicate.rs` (WitnessedPredicate + registry);
  `cell/src/capability.rs`, `facet.rs`; `blocklace/` + `paper/sections/06-fabric.typ` (fabric/τ);
  `intent/src/{solver,matcher,fulfillment,trustless}.rs`; `token/`, `macaroon/`, `discharge-gateway/`;
  `circuit/src/effect_vm/`, `stark_zk.rs`, `ivc.rs`; `~/dev/mina/src/lib/mina_base/`,
  `transaction_logic/`; `pdfs/{constitutional-consensus,grassroots-federation,blocklace,cordial-miners}.pdf`;
  `houyhnhnm.total.txt`; `~/src/spritely-whitepapers/`.
