# READING-LIST — the bangers

> Opinionated, ranked subset of the 249-paper library for whoever is building dregg2.
> `INDEX.md` is the complete map; **this is "if you read 50, read these, and here's what
> each one buys."** Markers: **◎** = read no matter what you're working on · **●** =
> read for that axis · **○** = strong, second pass. Tags: foundational-canon vs
> *decision-changing/novel-convergent* noted inline. Pairs with the four candidate docs
> (`docs/rebuild/cand-A/B/C/D`) and the synthesis set (`discoveries.md`, `decisions.md`,
> `discoveries-2.md`, `STUDY-*.md`).

---

## The Critical Seven (read first — they change the calculus)

1. **◎ `proof-carrying-crdts-byzantine-update-papoc25`** — *decision-changing.* The fellow-traveler that **confirmed, didn't scoop** dregg2. Re-anchor the novelty claim on it, and **steal its fixed-circuit-over-variable-predecessors Merkle–Damgård trick** — it closes the `ChainLink`/graph-folding-flat gap *and* the in-AIR-Merkle M2 gap. Highest practical leverage in the library.
2. **◎ `byzantine-eventual-consistency`** — the I-confluence **iff**-theorem. The hard limit on tier-1, the 4-corners well-formedness side-condition, and what cand-D's equivocation gap bottoms out on. Law 2 rests here.
3. **◎ `proof-carrying-authentication-appel-felten`** — "authorization *is* a checkable proof." The ancestor of the auth-in-proof critical path (ROADMAP Phase 2); the model for a decidable in-circuit policy check with search pushed out.
4. **◎ `verifying-strong-eventual-consistency-crdt-isabelle`** (Gomes–Kleppmann) — the machine-checked "prove-SEC-once, instantiate-per-type" template `Metatheory/Confluence.lean` should copy.
5. **◎ `robust-composition`** (Miller) — the ocap/membrane/promise bible; its "concurrency among strangers" is the exact constraint cand-D's open-world law must honor.
6. **◎ `valiant-conjecture-ivc-impossibility`** — *decision-changing.* Why recursion is **deferrable, not soundness-critical** (no unbounded ZK-IVC in ROM). The citation behind `decisions §0.2` and the whole "soundness ≠ recursion" reframe.
7. **◎ `capability-myths-demolished`** — caps-as-caps vs ACL/keys, the distinctions the caps↔keys lossy functor is built on.

---

## Path A — the soundness-critical spine (ROADMAP Phase 0–2)
*Make the per-turn proof step-complete; this is the only soundness-critical work.*
- **● `proof-carrying-authentication-appel-felten`** (above) — auth-in-proof.
- **● `move-resources-safe-abstraction-money`** — linear resource types in a real language (the conservation rib, Law 1, made concrete).
- **● `coherence-generalises-duality-mpst`** — conservation living *in* the types (linear-logic session types).
- **● `jolt`** + **○ `segment-parallel-zkvm`** — zkVM via lookups (the LogUp decision) + the segment/continuation model for per-action proofs.
- **● `orion-soundness-restored`** + **● `gemini-pcs-soundness-attack`** — *real soundness bugs found+fixed*; the basis for the 11-item adversarial test checklist (the unaudited PCS layer is the live risk). **○ `sok-snark-vulnerabilities`** for the landscape.
- **○ `verifiable-streaming-computation`** — IVsC / succinct-unbounded-history from *falsifiable* assumptions (the teleport/late-join axis, kept off the soundness law).

## Path D — the coordination front-end (read with `cand-D`)
*Choreography-first as the syntactic spine; the open-world resolution.*
- **● `deadlock-freedom-by-design-choreography-cm13`** — projection-preserves-a-property (the template the projection-split extends).
- **● `mpst-meet-communicating-automata`** — bottom-up **compatibility** without a pre-agreed global type (the "strangers share no script" mechanism).
- **● `gradual-session-types`** — typed-overlay-over-untyped with **blame** = cand-D's resolution, formalized. **○ `hybrid-multiparty-session-types`** extends it.
- **● `compositional-choreographies`** — protocols compose at typed interfaces (no single cathedral `G`).
- **● `monitorability-of-session-types`** — the keystone convergence: **monitor = membrane = verifier**, blame = de-jure/de-facto.
- **● `explicit-connection-actions-mpst`** — dynamic join/leave/optional participants. **○ `dynamic-multirole-session-types`**, **○ `parameterised-multiparty-session-types`**, **○ `precise-subtyping-async-multiparty-sessions`** for the rest of the open-world toolkit.
- **● `mpst-honda-yoshida-carbone-jacm`** + **○ `less-is-more-mpst-revisited`** — the MPST foundation + the modern (bottom-up) theory. **○ `montesi-choreographic-programming-book`** — the canonical text.
- **○ `mpst-crash-stop-async`** — failure-aware projection.

## Path R — the recursion backend (Path B / `decisions.md`)
*Swappable accumulation; recursion is a deferred feature, not the soundness path.*
- **● `pcd-from-accumulation-schemes`** + **● `halo-infinite-accumulation`** — the BCMS20 accumulation interface = the `RecursionBackend` trait's theory (homomorphic↔PQ swap).
- **● `nova`** + **○ `protostar`** — the folding canon (origin + generic accumulation), for vocabulary (folding-on-FRI is out, but the abstraction matters).
- **● `whir`** + **○ `stir`** — FRI→WHIR cheapens the recursive verifier (the PCS decision). **○ `basefold`**, **○ `binius-towers-binary-fields`**, **○ `proximity-gaps-reed-solomon`** for the field/code/soundness backbone.
- **● `fractal-pq-transparent-recursive`** + **○ `plonky2-recursive-fri-plonk`** — the hash-native PQ recursion track (the "as PQ-now as possible" option).
- **○ `latticefold-plus`** / **○ `neo-superneo-pq-folding`** — the lattice (PQ-folding) migration target.
- **○ `kachina-private-contracts`** — the Midnight private-contract foundation. **○ `malleable-snarks`** + **○ `sumcheck-zksnarks-non-malleable`** — rejuvenation (controlled-malleability vs non-malleability).

## Path L2 — consensus, I-confluence & the finality tiers
- **● `blocklace`** + **○ `cordial-miners`** — the CRDT-DAG substrate + the τ ordering. **○ `extend-only-directed-posets-byzantine-crdts`** — the semilattice underpinning for CDT ≡ blocklace.
- **● `keeping-calm-distributed-consistency`** — CALM (monotonicity ⟺ coordination-free), the theorem behind tier selection.
- **● `coordination-avoidance-bailis-vldb`** + **● `interactive-checks-coordination-avoidance-vldb19`** — invariant-confluence + the *segmented* **checker** = the projection-split's front-end tooling.
- **● `cryptoconcurrency`** + **● `sui-lutris-broadcast-and-consensus`** — when consensus is avoidable (per-cell finality), in theory and as a *shipped* system. **○ `mysticeti-uncertified-dags`**, **○ `narwhal-and-tusk-dag-bft`** — the modern DAG-BFT tiers.
- **○ `themis-order-fairness-byzantine-consensus`** (anti-MEV ordering) + **○ `cft-forensics-byzantine-accountability`** (the slashable-attestation/accountability basis).
- **○ `local-first-software-kleppmann`** — the liquid-default philosophy.

## Path L1 — the Confluence module & certified replication
- **● `verifying-strong-eventual-consistency-crdt-isabelle`** (above) — the template.
- **● `replicated-data-types-spec-verification-optimality-popl14`** (Burckhardt) — the abstract-state/visibility spec model the judgement quantifies over.
- **○ `certified-mergeable-replicated-data-types-pldi22`** (reduce-to-sequential-spec) · **○ `merkle-crdts-merkle-dags`** (= the blocklace shape) · **○ `katara-synthesizing-crdts-verified-lifting`** (synthesize the merge).

## Path M — the metatheory (Lean4)
- **● `mathematical-theory-of-resources`** — conservation = symmetric-monoidal (Law 1, `Core.lean`).
- **● `mixing-induction-coinduction`** — the `νC.µI` nesting (bounded proof inside unbounded life).
- **● `lean4-codatatype-package-qpf-keizer`** — how to actually encode `νC.µI` + the relational gfp in Lean4 (resolves the `Boundary.lean` tooling worry). **○ `guarded-dependent-type-theory-coinductive`** — the `▶` guard.
- **● `velisarios-bft-coq`** — BFT verified in Coq = the finality-tier proof template. **○ `igloo-refinement-separation-logic`** — the spec↔impl bridge model (= the dregg-dsl-differential contract). **○ `ironfleet-distributed-systems`** — safety+liveness scope. **○ `iris-from-the-ground-up`** — only if the live-session interior ever needs concurrent separation logic.

## Path C — capability theory & the Robigalia vision
- **● `eros-fast-capability-system`** — the persistent capability OS precedent (trusted-island-that-persists). **○ `capdl-sel4`** — the reflection-seam shape. **○ `doerrie-mechanized-confinement-capability-systems`** — *mechanized* confinement = the Lean precedent.
- **● `fabric-secure-distributed-computation-sosp09`** — the closest *full-system* precedent (distributed + persistent + secure-cross-trust-domain). Read to see what it solved that dregg re-solves, and where proofs beat IFC labels.
- **● `holistic-specifications-robust-programs`** + **○ `robustly-safe-compilation-toplas21`** — robust safety = "untrusted code, no hacks" as a *preserved property* (the Robigalia vision, named formally).
- **● `concurrency-among-strangers-e-promises`** — the promise/await ancestor (zkpromise) + the "strangers" framing. **○ `take-grant-protection-model`** — decidable safety. **○ `the-need-for-capability-policies-drossopoulou`** — rely/deny = the de-jure/de-facto vocabulary.
- **○ `empowering-wasm-thin-kernel-interfaces`** — the WASM-confined-by-thin-kernel Robigalia userspace seam.

## Path W — continuations, effects & the await family
- **● `handlers-of-algebraic-effects-plotkin-power`** — the turn **is** the rollback handler; effects-held-until-commit.
- **● `undecidability-higher-order-unification-coq`** — the machine-checked **find-undecidable** proof (the verify/find seam; `no_general_matcher`).
- **○ `one-shot-continuations-dybvig`** (linear = conservation-respecting await) · **○ `monadic-framework-delimited-continuations`** (delimited continuations).

## Path P — privacy, accountability & metadata
*The network/storage-layer tier that complements dregg's data-layer privacy stack.*
- **● `towards-accountability-for-anonymous-credentials`** — the de-jure/de-facto badge split, made about credentials. **● `private-delegation-nonmembership-proof-updates-accumulators`** — directly the revocation non-membership seam + private update delegation.
- **● `coconut-threshold-selective-disclosure-credentials`** — distributed credential authority (the graph-privacy / anonymous-delegation tier).
- **● `sphinx-compact-provably-secure-mix-format`** + **● `anonymity-trilemma`** — the canonical mix format + the strong-anon⊥latency⊥bandwidth tradeoff ("how much unlinkability can a tier afford"). **○ `anonymity-unlinkability-pseudonymity-terminology-pfitzmann-hansen`** — the rigorous definitions.
- **○ `vuvuzela-private-messaging-traffic-analysis`** (metadata-private messaging) · **○ `simplepir-single-server-pir`** / **○ `path-oram-oblivious-ram`** (private reads / oblivious structures = the blinded-queue complement).

## Path X — schema, GC, mechanism design (axis-completing)
- **○ `preserves-spec`** — the content-addressed data substrate (cell-state/facet/AIR-id).
- **○ `edit-lenses-hofmann-pierce-wagner`** + **○ `cambria-schema-evolution-edit-lenses-papoc21`** — the schema-DAG migration mechanism (the theorem stays open).
- **○ `orca-soundness-concurrent-actor-gc-esop18`** — verified concurrent actor GC (the cyclic-GC trust-scoped-hybrid basis).
- **○ `credible-optimal-auctions-via-blockchains`** — the intent-matcher incentive layer.
- **○ `safetynets-verifiable-dnn-execution`** + **○ `practical-secure-aggregation-federated-learning-bonawitz`** — verifiable-inference + secure-aggregation, *if* the agent/zkRPC product proves over models.

---

## How to use this
- **Building the soundness spine right now?** Critical Seven + Path A.
- **Exploring cand-D / coordination?** Critical Seven (1,2,5) + Path D + Path L2's I-confluence checker.
- **The recursion/ZK backend?** Path R + `decisions.md`.
- **The Lean metatheory?** Path M + Path L1 + Critical #4/#6.
- **"How novel are we?"** Critical #1 (`proof-carrying-crdts`) + `STUDY-acm-papers.md`.

Everything not starred here is in `INDEX.md` — those are real references, just not the ones
that change a decision. ~70 papers carry stars; the other ~180 are the supporting cast.
