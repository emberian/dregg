# Research Library Index

**238 papers**, grouped by the dregg2 axis each one feeds. Read against `docs/rebuild/dregg2.md`
(canonical architecture) + `ROADMAP.md`. Filenames carry the source id where stable
(`…-YYYY-NNN` = IACR eprint, `…-YYMM.NNNNN` = arXiv).

**Synthesis & study docs in this dir** (not papers — our own analysis, pass-it-upward):
`discoveries.md` (conceptual mining + corrections to `00-synthesis`), `decisions.md` (ZK recursion/PCS
rollup), `discoveries-2.md` (5 design gaps + the 4-study rollup); the per-cluster `LEARNINGS-*.md`,
`DECISION-*.md` / `PATHB-*.md` (Path-B research), and `STUDY-*.md` (cyclic-GC, confluence-module,
lean4-coinduction, projection-split, the 5 ACM papers).

---

## 1. Capability theory & object-capabilities (caps-as-caps)
- **robust-composition** — Miller's thesis; the ocap/membrane/promise-pipelining bible.
- **capability-myths-demolished** — caps-as-caps vs ACL/keys (Properties A–G).
- **take-grant-protection-model** · **hru-foundational-revisited** · **typed-access-matrix-model-sandhu** — decidable-safety lineage.
- **the-need-for-capability-policies-drossopoulou** — rely/deny vocabulary (= the de-jure/de-facto badge split).

## 2. Robust safety & secure compilation (the Robigalia formal underpinning)
- **holistic-specifications-robust-programs-drossopoulou** · **swapsies-on-the-internet-capability-reasoning** — reasoning about ocap programs vs an adversarial environment.
- **robustly-safe-compilation-toplas21** · **secure-compilation-survey-patrignani** — "untrusted code, no hacks" as a *preserved property* (robust hyperproperty preservation).

## 3. Capability OS, confinement & orthogonal persistence
- **eros-fast-capability-system** · **keykos-nanokernel-architecture** — persistent capability OSes.
- **capdl-sel4** — seL4 capability-distribution language (the reflection seam).
- **verifying-eros-confinement** · **doerrie-mechanized-confinement-capability-systems** — *mechanized* confinement proofs.
- **persistent-operating-system-dearle** — orthogonal persistence.
- **empowering-wasm-thin-kernel-interfaces** — WASM confined by a thin (seL4-style) kernel = the Robigalia userspace seam.
- **wasm-security-review** — WASM sandbox security (the studio runtime).

## 4. Object-capability networking (CapTP / E / promises)
- **concurrency-among-strangers-e-promises** — Miller/Tribble; promise pipelining = the zkpromise ancestor.
- **captp-capability-transport-protocol-spritely** · **ocapn-interoperable-capabilities-network-spritely** — the protocols dregg reflects (caps↔keys conversion membrane).

## 5. Keys-as-caps & proof-carrying authorization
- **proof-carrying-authentication-appel-felten** — authorization = a checkable proof (the auth-in-proof ancestor).
- **intro-to-proof-carrying-authorization-garg** · **proof-carrying-authorization-system-bauer** — PCA intro + system.
- **macaroons** · **rfc2693-spki-sdsi** · **ucan-spec** — bearer-token / keys-as-caps lineage (third-party caveat = discharge).
- **governing-dynamic-capabilities** · **agent-identity-delegation-mcp-a2a** — 2026 crypto-bound dynamic caps + agent delegation across MCP/A2A.

## 6. Information flow, noninterference & DIFC distributed systems
- **sel4-information-flow-enforcement** · **noninterference-for-os-kernels-murray** · **complexity-of-intransitive-noninterference** — the integrity/info-flow theorem genre.
- **declassification-dimensions-and-principles** — "what crosses the membrane gets revealed" (selective-disclosure theory).
- **fabric-secure-distributed-computation-sosp09** · **sharing-mobile-code-securely-ifc-oakland12** · **securing-distributed-systems-ifc-zeldovich-nsdi08** — the closest full-system precedent: distributed + persistent + secure-cross-trust-domain.

## 7. Continuations & algebraic effects (the await / intent / zkpromise family)
- **handlers-of-algebraic-effects-plotkin-power** · **handling-algebraic-effects-plotkin-pretnar** — effects-as-suspended-computation.
- **monadic-framework-delimited-continuations** · **one-shot-continuations-dybvig** (linear = conservation-respecting await) · **expressive-power-one-shot-control**.
- **effective-concurrency-algebraic-effects** — effects→concurrency→promises.

## 8. Matching & unification (the intent-matching decidability seam)
- **undecidability-higher-order-unification-coq** — machine-checked; matching undecidable at the flex-head.
- **efficient-full-higher-order-unification** — the bounded practical solver.
- **winner-determination-combinatorial-auctions-sandholm** — market-clearing complexity.

## 9. Linear logic & (binary) session types
- **girard-linear-logic-syntax-semantics** — the source.
- **sessions-as-propositions** · **comparing-session-type-systems-linear-logic** · **dependent-session-types-verified-concurrency**.
- **coherence-generalises-duality-mpst** · **logical-interpretation-async-mpst** — MPST *from* linear logic (the conservation⊗ordering coupling).

## 10. Multiparty session types & choreographies (the coordination axis)
- **mpst-honda-yoshida-carbone-jacm** — the MPST foundation.
- **less-is-more-mpst-revisited** · **less-is-more-revisited** — the modern (bottom-up) MPST theory.
- **mpst-generalising-projection** · **mpst-semantic-global-type-wellformedness** — endpoint projection / well-formedness (the projection-split core).
- **mpst-crash-stop-async** · **mpst-crash-failure-typing-viering** · **omission-failures-choreographic** — failure-aware projection.
- **affine-rust-mpst** — affine (drop/cancel) MPST in Rust.
- **montesi-choreographic-programming-book** · **choral-choreographic-oop** · **functional-choreographic-programming** · **haschor-functional-choreographies-icfp23** — choreographic programming languages.
- **deadlock-freedom-by-design-choreography-cm13** — projection-preserves-a-property (the template the projection-split extends).
- **formulas-as-processes-deadlock-freedom-choreographies** — LL + choreographies + deadlock-freedom.
- **cryptographic-choreographies** · **security-protocols-as-choreographies** · **bft-web-services-session-types** — Byzantine/crypto choreographies (the over-Byzantine half).

## 11. Category theory, coalgebra & coinduction (the metatheory core)
- **mathematical-theory-of-resources** — resource theory = conservation-as-symmetric-monoidal (Law 1).
- **selinger-graphical-languages-monoidal** · **string-diagrams-closed-symmetric-monoidal-csl2026** — string diagrams / SMC.
- **open-petri-nets-baez** — open Petri nets as SMCs (compositional concurrency).
- **coalgebraic-semantics-silva** — coalgebra/bisimulation basics (the cell = final coalgebra).
- **mixing-induction-coinduction** — the `νC.µI` nesting (bounded proof inside unbounded life).
- **guarded-recursion-coinductive** · **guarded-dependent-type-theory-coinductive** · **generalized-modality-for-recursion-later** — the `▶` guard (= `previous_receipt_hash`).
- **coinductive-proofs-regex-zk** — coinduction *inside* a ZK proof.
- **lean4-codatatype-package-qpf-keizer** — how to build codatatypes in Lean4 (QPF) — the `Boundary.lean` tooling.

## 12. Formal verification: provers & distributed-systems verification
- **lean4-theorem-prover-and-language** · **lean4-comprehensive-survey** — the metatheory's tool.
- **iris-from-the-ground-up** · **beginners-guide-iris-coq-separation-logic** · **concurrent-separation-logic-brookes-ohearn** — concurrent separation logic.
- **actris2-session-types-separation-logic** — verified MPST *in* Iris.
- **verdi-verified-distributed-pldi15** · **disel-distributed-separation-logic** · **velisarios-bft-coq** (BFT in Coq) · **ironfleet-distributed-systems** · **igloo-refinement-separation-logic-oopsla20** — the consensus-side l4v analogs (the finality-tier proof templates).

## 13. CRDTs, invariant-confluence, local-first & CALM (Law 2 / the I-confluence judgement)
- **crdts-comprehensive-study-rr7506** · **crdts-shapiro-sss-2011** — the CRDT design space.
- **replicated-data-types-spec-verification-optimality-popl14** — Burckhardt's spec/verification framework.
- **verifying-strong-eventual-consistency-crdt-isabelle** — Gomes–Kleppmann (the `Confluence.lean` template).
- **certified-mergeable-replicated-data-types-pldi22** · **katara-synthesizing-crdts-verified-lifting** · **opsets-sequential-specifications-replicated** — certified/synthesized merges.
- **merkle-crdts-merkle-dags** — Merkle-DAG + CRDT = the blocklace shape.
- **local-first-software-kleppmann** — the liquid-default philosophy.
- **byzantine-eventual-consistency** — the I-confluence iff-theorem (tier-1 limit).
- **making-crdts-byzantine-fault-tolerant**.
- **keeping-calm-distributed-consistency** — CALM (monotonicity ⟺ coordination-free).
- **coordination-avoidance-bailis-vldb** · **interactive-checks-coordination-avoidance-vldb19** (the I-confluence *checker* = the projection-split tooling) · **coordination-criterion** (2026).
- **dedalus-datalog-in-time-and-space** · **hydro-compiler-for-distributed-programs** — CALM-based languages (compiling the I-confluent fragment).

## 14. Byzantine CRDTs & proof-carrying / authenticated replication (fellow travelers)
- **proof-carrying-crdts-byzantine-update-papoc25** — the on-the-nose convergent paper (CONFIRMED, not scooped — see `STUDY-acm-papers.md`).
- **extend-only-directed-posets-byzantine-crdts** — semilattice underpinning for CDT ≡ blocklace.
- **bounding-byzantine-impact-open-crdt-systems** — the open-deployment spam side-condition.
- **authenticated-conflict-free-replicated-data-types** · **byzantine-ft-crdts-from-cryptocurrencies**.

## 15. Consensus, DAG-BFT, order-fairness & accountability (Law 2 finality tiers)
**Grassroots / blocklace lineage (original library):**
- **blocklace** · **blocklace-byzantine-repelling-universal** — the CRDT-DAG substrate.
- **cordial-miners** (the τ ordering) · **constitutional-consensus** (tier-4 governance) · **grassroots-federation** · **grassroots-flash**.
- **cryptoconcurrency** — (almost) consensusless asset transfer (when consensus is avoidable).
- **dyno-dynamic-bft** · **adversary-majority** · **2304.14701** (Permissionless Consensus, Lewis-Pye/Roughgarden) · **dyna-hints** (silent threshold sigs, dynamic committees) · **ensue-whitepaper**.

**Modern DAG-BFT:**
- **narwhal-and-tusk-dag-bft** · **bullshark-dag-bft** · **mysticeti-uncertified-dags** (validates tier-1 causal-only) · **dag-rider-all-you-need-is-dag**.
- **sui-lutris-broadcast-and-consensus** — broadcast-for-owned + consensus-for-shared = a *shipped* per-cell-finality system.
- **sui-shared-objects-owned-vs-shared** — the owned-object (no consensus) vs shared-object (consensus) split = dregg's tier-1-vs-tier-3 per-cell finality, in a deployed system.

**Order-fairness & accountability:**
- **themis-order-fairness-byzantine-consensus** · **sok-consensus-fair-message-ordering** — anti-MEV order-fairness.
- **cft-forensics-byzantine-accountability** — accountability/forensics (the slashable-attestation basis).

## 16. Schema evolution, lenses & data substrate
- **preserves-spec** — content-addressed data + schema (cell-state/facet/AIR-id).
- **gradual-typing-as-if-types-mattered** — typed old→new boundaries.
- **safe-on-the-fly-relational-schema-evolution** — live migration.
- **edit-lenses-hofmann-pierce-wagner** — the bidirectional mechanism behind Cambria.
- **cambria-schema-evolution-edit-lenses-papoc21** — lens-graph = the schema-DAG (mechanism, not the theorem; the DAG-merge case stays open).

## 17. Distributed garbage collection (cell-liveness)
- **orca-actor-gc-type-codesign-oopsla17** · **orca-soundness-concurrent-actor-gc-esop18** — Pony ORCA (verified concurrent actor GC); the trust-scoped-hybrid basis (see `STUDY-cyclic-gc.md`).

## 18. ZK — folding & accumulation schemes
- **pcd-without-succinct-arguments** · **pcd-from-accumulation-schemes** — PCD/IVC-from-accumulation (the BCMS20 interface).
- **nova** · **protostar** · **hypernova** · **protogalaxy** · **cyclefold** · **kilonova** — the curve-cycle folding line.
- **mova** (no error-term commits) · **neutronnova** (zero-check) · **mangrove** (tree) · **hekaton** (horizontal) · **accumulation-without-homomorphism** · **linear-time-accumulation** · **distributed-snark-via-folding**.
- **latticefold** · **latticefold-plus** · **neo-lattice-folding-ccs** · **neo-superneo-pq-folding** · **lova-lattice-folding-unstructured** — the post-quantum / lattice folding track.
- **halo-recursive-no-trusted-setup** · **halo-infinite-accumulation** — accumulation from any additive PC (the swappable-backend theory).
- **zk-pcd-from-accumulation** — ZK proof-carrying data from accumulation (2026).

## 19. ZK — recursion / IVC foundations
- **valiant-incrementally-verifiable-computation** (the original) · **valiant-conjecture-ivc-impossibility** (when IVC is impossible) · **ivc-for-np-standard-assumptions** · **ivc-arbitrary-depth**.
- **fractal-pq-transparent-recursive** — PQ + transparent recursion from holography.
- **plonky2-recursive-fri-plonk** — practical hash-native recursive STARK.

## 20. ZK — proximity testing, polynomial commitments & codes
- **deep-fri** · **proximity-gaps-reed-solomon** — the soundness backbone.
- **stir** · **whir** — modern FRI successors (the recursion-verifier cheapener).
- **basefold** · **deepfold** · **arc-reed-solomon-codes** · **blaze-interleaved-raa-codes** — code-based PCS.
- **circle-starks** (Mersenne-31) · **binius-towers-binary-fields** · **binius-multilinear-binary-towers** — small/binary fields.
- **greyhound-lattice-pcs** · **hachi-lattice-multilinear-pcs** — lattice PCS (PQ).
- **frida-das-from-fri** · **hyrax-doubly-efficient** · **gemini-elastic-snark** · **brakedown** · **brakingbase** · **samaritan-multilinear-snark** · **lightning-field-agnostic-pcs**.
- **multivariate-pcs-survey** · **divide-and-conquer-sumcheck** · **pcs-evolution-shred-to-shine** — surveys/sumcheck.

## 21. ZK — zkVM, lookups, STARK adjacency & private contracts
- **jolt** · **understanding-lasso** · **segment-parallel-zkvm** · **verifying-jolt-zkvm-lookup-semantics** — zkVM + lookups (the LogUp decision).
- **zk-for-starks-note** (adding ZK to STARKs) · **pq-transparent-distributed-snark**.
- **kachina-private-contracts** (the Midnight foundation) · **uc-zk-smart-contracts**.

## 22. ZK — soundness, malleability, streaming & surveys
- **gemini-pcs-soundness-attack** · **orion-soundness-restored** — real soundness bugs (the adversarial-test basis).
- **sok-snark-vulnerabilities** · **zk-frameworks-survey** — the landscape + the unaudited-stack risk.
- **malleable-snarks** (controlled malleability = rejuvenation) · **sumcheck-zksnarks-non-malleable** (the soundness counterpart).
- **verifiable-streaming-computation** · **streaming-zero-knowledge-proofs** — incremental proofs over unbounded streams (succinct-unbounded-history).

## 23. Verifiable ML & federated learning (the agent/zkRPC product surface)
- **zkml-verifiable-machine-learning-survey** · **zk-proofs-of-training-deep-neural-networks** (verifiable *training*) · **safetynets-verifiable-dnn-execution** (verifiable inference).
- **practical-secure-aggregation-federated-learning-bonawitz** · **byzantine-robust-federated-learning-learnable-aggregation**.

## 24. Anonymous credentials, accountable anonymity & revocation
- **anoncreds-from-ecdsa** · **did-vc-survey** · **coconut-threshold-selective-disclosure-credentials** (distributed credential authority).
- **revocable-proof-systems** — limits on revocable proof systems (stateless-chain bounds).
- **privacy-by-design-self-sovereign-identity** — SSI privacy reference.
- **towards-accountability-for-anonymous-credentials** · **publicly-auditable-privacy-revocation-anoncreds** — accountable anonymity (the de-jure/de-facto + auditable revocation).
- **lattice-accumulator-anonymous-credential** (PQ accumulator) · **private-delegation-nonmembership-proof-updates-accumulators** — the revocation non-membership seam (§3) + private update delegation.

## 25. Privacy: mixnets, unlinkability, PIR/ORAM, metadata-private messaging
*(The network/storage-layer privacy tier — complements dregg's data-layer privacy stack.)*
- **sphinx-compact-provably-secure-mix-format** — the canonical mix packet format.
- **loopix-anonymity-system** — modern low-latency mixnet.
- **anonymity-trilemma** — the strong-anon ⊥ latency ⊥ bandwidth tradeoff.
- **on-privacy-notions-anonymous-communication** · **anonymity-unlinkability-pseudonymity-terminology-pfitzmann-hansen** — the rigorous sender/receiver-unlinkability definitions.
- **vuvuzela-private-messaging-traffic-analysis** (mixnet-noise) · **riposte-anonymous-messaging-millions** (DC-net/PIR-write) · **talek-private-group-messaging-hidden-access** (PIR-log, hidden access patterns).
- **simplepir-single-server-pir** · **path-oram-oblivious-ram** · **oblivious-data-structures** — private reads / oblivious structures (the blinded-queue complement).
- **quasar-multicast-commitment-mixing-recursive-accumulation** — commitment mixing ⊗ recursive accumulation.

## 26. Mechanism design & resource-safe contract languages
- **credible-optimal-auctions-via-blockchains** — credible auctions (the intent-matcher incentive layer).
- **move-resources-safe-abstraction-money** — linear resource types (conservation in a real language).
- **movescanner-move-smart-contract-security** — Move resource-safety failure modes.

---

## Known gaps / not yet pulled
- **Privacy-pools / compliant-anonymity proper** (Buterin et al. "association sets") — only an attack-on-Tornado surfaced; the real paper didn't.
- **Plainfossé distributed-GC survey** — free but HAL served HTML; ORCA covers the substance.
- **Robigalia / Pickles internals** — read from `~/dev/sel4`, `~/dev/l4v`, `~/dev/proof-systems` directly.
- **DC-nets / Dining-Cryptographers foundations**, **traffic-analysis defenses** — adjacent to §25, not yet pulled.

*Library expanded via the Kagi search API (`~/dev/allgame/.env`); see the
`reference-kagi-paper-search` memory for the harness.*
