# Research Library Index

136 papers, grouped by the axis of the dregg rebuild each one feeds. Each entry notes
the **gap it closes** — read against `docs/rebuild/00-synthesis.md` (the skeleton:
*turn = generator; cell/cap/proof = three projections; conservation + ordering = two
ambient laws*; the *two-inheritances* thesis; the *liquid→solid* trust-boundary model).

Filenames carry the source id where stable: `eprint.iacr.org/YYYY/NNN` → `…-YYYY-NNN`,
arXiv → `…-YYMM.NNNNN`. Conventions are descriptive otherwise.

---

## 1. Capability theory & object-capabilities (caps-as-caps)
*The membrane / vat-boundary law; the authority projection. The theory dregg's cap model rhymes with.*

- **robust-composition.pdf** — Miller, *Robust Composition* (2006 thesis). The ocap/E/CapTP bible: membrane, promise pipelining, when-blocks (the zkpromise/zkawait ancestor). NB: "membrane" is Miller's narrow term (a revocable forwarder) — see the vocab correction in the synthesis.
- **capability-myths-demolished.pdf** — Miller/Yee/Shapiro. The caps-as-caps vs ACL/keys distinctions, verbatim — underwrites the caps↔keys functor.
- **take-grant-protection-model.pdf** — Decidable safety of capability propagation; "the authority structure is analyzable."
- **hru-foundational-revisited.pdf** — Harrison-Ruzzo-Ullman access-matrix safety (un)decidability — the foundation take-grant escapes.
- **typed-access-matrix-model-sandhu.pdf** — TAM; the decidable-safety lineage mapped onto typed authority.

## 2. Capability OS, confinement & orthogonal persistence
*Trusted-island precedent; the seL4-reflection seam; "log is the inputs" persistence.*

- **eros-fast-capability-system.pdf** — Shapiro et al. Persistent capability OS = our "trusted island that persists and is portable," decades early.
- **keykos-nanokernel-architecture.pdf** — KeyKOS; persistent capability nanokernel + checkpoint persistence.
- **capdl-sel4.pdf** — seL4 capability distribution language; the concrete shape for the reflection seam (CNode/CSpace/CSlot).
- **verifying-eros-confinement.pdf** — The EROS confinement mechanism verified; the "confined interior" as a provable claim.
- **doerrie-mechanized-confinement-capability-systems.pdf** — *Mechanized* confinement proof (Coyotos lineage). Direct precedent for the Lean confinement work.
- **persistent-operating-system-dearle.pdf** — Orthogonal persistence / single-level store survey (houyhnhnm "keep the inputs").

## 3. Object-capability networking (CapTP / E / promises)
*The protocols dregg reflects; the live caps-as-caps interior.*

- **concurrency-among-strangers-e-promises.pdf** — Miller/Tribble/Shapiro. Promise pipelining in E = **the literal ancestor of zkpromise/zkawait**.
- **captp-capability-transport-protocol-spritely.pdf** — CapTP spec (Goblins). The caps↔keys conversion membrane (near = caps-as-caps, sturdy = keys-as-caps).
- **ocapn-interoperable-capabilities-network-spritely.pdf** — OCapN; the netlayer family the reflection seam degrades into.

## 4. Keys-as-caps & proof-carrying authorization
*The cryptographic-sea half; the auth-in-proof recovery (the Mina inheritance dregg dropped).*

- **proof-carrying-authentication-appel-felten.pdf** — Appel/Felten PCA. **The foundational ancestor of "authorization inside the proof."**
- **intro-to-proof-carrying-authorization-garg.pdf** — Accessible PCA intro.
- **proof-carrying-authorization-system-bauer.pdf** — A PCA system realization.
- **macaroons.pdf** — Birgisson et al. Bearer tokens with caveats = the `token/` system's theory.
- **rfc2693-spki-sdsi.pdf** — SPKI/SDSI certificate theory; keys-as-caps formal lineage.
- **ucan-spec.pdf** — UCAN delegation (DID-rooted late-bound cert chains).
- **governing-dynamic-capabilities-2603.14332.pdf** — Cryptographic binding of dynamic capabilities (2026, bleeding edge).
- **agent-identity-delegation-mcp-a2a-2603.24775.pdf** — Verifiable delegation across MCP/A2A (2026) — agents-as-caps, the zkRPC-toolcall product axis.

## 5. Information flow / noninterference / declassification
*What's lost at the boundary; selective disclosure (FieldVisibility) theory.*

- **sel4-information-flow-enforcement.pdf** — seL4's machine-checked info-flow proof; the integrity-theorem genre the membrane law mirrors.
- **noninterference-for-os-kernels-murray.pdf** — Noninterference for OS kernels (the seL4 confidentiality basis).
- **complexity-of-intransitive-noninterference.pdf** — Complexity of the boundary info-flow relation.
- **declassification-dimensions-and-principles.pdf** — Sabelfeld/Sands. **Declassification = "what crosses the membrane / what gets revealed"** — the selective-disclosure theory.

## 6. Continuations & algebraic effects (the await / intent / zkpromise family)
*Intent = inverse membrane = a suspended morphism awaiting a predicate-satisfying fill = a continuation.*

- **handlers-of-algebraic-effects-plotkin-power.pdf** — Plotkin/Power. The semantic basis for effects-as-suspended-computation.
- **handling-algebraic-effects-plotkin-pretnar-1312.1399.pdf** — Plotkin/Pretnar; effect handlers.
- **monadic-framework-delimited-continuations.pdf** — Dybvig/Peyton-Jones/Sabry; delimited continuations (shift/reset).
- **one-shot-continuations-dybvig.pdf** — One-shot = **linear** continuation = the conservation-respecting await.
- **expressive-power-one-shot-control-2509.11901.pdf** — One-shot control operators & coroutines (2025).
- **effective-concurrency-algebraic-effects.pdf** — Dolan et al.; effects→concurrency→promises (the multicore-OCaml basis).

## 7. Matching & unification (the intent-matching seam)
*Verify-a-fill is cheap & universal; find-a-fill is undecidable → a bounded pluggable solver.*

- **undecidability-higher-order-unification-coq.pdf** — Spies/Forster. **Machine-checked undecidability of HOU** — the literal precedent for "general intent matching is undecidable."
- **efficient-full-higher-order-unification.pdf** — The bounded, practical solver side.
- **winner-determination-combinatorial-auctions-sandholm.pdf** — Market-clearing / auction matching = the domain-specific matcher (order-books, swaps).

## 8. Linear logic & session types
*Conservation (Law 1) as linear/monoidal structure; ordering as session sequencing.*

- **girard-linear-logic-syntax-semantics.pdf** — Girard. The source.
- **sessions-as-propositions-1406.3479.pdf** — Propositions-as-sessions (Caires/Pfenning/Wadler line).
- **comparing-session-type-systems-linear-logic-2401.14763.pdf** — Comparison of the linear-logic-derived session systems.
- **dependent-session-types-verified-concurrency-2510.19129.pdf** — Dependent session types for verified concurrency (2025) — closest to the Lean target.

## 9. Category theory & resource theories
*The honest categorical reading; conservation as a symmetric-monoidal resource law.*

- **mathematical-theory-of-resources-1409.5531.pdf** — Coecke/Fritz/Spekkens. **Resource theory = conservation-as-monoidal**, exactly Law 1.
- **selinger-graphical-languages-monoidal-0908.3347.pdf** — String-diagram / monoidal-category reference.
- **string-diagrams-closed-symmetric-monoidal-csl2026.pdf** — String diagrams for closed SMCs (CSL 2026).

## 10. Formal verification: theorem provers & distributed-systems verification
*Lean for the core; the consensus-side analog to l4v (machine-checked distributed protocols).*

- **lean4-theorem-prover-and-language.pdf** — de Moura/Ullrich; Lean 4 system description.
- **lean4-comprehensive-survey-2501.18639.pdf** — Lean 4 architecture survey (2025).
- **iris-from-the-ground-up.pdf** — Iris higher-order concurrent separation logic (the verification substrate).
- **beginners-guide-iris-coq-separation-logic-2105.12077.pdf** — Accessible Iris/Coq/sep-logic entry.
- **concurrent-separation-logic-brookes-ohearn.pdf** — Brookes/O'Hearn; CSL foundations.
- **verdi-verified-distributed-pldi15.pdf** — Verified distributed systems in Coq.
- **disel-distributed-separation-logic.pdf** — Distributed separation logic (program-and-prove protocols).
- **velisarios-bft-coq.pdf** — **BFT/PBFT verified in Coq** — closest precedent for proving the finality tiers.
- **ironfleet-distributed-systems.pdf** — Proving practical distributed systems correct (safety+liveness).
- **igloo-refinement-separation-logic-oopsla20.pdf** — Soundly linking compositional refinement to separation logic.

## 11. Schema evolution / gradual typing (the frozen-AIR / Urbit-trap fix)
- **preserves-spec.pdf** — Garnock-Jones. Content-addressed data + schema; facet/AIR-by-content-hash substrate.
- **gradual-typing-as-if-types-mattered.pdf** — Gradual typing (typed old→new boundaries).
- **safe-on-the-fly-relational-schema-evolution.pdf** — Live schema migration = the typed-upgrade discipline.

## 12. Consensus, CRDTs, DAG-BFT, local-first
*Law 2 (ordering). The liquid substrate + the pluggable-finality menu. "Use, but not directly."*

**Grassroots / blocklace lineage (original library):**
- **blocklace.pdf** — The CRDT DAG substrate (per-creator chains, union-merge); the liquid default.
- **cordial-miners.pdf** — The τ ordering layer (waves/leaders) — finality tier 3.
- **constitutional-consensus.pdf** — Self-amending governance — tier-4 plugin (minus its 4 globalism seams).
- **grassroots-federation.pdf** — Organic federation-as-spectrum (n=1 grows; no genesis ceremony).
- **grassroots-flash.pdf** — Grassroots payment/flash construction.
- **cryptoconcurrency.pdf** — Tonkikh/Ponomarev; (almost) consensusless asset transfer — the conservation-without-total-order point.
- **dyno-dynamic-bft.pdf** — Duan/Zhang, *Foundations of Dynamic BFT* (changing membership).
- **adversary-majority.pdf** — *Consensus Under Adversary Majority Done Right.*
- **2304.14701.pdf** — Lewis-Pye & Roughgarden, *Permissionless Consensus* (the impossibility/landscape map).
- **dyna-hints.pdf** — *Dyna-hinTS: Silent Threshold Signatures for Dynamic Committees.*
- **ensue-whitepaper.pdf** — Ensue (project whitepaper).

**Modern DAG-BFT (cordial-miners successors):**
- **narwhal-and-tusk-dag-bft-2105.11827.pdf** — DAG mempool + BFT consensus separation.
- **bullshark-dag-bft-2201.05677.pdf** — Partially-synchronous DAG BFT.
- **mysticeti-uncertified-dags-2310.14821.pdf** — **Uncertified DAGs** ≈ the tier-1 causal-only default at low latency.
- **dag-rider-all-you-need-is-dag-2102.08325.pdf** — Asynchronous Byzantine atomic broadcast on a DAG.

**CRDT / local-first foundations:**
- **crdts-comprehensive-study-rr7506.pdf** — Shapiro et al. The canonical CRDT tech report.
- **crdts-shapiro-sss-2011.pdf** — The SSS 2011 short version.
- **byzantine-eventual-consistency-2012.00472.pdf** — **Limits of P2P / Byzantine causal consistency** — directly the grassroots/blocklace boundary.
- **merkle-crdts-merkle-dags-2004.00107.pdf** — Merkle-DAG + CRDT = the blocklace shape itself.
- **making-crdts-byzantine-fault-tolerant.pdf** — Kleppmann; BFT CRDTs.
- **local-first-software-kleppmann.pdf** — The local-first manifesto (the liquid-default philosophy).

## 13. ZK — folding & accumulation schemes
*Real recursion replaces classical PI-matching (proof-spine §2; IVC; aggregation).*

- **pcd-without-succinct-arguments-2020-1618.pdf** — PCD; the conceptual root.
- **nova-2021-370.pdf** — Nova, the folding origin.
- **protostar-2023-620.pdf** / **hypernova-2023-573.pdf** — generic accumulation / CCS folding.
- **protogalaxy-2023-1106.pdf** — multi-instance ProtoStar-style folding.
- **cyclefold-2023-1192.pdf** — folding over a curve cycle.
- **kilonova-2023-1579.pdf** — preprocessing folding SNARKs.
- **mova-2024-1220.pdf** — folding without committing to error terms.
- **neutronnova-2024-1606.pdf** — folding everything that reduces to zero-check.
- **mangrove-2024-416.pdf** — tree-based folding SNARKs.
- **hekaton-2024-1208.pdf** — horizontally-scalable folding/aggregation.
- **accumulation-without-homomorphism-2024-474.pdf** / **linear-time-accumulation-2025-753.pdf** — accumulation theory.
- **distributed-snark-via-folding-2025-1653.pdf** — distribution via folding.
- **latticefold-2024-257.pdf** / **latticefold-plus-2025-247.pdf** / **neo-lattice-folding-ccs-2025-294.pdf** / **neo-superneo-pq-folding-2026-242.pdf** — **post-quantum / lattice folding** (closes the PQ gap).
- **zk-pcd-from-accumulation-2026-289.pdf** — ZK proof-carrying data from accumulation (2026) — directly the proof-spine.

## 14. ZK — proximity testing, polynomial commitments & codes
*The soundness backbone under WHIR/STIR; the STARK/Binius PCS layer.*

- **deep-fri-2019-1903.12243.pdf** — the proximity-gap anchor.
- **proximity-gaps-reed-solomon-2025-2055.pdf** — modern RS proximity-gap restatement.
- **stir-2024-390.pdf** / **whir-2024-1586.pdf** — the modern FRI successors (fewer queries / super-fast verify).
- **basefold-2023-1705.pdf** / **deepfold-2024-1595.pdf** — field-agnostic / multilinear code-based PCS.
- **arc-reed-solomon-codes-2024-1731.pdf** — accumulation for RS codes (the folding↔proximity bridge).
- **blaze-interleaved-raa-codes-2024-1609.pdf** — fast SNARKs from RAA codes.
- **circle-starks-2024-278.pdf** — Mersenne-31 circle STARKs.
- **binius-towers-binary-fields-2023-1784.pdf** / **binius-multilinear-binary-towers-2024-504.pdf** — Binius (binary tower fields).
- **greyhound-lattice-pcs-2024-1293.pdf** / **hachi-lattice-multilinear-pcs-2026-156.pdf** — lattice PCS (2026).
- **frida-das-from-fri-2024-248.pdf** — data-availability sampling from FRI.
- **hyrax-doubly-efficient-2017-1132.pdf** / **gemini-elastic-snark-2022-420.pdf** — doubly-efficient / elastic SNARKs.
- **gemini-pcs-soundness-attack-2025-565.pdf** / **orion-soundness-restored-2024-1164.pdf** — **soundness attacks** (a real bug found+fixed in each).
- **brakedown-2021-1043.pdf** / **brakingbase-2024-1825.pdf** — linear-time field-agnostic codes.
- **samaritan-multilinear-snark-2025-419.pdf** / **lightning-field-agnostic-pcs-2026-258.pdf** — 2025/26 multilinear PCS.
- **pcs-evolution-shred-to-shine-2025-1354.pdf** — PCS evolution overview.
- **multivariate-pcs-survey-2306.11383.pdf** — multivariate PCS survey.
- **divide-and-conquer-sumcheck-2504.00693.pdf** — sumcheck (core to all the above).

## 15. ZK — IVC / recursion foundations, zkVM, lookups
- **valiant-incrementally-verifiable-computation.pdf** — Valiant; the original IVC.
- **valiant-conjecture-ivc-impossibility-2022-542.pdf** — **when IVC is impossible** (a boundary, not a recipe).
- **ivc-for-np-standard-assumptions-2025-1546.pdf** — IVC for NP from standard assumptions (2025).
- **ivc-arbitrary-depth-2025-1413.pdf** — when can we incrementally prove arbitrary depth (2025).
- **jolt-2023-1217.pdf** / **understanding-lasso-2025-1169.pdf** — zkVM via lookups (Jolt/Lasso).
- **segment-parallel-zkvm-2024-387.pdf** — non-uniform / segment / parallel zkVM = the continuation/segment angle.

## 16. ZK — STARK adjacency & private smart contracts
- **zk-for-starks-note-2024-1037.pdf** — adding zero-knowledge to STARKs (the ZK-gap).
- **pq-transparent-distributed-snark-2025-2327.pdf** — post-quantum + transparent distributed SNARK.
- **kachina-private-contracts-2020-543.pdf** — Kachina; **the Midnight foundation** for private smart contracts.
- **uc-zk-smart-contracts-2022-670.pdf** — practical UC-secure ZK smart contracts.

## 17. Anonymous credentials, identity & misc reference
- **anoncreds-from-ecdsa-2024-2010.pdf** — anonymous credentials from ECDSA.
- **did-vc-survey-2402.02455.pdf** — survey of DIDs & verifiable credentials.
- **revocable-proof-systems.pdf** — Christ/Bonneau, *Limits on revocable proof systems* (stateless-blockchain revocation bounds).
- **zk-frameworks-survey-2502.07063.pdf** — ZK proof-frameworks landscape survey (2025).
- **wasm-security-review-2407.12297.pdf** — WebAssembly security review (the studio wasm-runtime sandbox).

---

## Known gaps / not yet pulled
- **Robigalia** — no clean paper exists; it's a codebase (`~/dev/sel4`, `~/dev/l4v` locally).
- **Spartan / Lasso originals** — the zkVM lookup lineage is only partially here (Jolt + "Understanding Lasso").
- **Mina / Pickles** — read from `~/dev/mina` source directly.
- A non-arXiv classic occasionally needs a course-mirror fallback (HAL/lip6 serve landing pages); see git history of this dir for working URLs.

*Library expanded via the Kagi search API (`~/dev/allgame/.env: KAGI_API_KEY`); see the
`reference-kagi-paper-search` memory for the reusable query harness.*
