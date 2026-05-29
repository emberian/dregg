# DECISION — Folding-scheme variant landscape (conditional)

> **Scope.** *If* dregg adopts a folding/accumulation scheme as its recursion mechanism, which
> variant fits a **hash-based, FRI-committed, transparent, post-quantum-aiming, small-field
> (BabyBear, p = 2³¹ − 1) STARK**? This memo compares nine candidates and reaches a concrete
> recommendation. It is *conditional* on the sibling memo below.
>
> **Markers:** [C] = claim grounded in a read source (PDF or repo file:line). [A] = my
> analytic inference from those sources. [F] = forward design / engineering judgment.

---

## Dependency on DECISION-recursion-strategy (state it up front)

This memo is **subordinate** to `DECISION-recursion-strategy.md`, which decides whether folding
is even viable for a hash-based STARK *at all*. The dependency is hard, not soft:

- **The entire Nova lineage of folding schemes is built on additively-homomorphic vector/
  polynomial commitments.** This is not incidental — it is the *defining template*.
  Protogalaxy states it outright: *"All known folding schemes rely on additively homomorphic
  vector commitments… the verifier takes a random combination of the witness commitments"* [C,
  protogalaxy §1.2]. Mova: *"Nova requires using a homomorphic commitment scheme, which in
  practical scenarios is typically chosen to be an elliptic curve-based scheme such as Pedersen
  or KZG"* [C, mova §1]. The distributed-SNARK paper: *"the folding scheme requires linear
  combination of commitments"* and is *"compiled with SamaritanPCS, an additively homomorphic
  multilinear PCS"* [C, distributed-snark §1.1].
- **dregg's commitment scheme is hash-based (Poseidon2 / FRI). Hashes are NOT additively
  homomorphic** [C, repo: `circuit/src/poseidon_stark_verifier_circuit.rs`, FRI fold tests
  `circuit/tests/fri_fold_*.rs`; field `circuit/src/lib.rs:80` BabyBear p=2³¹−1]. There is no
  curve, no MSM, no `Com(a)+Com(b)=Com(a+b)` operation.

**Therefore the decision tree is:**

1. **If `recursion-strategy` chooses folding-over-an-additively-homomorphic-PCS** (i.e. dregg
   *bolts on* a curve-based or lattice/Samaritan-style homomorphic commitment beside its
   STARK) → **this memo is live; pick the recommended variant below.**
2. **If `recursion-strategy` keeps the commitment hash-only and wants accumulation anyway** →
   **only ONE scheme in this set qualifies: WARP** (linear-time-accumulation, hash-based, RO-
   secure, post-quantum, *no homomorphic commitment*) [C, linear-time-accumulation abstract].
   All eight Nova-lineage schemes are **MOOT**.
3. **If `recursion-strategy` rejects folding entirely** → route to STARK-native recursion
   (an in-circuit FRI/STARK verifier AIR — the path dregg's `plonky3_recursion.rs` and the
   `feature = "recursion"` Golden Vision already gesture at) [C, repo: `circuit/src/
   plonky3_recursion.rs:20-27` "NOT full in-circuit recursion… that requires implementing the
   Plonky3 verifier as an AIR"]. **This whole memo is then moot.**

dregg's *current* "composition" is neither folding nor real recursion: it is a Poseidon2
hash-chain over inner-proof public inputs plus classical PI-matching [C, repo:
`circuit/src/ivc.rs:30-38` "implemented as a HASH CHAIN with constraint checking",
`plonky3_recursion.rs` "proof aggregation via AIR… the verifier still needs access to the
inner proofs"]. That is an aggregation *binding*, not soundness-carrying accumulation.

---

## The variants (one para each)

**ProtoGalaxy** (2023/1106) [C]. ProtoStar-style *multi-instance* (k-fold) folding. Reduces
recursive-verifier marginal work to a logarithmic number of field ops + a constant number of
hashes; folding k instances at once makes per-instance verifier work *constant* (Lagrange-basis
trick avoids exponentially-growing degrees). Explicitly built on additively-homomorphic
commitments + in-circuit MSM. Best-in-class when you genuinely need to fold many instances per
step.

**CycleFold** (2023/1192) [C]. Not a folding scheme itself — an *engineering pattern* for the
curve-cycle problem. Observes that a folding verifier's only non-native work is a handful of
scalar muls (2 in Nova, 1 in HyperNova, 3 in ProtoStar), so it puts *only that one scalar mul*
on the second curve (~1k–1.5k gates vs Nova's ~10k on both curves). Presupposes curve-based
homomorphic commitments; entirely about minimizing the second-curve circuit. Irrelevant to a
field-only hash-STARK except as the thing you'd need *if* you went curve-based.

**KiloNova** (2023/1579) [C]. Preprocessing recursive SNARK for *non-uniform machine
execution* (zkVM). Introduces a "holographic folding scheme" that folds across multiple
high-degree CCS relations with *non-uniform indices* (the "index-folding problem"), giving a
multi-predicate PCD with a *constant* number of running instances (vs SuperNova's list of one-
per-circuit). Built on committed-CCS + sparse-polynomial commitments (homomorphic). The pick
if dregg's turns were heterogeneous opcodes needing per-step circuit selection.

**Mova** (2024/1220) [C]. Nova-derivative whose contribution is *dropping the commitment to
the error/cross terms* E and T — replacing them with MLE evaluations at a verifier-random
point (E is implicitly committed by the witness commitment). 5–10× faster prover than Nova,
no sumcheck, 3 rounds. **Still requires a homomorphic commitment to the witness Z** [C, mova
§1]. Lowers prover cost but does not remove the homomorphism dependency.

**NeutronNova** (2024/1606) [C]. Folds the *zero-check* relation (multivariate poly = 0 over
the hypercube) via a single round of sumcheck; generalizes by reduction-of-knowledge from any
relation reducible to zero-check (lookups, grand products, CCS ⊇ AIR/Plonkish/R1CS). Prover =
commit witness + one sumcheck round; if witness elements are *small*, only small elements are
committed. Folds multiple instances in log n rounds. Verifier = constant group scalar muls +
field ops + hashes — i.e. **still homomorphic-commitment-based** [C]. Strong fit *conceptually*
because dregg is AIR (CCS-expressible), but the commitment requirement is the blocker.

**Mangrove** (2024/416) [C]. A *framework* for folding-based SNARKs: a "uniformizing" compiler
turns any poly-time computation into identical simple steps (ideal for IVC), plus a commit-and-
fold strategy and a tree/PCD structure. Headline is *prover scalability*: constant-size
transparent CRS, low memory, two passes, highly parallel — 2 min for 2²⁴ gates, ~8 h for 2³²
on a laptop. Generic over the folding scheme but instantiated over homomorphic polynomial
relations. The pick for *streaming/low-memory single-machine* proving — orthogonal to the
homomorphism question (it inherits whatever the leaf folding scheme needs).

**Hekaton** (2024/1208) [C]. Not folding at all — *horizontal* "distribute-and-aggregate":
chunk a huge circuit, prove chunks in parallel across a cluster, aggregate via pairing-product
arguments over commit-carrying SNARKs (Mirage/Groth16-family). Strong horizontal scaling (2³⁵
gates < 1 h). Pairing-based ⇒ **not post-quantum, curve-based**. Relevant only as the
*aggregation/distribution architecture* dregg might emulate, not as a folding primitive.

**Distributed-SNARK-via-folding** (2025/1653) [C]. Distributed HyperPlonk prover: a
*distributed SumFold* folds many sumcheck instances (one per sub-circuit/node) into one, so a
*single* prover does the final PCS opening. Explicitly compiled with SamaritanPCS, an
**additively-homomorphic** multilinear PCS, "as the folding scheme requires linear combination
of commitments" [C]. 4.1–4.9× prover speedup over HyperPianist. Data-parallel circuits only.
Homomorphism is load-bearing.

**WARP / Linear-Time Accumulation** (2025/753) [C]. The outlier. *"The first accumulation
scheme with linear prover time and logarithmic verifier time… hash-based (secure in the
random oracle model), plausibly post-quantum secure, supports unbounded accumulation depth."*
Built from an *interactive oracle reduction of proximity that works with any linear code over a
sufficiently large field*, with a straightline extractor based on erasure correction [C,
abstract + §2.7, §10]. **This is the only scheme in the set that does not need an additively-
homomorphic commitment** — it accumulates *codeword/proximity* claims, exactly the kind FRI
already produces.

---

## Comparison table

Columns: **Homom?** = requires additively-homomorphic commitment (the gate for a hash-STARK).
**Prover** = dominant prover cost. **Error term** = how cross/error terms handled. **Multi-inst**
= native k-folding. **Scaling** = tree/distributed story. **Maturity**.

| Variant | **Homom-commit required?** | Prover cost | Error-term handling | Multi-instance | Scaling (tree/dist) | Maturity |
|---|---|---|---|---|---|---|
| **WARP** (2025/753) | **NO** [C] — any linear code, RO-only | **Linear** prover, log verifier [C] | N/A — proximity/codeword accumulation, no E/T commitment | Codeword batching w/ constraints [C] | Unbounded depth; PCD-native [C] | **Newest (2025), paper-only, no impl** [A] |
| ProtoGalaxy (2023/1106) | **YES** [C] | O(n) field+group; in-circuit k-MSM | Combines randomized sums; β-power Lagrange | **Best** — constant verifier work/inst [C] | sequential ∘ composition ∘ k-fold combos | Mature, multiple impls [A] |
| CycleFold (2023/1192) | **YES** (curve-cycle) [C] | Tiny 2nd-curve circuit (~1–1.5k gates) | Inherits base scheme | Inherits | Binary-tree IVC friendly [C] | Mature, in Nova ecosystems [A] |
| KiloNova (2023/1579) | **YES** [C] | Holographic fold of high-deg CCS | Cross-term mitigation in index-fold [C] | Multi-predicate, const running insts [C] | PCD, non-uniform/zkVM [C] | Research (2023) [A] |
| Mova (2024/1220) | **YES** [C] | **5–10× < Nova**; no sumcheck, 3 rounds | **Drops E/T commitment** → MLE evals [C] | Folds 2 accumulated insts (PCD) [C] | via PCD | Research + benchmarks [C] |
| NeutronNova (2024/1606) | **YES** [C] | commit + 1 sumcheck round; small-elt friendly | zero-check, no explicit error commit | log n rounds, multi-inst [C] | tree/PCD [C] | Research (2024) [A] |
| Mangrove (2024/416) | inherits leaf (homom in paper) [A] | **Low-mem, 2-pass, parallel**; 2³²→~8h laptop [C] | inherits leaf | leaf-dependent | **PCD tree, streaming** [C] | Research + microbench [C] |
| Hekaton (2024/1208) | **YES** (pairing) [C] | Distributed; 2³⁵ gates < 1h cluster [C] | N/A (aggregation, not folding) | aggregates heterogeneous proofs [C] | **Best horizontal/cluster** [C] | Impl + cluster eval [C] |
| Distributed-SNARK-fold (2025/1653) | **YES** (SamaritanPCS) [C] | 4.1–4.9× < HyperPianist, 8 machines [C] | sumcheck (SumFold), no error commit | distributed SumFold [C] | **Distributed, data-parallel** [C] | Impl + 8-machine eval [C] |

**The decisive column is the first one.** For a hash-only commitment, every "YES" row is moot
unless dregg adds a homomorphic PCS. Only **WARP** is a "NO."

---

## Recommendation (conditional)

**Primary recommendation — pick by branch of the recursion-strategy verdict:**

- **[F] If `recursion-strategy` keeps the commitment hash-based (the post-quantum-faithful
  branch) and still wants accumulation → WARP (linear-time-accumulation, 2025/753).** It is the
  *only* member of this landscape that is internally consistent with dregg's stack: hash-based,
  RO/post-quantum, transparent, no homomorphic commitment, linear prover, unbounded depth, and
  it accumulates exactly the *proximity-to-a-linear-code* claims that FRI already produces. No
  curve, no MSM, no second field, no cycle. This is the recommendation that preserves every
  property dregg's synthesis says it is aiming for [C, 00-synthesis §2.3 liquid→rigid
  "crystallizes a proof obligation"; post-quantum goal]. **Deciding factor: it is the only
  scheme that doesn't silently re-introduce the curve dependency the STARK was chosen to avoid.**

- **[F] If `recursion-strategy` decides a homomorphic PCS *is* acceptable** (dregg pairs the
  STARK with a Pedersen/KZG/Samaritan commitment for the accumulator only) → **NeutronNova
  (2024/1606)** is the best *core* fold: it folds the zero-check relation, and dregg's
  arithmetization is AIR ⊆ CCS, which NeutronNova folds natively; its prover only commits to
  *small* witness elements (a fit for BabyBear traces), and it does multi-instance folding in
  log n rounds. Wrap it in **Mangrove's** uniformizing compiler + streaming PCD tree for low-
  memory parallel proving, and adopt **CycleFold's** "only-one-scalar-mul-on-the-2nd-curve"
  pattern to keep the recursive circuit small. Use **Mova's** "no error-term commitment" trick
  if you stay R1CS-shaped rather than CCS. **Deciding factor: zero-check folding matches AIR
  with no relation translation; small-element commitments match the small field.**

- **[F] If the workload is genuinely non-uniform** (heterogeneous turn/opcode circuits per
  step) → **KiloNova** for its constant-size multi-predicate running instance; if the goal is
  raw *throughput across machines* rather than incremental depth → **Hekaton** (cluster
  aggregation) or **Distributed-SNARK-via-folding** (distributed SumFold). Both of the latter
  are curve/pairing-based and so, again, **moot on a pure hash-STARK.**

**Bottom line:** for dregg *as it actually is today*, the honest answer is **WARP if folding,
else STARK-native recursion.** The Nova lineage (Protogalaxy/CycleFold/KiloNova/Mova/
NeutronNova/Mangrove-leaf/Hekaton/Distributed-fold) is a rich menu **only after** dregg has
committed to carrying an additively-homomorphic commitment alongside its FRI — a decision that
belongs to `DECISION-recursion-strategy`, not here.

---

## What to build

[F] Assuming the **WARP branch** (the one consistent with dregg today):

1. **Confirm the codeword interface.** WARP accumulates proximity claims for *any linear code
   over a large field*. dregg's BabyBear (p=2³¹−1, ~31 bits) is likely *too small* for the
   soundness/extraction margin — WARP's abstract says "sufficiently large field" [C]. **Build
   step 0: decide the accumulation field** — almost certainly an *extension field* of BabyBear
   (degree-4/5, matching Plonky3's challenge field) or migrate the FRI to a Reed–Solomon code
   over that extension. This is the single biggest open dependency.
2. **Implement WARP's IOR-of-proximity + straightline (erasure-correction) extractor** as a
   reduction over dregg's existing FRI codewords, replacing the current `ivc.rs` Poseidon2
   hash-chain (which is a *binding*, not an accumulator) [C, repo `circuit/src/ivc.rs:30`].
3. **Replace `plonky3_recursion.rs` aggregation** (currently "verifier still needs the inner
   proofs" [C, `plonky3_recursion.rs:25`]) with a true accumulator whose decider runs once at
   the boundary — matching synthesis §2.4 "proof = the export format of the log, generated
   lazily, retroactively, at the crossing" [C, 00-synthesis §2.4].
4. **Wire the accumulator into the membrane/phase model** (§2.3): a cell stays liquid (log-only)
   until a boundary crystallizes; at that point fold the strand's per-turn proximity claims into
   one WARP accumulator and emit the single decider proof. Unbounded depth = unbounded strand
   length, which is exactly what a long-running cell needs [C, WARP abstract; 00-synthesis §2.3].

[F] If the **homomorphic-PCS branch** is chosen instead, build NeutronNova-over-AIR + a
CycleFold-style single-scalar-mul second circuit + Mangrove streaming, and accept the curve as
a *non-post-quantum island* (and flag the PQ regression to the recursion-strategy owner).

---

## Risks & open questions

- **[A] Field size is the gating risk for WARP.** "Sufficiently large field" likely rules out
  raw BabyBear; the whole recommendation hinges on accumulating over an extension field /
  large-field RS code. If that integration is infeasible, WARP collapses and the hash-STARK has
  *no* folding option → forced to STARK-native recursion. Resolve before committing.
- **[A] WARP maturity.** It is a May-2025 paper with (as of the abstract) no production
  implementation and a *novel* round-by-round-soundness + erasure-correction extraction
  technique. dregg would likely be an early implementor — schedule/audit risk vs the battle-
  tested Nova lineage.
- **[C/A] Every Nova-lineage scheme silently re-imports a curve.** Adopting any of
  Protogalaxy/CycleFold/KiloNova/Mova/NeutronNova/Distributed-fold/Hekaton means pairing a
  curve-based or pairing-based homomorphic commitment with the STARK — directly conceding the
  post-quantum goal *for the accumulator*, even if the leaf STARK stays PQ. This is a
  philosophy-level decision the synthesis's "post-quantum" framing should adjudicate.
- **[F] Is folding even the right shape for dregg's "turns"?** Folding/IVC shines for *long
  uniform sequential* computation (a cell's strand of turns is plausibly uniform). For
  *branch/merge* and *monoidal multi-cell* turns — which synthesis §1 says are "not free" and
  must be built [C, 00-synthesis §1] — a *PCD/tree* accumulator (WARP supports PCD; Mangrove/
  KiloNova are PCD) is needed, not linear IVC. Confirm the topology with the cell-spine before
  picking linear-vs-tree.
- **[A] Decider frequency.** Protogalaxy §1.1 warns that in a mutually-distrusting decentralized
  setting (which dregg's reference-group/federation model *is*), each party must run the decider
  before folding, so "moving work to the decider" stops being free [C, protogalaxy §1.1]. dregg's
  membrane crossings are exactly such trust boundaries — budget for frequent decider runs.
- **[F] No code exists for any of this.** `circuit/` has FRI-*fold* (low-degree-test internals)
  and a hash-chain "IVC," but **zero** folding-scheme accumulation [C, repo grep]. This is
  green-field regardless of variant.
