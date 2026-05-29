# DECISION — Recursion strategy

> **Verdict (one line):** dregg's recursion is **STARK-native recursive-verifier
> recursion**, not folding — because a hash-based FRI STARK has **no additively-homomorphic
> commitment**, and that single constraint kills the entire Nova/HyperNova/ProtoStar folding
> line outright. The code already started down exactly this road; the memo says *finish it*,
> and keep lattice folding (Neo/SuperNeo) on a watch-list as the only credible PQ folding
> fallback if recursion-circuit cost becomes the binding constraint.

Legend: **[C]** confirmed from code/docs · **[A]** assumed (stated where unconfirmable) · **[F]** forward-design / from-paper.

---

## dregg's constraints that drive this

1. **Field is BabyBear** — `p = 2^31 − 2^27 + 1 = 2013265921`, a 31-bit small field, with a
   degree-4 / degree-8 extension tower for soundness (`circuit/src/field.rs:1-12`,
   `babybear8.rs:1-30`). **[C]** This is a *small field*. (The Plonky3 recursion config uses
   `BinomialExtensionField<BabyBear,4>`, `plonky3_recursion_impl.rs:~95`.) **[C]**
2. **Commitment scheme is hash-based Merkle/FRI** — Poseidon2-over-Merkle MMCS + FRI PCS
   (`plonky3_recursion_impl.rs` `MerkleTreeMmcs`/`TwoAdicFriPcs`; ZK path `stark_zk.rs`
   `MerkleTreeHidingMmcs` + `HidingFriPcs`). **There is no additive homomorphism anywhere in
   the commitment layer.** **[C]** This is the deciding constraint.
3. **Transparent, no trusted setup; aiming post-quantum** — FRI + Poseidon2 are
   plausibly-PQ and setup-free. Any recursion strategy must preserve both. **[C]** (design
   intent throughout `stark_zk.rs` and synthesis §0.)
4. **A second proving path exists — Kimchi/Pickles (Pasta curves, IPA)** —
   `circuit/src/backends/{mina,kimchi_native}/` use `mina_curves::pasta::{Fp,Vesta}` and an
   IPA verifier (`mina/ipa_verifier.rs`). **[C]** This path *is* curve-cycle-based and *is*
   homomorphic-commitment recursion (Pickles). It is **not** PQ and **not** the BabyBear/FRI
   spine; treat it as a separate interop/Mina-compat backend, **not** the primary recursion
   substrate.
5. **The composition gap is real and named** — proof-spine §2: "Today composition is
   **classical PI-matching** … not *succinct in N*" (`03-spine-proof.md:185-188`). Concretely:
   - `ivc.rs` is an honest **hash-chain placeholder**, not folding: its own header says
     "Without the real recursion backend, the IVC is implemented as a HASH CHAIN … When real
     STARK recursion is available (Plonky3's recursive verifier), the accumulated_hash step
     becomes 'verify the previous proof' inside the circuit" (`ivc.rs:30-43`). **[C]**
   - `effect_vm/per_action.rs` stitches per-action proofs **by clear-text summary**, not a
     recursive STARK, and explicitly labels the recursive version "Golden-vision algebraic
     folding" (`per_action.rs:28-45`). **[C]**
6. **The recursive-verifier substrate already exists in-tree.** **[C]** This is the most
   important code fact, and it pre-decides the direction:
   - `p3-recursion`, `p3-circuit`, `p3-circuit-prover` are real workspace deps, **on by
     default** (`circuit/Cargo.toml:28-30,78,98-100`; `default = ["plonky3","recursion","mina"]`).
   - `plonky3_recursion_impl.rs` runs **real in-circuit STARK verification**: "Given an inner
     proof … we generate a proof-of-proof … enabling unbounded recursion," generic over any
     `Air` (`AggregationAir`, the Effect-VM AIR). **[C]**
   - `stark_zk.rs` ships **`RecursiveFriAir` + `FriVerifierGadget`** (W3-A): an *outer AIR
     whose constraints algebraically enforce the FRI folding relation `folded = even + beta*odd`*
     re-executed over the inner proof's FRI layers (`stark_zk.rs:30-46,193-234`). **[C]** This
     is the hand-rolled twin of the p3-recursion path — recursion teeth for the *custom* STARK.
   - `plonky3_verifier_air.rs` is the convenience surface with a `RecursionMode { HashChain,
     Recursive }` switch — `Recursive` produces "a **real** recursive proof, not a placeholder"
     (`plonky3_verifier_air.rs:1-60`). **[C]**

   **So dregg has *already chosen* recursive-verifier recursion in code — the gap is wiring it
   into composition, not picking a strategy.** Folding was never started; `*fold*` files
   (`fold_air.rs`, `dsl/fold.rs`, `ivc.rs`) are *attenuation-set folding* (removing facts from a
   Merkle tree) and *hash-chain accumulation*, **not** Nova-style instance folding. **[C]**

---

## The options

- **(0) Curve-cycle folding — Nova / HyperNova / ProtoStar.** The mainstream IVC/PCD line.
  Nova (`2021/370`) introduced folding as "a weaker, simpler primitive than SNARKs"; HyperNova
  (`2023/573`) folds CCS (which *generalizes R1CS, Plonkish, and AIR*) with a single MSM and
  free ZK via blinding; ProtoStar (`2023/620`) accumulates any special-sound protocol with a
  tiny recursive circuit. **All three explicitly rely on an additively-homomorphic,
  discrete-log (Pedersen/MSM) commitment and a cycle of elliptic curves** (HyperNova's CycleFold;
  ProtoStar's "k+2 EC multiplications"). LatticeFold's own abstract states this disqualification
  plainly: "all of them rely on an additively homomorphic commitment scheme based on discrete
  log, and are therefore not post-quantum secure and require a large (256-bit) field." **[F]**
  → **Incompatible by construction with dregg's hash-FRI/BabyBear spine. Eliminated.**

- **(a) Lattice folding — LatticeFold / LatticeFold+ / Neo / SuperNeo.** Replaces the
  discrete-log commitment with a *different* homomorphic commitment — Ajtai / Module-SIS —
  that **is** PQ and **does** work over small fields. LatticeFold (`2024/257`) folds R1CS+CCS
  over a 64-bit field, "as performant as HyperNova," PQ-plausible, but needs cyclotomic-ring
  arithmetic + bit-decomposition range proofs and **is not compatible with Goldilocks**.
  LatticeFold+ (`2025/247`) makes the prover faster / verifier circuit simpler via algebraic
  range proofs + double commitments. Neo (`2025/294`) adapts HyperNova to lattices with
  *pay-per-bit* Ajtai commitments **over small prime fields incl. Goldilocks**, folding **CCS —
  which subsumes AIR**. SuperNeo (`2026/242`) is the current frontier: the *first* scheme to
  hit all six of {PQ · pay-per-bit · field-native · general (non-SIMD) constraints · small-field
  (Goldilocks) · low recursion overhead}. **[F]** → PQ ✔, small-field ✔, folds AIR ✔ — **but it
  is still a homomorphic (Ajtai) commitment**: adopting it means *replacing FRI/Merkle with
  Module-SIS lattice commitments* across the whole prover, not bolting onto dregg's existing
  hash-FRI STARK.

- **(b) Accumulation WITHOUT homomorphism (`2024/474`, Bünz–Mishra–Nguyen–Wang).** Directly
  answers our crux: yes, you *can* build an accumulation scheme from **non-homomorphic vector
  commitments realizable from symmetric-key assumptions alone (e.g. Merkle trees)**, by
  "performing spot-checks over error-correcting encodings of the committed vectors" instead of
  exploiting homomorphism. **The catch the abstract flags itself:** "our scheme only supports a
  **bounded** number of accumulation steps" — bounded-depth accumulation, which still suffices
  for (bounded-depth) PCD. **[F]** → The *only* accumulation/folding-family option that natively
  fits hash commitments, but **depth-bounded** — a hard ceiling on chain/turn depth.

- **(c) zk-PCD from accumulation (`2026/289`, Zheng–Gao–Liu).** Not a new commitment line — an
  *efficiency/ZK layer* over accumulation-based PCD: separates the compliance predicate from
  accumulation verification (drops the zk-NARK requirement) and adds a zk accumulation scheme
  with masking vectors + zk-sumcheck, achieving log proof size/verify for degree-d relations.
  **[F]** → Relevant *only if* dregg picks an accumulation path (a or b); it is the ZK-PCD
  recipe to layer on top, **not** itself a homomorphic-vs-not decision. Orthogonal.

- **(d) STARK-native recursive-verifier recursion (Plonky2/3-style).** Each step's circuit
  *re-executes the FRI/STIR/WHIR verifier of the inner proof* as an AIR; the outer proof
  attests "the inner proof verified." No homomorphic commitment, no curve cycle — **the only
  requirement is a hash and a FRI-verifier-as-circuit, both of which dregg has.** SuperNeo's
  abstract names exactly this family's tradeoff: "hash-based schemes (e.g., Arc) incur **large
  verifier circuits**" — i.e. correctness is free, *prover cost per recursion step is the price*.
  **[C, in-tree]** → This is `p3-recursion` (`plonky3_recursion_impl.rs`) and `RecursiveFriAir`
  (`stark_zk.rs`) — **already built, already default-on.**

---

## Comparison table

| Option | PQ? | Trusted setup? | Needs homomorphic commitment? | Fits hash-FRI STARK? | Small-field fit | Recursion verifier cost | Maturity |
|---|---|---|---|---|---|---|---|
| **(0) Nova/HyperNova/ProtoStar** (curve-cycle folding) | ✗ | ✗ (transparent) | **✗ requires it** (Pedersen/MSM + curve cycle) | **✗ no** | ✗ needs ~256-bit field | tiny (≈2–3 EC scalar muls) | high (deployed) |
| **(a) Lattice folding** (LatticeFold+/Neo/**SuperNeo**) | ✔ plausible | ✗ | **✗ requires it, but PQ** (Ajtai/Module-SIS) | **✗ replaces FRI/Merkle** | ✔ (Neo/SuperNeo: Goldilocks; LF: not Goldilocks) | low–moderate (single sumcheck; SuperNeo "low recursion overhead") | low / very new (SuperNeo 2026) |
| **(b) Accumulation w/o homomorphism** (`2024/474`) | ✔ (symmetric-key only) | ✗ | **✔ NO — Merkle/spot-check** | **✔ yes (Merkle-native)** | ✔ (commitment-agnostic) | moderate (encode + spot-check) | low (2024, no production impl in dregg) |
| **(c) zk-PCD from accumulation** (`2026/289`) | inherits (a)/(b) | ✗ | inherits | inherits | inherits | log (adds zk-sumcheck masking) | low (2026; a *layer*, not a base) |
| **(d) STARK-native recursive verifier** (Plonky3 `p3-recursion`, `RecursiveFriAir`) | ✔ | ✗ | **✔ NO — hash + FRI-verifier-circuit** | **✔ native — it IS the STARK** | ✔ (BabyBear today) | **high prover cost** ("large verifier circuits"); O(1) outer verify | **in-tree, default-on**; FRI-verifier recursion is the most battle-tested PQ recursion (Plonky2/3, RISC-Zero, SP1) |

---

## Recommendation

**Primary: (d) STARK-native recursive-verifier recursion.** Finish wiring the
`p3-recursion` in-circuit verifier + `RecursiveFriAir`/`FriVerifierGadget` into composition.
**Fallback / watch-list: (a) lattice folding — specifically Neo/SuperNeo** if, and only if,
per-step recursion prover cost (the "large verifier circuit" tax) becomes the binding
constraint on deep cap-chains / many-cell aggregation.

**The deciding constraint:** *a hash-based FRI STARK has no additively-homomorphic
commitment.* That one fact:
- **eliminates (0) outright** — Nova/HyperNova/ProtoStar are structurally inseparable from
  Pedersen/MSM + curve cycles, are non-PQ, and want a 256-bit field; nothing about them
  survives transplant onto BabyBear/FRI;
- **demotes (a)** from "primary" to "fallback": it *solves* the homomorphism problem the PQ way
  (Ajtai/Module-SIS) and fits small fields (Neo/SuperNeo even fold AIR over Goldilocks) — **but
  the homomorphic commitment it needs is a different commitment than the one dregg has.**
  Adopting it is a **commitment-layer transplant** (rip out FRI/Merkle, install Module-SIS),
  not an add-on, on a scheme (SuperNeo) that is months old with no audited implementation;
- **promotes (d)**: the *only* recursion families that need **no** homomorphic commitment are
  (b) Merkle-spot-check accumulation and (d) FRI-verifier-in-circuit. Between them, (d) is
  **unbounded-depth**, **already in the tree, default-on**, and is the most battle-tested PQ
  recursion in the field (Plonky2/3, RISC-Zero, SP1 all do exactly this); (b) is
  **depth-bounded** and unbuilt. Depth-bounding is fatal for dregg's "indefinite cap-chains /
  unbounded turn strands" model, so (b) is rejected as primary too.

**The downstream consequence (state this loudly):** This verdict makes dregg's recursion
**recursive-verifier-based, NOT folding-based.** Every place the design currently says "fold"
in the IVC/composition sense (`ivc.rs` hash-chain, `per_action.rs` clear-text summary stitch,
proof-spine §2.2 cross-cell aggregation, the `effects_hash_global ← Σ effects_local` merge)
becomes **"recursively verify the inner STARK in-circuit and bind its PI,"** *not* "fold two
instances into one." Concretely:
- composition succinctness comes from **recursive proof-of-proof**, so deep chains stay O(1) to
  *verify* (cost moves to the prover);
- there is **no folding accumulator instance type** to design — no relaxed-R1CS / committed
  CCS error term, no cross-field "non-native scalar mul in the recursion circuit" tax;
- ZK comes from `HidingFriPcs` (`stark_zk.rs`), **not** from a folding blinding trick;
- the Kimchi/Pickles path stays a **separate, non-PQ interop backend** (Mina compat) and is
  *not* unified into the primary recursion story.

This is the cheaper and more honest choice precisely because **dregg already built it** — the
gap is integration, not invention.

---

## What to build (concrete)

1. **Promote `RecursionMode::Recursive` from available-but-unwired to the composition default**
   (`plonky3_verifier_air.rs`). The `HashChain` mode in `ivc.rs` stays only as a fast,
   *unproven-liquid* path (matches synthesis §2.3 liquid-default); crossing a membrane flips it
   to `Recursive`.
2. **Replace `ivc.rs`'s accumulated-hash step with the in-circuit verify.** `ivc.rs:38-43`
   already promises "swapping to real recursion requires no changes to callers" — honor it:
   `AccumulatedProof.proof` becomes a `RecursionOutput<DreggRecursionConfig>` from
   `plonky3_recursion_impl::recursive::prove_recursive_layer_for_air`, not a `ConstraintProof`
   over a Poseidon2 chain.
3. **Cross-cell aggregation (proof-spine §2.2) = recursive verify, not Σ-fold.** Make the
   `effects_hash_global ← Σ effects_local` merge an **aggregation micro-AIR that recursively
   verifies the N per-cell proofs** (the doc already says this; wire it through `AggregationAir`
   + `prove_recursive_layer_for_air`, which is already generic over arbitrary `Air`).
4. **Custom-effect sub-proofs = the canonical recursion site.** A `Custom` effect's truth is its
   sub-proof's truth — verify it with `RecursiveFriAir`/`FriVerifierGadget` and bind the inner
   VK to the committed program VK (proof-spine §2 lines 232-237). This is where classical
   PI-matching *must* die.
5. **Upgrade `per_action.rs` composition incrementally.** Keep the clear-text summary stitch as
   the working baseline; replace the `compose_action_summaries` clear-text chain check with a
   recursive verify per action once (3) is proven out, so the `ActionForestAccumulator` root
   becomes a recursive-proof binding rather than a Poseidon2 hash binding.
6. **Make `effects_hash` an in-circuit rolling fold** (proof-spine §1.2 / §2.1): a Poseidon2
   absorb over the canonical-DFS effect stream *inside* the AIR, replacing the host commitment
   the AIR never re-derives. This is a *Poseidon2 fold* (a rolling hash), **not** an
   instance-folding accumulator — keep the terminology straight to avoid re-importing the Nova
   mental model.
7. **Auth-in-proof rides the same recursion** (synthesis §5.3): compose `schnorr_air` /
   `native_signature_air` + permission-lattice `spec_eval` + Effect-VM into one statement; the
   recursion glues sub-statements, the in-circuit `effects_hash` fold binds them.

---

## Risks & open questions to confirm in code

- **[A→confirm] Recursion-step prover cost on BabyBear with degree-7 AIRs.** SuperNeo's
  "hash-based ⇒ large verifier circuits" warning is the real risk. `plonky3_recursion_impl.rs`
  notes `log_blowup=3` is *forced* by the degree-7 `P3MerklePoseidon2Air`; measure end-to-end
  recursion-layer prove time for the Effect-VM AIR + an auth-AIR before committing deep chains.
  **If this tax is prohibitive, that is the trigger to revisit (a) Neo/SuperNeo** — they exist
  precisely to cut recursion overhead while staying PQ + small-field.
- **[C→exploit] Two recursion implementations coexist** — `p3-recursion`
  (`plonky3_recursion_impl.rs`, gated `feature="recursion"`, default-on) **and** the hand-rolled
  `RecursiveFriAir`/`FriVerifierGadget` (`stark_zk.rs`, for the *custom* `crate::stark` prover).
  Confirm which prover backs which composition site and **do not maintain two FRI-verifier
  gadgets** long-term; pick the `p3-recursion` path as canonical unless the custom STARK is
  load-bearing somewhere the audit missed.
- **[A→confirm] Does the recursion config field-match the ZK (`HidingFriPcs`) config?**
  `stark_zk.rs` uses `MerkleTreeHidingMmcs` + `HidingFriPcs`; `plonky3_recursion_impl.rs` uses
  non-hiding `MerkleTreeMmcs` + `TwoAdicFriPcs`. Recursively verifying a *hiding* inner proof may
  need a hiding-aware verifier gadget — confirm the recursion gadget can consume a salted-leaf /
  hiding-PCS inner proof, or that ZK is applied only at the outermost layer.
- **[F] Bounded vs unbounded depth is the (b)/(d) discriminator.** Confirmed (b) `2024/474` is
  depth-bounded; (d) is unbounded. If any product requirement *caps* turn/cap-chain depth, (b)
  becomes a legitimate lighter-weight alternative — but dregg's "indefinite strands" model
  argues against ever accepting a depth bound.
- **[C] Keep Kimchi/Pickles quarantined.** It is genuine homomorphic-commitment recursion (Pasta
  + IPA, `mina/ipa_verifier.rs`) and non-PQ; ensure no design doc accidentally treats it as part
  of the PQ recursion spine. It is the Mina-interop backend only.
- **[F] (c) `2026/289` is shelf-ready *if* the strategy ever flips to accumulation.** Park it as
  the zk-PCD recipe for an (a)/(b) world; it is irrelevant to the (d) primary path (where ZK is
  `HidingFriPcs`).
