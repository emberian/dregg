# PATH B — What dregg borrows from Mina Pickles/Kimchi

> **Decision context:** dregg chose **Path B** — adopt homomorphic, cycle-of-curves /
> accumulation-based recursion **now** for genuine succinct **unbounded IVC**, leaning on
> Mina's audited Pickles/Kimchi as the working reference, with a PQ migration path later that
> *preserves the accumulation abstraction*. This reverses the earlier `DECISION-recursion-strategy.md`
> verdict (which picked Path D = STARK-native FRI-verifier recursion and quarantined Kimchi/Pickles).
> The tension is real and named in the Risks section. This memo grounds Path B in the actual
> `~/dev/proof-systems` code + the Halo / PCD-accumulation papers, and tells dregg exactly what to borrow.

Legend: **[C]** grounded in code or paper (path/line cited) · **[F]** forward-design / recommendation.

---

## What's in ~/dev/proof-systems (crates, key files)

This is the **o1Labs Rust** repo. **Pickles itself is NOT here** — the Pickles step/wrap orchestration
lives in OCaml in the Mina monorepo (`~/dev/mina/src/lib/pickles/`, referenced by dregg's own code).
What the Rust repo gives you is **the substrate Pickles is built on, plus its full spec**: **[C]**

- **`kimchi/`** — the PLONK-ish prover/verifier (Plonkish arith, custom gates: Poseidon, CompleteAdd,
  EndoMul/`varbasemul`, range-check, foreign-field, lookups). The recursion hook is
  `proof::RecursionChallenge` (`kimchi/src/proof.rs:225-242`) and `ProverProof::create_recursive`
  (prover threads `prev_challenges`, `kimchi/src/prover.rs:178,263,1172-1188`; verifier absorbs +
  re-evaluates them, `kimchi/src/verifier.rs:166,289-323,810`). End-to-end recursion smoke test:
  `kimchi/src/tests/recursion.rs` (builds a `RecursionChallenge` from `b_poly_coefficients`, feeds
  `.recursion(vec![prev])`, proves+verifies). **[C]**
- **`poly-commitment/`** — the IPA / bulletproof-style Pedersen commitment that is the *homomorphic*
  heart. `ipa.rs` (`SRS::verify`, lines 268-460+: the batched deferred MSM), `commitment.rs:426`
  `b_poly`, `:464` `b_poly_coefficients`, `:622` `combined_inner_product`. `kzg.rs` is the pairing
  alternative (not used by Pickles). **[C]**
- **`book/docs/pickles/`** — the **authoritative spec** for the recursion mechanics:
  `overview.md` (step/wrap, accumulator = `sg`), `accumulation.md` (the 4-reduction cycle + the
  "Halo trick", ~930 lines), `deferred.md` (passthrough / cross-field "passing"), plus
  `specs/pickles.md`, `specs/pasta.md`, `pickles/diagrams.md`. **This is the highest-value artifact in
  the repo for dregg.** **[C]**
- **`curves/`, `poseidon/`, `groupmap/`, `signer/`, `hasher/`** — Pasta (Pallas/Vesta) field/curve
  defs, the Poseidon sponge (Fiat-Shamir oracle), hash-to-curve (`groupmap`, samples the `U`/`H`
  bases). **[C]**
- **`arrabbiata/`** — a *separate, newer, incomplete* **Nova/ProtoStar-style folding IVC** over Pasta
  + IPA. Rich design doc in `interpreter.rs` (accumulator columns, cross-terms, error terms,
  homogenization, message-passing `acc_(p,n)`/`r`/`t_(p,n,i)` — `interpreter.rs:200-510`), `mvpoly` for
  cross-term computation. **But its decider is a stub**: `decider/proof.rs` is `pub struct Proof {}`,
  `decider/prover.rs:25` is `unimplemented!()`, `decider/verifier.rs` is empty. So arrabbiata is the
  *folding* (Nova) flavor and is **not production**; the *accumulation* (Halo/IPA) flavor in
  kimchi+poly-commitment **is** what Mina ships. **[C]**
- **`o1vm/src/pickles/`** — confusingly named; it's a STARK-ish *prover flavor* for the zkVM, **not**
  the recursion layer. Ignore for Path B. **[C]**
- **`msm/`, `mvpoly/`, `srs/`** — supporting (multi-scalar-mul, multivariate polys, structured ref string). **[C]**

**dregg already has a ~21k-line Mina/Pickles backend** (`circuit/src/backends/mina/` +
`kimchi_native/`): `pickles.rs` (875 L, "OPERATIONAL" assisted recursion), `step_verifier.rs` (729 L),
`wrap_verifier.rs` (1151 L), `ipa_verifier.rs` (1144 L, in-circuit IPA gadget), `glv.rs` (643 L,
GLV/EndoMul), `standalone.rs` (1092 L, Mina-equivalent in-circuit path), `kimchi_native/ivc.rs`,
`kimchi_native/fold.rs`, and **`stark_in_pickles.rs`** (728 L — wraps a BabyBear STARK *inside* a
Pickles proof). These vendor `kimchi`, `poly_commitment`, `mina_curves::pasta`, and explicitly port
`~/dev/mina/src/lib/pickles/`. Stub-marker density is very low. **This is the single most important
fact for the decision: the borrow has largely already happened.** **[C]**

---

## Pickles recursion mechanics (step/wrap, accumulator, the Halo/IPA trick)

**Cycle of curves (Pasta).** Pallas/Vesta are a 2-cycle: `Fp = scalar(Vesta) = base(Pallas)`,
`Fq = scalar(Pallas) = base(Vesta)`. Each curve's *base* field is the other's *scalar* field, so EC
operations on one curve are native field arithmetic on the other. Two kimchi instances run "mirrored,"
one per curve (`overview.md:11-23`, `deferred.md:3-17`). **[C]**

**Step vs Wrap** (`overview.md:16-47`): **[C]**
- **Step** = the application circuit. It (1) runs app logic, (2) verifies the previous *Wrap* proof's
  *first-half* (the checks cheap on this curve), (3) verifies the previous *Step* proof's *second-half*
  (the checks that were deferred when that Step was wrapped), and (4) checks the accumulator was
  aggregated: `acc₂ = Aggregate(acc₁, π_step,2)`. Step may repeat (2)-(3) to ingest up to 2 wrap proofs
  → this n-to-1 ingest is what makes it **PCD**, not just linear IVC.
- **Wrap** = a pure verifier circuit, no app logic: it verifies the Step proof and re-exposes it on the
  other curve. Every Step output is immediately Wrapped.

**The accumulator IS the IPA `sg` commitment** (`overview.md:49-70`). A kimchi proof = (poly
commitments, evaluations, opening proof). The "accumulator" is the `sg` field of the opening proof —
semantically a Pedersen commitment `U = ⟨h, G⟩` to the *challenge polynomial*
`h(X) = ∏_{i=0}^{k-1} (1 + u_{k-i}·X^{2^i})` built from the IPA folding challenges `u_i`
(`commitment.rs:426` `b_poly`; spec `accumulation.md:583-655`). The struct that carries it across steps
is **`RecursionChallenge { chals: Vec<F>, comm: PolyComm<G> }`** (`proof.rs:225-242`) — `chals` = the
`u_i` (`prev_challenges`), `comm` = `U`/`sg`. **[C]**

**The Halo trick = defer the expensive MSM** (`accumulation.md:621-665`, this is *the* mechanism for
unbounded depth). IPA folding gives an `O(log ℓ)`-size proof but the verifier still needs `O(ℓ)` to
recompute the folded base `G^{(k)} = ⟨h, G⟩` (an `ℓ`-size MSM). The trick: **don't.** Observe `G^{(k)}`
is itself a *polynomial commitment to `h(X)`*. The fact `sg = ⟨h,G⟩` is **never proven in-circuit**;
instead the new proof just *absorbs* the previous `sg` and asserts the cheap part (`h(z)` evaluates in
`O(log ℓ)` via `b_poly`). The expensive `O(ℓ)` MSM check is **deferred to the final out-of-circuit
verifier** — exactly what `poly-commitment/src/ipa.rs SRS::verify` does, with the explicit comment:
*"IPA verification is deferred by storing accumulators (`RecursionChallenge`) rather than verifying
in-circuit. This method performs the final out-of-circuit verification."* (`ipa.rs:268-293`). Because
the per-step circuit never pays the MSM, **depth is unbounded** — each step's cost is constant. **[C]**

**The 4-reduction cycle** (`accumulation.md`, the formal frame, from PCD-from-Accumulation 2020/499
App. A.2): the accumulation scheme is a *cycle of interactive reductions*
`Acc → PCS_d → IPA_ℓ → IPA_1 → Acc`. Any number of `Acc` instances reduce to a single `PCS_d`
(n-to-1), which the IPA folding collapses to `IPA_1`, which becomes one new `Acc`. *"The language is
self-reducing via a series of interactive reductions"* (`accumulation.md:77-138`). For **PCD**
(multiple input proofs) you carry **multiple accumulators**, one per input proof, all combined into the
single new one (`accumulation.md:783-816`). **[C]**

**Deferred values / passthrough** (`deferred.md`). A value `v ∈ Fq` needed both as `Fq` field
arithmetic *and* as an `Fq`-curve scalar can't be computed efficiently on one side. Pickles **"passes"**
it: keep `ṽ ∈ Fp` and `v ∈ Fq` equal-as-integers, decompose `v = 2h+l` to fit the smaller field, and
**bind** them by putting `(h,l)` in `Fp`'s public input and checking the commitment
`P_p = [h]G_h + [l]G_l` *on the Fq side* (where `E_p` is defined over `Fq`, so it's cheap). This is the
**`passthrough` data** in Pickles (`deferred.md:19-133`). It's how the transcript and accumulator hop
the curve boundary. Note (`accumulation.md:919-928`): the cycle-of-curves does **not** appear in the
accumulation math itself — there's *one accumulator per curve*, and the final verifier checks **both**;
the curve cycle is purely an efficiency device for the in-circuit EC ops, surfaced as `passthrough`. **[C]**

dregg's port of all of this is real: `step_verifier.rs` (Fiat-Shamir replay + `b(zeta)` native on Fp,
defers EC ops as public inputs), `wrap_verifier.rs` (`WrapVerifierWitness` carries L/R points as Fq
coords, prechallenges for EndoMul, the `c*Q + delta = z1*(sg + b(z)*U) + z2*H` check), `ipa_verifier.rs`
(the in-circuit IPA gadget, EndoMul+CompleteAdd), `glv.rs` (GLV endomorphism for the scalar muls). **[C]**

---

## The decider / compression step (= dregg's finalization & rejuvenation primitive)

**Yes, there is a final compression step, and it has a precise location.** In the accumulation frame the
"decider" is **Reduction 4 + the out-of-circuit `SRS::verify`**: at the end of a chain you take the
single carried `Acc` instance `(U, ⃗u)` and *actually* check `U = ⟨h, G⟩` — the one `O(ℓ)` MSM that was
deferred at every step. That is `poly-commitment/src/ipa.rs SRS::verify` (`ipa.rs:301-460+`): it
reconstructs `b(X)` from the challenges, batches all accumulators + PlonK poly commitments into **one
big multiexp** (`scalars`/`points`), and checks it. *This single batched MSM is dregg's "rejuvenation /
finalization" primitive: it collapses an unbounded chain of deferred checks into one verification.* **[C]**

Two compression flavors, both present in dregg's backend (`mina/pickles.rs:1-30`): **[C]**
- **Assisted recursion (the OPERATIONAL/production path):** each step *defers all* IPA ops; the final
  external verifier runs full `kimchi::verifier::verify`, which batch-checks **all** accumulated IPA
  commitments in one MSM. Simpler circuit, heavier final verify.
- **Mina-equivalent (`standalone.rs`):** verifies everything in-circuit *except* the `sg` MSM; the
  external verifier does only `batch_dlog_accumulator_check` (one batch MSM over SRS generators).
  Heavier circuit (EndoMul+CompleteAdd), minimal final verify. This is the target for "smallest decider."

For a true **constant-size succinct final proof** (not just a batched check), Mina wraps the terminal
proof so the on-chain verifier is constant work — this is what `arrabbiata`'s decider was *meant* to be
(`lib.rs:11` "the SNARK used on the accumulation scheme") but it's **`unimplemented!()`**. So for Path B
dregg's decider = **the kimchi/IPA batched `SRS::verify` (real, audited-lineage)**, not arrabbiata's
folding decider (vapor). **[C]** dregg's `stark_in_pickles.rs` already shows the constant-size wrap:
STARK → Kimchi (~5 KiB) → Pickles recursive (~5 KiB, constant-size, composable). **[C]**

---

## Borrow vs reimplement: the integration recommendation

**Recommendation: BORROW by vendoring `kimchi` + `poly-commitment` + `mina-curves` directly, and keep
dregg's existing `circuit/src/backends/mina` Pickles-shaped layer as the recursion driver. Do NOT
reimplement the accumulation math, and do NOT wait on arrabbiata.** **[F]**

Rationale, grounded:
1. **dregg already did ~80% of the borrow.** The `mina/` backend ports the real step/wrap dual-curve
   architecture, the in-circuit IPA verifier, GLV/EndoMul, and `RecursionChallenge` passthrough, calling
   straight into upstream `kimchi`/`poly_commitment`. `pickles.rs` is self-described "OPERATIONAL —
   tested, sound, used in production paths." The realistic Path-B task is **finish + harden**, not build. **[C]**
2. **The accumulation core is curve-arithmetic-heavy and audit-sensitive — exactly the code you must NOT
   hand-roll.** Vendor `poly-commitment` (IPA) and `kimchi` (PLONK + gates) verbatim; treat `book/docs/pickles/`
   as the conformance spec. dregg's value-add is the *application circuit* (the Step circuit's app logic =
   the Effect-VM / auth statement), not the accumulator. **[F]**
3. **Use `stark_in_pickles.rs` as the keystone integration shape.** It already bridges dregg's BabyBear
   STARK world into Pickles: BabyBear STARK → (Kimchi verifier circuit, Poseidon-Merkle to cut rows
   272K→30K) → Kimchi proof → Pickles recursive wrap = constant-size, composable. This is **the** path
   to make Pickles dregg's *primary* unbounded-IVC engine while reusing the STARK AIRs as leaf provers. **[C]**
4. **Avoid arrabbiata for now.** It's the Nova/ProtoStar folding flavor with a stubbed decider; adopting
   it would be reimplementing what kimchi+IPA already ship audited. Park it as a *future folding option*
   only. **[C]**

**Concrete integration shape (Path B primary IVC):** **[F]**
- **Leaf:** an Effect-VM / auth-statement proof. Either a kimchi Step circuit directly, or a BabyBear
  STARK lifted via `stark_in_pickles.rs`.
- **Step circuit** = app logic (the 6-clause auth-in-proof statement: key→delegation→policy→effect-fold→
  replay→cell-root) **+** verify-previous-wrap (first half) + verify-previous-step (second half) +
  `acc = Aggregate(prev_acc, π)`.
- **Carry** = `RecursionChallenge` (the `sg`/`U` accumulator + `chals`) as the IVC state, threaded via
  `create_recursive`. This *is* dregg's per-turn / per-cap-chain succinct state.
- **PCD** (cross-cell aggregation): a Step that ingests N wrap proofs → N input accumulators combined
  into one. This replaces the current `effects_hash_global ← Σ effects_local` clear-text stitch with a
  genuine n-to-1 accumulation.
- **Decider / rejuvenation:** the batched `SRS::verify` (assisted) or `batch_dlog_accumulator_check`
  (standalone). One MSM finalizes an unbounded chain.

---

## The PQ-migration seam (is the accumulation abstraction swappable?)

**Verdict: the *abstraction* is clean and swappable; the *current code* is curve-entangled. "Homomorphic-now +
PQ-later, abstraction preserved" is REAL — but the seam is the accumulation-scheme *interface*, not the
kimchi codebase, and you must architect to that interface deliberately.** **[C for the entanglement, F for the seam]**

What is genuinely abstract (the good news): **[C]**
- The PCD-from-Accumulation paper (2020/499) *defines* an **accumulation scheme** as an interface
  (`Acc.Prover`, `Acc.Verifier`, `Acc.Decider`) over *any* non-interactive argument — explicitly *"even
  if the argument itself does not have a sublinear-time verifier."* The whole Pickles construction is
  an *instance* of this interface. The spec's "cycle of reductions" view (`accumulation.md`) is
  presentation-agnostic: `Acc → PCS_d → IPA → Acc`. If you replace `PCS_d`/the folding reduction with a
  PQ analogue, the *cycle/IVC orchestration is unchanged*.
- **What would swap to go PQ, precisely:** the **commitment + its reduction-3/4 (the Halo trick)**.
  - Pasta (Pallas/Vesta) → a PQ accumulation substrate. Options on dregg's shelf:
    **lattice folding** (LatticeFold+/Neo/SuperNeo — Ajtai/Module-SIS homomorphic commitment, PQ,
    small-field) *keeps* the homomorphism (so the fold/accumulate shape survives almost 1:1), or
    **Fractal-style holographic recursion** (`fractal-pq-transparent-recursive-2019-1076.pdf` —
    Reed-Solomon/FRI + a holographic IOP, transparent + PQ) which *drops* homomorphism and instead does
    recursive-verifier-in-circuit (the Path-D shape).
  - The `b_poly`/`sg`/`RecursionChallenge` triple (the Halo trick) is *intrinsically* discrete-log: it
    relies on `U = ⟨h,G⟩` being a homomorphic Pedersen commitment whose MSM you can defer. Lattice
    folding has a *direct analogue* (the Ajtai commitment is also additively homomorphic, so "defer the
    expensive opening" survives); Fractal/FRI does **not** — there the accumulator becomes a FRI
    folding-relation re-execution, a *different* `Acc.Verifier`.

What is curve-entangled (the honest catch): **[C]**
- `RecursionChallenge` is generic over `G: AffineRepr` but the *meaning* of `comm`/`b_poly`/the deferred
  MSM is dlog-specific. The Pasta cycle, GLV/EndoMul gates (`glv.rs`), the `passthrough` field-hopping
  (`deferred.md`), and hash-to-curve `U`/`H` bases are all curve machinery. None of these survive a PQ
  swap unchanged — they'd be replaced by the lattice/FRI equivalents.
- So the migration is **not** "flip a commitment trait inside kimchi." It is: **define a dregg
  `AccumulationScheme` trait** (`prove_step`, `aggregate`, `decide`) with `kimchi+IPA` as instance #1,
  and re-instantiate it on lattice folding (Neo/SuperNeo, keeping homomorphism + the defer-the-MSM shape)
  or on FRI (Fractal, dropping homomorphism). **The seam is real iff dregg writes that trait now and
  routes all IVC through it** — otherwise the Pasta types leak everywhere and PQ-later becomes a rewrite. **[F]**
- **`stark_in_pickles.rs` is the practical hedge** that makes this less binary: BabyBear-STARK-as-leaf +
  Pickles-as-recursion means the PQ-sensitive part (the leaf computation, hash-based) is already PQ;
  only the *recursion glue* is pre-quantum. PQ migration then = swap *only* the glue, leaf AIRs untouched. **[C]**

---

## Coinductive fit

**Strong fit.** Pickles' per-step invariant — *"verify the previous proof + carry an accumulator,
producing a new proof of the same shape"* — is a **guarded corecursive step**, which is exactly the
coinductive soundness frame. **[C/F]**
- The IVC step is an endo-map on a *coinductive* state: `State = (app_state, Acc)`,
  `step : State → π → State`, where each step *consumes* one proof and *produces* one of the same type
  (`acc₂ = Aggregate(acc₁, π₂)`, `overview.md:36-38`). This is precisely the *unfold* of a final
  coalgebra: the proof stream is potentially infinite (unbounded depth), and soundness is a **safety
  property maintained coinductively** — "for all n, the n-th carried accumulator is valid."
- **Guardedness** = the Halo trick. Each step does only *bounded* (constant) productive work and
  **defers** the expensive MSM; the deferral is the guard that keeps the corecursion well-defined
  (productive) at unbounded depth. The decider (`SRS::verify`) is the *eventual* discharge — the
  coinductive equivalent of "observe the stream." This maps cleanly onto dregg's
  `guarded-recursion-coinductive.pdf` / `coinductive-proofs-regex-zk` framing and the "turn = guarded
  corecursive step" model: a turn verifies the prior turn's proof and emits a same-typed proof, deferring
  the heavy check to the vat-boundary decider. **[C for the mechanics, F for the dregg mapping]**
- PCD (n-to-1 accumulator combination) generalizes the corecursion from a *stream* to a *tree/DAG*
  unfold — matching dregg's cap-chain/cell-DAG topology, not just a linear chain. **[C]**

---

## Risks & open questions

1. **[C] This contradicts the standing `DECISION-recursion-strategy.md` (Path D).** That memo's deciding
   constraint — *"a hash-based FRI STARK has no additively-homomorphic commitment"* — is **correct and
   unchanged**. Path B does **not** refute it; Path B *adds a homomorphic substrate (Pasta/IPA) alongside
   the FRI spine* rather than transplanting folding onto FRI. The two reconcile **only** via
   `stark_in_pickles.rs`: FRI/BabyBear stays the **leaf** prover; Pickles/IPA becomes the **recursion/IVC**
   layer above it. dregg must decide consciously: Path B = "homomorphic recursion over hash-based leaves,"
   *not* "folding on FRI" (which remains impossible). State this in the synthesis or the contradiction will
   re-litigate itself.
2. **[C] Path B is NOT post-quantum today.** Pasta + IPA are pre-quantum, full stop. Path B's PQ story is
   entirely deferred to the migration seam — which is only real if dregg writes the `AccumulationScheme`
   trait *now* (see PQ section). If dregg ships Pickles-IVC without that abstraction boundary, "PQ-later"
   degrades to "PQ-rewrite."
3. **[C] 256-bit field tax.** Pasta is ~255-bit; dregg's native arithmetic is BabyBear (31-bit). Every
   BabyBear element embeds trivially in Fp, but BabyBear *multiplication* costs 3 Generic gates
   (`stark_in_pickles.rs`). Measure the Step-circuit row count for the real auth-in-proof statement before
   committing — the embedding is cheap per-element but the circuit is large.
4. **[C→confirm] How sound/complete is dregg's existing `mina/` port really?** `pickles.rs` claims
   "OPERATIONAL, tested, sound," but per global memory dregg's ZK is "partial, under-integrated, never
   audited." Before promoting to primary IVC: confirm `wrap_verifier.rs`'s in-circuit EndoMul actually
   *constrains* (non-zero coefficients, adversarial tests) the IPA check rather than merely witnessing it —
   this is the exact failure mode flagged in `feedback-kimchi-circuit-agents`. Audit `step_verifier` ↔
   `wrap_verifier` ↔ `ipa_verifier` deferred-value *binding* (the `passthrough` equality), since a missing
   bind silently breaks soundness (`deferred.md:54-58`).
5. **[C] arrabbiata is a trap, not a resource.** Its decider is `unimplemented!()`. Do not let "Mina has a
   folding crate" imply folding-IVC is available — the *accumulation* (Halo) path is what ships; the
   *folding* (Nova) path is vapor. If dregg later wants true folding, that's a separate build.
6. **[F] Decider succinctness.** The batched `SRS::verify` is a *check*, not a *constant-size proof*. For
   on-chain / cross-vat hand-off you want the constant-size Pickles wrap (`stark_in_pickles.rs` shows ~5
   KiB constant). Confirm the terminal wrap exists end-to-end in dregg, not just the batched check.
7. **[F] Two recursion engines will coexist** (FRI-verifier `p3-recursion`/`RecursiveFriAir` from Path D,
   and Pickles/IPA from Path B). Decide the division of labor explicitly: leaf=FRI, IVC-glue=Pickles is
   coherent; maintaining *two* unbounded-IVC engines is not. The `AccumulationScheme` trait is also what
   lets these share one IVC orchestration surface.
