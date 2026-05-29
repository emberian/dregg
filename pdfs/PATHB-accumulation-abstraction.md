# PATH B — The accumulation abstraction & swappable backend

> **Mandate.** dregg chose PATH B: homomorphic cycle-of-curves / folding recursion *now* for
> succinct unbounded IVC (Mina-Pickles reference), with the constraint *"be as PQ-now/hash-native
> as we can — maybe run a homomorphic track AND a PQ/hash track in parallel behind ONE swappable
> accumulation interface."* This memo answers: **is that swappable interface real, and what is it?**
>
> **One-line verdict.** The *signatures* (`Prove`/`Verify`/`Decider`) abstract cleanly across all
> four backends — BCMS20 already wrote that trait. **The homomorphism assumption does NOT leak
> through the signatures; it leaks through the soundness contract as a *depth bound*.** So a single
> `AccumulationScheme` trait is real **iff the IVC/PCD layer is written against a depth-parameterised
> soundness contract** (a *family* of deciders `{D_s}`), with `d = ∞` for homomorphic/lattice
> backends and `d < ∞` for the hash-native backend. Get that one type right and homomorphic-now →
> PQ-later is a backend swap, **not** an IVC rewrite. Get it wrong (assume `d = ∞` everywhere) and
> you have silently baked the homomorphism in. Legend: **[G]** grounded in a paper read here ·
> **[F]** forward-design.

---

## The accumulation-scheme interface (BCMS20 / Halo-Infinite, with signatures)

**BCMS20 (`2020/499`, §4.1) is the canonical interface.** [G] An accumulation scheme for a predicate
`Φ : U(∗) × ({0,1}*)³ → {0,1}` (the thing being batch-checked — for us `Φ = ` "the inner STARK/SNARK
verifier accepts `(x, π)`") is a **5-tuple of algorithms** `AS = (G, I, P, V, D)`, all sharing a
random oracle `ρ`:

```
G(1^λ)                       -> pp                         -- Generator: public parameters
I(pp, pp_Φ, i_Φ)             -> (apk, avk, dk)             -- Indexer: prove/verify/decide keys
P(apk, [q_i]_{i=1..n},                                     -- Accumulation PROVER:
       [acc_j]_{j=1..m})     -> (acc, π_V)                 --   fold n new inputs + m old accumulators
                                                           --   into one new accumulator + helper proof
V(avk, [q_i], [acc_j],                                     -- Accumulation VERIFIER (the *recursive*
       acc, π_V)             -> bit                        --   one — must be CHEAP / sublinear)
D(dk, acc)                   -> bit                        -- DECIDER: one final check that ALL
                                                           --   accumulated q_i satisfied Φ
```

with the two load-bearing properties (verbatim shape from §4.1):

- **Completeness:** if every old `acc_j` decides (`D(dk,acc_j)=1`) and every new input satisfies the
  predicate (`Φ(q_i)=1`), then `P` produces `(acc, π_V)` with `V(...)=1` **and** `D(dk,acc)=1`.
- **Soundness:** if `V(...)=1` **and** `D(dk,acc)=1`, then (knowledge-extractably) every old
  accumulator decided **and** every new `Φ(q_i)=1`. *This is the clause where the homomorphism leaks.*

**Two refinements that matter for the trait:**

1. **Split accumulation (BCLMS21 / `pcd-without-succinct-arguments-2020/1618`, used by acc-w/o-homo).** [G]
   Every accumulator splits `acc = (acc.x, acc.w)` into a **short instance part** `acc.x` and a
   **long witness part** `acc.w`; likewise `π = (π.x, π.w)`. The recursive verifier `V` touches only
   the short `.x` parts; the decider `D` touches the witness. This is the structure that makes the
   recursive circuit cheap and is the one all hash-native schemes use. **The dregg trait must be the
   *split* form**, not atomic.

2. **Halo-Infinite (`2020/1536`) is the same object specialised to a PCS, and names the leak.** [G]
   Its "PCS aggregation / accumulation scheme" *coincides* with BCMS20's PCS accumulation (§stated
   explicitly, "our notion of public aggregation coincides with PCS accumulation"). Its headline
   theorem: **every *additive* PCS has an efficient aggregation scheme**, where the prover only needs a
   **Linear-Combination Scheme (LCS)** — "compute linear combinations of commitments over G … no
   additional proof is required." That LCS *is* the homomorphism, stated as the genericity boundary.

`I, P, V, D` (and split-`acc`) are the four method signatures of the dregg trait. **They are
backend-agnostic.** What differs per backend is *what `D` costs, whether `V` is sublinear, and — the
crux — whether soundness holds for unbounded `n` chained steps.*

---

## What each backend needs of the commitment (the leak table)

The predicate Φ is always "an inner verifier accepted." What changes is **how `P` folds** and
therefore **what algebraic structure the commitment must have**.

| Backend | Commitment | Additive? | Homomorphic? | What `P` does to fold | `V` (recursive) cost | `D` (final) cost | Depth | PQ? | Fits dregg FRI/BabyBear? |
|---|---|---|---|---|---|---|---|---|---|
| **(a) Halo / IPA / Pickles** (`2019/1021`, `2020/1536`) | Pedersen / IPA over a curve | **yes** | **yes** | random linear combo of commitments **in G** (LCS), no proof needed | O(1) (a few EC muls) + non-native field ⇒ **curve cycle** | one IPA/MSM check, ~O(√d or log d) | **∞ (unbounded)** | **no** (dlog) | **no** — homomorphic, non-PQ; this is the Mina-interop quarantine backend [G] |
| **(b) Nova-folding** (`2021/370`) | Pedersen of relaxed-R1CS witness | **yes** | **yes** | fold two relaxed-R1CS instances: `E ← E₁ + r·T + r²·E₂`, `W ← W₁+rW₂` — **needs `Com` homomorphic** | O(1), 2–3 EC muls (+ CycleFold) | one R1CS-sat + commitment opening | **∞** | **no** | **no** — explicitly "Pedersen … homomorphic"; eliminated by DECISION-recursion-strategy [G] |
| **(c) ProtoStar** (`2023/620`) | **homomorphic** commitment (Pedersen default) | **yes** | **yes** (stated step 1: "compress prover messages by committing in a *homomorphic* commitment scheme") | sample `α`, **linear combination** of accumulator + NARK; `k+2` group muls | O(k) group muls | one NARK-check + error-term check | **∞** | **no** | **no** — generic over *special-sound protocols* but **not** over the commitment; homomorphism is step 1 [G] |
| **(d) Acc-without-homomorphism** (`2024/474`) | **non-homomorphic** vector commitment (Merkle / sym-key) + a linear code C | **no** | **NO** | commit `acc.w = C(w)` as codeword; fold by **spot-checking** `α·acc₁.w + β·acc₂.w ≈_δ acc₃.w` over the encoding | O(spot-checks) Merkle openings | check `acc.x` commits `acc.w` **and** `acc.w` is δ-close to C | **BOUNDED `d`** (relaxed-decider drift attack) | **yes** (sym-key only) | **YES — Merkle-native, the only one** [G] |
| **(e) Lattice folding** (LatticeFold+/Neo/SuperNeo, watch-list) | **Ajtai / Module-SIS** | **yes (module)** | **yes** | linear combination in the module + range/norm proof (bit-decomp) | one sumcheck | norm/range check | **∞** | **yes (plausible)** | **no** — PQ *but a different homomorphic commitment*; adopting = rip out FRI, install Module-SIS [G via DECISION memo] |

**Reading the table — the one fact that organises everything:**

- Backends (a),(b),(c),(e) all fold by a **linear combination of commitments**. That step is *only
  sound and succinct* because `Com(αx+βy) = α·Com(x)+β·Com(y)` — **additivity/homomorphism**. Take it
  away and the linear combination of *commitments* no longer corresponds to the linear combination of
  *witnesses*. This is why Nova needed *relaxed* R1CS (an error term `E` to absorb the cross-term),
  why ProtoStar lists homomorphic commitment as step 1, and why Halo-Infinite's whole genericity is
  bounded by "additive PCS / has an LCS."
- Backend (d) is the *existence proof* that you can keep **the exact same `(P,V,D)` interface** with a
  **non-homomorphic Merkle commitment** — by replacing "linear combination of commitments" with
  "**spot-check a linear relation over an error-correcting encoding** of the witnesses." [G] **The
  price is paid in the soundness clause, not the signature:** the extractor only yields witnesses that
  are *δ-close* to the code (a **relaxed decider**), and a cheating prover can walk a bad codeword to a
  good one over `k` steps ⇒ soundness holds only up to a **fixed maximum depth `d`** (§"bounded-depth",
  Def. with a *family* of deciders `{D_s}_{s=0..d}`, `D = D_0`, `d = ∞` recovers ordinary soundness). [G]

**Therefore the leak is precisely:** the homomorphism does **not** show up as a different method
signature (every backend has `P/V/D` over a split `acc`). It shows up as **whether the soundness
contract is `d = ∞` or `d < ∞`**, plus the *cost profile* of `V` (sublinear & curve-cycle-free?) and
`D`. An interface that hard-codes `d = ∞` and ignores `D`-cost has silently assumed homomorphism.

---

## VERDICT: is a swappable `AccumulationScheme` trait real?

**Yes — with one non-negotiable shape constraint, and one honest caveat.** [F, grounded in the four papers]

**Real, because:** BCMS20 *already proved* the genericity that the dregg constraint is asking for. Its
PCD/IVC construction (§2.1, §5) is written **against the abstract `AS = (G,I,P,V,D)` interface and
nothing else** — it instantiates that interface with *both* a dlog backend (`PCD_L`, IPA) *and* an
AGM/pairing backend (`PCD_AGM`) from the *same* PCD theorem. Halo-Infinite extends the *same*
aggregation interface to "any additive PCS." Acc-without-homomorphism re-uses *literally the same
split-`(P,V,D)`* and gets PCD from it. So **four papers independently target one interface.** The
trait is not invented by dregg; it is the lingua franca of the whole accumulation literature.

**The one shape constraint — the narrowest viable interface — the IVC layer MUST be written against:**

1. **Split accumulator**: `type Instance` (short, what `V` sees) + `type Witness` (long, what `D` sees).
2. **Depth-parameterised soundness**: the trait carries a `const MAX_DEPTH: Option<u64>` (≡ BCMS20/acc-w-o-homo
   `d`, `None = ∞`). The IVC layer must treat `D` as a **family `{D_s}`** and refuse to compile a PCD
   graph whose depth exceeds `MAX_DEPTH`. Homomorphic/lattice backends set `None`; the hash backend
   sets `Some(d)`. **This single associated const is where the homomorphism assumption is quarantined.**
3. **No commitment type in the interface.** `Com`, "additive," "curve cycle," "Ajtai," "Merkle" must
   **not** appear in the trait. They are private to the impl. (Halo/ProtoStar/Nova *would* tempt you to
   expose an `additive_combine(&[C], &[F]) -> C` — **do not**; that method *is* the homomorphism leak,
   and backend (d) cannot implement it.)
4. **`V` advertises its own recursion cost shape** (an associated `RecursionShape { native_field, needs_cycle: bool }`)
   so the IVC layer can decide whether it must instantiate a *cycle of curves* (Halo/Nova/ProtoStar:
   `needs_cycle = true`) or stay single-field (acc-w-o-homo, FRI-recursion: `false`). This is the
   *second* thing that leaks — but it leaks as **data the IVC layer reads**, not as a rewrite.

**The honest caveat (the irreducible part).** The homomorphism assumption **cannot be fully hidden**,
because it is equivalent to **unbounded depth**. You can abstract *whether the commitment is
homomorphic* (the trait doesn't name `Com`), but you **cannot abstract away its consequence** — an
unbounded-IVC layer is sound on a homomorphic backend and **unsound on the hash backend past depth `d`.**
So the narrowest faithful interface abstracts the *mechanism* (homomorphic combine vs. code spot-check)
**but exposes the *capability* (`MAX_DEPTH`)**. Any design that hides `MAX_DEPTH` is lying.

**For dregg specifically (reconciling with `DECISION-recursion-strategy.md`):** that memo *eliminated*
the folding line (a,b,c,e) for the FRI spine because FRI has no homomorphic commitment, and chose
**STARK-native recursive-verifier recursion** (Plonky3 `p3-recursion` / `RecursiveFriAir`) as primary —
which is **unbounded-depth and already in-tree**. Note: **recursive-verifier recursion is *not* an
accumulation scheme** — it has no `acc` and no `D`; the recursive `V` *is* the full inner verifier.
So the cleanest dregg framing is a slightly **wider** trait, `RecursionBackend`, with **two
sub-shapes** under one IVC layer:

- **AccumulationBackend** (`P,V,D`, split `acc`, `MAX_DEPTH`) — homomorphic (Pickles, interop), lattice
  (Neo/SuperNeo, PQ watch-list), or hash-spot-check (acc-w-o-homo, PQ, bounded).
- **RecursiveVerifierBackend** (no `acc`/`D`; `V_inner` in-circuit; `MAX_DEPTH = None`) — FRI-verifier
  recursion, the in-tree default.

Both expose the *same upward contract to the IVC/PCD layer*: "given a child node's `(x, proof)`, produce
a parent `proof` that succinctly attests the child verified, bounded by `MAX_DEPTH`." **That upward
contract is the genuinely swappable interface.** The accumulator-internal `(P,V,D)` is an
*implementation detail of the AccumulationBackend variant.*

---

## "Both in parallel": one trait / two impls vs two IVC layers?

**It is ONE IVC/PCD layer over ONE upward contract — with TWO backend *families* under it, not two IVC
layers.** [F] Concretely:

- The IVC layer only ever calls `prove_step(parent_inputs, [child_proofs]) -> parent_proof` and
  `verify(proof) -> bool`, and reads `MAX_DEPTH` + `RecursionShape` to (a) reject over-deep graphs and
  (b) decide whether to stand up a curve-cycle co-processor. **Nothing above the trait knows whether
  folding, accumulation, or recursive-verification happened underneath.** This is exactly what BCMS20
  delivers: one PCD theorem, multiple commitment instantiations.

- **But "both in parallel" is two *impls* only if you accept the union of their constraints.** The
  homomorphic track (Pickles) needs a **curve cycle + curve-cycle co-processor** in the recursion
  circuit; the hash track does not. So "one trait, two impls" is true at the *type* level, but the two
  impls do **not share a circuit substrate** — the recursion circuit for Halo is a foreign-field EC
  arithmetic circuit; for FRI-recursion it is a Poseidon2/FRI-fold circuit. They share the *trait* and
  the *IVC orchestration*, they do **not** share the *gadget library*.

- **The two-track recommendation, made precise:** run the **homomorphic track as a *bounded interop
  appendage*** (the existing Kimchi/Pickles backend, Pasta+IPA, `MAX_DEPTH = None`, `needs_cycle = true`)
  behind the trait — used for **Mina interop only**, exactly as the DECISION memo quarantines it. Run
  the **hash track (FRI recursive-verifier, `RecursiveVerifierBackend`, unbounded, `needs_cycle = false`)
  as the primary PQ spine.** They are **one trait, two impls, one IVC layer** — *provided the IVC layer
  was written against the depth-parameterised, commitment-free contract above.* If instead the IVC layer
  had been written against a homomorphic `additive_combine`, you would have **two IVC layers**, because
  the hash impl literally cannot provide that method. **So the abstraction's reality is entirely
  decided by whether you expose `additive_combine` (two layers) or `MAX_DEPTH` (one layer).** Choose
  `MAX_DEPTH`.

- **Migration test (the user's "migrate to PQ later without rewriting IVC"):** start on the homomorphic
  Pickles impl; later swap to FRI-recursion or lattice (Neo/SuperNeo) impl. **If and only if** the IVC
  layer never called a homomorphism-specific method and tolerates `MAX_DEPTH`, the swap is a
  `Box<dyn RecursionBackend>` substitution + a circuit-substrate switch. **The IVC/PCD orchestration
  code does not change.** That is the whole prize, and it is achievable. [F]

---

## Proposed dregg trait sketch (Rust + Lean spec stub)

```rust
/// The single upward contract the IVC/PCD layer is written against.
/// NOTHING here names a commitment, a curve, additivity, or a field choice:
/// those are the leak surfaces and live entirely inside impls.
pub trait RecursionBackend {
    /// Short, recursively-verified part of a node's evidence (BCMS20 acc.x / a proof).
    type Instance: Clone;
    /// Long witness part the Decider consumes (acc.w); `()` for recursive-verifier backends.
    type Witness;
    /// The succinct object passed up the PCD edge.
    type Proof: Clone;
    type VerifyKey;

    /// THE leak, quarantined to one associated const.
    /// `None` = unbounded-depth soundness (homomorphic / lattice / FRI-recursion).
    /// `Some(d)` = bounded-depth (acc-without-homomorphism): IVC MUST reject deeper graphs.
    const MAX_DEPTH: Option<u64>;

    /// The OTHER leak, exposed as inspectable data, never as a rewrite:
    /// does this backend force a cycle-of-curves recursion co-processor?
    fn recursion_shape(&self) -> RecursionShape; // { native_field, needs_cycle: bool }

    /// Fold/accumulate/recursively-verify children + this node into one parent proof.
    /// (Internally: Halo = LCS over G; Nova = relaxed-R1CS fold; ProtoStar = α-combine;
    ///  acc-w/o-homo = code spot-check; FRI = in-circuit inner verifier. All hidden here.)
    fn prove_step(
        &self,
        node_statement: &NodeStatement,
        children: &[(Self::Instance, Self::Proof)],
    ) -> Result<(Self::Instance, Self::Proof), BackendError>;

    /// Cheap recursive check (BCMS20 V): used INSIDE prove_step's circuit.
    fn verify_step(&self, vk: &Self::VerifyKey,
                   parent: &Self::Instance,
                   children: &[Self::Instance],
                   proof: &Self::Proof) -> bool;

    /// Final, one-shot check (BCMS20 Decider D). For bounded-depth backends this is
    /// the depth-indexed D_s; `remaining_depth` is ignored when MAX_DEPTH == None.
    fn decide(&self, vk: &Self::VerifyKey,
              acc: &Self::Instance, wit: &Self::Witness,
              remaining_depth: u64) -> bool;
}

/// Impls (one trait, several impls — the "parallel tracks"):
///   PicklesBackend     : Instance=acc.x over Pasta, MAX_DEPTH=None, needs_cycle=true   (interop, non-PQ)
///   FriRecursionBackend: Witness=(),              MAX_DEPTH=None, needs_cycle=false   (PRIMARY, PQ, in-tree)
///   MerkleAccBackend   : code-spot-check acc,     MAX_DEPTH=Some(D), needs_cycle=false (PQ, bounded — 2024/474)
///   NeoLatticeBackend  : Ajtai acc,               MAX_DEPTH=None, needs_cycle=false   (PQ watch-list)
```

```lean
-- Lean spec stub: the soundness contract is depth-indexed (the homomorphism quarantine,
-- following acc-without-homomorphism §"bounded-depth knowledge soundness").
structure RecursionBackend where
  Instance : Type
  Witness  : Type
  Proof    : Type
  maxDepth : Option Nat            -- none = ∞ (homomorphic / lattice / FRI)
  proveStep : NodeStatement → List (Instance × Proof) → Option (Instance × Proof)
  verifyStep : Instance → List Instance → Proof → Bool
  decide   : Nat → Instance → Witness → Bool   -- D_s : the family, indexed by remaining depth

/-- The single IVC/PCD soundness law, stated ONCE against the abstract backend.
    For `maxDepth = none` it is ordinary (unbounded) knowledge soundness;
    for `some d` it is bounded-depth KS. The proof obligation each impl discharges
    is the SAME statement; only the depth parameter differs. -/
theorem ivc_sound (B : RecursionBackend) (s : Nat)
    (h : ∀ d, B.maxDepth = some d → s ≤ d) :
    -- if a parent decides at remaining-depth s and verifyStep accepts,
    -- an extractor yields child witnesses that decided at depth (s-1)
    KnowledgeSound B s := by
  sorry  -- discharged per-impl; homomorphic & FRI: s arbitrary; Merkle: s ≤ d
```

The Lean stub makes the verdict checkable: **there is one `ivc_sound` statement; the homomorphism
difference is the single hypothesis `h` on `s` vs `maxDepth`.** That is the formal meaning of "the
abstraction is real but the homomorphism leaks as a depth bound."

---

## Risks & open questions

- **[F] The `additive_combine` temptation is the single failure mode.** Any PR that adds a
  homomorphic-combine method to the trait (because it's "convenient for the Pickles/Nova impl") instantly
  forks the abstraction into two IVC layers. Guard this in review: the trait must stay commitment-free.
- **[G] Bounded depth is fatal for dregg's stated model.** acc-without-homomorphism is the *only*
  hash-native accumulation scheme, and it is depth-bounded; dregg's "indefinite cap-chains / unbounded
  turn strands" model wants `MAX_DEPTH = None`. ⇒ the PQ-now answer is **not** acc-w-o-homo; it is the
  in-tree **FRI recursive-verifier** (unbounded, but *not* an accumulation scheme — `Witness = ()`,
  `decide` trivial). Hence the trait must be `RecursionBackend` (superset), not `AccumulationScheme`
  (which would exclude the actual primary backend). **This is the most important correction.**
- **[F] Curve-cycle co-processor is a real, non-abstractable substrate cost.** `needs_cycle = true`
  backends (Pickles/Nova/ProtoStar) require a foreign-field EC gadget library the FRI track never builds.
  The trait abstracts orchestration, not gadgets; budget two gadget libraries if you truly keep the
  homomorphic track live, and prefer keeping Pickles as a thin interop appendage rather than a co-equal track.
- **[G] BCMS20's `V` must be *sublinear* for recursion to close.** The interface permits an expensive `V`;
  the IVC layer needs `V` sublinear (BCMS20 Thm: "accumulation verifier sublinear ⇒ PCD"). Make
  sublinear-`V` a documented precondition the IVC layer asserts, not an assumption.
- **[F] ZK is a per-impl property, not interface-level.** BCMS20 defines AS zero-knowledge separately;
  dregg's ZK comes from `HidingFriPcs` on the FRI track and from blinding on the homomorphic track. Do
  **not** put a ZK method on the trait; make it an impl capability flag.
- **[F] Lattice (Neo/SuperNeo) fits the trait at `MAX_DEPTH = None, needs_cycle = false`** — so it is the
  *clean* PQ migration target *if* FRI-recursion's prover cost ("large verifier circuits") becomes the
  binding constraint. The trait is what makes that future swap a backend change, not a rewrite. Confirm
  Neo's commitment can be slotted without an `additive_combine` escape on the trait (it can — keep it
  inside the impl). **[A→confirm against a Neo/SuperNeo read.]**
