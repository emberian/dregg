# LEARNINGS — Metatheory tooling & the integrity-theorem precedent

> Axis: how to structure `./metatheory` (Lean4) + the integrity-theorem precedent for the
> vat-boundary law. Grounded in six PDFs read in full/part (see below) + `docs/rebuild/00-synthesis.md`
> §8–9. Tags: **[G]** = grounded in a paper/code coordinate I read; **[F]** = forward design
> (my recommendation, not in any source). Honest bias note: none of these six papers formalizes
> a *capability* integrity theorem — that precedent is seL4/l4v (`~/dev/l4v`), which I did not
> read here; I lean on the synthesis doc's framing of it and mark those claims **[F-on-l4v]**.

## Papers read
- **lean4-theorem-prover-and-language.pdf** [G, full] — de Moura & Ullrich. Lean4 is *both* a
  CIC-based prover *and* a strict FP language compiling to C; small trusted kernel; reference
  checkers / export; hygienic macro system (build EDSLs as `syntax` + `macro_rules`); `deriving`
  for `DecidableEq`/`Repr`; `#eval`/`decide` execute decidable props; FBIP for fast pure code.
- **igloo-refinement-separation-logic-oopsla20.pdf** [G, §1–2] — Sprenger et al. (Isabelle/HOL).
  Six-step methodology linking an abstract event-system model → I/O specs → separation-logic code
  proofs, *without modifying the program verifier*. The key device is a **simulation-relation
  refinement** `(E₂,I₂) ⊑_π (E₁,I₁)` plus a "verifier assumption": a Hoare triple over the I/O
  spec *implies* the code's I/O behavior refines the spec. Decouples model from code → multiple
  languages/verifiers (Java/VeriFast, Python/Nagini).
- **verdi-verified-distributed-pldi15.pdf** [G, §1–2] — Wilcox et al. (Coq). Write+verify in Coq,
  **extract to OCaml**; pick a *network semantics* (fault model) as a parameter; **verified
  system transformers (VST)**: prove under an idealized fault model, then a transformer carries
  the guarantee to a harsher model *with no extra proof burden*. First mechanized linearizability
  proof of Raft. Explicitly **safety only; liveness left to future work.**
- **velisarios-bft-coq.pdf** [G, §1,4] — Rahli et al. (Coq). "Logic of events" framework for
  BFT-SMR; machine-checked **PBFT agreement (safety)**. Core reusable kit: a **quorum-overlap
  lemma** (any two ≥-quorum sets share a correct node), **certificates** (strong = 2f+1, weak =
  f+1), and a **distributed-knowledge / epistemic** layer (`know`/`learn`, "a node knows X iff X
  is stored locally"). Extracts to OCaml runtime. Agreement needs only *past* events.
- **ironfleet-distributed-systems.pdf** [G, §1–3] — Hawblitzel et al. (Dafny/TLA). **Two-level
  refinement**: TLA-style state-machine refinement (high spec ← protocol layer) stacked on
  Floyd-Hoare refinement (protocol ← imperative impl). **Reduction** collapses fine-grained
  concurrent steps to coarse atomic ones (needs a reduction-enabling obligation). **Always-enabled
  actions** tame liveness. Proves *both* safety and liveness of Paxos-RSM + sharded KV.
- **iris-from-the-ground-up.pdf** [G, §1–2] — Jung et al. (Coq). Higher-order concurrent
  separation logic = **PCMs (partial commutative monoids) for user-defined ghost state** + **invariants**.
  PCMs encode "permissions, tokens, capabilities, histories, protocols"; **fictional separation**
  ties ghost state to physical state; **frame-preserving updates** + **view shifts**; cameras
  (step-indexed PCMs) for higher-order ghost state. Slogan: "monoids and invariants are all you need."

## Key ideas (attributed)
- **[G, Lean4]** Spec and executable oracle in *one* artifact: a Lean `def` is runnable
  (`#eval`/compiled C) and provable; `deriving DecidableEq` + `decide` turn the spec into a
  decision procedure for free — exactly what a golden oracle needs. Small kernel + export ⇒ the
  certified core is checkable independently of Rust.
- **[G, IGLOO]** You can soundly bridge an abstract model to real code *through an interface*
  (I/O spec) instead of extracting code: the model proof and the code proof meet at a refinement
  obligation, and the code verifier is used unmodified. The bridge contract is one implication:
  "verifier accepts the triple ⇒ behavior refines the spec."
- **[G, Verdi]** *Parameterize over the adversary.* The fault/network model is a pluggable
  semantics; transformers move a proof between models for free. Maps 1:1 onto dregg's *pluggable
  finality menu* (§4 of synthesis): tier = a network/fault semantics; a tier-lift is a VST.
- **[G, Velisarios]** A BFT safety proof reduces to **quorum overlap + certificate + "a correct
  node vouches"**. This is the entire reusable spine of a finality-tier proof; agreement uses only
  past events (no liveness, no clocks).
- **[G, IronFleet]** Layered refinement (spec ⇇ protocol ⇇ impl) + reduction is the maximal
  ambition; it gets liveness too but at very high proof cost and a fixed language (Dafny).
- **[G, Iris]** Conservation/linearity *is* a PCM; capabilities/tokens are *literally* the
  canonical Iris ghost-state examples. If dregg ever needs to reason about a *concurrent mutable
  interior*, Iris is the off-the-shelf logic — but its machinery is the heaviest of all six.

## Takeaways for dregg (idea → move)
1. **[F, from Lean4]** Make the Lean core *executable as the oracle*. Every semantic def
   (`step`, `compose`, `conserve`, `verifyWitness`) is a plain Lean function with `deriving Repr,
   DecidableEq`; the difftest harness `#eval`s / FFI-calls the compiled core. No separate "model"
   — the proof target and the oracle are the same code. This directly answers Decision §9.1
   (Lean = semantic core *and* golden oracle).
2. **[F, from IGLOO+Verdi] Use refinement-as-contract, NOT extraction, for the Rust bridge.**
   Verdi extracts (purely functional OCaml, "suboptimal performance" — IGLOO's own critique [G]);
   dregg explicitly keeps Rust as the crypto engine (§9.1), so extraction is wrong. Instead adopt
   IGLOO's stance: the Lean spec is the abstract event system; the Rust impl must *refine* it; the
   refinement obligation is discharged by **differential testing** rather than a Rust program
   logic (dregg has no Rust separation-logic verifier and shouldn't build one). The difftest *is*
   dregg's "verifier assumption," empirically rather than deductively checked.
3. **[F, from Verdi]** Encode the **finality tier as a Verdi-style pluggable semantics** in the
   Lean model: `Tier` is a parameter; tier-lifts (causal→ack-threshold→BFT) are transformer lemmas.
   This makes §4's "same DAG carries all four tiers" a *theorem schema*, not prose.
4. **[F, from Velisarios]** A machine-checked finality tier = **quorum-overlap lemma + certificate
   abstraction + agreement-from-past-events**. Realistic for tier-3 (BFT) *safety*. Lift the
   hardcoded `½(n+f)` (synthesis §4) into the quorum predicate the overlap lemma is parameterized by.
5. **[F, from Iris]** Do **not** reach for Iris for the categorical skeleton or the laws — an
   equational/monoidal model in plain Lean+mathlib is enough and far cheaper. *Reserve* Iris (or
   a hand-rolled PCM/ghost-state argument) for one place only: proving the **live-session interior**
   (CapSession, near-synchronous caps-as-caps) preserves the conservation invariant under
   concurrency. That is the single spot in dregg whose proof obligation is genuinely concurrent
   (see Q5).

## Proposed `./metatheory` layout & build order

**[F]** Lean4 project (`lakefile.lean`, depend on mathlib4 at `~/src/mathlib4`). Order is
cheapest-coherence-first; each step has a clear `sorry`-to-`theorem` arc.

```
metatheory/
  README.md                  -- the §8 caveat IN PROSE: Lean certifies the SEMANTIC skeleton & the
                             --   two laws; it does NOT establish cryptographic soundness (that the
                             --   STARK attests the morphism) — that lives in the circuit. Don't conflate.
  Dregg/
    Core/
      Cell.lean              -- (1) objects: CellState (content-addressed; do NOT bake N8 — synthesis §5.2)
      Turn.lean              -- (1) morphism: Turn over a flat Action-seq; id; comp (∘); category laws
      Category.lean          -- (1) thin posetal category: assoc + id (mathlib `Category`? or bespoke
                             --     `Quiver`+laws — keep it SMALL; a full mathlib `Category` instance
                             --     is optional sugar, the laws are the point)
    Laws/
      Conservation.lean      -- (2) LinearityClass; per-class sum; THEOREM: comp preserves the sum
                             --     (model as a monoid hom `Turn → (Class → ℤ or multiset)`). This is
                             --     the symmetric-monoidal / linear law all three spines kept.
      Ordering.lean          -- (2) strand = composable chain; canonicity; the "not subsumable" claim
                             --     stated (proved later / `sorry` first)
    Authority/
      Positional.lean        -- (3) caps-as-caps: authority = possession of a slot in a CDT/CSpace-like
                             --     structure; mediator-enforced; unforgeable by construction
      Epistemic.lean         -- (3) keys-as-caps: authority = knowledge of a key / a verifier-checkable
                             --     derivation proof; freely copyable
      LossyMorphism.lean     -- (3) the membrane functor caps→keys; THEOREM stating PRECISELY what is
                             --     lost (the mediator's structural guarantee) — the seL4-reflection
                             --     impedance mismatch as a theorem, not a hand-wave
    Membrane/
      Predicate.lean         -- Heyting predicate algebra on cell-states (synthesis §1)
      Witness.lean           -- Witness objects; the `Predicate ⊣ Witness` adjunction (unit/counit)
      VatBoundary.lean       -- (4) THE LAW (sketch below). Within-root: no witness. Cross-root: witness
                             --     mandatory. THE keystone theorem.
    Finality/
      Tier.lean              -- [Verdi] Tier as a pluggable ordering semantics; quorum predicate param
      QuorumOverlap.lean     -- [Velisarios] overlapping-quorums lemma (parameterized by σ, not ½(n+f))
      Agreement.lean         -- [Velisarios] tier-3 BFT agreement (safety) from certificates + past events
    Oracle/
      Eval.lean              -- executable `step`/`verify` with `deriving Repr, DecidableEq`; the
                             --   difftest entry points (JSON in/out for the Rust harness)
  test/                      -- Lean-side golden vectors (mirror dregg-dsl-differential corpus)
```

**Build order & what to `sorry` first:**
1. **`Core/` (Cell, Turn, Category)** — fully prove `id`/`∘`/assoc. No `sorry`. This is the
   coherence stress-test of "turn-as-generator" (§8): if `comp` won't typecheck cleanly, the
   spine is wrong. Cheapest, highest signal. **[F]**
2. **`Laws/Conservation`** — *prove* the monoid-hom preservation theorem early; it's small and it's
   the claim "all three spines asserted" (§1). `Laws/Ordering` — *state* canonicity, `sorry` the
   "not subsumable" non-existence result (it's the hardest pure-math claim; defer). **[F]**
3. **`Authority/` three files** — define both models; `sorry` `LossyMorphism`'s loss theorem until
   the two models are stable (you need both before you can state what the morphism drops). **[F]**
4. **`Membrane/VatBoundary`** — state the law immediately (so it anchors design), `sorry` the proof;
   it depends on 1–3. This is the one to make `sorry`-free *last*, deliberately. **[F]**
5. **`Finality/` + `Oracle/`** — independent of the membrane; can proceed in parallel. `Oracle` is
   `sorry`-free by construction (it's executable code). `Finality` follows the Velisarios template. **[F]**

`sorry`-first discipline: state *every* top-level theorem with its real signature on day 1
(so the .lean compiles and the shape is reviewable), `sorry` the bodies, then discharge
bottom-up (Core → Laws → Authority → Membrane). This mirrors l4v's "spec first, proof grinds up."

## The vat-boundary law: Lean statement sketch (with the crypto-attestation substitution)

**[F]** Core move: a `Turn` carries the trust-root(s) it touches; a turn is *intra-vat* when its
source/target endpoints share a root. The law says intra-vat turns are admissible with the
*trivial* witness, and inter-vat turns require a witness that **discharges the `Predicate ⊣
Witness` adjunction's unit** — and crucially, the witness is a *verifier-checkable object*, not a
kernel-read positional slot (the seL4→dregg substitution).

```lean
-- Authority/Positional.lean  (caps-as-caps: the seL4 integrity-theorem shape)
-- Integrity (seL4/l4v precedent [F-on-l4v]): a step modifies only cells it is authorized for.
def Authorized (caps : CapSet) (t : Turn) : Prop :=
  ∀ c ∈ t.touched, ∃ cap ∈ caps, cap.grants c t.mode      -- positional: possession ⇒ authority

theorem integrity (caps : CapSet) (s s' : CellState) (t : Turn) :
    Authorized caps t → step s t = s' →
    ∀ c, s.at c ≠ s'.at c → ∃ cap ∈ caps, cap.grants c t.mode := ...
    -- "a subject modifies only what its caps authorize" — the l4v integrity theorem, restated.

-- Membrane/VatBoundary.lean
structure Vat where root : TrustRoot
def Intra (t : Turn) : Prop := ∀ e ∈ t.endpoints, e.root = t.endpoints.head.root

-- The adjunction Predicate ⊣ Witness (Membrane/Witness.lean):
--   Predicate : Witness → Prop          (what a witness proves)
--   Witness   : carrier of evidence
-- A gate is `WitnessedCondition` (synthesis §3.1): satisfied by a witness w with  Verify P w = true.
def Discharged (P : Predicate) (w : Witness) : Prop := Verify P w = true   -- DECIDABLE / executable

-- THE LAW.  Two halves:
theorem vat_boundary_intra (caps : CapSet) (t : Turn) (s : CellState) :
    Intra t → Authorized caps t →
    Admissible s t (witness := Witness.trivial) := ...
    -- inside one trust-root the MEDIATOR (live session / trusted executor on its island)
    -- supplies the positional guarantee; NO cryptographic witness is needed.

theorem vat_boundary_cross (t : Turn) (s : CellState) (P : Predicate) :
    ¬ Intra t → t.gate = P →
    (Admissible s t (witness := w)  ↔  Discharged P w) := ...
    -- crossing a boundary: admissibility is EXACTLY witness-discharge of the gate predicate.
    -- This is where the WITNESS SIDE of the adjunction becomes mandatory.
```

**The crypto-attestation substitution, stated as the difference between the two theorems [F]:**
in `vat_boundary_intra`, authorization is *positional* (`Authorized caps t` — a `∃ cap ∈ caps`,
i.e. a kernel/mediator read of a slot it owns). In `vat_boundary_cross`, authorization is
*epistemic*: `Discharged P w` is a **decidable predicate `Verify P w = true`** — the witness `w`
is a freely-copyable, verifier-checkable object (a STARK proof / Merkle path / signature), and
there is **no mediator to read a slot** off-island (synthesis §2.2: "no shared kernel off-island").
So the substitution is literally: *replace the positional existential `∃ cap ∈ caps, cap.grants …`
(read by a trusted party) with the executable verification `Verify P w = true` (checked by anyone)*.
The `LossyMorphism` theorem then says precisely what crossing drops: the mediator's *structural*
unforgeability (caps-as-caps) is replaced by *cryptographic* unforgeability (keys-as-caps), and
the thing lost is **revocation-by-construction / non-copyability** — exactly the
"caps→keys drops the mediator's structural guarantee" of §2.2.

Note **[F]**: keep `Verify` as a Lean function returning `Bool` (`deriving DecidableEq`), *not* an
opaque axiom — that keeps the law executable as an oracle. But abstract `Verify` over a `VerifyKit`
typeclass so the Lean side does NOT model STARK internals (those stay in Rust; conflating them is
the §8 mistake). Lean proves "*if* Verify accepts *then* the morphism is admissible"; Rust+circuit
prove "Verify accepts ⇒ the computation actually happened." Two obligations, never merged.

## The spec↔impl bridge recommendation

**[F] Recommendation: differential testing, IGLOO-shaped, not extraction.** Reasoning, grounded:
- **Reject extraction (Verdi/Velisarios path).** Both extract to OCaml; IGLOO explicitly critiques
  extracted code as "purely functional…suboptimal performance," and "manual optimizations
  invalidate the correctness argument" [G]. dregg's whole §9.1 decision is *Rust stays the engine*;
  extracting a Lean prover would re-implement what must stay in Rust. Out.
- **Reject a Rust program logic (IronFleet/IGLOO-code-verifier path).** IGLOO needs VeriFast/Nagini;
  there is no production separation-logic verifier for the *specific* Rust dregg writes, and
  building one is a multi-year project. Out for a week-old rebuild.
- **Adopt IGLOO's *contract*, discharge it by difftest.** IGLOO's soundness rests on one
  implication: "verifier accepts ⇒ impl behavior refines spec" (the "verifier assumption"). dregg
  substitutes an *empirical* refinement check for the deductive one: the Lean core is the abstract
  event system; for a shared corpus of turns, **`Lean.step == Rust.execute` on all observable
  projections** (post-state commitment, conservation tally, witness-accept bit). dregg already has
  the `dregg-dsl-differential` 7-backend harness — wire Lean in as backend #8, the *golden oracle*.

**Exact wiring [F]:**
1. `metatheory/Dregg/Oracle/Eval.lean` exposes `step : CellState → Turn → CellState` and
   `verify : Predicate → Witness → Bool`, both `deriving Repr`, with JSON (de)serialization
   (`Lean.Json`). Compile to a small CLI (`lake exe oracle`) reading a turn vector on stdin,
   writing the post-state + tallies + accept-bit on stdout.
2. The Rust harness feeds **the same corpus** (canonicalized turn vectors — reuse the existing
   differential corpus) to both `lake exe oracle` and the Rust executor; assert observable equality.
   Lean is the *golden* side (its output defines "correct"); a mismatch is a Rust bug **unless**
   the Lean theorem for that case is still `sorry` (track this — an un-proved oracle is only as good
   as its test coverage; be honest about it).
3. Direction of trust: **for proven theorems**, Lean is ground truth and Rust is checked against it.
   **For `sorry`'d regions**, the difftest is just cross-validation (neither side certified) — mark
   these in the corpus so reports don't overclaim.
4. Long-game **[F]**: as `Membrane/VatBoundary` becomes `sorry`-free, the difftest upgrades from
   "cross-check" to "Rust conforms to a *certified* oracle" — the property that answers the peers'
   "huge-TCB / incoherent" complaints (§9.1 rationale).

## Distributed-protocol verification: what's realistically provable

**[G→F] Template for machine-checking a finality tier (a consensus rule):**
1. Model replicas as state machines over a message/event log (Velisarios "logic of events";
   IronFleet protocol layer). **[G]**
2. Define the tier's quorum/certificate predicate; prove the **quorum-overlap lemma** (Velisarios:
   any two write-quorums share ≥1 correct node), parameterized by the group's σ rather than `½(n+f)`. **[G→F]**
3. Prove **agreement (safety)** from overlap + certificates + "a correct node vouches, trace back to
   where the info was generated" — uses only *past* events, no clocks, no liveness. **[G]**
4. **[F]** Use Verdi-style transformers to lift a tier-1 (causal/CRDT) result to tier-2/3 as a
   change-of-semantics, matching synthesis §4's "same DAG, finalized later under a higher tier."

**Realistic vs out-of-scope for a week-old rebuild [F]:**
- **In scope (safety):** tier-3 BFT *agreement* (Velisarios shows it's a bounded, reusable proof);
  the quorum-overlap lemma (small, pure combinatorics — start here, it's a great first finality
  `theorem`); the conservation/integrity theorems (these are the real keystones and are *local*,
  not distributed).
- **Out of scope (for now):** *liveness* (Verdi & Velisarios both punt; only IronFleet does it, at
  enormous cost with always-enabled actions + a TLA embedding + reduction); full PBFT view-change;
  any *cryptographic* soundness of the witness (circuit obligation, not Lean). Honest framing: aim
  for **safety of one tier + the two laws**, not a verified consensus stack.

## Is Iris needed? (Q5)

**[F] Mostly overkill; reserve it for exactly one obligation.** The categorical skeleton + the two
laws + the vat-boundary law are *equational / order-theoretic / functorial* — plain Lean + mathlib4
(monoids, posets, maybe a hand-rolled adjunction) covers them, and Lean's executability gives the
oracle for free. Iris's heavy machinery (cameras, view shifts, weakest preconditions, invariants)
buys nothing there and would balloon the TCB the peers already complained about.

**When dregg *would* want Iris-style CSL [G→F]:** the **live-session interior** — `CapSession`
near-synchronous caps-as-caps (synthesis §2.1, §6) — is the one genuinely *concurrent mutable*
region (multiple promises/facets resolving against shared session tables). If you ever need to
prove "concurrent intra-vat turns preserve the conservation invariant and never forge a cap," that
is *precisely* an Iris obligation: conservation is a **PCM** (Iris's canonical ghost state — it
lists "tokens, capabilities" as the motivating examples [G]), and the session invariant is an Iris
**invariant**. Even then, prefer a *hand-rolled PCM/frame argument in Lean* over importing an Iris
port unless the concurrency genuinely defeats it — match synthesis's "simpler equational model"
preference and the "switch to the obviously-cleaner construct" memory. **Verdict: build the
skeleton + laws in plain Lean; flag the live-session interior as the one future Iris candidate.**

## Open questions / what to read next
- **[F]** Does dregg want a *full mathlib `CategoryTheory.Category` instance* for the base category,
  or a minimal bespoke `Quiver`+laws? (mathlib buys functor/adjunction lemmas for `Predicate ⊣
  Witness` — likely worth it; verify the import cost.) **Read next:** mathlib4 `CategoryTheory.Adjunction`.
- **[F-on-l4v]** I did *not* read l4v here. **Read next (highest priority):** the l4v integrity
  theorem (`~/dev/l4v`, the `Access`/`integrity`/`authorised` defs) to copy the *exact* shape of
  "a subject modifies only what its caps authorize" into `Authority/Positional.lean` — that is the
  literal precedent the user named.
- **[F]** How to canonicalize a `Turn` identically in Lean and Rust for the difftest corpus? The
  serialization must be byte-identical or the oracle comparison is on observable projections only
  (recommended) — decide which. **Read next:** the existing `dregg-dsl-differential` harness format.
- **[F]** Is the "ordering not subsumable" claim (synthesis §1) a provable *non-existence* result
  (no projection recovers canonicity) or a design stance? If provable it's a real (hard) Lean
  theorem; if a stance, mark it as an axiom with prose. Resolve before committing `Laws/Ordering`.
- **[G/Verdi]** Verdi's VST gives transformer composition "for free" — confirm whether a Lean
  encoding of tier-lifts can reuse that pattern or needs per-lift proofs. **Read next:** Verdi §3–4
  (transformer soundness) which I did not reach.
