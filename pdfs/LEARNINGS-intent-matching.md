# LEARNINGS — The intent-matching decidability seam

> Axis: the **verify/find** split in the intent/await family. The synthesis (`docs/rebuild/00-synthesis.md` §3.2)
> already *asserts* the seam ("VERIFY a fill = tractable; FIND a fill = undecidable in general; matcher must be a
> bounded pluggable domain-specific solver, never a general matcher"). This note **grounds** that assertion in three
> papers — gives it exact decidability boundaries, complexity classes, and a named Lean target — and marks where the
> synthesis is **forward design** vs. **grounded**.
>
> Legend: **[G]** grounded in a paper read here · **[C]** grounded in dregg code · **[F]** forward design (my proposal).

---

## Papers read

1. **Spies & Forster, "Undecidability of Higher-Order Unification, Formalised in Coq", CPP '20**
   (`undecidability-higher-order-unification-coq.pdf`). Machine-checked, in the Coq library of undecidable problems
   (uds-psl). The *precedent* for stating impossibility inside a proof assistant.
2. **Vukmirović, Bentkamp & Nummelin, "Efficient Full Higher-Order Unification"**
   (`efficient-full-higher-order-unification.pdf`). The practical *bounded* enumerator (Zipperposition); shows the
   real shape of "checking decidable fragments per-subproblem + a depth-limited pragmatic variant."
3. **Lehmann, Müller & Sandholm, "The Winner Determination Problem" (ch. 12, *Combinatorial Auctions*)**
   (`winner-determination-combinatorial-auctions-sandholm.pdf`). Market-clearing complexity: NP-hardness,
   inapproximability, and the special cases that *are* tractable.

---

## Key ideas (attributed)

### A. What is undecidable, what is decidable (Spies/Forster) **[G]**
- **Higher-order unification (HOU)**: given two simply-typed λ-terms `s,t`, does there exist a (well-typed)
  substitution σ with `s[σ] ≡ t[σ]` (convertible, *up to β*)? "Higher-order" because σ may insert λ-abstractions.
- **Undecidable in general**, by reduction `H10 ⪯ HOU` (Hilbert's 10th / Diophantine solvability, via Dowek).
  Sharpened: **second-order is undecidable** (Goldfarb, reduce H10) and **third-order is undecidable** (Huet, reduce
  modified Post Correspondence Problem). So undecidability bites *very low* — you do not need full higher order;
  **order ≥ 2 with function-valued unknowns already is undecidable.**
- **First-order unification IS decidable** (their Theorem 7.6; Robinson 1965, linear-time Martelli–Montanari /
  Paterson–Wegman). The decider: normalize, then a `decomp` rule that for `a sₘ =? a tₘ` with **rigid (constant)
  head** decomposes into `s₁=?t₁ … sₘ=?tₘ`, plus an **occurs check**; head-clash ⇒ no unifier. The whole difficulty
  of HOU is precisely the **flex head** (a *variable* in function position) — that is the gate from decidable to not.
- Methodological frame: **synthetic undecidability** — `P` is undecidable iff `dec P → dec Halt`. Undecidability is
  stated as *a reduction*, a function, not as a non-existence axiom (important for the Lean port below).

### B. The shape of a bounded solver (Vukmirović et al.) **[G]**
- The explosiveness lives in **flex-flex pairs** `F X =? G a` — infinitely many incomparable unifiers; even
  `X =? f X` (occurs) loops in naive procedures. So the practical answer is **not** "solve HOU"; it is:
- **Oracles for decidable fragments, checked per-subproblem.** Maintain a set of sub-fragments that admit a *finite*
  Complete Set of Unifiers (CSU): **first-order terms**, **(Miller) patterns** — flex heads applied only to *distinct
  bound variables* — **functions-as-constructors**, and a new "solid" fragment. When a subproblem falls in a fragment,
  call its oracle (which returns the finite CSU or a definite "no"); otherwise branch (imitate/project) generically.
- **The pragmatic variant = depth-bounded.** It "imposes limits on the number of bindings applied, counting locally
  per constraint" (functional projections, eliminations, imitations, identifications, and a global cap). "Due to limits
  on application of bindings, the pragmatic variant terminates." On hitting the limit it either emits a *trivial*
  flex-flex unifier or **fails / reports out-of-fragment** — i.e. it is honestly **incomplete but always-terminating**.
- The deep lesson: a real-world higher-order matcher is **(tractable oracles) ∪ (bounded generic search) ∪ (honest
  "I gave up")**. Exactly the architecture the synthesis wants for intent matching.

### C. Market clearing complexity (Lehmann/Müller/Sandholm) **[G]**
- **Winner Determination (WDP)**: given combinatorial bids `vᵢ(S)` over items `M`, pick a feasible allocation
  (each item ≤ once; ≤ one bundle per bidder for XOR) maximizing Σ value. This is the canonical *matching/clearing*
  problem behind auctions/exchanges.
- **WDP = weighted set packing ⇒ NP-complete** (Thm 3.1), and stays NP-complete under savage restriction: every bid
  value = 1, one bid per bidder, each item in exactly 2 bids; or bundles of size ≤ 3 (Thm 3.2); XOR with bundles of
  size ≤ 2 (Thm 3.3). Even **2 bidders with additive-bids-plus-budget is NP-hard** (Thm 3.4, reduce knapsack).
- **Inapproximable**: unless NP=ZPP, no poly-time algorithm approximates WDP within `min(l^{1-ε}, m^{1/2-ε})`
  (l = #bids, m = #items; Cor 4.2, from Håstad's max-clique). **No PTAS** unless P=NP (Cor 4.5).
- **But tractable special cases exist** (the whole point): items **linearly ordered + bids on contiguous intervals**
  → WDP_OR polynomial (interval structure); **bipartite matching** when bundles are single items / pairs; dynamic
  programming when #items is tiny; **2-approximation for submodular bids** (Thm 4.9, Lehmann et al.). VCG just calls
  WDP `n+1` times — the *mechanism* is a thin wrapper over the *clearing*.

---

## Takeaways for dregg (idea → move; map to synthesis §/code/Lean)

1. **The seam is real, and it is *lower* than "higher-order".** [G→C] The synthesis (§3.2) says "FIND a fill =
   undecidable in general (∃ predicate∩predicate)." Ground it precisely: matching is **existential unification**
   `∃X,Y. P_A(X,Y) ∧ P_B(X,Y)` with outputs threaded — i.e. a *system* of unification constraints (Spies/Forster's
   `SU`). Undecidability does **not** require exotic predicates; **second-order suffices** (Goldfarb). The honest claim
   for dregg is therefore *stronger* than the synthesis states: as soon as an intent predicate can quantify over a
   *function/relation-valued* unknown (e.g. "find a fill *strategy* g such that …"), matching is undecidable. The
   first-order/pattern boundary is the exact knife-edge.

2. **Keep VERIFY as the one universal gate; never let the registry host a *solver*.** [C] `cell/src/predicate.rs`
   `WitnessedPredicate` + `IntentPredicateVerifier` is *evaluation* of P against a *supplied* witness/proof — this is
   the decidable, cheap side (synthesis §3.1 "four gates → one `WitnessedCondition`"). The code is already disciplined:
   `intent/src/matcher.rs:302` `satisfies_spec` is **fail-closed** when `predicate_requirements` is non-empty ("a spec
   with predicate requirements cannot be honestly matched [without proofs]"); `solver.rs:167 validate_predicates`
   *verifies* a parallel slice of `(predicate, input, proof)` — it never *searches* for the witness. **Move: preserve
   this invariant as a typed law** — the matcher receives a *candidate fill* and only ever calls the verifier.

3. **`RingSolver` is the model of a *correct* bounded matcher — generalize its discipline, not its algorithm.** [C→F]
   `intent/src/solver.rs` is Johnson's elementary-circuits over *structural* compatibility (`asset==asset ∧ amount≥want`),
   `max_ring_size`-capped (`solver.rs:120`, floored at 2). That is exactly Vukmirović's **first-order/oracle fragment
   + a depth bound**: structural equality is first-order unification (decidable, occurs-check), the ring-size cap is the
   pragmatic depth limit. **Move [F]:** define a `Matcher` trait whose contract is *"bounded, sound, incomplete"* — it
   may return ∅ ("found nothing within budget") but every non-∅ result is a fill that the universal gate will accept.
   Order-books, periodic auctions (WDP), and swap-rings are *plugins*; the kernel ships none as "the matcher."

4. **What a matcher plugin can *honestly* promise, by class** [G]:
   - **First-order / structural-equality matching** (token swaps, asset==asset, amount thresholds): *decidable +
     poly* (often linear). Promise: completeness + termination. (Spies/Forster Thm 7.6; the `RingSolver` case.)
   - **Pattern (Miller) matching** — predicates over distinct-bound-variable holes: *decidable, finite CSU*. Promise:
     completeness within the fragment. (Vukmirović oracle set.)
   - **Combinatorial clearing / WDP** (bundle bids, multi-item exchange): *NP-hard, no PTAS, inapproximable past
     `m^{1/2-ε}`*. A plugin may **only** promise: optimal on *small* m (DP / branch-and-bound), *polynomial* on a
     declared tractable structure (interval/contiguous bids, single-item ⇒ bipartite matching), or a *bounded-factor*
     approximation **only** for the submodular sub-case (2-approx). It must **not** advertise a general efficient
     optimum. (Sandholm Thms 3.1–3.4, Cor 4.2/4.5, Thm 4.9.)
   - **Arbitrary-circuit / second-order+ predicates** (a `Custom { vk_hash }` whose satisfaction requires solving for a
     function-valued unknown): *undecidable to match*. A plugin may only do bounded search and **honestly time out**.

5. **Conservation prunes, it does not decide.** [G→C] The synthesis (§3.2) already says this; ground it: the linear
   resource law (`LinearityClass`; `intent/src/trustless.rs check_settlement_conservation`) is a *feasibility constraint
   on the allocation* — in WDP terms it is constraint (1)/(2) "each item allocated ≤ once," i.e. the very thing that
   makes WDP = set *packing*. Adding it **prunes** the search (a smaller feasible region) but the reductions in §C are
   *built from* packing/matching with conservation already in force — so conservation **cannot restore decidability**
   for the unification side and **does not lower** WDP below NP-hard for the clearing side. What it *does* buy:
   (a) it makes "verify a proposed allocation" trivially poly (check sums + no double-spend), strengthening the
   propose-then-verify asymmetry; (b) it can make special structures tractable (single-unit conservation ⇒ bipartite
   matching is poly). So: **conservation bounds and shapes; it never decides.**

6. **The architecture is "propose-then-verify": untrusted solver emits a checkable witness.** [G→F] This is the
   load-bearing move and the papers make it precise:
   - HOU/clearing are **in NP** for the *decision* form — "we can verify in polynomial time whether a particular
     [allocation/substitution] is feasible and its value" (Sandholm §3, the NP definition); the *certificate* is the
     fill itself. Finding is hard; **checking the certificate is poly.** That gap *is* dregg's seam.
   - So: **the matcher is an untrusted NP-witness producer.** It runs *outside* the trust boundary (any peer, any
     market service, an off-chain solver), under its own time/space budget, by whatever heuristic. It emits a proposed
     fill = `(participants, allocation, threaded outputs, predicate proofs)`. The **universal gate verifies it**:
     conservation check + `validate_predicates` (`solver.rs:167`) + canonical turn verify. **No matcher is trusted; a
     bad or adversarial matcher can only fail to find or propose an invalid fill, which verification rejects.** This
     mirrors Vukmirović's oracles (a fragment oracle is "untrusted" in that its output is re-checked by the same
     transition rules) and VCG-over-WDP (clear once, then *verify* per-bidder).
   - **Stated precisely [F]:** *Matching is sound-by-verification, not sound-by-construction.* The TCB contains the
     **verifier** (`WitnessedPredicate` evaluation + conservation), never the **solver**. Maps to synthesis §3.3 move
     #3 ("make `intent::fulfill` a thin shim over `submit_pending`+`resolve`, running conservation + the canonical
     verify") — that shim *is* the verify gate; the matcher feeds it.

---

## The decidability map (dregg predicate kind → matchable? / complexity)

| dregg predicate kind (where) | as a matching problem | decidable to MATCH? | complexity / honest promise | VERIFY |
|---|---|---|---|---|
| **Structural compat**: `asset==asset ∧ amount≥want` (`RingSolver`, `matcher::satisfies_spec` minus predicates) | first-order unification + threshold | **Yes** | poly/linear; complete + terminating | trivial |
| **Datalog caveats** (biscuit/macaroon engine, synthesis §3.1) over a *finite* fact base, no function symbols / safe rules | conjunctive query / Datalog satisfiability | **Yes** (decidable; data-complexity in P) | poly in DB; complete | poly logic-eval |
| **Datalog with unsafe rules / function symbols / recursion-through-arithmetic** | ≈ first-order logic / Prolog | **No** in general | bounded search + timeout | still poly to *check* a derivation |
| **Miller-pattern predicates** (holes = distinct bound vars) | pattern unification | **Yes** | decidable, finite CSU (oracle) | poly |
| **Combinatorial clearing**: bundle/multi-item intents, exchange `intent/src/exchange.rs` | Winner Determination (set packing) | decidable but **NP-hard**, **no PTAS**, inapprox past `m^{1/2-ε}` | optimal only for small m / interval / single-item(bipartite); 2-approx iff submodular | poly (check allocation: sums + ≤-once) |
| **STARK-witnessed predicate** `WitnessedPredicate{Custom{vk_hash}}` (`cell/src/predicate.rs`) — *first-order* statement, witness supplied | not a search; a *check* | **N/A to match** — it's a verify-only gate | the universal gate; cheap | the canonical cheap path |
| **Arbitrary-circuit / 2nd-order+ predicate**: "find a *function* g s.t. P_A(g)∧P_B(g)" | second/third-order unification | **No** (Goldfarb/Huet, machine-checked) | bounded search; must honestly time out | still poly to verify a *supplied* g |

**One-line reading:** everything to the *left* of "function-valued unknown" is matchable (and mostly poly); the moment
matching must *invent a function/relation* (2nd-order) it is **provably undecidable**; in between sits clearing, which is
decidable-but-NP-hard. **VERIFY is poly in every row.**

---

## Proposed Lean/metatheory artifacts (the verify/find split; an undecidability statement as a named target)

Maps onto synthesis §8 (the `./metatheory` Lean4 core) and the user's "honestly document: no general matcher exists."

1. **`Predicate` and the verify side (the universal gate).** [F] Model an intent predicate as
   `P : Fill → Prop` with a **decidable evaluator** `verify : (p : Predicate) → (f : Fill) → Bool` and a soundness
   lemma `verify p f = true ↔ P p f`. This *is* the `Predicate ⊣ Witness` adjunction's witness side (§1, §8.4):
   crossing a membrane needs the witness; `verify` consumes it. Cheap, total, in the TCB.

2. **`Match` as existential, with the explicit hole.** [F] An intent =
   `λ(f satisfying P). effects` (synthesis §3.2 "continuation with an ∃ hole"). Matching =
   `Match P_A P_B := ∃ f, verify P_A f ∧ verify P_B f ∧ ConservationOK f`. Two lemmas to state:
   - `verify_is_decidable : Decidable (P p f)` — *the gate is a decision procedure* (the easy, true direction).
   - `propose_then_verify : (∃ f, Match … f) ↔ ∃ f, (untrustedSolver _ = some f ∧ verify … f)` — i.e. *finding*
     factors through *any* candidate generator followed by the gate. This is the formal "matcher is untrusted."

3. **The named impossibility target (the honest "no general matcher").** [F, modeled on G]
   Following Spies/Forster's *synthetic* style — undecidability = a reduction, not an axiom — state:
   ```
   /-- There is no total, sound, complete matcher over expressive (≥ 2nd-order / function-valued-hole)
       predicates: a decider for `Match` over that class would decide Higher-Order Unification (hence Halt). -/
   theorem no_general_matcher
     (decideMatch : ∀ (P_A P_B : Predicate), Decidable (∃ f, Match P_A P_B f)) :
       Decidable HOU   -- ⟶ Decidable Halt, the contradiction
   ```
   This is **a reduction `HOU ⪯ GeneralMatch`** (mirror of Spies/Forster's `H10 ⪯ HOU` / `MPCP ⪯ U₃`), encoding intent
   predicates as λ-terms so that an existential match solves a unification system `SU`. We do **not** re-prove HOU
   undecidability in Lean (cite the Coq library result, or `axiom hou_undecidable`); we prove the *one* reduction that
   carries it onto dregg's `Match`. The deliverable is the **type signature as documentation**: the system *states in
   its core* that a general matcher cannot exist, and forces every concrete matcher to be a *bounded plugin* instead.

4. **The decidable counterpart (the positive law).** [F] Dually, prove
   `firstOrderMatch_decidable : Decidable (∃ f, Match P_A P_B f)` **when `P_A,P_B` are first-order / pattern** — i.e.
   `RingSolver`'s fragment is *certified* matchable. This pairs with #3: the seam becomes a *theorem about where the
   line is*, not a hand-wave. Differential-test the Rust `RingSolver` against this Lean oracle (synthesis §9 decision
   #1, the `dregg-dsl-differential` pattern).

5. **A `MatcherPlugin` contract lemma.** [F] `∀ result ∈ solver.matches(intents), verify_all result = true` — the
   only obligation a plugin carries is *soundness-by-verification*; **completeness and termination are explicitly
   NOT required** (the WDP/HOU results say they cannot be, in general). This is the type-level encoding of "bounded,
   pluggable, domain-specific" from synthesis §3.2 and the pluggable-finality analogy in §4.

*Caveat (honest scope):* per synthesis §8, Lean buys **semantic** coherence of this seam — it does **not** establish
that the STARK actually attests the morphism (separate crypto obligation). The `no_general_matcher` theorem is a claim
about the *search problem's* decidability, not about proof soundness; do not conflate.

---

## Open questions / what to read next

- **Datalog boundary, precisely.** I asserted plain Datalog matching is decidable (P data-complexity) but
  function-symbol/unsafe Datalog is not. dregg's biscuit/macaroon caveat language needs auditing against this line —
  *which* caveats are safe-Datalog? (Read `macaroons.pdf`, the biscuit Datalog spec; not in this batch.) This decides
  how much of the "Datalog engine" half of `WitnessedCondition` is *matchable* vs verify-only.
- **Is intent matching ever genuinely 2nd-order in dregg today, or always first-order-structural?** If the *current*
  `MatchSpec` only ever expresses first-order/threshold predicates, then today's matching is *decidable* and the
  undecidability is a **future-proofing** statement (forward design), not a present bug. Worth confirming against
  `intent/src/predicate.rs` + `generalized.rs` + `state_machine.rs`.
- **VCG / mechanism-design layer.** Sandholm notes WDP is also the engine of incentive-compatible pricing (VCG = solve
  WDP n+1 times). If dregg ever wants strategy-proof clearing, that's *another* poly-factor over an already NP-hard core
  — relevant to `exchange.rs`. Read Ausubel–Milgrom / the rest of the Combinatorial Auctions book.
- **Bounded-completeness guarantees.** Vukmirović's pragmatic variant is incomplete-but-terminating; is there a
  *certified* depth at which `RingSolver`/an auction plugin is *complete* for a declared structural fragment? That
  would let a plugin honestly promise completeness (not just soundness) on its declared domain — strengthens artifact #5.
- **Approximation honesty in code.** If an exchange plugin ships a 2-approx, the *type* should carry the factor and the
  submodularity precondition (Thm 4.9 only holds for submodular bids). How to encode "this matcher is a 2-approx **iff**
  bids are submodular" as a checkable plugin obligation? (Forward design.)
