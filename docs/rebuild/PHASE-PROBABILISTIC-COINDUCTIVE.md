# PHASE — the probabilistic / coinductive frontier (the deep residual)

> 2026-05-30. After four autonomous waves drove the metatheory to 3 by-design sorries with every
> finite/constructive distributed+crypto problem proved-or-bounded, the GENUINE remaining research
> collapsed to three problems that are all **probabilistic or coinductive** — a qualitatively
> different class. This doc records the infrastructure inventory (Kagi-researched + local-mathlib
> verified) and the build/transport strategy.

## The three deep problems
1. **Coinductive unbounded-interleaving cross-cell adversary** — `Proof/ContendedCrossCell.lean`
   proved the *finite* contention dichotomy (I-confluent ⇒ schedule-agnostic commit; coupled ⇒ `¬∃`
   schedule-agnostic commit). The lift: an *infinite* adversarial schedule of overlapping turns, where
   the safe-fragment result becomes **confluence-up-to-bisimulation over the `Boundary` νF coalgebra**.
2. **Randomized synchronizer construction** — `Proof/BFTLiveness.lean` proved the GST round obtains
   *given* a `Pacemaker` synchronizer (ELRS Def 3.1). The residual: *construct* the synchronizer —
   the randomized `Relay(r,k)` leader rotation, proving expected-O(1)-views-to-an-honest-leader over
   `World.rand` (ELRS §5).
3. **Dynamic UC composition** — `Metatheory/EpistemicConsensus.lean` proved a UC *static* fragment;
   the full Canetti composition theorem needs probabilistic execution + computational
   indistinguishability (environment/simulator quantification).

## Infrastructure inventory (what exists, where)
**In-Lean already (no new dependency):**
- **Probability** — mathlib `Probability/ProbabilityMassFunction` (PMF), `Kernel` (Giry), `Martingale`,
  `ConditionalExpectation`, `Independence`, `Moments`, `Distributions/*`. Covers problem (2)'s
  expected-value / geometric-leader argument.
- **Coinduction** — mathlib `Data/QPF/*` + `Data/PFunctor/*/M` (codata, `Cofix`, bisimulation) AND
  **Lean 4.25+ native coinductive-predicate support** (we are on 4.30). Covers problem (1)'s base.

**Available as deps if the native infra proves insufficient (verify Lean-4.30/mathlib-rev compat in an
isolated worktree BEFORE adding to the lakefile — a fresh worktree rebuilds mathlib, so dep-compat
testing is the one place worktree isolation earns its cost):**
- **Paco for Lean 4** (`hxrts.com/paco-lean/`) — parametrized coinduction + up-to/closure operators (Coq Paco analog).
- **CSLib** (arXiv 2602.15078) — bisimulation-up-to + LTS/weak-bisimulation infrastructure.
- **iris-lean** (`leanprover-community/iris-lean`) — `IProp`/UPred/MoSeL/invariants/later-credits; a
  functional step-indexed foundation (not yet Coq parity).

**For UC specifically — NO proof transport exists** (EasyCrypt/CryptHOL/SSProve vs Lean = different
foundational logics, different probability models). Two honest options:
1. **Restate-with-cross-system-trust-assumption** — do the UC/game-based proof in the purpose-built
   tool (EasyCrypt = industry standard PRHL; SSProve = Coq modular; CryptHOL = Isabelle), and state
   the result in Lean as a named `Prop` carrier with an explicit cross-system-trust caveat. **This is
   exactly the §8-boundary philosophy** (crypto soundness is already a `Prop` carrier discharged by
   circuits; the UC theorem becomes a `Prop` carrier discharged by EasyCrypt) — clean and honest *if
   labeled as such*. The trust argument widens to include the foreign prover's kernel.
2. **Native re-formalization in Lean** — CatCrypt (eprint 2026/604) shows game-based crypto security
   *can* be done natively in Lean 4 now. Higher cost, no trust widening. The long-run ideal.

## The strategy
- **Problems (1) and (2): build IN-LEAN, no new deps** — native coinduction + mathlib QPF/PMF. Attempt
  the tractable fragment; only investigate Paco-Lean/CSLib deps (worktree-tested) if the native infra
  genuinely blocks the up-to enhancement.
- **Problem (3) UC: defer + carrier** — no current OPEN strictly requires full dynamic UC (it's a
  whole-node-UC-realization nice-to-have). When wanted, restate-with-trust-caveat (option 1) is the
  pragmatic move; native Lean UC (option 2, CatCrypt-style) is the long-run ideal. Do not build now.
- **Dependency discipline:** the needed infra is already present; do NOT add deps speculatively
  (version-compat risk against pinned Lean 4.30 + the mathlib rev). If a dep is needed, test it in an
  isolated git worktree first (the one place worktree isolation is worth the mathlib rebuild).
