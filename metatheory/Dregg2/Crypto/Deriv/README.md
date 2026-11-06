# `Deriv/`: symbolic derivatives over `Pred`

2026-11-06, lane C of the automata program. The semantics layer for the regex and predicate-automaton
families (`docs/automata/02-derivatives.md`, hub row "symbolic / predicate automata"). A `PredRE` is a
Boolean-closed regex whose symbols are dregg `Pred`s; its derivative table, compiled to a `TableDfa`, is
the DFA certificate's transition table. Every file except the two `RealGuardAudit` sweeps (Bool `#guard` verdicts only) ends in
`#assert_all_clean` (kernel axioms only).

## Gate

```
cd metatheory
scripts/automata-check.sh                                   # the program gate (5 of these files)
scripts/automata-check.sh --files "$(ls Dregg2/Crypto/Deriv/*.lean | tr '\n' ,)"   # all of them
```

[MEASURED, Mac M2 Max, -j 4, 2026-11-06] all 34 files green, 315 `#guard`s, 389 kernel-clean
keystones, 76.3 s wall. The script is `metatheory/scripts/automata-check.sh`; `docs/automata/BUILD.md` has
both machines' commands.

Keystone column: **yes** marks the five files on the program gate list and the table bridge they feed
(`tableDfa_faithful`); the counts are what the gate reports for each file.

## Semantics and correctness

| file | what it proves | gate keystone | `#guard`s | kernel-clean pins |
|---|---|---|---:|---:|
| `Core.lean` | `PredRE` (regex over `Pred`: `ε, sym φ, alt, inter, cat, star, neg`), `null`, the derivative `der`, the matcher `derives` | **yes** | 24 | 11 |
| `Correctness.lean` | `correctness : derives w R = true ↔ Matches w R`, constructor by constructor (`derives_neg`, `derives_star_*`) | **yes** | 0 | 13 |

## Finiteness up to similarity (Brzozowski, after ITP'25 `finiteness-derivatives`)

| file | what it proves | gate keystone | `#guard`s | kernel-clean pins |
|---|---|---|---:|---:|
| `Similarity.lean` | the ACI similarity `≅` on `alt`; `sim_sound`, `sim_derives`: derivatives are finite only up to `≅` |  | 6 | 7 |
| `AciNormal.lean` | a computable one-sided equality test `predBEq`/`reEq` (never `true` on distinct terms) |  | 37 | 14 |
| `AciComplete.lean` | completeness of the ACI decision on the rigid fragment; `simDecide` |  | 40 | 55 |
| `Combinatorics.lean` | regex-free list combinatorics (`subset_up_to`, `neSublists`) under the finiteness tower |  | 0 | 6 |
| `Pieces.lean` | `pieces R`: the finite over-approximation of reachable derivative states |  | 0 | 2 |
| `Permute.lean` | `toSum`, `neSubsets`: collecting `pieces` into finitely many `alt`-sums |  | 0 | 6 |
| `Monotone.lean` | the multi-step chain `steps r n ⊆[≅] ⊕(pieces r)` (classical `DecidableEq PredRE`, existential count only) |  | 0 | 4 |
| `Finite.lean` | one symbolic step stays `≅` inside `pieces` |  | 0 | 2 |
| `TTerm.lean` | transition terms: the alphabet-independent symbolic derivative |  | 0 | 5 |
| `SymbolicDerivative.lean` | the symbolic `step` (every frame at once), `step_neg`, `step_star`, `step_alt` |  | 0 | 5 |
| `Finiteness.lean` | `der_finite`: the whole symbolic state space reachable from `r` is finite up to `≅` | **yes** | 0 | 5 |
| `StepBridge.lean` | `der a r ∈ step r`: concrete derivatives land in the symbolic step, so `der_finite` bounds them |  | 6 | 6 |

## Determinization and the flat table

| file | what it proves | gate keystone | `#guard`s | kernel-clean pins |
|---|---|---|---:|---:|
| `Determinize.lean` | the derivative automaton (states `PredRE`, transition `der`, accept `null`); `derivativeDfa_correct` |  | 0 | 5 |
| `Powerset.lean` | `LangEquiv`, and `determinizer_faithful` for any derivative determinizer |  | 0 | 6 |
| `TableDfa.lean` | `TableDfa`, the flat table the Rust `compiler.rs::Dfa` runs; `tableDfa_faithful` (with its agreement premise) | **yes** | 0 | 5 |
| `Thompson.lean` | mathlib `DFA` → `TableDfa`; `thompson_recognizes`, `legacy_determinized_faithful_thompson` (the Thompson/subset path) | **yes** | 0 | 9 |

## Symbolic decisions (emptiness, equivalence) over guard predicates

| file | what it proves | gate keystone | `#guard`s | kernel-clean pins |
|---|---|---|---:|---:|
| `PredicateLibrary.lean` | builder combinators over `Pred` (`pAnd`, `pOr`, `pNot`) with their evaluation lemmas |  | 16 | 15 |
| `SatOracle.lean` | the deployed guard leaf algebra `{braceP}`: both minterms decided. Not imported by any module; checked standalone |  | 0 | 7 |
| `SymbolicMinterms.lean` | minterm covers over a leaf list: emptiness and equivalence for arbitrary decidable-leaf guards |  | 10 | 32 |
| `SymbolicMintermsPlus.lean` | more leaf classes (`allOf`/`anyOf`, `symMemberOf`, `digFieldEq`); `IsSymbolic → RigidFull` |  | 10 | 21 |
| `SymbolicIntervals.lean` | interval atoms: thresholds, two-sided ranges, scalar enums in the minterm tower |  | 9 | 25 |
| `SymbolicAffine.lean` | `allowedTransitions` state-machine guards (exact) and bounded-domain affine guards |  | 13 | 26 |
| `SymbolicDifference.lean` | difference-bound (DBM) guards: an executable negative-cycle check behind `MintermCover` |  | 16 | 15 |
| `SymbolicEmptiness.lean` | bounded nonemptiness `∃ w, w.length ≤ n ∧ derives w R`; `reachableWithin_sound` |  | 9 | 15 |
| `SymbolicEmptinessUnbounded.lean` | pigeonhole excision: deleting a `≅`-loop preserves the verdict, so emptiness is `n`-free |  | 4 | 9 |
| `SymbolicDecision.lean` | `predRE_emptiness_decidable`: the `n`-free emptiness decision as a type |  | 3 | 5 |
| `SymbolicEquivalence.lean` | `symDiff`, `langEq_iff_symDiff_empty`: language equivalence via emptiness of the symmetric difference | **yes** | 2 | 7 |
| `SymbolicFixpoint.lean` | the runnable worklist fixpoint (`reachFix`, `emptyFix`) over `simDecide`; rigidity is root-only |  | 13 | 15 |
| `EquivalenceFixpoint.lean` | the `≅`-fixpoint composed onto `symDiff`: runnable equivalence (`role3_not_equiv_role4`) |  | 12 | 5 |

## Real-guard audits

| file | what it proves | gate keystone | `#guard`s | kernel-clean pins |
|---|---|---|---:|---:|
| `RealGuardAudit.lean` | 24 real dregg guards (each cited file:line) classified by fragment; `#guard` verdicts only |  | 43 | 0 |
| `RealGuardAudit2.lean` | the reactive guards (`WriteOnce`) moved into the DBM fragment; `#guard` verdicts only |  | 35 | 0 |
| `RealGuardDecisionLift.lean` | the swept guards' Bool verdicts lifted to `Prop` (`rfl`s) on the interval and correlated-witness covers |  | 7 | 26 |

## What is not here

- The Rust compiler (`dfa::compiler::Re::compile`) is not proved against `determinizer_faithful`;
  `tableDfa_faithful` takes the table's agreement with `derives` as a premise. A conformance corpus is
  regression evidence for that premise, not a discharge of it.
- `SatOracle.lean` is not imported by any module (its header says so); the gate checks it standalone.
- Pinned counts for the circuit side of these families live in `docs/automata/COUNTS.md`.
