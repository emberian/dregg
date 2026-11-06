# Alternating automata for policy conjunction — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned #guard or a run; [CLAIM] asserted elsewhere; [INFERRED] derived here.

Paths: `M` = `/Users/ember/dev/breadstuffs/metatheory/Dregg2`, `R` = `/Users/ember/dev/breadstuffs`.
Hub: §2 row "alternating automata (policy conjunction)", §3 row "product", §5 item 3.

**Status.** No AFA exists in `M`. The deployed conjunction shape is the product witness in
`M/Circuit/Emit/TinyAutomataLanesK.lean` (`k` lanes), and its sibling, the product-first route in
`TinyAutomataSatisfiable.lean`. Both are witnessed at `k = 1..4` [READ `TinyAutomataLanesK.lean:1-50`].

## 1. Semantics object (Lean)

Proposed. Transitions are positive Boolean formulas over states. Acceptance is evaluated backwards
from the end of the word. A run-DAG certificate is a sequence of obligation sets, one per position.

```lean
namespace Dregg2.Crypto.Alternating

inductive PBF (Q : Type) where
  | tt | ff
  | atom (q : Q)
  | and  (a b : PBF Q)
  | or   (a b : PBF Q)

def PBF.evalB (v : Q → Bool) : PBF Q → Bool
  | .tt => true | .ff => false
  | .atom q  => v q
  | .and a b => a.evalB v && b.evalB v
  | .or a b  => a.evalB v || b.evalB v

structure AFA (Q Sym : Type) where
  δ     : Q → Sym → PBF Q
  init  : PBF Q
  final : Q → Bool

def AFA.accFrom (A : AFA Q Sym) : List Sym → Q → Bool
  | [],      q => A.final q
  | a :: as, q => (A.δ q a).evalB (A.accFrom as)

def AFA.accepts (A : AFA Q Sym) (w : List Sym) : Bool := A.init.evalB (A.accFrom w)

/-- Run-DAG check: `Ss[i]` is the obligation set at position `i`; every obligation's formula is
satisfied by the next set, and the last set is final. -/
def AFA.dagChecks [DecidableEq Q] (A : AFA Q Sym) : List Sym → List (List Q) → Bool
  | [],      [S]           => S.all A.final
  | a :: as, S :: S' :: rest =>
      S.all (fun q => (A.δ q a).evalB (fun q' => decide (q' ∈ S'))) && A.dagChecks as (S' :: rest)
  | _,       _             => false

def AFA.dagAccepts [DecidableEq Q] (A : AFA Q Sym) (w : List Sym) (Ss : List (List Q)) : Bool :=
  match Ss with
  | S :: _ => A.init.evalB (fun q => decide (q ∈ S)) && A.dagChecks w Ss
  | []     => false

/-- Conjunction of two DFAs as an AFA on `Q₁ ⊕ Q₂`: `|Q₁| + |Q₂|` states, not `|Q₁|·|Q₂|`. -/
def AFA.conj (s₁ : Q₁ → Sym → Q₁) (q₁ : Q₁) (f₁ : Q₁ → Bool)
             (s₂ : Q₂ → Sym → Q₂) (q₂ : Q₂) (f₂ : Q₂ → Bool) : AFA (Q₁ ⊕ Q₂) Sym :=
  { δ     := fun q a => match q with
                        | .inl p => .atom (.inl (s₁ p a))
                        | .inr p => .atom (.inr (s₂ p a))
    init  := .and (.atom (.inl q₁)) (.atom (.inr q₂))
    final := fun q => match q with | .inl p => f₁ p | .inr p => f₂ p }

end Dregg2.Crypto.Alternating
```

## 2. Certificate shapes, side by side

1. **Lanes (deployed)**: one row per symbol; lane `i` carries `(CURRENT_i, NEXT_i)` and does one table
   lookup; all lanes read one shared `SYMBOL` column. Each lane declares its own RUN table (its
   traversed edges, `|w|` rows), not its transition table, because the deployed `exactPublicRows`
   table is unit-capacity and whole-graph tables hit the Eulerian obstruction [READ
   `TinyAutomataLanesK.lean:20-30`; census §1(b)4].
2. **Product-first (also witnessed)**: one state column carrying the mixed-radix packing of the `k`
   component states, one lookup into the product's run table (`|w|` rows) [READ
   `TinyAutomataCompose.lean` header, "WHAT SURVIVES"; MEASURED below].
3. **AFA run DAG (proposed)**: one row per `(position i, obligation q ∈ S_i)`. Each row picks a clause
   of `δ(q, a_i)` (positive formulas in DNF) and emits one demand `(i + 1, q')` per state in the
   clause. A multiset argument matches demands at `i + 1` against the rows at `i + 1` (each row
   provides with a multiplicity). Each row's `SYM` is looked up against the word by position. Public:
   `c` (the word), the AFA's clause table. Witness: the rows.

## 3. Arithmetization and counts

**Measured, lanes route** [MEASURED `TinyAutomataLanesK.lean:784-791`, `costOf (lanesRunIK k probeW)`,
`|probeW| = 8`]:

| k | traceWidth | constraints | tables | declaredRows |
|---|---|---|---|---|
| 1 | 3 | 4 | 1 | 8 |
| 2 | 5 | 8 | 2 | 16 |
| 3 | 7 | 12 | 3 | 24 |
| 4 | 9 | 16 | 4 | 32 |

So per symbol: `2k + 1` cells, `k` lookups, `4k` constraints.

**Measured, product-first vs lanes, area** [MEASURED `TinyAutomataLanesK.lean:796-797`]: over
`k = 1..4`, product-first `24, 24, 24, 24` against lanes `24, 40, 56, 72` (8 symbols). Product-first
is 3 cells and 1 lookup per symbol, flat in `k`, on run tables. Wire bytes `669, 669, 680, 685`
against `672, 1168, 1664, 2160` [MEASURED `:800-801`]. The whole-graph, reachability-minimized product
(which commits the automaton rather than the run) has area `12, 36, 72, 150` with NO witness for any
`k` [MEASURED `TinyAutomataSatisfiable.lean:988`]. Two caveats on the run-table routes: the run table
is in the descriptor, so the multiset of `(state, symbol, next)` triples is public; and the table's
validity against the automaton is checked outside the AIR.

**AFA run DAG, per obligation row** [INFERRED], with `w` the maximum clause width:
- columns: `POS, STATE, SYM, CLAUSE, MULT` + `w` demand columns = `5 + w`;
- lookups: 1 clause-table lookup `(STATE, SYM, CLAUSE, NEXT_1..NEXT_w)` + `w` demand sends + 1 provide
  (with multiplicity `MULT`) + 1 word lookup `(POS, SYM)` = `3 + w`;
- constraints: `(POS' − POS)·(POS' − POS − 1) = 0` (rows sorted by position, degree 2) + boundary
  pins on `POS₀ = 0` and the init formula's obligations at position 0 + final-state pins on the
  last position's rows. About 3 + pins;
- the word itself: `n` rows `(POS, SYM)` bound to `c` by the route chain.

Per symbol the DAG costs `(5 + w)·s̄` cells and `(3 + w)·s̄` lookups, where `s̄` is the average
obligation-set size `avg |S_i|`.

**The crossover** [INFERRED]. The DAG beats lanes iff `(5 + w)·s̄ < 2k + 1` in cells and
`(3 + w)·s̄ < k` in lookups.
- **Conjunction of `k` always-live DFAs** (the `TinyAutomataLanesK` workload): every conjunct holds
  exactly one obligation at every position, so `s̄ = k`, `w = 1`. The DAG costs `6k` cells and `4k`
  lookups against `2k + 1` and `k`. **It never wins, at any `k`.** At the milestone point `k = 3`:
  DAG 18 cells and 12 lookups per symbol; lanes 7 and 3; product-first 3 and 1.
- **Sparse obligations**, `s̄ = 1`, `w = 1`: the DAG wins in cells from `k ≥ 3` (`6 < 7`) and in
  lookups from `k > 4` (`4 < k`). **That is the only reading under which the hub's "the AFA DAG form
  only wins when `k > 4`" (§5 item 3) holds.**
- **Where sparsity is real**: policies with on-demand universal branching. "Every request of type `j`
  (`j < m`) is answered before the next request of type `j`" is `m` two-state DFAs in lanes
  (`2m + 1` cells per symbol), or an AFA with `m + 1` states: a watcher with
  `δ(watch, req_j) = watch ∧ pend_j`, so `w = 2` and `s̄ = 1 +` average pending. At `m = 16` with one
  request pending on average: DAG `7 · 2 = 14` cells and `5 · 2 = 10` lookups, against lanes 33 cells
  and 16 lookups.

Jirásková's `m + n` versus `m · n` is about state count, which here means TABLE size. Lanes already
keep component tables separate, so for a pure conjunction the AFA buys no table size over lanes. Its
real lever is policies whose DFA form is exponential (AFA to DFA can be doubly exponential [RECALLED,
Chandra-Kozen-Stockmeyer]), where lanes cannot even be written.

Commitment cost is unchanged by the choice: `⌈(⌈n/2⌉ + 4)/4⌉ + 1` permutations for an `n`-byte word,
e.g. 514 for `n = 4096`, at 352 cells each [INFERRED from `R/sel4/dregg-pd/executor-pd/crypto-floor/src/field.rs:94-112`,
`R/circuit/src/poseidon2.rs:410-435`; MEASURED 352 at `Poseidon2RoundGates.lean:121`]. At 180,928
cells for 4096 bytes, the gap between 7 and 18 cells per symbol (28,672 vs 73,728) is visible but
still below the hash.

## 4. Binding to the content commitment

- Lanes and product-first: the shared `SYMBOL` column is bound to `c` by the route chain (`+1`
  arity-2 chip lookup per row) or by shared sponge cells. Today the theorems read the word off the
  private `SYMBOL` column (as `tableRouting_refines_classify` does), so they are NOT BOUND to a content
  commitment [READ census §1(c)].
- DAG: rows are not one per symbol, so they cannot share a `SYMBOL` cell. Each row's `SYM` is bound
  by its `(POS, SYM)` lookup into the word trace, and the word trace is bound to `c`. That is one extra
  lookup per obligation row, already counted above.

## 5. Soundness statement (Lean syntax) and its vacuity falsifier

```lean
open Dregg2.Crypto.Dfa (ContentScheme)

/-- A checking DAG implies acceptance (positive formulas are monotone in the valuation). -/
theorem dag_sound [DecidableEq Q] (A : AFA Q Sym) (w : List Sym) (Ss : List (List Q))
    (h : A.dagAccepts w Ss = true) : A.accepts w = true

/-- The conjunction AFA accepts iff both components accept: one certificate, both policies. -/
theorem conj_accepts_iff (s₁ : Q₁ → Sym → Q₁) (q₁ : Q₁) (f₁ : Q₁ → Bool)
    (s₂ : Q₂ → Sym → Q₂) (q₂ : Q₂) (f₂ : Q₂ → Bool) (w : List Sym) :
    (AFA.conj s₁ q₁ f₁ s₂ q₂ f₂).accepts w = (f₁ (w.foldl s₁ q₁) && f₂ (w.foldl s₂ q₂))

structure AfaStatement (D : Type) where
  c : D

/-- Content-bound soundness: the word behind `c` satisfies EVERY conjunct. -/
theorem afa_dag_bound_sound [DecidableEq Q] [K : AfaKernel Q Sym D S A Proof] (hext : K.extractable)
    (st : AfaStatement D) (π : Proof) (hacc : K.verify st π = true) :
    ∃ w, S.commit w = st.c ∧ A.accepts w = true
```

(`AfaKernel.extract` delivers `w` and `Ss` with `S.commit w = st.c ∧ A.dagAccepts w Ss = true`; the
theorem is `extract` then `dag_sound`, the `DfaBoundVerifierKernel` pattern of
`M/Crypto/Dfa.lean:257`.)

**Falsifier** (a DAG that omits one conjunct's obligation). Policy 1: "no `b`" (symbols `0 = a`,
`1 = b`). Policy 2: "ends with `a`". The word `ba` violates policy 1 and satisfies policy 2:

```lean
def noB  : ℕ → ℕ → ℕ := fun q a => if a = 1 then 1 else q        -- 0 ok, 1 dead
def endA : ℕ → ℕ → ℕ := fun _ a => if a = 0 then 1 else 0        -- 1 = last symbol was a
def pol : AFA (ℕ ⊕ ℕ) ℕ := AFA.conj noB 0 (· == 0) endA 0 (· == 1)

/-- The weaker checker: reads the init conjunction as "some conjunct is present". -/
def PBF.evalAny (v : Q → Bool) : PBF Q → Bool
  | .tt => true | .ff => false | .atom q => v q
  | .and a b | .or a b => a.evalAny v || b.evalAny v

def dagAcceptsWeak (A : AFA (ℕ ⊕ ℕ) ℕ) (w : List ℕ) (Ss : List (List (ℕ ⊕ ℕ))) : Bool :=
  match Ss with
  | S :: _ => A.init.evalAny (fun q => decide (q ∈ S)) && A.dagChecks w Ss
  | []     => false

def omitting : List (List (ℕ ⊕ ℕ)) := [[.inr 0], [.inr 0], [.inr 1]]   -- policy 1's obligation dropped

example : pol.accepts [1, 0]                   = false := by decide
example : dagAcceptsWeak pol [1, 0] omitting   = true  := by decide   -- accepted: conjunct omitted
example : pol.dagAccepts [1, 0] omitting       = false := by decide   -- refused: `.inl 0 ∉ S₀`
```

The same omission at a row (dropping one demand of a clause `q' ∧ q''`) is caught the same way: the
clause lookup fixes all `w` demand columns, and the multiset argument forces every demand to be
provided at `i + 1`.

## 6. Composition behaviour

- **Conjunction (∧)**: the point of the family; `m + n` states, one certificate, no `bindAdv` term
  (one witness, hub §3 row "product").
- **Disjunction (∨)**: the prover picks one disjunct, so its rows exist only for the chosen branch.
  This is where the DAG beats a determinized product.
- **Complement**: dualize (swap `∧`/`∨`, `tt`/`ff`, complement `final`): `|Q|` states (Jirásková's
  `n` bound). The certificate for the dual is a DAG of the dual, not a missing DAG of the original.
- **Concatenation and star**: through the derivative/regex route (`02-derivatives.md`), compiled to an
  AFA instead of a DFA; not priced here.
- **Weld to commitment**: via the word trace, `+1` lookup per obligation row.
- **Fusion (U3)**: the DAG reads the output cells by position; it fuses without a second commitment.
- **ε-additivity**: one witness, so additive. It FAILS if conjuncts are proved as separate DAGs
  against one `c` without binding (L1's `bindAdv`), which is the `zkOracle_sound` shape (hub §3.1
  item 1).

## 7. Prior art

- Jirásková, *Operations on Boolean and Alternating Finite Automata*, AFL 2023, arXiv 2309.02748
  [READ in PRIOR-ART §9]: tight bounds; intersection `m + n` on AFA versus `m · n` for DFAs;
  complement `n`.
- Reef's Skipping Alternating Finite Automata (SAFA), ePrint 2023/1886 [READ in PRIOR-ART §9, snippet of
  the PDF]: alternation is already used in ZK regex proofs.
- Chistikov, Rino, *Intersecting Dense Automata*, arXiv 2605.20421 [READ in PRIOR-ART §9]: a
  certification scheme for NFA intersection emptiness.
- Stanford, Veanes, Bjørner, *Symbolic Boolean Derivatives*, PLDI 2021 [SNIPPET in PRIOR-ART §2]: unify
  derivatives with alternating and Boolean automata.
- Kozen, FOCS 1977 [RECALLED]: DFA intersection non-emptiness is PSPACE-complete.

Not claimed as ours: alternation in ZK (Reef), the state bounds (Jirásková).

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| lanes witness, `lanesKWit_satisfies` | `M/Circuit/Emit/TinyAutomataLanesK.lean:456` | L3 (emitted AIR + witness, `k = 1..4`) |
| product-first run-table route | `M/Circuit/Emit/TinyAutomataSatisfiable.lean:444` (`prodRunDesc`) | L3 |
| `PBF`, `AFA`, `dagChecks`, `AFA.conj` | proposed | none |
| `dag_sound`, `conj_accepts_iff`, `afa_dag_bound_sound` | proposed | L0 |
| DAG AIR (`5 + w` columns, `3 + w` lookups per obligation row) | proposed | none |

**Milestone**: a 3-policy conjunction at `k = 3` with pinned counts on all three routes: lanes
(existing, 7 cells and 3 lookups per symbol), product-first (3 and 1), and an emitted DAG descriptor
(predicted 18 and 12), plus the sparse watcher policy at `m = 16` where the DAG is predicted at 14 cells
per symbol against 33 for lanes. The `decide` falsifier above lands first, in
`M/Crypto/Alternating.lean`.
