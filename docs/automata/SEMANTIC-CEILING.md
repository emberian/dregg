# The semantic ceiling: what logics this certificate system can express and verify, and at what cost

2026-11-05. Tags: [READ] seen at file:line; [MEASURED] a pinned `#guard` or a run; [CLAIM] asserted
elsewhere, unchecked; [INFERRED] derived here. Hub: `AUTOMATA-ARITHMETIZATION-PROGRAM.md`.
Ember's question: *"can we express full Datalog or hella-symbolic SMT style things too..?"*

The short answer, before the ladder: **yes to positive and stratified Datalog as a certificate
with an exactness leg (positive landed today at L2); yes to SMT-shaped things as certificate
families, where the certificate is the solver's proof object (LRAT, e-graph explanation,
derivative bisimulation) and the circuit is its checker; the ceiling is not expressiveness but
the price of universal statements** ("no other fact", "no parse", "unsat"): every one of those is
a closure or a refutation, and closures cost an enumeration where memberships cost a path.

---

## 0. The unit of account

A certificate is a relation `R(x, w)` with `x ∋ c` (the content commitment). Its price has three
terms: (i) the commitment, `n/8` Poseidon2 permutations for `n` bytes at 352 committed cells each,
44 cells per byte [READ `circuit/src/poseidon2.rs:704`; `crypto-floor/src/field.rs:94`; MEASURED
`Poseidon2RoundGates.lean`]; (ii) the run, rows × columns and lookups per symbol; (iii) the
universal leg, if the statement has one: an enumeration (closure, rejection, unsat) priced in
lookups per candidate. A statement is "cheap" when (iii) is absent or sorted (one lookup per
candidate against a sorted table), "expensive" when it is a product over a domain.

The soundness error composes as `ε_run + bindAdv` for one statement and `ε₁ + ε₂ + bindAdv` for
two statements over one `c` (CERTIFICATES.md L1), `N·ε + bindAdv_MMR` over a corpus (L2); the
non-additive cases are in the hub §3.1.

---

## 1. Datalog

### 1.1 Positive Datalog: least-fixpoint certificates (landed at L2)

`Dregg2/Datalog/FixpointCert.lean` [READ]: statement `(program, root, pred, count)`; certificate =
EDB + semi-naive trace; verifier = root recompute (injective flattening) + replay with
active-domain substitutions + **closure by enumeration** + count. Theorems: `replay_sound`,
`closed_complete`, `verify_sound` (`db` is EXACTLY the derivable facts, duplicate-free, count
exact, root bound), `edb_bound_or_collides`, `count_unique_or_collides` (Count is a function of
`(program, root, pred)` or the sponge collides at the named `mrootFind` pair). Falsifiers as
kernel-evaluated `#guard`s: the open trace is refused at the honest count AND at the count of what
it derived — closure is the gate. 28 keystones kernel-clean.

Two certificate shapes compared:
- **Derivation-tree / DAG certificates** (Tantow et al., ITP 2025 [READ]; Soufflé provenance
  [READ]): certify `f ∈ lfp` for the listed facts. Cost: one tree per fact, `O(depth · |body|)`
  memberships. Soundness only: they cannot certify "and no others", so Count is "≥".
- **Trace certificates** (ours): the whole semi-naive log plus closure. Cost: all firings once
  plus `|P| · |dom|^{vars}` closure checks. Soundness AND completeness: Count is "=".

The `|dom|^{vars}` term is the ceiling. In-circuit it must be sorted, not enumerated by map-op
openings (hub note `13` §3): per rule, the candidate heads over `dom^{vars}` are compared against
the present facts of that predicate as two sorted lists, one lookup per candidate.

### 1.2 Stratified negation

A negated body atom `¬q(t)` is sound only against the CLOSED lower stratum: the certificate for
stratum `i` is the positive certificate for `P_i` with the extra leg "the negated facts are absent
in the final database of stratum `i−1`", which is a non-membership opening against that
database's sorted commitment (`opensTo … none`, `DescriptorIR2.opensTo_none_of_gap` [READ]) — one
gap opening per negated atom per firing. Stratification itself is a syntactic check on the
dependency graph (no cycle through negation), decidable, and part of `x`. This is the whole of
"full Datalog" minus aggregation; `dregg-query`'s CALM classifier already grades negation as
finalized-dependent [READ `classify.rs` header], which is exactly the statement "exact as of the
committed root".

### 1.3 Aggregation (Count, Sum, Min, Max) and CALM

Count landed. Sum/Min/Max over a closed predicate are the weighted-automaton accumulator (hub
`08`): one extra column and one degree-1 gate per fact in a sorted enumeration of the predicate.
CALM (Hellerstein-Alvaro [READ]) says the monotone fragment is coordination-free: for us, the
monotone fragment's certificates COMPOSE under MMR append (the delta's rounds extend the old
trace), while negation and aggregation re-run closure at the new root. That is the certificate
algebra's version of the theorem, and it is where `dregg-query`'s "no recursion" line moves:
recursion is monotone, so it belongs on the cheap side.

### 1.4 Datalog with order, arithmetic, and functions

Builtins (`<`, `+`) on the active domain are lookups (nibble range table, `2·⌈bits/4⌉` per
comparison) and gates; they keep the active-domain semantics only if range-restricted. Function
symbols (Datalog with constructors) break finiteness of the active domain; the certificate then
needs a depth bound, which is the `n+1` rounds bound of the trace: honest, but it is a bounded
fixpoint, not the least one.

---

## 2. SMT-shaped certificates

The pattern throughout: do not arithmetize the SOLVER, arithmetize the CHECKER of its proof object.
The certificate is the proof; the circuit checks it; soundness is the checker's.

| theory / object | certificate | per-step cost [INFERRED] | universal leg | prior art |
|---|---|---|---|---|
| propositional UNSAT | LRAT/DRAT: clause list + resolution chains (or RAT steps) | one chain step = `|clause|` lookups into the clause table + a pivot equality gate; normalized chains of fixed length `k` remove length leakage | none: a refutation IS the universal statement, by derivation of `⊥` | ZKUNSAT (2022/206) [READ]: resolution only; normalized chaining (2609.19353) [READ]: LRAT-style, fixed `k`; **no verified LRAT checker in this tree** (first milestone) |
| bit-vectors | bit-blast to CNF + LRAT, or theory lemmas as lookups (`a + b = c mod 2^w` is a lookup into a `2^{2w}` table only for tiny `w`; otherwise limb gates with `⌈w/4⌉` nibble lookups per operand) | per lemma: `3·⌈w/4⌉` lookups + 1 carry gate | as UNSAT | standard; the nibble table is `ByteTableEmit` (`HEIGHT = 16` [MEASURED]) |
| linear integer arithmetic | Farkas certificate: nonnegative multipliers `λ` with `λ·A = 0`, `λ·b < 0` | one inner product per row: `|A|` degree-2 gates, plus range lookups on `λ` | none | textbook; the certificate is a vector |
| equality + uninterpreted functions | e-graph explanation: a sequence of congruence/rewrite steps between two terms | one step = 2 lookups (the rule, the parent e-class) + 1 equality gate; extraction = one lookup per DAG node | none for `t₁ = t₂`; for `t₁ ≠ t₂` a disequality certificate needs a model, i.e. a universal leg over the e-graph | Ramos et al., AFP 2026 (verified egg-explanation checker, Isabelle) [READ]; Flatt et al. FMCAD 2022 [RECALLED] |
| regex equivalence | derivative bisimulation (Crepe) | one bisimulation pair per derivative pair; `|pairs| · |Σ-classes|` lookups | the bisimulation IS the universal statement, finite by `der_finite` [READ `Deriv/Finiteness.lean:347`] | Crepe (2504.01198) [READ]; Nipkow-Traytel [READ]; our `SymbolicEquivalence.predRE_equivalence_decidable` [READ] is the Lean decider, not yet a certificate |
| symbolic execution | a path = an automaton over constraint sets: one row per instruction with the path condition as a conjunction certificate; "no bug" = every path infeasible = UNSAT per path | per path: the program trace (as a VM proof) + one UNSAT certificate | the enumeration of paths, bounded by depth | Cheesecloth [SNIPPET] proves a bug exists (one path); absence of bugs needs the universal leg and is the expensive direction |

The honest reading: **membership-shaped SMT facts (this term equals that term, this formula is
unsat) are certificate families at the cost of their proof objects, with no new trust**; the
**model-shaped facts (this formula is SAT, these terms differ, this program has no bug) are the
universal legs and cost an enumeration or a model**. "Hella symbolic" is possible exactly where
the solver already emits a proof object.

---

## 3. The Chomsky and descriptive-complexity ladder, priced

| level | logic | automaton | certificate | per-symbol cost | universal leg (rejection / absence) | status |
|---|---|---|---|---|---|---|
| regular | MSO on strings | DFA (public or committed) | replay row | 3-11 cells + 1 lookup (+ 2 perms if hash-chained) | free: complement of a total DFA is a DFA (absence = padded complement, L3) | built, bound statement landed |
| regular, extended | MSO with Boolean closure | derivatives (`neg`, `inter`) | same | same, after a per-regex table compile | same | built (Lean), Rust unproved |
| regular, quantitative | weighted MSO | weighted/counting | row + accumulator | +1 column, +1 degree-1 gate | Count = 0 is L2∘L3 | proposed (`08`) |
| context-free, deterministic | — | VPA / LL(1) | stack replay | ≈2 rows, 2 chip per row (bracket circuit [MEASURED]) | `O(n)` for deterministic grammars (a validated parser rejects) | one finite-depth grammar built; general VPA decidable, no circuit |
| context-free, general | — | PDA | leftmost replay (membership) / CYK (rejection) | `O(n)` rows / `|R_bin|·(n³−n)/6` checks | CYK is the universal leg for arbitrary grammars | replay proved (Lean), Rust-native; CYK proposed |
| indexed / tree-adjoining | — | nested stacks | replay with a stack of stacks | `O(n)` rows with a depth-`d` stack column group | rejection: `O(n⁶)` (TAG parsing) | not proposed: no consumer |
| context-sensitive | — | LBA | bounded-tape trace: a VM trace of `O(n)` cells for `O(2^{cn})` steps | one VM row per step: this is "any polynomial verifier" below | rejection = exhaustion of the LBA's configuration space | expensive, trivially expressible |
| P (polynomial-time verifier) | FO(LFP) on ordered structures = P (Immerman-Vardi) | — | the VM trace of the verifier + MMR non-omission over its input | one VM row per step (the `Satisfied2` machinery) + `log N` per input opening; recursion folds the `N·ε` | none: the verifier's acceptance IS the statement | this is what MMR + `RecursiveAggregation` give "trivially but expensively": every PTIME check is a certificate at VM-row prices, with `ε_engine` undischarged [READ `RecursiveAggregation.lean:121`] |
| FO(LFP) = Datalog with negation and order | same | — | the Datalog certificate of §1 | firings + closure | closure | positive landed (L2); stratified proposed |
| NP | ∃SO | — | a witness + a P verifier | as P | — | the proof system itself |

Reading the ladder: the system expresses everything up to P natively (a VM trace is a certificate
of any polynomial-time verifier), so **expressiveness is not the ceiling**. The ceiling is the
cost gradient: regular things cost one lookup per symbol and have free complements; context-free
things cost `O(n)` for membership and an `O(n³)` fallback for rejection; fixpoint things cost
their closure; and everything above that costs VM rows. The design question is always whether a
statement can be pushed DOWN the ladder (a schema as a VPA rather than a tree automaton; a policy
as a DFA conjunction rather than a program) before it is arithmetized.

---

## 4. The "hella symbolic" question: claims about an unrevealed string

Can a certificate carry a symbolic claim — membership of a committed, unrevealed word in a
language — with zero knowledge?

- **What the shape is.** `R(x = (c, L), w)` with `w` the word: the DFA replay over `w` with `c =
  commit w` opened by position. The run is private (rows are witness cells); `x` reveals `L` and
  `c`. This is the Reef statement (2023/1886) [READ]: a committed document matches, or does not
  match, a public regex, in ZK, with skipping automata so that the cost is the number of symbols
  the automaton actually inspects, not `|w|`. ZK Email (2026/1284) [READ]: the same for an NFA path,
  linear in the path, with selective reveal of captures. Neither has complement in the regex
  syntax; Reef has non-match as a statement, ZK Email does not.
- **What we add.** (i) Machine-checked complement and intersection compilation
  (`derives_neg`, `correctness`, `der_finite`, `tableDfa_faithful` [READ `Deriv/`]), so "does not
  match `P` anywhere" is `neg (any* · P · any*)` by a proved law (L3), not by a second circuit.
  (ii) The bound statement with the record-or-collision disjunct
  (`dfa_bound_identifies_record_or_collides`), so the ZK claim is about THE committed record up
  to a named equivocation. (iii) Corpus-level absence composed with non-omission (L2∘L3,
  `MMR.server_cannot_omit_position` [READ `:780`]), which neither prior system has: "no record in
  this log matches `P`" as one statement.
- **What ZK costs here.** Hiding `w` costs nothing extra in the run (rows are already witness);
  it costs the commitment's hiding: salted leaves at pattern granularity or a hiding sponge
  (CERTIFICATES L6). The private position of a match (`OccursIn`) is free in a DFA run (the
  automaton finds it) and expensive as an opening (`O(|w|)`).
- **Symbolic in the other sense: claims about an UNKNOWN language.** "There exists a regex `r`
  in class `C` such that `w ∈ r`" is a statement with `r` in the witness: the table of `r` becomes
  witness cells (a committed automaton, the attested shape of hub `01`), bound by its 8-felt root.
  That is exactly the weld, and it is why the weld's lane-complete denotation (landed today) is a
  ZK enabler and not only a security fix: a hidden automaton certified against a public root is a
  symbolic claim about the policy, not the word.
- **Where the ceiling is.** Claims that quantify over all words (`L₁ ⊆ L₂`, equivalence) are
  certificates of the bisimulation kind (Crepe): their cost is the automaton size, not the word;
  they are available now via `SymbolicEquivalence` as a Lean decider and are a certificate family
  once the bisimulation is a trace. Claims that quantify over all languages are not statements.

---

## 5. Ranked: the five semantic extensions with the best richness per felt

Ranked by (new statements enabled) / (cells per statement), each with an evaluable milestone.

1. **Stratified negation for the Datalog certificate** (§1.2). Price: one gap opening
   (`opensTo … none`, 16 chip rows at depth 16 [MEASURED aux bill]) per negated atom per firing,
   on top of the positive certificate. Richness: closes "full Datalog" minus aggregates; makes
   "not revoked" certifiable with an exactness leg, which `dregg-query` cannot do today.
   Milestone: `FixpointCert` extended with strata; `#guard` on a 2-stratum revocation program
   (`active(X) :- issued(X), ¬revoked(X)`) with the forged-absence falsifier (a negated fact that
   IS present must be refused by the gap opening).
2. **Route-commitment column for every built replay family** (hub §5.1). Price: `+1` arity-2
   chip lookup per row (352 cells) or a once-per-word sponge opened by position (44 cells/byte).
   Richness: every "word read off the trace" theorem becomes a content-bound one — the whole
   regular level moves from statement-without-record to L0-compliant. Milestone:
   `tableRouting_refines_classify` restated with a `c` conjunct and the splice falsifier; wire delta
   `+25` felts per row [INFERRED from `CHIP_TUPLE_LEN = 25`].
3. **LRAT checking as a certificate family** (§2). Price: `|clause|` lookups + 1 gate per chain
   step; normalized to fixed `k`. Richness: every bit-vector / propositional fact the policy
   language can state (budget arithmetic, mutual exclusion of flags) becomes a certificate with no
   new trust. Milestone: a verified LRAT checker in Lean (none exists in the tree), `#guard` on a
   pigeonhole-3 refutation, then its AIR counts.
4. **Derivative-bisimulation certificates for language inclusion** (§4). Price: `|pairs| ·
   |Σ-classes|` lookups, independent of any word. Richness: "policy `P'` is at least as strict as
   `P`" as a statement — policy upgrades become certifiable. Milestone: `SymbolicEquivalence`'s
   decider emitting its bisimulation as a list, a checker `bisimOk`, `#guard` on
   `noDoubleBraceRE ⊆ star any`.
5. **Weighted accumulators for Sum/Min/Max and budgets** (§1.3, hub `08`). Price: +1 column,
   +1 degree-1 gate per fact. Richness: `audit::BudgetProof`'s arithmetic becomes a statement over
   an exact Count rather than over an unbound `CountProof`. Milestone: `seq_acc_is_fold` proved,
   the tampered-row falsifier, and `BudgetProof` restated over `FixpointCert.verify`.

Not ranked but named: detokenization for U3 (hub `06`; no consumer until an inference prover
exposes its output boundary), CYK rejection (fallback only), tree automata beyond the VPA core
(no schema needs it yet).
