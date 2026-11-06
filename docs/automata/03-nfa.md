# Nondeterministic finite automata — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned #guard or a run; [CLAIM] asserted elsewhere; [INFERRED] derived here.

Hub: `AUTOMATA-ARITHMETIZATION-PROGRAM.md` §2 row "NFA". M = `/Users/ember/dev/breadstuffs/metatheory/Dregg2`,
ML = `/Users/ember/dev/breadstuffs/metatheory/.lake/packages/mathlib/Mathlib/Computability`.

An NFA has three certificate shapes and they certify different things. (a) Determinize offline and
run the DFA: certifies membership and non-membership, and pays in table size. (b) Carry the subset
of live states per row: also both polarities, and it pays in columns. (c) Supply one accepting path
(ZK Email): membership only, and it is the cheapest. The note's main point is the polarity table in
§5: a path certifies `w ∈ L`, and nothing about `w ∉ L`.

## 1. Semantics object (Lean)

mathlib, verbatim [READ]:

```lean
-- ML/NFA.lean:55
structure NFA (α : Type u) (σ : Type v) where
  step : σ → α → Set σ
  start : Set σ
  accept : Set σ

-- ML/EpsilonNFA.lean:39
structure εNFA (α : Type u) (σ : Type v) where
  step : σ → Option α → Set σ
  start : Set σ
  accept : Set σ

-- ML/NFA.lean:280
inductive Path : σ → σ → List α → Type (max u v)
  | nil (s : σ) : Path s s []
  | cons (t s u : σ) (a : α) (x : List α) :
      t ∈ M.step s a → Path t u x → Path s u (a :: x)

-- ML/NFA.lean:309
theorem accepts_iff_exists_path {x : List α} :
    x ∈ M.accepts ↔ ∃ s ∈ M.start, ∃ t ∈ M.accept, Nonempty (M.Path s t x)

-- ML/NFA.lean:317, :323
def toDFA : DFA α (Set σ) where
  step := M.stepSet
  start := M.start
  accept := { S | ∃ s ∈ S, s ∈ M.accept }
theorem toDFA_correct : M.toDFA.accepts = M.accepts

-- ML/EpsilonNFA.lean:278
theorem toNFA_correct : M.toNFA.accepts = M.accepts
```

The tree's Thompson construction, `M/Crypto/Deriv/Thompson.lean` [READ]:

```lean
-- :338
def thompson (R : PredRE) : εNFA Value (TState R) where
  step := tStep R
  start := {tStart R}
  accept := {tAccept R}

-- :118
def determinizedTable {σ : Type} (M : εNFA Value σ) : TableDfa (Set σ) Value :=
  ofDFA M.toNFA.toDFA

-- :751
theorem thompson_recognizes (R : PredRE) (h : IsThompson R) :
    ThompsonRecognizes (thompson R) R

-- :760
theorem legacy_determinized_faithful_thompson (R : PredRE) (h : IsThompson R) (w : List Value) :
    (determinizedTable (thompson R)).accepts w ↔ Matches w R
```

`IsThompson` (:725) excludes `inter` and `neg`; those go through the derivative determinizer (`02`).
`TState` (:278) gives `|TState ε| = |TState (sym φ)| = 2`, `|TState (alt l r)| = 2 + |l| + |r|`,
`|TState (cat l r)| = |l| + |r|`, `|TState (star r)| = 2 + |r|`. So a Thompson NFA has at most
`2·size(R)` states [INFERRED from the definition].

Two caveats on (a). `determinizedTable` has state type `Set σ`, which is not computable, so it is a
semantic object and not an executable table. The docstring at :112-117 says the deployed integer state
IDs are "a bijective relabeling, immaterial". That sentence is a [CLAIM]: no theorem relates
`compiler.rs::Nfa::determinize`'s integer table to `M.toNFA.toDFA`.

## 2. Certificate shape

Word `w = a₁…aₙ`, content commitment `c` of `w` (bytes; `hash_bytes_8`). Public `x` always contains `c`.

| route | public `x` | witness | row `i` holds |
|---|---|---|---|
| (a) determinization certificate | `c`, the determinized table `T : Q_D × Σ → Q_D` (or its commitment), accept bits | `w` | `(d_{i-1}, a_i, d_i)`, with `T(d_{i-1}, a_i) = d_i` |
| (b) on-the-fly subset witness | `c`, the NFA edge list `δ ⊆ Q × Σ × Q` (ε-free), `start`, `accept` | `w`, the sets `S_0 … S_n ⊆ Q` | `a_i` and `|Q|` bit columns for `S_i` |
| (c) path certificate (ZK Email, ePrint 2026/1284) | `c`, `δ`, `q₀`, `F`, optionally capture outputs | `w` (or the span), the path `p_0 … p_k` | `(p_{i-1}, a_i, p_i)` with the edge in `δ` |

For (a) the table is checked once against the NFA, offline: in Lean by
`legacy_determinized_faithful_thompson` for the Thompson fragment, modulo the relabeling [CLAIM] above.

For (b) the per-row check has two halves, and which half is enforced decides the polarity:

- **upper closure** `δ(S_{i-1}, a_i) ⊆ S_i`: for each edge `(q, a, q')`, `S_{i-1}[q] · [a_i = a] · (1 − S_i[q']) = 0`;
- **lower support** `S_i ⊆ δ(S_{i-1}, a_i)`: each `q' ∈ S_i` has a predecessor; one witness column per state.

For (c) ZK Email's relation, per CERTIFICATES §6 [READ, the PDF]: `p₀ = q₀ ∧ p_k ∈ F ∧ ∀i (p_{i−1}, a_i, p_i) ∈ δ ∧ c_i = Cap(a_i, p_{i−1})`,
over an ε-free NFA. The path covers the matched span only, so prover cost is linear in the captured span
and independent of the document's length.

## 3. Arithmetization and counts

Per symbol, byte alphabet, `|Q|` NFA states, `|δ|` symbolic edges (edge label = a byte class), `k`
minterm classes. Pinned shapes where a descriptor exists:

| route | rows / symbol | columns | lookups / symbol | gates / symbol (max degree) | table rows | perms / symbol |
|---|---|---|---|---|---|---|
| (a) | 1 | 3 [MEASURED `DfaRoutingTableEmit` `TRT_WIDTH = 3`] | 1 (arity 3) | 4 constraints total [MEASURED] (2) | `|Q_D|·256`, `|Q_D| ≤ 2^|Q|` | 0 |
| (b) | 1 | `|Q| + k + 1` [INFERRED] | 1 (byte → one-hot class, 256 rows) | `|Q|` booleanity (2) + `|δ|` closure (3) [INFERRED] | 256 | 0 |
| (c) | 1 per span symbol | 3 [INFERRED, same row shape as (a)] | 1 (arity 3, into `δ` expanded per byte) or 2 (class lookup + `(p, class, p')`) | 0 beyond the lookup | `|δ_bytes|` or `256 + |δ|` | 0 |

Arithmetic for the comparison, on two regexes:

1. **Padded literal**, `any* · P · any*` with `|P| = 32` bytes. The ε-free NFA has `33` states and
   `32` literal edges plus one `any` self-loop at each end; the DFA (the KMP automaton) also has `33`
   states [INFERRED, standard]. (a): one lookup per byte into `33 · 256 = 8,448` table rows. (b):
   `33 + k + 1` columns with `k = 33` classes at most (each distinct byte of `P`, plus "other";
   ≤ 33), so ≤ 67 columns, and `33 + 34 = 67` gates per byte [INFERRED]. (c): `33` edges, but a path
   through `any*` loops costs one row per byte of the whole document, so (c) has no span advantage on
   a padded pattern. Here (a) wins: 3 columns against ~67.
2. **The determinization blow-up**, `(a|b)* a (a|b)^m` at `m = 20`. NFA: `m + 2 = 22` states and
   about `2(m+2)` edges; minimal DFA: `2^(m+1) = 2,097,152` states [INFERRED, standard]. (a): table
   `2^21 · 2 = 4,194,304` rows. Any lookup argument's table side has at least that many rows, so for
   words shorter than 4M symbols the table dominates the trace. (b): `22 + 2 + 1 = 25` columns,
   `22 + 44 = 66` gates per symbol, and a 2-row class table. (c): 3 columns, one lookup into a
   `~44`-row edge table. Here (b) and (c) win by five orders of magnitude in table size.

**Commitment cost:** `n/8` permutations for `n` bytes = 44 committed cells per byte at the 352-cell
permutation [READ `circuit/src/poseidon2.rs:704`, `crypto-floor/src/field.rs:94`; MEASURED
`POSEIDON2_AUX_COLS == 352`]. Against it: (a) and (c) rows are 3 cells, ~15× cheaper than the hash; (b) at
`|Q| = 22` is 25 cells, still under 44, and (b) crosses the hash cost at `|Q| + k + 1 > 44`
[INFERRED]. So the hub's law ("the automaton is free, the commitment is the bill") holds for (b) only
up to about 40 NFA states.

The span lever of (c) does not survive our commitment. ZK Email hashes a Merkle-Damgård SHA-256 and
reveals the compression state after the prefix ("partial precomputation"). The analogue for a sponge
`c` is to reveal the sponge state at the span start and absorb in-circuit from there to the end, so
(c) pays `(n − i)/8` permutations, not `|span|/8` [INFERRED]. Paying only `|span|/8` needs a
position-openable content scheme (a Merkle tree over leaves, CERTIFICATES L6), not a sponge.

The table-routing descriptor's `exactPublicRows` is a unit-capacity LogUp receive, so a word that
uses one transition twice has no witness unless the declared multiset matches its usage (the census's
"Eulerian obstruction" [READ census]). (a) and (c) both inherit this; (b) has no data-dependent table
and does not.

## 4. Binding to the content commitment

None of the three is bound in the tree today. (a) inherits `01-dfa.md`: the abstract
`BoundStatement`/`dfa_bound_verify_sound` (`Dfa.lean:249, 273`) binds, and the table-routing refinement
`tableRouting_refines_classify` (`DfaRoutingTableEmit.lean:438`) reads the word off the private SYMBOL
column [READ census]. (b) and (c) have no circuit. For all three the binding is the same added leg:
the SYMBOL column must be the word `c` commits. Either a route-commitment column (`+1` arity-2 chip
lookup per row, hub §2.1) or an in-circuit sponge over the SYMBOL column (`n/8` perms).

For (c) the statement must bind the span position as well as the bytes: if `i` is hidden, the
statement is `OccursIn`/`MatchesAt` with an existential `i` (CERTIFICATES §1). That is fine for
membership. It is not a statement about a particular field unless `i` is pinned by a structural
certificate (a parse, `05`).

## 5. Soundness statement (Lean syntax) and its vacuity falsifier

The three routes certify different relations. Proposed:

```lean
variable {σ D : Type} [Fintype σ] [DecidableEq σ] (S : ContentScheme UInt8 D)

/-- (c) the path certificate: MEMBERSHIP only. Its soundness is mathlib's
    `NFA.accepts_iff_exists_path` (NFA.lean:309) plus the content leg. -/
structure PathCert (M : NFA UInt8 σ) where
  word : List UInt8
  s t  : σ
  hs   : s ∈ M.start
  ht   : t ∈ M.accept
  path : M.Path s t word

theorem pathCert_bound_sound (M : NFA UInt8 σ) (c : D) (π : PathCert M)
    (hc : S.commit π.word = c) :
    ∃ w, S.commit w = c ∧ w ∈ M.accepts :=
  ⟨π.word, hc, NFA.accepts_iff_exists_path.mpr ⟨π.s, π.hs, π.t, π.ht, ⟨π.path⟩⟩⟩

/-- (b) the subset witness with UPPER closure: NON-MEMBERSHIP. -/
structure SubsetCert (M : NFA UInt8 σ) where
  word : List UInt8
  sets : List (Finset σ)                  -- S_0 … S_n
  hlen : sets.length = word.length + 1
  h0   : ∀ q ∈ M.start, q ∈ sets[0]!
  hup  : ∀ i (hi : i < word.length), ∀ q ∈ sets[i]!, ∀ q' ∈ M.step q (word[i]'hi), q' ∈ sets[i+1]!
  hrej : ∀ q ∈ sets[word.length]!, q ∉ M.accept

theorem subsetCert_bound_rejects (M : NFA UInt8 σ) (c : D) (π : SubsetCert M)
    (hc : S.commit π.word = c) :
    ∃ w, S.commit w = c ∧ w ∉ M.accepts
```

`subsetCert_bound_rejects` holds because `hup` makes each `S_i` a superset of `M.evalFrom M.start (w.take i)`
(induction on `i`), and `hrej` then leaves no accepting state reachable. Note what each certificate
does **not** need: (c) needs no closure, and (b)-for-rejection needs no lower support. (b) with both
halves is the determinized run, exact in both polarities. These statements meet L0: `c` and `w` are
in the conclusion. The kernel-level form (extract `π` from an accepted proof) wraps them exactly as
`dfa_bound_verify_sound` wraps `dfa_sound`.

**Falsifier 1 (a path is not a non-membership certificate).** Take `M` for `(a|b)* a` with
states `{0, 1}`, `0 →a 0`, `0 →b 0`, `0 →a 1`, `start = {0}`, `accept = {1}`, and the word `w = [a]`.
The path `0 →a 0` ends in a non-accepting state. A verifier that reads "the path ends outside `F`"
as `w ∉ L` accepts it, but `w ∈ M.accepts` through `0 →a 1`. In Lean:
`∃ (π : M.Path 0 0 [a]), 0 ∉ M.accept ∧ [a] ∈ M.accepts`, discharged by `decide` on a `Fin 2` encoding.
The same word refutes a `SubsetCert` built with lower support only (`S_1 = {0}`): it fails `hup`
because `1 ∈ M.step 0 a` and `1 ∉ S_1`.

**Falsifier 2 (ambiguity: "the path" is "a path").** Membership survives ambiguity, by
`accepts_iff_exists_path`. Capture output does not. Take `(a*)(a*)` with group 1 captured, and `w = aa`.
The paths assign group 1 to `""`, `"a"` or `"aa"`, and all three satisfy ZK Email's `R_regex`. A
statement "the captured field is `x`" therefore means "some accepting parse captures `x`". It means
"the leftmost-greedy capture is `x`" only for an unambiguous NFA, or when the relation forces the
canonical path (for example the lexicographically least one, which needs a per-row order check). The
hub's row says the path must be "*the* path only for unambiguous NFAs". The precise reading is that
membership needs no uniqueness, and capture semantics does.

## 6. Composition behaviour

| operator | (a) | (b) | (c) |
|---|---|---|---|
| product / intersection | `k`-lane product of DFAs (hub §3) | `S_i ⊆ Q₁ ⊎ Q₂`: columns add, `|Q₁| + |Q₂|` | two paths, one per automaton, sharing the SYMBOL column: `+1` lookup per row |
| union | determinize the union | free: union of NFAs is an NFA | free |
| complement | swap accept bits (total table) | **upper-closure subset certificate** | **none**: a path certificate cannot express `w ∉ L` |
| concatenation, star | via the NFA, then determinize | NFA constructions, ε-closure precomputed | free (one split position) |
| weld to `c` | as DFA | `+1` chip lookup per row, or a sponge | as DFA; the span lever needs a position-openable scheme (§3) |
| MMR aggregation (L2) | yes | yes; Count=0 is L2 ∘ (b)-rejection over the padded pattern | **only for positive `φ`**: "every record contains P"; not Count=0 |

Where ε-additivity fails for this family: a conjunction "`w ∈ L₁` by a path ∧ `w ∉ L₂` by a subset
witness" over one `c` is L1 and costs `ε₁ + ε₂ + b`, unless both are rows of one trace sharing the
SYMBOL column, in which case there is one witness and no `b` term (hub §3 "product").

## 7. Prior art

- ZK Email, *generalized regex*, ePrint 2026/1284, PoPETs 2026 [READ, via CERTIFICATES §6]: path
  verification over ε-free NFAs, with capture groups, DKIM and partial SHA-256 precomputation; no
  complement or absence.
- Luo, Weng, Singh, Tan, Piskac, Raykova, *Privacy-Preserving Regular Expression Matching using
  Nondeterministic Finite Automata*, ePrint 2023/643 [READ]: input-oblivious `O(mn)` Thompson-NFA
  matching with a ZK proof. That is the subset-simulation shape (b), in the interactive setting.
- Reef, ePrint 2023/1886 [cited in CERTIFICATES §6]: skipping alternating automata; match and non-match.
- Chistikov, Rino, *Intersecting Dense Automata*, arXiv 2605.20421 [READ]: a cheaper certification
  scheme for NFA intersection emptiness, which bears on product certificates of type (b).
- mathlib `NFA.toDFA_correct`, `εNFA.toNFA_correct`, `NFA.accepts_iff_exists_path` [READ].

Not claimed as ours: NFA path certificates (ZK Email), oblivious subset simulation in ZK (Luo et al.),
NFA non-match in ZK (Reef). The polarity table of §5 is textbook automata theory; what may be ours is
stating it as two Lean theorems with the content leg.

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| `NFA`, `εNFA`, `Path`, `accepts_iff_exists_path`, `toDFA_correct`, `toNFA_correct` | mathlib `NFA.lean:55, 280, 309, 323`; `EpsilonNFA.lean:39, 278` | L1 (library) |
| `thompson`, `thompson_recognizes`, `legacy_determinized_faithful_thompson` | `Deriv/Thompson.lean:338, 751, 760` | L1; table is `Set σ`, not executable |
| integer relabeling of `determinizedTable` | `compiler.rs::Nfa::determinize` | L4 deployed, [CLAIM] "immaterial", unproved |
| (a) run | as `01-dfa.md` table routing | L3 (unbound word) |
| `PathCert`, `pathCert_bound_sound` | proposed | L0; the proof is one line over mathlib |
| `SubsetCert`, `subsetCert_bound_rejects` | proposed | L0 |
| (b) AIR, (c) AIR | proposed | L0 |

**Milestone:** land `pathCert_bound_sound`, `subsetCert_bound_rejects` and falsifier 1 in one Lean file,
with a `#guard` that runs a `SubsetCert` checker on the `m = 4` instance of `(a|b)* a (a|b)^m`
(6 NFA states) over a 16-symbol word with no `a` at position `n − 5`. It must return `true`, and it must
return `false` when one set has a reachable state dropped. Pin the per-row column count
`|Q| + k + 1 = 6 + 2 + 1 = 9` beside it. The comparison point is the determinized table: the minimal
DFA has `2^(m+1) = 32` states, so its table has `32 · 2 = 64` rows [INFERRED]. Rung L2.
