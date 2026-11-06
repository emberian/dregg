# Weighted and counting automata over a semiring — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned #guard or a run; [CLAIM] asserted elsewhere; [INFERRED] derived here.

Paths: `M` = `/Users/ember/dev/breadstuffs/metatheory/Dregg2`, `R` = `/Users/ember/dev/breadstuffs`.
Hub: §2 row "weighted / counting automata", §3 rows "complement" and "MMR aggregation".

**Status.** No weighted automaton exists in `M` (the 72 grep hits for "weighted" are generic [READ,
census §8]). The one counting artefact in the tree is Rust `R/audit/src/proofs.rs` `CountProof` /
`BudgetProof`, read honestly in §2.1 below.

## 1. Semantics object (Lean)

Proposed. Two layers: the general weighted automaton (sum over runs, as a vector-matrix product) and
the sequential one (deterministic skeleton, one run, value = ⊗-fold), which is the one the certificate
arithmetizes.

```lean
namespace Dregg2.Crypto.Weighted
open BigOperators

/-- General weighted automaton over a semiring `K`: `value w = init · M(a₁) ⋯ M(aₙ) · final`, i.e.
⊕ over all runs of the ⊗ of their edge weights. -/
structure WFA (Q Sym K : Type) [Fintype Q] [Semiring K] where
  init  : Q → K
  trans : Sym → Q → Q → K
  final : Q → K

def WFA.stepVec [Fintype Q] [Semiring K] (A : WFA Q Sym K) (v : Q → K) (a : Sym) : Q → K :=
  fun q' => ∑ q, v q * A.trans a q q'

def WFA.value [Fintype Q] [Semiring K] (A : WFA Q Sym K) (w : List Sym) : K :=
  ∑ q, (w.foldl A.stepVec A.init) q * A.final q

/-- Sequential weighted automaton: a deterministic skeleton with a weight per edge. One run, so ⊕ is
never used; the value is the ⊗-fold of the run's weights, times the final weight. -/
structure SeqWFA (Q Sym K : Type) [Monoid K] where
  step  : Q → Sym → Q
  wt    : Q → Sym → K
  start : Q
  final : Q → K

def SeqWFA.runFrom [Monoid K] (A : SeqWFA Q Sym K) : Q → K → List Sym → Q × K
  | q, acc, []      => (q, acc)
  | q, acc, a :: as => A.runFrom (A.step q a) (acc * A.wt q a) as

def SeqWFA.value [Monoid K] (A : SeqWFA Q Sym K) (w : List Sym) : K :=
  let r := A.runFrom A.start 1 w
  r.2 * A.final r.1

/-- The accumulator column a certificate carries: the prefix folds. -/
def SeqWFA.accCol [Monoid K] (A : SeqWFA Q Sym K) : Q → K → List Sym → List K
  | _, acc, []      => [acc]
  | q, acc, a :: as => acc :: A.accCol (A.step q a) (acc * A.wt q a) as

/-- Counting: `K := Multiplicative ℕ`, so ⊗ is `+` and the value is the number of weight-1 steps.
`Count = 0` is `value w = 1` (that is, `ofAdd 0`). Budgets: weights are costs; acceptance is
`toAdd (value w) ≤ limit`. -/
def CountAccepts (A : SeqWFA Q Sym (Multiplicative ℕ)) (k : ℕ) (w : List Sym) : Prop :=
  Multiplicative.toAdd (A.value w) = k

def BudgetAccepts (A : SeqWFA Q Sym (Multiplicative ℕ)) (limit : ℕ) (w : List Sym) : Prop :=
  Multiplicative.toAdd (A.value w) ≤ limit

end Dregg2.Crypto.Weighted
```

The algebraic bridge is Green-Karvounarakis-Tannen: annotate each edge (or each source record) with a
variable of the provenance semiring `ℕ[X]`. The value is then a provenance polynomial, and every other
reading is its image under a semiring homomorphism: `X ↦ 1` into `ℕ` counts, into `Bool` decides,
into a tropical semiring prices. The statement to prove (L1) is

```lean
theorem WFA.value_map [Fintype Q] [Semiring K] [Semiring K'] (h : K →+* K') (A : WFA Q Sym K)
    (w : List Sym) :
    h (A.value w) = (⟨h ∘ A.init, fun a q q' => h (A.trans a q q'), h ∘ A.final⟩ : WFA Q Sym K').value w
```

so one certificate over `ℕ[X]` specializes to Count, Boolean absence and cost by a public
homomorphism, never by a second proof.

## 2. Certificate shape

Sequential case (the one arithmetized). Public `x = (c, tbl, v)`: content commitment `c` of the word
`w`, the public weighted transition table `tbl` with rows `(q, a, step q a, wt q a)`, and the claimed
value `v` (a count, or a budget bound). Witness: the run rows `(state, sym, next, acc)`, where `acc`
is the prefix fold `accCol`.

General (nondeterministic) case: the vector state `v_i : Q → K` per row (`|Q|` columns), with
`v_{i+1} = stepVec v_i a_i`. That costs `|Q|²` degree-2 terms per row and is only worth it when no
deterministic skeleton exists.

`Count = 0` over a CORPUS is L2∘L3 (CERTIFICATES §2): per record, the count automaton (or the padded
complement DFA `neg (any* · P · any*)`) proves value 0 against that record's `c_k`; MMR aggregation
plus non-omission over `[0, N − 1]` makes it a statement about every record.

### 2.1 The honest reading of `audit::CountProof`

[READ `R/audit/src/proofs.rs:22-90`, `R/audit/src/event.rs:92-134`]. `CountProof::verify` checks:
(1) `event_proofs.len() == count`; (2) per entry, `global_index < log_size`, the index is unique, the
leaf hash matches the proof's, and `proof.verify(&log_root)` holds; (3) `index_commitment` is the
blake3 hash of the claimed indices. What it does not check:

- `token_id` appears nowhere in `verify`. No leaf is shown to belong to token X (census §7 found this).
- **`global_index` is not tied to the path.** `InclusionProof::verify(&self, root)` takes no index
  and never compares `path_indices` with `global_index` (`event.rs:103-134`). The "unique indices"
  are unique labels: K copies of ONE valid inclusion proof under K distinct labels pass. So the census
  phrase "certifies ≥ K distinct leaves" (census §7, repeated in the hub's §2 row) is too generous. It
  certifies "the root has at least one leaf" when `count ≥ 1` [INFERRED from the code; not run].
- `log_size` is a free field, not bound to `log_root`.
- No non-omission. Uses can be left out, so the count is not an upper bound either.
- **At `count = 0` it certifies nothing**: empty `event_proofs` plus the blake3 hash of no indices
  verifies for every `token_id` and every `log_root`. "Token X was used 0 times" is accepted
  unconditionally. `BudgetProof::verify` (`proofs.rs:284-305`) inherits this (`uses_consumed = 0`,
  `remaining = limit`), and it never reads its own `windowed`, `window_start` or `window_end` fields.

The doc comment (`proofs.rs:11`) says "Proof that a token was used exactly K times". The code proves
neither "exactly" nor "of token X".

## 3. Arithmetization and counts

Pinned: table-routing DFA step 3 columns, 1 lookup, 4 constraints [MEASURED
`M/Circuit/Emit/DfaRoutingTableEmit.lean:540-543`]; Poseidon2 352 / 141 cells [MEASURED
`Poseidon2RoundGates.lean:121`, `:833`]; nibble table, 4 bits per lookup [MEASURED
`M/Circuit/Emit/ByteTableEmit.lean:108` `HEIGHT == 16`]; MMR opening `log₂ N` compressions (hub §3).

**Per symbol, additive weights (Count, budget)** [INFERRED]:
- columns: `CURRENT, SYMBOL, NEXT` (3) + `ACC` (1) + `WT` (1) = 5. The hub's "+1 column" is reachable
  if a lookup tuple may contain the next-row expression `ACC' − ACC` in place of `WT`. Whether the IR2
  lookup tuples may read next-row cells is not established here, so 5 is the safe count;
- lookups: 1, tuple `(CURRENT, SYMBOL, NEXT, WT)` into a table of arity 4 (`|Q|·|Σ|` rows);
- constraints: 4 (routing) + `ACC' = ACC + WT` (degree 1) + boundaries `ACC₀ = 0` and
  `ACC_last + final(NEXT_last) = v` = 7. Max degree 2, coming from the routing gates, not the weight.
  The hub's "+1 degree-2 gate" is the MULTIPLICATIVE case (`ACC' = ACC · WT`);
- permutations in the run: 0.

**No-wrap condition**: `ACC` is a BabyBear felt (`p = 2013265921 ≈ 2^30.91`). The fold equals the
integer sum only if `n · max wt < p`. For a count (`wt ∈ {0, 1}`) that is `n < p`. For a budget with
costs up to `2^18` it allows `n < 2^12.9`, so about 7,680 events [INFERRED].

**Threshold acceptance** `value ≤ limit`: one range check of `limit − ACC_last` into `[0, 2^b)`,
`⌈b/4⌉` nibble lookups, once per word. At `b = 28` that is 7 lookups. It is sound if
`2^b + n · max wt < p`.

**Worked instance** (one 4096-byte record, count of a pattern) [INFERRED]: run 4096 rows × 5 = 20,480
cells, 4096 lookups; commitment `⌈(2048 + 4)/4⌉ + 1 = 514` permutations × 352 = 180,928 cells. The hash
is `≈ 8.8×` the automaton (11× with the hub's 4-column variant).

**Corpus Count** over `N` records: `N` per-record certificates + `N` MMR openings of `log₂ N`
compressions each + one sum over the per-record `v_k` public inputs. At `N = 2^20` that is 20
compressions per record for the openings alone [INFERRED].

## 4. Binding to the content commitment

The `SYMBOL` column is the word. It is bound to `c` by the route chain (`+1` arity-2 chip lookup per
row, hub §2.1), or by shared witness cells when `c` is a sponge over the same column (U3). The value `v`
is a public input pinned to `ACC_last`. Today: NOT BOUND, because nothing is built. The Rust
`CountProof` binds neither the token (no leaf content is read) nor the positions (§2.1).

## 5. Soundness statement (Lean syntax) and its vacuity falsifier

```lean
open Dregg2.Crypto.Dfa (ContentScheme)

/-- The accumulator column IS the semiring fold of the run: row i holds the ⊗ of the first i weights. -/
theorem seq_acc_is_fold [Monoid K] (A : SeqWFA Q Sym K) (w : List Sym) (i : ℕ) (hi : i ≤ w.length) :
    (A.accCol A.start 1 w)[i]? = some (A.runFrom A.start 1 (w.take i)).2

structure WeightedStatement (D : Type) where
  c : D            -- commitment to the word
  v : ℕ            -- claimed count / total cost

class WeightedKernel (Q Sym D : Type) (S : ContentScheme Sym D) (A : SeqWFA Q Sym (Multiplicative ℕ))
    (Proof : Type) where
  verify      : WeightedStatement D → Proof → Bool
  extractable : Prop
  extract : extractable → ∀ st π, verify st π = true →
    ∃ (w : List Sym) (acc : List (Multiplicative ℕ)),
      S.commit w = st.c ∧ acc = A.accCol A.start 1 w ∧
      Multiplicative.toAdd (acc.getLast! * A.final (A.runFrom A.start 1 w).1) = st.v

/-- Soundness: the word behind `c` has weighted value exactly `v`, and the certificate's accumulator
column is the fold of that word's run. -/
theorem weighted_bound_sound [K : WeightedKernel Q Sym D S A Proof] (hext : K.extractable)
    (st : WeightedStatement D) (π : Proof) (hacc : K.verify st π = true) :
    ∃ w, S.commit w = st.c ∧ CountAccepts A st.v w
```

**Falsifier** (a run whose accumulator column is not the fold: one tampered row). Count the `0`s in
`[0, 1, 0]`; the honest column is `[0, 1, 1, 2]`. Tamper row 3 to `1`:

```lean
def cnt : ℕ → ℕ := fun a => if a = 0 then 1 else 0

/-- The per-row gate: ACC' = ACC + WT on every row, and ACC₀ = 0. -/
def accValid (wt : ℕ → ℕ) : List ℕ → List ℕ → Bool
  | [],      [_]           => true
  | a :: as, x :: y :: rest => y == x + wt a && accValid wt as (y :: rest)
  | _,       _             => false

def accValidFrom0 (wt : ℕ → ℕ) (w : List ℕ) (acc : List ℕ) : Bool :=
  acc.head? == some 0 && accValid wt w acc

/-- The weaker shape: length and the initial pin only, with the final row read as the value. -/
def weakValid (w : List ℕ) (acc : List ℕ) : Bool :=
  acc.length == w.length + 1 && acc.head? == some 0

example : accValidFrom0 cnt [0, 1, 0] [0, 1, 1, 2] = true  := by decide
example : weakValid [0, 1, 0] [0, 1, 1, 1]             = true  := by decide  -- claims count 1
example : accValidFrom0 cnt [0, 1, 0] [0, 1, 1, 1] = false := by decide  -- refused
```

The tampered trace meets the weak shape and claims `v = 1`. The real value is 2, and
`seq_acc_is_fold` refutes it at row 3. **Second falsifier, from the tree**: a Lean model of
`CountProof::verify` must make `count = 0, event_proofs = []` verify for every `token_id` and
`log_root` (§2.1). `weighted_bound_sound` composed with non-omission must refute "zero uses" on a log
that contains one use of token X.

## 6. Composition behaviour

- **Product with a DFA**: the weight lane is one more column on a product or lanes trace; weights
  add per lane.
- **Complement**: defined for the Boolean image only (`value = 0` versus `≠ 0`). `Count = 0` is the
  padded complement of L3. Weighted complement in general is not a semiring operation.
- **Concatenation and star**: the sequential value of a concatenation is the ⊗ of the parts at the
  split. That holds only for a deterministic skeleton; the general WFA needs the sum over splits.
- **MMR aggregation (L2)**: the corpus total is `Σ_k v_k`. A lower bound (`≥ K`) needs only distinct
  positions BOUND to the root (exactly what `CountProof` lacks). `= K`, `≤ K` and `= 0` need
  `server_cannot_omit_position` over the whole range.
- **Recursion**: the running total is the fold state, so it composes under folding with the
  `(t+k)ε` depth bound.
- **ε-additivity fails** for counts aggregated from independently proved records unless each record's
  `c_k` is the MMR leaf (otherwise two records can share a commitment and be counted twice, the L1
  `bindAdv` term). The no-wrap condition is a further non-cryptographic failure: past `n · max wt ≥ p`
  the certificate proves a residue mod `p`, not a count.

## 7. Prior art

- Green, Karvounarakis, Tannen, *Provenance Semirings*, PODS 2007 [SNIPPET in PRIOR-ART §5/§8]: the
  semiring annotation used in §1.
- Green, Tannen, *The Semiring Framework for Database Provenance*, PODS 2017 [SNIPPET in PRIOR-ART §8].
- *Provenance for Regular Path Queries*, arXiv 2001.09864 [SNIPPET in PRIOR-ART §8]: semiring provenance
  for automaton-shaped queries.
- Zhao, Subotić, Scholz, *Provenance for Large-scale Datalog*, arXiv 1907.05045 [READ in PRIOR-ART §5].
- PRIOR-ART §8 records no hit for any ZK use of weighted automata. "No hit" is not "none exists".

Not claimed as ours: semiring provenance and weighted automata themselves. What may be ours is only
the `CountProof` reading and the bound statement with its falsifiers.

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| `WFA`, `SeqWFA`, `accCol`, `CountAccepts`, `BudgetAccepts` | proposed | none |
| `seq_acc_is_fold`, `weighted_bound_sound`, `WFA.value_map` | proposed | L0 |
| `CountProof`, `BudgetProof` | `R/audit/src/proofs.rs:22`, `:258` | L4 deployed Rust; certifies less than its doc says (§2.1); no Lean twin |
| weighted AIR (5 columns, 1 lookup, 7 constraints per symbol) | proposed | none |

**Milestone**: `M/Crypto/Weighted.lean` at L2: `seq_acc_is_fold` proved, the three `decide` facts of
§5, and `countProof_zero_vacuous`, a model of `CountProof::verify` in which `count = 0` verifies for
all 2 × 2 choices of (token, root) in a toy instance. Pinned with a `#guard` on the 4096-symbol bill:
20,480 run cells against 514 commitment permutations.
