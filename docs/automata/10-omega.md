# Büchi / ω-automata for streaming logs — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned #guard or a run; [CLAIM] asserted elsewhere; [INFERRED] derived here.

Paths: `M` = `/Users/ember/dev/breadstuffs/metatheory/Dregg2`, `R` = `/Users/ember/dev/breadstuffs`.
Hub: §2 row "Büchi / ω-automata for streaming logs", §3 rows "MMR aggregation" and "recursion".

**Status.** The only Büchi content in `M` is a decision procedure, not a certificate:
`M/Deos/FlowRefine.lean:18` uses well-foundedness (`pstep_decreases`) to collapse Pradic's Büchi
acceptance in the flow-refinement simulation game [READ]. The MMR non-omission theory this note rests
on is built and proved (`M/Lightclient/MMR.lean`).

## 1. Semantics object (Lean)

Proposed. A log is the finite prefix of an infinite stream. What can be certified at a finite prefix
is a verdict about the prefix's relation to an ω-language: it is a bad prefix (every continuation
violates), a good prefix (every continuation satisfies), or neither.

```lean
namespace Dregg2.Crypto.Omega
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa classify classifyFrom)

abbrev OWord (Sym : Type) := ℕ → Sym

def Extends (σ : OWord Sym) (u : List Sym) : Prop := ∀ i (h : i < u.length), σ i = u[i]

def BadPrefix  (P : OWord Sym → Prop) (u : List Sym) : Prop := ∀ σ, Extends σ u → ¬ P σ
def GoodPrefix (P : OWord Sym → Prop) (u : List Sym) : Prop := ∀ σ, Extends σ u → P σ

def prefixOf (σ : OWord Sym) (n : ℕ) : List Sym := List.ofFn fun i : Fin n => σ i

/-- Safety: every violation is witnessed by a finite bad prefix. Co-safety: dually, good prefixes. -/
def IsSafety   (P : OWord Sym → Prop) : Prop := ∀ σ, ¬ P σ → ∃ n, BadPrefix P (prefixOf σ n)
def IsCoSafety (P : OWord Sym → Prop) : Prop := ∀ σ, P σ → ∃ n, GoodPrefix P (prefixOf σ n)

/-- Deterministic Büchi automaton: accept iff an accepting state recurs infinitely often. -/
structure DBuchi (State Sym : Type) where
  step   : State → Sym → State
  start  : State
  accept : State → Prop

def DBuchi.run (A : DBuchi State Sym) (σ : OWord Sym) : ℕ → State
  | 0     => A.start
  | n + 1 => A.step (A.run σ n) (σ n)

def DBuchi.Accepts (A : DBuchi State Sym) (σ : OWord Sym) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ A.accept (A.run σ n)

/-- The safety language of a monitor DFA with an absorbing `bad` set: no prefix reaches `bad`. -/
def SafeLang (d : TableDfa State Sym) (bad : State → Prop) : OWord Sym → Prop :=
  fun σ => ∀ n, ¬ bad (classify d (prefixOf σ n))

def BadAbsorbing (d : TableDfa State Sym) (bad : State → Prop) : Prop :=
  ∀ q a, bad q → bad (d.step q a)

/-- The three-valued verdict of a finite prefix (LTL3-style). -/
inductive Verdict | violated | satisfied | inconclusive

end Dregg2.Crypto.Omega
```

## 2. Certificate shape

Public `x = (R, d, bad, q)`: the MMR root `R` of the log (the prefix commitment), the monitor DFA, its
bad set, and the claimed final monitor state `q`. Witness: the log entries in order, each with its
leaf digest, a positional range answer `vals` over `[0, hi]` with `hi + 1 ≥` the log length, and the
monitor run over `vals.map dec`.

Two verdicts are certifiable at a finite prefix:
- **"Not violated so far"** (safety): the run over the WHOLE log ends outside `bad`. Since `bad` is
  absorbing, no prefix of the log is a bad prefix. Non-omission is what makes "the whole log" true: a
  certificate over a log with one entry left out says nothing.
- **"Violated at position j"**: the run over `[0, j]` reaches `bad`. Only `[0, j]` needs to be dense,
  but density matters here too: omitting the entry that would have disarmed the monitor manufactures
  a false violation.

Co-safety ("eventually p") is dual: a good prefix reaches an absorbing accept state.

**What cannot be certified at a finite prefix: liveness.** For `□(req → ◇resp)` every finite prefix
extends to a satisfying stream (append a response), so no prefix is bad, and the verdict is
`inconclusive` forever. The finite certificate's honest output is the monitor state, nothing more.
A Büchi condition is invisible at every finite prefix.

**Bounded liveness becomes safety.** `□(req → ◇_{≤D} resp)` (within `D` entries) has bad prefixes:
a request followed by `D` entries with no response. With at most one pending request it is a DFA with
`D + 3` states (idle, pending counter `0..D`, dead) [INFERRED]. With many pending requests it needs
the oldest deadline in a register (`11-register.md`)
or a clock (`09-timed.md`).

## 3. Arithmetization and counts

Pinned: table-routing DFA step 3 columns, 1 lookup, 4 constraints [MEASURED
`M/Circuit/Emit/DfaRoutingTableEmit.lean:540-543`]; Poseidon2 352 / 141 cells [MEASURED
`Poseidon2RoundGates.lean:121`, `:833`]; MMR opening `log₂ N` compressions (hub §3).

Per log entry, assuming 128-byte entries and `N = 2^20` (both assumptions) [INFERRED]:
- monitor step: 3 columns, 1 lookup, 4 constraints, table `|Q|·|Σ|` rows. Bounded liveness with
  `D = 64` over a 4-symbol alphabet: `67 · 4 = 268` rows;
- entry digest (so the monitor's symbol is decoded from the bytes the leaf commits):
  `⌈(64 + 4)/4⌉ + 1 = 18` permutations;
- **opening route**: `+ log₂ N = 20` compressions per entry, so 38 permutations = 13,376 cells per
  entry;
- **streaming route** (rebuild the MMR in the trace; the natural one for "the whole log"):
  `N − popcount(N)` merges over the whole log, under 1 compression per entry amortized, so about
  19 permutations = 6,688 cells per entry [INFERRED from the carry in `push`, `MMR.lean:263`, and
  `peaksOf L = L.foldl appendLeaf []`, `:278`];
- either way the monitor is 3 cells against thousands of hash cells. The hub's cost law holds with a
  factor in the thousands, not 4-15×, because each entry is a full record digest.

**Incremental extension** (height `N` to `N + 1`): one monitor step + one entry digest + the carry
merges. `append_preserves_opens` (`MMR.lean:673`) and `append_preserves_range` (`:684`) say earlier
openings and ranges survive appends verbatim, so an old certificate is still a certificate about the
old prefix of the new log.

## 4. Binding to the content commitment

The commitment is the MMR root. Under the streaming route, the trace's own final peaks bag to a public
`R` (shared cells: the entry digests ARE the leaves). Under the opening route, each entry's digest is
opened at its dense position. "The prefix is the whole log" is the conjunction of `RVerifies` over
`[0, hi]` with `hi + 1 ≥ |L|` and `server_cannot_omit_position`, which pins `vals = mrange L 0 hi`, and
`mrange L 0 hi = L` once `|L| ≤ hi + 1`.

The length matters: `RVerifies` checks `vals.length = rangeCount L'.length lo hi`, which presumes the
verifier evaluates the count at the committed length. The Rust windowed reader pins "the same
root-derived log length" for every page and requires the pages to tile `[0, len − 1]` with "no
truncated prefix or tail" [READ `R/dregg-query/src/windows.rs:1-24`]. A certificate that lets the
prover choose `hi` without that length pin certifies a prefix, not the log.

Today: the MMR side is BOUND and proved; no monitor certificate exists.

## 5. Soundness statement (Lean syntax) and its vacuity falsifier

Non-omission, verbatim [READ `M/Lightclient/MMR.lean:780-785`]:

```lean
theorem server_cannot_omit_position (hash : List ℤ → ℤ)
    {L L' : List ℤ} (hroot : mroot hash L' = mroot hash L)
    (hno : ¬ MRootColl hash L' L)
    {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L' lo hi vals) :
    vals = mrange L lo hi
    ∧ ∀ i, lo ≤ i → i ≤ hi → i < L.length →
        ∃ v, vals[i - lo]? = some v ∧ Opens L i v
```

Proposed (L1, provable from the above plus two list lemmas):

```lean
open Dregg2.Lightclient.MMR

theorem mrange_whole (L : List ℤ) {hi : ℕ} (h : L.length ≤ hi + 1) : mrange L 0 hi = L

/-- The bad set is absorbing, so a safe final state means NO prefix is bad. -/
theorem safe_final_no_bad_prefix (d : TableDfa State Sym) (bad : State → Prop)
    (habs : BadAbsorbing d bad) (u : List Sym) (h : ¬ bad (classify d u)) :
    ∀ n ≤ u.length, ¬ bad (classify d (u.take n))

/-- The monitor verdict is about THE WHOLE genuine log behind the root. -/
theorem monitor_whole_log_sound (hash : List ℤ → ℤ) (dec : ℤ → Sym) (d : TableDfa State Sym)
    {L L' : List ℤ} (hroot : mroot hash L' = mroot hash L) (hno : ¬ MRootColl hash L' L)
    {hi : ℕ} (hlen : L.length ≤ hi + 1) {vals : List ℤ} (hv : RVerifies L' 0 hi vals)
    {q : State} (hq : classify d (vals.map dec) = q) :
    classify d (L.map dec) = q
```

The kernel form names `R`: `K.verify ⟨R, d, bad, q⟩ π = true → ∃ L', mroot hash L' = R ∧ …`, and the
conclusion against the genuine `L` with `mroot hash L = R` carries the `MRootColl` disjunct, as in
`09-timed.md` §5.

**Falsifier** (a truncated tail: the prefix certificate passed off as the whole log). The log is
`[1, 1, 9]` with `9` the violating entry. The prover answers `[1, 1]`:

```lean
example : mrange [1, 1, 9] 0 5 = [1, 1, 9]   := by decide   -- a whole-log query (hi + 1 ≥ 3)
example : ([1, 1] : List ℤ) ≠ mrange [1, 1, 9] 0 5 := by decide
-- so by `rverifies_iff_exact` (MMR.lean:734), `¬ RVerifies [1, 1, 9] 0 5 [1, 1]`
example : mrange [1, 1, 9] 0 1 = [1, 1]      := by decide   -- the truncated query verifies,
-- but `hlen : 3 ≤ 1 + 1` is false, so `monitor_whole_log_sound` does not apply to it
```

A weaker statement that drops `hlen` (accepts `RVerifies L' 0 hi vals` for a prover-chosen `hi`)
certifies "never violated" for the log `[1, 1, 9]` from the answer `[1, 1]` at `hi = 1`. The stated
theorem refuses it: either `hi ≥ 2`, in which case `vals` must contain `9` and the monitor reaches
`bad`, or `hlen` fails.

## 6. Composition behaviour

- **Product**: several safety monitors over one log are lanes on one trace; the intersection of
  safety languages is safety.
- **Union**: safety languages are closed under finite union (product with an "either not bad" accept
  set).
- **Complement**: the complement of a safety language is co-safety, and the certificate flips from
  "no bad prefix" to "a good prefix", so it is a different certificate, not a swapped accept set.
- **MMR aggregation and recursion**: native. As IVC, the fold state is `(monitor state, peaks, N)`;
  one fold step per entry; error `(t+k)ε` (Selvage depth bound, hub §3), not `N·ε`.
- **Concatenation and star**: not meaningful on ω-words in this certificate. A Büchi condition has no
  finite certificate, so this family supports only its safety and co-safety fragments.
- **ε-additivity fails** if two monitors certify against two different heights of the same log (the
  prefix at `N` and at `N + 1` are different statements; `append_preserves_range` relates them, but
  only one-way).

## 7. Prior art

- Lola (D'Angelo et al., TIME 2005) and RTLola (Baumeister, Finkbeiner et al., CAV 2020)
  [RECALLED in PRIOR-ART §8]: stream runtime verification with bounded-memory monitors.
- Cohen, Havelund et al., *Monitoring LLM Conversations with First-Order Temporal Logic*, RV 2026
  [SNIPPET in PRIOR-ART §8].
- Three-valued LTL monitoring (Bauer, Leucker, Schallhart, LTL3) and Kupferman-Vardi bad prefixes for
  safety [RECALLED, not in PRIOR-ART.md].
- Tomescu et al., transparency logs, CCS 2019 [READ in PRIOR-ART §10]; Bonneau, Chen, Christ,
  Karantaidou, *Merkle Mountain Ranges are Optimal*, CRYPTO 2025 [READ in PRIOR-ART §10].
- PRIOR-ART §8 records no hit for ZK runtime monitoring of logs, and §10 none for IVC non-omission
  over an MMR. "No hit" is not "none exists", and this note claims no first.

Not claimed as ours: prefix semantics, runtime monitoring, MMRs, transparency logs.

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| `server_cannot_omit_position`, `range_complete`, `rverifies_iff_exact` | `M/Lightclient/MMR.lean:780`, `:718`, `:734` | L1 |
| `append_preserves_opens`, `append_preserves_range` | `MMR.lean:673`, `:684` | L1 |
| windowed whole-log reader | `R/dregg-query/src/windows.rs` | L4 Rust (blake3) |
| `BadPrefix`, `DBuchi`, `SafeLang`, `Verdict` | proposed | none |
| `monitor_whole_log_sound`, `safe_final_no_bad_prefix`, `mrange_whole` | proposed | L0 (L1 is a short proof) |
| Büchi decision content | `M/Deos/FlowRefine.lean:18` | decision procedure, not a certificate |

**Milestone**: `M/Crypto/Omega/PrefixMonitor.lean` at L1/L2: the three theorems of §5 proved, the
truncated-tail falsifier as `decide` facts, and a `#guard` pinning the per-entry bill at
`N = 2^20`, 128-byte entries: 19 permutations streaming against 38 via openings.
