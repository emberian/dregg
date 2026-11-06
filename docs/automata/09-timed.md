# Timed automata for receipt windows — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned #guard or a run; [CLAIM] asserted elsewhere; [INFERRED] derived here.

Paths: `M` = `/Users/ember/dev/breadstuffs/metatheory/Dregg2`, `R` = `/Users/ember/dev/breadstuffs`.
Hub: §2 row "timed automata (receipt windows)".

**Status.** No timed automaton exists in `M`. The deployed artefact closest to it is Rust
`R/audit/src/proofs.rs:103 RangeProof` ("all uses of a token fall within a time range"), and it is
this note's falsifier (§5).

## 1. Semantics object (Lean)

Proposed. One clock is enough for receipt windows: "every receipt in the range lies in
`[t₀ + lo, t₀ + hi]`" and "each response follows its request within `W`" both need one clock that is
reset at an anchor event. Guards are closed intervals on the clock, so the automaton is
diagonal-free. Time is `ℕ` (seconds, relative to the statement's origin `t₀`).

```lean
namespace Dregg2.Crypto.Timed

/-- One-clock deterministic timed automaton. Edge `(q, a)` is enabled iff the clock value
`x = t − lastReset` lies in `guard q a = (lo, hi)`; `reset q a` restarts the clock at `t`. -/
structure Timed1 (State Sym : Type) where
  step   : State → Sym → State
  guard  : State → Sym → ℕ × ℕ
  reset  : State → Sym → Bool
  start  : State
  accept : State → Bool

/-- Run over a timed word `[(a, t)]`: `r` is the last reset time, `tp` the previous timestamp.
Timestamps must be non-decreasing; a failed guard or a time reversal rejects. -/
def Timed1.runFrom (A : Timed1 State Sym) : State → ℕ → ℕ → List (Sym × ℕ) → Option State
  | q, _, _,  []            => some q
  | q, r, tp, (a, t) :: ws  =>
      if tp ≤ t ∧ r ≤ t ∧ (A.guard q a).1 ≤ t - r ∧ t - r ≤ (A.guard q a).2 then
        A.runFrom (A.step q a) (if A.reset q a then t else r) t ws
      else none

def Timed1.acceptsB (A : Timed1 State Sym) (t₀ : ℕ) (w : List (Sym × ℕ)) : Bool :=
  match A.runFrom A.start t₀ t₀ w with
  | some q => A.accept q
  | none   => false

/-- A receipt as the MMR leaf commits it: a symbol (the receipt kind), its timestamp, the rest. -/
structure Receipt where
  sym  : ℕ
  ts   : ℕ
  body : List ℤ

def timedWord (rs : List Receipt) : List (ℕ × ℕ) := rs.map fun r => (r.sym, r.ts)

end Dregg2.Crypto.Timed
```

## 2. Certificate shape

Public `x = (R, lo, hi, t₀, A)`: the MMR root `R` of the receipt log, the position range
`[lo, hi]` the claim covers, the clock origin `t₀`, and the public automaton (as a table). Witness:
the receipts `rs` at positions `lo..hi`; per receipt, its bytes, its leaf digest, and the MMR
opening; and the run rows `(state, sym, next, r, t, tp)` with the limb decompositions of the guard
differences.

**The timestamp comes from the leaf, never from a free column.** The `t` cell of row `i` is decoded
from the same bytes whose digest is the opened leaf `L[lo + i]`. That is the whole point of the
family and the whole failure of `RangeProof` (§5).

## 3. Arithmetization and counts

Pinned: table-routing DFA step 3 columns, 1 lookup, 4 constraints [MEASURED
`M/Circuit/Emit/DfaRoutingTableEmit.lean:540-543`]; nibble table, 4 bits per lookup [MEASURED
`M/Circuit/Emit/ByteTableEmit.lean:108` `HEIGHT == 16`]; Poseidon2 352 / 141 cells [MEASURED
`Poseidon2RoundGates.lean:121`, `:833`]; MMR opening `log₂ N` compressions (hub §3).

**Clock width.** BabyBear `p = 2013265921 ≈ 2^30.91`. Absolute Unix seconds exceed `p` at
2033-10-18 16:32:01 UTC (`date -u -r 2013265921`) [INFERRED], so an absolute timestamp cannot live in
one felt past that date. The clock is therefore relative (`t − t₀`, which is what a timed-automaton
clock is anyway), and a range check of `b` bits is sound only if `2 · 2^b < p`, i.e. `b ≤ 29`. Take
`b = 28` (windows up to `2^28` s ≈ 8.5 years): `⌈28/4⌉ = 7` nibble lookups per range check [INFERRED].

**Per receipt (one run row)** [INFERRED]:
- run columns: `CURRENT, SYMBOL, NEXT` (3) + `R` (last reset), `T`, `TP` (3) = 6;
- transition lookup: 1, tuple `(CURRENT, SYMBOL, NEXT, LO, HI, RESET)`, arity 6, table `|Q|·|Σ|` rows
  (the guard bounds ride in the table, so `LO`, `HI`, `RESET` are 3 more columns: 9);
- guard: `(T − R) − LO ∈ [0, 2^28)` and `HI − (T − R) ∈ [0, 2^28)`: 2 × 7 = 14 nibble lookups;
- monotonicity: `T − TP ∈ [0, 2^28)`: 7 nibble lookups;
- limb columns: 3 × 7 = 21; recomposition gates: 3 (degree 1);
- clock update: `R' = RESET · T + (1 − RESET) · R` (degree 2), `TP' = T` (degree 1);
- total: 30 columns, 22 lookups (1 transition + 21 nibble), 4 + 3 + 2 = 9 constraints plus 2 boundary
  pins (`R₀ = TP₀ = 0` relative to `t₀`).

**The leaf and the opening, per receipt** (assuming 256-byte receipts and `N = 2^20` positions; both
are assumptions):
- leaf digest: `⌈(128 + 4)/4⌉ + 1 = 34` permutations;
- MMR opening: `log₂ N = 20` compressions (bagging over the at most `log₂ N` peaks adds up to 20 more
  per opening if not shared [INFERRED from `peaksOf_mountains`, `M/Lightclient/MMR.lean:371`]);
- total: 54 permutations = 19,008 cells, against 30 run cells: the hash is about 630× the clock.
  For this family the timed automaton is a rounding error.

**Whole-range alternative**: when `[lo, hi]` is the whole log, rebuild the MMR in the trace instead of
opening every leaf: `N − popcount(N)` merges in total, under 1 compression per receipt, plus the leaf
digest. That is about 35 permutations per receipt instead of 54 [INFERRED from the carry in
`push`, `MMR.lean:263`].

**Hash instantiation caveat**: the Lean MMR is over an abstract `hash : List ℤ → ℤ`, while the Rust
query-side MMR is blake3 (`Blake3Mmr`, census §7). The permutation counts above assume a Poseidon2
MMR. Opening a blake3 MMR in-circuit is unpriced here.

## 4. Binding to the content commitment

The content commitment is the MMR root `R` itself. Row `i`'s receipt bytes are absorbed into the leaf
sponge (shared witness cells, U3 style); the sponge output is the leaf the opening proves at position
`lo + i` against `R`; and `T` is a degree-1 recomposition of the timestamp's 16-bit lanes from those
same absorbed cells. So the timestamp column is bound, through the leaf, to the root. Today: NOT
BOUND anywhere, because nothing is built, and the Rust `RangeProof` leaves the timestamp free (§5).

## 5. Soundness statement (Lean syntax) and its vacuity falsifier

The aggregation fact this rests on, verbatim [READ `M/Lightclient/MMR.lean:780-785`]:

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

The proposed statement, with the root in it:

```lean
open Dregg2.Lightclient.MMR

structure WindowStatement where
  R  : ℤ        -- MMR root of the receipt log
  lo : ℕ
  hi : ℕ
  t₀ : ℕ        -- clock origin

class TimedKernel (hash : List ℤ → ℤ) (leaf : Receipt → ℤ) (A : Timed1 ℕ ℕ) (Proof : Type) where
  verify      : WindowStatement → Proof → Bool
  extractable : Prop
  extract : extractable → ∀ st π, verify st π = true →
    ∃ (L' : List ℤ) (rs : List Receipt),
      mroot hash L' = st.R ∧ RVerifies L' st.lo st.hi (rs.map leaf) ∧
      A.acceptsB st.t₀ (timedWord rs) = true

/-- Soundness against the GENUINE log `L` behind `R`: the accepted timed word is read off receipts
whose leaves are exactly the genuine range, or the server found a root collision, or two receipts
share a leaf digest. Both escape events are named, not assumed away. -/
theorem timed_window_sound [K : TimedKernel hash leaf A Proof] (hext : K.extractable)
    (st : WindowStatement) (π : Proof) (hacc : K.verify st π = true)
    (L : List ℤ) (hL : mroot hash L = st.R) (gs : List Receipt) (hgs : gs.map leaf = mrange L st.lo st.hi) :
    A.acceptsB st.t₀ (timedWord gs) = true
    ∨ (∃ L', mroot hash L' = mroot hash L ∧ MRootColl hash L' L)
    ∨ (∃ r g, r ≠ g ∧ leaf r = leaf g)
```

Proof route: `extract`, then `server_cannot_omit_position` (or the `MRootColl` disjunct) gives
`rs.map leaf = mrange L lo hi = gs.map leaf`; then `rs = gs` or a leaf collision; then rewrite.

**Falsifier** (a receipt outside the window whose timestamp column was forged). The log holds one
receipt at `ts = 2000`; the window demands `ts ∈ [1000, 1060]`. The prover submits the genuine leaf
with a forged timestamp `1030`. Toy injective leaf `leafT r = r.ts · 1000 + r.sym` (for `sym < 1000`):

```lean
def leafT (r : Receipt) : ℤ := (r.ts : ℤ) * 1000 + r.sym
def genuine : Receipt := ⟨1, 2000, []⟩
def forged  : Receipt := ⟨1, 1030, []⟩
def L₀ : List ℤ := [leafT genuine]                                   -- = [2000001]

def win : Timed1 Unit ℕ :=
  { step := fun _ _ => (), guard := fun _ _ => (1000, 1060), reset := fun _ _ => false
    start := (), accept := fun _ => true }

/-- The `RangeProof` shape (`proofs.rs:125-157`): the leaf opens, and a SEPARATE timestamp field is
in range. Nothing ties the timestamp to the leaf. -/
def weakCheck (L : List ℤ) (claims : List (ℤ × ℕ)) : Bool :=
  claims.length == L.length &&
  (claims.zip L).all (fun (c, l) => c.1 == l && 1000 ≤ c.2 && c.2 ≤ 1060)

/-- The bound shape: the leaf is RECOMPUTED from the receipt whose timestamp the run reads. -/
def boundCheck (L : List ℤ) (rs : List Receipt) : Bool :=
  rs.map leafT == mrange L 0 (L.length - 1) && win.acceptsB 0 (timedWord rs)

example : weakCheck L₀ [(leafT genuine, 1030)] = true  := by decide   -- accepted: forged ts
example : boundCheck L₀ [forged]               = false := by decide   -- leafT forged = 1030001 ≠ 2000001
example : boundCheck L₀ [genuine]              = false := by decide   -- the genuine ts fails the guard
```

`weakCheck` is a faithful model of `RangeProof::verify` [READ `R/audit/src/proofs.rs:125-157`]: it
checks `witness.timestamp` against `[range_start, range_end]` and `witness.inclusion_proof` against
`log_root`, and never relates `timestamp` to `leaf_hash` or `event_hash`. (Also, as with `CountProof`,
`global_index` is not tied to the path, and the "timestamp witnesses for each event of this token"
are not shown to be all of them; see `08-weighted.md` §2.1.) The forged certificate meets the weak
shape and is refused by the opening against the root, because the recomputed leaf differs.

## 6. Composition behaviour

- **Product with DFAs**: the clock is one more lane on a lanes trace; a policy DFA over receipt kinds
  shares `SYMBOL`.
- **More clocks**: each extra clock is `+1` column and `+14` nibble lookups per guarded edge. Two
  clocks are needed for "within `W` of its request AND within the epoch".
- **Concatenation**: the clock state `(R, TP)` crosses the split, so the boundary row carries it
  (`+2` copy constraints). **Star**: fine. **Complement**: the deterministic one-clock automaton is
  closed under complement by swapping `accept` (the guard partition must be total per `(q, a)`, the
  same totality condition as hub §3's complement row).
- **MMR aggregation**: native; this family IS an aggregation statement.
- **Weighted**: a budget per window is `08-weighted.md`'s accumulator reset by the clock's reset.
- **ε-additivity fails** if timestamps are proved in one certificate and the window in another
  without sharing the leaf (that is the `RangeProof` shape). It also fails silently past 2033-10-18
  if absolute times are used in one felt.

## 7. Prior art

- Alur-Dill timed automata (TCS 1994) [RECALLED]; one-clock timed automata have decidable inclusion
  (Ouaknine-Worrell, LICS 2004) [RECALLED].
- Transparency logs: Tomescu et al., CCS 2019, ePrint 2018/721 [READ in PRIOR-ART §10], for the
  append-only, non-omission primitive.
- RTLola (Baumeister, Finkbeiner et al., CAV 2020) [RECALLED in PRIOR-ART §8]: real-time stream
  monitors with bounded memory.
- PRIOR-ART §8 records no hit for any ZK use of timed automata. "No hit" is not "none exists".

Not claimed as ours: timed automata, one-clock decidability, or windowed log queries.

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| `Timed1`, `runFrom`, `acceptsB`, `Receipt` | proposed | none |
| `timed_window_sound` | proposed | L0 |
| `server_cannot_omit_position` | `M/Lightclient/MMR.lean:780` | L1 |
| `RangeProof` | `R/audit/src/proofs.rs:103` | L4 deployed Rust; timestamp unbound (the falsifier) |
| one-clock AIR (30 columns, 22 lookups per receipt) | proposed | none |

**Milestone**: `M/Crypto/Timed.lean` at L2: `timed_window_sound` proved off
`server_cannot_omit_position`; the three `decide` facts above; and a `#guard` pinning the per-receipt
bill at `b = 28`, `N = 2^20`: 21 nibble lookups and 54 permutations per receipt.
