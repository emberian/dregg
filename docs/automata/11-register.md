# Register automata over data words (session ids) — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned #guard or a run; [CLAIM] asserted elsewhere; [INFERRED] derived here.

Paths: `M` = `/Users/ember/dev/breadstuffs/metatheory/Dregg2`, `R` = `/Users/ember/dev/breadstuffs`.
Hub: §2 row "register automata (session ids)".

**Status.** No register automaton exists in `M` (grep "register automat": 0 files [READ, census §8]).
The non-membership opening it needs for freshness is built: `opensTo … none` over the deployed
indexed-Merkle map (`M/Circuit/DescriptorIR2.lean:1102`, `:1141`, `:1180`).

## 1. Semantics object (Lean)

Proposed. A data word is a list of `(symbol, datum)` pairs; the datum is a session id (a felt). The
automaton has `k` registers. A transition sees which registers equal the current datum, and chooses
the next state and which registers to load with it. A freshness flag on an edge demands that the
datum was never seen before: GLOBAL freshness over the history, as in fresh-register automata.

```lean
namespace Dregg2.Crypto.Register

structure RegAut (State Sym D : Type) (k : ℕ) where
  start  : State
  init   : Fin k → D                                          -- e.g. a reserved "no session" value
  step   : State → Sym → (Fin k → Bool) → State × (Fin k → Bool)   -- (eq pattern) ↦ (next, load mask)
  fresh  : State → Sym → Bool                                 -- this edge demands an unseen datum
  accept : State → Bool

structure Cfg (State D : Type) (k : ℕ) where
  q    : State
  regs : Fin k → D
  seen : List D

def RegAut.stepCfg [DecidableEq D] (A : RegAut State Sym D k) (c : Cfg State D k) (x : Sym × D) :
    Option (Cfg State D k) :=
  let (a, d) := x
  if A.fresh c.q a ∧ d ∈ c.seen then none else
    let r := A.step c.q a (fun j => decide (c.regs j = d))
    some ⟨r.1, fun j => if r.2 j then d else c.regs j, d :: c.seen⟩

def RegAut.runFrom [DecidableEq D] (A : RegAut State Sym D k) :
    Cfg State D k → List (Sym × D) → Option (Cfg State D k)
  | c, []      => some c
  | c, x :: xs => (A.stepCfg c x).bind fun c' => A.runFrom c' xs

/-- Acceptance from an initial seen-set (the history before this word). -/
def RegAut.acceptsFrom [DecidableEq D] (A : RegAut State Sym D k) (seen₀ : List D)
    (w : List (Sym × D)) : Bool :=
  match A.runFrom ⟨A.start, A.init, seen₀⟩ w with
  | some c => A.accept c.q
  | none   => false

end Dregg2.Crypto.Register
```

`k = 1` is session binding: the register holds the open session's id, `msg` and `close` must match it,
and `open` must carry a fresh id.

## 2. Certificate shape

Public `x = (c, R₀, R_N)`: the commitment `c` of the data word, and the seen-set roots before and
after (deployed indexed-Merkle map roots). Witness: one row per data symbol with `k` register columns,
equality bits and inverse witnesses, load bits, and, on fresh edges, a non-membership opening of the
datum against the current seen-set root followed by an insert.

Two freshness notions, two prices:
- **local** (the datum differs from every register): `k` disequality gates, no opening;
- **global** (never seen in the history): a sorted-set opening (`.absent`, then `.write`) per fresh
  event. That is the one session ids need, because a closed session's id leaves the register.

## 3. Arithmetization and counts

Pinned: table-routing DFA step 3 columns, 1 lookup, 4 constraints [MEASURED
`M/Circuit/Emit/DfaRoutingTableEmit.lean:540-543`]; map-op opening 16 chip rows per opened key at
depth 16 [MEASURED `M/Circuit/Emit/AttestedAutomatonEmit.lean:1201`]; Poseidon2 352 / 141 cells
[MEASURED `Poseidon2RoundGates.lean:121`, `:833`]; nibble table, 4 bits per lookup [MEASURED
`ByteTableEmit.lean:108`].

**Per data symbol** [INFERRED]:
- columns: `CURRENT, SYMBOL, NEXT` (3) + `DATUM` (1) + `FRESH` (1) + per register `R_j, E_j, INV_j,
  LD_j` (4k) = `5 + 4k`. At `k = 1`: 9;
- per-register gates, all degree 2: `E_j·(1 − E_j) = 0`; `E_j·(R_j − DATUM) = 0` (equal when
  claimed); `(R_j − DATUM)·INV_j = 1 − E_j` (unequal when claimed, via the inverse);
  `R_j' = LD_j·DATUM + (1 − LD_j)·R_j`. That is 4 per register;
- constraints: `4 + 4k` (routing + registers) + `k` boundary pins (`R_j,0 = init j`). At `k = 1`: 9;
- transition lookup: 1, tuple `(CURRENT, SYMBOL, E_1..E_k, NEXT, LD_1..LD_k, FRESH)`, arity `3 + 2k + 1`,
  table `|Q|·|Σ|·2^k` rows;
- permutations in the run: 0.

**Global freshness, per fresh event**: `.absent` at the current root, then `.write` of the datum:
2 map-op openings × 16 chip rows = 32 chip rows (permutations), plus 2 root columns
(`ROOT, ROOT'`) [INFERRED from the pinned 16 per key]. Capacity: the deployed map holds at most
`2^16 = 65,536` keys (`hlen : h.length ≤ 2 ^ MAP_TREE_DEPTH` in `opensTo_none_of_gap`), so at most
65,536 sessions per seen-set root.

**Commitment of the data word**: 2 felts per symbol (symbol, datum), felt-native `hash_many_8`:
`⌈2n/4⌉ + 1` permutations [INFERRED from `R/circuit/src/poseidon2.rs:410-435`].

**Worked instance** (`k = 1`, `n = 1024` events, 64 sessions; the session count is an assumption)
[INFERRED]:
- run: 1024 × 9 = 9,216 cells; 1024 transition lookups;
- commitment: `⌈2048/4⌉ + 1 = 513` permutations = 180,576 cells;
- freshness: `64 × 32 = 2,048` permutations = 720,896 cells.
- Freshness is the bill here, 4× the commitment and 78× the run.

**Cheaper freshness within one word** [INFERRED]: if only the ids opened INSIDE this word must be
pairwise distinct, sort them in a side column (a permutation argument: 1 lookup per open) and range
check the consecutive differences as positive (`⌈29/4⌉ = 8` nibble lookups each, with `2 · 2^29 < p`).
That is 9 lookups per open and no permutations. Cross-history freshness still needs the set root, once
per certificate rather than per open, if the word's sorted ids are merged into the set in one batch.

## 4. Binding to the content commitment

The `(SYMBOL, DATUM)` columns are bound to `c` by the route chain (`+1` arity-2 chip lookup per row)
or by shared sponge cells. The seen-set is bound by its roots: the first fresh row reads `R₀` (public),
each fresh row's `ROOT'` becomes the next fresh row's `ROOT`, and the last equals `R_N` (public), as a
running-root column with copy constraints on non-fresh rows. Today: NOT BOUND, nothing is built. The
`opensTo` denotation it would use reads lane 0 of the root only, which is the hub §1 weld wound,
binding about `2^15.5` [READ hub §1, census §6], until the `MapOp.holdsAt8` flag day.

## 5. Soundness statement (Lean syntax) and its vacuity falsifier

The two deployed facts freshness rests on, verbatim [READ `M/Circuit/DescriptorIR2.lean:1141-1146`,
`:1180-1188`]:

```lean
theorem opensTo_some_excludes_none (hash : List ℤ → ℤ)
    {r k v : ℤ} (h₁ : opensTo hash r k (some v)) (h₂ : opensTo hash r k none)
    (hno : ¬ OpenColl hash h₁ h₂) : False

theorem opensTo_none_of_gap (hash : List ℤ → ℤ) {h : Heap.FeltHeap} {r lo hi k : ℤ}
    (hs : Heap.SortedKeys h) (hlen : h.length ≤ 2 ^ MAP_TREE_DEPTH)
    (hb : ∀ x ∈ Heap.keys h, x < MAP_SENTINEL)
    (hr : DeployedMapDenotation.padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h = r)
    (hadj : Dregg2.Crypto.NonMembership.Adjacent (Heap.keys h) lo hi)
    (hlo : lo < k) (hhi : k < hi) : opensTo hash r k none
```

(Statements copied up to the type; proofs elided.)

The first is SOUNDNESS of a freshness check (a datum that is in the set cannot also open as absent,
up to the named residual). The second is COMPLETENESS (an honest prover can always build the
non-membership opening from the sorted gap).

Proposed:

```lean
open Dregg2.Crypto.Dfa (ContentScheme)
open Dregg2.Circuit.DescriptorIR2 (opensTo OpenColl)

structure RegStatement (D : Type) where
  c  : D        -- commitment to the data word
  R₀ : ℤ        -- seen-set root before
  R_N : ℤ       -- seen-set root after

/-- Soundness: the data word behind `c` is accepted by `A` from the seen-set behind `R₀`, or some
fresh-event opening equivocates (the named per-instance residual). -/
theorem reg_bound_sound [K : RegKernel hash S A Proof] (hext : K.extractable)
    (st : RegStatement Dg) (π : Proof) (hacc : K.verify st π = true)
    (h₀ : Heap.FeltHeap)
    (hr₀ : DeployedMapDenotation.padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h₀ = st.R₀) :
    (∃ w, S.commit w = st.c ∧ A.acceptsFrom (Heap.keys h₀) w = true)
    ∨ (∃ (r d v : ℤ) (h₁ : opensTo hash r d (some v)) (h₂ : opensTo hash r d none),
         OpenColl hash h₁ h₂)
```

(`RegKernel` is the `DfaBoundVerifierKernel` pattern of `M/Crypto/Dfa.lean:257`: `extract` delivers
`w` with `S.commit w = st.c`, the run rows, and per fresh row an `opensTo hash ROOT DATUM none` and a
`writesTo` to `ROOT'`.)

**Falsifier** (a replayed session id accepted when freshness is dropped). `k = 1`. States
`0 = idle, 1 = active, 2 = dead`; symbols `0 = open, 1 = msg, 2 = close`:

```lean
def sess : RegAut ℕ ℕ ℕ 1 :=
  { start := 0, init := fun _ => 0
    step := fun q a e =>
      match q, a, e 0 with
      | 0, 0, _     => (1, fun _ => true)    -- open: load the datum
      | 1, 1, true  => (1, fun _ => false)   -- msg in the open session
      | 1, 2, true  => (0, fun _ => false)   -- close the open session
      | _, _, _     => (2, fun _ => false)
    fresh := fun q a => q == 0 && a == 0     -- open demands an unseen id
    accept := fun q => q == 0 }

def noFresh : RegAut ℕ ℕ ℕ 1 := { sess with fresh := fun _ _ => false }

def replayW : List (ℕ × ℕ) := [(0, 7), (1, 7), (2, 7), (0, 7), (1, 7), (2, 7)]   -- id 7 reopened

example : sess.acceptsFrom    [] replayW = false := by decide   -- second open: 7 ∈ seen, refused
example : noFresh.acceptsFrom [] replayW = true  := by decide   -- the checker without freshness accepts
example : sess.acceptsFrom [] [(0, 7), (1, 7), (2, 7), (0, 8), (1, 8), (2, 8)] = true := by decide
```

In circuit terms: dropping the `.absent` map-op on fresh rows (keeping only the `.write`, which is an
insert-or-update, `writesTo` at `DescriptorIR2.lean:1107`) accepts `replayW`, because the write of an
existing key succeeds. With the `.absent` opening, the second `open` at `7` must satisfy
`opensTo hash ROOT 7 none` while the heap behind `ROOT` reads `7 ↦ 1`: `opensTo_some_excludes_none`
refutes it unless `OpenColl` holds.

## 6. Composition behaviour

- **Product with DFAs**: a register lane is `4` columns + `4` gates per register on a lanes trace;
  DFA policies over symbols share `SYMBOL`.
- **Intersection**: register automata are closed under intersection (registers add: `k₁ + k₂`).
  **Union**: closed. **Complement**: NOT closed in general for nondeterministic register automata
  [RECALLED, Kaminski-Francez]. The deterministic form above complements by swapping `accept`, with
  the same totality condition as DFAs (every `(q, a, eq-pattern)` has an edge, which `step`'s type
  gives).
- **Concatenation**: the configuration (registers + seen-root) crosses the split.
- **MMR aggregation**: each record's certificate exposes `(R₀, R_N)`; chaining requires
  `R_N(k) = R₀(k + 1)`, which is a sequential, not parallel, aggregation.
- **ε-additivity fails** for freshness across certificates proved in parallel against the same `R₀`:
  each is sound alone, and two of them can insert the same id (a double spend of the session). The
  roots must chain.

## 7. Prior art

- Kaminski, Francez, *Finite-memory automata*, TCS 1994 [RECALLED, not in PRIOR-ART.md]: register
  automata over infinite alphabets.
- Tzevelekos, *Fresh-register automata*, POPL 2011 [RECALLED, not in PRIOR-ART.md]: global freshness.
- Nullifier sets in shielded-payment systems (non-membership as double-spend prevention) [RECALLED];
  the in-tree analogue is the cap/nullifier non-membership argument the `opensTo_some_excludes_none`
  docstring names.
- PRIOR-ART §8 records no hit for any ZK use of register automata. "No hit" is not "none exists".

Not claimed as ours: register automata, freshness, nullifier-style non-membership.

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| `opensTo`, `writesTo` | `M/Circuit/DescriptorIR2.lean:1102`, `:1107` | L3 (deployed map-ops denotation; lane 0) |
| `opensTo_some_excludes_none` | `DescriptorIR2.lean:1141` | L1 |
| `opensTo_none_of_gap` | `DescriptorIR2.lean:1180` | L1 |
| `RegAut`, `acceptsFrom` | proposed | none |
| `reg_bound_sound` | proposed | L0 |
| register AIR (`5 + 4k` columns, `4 + 5k` constraints, 1 lookup per symbol; 32 chip rows per fresh event) | proposed | none |

**Milestone**: `M/Crypto/Register.lean` at L2: `sess`, `noFresh` and the three `decide` facts above;
`reg_bound_sound` proved from a `RegKernel` and `opensTo_some_excludes_none`; and a `#guard` pinning
the `k = 1` instance's bill: 9 columns, 9 constraints, 1 lookup per symbol, and 2,048 freshness
permutations for 64 sessions.
