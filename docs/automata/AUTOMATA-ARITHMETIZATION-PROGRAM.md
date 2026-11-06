# Verified arithmetization of automata, their compositions, and the semantic ceiling

2026-11-05. Hub document; one note per family under `docs/automata/`. Tags: [READ] seen at the
cited file:line; [MEASURED] a pinned `#guard` or a run; [CLAIM] asserted elsewhere, unchecked;
[INFERRED] derived here. Counts over clocks. Companions: `zkml-research/docs/CERTIFICATES.md`
(the certificate algebra), `zkml-research/docs/PROOF-SYSTEM-SPACE.md` (U3), `SEMANTIC-CEILING.md`
(what logics the system can express), `codex-synthesis.md` (the adversarial rounds).

Ember's ask: *"verified arithmetization of various automata and compositions of automata ...
different ways of composing proofs and automata ... as much semantic richness as we can (full
Datalog? hella-symbolic SMT-style things?)"*, built towards *"something meaningful that we can
evaluate."*

---

## 0. The thesis in one paragraph

A certificate in this system is a **relation `R(x, w)` on public data `x` and a witness `w`**, checked
by an AIR (rows of a trace, lookups into tables, boundary pins), where `x` always contains a
**content commitment `c`** of the word the automaton read (law L0 of CERTIFICATES.md). An automaton
family is admitted to the zoo when it has: a Lean semantics object (what the language IS), a
certificate shape (what the prover supplies), an arithmetization with pinned counts (what it costs
per symbol), a binding to `c` (what ties the run to the record), a soundness statement whose
hypotheses are inhabited and whose conclusion names `c` and the word, and a vacuity falsifier (a
concrete acceptance test that meets a weaker shape and fails this one). Composition is where the
value is and where the errors hide: conjunction over one `c` costs `ε₁ + ε₂ + bindAdv`, aggregation
costs `N·ε + bindAdv_MMR`, and three compositions are **not** additive (shared randomness, shared
commitment without binding, order-dependent transducer chains). The cost law that governs every
family: **the content commitment is ~n/8 Poseidon2 permutations for n bytes [READ,
`circuit/src/poseidon2.rs:704` rate-4 absorb; `sel4/.../crypto-floor/src/field.rs:94` two bytes
per lane plus four length lanes], i.e. 44 committed cells per byte at the deployed 352-cell
permutation [MEASURED, `Poseidon2RoundGates.lean`], while a table-routing DFA step is 3 cells per byte [MEASURED] (the 11-column attested shape is over
BINARY symbols and adds 16 chip rows of map authentication per step, so it is not a byte-step
number; codex round 2). Exactly: `hash_bytes_8` costs `⌈n/8⌉ + 2` permutations (`⌈(⌈n/2⌉+4)/4⌉`
absorbs plus the squeeze permutation at `poseidon2.rs:430` [READ, codex round 2]).
The hash dominates the plain regular families by about 4-15× per byte; it does NOT dominate
families whose per-symbol work is itself a Merkle opening (attested) or a subset trace (NFA on the
fly); the commitment is the bill wherever the run is a lookup, and the design question is always
how many statements share one commitment.**

---

## 1. What landed today (Part A), and what it fixed

| defect (yesterday) | repair | statement, falsifier | where |
|---|---|---|---|
| `Dfa.Statement` holds no word, no commitment; `dfa_verify_sound` concludes `∃ trace, DfaAccepts …`, which an accepting run over a benign word discharges for ANY record (the splice) | Layer B′: `BoundStatement` carries `c`; `DfaBoundVerifierKernel.extract` delivers a run whose word commits to `c`; dial wiring re-pointed | `dfa_bound_verify_sound : … → ∃ w, S.commit w = stmt.c ∧ ∃ trace, DfaAccepts … trace ∧ traceWord trace = w`. Falsifier: `Reference.splice_meets_unbound` ∧ `Reference.splice_fails_bound` (the record-ignoring acceptance test meets the unbound extract shape and refutes the bound one) | `metatheory/Dregg2/Crypto/Dfa.lean` |
| The weld carries 8 root lanes on the wire but `DescriptorIR2.MapOp.holdsAt` reads lane 0: lanes 1-7 content-unforced, `weld_completion_lanes_free` proves it; binding ≈ 2^15.5; unrouted | `AttestedAutomatonLanes8.lean`: `MapOp.holdsAt8` (the `.mapOp` arm opens the full 8-felt group against the deployed `node8` tree), `rowAt8` (19-felt map row), `Satisfied2Lanes8` (= `Satisfied2Public` with those two legs swapped); routing entry + by-name artifact + Rust arm (see §1.1) | `weld8_forged_edge_refused`: a Lanes8-accepted trace whose public root commits `d` and claims `next ≠ d.step s y` must supply a 2^16-leaf heap behind the same 8-felt root reading the forged value, and `MapRootColl S8 16 mRow m` names the arity-16 chip collision. Falsifier: `weld_completion_lanes_not_free` (at the constant toy chip every root is zero, so arbitrary completion lanes do NOT satisfy), the exact flip of `weld_completion_lanes_free`, which still holds under the scalar denotation | `metatheory/Dregg2/Circuit/Emit/AttestedAutomatonLanes8.lean` |

Both are additive to shared files (no renamed declarations); every direct importer of `Dfa.lean`
was re-checked single-file. The shared `DescriptorIR2.MapOp.holdsAt` still denotes map ops at lane
0 for its 43 consumer files; moving it is the named flag day, after which `Satisfied2Lanes8` is
definitionally `Satisfied2Public`.

### 1.1 What "routed" means on the Rust side

See the Weld8 note and the commit series. The Lean denotation (`Satisfied2Lanes8`) is a model of
the deployed verifier; which lanes the deployed map-ops chip forces is a Rust fact recorded with
the routing commit, not inferred from Lean.

### 1.2 The one deployed carrier that already names the word

`DfaAcceptanceAir.lean` (the routing AIR the Rust `dfa-routing-toggle-2state::poseidon2-v1`
descriptor realizes) binds the word through its hash chain: `running_{i+1} = compress running_i
(hash4 state sym next 0)` seeded at `tableCommitment` and pinned at `routeCommitment` [READ,
`:135-178`]. Its soundness `dfaAir_verify_sound` concludes `∃ rows, Satisfies … ∧ finalState =
classify d (symbols rows)` [READ, `:526`]; the word is `symbols rows` and the chain ties it to the
public `routeCommitment`, but the statement does not say so explicitly. The explicit corollary
("`routeCommitment` = the chain over `symbols rows`") is a cheap follow-up; `Dfa.lean`'s
`BoundStatement` is the abstract shape it should refine.

---

## 2. The zoo: families, status, per-symbol cost

Per-symbol costs are for byte alphabets unless noted. "perms" are Poseidon2 permutations
(352 committed cells wide, 141 narrow [MEASURED]). The commitment column is the price of binding
the word to `c` once, shared by every statement over the same `c`.

| family | note | semantics object (Lean) | certificate shape | per symbol: rows / lookups / perms / degree | binds `c`? | status |
|---|---|---|---|---|---|---|
| DFA, public automaton | `01-dfa.md` | `Dfa.DfaAccepts`, `DfaAcceptanceAir.TableDfa` | replay row `(state, sym, next)`; table lookup or interpolant gate | 1 / 1 / 0 / 2 (table routing [MEASURED `DfaRoutingTableEmit`: 3 cols, 4 constraints]); 1 / 2 chip / 2 / 7 (hash-chained routing [MEASURED `DfaRoutingGeneralEmit`: 22 cols, 14 constraints]) | abstract: yes (today); routing AIR: via `routeCommitment` chain | built; bound statement landed |
| DFA, committed (attested) automaton | `01-dfa.md` §weld | `TableDfa` under `CommitsAutomaton8By` | replay row + one map-op read per row against the automaton's 8-felt root | 1 / 1 map-op / 16 chip rows / 2 [MEASURED `AttestedAutomatonWeld8`: 11 cols, 20 constraints, 10 PIs, 2611 wire bytes constant] | automaton: yes (8 felts, today); word: no (follow-up: route commitment over the rows) | built; denotation landed today |
| symbolic / predicate automata, Boolean-closed derivatives | `02-derivatives.md` | `Deriv.PredRE` (`ε, sym φ, alt, inter, cat, star, neg`), `derives`, `Matches` | the derivative table (states = ACI-normal derivatives) compiled to a DFA; the run is the DFA certificate | as DFA, after a per-regex table compile; table size ≤ `der_finite`'s bound | as DFA | built (Lean: `correctness`, `derives_neg`, `der_finite`, `tableDfa_faithful` with its agreement premise); the Rust `Re::compile` is unproved against `determinizer_faithful` |
| NFA | `03-nfa.md` | mathlib `εNFA`/`NFA`; `Deriv.Thompson.thompson`, `determinizedTable` | (a) determinization certificate: the subset table, checked offline, run as DFA; (b) on-the-fly subset witness: a `Finset State` per row, checked by a lookup per NFA edge; (c) ZK-Email path certificate: one accepting path | (a) as DFA; (b) 1 row / ≤ `|δ|` lookups; (c) 1 row / 1 lookup; a single path certifies MEMBERSHIP for any NFA, never non-membership, and under ambiguity it fixes which captures are reported, not whether the word is accepted | as DFA | (a) proved in Lean (`thompson_recognizes`, `legacy_determinized_faithful_thompson`); (b), (c) proposed |
| visibly pushdown / nested brackets | `04-vpa-dyck.md` | `Cfg.Reference.dyck` (`S → [S] \| ε`: single nesting `[ᵏ]ᵏ`, NOT the Dyck language of all balanced strings — no `S → SS` rule [READ `Cfg.lean:141-162`]), `VpaAsCert.Vpa`, `VpaAccepts` | leftmost-derivation replay as a stack log with fixed depth 5; the overflow guards cap pushes at `k ≤ 3` [READ `DyckStackEmit.lean:35,288`] | ≈2 rows / 2 chip per row / ≈4 / gate degree 8 (the chip's S-box is 7) [MEASURED `DyckStackEmit`: 24 cols, 79 constraints, 4 PIs] | PIs exist (`table`, `route`); the theorem does not mention them | built for ONE finite-depth grammar; general VPA decidable (`VpaDecidable`) but no circuit |
| CFG, compact leftmost replay | `05-cfg.md` | mathlib `ContextFreeGrammar`, `CfgCompact.Replay` (`:48`), `ReplayAccepts` (`:60`) | O(tokens) rule sequence; stack replay | native Rust check today; in-circuit: as the bracket replay with a rule table lookup per rule row | word explicit in `compact_sound` (`:81`); no `c` | proved (`compact_sound`, `compact_to_chain` `:90`); circuit only for the bracket grammar |
| CFG, Earley/CYK certificates | `05-cfg.md` §compare | same | CYK: an `n×n×|N|` table with one check per (span, split, binary rule); Earley: item sets with predict/scan/complete rows (O(n²) for unambiguous, O(n³) worst) | CYK: `|R_bin|·(n³−n)/6` checks per word [INFERRED, lane A: 47.5M at `n = 256` for the 16-NT JSON normal form]; replay: `O(n)` rows | same | proposed; replay wins for unambiguous grammars by `n²`; CYK certifies REJECTION (no parse) for ARBITRARY grammars without a complement grammar, but for deterministic grammars (LL(1), visibly pushdown over tokens — JSON is both) a validated deterministic parser certifies rejection in `O(n)` rows, so CYK is the fallback, not the default |
| transducers / Mealy; tokenization and detokenization | `06-transducers.md` | proposed `Mealy State In Out`; BPE as a finite-state transducer (Cognetta-Okazaki) | the run row `(state, in, out, next)`; output word committed separately (`c_in`, `c_out`) | 1 / 1 / 0 (+2·n/8 perms for the two commitments) | both `c_in`, `c_out` | **not built** (census: no tokenizer certificate exists; `tokenizer/` is credential sealing) |
| tree automata over JSON/CBOR | `07-tree-automata.md` | proposed `TreeAut`; JSON Schema ≡ VPA (TACAS 2023) for the streaming form; modern JSON Schema exceeds tree automata (POPL 2024), so only the regular core is a tree-automaton language | serialized pre-order run = a VPA run over the byte stream; or a Merkleized AST with per-node lookups | as VPA; AST form: 1 node = 3 lookups + 2 permutations (17 input lanes exceed `CHIP_RATE = 16`) [INFERRED, lane A] | `c` of the serialization | proposed; the VPA route reuses `04` |
| weighted / counting automata | `08-weighted.md` | proposed `Weighted State Sym K` over a semiring `K`; Count=0 and budgets as weight-accumulation | run row + one accumulator column; `Count = 0` over a corpus is L2∘L3 (padded complement) | +1 column, +1 degree-1 gate per row for additive weights (degree 2 only for products) | as DFA | proposed; `audit::CountProof` exists in Rust and certifies even less than "≥ K distinct leaves": `global_index` is never tied to the inclusion path, `log_size` is unbound, and `count = 0` verifies for any token and root [READ, lane B] |
| timed automata (receipt windows) | `09-timed.md` | proposed `Timed` with clock valuations; one clock suffices for receipt windows | run row with a clock column; guards as range lookups (nibble table, 4 bits per lookup) | 1 row / `2·⌈bits/4⌉` range lookups per interval guard (two bounds) | timestamps from the MMR leaf (`c` of the receipt); the deployed `audit::RangeProof` never ties the timestamp to the leaf [READ, lane B]; Unix seconds exceed the BabyBear modulus on 2033-10-18 [INFERRED, lane B] | proposed |
| Büchi / ω-automata for streaming logs | `10-omega.md` | prefix semantics: `GoodPrefix`/`BadPrefix` of an ω-language; the MMR gives the prefix | the finite run over the committed prefix, plus the MMR non-omission proof that the prefix is the whole log | as DFA per entry + MMR opening per entry | the MMR root | proposed; composes with `MMR.lean` (`server_cannot_omit_position`) |
| register automata (session ids) | `11-register.md` | proposed `RegAut` over data words with `k` registers | run row with `k` register columns; equality guards as degree-2 gates; freshness via a sorted set opening | 1 row / `k` columns / 0 | as DFA | proposed; `k = 1` is the session-binding case |
| alternating automata (policy conjunction) | `12-alternating.md` | proposed `AFA` with `∧/∨` transition formulas; Jirásková: `m + n` states vs `m·n` product | one row per (position, active state) pair of a run DAG, or a product trace with `k` state columns | product: 1 row / `k` lookups; AFA DAG: ≤ `|Q|` rows per symbol | as DFA | proposed; Reef's SAFA is prior art for alternation in ZK |
| Datalog derivation (single firing) | `13-datalog.md` | `DerivationEmit` (one rule firing: head = `hash_fact`, body facts opened against `state_root`) | one descriptor per firing [MEASURED: 386 cols, 393 constraints, 13 PIs, degree 8] | n/a | `state_root` | built (one firing); fixpoint and Count are Part D |

### 2.0 Families and operators added after codex round 2 (`codex-synthesis.md` §2)

- **Weighted automata, general**: one accumulator prices a single deterministic path; a semiring
  sum over ALL accepting paths needs state-vector propagation (`|Q|` accumulator columns) or a
  certified aggregation, plus overflow handling for integer counts. Note `08` prices the
  deterministic case only.
- **Counter / Parikh automata**: bounded counters (quotas, balances, conservation) without
  blowing the counter into states: `k` counter columns with limb range checks (`2·⌈b/4⌉` nibble
  lookups per guard), not one unrestricted felt.
- **Two-way automata**: a head-position witness with authenticated reads; cost is the number of
  visited transitions, which can exceed `|w|`; the input commitment must be position-openable.
- **Shuffle / asynchronous product**: a selector column advances one component while the others
  stutter; interleaved protocols at `k` lookups per row, which synchronous intersection does not cover.
- **Intersection of CFL certificates**: two stack runs over one byte column certify `L₁ ∩ L₂`
  even though CFLs are not closed under intersection — closure of the LANGUAGE class is
  irrelevant to closure of the CERTIFICATE class (note `05` §composition overstated this).
- **Relational transduction / inverse images**: `parse(bytes) = tree ∧ schema(tree)` over one
  witness is sound for many-to-one parsing; JSON's non-injectivity only blocks recovering unique
  bytes from a tree commitment (note `07` overstated this).
- **Kleene star**: "no extra rows" hides the determinized table's growth; the alternative is a
  factor-boundary certificate with explicit empty-word handling.
- **Symbolic predicate automata**: evaluating the committed symbol's predicate / minterm class is
  additional per-symbol work (one lookup into the class table per byte, or a gate per predicate);
  "as DFA" prices only an already-encoded class stream (note `02`).

### 2.1 Reading the table

- **Only two families bind the word to a commitment in a theorem today**: the abstract DFA
  (after today's repair) and, implicitly, the routing AIR through its hash chain. Every other
  built family reads the word off the private trace. That is the single most important gap and
  the cheapest to close family by family: a route-commitment column (one arity-2 chip lookup per
  row, `+1` perm per symbol) or a shared content commitment opened by position.
- **The automaton is never the bill.** A table-routing DFA step is 3 cells and one lookup; the
  content commitment is 44 cells per byte. Two consequences: (i) product constructions that
  multiply state count are cheap in rows (one lookup per factor) and expensive only in table size;
  (ii) U3 (`PROOF-SYSTEM-SPACE.md`) is right that fusing a policy automaton into an inference
  prover's output boundary is free *if* the output cells are already committed, and the
  detokenizer is the real price.

---

## 3. Composition operators and their cost laws

Notation: `Cert(c, φ; ε)` is a certificate that the word behind `c` satisfies `φ`, with knowledge
error `ε`. `b` is the content scheme's binding advantage, `b_M` the MMR's. Costs are per word of
`n` symbols unless stated.

| operator | statement produced | rows / lookups | ε law | additive? |
|---|---|---|---|---|
| **product** `A₁ × A₂` (intersection of languages) | `Cert(c, φ₁ ∧ φ₂)` over one run | `n` rows with `k` state columns, `k` lookups per row; `TinyAutomataLanesK` declares one RUN table of `|w|` rows per lane (not `|Qᵢ|·|Σ|` transition tables), and the product-first run-table route is cheaper (area 24 flat vs 24/40/56/72 at `k = 1..4`) [READ, lane B] | `ε` of one proof: the run is ONE witness, so no `b` term | yes, trivially: one proof |
| **conjunction of two proofs** `Cert(c, φ₁; ε₁) ∧ Cert(c, φ₂; ε₂)` | `Cert(c, φ₁ ∧ φ₂)` | two proofs | `ε₁ + ε₂ + b` (L1) | **no** unless `b` is paid: the two extractors may return `w₁ ≠ w₂` with `commit w₁ = commit w₂ = c`; `zkOracle_sound` is exactly this shape without the `b` term [READ `ZkOracle.lean:90`, header says "three sound legs, not a proof they are one request"] |
| **concatenation** `L₁ · L₂` | `Cert(c, w ∈ L₁L₂)` | one run with a split position `i` as a hidden witness; a boundary row where `A₁` accepts and `A₂` starts: `+1` selector column, `+2` gates | one proof | yes |
| **Kleene star** `L*` | `Cert(c, w ∈ L*)` | the DFA of `L*` (via derivatives: `der a (star r) = cat (der a r) (star r)`, finite by `der_finite`); no extra rows | one proof | yes |
| **complement** `¬L` | `Cert(c, w ∉ L)`; **absence** is `¬(any*·P·any*)`, not `¬P` (L3) | the complement DFA has the same table size (swap accept set); rows unchanged | one proof; **soundness needs totality of the DFA** (every `(q, a)` has an edge), which `TableDfa.step` gives by type | yes |
| **weld to commitment** (bind the run to `c`) | turns a trace-private word into `Cert(c, φ)` | `+1` arity-2 chip lookup per row (route chain) or `n/8` perms once if `c` is a sponge over the word and the run opens it by position | `ε + b` | the `b` is paid here, once, and then shared by every conjunct over `c` |
| **MMR aggregation** over `N` records (L2) | `AllRecords(R, N, φ)` | `N` certificates + `N` MMR openings (`log N` compressions each) | `N·ε + b_M + b` (union bound) | yes, but linear in `N`; the `N·ε` is what recursion removes |
| **recursion / folding** over the aggregation | same, one proof | one wrap per fold step; `recursion_tower_profile` is the unmeasured decision number [READ, synthesis §hbox 1] | `ε_engine` (the `EngineSound` hypothesis, `RecursiveAggregation.lean:121`), named and inhabited only by `real_engine_sound`'s satisfiability | **not additive in the naive sense**: Fiat-Shamir randomness is shared across the fold, so the error is the accumulation-depth bound, not a sum (`Selvage/Depth.lean`, `(t+k)ε`) |
| **automaton fused into another statement's trace** (U3) | `Produced(m, c_in, c_out) ∧ φ(out)` as ONE relation | `+1` lookup per output cell against the policy table; no second commitment, no bridge | `ε_inf` only, no `b` (one witness) | yes; and it is the only composition with zero binding cost, because the output cells are the witness |
| **transducer chain** `T₂ ∘ T₁` (tokenize then classify) | `Cert(c_in, φ(T(w)))` | two runs sharing the intermediate word as a hidden witness column; `+1` commitment if the intermediate is exposed | one proof | **order-dependent**: `T₂ ∘ T₁ ≠ T₁ ∘ T₂`, and a BPE transducer is not functional on arbitrary inputs (several tokenizations of one string), so the certificate must fix the canonical one (Cognetta-Okazaki) or soundness is "some tokenization", not "the tokenization" |

### 3.1 Where additivity fails, named

1. **Shared commitment without binding** (L1 without `b`): `zkOracle_sound` today. Repair: thread
   `bindAdv` (CERTIFICATES P1, P5).
2. **Shared randomness** (recursion, folding, any two statements proved under one Fiat-Shamir
   transcript): a union bound still applies (union bounds need no independence; codex round 2
   corrected the earlier wording), but each per-statement `ε` must be justified in the JOINT,
   adaptive experiment, not taken from its standalone analysis; the accumulation-depth bound
   (`Selvage`'s `(t+k)ε`) is that justification, and recursion does not remove accumulated error
   by itself — `ε_engine` must bound it.
3. **Order-dependent transducers**: tokenization is not functional unless canonicalized;
   detokenization is functional. U3 needs detokenization (tokens → bytes) and can get away without
   tokenization; that is why the detokenizer is the cheaper object (note `06`).
4. **Commitment-scheme morphisms** (L5): transporting a certificate across schemes adds
   `b_S + b_S'`, and if the morphism is not injective on the padded encoding (the `PadGhost3`
   wound in `heap_root.rs` [READ census]) the transport is unsound regardless of `ε`.

---

## 4. Part D: what to build, and why Datalog fixpoints over an MMR-committed EDB

Candidates: (a) a positive-Datalog least-fixpoint certificate over an MMR-committed EDB with a
Count query; (b) the detokenization transducer for U3.

**Choice: (a).** Reasons:
- It joins three things this tree already has and never composed: `DerivationEmit` (one rule
  firing, built, 386 columns), `MMR.lean` (non-omission over a committed log, built), and
  `dregg-query`'s CALM classification (monotone vs finalized-dependent, built, no recursion). The
  gap it closes is exactly the one the census names: "no recursion", and "Count is certified by
  recomputation, not as a statement".
- It is evaluable at L2 in Lean alone: a semi-naive trace is an executable certificate, the
  checker is a Lean function, the soundness theorem (every fact in the trace is in the least
  fixpoint) and the closure theorem (a closed trace IS the fixpoint, so Count is exact) are
  statements with inhabited hypotheses and a concrete falsifier (an open trace whose Count is
  wrong).
- The detokenizer (b) is cheaper to arithmetize but has no consumer until an inference prover
  exposes its output boundary (U3 is "unoccupied" because no prover does); it would be a
  certificate with no statement to join. It stays the first follow-up.

The object lands as a new module `Dregg2.Datalog.FixpointCert` (statement, checker, theorems,
`#guard` counts on a transitive-closure instance over an MMR-committed edge list). Its note is
`13-datalog.md`.

---

## 5. The five richest extensions per felt (from `SEMANTIC-CEILING.md`, ranked)

1. **Route-commitment column for every built replay family** (DFA table routing, Dyck, attested):
   `+1` arity-2 chip lookup per row; turns every "word read off the trace" theorem into a
   content-bound one. Milestone: `tableRouting_refines_classify` restated with a `c` conjunct and
   the splice falsifier, `#guard` on the wire delta.
2. **Datalog positive fixpoint + Count over an MMR EDB** (Part D). Milestone: L2 in Lean; L3 is
   the firing AIR iterated under a fold, measured on hbox.
3. **Alternating-automaton policy conjunction** (one run, `m + n` states): a product witness with
   `k` lookups per row is the deployed shape (`TinyAutomataLanesK`); the AFA run-DAG form wins
   only when obligations are sparse: with `s̄` live obligations per symbol and clause width `w`,
   it wins in cells iff `(5 + w)·s̄ < 2k + 1` and in lookups iff `(3 + w)·s̄ < k` [INFERRED, lane B];
   for a conjunction of always-live DFAs it never wins. Milestone: a 3-policy conjunction at
   `k = 3` with pinned counts for the three routes (lanes 7 cells / 3 lookups, product-first 3 / 1,
   DAG predicted 18 / 12).
4. **Rejection certificates for grammars**: a validated deterministic parser (LL(1) / visibly
   pushdown over tokens; JSON is both) certifies "does not parse" in `O(n)` rows; CYK
   (`|R_bin|·(n³−n)/6` checks) is the fallback for arbitrary grammars. Milestone: the JSON-subset
   deterministic rejection certificate at `n = 256` with counts, and the CYK number beside it as
   the price of generality.
5. **LRAT checking in-AIR** (the SMT-shaped family with the best richness per felt): one resolution
   step is a clause lookup plus a pivot check; ZKUNSAT (2022/206) and normalized chaining
   (2609.19353) are the prior art. Milestone: a verified LRAT checker as a Lean function first
   (there is none in this tree), then its AIR.

---

## 6. Discipline

- No "first" claims: Reef (absence over committed documents), Coral (ZK CFG parsing), Crepe (ZK
  regex equivalence), ZKUNSAT, Tantow et al. (Lean Datalog certificate checking), Ramos et al.
  (verified egg-explanation checking) are all prior and cited in the notes. What the notes may
  say is ours: machine-checked complement compilation, the `bindAdv` accounting, L2∘L3 absence
  over a non-omission log, and the lane-complete weld. See `PRIOR-ART` in `codex-synthesis.md`
  for the search log (38 queries; "no hit" is never "none exists").
- Every proposed family's soundness statement is written in Lean syntax in its note with a
  falsifier, before any AIR is emitted for it. A note that lacks a falsifier is not done.
