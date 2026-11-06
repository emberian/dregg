# DFA (public automaton, and committed "attested" automaton) — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned `#guard` or a run; [CLAIM] asserted elsewhere;
[INFERRED] derived here. Metatheory root `M = /Users/ember/dev/breadstuffs/metatheory/Dregg2`.

## 1. Semantics object (Lean)

Two objects, two uses.

- Relational, abstract (the statement algebra) [READ `M/Crypto/Dfa.lean:48,74`]:
  ```lean
  structure Step (State Sym : Type u) where state : State; sym : Sym; next : State
  def DfaAccepts (δ : State → Sym → State → Prop) (q₀ : State) (accept : State → Prop)
      (trace : List (Step State Sym)) : Prop :=
    ∃ first last, trace.head? = some first ∧ trace.getLast? = some last ∧
      first.state = q₀ ∧ accept last.next ∧ (∀ s ∈ trace, stepValid δ s) ∧ chained trace
  def traceWord (trace : List (Step State Sym)) : List Sym := trace.map (·.sym)   -- new today
  ```
- Functional, total (the circuit's object) [READ `M/Crypto/DfaAcceptanceAir.lean:81,91`]:
  ```lean
  structure TableDfa (State Sym : Type u) where
    step : State → Sym → State; start : State; accepts : State → Prop
  def classifyFrom (d : TableDfa State Sym) (q : State) : List Sym → State
    | [] => q | y :: ys => classifyFrom d (d.step q y) ys
  ```
  Totality of `step` is what makes complement sound (swap the accept set; no missing edge can
  reject by absence of a row). `TableDfa.lean:110 tableRun_dfaAccepts` bridges the two for
  non-empty words [READ].

## 2. Certificate shape

Public `x = (q₀, q_final, c)` plus, for the attested variant, the automaton's 8-felt root `R8`.
Witness `w` = the replay: one row per symbol `(current, symbol, next)`; the word is the `SYMBOL`
column. Three deployed shapes:

| shape | file | how the transition is enforced |
|---|---|---|
| table routing | `M/Circuit/Emit/DfaRoutingTableEmit.lean` | one lookup per row into an `exactPublicRows` table whose rows ARE the descriptor bytes (`(s, y, step s y)`) |
| hash-chained routing | served: `M/Circuit/Emit/DfaRoutingEmit.lean` (2-state toggle, `dfa-routing-toggle-2state::poseidon2-v1`, narrow chip); also `M/Circuit/Emit/DfaRoutingGeneralEmit.lean` (3-state injection, `dfa-routing-injection-3state::poseidon2-v1`, wide chip, not routed by name [READ `circuit/src/descriptor_by_name.rs:83`]); both modelled by `DfaAcceptanceAir.lean` | a bivariate interpolant gate for the transition, plus a per-row entry hash and a running hash seeded at the table commitment and pinned at `routeCommitment` |
| attested (committed automaton) | `M/Circuit/Emit/AttestedAutomatonWeld8.lean` + `AttestedAutomatonLanes8.lean` | one map-op READ per row against the automaton's root: key `2·current + symbol ↦ next` |

## 3. Arithmetization and counts

| shape | columns | PIs | constraints | per symbol: rows / lookups / perms | degree | wire bytes | source |
|---|---|---|---|---|---|---|---|
| table routing | 3 | 2 | 4 | 1 / 1 table / 0 | 2 | golden pinned (`:536`) | [MEASURED `DfaRoutingTableEmit.lean:540-543`] |
| hash-chained routing, toggle (served) | 8 | 4 | 14 | 1 / 2 chip (narrow) / 2 (×141 cells) | 7 (S-box) | byte-pinned | [MEASURED `DfaRoutingEmit.lean:275-277`] |
| hash-chained routing, injection (emitted, not routed) | 22 (8 base + 2×7 chip lanes) | 4 | 14 | 1 / 2 chip / 2 (×352 cells wide) | 7 (S-box) | byte-pinned `:225` | [MEASURED `DfaRoutingGeneralEmit.lean:272-278`] |
| attested, scalar root | 4 | 3 | 6 | 1 / 1 map-op (5 felts) / 16 chip rows + 1 leaf digest | 2 | 1205 | [MEASURED `AttestedAutomatonEmit.lean:1171-1212`] |
| attested, 8-felt weld, graduated (served) | 11 | 10 | 22 | 1 / 1 map-op (19 felts deployed) + 2 range lookups / 16 chip rows + 1 leaf digest | 2 | 2803 | [MEASURED `AttestedAutomatonWeld8.lean:943-957`] |

Table sizes: table routing ships `|Q|·|Σ|` rows in the descriptor (one object per automaton); the
attested shape ships ZERO rows and one `2^16`-leaf map root (`ASTATES = 32768`, `ASYM = 2`,
`NKEYS = 65536 = 2^MAP_TREE_DEPTH` [MEASURED]). Main-trace area: `3·|w|` / `22·|w|` / `4·|w|` /
`11·|w|`.

**Weld graduation (2026-11-06).** The v2 assembly refuses a descriptor with a non-empty `ranges`
carrier, so the weld's two teeth (`CURRENT < 2^15`, `SYMBOL < 2`) became lookups into the served
`range_w15` (wire id 84) and `range_w1` (wire id 70) tables; no limb split was needed because a
15-bit table exists, so the Lean main trace gains no column. Delta against the ungraduated weld
[MEASURED, `#guard`]: columns 11 → 11, PIs 10 → 10, constraints 20 → 22, tables 1 → 3, wire bytes
2611 → 2803 (+192), byte crossover against the run table `|w| = 201 → 220`. The kept tooth is
`weld_lookups_bound` / `lanes8_row_bounded` (faithful range tables ⇒ every accepted row is in
domain) with the falsifier `weld_range_refuses_out_of_domain`. Served:
`circuit/tests/weld8_served.rs` loads it through `descriptor_by_name`, passes
`check_descriptor2_wellformed`, proves and verifies an 8-symbol run of a 3-state automaton
committed in the 8-felt map tree (debug profile on the Mac: prove 1178 ms, verify 35 ms, 4 batch
instances, degree bits `[3, 5, 4, 3]` [MEASURED]), and refuses the Lanes8 forgery shape
(`forgeD` committed, `forgeE` run) at the pre-flight and, with the pre-flight bypassed, at the
`ir2_p2` chip bus. ⚠ Residual found on contact: the deployed indexed-Merkle tree reserves key `0`
(edge `(0, 0)`) as its MIN sentinel with value `0`, so an automaton is committable there only if
`step(0, 0) = 0`; the Lean model's dense `2^16`-leaf heap has no such side condition.

The commitment, the real bill: `c = hash_bytes_8(w)` is a rate-4 sponge over `bytes_to_lanes w`
(2 bytes per lane, 4 length lanes) [READ `circuit/src/poseidon2.rs:704`;
`sel4/dregg-pd/executor-pd/crypto-floor/src/field.rs:94`], i.e. `⌈(⌈n/2⌉ + 4)/4⌉ + 1 = ⌈n/8⌉ + 2`
permutations for `n` bytes (the `+1` is the squeeze permutation, `poseidon2.rs:430` [READ, codex round 2]), 352 committed cells each (wide) [MEASURED `Poseidon2RoundGates.lean`
`POSEIDON2_AUX_COLS == 352`] = **44 cells per byte** [INFERRED]. Against 3 main cells per byte for the table-routing run (the 11-column attested shape is
over binary symbols with 16 chip rows of map authentication per step; not a byte-step number). The hash-chained routing shape pays 2 permutations PER SYMBOL (704 cells),
which is 16× the sponge's per-byte price: it binds the word per row rather than once. That is
the wrong trade for long words and the right one when the word is short and the chain is also
the route commitment (the toggle descriptor's use).

## 4. Binding to the content commitment

| shape | bound? | how |
|---|---|---|
| table routing | **no** | `tableRouting_refines_classify` reads the word off the SYMBOL column [READ `:438-452`]; the table is bound by the descriptor bytes, the word by nothing |
| hash-chained routing | yes, implicitly | `routeCommitment = fold compress (compress tableCommitment h₀) …` over `hash4 (state, sym, next, 0)` [READ `DfaAcceptanceAir.lean:135-178`]; `dfaAir_verify_sound` [READ `:526`] concludes `∃ rows, Satisfies … ∧ finalState = classify d (symbols rows)` and the chain inside `Satisfies` ties `symbols rows` to the public `routeCommitment`, but no theorem states the equation `routeCommitment = routeOf (symbols rows)` explicitly |
| attested (scalar / weld) | automaton: yes; word: **no** | automaton at 1 felt (`root_binds_automaton`, hypothesis refuted at BabyBear) / 8 felts (`root8_binds_automaton_or_collides`, floor-free; the denotation routed through all lanes today, `Lanes8`); the word is the private SYMBOL column |
| abstract `Dfa.lean` | yes (today) | `BoundStatement.c`; `dfa_bound_verify_sound`, `dfa_bound_identifies_record_or_collides` |

The uniform repair (program doc §5.1): a route-commitment column (one arity-2 chip lookup per
row, `+1` permutation per symbol, 352 cells) or, cheaper for long words, a once-per-word sponge
`c` opened by position with one lookup per row into the lane table of `bytes_to_lanes w`.

## 5. Soundness statement (Lean syntax) and vacuity falsifier

Landed today [READ `M/Crypto/Dfa.lean`, Layer B′]:
```lean
theorem dfa_bound_verify_sound {State Sym D : Type} {S : ContentScheme Sym D}
    [K : DfaBoundVerifierKernel State Sym D S Proof]
    (hext : K.extractable) (stmt : BoundStatement State Sym D) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    ∃ w : List Sym, S.commit w = stmt.c ∧
      ∃ trace : List (Step State Sym),
        DfaAccepts stmt.δ stmt.q₀ stmt.accept trace ∧ traceWord trace = w

theorem dfa_bound_identifies_record_or_collides … (record : List Sym) (hrec : S.commit record = stmt.c) :
    ∃ trace, DfaAccepts stmt.δ stmt.q₀ stmt.accept trace ∧
      (traceWord trace = record ∨
        (traceWord trace ≠ record ∧ S.commit (traceWord trace) = S.commit record))
```
The second is the one that names THE record: either the run read it, or the extracted word is a
different preimage of `c` (the binding event, pinned to two concrete words; a computational
consumer bounds it by `bindAdv`). Law L0 met.

Falsifier [READ `Dfa.lean` `Reference`]: `splice_meets_unbound` (the record-ignoring acceptance
test — "the proof is an accepting run of `a⁺b`" — satisfies the unbound extract shape for every
`c`) and `splice_fails_bound` (at `c := [0x7a]`, identity scheme, with the `"aab"` run it accepts,
no satisfying trace reads `"z"`: `δ` has no `0x7a` edge). `splice_fails_bound_of_sep` is the
scheme-generic form. Codex round 1 confirmed the separation is genuine and scheme-relative.

For the deployed routing AIR the statement to add (cheap, next):
```lean
theorem route_commits_word … (h : Satisfies d encState encSym tableCommitment q₀ qf C rows) :
    C = routeOf encState encSym tableCommitment rows      -- the explicit chain over (state, sym, next)
```
with falsifier: a trace with one symbol replaced and the same `C` must violate `accum` (needs the
`CollisionFree` carrier the file already uses at `:298`).

For the attested weld the statement landed today [READ `AttestedAutomatonLanes8.lean` §4]:
```lean
theorem weld8_forged_edge_refused (S8 : Heap8Scheme) … (t : VmTrace)
    (h : Satisfied2Lanes8 S8 hash (weldDesc name) minit mfin maddrs t) (hcan : LaneCanonical t)
    (d : TableDfa Nat Nat) {m : Heap.FeltHeap} (hd : CommitsAutomaton8By S8 m (pubRoot t) d)
    (i : Nat) (hi : i < t.rows.length) (s y : Nat) (hs : s < ASTATES) (hy : y < ASYM)
    (hcur : (envAt t i).loc CURRENT = Int.ofNat s) (hsym : (envAt t i).loc SYMBOL = Int.ofNat y)
    (hbad : (envAt t i).loc NEXT ≠ Int.ofNat (d.step s y)) :
    ∃ mRow : Heap.FeltHeap,
      Heap.SortedKeys mRow ∧ mRow.length = 2 ^ MAP_TREE_DEPTH
        ∧ mapRoot8 S8 MAP_TREE_DEPTH mRow = pubRoot t
        ∧ Heap.get mRow ((keyOf s y : Nat) : ℤ) = some ((envAt t i).loc NEXT)
        ∧ MapRootColl S8 MAP_TREE_DEPTH mRow m
```
Falsifier: `weld_completion_lanes_not_free` and the characterization `lanes8_constChip_iff`
(at the constant chip, satisfaction ⇔ zero root); inhabitation of the forgery premises:
`weld8_forgery_premises_inhabited` (constant-0 automaton committed, constant-1 run accepted at the
same root). What is NOT claimed: the deployed padded occupancy model (`padImtRoot8`), an executable
heap extractor, a whole-run statement (see `codex-synthesis.md` round 1).

## 6. Composition behaviour

Product: `k` DFAs as `k` state columns and `k` lookups per row [MEASURED `TinyAutomataLanesK`];
one witness, no `b` term. Concatenation and star: by derivatives, no extra rows. Complement:
sound by totality of `step`; absence is the padded complement (L3). Weld: the route column (+1
perm/row) or the once-per-word sponge. MMR aggregation: `N·ε + b_M + b`. Where additivity fails
for this family specifically: two DFA proofs over one `c` without `b` (the `zkOracle_sound`
shape) and the hash-chained shape's `CollisionFree` carrier, which is an injectivity floor of the
kind `HashFloorHonesty` refutes at BabyBear [READ census §0]; the chain binds at the chip's
collision resistance, 8 lanes at `~2^123.6` only if all eight are carried (the toggle descriptor
carries `ENTRY_HASH`/`RUNNING_HASH` as single narrow-chip lanes, 8 columns in all [READ `DfaRoutingEmit.lean:241` golden]; the
injection object `DfaRoutingGeneralEmit` carries them as 1 + 7 lanes [READ its pins]).

## 7. Prior art

Reef (ePrint 2023/1886) [READ]: regex match AND non-match over a committed document, skipping
automata on Nova. ZK Email (2026/1284) [READ]: NFA path verification, linear in the path. Luo et
al. (2023/643) [READ]: oblivious NFA matching. Vega (2025/2094) [READ]: lookup-centric field
extraction without parsing. Not ours to claim: ZK regex membership or absence. Ours: the bound
statement with a named record-or-collision disjunct, the lane-complete committed-automaton weld,
and the per-byte cost law (hash dominates).

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| `DfaAccepts`, `dfa_bridge`, `dfa_bound_verify_sound`, `dfa_bound_identifies_record_or_collides`, splice falsifiers | `Dfa.lean` | L1 (statement + proof; kernel OPEN) |
| table routing descriptor + `tableRouting_refines_classify` | `DfaRoutingTableEmit.lean` | L3 (emitted, witness, refinement) — word unbound |
| hash-chained routing + `dfaAir_verify_sound` | `DfaRoutingEmit.lean` (served toggle), `DfaRoutingGeneralEmit.lean` (injection, not routed), `DfaAcceptanceAir.lean` | L4 for the toggle (deployed as `dfa-routing-toggle-2state::poseidon2-v1`) — word bound by chain, not stated |
| attested weld, 8 lanes: `Satisfied2Lanes8`, `weld8_forged_edge_refused`, graduated range lookups, served | `AttestedAutomatonWeld8.lean`, `AttestedAutomatonLanes8.lean`, `descriptor_by_name.rs`, `circuit/tests/weld8_served.rs` | L4 (emitted + witness + binding, proved and verified by the v2 assembly); dense model, sentinel residual |
| `route_commits_word` for the routing AIR | proposed | L1, one afternoon |
| route column for table routing / attested | proposed | L3; milestone: `#guard` the wire delta (+1 chip lookup tuple per row = +25 wire felts per row [INFERRED from `CHIP_TUPLE_LEN = 25`]) and restate `tableRouting_refines_classify` with a `c` conjunct and the splice falsifier |
