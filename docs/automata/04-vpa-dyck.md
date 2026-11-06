# Visibly pushdown automata and the Dyck replay circuit — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned #guard or a run; [CLAIM] asserted elsewhere; [INFERRED] derived here.

Hub: `AUTOMATA-ARITHMETIZATION-PROGRAM.md` §2 row "visibly pushdown / Dyck". M = `/Users/ember/dev/breadstuffs/metatheory/Dregg2`.

Two objects share this family and they are not the same object. `VpaAsCert`/`VpaDecidable` define
and decide general VPAs and have no circuit. `DyckStackEmit` is a deployed circuit for one grammar,
and it is a leftmost-derivation replay (a CFG certificate, `05`), not a VPA run. Below, §3 shows that
the grammar it targets is `{[ᵏ ]ᵏ}`, not the Dyck language. With the descriptor's depth bound, the
circuit's language is finite.

## 2026-11-06 record-binding repair (initiative 1)

[READ] `DyckStackBound.boundAccepts_sound` now binds one proof trace to the caller's
record. It recomputes canonical rule/terminal entry preimages and deterministic
power-of-two padding, and checks the route and main-row count. Its conclusion is
record equality plus grammar replay, or the named `recordFind` collision on those
two actual chains. It needs no reference trace or globally injective hash. The
first-done row and live prefix are derived from the record encoding. Residuals are
chip soundness/wiring, field and PI canonicality, initial S and core length < p.
The older globally injective `dyck_bound` remains an explicitly ideal lemma;
`dyck_bound_or_collides` supplies its named-collision replacement.

[READ] The served descriptor gains two inverse-selector gates and four last-row
zero boundaries: ordinary gates skip the final row although the hash lookups do
not. Width stays 24, public inputs stay four, constraints increase **79 → 85**,
and hashes stay two per row. `DyckStackEmit.constraint_count` is a named kernel
fact. `fullWit_satisfies`, `fullWit_record_fires` and the exact collision-exclusion
lemma jointly instantiate the full statement; a route-only forgery has weak
acceptance, full-descriptor refusal, and inhabited chip/canonicality envelopes.

[READ] `circuit::dsl::dyck_stack::verify_record` computes public inputs from the
record and checks the proof's main degree against its expected padded height.
The Rust codec/Lean encoding correspondence is tested on shipped words, not yet
an extraction theorem. Canonical padding requires a successor after the first
done: `[ ]` stays eight rows (16 permutations); `[[ ]]` changes eight → sixteen
rows (16 → 32 permutations). This is a deliberate cost for meeting the current
replay theorem's successor envelope; removing that envelope would recover the
old eight-row nested trace. The raw descriptor interface remains available;
record-binding claims belong to the record-facing verifier.

The sections below retain the original survey's broader VPA/design discussion;
its projection-only milestone is superseded by the binding repair above.

## 1. Semantics object (Lean)

General VPA, `M/Crypto/VpaAsCert.lean` [READ], verbatim (doc comments elided):

```lean
-- :65
inductive Sym | op | cl | dat
  deriving DecidableEq, Repr

-- :112
structure Vpa (State Gamma : Type u) where
  call : State → Sym → State → Gamma → Prop
  ret : State → Sym → State → Gamma → Prop
  int : State → Sym → State → Prop

-- :151
def VpaAccepts (M : Vpa State Gamma) (q₀ : State) (accept : State → Prop)
    (run : List (VStep State Gamma)) : Prop :=
  ∃ first last : VStep State Gamma,
    run.head? = some first ∧
    run.getLast? = some last ∧
    first.pre.state = q₀ ∧
    first.pre.stack = [] ∧
    accept last.post.state ∧
    last.post.stack = [] ∧
    (∀ s ∈ run, stepValid M s) ∧
    vchained run

-- :320
theorem stack_height_input_determined (M : Vpa State Gamma)
    (run₁ run₂ : List (VStep State Gamma))
    (hval₁ : ∀ s ∈ run₁, stepValid M s) (hch₁ : vchained run₁)
    (hval₂ : ∀ s ∈ run₂, stepValid M s) (hch₂ : vchained run₂)
    (f₁ l₁ f₂ l₂ : VStep State Gamma)
    (hh₁ : run₁.head? = some f₁) (hl₁ : run₁.getLast? = some l₁)
    (hh₂ : run₂.head? = some f₂) (hl₂ : run₂.getLast? = some l₂)
    (hword : run₁.map (fun s => s.sym) = run₂.map (fun s => s.sym))
    (hinit : f₁.pre.stack.length = f₂.pre.stack.length) :
    l₁.post.stack.length = l₂.post.stack.length
```

The language, `M/Crypto/VpaDecidable.lean:70`:
`def Lang (M : Vpa State Gamma) (q₀ : State) (accept : State → Prop) (w : List Sym) : Prop := ∃ run, VpaAccepts M q₀ accept run ∧ run.map (fun s => s.sym) = w` [READ].
Determinization, `:1371 def detVpa : Vpa (Finset (S × S)) (Finset (S × S))` (Alur–Madhusudan summaries).
Equivalence, `:1624` [READ]:

```lean
def decidable_template_equivalence
    [DecidableEq S₁] [Fintype S₁] [Fintype G₁] [DecidableEq S₂] [Fintype S₂] [Fintype G₂]
    (M₁ : Vpa S₁ G₁) (q₁ : S₁) (acc₁ : S₁ → Prop) [DecidablePred acc₁]
    (M₂ : Vpa S₂ G₂) (q₂ : S₂) (acc₂ : S₂ → Prop) [DecidablePred acc₂]
    [∀ q s q' γ, Decidable (M₁.call q s q' γ)] [∀ q s q' γ, Decidable (M₁.ret q s q' γ)]
    [∀ q s q', Decidable (M₁.int q s q')]
    [∀ q s q' γ, Decidable (M₂.call q s q' γ)] [∀ q s q' γ, Decidable (M₂.ret q s q' γ)]
    [∀ q s q', Decidable (M₂.int q s q')] :
    Decidable (∀ w, Lang M₁ q₁ acc₁ w ↔ Lang M₂ q₂ acc₂ w)
```

It is a `def` (a decision procedure), computable, and EXPTIME: the determinized state space is
`Finset (S × S)`, so `2^(|S|²)` states. That is `512` at `|S| = 3`, `65,536` at `|S| = 4` and
`2^25 = 33,554,432` at `|S| = 5` [INFERRED]. It is an offline, public equivalence check between two
templates. It is not a certificate, and there is no circuit for it.

Three limits of this object:

- **One call symbol.** `Sym` is fixed to `op | cl | dat`. JSON needs two call symbols (`{`, `[`) and two
  return symbols, so that `[}` is refused. A VPA over this `Sym` cannot tell them apart, because the
  pushed `γ` can depend only on `(state, op)`. The repair is a partitioned alphabet (proposed):
  ```lean
  structure VAlphabet where
    Call : Type
    Ret  : Type
    Int  : Type
  abbrev VAlphabet.Sym (A : VAlphabet) := A.Call ⊕ A.Ret ⊕ A.Int
  structure VpaOver (A : VAlphabet) (State Gamma : Type u) where
    call : State → A.Call → State → Gamma → Prop
    ret  : State → A.Ret → State → Gamma → Prop
    int  : State → A.Int → State → Prop
  ```
  `stack_height_input_determined`, `detVpa` and `decidable_template_equivalence` then need re-proof
  over `VpaOver`. They dispatch on `classOf`, which `VAlphabet.Sym` gives by its constructor.
- **No empty word.** `VpaAccepts` requires a non-empty run, so `[] ∉ Lang M q₀ acc` for every `M`.
- **Finite alphabet only.** The infinite `Value` alphabet is out of scope (`VpaDecidable` header [READ census]).

The deployed circuit's target, `M/Crypto/Cfg.lean:141-162` [READ]: `inductive Brk | op | cl`,
`rBracket : S → [ S ]`, `rEmpty : S → ε`, `def dyck : ContextFreeGrammar Brk := ⟨NTs, NTs.S, {rBracket, rEmpty}⟩`.
With no `S → S S` rule this generates `{[ᵏ ]ᵏ | k ≥ 0}`, not the Dyck language: `[][]` is not in it
[INFERRED from the two rules]. The hub calls this object "Dyck" and so does the descriptor. The name
is inherited, and the language is the textbook `aⁿbⁿ`.

## 2. Certificate shape

**Deployed (`dregg-dyck-parse-v1`).** A leftmost-derivation replay laid out as a stack log. Public
`x` = `[PI_INITIAL, PI_INPUT_LEN, PI_TABLE, PI_ROUTE]` (`DyckStackEmit.lean:173-179` [READ]). The witness
is the trace: per row, a fixed-depth stack `STACK[0..4]`, depth, selectors `IS_RULE/IS_TERM/IS_DONE`,
`RULE_ID`, `INPUT_TOKEN`, `INPUT_POS`, `ENTRY_HASH = P2(RULE_ID, STACK0, INPUT_TOKEN, 0)`, and
`RUNNING_HASH = P2(ACC, ENTRY_HASH)` with `ACC` seeded at `PI_TABLE` (`seedAccPin`, :361) and the
last row's `RUNNING_HASH` pinned to `PI_ROUTE` (:461) [READ]. The word is the sequence of consumed
terminals on `term` rows. It is **not public** and is **not committed by any `c`**. `PI_ROUTE` commits
the `(rule, top, token)` sequence: a commitment to the derivation, which determines the word.

**Proposed (general VPA run).** One row per input symbol, with the stack held in memory instead of
columns:

| column | meaning |
|---|---|
| `q`, `a`, `cls`, `q'` | control state, symbol, its class, next state |
| `γ` | pushed symbol (call) or popped symbol (return) |
| `ptr`, `ptr'` | row index of the call matching the current stack top, before and after |
| `prev` | on a call, the old `ptr`, stored with the pushed record |

A call at row `s` writes the record `(s, γ, prev = ptr)` and sets `ptr' = s`. A return reads the
record at key `ptr` and sets `ptr' = prev`. An internal symbol copies `ptr`. Records are keyed by the
row index of their call, so each key is written once and read once. A LogUp multiset argument
(`+1` on write, `−1` on read) then forces each return to read exactly the record its matching call
wrote. Matching on `(height, γ)` alone is unsound: two pushes at one height at different times can
be swapped [INFERRED].

## 3. Arithmetization and counts

**Deployed Dyck descriptor** [MEASURED `DyckStackEmit.lean:629-641`]:

```
#guard dyckParseDesc.traceWidth == DYCK_WIDTH          -- DYCK_WIDTH = 24
#guard dyckParseDesc.piCount == 4
theorem constraint_count : dyckParseDesc.constraints.length = 85 := rfl
#guard DYCK_WIDTH + 2 * (CHIP_OUT_LANES - 1) == 38
```

Two narrow-chip lookups per row: arity 4 `(RULE_ID, STACK0, INPUT_TOKEN, 0)` and arity 2
`(ACC, ENTRY_HASH)`, each of tuple length `CHIP_RATE + 1 + 1` [MEASURED, same block]. Fixed stack depth
`STACK_D = 5` (:117) [READ].

Rows for the word `[ᵏ ]ᵏ`: `k` `rBracket` rows, one `rEmpty` row, `2k` `term` rows and one `done` row,
so `3k + 2` [INFERRED]. At `k = 1` that gives 5, which matches the pin
`#guard (decodeRun [op, cl] witTrace 5).length = 5` [MEASURED `DyckStackReplay.lean`, §6 guards]. Per
token: `(3k + 2)/(2k)` rows, which is 2.5 at `k = 1` and 1.83 at `k = 3`. Permutations per token:
`2(3k + 2)/(2k)`, which is 5 at `k = 1` and 3.67 at `k = 3` [INFERRED].

**The depth bound makes the language finite.** `bracketOverflowGuards` (:293) forces
`SEL_BRACKET · (STACK[3] − EMPTY) = 0` and the same for `STACK[4]` [READ]: an `rBracket` row needs
depth ≤ 3. Before the `j`-th nested `rBracket` the stack is `[S, cl^(j−1)]`, depth `j`. So `j ≤ 3`, and
the descriptor accepts `[ᵏ ]ᵏ` only for `k ≤ 3`: a language of at most four words, the longest of
length 6, in at most 11 rows [INFERRED from the guard and the two rules; no test pins it]. A finite
language is regular, so this circuit exercises no pushdown power. It is a sound replay of a CFG
derivation at bounded depth, which is what it was built to show.

**Degree.** `nonEmptyBelowBody 4` (:256, used in `occupancyTooth` :402) is a cubic in `STACK[4]` times
five linear factors in `STACK_DEPTH`, so degree 8. The depth range `∏_{v=0}^{5}(depth − v)` is degree 6
[INFERRED from the expressions; no degree pin in the file]. The hub's "degree 7" is the Poseidon2 chip's
`max_constraint_degree = 7` [READ census], not this descriptor's main-trace maximum.

**Proposed general VPA run**, per symbol [INFERRED]: 1 row; about 8 main columns (`q, a, cls, γ, ptr, ptr', prev, q'`)
plus LogUp auxiliaries; 1 transition-table lookup (arity 5: `(q, a, γ, q', cls)`) and 1 memory
multiset entry; 0 permutations; max degree 2 (class-gated copies). The depth is unbounded, and the cost
does not depend on depth. Compare the fixed-column shape, which pays `D` stack columns and `O(D)` shift
gates per row and refuses depth `> D`.

**Commitment cost:** `n/8` permutations for `n` bytes = 44 committed cells per byte at 352 cells
[READ `circuit/src/poseidon2.rs:704`, `crypto-floor/src/field.rs:94`; MEASURED `POSEIDON2_AUX_COLS == 352`].
The Dyck descriptor spends 2 permutations per row on its route chain, i.e. `2 · 352 = 704` committed
chip cells per row at the wide arm [INFERRED], already 16× the content-commitment cost per byte. The
route chain duplicates the binding work: if `c` is computed in-circuit over the term-row tokens, the
route chain could go (the table seed moves to a PI-pinned constant), and the per-row hash bill would
drop from 2 permutations to the `1/8` per byte of the sponge [INFERRED].

## 4. Binding to the content commitment

**NOT BOUND.** The theorem reads the word off the trace and does not mention any public input other
than `PI_INITIAL`. `M/Circuit/Emit/DyckStackReplay.lean:934` [READ], verbatim:

```lean
theorem parse_sat_imp_replay_emit_unconditional {hash : List ℤ → ℤ} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t) (hcanon : DyckCanon t)
    (n : Nat) (hn : n + 1 < t.rows.length) (hnp : n < 2013265921)
    (hpi : t.pub PI_INITIAL = SYM_S)
    (hdone : (envAt t n).loc IS_DONE = 1)
    (hlive : ∀ i, i < n → (envAt t i).loc IS_DONE = 0) :
    ReplayAccepts dyck (rulesOf (decodeRun (decodedWord t n) t (n + 1))) (decodedWord t n)
```

`decodedWord t n := decodeWordSeg t 0 n` (:776), the `term` rows' stack tops [READ]. `PI_INPUT_LEN`,
`PI_TABLE` and `PI_ROUTE` are absent from the statement, so it violates L0. `DyckCanon t` (`DyckStackRefine.lean:379`)
is field canonicality of every cell.

Two binding legs are available, at different costs:

1. **Bind to the route commitment (no new AIR).** State what the descriptor already pins: `PI_INPUT_LEN`
   is the word's length and `PI_ROUTE` is the chain over the decoded rows. Then prove a route-binding
   lemma in the shape of `DfaAcceptanceAir.route_commitment_binds_trace` (:418), with a per-instance
   collision disjunct in place of its `CollisionFree` carrier. This gives a content scheme
   `c_route := PI_ROUTE` that commits the derivation and, through it, the word. A consumer whose `c`
   is `hash_bytes_8` of the bytes still needs a morphism (L5).
2. **Bind to `c` (new AIR leg).** Absorb `INPUT_TOKEN` of each term row into an in-circuit sponge whose
   output is pinned to 8 PIs `PI_C`. Cost: one permutation per 8 tokens (rate-4 absorb, 2 symbols
   per lane, as for bytes), plus the 8 PIs [INFERRED].

## 5. Soundness statement (Lean syntax) and its vacuity falsifier

Repaired statement, leg 1 (restates what the descriptor already enforces):

```lean
/-- The route chain the descriptor computes over rows `0..n`. -/
def dyckRoute (hash : List ℤ → ℤ) (seed : ℤ) (rows : List MRow) : ℤ :=
  rows.foldl (fun acc r => hash [acc, hash [r.ruleId, r.top, r.token, 0]]) seed

theorem parse_sat_imp_replay_routed {hash : List ℤ → ℤ} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash DyckStackEmit.dyckParseDesc minit mfin maddrs t) (hcanon : DyckCanon t)
    (n : Nat) (hn : n + 1 < t.rows.length) (hnp : n < 2013265921)
    (hpi : t.pub PI_INITIAL = SYM_S)
    (hdone : (envAt t n).loc IS_DONE = 1)
    (hlive : ∀ i, i < n → (envAt t i).loc IS_DONE = 0) :
    let w := decodedWord t n
    t.pub PI_INPUT_LEN = (w.length : ℤ) ∧
    t.pub PI_ROUTE = dyckRoute hash (t.pub PI_TABLE) (decodeRun w t (n + 1)) ∧
    ReplayAccepts dyck (rulesOf (decodeRun w t (n + 1))) w
```

(`MRow` is the decoded-row type of `decodeRun`, `DyckStackReplay.lean:150`; its field names here are
placeholders.) Repaired statement, leg 2 (content-bound, against an extended descriptor
`dyckParseBoundDesc` with 8 more PIs):

```lean
theorem parse_sat_imp_replay_bound {D : Type} (S : ContentScheme Brk D)
    (pubC : VmTrace → D)                       -- reads PI_C..PI_C+7
    (hS : ∀ t, Satisfied2 hash dyckParseBoundDesc minit mfin maddrs t →
             ∀ n, (envAt t n).loc IS_DONE = 1 → S.commit (decodedWord t n) = pubC t)
    ... (same hypotheses over dyckParseBoundDesc) ... :
    ∃ w, S.commit w = pubC t ∧ w = decodedWord t n ∧ w ∈ dyck.language
```

`hS` is the sponge-refinement lemma that leg 2's AIR must prove. It is a hypothesis here only to show
the shape. The conclusion names `c` and the word, so it meets L0. `w ∈ dyck.language` follows from
`ReplayAccepts` by `compact_sound` (`CfgCompact.lean:81`).

**Falsifier: the splice, transported from `Dfa.lean:513/520`.** `witTrace` satisfies every hypothesis
of `parse_sat_imp_replay_emit_unconditional` (`witTrace_replays_unconditional`, `DyckStackReplay.lean:954`),
and its conclusion mentions no record. So, with the identity scheme `S := ⟨id⟩` and the record
`c := [op, op]` (unbalanced, not in `dyck.language`), the old shape is met for that record:

```lean
theorem dyck_splice_meets_unbound :
    ∀ (c : List Brk), ReplayAccepts dyck (rulesOf (decodeRun (decodedWord witTrace 4) witTrace 5))
                                        (decodedWord witTrace 4) :=
  fun _ => witTrace_replays_unconditional

theorem dyck_splice_fails_bound :
    ¬ ∃ w, (⟨id⟩ : ContentScheme Brk (List Brk)).commit w = [op, op] ∧
           w = decodedWord witTrace 4 ∧ w ∈ dyck.language := by
  rintro ⟨w, hc, hw, _⟩
  -- hc : w = [op, op], hw : w = [op, cl] by `decodedWord_witTrace` (:948); `decide` closes it
```

A second falsifier, for the finite-language finding of §3: the prover's witness generator must refuse
`[[[[]]]]` (`k = 4`). The census names a Rust tamper suite (`circuit-prove/tests/dyck_parse_tamper.rs`,
not read). A pinned negative test there, together with a positive test at `k = 3`, would turn the
[INFERRED] bound into [MEASURED].

## 6. Composition behaviour

| operator | VPA (general) | deployed descriptor |
|---|---|---|
| product / intersection | closed: VPLs over one partitioned alphabet intersect by a product (stacks synchronize because heights are input-determined, `stack_height_input_determined`); `prodVpa` (`VpaDecidable.lean:106`, `:337 prodVpa_lang`) [READ census] | n/a (one grammar) |
| complement | closed (`complement_closure`, `VpaDecidable.lean:1607`), but through `detVpa`'s `2^(|S|²)` states, so an in-circuit rejection certificate is a determinized run and is affordable only for `|S| ≤ 3` or 4 | n/a |
| concatenation, star | closed for well-matched words | n/a |
| weld to `c` | `+n/8` perms for a sponge over the SYMBOL column | leg 1 (route PI, no AIR change) or leg 2 (sponge, §4) |
| MMR aggregation | as any certificate (L2) | yes, once bound |
| fusion with a DFA over the same word | a DFA is a VPA with internal-only moves: run both on one SYMBOL column, `+1` lookup per row, no `b` term | the Dyck replay rows are not one-per-symbol, so a fused DFA must read only `term` rows (gate by `IS_TERM`) |

Where additivity fails: `zkOracle_sound` conjoins a grammar leg and a guard leg over independent words
(`ZkOracle.lean:90` [READ census]). For the Dyck leg the fix is leg 2, so that both legs open one `c`
and L1 can pay `b` once.

## 7. Prior art

- Alur, Madhusudan, *Visibly Pushdown Languages*, STOC 2004 [RECALLED]: the determinization `detVpa` implements.
- Bruyère, Pérez, Staquet, *Validating Streaming JSON Documents with Learned VPAs*, TACAS 2023,
  arXiv 2211.08891 [READ]: every JSON Schema has an equivalent VPA (with key order fixed). This is the
  structured-data link, and it needs the partitioned alphabet of §1.
- Coral, ePrint 2025/1420 [READ]: ZK CFG parsing of a committed stream; the nearest ZK pushdown prior art.
- No hit for visibly pushdown automata in a circuit, with the query "visibly pushdown automata
  zero-knowledge proof JSON" (PRIOR-ART §3). That is "no hit", not "none exists".

Not claimed as ours: VPA theory, JSON-Schema-as-VPA (Bruyère et al.), ZK grammar parsing (Coral). The
Lean `decidable_template_equivalence` is a mechanization of Alur–Madhusudan.

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| `Vpa`, `VpaAccepts`, `stack_height_input_determined` | `VpaAsCert.lean:112, 151, 320` | L1, fixed 3-symbol alphabet |
| `detVpa`, `complement_closure`, `decidable_template_equivalence` | `VpaDecidable.lean:1371, 1607, 1624` | L1/L2 (computable, `#guard`ed on concrete machines per its docstring) |
| Dyck replay descriptor (`{[ᵏ]ᵏ | k ≤ 3}` [INFERRED]) | `DyckStackEmit.lean`, served by `descriptor_by_name` | L4 deployed |
| `parse_sat_imp_replay_emit_unconditional` | `DyckStackReplay.lean:934` | L1, violates L0 |
| `VAlphabet`/`VpaOver`, memory-stack VPA run | proposed | L0 |
| `boundAccepts_sound`, full-descriptor witness and weak/strong splice pair | `DyckStackBound.lean`; `dyck_stack::verify_record` | record-facing implementation, served tests pending |

**Milestone:** prove `parse_sat_imp_replay_routed` (leg 1, no descriptor change) with the splice pair
`dyck_splice_meets_unbound` / `dyck_splice_fails_bound`, and pin the depth finding with two Rust tests
(`k = 3` proves, `k = 4` refused) next to the named `constraint_count` fact. Rung L1
for the theorem, L3 for the pinned bound. The number to report: the maximum accepted `k`, predicted 3.
