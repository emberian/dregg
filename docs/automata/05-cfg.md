# Context-free grammars: compact replay versus CYK and Earley — arithmetization note (2026-11-05)

Tags: [READ] seen at file:line; [MEASURED] a pinned #guard or a run; [CLAIM] asserted elsewhere; [INFERRED] derived here.

Hub: `AUTOMATA-ARITHMETIZATION-PROGRAM.md` §2 rows "CFG, compact leftmost replay" and "CFG, Earley/CYK".
M = `/Users/ember/dev/breadstuffs/metatheory/Dregg2`, R = `/Users/ember/dev/breadstuffs`.
Script for the counts marked "run": `/private/tmp/claude-501/-Users-ember-dev-aidev/78fef112-a52f-425f-8503-f3fa24ff087c/scratchpad/notesA/cfgcount.py`
(a Python mirror of `json_grammar`; it is not the Rust prover).

Three certificate shapes for one question, `w ∈ L(G)`. They differ mainly in which polarity they can
certify. The compact replay is `O(n)` and certifies acceptance only. CYK certifies rejection for any
grammar, at `|R_bin|·(n³ − n)/6` checks. A validated deterministic parser certifies both polarities in
`O(n)`, but only for deterministic grammars, and JSON's grammar is one. §3 also corrects the hub's CYK
formula.

## 1. Semantics object (Lean)

mathlib `ContextFreeGrammar` (`Produces`, `Derives`, `language`). In the tree [READ], verbatim:

```lean
-- M/Crypto/Cfg.lean:66
def CfgAccepts (g : ContextFreeGrammar T) (input : List T)
    (chain : List (List (Symbol T g.NT))) : Prop :=
  Hypergraph.Cert g.Produces [Symbol.nonterminal g.initial] (input.map Symbol.terminal) chain

-- Cfg.lean:83
theorem cfg_bridge (g : ContextFreeGrammar T) (input : List T) :
    (∃ chain, CfgAccepts g input chain) ↔ input ∈ g.language

-- Cfg.lean:122
theorem cfg_verify_sound {T : Type} [K : CfgVerifierKernel T Proof]
    (hext : K.extractable) (stmt : Statement T) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    stmt.input ∈ stmt.g.language
```

`Statement T` holds `g` and `input` (`Cfg.lean`, the structure before `CfgVerifierKernel`). So
`cfg_verify_sound` **does** name the input word, because the input is public at the `fullDisclosure`
floor. It has no content commitment `c`.

The compact certificate, `M/Crypto/CfgCompact.lean` [READ]:

```lean
-- :48
inductive Replay (g : ContextFreeGrammar T) :
    List (ContextFreeRule T g.NT) → List T → List (Symbol T g.NT) → Prop
  | done : Replay g [] [] []
  | term {rs : List (ContextFreeRule T g.NT)} {input : List T} {stk : List (Symbol T g.NT)}
      (t : T) : Replay g rs input stk → Replay g rs (t :: input) (Symbol.terminal t :: stk)
  | rule {r : ContextFreeRule T g.NT} {rs : List (ContextFreeRule T g.NT)} {input : List T}
      {stk : List (Symbol T g.NT)} (hr : r ∈ g.rules) :
      Replay g rs input (r.output ++ stk) →
      Replay g (r :: rs) input (Symbol.nonterminal r.input :: stk)

-- :60
def ReplayAccepts (g : ContextFreeGrammar T) (rs : List (ContextFreeRule T g.NT))
    (input : List T) : Prop :=
  Replay g rs input [Symbol.nonterminal g.initial]

-- :81
theorem compact_sound (g : ContextFreeGrammar T) (rs : List (ContextFreeRule T g.NT))
    (input : List T) (h : ReplayAccepts g rs input) : input ∈ g.language

-- :90
theorem compact_to_chain (g : ContextFreeGrammar T) (rs : List (ContextFreeRule T g.NT))
    (input : List T) (h : ReplayAccepts g rs input) :
    ∃ chain, CfgAccepts g input chain
```

(Line drift: the brief and the census cite `:43`, `:86`, `:96`. At HEAD the declarations are at
`:48`, `:60`, `:81`, `:90`, which matches CERTIFICATES.md §4.)

The template-shaped sub-family [READ]:

```lean
-- M/Crypto/HandlebarsGuarded.lean:145
theorem guarded_render_mem_language (T : GuardedTemplate) (d : Nat → List Value)
    (hsafe : guardedSafe T d) :
    render T d ∈ (guardedToGrammar T).language

-- M/Crypto/SlotConfinement.lean:190
theorem slot_confinement (T : Template Name) (b : Name → List Value)
    (hb : ∀ n, Seg.slot n ∈ T → InjectionFree (b n)) :
    controlTokens (render b T) = controlTokens (litOnly T)
```

`GuardedGrammar` is a list of `Leaf.fixed w | Leaf.guarded g` leaves with
`gLang (l :: ls) u = ∃ a b, a ++ b = u ∧ l.lang a ∧ gLang ls b` (`HandlebarsGuarded.lean:86-118`) [READ].
That is a **concatenation of regular languages, so it is regular**: the sub-family is CFG-named but
needs no stack. Its file says it is "NOT a finite `ContextFreeGrammar`", because the `Value` alphabet is infinite.

## 2. Certificate shape

Word: a JSON token sequence `toks` over the 11 `JTok` classes (`zkoracle-prove/src/cfg.rs:32`) [READ],
produced from the body bytes by the lexer `cfg.rs:215 tokenize(body: &[u8]) -> Result<Vec<JTok>, CfgError>`,
which has no Lean twin [READ census]. Content commitment: `c = content_commitment(body)`
(`attestation.rs:84`), a Poseidon2 sponge over the **bytes** [READ]. So `c` and the grammar range over
different alphabets, and the lexer sits between them.

| shape | public `x` | witness | size | polarity |
|---|---|---|---|---|
| form chain (`CfgAccepts`) | `g`, `c` | all sentential forms | `O(n²)` symbols | accept |
| **compact replay** (`ReplayAccepts`; Rust `CompactCert { rules: Vec<u8> }`, `cfg.rs:605`) | `g`, `c` | the leftmost rule sequence | `O(n)` | accept |
| **CYK table** (CNF `G'`) | `G'`, `c` | a bit per (span, nonterminal) | `n(n+1)/2 · |N'|` bits | **reject** (closed table); accept (a parse tree, `O(n)`) |
| **Earley chart** | `g`, `c` | item sets `S_0 … S_n` | `≤ |items|·n(n+1)/2` items | reject (closed chart) or accept |
| **validated deterministic parser run** | `g`, the LR/LL automaton, a validation certificate | the parser's configuration per step | `O(n)` | **both** |

The Rust verifier `verify_cfg_compact(cert: &CompactCert, body: &[u8])` (`cfg.rs:766`) re-tokenizes the
body itself and replays the rules natively. It does not run in a circuit [READ]. The attestation
verifier compares `att.content_commit` with `content_commitment(&session.response_body)` and then
calls `verify_cfg_compact(&att.cfg_cert, &session.response_body)` (`attestation.rs:515, 521`) [READ].
The binding is therefore "both legs ran natively over the same bytes". It is not a proof relation.

## 3. Arithmetization and counts

The grammar, `json_grammar` (`cfg.rs:108`) [READ]: 6 nonterminals, 16 rules, right-hand sides of
length ≤ 3, and 44 dotted items [MEASURED, run]. Its CNF (TERM, BIN, UNIT elimination, unreachable
symbols dropped) has `|N'| = 16`, `|R_bin| = 17` and `|R_term| = 17` [MEASURED, run; a by-hand count
agrees]. The pinned mathlib has no Chomsky normal form (a grep for `ChomskyNormalForm` under
`.lake/packages/mathlib/Mathlib` returns nothing) [READ]. So any CYK certificate carries a per-grammar
CNF-equivalence obligation as well.

**Compact replay.** Rows = tokens + rules + 1 (`done`). From the run on the Python mirror: a 24-token
object with nesting gives 23 rules and 48 rows, and an array of 64 numbers (129 tokens) gives 130 rules
and 260 rows. So about `2n + 2` rows for `n` tokens [MEASURED, run]. In circuit (proposed), the Dyck
shape (`04`) generalizes: one rule-table lookup per rule row (arity 5: `RULE_ID, lhs, rhs₀, rhs₁, rhs₂`,
into a 16-row table) in place of the Dyck descriptor's vanishing-polynomial rule pins, a `STACK0 = token`
gate on term rows, and the memory stack of `04` §2 for unbounded nesting. Per token: ~2 rows, ~1
lookup, 0 permutations if the route chain is replaced by the content sponge [INFERRED]. The deployed
Dyck descriptor's comparison point is 24 columns, 79 constraints and 2 chip lookups per row
[MEASURED `DyckStackEmit.lean:629-641`].

**CYK, rejection.** A table `tbl : span → N' → Bool` is *closed* when it contains every terminal fact
and is closed under every binary rule at every split. The least closed table is the CYK table, so if
any closed table lacks `S` at `(0, n)`, then `w ∉ L`. The certificate is a pre-fixpoint, and the
verifier checks closure. It need not check minimality. Count:

- splits: `Σ_{ℓ=2}^{n} (n − ℓ + 1)(ℓ − 1) = (n³ − n)/6` (span, split) pairs;
- checks: `|R_bin| · (n³ − n)/6`, one degree-3 gate `bit_B(i,k) · bit_C(k,j) · (1 − bit_A(i,j)) = 0` per (pair, rule);
- reads: 3 cell lookups per (span, split) row (arity `|N'| + 2 = 18`).

At `n = 256`: `(256³ − 256)/6 = 2,796,160` rows, `17 · 2,796,160 = 47,534,720` gates, `8,388,480` cell
lookups, and `256·257/2 · 16 = 526,336` table bits [MEASURED, run, for the first two; INFERRED arithmetic
for the last two]. At `n = 1024`: `17 · 178,956,800 = 3,042,265,600` gates [MEASURED, run].

**The hub's CYK cost is not this.** It gives `n²·|N|·|R|` lookups (and `O(n³)` in the next column of
the same row). `n²·|N|·|R|` omits the split factor and multiplies by `|N|` instead. At `n = 256`,
`|N'| = 16`, `|R'| = 34` it gives `35,651,584`. That is within 1.3× of `47,534,720` at this `n` and
low by `(n/6)·|R_bin|/(|N'|·|R'|)` in general (5.3× at `n = 1024`: `570,425,344` against
`3,042,265,600`) [MEASURED, run]. The correct law is cubic.

**CYK, acceptance** needs no table: a parse tree (`2n − 1` nodes in CNF) is a certificate, `O(n)`, and
the compact replay already does it.

**Earley.** The chart holds at most `44 · n(n+1)/2` items, which is `1,447,424` at `n = 256` [INFERRED].
Checking closure under predict/scan/complete is `O(n³)` in general and `O(n²)` for unambiguous grammars
(Earley's bound) [RECALLED]. As a rejection certificate it is a pre-fixpoint in the same sense as CYK.
It needs no CNF, so it carries no CNF obligation, but its `complete` closure is a join over origins and
does not have CYK's fixed 3-cell access pattern.

**Validated deterministic parser.** JSON's grammar is LL(1) after left-factoring
`Members → Member (, Members)?` and `Elements → Value (, Elements)?` [INFERRED]. Over tokens it is also
a VPL (calls `{ [`, returns `} ]`, `04`). A deterministic parser's run is a total function of the input,
so its run to an error configuration certifies rejection in `O(n)` rows. That is sound once the parser
automaton is validated against the grammar, which is a one-time check (Jourdan, Pottier, Leroy). This
is cheaper than CYK by a factor of order `n²` for JSON.

**Commitment and lexer cost.** `n_b/8` permutations for `n_b` body bytes = 44 committed cells per byte
at 352 cells [READ `circuit/src/poseidon2.rs:704`, `crypto-floor/src/field.rs:94`; MEASURED
`POSEIDON2_AUX_COLS == 352`]. The lexer is a byte-level DFA with token-boundary output: in circuit, 1 row
and 1 lookup per byte (`01`/`06`) [INFERRED]. For JSON, bytes per token is ≥ 1 and typically larger,
so the per-byte bill is roughly: hash 44 cells, lexer ~3 cells, replay ~2 rows per token [INFERRED].
As for every regular family, the hash dominates.

## 4. Binding to the content commitment

**NOT BOUND in any CFG theorem.** `compact_sound`, `compact_to_chain` and `cfg_bridge` name the word
and are language facts. `cfg_verify_sound` names `stmt.input` and is correct at full disclosure. None
mentions `c`. There are two gaps, in this order:

1. **bytes → tokens.** `c` commits bytes and the grammar reads tokens. `tokenize` is unverified Rust.
   The binding needs a Lean lexer `lex : List UInt8 → Option (List JTok)`, then either an in-circuit
   lexer run that opens `c` byte by byte, or a statement that names `lex`.
2. **tokens → rules.** The replay rows must read the token sequence that `lex body` produced, through
   shared SYMBOL cells (one trace: lexer rows emit tokens, and replay term rows consume them, by a
   permutation or LogUp argument between the two row kinds), so there is no second commitment.

`zkOracle_sound` (`ZkOracle.lean:90`) concludes `body ∈ jsonGrammar.language` over a `body : List T`
that nothing relates to the authenticated bytes, and its header says its three legs are independent
[READ census]. This family's repair is the repair of that theorem's grammar leg.

## 5. Soundness statement (Lean syntax) and its vacuity falsifier

```lean
/-- Content-bound CFG statement over a byte body, through a named lexer. -/
structure CfgBoundStatement (T D : Type) where
  g   : ContextFreeGrammar T
  lex : List UInt8 → Option (List T)
  c   : D

class CfgBoundVerifierKernel (T D : Type) (S : ContentScheme UInt8 D) (Proof : Type) where
  verify      : CfgBoundStatement T D → Proof → Bool
  extractable : Prop
  extract : extractable → ∀ stmt proof, verify stmt proof = true →
    ∃ body rs toks, S.commit body = stmt.c ∧ stmt.lex body = some toks ∧ ReplayAccepts stmt.g rs toks

theorem cfg_bound_verify_sound {T D Proof} {S : ContentScheme UInt8 D}
    [K : CfgBoundVerifierKernel T D S Proof]
    (hext : K.extractable) (stmt : CfgBoundStatement T D) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    ∃ body, S.commit body = stmt.c ∧ ∃ toks, stmt.lex body = some toks ∧ toks ∈ stmt.g.language
```

Its proof is `extract` followed by `compact_sound`. It meets L0. The rejection counterpart, for a CNF
grammar:

```lean
structure Cnf (T N : Type) where
  start : N
  bin   : List (N × N × N)        -- A → B C
  term  : List (N × T)            -- A → a

inductive Cnf.Gen (g : Cnf T N) : N → List T → Prop
  | term {A a} : (A, a) ∈ g.term → g.Gen A [a]
  | bin {A B C u v} : (A, B, C) ∈ g.bin → g.Gen B u → g.Gen C v → g.Gen A (u ++ v)

/-- A closed (pre-fixpoint) CYK table for `w`. -/
def Closed (g : Cnf T N) (w : List T) (tbl : Nat → Nat → N → Bool) : Prop :=
  (∀ i (hi : i < w.length) A, (A, w[i]) ∈ g.term → tbl i (i + 1) A = true) ∧
  (∀ i k j, i < k → k < j → j ≤ w.length → ∀ A B C, (A, B, C) ∈ g.bin →
      tbl i k B = true → tbl k j C = true → tbl i j A = true)

theorem cyk_closed_rejects (g : Cnf T N) (w : List T) (tbl : Nat → Nat → N → Bool)
    (hc : Closed g w tbl) (hS : tbl 0 w.length g.start = false) :
    ¬ g.Gen g.start w
```

`cyk_closed_rejects` is the least-fixpoint lemma: `Gen A (w.take j |>.drop i) → tbl i j A = true`, by
induction on `Gen`. It is the same lemma Part D needs for Datalog (hub §4): CYK is a Datalog program,
and a closed table is a closed trace. The content-bound form adds `S.commit body = c ∧ lex body = some w`
exactly as above.

**Falsifier 1 (the splice, for the compact certificate).** `brackets_replays : ReplayAccepts dyck [rBracket, rEmpty] [op, cl]`
(`CfgCompact.lean:111`) holds for every record, so a statement shaped like `compact_sound`, with the
word supplied by the prover, accepts the record `[op, op]`. The bound shape, at the identity scheme,
requires `∃ rs, ReplayAccepts dyck rs [op, op]`. That is refuted by inversion on `Replay`, where every
step is forced: `rule rBracket`, `term op`, `rule rBracket`, `term op`, then the stack `[S, cl, cl]` has
no consuming move on empty input. Lean: `dyck_splice_fails_bound : ¬ ∃ rs, ReplayAccepts dyck rs [op, op]`.

**Falsifier 2 (CYK minimality is not needed, closure is).** For a CNF grammar with `S → A B`, `A → a`,
`B → b` and the word `ab`, the table that marks only `A` at `(0,1)` and `B` at `(1,2)` violates
`Closed` (the binary rule forces `S` at `(0,2)`). A verifier that checks only the terminal facts would
accept "`S ∉ (0,2)`", that is, `ab ∉ L`. It is false. The `#guard` is a decidable `Closed` checker
returning `false` on that table, and `true` on the same table with `S` added.

## 6. Composition behaviour

| operator | replay | CYK / Earley | template sub-family |
|---|---|---|---|
| intersection with a regular language (a schema refinement, a DFA over tokens) | fuse: run the DFA on the term rows' SYMBOL cells, `+1` lookup per term row, one witness | the Bar-Hillel product grammar, `|N'|·|Q|²` nonterminals | a DFA per hole, `02` |
| intersection with a CFL | not closed (CFLs are not closed under ∩); two independent certificates over one `c`, at `ε₁ + ε₂ + b` (L1) | same | n/a |
| complement | not available from a replay | **the purpose of the closed table** | regular, so `02`'s complement applies |
| concatenation, star | grammar constructions | grammar constructions | native (`gLang` is a concatenation) |
| weld to `c` | §4, through the lexer | same | per-hole openings |
| MMR aggregation | positive `φ` ("every record parses"): L2 | negative `φ` ("no record parses as X"): L2 over closed tables, cubic per record | yes |

Where ε-additivity fails for this family: (i) the lexer is a transducer, and a "some tokenization"
statement is weaker than a "the tokenization" statement unless `lex` is a function (it is, for JSON:
`tokenize` is deterministic). (ii) `zkOracle_sound`'s legs are not one request (§4). (iii) For the
template family, `slot_confinement` treats `{{` as one atomic `Value` frame (code 123), so a byte-level
`{` ending a hole next to a literal `{` produces `{{` across the junction at the byte level while the
frame-level theorem still holds. The junction breakout is listed as a residual in `HandlebarsGuarded`
§7 [READ census]. The byte twin is `02`'s padded complement run over the rendered bytes, not per hole.

## 7. Prior art

- Coral, Angel, Celi, Margolin, Mishra, Sander, Woods, IEEE S&P 2026, ePrint 2025/1420 [READ]: ZK proofs
  that a committed byte stream parses under a CFG (JSON, TOML, C), through a left-child right-sibling tree
  and segmented memory. The closest prior art for the whole family.
- Malvai, Hussain, Neven, Miller, *Practical Proofs of Parsing for Context-free Grammars*, ePrint
  2024/562 [READ]: ZK CFG parsing linear in the string length; about 24 s for 1 KB.
- Firsov, Uustalu, *Certified CYK parsing of context-free languages* (Agda) [SNIPPET]: CYK by matrix
  multiplication over nonterminal sets, with correctness proofs.
- Jourdan, Pottier, Leroy, *Validating LR(1) Parsers*, ESOP 2012 [SNIPPET]: a Coq validator for an LR(1)
  automaton against its grammar; the one-time check behind the deterministic-parser row.
- Earley's algorithm [RECALLED]: `O(n³)` general, `O(n²)` unambiguous.

Not claimed as ours: ZK CFG parsing (Coral, Malvai et al.), certified CYK (Firsov-Uustalu), parser
validation (JPL). A ZK rejection certificate for a CFG got no hit in PRIOR-ART §3 ("does not mention
non-parse (rejection) proofs" for both Coral and Malvai). That is a "no hit" and is not claimed as a gap.

## 8. Built vs proposed

| object | where | rung |
|---|---|---|
| `CfgAccepts`, `cfg_bridge`, `cfg_verify_sound` | `Cfg.lean:66, 83, 122` | L1; names the input, no `c` |
| `Replay`, `ReplayAccepts`, `compact_sound`, `compact_to_chain` | `CfgCompact.lean:48, 60, 81, 90` | L1 |
| `verify_cfg_compact` (native) | `zkoracle-prove/src/cfg.rs:766` | L4 deployed, not in circuit |
| JSON lexer | `cfg.rs:215`, no Lean twin | L4 deployed, unverified |
| in-circuit replay | only for `{[ᵏ]ᵏ}` (`04`) | L3/L4 for that grammar |
| `guarded_render_mem_language`, `slot_confinement` | `HandlebarsGuarded.lean:145`, `SlotConfinement.lean:190` | L1, no circuit |
| `CfgBoundStatement`, `cfg_bound_verify_sound` | proposed | L0 |
| `Cnf`, `Closed`, `cyk_closed_rejects`, both falsifiers | proposed | L0 |
| CYK AIR | proposed | L0 |

**Milestone:** `cyk_closed_rejects` proved, with a decidable `Closed` checker `#guard`ed on the 16-nonterminal
CNF of `json_grammar` for one rejected token word of length `n = 16` (for example `[ Num , Num , … , Num`,
seven `, Num` pairs and no closing `]`),
plus falsifier 2. Pin `17 · (16³ − 16)/6 = 17 · 680 = 11,560` gate evaluations as the counted cost
[INFERRED arithmetic] next to the replay's `≈ 2·16 + 2 = 34` rows for an accepted word of the same
length. Rung L2. The CNF-equivalence obligation stays named, as an open hypothesis.
