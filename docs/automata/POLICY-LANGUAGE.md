# The policy language

2026-11-06, lane B of the automata program (`SUBSTRATE-DECISION.md` §5 item 5, §7 row B). Tags:
[READ] seen in the file; [MEASURED] a run of the compiled `policyc` or a pinned `#guard`;
[INFERRED] derived here. Lean sources: `metatheory/Dregg2/Policy/` (file list and gate in
`metatheory/Dregg2/Policy/README.md`); executable: `lake exe policyc` (`metatheory/Policyc.lean`).

One surface for the claim families the program arithmetizes: byte patterns with native
intersection and complement, context-free grammars, Datalog rules with negation, and aggregate
budgets, gathered into `policy` blocks shaped like Lucid's `policy.forbid(...)`. The parser lives
in Lean, carries a round-trip theorem, and is the code `policyc` runs, so there is no second,
unproved grammar in Rust.

## 1. Grammar (EBNF)

```
file     ::= decl*
decl     ::= "pattern" IDENT "=" re ";"
           | "grammar" IDENT "{" prod* "}"
           | "rule" atom ( ":-" lit ( "," lit )* )? "."
           | "budget" IDENT ":" agg "<=" NAT ";"
           | "policy" IDENT "{" claim* "}"

re       ::= inter ( "|" re )?                     -- loosest, right-associative
inter    ::= cat ( "&" inter )?
cat      ::= unary cat?                            -- juxtaposition
unary    ::= "~" unary | postfix
postfix  ::= atom ( "*" | "+" | "?" | "{" NAT "," NAT "}" | "{" NAT "}" )*
atom     ::= STRING | CLASS | "\d" | "\w" | "\s" | "." | "(" re ")"

prod     ::= IDENT "->" ( alt ( "|" alt )* )? ";"
alt      ::= "ε" | ( IDENT | STRING )+

atom     ::= IDENT "(" ( arg ( "," arg )* )? ")"   -- in rules
lit      ::= "!"? atom
arg      ::= VAR | INT                              -- VAR: identifier starting A-Z

agg      ::= "sum" "(" IDENT "." NAT ")" | "count" "(" IDENT ")"
claim    ::= ( "forbid" | "require" ) "pattern" IDENT "in" IDENT ";"
           | ( "forbid" | "require" ) "rule" IDENT ";"
           | "require" "budget" IDENT ";"
```

Lexical: `STRING` is `"…"` with raw printable ASCII and the escapes `\" \\ \n \t \r \xHH`;
`CLASS` is `[…]` or `[^…]` with items `c` or `c-c`, where `c` is raw printable ASCII other than
`] \ -`, or `\] \\ \- \^ \[ \n \t \r \xHH`; `#` starts a line comment. A byte range is written
`[\x00-\x1f]`, not `[0x00-0x1f]`: inside a class `[0x41]` would read as one byte or as the four
characters `0 x 4 1`, so the hex form uses the backslash. Keywords are contextual identifiers.

Meanings. `~r` is complement over byte WORDS; one byte that is not `a` is `. & ~[a]` or `[^a]`.
`r{m,n}` with `m > n` is the empty language. `forbid pattern P in F` means no factor of field `F`
matches `P`; `require pattern P in F` means the whole field matches. `forbid rule R` is the exact
claim `Count(R) = 0`; `require rule R` is `Count(R) ≥ 1`. A budget bounds
`Aggregates.sumAt` (argument position, 0-based) or `FixpointCert.countQ`.

## 2. Worked examples (`metatheory/Dregg2/Policy/examples/`)

**Absence** (`absence.policy`):

```
pattern apikey = "sk-" \w{20,32};
pattern delim = "{{";
policy clean {
  forbid pattern apikey in body;
  forbid pattern delim in body;
}
```

`policyc compile absence.policy --pattern delim --absence` prints a 3-state table. `delim`'s
whole-word table has 4 states [MEASURED]. Lane C's `dfa-run` reads the table unchanged:
`x = "{{ y }}"` is REJECT, `a { b } c` is ACCEPT [MEASURED].

**Revocation with negation** (`revocation.policy`):

```
rule issued(1).  rule issued(2).  rule revoked(2).
rule used(10, 1).  rule used(11, 2).
rule usable(K) :- issued(K), !revoked(K).
rule violation(U) :- used(U, K), !usable(K).
policy keys { forbid rule violation; require rule usable; }
```

`policyc rules` emits the `StratifiedCert` program with the strata `[[0,1,2,3,4],[5],[6]]`.
`stratifiedB` accepts it [MEASURED]. On this EDB `violation(11)` is derivable (key 2 is revoked),
so `datalog-check` would refuse a receipt that claims `Count(violation) = 0`. The example is
written to fail that claim.

**Budget** (`budget.policy`):

```
rule spend(1, 40).  rule spend(2, 35).  rule spend(3, 20).
budget daily: sum(spend.1) <= 100;
budget nospam: count(spam) <= 0;
rule spam(X) :- spend(X, 1000).
policy money { require budget daily; require budget nospam; }
```

`elabClaims` resolves each claim to `BudgetClaim.holds`: `sumAt db spend 1 ≤ 100` and
`countQ db spam ≤ 0`.

## 3. The theorems, verbatim

The parser theorem (`Theorems.lean`) covers the whole language, not one fragment:

```lean
theorem parse_print_roundtrip (p : Policy) (hwf : p.wf = true) : parse (print p) = .ok p
theorem print_injective (p q : Policy) (hp : p.wf = true) (hq : q.wf = true)
    (h : print p = print q) : p = q
```

The proof has two halves:
- `ParseRoundTrip.parseTokens_toks` handles tokens → AST. The regex case is one induction
  carrying the parse at every precedence level and after any run of postfix operators.
- `LexRoundTrip.lexChars_render` together with `layout_good` handles text → tokens.

`p.wf` (identifiers are identifiers, variables are capitalized, bytes are below 256) is necessary.
`badVar_not_wf` and its `#guard` exhibit a lowercase variable that prints but does not parse back.

Elaboration (`Elab.lean`). `ReSem` is the textbook semantics of the surface regex:

```lean
theorem elabRe_semantics : ∀ (r : Re) (w : List Nat), Matches (w.map byteFrame) (elabRe r) ↔ ReSem r w
theorem elabRe_derives (r : Re) (w : List Nat) :
    derives (w.map byteFrame) (elabRe r) = true ↔ ReSem r w
theorem absenceOf_semantics (r : Re) (w : List Nat) :
    Matches (w.map byteFrame) (absenceOf (elabRe r)) ↔ ¬ ∃ x y z, w = x ++ y ++ z ∧ ReSem r y
theorem absenceOf_derives (R : PredRE) (w : List Value) :
    derives w (absenceOf R) = !(derives w (.cat (.star any) (.cat R (.star any))))
theorem elabGrammar_rules (name : String) (ps : List Prod) (r : ContextFreeRule Nat String) :
    r ∈ (elabGrammar name ps).rules ↔ ∃ p ∈ ps, ∃ a ∈ p.alts, r = ⟨p.lhs, elabAlt a⟩
theorem dyck_derives : [91, 93] ∈ (elabGrammar "dyck" dyckProds).language
```

Compilation (`Compile.lean`, `Factor.lean`):

```lean
theorem compiled_decides (c : Compiled R) (w : List Nat) :
    c.accepting (c.run c.start w) = true ↔ derives (w.map byteFrame) R = true
theorem absence_decides (r : Re) (D : Certified (elabRe r)) (hD : closedB D.t = true) {E : Table}
    {lab : Nat → Bits × Bool} (h : labCheck D.t E lab = true) (w : List Nat) (hw : w.all (· < 256) = true) :
    E.acc (E.run E.start w) = true ↔ ¬ ∃ x y z, w = x ++ y ++ z ∧ ReSem r y
```

Every table `policyc compile` prints is the `t` of a `Certified R`. Its field
`hdec : ∀ w, w.all (· < 256) → (t.acc (t.run t.start w) = true ↔ derives (w.map byteFrame) R = true)`
reaches the printed table through three steps, each kept only if its check passes:
- the derivative determinizer (`GuardAut.guardDfa_decides` on a deduplicated minterm cover);
- minimization (`simCheck_verdict`, an enumerated simulation check);
- for `--absence`, the factor construction (`labCheck`).

All theorem files end in `#assert_all_clean`. There is no `sorry` and no `native_decide`.

## 4. Counts

The original measurements below are retained as the baseline. The normalization cache
now compiles `"sk-" \w{20,64}` in 3.1 seconds on bb2 (69 states, 17,664 transitions);
see [the reproducible comparison](policy-compile-performance.md). Surface alternatives
now compile their branches separately and use the proved finite-table union product,
followed by checked reachability restriction, the shared checked minimization and absence
construction. The demo union compiles to 129 states / 33,024 transitions in 28.86 seconds
on bb2, with twelve byte-language controls passing (0.83 s since 2026-11-07: see
"Compile performance" below).

- **Parser** [MEASURED, `#guard`]: the falsifiers below are `#guard`s in `Theorems.lean`.
  - An unbalanced `(` is reported at `1:23`, found `;`, expected `` `)` ``. On a second line it is reported at `2:17`.
  - `\q` is reported at `1:18`, with the expected set `\d \w \s`.
  - A lowercase variable in a rule head is reported at `1:11`.
  - `policyc check` on the three examples exits 0.
  - `fmt` is idempotent on all three examples.
- **`lake env lean` wall time on this Mac** [MEASURED]:

  | file | time |
  |---|---|
  | `ParseRoundTrip` | 7 s |
  | `LexRoundTrip` | 20 s |
  | `Theorems` | 14 s |
  | `Elab` | 9 s |
  | `Compile` | 15 s |
  | `Factor` | 15 s |

- **Tables**: minimized state counts and compile time of the native `policyc` [MEASURED, 2026-11-06].

  | pattern | whole-word | absence | absence compile |
  |---|---|---|---|
  | `"{{"` | 4 | 3 | 4 ms |
  | `"-----BEGIN"` | | 11 | 92 ms |
  | `"password=" \| "secret=" \| "api_key="` | | 21 | 659 ms |
  | `[\x00-\x08]` | | 2 | 1 ms |
  | `"AKIA" [A-Z]{2}` | | 7 | 24 ms |
  | `\d\d` | | 3 | 4 ms |
  | `"sk-" \w{4,8}` | | 12 | 83 ms |
  | `"sk-" \w{8,16}` | | 24 | 583 ms |
  | `"sk-" \w{16}` | | 48 | 1.5 s |
  | `"sk-" \w{20,32}` | | 60 | 9.5 s |
  | `"sk-" \w{32}` | | 96 | 21.7 s |
  | `"sk-" \w{20,64}` | — | — | more than 120 s; the whole-word derivative step is the bottleneck |

The derivative factor search alone could not handle absence. Compiling `absenceOf R` directly by
derivatives exceeded 60 s on `"-----BEGIN"`. ACI similarity `≅` does not identify the
derivative terms of different partial-match sets, so the state count explodes. `Factor.lean`
instead builds the absence automaton from the whole-word table by a subset construction whose
output is label-checked. Counting classes still scale as roughly the cube of the count [MEASURED:
`\w{16}` 1.5 s, `\w{32}` 21.7 s]. The cost is the derivative determinizer's `simDecide` against
every seen state, not the table size.

### Compile performance (2026-11-07)

[MEASURED, bb2, native `policyc`, warm, wall including process start] The demo policy
(`demo/absence-receipt/policy.policy`, `--pattern secrets --absence`) compiles in **0.83 s**
(three runs: 0.83, 0.84, 0.83), down from 28.9 s (the 2026-11-06 measurement) and 21.9 s for
the pre-change binary on the same box today. The Rust crate compiler takes 2.7 s on the same
policy. The output is byte-identical to the checked-in `absence-table.json` (`cmp`, 200,146 bytes),
and so are the `policyc/aws-absence.json` and `policyc/pem-absence.json` fixtures.

`perf` on the 21.9 s binary showed three costs:

1. Composed tables were closures. After union, trim, minimize and relabel, every `D.step`/`D.acc`
   call re-ran that whole chain. `Table.materialize` puts the rows into arrays.
   `Table.materialize_eq : t.materialize = t` is an equality of tables, so `Certified.optimize`
   returns the materialized table under the same `hdec`.
2. `nextSet`/`anyAcc` read the `List Bool` bitmap with `getD`, which is linear per lookup, and
   scanned a target list once for each destination. Both now read through an array copy, and the
   successor image is built in one pass. The new `nextSet_spec` proves it equal to the original
   pointwise set expression, for every table, bitmap and byte. `anyAcc_spec` does the same for
   `anyAcc`. `absRun_spec` goes through these two lemmas unchanged.
3. The factor exploration visits 6,707 abstract states before minimization, and `labCheck`
   recomputed `absStep` for all 256 bytes of each one. The whole-word table has few distinct byte
   columns. `labCheckRep` computes `absStep` only at each column class's least byte. Every other
   byte must step to the same numbered state as its representative, and `colCheck` verifies
   that the class map really preserves columns. `labCheckRep_sound` (through `absStep_col`)
   proves that `labCheckRep` implies `labCheck`, so `absence_decides` applies unchanged.
   Exploration and the Moore refinement signatures use the same classes. Both are untrusted and
   still checked by `labCheck`/`simCheck`.

Phase clocks (`POLICYC_PROFILE=1`): whole-word 265 ms, factor exploration 158 ms (6,707
states), the whole absence phase 481 ms.

| pattern | mode | states | before | after | bytes |
|---|---|---:|---:|---:|---|
| demo union | absence | 129 | 21.9 s | 0.83 s | identical |
| `"sk-" \w{16}` | absence | 48 | 157 ms | 75 ms | identical |
| `"sk-" \w{32}` | absence | 96 | 729 ms | 361 ms | identical |
| `"sk-" \w{20,64}` | absence | 60 | 2.13 s | 1.32 s | identical |
| `"sk-" \w{64}` | absence | 192 | 6.28 s | 4.21 s | identical |
| `"sk-" \w{20,64}` | whole-word | 69 | 1.72 s | 1.42 s | identical (benchmark digest) |
| `"sk-" \w{64}` | whole-word | 69 | 5.03 s | 4.33 s | identical (benchmark digest) |

"before" is the 2026-11-06 binary (normalization cache and factor-successor hoist already
included), run on the same box. The counted-repeat cases are now dominated by the derivative
determinizer (`simDecide` normalization), not by the factor construction.

## 5. What is NOT claimed

- That `print (parse s) = s`. `fmt` normalizes spacing, comments, redundant parentheses, and
  `{m}` (printed `{m, m}`). It is idempotent on the examples, and that is a test, not a theorem.
- That every successful parse is well formed. This is true by construction of the lexer and of
  `parseArg`, but it is not stated.
- Anything about non-byte frames. `elabRe` maps `.` to `Pred.tt`, and the semantic theorems
  quantify over byte words `w.map byteFrame`.
- The JSON printing in `policyc`, its argument handling, and `explore`/`minimize` themselves. These
  are unproved shell. What is proved is the correctness of the table they print: each one passes
  `simCheck`/`labCheck`, or `policyc` says it did not.
- Negation in `FixpointCert`. `elabRules` refuses a negated literal. Negation elaborates to
  `StratifiedCert.SRule` (`elabProgram`), and `strataOf` computes a stratification by predicate
  rank that `stratifiedB` re-checks. The JSON matches the `program`/`strata` shape that
  `datalog-check` reads [READ `DatalogCheck.lean`]. The EDB, root and count are the caller's.
- Grammar membership decisions. `elabGrammar` produces mathlib's `ContextFreeGrammar Nat`, and
  certificates for it are `CfgCompact`'s. `policyc` does not compile grammars.
- Any first. Verified parsers exist (CompCert's validated Menhir parsers, Jourdan, Pottier and
  Leroy, ESOP 2012), and printer/parser round trips are routine in proof assistants. This is
  that standard result, for this language's hand-written parser.

## 6. Follow-ups

1. Counted-class normalization caching is implemented and measured; exact worklist and lookup
   equivalence are proved. Remaining performance work is tracked in
   [policy-compile-performance.md](policy-compile-performance.md).
2. A theorem that `parse` output is well formed (`parse s = .ok p → p.wf`). With it,
   `print_injective` would become `parse ∘ print = id` on the image of `parse`.
3. Named pattern references (`pattern b = a & ~c`) need an environment in `elabRe`. They are
   omitted to keep every construct closed.
