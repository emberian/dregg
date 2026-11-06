# `Dregg2/Policy/` — the policy language

The language, its grammar, its worked examples, and what is and is not claimed are in
`docs/automata/POLICY-LANGUAGE.md`. This file lists the files and the gate.

| file | contents | keystones (`#assert_all_clean` at the end of each theorem file) |
|---|---|---|
| `Syntax.lean` | the AST (`Re`, `Prod`, `Rule`, `Agg`, `Claim`, `Decl`, `Policy`) and `Policy.wf` | — |
| `Lexer.lean` | tokens, their canonical spelling `Tok.text`, the total lexer `lex` (line:col errors) | — |
| `Pretty.lean` | the token printer (minimal parentheses) and the layout; `print` | — |
| `Parser.lean` | recursive descent, no `partial`; `parse` | — |
| `ParseRoundTrip.lean` | tokens → AST: `parseTokens_toks`, `parseRe_toks` | 17 |
| `LexRoundTrip.lean` | text → tokens: `lexChars_render`, `layout_good` | — (consumed by `Theorems`) |
| `Theorems.lean` | ⚑ `parse_print_roundtrip`, `print_injective`, error-position falsifiers | 11 |
| `Elab.lean` | `elabRe` + `elabRe_semantics`, `absenceOf` + `absenceOf_semantics`, `elabGrammar` + `dyck_derives`, `elabProgram`/`elabRules`/`strataOf`, `BudgetClaim`, `elabClaims` | 14 |
| `Compile.lean` | the executable determinizer on a signature-deduplicated cover, memoized byte table, checked minimization; `compiled_decides`, `simCheck_verdict`, `Certified` | 9 |
| `Factor.lean` | the absence automaton by a label-checked factor (subset) construction over the whole-word table; `absRun_spec`, `absence_decides` | 7 |
| `examples/*.policy` | the three worked examples of the note | — |

`../../Policyc.lean` is the `lake exe policyc` entry point (`check`, `fmt`, `compile`, `rules`).

## Gate (this Mac; never a bare `lake build` in `metatheory`)

```
cd /Users/ember/dev/breadstuffs/metatheory
lake build Dregg2.Policy.Theorems Dregg2.Policy.Compile    # the import closures, with every #guard
lake build policyc
./.lake/build/bin/policyc check Dregg2/Policy/examples/absence.policy
./.lake/build/bin/policyc compile Dregg2/Policy/examples/absence.policy --pattern delim --absence
./.lake/build/bin/policyc rules Dregg2/Policy/examples/revocation.policy
```

`Compile.lean`/`Factor.lean` pin no table sizes by `#guard`: under Lean's interpreter the
determinizer is minutes-slow even on small patterns, so the sizes are measured by the compiled
`policyc` and recorded in the note (§4). The elaborated regexes' admit/reject falsifiers are
`#guard`s in `Elab.lean` (evaluated through `derives`).
