/-
# Dregg2.Policy.Theorems — ⚑ the parser theorem.

    parse_print_roundtrip : ∀ p : Policy, p.wf = true → parse (print p) = .ok p

for the WHOLE language (patterns, grammars, rules with negation, budgets, policy blocks), composed
from the two halves:

  * `LexRoundTrip.lexChars_render` + `layout_good`: the lexer reads the printer's text back as
    exactly the printed tokens followed by `eof`;
  * `ParseRoundTrip.parseTokens_toks`: the parser reads those tokens back as the policy.

`p.wf` is necessary, not a convenience: an AST is free to hold the identifier `"1x"`, the
variable `"x"` (lowercase), or the byte `300`, none of which has a spelling the lexer accepts; `wf`
says exactly that names are identifiers, variables are capitalized, and bytes are below 256.

`print_injective` follows. What is NOT claimed here: that `print ∘ parse` is the identity on text
(it is not: comments, spacing, redundant parentheses and `\d`-vs-`[0-9]`-style spellings are
normalized), and that every successful parse is well formed (true by construction of the lexer and
`parseArg`, but not stated as a theorem).

Prior art for the shape of the result (we rely on none of it as code): CompCert's validated
Menhir parsers (Jourdan, Pottier, Leroy, ESOP 2012) prove a parser correct against a grammar;
printer/parser round trips of this kind are routine in Lean/Coq developments. This file proves the
round trip for this language's hand-written recursive-descent parser and its canonical printer.
-/
import Dregg2.Policy.ParseRoundTrip
import Dregg2.Policy.LexRoundTrip

namespace Dregg2.Policy

set_option autoImplicit false

/-- ⚑⚑ **`parse_print_roundtrip`** — the parser inverts the canonical printer on every
well-formed policy. -/
theorem parse_print_roundtrip (p : Policy) (hwf : p.wf = true) : parse (print p) = .ok p := by
  obtain ⟨hg, hfst⟩ := layout_good p hwf
  obtain ⟨pts, hlex, hmap⟩ := lexChars_render p.layout hg
  rw [hfst] at hmap
  obtain ⟨ps, es, rfl, hps, hes⟩ := List.map_eq_append_iff.mp hmap
  obtain ⟨e, rfl, he⟩ := List.map_eq_singleton_iff.mp hes
  simp only [parse, print, lex, String.toList_ofList, hlex, bind, Except.bind]
  exact parseTokens_toks p hwf ps e he hps

/-- **`print_injective`** — distinct well-formed policies print differently. -/
theorem print_injective (p q : Policy) (hp : p.wf = true) (hq : q.wf = true)
    (h : print p = print q) : p = q := by
  have h1 := parse_print_roundtrip p hp
  rw [h, parse_print_roundtrip q hq] at h1
  exact (Except.ok.inj h1).symm

/-- The regex fragment on its own: a pattern declaration round-trips for every well-formed regex
and pattern name. -/
theorem pattern_roundtrip (n : String) (r : Re) (hn : isIdent n = true) (hr : r.wf = true) :
    parse (print ⟨[.pattern n r]⟩) = .ok ⟨[.pattern n r]⟩ :=
  parse_print_roundtrip _ (by simp [Policy.wf, Decl.wf, hn, hr])

/-- The rule fragment on its own. -/
theorem rule_roundtrip (r : Rule) (hr : r.wf = true) :
    parse (print ⟨[.rule r]⟩) = .ok ⟨[.rule r]⟩ :=
  parse_print_roundtrip _ (by simp [Policy.wf, Decl.wf, hr])

/-! ## Non-vacuity: the hypothesis is inhabited and the theorem fires on real policies. -/

/-- A policy exercising every declaration form, negation in a rule body, intersection and
complement in a pattern, a bounded repetition, a negated class with escapes. -/
def demo : Policy := ⟨[
  .pattern "secret" (.cat (.lit [115, 107, 45]) (.rep (.esc .word) 20 64)),
  .pattern "ctl" (.inter (.set false [(0, 31), (127, 127)]) (.neg (.set false [(10, 10)]))),
  .pattern "odd" (.alt (.star (.cat .any .any)) (.plus (.opt (.set true [(34, 34), (92, 92), (93, 93)])))),
  .grammar "dyck" [⟨"S", [[.t [91], .nt "S", .t [93]], []]⟩],
  .rule ⟨⟨"active", [.var "K"]⟩, [⟨false, ⟨"issued", [.var "K"]⟩⟩, ⟨true, ⟨"revoked", [.var "K"]⟩⟩]⟩,
  .rule ⟨⟨"issued", [.int 7]⟩, []⟩,
  .rule ⟨⟨"spend", [.var "U", .int (-3)]⟩, []⟩,
  .budget "cap" (.sum "spend" 1) 100,
  .budget "none" (.count "violation") 0,
  .policy "p" [.forbidPattern "secret" "body", .requirePattern "dyck" "path", .forbidRule "violation",
    .requireRule "active", .requireBudget "cap"]
]⟩

theorem demo_wf : demo.wf = true := by decide

/-- The round trip, fired on `demo` through the theorem (not by evaluation). -/
theorem demo_roundtrip : parse (print demo) = .ok demo := parse_print_roundtrip demo demo_wf

/-- The `wf` hypothesis is not decorative: a lowercase "variable" prints as an identifier that the
parser refuses as an argument, so the round trip FAILS without `wf`. -/
def badVar : Policy := ⟨[.rule ⟨⟨"p", [.var "x"]⟩, []⟩]⟩

theorem badVar_not_wf : badVar.wf = false := by decide

/-! ## `#guard`s (compiled evaluation): the printed text, and the round trip by evaluation too. -/

#guard print demo ==
  "pattern secret = \"sk-\" \\w{20, 64};\n" ++
  "pattern ctl = [\\x00-\\x1f\\x7f] & ~[\\x0a];\n" ++
  "pattern odd = (. .)* | [^\"\\\\\\]]?+;\n" ++
  "grammar dyck {\n  S -> \"[\" S \"]\" | ε;\n}\n" ++
  "rule active(K) :- issued(K), !revoked(K).\n" ++
  "rule issued(7).\n" ++
  "rule spend(U, -3).\n" ++
  "budget cap: sum(spend.1) <= 100;\n" ++
  "budget none: count(violation) <= 0;\n" ++
  "policy p {\n  forbid pattern secret in body;\n  require pattern dyck in path;\n" ++
  "  forbid rule violation;\n  require rule active;\n  require budget cap;\n}\n"
#guard (parse (print demo)).toOption == some demo
#guard (parse (print badVar)).toOption == none

/-! ## Error-message falsifiers: located errors with the right expected sets. -/

/-- The error of a failing parse, if any. -/
def errOf (s : String) : Option ParseError :=
  match parse s with
  | .ok _ => none
  | .error e => some e

-- An unbalanced parenthesis: reported at the `;` (line 1, column 23) where `)` was expected.
#guard errOf "pattern p = (\"a\" | \"b\";" == some ⟨⟨1, 23⟩, "`;`", ["`)`"]⟩
-- …and on a later line, the line number moves with it.
#guard (errOf "rule ok(1).\npattern p = (\"a\";").map (·.pos) == some ⟨2, 17⟩
-- An unknown regex escape `\q`: reported at the backslash with the expected set `\d \w \s`.
#guard errOf "pattern p = \"a\" \\q;" == some ⟨⟨1, 18⟩, "`\\q`", ["\\d", "\\w", "\\s"]⟩
-- An unknown string escape: the string-escape expected set.
#guard (errOf "pattern p = \"a\\qb\";").map (·.expected) == some escExpected
-- A lowercase variable in a rule head: located at the offending identifier.
#guard errOf "rule path(x, Y) :- edge(x, Y)." ==
  some ⟨⟨1, 11⟩, "identifier `x`", argExpected⟩
-- An unknown declaration keyword.
#guard (errOf "patern p = \"a\";").map (·.expected) == some declExpected
-- `forbid budget` is not a claim (only `require budget` is).
#guard (errOf "policy p { forbid budget b; }").map (·.expected) == some ["`pattern`", "`rule`"]

#assert_all_clean [parse_print_roundtrip, print_injective, pattern_roundtrip, rule_roundtrip,
  demo_wf, demo_roundtrip, badVar_not_wf, lexChars_render, layout_good, parseTokens_toks,
  parseRe_toks]

end Dregg2.Policy
