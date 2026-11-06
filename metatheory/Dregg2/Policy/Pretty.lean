/-
# Dregg2.Policy.Pretty — the canonical printer.

Printing is two layers, and the round-trip proof follows the same seam:

  1. **tokens** (`Re.toks`, `Rule.toks`, `Decl.toks`, `Policy.toks`): the AST as a token list, with
     the FEWEST parentheses the precedence order allows
     (`|` < `&` < concatenation < `~` < postfix `* + ? {m,n}` < atoms). Binary operators are
     right-associative, which is how the recursive-descent parser builds them, so a parsed regex
     prints back with no added parentheses;
  2. **layout** (`Policy.layout`): each token paired with the whitespace after it. A pair of tokens
     is glued with no space only when the glue table asks for it AND `Tok.delim` says the lexer
     stops there, so the layout cannot change the token stream whatever the glue table says.

`print p = String.ofList (render (layout p))`. Comments in the source are not preserved by `fmt`.
-/
import Dregg2.Policy.Lexer

namespace Dregg2.Policy

/-! ## Token shorthands. -/

abbrev tLP : Tok := .punct .lparen
abbrev tRP : Tok := .punct .rparen
abbrev tLB : Tok := .punct .lbrace
abbrev tRB : Tok := .punct .rbrace
abbrev tComma : Tok := .punct .comma
abbrev tSemi : Tok := .punct .semi
abbrev tDot : Tok := .punct .dot
abbrev tBar : Tok := .punct .bar
abbrev tAmp : Tok := .punct .amp
abbrev tTilde : Tok := .punct .tilde
abbrev tStar : Tok := .punct .star
abbrev tPlus : Tok := .punct .plus
abbrev tQuest : Tok := .punct .quest
abbrev tBang : Tok := .punct .bang
abbrev tColon : Tok := .punct .colon
abbrev tTurn : Tok := .punct .turnstile
abbrev tArrow : Tok := .punct .arrow
abbrev tLe : Tok := .punct .le
abbrev tEq : Tok := .punct .eq
abbrev kw (s : String) : Tok := .ident s

/-! ## Regex tokens. -/

/-- Precedence: 0 `|`, 1 `&`, 2 concatenation, 3 `~`, 4 postfix, 5 atom. -/
def Re.prec : Re → Nat
  | .alt _ _ => 0
  | .inter _ _ => 1
  | .cat _ _ => 2
  | .neg _ => 3
  | .star _ | .plus _ | .opt _ | .rep _ _ _ => 4
  | _ => 5

/-- Parenthesize `ts` (the tokens of `r`) when `r` binds looser than level `k`. -/
def wrap (k : Nat) (r : Re) (ts : List Tok) : List Tok :=
  if k ≤ r.prec then ts else tLP :: (ts ++ [tRP])

/-- **`Re.toks`** — a regex's tokens at its own precedence level. -/
def Re.toks : Re → List Tok
  | .lit bs => [.str bs]
  | .set n rs => [.cls n rs]
  | .esc e => [.esc e]
  | .any => [tDot]
  | .alt l r => wrap 1 l l.toks ++ (tBar :: wrap 0 r r.toks)
  | .inter l r => wrap 2 l l.toks ++ (tAmp :: wrap 1 r r.toks)
  | .cat l r => wrap 3 l l.toks ++ wrap 2 r r.toks
  | .neg r => tTilde :: wrap 3 r r.toks
  | .star r => wrap 4 r r.toks ++ [tStar]
  | .plus r => wrap 4 r r.toks ++ [tPlus]
  | .opt r => wrap 4 r r.toks ++ [tQuest]
  | .rep r m n => wrap 4 r r.toks ++ [tLB, .int m, tComma, .int n, tRB]

/-- The tokens of `r` printed at level `k`. -/
def Re.toksAt (k : Nat) (r : Re) : List Tok := wrap k r r.toks

/-! ## Datalog tokens. -/

def Arg.tok : Arg → Tok
  | .var n => .ident n
  | .int z => .int z

/-- `x₁ s x₂ s … xₙ` (no brackets). -/
def sepBy {α : Type} (s : Tok) (f : α → List Tok) : List α → List Tok
  | [] => []
  | [x] => f x
  | x :: xs => f x ++ (s :: sepBy s f xs)

theorem sepBy_cons_cons {α : Type} (s : Tok) (f : α → List Tok) (x y : α) (ys : List α) :
    sepBy s f (x :: y :: ys) = f x ++ (s :: sepBy s f (y :: ys)) := rfl

/-- `a, b, c`. -/
abbrev commaSep {α : Type} (f : α → List Tok) : List α → List Tok := sepBy tComma f

def Atom.toks (a : Atom) : List Tok :=
  .ident a.pred :: tLP :: (commaSep (fun x => [Arg.tok x]) a.args ++ [tRP])

def Lit.toks (l : Lit) : List Tok := (if l.neg then [tBang] else []) ++ l.atom.toks

def Rule.toks (r : Rule) : List Tok :=
  kw "rule" :: (r.head.toks ++ ((if r.body = [] then [] else tTurn :: commaSep Lit.toks r.body) ++ [tDot]))

/-! ## Grammar tokens. -/

def GSym.tok : GSym → Tok
  | .nt n => .ident n
  | .t bs => .str bs

def altToks : List GSym → List Tok
  | [] => [.eps]
  | ss => ss.map GSym.tok

/-- `α₁ | α₂ | …` -/
abbrev barSep : List (List GSym) → List Tok := sepBy tBar altToks

def Prod.toks (p : Prod) : List Tok := .ident p.lhs :: tArrow :: (barSep p.alts ++ [tSemi])

/-! ## Budget and policy tokens. -/

def Agg.toks : Agg → List Tok
  | .sum p i => [kw "sum", tLP, .ident p, tDot, .int i, tRP]
  | .count p => [kw "count", tLP, .ident p, tRP]

def Claim.toks : Claim → List Tok
  | .forbidPattern p f => [kw "forbid", kw "pattern", .ident p, kw "in", .ident f, tSemi]
  | .requirePattern p f => [kw "require", kw "pattern", .ident p, kw "in", .ident f, tSemi]
  | .forbidRule p => [kw "forbid", kw "rule", .ident p, tSemi]
  | .requireRule p => [kw "require", kw "rule", .ident p, tSemi]
  | .requireBudget b => [kw "require", kw "budget", .ident b, tSemi]

/-- **`Decl.toks`**. -/
def Decl.toks : Decl → List Tok
  | .pattern n r => kw "pattern" :: .ident n :: tEq :: (r.toksAt 0 ++ [tSemi])
  | .grammar n ps => kw "grammar" :: .ident n :: tLB :: (ps.flatMap Prod.toks ++ [tRB])
  | .rule r => r.toks
  | .budget n a b => kw "budget" :: .ident n :: tColon :: (a.toks ++ [tLe, .int b, tSemi])
  | .policy n cs => kw "policy" :: .ident n :: tLB :: (cs.flatMap Claim.toks ++ [tRB])

def Policy.toks (p : Policy) : List Tok := p.decls.flatMap Decl.toks

/-! ## Layout. -/

/-- Where the printer would like no space between two tokens (a preference only: `sepWithin`
also asks `Tok.delim`). -/
def glue : Tok → Tok → Bool
  | _, .punct .rparen | _, .punct .comma | _, .punct .semi => true
  | _, .punct .star | _, .punct .plus | _, .punct .quest => true
  | .punct .lparen, _ | .punct .bang, _ | .punct .tilde, _ => true
  | .ident _, .punct .lparen | .ident _, .punct .dot | .ident _, .punct .colon => true
  | .punct .rparen, .punct .dot | .punct .dot, .int _ => true
  | .punct .lbrace, .int _ | .int _, .punct .rbrace => true
  | .str _, .punct .lbrace | .cls _ _, .punct .lbrace | .esc _, .punct .lbrace => true
  | .punct .rparen, .punct .lbrace | .punct .star, .punct .lbrace => true
  | .punct .plus, .punct .lbrace | .punct .quest, .punct .lbrace => true
  | .punct .rbrace, .punct .lbrace | .punct .dot, .punct .lbrace => true
  | _, _ => false

/-- The whitespace between two tokens on one line. -/
def sepWithin (t t' : Tok) : List Char :=
  if glue t t' && t.delim (t'.text.headD ' ') then [] else [' ']

/-- One line's tokens, each paired with the whitespace after it; the last gets `last`. -/
def layoutLine (last : List Char) : List Tok → List (Tok × List Char)
  | [] => []
  | [t] => [(t, last)]
  | t :: t' :: ts => (t, sepWithin t t') :: layoutLine last (t' :: ts)

def spaces (n : Nat) : List Char := List.replicate n ' '

/-- Lines `(indent, tokens)`; each line ends in a newline followed by the NEXT line's indent. -/
def layoutLines : List (Nat × List Tok) → List (Tok × List Char)
  | [] => []
  | [(_, ts)] => layoutLine ['\n'] ts
  | (_, ts) :: (i, ts') :: ls => layoutLine ('\n' :: spaces i) ts ++ layoutLines ((i, ts') :: ls)

def Decl.lines : Decl → List (Nat × List Tok)
  | .grammar n ps =>
      (0, [kw "grammar", .ident n, tLB]) :: (ps.map (fun p => (2, p.toks)) ++ [(0, [tRB])])
  | .policy n cs =>
      (0, [kw "policy", .ident n, tLB]) :: (cs.map (fun c => (2, c.toks)) ++ [(0, [tRB])])
  | d => [(0, d.toks)]

def Policy.lines (p : Policy) : List (Nat × List Tok) := p.decls.flatMap Decl.lines

def Policy.layout (p : Policy) : List (Tok × List Char) := layoutLines p.lines

def render (ps : List (Tok × List Char)) : List Char := ps.flatMap (fun p => p.1.text ++ p.2)

/-- **`print`** — the canonical text of a policy. -/
def print (p : Policy) : String := String.ofList (render p.layout)

/-- A regex alone, canonically (for messages). -/
def printRe (r : Re) : String := String.ofList (render (layoutLine [] (r.toksAt 0)))

end Dregg2.Policy
