/-
# Dregg2.Policy.Parser — hand-written recursive descent, total, with located errors.

Input: the lexer's positioned tokens (ending in `eof`). Output: `Except ParseError (α × rest)`.

**Termination, said exactly.** No `partial`. Three schemes:
  * `parseRe fuel lvl ts` is structural on `fuel`; `parseReTop` supplies `3 * ts.length + 6`, which
    `Theorems.lean` proves suffices for every printed regex (each call below level 5 either
    consumes a token or descends one level, and a parenthesis costs three units of fuel per token
    it encloses). Running out is an error, never a silent truncation.
  * `postfixLoop`, `parseGSyms`, `argsTail` are structural on the token list.
  * the list combinators `sepEnd` and `manyUntil` are structural on a fuel equal to the remaining
    token count (each element consumes at least one token).

Precedence, loosest first: `|` (level 0) < `&` (1) < concatenation (2) < prefix `~` (3) <
postfix `* + ? {m,n}` (4) < atoms (5). Binary operators associate to the right.
-/
import Dregg2.Policy.Pretty

namespace Dregg2.Policy


/-- The error "expected `exp` at the head of `ts`". -/
def errAt (ts : List PTok) (exp : List String) : ParseError :=
  match ts with
  | [] => ⟨Pos.start, "end of input", exp⟩
  | t :: _ => ⟨t.pos, t.tok.describe, exp⟩

def headTok (ts : List PTok) : Tok := match ts with | [] => .eof | t :: _ => t.tok

/-- Consume one punctuation token. -/
def expectP (p : Punct) (ts : List PTok) : Except ParseError (List PTok) :=
  match ts with
  | t :: rest => if t.tok = .punct p then .ok rest else .error (errAt ts [s!"`{String.ofList p.text}`"])
  | [] => .error (errAt [] [s!"`{String.ofList p.text}`"])

/-- Consume a keyword (a contextual identifier). -/
def expectKw (k : String) (ts : List PTok) : Except ParseError (List PTok) :=
  match ts with
  | t :: rest => if t.tok = .ident k then .ok rest else .error (errAt ts [s!"`{k}`"])
  | [] => .error (errAt [] [s!"`{k}`"])

/-- Consume an identifier. -/
def expectIdent (what : String) (ts : List PTok) : Except ParseError (String × List PTok) :=
  match ts with
  | t :: rest => match t.tok with
    | .ident s => .ok (s, rest)
    | _ => .error (errAt ts [what])
  | [] => .error (errAt [] [what])

/-- Consume a natural number. -/
def expectNat (ts : List PTok) : Except ParseError (Nat × List PTok) :=
  match ts with
  | t :: rest => match t.tok with
    | .int (.ofNat n) => .ok (n, rest)
    | _ => .error (errAt ts ["a natural number"])
  | [] => .error (errAt [] ["a natural number"])

/-! ## Regular expressions. -/

/-- Tokens that can begin a level-3 (unary) expression. -/
def startsUnary : Tok → Bool
  | .str _ | .cls _ _ | .esc _ | .punct .dot | .punct .lparen | .punct .tilde => true
  | _ => false

def atomExpected : List String :=
  ["a string literal", "a character class", "`\\d`", "`\\w`", "`\\s`", "`.`", "`(`", "`~`"]

/-- Postfix operators after an atom: `*`, `+`, `?`, `{m,n}`. Structural on the tokens. -/
def postfixLoop (acc : Re) : List PTok → Except ParseError (Re × List PTok)
  | [] => .ok (acc, [])
  | t :: ts =>
    match t.tok with
    | .punct .star => postfixLoop (.star acc) ts
    | .punct .plus => postfixLoop (.plus acc) ts
    | .punct .quest => postfixLoop (.opt acc) ts
    | .punct .lbrace =>
      match ts with
      | a :: ts1 =>
        match a.tok with
        | .int (.ofNat m) =>
          match ts1 with
          | b :: ts2 =>
            if b.tok = .punct .comma then
              match ts2 with
              | c :: ts3 =>
                match c.tok with
                | .int (.ofNat n) =>
                  match ts3 with
                  | d :: ts4 =>
                    if d.tok = .punct .rbrace then postfixLoop (.rep acc m n) ts4
                    else .error (errAt (d :: ts4) ["`}`"])
                  | [] => .error (errAt [] ["`}`"])
                | _ => .error (errAt (c :: ts3) ["a natural number"])
              | [] => .error (errAt [] ["a natural number"])
            else .error (errAt (b :: ts2) ["`,`"])
          | [] => .error (errAt [] ["`,`"])
        | _ => .error (errAt (a :: ts1) ["a natural number"])
      | [] => .error (errAt [] ["a natural number"])
    | _ => .ok (acc, t :: ts)

/-- **`parseRe fuel lvl ts`** — parse a regex at precedence level `lvl` (0 = loosest). -/
def parseRe : Nat → Nat → List PTok → Except ParseError (Re × List PTok)
  | 0, _, ts => .error (errAt ts ["a shallower regex (parser fuel exhausted)"])
  | n + 1, 0, ts => do
      let (l, ts) ← parseRe n 1 ts
      match ts with
      | t :: ts' =>
        if t.tok = .punct .bar then do
          let (r, ts'') ← parseRe n 0 ts'
          pure (.alt l r, ts'')
        else pure (l, t :: ts')
      | [] => pure (l, [])
  | n + 1, 1, ts => do
      let (l, ts) ← parseRe n 2 ts
      match ts with
      | t :: ts' =>
        if t.tok = .punct .amp then do
          let (r, ts'') ← parseRe n 1 ts'
          pure (.inter l r, ts'')
        else pure (l, t :: ts')
      | [] => pure (l, [])
  | n + 1, 2, ts => do
      let (l, ts) ← parseRe n 3 ts
      if startsUnary (headTok ts) then do
        let (r, ts') ← parseRe n 2 ts
        pure (.cat l r, ts')
      else pure (l, ts)
  | n + 1, 3, ts =>
      match ts with
      | t :: ts' =>
        if t.tok = .punct .tilde then do
          let (r, ts'') ← parseRe n 3 ts'
          pure (.neg r, ts'')
        else parseRe n 4 (t :: ts')
      | [] => parseRe n 4 []
  | n + 1, 4, ts => do
      let (a, ts) ← parseRe n 5 ts
      postfixLoop a ts
  | n + 1, _, ts =>
      match ts with
      | t :: ts' =>
        match t.tok with
        | .str bs => .ok (.lit bs, ts')
        | .cls neg rs => .ok (.set neg rs, ts')
        | .esc e => .ok (.esc e, ts')
        | .punct .dot => .ok (.any, ts')
        | .punct .lparen => do
            let (r, ts'') ← parseRe n 0 ts'
            let rest ← expectP .rparen ts''
            pure (r, rest)
        | _ => .error (errAt ts atomExpected)
      | [] => .error (errAt [] atomExpected)

/-- A regex with enough fuel (`Theorems.parseReTop_toks`). -/
def parseReTop (ts : List PTok) : Except ParseError (Re × List PTok) := parseRe (3 * ts.length + 6) 0 ts

/-! ## List combinators. -/

/-- `p (sep p)* term`, structural on fuel. -/
def sepEnd {α : Type} (p : List PTok → Except ParseError (α × List PTok)) (sep term : Punct) : Nat → List PTok → Except ParseError ((List α) × List PTok)
  | 0, ts => .error (errAt ts ["a shorter list (parser fuel exhausted)"])
  | n + 1, ts => do
      let (x, ts) ← p ts
      match ts with
      | t :: rest =>
        if t.tok = .punct sep then do
          let (xs, r) ← sepEnd p sep term n rest
          pure (x :: xs, r)
        else if t.tok = .punct term then pure ([x], rest)
        else .error (errAt ts [s!"`{String.ofList sep.text}`", s!"`{String.ofList term.text}`"])
      | [] => .error (errAt [] [s!"`{String.ofList sep.text}`", s!"`{String.ofList term.text}`"])

/-- `p*` up to (not consuming) a token satisfying `stop`, structural on fuel. -/
def manyUntil {α : Type} (p : List PTok → Except ParseError (α × List PTok)) (stop : Tok → Bool) : Nat → List PTok → Except ParseError ((List α) × List PTok)
  | 0, ts => .error (errAt ts ["a shorter list (parser fuel exhausted)"])
  | n + 1, ts =>
      if stop (headTok ts) then .ok ([], ts)
      else do
        let (x, ts) ← p ts
        let (xs, r) ← manyUntil p stop n ts
        pure (x :: xs, r)

/-! ## Datalog. -/

def argExpected : List String := ["a variable (capitalized identifier)", "an integer"]

def parseArg (t : PTok) : Except ParseError Arg :=
  match t.tok with
  | .ident s => if isVar s then .ok (.var s) else .error ⟨t.pos, t.tok.describe, argExpected⟩
  | .int z => .ok (.int z)
  | _ => .error ⟨t.pos, t.tok.describe, argExpected⟩

/-- After an argument: `)` or `, arg …`. Structural on the tokens. -/
def argsTail : List PTok → Except ParseError ((List Arg) × List PTok)
  | t :: ts =>
    if t.tok = .punct .rparen then .ok ([], ts)
    else if t.tok = .punct .comma then
      match ts with
      | a :: ts' => do
          let x ← parseArg a
          let (xs, r) ← argsTail ts'
          pure (x :: xs, r)
      | [] => .error (errAt [] argExpected)
    else .error (errAt (t :: ts) ["`,`", "`)`"])
  | [] => .error (errAt [] ["`,`", "`)`"])

/-- `(args)`. -/
def parseArgs (ts : List PTok) : Except ParseError ((List Arg) × List PTok) := do
  let ts ← expectP .lparen ts
  match ts with
  | t :: ts' =>
    if t.tok = .punct .rparen then pure ([], ts')
    else do
      let x ← parseArg t
      let (xs, r) ← argsTail ts'
      pure (x :: xs, r)
  | [] => .error (errAt [] ("`)`" :: argExpected))

def parseAtom (ts : List PTok) : Except ParseError (Atom × List PTok) := do
  let (p, ts) ← expectIdent "a predicate name" ts
  let (args, ts) ← parseArgs ts
  pure (⟨p, args⟩, ts)

def parseLit (ts : List PTok) : Except ParseError (Lit × List PTok) :=
  match ts with
  | t :: ts' =>
    if t.tok = .punct .bang then do
      let (a, r) ← parseAtom ts'
      pure (⟨true, a⟩, r)
    else do
      let (a, r) ← parseAtom ts
      pure (⟨false, a⟩, r)
  | [] => .error (errAt [] ["`!`", "a predicate name"])

/-- After `rule`: `head .` or `head :- lits .`. -/
def parseRule (ts : List PTok) : Except ParseError (Rule × List PTok) := do
  let (h, ts) ← parseAtom ts
  match ts with
  | t :: ts' =>
    if t.tok = .punct .dot then pure (⟨h, []⟩, ts')
    else if t.tok = .punct .turnstile then do
      let (body, r) ← sepEnd parseLit .comma .dot ts'.length ts'
      pure (⟨h, body⟩, r)
    else .error (errAt ts ["`:-`", "`.`"])
  | [] => .error (errAt [] ["`:-`", "`.`"])

/-! ## Grammars. -/

def isGSymTok : Tok → Bool
  | .ident _ | .str _ => true
  | _ => false

/-- Grammar symbols while the next token is an identifier or a string. Structural. -/
def parseGSyms : List PTok → List GSym × List PTok
  | t :: ts =>
    match t.tok with
    | .ident n => let p := parseGSyms ts; (.nt n :: p.1, p.2)
    | .str bs => let p := parseGSyms ts; (.t bs :: p.1, p.2)
    | _ => ([], t :: ts)
  | [] => ([], [])

/-- One alternative: `ε` or a nonempty symbol sequence. -/
def parseGAlt (ts : List PTok) : Except ParseError ((List GSym) × List PTok) :=
  match ts with
  | t :: ts' =>
    if t.tok = .eps then .ok ([], ts')
    else if isGSymTok t.tok then .ok (parseGSyms ts)
    else .error (errAt ts ["`ε`", "a nonterminal", "a string literal"])
  | [] => .error (errAt [] ["`ε`", "a nonterminal", "a string literal"])

/-- `S -> α | β ;` (or `S -> ;`). -/
def parseProd (ts : List PTok) : Except ParseError (Prod × List PTok) := do
  let (lhs, ts) ← expectIdent "a nonterminal" ts
  let ts ← expectP .arrow ts
  match ts with
  | t :: ts' =>
    if t.tok = .punct .semi then pure (⟨lhs, []⟩, ts')
    else do
      let (alts, r) ← sepEnd parseGAlt .bar .semi ts.length ts
      pure (⟨lhs, alts⟩, r)
  | [] => .error (errAt [] ["`;`", "`ε`", "a nonterminal", "a string literal"])

/-! ## Budgets and policies. -/

def parseAgg (ts : List PTok) : Except ParseError (Agg × List PTok) :=
  match ts with
  | t :: ts' =>
    if t.tok = .ident "sum" then do
      let ts ← expectP .lparen ts'
      let (p, ts) ← expectIdent "a predicate name" ts
      let ts ← expectP .dot ts
      let (i, ts) ← expectNat ts
      let ts ← expectP .rparen ts
      pure (.sum p i, ts)
    else if t.tok = .ident "count" then do
      let ts ← expectP .lparen ts'
      let (p, ts) ← expectIdent "a predicate name" ts
      let ts ← expectP .rparen ts
      pure (.count p, ts)
    else .error (errAt ts ["`sum`", "`count`"])
  | [] => .error (errAt [] ["`sum`", "`count`"])

def parseClaim (ts : List PTok) : Except ParseError (Claim × List PTok) :=
  match ts with
  | t :: k :: ts' =>
    let forbid := t.tok = .ident "forbid"
    if forbid || t.tok = .ident "require" then
      if k.tok = .ident "pattern" then do
        let (p, ts) ← expectIdent "a pattern name" ts'
        let ts ← expectKw "in" ts
        let (f, ts) ← expectIdent "a field name" ts
        let ts ← expectP .semi ts
        pure (if forbid then .forbidPattern p f else .requirePattern p f, ts)
      else if k.tok = .ident "rule" then do
        let (p, ts) ← expectIdent "a predicate name" ts'
        let ts ← expectP .semi ts
        pure (if forbid then .forbidRule p else .requireRule p, ts)
      else if k.tok = .ident "budget" && !forbid then do
        let (b, ts) ← expectIdent "a budget name" ts'
        let ts ← expectP .semi ts
        pure (.requireBudget b, ts)
      else .error (errAt (k :: ts')
        (if forbid then ["`pattern`", "`rule`"] else ["`pattern`", "`rule`", "`budget`"]))
    else .error (errAt (t :: k :: ts') ["`forbid`", "`require`", "`}`"])
  | ts => .error (errAt ts ["`forbid`", "`require`", "`}`"])

/-! ## Declarations. -/

def declExpected : List String := ["`pattern`", "`grammar`", "`rule`", "`budget`", "`policy`"]

def parseDecl (ts : List PTok) : Except ParseError (Decl × List PTok) :=
  match ts with
  | t :: ts' =>
    if t.tok = .ident "pattern" then do
      let (n, ts) ← expectIdent "a pattern name" ts'
      let ts ← expectP .eq ts
      let (r, ts) ← parseReTop ts
      let ts ← expectP .semi ts
      pure (.pattern n r, ts)
    else if t.tok = .ident "grammar" then do
      let (n, ts) ← expectIdent "a grammar name" ts'
      let ts ← expectP .lbrace ts
      let (ps, ts) ← manyUntil parseProd (· = .punct .rbrace) ts.length ts
      let ts ← expectP .rbrace ts
      pure (.grammar n ps, ts)
    else if t.tok = .ident "rule" then do
      let (r, ts) ← parseRule ts'
      pure (.rule r, ts)
    else if t.tok = .ident "budget" then do
      let (n, ts) ← expectIdent "a budget name" ts'
      let ts ← expectP .colon ts
      let (a, ts) ← parseAgg ts
      let ts ← expectP .le ts
      let (b, ts) ← expectNat ts
      let ts ← expectP .semi ts
      pure (.budget n a b, ts)
    else if t.tok = .ident "policy" then do
      let (n, ts) ← expectIdent "a policy name" ts'
      let ts ← expectP .lbrace ts
      let (cs, ts) ← manyUntil parseClaim (· = .punct .rbrace) ts.length ts
      let ts ← expectP .rbrace ts
      pure (.policy n cs, ts)
    else .error (errAt ts declExpected)
  | [] => .error (errAt [] declExpected)

/-- **`parseTokens`** — a whole file's tokens, through `eof`. -/
def parseTokens (ts : List PTok) : Except ParseError Policy := do
  let (ds, rest) ← manyUntil parseDecl (· = .eof) ts.length ts
  match rest with
  | [t] => if t.tok = .eof then pure ⟨ds⟩ else .error (errAt rest ["end of input"])
  | _ => .error (errAt rest ["end of input"])

/-- **`parse`** — source text to a policy, or a located error. -/
def parse (s : String) : Except ParseError Policy := do
  let ts ← lex s
  parseTokens ts

/-! ## Smoke tests. -/

#guard (parse "pattern p = \"a\" | \"b\" \"c\"* ;").toOption ==
  some ⟨[.pattern "p" (.alt (.lit [97]) (.cat (.lit [98]) (.star (.lit [99]))))]⟩
#guard (parse "rule path(X, Z) :- edge(X, Y), !blocked(Y), path(Y, Z).").toOption ==
  some ⟨[.rule ⟨⟨"path", [.var "X", .var "Z"]⟩,
    [⟨false, ⟨"edge", [.var "X", .var "Y"]⟩⟩, ⟨true, ⟨"blocked", [.var "Y"]⟩⟩,
     ⟨false, ⟨"path", [.var "Y", .var "Z"]⟩⟩]⟩]⟩

end Dregg2.Policy
