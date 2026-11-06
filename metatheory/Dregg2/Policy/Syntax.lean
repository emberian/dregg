/-
# Dregg2.Policy.Syntax — the abstract syntax of the policy language.

One surface for the four claim families the automata program arithmetizes
(`docs/automata/SUBSTRATE-DECISION.md` §5 item 5): byte patterns with native intersection and
complement (elaborated to `Crypto.Deriv.PredRE`), context-free grammars (to mathlib's
`ContextFreeGrammar`), Datalog rules with negation (to `Datalog.FixpointCert.Program` for the
positive fragment), and aggregate budgets. A `policy NAME { … }` block is a conjunction of named
claims over named fields, the shape of Lucid's `policy.forbid(...)`.

Every constructor here elaborates to an existing Lean object (`Elab.lean`); nothing in this file
has a meaning of its own beyond being the parser's output and the printer's input.

    pattern NAME = <re> ;
    grammar NAME { S -> "[" S "]" | ε ; }
    rule head(X, 1) :- body(X), !neg(X) .
    budget NAME : sum(pred.1) <= 100 ;      budget NAME : count(pred) <= 0 ;
    policy NAME { forbid pattern P in FIELD ; require rule R ; require budget B ; }

The well-formedness predicate `Policy.wf` (identifiers are identifiers, variables are capitalized,
bytes are bytes) is what the round-trip theorem assumes; the parser's output always satisfies it
by construction of the lexer, and `Theorems.lean` states which direction is proved.
-/

namespace Dregg2.Policy

/-! ## Regular expressions over bytes. -/

/-- The three backslash classes. `\d` = `[0-9]`, `\w` = `[0-9A-Z_a-z]`, `\s` = `[\t\n\x0b\x0c\r ]`. -/
inductive ClassEsc where
  | digit
  | word
  | space
  deriving Repr, DecidableEq, Inhabited

/-- A surface regular expression over the byte alphabet. Bytes are `Nat`s below 256 (`Re.wf`). -/
inductive Re where
  /-- A string literal `"abc"`: exactly this byte sequence (`""` is the empty word). -/
  | lit (bs : List Nat)
  /-- A bracket class `[a-z_]` (or `[^…]` when `neg`): one byte in (or not in) the inclusive ranges. -/
  | set (neg : Bool) (rs : List (Nat × Nat))
  /-- `\d`, `\w`, `\s`. -/
  | esc (e : ClassEsc)
  /-- `.`: any one byte. -/
  | any
  /-- `l | r`. -/
  | alt (l r : Re)
  /-- `l & r`: intersection (native, the derivative engine's `inter`). -/
  | inter (l r : Re)
  /-- `l r`: concatenation. -/
  | cat (l r : Re)
  /-- `~r`: complement over byte WORDS (not over single bytes; `. & ~[a]` is "one byte, not `a`"). -/
  | neg (r : Re)
  /-- `r*`. -/
  | star (r : Re)
  /-- `r+`. -/
  | plus (r : Re)
  /-- `r?`. -/
  | opt (r : Re)
  /-- `r{m,n}`: between `m` and `n` copies (empty language when `m > n`). -/
  | rep (r : Re) (m n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-! ## Grammars. -/

/-- A grammar symbol: a nonterminal name or a terminal string (a run of terminal bytes). -/
inductive GSym where
  | nt (name : String)
  | t (bs : List Nat)
  deriving Repr, DecidableEq, Inhabited

/-- One production group `S -> α₁ | α₂ | … ;`. An empty alternative is `ε`. -/
structure Prod where
  lhs : String
  alts : List (List GSym)
  deriving Repr, DecidableEq, Inhabited

/-! ## Datalog. -/

/-- A rule argument: a capitalized variable or an integer constant. -/
inductive Arg where
  | var (name : String)
  | int (z : Int)
  deriving Repr, DecidableEq, Inhabited

/-- An atom `pred(args)`. -/
structure Atom where
  pred : String
  args : List Arg
  deriving Repr, DecidableEq, Inhabited

/-- A body literal: `atom` or `!atom`. -/
structure Lit where
  neg : Bool
  atom : Atom
  deriving Repr, DecidableEq, Inhabited

/-- `head :- body.` (a fact when `body = []`). -/
structure Rule where
  head : Atom
  body : List Lit
  deriving Repr, DecidableEq, Inhabited

/-! ## Budgets and policies. -/

/-- The aggregate a budget bounds: `sum(pred.i)` (argument position `i`, 0-based) or `count(pred)`. -/
inductive Agg where
  | sum (pred : String) (pos : Nat)
  | count (pred : String)
  deriving Repr, DecidableEq, Inhabited

/-- A claim inside `policy NAME { … }`. -/
inductive Claim where
  /-- `forbid pattern P in F;` — no substring of field `F` matches `P`. -/
  | forbidPattern (pat field : String)
  /-- `require pattern P in F;` — field `F` (the whole field) matches `P`. -/
  | requirePattern (pat field : String)
  /-- `forbid rule R;` — predicate `R` has no derivable fact (an exact `Count = 0`). -/
  | forbidRule (pred : String)
  /-- `require rule R;` — predicate `R` has at least one derivable fact. -/
  | requireRule (pred : String)
  /-- `require budget B;` — budget `B` holds. -/
  | requireBudget (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- A top-level declaration. -/
inductive Decl where
  | pattern (name : String) (re : Re)
  | grammar (name : String) (prods : List Prod)
  | rule (r : Rule)
  | budget (name : String) (agg : Agg) (bound : Nat)
  | policy (name : String) (claims : List Claim)
  deriving Repr, DecidableEq, Inhabited

/-- A policy file: a list of declarations. -/
structure Policy where
  decls : List Decl
  deriving Repr, DecidableEq, Inhabited

/-! ## Well-formedness — what the round trip assumes. -/

/-- Identifier start character: an ASCII letter or `_`. -/
def isIdStart (c : Char) : Bool := c.isAlpha || c == '_'

/-- Identifier continuation character: an ASCII letter, digit, or `_`. -/
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- An identifier: nonempty, starts with a letter or `_`, continues with letters, digits, `_`. -/
def isIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdStart c && cs.all isIdChar

/-- A variable: an identifier whose first character is an uppercase ASCII letter. -/
def isVar (s : String) : Bool :=
  isIdent s && (match s.toList with | c :: _ => c.isUpper | [] => false)

/-- A byte. -/
def isByte (b : Nat) : Bool := decide (b < 256)

/-- Bytes of a regex / grammar terminal are bytes. -/
def Re.wf : Re → Bool
  | .lit bs => bs.all isByte
  | .set _ rs => rs.all (fun p => isByte p.1 && isByte p.2)
  | .esc _ => true
  | .any => true
  | .alt l r => l.wf && r.wf
  | .inter l r => l.wf && r.wf
  | .cat l r => l.wf && r.wf
  | .neg r => r.wf
  | .star r => r.wf
  | .plus r => r.wf
  | .opt r => r.wf
  | .rep r _ _ => r.wf

def GSym.wf : GSym → Bool
  | .nt n => isIdent n
  | .t bs => bs.all isByte

def Prod.wf (p : Prod) : Bool := isIdent p.lhs && p.alts.all (fun a => a.all GSym.wf)

def Arg.wf : Arg → Bool
  | .var n => isVar n
  | .int _ => true

def Atom.wf (a : Atom) : Bool := isIdent a.pred && a.args.all Arg.wf

def Rule.wf (r : Rule) : Bool := r.head.wf && r.body.all (fun l => l.atom.wf)

def Agg.wf : Agg → Bool
  | .sum p _ => isIdent p
  | .count p => isIdent p

def Claim.wf : Claim → Bool
  | .forbidPattern p f => isIdent p && isIdent f
  | .requirePattern p f => isIdent p && isIdent f
  | .forbidRule p => isIdent p
  | .requireRule p => isIdent p
  | .requireBudget b => isIdent b

def Decl.wf : Decl → Bool
  | .pattern n r => isIdent n && r.wf
  | .grammar n ps => isIdent n && ps.all Prod.wf
  | .rule r => r.wf
  | .budget n a _ => isIdent n && a.wf
  | .policy n cs => isIdent n && cs.all Claim.wf

def Policy.wf (p : Policy) : Bool := p.decls.all Decl.wf

/-! ## The class escapes as byte ranges (shared by the semantics and the elaborator). -/

def ClassEsc.ranges : ClassEsc → List (Nat × Nat)
  | .digit => [(48, 57)]
  | .word => [(48, 57), (65, 90), (95, 95), (97, 122)]
  | .space => [(9, 13), (32, 32)]

/-- `c` lies in one of the inclusive ranges. -/
def inRanges (rs : List (Nat × Nat)) (c : Nat) : Bool := rs.any (fun p => p.1 ≤ c && c ≤ p.2)

end Dregg2.Policy
