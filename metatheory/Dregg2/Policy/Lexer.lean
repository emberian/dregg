/-
# Dregg2.Policy.Lexer — tokens, their canonical spelling, and a total, position-tracking lexer.

The lexer reads a `List Char` (the source's `String.toList`) and produces a list of positioned
tokens ending in exactly one `eof`. It is total: every function here is structural (the main loop
on a fuel argument equal to the input length plus one, each iteration consuming at least one
character; the sub-lexers on the character list itself). Errors carry a 1-based `line:col`, the
text found there, and the set of things that would have been accepted.

`Tok.text` is the canonical spelling the printer uses. `Theorems.lean` proves the lexer inverts
it: `lex` of any whitespace-separated rendering of well-formed tokens returns exactly those tokens
(`lex_render`). The spelling choices are made so that inversion holds without look-behind:

  * a class byte is written raw (printable ASCII other than `] \ - ^ [`), escaped (`\] \\ \- \^ \[`),
    or as `\xHH`; the brief's `[0x00-0x1f]` is spelled `[\x00-\x1f]` here, because a `0x` prefix
    inside a class is ambiguous with the two raw bytes `0`, `x` (`[0x41]` would be both);
  * a string byte is raw printable ASCII other than `"` and `\`, or `\"`, `\\`, `\xHH`;
  * two tokens may be glued with no space only when `Tok.delim` says the first token's lexer stops
    at the second token's first character.
-/
import Dregg2.Policy.Syntax

namespace Dregg2.Policy

/-! ## Tokens. -/

inductive Punct where
  | lparen | rparen | lbrace | rbrace | comma | semi | dot | bar | amp | tilde
  | star | plus | quest | bang | colon | turnstile | arrow | le | eq
  deriving Repr, DecidableEq, Inhabited

inductive Tok where
  | ident (s : String)
  | int (z : Int)
  | str (bs : List Nat)
  | cls (neg : Bool) (rs : List (Nat × Nat))
  | esc (e : ClassEsc)
  | eps
  | punct (p : Punct)
  | eof
  deriving Repr, DecidableEq, Inhabited

/-- A 1-based source position. -/
structure Pos where
  line : Nat
  col : Nat
  deriving Repr, DecidableEq, Inhabited

def Pos.start : Pos := ⟨1, 1⟩

instance : ToString Pos := ⟨fun p => s!"{p.line}:{p.col}"⟩

structure PTok where
  tok : Tok
  pos : Pos
  deriving Repr, DecidableEq, Inhabited

/-- A located error: where, what was found, what would have been accepted. -/
structure ParseError where
  pos : Pos
  found : String
  expected : List String
  deriving Repr, DecidableEq, Inhabited

instance : ToString ParseError :=
  ⟨fun e => s!"{e.pos}: found {e.found}, expected one of {e.expected}"⟩

/-! ## Character helpers. -/

def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

def hexChar (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

def isHexDigit (c : Char) : Bool :=
  c.isDigit || (decide ('a' ≤ c) && decide (c ≤ 'f')) || (decide ('A' ≤ c) && decide (c ≤ 'F'))

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48
  else if decide ('a' ≤ c) && decide (c ≤ 'f') then c.toNat - 87
  else c.toNat - 55

def hex2 (b : Nat) : List Char := [hexChar (b / 16), hexChar (b % 16)]

/-- The decimal digits of `n`, most significant first. -/
def natDigits (n : Nat) : List Char :=
  if h : n < 10 then [digitChar n]
  else natDigits (n / 10) ++ [digitChar (n % 10)]
termination_by n
decreasing_by omega

def digitsVal (cs : List Char) : Nat := cs.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

def isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-! ## Canonical spelling. -/

/-- Printable ASCII written raw inside a string literal. -/
def strRaw (b : Nat) : Bool := decide (32 ≤ b) && decide (b < 127) && b != 34 && b != 92

def strByte (b : Nat) : List Char :=
  if b == 34 then ['\\', '"']
  else if b == 92 then ['\\', '\\']
  else if strRaw b then [Char.ofNat b]
  else '\\' :: 'x' :: hex2 b

/-- Class bytes needing a backslash: `]` `\` `-` `^` `[`. -/
def clsSpecial (b : Nat) : Bool := b == 93 || b == 92 || b == 45 || b == 94 || b == 91

def clsRaw (b : Nat) : Bool := decide (33 ≤ b) && decide (b < 127) && !clsSpecial b

def clsByte (b : Nat) : List Char :=
  if clsSpecial b then ['\\', Char.ofNat b]
  else if clsRaw b then [Char.ofNat b]
  else '\\' :: 'x' :: hex2 b

def rangeText (p : Nat × Nat) : List Char :=
  clsByte p.1 ++ (if p.1 == p.2 then [] else '-' :: clsByte p.2)

def ClassEsc.char : ClassEsc → Char
  | .digit => 'd'
  | .word => 'w'
  | .space => 's'

def Punct.text : Punct → List Char
  | .lparen => ['('] | .rparen => [')'] | .lbrace => ['{'] | .rbrace => ['}']
  | .comma => [','] | .semi => [';'] | .dot => ['.'] | .bar => ['|'] | .amp => ['&']
  | .tilde => ['~'] | .star => ['*'] | .plus => ['+'] | .quest => ['?'] | .bang => ['!']
  | .colon => [':'] | .turnstile => [':', '-'] | .arrow => ['-', '>'] | .le => ['<', '=']
  | .eq => ['=']

def intText (z : Int) : List Char :=
  match z with
  | .ofNat n => natDigits n
  | .negSucc n => '-' :: natDigits (n + 1)

/-- **`Tok.text`** — the canonical spelling of a token. -/
def Tok.text : Tok → List Char
  | .ident s => s.toList
  | .int z => intText z
  | .str bs => '"' :: (bs.flatMap strByte ++ ['"'])
  | .cls neg rs => '[' :: ((if neg then ['^'] else []) ++ (rs.flatMap rangeText ++ [']']))
  | .esc e => ['\\', e.char]
  | .eps => ['ε']
  | .punct p => p.text
  | .eof => []

/-- **`Tok.delim t c`** — the lexer, having read `t.text`, stops before a following `c` (so the
two may be written with no space between them). -/
def Tok.delim : Tok → Char → Bool
  | .ident _, c => !isIdChar c
  | .int _, c => !c.isDigit
  | .punct .colon, c => c != '-'
  | _, _ => true

/-- A short human description of a token (for error messages). -/
def Tok.describe : Tok → String
  | .eof => "end of input"
  | .ident s => s!"identifier `{s}`"
  | .int z => s!"integer {z}"
  | .str _ => "string literal"
  | .cls _ _ => "character class"
  | t => s!"`{String.ofList t.text}`"

/-! ## Sub-lexers. Each returns the rest of the input; an error carries the length of the input
remaining at the error point (the main loop turns that into a column). -/

/-- An error inside a token: remaining length, found, expected. -/
abbrev LexErr := Nat × String × List String

/-- `spanP p cs`: the longest `p`-prefix and the rest. -/
def spanP (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if p c then ((c :: (spanP p cs).1), (spanP p cs).2) else ([], c :: cs)

def foundOf : List Char → String
  | [] => "end of input"
  | c :: _ => s!"`{c}`"

def escExpected : List String := ["\\xHH", "\\\"", "\\\\", "\\n", "\\t", "\\r"]

/-- Read `\xHH`'s two hex digits. -/
def lexHex : List Char → Except LexErr (Nat × List Char)
  | h1 :: h2 :: rest =>
      if isHexDigit h1 && isHexDigit h2 then .ok (hexVal h1 * 16 + hexVal h2, rest)
      else .error ((h1 :: h2 :: rest).length, foundOf (h1 :: h2 :: rest), ["two hex digits"])
  | cs => .error (cs.length, foundOf cs, ["two hex digits"])

/-- The body of a string literal, after the opening `"`, through the closing `"`. -/
def lexStr : List Char → Except LexErr (List Nat × List Char)
  | [] => .error (0, "end of input", ["`\"`"])
  | '"' :: rest => .ok ([], rest)
  | '\n' :: rest => .error (rest.length + 1, "newline", ["`\"`"])
  | '\\' :: 'x' :: h1 :: h2 :: rest =>
      if isHexDigit h1 && isHexDigit h2 then
        (lexStr rest).map (fun p => ((hexVal h1 * 16 + hexVal h2) :: p.1, p.2))
      else .error ((h1 :: h2 :: rest).length, foundOf (h1 :: h2 :: rest), ["two hex digits"])
  | '\\' :: 'x' :: rest => .error (rest.length, foundOf rest, ["two hex digits"])
  | '\\' :: '"' :: rest => (lexStr rest).map (fun p => (34 :: p.1, p.2))
  | '\\' :: '\\' :: rest => (lexStr rest).map (fun p => (92 :: p.1, p.2))
  | '\\' :: 'n' :: rest => (lexStr rest).map (fun p => (10 :: p.1, p.2))
  | '\\' :: 't' :: rest => (lexStr rest).map (fun p => (9 :: p.1, p.2))
  | '\\' :: 'r' :: rest => (lexStr rest).map (fun p => (13 :: p.1, p.2))
  | '\\' :: rest => .error (rest.length, foundOf rest, escExpected)
  | c :: rest =>
      if c.toNat < 128 then (lexStr rest).map (fun p => (c.toNat :: p.1, p.2))
      else (lexStr rest).map (fun p => ((String.utf8EncodeChar c).map (·.toNat) ++ p.1, p.2))

def clsEscExpected : List String := ["\\xHH", "\\]", "\\\\", "\\-", "\\^", "\\[", "\\n", "\\t", "\\r"]

/-- One class byte (raw or escaped). -/
def lexClsByte : List Char → Except LexErr (Nat × List Char)
  | '\\' :: 'x' :: rest => lexHex rest
  | '\\' :: c :: rest =>
      if c == ']' || c == '\\' || c == '-' || c == '^' || c == '[' then .ok (c.toNat, rest)
      else if c == 'n' then .ok (10, rest)
      else if c == 't' then .ok (9, rest)
      else if c == 'r' then .ok (13, rest)
      else .error ((c :: rest).length, s!"`{c}`", clsEscExpected)
  | c :: rest =>
      if c == ']' || c == '-' || c == '\\' || c == '\n' || c.toNat ≥ 128 then
        .error ((c :: rest).length, s!"`{c}`", ["a class byte"])
      else .ok (c.toNat, rest)
  | [] => .error (0, "end of input", ["a class byte", "`]`"])

theorem lexHex_len {cs rest : List Char} {b : Nat} (h : lexHex cs = .ok (b, rest)) :
    rest.length + 2 = cs.length := by
  unfold lexHex at h
  split at h
  · split at h
    · cases h; simp only [List.length_cons]
    · cases h
  · cases h

theorem lexClsByte_len {cs rest : List Char} {b : Nat} (h : lexClsByte cs = .ok (b, rest)) :
    rest.length < cs.length := by
  unfold lexClsByte at h
  split at h
  · have := lexHex_len h; simp; omega
  · split at h
    · cases h; simp only [List.length_cons]; omega
    · split at h
      · cases h; simp only [List.length_cons]; omega
      · split at h
        · cases h; simp only [List.length_cons]; omega
        · split at h
          · cases h; simp only [List.length_cons]; omega
          · cases h
  · split at h
    · cases h
    · cases h; simp only [List.length_cons]; omega
  · cases h

/-- The items of a class through the closing `]`. Well-founded on the input length
(`lexClsByte_len`). -/
def lexClsItems (cs : List Char) : Except LexErr (List (Nat × Nat) × List Char) :=
  match cs with
  | [] => .error (0, "end of input", ["`]`"])
  | ']' :: rest => .ok ([], rest)
  | c :: cs' =>
      match h : lexClsByte (c :: cs') with
      | .error e => .error e
      | .ok (lo, rest) =>
          have h1 : rest.length < (c :: cs').length := lexClsByte_len h
          match rest, h1 with
          | '-' :: rest2, h1 =>
              match h2 : lexClsByte rest2 with
              | .error e => .error e
              | .ok (hi, rest3) =>
                  have : rest3.length < (c :: cs').length := by
                    have := lexClsByte_len h2; simp at h1 ⊢; omega
                  (lexClsItems rest3).map (fun p => ((lo, hi) :: p.1, p.2))
          | rest, h1 => (lexClsItems rest).map (fun p => ((lo, lo) :: p.1, p.2))
termination_by cs.length

/-- A class after its `[`. -/
def lexClass : List Char → Except LexErr (Tok × List Char)
  | '^' :: rest => (lexClsItems rest).map (fun p => (.cls true p.1, p.2))
  | cs => (lexClsItems cs).map (fun p => (.cls false p.1, p.2))

def escClassExpected : List String := ["\\d", "\\w", "\\s"]

/-- **`lexToken`** — one token from a nonempty, non-whitespace input. -/
def lexToken : List Char → Except LexErr (Tok × List Char)
  | [] => .error (0, "end of input", ["a token"])
  | c :: cs =>
      if isIdStart c then
        let p := spanP isIdChar (c :: cs)
        .ok (.ident (String.ofList p.1), p.2)
      else if c.isDigit then
        let p := spanP Char.isDigit (c :: cs)
        .ok (.int (Int.ofNat (digitsVal p.1)), p.2)
      else match c, cs with
      | '-', d :: ds =>
          if d.isDigit then
            let p := spanP Char.isDigit (d :: ds)
            .ok (.int (-(Int.ofNat (digitsVal p.1))), p.2)
          else if d == '>' then .ok (.punct .arrow, ds)
          else .error ((d :: ds).length, s!"`{d}`", ["`->`", "a digit"])
      | '-', [] => .error (0, "end of input", ["`->`", "a digit"])
      | ':', '-' :: ds => .ok (.punct .turnstile, ds)
      | ':', ds => .ok (.punct .colon, ds)
      | '<', '=' :: ds => .ok (.punct .le, ds)
      | '<', ds => .error (ds.length, foundOf ds, ["`<=`"])
      | '"', ds => (lexStr ds).map (fun p => (.str p.1, p.2))
      | '[', ds => lexClass ds
      | '\\', d :: ds =>
          if d == 'd' then .ok (.esc .digit, ds)
          else if d == 'w' then .ok (.esc .word, ds)
          else if d == 's' then .ok (.esc .space, ds)
          else .error ((d :: ds).length, s!"`\\{d}`", escClassExpected)
      | '\\', [] => .error (0, "end of input", escClassExpected)
      | 'ε', ds => .ok (.eps, ds)
      | '(', ds => .ok (.punct .lparen, ds)
      | ')', ds => .ok (.punct .rparen, ds)
      | '{', ds => .ok (.punct .lbrace, ds)
      | '}', ds => .ok (.punct .rbrace, ds)
      | ',', ds => .ok (.punct .comma, ds)
      | ';', ds => .ok (.punct .semi, ds)
      | '.', ds => .ok (.punct .dot, ds)
      | '|', ds => .ok (.punct .bar, ds)
      | '&', ds => .ok (.punct .amp, ds)
      | '~', ds => .ok (.punct .tilde, ds)
      | '*', ds => .ok (.punct .star, ds)
      | '+', ds => .ok (.punct .plus, ds)
      | '?', ds => .ok (.punct .quest, ds)
      | '!', ds => .ok (.punct .bang, ds)
      | '=', ds => .ok (.punct .eq, ds)
      | c, ds => .error ((c :: ds).length, s!"`{c}`", ["a token"])

/-- Skip a `#` comment through (not including) the newline. -/
def skipComment : List Char → List Char
  | [] => []
  | '\n' :: rest => '\n' :: rest
  | _ :: rest => skipComment rest

/-- **The main loop.** Fuel = input length + 1 suffices (`lex` supplies it); running out of fuel
is reported as an error, never silently. -/
def lexAux : Nat → Pos → List Char → Except ParseError (List PTok)
  | 0, pos, _ => .error ⟨pos, "input", ["lexer fuel (input too long)"]⟩
  | _ + 1, pos, [] => .ok [⟨.eof, pos⟩]
  | fuel + 1, pos, c :: cs =>
      if c == '\n' then lexAux fuel ⟨pos.line + 1, 1⟩ cs
      else if isWs c then lexAux fuel ⟨pos.line, pos.col + 1⟩ cs
      else if c == '#' then
        let rest := skipComment cs
        lexAux fuel ⟨pos.line, pos.col + 1 + (cs.length - rest.length)⟩ rest
      else match lexToken (c :: cs) with
        | .error (rem, found, exp) =>
            .error ⟨⟨pos.line, pos.col + ((c :: cs).length - rem)⟩, found, exp⟩
        | .ok (t, rest) =>
            if rest.length < (c :: cs).length then
              (lexAux fuel ⟨pos.line, pos.col + ((c :: cs).length - rest.length)⟩ rest).map
                (fun ts => ⟨t, pos⟩ :: ts)
            else .error ⟨pos, s!"`{c}`", ["progress (lexer bug)"]⟩

/-- **`lexChars`** — lex a character list. -/
def lexChars (cs : List Char) : Except ParseError (List PTok) := lexAux (cs.length + 1) Pos.start cs

/-- **`lex`** — lex a source string. -/
def lex (s : String) : Except ParseError (List PTok) := lexChars s.toList

/-! ## Smoke tests (compiled evaluation). -/

#guard (lex "pattern p = \"ab\" [a-z]* ;").toOption.map (·.map (·.tok)) ==
  some [.ident "pattern", .ident "p", .punct .eq, .str [97, 98], .cls false [(97, 122)],
       .punct .star, .punct .semi, .eof]
#guard (lex "rule p(X, -3) :- q(X).").toOption.map (·.map (·.tok)) ==
  some [.ident "rule", .ident "p", .punct .lparen, .ident "X", .punct .comma, .int (-3),
       .punct .rparen, .punct .turnstile, .ident "q", .punct .lparen, .ident "X", .punct .rparen,
       .punct .dot, .eof]
#guard (lex "[^\\x00-\\x1f\\]] \\d").toOption.map (·.map (·.tok)) ==
  some [.cls true [(0, 31), (93, 93)], .esc .digit, .eof]
#guard (lex "# comment\nS -> ε").toOption.map (·.map (·.tok)) ==
  some [.ident "S", .punct .arrow, .eps, .eof]

end Dregg2.Policy
