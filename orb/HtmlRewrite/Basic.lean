/-!
# Streaming HTML tokenizer

A minimal, honest tokenizer that splits a byte stream into `text` and `tag`
tokens (`tag` = a `<…>` span; everything else is `text`). It is modelled as a
byte-fold with a carried state, which is exactly what makes it *streaming*: the
per-byte transition is the same whether the input arrives whole or split into
chunks.

The theorems:

* **chunk-boundary safety** (`feedBytes_append`, `stream_eq_whole`) — feeding the
  input split at *any* boundary yields the same tokenizer state as feeding it
  whole. This is the property a naive chunk-at-a-time rewriter gets wrong; here
  it is `List.foldl_append`.
* **byte conservation** (`feed_conserves`, `bytesOf_tokenize`) — every input byte
  ends up in exactly one token (or the in-progress buffer); nothing is dropped
  or duplicated, so re-serializing recovers the input (`roundtrip`).
-/

namespace HtmlRewrite

abbrev Byte := UInt8

/-- `<` and `>` as bytes. -/
def lt : Byte := 60
def gt : Byte := 62

/-- A token: a run of text, or a `<…>` tag span. Both retain their exact bytes
(a tag includes its `<` and `>`), so tokenization is lossless. -/
inductive Token where
  | text (bytes : List Byte)
  | tag (bytes : List Byte)
deriving Repr, DecidableEq

/-- The bytes a token carries. -/
def Token.bytes : Token → List Byte
  | .text b => b
  | .tag b => b

/-- Tokenizer mode: scanning text, or inside a tag. -/
inductive Mode where
  | text
  | tag
deriving Repr, DecidableEq

/-- Tokenizer state: the mode, the bytes of the token under construction, and the
completed tokens so far (most recent first). -/
structure TState where
  mode : Mode
  cur : List Byte
  toks : List Token
deriving Repr

/-- The initial state. -/
def init : TState := { mode := .text, cur := [], toks := [] }

/-- Flush the current buffer as a token of the given kind, if non-empty. -/
def flush (mkTok : List Byte → Token) (cur : List Byte) (toks : List Token) : List Token :=
  if cur = [] then toks else mkTok cur :: toks

/-- Feed one byte. In text mode, `<` closes any text run and opens a tag; other
bytes extend the text. In tag mode, `>` closes the tag; other bytes extend it. -/
def feed (s : TState) (b : Byte) : TState :=
  match s.mode with
  | .text =>
    if b = lt then
      { mode := .tag, cur := [lt], toks := flush Token.text s.cur s.toks }
    else
      { s with cur := s.cur ++ [b] }
  | .tag =>
    if b = gt then
      { mode := .text, cur := [], toks := Token.tag (s.cur ++ [gt]) :: s.toks }
    else
      { s with cur := s.cur ++ [b] }

/-- Fold the tokenizer over a byte list from a given state. -/
def feedBytes (s : TState) (bs : List Byte) : TState := bs.foldl feed s

/-- Tokenize a whole input from the initial state. -/
def tokenize (bs : List Byte) : TState := feedBytes init bs

/-- **Chunk-boundary safety (fold form).** Feeding `a` then `b` from a state is
the same as feeding `a ++ b` — the boundary is invisible. -/
theorem feedBytes_append (s : TState) (a b : List Byte) :
    feedBytes s (a ++ b) = feedBytes (feedBytes s a) b := by
  unfold feedBytes
  rw [List.foldl_append]

/-- **Chunk-boundary safety (streaming = whole).** Splitting the input at any
single boundary and streaming the two chunks yields the same final state as
tokenizing the whole input at once. -/
theorem stream_eq_whole (a b : List Byte) :
    feedBytes (tokenize a) b = tokenize (a ++ b) := by
  unfold tokenize
  rw [feedBytes_append]

/-- The bytes captured by a state: completed tokens (in chronological order)
followed by the in-progress buffer. -/
def bytesOf (s : TState) : List Byte :=
  (s.toks.reverse.flatMap Token.bytes) ++ s.cur

/-- **Byte conservation (per step).** Feeding one byte appends exactly that byte
to the captured bytes — nothing is dropped or duplicated. -/
theorem feed_conserves (s : TState) (b : Byte) :
    bytesOf (feed s b) = bytesOf s ++ [b] := by
  unfold feed bytesOf flush
  cases s.mode with
  | text =>
    by_cases hb : b = lt
    · subst hb
      by_cases hc : s.cur = []
      · simp [hc, Token.bytes]
      · simp [hc, Token.bytes, List.append_assoc]
    · simp [hb, List.append_assoc]
  | tag =>
    by_cases hb : b = gt
    · subst hb
      simp [Token.bytes, List.append_assoc]
    · simp [hb, List.append_assoc]

/-- **Byte conservation (whole).** Tokenizing an input captures exactly its
bytes — a lossless split. -/
theorem bytesOf_feedBytes (s : TState) (bs : List Byte) :
    bytesOf (feedBytes s bs) = bytesOf s ++ bs := by
  induction bs generalizing s with
  | nil => simp [feedBytes, bytesOf]
  | cons b bs ih =>
    unfold feedBytes at *
    simp only [List.foldl_cons]
    rw [ih, feed_conserves]
    simp

/-- **Round-trip / losslessness.** Re-serializing the captured bytes of a
tokenized input recovers the input exactly (identity rewrite is the identity). -/
theorem roundtrip (bs : List Byte) : bytesOf (tokenize bs) = bs := by
  unfold tokenize
  rw [bytesOf_feedBytes]
  simp [bytesOf, init]

/-- The tokenizer is total (a `def`, hence total on every input) — stated for the
record via a trivial reflexivity. -/
theorem feed_total (s : TState) (b : Byte) : feed s b = feed s b := rfl

/-- **Text safety.** In text mode a byte other than `<` is never treated as
markup — it just extends the current text run, and the mode stays `text`. -/
theorem text_stays_text (s : TState) (b : Byte) (hmode : s.mode = .text) (hb : b ≠ lt) :
    (feed s b).mode = .text := by
  simp [feed, hmode, hb]

def version : String := "0.1.0"

end HtmlRewrite
