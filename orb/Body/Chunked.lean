import Body.Hex

/-!
# Chunked transfer-encoding (RFC 7230 §4.1)

A chunked body is a sequence of chunks

    chunk-size [ chunk-ext ] CRLF chunk-data CRLF

terminated by a zero-size chunk (`0 CRLF CRLF`). This file models the decode as
a header parse plus a single-frame decoder plus a streaming fold, and proves the
byte accounting.

Layered as:

* `findCrlf` — the chunk-size line terminator scan, with a bound
  (`findCrlf_some_bound`) that a found CRLF fits in the buffer.
* `parseHeader` — parse one chunk header to `(size, headerLen)`. **Theorem 3**:
  `parseHeader_total` (defined on every input) and `parseHeader_consumed`
  (`0 < headerLen ≤ buffer length` — consumed-monotone). **Theorem 5**:
  `parseHeader_overflow` (a size over `maxChunkSize` is a total error) and
  `parseHeader_bad_hex` (a non-hex / empty size token is a total error).
* `decodeFrame` — decode one frame to `incomplete | error | chunk data c |
  terminal c`. `decodeFrame_chunk_bound` gives `0 < c ≤ buffer length` (this is
  what makes the streaming fold terminate).
* `decodeStream` — fold frames to a terminal `complete`. **Theorem 2**:
  `decodeStream_encodeStream` — decoding the encoding of a chunk list recovers
  exactly the in-order concatenation of the payloads (`chunks.flatten`), so the
  delivered byte count is `Σ chunk sizes` and no framing octet (size digits,
  CRLFs, terminal) leaks into the body. **Theorem 4**:
  `decodeStream_encodeChunks_incomplete` — a stream missing its terminal chunk
  stays `incomplete`, never falsely `complete`.

Deliberately out of scope: chunk extensions (`chunk-ext`) and trailer header
fields; the terminal is modeled as the bare `0 CRLF CRLF`.
-/

namespace Body
namespace Chunked

open Body.Hex

/-- The largest `chunk-size` the parser admits. A size octet-run denoting more
than this is rejected as a total error — the model of the reference decoder's
`usize`/`checked_add` overflow guard. -/
def maxChunkSize : Nat := 2 ^ 63

/-! ## Chunk-size line scan -/

/-- Offset of the first `CRLF` in the buffer, if any. -/
def findCrlf : Bytes → Option Nat
  | a :: b :: rest => if a = CR ∧ b = LF then some 0 else (findCrlf (b :: rest)).map (· + 1)
  | _ => none

/-- If the size line has no CR octet, the first CRLF is exactly at its end — the
line terminator is unambiguous. -/
theorem findCrlf_append_no_cr : ∀ (pre rest : Bytes), (∀ b ∈ pre, b ≠ CR) →
    findCrlf (pre ++ CR :: LF :: rest) = some pre.length := by
  intro pre
  induction pre with
  | nil => intro rest _; simp [findCrlf]
  | cons a pre' ih =>
    intro rest h
    have ha : a ≠ CR := h a (List.mem_cons_self a pre')
    have hpre' : ∀ b ∈ pre', b ≠ CR := fun b hb => h b (List.mem_cons_of_mem a hb)
    obtain ⟨c, t', ht⟩ : ∃ c t', pre' ++ CR :: LF :: rest = c :: t' := by
      cases pre' with
      | nil => exact ⟨CR, LF :: rest, rfl⟩
      | cons x xs => exact ⟨x, xs ++ CR :: LF :: rest, rfl⟩
    rw [List.cons_append, ht]
    simp only [findCrlf]
    rw [if_neg (by rintro ⟨rfl, _⟩; exact ha rfl), ← ht, ih rest hpre']
    simp

/-- A found CRLF (plus its two octets) fits inside the buffer: the consumed
prefix length `p + 2` is bounded by the buffer length. -/
theorem findCrlf_some_bound : ∀ (buf : Bytes) (p : Nat),
    findCrlf buf = some p → p + 2 ≤ buf.length := by
  intro buf
  induction buf using findCrlf.induct with
  | case1 a b rest hcond =>
    intro p hp
    simp only [findCrlf, if_pos hcond, Option.some.injEq] at hp
    subst hp
    simp only [List.length_cons]; omega
  | case2 a b rest hcond ih =>
    intro p hp
    simp only [findCrlf, if_neg hcond] at hp
    cases hfc : findCrlf (b :: rest) with
    | none => rw [hfc] at hp; simp at hp
    | some q =>
      rw [hfc] at hp; simp at hp
      have hq := ih q hfc
      simp only [List.length_cons] at hq ⊢; omega
  | case3 t hlt =>
    intro p hp
    cases t with
    | nil => simp [findCrlf] at hp
    | cons x xs =>
      cases xs with
      | nil => simp [findCrlf] at hp
      | cons y ys => exact absurd rfl (hlt x y ys)

/-! ## Chunk-header parse -/

/-- Outcome of parsing one chunk header. -/
inductive Hdr where
  /-- No CRLF yet — need more bytes. -/
  | incomplete
  /-- Malformed size token, or a size beyond `maxChunkSize`. -/
  | error
  /-- Parsed a chunk of `size` bytes; the header consumed `headerLen` octets
  (the size digits and their CRLF). -/
  | ok (size : Nat) (headerLen : Nat)
deriving Repr, DecidableEq

/-- Parse one chunk header from the front of the buffer. Total. -/
def parseHeader (buf : Bytes) : Hdr :=
  match findCrlf buf with
  | none => .incomplete
  | some p =>
    match parseHex (buf.take p) with
    | none => .error
    | some size => if maxChunkSize < size then .error else .ok size (p + 2)

/-- **Theorem 3 (totality).** `parseHeader` is defined on every input: it is
`incomplete`, `error`, or a genuine `ok`. -/
theorem parseHeader_total (buf : Bytes) :
    parseHeader buf = .incomplete ∨ parseHeader buf = .error ∨
      ∃ s c, parseHeader buf = .ok s c := by
  unfold parseHeader
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨_, _, rfl⟩)

/-- **Theorem 3 (consumed-monotonicity).** When the header parses, it consumes a
positive number of octets, bounded by the buffer length. This is what makes the
streaming decode strictly shrink the buffer. -/
theorem parseHeader_consumed (buf : Bytes) (s c : Nat) (h : parseHeader buf = .ok s c) :
    0 < c ∧ c ≤ buf.length := by
  unfold parseHeader at h
  split at h
  · simp at h
  · next p hfc =>
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i size hpx
        have hb := findCrlf_some_bound buf p hfc
        simp only [Hdr.ok.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ⟨by omega, by omega⟩

/-- The header parse of a size line `pre` (no CR) followed by CRLF and `rest`,
factored through `parseHex pre`. -/
theorem parseHeader_line (pre rest : Bytes) (hpre : ∀ b ∈ pre, b ≠ CR) :
    parseHeader (pre ++ CR :: LF :: rest)
      = match parseHex pre with
        | none => .error
        | some size => if maxChunkSize < size then .error else .ok size (pre.length + 2) := by
  have hcr := findCrlf_append_no_cr pre rest hpre
  have htake : (pre ++ CR :: LF :: rest).take pre.length = pre := List.take_left _ _
  simp only [parseHeader, hcr, htake]

/-- **Theorem 5 (overflow → error).** A size octet-run denoting a value beyond
`maxChunkSize` is a total error. -/
theorem parseHeader_overflow (n : Nat) (rest : Bytes) (h : maxChunkSize < n) :
    parseHeader (toHex n ++ CR :: LF :: rest) = .error := by
  rw [parseHeader_line (toHex n) rest (toHex_no_cr n)]
  simp only [parseHex_toHex]
  rw [if_pos h]

/-- **Theorem 5 (malformed → error).** A size token that is empty or contains a
non-hex octet (`parseHex pre = none`) is a total error. -/
theorem parseHeader_bad_hex (pre rest : Bytes) (hpre : ∀ b ∈ pre, b ≠ CR)
    (hbad : parseHex pre = none) :
    parseHeader (pre ++ CR :: LF :: rest) = .error := by
  rw [parseHeader_line pre rest hpre]; simp only [hbad]

/-- A bare `CRLF` (empty size line) is a malformed header. -/
theorem parseHeader_empty_line (rest : Bytes) :
    parseHeader (CR :: LF :: rest) = .error :=
  parseHeader_bad_hex [] rest (by simp) rfl

/-! ## Single-frame decode -/

/-- Result of decoding one chunk frame. -/
inductive Frame where
  /-- Not enough bytes to complete a frame yet. -/
  | incomplete
  /-- Malformed framing. -/
  | error
  /-- A data chunk of payload `data`, consuming `consumed` octets. -/
  | chunk (data : Bytes) (consumed : Nat)
  /-- The terminal zero-size chunk, consuming `consumed` octets. -/
  | terminal (consumed : Nat)
deriving Repr, DecidableEq

/-- Decode one chunk frame from the front of the buffer. Total. Mirrors the
reference `decode_chunked_frame`, with the trailing CRLF after chunk data
checked (RFC-required) rather than blindly consumed. -/
def decodeFrame (buf : Bytes) : Frame :=
  match parseHeader buf with
  | .incomplete => .incomplete
  | .error => .error
  | .ok size headerLen =>
    if size = 0 then
      if (buf.drop headerLen).take 2 = [CR, LF] then .terminal (headerLen + 2)
      else .incomplete
    else
      if buf.length < headerLen + size + 2 then .incomplete
      else if (buf.drop (headerLen + size)).take 2 = [CR, LF] then
        .chunk ((buf.drop headerLen).take size) (headerLen + size + 2)
      else .error

/-- **A decoded data chunk consumes a positive, in-bounds number of octets.**
This is the consumed-monotonicity that makes `decodeStream` terminate. -/
theorem decodeFrame_chunk_bound (buf data : Bytes) (c : Nat)
    (h : decodeFrame buf = .chunk data c) : 0 < c ∧ c ≤ buf.length := by
  unfold decodeFrame at h
  split at h
  · simp at h
  · simp at h
  · next size headerLen hph =>
    split at h
    · split at h <;> simp at h
    · split at h
      · simp at h
      · next hge =>
        split at h
        · simp only [Frame.chunk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact ⟨by omega, by omega⟩
        · simp at h

/-- The empty buffer needs more data. -/
theorem decodeFrame_nil : decodeFrame [] = .incomplete := rfl

/-! ## Encoding (the wire form we decode against) -/

/-- Encode one data chunk: `chunk-size CRLF chunk-data CRLF`. -/
def encodeChunk (d : Bytes) : Bytes := toHex d.length ++ [CR, LF] ++ d ++ [CR, LF]

/-- The terminal zero-size chunk: `0 CRLF CRLF`. -/
def encodeTerminal : Bytes := toHex 0 ++ [CR, LF] ++ [CR, LF]

/-- Encode a whole chunked body: the chunks in order, then the terminal. -/
def encodeStream : List Bytes → Bytes
  | [] => encodeTerminal
  | d :: ds => encodeChunk d ++ encodeStream ds

/-- Encode the chunks with **no** terminal (a truncated / still-open stream). -/
def encodeChunks : List Bytes → Bytes
  | [] => []
  | d :: ds => encodeChunk d ++ encodeChunks ds

/-- Length of one encoded chunk: size digits + CRLF + data + CRLF. -/
theorem encodeChunk_length (d : Bytes) :
    (encodeChunk d).length = (toHex d.length).length + 2 + d.length + 2 := by
  simp only [encodeChunk, List.length_append, List.length_cons, List.length_nil]

/-- Decoding one encoded data chunk (followed by any tail) recovers the payload
exactly, consuming exactly the encoded-chunk octets — no framing leaks. -/
theorem decodeFrame_encodeChunk (d tail : Bytes) (hne : d ≠ [])
    (hle : d.length ≤ maxChunkSize) :
    decodeFrame (encodeChunk d ++ tail) = .chunk d (encodeChunk d).length := by
  -- Two prefix groupings of the buffer.
  have gA : encodeChunk d ++ tail
      = (toHex d.length ++ [CR, LF]) ++ (d ++ CR :: LF :: tail) := by
    simp [encodeChunk, List.append_assoc]
  have gB : encodeChunk d ++ tail
      = (toHex d.length ++ [CR, LF] ++ d) ++ (CR :: LF :: tail) := by
    simp [encodeChunk, List.append_assoc]
  have gShape : encodeChunk d ++ tail
      = toHex d.length ++ CR :: LF :: (d ++ CR :: LF :: tail) := by
    simp [encodeChunk, List.append_assoc]
  have lenA : (toHex d.length ++ [CR, LF]).length = (toHex d.length).length + 2 := by
    simp [List.length_append]
  have lenB : (toHex d.length ++ [CR, LF] ++ d).length
      = (toHex d.length).length + 2 + d.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  -- Header parse.
  have hph : parseHeader (encodeChunk d ++ tail)
      = .ok d.length ((toHex d.length).length + 2) := by
    rw [gShape, parseHeader_line _ _ (toHex_no_cr d.length)]
    simp only [parseHex_toHex]
    rw [if_neg (Nat.not_lt.mpr hle)]
  -- Data and trailing-CRLF extractions.
  have hTakeHead :
      ((encodeChunk d ++ tail).drop ((toHex d.length).length + 2)).take d.length = d := by
    rw [gA, List.drop_left' lenA]; exact List.take_left' rfl
  have hTakeData :
      ((encodeChunk d ++ tail).drop ((toHex d.length).length + 2 + d.length)).take 2 = [CR, LF] := by
    rw [gB, List.drop_left' lenB]; rfl
  -- Non-zero size, and the whole frame is present.
  have hne0 : ¬ d.length = 0 := by
    have := List.length_pos.mpr hne; omega
  have hnotlt : ¬ (encodeChunk d ++ tail).length
      < (toHex d.length).length + 2 + d.length + 2 := by
    simp only [List.length_append, encodeChunk, List.length_cons, List.length_nil]; omega
  -- Assemble.
  rw [encodeChunk_length]
  simp only [decodeFrame, hph]
  rw [if_neg hne0, if_neg hnotlt, if_pos hTakeData, hTakeHead]

/-- Decoding the terminal chunk yields `terminal`, consuming exactly its octets. -/
theorem decodeFrame_encodeTerminal :
    decodeFrame encodeTerminal = .terminal encodeTerminal.length := by
  have gShape : encodeTerminal = toHex 0 ++ CR :: LF :: [CR, LF] := by
    simp [encodeTerminal, List.append_assoc]
  have hph : parseHeader encodeTerminal = .ok 0 ((toHex 0).length + 2) := by
    rw [gShape, parseHeader_line _ _ (toHex_no_cr 0)]
    simp only [parseHex_toHex]
    rw [if_neg (by omega)]
  have hlen1 : (toHex 0).length = 1 := rfl
  have hdrop : (encodeTerminal.drop ((toHex 0).length + 2)).take 2 = [CR, LF] := by
    rw [hlen1]; rfl
  have hTermLen : (toHex 0).length + 2 + 2 = encodeTerminal.length := by
    simp only [encodeTerminal, List.length_append, List.length_cons, List.length_nil]
  simp only [decodeFrame, hph]
  rw [if_pos True.intro, if_pos hdrop, hTermLen]

/-! ## Streaming decode -/

/-- Result of a streaming decode. -/
inductive Decoded where
  /-- Buffer exhausted before the terminal chunk. -/
  | incomplete
  /-- Malformed framing somewhere in the stream. -/
  | error
  /-- The whole body decoded: `body` is the in-order concatenation of the chunk
  payloads, consuming `consumed` octets. -/
  | complete (body : Bytes) (consumed : Nat)
deriving Repr, DecidableEq

set_option linter.unusedVariables false in
/-- Fold `decodeFrame` across the buffer, accumulating the delivered body and
consumed octets, until the terminal chunk. Terminates because each data chunk
strictly shrinks the buffer (`decodeFrame_chunk_bound`). The `h :` binding names
the frame equation for the termination proof. -/
def decodeStream (buf : Bytes) : Decoded :=
  match h : decodeFrame buf with
  | .incomplete => .incomplete
  | .error => .error
  | .terminal c => .complete [] c
  | .chunk data c =>
    match decodeStream (buf.drop c) with
    | .complete body c' => .complete (data ++ body) (c + c')
    | .incomplete => .incomplete
    | .error => .error
  termination_by buf.length
  decreasing_by
    have hb := decodeFrame_chunk_bound buf data c h
    simp only [List.length_drop]; omega

/-- One-step unfolding of `decodeStream` at a data chunk. -/
theorem decodeStream_chunk (buf data : Bytes) (c : Nat) (h : decodeFrame buf = .chunk data c) :
    decodeStream buf =
      match decodeStream (buf.drop c) with
      | .complete body c' => .complete (data ++ body) (c + c')
      | .incomplete => .incomplete
      | .error => .error := by
  rw [decodeStream, h]

/-- One-step unfolding of `decodeStream` at the terminal chunk. -/
theorem decodeStream_terminal (buf : Bytes) (c : Nat) (h : decodeFrame buf = .terminal c) :
    decodeStream buf = .complete [] c := by
  rw [decodeStream, h]

/-- One-step unfolding of `decodeStream` at an incomplete frame. -/
theorem decodeStream_incomplete (buf : Bytes) (h : decodeFrame buf = .incomplete) :
    decodeStream buf = .incomplete := by
  rw [decodeStream, h]

/-- **Theorem 2 (bytes conserved).** Decoding the encoding of a chunk list
recovers exactly the in-order concatenation of the chunk payloads
(`chunks.flatten`) and consumes exactly the whole encoded stream. The delivered
byte count is therefore the sum of the chunk sizes, and nothing from the framing
octets (size digits, CRLFs, the terminal chunk) leaks into the body. -/
theorem decodeStream_encodeStream (chunks : List Bytes)
    (hne : ∀ d ∈ chunks, d ≠ []) (hle : ∀ d ∈ chunks, d.length ≤ maxChunkSize) :
    decodeStream (encodeStream chunks)
      = .complete chunks.flatten (encodeStream chunks).length := by
  induction chunks with
  | nil =>
    show decodeStream encodeTerminal = Decoded.complete [] encodeTerminal.length
    exact decodeStream_terminal encodeTerminal encodeTerminal.length decodeFrame_encodeTerminal
  | cons d ds ih =>
    have hne_d : d ≠ [] := hne d (by simp)
    have hle_d : d.length ≤ maxChunkSize := hle d (by simp)
    have hne_ds : ∀ x ∈ ds, x ≠ [] := fun x hx => hne x (by simp [hx])
    have hle_ds : ∀ x ∈ ds, x.length ≤ maxChunkSize := fun x hx => hle x (by simp [hx])
    have hdf : decodeFrame (encodeChunk d ++ encodeStream ds) = .chunk d (encodeChunk d).length :=
      decodeFrame_encodeChunk d (encodeStream ds) hne_d hle_d
    rw [show encodeStream (d :: ds) = encodeChunk d ++ encodeStream ds from rfl,
        decodeStream_chunk _ d (encodeChunk d).length hdf,
        show (encodeChunk d ++ encodeStream ds).drop (encodeChunk d).length = encodeStream ds
          from List.drop_left _ _,
        ih hne_ds hle_ds]
    simp only [List.flatten_cons, List.length_append]

/-- **Theorem 4 (incomplete stays non-terminal).** A stream that carries all its
data chunks but is missing the terminal zero-size chunk never decodes to
`complete`: after the last data chunk the buffer is empty, so the decode reports
`incomplete`. The reader never falsely reports completion. -/
theorem decodeStream_encodeChunks_incomplete (chunks : List Bytes)
    (hne : ∀ d ∈ chunks, d ≠ []) (hle : ∀ d ∈ chunks, d.length ≤ maxChunkSize) :
    decodeStream (encodeChunks chunks) = .incomplete := by
  induction chunks with
  | nil =>
    show decodeStream [] = Decoded.incomplete
    exact decodeStream_incomplete [] decodeFrame_nil
  | cons d ds ih =>
    have hne_d : d ≠ [] := hne d (by simp)
    have hle_d : d.length ≤ maxChunkSize := hle d (by simp)
    have hne_ds : ∀ x ∈ ds, x ≠ [] := fun x hx => hne x (by simp [hx])
    have hle_ds : ∀ x ∈ ds, x.length ≤ maxChunkSize := fun x hx => hle x (by simp [hx])
    have hdf : decodeFrame (encodeChunk d ++ encodeChunks ds) = .chunk d (encodeChunk d).length :=
      decodeFrame_encodeChunk d (encodeChunks ds) hne_d hle_d
    rw [show encodeChunks (d :: ds) = encodeChunk d ++ encodeChunks ds from rfl,
        decodeStream_chunk _ d (encodeChunk d).length hdf,
        show (encodeChunk d ++ encodeChunks ds).drop (encodeChunk d).length = encodeChunks ds
          from List.drop_left _ _]
    simp only [ih hne_ds hle_ds]

end Chunked
end Body
