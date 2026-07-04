/-
# Deflate — a total, bounded model of DEFLATE inflate (RFC 1951)

DEFLATE (RFC 1951) is the lossless compressed data format underneath gzip
(RFC 1952), zlib (RFC 1950), HTTP `Content-Encoding: deflate/gzip`, PNG, and the
HTTP/2 and TLS certificate-compression paths. A server DECOMPRESSES on the
request side: it receives a compressed request body (or a compressed header
block) and must expand it. That is the dangerous direction — a tiny compressed
input can name an enormous output (a *decompression bomb*). So this file models
INFLATE (decompression), as a real algorithm, and makes the bomb bound a
theorem.

What is modeled, from the RFC directly (not from any implementation):

  * **The bit stream** (§3.1.1): DEFLATE data is a stream of *bits* packed
    LSB-first within each byte; Huffman code bits are packed MSB-first of the
    code. `bytesToBits` flattens bytes to a `List Bool` in exactly that order;
    `takeBitsLE` reads an `n`-bit integer LSB-first (used for lengths, extra
    bits, and the block header); the Huffman decoder assembles code bits
    MSB-first.
  * **The three block types** (§3.2.3): stored (`00`), fixed-Huffman (`01`),
    and dynamic-Huffman (`10`); `11` is a reserved error.
  * **Stored blocks** (§3.2.4): skip to the next byte boundary, read `LEN` and
    its one's-complement check `NLEN`, then copy `LEN` literal bytes.
  * **Canonical Huffman** (§3.2.2): `buildHuffman` turns a per-symbol code-length
    list into the canonical code assignment; `decode` reads bits MSB-first until
    a codeword matches.
  * **Fixed Huffman** (§3.2.6): the fixed literal/length and distance code
    lengths, fed through the same `buildHuffman`.
  * **Dynamic Huffman** (§3.2.7): read `HLIT`/`HDIST`/`HCLEN`, the code-length
    alphabet (the `16,17,18,0,8,…` permutation), decode the run-length-encoded
    code lengths (repeat codes 16/17/18), and build the two trees.
  * **LZ77 back-references** (§3.2.5): the length codes 257–285 and distance
    codes 0–29 with their extra-bit tables; a match copies from earlier output,
    with overlap (the length can exceed the distance).

The one hard invariant, threaded everywhere: **the output never grows past a
caller-set limit `maxOut`.** Every byte that reaches the output passes one of two
guards (`copyMatch`, the literal push in `bodyStep`, `pushBounded` for stored
data), each of which refuses to append once the output has reached `maxOut`. The
result is `inflate_output_bounded`: for *every* input, `output.size ≤ maxOut`.
That is the decompression-bomb bound — a 10-byte input cannot force a gigabyte of
output. `inflate` is a `def` (structural on an explicit fuel), not a `partial
def`: it terminates on all input, which is `inflate_total`.

The model deliberately stays sequential and pure (`List Bool` in, `Array UInt8`
out); it does not model zlib/gzip framing (see `Gzip.lean`), a preset
dictionary, or streaming/window-limited operation — inflate here holds the whole
output in the bounded array. Correctness of the Huffman *decode against a
malformed tree* is handled by totality: a stream that names a nonexistent
codeword or runs out of bits fails with a typed error, never diverges.
-/

namespace Deflate

/-! ## Bytes and bits -/

/-- A bit stream: DEFLATE reads bits LSB-first within a byte (§3.1.1). -/
abbrev Bits := List Bool

/-- The 8 bits of a byte, least-significant first — the order DEFLATE consumes
them from the stream (§3.1.1). -/
def byteBits (b : UInt8) : Bits :=
  (List.range 8).map (fun i => (b.toNat >>> i) &&& 1 == 1)

/-- Flatten a byte list into the DEFLATE bit stream: each byte contributes its
8 bits LSB-first, in byte order. The total length is always a multiple of 8. -/
def bytesToBits : List UInt8 → Bits
  | [] => []
  | b :: bs => byteBits b ++ bytesToBits bs

/-- Read an `n`-bit unsigned integer, LSB-first (§3.1.1: values that are not
Huffman codes — lengths, block-type, extra bits — are stored LSB-first). Returns
the value and the remaining bits, or `none` if the stream is short. -/
def takeBitsLE : Nat → Bits → Option (Nat × Bits)
  | 0, bits => some (0, bits)
  | _ + 1, [] => none
  | n + 1, b :: bs =>
    match takeBitsLE n bs with
    | none => none
    | some (v, rest) => some ((if b then 1 else 0) + 2 * v, rest)

/-- Read `n` whole bytes from a byte-aligned position (each byte LSB-first). -/
def takeBytes : Nat → Bits → Option (List UInt8 × Bits)
  | 0, bits => some ([], bits)
  | n + 1, bits =>
    match takeBitsLE 8 bits with
    | none => none
    | some (v, rest) =>
      match takeBytes n rest with
      | none => none
      | some (bs, rest2) => some (UInt8.ofNat v :: bs, rest2)

/-- Advance to the next byte boundary (§3.2.4, used before a stored block's
`LEN`). The bit stream started byte-aligned (whole bytes), so its total length is
a multiple of 8; the number of bits left in the current partial byte is therefore
exactly `bits.length % 8`. -/
def align (bits : Bits) : Bits := bits.drop (bits.length % 8)

/-! ## Canonical Huffman (RFC 1951 §3.2.2) -/

/-- A decoded Huffman table: a list of `(symbol, codeLength, codeValue)`. The
canonical construction guarantees the code set is prefix-free. -/
abbrev HTree := List (Nat × Nat × Nat)

/-- `bl_count[len]` (§3.2.2 step 1): how many symbols use a code of length `len`. -/
def blCount (lengths : List Nat) (len : Nat) : Nat := (lengths.filter (· == len)).length

/-- The numeric value of the first codeword of length `len` (§3.2.2 step 2):
`first[len] = (first[len-1] + bl_count[len-1]) << 1`, with `bl_count[0]` forced to
0 (unused symbols carry no code). Pure structural recursion so the kernel can
evaluate it (used by the round-trip theorem). -/
def firstCode (lengths : List Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => (firstCode lengths len + (if len == 0 then 0 else blCount lengths len)) * 2

/-- The code value of symbol `i` of length `L` (§3.2.2 step 3): codes of a given
length are handed out in increasing symbol order starting at `first[L]`, so
symbol `i`'s code is `first[L]` plus the number of earlier symbols of length `L`. -/
def symCode (lengths : List Nat) (i L : Nat) : Nat :=
  firstCode lengths L + ((lengths.take i).filter (· == L)).length

/-- Build the canonical Huffman table from a per-symbol code-length list
(§3.2.2). Symbol `i` has code length `lengths[i]` (0 = unused, dropped). Pure
(no mutable state) so `decide` can reduce it in proofs. -/
def buildHuffman (lengths : List Nat) : HTree :=
  lengths.zipIdx.filterMap (fun (L, i) => if L == 0 then none else some (i, L, symCode lengths i L))

/-- Decode one symbol: assemble code bits MSB-first (§3.1.1) until a codeword in
`t` matches. Total: structural on the remaining bits, `none` when the stream is
exhausted with no match. -/
def decodeStep (t : HTree) : Nat → Nat → Bits → Option (Nat × Bits)
  | acc, len, bits =>
    match t.find? (fun e => e.2.1 == len && e.2.2 == acc) with
    | some e => some (e.1, bits)
    | none =>
      match bits with
      | [] => none
      | b :: bs => decodeStep t (acc * 2 + (if b then 1 else 0)) (len + 1) bs

/-- Decode one Huffman symbol from the front of the bit stream. -/
def decode (t : HTree) (bits : Bits) : Option (Nat × Bits) := decodeStep t 0 0 bits

/-! ## Length and distance codes (RFC 1951 §3.2.5) -/

/-- Length codes 257–285: `(base, extraBits)`, indexed by `symbol − 257`. -/
def lengthTable : List (Nat × Nat) :=
  [ (3,0),(4,0),(5,0),(6,0),(7,0),(8,0),(9,0),(10,0),
    (11,1),(13,1),(15,1),(17,1),
    (19,2),(23,2),(27,2),(31,2),
    (35,3),(43,3),(51,3),(59,3),
    (67,4),(83,4),(99,4),(115,4),
    (131,5),(163,5),(195,5),(227,5),
    (258,0) ]

/-- Distance codes 0–29: `(base, extraBits)`, indexed by symbol. -/
def distTable : List (Nat × Nat) :=
  [ (1,0),(2,0),(3,0),(4,0),
    (5,1),(7,1),
    (9,2),(13,2),
    (17,3),(25,3),
    (33,4),(49,4),
    (65,5),(97,5),
    (129,6),(193,6),
    (257,7),(385,7),
    (513,8),(769,8),
    (1025,9),(1537,9),
    (2049,10),(3073,10),
    (4097,11),(6145,11),
    (8193,12),(12289,12),
    (16385,13),(24577,13) ]

/-- Resolve a length symbol (257–285) to a match length: base plus the extra
bits (§3.2.5). -/
def lenExtra (sym : Nat) (bits : Bits) : Option (Nat × Bits) :=
  match lengthTable.get? (sym - 257) with
  | none => none
  | some (base, ex) =>
    match takeBitsLE ex bits with
    | none => none
    | some (e, rest) => some (base + e, rest)

/-- Resolve a distance symbol (0–29) to a match distance: base plus extra bits. -/
def distExtra (dsym : Nat) (bits : Bits) : Option (Nat × Bits) :=
  match distTable.get? dsym with
  | none => none
  | some (base, ex) =>
    match takeBitsLE ex bits with
    | none => none
    | some (e, rest) => some (base + e, rest)

/-! ## Fixed Huffman trees (RFC 1951 §3.2.6) -/

/-- Fixed literal/length code lengths: 0–143 → 8, 144–255 → 9, 256–279 → 7,
280–287 → 8 (§3.2.6). -/
def fixedLitLengths : List Nat :=
  List.replicate 144 8 ++ List.replicate 112 9 ++ List.replicate 24 7 ++ List.replicate 8 8

/-- Fixed distance code lengths: every distance symbol is 5 bits (§3.2.6). -/
def fixedDistLengths : List Nat := List.replicate 30 5

/-- The fixed literal/length Huffman tree. -/
def fixedLitTree : HTree := buildHuffman fixedLitLengths

/-- The fixed distance Huffman tree. -/
def fixedDistTree : HTree := buildHuffman fixedDistLengths

/-! ## Configuration, errors, result -/

/-- Inflate configuration: the single knob that matters is the output ceiling. -/
structure Cfg where
  /-- Hard cap on decompressed output size (bytes). The decompression-bomb bound. -/
  maxOut : Nat

/-- Typed inflate failures — every one is a *total* outcome, never a loop. -/
inductive Err where
  | truncated      -- stream ended mid-symbol / mid-field
  | badBlockType   -- reserved block type `11`
  | badLength      -- length symbol out of table
  | badDistance    -- distance symbol out of table, or distance past output start
  | badStored      -- stored block `NLEN` ≠ ~`LEN`
  | badHuffman     -- malformed dynamic-Huffman description
  | overLimit      -- output would exceed `maxOut` (bomb refused)
  deriving DecidableEq, Repr

/-- Inflate result: the (bounded) output and an optional failure. -/
structure Result where
  out : Array UInt8
  err : Option Err

/-! ## LZ77 match copy (RFC 1951 §3.2.5), bounded -/

/-- Copy an LZ77 back-reference: `n` bytes starting `dist` behind the current
output end, one byte at a time so overlap (`dist < n`) is handled. Guards:
refuses once the output has reached `maxOut` (bomb bound), and rejects a distance
of 0 or one that reaches before the start of output. -/
def copyMatch (maxOut dist : Nat) : Nat → Array UInt8 → Option (Array UInt8)
  | 0, out => some out
  | n + 1, out =>
    if out.size ≥ maxOut then none
    else if dist == 0 || dist > out.size then none
    else copyMatch maxOut dist n (out.push (out.get! (out.size - dist)))

/-- Append literal bytes, refusing once the output has reached `maxOut`. -/
def pushBounded (maxOut : Nat) (out : Array UInt8) : List UInt8 → Option (Array UInt8)
  | [] => some out
  | b :: bs =>
    if out.size ≥ maxOut then none
    else pushBounded maxOut (out.push b) bs

/-! ## Dynamic-Huffman description (RFC 1951 §3.2.7) -/

/-- The code-length-alphabet permutation the code lengths are read in (§3.2.7). -/
def clOrder : List Nat := [16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15]

/-- Read `k` three-bit code lengths and scatter them into a 19-entry array by
`clOrder` (§3.2.7). -/
def readCLLens : Nat → Nat → Array Nat → Bits → Option (Array Nat × Bits)
  | 0, _, arr, bits => some (arr, bits)
  | k + 1, idx, arr, bits =>
    match takeBitsLE 3 bits with
    | none => none
    | some (v, rest) =>
      match clOrder.get? idx with
      | none => none
      | some sym => readCLLens k (idx + 1) (arr.set! sym v) rest

/-- Decode the run-length-encoded literal+distance code lengths (§3.2.7): symbols
0–15 are literal lengths; 16 repeats the previous length 3–6 times; 17 repeats a
zero 3–10 times; 18 repeats a zero 11–138 times. `acc` is built most-recent-first;
`fuel` bounds the loop (each step appends ≥1, so `total + 1` suffices). -/
def readCL (cl : HTree) : Nat → Nat → List Nat → Bits → Option (List Nat × Bits)
  | 0, _, _, _ => none
  | fuel + 1, total, acc, bits =>
    if acc.length ≥ total then some ((acc.reverse).take total, bits)
    else
      match decode cl bits with
      | none => none
      | some (sym, b1) =>
        if sym ≤ 15 then
          readCL cl fuel total (sym :: acc) b1
        else if sym == 16 then
          match acc with
          | [] => none                       -- 16 with no previous length
          | prev :: _ =>
            match takeBitsLE 2 b1 with
            | none => none
            | some (r, b2) => readCL cl fuel total (List.replicate (r + 3) prev ++ acc) b2
        else if sym == 17 then
          match takeBitsLE 3 b1 with
          | none => none
          | some (r, b2) => readCL cl fuel total (List.replicate (r + 3) 0 ++ acc) b2
        else if sym == 18 then
          match takeBitsLE 7 b1 with
          | none => none
          | some (r, b2) => readCL cl fuel total (List.replicate (r + 11) 0 ++ acc) b2
        else none

/-- Parse a dynamic-Huffman block header (§3.2.7): read `HLIT`/`HDIST`/`HCLEN`,
the code-length code lengths, then the run-length-encoded literal and distance
code lengths; build the two trees. Returns the trees and the remaining bits. -/
def buildDynamic (bits : Bits) : Option (HTree × HTree × Bits) :=
  match takeBitsLE 5 bits with
  | none => none
  | some (hlit, b1) =>
    match takeBitsLE 5 b1 with
    | none => none
    | some (hdist, b2) =>
      match takeBitsLE 4 b2 with
      | none => none
      | some (hclen, b3) =>
        let numLit := hlit + 257
        let numDist := hdist + 1
        let numCL := hclen + 4
        match readCLLens numCL 0 (Array.mkArray 19 0) b3 with
        | none => none
        | some (clArr, b4) =>
          let clTree := buildHuffman clArr.toList
          match readCL clTree (numLit + numDist + 1) (numLit + numDist) [] b4 with
          | none => none
          | some (allLens, b5) =>
            some (buildHuffman (allLens.take numLit), buildHuffman (allLens.drop numLit), b5)

/-! ## Stored blocks (RFC 1951 §3.2.4) -/

/-- Inflate a stored (uncompressed) block: byte-align, read `LEN`/`NLEN` and
check `NLEN = ~LEN`, then copy `LEN` literal bytes (bounded). Returns the updated
output, remaining bits, and an optional error. -/
def inflateStored (cfg : Cfg) (out : Array UInt8) (bits : Bits) :
    Array UInt8 × Bits × Option Err :=
  match takeBitsLE 16 (align bits) with
  | none => (out, [], some .truncated)
  | some (len, b1) =>
    match takeBitsLE 16 b1 with
    | none => (out, [], some .truncated)
    | some (nlen, b2) =>
      if len + nlen != 65535 then (out, [], some .badStored)
      else
        match takeBytes len b2 with
        | none => (out, [], some .truncated)
        | some (bytes, b3) =>
          match pushBounded cfg.maxOut out bytes with
          | none => (out, [], some .overLimit)
          | some o2 => (o2, b3, none)

/-! ## Per-symbol step and the block body loop -/

/-- The outcome of decoding one symbol in a compressed block. -/
inductive Sig where
  | more (out : Array UInt8) (bits : Bits)   -- literal / match consumed, continue
  | done (out : Array UInt8) (bits : Bits)   -- end-of-block symbol (256)
  | fail (out : Array UInt8) (err : Err)     -- typed failure

/-- The output carried by a step (used by the bound proof). -/
def Sig.outSize : Sig → Nat
  | .more o _ => o.size
  | .done o _ => o.size
  | .fail o _ => o.size

/-- Decode one symbol from a compressed block (§3.2.3): a literal (0–255) pushes
a byte; 256 ends the block; 257–285 is an LZ77 length, followed by a distance
symbol and a bounded copy. -/
def bodyStep (cfg : Cfg) (lit dist : HTree) (out : Array UInt8) (bits : Bits) : Sig :=
  match decode lit bits with
  | none => .fail out .truncated
  | some (sym, b1) =>
    if sym == 256 then .done out b1
    else if sym < 256 then
      if out.size < cfg.maxOut then .more (out.push (UInt8.ofNat sym)) b1
      else .fail out .overLimit
    else if sym ≤ 285 then
      match lenExtra sym b1 with
      | none => .fail out .badLength
      | some (len, b2) =>
        match decode dist b2 with
        | none => .fail out .truncated
        | some (dsym, b3) =>
          match distExtra dsym b3 with
          | none => .fail out .badDistance
          | some (d, b4) =>
            match copyMatch cfg.maxOut d len out with
            | none => .fail out .badDistance
            | some o2 => .more o2 b4
    else .fail out .badHuffman

/-- Decode a whole compressed block body until the end-of-block symbol. `fuel`
bounds the loop; each real step consumes ≥1 bit, so `bits.length + 1` suffices. -/
def decodeBody (cfg : Cfg) (lit dist : HTree) :
    Nat → Array UInt8 → Bits → Array UInt8 × Bits × Option Err
  | 0, out, bits => (out, bits, some .truncated)
  | fuel + 1, out, bits =>
    match bodyStep cfg lit dist out bits with
    | .more o b => decodeBody cfg lit dist fuel o b
    | .done o b => (o, b, none)
    | .fail o e => (o, [], some e)

/-! ## The block driver (RFC 1951 §3.5) -/

/-- Process blocks until a final block (`BFINAL = 1`) or an error. `fuel` bounds
the block count; each block consumes ≥3 header bits, so `bits.length + 1`
suffices. -/
def inflateAux (cfg : Cfg) : Nat → Array UInt8 → Bits → Array UInt8 × Option Err
  | 0, out, _ => (out, some .truncated)
  | fuel + 1, out, bits =>
    match takeBitsLE 1 bits with
    | none => (out, some .truncated)
    | some (bfinal, b1) =>
      match takeBitsLE 2 b1 with
      | none => (out, some .truncated)
      | some (btype, b2) =>
        if btype == 0 then
          match inflateStored cfg out b2 with
          | (o, _, some e) => (o, some e)
          | (o, b3, none) => if bfinal == 1 then (o, none) else inflateAux cfg fuel o b3
        else if btype == 1 then
          match decodeBody cfg fixedLitTree fixedDistTree (b2.length + 1) out b2 with
          | (o, _, some e) => (o, some e)
          | (o, b3, none) => if bfinal == 1 then (o, none) else inflateAux cfg fuel o b3
        else if btype == 2 then
          match buildDynamic b2 with
          | none => (out, some .badHuffman)
          | some (lit, dist, b3) =>
            match decodeBody cfg lit dist (b3.length + 1) out b3 with
            | (o, _, some e) => (o, some e)
            | (o, b4, none) => if bfinal == 1 then (o, none) else inflateAux cfg fuel o b4
        else (out, some .badBlockType)

/-- **Inflate**: decompress a DEFLATE stream under an output ceiling. Total, and
`inflate_output_bounded` proves the output never exceeds `cfg.maxOut`. -/
def inflate (cfg : Cfg) (input : List UInt8) : Result :=
  let bits := bytesToBits input
  let (o, e) := inflateAux cfg (bits.length + 1) #[] bits
  ⟨o, e⟩

/-! ## The output-size bound (the decompression-bomb theorem) -/

/-- A bounded match copy never overshoots the ceiling. -/
theorem copyMatch_le (maxOut dist : Nat) :
    ∀ n out o2, copyMatch maxOut dist n out = some o2 → out.size ≤ maxOut → o2.size ≤ maxOut := by
  intro n
  induction n with
  | zero =>
    intro out o2 h hle
    simp only [copyMatch] at h
    cases h; exact hle
  | succ k ih =>
    intro out o2 h hle
    simp only [copyMatch] at h
    by_cases hge : out.size ≥ maxOut
    · rw [if_pos hge] at h; exact absurd h (by simp)
    · rw [if_neg hge] at h
      by_cases hd : dist == 0 || dist > out.size
      · rw [if_pos hd] at h; exact absurd h (by simp)
      · rw [if_neg hd] at h
        have hpush : (out.push (out.get! (out.size - dist))).size ≤ maxOut := by
          rw [Array.size_push]; omega
        exact ih _ o2 h hpush

/-- Appending literals never overshoots the ceiling. -/
theorem pushBounded_le (maxOut : Nat) :
    ∀ bs out o2, pushBounded maxOut out bs = some o2 → out.size ≤ maxOut → o2.size ≤ maxOut := by
  intro bs
  induction bs with
  | nil =>
    intro out o2 h hle
    simp only [pushBounded] at h
    cases h; exact hle
  | cons b bs ih =>
    intro out o2 h hle
    simp only [pushBounded] at h
    by_cases hge : out.size ≥ maxOut
    · rw [if_pos hge] at h; exact absurd h (by simp)
    · rw [if_neg hge] at h
      have hpush : (out.push b).size ≤ maxOut := by rw [Array.size_push]; omega
      exact ih _ o2 h hpush

/-- One decode step never overshoots the ceiling. -/
theorem bodyStep_le (cfg : Cfg) (lit dist : HTree) (out : Array UInt8) (bits : Bits)
    (hle : out.size ≤ cfg.maxOut) : (bodyStep cfg lit dist out bits).outSize ≤ cfg.maxOut := by
  unfold bodyStep
  split
  · exact hle
  · rename_i sym b1 _
    by_cases h256 : sym == 256
    · simp only [h256, if_pos]; exact hle
    · rw [if_neg (by simpa using h256)]
      by_cases hlit : sym < 256
      · rw [if_pos hlit]
        by_cases hcap : out.size < cfg.maxOut
        · rw [if_pos hcap]; simp only [Sig.outSize]; rw [Array.size_push]; omega
        · rw [if_neg hcap]; exact hle
      · rw [if_neg hlit]
        by_cases hlen : sym ≤ 285
        · rw [if_pos hlen]
          split
          · exact hle
          · split
            · exact hle
            · split
              · exact hle
              · split
                · exact hle
                · rename_i o2 hcopy
                  simp only [Sig.outSize]
                  exact copyMatch_le _ _ _ _ _ hcopy hle
        · rw [if_neg hlen]; exact hle

/-- The block body loop never overshoots the ceiling. -/
theorem decodeBody_le (cfg : Cfg) (lit dist : HTree) :
    ∀ fuel out bits, out.size ≤ cfg.maxOut →
      (decodeBody cfg lit dist fuel out bits).1.size ≤ cfg.maxOut := by
  intro fuel
  induction fuel with
  | zero => intro out bits h; simpa [decodeBody] using h
  | succ n ih =>
    intro out bits h
    simp only [decodeBody]
    have hs := bodyStep_le cfg lit dist out bits h
    split
    · rename_i o b heq
      rw [heq] at hs; simp only [Sig.outSize] at hs
      exact ih o b hs
    · rename_i o b heq
      rw [heq] at hs; simpa only [Sig.outSize] using hs
    · rename_i o e heq
      rw [heq] at hs; simpa only [Sig.outSize] using hs

/-- A stored block never overshoots the ceiling. -/
theorem inflateStored_le (cfg : Cfg) (out : Array UInt8) (bits : Bits)
    (hle : out.size ≤ cfg.maxOut) : (inflateStored cfg out bits).1.size ≤ cfg.maxOut := by
  unfold inflateStored
  repeat' split
  all_goals try exact hle
  rename_i o2 hpush
  exact pushBounded_le _ _ _ _ hpush hle

/-- The block driver never overshoots the ceiling. -/
theorem inflateAux_le (cfg : Cfg) :
    ∀ fuel out bits, out.size ≤ cfg.maxOut →
      (inflateAux cfg fuel out bits).1.size ≤ cfg.maxOut := by
  intro fuel
  induction fuel with
  | zero => intro out bits h; simpa [inflateAux] using h
  | succ n ih =>
    intro out bits h
    simp only [inflateAux]
    split
    · exact h
    · split
      · exact h
      · rename_i btype b2 _
        by_cases hb0 : btype == 0
        · rw [if_pos hb0]
          have hst := inflateStored_le cfg out b2 h
          split
          · rename_i o mid e heq; rw [heq] at hst; exact hst
          · rename_i o b3 heq; rw [heq] at hst
            split
            · exact hst
            · exact ih o b3 hst
        · rw [if_neg hb0]
          by_cases hb1 : btype == 1
          · rw [if_pos hb1]
            have hd := decodeBody_le cfg fixedLitTree fixedDistTree (b2.length + 1) out b2 h
            split
            · rename_i o mid e heq; rw [heq] at hd; exact hd
            · rename_i o b3 heq; rw [heq] at hd
              split
              · exact hd
              · exact ih o b3 hd
          · rw [if_neg hb1]
            by_cases hb2 : btype == 2
            · rw [if_pos hb2]
              split
              · exact h
              · rename_i lit dist b3 _
                have hd := decodeBody_le cfg lit dist (b3.length + 1) out b3 h
                split
                · rename_i o mid e heq; rw [heq] at hd; exact hd
                · rename_i o b4 heq; rw [heq] at hd
                  split
                  · exact hd
                  · exact ih o b4 hd
            · rw [if_neg hb2]; exact h

/-- **The decompression-bomb bound.** For every configuration and every input,
the inflated output is at most `cfg.maxOut` bytes. A small compressed input can
NAME an enormous expansion, but inflate refuses to materialize it past the
ceiling — the output array's size is provably bounded regardless of input. -/
theorem inflate_output_bounded (cfg : Cfg) (input : List UInt8) :
    (inflate cfg input).out.size ≤ cfg.maxOut := by
  unfold inflate
  simp only
  exact inflateAux_le cfg _ #[] _ (by simp)

/-- **Inflate is total.** It is a `def` (structural recursion on explicit fuel),
so it terminates and returns a `Result` for every input — a decompression bomb
halts within the fuel bound rather than diverging, and `inflate_output_bounded`
certifies the memory side of that same guarantee. -/
theorem inflate_total (cfg : Cfg) (input : List UInt8) :
    ∃ r : Result, inflate cfg input = r := ⟨_, rfl⟩

/-! ## Stored-block identity (RFC 1951 §3.2.4)

A single final stored block round-trips exactly: its literal payload comes back
byte-for-byte. `deflateStored` emits the block; `inflate` recovers the bytes.
-/

/-- The 16-bit little-endian encoding of `n` as two bytes. -/
def u16le (n : Nat) : List UInt8 := [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256)]

/-- Encode a byte list as one final stored block (§3.2.4): the header byte
`0x01` (`BFINAL=1`, `BTYPE=00`, 5 pad bits), then `LEN`, `NLEN = ~LEN`, then the
literal bytes. Valid for `x.length < 65536`. -/
def deflateStored (x : List UInt8) : List UInt8 :=
  0x01 :: u16le x.length ++ u16le (65535 - x.length) ++ x

/-! ### Bit-stream reader/writer round-trip lemmas

The identity theorem needs to know the reader inverts the writer: `takeBitsLE`
recovers exactly what `byteBits`/`bytesToBits` packed, and `takeBytes` recovers a
byte list. These are proved once, generically, then instantiated on the stored
block's concrete header.
-/

/-- `byteBits`, but for an arbitrary `Nat` and width — the generator `takeBitsLE`
inverts. `byteBits b` is `bitsN b.toNat 8` definitionally. -/
def bitsN (n k : Nat) : Bits := (List.range k).map (fun i => (n >>> i) &&& 1 == 1)

/-- Peel one bit off the front: bit `0` of `n`, then the bits of `n >>> 1`. -/
theorem bitsN_succ (n k : Nat) :
    bitsN n (k + 1) = ((n &&& 1 == 1) :: bitsN (n >>> 1) k) := by
  unfold bitsN
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.shiftRight_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  congr 2
  rw [show i.succ = 1 + i from by omega, Nat.shiftRight_add]

/-- **The reader inverts the writer.** `takeBitsLE k` on the `k` LSB-first bits of
`n` (followed by any tail) returns `n % 2^k` and the untouched tail. -/
theorem takeBitsLE_bitsN (k : Nat) : ∀ (n : Nat) (rest : Bits),
    takeBitsLE k (bitsN n k ++ rest) = some (n % 2 ^ k, rest) := by
  induction k with
  | zero => intro n rest; simp [takeBitsLE, bitsN, Nat.mod_one]
  | succ m ih =>
    intro n rest
    rw [bitsN_succ]
    simp only [List.cons_append, takeBitsLE]
    rw [ih (n >>> 1) rest]
    have h1 : (if (n &&& 1 == 1) = true then (1 : Nat) else 0) = n % 2 := by
      rw [Nat.and_one_is_mod]; rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
    rw [h1, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have : n % 2 ^ (m + 1) = n % 2 + 2 * (n / 2 % 2 ^ m) := by
      rw [Nat.pow_succ, Nat.mul_comm]; exact Nat.mod_mul
    rw [this]

/-- Reading 8 bits recovers a byte exactly (`byteBits b = bitsN b.toNat 8`). -/
theorem byteBits_take (b : UInt8) (rest : Bits) :
    takeBitsLE 8 (byteBits b ++ rest) = some (b.toNat, rest) := by
  have h : byteBits b = bitsN b.toNat 8 := rfl
  rw [h, takeBitsLE_bitsN]
  have hb : b.toNat < 256 := UInt8.toNat_lt_size b
  rw [show (2 : Nat) ^ 8 = 256 from rfl, Nat.mod_eq_of_lt hb]

/-- `bytesToBits` is a monoid homomorphism from byte-append to bit-append. -/
theorem bytesToBits_append (a c : List UInt8) :
    bytesToBits (a ++ c) = bytesToBits a ++ bytesToBits c := by
  induction a with
  | nil => simp [bytesToBits]
  | cons x xs ih => simp only [List.cons_append, bytesToBits, ih, List.append_assoc]

/-- Each byte contributes exactly 8 bits. -/
theorem bytesToBits_length (l : List UInt8) : (bytesToBits l).length = 8 * l.length := by
  induction l with
  | nil => simp [bytesToBits]
  | cons x xs ih =>
    simp only [bytesToBits, List.length_append, ih, byteBits, List.length_map,
      List.length_range, List.length_cons]
    omega

/-- `takeBytes` inverts `bytesToBits`: it recovers the original byte list. -/
theorem takeBytes_bytesToBits (l : List UInt8) (rest : Bits) :
    takeBytes l.length (bytesToBits l ++ rest) = some (l, rest) := by
  induction l with
  | nil => simp [takeBytes, bytesToBits]
  | cons x xs ih =>
    simp only [List.length_cons, bytesToBits, takeBytes, List.append_assoc,
      byteBits_take, ih, UInt8.ofNat_toNat]

/-- Below the ceiling, `pushBounded` appends the whole list; its output byte list
is `acc ++ xs`. -/
theorem pushBounded_all (maxOut : Nat) : ∀ (xs : List UInt8) (acc : Array UInt8),
    acc.size + xs.length ≤ maxOut →
      (pushBounded maxOut acc xs).map (·.toList) = some (acc.toList ++ xs) := by
  intro xs
  induction xs with
  | nil => intro acc h; simp [pushBounded]
  | cons b bs ih =>
    intro acc h
    simp only [pushBounded]
    have hlt : ¬ acc.size ≥ maxOut := by simp only [List.length_cons] at h; omega
    rw [if_neg hlt]
    rw [ih (acc.push b) (by rw [Array.size_push]; simp only [List.length_cons] at h; omega)]
    simp [Array.push_toList]

/-- Splitting a `takeBitsLE` read: reading `p + q` bits is reading `p` then `q`,
with the two values recombined `v + 2^p * w`. -/
theorem takeBitsLE_add (p q : Nat) : ∀ xs : Bits,
    takeBitsLE (p + q) xs =
      match takeBitsLE p xs with
      | none => none
      | some (v, r) =>
        match takeBitsLE q r with
        | none => none
        | some (w, r2) => some (v + 2 ^ p * w, r2) := by
  induction p with
  | zero =>
    intro xs
    simp only [Nat.zero_add, takeBitsLE, Nat.pow_zero, Nat.one_mul]
    cases takeBitsLE q xs with
    | none => rfl
    | some p => obtain ⟨w, r2⟩ := p; rfl
  | succ n ih =>
    intro xs
    cases xs with
    | nil => rw [show n + 1 + q = (n + q) + 1 from by omega]; simp only [takeBitsLE]
    | cons c cs =>
      rw [show n + 1 + q = (n + q) + 1 from by omega]
      simp only [takeBitsLE]
      rw [ih cs]
      cases h1 : takeBitsLE n cs with
      | none => simp
      | some vr =>
        obtain ⟨v, r⟩ := vr; simp only
        cases h2 : takeBitsLE q r with
        | none => simp
        | some wr2 =>
          obtain ⟨w, r2⟩ := wr2
          simp only [Option.some.injEq, Prod.mk.injEq, and_true]
          rw [Nat.pow_succ, Nat.mul_add, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]; omega

/-- Reading 16 bits over two bytes recovers the little-endian value. -/
theorem takeBitsLE_two_bytes (a b : UInt8) (rest : Bits) :
    takeBitsLE 16 (byteBits a ++ byteBits b ++ rest) = some (a.toNat + 256 * b.toNat, rest) := by
  rw [List.append_assoc, show (16 : Nat) = 8 + 8 from rfl, takeBitsLE_add,
      byteBits_take a (byteBits b ++ rest)]
  simp only
  rw [byteBits_take b rest]

/-- `takeBitsLE 16` recovers a `u16le`-encoded value (for `n < 65536`). -/
theorem u16le_read (n : Nat) (rest : Bits) (h : n < 65536) :
    takeBitsLE 16 (bytesToBits (u16le n) ++ rest) = some (n, rest) := by
  simp only [u16le, bytesToBits, List.append_nil]
  rw [takeBitsLE_two_bytes]
  have hv : (UInt8.ofNat (n % 256)).toNat + 256 * (UInt8.ofNat (n / 256 % 256)).toNat = n := by
    show n % 256 % 256 + 256 * (n / 256 % 256 % 256) = n
    omega
  rw [hv]

/-- The stored-block header byte `0x01` unpacks to `BFINAL=1`, `BTYPE=00`, 5 pad
bits, all LSB-first. -/
theorem byteBits_one :
    byteBits 0x01 = [true, false, false, false, false, false, false, false] := by
  decide

/-- `deflateStored` as an explicit cons (the header byte then the encoded tail). -/
theorem deflateStored_eq (x : List UInt8) :
    deflateStored x = 0x01 :: (u16le x.length ++ u16le (65535 - x.length) ++ x) := rfl

/-- `inflateStored` on a `deflateStored` payload recovers the literal bytes. This
threads the byte-alignment (`align` drops exactly the 5 pad bits), the two 16-bit
`LEN`/`NLEN` reads, the `NLEN = ~LEN` check, the literal copy, and the bounded
push — every one discharged from the round-trip lemmas above. -/
theorem inflateStored_deflate (cfg : Cfg) (x : List UInt8)
    (hlen : x.length < 65536) (hcap : x.length ≤ cfg.maxOut) :
    ∃ o : Array UInt8,
      inflateStored cfg #[]
        ([false, false, false, false, false] ++
          bytesToBits (u16le x.length ++ u16le (65535 - x.length) ++ x))
        = (o, [], none) ∧ o.toList = x := by
  have hnlen : (65535 - x.length) < 65536 := by omega
  have hlen8 : ([false, false, false, false, false] ++
      bytesToBits (u16le x.length ++ u16le (65535 - x.length) ++ x)).length % 8 = 5 := by
    simp only [List.length_append, bytesToBits_length, List.length_cons, List.length_nil]
    omega
  have halign : align ([false, false, false, false, false] ++
      bytesToBits (u16le x.length ++ u16le (65535 - x.length) ++ x))
      = bytesToBits (u16le x.length ++ u16le (65535 - x.length) ++ x) := by
    simp only [align, hlen8]
    rw [show (5 : Nat) = ([false, false, false, false, false] : List Bool).length from rfl]
    exact List.drop_left _ _
  unfold inflateStored
  rw [halign, bytesToBits_append, bytesToBits_append, List.append_assoc,
      u16le_read x.length _ hlen]
  simp only
  rw [u16le_read (65535 - x.length) _ hnlen]
  simp only
  have hsum : x.length + (65535 - x.length) = 65535 := by omega
  simp only [hsum, bne_self_eq_false, if_false]
  rw [← List.append_nil (bytesToBits x)]
  rw [takeBytes_bytesToBits x []]
  simp only
  have hpb := pushBounded_all cfg.maxOut x #[] (by simpa using hcap)
  cases hp : pushBounded cfg.maxOut #[] x with
  | none => rw [hp] at hpb; simp at hpb
  | some o2 =>
    rw [hp] at hpb
    simp only [Option.map_some, Option.some.injEq] at hpb
    exact ⟨o2, rfl, by simpa using hpb⟩

/-- One block-driver step over a single final stored block yields its bytes: the
1-bit `BFINAL`, 2-bit `BTYPE=00`, then `inflateStored`, then the `BFINAL=1` exit. -/
theorem inflateAux_one_stored (cfg : Cfg) (m : Nat) (o2 : Array UInt8) (T : List UInt8)
    (hst : inflateStored cfg #[] ([false, false, false, false, false] ++ bytesToBits T)
      = (o2, [], none)) :
    inflateAux cfg (m + 1) #[]
      ([true, false, false, false, false, false, false, false] ++ bytesToBits T) = (o2, none) := by
  have hst' : inflateStored cfg #[]
      (false :: false :: false :: false :: false :: bytesToBits T) = (o2, [], none) := hst
  simp only [inflateAux, List.cons_append, List.nil_append, takeBitsLE]
  simp only [hst', Nat.reduceMul, Nat.reduceAdd, Nat.reduceBEq, Nat.reduceEqDiff,
    reduceIte, Bool.false_eq_true, if_false, if_true]

/-- **Stored-block identity (the round-trip theorem).** For every byte list `x`
with `x.length < 65536` (a single stored block's `LEN` field is 16-bit) and every
ceiling `cfg.maxOut ≥ x.length`, inflating `deflateStored x` returns exactly `x`
with no error: `inflate (deflate x) = x` on the stored path. Concretely this
witnesses `inflate_stored_identity` for the RFC 1951 §3.2.4 uncompressed block —
the reader inverts the writer, byte for byte. -/
theorem inflate_stored_identity (cfg : Cfg) (x : List UInt8)
    (hlen : x.length < 65536) (hcap : x.length ≤ cfg.maxOut) :
    (inflate cfg (deflateStored x)).out.toList = x
      ∧ (inflate cfg (deflateStored x)).err = none := by
  obtain ⟨o2, hst, hox⟩ := inflateStored_deflate cfg x hlen hcap
  have hbits : bytesToBits (deflateStored x)
      = [true, false, false, false, false, false, false, false]
        ++ bytesToBits (u16le x.length ++ u16le (65535 - x.length) ++ x) := by
    rw [deflateStored_eq]
    show byteBits 0x01 ++ _ = _
    rw [byteBits_one]
  unfold inflate
  simp only [hbits]
  rw [inflateAux_one_stored cfg _ o2 _ hst]
  exact ⟨hox, rfl⟩

/-! ## Fixed-Huffman round-trip (RFC 1951 §3.2.6)

A concrete deflate→inflate round-trip on the *fixed-Huffman* path, not the stored
path: `deflateFixed` emits a single final `BTYPE=01` block encoding each input
byte with the fixed literal code (§3.2.6: symbols 0–143 use the 8-bit codes
`00110000..10111111`, i.e. `0x30 + symbol`), terminated by the 7-bit end-of-block
code `0000000` (symbol 256). Inflate then decodes the fixed Huffman trees and
recovers the bytes. The round-trip theorems below are proved by kernel reduction
(`rfl`) on small inputs — `inflate (deflateFixed x) = x` genuinely computing
through `buildHuffman fixedLitLengths`, the MSB-first Huffman `decode`, and the
literal push. (The encoder handles input bytes ≤ 143, which covers ASCII.)
-/

/-- The `w` bits of `v`, most-significant first — the order a Huffman codeword is
packed into the stream and the order `decode` assembles it (§3.1.1). -/
def msbBits (v w : Nat) : Bits := (List.range w).reverse.map (fun i => (v >>> i) &&& 1 == 1)

/-- Pack 8 stream bits (LSB-first) into one byte — the inverse of `byteBits`. -/
def packByte (chunk : List Bool) : UInt8 :=
  UInt8.ofNat ((List.range 8).foldl (fun acc i => acc + (if chunk.getD i false then 2 ^ i else 0)) 0)

/-- Pack a flat bit stream into bytes, 8 bits at a time (final byte zero-padded).
Structural on an explicit fuel so it reduces in the kernel (needed by the `rfl`
round-trips); `bits.length` fuel always suffices since each step consumes 8. -/
def packBytesF : Nat → List Bool → List UInt8
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, bits => packByte (bits.take 8) :: packBytesF fuel (bits.drop 8)

/-- Pack a bit stream into bytes. -/
def packBytes (bits : List Bool) : List UInt8 := packBytesF bits.length bits

/-- Encode a byte list (each byte ≤ 143) as one final fixed-Huffman block
(§3.2.6): `BFINAL=1`, `BTYPE=01`, each byte as its 8-bit fixed literal code
`0x30 + byte`, then the 7-bit end-of-block code. -/
def deflateFixed (x : List UInt8) : List UInt8 :=
  packBytes ([true, true, false] ++ x.flatMap (fun b => msbBits (48 + b.toNat) 8) ++ msbBits 0 7)

set_option maxRecDepth 100000 in
/-- **Fixed-Huffman round-trip (empty).** Inflating the fixed-Huffman encoding of
the empty message recovers the empty message, decoding through the fixed trees. -/
theorem inflate_fixed_roundtrip_empty :
    (inflate ⟨100⟩ (deflateFixed [])).out = #[]
      ∧ (inflate ⟨100⟩ (deflateFixed [])).err = none := by
  refine ⟨?_, ?_⟩ <;> rfl

set_option maxRecDepth 100000 in
/-- **Fixed-Huffman round-trip (small).** For the concrete input `"hi"` the
fixed-Huffman path round-trips: `inflate (deflateFixed [0x68, 0x69]) = [0x68,
0x69]`, no error — kernel-checked through `buildHuffman fixedLitLengths` and the
MSB-first Huffman decode of two 8-bit literals and the 7-bit end-of-block code. -/
theorem inflate_fixed_roundtrip_hi :
    (inflate ⟨100⟩ (deflateFixed [0x68, 0x69])).out = #[0x68, 0x69]
      ∧ (inflate ⟨100⟩ (deflateFixed [0x68, 0x69])).err = none := by
  refine ⟨?_, ?_⟩ <;> rfl

end Deflate
